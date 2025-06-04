import Lean
import Lake


open Lean Elab System

set_option maxHeartbeats 2000000  -- 10x the default maxHeartbeats.


instance : ToJson Substring where
  toJson s := toJson s.toString

instance : ToJson String.Pos where
  toJson n := toJson n.1

deriving instance ToJson for SourceInfo
deriving instance ToJson for Syntax.Preresolved
deriving instance ToJson for Syntax
deriving instance ToJson for Position


-- namespace LeanDojo


/--
The trace of a tactic.
-/
structure TacticTrace where
  stateBefore: String
  stateAfter: String
  pos: String.Pos      -- Start position of the tactic.
  endPos: String.Pos   -- End position of the tactic.
deriving ToJson

-- 定义配置结构
structure ExtractionConfig where
  extractTactics : Bool
  extractPremises : Bool

/--
The trace of a premise.
-/
structure PremiseTrace where
  fullName: String            -- Fully-qualified name of the premise.
  defPos: Option Position     -- Where the premise is defined.
  defEndPos: Option Position
  modName: String             -- In which module the premise is defined.
  defPath: String             -- The path of the file where the premise is defined.
  pos: Option Position        -- Where the premise is used.
  endPos: Option Position
deriving ToJson


/--
The trace of a Lean file.
-/
structure Trace where
  commandASTs : Array Syntax    -- The ASTs of the commands in the file.
  tactics: Array TacticTrace    -- All tactics in the file.
  premises: Array PremiseTrace  -- All premises in the file.
deriving ToJson


abbrev TraceM := StateT Trace MetaM


namespace Pp


private def addLine (s : String) : String :=
  if s.isEmpty then s else s ++ "\n"


-- Similar to `Meta.ppGoal` but uses String instead of Format to make sure local declarations are separated by "\n".
private def ppGoal (mvarId : MVarId) : MetaM String := do
  match (← getMCtx).findDecl? mvarId with
  | none          => return "unknown goal"
  | some mvarDecl =>
    let indent         := 2
    let lctx           := mvarDecl.lctx
    let lctx           := lctx.sanitizeNames.run' { options := (← getOptions) }
    Meta.withLCtx lctx mvarDecl.localInstances do
      -- The followint two `let rec`s are being used to control the generated code size.
      -- Then should be remove after we rewrite the compiler in Lean
      let rec pushPending (ids : List Name) (type? : Option Expr) (s : String) : MetaM String := do
        if ids.isEmpty then
          return s
        else
          let s := addLine s
          match type? with
          | none      => return s
          | some type =>
            let typeFmt ← Meta.ppExpr type
            return (s ++ (Format.joinSep ids.reverse (format " ") ++ " :" ++ Format.nest indent (Format.line ++ typeFmt)).group).pretty
      let rec ppVars (varNames : List Name) (prevType? : Option Expr) (s : String) (localDecl : LocalDecl) : MetaM (List Name × Option Expr × String) := do
        match localDecl with
        | .cdecl _ _ varName type _ _ =>
          let varName := varName.simpMacroScopes
          let type ← instantiateMVars type
          if prevType? == none || prevType? == some type then
            return (varName :: varNames, some type, s)
          else do
            let s ← pushPending varNames prevType? s
            return ([varName], some type, s)
        | .ldecl _ _ varName type val _ _ => do
          let varName := varName.simpMacroScopes
          let s ← pushPending varNames prevType? s
          let s  := addLine s
          let type ← instantiateMVars type
          let typeFmt ← Meta.ppExpr type
          let mut fmtElem  := format varName ++ " : " ++ typeFmt
          let val ← instantiateMVars val
          let valFmt ← Meta.ppExpr val
          fmtElem := fmtElem ++ " :=" ++ Format.nest indent (Format.line ++ valFmt)
          let s := s ++ fmtElem.group.pretty
          return ([], none, s)
      let (varNames, type?, s) ← lctx.foldlM (init := ([], none, "")) fun (varNames, prevType?, s) (localDecl : LocalDecl) =>
         if localDecl.isAuxDecl || localDecl.isImplementationDetail then
           -- Ignore auxiliary declarations and implementation details.
           return (varNames, prevType?, s)
         else
           ppVars varNames prevType? s localDecl
      let s ← pushPending varNames type? s
      let goalTypeFmt ← Meta.ppExpr (← instantiateMVars mvarDecl.type)
      let goalFmt := Meta.getGoalPrefix mvarDecl ++ Format.nest indent goalTypeFmt
      let s := s ++ "\n" ++ goalFmt.pretty
      match mvarDecl.userName with
      | Name.anonymous => return s
      | name           => return "case " ++ name.eraseMacroScopes.toString ++ "\n" ++ s


def ppGoals (ctx : ContextInfo) (goals : List MVarId) : IO String :=
  if goals.isEmpty then
    return "no goals"
  else
    let fmt := ctx.runMetaM {} (return Std.Format.prefixJoin "\n\n" (← goals.mapM (ppGoal ·)))
    return (← fmt).pretty.trim


end Pp


namespace Path

/--
Return the path of `path` relative to `parent`.
-/
def relativeTo (path parent : FilePath) : Option FilePath :=
  let rec componentsRelativeTo (pathComps parentComps : List String) : Option FilePath :=
    match pathComps, parentComps with
    | _, [] => mkFilePath pathComps
    | [], _ => none
    | (h₁ :: t₁), (h₂ :: t₂) =>
      if h₁ == h₂ then
        componentsRelativeTo t₁ t₂
      else
        none

    componentsRelativeTo path.components parent.components


/--
Return if the path `path` is relative to `parent`.
-/
def isRelativeTo (path parent : FilePath) : Bool :=
  match relativeTo path parent with
  | some _ => true
  | none => false


/--
Convert the path `path` to an absolute path.
-/
def toAbsolute (path : FilePath) : IO FilePath := do
  if path.isAbsolute then
    pure path
  else
    let cwd ← IO.currentDir
    pure $ cwd / path


private def trim (path : FilePath) : FilePath :=
  assert! path.isRelative
  mkFilePath $ path.components.filter (· != ".")


def packagesDir : FilePath :=
  if Lake.defaultPackagesDir == "packages"  then
    ".lake" / Lake.defaultPackagesDir
  else
    Lake.defaultPackagesDir


def buildDir : FilePath :=
  if Lake.defaultPackagesDir.fileName == "packages" then  -- Lean >= v4.3.0-rc2
    ".lake/build"
  else  -- Lean < v4.3.0-rc2
   "build"


def libDir : FilePath := buildDir / "lib"


/--
Convert the path of a *.lean file to its corresponding file (e.g., *.olean) in the "build" directory.
-/
def toBuildDir (subDir : FilePath) (path : FilePath) (ext : String) : Option FilePath :=
  let path' := (trim path).withExtension ext
  match relativeTo path' $ packagesDir / "lean4/src" with
  | some p =>
    match relativeTo p "lean/lake" with
    | some p' => packagesDir / "lean4/lib/lean" / p'
    | none => packagesDir / "lean4/lib" / p
  | none => match relativeTo path' packagesDir with
    | some p =>
      match p.components with
      | [] => none
      | hd :: tl => packagesDir / hd / buildDir / subDir / (mkFilePath tl)
    | none => buildDir / subDir / path'


/--
The reverse of `toBuildDir`.
-/
-- proofwidgets/build/lib/ProofWidgets/Compat.lean
-- proofwidgets/.lake/build/lib
def toSrcDir! (path : FilePath) (ext : String) : FilePath :=
  let path' := (trim path).withExtension ext
  match relativeTo path' $ packagesDir / "lean4/lib" with
  | some p =>  -- E.g., `.lake/packages/lean4/lib/lean/Init/Prelude.olean` -> `.lake/packages/lean4/src/lean/Init/Prelude.lean`
    packagesDir / "lean4/src" / p
  | none =>
    match relativeTo path' packagesDir with
    | some p =>  -- E.g., `.lake/packages/aesop/.lake/build/lib/Aesop.olean`-> `.lake/packages/aesop/Aesop.lean`
      let pkgName := p.components.head!
      let sep := "build/lib/"
      packagesDir / pkgName / (p.toString.splitOn sep |>.tail!.head!)
    | none =>
      -- E.g., `.lake/build/lib/Mathlib/LinearAlgebra/Basic.olean` -> `Mathlib/LinearAlgebra/Basic.lean`
      relativeTo path' libDir |>.get!


/--
Create all parent directories of `p` if they don't exist.
-/
def makeParentDirs (p : FilePath) : IO Unit := do
  let some parent := p.parent | throw $ IO.userError s!"Unable to get the parent of {p}"
  IO.FS.createDirAll parent


/--
Return the *.lean file corresponding to a module name.
-/
def findLean (mod : Name) : IO FilePath := do
  let modStr := mod.toString
  if modStr.startsWith "«lake-packages»." then
    return FilePath.mk (modStr.replace "«lake-packages»" "lake-packages" |>.replace "." "/") |>.withExtension "lean"
  if modStr.startsWith "«.lake»." then
    return FilePath.mk (modStr.replace "«.lake»" ".lake" |>.replace "." "/") |>.withExtension "lean"
  let olean ← findOLean mod
  -- Remove a "build/lib/" substring from the path.
  let lean := olean.toString.replace ".lake/build/lib/" ""
    |>.replace "build/lib/" "" |>.replace "lib/lean/Lake/" "lib/lean/lake/Lake/" |>.replace "lib/lean/Init" "src/lean/Init"
  let mut path := FilePath.mk lean |>.withExtension "lean"
  let leanLib ← getLibDir (← getBuildDir)
  -- let projectRoot := (leanLib.parent >>= (·.parent) >>= (·.parent) >>= (·.parent) >>= (·.parent) >>= (·.parent) >>= (·.parent)).get!
  if let some p := relativeTo path leanLib then
    path := packagesDir / "lean4/src/lean" / p
  if !(← path.pathExists) then
    -- IO.println s!"WARNING: Path does not exist: {path}"
    -- IO.println s!"OLean file: {olean.toString}"
    -- IO.println s!"path: {path}"
    -- Instead of using assert!, return an error or handle it appropriately
    throw <| IO.userError s!"Path does not exist: {path}"
  return path

end Path


namespace Traversal


/--
Extract tactic information from `TacticInfo` in `InfoTree`.
-/
private def visitTacticInfo (ctx : ContextInfo) (ti : TacticInfo) (parent : InfoTree) (config : ExtractionConfig) : TraceM Unit := do
  if not config.extractTactics then
    return ()
  match ti.stx.getKind with
  | ``Lean.Parser.Term.byTactic =>
    match ti.stx with
    | .node _ _ #[.atom _ "by", .node _ ``Lean.Parser.Tactic.tacticSeq _] => pure ()
    | _ => assert! false

  | ``Lean.Parser.Tactic.tacticSeq =>
    match ti.stx with
    | .node _ _ #[.node _ ``Lean.Parser.Tactic.tacticSeq1Indented _] => pure ()
    | .node _ _ #[.node _ ``Lean.Parser.Tactic.tacticSeqBracketed _] => pure ()
    | _ => assert! false

  | _ => pure ()

  match parent with
  | .node (Info.ofTacticInfo i) _ =>
    match i.stx.getKind with
    | ``Lean.Parser.Tactic.tacticSeq1Indented | ``Lean.Parser.Tactic.tacticSeqBracketed | ``Lean.Parser.Tactic.rewriteSeq =>
      let ctxBefore := { ctx with mctx := ti.mctxBefore }
      let ctxAfter := { ctx with mctx := ti.mctxAfter }
      let stateBefore ← Pp.ppGoals ctxBefore ti.goalsBefore
      let stateAfter ← Pp.ppGoals ctxAfter ti.goalsAfter
      if stateBefore == "no goals" || stateBefore == stateAfter then
        pure ()
      else
        let some posBefore := ti.stx.getPos? true | pure ()
        let some posAfter := ti.stx.getTailPos? true | pure ()
        match ti.stx with
        | .node _ _ _ =>
          modify fun trace => {
            trace with tactics := trace.tactics.push {
              stateBefore := stateBefore,
              stateAfter := stateAfter,
              pos := posBefore,
              endPos := posAfter,
             }
          }
        | _ => pure ()
    | _ => pure ()
  | _ => pure ()


/--
Extract premise information from `TermInfo` in `InfoTree`.
-/
private def visitTermInfo (ti : TermInfo) (env : Environment) (config : ExtractionConfig) : TraceM Unit := do
  if not config.extractPremises then
    return ()
  let some fullName := ti.expr.constName? | return ()
  let fileMap ← getFileMap

  let posBefore := match ti.toElabInfo.stx.getPos? with
    | some posInfo => fileMap.toPosition posInfo
    | none => none

  let posAfter := match ti.toElabInfo.stx.getTailPos? with
    | some posInfo => fileMap.toPosition posInfo
    | none => none

  let decRanges ← withEnv env $ findDeclarationRanges? fullName
  let defPos := decRanges >>= fun (decR : DeclarationRanges) => decR.selectionRange.pos
  let defEndPos := decRanges >>= fun (decR : DeclarationRanges) => decR.selectionRange.endPos

  let modName :=
  if let some modIdx := env.const2ModIdx.find? fullName then
    env.header.moduleNames[modIdx.toNat]!
  else
    env.header.mainModule

  -- -- 添加调试输出
  -- IO.println s!"modName: {modName}"

  let mut defPath := ""
  try
    defPath := toString $ ← Path.findLean modName
    if defPath.startsWith "./" then
      defPath := defPath.drop 2
    if defPath.startsWith "/lake/" then
      defPath := ".lake/" ++ (defPath.drop 6)
  catch _ =>
    defPath := toString modName

  if defPos != posBefore ∧ defEndPos != posAfter then  -- Don't include defintions as premises.
    modify fun trace => {
        trace with premises := trace.premises.push {
          fullName := toString fullName,
          defPos := defPos,
          defEndPos := defEndPos,
          defPath := defPath,
          modName := toString modName,
          pos := posBefore,
          endPos := posAfter,
        }
    }

-- 修改 visitInfo 函数
private def visitInfo (ctx : ContextInfo) (i : Info) (parent : InfoTree) (env : Environment) (config : ExtractionConfig) : TraceM Unit := do
  match i with
  | .ofTacticInfo ti => visitTacticInfo ctx ti parent config
  | .ofTermInfo ti => visitTermInfo ti env config
  | _ => pure ()

-- 假设 ContextInfo 是一个记录类型，我们需要为其实现 ToString 实例
-- instance : ToString ContextInfo where
--   toString ctx := s!"ContextInfo(mctx: {ctx.mctx}, lctx: {ctx.lctx}, declName: {ctx.declName})"

-- 修改 traverseTree 函数
private partial def traverseTree (ctx: ContextInfo) (tree : InfoTree)
(parent : InfoTree) (env : Environment) (config : ExtractionConfig) : TraceM Unit := do
  match tree with
  | .context ctx' t =>
    match ctx'.mergeIntoOuter? ctx with
    | some ctx' =>
      traverseTree ctx' t tree env config
    | none => panic! "fail to synthesis contextInfo when traversing infoTree"
  | .node i children =>
    visitInfo ctx i parent env config
    for x in children do
      traverseTree ctx x tree env config
  | _ => pure ()


-- 修改 traverseTopLevelTree 函数
private def traverseTopLevelTree (tree : InfoTree) (env : Environment) (config : ExtractionConfig) : TraceM Unit := do
  match tree with
  | .context ctx t =>
    match ctx.mergeIntoOuter? none with
    | some ctx => traverseTree ctx t tree env config
    | none => panic! "fail to synthesis contextInfo for top-level infoTree"
  | _ => pure ()


-- 修改 traverseForest 函数
def traverseForest (trees : Array InfoTree) (env : Environment) (config : ExtractionConfig) : TraceM Trace := do
  for t in trees do
    traverseTopLevelTree t env config
  get


end Traversal


open Traversal


def getImports (header: Syntax) : IO String := do
  -- Similar to `lean --deps` in Lean 3.
  let mut s := ""

  for dep in headerToImports header do
    let oleanPath ← findOLean dep.module
    if oleanPath.isRelative then
      let leanPath := Path.toSrcDir! oleanPath "lean"
      assert! ← leanPath.pathExists
      s := s ++ "\n" ++ leanPath.toString
    else if ¬(oleanPath.toString.endsWith "/lib/lean/Init.olean") then
      let mut p := (Path.packagesDir / "lean4").toString ++ FilePath.pathSeparator.toString
      let mut found := false
      for c in (oleanPath.withExtension "lean").components do
        if c == "lib" then
          found := true
          p := p ++ "src"
          continue
        if found then
          p := p ++ FilePath.pathSeparator.toString ++ c
      p := p.replace "/lean4/src/lean/Lake" "/lean4/src/lean/lake/Lake"
      assert! ← FilePath.mk p |>.pathExists
      s := s ++ "\n" ++ p

  return s.trim

-- 修改 extractAST 函数
def extractAST (code : String) (config : ExtractionConfig) : IO Json := do
  let inputCtx := Parser.mkInputContext code "<input>"
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx
  if messages.hasErrors then
    for msg in messages.toList do
      if msg.severity == .error then
        println! "ERROR: {← msg.toString}"
    throw $ IO.userError "Errors during import; aborting"
  let commandState := { Command.mkState env messages {} with infoState.enabled := true }
  let s ← IO.processCommands inputCtx parserState commandState
  let env' := s.commandState.env
  let commands := s.commands.pop -- Remove EOI command.
  let trees := s.commandState.infoState.trees.toArray
  let traceM := (traverseForest trees env' config).run' ⟨#[header] ++ commands, #[], #[]⟩
  let (trace, _) ← traceM.run'.toIO {fileName := "<input>", fileMap := FileMap.ofString code} {env := env}
  return toJson trace -- 返回AST的JSON表示
