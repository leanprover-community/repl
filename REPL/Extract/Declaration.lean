import REPL.JSON

open Lean Elab System Parser

namespace REPL

/-! Extract information about declarations from info trees
Inspired by <https://github.com/frenzymath/jixia>
-/

/-- See `Lean.Parser.Command.declModifiers` and `Lean.Elab.elabModifiers` -/
def getModifiers (stx : Syntax) (ctx: ContextInfo): DeclModifiers :=
  match stx with
  | .node _ ``Command.declModifiers _ =>
    { docString := stx[0].getOptional?.map (fun stx =>
        { content := stx.prettyPrint.pretty, range := stx.toRange ctx }),
      visibility := (stx[2].getOptional?.map (·.prettyPrint.pretty.trim)).getD "regular",
      computeKind := (stx[4].getOptional?.map (·.prettyPrint.pretty.trim)).getD "regular",
      isProtected := !stx[3].isNone,
      isUnsafe := !stx[5].isNone,
      recKind := (stx[6].getOptional?.map (·.prettyPrint.pretty.trim)).getD "default",
      attributes := stx[1].getArgs.toList.flatMap parseAttributes, }
  | _ => {}
  where
    /-- Parse attribute instances from a Term.attributes syntax node
    See `Lean.Parser.Term.attributes`.
    -/
    parseAttributes (attrSyntax : Syntax) : List String :=
      match attrSyntax with
      | .node _ ``Term.attributes args =>
        -- args[0] is "@[", args[1] is the attribute list, args[2] is "]"
        if args.size > 1 then
          args[1]!.getArgs.toList.flatMap fun inst =>
            match inst with
            | .node _ ``Term.attrInstance _ => [inst.prettyPrint.pretty.trim]
            | _ => []
        else []
      | _ => []

partial def getIdents (stx : Syntax) : Array Name :=
  match stx with
  | .node _ _ args => args.flatMap getIdents
  | .ident _ _ id _ => #[id]
  | _ => #[]

/-- See `Lean.Elab.Term.toBinderViews` -/
def toBinderViews (stx : Syntax) : Array BinderView :=
  let k := stx.getKind
  if stx.isIdent || k == ``Term.hole then
    -- binderIdent
    #[{ id := (expandBinderIdent stx), type := mkHole stx, binderInfo := "default" }]
  else if k == ``Lean.Parser.Term.explicitBinder then
    -- `(` binderIdent+ binderType (binderDefault <|> binderTactic)? `)`
    let ids := getBinderIds stx[1]
    let type        := stx[2]
    -- let optModifier := stx[3]
    ids.map fun id => { id := (expandBinderIdent id), type := (expandBinderType id type), binderInfo := "default" }
  else if k == ``Lean.Parser.Term.implicitBinder then
    -- `{` binderIdent+ binderType `}`
    let ids := getBinderIds stx[1]
    let type := stx[2]
    ids.map fun id => { id := (expandBinderIdent id), type := (expandBinderType id type), binderInfo := "implicit" }
  else if k == ``Lean.Parser.Term.strictImplicitBinder then
    -- `⦃` binderIdent+ binderType `⦄`
    let ids := getBinderIds stx[1]
    let type := stx[2]
    ids.map fun id => { id := (expandBinderIdent id), type := (expandBinderType id type), binderInfo := "strictImplicit" }
  else if k == ``Lean.Parser.Term.instBinder then
    -- `[` optIdent type `]`
    let id := expandOptIdent stx[1]
    let type := stx[2]
    #[ { id := id, type := type, binderInfo := "instImplicit" } ]
  else
    #[]
  where
    getBinderIds (ids : Syntax) : Array Syntax :=
      ids.getArgs.map fun (id : Syntax) =>
        let k := id.getKind
        if k == identKind || k == `Lean.Parser.Term.hole then id
        else Syntax.missing
    expandBinderType (ref : Syntax) (stx : Syntax) : Syntax :=
      if stx.getNumArgs == 0 then mkHole ref else stx[1]
    expandBinderIdent (stx : Syntax) : Syntax :=
      match stx with
      | `(_) => Syntax.missing
      | _    => stx
    expandOptIdent (stx : Syntax) : Syntax :=
      if stx.isNone then Syntax.missing else stx[0]

def getScope (ctx : ContextInfo) (state : Command.State) : ScopeInfo :=
  let scope := state.scopes.head!
  {
    varDecls := scope.varDecls.map fun stx => s!"variable {stx.raw.prettyPrint.pretty}",
    includeVars := scope.includedVars.toArray.map fun name => name.eraseMacroScopes,
    omitVars := scope.omittedVars.toArray.map fun name => name.eraseMacroScopes,
    levelNames := scope.levelNames.toArray,
    currNamespace := ctx.currNamespace,
    openDecl := ctx.openDecls,
  }

partial def extractDeclarationInfo (cmdInfo : CommandInfo) (infoTree : InfoTree) (ctx : ContextInfo)
  (prevState : Command.State) : DeclarationInfo :=
  let stx := cmdInfo.stx
  let modifiers := getModifiers stx[0] ctx
  let decl := stx[1]
  let kind := decl.getKind
  let kindStr := match kind with
    | .str _ s => s
    | _ => kind.toString

  -- See `Lean.Elab.DefView`
  let (signature, id, binders, type?, value?) := match kind with
    | ``Command.abbrev
    | ``Command.definition =>
      let (binders, type) := expandOptDeclSig decl[2]
      (decl[2], decl[1], binders, type, some decl[3])
    | ``Command.theorem =>
      let (binders, type) := expandDeclSig decl[2]
      (decl[2], decl[1], binders, some type, some decl[3])
    | ``Command.opaque =>
      let (binders, type) := expandDeclSig decl[2]
      (decl[2], decl[1], binders, some type, decl[3].getOptional?)
    | ``Command.axiom =>
      let (binders, type) := expandDeclSig decl[2]
      (decl[2], decl[1], binders, some type, none)
    | ``Command.inductive
    | ``Command.classInductive =>
      let (binders, type) := expandOptDeclSig decl[2]
      (decl[2], decl[1], binders, type, some decl[4])
    | ``Command.instance =>
      let (binders, type) := expandDeclSig decl[4]
      let declId := match stx[3].getOptional? with
        | some declId => declId
        | none        => Syntax.missing -- TODO: improve this
      (decl[4], declId, binders, some type, some decl[5])
    | ``Command.example =>
      let id              := mkIdentFrom stx[0] `_example (canonical := true)
      let declId          := mkNode ``Parser.Command.declId #[id, mkNullNode]
      let (binders, type) := expandOptDeclSig decl[1]
      (decl[1], declId, binders, type, some decl[2])
    | ``Command.structure =>
      let signature := Syntax.node2 .none ``Command.optDeclSig decl[2] decl[4]
      let (binders, type) := (decl[2], some decl[4])
      (signature, decl[1], binders, type, none)
    | _ => unreachable!

  let name := id[0].getId
  let fullName := match getFullname infoTree name with -- TODO: could be better
    | [] => name
    | a :: _  => a

  let binders : Option DeclBinders := match binders.getArgs with
    | #[] => none
    | _ => some { pp := binders.prettyPrint.pretty,
                  groups := binders.getArgs.map (·.prettyPrint.pretty),
                  map := binders.getArgs.flatMap toBinderViews,
                  range := binders.toRange ctx }

  -- let a := prevState.env.constants.find! decl[1].getId
  -- a.getUsedConstantsAsSet

  let extractConstants (stx : Syntax) : Array Name := -- TODO: improve this
    let idents := ((getIdents stx).foldl
      (init := NameSet.empty) fun acc name => acc.insert name).toArray
    idents
    -- idents.filter prevState.env.constants.contains

  {
    pp := stx.prettyPrint.pretty,
    name,
    fullName,
    kind := kindStr,
    modifiers,
    scope := getScope ctx prevState,
    signature := { pp := signature.prettyPrint.pretty,
                    constants := extractConstants signature,
                    range := signature.toRange ctx },
    binders,
    type := type?.map fun t =>
      { pp := t.prettyPrint.pretty, constants := extractConstants t, range := t.toRange ctx },
    value := value?.map fun v =>
      { pp := v.prettyPrint.pretty, constants := extractConstants v, range := v.toRange ctx },
    range := stx.toRange ctx
  }
where
  getFullname (infoTree : InfoTree) (shortName : Name) : List Name :=
    match infoTree with
    | .context _ t => getFullname t shortName
    | .node i ts  =>
      match i with
        | .ofTermInfo ti => ti.expr.constName?.toList.filter (fun n =>
              match shortName.componentsRev with
              | [] => true
              | h :: _ => match n.componentsRev with
                | [] => false
                | h' :: _ => h == h'
            )
        | _ => ts.toList.flatMap (getFullname · shortName)
    | _ => []

open Lean.Parser in
/-- Extract all declarations from InfoTrees -/
partial def extractCmdDeclarationInfos (trees : List InfoTree) (prevState : Command.State) :
    List DeclarationInfo :=
  let allDecls := trees.map (extractFromTree · none prevState)
  allDecls.flatten
where
  extractFromTree (t : InfoTree) (ctx? : Option ContextInfo) (prevState : Command.State) :
      List DeclarationInfo :=
    match t with
    | .context ctx t => extractFromTree t (ctx.mergeIntoOuter? ctx?) prevState
    | .node i ts =>
      match i with
      | .ofCommandInfo cmdInfo =>
        match ctx? with
        | some ctx =>
          if cmdInfo.stx.getKind == ``Command.declaration then
            [extractDeclarationInfo cmdInfo t ctx prevState]
          else
            ts.toList.flatMap (extractFromTree · ctx? prevState)
        | none => ts.toList.flatMap (extractFromTree · ctx? prevState)
      | _ => ts.toList.flatMap (extractFromTree · ctx? prevState)
    | _ => []

def extractAllDeclarationInfos (treeList : List (IncrementalState × Option InfoTree)) (prevState : Command.State) : List DeclarationInfo :=
  match treeList with
  | [] => []
  | (state, infoTree?) :: rest =>
    let decls := extractCmdDeclarationInfos infoTree?.toList prevState
    let restDecls := extractAllDeclarationInfos rest state.commandState
    decls ++ restDecls
