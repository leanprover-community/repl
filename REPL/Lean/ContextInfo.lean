/-
Copyright (c) 2023 Kim Morrison. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lean

namespace Lean.Elab.ContextInfo

/-- Pretty print an expression in the given `ContextInfo` with the given `LocalContext`. -/
def ppExpr (ctx : ContextInfo) (lctx : LocalContext) (e : Expr) : IO Format :=
  ctx.runMetaM lctx (do Meta.ppExpr (← instantiateMVars e))

end Lean.Elab.ContextInfo
