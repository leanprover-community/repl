/-
Copyright (c) 2023 Kim Morrison. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lean.Environment

/-!
# Replay constants into an elaboration environment

In Lean v4.30+, `Environment.replay` returns an environment via `ofKernelEnv` whose
constants live in `Kernel.Environment.constants.map₂`. However, `Environment.find?`
only checks `constants.map₁` and `asyncConstsMap`, so replayed constants are invisible
to elaboration. (LeanChecker confirms this: in v4.30 it discards the env after replay
— `replay` is purely a verification tool now.)

This module provides `replayToElabEnv`, which uses the FFI export `lake_environment_add`
that Lake declares in `src/lake/Lake/Load/Lean/Elab.lean` (the export of the private
`Lean.Environment.lakeAdd`). That helper inserts a `ConstantInfo` into both the kernel
environment's constant map *and* `asyncConstsMap`, which is what `Environment.find?`
needs.

## Trust model

`replayToElabEnv` bypasses kernel type-checking. The REPL produces and consumes its own
pickles, so the constants being replayed have already been checked by the kernel once.
**Pickles are trusted artifacts; this is not a verifier boundary.** A malicious or
corrupt `.olean` could install unchecked constants directly into the environment.

## Caveats

* This only restores constants — *not* environment extension entries (which Lake's
  `importConfigFileCore` partially handles via `IR.declMapExt`). This matches the
  existing REPL limitation around scoped extensions.
* `lake_environment_add` is a private Lean export ("only needed for the lakefile.lean
  cache", per the comment in `Lean.Environment`). It is not a stable public API. If
  this file stops compiling against a future Lean release, search lean4 for
  `lake_environment_add` and adapt. The REPL is unlikely to get a supported public API
  for this since it is on a deprecation path.
-/

namespace Lean.Environment

-- `compiler.ignoreBorrowAnnotation` matches the C ABI of the exported `lake_environment_add`
-- symbol; Lake uses the same option for the same wrapper.
set_option compiler.ignoreBorrowAnnotation true in
/--
Insert an already-kernel-checked `ConstantInfo` directly into an `Environment`,
populating both the kernel constant map and `asyncConstsMap`. **No type checking.**
This is the FFI symbol Lake uses in `importConfigFileCore`.
-/
@[extern "lake_environment_add"]
private opaque addAlreadyCheckedConstantInfo
    (env : Environment) (_ : ConstantInfo) : Environment

/--
Add new constants to an elaboration `Environment`, ensuring they are visible to
`Environment.find?`.

This replaces `Environment.replay` for use cases where the resulting environment
needs to be used for elaboration (not just verification). It does not perform kernel
checking; see the trust model in the module docstring.
-/
def replayToElabEnv (env : Environment)
    (newConstants : Std.HashMap Name ConstantInfo) : Environment :=
  newConstants.fold (init := env) fun env _ ci =>
    if ci.isUnsafe || ci.isPartial then env else addAlreadyCheckedConstantInfo env ci

end Lean.Environment
