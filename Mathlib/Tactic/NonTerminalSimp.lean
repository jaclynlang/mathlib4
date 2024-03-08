/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Elab.Command

/-!
#  The non-terminal `simp` linter

The non-terminal `simp` linter makes sure that `simp` is not used as a finishing tactic.
If you want to use `simp [...]` followed by other tactics, then replace `simp [...]`
by the output of `simp? [...]`, so that the final code contains `simp only [...]`.

Currently, the linter is conservative in catching non-terminal `simp`s.
It only uses syntax information.
In its current form, the (almost) only false positives are situations of the form
```lean
  ...
  tactic producing two goals <;> [simp; simp]
```
-/

open Lean

namespace Mathlib.Linter

/-- The non-terminal `simp` linter makes sure that `simp` is not used as a finishing tactic. -/
register_option linter.nonTerminalSimp : Bool := {
  defValue := false
  descr := "enable the 'non-terminal `simp`' linter"
}

namespace nonTerminalSimpLinter

/-- `onlyOrNotSimp stx` if `stx` is syntax for `simp` *without* `only`, then returns `false` else
returchecks whether `stx` is `simp only -/
def onlyOrNotSimp : Syntax → Bool
  | .node _info `Lean.Parser.Tactic.simp #[_, _, _, only?, _, _] =>
    only?[0].getAtomVal == "only"
  | _ => true

variable {m : Type → Type} [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m] in
/-- `nonTerminalSimp stx` loops inside `stx` looking for nodes corresponding to `simp` calls
that are not `simp only` calls.  Among those, it checks whether there are further tactics
after the `simp`, and, if there are, then it emits a warning. -/
partial
def nonTerminalSimp : Syntax → m Unit
  | .node _ _ args => do
    match args.findIdx? (! onlyOrNotSimp ·) with
      | none => default
      | some n =>
        for i in [n+1:args.size] do
          if "Lean.Parser.Tactic".isPrefixOf args[i]!.getKind.toString then
            logWarningAt args[n]!
              "non-terminal simp: consider replacing it with the output of `simp?`"
    let _ ← args.mapM nonTerminalSimp
  | _ => default

/-- Gets the value of the `linter.nonTerminalSimp` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.nonTerminalSimp o

@[inherit_doc linter.nonTerminalSimp]
def nonTerminalSimpLinter : Linter where run := withSetOptionIn fun stx => do
  if getLinterHash (← getOptions) then
    nonTerminalSimp stx

initialize addLinter nonTerminalSimpLinter
