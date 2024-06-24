/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/

import Lean.Elab.Tactic.Rewrite

/-!
# `nth_rewrite` tactic

The tactic `nth_rewrite` and `nth_rw` are variants of `rewrite` and `rw` that only performs the
`n`th possible rewrite.

-/
namespace Mathlib.Tactic

open Lean Elab Tactic Meta Parser.Tactic

/-- `nth_rewrite` is a variant of `rewrite` that only changes the `n`ᵗʰ _occurrence_ of the
expression to be rewritten. `nth_rewrite n [eq₁, eq₂, ..., eqₘ]` will rewrite the `n`ᵗʰ _occurrence_
of each of the `m` equalities `eqᵢ`in that order. Occurrences are counted beginning with `1`.
If a term `t` is introduced by rewriting with `eqᵢ`, then this instance of `t` will be counted
as an _occurrence_ of `t` for all subsequent rewrites of `t` with `eqⱼ` for `j > i`.

Note: The occurrences are counted beginning with `1` and not `0`, this is different than in
mathlib3. The translation will be handled by mathport. -/
syntax (name := nthRewriteSeq) "nth_rewrite" (config)? ppSpace num rwRuleSeq (location)? : tactic

@[inherit_doc nthRewriteSeq, tactic nthRewriteSeq] def evalNthRewriteSeq : Tactic := fun stx => do
  match stx with
  | `(tactic| nth_rewrite $[$_cfg]? $n $_rules $[$_loc]?) =>
    -- [TODO] `stx` should not be used directly, but the corresponding functions do not yet exist
    -- in Lean 4 core
    let cfg ← elabRewriteConfig stx[1]
    let loc := expandOptLocation stx[4]
    let occ := Occurrences.pos [n.getNat]
    let cfg := { cfg with occs := occ }
    withRWRulesSeq stx[0] stx[3] fun symm term => do
      withLocation loc
        (rewriteLocalDecl term symm · cfg)
        (rewriteTarget term symm cfg)
        (throwTacticEx `nth_rewrite · "did not find instance of the pattern in the current goal")
  | _ => throwUnsupportedSyntax

/--
`nth_rw` is a variant of `nth_rewrite` that also tries to close the goal by trying `rfl` afterwards.
`nth_rw n [eq₁, eq₂,..., eqₘ]` will rewrite the `n`ᵗʰ _occurrence_ of each of the `m` equalities
`eqᵢ`in that order. Occurrences are counted beginning with `1`. If a term `t` is introduced
by rewriting with `eqᵢ`, then this instance of `t` will be counted as an _occurrence_ of `t` for all
subsequent rewrites of `t` with `eqⱼ` for `j > i`. Further, `nth_rw` will close the remaining goal
with `rfl` if possible.
-/
macro (name := nthRwSeq) "nth_rw" c:(config)? ppSpace n:num s:rwRuleSeq l:(location)? : tactic =>
  -- Note: This is a direct copy of `nth_rw` from core.
  match s with
  | `(rwRuleSeq| [$rs,*]%$rbrak) =>
    -- We show the `rfl` state on `]`
    `(tactic| (nth_rewrite $(c)? $n [$rs,*] $(l)?; with_annotate_state $rbrak
      (try (with_reducible rfl))))
  | _ => Macro.throwUnsupported
