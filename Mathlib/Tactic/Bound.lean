/-
Copyright (c) 2024 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving
-/

import Aesop
import Mathlib.Algebra.Order.AbsoluteValue
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Bound.Attribute
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Core

/-!
## The `bound` tactic

`bound` is an `aesop` wrapper that proves inequalities by straightforward recursion on structure,
assuming that intermediate terms are nonnegative or positive as needed.  It also has some report
for guessing where it is unclear where to recurse, such as which side of a `min` or `max` to use
as the bound or whether to assume a power is less than or greater than one.

The functionality of `bound` overlaps with `positivity` and `gcongr`, but can jump back and forth
between `0 ≤ x` and `x ≤ y`-type inequalities.  For example, `bound` proves
  `0 ≤ c → b ≤ a → 0 ≤ a * c - b * c`
By turning the goal into `b * c ≤ a * c`, then using `mul_le_mul_of_nonneg_right`.  `bound` also
uses specialized lemmas for goals of the form `1 ≤ x, 1 < x, x ≤ 1, x < 1`.

Additional hypotheses can be passed as `bound [h0, h1 n, ...]`.  This is equivalent to declaring
them via `have` before calling `bound`.

See `test/Bound.lean` for tests.

### Calc usage

Since `bound` requires the inequality proof to exactly match the structure of the expression, it is
often useful to iterate between `bound` and `rw / simp` using `calc`.  Here is an example:

```
-- Calc example: A weak lower bound for `z ↦ z^2 + c`
lemma le_sqr_add {c z : ℂ} (cz : abs c ≤ abs z) (z3 : 3 ≤ abs z) :
    2 * abs z ≤ abs (z^2 + c) := by
  calc abs (z^2 + c)
    _ ≥ abs (z^2) - abs c := by bound
    _ ≥ abs (z^2) - abs z := by bound
    _ ≥ (abs z - 1) * abs z := by rw [mul_comm, mul_sub_one, ← pow_two, ← abs.map_pow]
    _ ≥ 2 * abs z := by bound
```

### Aesop rules

`bound` uses threes types of aesop rules: `apply`, `forward`, and closing `tactic`s.  To register a
lemma as an `apply` rule, tag it with `@[bound]`.  It will be automatically converted into either a
`norm apply` or `safe apply` rule depending on the number and type of its hypotheses:

1. Nonnegativity/positivity/nonpositivity/negativity hypotheses get score 1 (those involving `0`).
2. Other inequalities get score 10.
3. Disjunctions `a ∨ b` gets score 100, plus the score of `a` and `b`.

Score `0` lemmas turn into `norm apply` rules, and score `0 < s` lemmas turn into `safe apply s`
rules.  The score is roughly lexicographic ordering on the counts of the three type (guessing,
general, involving-zero), and tries to minimize the complexity of hypotheses we have to prove.
See `Mathlib.Tactic.Bound.Attribute` for the full algorithm.

To register a lemma as a `forward` rule, tag it with `@[bound_forward]`.  The most important
builtin forward rule is `le_of_lt`, so that strict inequalities can be used to prove weak
inequalities.  Another example is `HasFPowerSeriesOnBall.r_pos`, so that `bound` knows that any
power series present in the context have positive radius of convergence.  Custom `@[bound_forward]`
rules that similarly expose inequalities inside structures are often useful.

### Guessing apply rules

There are several cases where there are two standard ways to recurse down an inequality, and it is
not obvious which is correct without more information.  For example, `a ≤ min b c` is registered as
a `safe apply 4` rule, since we always need to prove `a ≤ b ∧ a ≤ c`.  But if we see `min a b ≤ c`,
either `a ≤ b` and `a ≤ c` suffices, and we don't know which.

In these cases we declare a new lemma with an `∨` hypotheses that covers the two cases.  Tagging
it as `@[bound]` will add a +100 penalty to the score, so that it will be used only if necessary.
Aesop will then try both ways by splitting on the resulting `∨` hypothesis.

Currently the two types of guessing rules are
1. `min` and `max` rules, for both `≤` and `<`
2. `pow` and `rpow` monotonicity rules which branch on `1 ≤ a` or `a ≤ 1`.

### Closing tactics

We close numerical goals with `norm_num` and `linarith`.
-/

open Lean Elab Meta Term Mathlib.Tactic Syntax
open Lean.Elab.Tactic (liftMetaTactic liftMetaTactic' TacticM getMainGoal)

namespace Bound

/-!
### Extra lemmas for `bound`
-/

/-- Possibly this one should be deleted, but we'd need to add support for `ℕ ≠ 0` goals -/
lemma le_self_pow_of_pos {R : Type} [OrderedSemiring R] {a : R} {m : ℕ} (ha : 1 ≤ a) (h : 0 < m) :
    a ≤ a^m :=
  le_self_pow ha h.ne'

/-!
### `.mpr` lemmas of iff statements for use as Aesop apply rules

Once Aesop can do general terms directly, we can remove these:

  https://github.com/leanprover-community/aesop/issues/107
-/

lemma mul_lt_mul_left_of_pos_of_lt {α : Type} {a b c : α} [Mul α] [Zero α] [Preorder α]
    [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a) : b < c → a * b < a * c :=
  (mul_lt_mul_left a0).mpr

lemma mul_lt_mul_right_of_pos_of_lt {α : Type} {a b c : α} [Mul α] [Zero α] [Preorder α]
    [MulPosStrictMono α] [MulPosReflectLT α] (c0 : 0 < c) : a < b → a * c < b * c :=
  (mul_lt_mul_right c0).mpr

lemma one_lt_div_of_pos_of_lt {α : Type} [LinearOrderedSemifield α] {a b : α} (b0 : 0 < b) :
    b < a → 1 < a / b :=
  (one_lt_div b0).mpr

lemma div_lt_one_of_pos_of_lt {α : Type} [LinearOrderedSemifield α] {a b : α} (b0 : 0 < b) :
    a < b → a / b < 1 :=
  (div_lt_one b0).mpr

lemma Nat.cast_pos_of_pos {R : Type} [OrderedSemiring R] [Nontrivial R] {n : ℕ} :
    0 < n → 0 < (n : R) :=
  Nat.cast_pos.mpr

lemma Nat.one_le_cast_of_le {α : Type} [AddCommMonoidWithOne α] [PartialOrder α]
    [CovariantClass α α (fun (x y : α) => x + y) fun (x y : α) => x ≤ y] [ZeroLEOneClass α]
    [CharZero α] {n : ℕ} : 1 ≤ n → 1 ≤ (n : α) :=
  Nat.one_le_cast.mpr

/-!
### Apply rules for `bound`
-/

-- Reflexivity
attribute [bound] le_refl

-- 0 ≤, 0 <
attribute [bound] sq_nonneg Nat.cast_nonneg abs_nonneg AbsoluteValue.nonneg Nat.zero_lt_succ
  Int.ceil_lt_add_one pow_pos pow_nonneg sub_nonneg_of_le sub_pos_of_lt inv_nonneg_of_nonneg
  inv_pos_of_pos tsub_pos_of_lt mul_pos mul_nonneg div_pos div_nonneg add_nonneg

-- 1 ≤, ≤ 1
attribute [bound] inv_le_one Nat.one_le_cast_of_le one_le_pow_of_one_le pow_le_one
  one_le_mul_of_one_le_of_one_le div_le_one_of_le mul_inv_le_one_of_le inv_mul_le_one_of_le

-- ≤
attribute [bound] le_abs_self Int.le_ceil neg_abs_le neg_le_neg tsub_le_tsub_right
  pow_le_pow_left div_le_div_of_nonneg_right mul_le_mul_of_nonneg_left
  mul_le_mul_of_nonneg_right div_le_self le_add_of_nonneg_right le_add_of_nonneg_left
  inv_le_inv_of_le le_self_pow_of_pos le_mul_of_one_le_right mul_le_of_le_one_right le_div_self
  Finset.sum_le_sum sub_le_sub add_le_add div_le_div mul_le_mul

-- Triangle inequalities
attribute [bound] AbsoluteValue.le_add AbsoluteValue.le_sub AbsoluteValue.add_le
  AbsoluteValue.sub_le_add AbsoluteValue.abs_abv_sub_le_abv_sub

-- <
attribute [bound] Nat.cast_pos_of_pos neg_lt_neg sub_lt_sub_left sub_lt_sub_right add_lt_add_left
  add_lt_add_right mul_lt_mul_left_of_pos_of_lt mul_lt_mul_right_of_pos_of_lt div_lt_div_of_pos_left
  div_lt_div_of_pos_right pow_lt_pow_left div_lt_self one_lt_div_of_pos_of_lt
  div_lt_one_of_pos_of_lt

-- min and max
attribute [bound] min_le_right min_le_left le_max_left le_max_right le_min max_le lt_min max_lt

-- Memorize a few constants to avoid going to `norm_num`
attribute [bound] zero_le_one zero_lt_one zero_le_two zero_lt_two

/-!
### Forward rules for `bound`
-/

-- Bound applies `le_of_lt` to all hypotheses
attribute [bound_forward] le_of_lt

/-!
### Guessing rules: when we don't know how to recurse
-/

section Guessing

variable {α : Type} [LinearOrder α] {a b c : α}

-- `min` and `max` guessing lemmas
lemma le_max_of_le_left_or_le_right : a ≤ b ∨ a ≤ c → a ≤ max b c := le_max_iff.mpr
lemma lt_max_of_lt_left_or_lt_right : a < b ∨ a < c → a < max b c := lt_max_iff.mpr
lemma min_le_of_left_le_or_right_le : a ≤ c ∨ b ≤ c → min a b ≤ c := min_le_iff.mpr
lemma min_lt_of_left_lt_or_right_lt : a < c ∨ b < c → min a b < c := min_lt_iff.mpr

/-- Branch on `1 ≤ a ∨ a ≤ 1` for `a^n` -/
lemma pow_le_pow_right_of_le_one_or_one_le {R : Type} [OrderedSemiring R] {a : R} {n m : ℕ}
    (h : 1 ≤ a ∧ n ≤ m ∨ 0 ≤ a ∧ a ≤ 1 ∧ m ≤ n) : a ^ n ≤ a ^ m := by
  rcases h with ⟨a1, nm⟩ | ⟨a0, a1, mn⟩
  · exact pow_le_pow_right a1 nm
  · exact pow_le_pow_of_le_one a0 a1 mn

-- Register guessing rules
attribute [bound]
  -- Which side of the `max` should we use as the lower bound?
  le_max_of_le_left_or_le_right
  lt_max_of_lt_left_or_lt_right
  -- Which side of the `min` should we use as the upper bound?
  min_le_of_left_le_or_right_le
  min_lt_of_left_lt_or_right_lt
  -- Given `a^m ≤ a^n`, is `1 ≤ a` or `a ≤ 1`?
  pow_le_pow_right_of_le_one_or_one_le

end Guessing

/-!
### Closing tactics
-/

/-- Close numerical goals with `norm_num` -/
def boundNormNum : Aesop.RuleTac :=
  Aesop.SingleRuleTac.toRuleTac fun i => do
    let tac := do Mathlib.Meta.NormNum.elabNormNum .missing .missing .missing
    let goals ← Lean.Elab.Tactic.run i.goal tac |>.run'
    if !goals.isEmpty then failure
    return (#[], none, some .hundred)
attribute [aesop unsafe 10% tactic (rule_sets := [Bound])] boundNormNum

/-- Close numerical and other goals with `linarith` -/
def boundLinarith : Aesop.RuleTac :=
  Aesop.SingleRuleTac.toRuleTac fun i => do
    Linarith.linarith false [] {} i.goal
    return (#[], none, some .hundred)
attribute [aesop unsafe 5% tactic (rule_sets := [Bound])] boundLinarith

/-!
### `bound` tactic implementation
-/

/-- Pull the array out of an optional `"[" term,* "]"` syntax, or return `#[]` -/
def maybeTerms : Syntax → Array Syntax
  | node _ _ #[_, node _ _ s, _] => s.getEvenElems
  | _ => #[]

/-- Add extra hypotheses -/
def addHyps (xs : Array Syntax) : TacticM Unit :=
  if xs.isEmpty then pure () else Tactic.withMainContext do
    for x in xs do
      let v ← elabTerm x none
      let t ← inferType v
      liftMetaTactic fun g ↦ do
        let g ← g.assert `h t v
        let (_, g) ← g.intro1P
        return [g]

/-- Aesop configuration for `bound` -/
def boundConfig : Aesop.Options := {
  enableSimp := false
}

end Bound

/-- `bound` tactic for proving inequalities via straightforward recursion on expression structure -/
elab "bound" lemmas:(("[" term,* "]")?) : tactic => do
  Bound.addHyps (Bound.maybeTerms lemmas)
  let tac ← `(tactic| aesop (rule_sets := [Bound, -default]) (config := Bound.boundConfig))
  liftMetaTactic fun g ↦ do return (← Lean.Elab.runTactic g tac.raw).1
