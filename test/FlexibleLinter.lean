import Std.Tactic.PermuteGoals
import Mathlib.Tactic.FlexibleLinter
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

set_option warningAsError true

-- for some reason, disabling and re-enabling the linter means that
-- `#guard_msgs` actually catches the output!
set_option linter.flexible false in
set_option linter.flexible true in
/--
error: 'simp at h' stains 'h'... [linter.flexible]
---
info: ... and 'exact h' uses 'h'!
-/
#guard_msgs in
example (h : 0 + 0 = 0) : True := by
  simp at h
  try exact h

-- `subst` does not use the goal
#guard_msgs in
example {a b : Nat} (h : a = b) : a + 0 = b := by
  simp
  subst h
  rfl

set_option linter.flexible false in
set_option linter.flexible true in
/--
error: 'simp at h' stains 'h'... [linter.flexible]
---
info: ... and 'exact h' uses 'h'!
-/
#guard_msgs in
example (h : 0 = 0 ∨ 0 = 0) : True := by
  cases h <;>
    rename_i h <;>
    simp at h
  · exact h
  · assumption --exact h

set_option linter.flexible false in
set_option linter.flexible true in
/--
error: 'simp' stains '⊢'... [linter.flexible]
---
info: ... and 'contradiction' uses '⊢'!
---
error: 'simp' stains '⊢'... [linter.flexible]
---
info: ... and 'contradiction' uses '⊢'!
-/
#guard_msgs in
example (h : 0 = 1 ∨ 0 = 1) : 0 = 1 ∧ 0 = 1 := by
  cases h <;> simp
  on_goal 2 => · contradiction
  · contradiction

-- `omega` is a follower and `all_goals` is a `combinatorLike`
#guard_msgs in
example {a : Nat} : a + 1 + 0 = 1 + a := by simp; all_goals omega

set_option linter.flexible false in
set_option linter.flexible true in
/--
error: 'simp' stains '⊢'... [linter.flexible]
---
info: ... and 'contradiction' uses '⊢'!
---
error: 'simp' stains '⊢'... [linter.flexible]
---
info: ... and 'contradiction' uses '⊢'!
-/
#guard_msgs in
example (h : 0 = 1 ∨ 0 = 1) : 0 = 1 ∧ 0 = 1 := by
  cases h <;> simp
  · contradiction
  · contradiction

set_option linter.flexible false in
set_option linter.flexible true in
/--
error: 'simp at h k' stains 'k'... [linter.flexible]
---
info: ... and 'rw [← Classical.not_not (a := True)] at k' uses 'k'!
---
error: 'simp at h k' stains 'h'... [linter.flexible]
---
info: ... and 'rw [← Classical.not_not (a := True)] at h' uses 'h'!
-/
#guard_msgs in
-- `simp at h` stains `h` but not other locations
example {h : 0 = 0} {k : 1 = 1} : True := by
  simp at h k;
  rw [← Classical.not_not (a := True)]
  -- flag the two below vvv do not above ^^^
  rw [← Classical.not_not (a := True)] at k
  rw [← Classical.not_not (a := True)] at h
  assumption

-- `specialize` does not touch, by default, the target
#guard_msgs in
example {a b : Nat} (h : ∀ c, c + a + b = a + c) : (0 + 2 + 1 + a + b) = a + 3 := by
  simp
  specialize h 3
  simp_all

-- `norm_num` is allowed after `simp`.
#guard_msgs in
example : (0 + 2 : Rat) < 3 := by
  simp
  norm_num

set_option linter.flexible false in
set_option linter.flexible true in
/--
error: 'simp' stains '⊢'... [linter.flexible]
---
info: ... and 'rw [add_comm]' uses '⊢'!
-/
#guard_msgs in
-- `norm_num` is allowed after `simp`, but "passes along the stain".
example {a : Rat} : a + (0 + 2 : Rat) < 3 + a := by
  simp
  norm_num
  rw [add_comm]
  norm_num

set_option linter.flexible false in
set_option linter.flexible true in
/--
error: 'simp' stains '⊢'... [linter.flexible]
---
info: ... and 'exact h.symm' uses '⊢'!
-/
#guard_msgs in
-- `congr` is allowed after `simp`, but "passes along the stain".
example {a b : Nat} (h : a = b) : a + b + 0 = b + a := by
  simp
  congr
  exact h.symm

-- `done` is an allowed follower
#guard_msgs in
example (h : False) : 0 ≠ 0 := by
  try (simp; done)
  exact h.elim

--  `abel_nf` is a `rigidifier`: the "stain" of `simp` does not continue past `abel_nf`.
#guard_msgs in
example {a b : Nat} (h : a + b = a + (b + 1)) : a + b = b + a + 0 + 1 := by
  simp
  abel_nf
  assumption

--  `abel` is an allowed `simp`-follower.
#guard_msgs in
example {a b : Nat} : a + b = b + a + 0 := by
  simp
  abel

--  `ring_nf` is a `rigidifier`: the "stain" of `simp` does not continue past `ring_nf`.
#guard_msgs in
example {a b : Nat} (h : a + b = 1 + a + b) : a + b = b + a + 0 + 1 := by
  simp
  ring_nf
  assumption

--  `ring` is an allowed `simp`-follower.
#guard_msgs in
example {a b : Nat} : a + b = b + a + 0 := by
  simp
  ring

set_option linter.flexible false in
set_option linter.flexible true in
/--
error: 'simp' stains '⊢'... [linter.flexible]
---
info: ... and 'contradiction' uses '⊢'!
-/
#guard_msgs in
example (h : 0 = 1 ∨ 0 = 1) : 0 = 1 ∧ 0 = 1 := by
  cases h <;> simp
  · simp_all
  · contradiction

-- forget stained locations, once the corresponding goal is closed
#guard_msgs in
example (n : Nat) : n + 1 = 1 + n := by
  by_cases 0 = 0
  · simp_all
    omega
  · have : 0 ≠ 1 := by
      intro h
      -- should not flag `cases`!
      cases h
    -- should not flag `exact`!
    exact Nat.add_comm ..

set_option linter.flexible false in
set_option linter.flexible true in
/--
error: 'simp at h' stains 'h'... [linter.flexible]
---
info: ... and 'rw [← Classical.not_not (a := True)] at h' uses 'h'!
-/
#guard_msgs in
-- `simp at h` stains `h` but not other locations
example {h : 0 = 0} {k : 1 = 1} : ¬ ¬ True := by
  simp at h
  rw [← Nat.add_zero 1] at k
  -- flag below vvv do not flag above ^^^
  rw [← Classical.not_not (a := True)] at h
  --exact h -- <-- flagged
  assumption


set_option linter.flexible false in
set_option linter.flexible true in
/--
error: 'simp at h k' stains 'k'... [linter.flexible]
---
info: ... and 'rw [← Classical.not_not (a := True)] at k' uses 'k'!
---
error: 'simp at h k' stains 'h'... [linter.flexible]
---
info: ... and 'rw [← Classical.not_not (a := True)] at h' uses 'h'!
-/
#guard_msgs in
-- `simp at h` stains `h` but not other locations
example {h : 0 = 0} {k : 1 = 1} : True := by
  simp at h k
  rw [← Classical.not_not (a := True)]
  -- flag the two below vvv do not above ^^^
  rw [← Classical.not_not (a := True)] at k
  rw [← Classical.not_not (a := True)] at h
  assumption

set_option linter.flexible false in
set_option linter.flexible true in
/--
error: 'simp at h' stains 'h'... [linter.flexible]
---
info: ... and 'rw [← Classical.not_not (a := True)] at h' uses 'h'!
-/
#guard_msgs in
-- `simp at h` stains `h` but not other locations
example {h : 0 = 0} : True := by
  simp at h
  rw [← Classical.not_not (a := True)]
  -- flag below vvv do not flag above ^^^
  rw [← Classical.not_not (a := True)] at h
  assumption

set_option linter.flexible false in
set_option linter.flexible true in
/--
error: 'simp' stains '⊢'... [linter.flexible]
---
info: ... and 'rwa [← Classical.not_not (a := False)]' uses '⊢'!
-/
#guard_msgs in
example {h : False} : 0 = 1 := by
  simp
  rw [← Classical.not_not (a := False)] at h
  -- flag below vvv do not flag above ^^^
  rwa [← Classical.not_not (a := False)]

set_option linter.flexible false in
set_option linter.flexible true in
/--
error: 'simp' stains '⊢'... [linter.flexible]
---
info: ... and 'rwa [← Classical.not_not (a := False)]' uses '⊢'!
-/
#guard_msgs in
example {h : False} : 0 = 1 ∧ 0 = 1 := by
  constructor
  · simpa
  . simp
    rw [← Classical.not_not (a := False)] at h
    rwa [← Classical.not_not (a := False)]

section test_internals
open Lean Mathlib.Linter.flexible

/-- `flex? tac` logs an info `true` if the tactic is flexible, logs a warning `false` otherwise. -/
elab "flex? " tac:tactic : command => do
  match flexible? tac with
    | true  => logWarningAt tac m!"{flexible? tac}"
    | false => logInfoAt tac m!"{flexible? tac}"

section set_option linter.unreachableTactic false
/-- info: false -/#guard_msgs in
flex? done
/-- info: false -/#guard_msgs in
flex? simp only
/-- info: false -/#guard_msgs in
flex? simp_all only
/-- error: true -/#guard_msgs in
flex? simp
/-- error: true -/#guard_msgs in
flex? simp_all
end

/-- info: #[h] -/ #guard_msgs in
#eval show CoreM _ from do
  let h := mkIdent `h
  let hc : TSyntax `Lean.Parser.Tactic.casesTarget := ⟨h⟩
  IO.println s!"{(toStained (← `(tactic| cases $hc))).toArray}"
