/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Data.Finset.Lattice

/-!
This file shows that each set `s` in a join-semilattice generates a set
`directedClosure s` such that:
* `subset_directedClosure`: `s` is a subset of `directedClosure s`
* `directedOn_directedClosure`: `directedClosure s` is directed
* `isLUB_directedClosure`: `u` is the least upper bound of `s` if and only if it is the least upper
  bound of `directedClosure s`
-/

namespace Finset
variable {α β : Type*} [SemilatticeSup α]

-- This will come from https://github.com/leanprover-community/mathlib/pull/18989
lemma sup'_union [DecidableEq β] {s₁ s₂ : Finset β} (h₁ : s₁.Nonempty) (h₂ : s₂.Nonempty)
  (f : β → α) :
  (s₁ ∪ s₂).sup' (h₁.mono $ subset_union_left _ _) f = s₁.sup' h₁ f ⊔ s₂.sup' h₂ f :=
eq_of_forall_ge_iff $ λ a ↦ by simp [or_imp, forall_and]

end Finset

variable {α : Type*} [SemilatticeSup α]
open Finset

/-- Every set in a join-semilattice generates a directed set. Note that this is **not** a closure
operator because directness is not preserved under intersections. -/
def directedClosure (s : Set α) : Set α :=
  {a | ∃ (t : Finset α) (ht : t.Nonempty), ↑t ⊆ s ∧ t.sup' ht id = a}

@[simp] lemma subset_directedClosure {s : Set α} : s ⊆ directedClosure s :=
λ a ha ↦ ⟨{a}, singleton_nonempty _, by simpa⟩

@[simp] lemma directedOn_directedClosure {s : Set α} : DirectedOn (. ≤ .) (directedClosure s) := by
  classical
  rintro _ ⟨t, ht, hts, rfl⟩ _ ⟨u, hu, hus, rfl⟩
  refine' ⟨_, ⟨_, ht.mono $ subset_union_left _ _, _, sup'_union ht hu _⟩,
    le_sup_left, le_sup_right⟩
  rw [coe_union]
  exact Set.union_subset hts hus

@[simp] lemma upperBounds_directedClosure {s : Set α} :
  upperBounds (directedClosure s) = upperBounds s :=
(upperBounds_mono_set subset_directedClosure).antisymm $ by
  rintro a ha _ ⟨t, ht, hts, rfl⟩
  exact sup'_le _ _ λ b hb ↦ ha $ hts hb

@[simp] lemma isLUB_directedClosure {s : Set α} {a : α} :
  IsLUB (directedClosure s) a ↔ IsLUB s a := by simp [IsLUB]
