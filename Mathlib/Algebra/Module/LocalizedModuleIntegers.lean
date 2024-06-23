/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Module.LocalizedModule

/-!
# Integer elements of a localization

## Main definitions

 * `IsLocalization.IsInteger` is a predicate stating that `x : S` is in the image of `R`

## Implementation notes

See `RingTheory/Localization/Basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/


variable {R : Type*} [CommSemiring R] {S : Submonoid R} {M : Type*} [AddCommMonoid M]
variable [Module R M]-- {P : Type*} [CommSemiring P]
variable {M' : Type*} [AddCommMonoid M'] [Module R M'] (f : M →ₗ[R] M')

open Function

namespace IsLocalizedModule

section

/-- Given `a : S`, `S` a localization of `R`, `IsInteger R a` iff `a` is in the image of
the localization map from `R` to `S`. -/
def IsInteger (m : M') : Prop :=
  m ∈ LinearMap.range f

end

/-
theorem isInteger_zero : IsInteger R (0 : S) :=
  Subsemiring.zero_mem _

theorem isInteger_one : IsInteger R (1 : S) :=
  Subsemiring.one_mem _

theorem isInteger_add {a b : S} (ha : IsInteger R a) (hb : IsInteger R b) : IsInteger R (a + b) :=
  Subsemiring.add_mem _ ha hb

theorem isInteger_mul {a b : S} (ha : IsInteger R a) (hb : IsInteger R b) : IsInteger R (a * b) :=
  Subsemiring.mul_mem _ ha hb

theorem isInteger_smul {a : R} {b : S} (hb : IsInteger R b) : IsInteger R (a • b) := by
  rcases hb with ⟨b', hb⟩
  use a * b'
  rw [← hb, (algebraMap R S).map_mul, Algebra.smul_def]
-/

variable (S)
variable [IsLocalizedModule S f]

/-- Each element `a : S` has an `M`-multiple which is an integer.

This version multiplies `a` on the right, matching the argument order in `LocalizationMap.surj`.
-/
theorem exists_integer_multiple (x : M') : ∃ a : S, IsInteger f (a.val • x) :=
  let ⟨⟨Num, denom⟩, h⟩ := IsLocalizedModule.surj S f x
  ⟨denom, Set.mem_range.mpr ⟨Num, h.symm⟩⟩

/-- We can clear the denominators of a `Finset`-indexed family of fractions. -/
theorem exist_integer_multiples {ι : Type*} (s : Finset ι) (g : ι → M') :
    ∃ b : S, ∀ i ∈ s, IsInteger f (b.val • g i) := by
  classical
  have (i : ι) := IsLocalizedModule.surj S f (g i)
  choose sec hsec using this
  refine ⟨∏ i ∈ s, (sec i).2, fun i hi => ⟨?_, ?_⟩⟩
  · exact (∏ j ∈ s.erase i, (sec j).2) • (sec i).1
  simp only [LinearMap.map_smul_of_tower, Submonoid.coe_finset_prod]
  rw [← hsec, ← mul_smul, Submonoid.smul_def]
  congr
  simp only [Submonoid.coe_mul, Submonoid.coe_finset_prod, mul_comm]
  rw [← Finset.prod_insert (f := fun i ↦ ((sec i).snd).val) (s.not_mem_erase i)]
  rw [Finset.insert_erase hi]

/-- We can clear the denominators of a finite indexed family of fractions. -/
theorem exist_integer_multiples_of_finite {ι : Type*} [Finite ι] (g : ι → M') :
    ∃ b : S, ∀ i, IsInteger f ((b : R) • g i) := by
  cases nonempty_fintype ι
  obtain ⟨b, hb⟩ := exist_integer_multiples S f Finset.univ g
  exact ⟨b, fun i => hb i (Finset.mem_univ _)⟩

/-- We can clear the denominators of a finite set of fractions. -/
theorem exist_integer_multiples_of_finset (s : Finset M') :
    ∃ b : S, ∀ a ∈ s, IsInteger f ((b : R) • a) :=
  exist_integer_multiples S f s id

/-- A choice of a common multiple of the denominators of a `Finset`-indexed family of fractions. -/
noncomputable def commonDenom {ι : Type*} (s : Finset ι) (g : ι → M') : S :=
  (exist_integer_multiples S f s g).choose

/-- The numerator of a fraction after clearing the denominators
of a `Finset`-indexed family of fractions. -/
noncomputable def integerMultiple {ι : Type*} (s : Finset ι) (g : ι → M') (i : s) : M :=
  ((exist_integer_multiples S f s g).choose_spec i i.prop).choose

@[simp]
theorem map_integerMultiple {ι : Type*} (s : Finset ι) (g : ι → M') (i : s) :
    f (integerMultiple S f s g i) = commonDenom S f s g • g i :=
  ((exist_integer_multiples S f s g).choose_spec _ i.prop).choose_spec

/-- A choice of a common multiple of the denominators of a finite set of fractions. -/
noncomputable def commonDenomOfFinset (s : Finset M') : S :=
  commonDenom S f s id

/-- The finset of numerators after clearing the denominators of a finite set of fractions. -/
noncomputable def finsetIntegerMultiple [DecidableEq M] (s : Finset M') : Finset M :=
  s.attach.image fun t => integerMultiple S f s id t

open Pointwise

theorem finsetIntegerMultiple_image [DecidableEq M] (s : Finset M') :
    f '' finsetIntegerMultiple S f s = commonDenomOfFinset S f s • (s : Set M') := by
  delta finsetIntegerMultiple commonDenom
  rw [Finset.coe_image]
  ext
  constructor
  · rintro ⟨_, ⟨x, -, rfl⟩, rfl⟩
    rw [map_integerMultiple]
    exact Set.mem_image_of_mem _ x.prop
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨⟨x, hx⟩, s.mem_attach _, rfl⟩, map_integerMultiple S f s id _⟩

end IsLocalizedModule
