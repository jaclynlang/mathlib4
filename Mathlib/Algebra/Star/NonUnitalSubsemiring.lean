/-
Copyright (c) 2024 Christopher Hoskin. All rights reserved.
Released under Apache 2. license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Subsemigroup.Basic
import Mathlib.RingTheory.NonUnitalSubsemiring.Basic
import Mathlib.Algebra.Ring.Subsemiring.Basic
import Mathlib.Algebra.Star.Center

/-!
# Non-unital Star Subsemirings

In this file we define `NonUnitalStarSubsemiring`s and the usual operations on them.

## Implementation

This file is heavily inspired by `Mathlib.Algebra.Star.NonUnitalSubalgebra`.

-/

universe v w w'

variable {A : Type v} {B : Type w} {C : Type w'}

/-- A sub star magma is a subset of a magma which is closed under the `star`-/
structure SubStarmagma (M : Type v) [Mul M] [Star M] extends Subsemigroup M : Type v where
  /-- The `carrier` of a `StarSubset` is closed under the `star` operation. -/
  star_mem' : ∀ {a : M} (_ha : a ∈ carrier), star a ∈ carrier

/-- Reinterpret a `SubStarmagma` as a `Subsemigroup`. -/
add_decl_doc SubStarmagma.toSubsemigroup

/-- A non-unital star subsemiring is a non-unital subsemiring which also is closed under the
`star` operation. -/
structure NonUnitalStarSubsemiring (R : Type v) [NonUnitalNonAssocSemiring R] [Star R]
    extends NonUnitalSubsemiring R : Type v where
  /-- The `carrier` of a `NonUnitalStarSubsemiring` is closed under the `star` operation. -/
  star_mem' : ∀ {a : R} (_ha : a ∈ carrier), star a ∈ carrier

/-- Reinterpret a `NonUnitalStarSubsemiring` as a `NonUnitalSubsemiring`. -/
add_decl_doc NonUnitalStarSubsemiring.toNonUnitalSubsemiring

/-- A (unital) star subsemiring is a non-associative ring which is closed under the `star`
operation. -/
structure StarSubsemiring (R : Type v) [NonAssocSemiring R] [Star R]
    extends Subsemiring R : Type v where
  /-- The `carrier` of a `StarSubsemiring` is closed under the `star` operation. -/
  star_mem' : ∀ {a : R} (_ha : a ∈ carrier), star a ∈ carrier

/-- Reinterpret a `StarSubsemiring` as a `Subsemiring`. -/
add_decl_doc StarSubsemiring.toSubsemiring

section NonUnitalStarSubsemiring

namespace NonUnitalStarSubsemiring

variable {R : Type v} [NonUnitalNonAssocSemiring R] [StarRing R]

instance instSetLike : SetLike (NonUnitalStarSubsemiring R) R where
  coe {s} := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.coe_injective h

instance instNonUnitalSubsemiringClass : NonUnitalSubsemiringClass (NonUnitalStarSubsemiring R) R
    where
  add_mem {s} := s.add_mem'
  mul_mem {s} := s.mul_mem'
  zero_mem {s} := s.zero_mem'

instance instStarMemClass : StarMemClass (NonUnitalStarSubsemiring R) R where
  star_mem {s} := s.star_mem'

theorem mem_carrier {s : NonUnitalStarSubsemiring R} {x : R} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

/-- Copy of a non-unital star subsemiring with a new `carrier` equal to the old one.
Useful to fix definitional equalities. -/
protected def copy (S : NonUnitalStarSubsemiring R) (s : Set R) (hs : s = ↑S) :
    NonUnitalStarSubsemiring R :=
  { S.toNonUnitalSubsemiring.copy s hs with
    star_mem' := @fun x (hx : x ∈ s) => by
      show star x ∈ s
      rw [hs] at hx ⊢
      exact S.star_mem' hx }

@[simp]
theorem coe_copy (S : NonUnitalStarSubsemiring R) (s : Set R) (hs : s = ↑S) :
    (S.copy s hs : Set R) = s :=
  rfl

theorem copy_eq (S : NonUnitalStarSubsemiring R) (s : Set R) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

section Center

variable (R)

/-- The center of a non-unital non-associative semiring `R` is the set of elements that
commute and associate with everything in `R`, here realized as non-unital star
subsemiring. -/
def center (R) [NonUnitalNonAssocSemiring R] [StarRing R] : NonUnitalStarSubsemiring R where
  toNonUnitalSubsemiring := NonUnitalSubsemiring.center R
  star_mem' := Set.star_mem_center

end Center

end NonUnitalStarSubsemiring

end NonUnitalStarSubsemiring

section StarSubsemiring

namespace StarSubsemiring

variable {R : Type v} [NonAssocSemiring R] [StarRing R]

instance instSetLike : SetLike (StarSubsemiring R) R where
  coe {s} := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.coe_injective h

instance instSubsemiringClass : SubsemiringClass (StarSubsemiring R) R
    where
  add_mem {s} := s.add_mem'
  mul_mem {s} := s.mul_mem'
  zero_mem {s} := s.zero_mem'
  one_mem {s} := s.one_mem'

instance instStarMemClass : StarMemClass (StarSubsemiring R) R where
  star_mem {s} := s.star_mem'

theorem mem_carrier {s : StarSubsemiring R} {x : R} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

/-- Copy of a non-unital star subalgebra with a new `carrier` equal to the old one.
Useful to fix definitional equalities. -/
protected def copy (S : StarSubsemiring R) (s : Set R) (hs : s = ↑S) :
    StarSubsemiring R :=
  { S.toSubsemiring.copy s hs with
    star_mem' := @fun x (hx : x ∈ s) => by
      show star x ∈ s
      rw [hs] at hx ⊢
      exact S.star_mem' hx }

@[simp]
theorem coe_copy (S : StarSubsemiring R) (s : Set R) (hs : s = ↑S) :
    (S.copy s hs : Set R) = s :=
  rfl

theorem copy_eq (S : StarSubsemiring R) (s : Set R) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

section Center

variable (R)

/-- The center of a semiring `R` is the set of elements that commute and associate with everything
in `R` -/
def center (R) [NonAssocSemiring R][StarRing R] : StarSubsemiring R where
  toSubsemiring := Subsemiring.center R
  star_mem' := Set.star_mem_center

end Center

end StarSubsemiring

end StarSubsemiring
section SubStarmagma

variable (A) [Mul A] [StarMul A]

namespace SubStarmagma

/-- The center of magma `A` is the set of elements that commute and associate
with everything in `A`, here realized as a `SubStarSemigroup`. -/
def center : SubStarmagma A :=
  { Subsemigroup.center A with
    star_mem' := Set.star_mem_center }

end SubStarmagma

end SubStarmagma
