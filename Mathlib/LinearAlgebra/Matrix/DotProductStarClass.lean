/-
Copyright (c) 2023 Mohanad ahmed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.IsROrC.Basic
import Mathlib.Data.Matrix.Rank

/-! # Fields with Star Inner Product (dotProduct or vector Product) as Norm

This file defines the class type `StarDotProductSpace` i.e. fields with star operation compatible
with field operations (StarRing) such that the stared vector product (in 1st argument) is zero only
if the vector is zero.
-/

open BigOperators Matrix

class StarDotProductSpace (n K) [Fintype n][Ring K][StarRing K] : Prop where
  dotProduct_star_self_eq_zero (v : n → K) : Matrix.dotProduct (star v) v = 0 ↔ v = 0

variable {n : Type _}[Fintype n]

lemma dotProduct_self_star_eq_zero  (v : n → K) [Ring K] [StarRing K]
  [StarDotProductSpace n K] : Matrix.dotProduct v (star v) = 0 ↔ v = 0 := by
  have : ∃ (w : n → K), star v = w := by simp only [exists_eq']
  obtain ⟨w, hw ⟩ := this
  replace h := congr_arg (fun x => star x) hw
  simp only [star_star] at h
  rw [h, star_star, star_eq_zero, StarDotProductSpace.dotProduct_star_self_eq_zero]

section IsROrCFields

variable {K: Type _} [IsROrC K]

@[simp, isROrC_simps]
theorem IsROrC.re_sum (f : n → K) : IsROrC.re (∑ i in s, f i) = ∑ i in s, IsROrC.re (f i) := by
  apply map_sum _ _

@[simp, isROrC_simps]
theorem IsROrC.im_sum (f : n → K) : IsROrC.im (∑ i in s, f i) = ∑ i in s, IsROrC.im (f i) := by
  apply map_sum _ _

open IsROrC
def instStarDotProduct_IsROrC [IsROrC K] : StarDotProductSpace n K where
  dotProduct_star_self_eq_zero := by
    intro v
    rw [dotProduct, IsROrC.ext_iff, IsROrC.ext_iff, Function.funext_iff]
    simp_rw [zero_re', map_zero, Pi.star_apply, star_def, IsROrC.conj_mul, re_sum, im_sum,
      ofReal_re, ofReal_im, re_to_real, im_to_real, Finset.sum_const_zero, and_true, Pi.zero_apply]
    rw [Finset.sum_eq_zero_iff_of_nonneg]
    simp only [Finset.mem_univ, map_eq_zero, forall_true_left]
    simp only [Finset.mem_univ, forall_true_left, normSq_nonneg, implies_true]

end IsROrCFields


def instStarDotProduct_R : StarDotProductSpace n ℝ where
  dotProduct_star_self_eq_zero := by
    intro v
    rw [star_trivial, dotProduct, Finset.sum_eq_zero_iff_of_nonneg, Function.funext_iff]
    all_goals ( simp only [Finset.mem_univ, mul_eq_zero, or_self, forall_true_left, Pi.zero_apply,
      mul_self_nonneg, implies_true] )

open Complex
def instStarDotProduct_C : StarDotProductSpace n ℂ where
  dotProduct_star_self_eq_zero := by
    intro v
    simp_rw [dotProduct, Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.ext_iff, Complex.im_sum, zero_im, ofReal_im, Finset.sum_const_zero, and_true,
      zero_re, re_sum, ofReal_re]
    rw [Finset.sum_eq_zero_iff_of_nonneg]
    simp only [Finset.mem_univ, map_eq_zero, forall_true_left]
    refine ⟨Function.funext_iff.2, Function.funext_iff.1⟩
    simp only [Finset.mem_univ, forall_true_left, normSq_nonneg, implies_true]

def instQStar_def : Star ℚ where
  star := fun x => x

instance instQStar : Star ℚ := instQStar_def

instance instTrivialQStar : TrivialStar ℚ where
  star_trivial := by
    intro x;
    unfold star instQStar instQStar_def
    simp only [Rat.cast_eq_id, id_eq]

def instQStarRing_def : StarRing ℚ where
  star_mul := by
    intros r s
    unfold star InvolutiveStar.toStar
    simp only
    unfold instQStar instQStar_def
    simp only
    exact mul_comm _ _
  star_add := by
    intros r s
    unfold star InvolutiveStar.toStar
    simp only
    unfold instQStar instQStar_def
    simp only
  star_involutive := by
    intros x
    unfold star instQStar instQStar_def
    simp only [Rat.cast_eq_id, id_eq]

instance instQStarRing : StarRing ℚ := instQStarRing_def

def instStarDotProduct_Q : StarDotProductSpace n ℚ where
  dotProduct_star_self_eq_zero := by
    intro v
    rw [star_trivial, dotProduct, Finset.sum_eq_zero_iff_of_nonneg, Function.funext_iff]
    all_goals ( simp only [Finset.mem_univ, mul_eq_zero, or_self, forall_true_left, Pi.zero_apply,
      mul_self_nonneg, implies_true] )

variable {K : Type _}

def instStarDotProduct_starOrderedRing [Field K] [PartialOrder K] [StarOrderedRing K] :
    StarDotProductSpace n K where
  dotProduct_star_self_eq_zero := by
    intro v
    rw [dotProduct, Finset.sum_eq_zero_iff_of_nonneg, Function.funext_iff]
    simp only [Finset.mem_univ, Pi.star_apply, mul_eq_zero, star_eq_zero, or_self, forall_true_left,
      Pi.zero_apply]
    simp only [Finset.mem_univ, Pi.star_apply, forall_true_left, star_mul_self_nonneg, implies_true]

section RankLemmas
variable {m : Type _} [Fintype m]
variable {R : Type _} [Field R] [StarRing R] [StarDotProductSpace m R] [StarDotProductSpace n R]
open FiniteDimensional


theorem ker_mulVecLin_conjTranspose_mul_self' (A : Matrix m n R) :
    LinearMap.ker (Aᴴ ⬝ A).mulVecLin = LinearMap.ker (mulVecLin A) := by
  ext x
  simp only [LinearMap.mem_ker, mulVecLin_apply, ← mulVec_mulVec]
  constructor
  · intro h
    replace h := congr_arg (dotProduct (star x)) h
    haveI : NoZeroDivisors R := inferInstance
    rwa [dotProduct_mulVec, dotProduct_zero, vecMul_conjTranspose, star_star,
      StarDotProductSpace.dotProduct_star_self_eq_zero] at h
  · intro h
    rw [h, mulVec_zero]

@[simp]
theorem rank_conjTranspose_mul_self' (A : Matrix m n R) :
    (Aᴴ ⬝ A).rank = A.rank := by
  dsimp only [Matrix.rank]
  refine' add_left_injective (finrank R (LinearMap.ker (mulVecLin A))) _
  dsimp only
  trans finrank R { x // x ∈ LinearMap.range (mulVecLin (Aᴴ ⬝ A)) } +
    finrank R { x // x ∈ LinearMap.ker (mulVecLin (Aᴴ ⬝ A)) }
  · rw [ker_mulVecLin_conjTranspose_mul_self']
  · simp only [LinearMap.finrank_range_add_finrank_ker]

@[simp]
theorem rank_conjTranspose' (A : Matrix m n R) : Aᴴ.rank = A.rank :=
  le_antisymm
    (((rank_conjTranspose_mul_self' _).symm.trans_le <| rank_mul_le_left _ _).trans_eq <|
      congr_arg _ <| conjTranspose_conjTranspose _)
    ((rank_conjTranspose_mul_self' _).symm.trans_le <| rank_mul_le_left _ _)

@[simp]
theorem rank_self_mul_conjTranspose' (A : Matrix m n R) : (A ⬝ Aᴴ).rank = A.rank := by
  simpa only [rank_conjTranspose', conjTranspose_conjTranspose] using
    rank_conjTranspose_mul_self' Aᴴ

end RankLemmas
