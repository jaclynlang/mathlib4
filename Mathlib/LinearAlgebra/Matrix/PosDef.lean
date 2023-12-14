/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Mohanad Ahmed
-/
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.QuadraticForm.Basic

#align_import linear_algebra.matrix.pos_def from "leanprover-community/mathlib"@"07992a1d1f7a4176c6d3f160209608be4e198566"

/-! # Positive Definite Matrices

This file defines positive (semi)definite matrices and connects the notion to positive definiteness
of quadratic forms. Most results require `𝕜 = ℝ` or `ℂ`.

## Main definitions

* `Matrix.PosDef` : a matrix `M : Matrix n n 𝕜` is positive definite if it is hermitian and `xᴴMx`
  is greater than zero for all nonzero `x`.
* `Matrix.PosSemidef` : a matrix `M : Matrix n n 𝕜` is positive semidefinite if it is hermitian
  and `xᴴMx` is nonnegative for all `x`.

## Main results

* `Matrix.posSemidef_iff_eq_transpose_mul_self` : a matrix `M : Matrix n n 𝕜` is positive
  semidefinite iff it has the form `Bᴴ B` for some `B`.
* `Matrix.PosSemidef.sqrt` : the unique positive semidefinite square root of a positive semidefinite
  matrix. (See `Matrix.PosSemidef.eq_sqrt_of_sq_eq` for the proof of uniqueness.)
-/

open scoped ComplexOrder

namespace Matrix

variable {m n R 𝕜 : Type*}
variable [Fintype m] [Fintype n]
variable [CommRing R] [PartialOrder R] [StarOrderedRing R]
variable [IsROrC 𝕜]
open scoped Matrix

/-!
## Positive semidefinite matrices
-/

/-- A matrix `M : Matrix n n R` is positive semidefinite if it is hermitian
   and `xᴴ M x` is nonnegative for all `x`. -/
def PosSemidef (M : Matrix n n R) :=
  M.IsHermitian ∧ ∀ x : n → R, 0 ≤ dotProduct (star x) (M.mulVec x)
#align matrix.pos_semidef Matrix.PosSemidef

/-- A diagonal matrix is positive semidefinite iff its diagonal entries are nonnegative. -/
lemma posSemidef_diagonal_iff_nonneg [DecidableEq n] {d : n → R} :
    PosSemidef (diagonal d) ↔ (∀ i : n, 0 ≤ d i) := by
  constructor
  · intro ⟨_, hP⟩ i
    simpa using hP (Pi.single i 1)
  · intro hd
    constructor
    · rw [IsHermitian, conjTranspose, diagonal_transpose, diagonal_map (star_zero R)]
      exact congr_arg _ (funext fun i ↦ star_eq_self_of_nonneg (hd i))
    · intro x
      rw [dotProduct]
      refine Finset.sum_nonneg fun i _ ↦ ?_
      simpa only [mulVec_diagonal, ← mul_assoc] using conjugate_nonneg (hd i) _

namespace PosSemidef

theorem isHermitian {M : Matrix n n R} (hM : M.PosSemidef) : M.IsHermitian :=
  hM.1

theorem re_dotProduct_nonneg {M : Matrix n n 𝕜} (hM : M.PosSemidef) (x : n → 𝕜) :
    0 ≤ IsROrC.re (dotProduct (star x) (M.mulVec x)) :=
  IsROrC.nonneg_iff.mp (hM.2 _) |>.1

lemma conjTranspose_mul_mul_same {A : Matrix n n R} (hA : PosSemidef A)
    {m : Type*} [Fintype m] (B : Matrix n m R) :
    PosSemidef (Bᴴ * A * B) := by
  constructor
  · rw [IsHermitian, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      Matrix.mul_assoc, hA.1]
  · intro x
    simpa only [star_mulVec, dotProduct_mulVec, vecMul_vecMul] using hA.2 (mulVec B x)

lemma mul_mul_conjTranspose_same {A : Matrix n n R} (hA : PosSemidef A)
    {m : Type*} [Fintype m] (B : Matrix m n R):
    PosSemidef (B * A * Bᴴ) := by
  simpa only [conjTranspose_conjTranspose] using hA.conjTranspose_mul_mul_same Bᴴ

theorem submatrix {M : Matrix n n R} (hM : M.PosSemidef) (e : m → n) [DecidableEq n] :
    (M.submatrix e e).PosSemidef := by
  rw [(by simp : M = 1 * M * 1), submatrix_mul (e₂ := id) (he₂ := Function.bijective_id),
    submatrix_mul (e₂ := id) (he₂ := Function.bijective_id), submatrix_id_id]
  simpa only [conjTranspose_submatrix, conjTranspose_one] using
    conjTranspose_mul_mul_same hM (Matrix.submatrix 1 id e)
#align matrix.pos_semidef.submatrix Matrix.PosSemidef.submatrix

/-- The eigenvalues of a positive semi-definite matrix are non-negative -/
lemma eigenvalues_nonneg [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : Matrix.PosSemidef A) (i : n) : 0 ≤ hA.1.eigenvalues i :=
  (hA.re_dotProduct_nonneg _).trans_eq (hA.1.eigenvalues_eq _).symm

theorem transpose {M : Matrix n n R} (hM : M.PosSemidef) : Mᵀ.PosSemidef := by
  refine ⟨IsHermitian.transpose hM.1, fun x => ?_⟩
  convert hM.2 (star x) using 1
  rw [mulVec_transpose, Matrix.dotProduct_mulVec, star_star, dotProduct_comm]

section sqrt

variable [DecidableEq n] {A : Matrix n n 𝕜} (hA : PosSemidef A)

/-- The positive semidefinite square root of a positive semidefinite matrix -/
@[pp_dot]
noncomputable def sqrt : Matrix n n 𝕜 :=
  hA.1.eigenvectorMatrix * diagonal ((↑) ∘ Real.sqrt ∘ hA.1.eigenvalues) * hA.1.eigenvectorMatrixᴴ

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Custom elaborator to produce output like `(_ : PosSemidef A).sqrt` in the goal view. -/
@[delab app.Matrix.PosSemidef.sqrt]
def delabSqrt : Delab :=
  whenPPOption getPPNotation <|
  whenNotPPOption getPPAnalysisSkip <|
  withOptionAtCurrPos `pp.analysis.skip true do
    let e ← getExpr
    guard <| e.isAppOfArity ``Matrix.PosSemidef.sqrt 7
    let optionsPerPos ← withNaryArg 6 do
      return (← read).optionsPerPos.setBool (← getPos) `pp.proofs.withType true
    withTheReader Context ({· with optionsPerPos}) delab

-- test for custom elaborator
/--
info: (_ : PosSemidef A).sqrt : Matrix n n 𝕜
-/
#guard_msgs in
#check (id hA).sqrt

lemma posSemidef_sqrt : PosSemidef hA.sqrt := by
  apply PosSemidef.mul_mul_conjTranspose_same
  refine posSemidef_diagonal_iff_nonneg.mpr fun i ↦ ?_
  rw [Function.comp_apply, IsROrC.nonneg_iff]
  constructor
  · simp only [IsROrC.ofReal_re]
    exact Real.sqrt_nonneg _
  · simp only [IsROrC.ofReal_im]

@[simp]
lemma sq_sqrt : hA.sqrt ^ 2 = A := by
  let C := hA.1.eigenvectorMatrix
  let E := diagonal ((↑) ∘ Real.sqrt ∘ hA.1.eigenvalues : n → 𝕜)
  suffices : C * (E * (Cᴴ * C) * E) * Cᴴ = A
  · rw [Matrix.PosSemidef.sqrt, pow_two]
    change (C * E * Cᴴ) * (C * E * Cᴴ) = A
    simpa only [← mul_assoc] using this
  have : Cᴴ * C = 1
  · rw [Matrix.IsHermitian.conjTranspose_eigenvectorMatrix, mul_eq_one_comm]
    exact hA.1.eigenvectorMatrix_mul_inv
  rw [this, mul_one]
  have : E * E = diagonal ((↑) ∘ hA.1.eigenvalues)
  · rw [diagonal_mul_diagonal]
    refine congr_arg _ (funext fun v ↦ ?_) -- why doesn't "congr with v" work?
    simp [← pow_two, ← IsROrC.ofReal_pow, Real.sq_sqrt (hA.eigenvalues_nonneg v)]
  rw [this]
  convert hA.1.spectral_theorem'.symm
  apply Matrix.IsHermitian.conjTranspose_eigenvectorMatrix

@[simp]
lemma sqrt_mul_self : hA.sqrt * hA.sqrt = A := by rw [← pow_two, sq_sqrt]

lemma eq_of_sq_eq_sq {B : Matrix n n 𝕜} (hB : PosSemidef B) (hAB : A ^ 2 = B ^ 2) : A = B := by
  /- This is deceptively hard, much more difficult than the positive *definite* case. We follow a
  clever proof due to Koeber and Schäfer. The idea is that if `A ≠ B`, then `A - B` has a nonzero
  real eigenvalue, with eigenvector `v`. Then a manipulation using the identity
  `A ^ 2 - B ^ 2 = A * (A - B) + (A - B) * B` leads to the conclusion that
  `⟨v, A v⟩ + ⟨v, B v⟩ = 0`. Since `A, B` are positive semidefinite, both terms must be zero. Thus
  `⟨v, (A - B) v⟩ = 0`, but this is a nonzero scalar multiple of `⟨v, v⟩`, contradiction. -/
  by_contra h_ne
  let ⟨v, t, ht, hv, hv'⟩ := (hA.1.sub hB.1).exists_eigenvector_of_ne_zero (sub_ne_zero.mpr h_ne)
  have h_sum : 0 = t * (star v ⬝ᵥ mulVec A v + star v ⬝ᵥ mulVec B v)
  · calc
      0 = star v ⬝ᵥ mulVec (A ^ 2 - B ^ 2) v := by rw [hAB, sub_self, zero_mulVec, dotProduct_zero]
      _ = star v ⬝ᵥ mulVec A (mulVec (A - B) v)  + star v ⬝ᵥ mulVec (A - B) (mulVec B v) := by
        rw [mulVec_mulVec, mulVec_mulVec, ← dotProduct_add, ← add_mulVec, mul_sub, sub_mul,
          add_sub, sub_add_cancel, pow_two, pow_two]
      _ = t * (star v ⬝ᵥ mulVec A v) + vecMul (star v) (A - B)ᴴ ⬝ᵥ mulVec B v := by
        rw [hv', mulVec_smul, dotProduct_smul, IsROrC.real_smul_eq_coe_mul,
          dotProduct_mulVec _ (A - B), hA.1.sub hB.1]
      _ = t * (star v ⬝ᵥ mulVec A v + star v ⬝ᵥ mulVec B v) := by
        simp_rw [← star_mulVec, hv', mul_add, ← IsROrC.real_smul_eq_coe_mul, ← smul_dotProduct]
        congr 2 with i
        simp only [Pi.star_apply, Pi.smul_apply, IsROrC.real_smul_eq_coe_mul, star_mul',
          IsROrC.star_def, IsROrC.conj_ofReal]
  replace h_sum : star v ⬝ᵥ mulVec A v + star v ⬝ᵥ mulVec B v = 0
  · rw [eq_comm, ← mul_zero (t : 𝕜)] at h_sum
    exact mul_left_cancel₀ (IsROrC.ofReal_ne_zero.mpr ht) h_sum
  have h_van : star v ⬝ᵥ mulVec A v = 0 ∧ star v ⬝ᵥ mulVec B v = 0
  · refine ⟨le_antisymm ?_ (hA.2 v), le_antisymm ?_ (hB.2 v)⟩
    · rw [add_comm, add_eq_zero_iff_eq_neg] at h_sum
      simpa only [h_sum, neg_nonneg] using hB.2 v
    · simpa only [add_eq_zero_iff_eq_neg.mp h_sum, neg_nonneg] using hA.2 v
  have aux : star v ⬝ᵥ mulVec (A - B) v = 0
  · rw [sub_mulVec, dotProduct_sub, h_van.1, h_van.2, sub_zero]
  rw [hv', dotProduct_smul, IsROrC.real_smul_eq_coe_mul, ← mul_zero ↑t] at aux
  exact hv <| Matrix.dotProduct_star_self_eq_zero.mp <| mul_left_cancel₀
    (IsROrC.ofReal_ne_zero.mpr ht) aux

lemma eq_sqrt_of_sq_eq {B : Matrix n n 𝕜} (hB : PosSemidef B) (hAB : A ^ 2 = B) : A = hB.sqrt :=
  hA.eq_of_sq_eq_sq hB.posSemidef_sqrt (hB.sq_sqrt.symm ▸ hAB)

end sqrt

end PosSemidef

@[simp]
theorem posSemidef_submatrix_equiv {M : Matrix n n R} (e : m ≃ n) [DecidableEq m] [DecidableEq n] :
    (M.submatrix e e).PosSemidef ↔ M.PosSemidef :=
  ⟨fun h => by simpa using h.submatrix e.symm, fun h => h.submatrix _⟩
#align matrix.pos_semidef_submatrix_equiv Matrix.posSemidef_submatrix_equiv

/-- The conjugate transpose of a matrix mulitplied by the matrix is positive semidefinite -/
theorem posSemidef_conjTranspose_mul_self (A : Matrix m n R) : PosSemidef (Aᴴ * A) := by
  refine ⟨isHermitian_transpose_mul_self _, fun x => ?_⟩
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose, star_star]
  exact Finset.sum_nonneg fun i _ => star_mul_self_nonneg _

/-- A matrix multiplied by its conjugate transpose is positive semidefinite -/
theorem posSemidef_self_mul_conjTranspose (A : Matrix m n R) : PosSemidef (A * Aᴴ) :=
  by simpa only [conjTranspose_conjTranspose] using posSemidef_conjTranspose_mul_self Aᴴ

lemma eigenvalues_conjTranspose_mul_self_nonneg (A : Matrix m n 𝕜) [DecidableEq n] (i : n) :
    0 ≤ (isHermitian_transpose_mul_self A).eigenvalues i :=
  (posSemidef_conjTranspose_mul_self _).eigenvalues_nonneg _

lemma eigenvalues_self_mul_conjTranspose_nonneg (A : Matrix m n 𝕜) [DecidableEq m] (i : m) :
    0 ≤ (isHermitian_mul_conjTranspose_self A).eigenvalues i :=
  (posSemidef_self_mul_conjTranspose _).eigenvalues_nonneg _

/-- A matrix is positive semidefinite if and only if it has the form `Bᴴ * B` for some `B`. -/
lemma posSemidef_iff_eq_transpose_mul_self [DecidableEq n] {A : Matrix n n 𝕜} :
    PosSemidef A ↔ ∃ (B : Matrix n n 𝕜), A = Bᴴ * B := by
  refine ⟨fun hA ↦ ⟨hA.sqrt, ?_⟩, fun ⟨B, hB⟩ ↦ (hB ▸ posSemidef_conjTranspose_mul_self B)⟩
  simp_rw [← PosSemidef.sq_sqrt hA, pow_two]
  rw [hA.posSemidef_sqrt.1]

/-- For `A` positive semidefinite, we have `x⋆ A x = 0` iff `A x = 0`. -/
theorem PosSemidef.dotProduct_mulVec_zero_iff [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : PosSemidef A) (x : n → 𝕜) :
    star x ⬝ᵥ mulVec A x = 0 ↔ mulVec A x = 0 := by
  constructor
  · obtain ⟨B, rfl⟩ := posSemidef_iff_eq_transpose_mul_self.mp hA
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec,
      vecMul_conjTranspose, star_star, dotProduct_star_self_eq_zero]
    intro h0
    rw [h0, mulVec_zero]
  · intro h0
    rw [h0, dotProduct_zero]

/-- For `A` positive semidefinite, we have `x⋆ A x = 0` iff `A x = 0` (linear maps version). -/
theorem PosSemidef.toLinearMap₂'_zero_iff [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : PosSemidef A) (x : n → 𝕜) :
    Matrix.toLinearMap₂' A (star x) x = 0 ↔ Matrix.toLin' A x = 0 := by
  simpa only [toLinearMap₂'_apply', toLin'_apply] using hA.dotProduct_mulVec_zero_iff x

/-!
## Positive definite matrices
-/

/-- A matrix `M : Matrix n n R` is positive definite if it is hermitian
   and `xᴴMx` is greater than zero for all nonzero `x`. -/
def PosDef (M : Matrix n n R) :=
  M.IsHermitian ∧ ∀ x : n → R, x ≠ 0 → 0 < dotProduct (star x) (M.mulVec x)
#align matrix.pos_def Matrix.PosDef

namespace PosDef

theorem isHermitian {M : Matrix n n R} (hM : M.PosDef) : M.IsHermitian :=
  hM.1
#align matrix.pos_def.is_hermitian Matrix.PosDef.isHermitian

theorem re_dotProduct_pos {M : Matrix n n 𝕜} (hM : M.PosDef) {x : n → 𝕜} (hx : x ≠ 0) :
    0 < IsROrC.re (dotProduct (star x) (M.mulVec x)) :=
  IsROrC.pos_iff.mp (hM.2 _ hx) |>.1

theorem posSemidef {M : Matrix n n R} (hM : M.PosDef) : M.PosSemidef := by
  refine' ⟨hM.1, _⟩
  intro x
  by_cases hx : x = 0
  · simp only [hx, zero_dotProduct, star_zero, IsROrC.zero_re']
    exact le_rfl
  · exact le_of_lt (hM.2 x hx)
#align matrix.pos_def.pos_semidef Matrix.PosDef.posSemidef

theorem transpose {M : Matrix n n R} (hM : M.PosDef) : Mᵀ.PosDef := by
  refine ⟨IsHermitian.transpose hM.1, fun x hx => ?_⟩
  convert hM.2 (star x) (star_ne_zero.2 hx) using 1
  rw [mulVec_transpose, Matrix.dotProduct_mulVec, star_star, dotProduct_comm]
#align matrix.pos_def.transpose Matrix.PosDef.transpose

theorem of_toQuadraticForm' [DecidableEq n] {M : Matrix n n ℝ} (hM : M.IsSymm)
    (hMq : M.toQuadraticForm'.PosDef) : M.PosDef := by
  refine' ⟨hM, fun x hx => _⟩
  simp only [toQuadraticForm', QuadraticForm.PosDef, BilinForm.toQuadraticForm_apply,
    Matrix.toBilin'_apply'] at hMq
  apply hMq x hx
#align matrix.pos_def_of_to_quadratic_form' Matrix.PosDef.of_toQuadraticForm'

theorem toQuadraticForm' [DecidableEq n] {M : Matrix n n ℝ} (hM : M.PosDef) :
    M.toQuadraticForm'.PosDef := by
  intro x hx
  simp only [Matrix.toQuadraticForm', BilinForm.toQuadraticForm_apply, Matrix.toBilin'_apply']
  apply hM.2 x hx
#align matrix.pos_def_to_quadratic_form' Matrix.PosDef.toQuadraticForm'

/-- The eigenvalues of a positive definite matrix are positive -/
lemma eigenvalues_pos [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : Matrix.PosDef A) (i : n) : 0 < hA.1.eigenvalues i := by
  rw [hA.1.eigenvalues_eq, hA.1.transpose_eigenvectorMatrix_apply]
  exact hA.re_dotProduct_pos <| hA.1.eigenvectorBasis.orthonormal.ne_zero i

theorem det_pos [DecidableEq n] {M : Matrix n n ℝ} (hM : M.PosDef) : 0 < det M := by
  rw [hM.isHermitian.det_eq_prod_eigenvalues]
  apply Finset.prod_pos
  intro i _
  rw [hM.isHermitian.eigenvalues_eq]
  refine hM.2 _ fun h => ?_
  have h_det : hM.isHermitian.eigenvectorMatrixᵀ.det = 0 :=
    Matrix.det_eq_zero_of_row_eq_zero i fun j => congr_fun h j
  simpa only [h_det, not_isUnit_zero] using
    isUnit_det_of_invertible hM.isHermitian.eigenvectorMatrixᵀ
#align matrix.pos_def.det_pos Matrix.PosDef.det_pos

end PosDef

end Matrix

namespace QuadraticForm

variable {n : Type*} [Fintype n]

theorem posDef_of_toMatrix' [DecidableEq n] {Q : QuadraticForm ℝ (n → ℝ)}
    (hQ : Q.toMatrix'.PosDef) : Q.PosDef := by
  rw [← toQuadraticForm_associated ℝ Q,
    ← BilinForm.toMatrix'.left_inv ((associatedHom (R := ℝ) ℝ) Q)]
  exact hQ.toQuadraticForm'
#align quadratic_form.pos_def_of_to_matrix' QuadraticForm.posDef_of_toMatrix'

theorem posDef_toMatrix' [DecidableEq n] {Q : QuadraticForm ℝ (n → ℝ)} (hQ : Q.PosDef) :
    Q.toMatrix'.PosDef := by
  rw [← toQuadraticForm_associated ℝ Q, ←
    BilinForm.toMatrix'.left_inv ((associatedHom (R := ℝ) ℝ) Q)] at hQ
  exact .of_toQuadraticForm' (isSymm_toMatrix' Q) hQ
#align quadratic_form.pos_def_to_matrix' QuadraticForm.posDef_toMatrix'

end QuadraticForm

namespace Matrix

variable {𝕜 : Type*} [IsROrC 𝕜] {n : Type*} [Fintype n]

/-- A positive definite matrix `M` induces a norm `‖x‖ = sqrt (re xᴴMx)`. -/
@[reducible]
noncomputable def NormedAddCommGroup.ofMatrix {M : Matrix n n 𝕜} (hM : M.PosDef) :
    NormedAddCommGroup (n → 𝕜) :=
  @InnerProductSpace.Core.toNormedAddCommGroup _ _ _ _ _
    { inner := fun x y => dotProduct (star x) (M.mulVec y)
      conj_symm := fun x y => by
        dsimp only [Inner.inner]
        rw [star_dotProduct, starRingEnd_apply, star_star, star_mulVec, dotProduct_mulVec,
          hM.isHermitian.eq]
      nonneg_re := fun x => by
        by_cases h : x = 0
        · simp [h]
        · exact le_of_lt (hM.re_dotProduct_pos h)
      definite := fun x (hx : dotProduct _ _ = 0) => by
        by_contra! h
        simpa [hx, lt_irrefl] using hM.re_dotProduct_pos h
      add_left := by simp only [star_add, add_dotProduct, eq_self_iff_true, forall_const]
      smul_left := fun x y r => by
        simp only
        rw [← smul_eq_mul, ← smul_dotProduct, starRingEnd_apply, ← star_smul] }
#align matrix.normed_add_comm_group.of_matrix Matrix.NormedAddCommGroup.ofMatrix

/-- A positive definite matrix `M` induces an inner product `⟪x, y⟫ = xᴴMy`. -/
def InnerProductSpace.ofMatrix {M : Matrix n n 𝕜} (hM : M.PosDef) :
    @InnerProductSpace 𝕜 (n → 𝕜) _ (NormedAddCommGroup.ofMatrix hM) :=
  InnerProductSpace.ofCore _
#align matrix.inner_product_space.of_matrix Matrix.InnerProductSpace.ofMatrix

end Matrix
