/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Complex.Module
import Mathlib.RingTheory.Polynomial.Chebyshev

#align_import analysis.special_functions.trigonometric.chebyshev from "leanprover-community/mathlib"@"2c1d8ca2812b64f88992a5294ea3dba144755cd1"

/-!
# Multiple angle formulas in terms of Chebyshev polynomials

This file gives the trigonometric characterizations of Chebyshev polynomials, for both the real
(`Real.cos`) and complex (`Complex.cos`) cosine.
-/

set_option linter.uppercaseLean3 false

namespace Polynomial.Chebyshev

open Polynomial

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

@[simp]
theorem aeval_T (x : A) (n : ℤ) : aeval x (T R n) = (T A n).eval x := by
  rw [aeval_def, eval₂_eq_eval_map, map_T]
#align polynomial.chebyshev.aeval_T Polynomial.Chebyshev.aeval_T

@[simp]
theorem aeval_U (x : A) (n : ℤ) : aeval x (U R n) = (U A n).eval x := by
  rw [aeval_def, eval₂_eq_eval_map, map_U]
#align polynomial.chebyshev.aeval_U Polynomial.Chebyshev.aeval_U

@[simp]
theorem algebraMap_eval_T (x : R) (n : ℤ) :
    algebraMap R A ((T R n).eval x) = (T A n).eval (algebraMap R A x) := by
  rw [← aeval_algebraMap_apply_eq_algebraMap_eval, aeval_T]
#align polynomial.chebyshev.algebra_map_eval_T Polynomial.Chebyshev.algebraMap_eval_T

@[simp]
theorem algebraMap_eval_U (x : R) (n : ℤ) :
    algebraMap R A ((U R n).eval x) = (U A n).eval (algebraMap R A x) := by
  rw [← aeval_algebraMap_apply_eq_algebraMap_eval, aeval_U]
#align polynomial.chebyshev.algebra_map_eval_U Polynomial.Chebyshev.algebraMap_eval_U

-- Porting note: added type ascriptions to the statement
@[simp, norm_cast]
theorem complex_ofReal_eval_T : ∀ (x : ℝ) n, (((T ℝ n).eval x : ℝ) : ℂ) = (T ℂ n).eval (x : ℂ) :=
  @algebraMap_eval_T ℝ ℂ _ _ _
#align polynomial.chebyshev.complex_of_real_eval_T Polynomial.Chebyshev.complex_ofReal_eval_T

-- Porting note: added type ascriptions to the statement
@[simp, norm_cast]
theorem complex_ofReal_eval_U : ∀ (x : ℝ) n, (((U ℝ n).eval x : ℝ) : ℂ) = (U ℂ n).eval (x : ℂ) :=
  @algebraMap_eval_U ℝ ℂ _ _ _
#align polynomial.chebyshev.complex_of_real_eval_U Polynomial.Chebyshev.complex_ofReal_eval_U

/-! ### Complex versions -/

section Complex

open Complex

variable (θ : ℂ)

/-- The `n`-th Chebyshev polynomial of the first kind evaluates on `cos θ` to the
value `cos (n * θ)`. -/
@[simp]
theorem T_complex_cos (n : ℤ) : (T ℂ n).eval (cos θ) = cos (n * θ) := by
  induction n using T.induct ℂ with
  | case1 => simp
  | case2 => simp
  | case3 n ih1 ih2 =>
    simp only [Nat.succ_eq_add_one, Int.ofNat_eq_coe, Nat.cast_add, Nat.cast_one, Int.cast_add,
      T_add_one ℂ (n + 1), add_sub_cancel_right, eval_sub, eval_mul,
      eval_X, eval_ofNat, ih1, ih2, sub_eq_iff_eq_add, cos_add_cos]
    ring_nf
  | case4 n ih1 ih2 =>
    simp only [Int.negSucc_eq, neg_add', T_sub_one ℂ (-n), add_sub_cancel_right, eval_sub, eval_mul,
      eval_X, eval_ofNat, ih1, ih2, sub_eq_iff_eq_add', cos_add_cos]
    push_cast
    ring_nf
#align polynomial.chebyshev.T_complex_cos Polynomial.Chebyshev.T_complex_cos

/-- The `n`-th Chebyshev polynomial of the second kind evaluates on `cos θ` to the
value `sin ((n + 1) * θ) / sin θ`. -/
@[simp]
theorem U_complex_cos (n : ℤ) : (U ℂ n).eval (cos θ) * sin θ = sin ((n + 1) * θ) := by
  induction n using U.induct ℂ with
  | case1 => simp
  | case2 => simp [one_add_one_eq_two, sin_two_mul]; ring
  | case3 n ih1 ih2 =>
    push_cast at ih1 ih2
    simp only [Nat.succ_eq_add_one, Int.ofNat_eq_coe, Nat.cast_add, Nat.cast_one, Int.cast_add,
      U_add_one ℂ (n + 1), add_sub_cancel_right, eval_sub, eval_mul, eval_X, eval_ofNat, sub_mul,
      mul_assoc, ih1, ih2, sub_eq_iff_eq_add, sin_add_sin]
    push_cast
    ring_nf
  | case4 n ih1 ih2 =>
    simp only [Int.negSucc_eq, neg_add', U_sub_one ℂ (-n), add_sub_cancel_right, eval_sub, eval_mul,
      eval_X, eval_ofNat, sub_mul, mul_assoc, ih1, ih2, sub_eq_iff_eq_add', sin_add_sin]
    push_cast
    ring_nf
#align polynomial.chebyshev.U_complex_cos Polynomial.Chebyshev.U_complex_cos

/-- The `n`-th rescaled Chebyshev polynomial of the first kind (Vieta–Lucas polynomial) evaluates on
`2 * cos θ` to the value `2 * cos (n * θ)`. -/
@[simp]
theorem C_two_mul_complex_cos (n : ℤ) : (C ℂ n).eval (2 * cos θ) = 2 * cos (n * θ) := by
  simp [C_eq_two_mul_T_comp_half_mul_X]

/-- The `n`-th rescaled Chebyshev polynomial of the second kind (Vieta–Fibonacci polynomial)
evaluates on `2 * cos θ` to the value `sin ((n + 1) * θ) / sin θ`. -/
@[simp]
theorem S_two_mul_complex_cos (n : ℤ) : (S ℂ n).eval (2 * cos θ) * sin θ = sin ((n + 1) * θ) := by
  simp [S_eq_U_comp_half_mul_X]

end Complex

/-! ### Real versions -/

section Real

open Real

variable (θ : ℝ) (n : ℤ)

/-- The `n`-th Chebyshev polynomial of the first kind evaluates on `cos θ` to the
value `cos (n * θ)`. -/
@[simp]
theorem T_real_cos : (T ℝ n).eval (cos θ) = cos (n * θ) := mod_cast T_complex_cos θ n
#align polynomial.chebyshev.T_real_cos Polynomial.Chebyshev.T_real_cos

/-- The `n`-th Chebyshev polynomial of the second kind evaluates on `cos θ` to the
value `sin ((n + 1) * θ) / sin θ`. -/
@[simp]
theorem U_real_cos : (U ℝ n).eval (cos θ) * sin θ = sin ((n + 1) * θ) :=
  mod_cast U_complex_cos θ n
#align polynomial.chebyshev.U_real_cos Polynomial.Chebyshev.U_real_cos

/-- The `n`-th rescaled Chebyshev polynomial of the first kind (Vieta–Lucas polynomial) evaluates on
`2 * cos θ` to the value `2 * cos (n * θ)`. -/
@[simp]
theorem C_two_mul_real_cos : (C ℝ n).eval (2 * cos θ) = 2 * cos (n * θ) := by
  simp [C_eq_two_mul_T_comp_half_mul_X]

/-- The `n`-th rescaled Chebyshev polynomial of the second kind (Vieta–Fibonacci polynomial)
evaluates on `2 * cos θ` to the value `sin ((n + 1) * θ) / sin θ`. -/
@[simp]
theorem S_two_mul_real_cos : (S ℝ n).eval (2 * cos θ) * sin θ = sin ((n + 1) * θ) := by
  simp [S_eq_U_comp_half_mul_X]

end Real

end Polynomial.Chebyshev
