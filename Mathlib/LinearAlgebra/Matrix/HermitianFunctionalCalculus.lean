/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jireh Loreaux
-/

import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Analysis.NormedSpace.Star.ContinuousFunctionalCalculus.Restrict
import Mathlib.Analysis.NormedSpace.Star.ContinuousFunctionalCalculus
import Mathlib.Analysis.NormedSpace.Star.Spectrum
import Mathlib.Topology.ContinuousFunction.UniqueCFC
/-
This file defines an instance of the continuous functional calculus for Hermitian matrices over an
RCLike field 𝕜.

## Tags

spectral theorem, diagonalization theorem, continuous functional calculus
-/

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

open scoped BigOperators
namespace IsHermitian
section DecidableEq

variable [DecidableEq n]

variable {A : Matrix n n 𝕜} (hA : IsHermitian A)

/-To do:

1) Somehow make this natural map defined in terms of the diagonal into a *-alg hom,
so I have to learn how to specify all of this data.

2) Use the resulting * algebra hom as the φ in the instance of the CFC.

-/

alias ⟨_root_.Module.End.HasEigenvalue.mem_spectrum,
       _root_.Module.End.HasEigenvalue.of_mem_spectrum⟩ := Module.End.hasEigenvalue_iff_mem_spectrum

theorem eigenvalue_mem_toEuclideanLin_spectrum_RCLike (i : n) :
    (RCLike.ofReal ∘ hA.eigenvalues) i ∈ spectrum 𝕜 (toEuclideanLin A) :=
  LinearMap.IsSymmetric.hasEigenvalue_eigenvalues _ _ _ |>.mem_spectrum

theorem eigenvalue_mem_toEuclideanLin_spectrum_real (i : n) :
    hA.eigenvalues i ∈ spectrum ℝ (toEuclideanLin A) :=
(spectrum.algebraMap_mem_iff (S := 𝕜) (r := hA.eigenvalues i)).mp
        (eigenvalue_mem_toEuclideanLin_spectrum_RCLike _ i)

--Now I need to get φ below to be a map from C(spectrum ℝ A, ℝ) into Matrix n n 𝕜.

def φ : StarAlgHom ℝ C(spectrum ℝ A, ℝ) (Matrix n n 𝕜) where
  toFun := fun f => (eigenvectorUnitary hA : Matrix n n 𝕜) *
  diagonal (RCLike.ofReal (K := 𝕜) ∘ f.1 ∘ hA.eigenvalues)
      * star (eigenvectorUnitary hA : Matrix n n 𝕜)
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry
  commutes' := sorry
  map_star' := fun
    | .mk toFun continuous_toFun => sorry



instance instContinuousFunctionalCalculus :
    ContinuousFunctionalCalculus 𝕜 (IsHermitian : Matrix n n 𝕜 → Prop) where
exists_cfc_of_predicate

sorry

-/

--
