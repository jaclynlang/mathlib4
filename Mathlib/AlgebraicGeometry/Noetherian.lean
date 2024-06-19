/-
Copyright (c) 2024 Geno Racklin Asher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Geno Racklin Asher.
-/
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Noetherian
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.Topology.NoetherianSpace

/-!
# Noetherian and Locally Noetherian Schemes

We introduce the concept of (locally) Noetherian schemes,
giving definitions, equivalent conditions, and basic properties.

## Main definitions

* `AlgebraicGeometry.IsLocallyNoetherian`: a scheme is locally Noetherian
  if the components of the structure sheaf at each affine open are Noetherian rings.

* `AlgebraicGeometry.IsNoetherian`: a scheme is Noetherian if it is locally Noetherian
  and compact as a topological space.

## Main results

* `AlgebraicGeometry.isLocallyNoetherian_iff_affine_cover`: a scheme is locally Noetherian
  if and only if it is covered by affine opens whose sections are Noetherian rings.

* `AlgebraicGeometry.IsLocallyNoetherian.quasiSeparated`: a locally Noetherian scheme is
  quasi-separated.

* `AlgebraicGeometry.isNoetherian_iff_finite_affine_cover`: a scheme is Noetherian
  if and only if it is covered by finitely many affine opens whose sections are Noetherian rings.

* `AlgebraicGeometry.IsNoetherian.noetherianSpace`: a Noetherian scheme is
  topologically a Noetherian space.

## References

* [Stacks: Noetherian Schemes](https://stacks.math.columbia.edu/tag/01OU)
* [Robin Hartshorne, *Algebraic Geometry*][Har77]

-/

universe u

open Opposite AlgebraicGeometry Localization IsLocalization TopologicalSpace

namespace AlgebraicGeometry

/-- A scheme `X` is locally noetherian if `𝒪ₓ(U)` is noetherian for all affine `U`. -/
class IsLocallyNoetherian (X : Scheme) : Prop where
  component_noetherian : ∀ (U: X.affineOpens), IsNoetherianRing (X.presheaf.obj (op U)) :=
    by infer_instance

section localizationProps

variable {R : Type u} [CommRing R] (S : Finset R) (hS: Ideal.span (α := R) S = ⊤)
  (hN: ∀ s : S, IsNoetherianRing (Away (M := R) s))

lemma ideal_eq_iInf_away (I : Ideal R) :
    I = ⨅ f ∈ S, (I.map (algebraMap R (Away f))).comap (algebraMap R (Away f)) := by
  apply le_antisymm
  · simp only [le_iInf₂_iff, ← Ideal.map_le_iff_le_comap, le_refl, implies_true]
  . intro x hx
    apply Submodule.mem_of_span_eq_top_of_smul_pow_mem _ _ hS
    rintro ⟨s, hs⟩
    simp only [Ideal.mem_iInf, Ideal.mem_comap] at hx
    obtain ⟨⟨y, ⟨_, n, rfl⟩⟩, e⟩ :=
      (IsLocalization.mem_map_algebraMap_iff (.powers s) _).mp (hx s hs)
    dsimp only at e
    rw [← map_mul, IsLocalization.eq_iff_exists (.powers s)] at e
    obtain ⟨⟨_, m, rfl⟩, e⟩ := e
    use m + n
    dsimp at e ⊢
    rw [pow_add, mul_assoc, ← mul_comm x, e]
    exact I.mul_mem_left _ y.2

lemma biInf_eq_iInf_comap_map_away (I : Ideal R): ⨅ f ∈ S, (I.map (algebraMap R (Away f))).comap (algebraMap R (Away f)) =
 ⨅ f : S, (I.map (algebraMap R (Away (M := R) f))).comap (algebraMap R (Away (M := R) f)) := by
  rw [Subtype.forall] at hN
  ext
  simp only [Ideal.mem_iInf, Ideal.mem_comap, Subtype.forall]

/-- Let `R` be a ring, and `f i` a finite collection of elements of `R` generating the unit ideal.
If the localization of `R` at each `f i` is noetherian, so is `R`.

We follow the proof given in [Har77], Proposition II.3.2 -/
theorem noetherianRing_of_away : IsNoetherianRing R := by
  apply Iff.mp
  apply monotone_stabilizes_iff_noetherian
  intro I
  let floc s := algebraMap R (Away (M := R) s)
  let suitableN s := { n : ℕ | ∀ m : ℕ, n ≤ m → (Ideal.map (floc s) (I n)) = (Ideal.map (floc s) (I m)) }
  let minN s := sInf (suitableN s)
  have hSuit : ∀ s : S, minN s ∈ suitableN s := by
    intro s
    apply Nat.sInf_mem
    let f : ℕ →o Ideal (Away (M := R) s) := ⟨
      fun n => Ideal.map (floc s) (I n),
      by
        intro n m hnm
        dsimp
        apply Ideal.map_mono
        exact I.monotone hnm
    ⟩
    exact monotone_stabilizes_iff_noetherian.mpr (hN s) f
  let N := Finset.sup S minN
  use N
  have hN : ∀ s : S, minN s ≤ N := fun s => Finset.le_sup s.prop
  intro n hn
  rw [ideal_eq_iInf_away S _ (I N), ideal_eq_iInf_away S _ (I n),
      biInf_eq_iInf_comap_map_away, biInf_eq_iInf_comap_map_away]
  apply iInf_congr
  intro s
  congr 1
  rw [←hSuit s N (hN s)]
  exact hSuit s n <| Nat.le_trans (hN s) hn
  assumption'

end localizationProps

variable {X : Scheme}

/-- If a scheme `X` has a cover by affine opens whose sections are noetherian rings,
then `X` is locally noetherian. -/
theorem isLocallyNoetherian_of_affine_cover (S : Set X.affineOpens)
    (hS : (⋃ i : S, i : Set X) = Set.univ)
    (hS' : ∀ (U : S), IsNoetherianRing (X.presheaf.obj (op U))) : IsLocallyNoetherian X := by
  refine ⟨fun U => ?_⟩
  apply of_affine_open_cover (P := _) U S _ _ hS hS'
  . intro U f hN
    let R := X.presheaf.obj (op U)
    let Rf := Localization.Away f
    have hh : IsLocalization _ Rf := isLocalization
    have : IsNoetherianRing Rf := by
      apply @IsLocalization.isNoetherianRing R _ _ Rf _ algebra hh
      assumption
    let Rf' := X.presheaf.obj (op (X.basicOpen f))
    have hAff := IsAffineOpen.isLocalization_basicOpen U.prop f
    have := @IsLocalization.algEquiv R _ _ Rf _ _ hh Rf' _ _ hAff
    apply isNoetherianRing_of_ringEquiv Rf
    exact this.toRingEquiv
  . intro U s _ hN
    let R := X.presheaf.obj (op U)
    have : ∀ f : s, IsNoetherianRing (Away (M := R) f) := by
      intro ⟨f, hf⟩
      have : IsNoetherianRing (X.presheaf.obj (op (X.basicOpen f))) := hN ⟨f, hf⟩
      apply isNoetherianRing_of_ringEquiv (X.presheaf.obj (op (X.basicOpen f)))
      let Rf := Localization.Away f
      have hh : IsLocalization _ Rf := isLocalization
      let Rf' := X.presheaf.obj (op (X.basicOpen f))
      have hAff := IsAffineOpen.isLocalization_basicOpen U.prop f
      have := @IsLocalization.algEquiv R _ _ Rf _ _ hh Rf' _ _ hAff
      exact this.symm.toRingEquiv
    apply noetherianRing_of_away
    assumption'

lemma cover_of_affineOpens : ⋃ i : {_U : X.affineOpens | True}, (i : Set X) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  apply Iff.mpr
  apply Set.mem_iUnion
  let topX : TopologicalSpace.Opens X := ⊤
  have hx : x ∈ topX := trivial
  obtain ⟨U, hU, hxU, _⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    (AlgebraicGeometry.isBasis_affine_open X) hx
  let U : X.affineOpens := ⟨U, hU⟩
  use ⟨U, trivial⟩
  exact hxU

/-- A scheme is locally noetherian if and only if it is covered by affine opens whose sections
are noetherian rings.

See [Har77], Proposition II.3.2. -/
theorem isLocallyNoetherian_iff_affine_cover :
  IsLocallyNoetherian X ↔
  ∃ (S : Set X.affineOpens), (⋃ i : S, i : Set X) = Set.univ ∧
  ∀ (U : S), IsNoetherianRing (X.presheaf.obj (op U)) :=
  ⟨fun h => by
    let S := {_U : X.affineOpens | True}
    have hS : (⋃ i : S, i : Set X) = Set.univ := cover_of_affineOpens
    have hS' : ∀ (U : S), IsNoetherianRing (X.presheaf.obj (op U)) :=
      fun U => h.component_noetherian U
    exact ⟨S, hS, hS'⟩,
  fun ⟨S, hS, hS'⟩ => isLocallyNoetherian_of_affine_cover S hS hS'⟩

/-- If `R` is a noetherian ring, `Spec R` is a noetherian topological space. -/
instance {R : CommRingCat} [IsNoetherianRing R] :
  NoetherianSpace (Scheme.Spec.obj <| op R) := by
  convert PrimeSpectrum.instNoetherianSpace (R := R)
