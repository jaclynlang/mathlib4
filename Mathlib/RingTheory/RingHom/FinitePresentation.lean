/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.LocalProperties
import Mathlib.RingTheory.Localization.InvSubmonoid
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.Algebra.Module.LocalizedModule
import Mathlib.RingTheory.RingHom.FiniteType
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.MvPolynomial.Localization

/-!

# The meta properties of finitely-presented ring homomorphisms.

The main result is `RingHom.finitePresentation_is_local`.

-/

section

variable {R S P : Type*} (Q : Type*) [CommSemiring R] [CommSemiring S] [CommSemiring P]
  [CommSemiring Q]
  {M : Submonoid R} {T : Submonoid P}
  [Algebra R S] [Algebra P Q] [IsLocalization M S] [IsLocalization T Q]
  (g : R →+* P) (hy : M ≤ Submonoid.comap g T)

variable (S) in
def kerMap : RingHom.ker g →ₗ[R] RingHom.ker (IsLocalization.map Q g hy : S →+* Q) where
  toFun x := ⟨algebraMap R S x, by simp [RingHom.mem_ker, (RingHom.mem_ker g).mp x.property]⟩
  map_add' x y := by
    simp only [AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid, map_add, AddSubmonoid.mk_add_mk]
  map_smul' a x := by
    simp only [SetLike.val_smul, smul_eq_mul, map_mul, RingHom.id_apply,
      SetLike.mk_smul_of_tower_mk, Algebra.smul_def]

@[simp]
lemma kerMap_apply (r : RingHom.ker g) :
    (kerMap S Q g hy r).val = algebraMap R S r :=
  rfl

theorem kerMap_isLocalizedModule (hT : Submonoid.map g M = T) :
    IsLocalizedModule M (kerMap S Q g hy) where
  map_units x := by
    rw [isUnit_iff_exists]
    have hu : IsUnit (algebraMap R S x) := IsLocalization.map_units S x
    let φ : Module.End R (RingHom.ker (IsLocalization.map Q g hy : S →+* Q)) := {
      toFun := fun y ↦ ⟨hu.unit⁻¹ * y, by
        simp [RingHom.mem_ker, (RingHom.mem_ker _).mp y.property]⟩
      map_add' := fun x y ↦ by simp [mul_add]
      map_smul' := fun a x ↦ by simp
    }
    refine ⟨φ, ?_, ?_⟩
    · ext y
      simp [φ, Algebra.smul_def, ← mul_assoc]
    · ext y
      simp [φ, Algebra.smul_def, ← mul_assoc]
  surj' y := by
    subst hT
    obtain ⟨⟨r, m⟩, hx⟩ := IsLocalization.surj (M := M) y.val
    have heq : algebraMap P Q (g r) = algebraMap P Q 0 := by
      rw [← IsLocalization.map_eq (S := S) hy r, ← hx]
      simp [(RingHom.mem_ker _).mp y.property]
    obtain ⟨⟨_, t, tM, rfl⟩, ht⟩ := (IsLocalization.eq_iff_exists (Submonoid.map g M) _).mp heq
    simp only [mul_zero] at ht
    have hr : t * r ∈ RingHom.ker g := by
      simp [RingHom.mem_ker]
      exact ht
    use ⟨⟨t * r, hr⟩, ⟨t, tM⟩ * m⟩
    ext
    simp only [SetLike.val_smul_of_tower, kerMap_apply]
    rw [mul_comm] at hx
    erw [Algebra.smul_def]
    simp only [map_mul, Submonoid.coe_subtype, mul_assoc, hx]
  exists_of_eq {x y} h := by
    apply congrArg Subtype.val at h
    obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := M) h
    use c
    ext
    exact hc

end

section

open scoped Pointwise TensorProduct

namespace RingHom

theorem finitePresentation_localizationPreserves : LocalizationPreserves @FinitePresentation := by
  introv R hf
  letI := f.toAlgebra
  letI := ((algebraMap S S').comp f).toAlgebra
  let f' : R' →+* S' := IsLocalization.map S' f M.le_comap_map
  letI := f'.toAlgebra
  haveI : IsScalarTower R R' S' :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.map_comp M.le_comap_map).symm
  obtain ⟨n, g, hgsurj, hgker⟩ := hf
  let MX : Submonoid (MvPolynomial (Fin n) R) :=
    Submonoid.map (MvPolynomial.C (σ := Fin n)) M
  let T : Submonoid S := M.map f
  have hy : MX ≤ Submonoid.comap g T := by
    intro x ⟨m, hm, h⟩
    simp
    use m, hm
    rw [← h]
    show f m = g (algebraMap R _ m)
    rw [g.map_algebraMap]
    rfl
  let g' : MvPolynomial (Fin n) R' →+* S' := IsLocalization.map S' g (T := T) hy
  let g'ₐ : MvPolynomial (Fin n) R' →ₐ[R'] S' := by
    apply AlgHom.mk g'
    intro c
    obtain ⟨a, m, rfl⟩ := IsLocalization.mk'_surjective M c
    show _ = f' _
    simp [g', f', MvPolynomial.isLocalization_C_mk', IsLocalization.map_mk']
    rfl
  have hT : Submonoid.map g.toRingHom MX = Submonoid.map f M := by
    ext
    simp [MX]
    rfl
  have : IsLocalization (Submonoid.map g.toRingHom MX) S' := by
    rw [hT]
    infer_instance
  have : IsLocalizedModule MX (kerMap (MvPolynomial (Fin n) R') S' g.toRingHom _) :=
    kerMap_isLocalizedModule S' g.toRingHom (T := T) hy hT
  have : Module.Finite (MvPolynomial (Fin n) R) (ker g.toRingHom) := by
    rw [Module.Finite.iff_fg]
    exact hgker
  refine ⟨n, g'ₐ, ?_, ?_⟩
  · exact IsLocalization.map_surjective_of_surjective
      MX (MvPolynomial (Fin n) R') (g := g.toRingHom)
      S' hgsurj
  · show Submodule.FG (RingHom.ker g')
    rw [← Module.Finite.iff_fg]
    exact Module.Finite.of_isLocalizedModule (R := MvPolynomial (Fin n) R)
      (S := MX)
      (f := (kerMap (MvPolynomial (Fin n) R') S' g.toRingHom _))

theorem finitePresentation_stableUnderComposition : StableUnderComposition @FinitePresentation := by
  introv R hf hg
  exact hg.comp hf

theorem finitePresentation_holdsForLocalizationAway :
    HoldsForLocalizationAway @FinitePresentation := by
  introv R _
  suffices Algebra.FinitePresentation R S by
    rw [RingHom.FinitePresentation]
    convert this; ext;
    rw [Algebra.smul_def]; rfl
  exact IsLocalization.Away.finitePresentation r

lemma ker_FG_ofLocalizationSpanTarget
    {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}
    (t : Finset R) (ht : Ideal.span (t : Set R) = ⊤)
    (H : ∀ g : t, (RingHom.ker (Localization.awayMap f g.val)).FG) :
    (RingHom.ker f).FG := by
  show Submodule.FG (RingHom.ker f)
  rw [← Module.Finite.iff_fg]
  have hfin (g : t) :
    Module.Finite (Localization.Away g.val) (RingHom.ker (Localization.awayMap f g.val)) := by
    rw [Module.Finite.iff_fg]
    exact H g
  have hT (g : t) : Submonoid.map f (Submonoid.powers g.val) =
      Submonoid.powers (f g.val) :=
    Submonoid.map_powers f g.val
  have hy (g : t) : Submonoid.powers g.val ≤
      Submonoid.comap f (Submonoid.powers (f g.val)) := by
    rw [← hT g]
    exact Submonoid.le_comap_map (Submonoid.powers g.val)
  have (g : t) := kerMap_isLocalizedModule
    (Localization.Away (f g.val)) f (hy g)
    (S := Localization.Away g.val)
    (hT g)
  let k (g : t) :=
    (kerMap (Localization.Away g.val) (Localization.Away (f g.val)) f (hy g))
  exact Module.Finite.of_localizationSpan_finite' t ht k hfin

lemma finitePresentation_ofLocalizationSpanTarget_aux
    {R S A : Type*} [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
    [Algebra.FinitePresentation R A] (f : A →ₐ[R] S) (hf : Function.Surjective f)
    (t : Finset A) (ht : Ideal.span (t : Set A) = ⊤)
    (H : ∀ g : t, Algebra.FinitePresentation R (Localization.Away (f g))) :
    Algebra.FinitePresentation R S := by
  apply Algebra.FinitePresentation.of_surjective hf
  let f' (g : t) : Localization.Away g.val →+* Localization.Away (f g) :=
    Localization.awayMap f.toRingHom g.val
  let f'ₐ (g : t) : Localization.Away g.val →ₐ[R] Localization.Away (f g) := by
    apply AlgHom.mk (f' g)
    intro c
    simp only [AlgHom.toRingHom_eq_coe, toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
      MonoidHom.toOneHom_coe, MonoidHom.coe_coe, f']
    erw [← IsLocalization.mk'_one (M := Submonoid.powers g.val) (Localization.Away g.val)]
    simp [Localization.awayMap, IsLocalization.Away.map]
    rw [IsLocalization.map_mk']
    simp only [coe_coe, AlgHom.commutes, OneMemClass.coe_one, map_one]
    erw [IsLocalization.mk'_one]
    rfl
  have h (g : t) : Submonoid.map f.toRingHom (Submonoid.powers g.val) = Submonoid.powers (f g) := by
    ext x
    simp
  have (g : t) : IsLocalization
    (Submonoid.map f.toRingHom (Submonoid.powers g.val)) (Localization.Away (f g)) := by
    rw [h g]
    infer_instance
  have hf' (g : t) : Function.Surjective (f' g) := by
    apply IsLocalization.map_surjective_of_surjective
    exact hf
  have (g : t) : Algebra.FinitePresentation R (Localization.Away g.val) :=
    haveI : Algebra.FinitePresentation A (Localization.Away g.val) :=
      IsLocalization.Away.finitePresentation g.val
    Algebra.FinitePresentation.trans R A (Localization.Away g.val)
  apply ker_FG_ofLocalizationSpanTarget t ht
  intro g
  exact Algebra.FinitePresentation.ker_fG_of_surjective (f'ₐ g) (hf' g)

theorem finitePresentation_ofLocalizationSpanTarget :
    OfLocalizationSpanTarget @FinitePresentation := by
  rw [ofLocalizationSpanTarget_iff_finite]
  introv R hs H
  classical
  letI := f.toAlgebra
  replace H : ∀ r : s, Algebra.FinitePresentation R (Localization.Away (r : S)) := by
    intro r; simp_rw [RingHom.FinitePresentation] at H;
    convert H r; ext; simp_rw [Algebra.smul_def]; rfl
  have : Algebra.FiniteType R S := by
    apply finiteType_ofLocalizationSpanTarget f s hs
    intro r
    convert_to Algebra.FiniteType R (Localization.Away r.val)
    · rw [RingHom.FiniteType]
      constructor
      intro h
      convert h
      ext
      simp_rw [Algebra.smul_def]
      rfl
      intro h
      convert h
      ext
      simp_rw [Algebra.smul_def]
      rfl
      --rw [RingHom.FiniteType]
    · infer_instance
  rw [RingHom.FinitePresentation]
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp this
  obtain ⟨l, hl⟩ :=
    (Finsupp.mem_span_iff_total S (s : Set S) 1).mp
      (show (1 : S) ∈ Ideal.span (s : Set S) by rw [hs]; trivial)
  have (g : s) : ∃ (g' : MvPolynomial (Fin n) R), f g' = g := hf g
  choose g' hg' using this
  have (g : s) : ∃ (h' : MvPolynomial (Fin n) R), f h' = l g := hf (l g)
  choose h' hh' using this
  let I : Ideal (MvPolynomial (Fin n) R) := Ideal.span { ∑ g : s, g' g * h' g - 1 }
  let A := MvPolynomial (Fin n) R ⧸ I
  have hfI : ∀ a ∈ I, f a = 0 := by
    intro p hp
    simp [I] at hp
    rw [Ideal.mem_span_singleton] at hp
    obtain ⟨q, hq⟩ := hp
    rw [hq]
    simp
    simp_rw [hg', hh']
    erw [Finsupp.total_apply_of_mem_supported S (s := s.attach)] at hl
    rw [← hl]
    simp
    simp_rw [mul_comm]
    simp
    rw [Finsupp.mem_supported]
    rintro a -
    simp
  let f' : A →ₐ[R] S := Ideal.Quotient.liftₐ I f hfI
  have hf' : Function.Surjective f' :=
    Ideal.Quotient.lift_surjective_of_surjective I hfI hf
  let t : Finset A := Finset.image (fun g ↦ g' g) Finset.univ
  have ht : Ideal.span (t : Set A) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have : (1 : A) = ∑ g : { x // x ∈ s }, g' g * h' g := by
      symm
      apply eq_of_sub_eq_zero
      show _ - Ideal.Quotient.mk I 1 = 0
      rw [← map_sub]
      rw [Ideal.Quotient.eq_zero_iff_mem]
      simp only [I]
      apply Ideal.subset_span
      simp
    rw [this]
    simp
    apply Ideal.sum_mem
    rintro g -
    apply Ideal.mul_mem_right
    apply Ideal.subset_span
    simp [t]
  have : Algebra.FinitePresentation R A := by
    apply Algebra.FinitePresentation.quotient
    simp only [Finset.univ_eq_attach, I]
    use {∑ g ∈ s.attach, g' g * h' g - 1}
    simp
  have Ht (g : t) : Algebra.FinitePresentation R (Localization.Away (f' g)) := by
    have := g.property
    simp [t] at this
    obtain ⟨r, hr, hrr⟩ := this
    rw [← hrr]
    simp [f']
    erw [Ideal.Quotient.lift_mk]
    erw [hg']
    apply H
  exact finitePresentation_ofLocalizationSpanTarget_aux f' hf' t ht Ht

theorem finitePresentation_is_local : PropertyIsLocal @FinitePresentation :=
  ⟨finitePresentation_localizationPreserves,
    finitePresentation_ofLocalizationSpanTarget, finitePresentation_stableUnderComposition,
    finitePresentation_holdsForLocalizationAway⟩

theorem finitePresentation_respectsIso : RingHom.RespectsIso @RingHom.FinitePresentation :=
  RingHom.finitePresentation_is_local.respectsIso

theorem finitePresentation_stableUnderBaseChange : StableUnderBaseChange @FinitePresentation := by
  apply StableUnderBaseChange.mk
  · exact finitePresentation_respectsIso
  · introv h
    replace h : Algebra.FinitePresentation R T := by
      rw [RingHom.FinitePresentation] at h; convert h; ext; simp_rw [Algebra.smul_def]; rfl
    suffices Algebra.FinitePresentation S (S ⊗[R] T) by
      rw [RingHom.FinitePresentation]; convert this; congr; ext; simp_rw [Algebra.smul_def]; rfl
    infer_instance

end RingHom
