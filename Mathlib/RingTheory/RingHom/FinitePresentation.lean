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
import Mathlib.Algebra.Module.LocalizedModuleIntegers

/-!

# The meta properties of finitely-presented ring homomorphisms.

The main result is `RingHom.finitePresentation_is_local`.

-/

section

variable {R Rₚ : Type*} [CommSemiring R] (S : Submonoid R)
  [CommSemiring Rₚ] [Algebra R Rₚ] [IsLocalization S Rₚ]
  {M Mₚ : Type*}
  [AddCommMonoid M] [AddCommMonoid Mₚ] [Module R M] [Module R Mₚ] (f : M →ₗ[R] Mₚ)
  [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ]
  [IsLocalizedModule S f]

lemma Module.Finite_of_isLocalizedModule [Module.Finite R M] : Module.Finite Rₚ Mₚ := by
  classical
  obtain ⟨T, hT⟩ := ‹Module.Finite R M›
  use T.image f
  rw [eq_top_iff]
  rintro x -
  obtain ⟨⟨y, m⟩, (hyx : IsLocalizedModule.mk' f y m = x)⟩ :=
    IsLocalizedModule.mk'_surjective S f x
  have hy : y ∈ Submodule.span R T := by rw [hT]; trivial
  have : f y ∈ Submodule.map f (Submodule.span R T) := Submodule.mem_map_of_mem hy
  rw [Submodule.map_span] at this
  have H : Submodule.span R (f '' T) ≤
      (Submodule.span Rₚ (f '' T)).restrictScalars R := by
    rw [Submodule.span_le]; exact Submodule.subset_span
  convert (Submodule.span Rₚ (f '' T)).smul_mem
    (IsLocalization.mk' Rₚ (1 : R) m) (H this) using 1
  · rw [← hyx, ← IsLocalizedModule.mk'_one S, IsLocalizedModule.mk'_smul_mk']
    simp
  · simp

end

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

@[to_additive]
lemma Finset.prod_eq' {α β : Type*} [CommMonoid β] {s : Finset α} {f : α → β}
    {b₁ b₂ : β}
    (h : ∃ a ∈ s, f a * b₁ = f a * b₂) :
    (∏ a ∈ s, f a) * b₁ = (∏ a ∈ s, f a) * b₂ := by
  obtain ⟨a, ha, h⟩ := h
  classical
  rw [← insert_erase ha]
  simp only [mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true, prod_insert]
  rw [mul_assoc, mul_comm, mul_assoc, mul_comm b₁, h, ← mul_assoc, mul_comm _ (f a)]

@[to_additive]
lemma Finsupp.prod_eq' {α M N : Type*} [Zero M] [CommMonoid N] {f : α →₀ M}
    {g : α → M → N} {n₁ n₂ : N} (h : ∃ a ∈ f.support, g a (f a) * n₁ = g a (f a) * n₂) :
    f.prod g * n₁ = f.prod g * n₂ :=
  Finset.prod_eq' h

end

section

variable {R S σ : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

noncomputable instance : Algebra (MvPolynomial σ R) (MvPolynomial σ S) :=
  (MvPolynomial.map (algebraMap R S)).toAlgebra

@[simp]
lemma MvPolynomial.algebraMap_def :
    algebraMap (MvPolynomial σ R) (MvPolynomial σ S) = MvPolynomial.map (algebraMap R S) :=
  rfl

end

open scoped Pointwise TensorProduct

instance MvPolynomial.isLocalization {σ R : Type*} [CommRing R] (M : Submonoid R)
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization M S] :
    IsLocalization (Submonoid.map (MvPolynomial.C (σ := σ)) M) (MvPolynomial σ S) where
  map_units' := by
    rintro ⟨p, q, hq, rfl⟩
    simp only [algebraMap_def, MvPolynomial.map_C]
    exact IsUnit.map _ (IsLocalization.map_units _ ⟨q, hq⟩)
  surj' p := by
    simp only [algebraMap_def, Prod.exists, Subtype.exists,
      Submonoid.mem_map, exists_prop, exists_exists_and_eq_and, MvPolynomial.map_C]
    refine MvPolynomial.induction_on' p ?_ ?_
    · intro u s
      obtain ⟨⟨r, m⟩, hr⟩ := IsLocalization.surj M s
      use MvPolynomial.monomial u r, m, m.property
      simp only [MvPolynomial.map_monomial]
      rw [← hr, mul_comm, MvPolynomial.C_mul_monomial, mul_comm]
    · intro p p' ⟨x, m, hm, hxm⟩ ⟨x', m', hm', hxm'⟩
      use x * (MvPolynomial.C m') + x' * (MvPolynomial.C m), m * m', Submonoid.mul_mem _ hm hm'
      simp only [map_mul, map_add, MvPolynomial.map_C]
      rw [add_mul, ← mul_assoc, hxm, ← mul_assoc, ← hxm, ← hxm']
      ring
  exists_of_eq {p q} := by
    intro h
    simp at h
    simp_rw [MvPolynomial.ext_iff, MvPolynomial.coeff_map] at h
    choose c hc using (fun m ↦ IsLocalization.exists_of_eq (M := M) (h m))
    simp only [Subtype.exists, Submonoid.mem_map, exists_prop, exists_exists_and_eq_and]
    classical
    refine ⟨Finset.prod (p.support ∪ q.support) (fun m ↦ c m), ?_, ?_⟩
    · exact M.prod_mem (fun m _ ↦ (c m).property)
    · ext m
      simp only [MvPolynomial.coeff_C_mul]
      by_cases h : m ∈ p.support ∪ q.support
      · apply Finset.prod_eq'
        use m, h, hc m
      · simp at h
        rw [h.left, h.right]

lemma MvPolynomial.isLocalization_C_mk' {σ R : Type*} [CommRing R] (M : Submonoid R)
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization M S]
    (a : R) (m : M) :
    MvPolynomial.C (IsLocalization.mk' S a m) =
      IsLocalization.mk' (MvPolynomial σ S) (MvPolynomial.C (σ := σ) a)
      ⟨MvPolynomial.C m, Submonoid.mem_map_of_mem MvPolynomial.C m.property⟩ := by
  simp_rw [IsLocalization.eq_mk'_iff_mul_eq, algebraMap_def, map_C, ← map_mul,
    IsLocalization.mk'_spec]

@[simp]
lemma MvPolynomial.algHom_C' {R S σ : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    (f : MvPolynomial σ R →ₐ[R] S) (r : R) :
    f (MvPolynomial.C r) = algebraMap R S r := by
  rw [← MvPolynomial.algebraMap_eq, AlgHom.map_algebraMap]

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
    exact Module.Finite_of_isLocalizedModule (R := MvPolynomial (Fin n) R)
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

theorem IsLocalizedModule.multiple_mem_span_of_mem_localization_span
    {R M : Type*} [CommRing R] [AddCommMonoid M] [Module R M] (S : Submonoid R) (R' : Type*)
    [CommRing R'] [Algebra R R'] [Module R' M] [IsScalarTower R R' M]
    [IsLocalization S R'] (s : Set M) (x : M) (hx : x ∈ Submodule.span R' s) :
    ∃ (t : S), t • x ∈ Submodule.span R s := by
  classical
  obtain ⟨s', hss', hs'⟩ := Submodule.mem_span_finite_of_mem_span hx
  rsuffices ⟨t, ht⟩ : ∃ t : S, t • x ∈ Submodule.span R (s' : Set M)
  · exact ⟨t, Submodule.span_mono hss' ht⟩
  clear hx hss' s
  induction s' using Finset.induction_on generalizing x
  · use 1; simpa using hs'
  rename_i a s _ hs
  simp only [Finset.coe_insert, Finset.image_insert, Finset.coe_image, Subtype.coe_mk,
    Submodule.mem_span_insert] at hs' ⊢
  rcases hs' with ⟨y, z, hz, rfl⟩
  rcases IsLocalization.surj S y with ⟨⟨y', s'⟩, e⟩
  simp at e
  apply congrArg (fun x ↦ x • a) at e
  simp at e
  --simp_rw [RingHom.map_mul, ← IsScalarTower.algebraMap_apply, mul_comm (algebraMap R' S y),
  --  mul_assoc, ← Algebra.smul_def] at e
  rcases hs _ hz with ⟨t, ht⟩
  refine ⟨t * s', t * y', _, (Submodule.span R (s : Set M)).smul_mem s' ht, ?_⟩
  rw [smul_add, ← smul_smul, mul_comm, ← smul_smul, ← smul_smul, ← e]
  rw [mul_comm, ← Algebra.smul_def]
  simp
  rfl

theorem IsLocalizedModule.smul_mem_finsetIntegerMultiple_span
    {R M M' : Type*} [CommRing R] [AddCommMonoid M] [Module R M] [AddCommMonoid M']
    [Module R M'] (f : M →ₗ[R] M') (S : Submonoid R) [IsLocalizedModule S f]
    [DecidableEq M]
    (x : M) (s : Finset M')
    (hx : f x ∈ Submodule.span R s) :
    ∃ (m : S), m • x ∈ Submodule.span R (IsLocalizedModule.finsetIntegerMultiple S f s) := by
  let y : S := IsLocalizedModule.commonDenomOfFinset S f s
  have hx₁ : (y : R) • (s : Set M') = f '' _ :=
    (IsLocalizedModule.finsetIntegerMultiple_image S f s).symm
  apply congrArg (Submodule.span R) at hx₁
  rw [Submodule.span_smul] at hx₁
  replace hx : _ ∈ y • Submodule.span R (s : Set M') := Set.smul_mem_smul_set hx
  erw [hx₁] at hx
  erw [← f.map_smul, ← Submodule.map_span f] at hx
  obtain ⟨x', hx', hx''⟩ := hx
  obtain ⟨a, ha⟩ := (IsLocalizedModule.eq_iff_exists S f).mp hx''
  use a * y
  convert (Submodule.span R
    (IsLocalizedModule.finsetIntegerMultiple S f s : Set M)).smul_mem
      a hx' using 1
  convert ha.symm using 1
  simp
  rw [Submonoid.smul_def]
  erw [← smul_smul]
  rfl

theorem finite_ofLocalizationSpanTarget' {R M : Type*} [CommRing R] [AddCommMonoid M]
    [Module R M] (t : Finset R) (ht : Ideal.span (t : Set R) = ⊤)
    {M' : ∀ (_ : t), Type*}
    [∀ (g : t), AddCommMonoid (M' g)]
    [∀ (g : t), Module R (M' g)]
    [∀ (g : t), Module (Localization.Away g.val) (M' g)]
    [∀ (g : t), IsScalarTower R (Localization.Away g.val) (M' g)]
    (f : ∀ (g : t), M →ₗ[R] M' g)
    [∀ (g : t), IsLocalizedModule (Submonoid.powers g.val) (f g)]
    (H : ∀ (g : t), Module.Finite (Localization.Away g.val) (M' g)) :
    Module.Finite R M := by
  constructor
  classical
  replace H := fun g => (H g).1
  choose s₁ s₂ using H
  let sf := fun x : t =>
    IsLocalizedModule.finsetIntegerMultiple (Submonoid.powers x.val) (f x) (s₁ x)
  use t.attach.biUnion sf
  rw [Submodule.span_attach_biUnion, eq_top_iff]
  rintro x -
  apply Submodule.mem_of_span_eq_top_of_smul_pow_mem _ (t : Set R) ht _ _
  intro r
  let S : Submonoid R := Submonoid.powers r.val
  have := IsLocalizedModule.multiple_mem_span_of_mem_localization_span
    (R := R) (M := M' r) S
    (Localization.Away (r : R)) (s₁ r : Set (M' r))
    (IsLocalizedModule.mk' (f r) x (1 : S))
    (by rw [s₂ r]; trivial)
  obtain ⟨⟨_, n₁, rfl⟩, hn₁⟩ := this
  dsimp only at hn₁
  rw [Submonoid.smul_def] at hn₁
  dsimp only at hn₁
  rw [← IsLocalizedModule.mk'_smul] at hn₁
  rw [IsLocalizedModule.mk'_one] at hn₁
  obtain ⟨⟨_, n₂, rfl⟩, hn₂⟩ := IsLocalizedModule.smul_mem_finsetIntegerMultiple_span
    (f r) S _ (s₁ r) hn₁
  rw [Submonoid.smul_def] at hn₂
  simp at hn₂
  use n₂ + n₁
  apply le_iSup (fun x : t ↦ Submodule.span R (sf x : Set M)) r
  rw [pow_add]
  rw [mul_smul]
  exact hn₂

theorem finite_ofLocalizationSpanTarget {R M : Type*} [CommRing R] [AddCommMonoid M]
    [Module R M] (t : Finset R) (ht : Ideal.span (t : Set R) = ⊤)
    (H : ∀ (g : t), Module.Finite (Localization.Away g.val)
      (LocalizedModule (Submonoid.powers g.val) M)) :
    Module.Finite R M := by
  constructor
  classical
  replace H := fun g => (H g).1
  choose s₁ s₂ using H
  let sf := fun x : t =>
    IsLocalizedModule.finsetIntegerMultiple (Submonoid.powers x.val) 
      (LocalizedModule.mkLinearMap (Submonoid.powers x.val) M) (s₁ x)
  use t.attach.biUnion sf
  rw [Submodule.span_attach_biUnion, eq_top_iff]
  rintro x -
  apply Submodule.mem_of_span_eq_top_of_smul_pow_mem _ (t : Set R) ht _ _
  intro r
  let S : Submonoid R := Submonoid.powers r.val
  let M' := LocalizedModule S M
  have := IsLocalizedModule.multiple_mem_span_of_mem_localization_span
    (R := R) (M := M') S
    (Localization.Away (r : R)) (s₁ r : Set (LocalizedModule (Submonoid.powers r.val) M))
    (LocalizedModule.mk x 1)
    (by rw [s₂ r]; trivial)
  obtain ⟨⟨_, n₁, rfl⟩, hn₁⟩ := this
  dsimp only at hn₁
  rw [Submonoid.smul_def] at hn₁
  simp at hn₁
  rw [LocalizedModule.smul'_mk] at hn₁
  obtain ⟨⟨_, n₂, rfl⟩, hn₂⟩ := IsLocalizedModule.smul_mem_finsetIntegerMultiple_span
    (LocalizedModule.mkLinearMap S M) S _ (s₁ r) hn₁
  rw [Submonoid.smul_def] at hn₂
  simp at hn₂
  use n₂ + n₁
  apply le_iSup (fun x : t ↦ Submodule.span R (sf x : Set M)) r
  rw [pow_add]
  rw [mul_smul]
  exact hn₂

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
  apply finite_ofLocalizationSpanTarget' t ht k
  intro g
  exact hfin g

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
