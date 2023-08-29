/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.GroupTheory.Coprod.CoprodI
import Mathlib.GroupTheory.Coprod.Coprod
import Mathlib.GroupTheory.QuotientGroup

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)] {H : Type*} [Group H]
  (φ : ∀ i, H →* G i) {K : Type*} [Group K]

open Monoid CoprodI Subgroup Coprod

def AmalgamatedProduct : Type _ :=
  ((CoprodI G) ∗ H) ⧸ normalClosure
    (⋃ (i : ι), Set.range (fun g : H => inl (of (φ i g)⁻¹) * (inr g)))

namespace AmalgamatedProduct

variable {φ}

instance : Group (AmalgamatedProduct φ) :=
  QuotientGroup.Quotient.group _

def of {i : ι} : G i →* AmalgamatedProduct φ :=
  (QuotientGroup.mk' _).comp <| inl.comp CoprodI.of

def base : H →* AmalgamatedProduct φ :=
  (QuotientGroup.mk' _).comp <| inr

@[simp]
theorem of_comp_eq_base (i : ι) : of.comp (φ i) = (base (φ := φ)) := by
  ext x
  apply QuotientGroup.eq.2
  refine subset_normalClosure ?_
  simp only [MonoidHom.comp_apply, Set.mem_iUnion, Set.mem_range]
  exact ⟨_, _, rfl⟩

@[simp]
theorem of_apply_eq_base (i : ι) (x : H) : of (φ i x) = base (φ := φ) x := by
  rw [← MonoidHom.comp_apply, of_comp_eq_base]

def lift (f : ∀ i, G i →* K) (k : H →* K)
    (hf : ∀ i, (f i).comp (φ i) = k) :
    AmalgamatedProduct φ →* K :=
  QuotientGroup.lift _ (Coprod.lift (CoprodI.lift f) k)
    (show normalClosure _ ≤ (Coprod.lift (CoprodI.lift f) k).ker
      from normalClosure_le_normal <| by
        simp only [Set.iUnion_subset_iff, Set.range_subset_iff,
          MonoidHom.mem_ker, SetLike.mem_coe]
        intro i h
        simp only [FunLike.ext_iff, MonoidHom.coe_comp, Function.comp_apply] at hf
        simp [hf i])

set_option maxHeartbeats 200000 in
@[simp]
theorem lift_of (f : ∀ i, G i →* K) (k : H →* K)
    (hf : ∀ i, (f i).comp (φ i) = k)
    {i : ι} (g : G i) : (lift f k hf) (of g : AmalgamatedProduct φ) = f i g := by
  delta AmalgamatedProduct lift of
  simp only [MonoidHom.coe_comp, QuotientGroup.coe_mk', Function.comp_apply,
    QuotientGroup.lift_mk, lift_inl, lift_of, CoprodI.lift_of]

set_option maxHeartbeats 200000 in
@[simp]
theorem lift_base (f : ∀ i, G i →* K) (k : H →* K)
    (hf : ∀ i, (f i).comp (φ i) = k)
    (g : H) : (lift f k hf) (base g : AmalgamatedProduct φ) = k g := by
  delta AmalgamatedProduct lift base
  simp only [MonoidHom.coe_comp, QuotientGroup.coe_mk', Function.comp_apply,
    QuotientGroup.lift_mk, lift_inr, lift_of]

set_option maxHeartbeats 200000 in
@[ext 1199]
theorem hom_ext {f g : AmalgamatedProduct φ →* K}
    (h : ∀ i, f.comp (of : G i →* _) = g.comp (of : G i →* _))
    (hbase : f.comp base = g.comp base) : f = g :=
  QuotientGroup.monoidHom_ext _ <|
    Coprod.ext_hom _ _
      (CoprodI.ext_hom _ _ h)
      hbase

@[ext high]
theorem hom_ext_nonempty [hn : Nonempty ι]
    {f g : AmalgamatedProduct φ →* K}
    (h : ∀ i, f.comp (of : G i →* _) = g.comp (of : G i →* _)) : f = g :=
  hom_ext h <| by
    cases hn with
    | intro i =>
      ext
      rw [← of_comp_eq_base i, ← MonoidHom.comp_assoc, h, MonoidHom.comp_assoc]

def ofCoprodI : CoprodI G →* AmalgamatedProduct φ :=
  CoprodI.lift (fun _ => of)

@[simp]
theorem ofCoprodI_of (i : ι) (g : G i) :
    (ofCoprodI (CoprodI.of g) : AmalgamatedProduct φ) = of g := by
  simp [ofCoprodI]

theorem induction_on {motive : AmalgamatedProduct φ → Prop}
    (x : AmalgamatedProduct φ)
    (of  : ∀ (i : ι) (g : G i), motive (of g))
    (base : ∀ h, motive (base h))
    (mul : ∀ x y, motive x → motive y → motive (x * y)) : motive x := by
  delta AmalgamatedProduct AmalgamatedProduct.of AmalgamatedProduct.base at *
  induction x using QuotientGroup.induction_on with
  | H x =>
    induction x using Coprod.induction_on with
    | h_inl g =>
      induction g using CoprodI.induction_on with
      | h_of i g => exact of i g
      | h_mul x y ihx ihy =>
        rw [map_mul]
        exact mul _ _ ihx ihy
      | h_one => simpa using base 1
    | h_inr h => exact base h
    | h_mul x y ihx ihy => exact mul _ _ ihx ihy

namespace NormalWord

open Coset

variable (φ)

noncomputable def normalizeSingle {i : ι} (g : G i) : H × G i :=
  letI := Classical.propDecidable (g ∈ (φ i).range )
  if hg : g ∈ (φ i).range
  then ⟨Classical.choose hg, 1⟩
  else
    let s : Set (G i) := rightCoset (φ i).range g
    have hs : s.Nonempty := ⟨g, mem_own_rightCoset _ _⟩
    let g' := Classical.choose hs
    let h' := Classical.choose (Classical.choose_spec (Classical.choose_spec hs)).1
    ⟨h'⁻¹, g'⟩

theorem normalizeSingle_fst_mul_normalizeSingle_snd {i : ι} (g : G i) :
    φ i (normalizeSingle φ g).1 * (normalizeSingle φ g).2 = g := by
  let s : Set (G i) := rightCoset (φ i).range g
  have hs : s.Nonempty := ⟨g, mem_own_rightCoset _ _⟩
  dsimp [normalizeSingle]
  split_ifs with hg
  · simp [Classical.choose_spec hg]
  · simp only [normalizeSingle, MonoidHom.coe_range, Set.mem_range, map_inv,
      Eq.ndrec, id_eq]
    rw [Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hs)).1,
      inv_mul_eq_iff_eq_mul]
    have := Classical.choose_spec (Classical.choose_spec hs)
    dsimp at this
    rw [this.2]

theorem normalizeSingle_fst_eq {i : ι} (g : G i) :
    φ i (normalizeSingle φ g).1 = g * (normalizeSingle φ g).2⁻¹ :=
  eq_mul_inv_iff_mul_eq.2 (normalizeSingle_fst_mul_normalizeSingle_snd _ _)

theorem normalizeSingle_snd_eq_of_rightCosetEquivalence {i : ι} {g₁ g₂ : G i}
    (h : RightCosetEquivalence (φ i).range g₁ g₂) :
    (normalizeSingle φ g₁).2 = (normalizeSingle φ g₂).2 := by
  simp [normalizeSingle]
  by_cases hg₁ : g₁ ∈ (φ i).range
  · have hg₂ : g₂ ∈ (φ i).range := by
      rwa [RightCosetEquivalence, rightCoset_eq_iff, mul_mem_cancel_right
        (inv_mem hg₁)] at h
    rw [dif_pos hg₁, dif_pos hg₂]
  · have hg₂ : g₂ ∉ (φ i).range := by
      intro hg₂
      rw [RightCosetEquivalence, rightCoset_eq_iff, mul_mem_cancel_left hg₂,
        inv_mem_iff (x := g₁)] at h
      exact hg₁ h
    rw [dif_neg hg₁, dif_neg hg₂]
    dsimp
    congr

theorem rightCosetEquivalence_normalizeSingle_snd {i : ι} (g : G i) :
    RightCosetEquivalence (φ i).range g (normalizeSingle φ g).2 := by
  dsimp only [normalizeSingle]
  split_ifs with hg
  · rwa [RightCosetEquivalence, rightCoset_eq_iff, _root_.one_mul,
      inv_mem_iff (x := g)]
  · let s : Set (G i) := rightCoset (φ i).range g
    have hs : s.Nonempty := ⟨g, mem_own_rightCoset _ _⟩
    erw [RightCosetEquivalence, rightCoset_eq_iff,
      ← mem_rightCoset_iff (s := (φ i).range) g]
    exact Classical.choose_spec hs

@[simp]
theorem normalizeSingle_snd_normalize_single_snd {i : ι} {g : G i} :
    (normalizeSingle φ (normalizeSingle φ g).2).2 = (normalizeSingle φ g).2 :=
  normalizeSingle_snd_eq_of_rightCosetEquivalence _
    (rightCosetEquivalence_normalizeSingle_snd _ _).symm

variable {φ} (hφ : ∀ _i, Function.Injective (φ _i))

theorem normalizeSingle_mul {i : ι} (h : H) (g : G i) :
    normalizeSingle φ (φ i h * g) = ⟨h * (normalizeSingle φ g).1,
      (normalizeSingle φ g).2⟩ := by
  have : (normalizeSingle φ (φ i h * g)).2 = (normalizeSingle φ g).2 :=
    normalizeSingle_snd_eq_of_rightCosetEquivalence _
      ((rightCoset_eq_iff _).2 (by simp))
  ext
  · apply hφ _
    erw [← mul_left_inj ((normalizeSingle φ (φ i h * g)).2),
      normalizeSingle_fst_mul_normalizeSingle_snd, this,
      map_mul, mul_assoc, normalizeSingle_fst_mul_normalizeSingle_snd]
  · exact this

theorem normalizeSingle_app {i : ι} (h : H) :
    (normalizeSingle φ (φ i h)) = (h, 1)  := by
  rw [normalizeSingle, dif_pos (MonoidHom.mem_range.2 ⟨_, rfl⟩)]
  simp only [Prod.mk.injEq, and_true]
  apply hφ i
  rw [Classical.choose_spec (MonoidHom.mem_range.2 ⟨_, rfl⟩)]

@[simp]
theorem normalizeSingle_one {i : ι} :
    (normalizeSingle (i := i) φ 1) = (1, 1)  := by
  have h1 : 1 ∈ (φ i).range := one_mem  _
  rw [normalizeSingle, dif_pos (one_mem _)]
  simp only [Prod.mk.injEq, and_true]
  apply hφ i
  rw [Classical.choose_spec h1, map_one]

theorem normalizeSingle_injective (i : ι) :
    Function.Injective (normalizeSingle φ (i := i)) := by
  intro g₁ g₂ H
  rw [← normalizeSingle_fst_mul_normalizeSingle_snd φ g₁,
    H, normalizeSingle_fst_mul_normalizeSingle_snd]

theorem mem_range_iff_normalizeSingle_snd_eq_one {i : ι} (g : G i) :
    (normalizeSingle φ g).snd = 1 ↔ g ∈ (φ i).range := by
  rw [← mul_right_inj (φ i (normalizeSingle φ g).fst),
    normalizeSingle_fst_mul_normalizeSingle_snd, mul_one]
  constructor
  · intro h; rw [h]; simp
  · rintro ⟨_, rfl⟩; simp [normalizeSingle_app hφ]

open List

variable (φ)

structure _root_.AmalgamatedProduct.NormalWord extends CoprodI.Word G where
  left : H
  normalized : ∀ i g, ⟨i, g⟩ ∈ toList → (normalizeSingle φ g).2 = g

variable {φ}

@[simps!]
def empty : NormalWord φ := ⟨CoprodI.Word.empty, 1, fun i g => by simp [CoprodI.Word.empty]⟩

instance : Inhabited (NormalWord φ) := ⟨NormalWord.empty⟩

variable (φ)

/- Inspired by a similar structure in `CoprodI` -/
structure Pair (i : ι) extends CoprodI.Word.Pair G i where
  normalized : ∀ i g, ⟨i, g⟩ ∈ tail.toList → (normalizeSingle φ g).2 = g

variable {φ}

instance (i : ι) : Inhabited (Pair φ i) :=
  ⟨{ (empty : NormalWord φ) with
      head := 1,
      fstIdx_ne := fun h => by cases h }⟩

variable [DecidableEq ι] [∀ i, DecidableEq (G i)]

@[ext]
theorem ext {w₁ w₂ : NormalWord φ} (hleft : w₁.left = w₂.left)
    (hlist : w₁.toList = w₂.toList) : w₁ = w₂ := by
  rcases w₁ with ⟨⟨_, _, _⟩, _, _⟩
  rcases w₂ with ⟨⟨_, _, _⟩, _, _⟩
  simp_all

theorem ext_iff {w₁ w₂ : NormalWord φ} : w₁ = w₂ ↔ w₁.left = w₂.left ∧ w₁.toList = w₂.toList :=
  ⟨fun h => by simp [h], fun ⟨h₁, h₂⟩ => ext h₁ h₂⟩

theorem eq_one_of_smul_normalized (w : CoprodI.Word G) {i : ι} (h : H)
    (hw : ∀ i g, ⟨i, g⟩ ∈ w.toList → (normalizeSingle φ g).2 = g)
    (hφw : ∀ j g, ⟨j, g⟩ ∈ (CoprodI.of (φ i h) • w).toList → (normalizeSingle φ g).2 = g) :
    h = 1 := by
  have hhead : (normalizeSingle φ (Word.equivPair i w).head).2 =
      (Word.equivPair i w).head := by
    rw [Word.equivPair_head]
    split_ifs with h
    · rcases h with ⟨_, rfl⟩
      dsimp
      exact hw _ _ (List.head_mem _)
    · rw [normalizeSingle_one hφ]
  by_contra hh1
  have := hφw i (φ i h * (Word.equivPair i w).head) ?_
  · apply hh1
    simpa [normalizeSingle_mul hφ, hhead, ((injective_iff_map_eq_one' _).1 (hφ i))] using this
  . simp only [Word.mem_smul_iff, not_true, false_and, ne_eq, Option.mem_def, mul_right_inj,
      exists_eq_right', mul_right_eq_self, exists_prop, true_and, false_or]
    constructor
    · intro h
      apply_fun (normalizeSingle φ) at h
      rw [normalizeSingle_one hφ, normalizeSingle_mul hφ, hhead,
        Prod.ext_iff] at h
      rcases h with ⟨h₁, h₂⟩
      dsimp at h₁ h₂
      rw [h₂, normalizeSingle_one hφ, mul_one] at h₁
      contradiction
    · rw [Word.equivPair_head]
      dsimp
      split_ifs with hep
      · rcases hep with ⟨hnil, rfl⟩
        rw [head?_eq_head _ hnil]
        simp_all
      · push_neg at hep
        by_cases hw : w.toList = []
        · simp [hw, Word.fstIdx]
        · simp [head?_eq_head _ hw, Word.fstIdx, hep hw]

theorem ext_smul {w₁ w₂ : NormalWord φ} (i : ι)
    (h : CoprodI.of (φ i w₁.left) • w₁.toWord =
      CoprodI.of (φ i w₂.left) • w₂.toWord) :
    w₁ = w₂ := by
  rcases w₁ with ⟨w₁, h₁, hw₁⟩
  rcases w₂ with ⟨w₂, h₂, hw₂⟩
  dsimp at *
  rw [smul_eq_iff_eq_inv_smul, ← mul_smul] at h
  subst h
  simp only [← map_inv, ← map_mul] at hw₁
  have : h₁⁻¹ * h₂ = 1 := eq_one_of_smul_normalized hφ _ (h₁⁻¹ * h₂) hw₂ hw₁
  rw [inv_mul_eq_one] at this; subst this
  simp

@[simps!]
noncomputable def cons {i} (g : G i) (w : NormalWord φ) (hmw : w.fstIdx ≠ some i)
    (hgr : g ∉ (φ i).range) : NormalWord φ :=
  letI n := normalizeSingle φ (g * (φ i w.left))
  letI w' := Word.cons n.2 w.toWord hmw
    (mt (mem_range_iff_normalizeSingle_snd_eq_one hφ _).1
      (mt (mul_mem_cancel_right (by simp)).1 hgr))
  { toWord := w'
    left := n.1
    normalized := fun i g hg => by
      simp only [Word.cons, mem_cons, Sigma.mk.inj_iff] at hg
      rcases hg with ⟨rfl, hg | hg⟩
      · simp
      · exact w.normalized _ _ (by assumption) }

noncomputable def rcons {i : ι} (p : Pair φ i) : NormalWord φ :=
  let n := normalizeSingle φ p.head
  let w := (Word.equivPair i).symm { p.toPair with head := n.2 }
  { toWord := w
    left := n.1
    normalized := fun i g hg => by
        dsimp at hg
        rw [Word.equivPair_symm, Word.mem_rcons_iff] at hg
        rcases hg with hg | ⟨_, rfl, rfl⟩
        · exact p.normalized _ _ hg
        · simp }

theorem rcons_injective {i : ι} : Function.Injective (rcons (φ := φ) (i := i)) := by
  rintro ⟨⟨head₁, tail₁⟩, _⟩ ⟨⟨head₂, tail₂⟩, _⟩
  simp only [rcons, NormalWord.mk.injEq, EmbeddingLike.apply_eq_iff_eq,
    Word.Pair.mk.injEq, Pair.mk.injEq, and_imp]
  intro h₁ h₂ h₃
  subst h₂
  rw [← normalizeSingle_fst_mul_normalizeSingle_snd φ head₁,
    h₁, h₃, normalizeSingle_fst_mul_normalizeSingle_snd]
  simp

noncomputable def equivPair (i) : NormalWord φ ≃ Pair φ i :=
  let toFun : NormalWord φ → Pair φ i :=
    fun w =>
      let p := Word.equivPair i (CoprodI.of (φ i w.left) • w.toWord)
      { toPair := p
        normalized := fun j g hg => by
          dsimp only at hg
          rw [Word.of_smul_def, ← Word.equivPair_symm, Equiv.apply_symm_apply] at hg
          dsimp at hg
          exact w.normalized _ _ (Word.mem_of_mem_equivPair_tail _ hg) }
  have leftInv : Function.LeftInverse (rcons (φ := φ)) toFun :=
    fun w => ext_smul hφ i <| by
      simp only [rcons, Word.equivPair_symm, Word.smul_eq_of_smul, Eq.ndrec, eq_mp_eq_cast,
        cast_eq, Word.rcons_eq_smul, ne_eq, id_eq, ← mul_smul, ← map_mul,
        normalizeSingle_fst_mul_normalizeSingle_snd, Word.equivPair_smul_same]
      simp only [map_mul, mul_smul, Word.equivPair_head_smul_equivPair_tail]
  { toFun := toFun
    invFun := rcons
    left_inv := leftInv
    right_inv := fun _ => rcons_injective (leftInv _) }

noncomputable def summandToEndNormalWord (i : ι) :
    G i →* Function.End (NormalWord φ) :=
  { toFun := fun g w => (equivPair hφ i).symm
      { equivPair hφ i w with
        head := g * (equivPair hφ i w).head }
    map_one' := by
      funext w
      dsimp [instHSMul]
      rw [one_mul]
      exact (equivPair hφ i).symm_apply_apply w
    map_mul' := fun _ _ => by
      funext w
      simp [mul_assoc, Equiv.apply_symm_apply, Function.End.mul_def] }

noncomputable def summandToPermNormalWord (i : ι) : G i →* Equiv.Perm (NormalWord φ) :=
  @MulAction.toPermHom _ _ _ (MulAction.ofEndHom (summandToEndNormalWord hφ i))

theorem summandToPermNormalWord_apply {i : ι} (g : G i) :
  (summandToPermNormalWord hφ i g : NormalWord φ → NormalWord φ) =
    fun w => (equivPair hφ i).symm
      { equivPair hφ i w with
        head := g * (equivPair hφ i w).head } := rfl

theorem summandToPermNormalWord_injective {i : ι} : Function.Injective (summandToPermNormalWord hφ i) := by
  simp [Function.Injective, Equiv.ext_iff, summandToPermNormalWord_apply, summandToEndNormalWord]

instance : MulAction H (NormalWord φ) :=
  { smul := fun h w => { w with left := h * w.left },
    one_smul := by simp [instHSMul]
    mul_smul := by simp [instHSMul, mul_assoc] }

theorem base_smul_def (h : H) (w : NormalWord φ) :
    h • w = { w with left := h * w.left } := rfl

@[simp]
def baseToEndNormalWord : H →* Function.End (NormalWord φ) :=
  MulAction.toEndHom

def baseToPermNormalWord : H →* Equiv.Perm (NormalWord φ) :=
  @MulAction.toPermHom _ _ _ (MulAction.ofEndHom baseToEndNormalWord)

theorem baseToPermNormalWord_apply (h : H) :
  (baseToPermNormalWord h : NormalWord φ → NormalWord φ) =
    fun w => { w with left := h * w.left } := rfl

@[simp]
theorem summandToPermNormalWord_app_eq_base {i : ι} (h : H) (w : NormalWord φ) :
    summandToPermNormalWord hφ i (φ i h) w = baseToPermNormalWord h w := by
  apply ext_smul hφ i
  simp only [summandToPermNormalWord_apply, equivPair, rcons, Word.equivPair_symm, Equiv.coe_fn_mk,
    Equiv.coe_fn_symm_mk, Word.rcons_eq_smul, baseToPermNormalWord_apply,
    Word.equivPair_smul_same, ← mul_smul, ← map_mul, Word.smul_eq_of_smul,
    normalizeSingle_fst_mul_normalizeSingle_snd]
  simp only [map_mul, mul_smul, Word.equivPair_head_smul_equivPair_tail]

noncomputable def toPermNormalWord [DecidableEq ι] [∀ i, DecidableEq (G i)] :
    AmalgamatedProduct φ →* Equiv.Perm (NormalWord φ) :=
  lift (summandToPermNormalWord hφ) baseToPermNormalWord (by intros; ext <;> simp)

@[elab_as_elim]
noncomputable def consRecOn {motive : NormalWord φ → Sort _} (w : NormalWord φ)
    (h_empty : motive empty)
    (h_cons : ∀ (i : ι) (g : G i) (w : NormalWord φ) (hmw : w.fstIdx ≠ some i)
      (_hgn : (normalizeSingle φ g).2 = g)
      (hgr : g ∉ (φ i).range) (_hw1 : w.left = 1),
      motive w →  motive (cons hφ g w hmw hgr))
    (h_base : ∀ (h : H) (w : NormalWord φ), w.left = 1 → motive w → motive (h • w)) :
      motive w := by
  rcases w with ⟨w, left, h3⟩
  convert h_base left ⟨w, 1, h3⟩ rfl ?_
  · simp [base_smul_def]
  · induction w using Word.consRecOn with
    | h_empty => exact h_empty
    | h_cons i g w h1 hg1 ih =>
      convert h_cons i g ⟨w, 1, fun _ _ h => h3 _ _ (List.mem_cons_of_mem _ h)⟩
        h1 (h3 _ _ (List.mem_cons_self _ _)) ?_ rfl
        (ih ?_)
      · ext; simp [Word.cons, cons, h3 _ _ (List.mem_cons_self _ _)]
      · apply hφ i
        simp [cons, normalizeSingle_fst_eq, h3 _ _ (List.mem_cons_self _ _)]
      · rwa [← mem_range_iff_normalizeSingle_snd_eq_one hφ,
          h3 _ _ (List.mem_cons_self _ _)]

def prod (w : NormalWord φ) : AmalgamatedProduct φ :=
  base w.left * ofCoprodI (w.toWord).prod

theorem cons_eq_summandToPermNormalWord {i : ι} (g : G i) (w : NormalWord φ) (hmw : w.fstIdx ≠ some i)
    (hgr : g ∉ (φ i).range) : cons hφ g w hmw hgr = summandToPermNormalWord hφ i g w := by
  apply ext_smul hφ i
  simp only [cons, ne_eq, Word.cons_eq_smul, summandToPermNormalWord_apply, equivPair, rcons,
    Word.equivPair_symm, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, Word.rcons_eq_smul]
  simp only [← mul_smul, ← map_mul, normalizeSingle_fst_mul_normalizeSingle_snd]
  simp only [mul_smul, map_mul, Word.equivPair_head_smul_equivPair_tail]

theorem prod_summandToPermNormalWord {i : ι} (g : G i) (w : NormalWord φ) :
    (summandToPermNormalWord hφ i g w).prod = of g * w.prod :=
  calc (summandToPermNormalWord hφ i g w).prod =
    ((equivPair hφ i).symm
      { equivPair hφ i w with head := g * (equivPair hφ i w).head }).prod := rfl
    _ = of (g * (φ i) w.left * ((Word.equivPair i) w.toWord).head) *
        ofCoprodI (Word.prod ((Word.equivPair i) w.toWord).tail) := by
      simp only [prod, rcons, equivPair, Word.rcons_eq_smul, Word.equivPair_symm,
        Word.prod_smul, Word.equivPair_smul_same]
      dsimp
      simp only [Word.prod_smul, map_mul, ofCoprodI_of, ← mul_assoc]
      simp only [← of_apply_eq_base i, ← map_mul, normalizeSingle_fst_mul_normalizeSingle_snd]
    _ = of g * of ((φ i) w.left) * ofCoprodI
        (CoprodI.of ((Word.equivPair i) w.toWord).head *
          Word.prod ((Word.equivPair i) w.toWord).tail) := by
      rw [map_mul, map_mul, map_mul, ofCoprodI_of, mul_assoc]
    _ = _ := by
      rw [← Word.prod_smul, Word.equivPair_head_smul_equivPair_tail, prod, mul_assoc,
        of_apply_eq_base]

theorem prod_baseToPermNormalWord (h : H) (w : NormalWord φ) :
    (baseToPermNormalWord h w).prod = base h * w.prod := by
  simp only [baseToPermNormalWord_apply, prod, map_mul, mul_assoc]

theorem prod_toPermNormalWord (g : AmalgamatedProduct φ) (w : NormalWord φ) :
    (toPermNormalWord hφ g w).prod = g * w.prod := by
  induction g using AmalgamatedProduct.induction_on generalizing w with
  | of i g => rw [toPermNormalWord, lift_of, prod_summandToPermNormalWord]
  | base h => rw [toPermNormalWord, lift_base, prod_baseToPermNormalWord]
  | mul x y ihx ihy => rw [map_mul, Equiv.Perm.mul_apply, ihx, ihy, mul_assoc]

@[simp]
theorem prod_empty : (empty : NormalWord φ).prod = 1 := by
  simp [prod, empty]

@[simp]
theorem prod_cons {i} (g : G i) (w : NormalWord φ) (hmw : w.fstIdx ≠ some i)
    (hgr : g ∉ (φ i).range) : (cons hφ g w hmw hgr).prod = of g * w.prod := by
  simp only [prod, cons, Word.prod, Word.cons, List.prod_cons,
    List.map_cons, map_mul, ofCoprodI_of, ← mul_assoc,
    ← of_apply_eq_base i, normalizeSingle_fst_eq φ]
  simp only [mul_assoc, ← map_mul, ← map_inv, inv_mul_self, mul_one]

noncomputable def equiv : AmalgamatedProduct φ ≃ NormalWord φ :=
  { toFun := fun g => toPermNormalWord hφ g .empty
    invFun := fun w => w.prod
    left_inv := fun g => by
      simp only [prod_toPermNormalWord, prod_empty, mul_one]
    right_inv := by
      intro w
      dsimp
      refine consRecOn hφ w ?_ ?_ ?_
      · simp
      · intro i g w _ _ _ _ ih
        rw [prod_cons, map_mul, Equiv.Perm.mul_apply, ih,
          cons_eq_summandToPermNormalWord, toPermNormalWord, lift_of]
      · intro h w hw1 ih
        rw [prod] at ih
        simp_all [toPermNormalWord, base_smul_def, lift_base,
          map_mul, prod, map_one, mul_one, ih, hw1,
          baseToPermNormalWord] }

theorem prod_injective : Function.Injective (prod : NormalWord φ → AmalgamatedProduct φ) := by
  letI := Classical.decEq ι
  letI := fun i => Classical.decEq (G i)
  classical exact (equiv hφ).symm.injective

end NormalWord

open NormalWord

theorem of_injective (hφ : ∀ i, Function.Injective (φ i)) (i : ι) :
    Function.Injective (of (φ := φ) (i := i)) := by
  let _ := Classical.decEq ι
  let _ := fun i => Classical.decEq (G i)
  refine Function.Injective.of_comp (f := toPermNormalWord hφ) ?_
  simp only [Function.comp, toPermNormalWord, lift_of]
  exact summandToPermNormalWord_injective hφ

section Reduced

open NormalWord

variable (φ)

def Reduced (w : Word G) : Prop :=
  ∀ i g, ⟨i, g⟩ ∈ w.toList → g ∉ (φ i).range

variable {φ} (hφ : ∀ _i, Function.Injective (φ _i))

theorem Reduced.exists_normalWord_prod_eq {w : Word G} (hw : Reduced φ w) :
    ∃ w' : NormalWord φ, w'.prod = ofCoprodI w.prod ∧
      w'.toList.map Sigma.fst = w.toList.map Sigma.fst := by
  letI := Classical.decEq ι
  letI := fun i => Classical.decEq (G i)
  induction w using Word.consRecOn with
  | h_empty => exact ⟨empty, by simp, rfl⟩
  | h_cons i g w hIdx hg1 ih =>
    rcases ih (fun _ _ hg => hw _ _ (List.mem_cons_of_mem _ hg)) with
      ⟨w', hw'prod, hw'map⟩
    refine ⟨cons hφ g w' ?_ ?_, ?_⟩
    · rwa [Word.fstIdx, ← List.head?_map, hw'map, List.head?_map]
    · exact hw _ _ (List.mem_cons_self _ _)
    · simp [hw'prod, hw'map]

theorem Reduced.eq_empty_of_mem_range {w : Word G} (hw : Reduced φ w) :
    ofCoprodI w.prod ∈ (base (φ := φ)).range → w = .empty := by
  rcases hw.exists_normalWord_prod_eq hφ with ⟨w', hw'prod, hw'map⟩
  rintro ⟨h, heq⟩
  have : (NormalWord.prod (G:=G) (φ := φ) ⟨.empty, h, by simp⟩) = base h := by
    simp [NormalWord.prod]
  rw [← hw'prod, ← this] at heq
  suffices : w'.toWord = .empty
  · simp [this, @eq_comm _ []] at hw'map
    ext
    simp [hw'map]
  · rw [← prod_injective hφ heq]

end Reduced

end AmalgamatedProduct
