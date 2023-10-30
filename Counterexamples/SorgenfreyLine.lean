/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.Instances.Irrational
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Data.Set.Intervals.Monotone
import Mathlib.Topology.Separation.NotNormal

#align_import sorgenfrey_line from "leanprover-community/mathlib"@"328375597f2c0dd00522d9c2e5a33b6a6128feeb"

/-!
# Sorgenfrey line

In this file we define `SorgenfreyLine` (notation: `ℝₗ`) to be the Sorgenfrey line. It is the real
line with the topology space structure generated by half-open intervals `Set.Ico a b`.

We prove that this line is a completely normal Hausdorff space but its product with itself is not a
normal space. In particular, this implies that the topology on `ℝₗ` is neither metrizable, nor
second countable.

## Notations

- `ℝₗ`: Sorgenfrey line.

## TODO

Prove that the Sorgenfrey line is a paracompact space.

-/


open Set Filter TopologicalSpace

open scoped Topology Filter Cardinal

namespace Counterexample

noncomputable section

/-- The Sorgenfrey line. It is the real line with the topology space structure generated by
half-open intervals `Set.Ico a b`. -/
def SorgenfreyLine : Type := ℝ
-- porting note: was deriving ConditionallyCompleteLinearOrder, LinearOrderedField, Archimedean
#align counterexample.sorgenfrey_line Counterexample.SorgenfreyLine

scoped[SorgenfreyLine] notation "ℝₗ" => Counterexample.SorgenfreyLine
open scoped SorgenfreyLine

instance : ConditionallyCompleteLinearOrder ℝₗ :=
  inferInstanceAs (ConditionallyCompleteLinearOrder ℝ)

instance : LinearOrderedField ℝₗ := inferInstanceAs (LinearOrderedField ℝ)

instance : Archimedean ℝₗ := inferInstanceAs (Archimedean ℝ)

namespace SorgenfreyLine

/-- Ring homomorphism between the Sorgenfrey line and the standard real line. -/
def toReal : ℝₗ ≃+* ℝ :=
  RingEquiv.refl ℝ
#align counterexample.sorgenfrey_line.to_real Counterexample.SorgenfreyLine.toReal

instance : TopologicalSpace ℝₗ :=
  TopologicalSpace.generateFrom {s : Set ℝₗ | ∃ a b : ℝₗ, Ico a b = s}

theorem isOpen_Ico (a b : ℝₗ) : IsOpen (Ico a b) :=
  TopologicalSpace.GenerateOpen.basic _ ⟨a, b, rfl⟩
#align counterexample.sorgenfrey_line.is_open_Ico Counterexample.SorgenfreyLine.isOpen_Ico

theorem isOpen_Ici (a : ℝₗ) : IsOpen (Ici a) :=
  iUnion_Ico_right a ▸ isOpen_iUnion (isOpen_Ico a)
#align counterexample.sorgenfrey_line.is_open_Ici Counterexample.SorgenfreyLine.isOpen_Ici

theorem nhds_basis_Ico (a : ℝₗ) : (𝓝 a).HasBasis (a < ·) (Ico a ·) := by
  rw [TopologicalSpace.nhds_generateFrom]
  haveI : Nonempty { x // x ≤ a } := Set.nonempty_Iic_subtype
  have : (⨅ x : { i // i ≤ a }, 𝓟 (Ici ↑x)) = 𝓟 (Ici a) := by
    refine' (IsLeast.isGLB _).iInf_eq
    exact ⟨⟨⟨a, le_rfl⟩, rfl⟩, forall_range_iff.2 fun b => principal_mono.2 <| Ici_subset_Ici.2 b.2⟩
  simp only [mem_setOf_eq, iInf_and, iInf_exists, @iInf_comm _ (_ ∈ _), @iInf_comm _ (Set ℝₗ),
    iInf_iInf_eq_right, mem_Ico]
  simp_rw [@iInf_comm _ ℝₗ (_ ≤ _), iInf_subtype', ← Ici_inter_Iio, ← inf_principal,
    ← inf_iInf, ← iInf_inf, this, iInf_subtype]
  suffices : (⨅ x ∈ Ioi a, 𝓟 (Iio x)).HasBasis (a < ·) Iio; exact this.principal_inf _
  refine' hasBasis_biInf_principal _ nonempty_Ioi
  exact directedOn_iff_directed.2 <| Monotone.directed_ge fun x y hxy ↦ Iio_subset_Iio hxy
#align counterexample.sorgenfrey_line.nhds_basis_Ico Counterexample.SorgenfreyLine.nhds_basis_Ico

theorem nhds_basis_Ico_rat (a : ℝₗ) :
    (𝓝 a).HasCountableBasis (fun r : ℚ => a < r) fun r => Ico a r := by
  refine' ⟨(nhds_basis_Ico a).to_hasBasis (fun b hb => _) fun r hr => ⟨_, hr, Subset.rfl⟩,
    Set.to_countable _⟩
  rcases exists_rat_btwn hb with ⟨r, har, hrb⟩
  exact ⟨r, har, Ico_subset_Ico_right hrb.le⟩
#align counterexample.sorgenfrey_line.nhds_basis_Ico_rat Counterexample.SorgenfreyLine.nhds_basis_Ico_rat

theorem nhds_basis_Ico_inv_pnat (a : ℝₗ) :
    (𝓝 a).HasBasis (fun _ : ℕ+ => True) fun n => Ico a (a + (n : ℝₗ)⁻¹) := by
  refine' (nhds_basis_Ico a).to_hasBasis (fun b hb => _) fun n hn =>
    ⟨_, lt_add_of_pos_right _ (inv_pos.2 <| Nat.cast_pos.2 n.pos), Subset.rfl⟩
  rcases exists_nat_one_div_lt (sub_pos.2 hb) with ⟨k, hk⟩
  rw [one_div] at hk
  rw [← Nat.cast_add_one] at hk
  exact ⟨k.succPNat, trivial, Ico_subset_Ico_right (le_sub_iff_add_le'.1 hk.le)⟩
#align counterexample.sorgenfrey_line.nhds_basis_Ico_inv_pnat Counterexample.SorgenfreyLine.nhds_basis_Ico_inv_pnat

theorem nhds_countable_basis_Ico_inv_pnat (a : ℝₗ) :
    (𝓝 a).HasCountableBasis (fun _ : ℕ+ => True) fun n => Ico a (a + (n : ℝₗ)⁻¹) :=
  ⟨nhds_basis_Ico_inv_pnat a, Set.to_countable _⟩
#align counterexample.sorgenfrey_line.nhds_countable_basis_Ico_inv_pnat Counterexample.SorgenfreyLine.nhds_countable_basis_Ico_inv_pnat

theorem nhds_antitone_basis_Ico_inv_pnat (a : ℝₗ) :
    (𝓝 a).HasAntitoneBasis fun n : ℕ+ => Ico a (a + (n : ℝₗ)⁻¹) :=
  ⟨nhds_basis_Ico_inv_pnat a, monotone_const.Ico <| Antitone.const_add
    (fun k _l hkl => inv_le_inv_of_le (Nat.cast_pos.2 k.2)
      (Nat.mono_cast $ Subtype.coe_le_coe.2 hkl)) _⟩
#align counterexample.sorgenfrey_line.nhds_antitone_basis_Ico_inv_pnat Counterexample.SorgenfreyLine.nhds_antitone_basis_Ico_inv_pnat

theorem isOpen_iff {s : Set ℝₗ} : IsOpen s ↔ ∀ x ∈ s, ∃ y > x, Ico x y ⊆ s :=
  isOpen_iff_mem_nhds.trans <| forall₂_congr fun x _ => (nhds_basis_Ico x).mem_iff
#align counterexample.sorgenfrey_line.is_open_iff Counterexample.SorgenfreyLine.isOpen_iff

theorem isClosed_iff {s : Set ℝₗ} : IsClosed s ↔ ∀ x, x ∉ s → ∃ y > x, Disjoint (Ico x y) s := by
  simp only [← isOpen_compl_iff, isOpen_iff, mem_compl_iff, subset_compl_iff_disjoint_right]
#align counterexample.sorgenfrey_line.is_closed_iff Counterexample.SorgenfreyLine.isClosed_iff

theorem exists_Ico_disjoint_closed {a : ℝₗ} {s : Set ℝₗ} (hs : IsClosed s) (ha : a ∉ s) :
    ∃ b > a, Disjoint (Ico a b) s :=
  isClosed_iff.1 hs a ha
#align counterexample.sorgenfrey_line.exists_Ico_disjoint_closed Counterexample.SorgenfreyLine.exists_Ico_disjoint_closed

@[simp]
theorem map_toReal_nhds (a : ℝₗ) : map toReal (𝓝 a) = 𝓝[≥] toReal a := by
  refine' ((nhds_basis_Ico a).map _).eq_of_same_basis _
  simpa only [toReal.image_eq_preimage] using nhdsWithin_Ici_basis_Ico (toReal a)
#align counterexample.sorgenfrey_line.map_to_real_nhds Counterexample.SorgenfreyLine.map_toReal_nhds

theorem nhds_eq_map (a : ℝₗ) : 𝓝 a = map toReal.symm (𝓝[≥] (toReal a)) := by
  simp_rw [← map_toReal_nhds, map_map, (· ∘ ·), toReal.symm_apply_apply, map_id']
#align counterexample.sorgenfrey_line.nhds_eq_map Counterexample.SorgenfreyLine.nhds_eq_map

theorem nhds_eq_comap (a : ℝₗ) : 𝓝 a = comap toReal (𝓝[≥] (toReal a)) := by
  rw [← map_toReal_nhds, comap_map toReal.injective]
#align counterexample.sorgenfrey_line.nhds_eq_comap Counterexample.SorgenfreyLine.nhds_eq_comap

@[continuity]
theorem continuous_toReal : Continuous toReal :=
  continuous_iff_continuousAt.2 fun x => by
    rw [ContinuousAt, Tendsto, map_toReal_nhds]
    exact inf_le_left
#align counterexample.sorgenfrey_line.continuous_to_real Counterexample.SorgenfreyLine.continuous_toReal

instance : OrderClosedTopology ℝₗ :=
  ⟨isClosed_le_prod.preimage (continuous_toReal.prod_map continuous_toReal)⟩

instance : ContinuousAdd ℝₗ := by
  refine' ⟨continuous_iff_continuousAt.2 _⟩
  rintro ⟨x, y⟩
  rw [ContinuousAt, nhds_prod_eq, nhds_eq_comap (x + y), tendsto_comap_iff,
    nhds_eq_map, nhds_eq_map, prod_map_map_eq, ← nhdsWithin_prod_eq, Ici_prod_Ici]
  exact (continuous_add.tendsto _).inf (MapsTo.tendsto fun x hx => add_le_add hx.1 hx.2)

theorem isClopen_Ici (a : ℝₗ) : IsClopen (Ici a) :=
  ⟨isOpen_Ici a, isClosed_Ici⟩
#align counterexample.sorgenfrey_line.is_clopen_Ici Counterexample.SorgenfreyLine.isClopen_Ici

theorem isClopen_Iio (a : ℝₗ) : IsClopen (Iio a) := by
  simpa only [compl_Ici] using (isClopen_Ici a).compl
#align counterexample.sorgenfrey_line.is_clopen_Iio Counterexample.SorgenfreyLine.isClopen_Iio

theorem isClopen_Ico (a b : ℝₗ) : IsClopen (Ico a b) :=
  (isClopen_Ici a).inter (isClopen_Iio b)
#align counterexample.sorgenfrey_line.is_clopen_Ico Counterexample.SorgenfreyLine.isClopen_Ico

instance : TotallyDisconnectedSpace ℝₗ :=
  ⟨fun _ _ hs x hx y hy =>
    le_antisymm (hs.subset_clopen (isClopen_Ici x) ⟨x, hx, left_mem_Ici⟩ hy)
      (hs.subset_clopen (isClopen_Ici y) ⟨y, hy, left_mem_Ici⟩ hx)⟩

instance : FirstCountableTopology ℝₗ :=
  ⟨fun x => (nhds_basis_Ico_rat x).isCountablyGenerated⟩

/-- Sorgenfrey line is a completely normal Hausdorff topological space. -/
instance : T5Space ℝₗ := by
  /-
  Let `s` and `t` be disjoint closed sets.
  For each `x ∈ s` we choose `X x` such that `Set.Ico x (X x)` is disjoint with `t`.
  Similarly, for each `y ∈ t` we choose `Y y` such that `Set.Ico y (Y y)` is disjoint with `s`.
  Then `⋃ x ∈ s, Ico x (X x)` and `⋃ y ∈ t, Ico y (Y y)` are
  disjoint open sets that include `s` and `t`.
  -/
  refine' ⟨fun s t hd₁ hd₂ => _⟩
  choose! X hX hXd using fun x (hx : x ∈ s) =>
    exists_Ico_disjoint_closed isClosed_closure (disjoint_left.1 hd₂ hx)
  choose! Y hY hYd using fun y (hy : y ∈ t) =>
    exists_Ico_disjoint_closed isClosed_closure (disjoint_right.1 hd₁ hy)
  refine' disjoint_of_disjoint_of_mem _
    (bUnion_mem_nhdsSet fun x hx => (isOpen_Ico x (X x)).mem_nhds <| left_mem_Ico.2 (hX x hx))
    (bUnion_mem_nhdsSet fun y hy => (isOpen_Ico y (Y y)).mem_nhds <| left_mem_Ico.2 (hY y hy))
  simp only [disjoint_iUnion_left, disjoint_iUnion_right, Ico_disjoint_Ico]
  intro y hy x hx
  cases' le_total x y with hle hle
  · calc
      min (X x) (Y y) ≤ X x := min_le_left _ _
      _ ≤ y := (not_lt.1 fun hyx => (hXd x hx).le_bot ⟨⟨hle, hyx⟩, subset_closure hy⟩)
      _ ≤ max x y := le_max_right _ _
  · calc
      min (X x) (Y y) ≤ Y y := min_le_right _ _
      _ ≤ x := (not_lt.1 fun hxy => (hYd y hy).le_bot ⟨⟨hle, hxy⟩, subset_closure hx⟩)
      _ ≤ max x y := le_max_left _ _

theorem denseRange_coe_rat : DenseRange ((↑) : ℚ → ℝₗ) := by
  refine' dense_iff_inter_open.2 _
  rintro U Uo ⟨x, hx⟩
  rcases isOpen_iff.1 Uo _ hx with ⟨y, hxy, hU⟩
  rcases exists_rat_btwn hxy with ⟨z, hxz, hzy⟩
  exact ⟨z, hU ⟨hxz.le, hzy⟩, mem_range_self _⟩
#align counterexample.sorgenfrey_line.dense_range_coe_rat Counterexample.SorgenfreyLine.denseRange_coe_rat

instance : SeparableSpace ℝₗ :=
  ⟨⟨_, countable_range _, denseRange_coe_rat⟩⟩

theorem isClosed_antidiagonal (c : ℝₗ) : IsClosed {x : ℝₗ × ℝₗ | x.1 + x.2 = c} :=
  isClosed_singleton.preimage continuous_add
#align counterexample.sorgenfrey_line.is_closed_antidiagonal Counterexample.SorgenfreyLine.isClosed_antidiagonal

theorem isClopen_Ici_prod (x : ℝₗ × ℝₗ) : IsClopen (Ici x) :=
  (Ici_prod_eq x).symm ▸ (isClopen_Ici _).prod (isClopen_Ici _)
#align counterexample.sorgenfrey_line.is_clopen_Ici_prod Counterexample.SorgenfreyLine.isClopen_Ici_prod

theorem cardinal_antidiagonal (c : ℝₗ) : #{x : ℝₗ × ℝₗ | x.1 + x.2 = c} = 𝔠 := by
  rw [← Cardinal.mk_real]
  exact Equiv.cardinal_eq ⟨fun x ↦ toReal x.1.1,
    fun x ↦ ⟨(toReal.symm x, c - toReal.symm x), by simp⟩,
    fun ⟨x, hx⟩ ↦ by ext <;> simp [← hx.out], fun x ↦ rfl⟩

/-- Any subset of an antidiagonal `{(x, y) : ℝₗ × ℝₗ| x + y = c}` is a closed set. -/
theorem isClosed_of_subset_antidiagonal {s : Set (ℝₗ × ℝₗ)} {c : ℝₗ} (hs : ∀ x ∈ s, x.1 + x.2 = c) :
    IsClosed s := by
  rw [← closure_subset_iff_isClosed]
  rintro ⟨x, y⟩ H
  obtain rfl : x + y = c := by
    change (x, y) ∈ {p : ℝₗ × ℝₗ | p.1 + p.2 = c}
    exact closure_minimal (hs : s ⊆ {x | x.1 + x.2 = c}) (isClosed_antidiagonal c) H
  rcases mem_closure_iff.1 H (Ici (x, y)) (isClopen_Ici_prod _).1 left_mem_Ici with
    ⟨⟨x', y'⟩, ⟨hx : x ≤ x', hy : y ≤ y'⟩, H⟩
  convert H
  · refine' hx.antisymm _
    rwa [← add_le_add_iff_right, hs _ H, add_le_add_iff_left]
  · refine' hy.antisymm _
    rwa [← add_le_add_iff_left, hs _ H, add_le_add_iff_right]
#align counterexample.sorgenfrey_line.is_closed_of_subset_antidiagonal Counterexample.SorgenfreyLine.isClosed_of_subset_antidiagonal

open Subtype in
instance (c : ℝₗ) : DiscreteTopology {x : ℝₗ × ℝₗ | x.1 + x.2 = c} :=
  forall_open_iff_discrete.1 fun U ↦ isClosed_compl_iff.1 <| isClosed_induced_iff.2
    ⟨val '' Uᶜ, isClosed_of_subset_antidiagonal <| coe_image_subset _ Uᶜ,
      preimage_image_eq _ val_injective⟩

/-- The Sorgenfrey plane `ℝₗ × ℝₗ` is not a normal space. -/
theorem not_normalSpace_prod : ¬NormalSpace (ℝₗ × ℝₗ) :=
  (isClosed_antidiagonal 0).not_normal_of_continuum_le_mk (cardinal_antidiagonal _).ge
#align counterexample.sorgenfrey_line.not_normal_space_prod Counterexample.SorgenfreyLine.not_normalSpace_prod

/-- An antidiagonal is a separable set but is not a separable space. -/
theorem isSeparable_antidiagonal (c : ℝₗ) : IsSeparable {x : ℝₗ × ℝₗ | x.1 + x.2 = c} :=
  isSeparable_of_separableSpace _

/-- An antidiagonal is a separable set but is not a separable space. -/
theorem not_separableSpace_antidiagonal (c : ℝₗ) :
    ¬SeparableSpace {x : ℝₗ × ℝₗ | x.1 + x.2 = c} := by
  rw [separableSpace_iff_countable, ← Cardinal.mk_le_aleph0_iff, cardinal_antidiagonal, not_le]
  exact Cardinal.aleph0_lt_continuum

theorem nhds_prod_antitone_basis_inv_pnat (x y : ℝₗ) :
    (𝓝 (x, y)).HasAntitoneBasis fun n : ℕ+ => Ico x (x + (n : ℝₗ)⁻¹) ×ˢ Ico y (y + (n : ℝₗ)⁻¹) := by
  rw [nhds_prod_eq]
  exact (nhds_antitone_basis_Ico_inv_pnat x).prod (nhds_antitone_basis_Ico_inv_pnat y)
#align counterexample.sorgenfrey_line.nhds_prod_antitone_basis_inv_pnat Counterexample.SorgenfreyLine.nhds_prod_antitone_basis_inv_pnat

/-- The sets of rational and irrational points of the antidiagonal `{(x, y) | x + y = 0}` cannot be
separated by open neighborhoods. This implies that `ℝₗ × ℝₗ` is not a normal space. -/
theorem not_separatedNhds_rat_irrational_antidiag :
    ¬SeparatedNhds {x : ℝₗ × ℝₗ | x.1 + x.2 = 0 ∧ ∃ r : ℚ, ↑r = x.1}
    {x : ℝₗ × ℝₗ | x.1 + x.2 = 0 ∧ Irrational (toReal x.1)} := by
  have h₀ : ∀ {n : ℕ+}, 0 < (n : ℝ)⁻¹ := inv_pos.2 (Nat.cast_pos.2 (PNat.pos _))
  have h₀' : ∀ {n : ℕ+} {x : ℝ}, x < x + (n : ℝ)⁻¹ := lt_add_of_pos_right _ h₀
  /- Let `S` be the set of points `(x, y)` on the line `x + y = 0` such that `x` is rational.
    Let `T` be the set of points `(x, y)` on the line `x + y = 0` such that `x` is irrational.
    These sets are closed, see `SorgenfreyLine.isClosed_of_subset_antidiagonal`, and disjoint. -/
  set S := {x : ℝₗ × ℝₗ | x.1 + x.2 = 0 ∧ ∃ r : ℚ, ↑r = x.1}
  set T := {x : ℝₗ × ℝₗ | x.1 + x.2 = 0 ∧ Irrational (toReal x.1)}
  -- Consider disjoint open sets `U ⊇ S` and `V ⊇ T`.
  rintro ⟨U, V, Uo, Vo, SU, TV, UV⟩
  /- For each point `(x, -x) ∈ T`, choose a neighborhood
    `Ico x (x + k⁻¹) ×ˢ Ico (-x) (-x + k⁻¹) ⊆ V`. -/
  have : ∀ x : ℝₗ, Irrational (toReal x) →
      ∃ k : ℕ+, Ico x (x + (k : ℝₗ)⁻¹) ×ˢ Ico (-x) (-x + (k : ℝₗ)⁻¹) ⊆ V := fun x hx ↦ by
    have hV : V ∈ 𝓝 (x, -x) := Vo.mem_nhds (@TV (x, -x) ⟨add_neg_self x, hx⟩)
    exact (nhds_prod_antitone_basis_inv_pnat _ _).mem_iff.1 hV
  choose! k hkV using this
  /- Since the set of irrational numbers is a dense Gδ set in the usual topology of `ℝ`, there
    exists `N > 0` such that the set `C N = {x : ℝ | Irrational x ∧ k x = N}` is dense in a nonempty
    interval. In other words, the closure of this set has a nonempty interior. -/
  set C : ℕ+ → Set ℝ := fun n => closure {x | Irrational x ∧ k (toReal.symm x) = n}
  have H : {x : ℝ | Irrational x} ⊆ ⋃ n, C n := fun x hx =>
    mem_iUnion.2 ⟨_, subset_closure ⟨hx, rfl⟩⟩
  have Hd : Dense (⋃ n, interior (C n)) :=
    isGδ_irrational.dense_iUnion_interior_of_closed dense_irrational (fun _ => isClosed_closure) H
  obtain ⟨N, hN⟩ : ∃ n : ℕ+, (interior <| C n).Nonempty; exact nonempty_iUnion.mp Hd.nonempty
  /- Choose a rational number `r` in the interior of the closure of `C N`, then choose `n ≥ N > 0`
    such that `Ico r (r + n⁻¹) × Ico (-r) (-r + n⁻¹) ⊆ U`. -/
  rcases Rat.denseRange_cast.exists_mem_open isOpen_interior hN with ⟨r, hr⟩
  have hrU : ((r, -r) : ℝₗ × ℝₗ) ∈ U := @SU (r, -r) ⟨add_neg_self _, r, rfl⟩
  obtain ⟨n, hnN, hn⟩ :
    ∃ n, N ≤ n ∧ Ico (r : ℝₗ) (r + (n : ℝₗ)⁻¹) ×ˢ Ico (-r : ℝₗ) (-r + (n : ℝₗ)⁻¹) ⊆ U
  exact ((nhds_prod_antitone_basis_inv_pnat _ _).hasBasis_ge N).mem_iff.1 (Uo.mem_nhds hrU)
  /- Finally, choose `x ∈ Ioo (r : ℝ) (r + n⁻¹) ∩ C N`. Then `(x, -r)` belongs both to `U` and `V`,
    so they are not disjoint. This contradiction completes the proof. -/
  obtain ⟨x, hxn, hx_irr, rfl⟩ :
      ∃ x : ℝ, x ∈ Ioo (r : ℝ) (r + (n : ℝ)⁻¹) ∧ Irrational x ∧ k (toReal.symm x) = N := by
    have : (r : ℝ) ∈ closure (Ioo (r : ℝ) (r + (n : ℝ)⁻¹)) := by
      rw [closure_Ioo h₀'.ne, left_mem_Icc]
      exact h₀'.le
    rcases mem_closure_iff_nhds.1 this _ (mem_interior_iff_mem_nhds.1 hr) with ⟨x', hx', hx'ε⟩
    exact mem_closure_iff.1 hx' _ isOpen_Ioo hx'ε
  refine' UV.le_bot (_ : (toReal.symm x, -(r : ℝₗ)) ∈ _)
  refine' ⟨hn ⟨_, _⟩, hkV (toReal.symm x) hx_irr ⟨_, _⟩⟩
  · exact Ioo_subset_Ico_self hxn
  · exact left_mem_Ico.2 h₀'
  · exact left_mem_Ico.2 h₀'
  · refine' (nhds_antitone_basis_Ico_inv_pnat (-x)).2 hnN ⟨neg_le_neg hxn.1.le, _⟩
    simp only [add_neg_lt_iff_le_add', lt_neg_add_iff_add_lt]
    exact hxn.2

/-- Topology on the Sorgenfrey line is not metrizable. -/
theorem not_metrizableSpace : ¬MetrizableSpace ℝₗ := by
  intro
  letI := metrizableSpaceMetric ℝₗ
  exact not_normalSpace_prod inferInstance
#align counterexample.sorgenfrey_line.not_metrizable_space Counterexample.SorgenfreyLine.not_metrizableSpace

/-- Topology on the Sorgenfrey line is not second countable. -/
theorem not_secondCountableTopology : ¬SecondCountableTopology ℝₗ :=
  fun _ ↦ not_metrizableSpace (metrizableSpace_of_t3_second_countable _)
#align counterexample.sorgenfrey_line.not_second_countable_topology Counterexample.SorgenfreyLine.not_secondCountableTopology

end SorgenfreyLine

end

end Counterexample
