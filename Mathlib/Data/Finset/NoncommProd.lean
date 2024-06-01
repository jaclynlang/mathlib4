/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Commute.Hom
import Mathlib.Data.Fintype.Card

#align_import data.finset.noncomm_prod from "leanprover-community/mathlib"@"509de852e1de55e1efa8eacfa11df0823f26f226"

/-!
# Products (respectively, sums) over a finset or a multiset.

The regular `Finset.prod` and `Multiset.prod` require `[CommMonoid α]`.
Often, there are collections `s : Finset α` where `[Monoid α]` and we know,
in a dependent fashion, that for all the terms `∀ (x ∈ s) (y ∈ s), Commute x y`.
This allows to still have a well-defined product over `s`.

## Main definitions

- `Finset.noncommProd`, requiring a proof of commutativity of held terms
- `Multiset.noncommProd`, requiring a proof of commutativity of held terms

## Implementation details

While `List.prod` is defined via `List.foldl`, `noncommProd` is defined via
`Multiset.foldr` for neater proofs and definitions. By the commutativity assumption,
the two must be equal.

TODO: Tidy up this file by using the fact that the submonoid generated by commuting
elements is commutative and using the `Finset.prod` versions of lemmas to prove the `noncommProd`
version.
-/

variable {F ι α β γ : Type*} (f : α → β → β) (op : α → α → α)

namespace Multiset

/-- Fold of a `s : Multiset α` with `f : α → β → β`, given a proof that `LeftCommutative f`
on all elements `x ∈ s`. -/
def noncommFoldr (s : Multiset α)
    (comm : { x | x ∈ s }.Pairwise fun x y => ∀ b, f x (f y b) = f y (f x b)) (b : β) : β :=
  s.attach.foldr (f ∘ Subtype.val)
    (fun ⟨_, hx⟩ ⟨_, hy⟩ =>
      haveI : IsRefl α fun x y => ∀ b, f x (f y b) = f y (f x b) := ⟨fun _ _ => rfl⟩
      comm.of_refl hx hy)
    b
#align multiset.noncomm_foldr Multiset.noncommFoldr

@[simp]
theorem noncommFoldr_coe (l : List α) (comm) (b : β) :
    noncommFoldr f (l : Multiset α) comm b = l.foldr f b := by
  simp only [noncommFoldr, coe_foldr, coe_attach, List.attach, List.attachWith, Function.comp]
  rw [← List.foldr_map]
  simp [List.map_pmap]
#align multiset.noncomm_foldr_coe Multiset.noncommFoldr_coe

@[simp]
theorem noncommFoldr_empty (h) (b : β) : noncommFoldr f (0 : Multiset α) h b = b :=
  rfl
#align multiset.noncomm_foldr_empty Multiset.noncommFoldr_empty

theorem noncommFoldr_cons (s : Multiset α) (a : α) (h h') (b : β) :
    noncommFoldr f (a ::ₘ s) h b = f a (noncommFoldr f s h' b) := by
  induction s using Quotient.inductionOn
  simp
#align multiset.noncomm_foldr_cons Multiset.noncommFoldr_cons

theorem noncommFoldr_eq_foldr (s : Multiset α) (h : LeftCommutative f) (b : β) :
    noncommFoldr f s (fun x _ y _ _ => h x y) b = foldr f h b s := by
  induction s using Quotient.inductionOn
  simp
#align multiset.noncomm_foldr_eq_foldr Multiset.noncommFoldr_eq_foldr

section assoc

variable [assoc : Std.Associative op]

/-- Fold of a `s : Multiset α` with an associative `op : α → α → α`, given a proofs that `op`
is commutative on all elements `x ∈ s`. -/
def noncommFold (s : Multiset α) (comm : { x | x ∈ s }.Pairwise fun x y => op x y = op y x) :
    α → α :=
  noncommFoldr op s fun x hx y hy h b => by rw [← assoc.assoc, comm hx hy h, assoc.assoc]
#align multiset.noncomm_fold Multiset.noncommFold

@[simp]
theorem noncommFold_coe (l : List α) (comm) (a : α) :
    noncommFold op (l : Multiset α) comm a = l.foldr op a := by simp [noncommFold]
#align multiset.noncomm_fold_coe Multiset.noncommFold_coe

@[simp]
theorem noncommFold_empty (h) (a : α) : noncommFold op (0 : Multiset α) h a = a :=
  rfl
#align multiset.noncomm_fold_empty Multiset.noncommFold_empty

theorem noncommFold_cons (s : Multiset α) (a : α) (h h') (x : α) :
    noncommFold op (a ::ₘ s) h x = op a (noncommFold op s h' x) := by
  induction s using Quotient.inductionOn
  simp
#align multiset.noncomm_fold_cons Multiset.noncommFold_cons

theorem noncommFold_eq_fold (s : Multiset α) [Std.Commutative op] (a : α) :
    noncommFold op s (fun x _ y _ _ => Std.Commutative.comm x y) a = fold op a s := by
  induction s using Quotient.inductionOn
  simp
#align multiset.noncomm_fold_eq_fold Multiset.noncommFold_eq_fold

end assoc

variable [Monoid α] [Monoid β]

/-- Product of a `s : Multiset α` with `[Monoid α]`, given a proof that `*` commutes
on all elements `x ∈ s`. -/
@[to_additive
      "Sum of a `s : Multiset α` with `[AddMonoid α]`, given a proof that `+` commutes
      on all elements `x ∈ s`."]
def noncommProd (s : Multiset α) (comm : { x | x ∈ s }.Pairwise Commute) : α :=
  s.noncommFold (· * ·) comm 1
#align multiset.noncomm_prod Multiset.noncommProd
#align multiset.noncomm_sum Multiset.noncommSum

@[to_additive (attr := simp)]
theorem noncommProd_coe (l : List α) (comm) : noncommProd (l : Multiset α) comm = l.prod := by
  rw [noncommProd]
  simp only [noncommFold_coe]
  induction' l with hd tl hl
  · simp
  · rw [List.prod_cons, List.foldr, hl]
    intro x hx y hy
    exact comm (List.mem_cons_of_mem _ hx) (List.mem_cons_of_mem _ hy)
#align multiset.noncomm_prod_coe Multiset.noncommProd_coe
#align multiset.noncomm_sum_coe Multiset.noncommSum_coe

@[to_additive (attr := simp)]
theorem noncommProd_empty (h) : noncommProd (0 : Multiset α) h = 1 :=
  rfl
#align multiset.noncomm_prod_empty Multiset.noncommProd_empty
#align multiset.noncomm_sum_empty Multiset.noncommSum_empty

@[to_additive (attr := simp)]
theorem noncommProd_cons (s : Multiset α) (a : α) (comm) :
    noncommProd (a ::ₘ s) comm = a * noncommProd s (comm.mono fun _ => mem_cons_of_mem) := by
  induction s using Quotient.inductionOn
  simp
#align multiset.noncomm_prod_cons Multiset.noncommProd_cons
#align multiset.noncomm_sum_cons Multiset.noncommSum_cons

@[to_additive]
theorem noncommProd_cons' (s : Multiset α) (a : α) (comm) :
    noncommProd (a ::ₘ s) comm = noncommProd s (comm.mono fun _ => mem_cons_of_mem) * a := by
  induction' s using Quotient.inductionOn with s
  simp only [quot_mk_to_coe, cons_coe, noncommProd_coe, List.prod_cons]
  induction' s with hd tl IH
  · simp
  · rw [List.prod_cons, mul_assoc, ← IH, ← mul_assoc, ← mul_assoc]
    · congr 1
      apply comm.of_refl <;> simp
    · intro x hx y hy
      simp only [quot_mk_to_coe, List.mem_cons, mem_coe, cons_coe] at hx hy
      apply comm
      · cases hx <;> simp [*]
      · cases hy <;> simp [*]
#align multiset.noncomm_prod_cons' Multiset.noncommProd_cons'
#align multiset.noncomm_sum_cons' Multiset.noncommSum_cons'

@[to_additive]
theorem noncommProd_add (s t : Multiset α) (comm) :
    noncommProd (s + t) comm =
      noncommProd s (comm.mono <| subset_of_le <| s.le_add_right t) *
        noncommProd t (comm.mono <| subset_of_le <| t.le_add_left s) := by
  rcases s with ⟨⟩
  rcases t with ⟨⟩
  simp
#align multiset.noncomm_prod_add Multiset.noncommProd_add
#align multiset.noncomm_sum_add Multiset.noncommSum_add

@[to_additive]
lemma noncommProd_induction (s : Multiset α) (comm)
    (p : α → Prop) (hom : ∀ a b, p a → p b → p (a * b)) (unit : p 1) (base : ∀ x ∈ s, p x) :
    p (s.noncommProd comm) := by
  induction' s using Quotient.inductionOn with l
  simp only [quot_mk_to_coe, noncommProd_coe, mem_coe] at base ⊢
  exact l.prod_induction p hom unit base

variable [FunLike F α β]

@[to_additive]
protected theorem noncommProd_map_aux [MonoidHomClass F α β] (s : Multiset α)
    (comm : { x | x ∈ s }.Pairwise Commute) (f : F) : { x | x ∈ s.map f }.Pairwise Commute := by
  simp only [Multiset.mem_map]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _
  exact (comm.of_refl hx hy).map f
#align multiset.noncomm_prod_map_aux Multiset.noncommProd_map_aux
#align multiset.noncomm_sum_map_aux Multiset.noncommSum_map_aux

@[to_additive]
theorem noncommProd_map [MonoidHomClass F α β] (s : Multiset α) (comm) (f : F) :
    f (s.noncommProd comm) = (s.map f).noncommProd (Multiset.noncommProd_map_aux s comm f) := by
  induction s using Quotient.inductionOn
  simpa using map_list_prod f _
#align multiset.noncomm_prod_map Multiset.noncommProd_map
#align multiset.noncomm_sum_map Multiset.noncommSum_map

@[to_additive noncommSum_eq_card_nsmul]
theorem noncommProd_eq_pow_card (s : Multiset α) (comm) (m : α) (h : ∀ x ∈ s, x = m) :
    s.noncommProd comm = m ^ Multiset.card s := by
  induction s using Quotient.inductionOn
  simp only [quot_mk_to_coe, noncommProd_coe, coe_card, mem_coe] at *
  exact List.prod_eq_pow_card _ m h
#align multiset.noncomm_prod_eq_pow_card Multiset.noncommProd_eq_pow_card
#align multiset.noncomm_sum_eq_card_nsmul Multiset.noncommSum_eq_card_nsmul

@[to_additive]
theorem noncommProd_eq_prod {α : Type*} [CommMonoid α] (s : Multiset α) :
    (noncommProd s fun _ _ _ _ _ => Commute.all _ _) = prod s := by
  induction s using Quotient.inductionOn
  simp
#align multiset.noncomm_prod_eq_prod Multiset.noncommProd_eq_prod
#align multiset.noncomm_sum_eq_sum Multiset.noncommSum_eq_sum

@[to_additive]
theorem noncommProd_commute (s : Multiset α) (comm) (y : α) (h : ∀ x ∈ s, Commute y x) :
    Commute y (s.noncommProd comm) := by
  induction s using Quotient.inductionOn
  simp only [quot_mk_to_coe, noncommProd_coe]
  exact Commute.list_prod_right _ _ h
#align multiset.noncomm_prod_commute Multiset.noncommProd_commute
#align multiset.noncomm_sum_add_commute Multiset.noncommSum_addCommute

theorem mul_noncommProd_erase [DecidableEq α] (s : Multiset α) {a : α} (h : a ∈ s) (comm)
    (comm' := fun x hx y hy hxy ↦ comm (s.mem_of_mem_erase hx) (s.mem_of_mem_erase hy) hxy) :
    a * (s.erase a).noncommProd comm' = s.noncommProd comm := by
  induction' s using Quotient.inductionOn with l
  simp only [quot_mk_to_coe, mem_coe, coe_erase, noncommProd_coe] at comm h ⊢
  suffices ∀ x ∈ l, ∀ y ∈ l, x * y = y * x by rw [List.prod_erase_of_comm h this]
  intro x hx y hy
  rcases eq_or_ne x y with rfl | hxy
  · rfl
  exact comm hx hy hxy

theorem noncommProd_erase_mul [DecidableEq α] (s : Multiset α) {a : α} (h : a ∈ s) (comm)
    (comm' := fun x hx y hy hxy ↦ comm (s.mem_of_mem_erase hx) (s.mem_of_mem_erase hy) hxy) :
    (s.erase a).noncommProd comm' * a = s.noncommProd comm := by
  suffices ∀ b ∈ erase s a, Commute a b by
    rw [← (noncommProd_commute (s.erase a) comm' a this).eq, mul_noncommProd_erase s h comm comm']
  intro b hb
  rcases eq_or_ne a b with rfl | hab
  · rfl
  exact comm h (mem_of_mem_erase hb) hab

end Multiset

namespace Finset

variable [Monoid β] [Monoid γ]


/-- Proof used in definition of `Finset.noncommProd` -/
@[to_additive]
theorem noncommProd_lemma (s : Finset α) (f : α → β)
    (comm : (s : Set α).Pairwise fun a b => Commute (f a) (f b)) :
    Set.Pairwise { x | x ∈ Multiset.map f s.val } Commute := by
  simp_rw [Multiset.mem_map]
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _
  exact comm.of_refl ha hb

/-- Product of a `s : Finset α` mapped with `f : α → β` with `[Monoid β]`,
given a proof that `*` commutes on all elements `f x` for `x ∈ s`. -/
@[to_additive
      "Sum of a `s : Finset α` mapped with `f : α → β` with `[AddMonoid β]`,
given a proof that `+` commutes on all elements `f x` for `x ∈ s`."]
def noncommProd (s : Finset α) (f : α → β)
    (comm : (s : Set α).Pairwise fun a b => Commute (f a) (f b)) : β :=
  (s.1.map f).noncommProd <| noncommProd_lemma s f comm
#align finset.noncomm_prod Finset.noncommProd
#align finset.noncomm_sum Finset.noncommSum

@[to_additive]
lemma noncommProd_induction (s : Finset α) (f : α → β) (comm)
    (p : β → Prop) (hom : ∀ a b, p a → p b → p (a * b)) (unit : p 1) (base : ∀ x ∈ s, p (f x)) :
    p (s.noncommProd f comm) := by
  refine Multiset.noncommProd_induction _ _ _ hom unit fun b hb ↦ ?_
  obtain (⟨a, ha : a ∈ s, rfl : f a = b⟩) := by simpa using hb
  exact base a ha

@[to_additive (attr := congr)]
theorem noncommProd_congr {s₁ s₂ : Finset α} {f g : α → β} (h₁ : s₁ = s₂)
    (h₂ : ∀ x ∈ s₂, f x = g x) (comm) :
    noncommProd s₁ f comm =
      noncommProd s₂ g fun x hx y hy h => by
        dsimp only
        rw [← h₂ _ hx, ← h₂ _ hy]
        subst h₁
        exact comm hx hy h := by
  simp_rw [noncommProd, Multiset.map_congr (congr_arg _ h₁) h₂]
#align finset.noncomm_prod_congr Finset.noncommProd_congr
#align finset.noncomm_sum_congr Finset.noncommSum_congr

@[to_additive (attr := simp)]
theorem noncommProd_toFinset [DecidableEq α] (l : List α) (f : α → β) (comm) (hl : l.Nodup) :
    noncommProd l.toFinset f comm = (l.map f).prod := by
  rw [← List.dedup_eq_self] at hl
  simp [noncommProd, hl]
#align finset.noncomm_prod_to_finset Finset.noncommProd_toFinset
#align finset.noncomm_sum_to_finset Finset.noncommSum_toFinset

@[to_additive (attr := simp)]
theorem noncommProd_empty (f : α → β) (h) : noncommProd (∅ : Finset α) f h = 1 :=
  rfl
#align finset.noncomm_prod_empty Finset.noncommProd_empty
#align finset.noncomm_sum_empty Finset.noncommSum_empty

@[to_additive (attr := simp)]
theorem noncommProd_cons (s : Finset α) (a : α) (f : α → β)
    (ha : a ∉ s) (comm) :
    noncommProd (cons a s ha) f comm =
      f a * noncommProd s f (comm.mono fun _ => Finset.mem_cons.2 ∘ .inr) := by
  simp_rw [noncommProd, Finset.cons_val, Multiset.map_cons, Multiset.noncommProd_cons]

@[to_additive]
theorem noncommProd_cons' (s : Finset α) (a : α) (f : α → β)
    (ha : a ∉ s) (comm) :
    noncommProd (cons a s ha) f comm =
      noncommProd s f (comm.mono fun _ => Finset.mem_cons.2 ∘ .inr) * f a := by
  simp_rw [noncommProd, Finset.cons_val, Multiset.map_cons, Multiset.noncommProd_cons']

@[to_additive (attr := simp)]
theorem noncommProd_insert_of_not_mem [DecidableEq α] (s : Finset α) (a : α) (f : α → β) (comm)
    (ha : a ∉ s) :
    noncommProd (insert a s) f comm =
      f a * noncommProd s f (comm.mono fun _ => mem_insert_of_mem) := by
  simp only [← cons_eq_insert _ _ ha, noncommProd_cons]
#align finset.noncomm_prod_insert_of_not_mem Finset.noncommProd_insert_of_not_mem
#align finset.noncomm_sum_insert_of_not_mem Finset.noncommSum_insert_of_not_mem

@[to_additive]
theorem noncommProd_insert_of_not_mem' [DecidableEq α] (s : Finset α) (a : α) (f : α → β) (comm)
    (ha : a ∉ s) :
    noncommProd (insert a s) f comm =
      noncommProd s f (comm.mono fun _ => mem_insert_of_mem) * f a := by
  simp only [← cons_eq_insert _ _ ha, noncommProd_cons']
#align finset.noncomm_prod_insert_of_not_mem' Finset.noncommProd_insert_of_not_mem'
#align finset.noncomm_sum_insert_of_not_mem' Finset.noncommSum_insert_of_not_mem'

@[to_additive (attr := simp)]
theorem noncommProd_singleton (a : α) (f : α → β) :
    noncommProd ({a} : Finset α) f
        (by
          norm_cast
          exact Set.pairwise_singleton _ _) =
      f a := mul_one _
#align finset.noncomm_prod_singleton Finset.noncommProd_singleton
#align finset.noncomm_sum_singleton Finset.noncommSum_singleton

variable [FunLike F β γ]

@[to_additive]
theorem noncommProd_map [MonoidHomClass F β γ] (s : Finset α) (f : α → β) (comm) (g : F) :
    g (s.noncommProd f comm) =
      s.noncommProd (fun i => g (f i)) fun x hx y hy _ => (comm.of_refl hx hy).map g := by
  simp [noncommProd, Multiset.noncommProd_map]
#align finset.noncomm_prod_map Finset.noncommProd_map
#align finset.noncomm_sum_map Finset.noncommSum_map

@[to_additive noncommSum_eq_card_nsmul]
theorem noncommProd_eq_pow_card (s : Finset α) (f : α → β) (comm) (m : β) (h : ∀ x ∈ s, f x = m) :
    s.noncommProd f comm = m ^ s.card := by
  rw [noncommProd, Multiset.noncommProd_eq_pow_card _ _ m]
  · simp only [Finset.card_def, Multiset.card_map]
  · simpa using h
#align finset.noncomm_prod_eq_pow_card Finset.noncommProd_eq_pow_card
#align finset.noncomm_sum_eq_card_nsmul Finset.noncommSum_eq_card_nsmul

@[to_additive]
theorem noncommProd_commute (s : Finset α) (f : α → β) (comm) (y : β)
    (h : ∀ x ∈ s, Commute y (f x)) : Commute y (s.noncommProd f comm) := by
  apply Multiset.noncommProd_commute
  intro y
  rw [Multiset.mem_map]
  rintro ⟨x, ⟨hx, rfl⟩⟩
  exact h x hx
#align finset.noncomm_prod_commute Finset.noncommProd_commute
#align finset.noncomm_sum_add_commute Finset.noncommSum_addCommute

theorem mul_noncommProd_erase [DecidableEq α] (s : Finset α) {a : α} (h : a ∈ s) (f : α → β) (comm)
    (comm' := fun x hx y hy hxy ↦ comm (s.mem_of_mem_erase hx) (s.mem_of_mem_erase hy) hxy) :
    f a * (s.erase a).noncommProd f comm' = s.noncommProd f comm := by
  classical
  simpa only [← Multiset.map_erase_of_mem _ _ h] using
    Multiset.mul_noncommProd_erase (s.1.map f) (Multiset.mem_map_of_mem f h) _

theorem noncommProd_erase_mul [DecidableEq α] (s : Finset α) {a : α} (h : a ∈ s) (f : α → β) (comm)
    (comm' := fun x hx y hy hxy ↦ comm (s.mem_of_mem_erase hx) (s.mem_of_mem_erase hy) hxy) :
    (s.erase a).noncommProd f comm' * f a = s.noncommProd f comm := by
  classical
  simpa only [← Multiset.map_erase_of_mem _ _ h] using
    Multiset.noncommProd_erase_mul (s.1.map f) (Multiset.mem_map_of_mem f h) _

@[to_additive]
theorem noncommProd_eq_prod {β : Type*} [CommMonoid β] (s : Finset α) (f : α → β) :
    (noncommProd s f fun _ _ _ _ _ => Commute.all _ _) = s.prod f := by
  induction' s using Finset.cons_induction_on with a s ha IH
  · simp
  · simp [ha, IH]
#align finset.noncomm_prod_eq_prod Finset.noncommProd_eq_prod
#align finset.noncomm_sum_eq_sum Finset.noncommSum_eq_sum

/-- The non-commutative version of `Finset.prod_union` -/
@[to_additive "The non-commutative version of `Finset.sum_union`"]
theorem noncommProd_union_of_disjoint [DecidableEq α] {s t : Finset α} (h : Disjoint s t)
    (f : α → β) (comm : { x | x ∈ s ∪ t }.Pairwise fun a b => Commute (f a) (f b)) :
    noncommProd (s ∪ t) f comm =
      noncommProd s f (comm.mono <| coe_subset.2 <| subset_union_left _ _) *
        noncommProd t f (comm.mono <| coe_subset.2 <| subset_union_right _ _) := by
  obtain ⟨sl, sl', rfl⟩ := exists_list_nodup_eq s
  obtain ⟨tl, tl', rfl⟩ := exists_list_nodup_eq t
  rw [List.disjoint_toFinset_iff_disjoint] at h
  calc noncommProd (List.toFinset sl ∪ List.toFinset tl) f comm
     = noncommProd ⟨↑(sl ++ tl), Multiset.coe_nodup.2 (sl'.append tl' h)⟩ f
         (by convert comm; simp [Set.ext_iff]) := noncommProd_congr (by ext; simp) (by simp) _
   _ = noncommProd (List.toFinset sl) f (comm.mono <| coe_subset.2 <| subset_union_left _ _) *
         noncommProd (List.toFinset tl) f (comm.mono <| coe_subset.2 <| subset_union_right _ _) :=
    by simp [noncommProd, List.dedup_eq_self.2 sl', List.dedup_eq_self.2 tl', h]
#align finset.noncomm_prod_union_of_disjoint Finset.noncommProd_union_of_disjoint
#align finset.noncomm_sum_union_of_disjoint Finset.noncommSum_union_of_disjoint

@[to_additive]
theorem noncommProd_mul_distrib_aux {s : Finset α} {f : α → β} {g : α → β}
    (comm_ff : (s : Set α).Pairwise fun x y => Commute (f x) (f y))
    (comm_gg : (s : Set α).Pairwise fun x y => Commute (g x) (g y))
    (comm_gf : (s : Set α).Pairwise fun x y => Commute (g x) (f y)) :
    (s : Set α).Pairwise fun x y => Commute ((f * g) x) ((f * g) y) := by
  intro x hx y hy h
  apply Commute.mul_left <;> apply Commute.mul_right
  · exact comm_ff.of_refl hx hy
  · exact (comm_gf hy hx h.symm).symm
  · exact comm_gf hx hy h
  · exact comm_gg.of_refl hx hy
#align finset.noncomm_prod_mul_distrib_aux Finset.noncommProd_mul_distrib_aux
#align finset.noncomm_sum_add_distrib_aux Finset.noncommSum_add_distrib_aux

/-- The non-commutative version of `Finset.prod_mul_distrib` -/
@[to_additive "The non-commutative version of `Finset.sum_add_distrib`"]
theorem noncommProd_mul_distrib {s : Finset α} (f : α → β) (g : α → β) (comm_ff comm_gg comm_gf) :
    noncommProd s (f * g) (noncommProd_mul_distrib_aux comm_ff comm_gg comm_gf) =
      noncommProd s f comm_ff * noncommProd s g comm_gg := by
  induction' s using Finset.cons_induction_on with x s hnmem ih
  · simp
  rw [Finset.noncommProd_cons, Finset.noncommProd_cons, Finset.noncommProd_cons, Pi.mul_apply,
    ih (comm_ff.mono fun _ => mem_cons_of_mem) (comm_gg.mono fun _ => mem_cons_of_mem)
      (comm_gf.mono fun _ => mem_cons_of_mem),
    (noncommProd_commute _ _ _ _ fun y hy => ?_).mul_mul_mul_comm]
  exact comm_gf (mem_cons_self x s) (mem_cons_of_mem hy) (ne_of_mem_of_not_mem hy hnmem).symm
#align finset.noncomm_prod_mul_distrib Finset.noncommProd_mul_distrib
#align finset.noncomm_sum_add_distrib Finset.noncommSum_add_distrib

section FinitePi

variable {M : ι → Type*} [∀ i, Monoid (M i)]

@[to_additive]
theorem noncommProd_mul_single [Fintype ι] [DecidableEq ι] (x : ∀ i, M i) :
    (univ.noncommProd (fun i => Pi.mulSingle i (x i)) fun i _ j _ _ =>
        Pi.mulSingle_apply_commute x i j) = x := by
  ext i
  apply (univ.noncommProd_map (fun i ↦ MonoidHom.mulSingle M i (x i)) ?a
    (Pi.evalMonoidHom M i)).trans
  case a =>
    intro i _ j _ _
    exact Pi.mulSingle_apply_commute x i j
  refine' (noncommProd_congr (insert_erase (mem_univ i)).symm _ _).trans _
  · intro j
    exact Pi.mulSingle j (x j) i
  · intro j _; dsimp
  · rw [noncommProd_insert_of_not_mem _ _ _ _ (not_mem_erase _ _),
      noncommProd_eq_pow_card (univ.erase i), one_pow, mul_one]
    · simp only [MonoidHom.mulSingle_apply, ne_eq, Pi.mulSingle_eq_same]
    · intro j hj
      simp? at hj says simp only [mem_erase, ne_eq, mem_univ, and_true] at hj
      simp only [MonoidHom.mulSingle_apply, Pi.mulSingle, Function.update, Eq.ndrec, Pi.one_apply,
        ne_eq, dite_eq_right_iff]
      intro h
      simp [*] at *
#align finset.noncomm_prod_mul_single Finset.noncommProd_mul_single
#align finset.noncomm_sum_single Finset.noncommSum_single

@[to_additive]
theorem _root_.MonoidHom.pi_ext [Finite ι] [DecidableEq ι] {f g : (∀ i, M i) →* γ}
    (h : ∀ i x, f (Pi.mulSingle i x) = g (Pi.mulSingle i x)) : f = g := by
  cases nonempty_fintype ι
  ext x
  rw [← noncommProd_mul_single x, univ.noncommProd_map, univ.noncommProd_map]
  congr 1 with i; exact h i (x i)
#align monoid_hom.pi_ext MonoidHom.pi_ext
#align add_monoid_hom.pi_ext AddMonoidHom.pi_ext

end FinitePi

end Finset
