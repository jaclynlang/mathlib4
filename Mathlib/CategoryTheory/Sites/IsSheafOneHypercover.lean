/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Sites.OneHypercover

/-!
# Characterization of sheaves using 1-hypercovers

In this file, given a Grothendieck topology `J` on a category `C`,
we define a type `J.OneHypercoverFamily` of families of 1-hypercovers.
When `H : J.OneHypercoverFamily`, we define a predicate `H.IsGenerating`
which means that any covering sieve contains the sieve generated by
the underlying covering of one of the 1-hypercovers in the family.
If this holds, we show in `OneHypercoverFamily.isSheaf_iff` that a
presheaf `P : Cᵒᵖ ⥤ A` is a sheaf iff for any 1-hypercover `E`
in the family, the multifork `E.multifork P` is limit.

There is a universe parameter `w` attached to `OneHypercoverFamily` and
`OneHypercover`. This universe controls the "size" of the 1-hypercovers:
the index types involved in the 1-hypercovers have to be in `Type w`.
Then, we introduce a type class
`GrothendieckTopology.IsGeneratedByOneHypercovers.{w} J` as an abbreviation for
`OneHypercoverFamily.IsGenerating.{w} (J := J) ⊤`. We shall show
that if `C : Type u` and `Category.{v} C`, then
`GrothendieckTopology.IsGeneratedByOneHypercovers.{max u v} J` holds (TODO).

## TODO
* Show that functors which preserve 1-hypercovers are continuous.
* Refactor `DenseSubsite` using `1`-hypercovers.

-/

universe w v v' u u'

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A : Type u'} [Category.{v'} A]

namespace GrothendieckTopology

/-- A family of 1-hypercovers consists of the data of a predicate on
`OneHypercover.{w} J X` for all `X`. -/
abbrev OneHypercoverFamily := ∀ ⦃X : C⦄, OneHypercover.{w} J X → Prop

namespace OneHypercoverFamily

variable {J}
variable (H : OneHypercoverFamily.{w} J)

/-- A family of 1-hypercovers generates the topology if any covering sieve
contains the sieve generated by the underlying covering of one of these 1-hypercovers.
See `OneHypercoverFamily.isSheaf_iff` for the characterization of sheaves. -/
class IsGenerating : Prop where
  le {X : C} (S : Sieve X) (hS : S ∈ J X) :
    ∃ (E : J.OneHypercover X) (_ : H E), E.sieve₀ ≤ S

variable [H.IsGenerating]

lemma exists_oneHypercover {X : C} (S : Sieve X) (hS : S ∈ J X) :
    ∃ (E : J.OneHypercover X) (_ : H E), E.sieve₀ ≤ S :=
  IsGenerating.le _ hS

variable (P : Cᵒᵖ ⥤ A)

namespace IsSheafIff

variable (hP : ∀ ⦃X : C⦄ (E : J.OneHypercover X) (_ : H E), Nonempty (IsLimit (E.multifork P)))

lemma hom_ext {X : C} (S : Sieve X) (hS : S ∈ J X) {T : A}
    {x y : T ⟶ P.obj (Opposite.op X)}
    (h : ∀ ⦃Y : C⦄ (f : Y ⟶ X) (_ : S f), x ≫ P.map f.op = y ≫ P.map f.op) :
    x = y := by
  obtain ⟨E, hE, le⟩ := H.exists_oneHypercover S hS
  exact Multifork.IsLimit.hom_ext (hP E hE).some (fun j => h _ (le _ (Sieve.ofArrows_mk _ _ _)))

variable {P H}
variable {X : C} {S : Sieve X} {E : J.OneHypercover X} (hE : H E) (le : E.sieve₀ ≤ S)

section

variable (F : Multifork (Cover.index ⟨S, J.superset_covering le E.mem₀⟩ P))

/-- Auxiliary definition for `isLimit`. -/
noncomputable def lift : F.pt ⟶ P.obj (Opposite.op X) :=
  Multifork.IsLimit.lift (hP E hE).some
    (fun i => F.ι ⟨_, E.f i, le _ (Sieve.ofArrows_mk _ _ _)⟩)
    (fun ⟨⟨i₁, i₂⟩, j⟩ => F.condition
        { h₁ := le _ ((Sieve.ofArrows_mk _ _ i₁))
          h₂ := le _ ((Sieve.ofArrows_mk _ _ i₂))
          w := E.w j })

@[reassoc]
lemma fac' (i : E.I₀) :
    lift hP hE le F ≫ P.map (E.f i).op =
      F.ι ⟨_, E.f i, le _ (Sieve.ofArrows_mk _ _ _)⟩ :=
  Multifork.IsLimit.fac (hP E hE).some _ _ i

lemma fac {Y : C} (f : Y ⟶ X) (hf : S f) :
    lift hP hE le F ≫ P.map f.op = F.ι ⟨Y, f, hf⟩ := by
  apply hom_ext H P hP _ (J.pullback_stable f E.mem₀)
  intro Z g
  rintro ⟨T, a, b, hb, fac⟩
  cases' hb with i
  rw [assoc, ← P.map_comp, ← op_comp, ← fac,
    op_comp, P.map_comp, fac'_assoc]
  exact F.condition
    { h₁ := le _ (Sieve.ofArrows_mk _ _ _)
      h₂ := hf
      w := fac }

end

/-- Auxiliary definition for `OneHypercoverFamily.isSheaf_iff`. -/
noncomputable def isLimit :
    IsLimit (Cover.multifork ⟨S, J.superset_covering le E.mem₀⟩ P) :=
  Multifork.IsLimit.mk _
    (fun F => lift hP hE le F)
    (fun F => by
      rintro ⟨Y, f, hf⟩
      apply fac)
    (fun F m hm => by
      apply hom_ext H P hP S (J.superset_covering le E.mem₀)
      intro Y f hf
      rw [fac _ _ _ _ _ hf]
      exact hm ⟨_, _, hf⟩)

end IsSheafIff

lemma isSheaf_iff :
    Presheaf.IsSheaf J P ↔ ∀ ⦃X : C⦄ (E : J.OneHypercover X)
      (_ : H E), Nonempty (IsLimit (E.multifork P)) := by
  constructor
  · intro hP X E _
    exact ⟨E.isLimitMultifork ⟨_, hP⟩⟩
  · intro hP
    rw [Presheaf.isSheaf_iff_multifork]
    rintro X ⟨S, hS⟩
    obtain ⟨E, hE, le⟩ := H.exists_oneHypercover S hS
    exact ⟨IsSheafIff.isLimit hP hE le⟩

end OneHypercoverFamily

/-- Condition that a topology is generated by 1-hypercovers of size `w`. -/
abbrev IsGeneratedByOneHypercovers : Prop :=
  OneHypercoverFamily.IsGenerating.{w} (J := J) ⊤

end GrothendieckTopology

namespace Presheaf

lemma isSheaf_iff_of_isGeneratedByOneHypercovers
    [GrothendieckTopology.IsGeneratedByOneHypercovers.{w} J] (P : Cᵒᵖ ⥤ A) :
    IsSheaf J P ↔ ∀ ⦃X : C⦄ (E : GrothendieckTopology.OneHypercover.{w} J X),
        Nonempty (IsLimit (E.multifork P)) := by
  simpa using GrothendieckTopology.OneHypercoverFamily.isSheaf_iff.{w} ⊤ P

end Presheaf

end CategoryTheory
