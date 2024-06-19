/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.DenseSubsite
import Mathlib.CategoryTheory.Sites.PreservesSheafification
/-!

# Discrete objects in sheaf categories.

This file defines the notion of a discrete object in a sheaf category. A discrete sheaf in this is a
context is a sheaf `F` such that the counit `(F(*))^cst ⟶ F` is an isomorphism. Here `*` denotes
a particular chosen terminal object of the defining site, and `cst` denotes the constant sheaf.

It is convenient to take an arbitrary terminal object; one might want to use this construction to
talk about discrete sheaves on a site which has a particularly convenient terminal object, such as
the one element space in `CompHaus`.

## Main results

* `isDiscrete_iff_mem_essImage` : A sheaf is discrete if and only if it is in the essential image
of the constant sheaf functor.
* `isDiscrete_iff_of_equivalence` : The property of a sheaf of being discrete is invariant under
equivalence of sheaf categories.
* `isDiscrete_iff_forget` : Given a "forgetful" functor `U : A ⥤ B` a sheaf `F : Sheaf J A` is
discrete if and only if the sheaf given by postcomposition with `U` is discrete.
-/

open CategoryTheory Limits Functor Adjunction Opposite

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category C] (J : GrothendieckTopology C) {A : Type*} [Category A]
  [HasWeakSheafify J A] [(constantSheaf J A).Faithful] [(constantSheaf J A).Full]
  {t : C} (ht : IsTerminal t)

/--
A sheaf is discrete if it is a discrete object of the "underlying object" functor from the sheaf
category to the target category.
-/
abbrev IsDiscrete (F : Sheaf J A) : Prop := IsIso ((constantSheafAdj J A ht).counit.app F)

theorem isDiscrete_iff_mem_essImage (F : Sheaf J A) :
    F.IsDiscrete J ht ↔ F ∈ (constantSheaf J A).essImage :=
  (constantSheafAdj J A ht).isIso_counit_app_iff_mem_essImage

section Equivalence

variable {D : Type*} [Category D] (K : GrothendieckTopology D) [HasWeakSheafify K A]
variable (G : C ⥤ D) [G.Full] [G.Faithful]
  [∀ (X : Dᵒᵖ), HasLimitsOfShape (StructuredArrow X G.op) A]
  [G.IsCoverDense K] [G.IsContinuous J K] [G.IsCocontinuous J K] (ht' : IsTerminal (G.obj t))

variable [(constantSheaf J A).Faithful] [(constantSheaf J A).Full]

open Functor.IsCoverDense

noncomputable example :
    let e : Sheaf J A ≌ Sheaf K A :=
      sheafEquivOfCoverPreservingCoverLifting G J K A
    e.inverse ⋙ (sheafSections J A).obj (op t) ≅ (sheafSections K A).obj (op (G.obj t)) :=
  Iso.refl _

variable (A) in
/--
The constant sheaf functor commutes up to isomorphism with any equivalence of sheaf categories.

This is an auxiliary definition used to prove `Sheaf.isDiscrete_iff` below, which says that the
property of a sheaf of being a discrete object is invariant under equivalence of sheaf categories.
-/
noncomputable def equivCommuteConstant :
    let e : Sheaf J A ≌ Sheaf K A :=
      sheafEquivOfCoverPreservingCoverLifting G J K A
    constantSheaf J A ⋙ e.functor ≅ constantSheaf K A :=
  let e : Sheaf J A ≌ Sheaf K A :=
      sheafEquivOfCoverPreservingCoverLifting G J K A
  (Adjunction.leftAdjointUniq ((constantSheafAdj J A ht).comp e.toAdjunction)
    (constantSheafAdj K A ht'))

variable (A) in
/--
The constant sheaf functor commutes up to isomorphism with any equivalence of sheaf categories.

This is an auxiliary definition used to prove `Sheaf.isDiscrete_iff` below, which says that the
property of a sheaf of being a discrete object is invariant under equivalence of sheaf categories.
-/
noncomputable def equivCommuteConstant' :
    let e : Sheaf J A ≌ Sheaf K A :=
      sheafEquivOfCoverPreservingCoverLifting G J K A
    constantSheaf J A ≅ constantSheaf K A ⋙ e.inverse :=
  let e : Sheaf J A ≌ Sheaf K A :=
      sheafEquivOfCoverPreservingCoverLifting G J K A
  isoWhiskerLeft (constantSheaf J A) e.unitIso ≪≫
    isoWhiskerRight (equivCommuteConstant J A ht K G ht') e.inverse

/--
The property of a sheaf of being a discrete object is invariant under equivalence of sheaf
categories.
-/
lemma isDiscrete_iff_of_equivalence (F : Sheaf K A) :
    let e : Sheaf J A ≌ Sheaf K A :=
      sheafEquivOfCoverPreservingCoverLifting G J K A
    haveI : (constantSheaf K A).Faithful :=
      Functor.Faithful.of_iso (equivCommuteConstant J A ht K G ht')
    haveI : (constantSheaf K A).Full :=
      Functor.Full.of_iso (equivCommuteConstant J A ht K G ht')
    (e.inverse.obj F).IsDiscrete J ht ↔ IsDiscrete K ht' F := by
  intro e
  have : (constantSheaf K A).Faithful :=
      Functor.Faithful.of_iso (equivCommuteConstant J A ht K G ht')
  have : (constantSheaf K A).Full :=
    Functor.Full.of_iso (equivCommuteConstant J A ht K G ht')
  simp only [isDiscrete_iff_mem_essImage]
  constructor
  · intro ⟨Y, ⟨i⟩⟩
    let j : (constantSheaf K A).obj Y ≅ F :=
      (equivCommuteConstant J A ht K G ht').symm.app _ ≪≫ e.functor.mapIso i ≪≫ e.counitIso.app _
    exact ⟨_, ⟨j⟩⟩
  · intro ⟨Y, ⟨i⟩⟩
    let j : (constantSheaf J A).obj Y ≅ e.inverse.obj F :=
      (equivCommuteConstant' J A ht K G ht').app _ ≪≫ e.inverse.mapIso i
    exact ⟨_, ⟨j⟩⟩

end Equivalence

section Forget

variable {B : Type*} [Category B] (U : A ⥤ B)
  [HasWeakSheafify J A] [HasWeakSheafify J B]
  [(constantSheaf J A).Faithful] [(constantSheaf J A).Full]
  [(constantSheaf J B).Faithful] [(constantSheaf J B).Full]
  [J.PreservesSheafification U] [J.HasSheafCompose U] (F : Sheaf J A)

/-- Auxiliary lemma for `sheafCompose_reflects_discrete`. -/
private lemma sheafifyComposeIso_comp_constantSheafAdj_counit :
  (sheafifyComposeIso J U ((const Cᵒᵖ).obj (F.val.obj { unop := t }))).hom ≫
    ((sheafCompose J U).map ((constantSheafAdj J A ht).counit.app F)).val =
      ((presheafToSheaf J B ⋙ sheafToPresheaf J B).mapIso (constComp Cᵒᵖ _ U)).hom ≫
        ((constantSheafAdj J B ht).counit.app ((sheafCompose J U).obj F)).val := by
  apply sheafify_hom_ext _ _ _ ((sheafCompose J U).obj F).cond
  simp only [sheafCompose_obj_val, id_obj, comp_obj, flip_obj_obj, sheafToPresheaf_obj,
    sheafComposeIso_hom_fac_assoc, mapIso_hom, Functor.comp_map, sheafToPresheaf_map]
  erw [Adjunction.unit_naturality_assoc]
  simp only [const_obj_obj, const_obj_map, id_obj, constComp, comp_obj, sheafToPresheaf_obj,
    sheafificationAdjunction_unit_app]
  ext
  simp only [comp_obj, const_obj_obj, NatTrans.comp_app, whiskerRight_app, Category.id_comp,
    comp_obj, flip_obj_obj, sheafToPresheaf_obj, id_obj, constantSheafAdj,
    Adjunction.comp, evaluation_obj_obj, NatTrans.comp_app, associator_hom_app, whiskerLeft_app,
    whiskerRight_app, map_comp, instCategorySheaf_comp_val, sheafCompose_obj_val,
    sheafCompose_map_val, instCategorySheaf_id_val, sheafificationAdjunction_counit_app_val,
    NatTrans.id_app, sheafifyMap_sheafifyLift, Category.comp_id, Category.id_comp]
  erw [Functor.map_id, Category.id_comp, ← NatTrans.comp_app]
  simp only [toSheafify_sheafifyLift, ← Functor.map_comp, ← NatTrans.comp_app,
    sheafifyMap_sheafifyLift, Category.comp_id,
    constantPresheafAdj, comp_obj, evaluation_obj_obj, id_obj, op_unop,
    mkOfUnitCounit_counit, Functor.comp_map]

/-- Auxiliary lemma for `sheafCompose_reflects_discrete`. -/
private lemma constantCommuteCompose_hom_counit :
    ((sheafifyComposeIso J U ((const Cᵒᵖ).obj (F.val.obj ⟨t⟩))).symm ≪≫
      (presheafToSheaf J B ⋙ sheafToPresheaf J B).mapIso (constComp Cᵒᵖ (F.val.obj ⟨t⟩) U)).hom ≫
        ((constantSheafAdj J B ht).counit.app ((sheafCompose J U).obj F)).val =
          ((sheafCompose J U).map ((constantSheafAdj J A ht).counit.app F)).val := by
  rw [← Iso.eq_inv_comp]
  simp only [comp_obj, flip_obj_obj, sheafToPresheaf_obj, sheafCompose_obj_val, id_obj,
    Iso.trans_inv, mapIso_inv, Functor.comp_map, sheafToPresheaf_map,
    Iso.symm_inv, Category.assoc, sheafifyComposeIso_comp_constantSheafAdj_counit, mapIso_hom,
    ← instCategorySheaf_comp_val, Iso.map_inv_hom_id_assoc]

lemma sheafCompose_reflects_discrete [(sheafCompose J U).ReflectsIsomorphisms]
    [((sheafCompose J U).obj F).IsDiscrete J ht] :
    F.IsDiscrete J ht := by
  let f := (sheafCompose J U).map ((constantSheafAdj J A ht).counit.app F)
  have : IsIso ((sheafToPresheaf J B).map f) := by
    simp only [comp_obj, flip_obj_obj, sheafToPresheaf_obj, sheafCompose_obj_val, id_obj,
      sheafToPresheaf_map, f, ← constantCommuteCompose_hom_counit]
    exact inferInstanceAs (IsIso (_ ≫ ((sheafToPresheaf J B).map
      ((constantSheafAdj J B ht).counit.app ((sheafCompose J U).obj F)))))
  have : IsIso f := by
    apply ReflectsIsomorphisms.reflects (sheafToPresheaf J B) _
  apply ReflectsIsomorphisms.reflects (sheafCompose J U) _

instance [h : F.IsDiscrete J ht] :
    ((sheafCompose J U).obj F).IsDiscrete J ht := by
  rw [isDiscrete_iff_mem_essImage] at h ⊢
  obtain ⟨Y, ⟨i⟩⟩ := h
  exact ⟨U.obj Y, ⟨(fullyFaithfulSheafToPresheaf _ _).preimageIso
    (((sheafifyComposeIso J U ((const Cᵒᵖ).obj Y)).symm ≪≫
      (presheafToSheaf J B ⋙ sheafToPresheaf J B).mapIso (constComp Cᵒᵖ Y U)).symm ≪≫
        (sheafToPresheaf _ _).mapIso ((sheafCompose J U).mapIso i))⟩⟩

lemma isDiscrete_iff_forget [(sheafCompose J U).ReflectsIsomorphisms] : F.IsDiscrete J ht ↔
    ((sheafCompose J U).obj F).IsDiscrete J ht :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ sheafCompose_reflects_discrete _ _ U F⟩

end Forget

end CategoryTheory.Sheaf
