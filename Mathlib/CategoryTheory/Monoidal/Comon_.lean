/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.CategoryTheory.Monoidal.Braided.Opposite
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# The category of comonoids in a monoidal category.

We define comonoids in a monoidal category `C`,
and show that they are equivalently monoid objects in the opposite category.

We construct the monoidal structure on `Comon_ C`, when `C` is braided.

An oplax monoidal functor takes comonoid objects to comonoid objects.
That is, a oplax monoidal functor `F : C ⥤ D` induces a functor `Comon_ C ⥤ Comon_ D`.

## TODO
* Comonoid objects in `C` are "just"
  oplax monoidal functors from the trivial monoidal category to `C`.
-/

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C]

/-- A comonoid object internal to a monoidal category.

When the monoidal category is preadditive, this is also sometimes called a "coalgebra object".
-/
structure Comon_ where
  /-- The underlying object of a comonoid object. -/
  X : C
  /-- The counit of a comonoid object. -/
  counit : X ⟶ 𝟙_ C
  /-- The comultiplication morphism of a comonoid object. -/
  comul : X ⟶ X ⊗ X
  counit_comul : comul ≫ (counit ▷ X) = (λ_ X).inv := by aesop_cat
  comul_counit : comul ≫ (X ◁ counit) = (ρ_ X).inv := by aesop_cat
  comul_assoc : comul ≫ (X ◁ comul) ≫ (α_ X X X).inv = comul ≫ (comul ▷ X) := by aesop_cat

attribute [reassoc] Comon_.counit_comul Comon_.comul_counit

attribute [reassoc (attr := simp)] Comon_.comul_assoc

namespace Comon_

/-- The trivial comonoid object. We later show this is terminal in `Comon_ C`.
-/
@[simps]
def trivial : Comon_ C where
  X := 𝟙_ C
  counit := 𝟙 _
  comul := (λ_ _).inv
  comul_assoc := by coherence
  counit_comul := by coherence
  comul_counit := by coherence

instance : Inhabited (Comon_ C) :=
  ⟨trivial C⟩

variable {C}
variable {M : Comon_ C}

@[reassoc (attr := simp)]
theorem counit_comul_hom {Z : C} (f : M.X ⟶ Z) : M.comul ≫ (M.counit ⊗ f) = f ≫ (λ_ Z).inv := by
  rw [leftUnitor_inv_naturality, tensorHom_def, counit_comul_assoc]

@[reassoc (attr := simp)]
theorem comul_counit_hom {Z : C} (f : M.X ⟶ Z) : M.comul ≫ (f ⊗ M.counit) = f ≫ (ρ_ Z).inv := by
  rw [rightUnitor_inv_naturality, tensorHom_def', comul_counit_assoc]

@[reassoc (attr := simp)] theorem comul_assoc_flip :
    M.comul ≫ (M.comul ▷ M.X) ≫ (α_ M.X M.X M.X).hom = M.comul ≫ (M.X ◁ M.comul) := by
  simp [← comul_assoc_assoc]

/-- A morphism of comonoid objects. -/
@[ext]
structure Hom (M N : Comon_ C) where
  /-- The underlying morphism of a morphism of comonoid objects. -/
  hom : M.X ⟶ N.X
  hom_counit : hom ≫ N.counit = M.counit := by aesop_cat
  hom_comul : hom ≫ N.comul = M.comul ≫ (hom ⊗ hom) := by aesop_cat

attribute [reassoc (attr := simp)] Hom.hom_counit Hom.hom_comul

/-- The identity morphism on a comonoid object. -/
@[simps]
def id (M : Comon_ C) : Hom M M where
  hom := 𝟙 M.X

instance homInhabited (M : Comon_ C) : Inhabited (Hom M M) :=
  ⟨id M⟩

/-- Composition of morphisms of monoid objects. -/
@[simps]
def comp {M N O : Comon_ C} (f : Hom M N) (g : Hom N O) : Hom M O where
  hom := f.hom ≫ g.hom

instance : Category (Comon_ C) where
  Hom M N := Hom M N
  id := id
  comp f g := comp f g

@[ext] lemma ext {X Y : Comon_ C} {f g : X ⟶ Y} (w : f.hom = g.hom) : f = g := Hom.ext _ _ w

@[simp] theorem id_hom' (M : Comon_ C) : (𝟙 M : Hom M M).hom = 𝟙 M.X := rfl

@[simp]
theorem comp_hom' {M N K : Comon_ C} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

section

variable (C)

/-- The forgetful functor from comonoid objects to the ambient category. -/
@[simps]
def forget : Comon_ C ⥤ C where
  obj A := A.X
  map f := f.hom

end

instance forget_faithful : (@forget C _ _).Faithful where

instance {A B : Comon_ C} (f : A ⟶ B) [e : IsIso ((forget C).map f)] : IsIso f.hom := e

/-- The forgetful functor from comonoid objects to the ambient category reflects isomorphisms. -/
instance : (forget C).ReflectsIsomorphisms where
  reflects f e :=
    ⟨⟨{ hom := inv f.hom }, by aesop_cat⟩⟩

/-- Construct an isomorphism of monoids by giving an isomorphism between the underlying objects
and checking compatibility with unit and multiplication only in the forward direction.
-/
@[simps]
def mkIso {M N : Comon_ C} (f : M.X ≅ N.X) (f_counit : f.hom ≫ N.counit = M.counit)
    (f_comul : f.hom ≫ N.comul = M.comul ≫ (f.hom ⊗ f.hom)) : M ≅ N where
  hom :=
    { hom := f.hom
      hom_counit := f_counit
      hom_comul := f_comul }
  inv :=
    { hom := f.inv
      hom_counit := by rw [← f_counit]; simp
      hom_comul := by
        rw [← cancel_epi f.hom]
        slice_rhs 1 2 => rw [f_comul]
        simp }

instance uniqueHomToTrivial (A : Comon_ C) : Unique (A ⟶ trivial C) where
  default :=
    { hom := A.counit
      hom_counit := by dsimp; simp
      hom_comul := by dsimp; simp [A.comul_counit, unitors_inv_equal] }
  uniq f := by
    ext; simp
    rw [← Category.comp_id f.hom]
    erw [f.hom_counit]

open CategoryTheory.Limits

instance : HasTerminal (Comon_ C) :=
  hasTerminal_of_unique (trivial C)

open Opposite

variable (C)

/--
Turn a comonoid object into a monoid object in the opposite category.
-/
@[simps] def Comon_to_Mon_op_op_obj' (A : Comon_ C) : Mon_ (Cᵒᵖ) where
  X := op A.X
  one := A.counit.op
  mul := A.comul.op
  one_mul := by
    rw [← op_whiskerRight, ← op_comp, counit_comul]
    rfl
  mul_one := by
    rw [← op_whiskerLeft, ← op_comp, comul_counit]
    rfl
  mul_assoc := by
    rw [← op_inv_associator, ← op_whiskerRight, ← op_comp, ← op_whiskerLeft, ← op_comp,
      ← comul_assoc, op_comp, op_comp_assoc]
    rfl

/--
The contravariant functor turning comonoid objects into monoid objects in the opposite category.
-/
@[simps] def Comon_to_Mon_op_op : Comon_ C ⥤ (Mon_ (Cᵒᵖ))ᵒᵖ where
  obj A := op (Comon_to_Mon_op_op_obj' C A)
  map := fun f => op <|
    { hom := f.hom.op
      one_hom := by apply Quiver.Hom.unop_inj; simp
      mul_hom := by apply Quiver.Hom.unop_inj; simp [op_tensorHom] }

/--
Turn a monoid object in the opposite category into a comonoid object.
-/
@[simps] def Mon_op_op_to_Comon_obj' (A : (Mon_ (Cᵒᵖ))) : Comon_ C where
  X := unop A.X
  counit := A.one.unop
  comul := A.mul.unop
  counit_comul := by rw [← unop_whiskerRight, ← unop_comp, Mon_.one_mul]; rfl
  comul_counit := by rw [← unop_whiskerLeft, ← unop_comp, Mon_.mul_one]; rfl
  comul_assoc := by
    rw [← unop_whiskerRight, ← unop_comp, ← unop_whiskerLeft, ← unop_comp_assoc, Mon_.mul_assoc]
    rfl

/--
The contravariant functor turning monoid objects in the opposite category into comonoid objects.
-/
@[simps]
def Mon_op_op_to_Comon : (Mon_ (Cᵒᵖ))ᵒᵖ ⥤ Comon_ C where
  obj A := Mon_op_op_to_Comon_obj' C (unop A)
  map := fun f =>
    { hom := f.unop.hom.unop
      hom_counit := by apply Quiver.Hom.op_inj; simp
      hom_comul := by apply Quiver.Hom.op_inj; simp [op_tensorHom] }

/--
Comonoid objects are contravariantly equivalent to monoid objects in the opposite category.
-/
@[simps]
def Comon_equiv_Mon_op_op : Comon_ C ≌ (Mon_ (Cᵒᵖ))ᵒᵖ :=
  { functor := Comon_to_Mon_op_op C
    inverse := Mon_op_op_to_Comon C
    unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
    counitIso := NatIso.ofComponents (fun _ => Iso.refl _) }

/--
Comonoid objects in a braided category form a monoidal category.

This definition is via transporting back and forth to monoids in the opposite category,
-/
instance [BraidedCategory C] : MonoidalCategory (Comon_ C) :=
  Monoidal.transport (Comon_equiv_Mon_op_op C).symm

variable [BraidedCategory C]

theorem tensorObj_X (A B : Comon_ C) : (A ⊗ B).X = A.X ⊗ B.X := rfl

theorem tensorObj_counit (A B : Comon_ C) : (A ⊗ B).counit = (A.counit ⊗ B.counit) ≫ (λ_ _).hom :=
  rfl

/--
Preliminary statement of the comultiplication for a tensor product of comonoids.
This version is the definitional equality provided by transport, and not quite as good as
the version provided in `tensorObj_comul` below.
-/
theorem tensorObj_comul' (A B : Comon_ C) :
    (A ⊗ B).comul =
      (A.comul ⊗ B.comul) ≫ (tensor_μ Cᵒᵖ (op A.X, op B.X) (op A.X, op B.X)).unop := by
  rfl

/--
The comultiplication on the tensor product of two comonoids is
the tensor product of the comultiplications followed by the tensor strength
(to shuffle the factors back into order).
-/
theorem tensorObj_comul (A B : Comon_ C) :
    (A ⊗ B).comul = (A.comul ⊗ B.comul) ≫ tensor_μ C (A.X, A.X) (B.X, B.X) := by
  rw [tensorObj_comul']
  congr
  simp only [tensor_μ, unop_tensorObj, unop_op]
  apply Quiver.Hom.unop_inj
  dsimp [op_tensorObj, op_associator]
  rw [Category.assoc, Category.assoc, Category.assoc]
  rfl

end Comon_

namespace CategoryTheory.OplaxMonoidalFunctor

variable {C} {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]

/-- A oplax monoidal functor takes comonoid objects to comonoid objects.

That is, a oplax monoidal functor `F : C ⥤ D` induces a functor `Comon_ C ⥤ Comon_ D`.
-/
@[simps]
def mapComon (F : OplaxMonoidalFunctor C D) : Comon_ C ⥤ Comon_ D where
  obj A :=
    { X := F.obj A.X
      counit := F.map A.counit ≫ F.ε
      comul := F.map A.comul ≫ F.μ _ _
      counit_comul := by
        simp_rw [comp_whiskerRight, Category.assoc, F.μ_natural_left_assoc, F.left_unitality,
          ← F.map_comp_assoc, A.counit_comul]
      comul_counit := by
        simp_rw [MonoidalCategory.whiskerLeft_comp, Category.assoc, F.μ_natural_right_assoc,
          F.right_unitality, ← F.map_comp_assoc, A.comul_counit]
      comul_assoc := by
        simp_rw [comp_whiskerRight, Category.assoc, F.μ_natural_left_assoc,
          MonoidalCategory.whiskerLeft_comp, Category.assoc, F.μ_natural_right_assoc,
          ← F.map_comp_assoc, ← A.comul_assoc_flip, F.map_comp, F.associativity_inv]
        slice_lhs 3 4 =>
          rw [← F.map_comp, Iso.hom_inv_id, F.map_id]
        simp only [Category.id_comp, Category.assoc] }
  map f :=
    { hom := F.map f.hom
      hom_counit := by dsimp; rw [← F.map_comp_assoc, f.hom_counit]
      hom_comul := by
        dsimp
        rw [Category.assoc, F.μ_natural, ← F.map_comp_assoc, ← F.map_comp_assoc, f.hom_comul] }
  map_id A := by ext; simp
  map_comp f g := by ext; simp

variable (C D)

-- TODO We haven't yet set up the category structure on `OplaxMonoidalFunctor C D`
-- and so can't state `mapComonFunctor : OplaxMonoidalFunctor C D ⥤ Comon_ C ⥤ Comon_ D`.


end CategoryTheory.OplaxMonoidalFunctor
