import Mathlib.CategoryTheory.Sites.Sheaf

universe v v' u u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (A : Type u') [Category.{v'} A]

class HasSheafify : Prop where
  isRightAdjoint : Nonempty <| IsRightAdjoint (sheafToPresheaf J A)

noncomputable section

instance [HasSheafify J A] : IsRightAdjoint (sheafToPresheaf J A) := HasSheafify.isRightAdjoint.some

def presheafToSheaf [HasSheafify J A] : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A :=
  leftAdjoint (sheafToPresheaf J A)

def sheafificationAdjunction [HasSheafify J A] : presheafToSheaf J A ⊣ sheafToPresheaf J A :=
  HasSheafify.isRightAdjoint.some.adj

instance [HasSheafify J A] : IsLeftAdjoint <| presheafToSheaf J A where
  right := sheafToPresheaf J A
  adj := sheafificationAdjunction J A

end

end CategoryTheory
