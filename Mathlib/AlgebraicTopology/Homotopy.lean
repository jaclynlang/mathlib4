import Mathlib.AlgebraicTopology.SimplicialSet
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Tactic
import Mathlib.Data.Fin.Basic

open CategoryTheory Limits Simplicial SimplexCategory

variable (X Y X' Y': SSet) (m n : ℕ) (f : X ⟶ Y)

namespace CategoryTheory

def isTerminalHom {C : Type _} [Category C] (X Y : C) (hY : IsTerminal Y) :
    IsTerminal (X ⟶ Y) :=
  letI : ∀ (W : Type _), Unique (W ⟶ (X ⟶ Y)) := fun W =>
    { default := fun _ => hY.from _
      uniq := fun a => by ext ; apply hY.hom_ext }
  IsTerminal.ofUnique _

def Functor.isTerminalOfObjIsTerminal {C D : Type _} [Category C] [Category D]
    (F : C ⥤ D) (hF : ∀ X : C, IsTerminal (F.obj X)) :
    IsTerminal F :=
  letI : ∀ (G : C ⥤ D), Unique (G ⟶ F) := fun _ => {
    default := {
      app := fun _ => (hF _).from _
      naturality := fun _ _ _ => (hF _).hom_ext _ _ }
    uniq := fun _ => NatTrans.ext _ _ <| funext fun _ => (hF _).hom_ext _ _ }
  IsTerminal.ofUnique _

end CategoryTheory

namespace SimplexCategory

def isTerminalZero : IsTerminal ([0] : SimplexCategory) :=
  letI : ∀ t : SimplexCategory, Unique (t ⟶ [0]) := fun t => {
    default := SimplexCategory.Hom.mk <| OrderHom.const _ 0
    uniq := fun m => SimplexCategory.Hom.ext _ _ <| OrderHom.ext _ _ <|
      funext fun _ => Fin.ext <| by simp }
  IsTerminal.ofUnique _

end SimplexCategory

namespace SSet

universe u

class IsKan (X : SSet) : Prop where
  cond : ∀ n i (f : Λ[n,i] ⟶ X), ∃ (g : Δ[n] ⟶ X), f = hornInclusion _ _ ≫ g

def d0 : Δ[0] ⟶ Δ[1] := standardSimplex.map (δ 0)
def d1 : Δ[0] ⟶ Δ[1] := standardSimplex.map (δ 1)

def D0 : Δ[1] ⟶ Δ[2] := standardSimplex.map (δ 0)
def D1 : Δ[1] ⟶ Δ[2] := standardSimplex.map (δ 1)
def D2 : Δ[1] ⟶ Δ[2] := standardSimplex.map (δ 2)

def ptIsTerminal : IsTerminal Δ[0] := Functor.isTerminalOfObjIsTerminal _ <|
  fun t => show IsTerminal (t.unop ⟶ [0]) from isTerminalHom _ _ isTerminalZero

def binaryFan (X : SSet.{0}) : BinaryFan Δ[0] X :=
  BinaryFan.mk (ptIsTerminal.from X) (𝟙 X)

def isLimitBinaryFan (X : SSet.{0}) : IsLimit (binaryFan X) where
  lift := fun (S : BinaryFan _ _) => S.snd
  fac := fun (S : BinaryFan _ _) => by
    rintro ⟨(_|_)⟩
    · apply ptIsTerminal.hom_ext
    · dsimp [binaryFan] ; simp
  uniq := fun (S : BinaryFan _ _) m hm => by
    specialize hm ⟨WalkingPair.right⟩
    simpa [binaryFan] using hm

noncomputable
def leftUnitor (X : SSet.{0}) : Δ[0] ⨯ X ≅ X :=
  (limit.isLimit _).conePointUniqueUpToIso (isLimitBinaryFan X)

structure Path {X : SSet.{0}} (a b : Δ[0] ⟶ X) where
  p : Δ[1] ⟶ X
  hp0 : d0 ≫ p = a
  hp1 : d1 ≫ p = b

def Path.rfl {X : SSet.{0}} (a : Δ[0] ⟶ X) : Path a a where
  p := ptIsTerminal.from _ ≫ a
  hp0 := by slice_lhs 1 2 => simp
  hp1 := by slice_lhs 1 2 => simp

--000T
def intoBoundary (n : ℕ) (j : Fin (n + 2)) : Δ[n] ⟶ ∂Δ[n + 1] where
  app k x := ⟨(standardSimplex.map (δ j)).app k x, fun h => by
    simpa using (show j ∈ Set.range (Fin.succAbove j) from Set.range_comp_subset_range _ _ (h j))⟩

--000Z, better way to say j ≠ i, (j : Fin.succAbove i) or {i}ᶜ
def intoHorn (n : ℕ) (i j : Fin (n + 2)) (hj : j ≠ i) : Δ[n] ⟶ Λ[n + 1, i] where
  app k x := ⟨(standardSimplex.map (δ j)).app k x, by
    rw [Set.ne_univ_iff_exists_not_mem]
    use j
    intro h
    cases h with
     | inl h =>
      simpa using (show j ∈ Set.range (Fin.succAbove j) from Set.range_comp_subset_range _ _ h)
     | inr h => exact hj h⟩

lemma switchtohorn (n : ℕ) (i j : Fin (n + 2)) (hj : j ≠ i) (g : Δ[n+1] ⟶ X) :
  standardSimplex.map (δ j) ≫ g = (intoHorn n i j hj) ≫ hornInclusion _ _ ≫ g := rfl

example : X _[1] → X _[0] := X.map (δ 0).op

def hornD0 : Δ[1] ⟶ Λ[2, 1] := (intoHorn 1 1 0 zero_ne_one)

def hornD2 : Δ[1] ⟶ Λ[2, 1] := by
  refine intoHorn 1 1 2 ?_
  sorry

def HornD0 : Δ[1] ⟶ Λ[2, 2] := by
  refine intoHorn 1 2 0 ?_
  sorry

def HornD1 : Δ[1] ⟶ Λ[2, 2] := by
  refine intoHorn 1 2 1 ?_
  sorry

instance Nonemp (n : ℕ) (i : Fin (n + 2)) : Nonempty (horn (n + 1) i ⟶ X) := by
  sorry

--000Z
def HornMapEmb (n : ℕ) (i : Fin (n + 2)) :
  (Λ[n + 1, i] ⟶ X) → ( ({i}ᶜ : Set (Fin (n + 2))) → (Δ[n] ⟶ X) ) :=
    fun f ⟨j, hj⟩ => (intoHorn n i j hj) ≫ f

def HornMapEmbInjective (n : ℕ) (i : Fin (n + 2)) : Function.Injective (HornMapEmb X n i) := by
  rintro f g h
  ext k x
  sorry

noncomputable
def HornMapEmbInverse (n : ℕ) (i : Fin (n + 2)) :
  ( ({i}ᶜ : Set (Fin (n + 2))) → (Δ[n] ⟶ X) ) → (Λ[n + 1, i] ⟶ X) :=
    Exists.choose (Function.Injective.hasLeftInverse (HornMapEmbInjective X n i))

lemma HornMapEmbInverse1 (n : ℕ) (i : Fin (n + 2)) (f : Λ[n + 1, i] ⟶ X) :
  HornMapEmbInverse X n i (HornMapEmb X n i f) = f :=
    Exists.choose_spec (Function.Injective.hasLeftInverse (HornMapEmbInjective X n i)) f

noncomputable
def transHom {X : SSet.{0}} {a b c : Δ[0] ⟶ X} [IsKan X] :
  Path a b → Path b c → (Λ[2,1] ⟶ X) := by
    rintro ⟨p₀, h0₀, h1₀⟩ ⟨p₂, h0₂, h1₂⟩
    apply HornMapEmbInverse X 1 1
    rintro ⟨j, hj : j ≠ 1⟩
    by_cases j = 0
    exact p₀
    have : j = 2 := sorry
    exact p₂

lemma transHom_compHorn0 {X : SSet.{0}} {a b c : Δ[0] ⟶ X} [IsKan X] (p₀ : Path a b) (p₂ : Path b c) :
  hornD0 ≫ (transHom p₀ p₂) = p₀.p := by
    have h := HornMapEmbInverse1 X 1 1 (transHom p₀ p₂)
    rw [← h]
    dsimp [hornD0]
    simp [transHom, hornD0, intoHorn, HornMapEmbInverse, HornMapEmb]
    sorry

@[simp]
lemma transHom_compHorn2 {X : SSet.{0}} {a b c : Δ[0] ⟶ X} [IsKan X] (p0 : Path a b) (p2 : Path b c) :
  hornD2 ≫ (transHom p0 p2) = p2.p := sorry

lemma aux1 : d1 ≫ D1 = d1 ≫ D2 := by
  have := @δ_comp_δ_self 0 1
  apply_fun (fun a => standardSimplex.map a) at this
  exact this

example : d0 ≫ D1 = d0 ≫ D0 := rfl

lemma aux2 : d0 ≫ D2 = d1 ≫ D0 := by
  have := @δ_comp_δ 0 0 1 (Nat.zero_le 1)
  apply_fun (fun a => standardSimplex.map a) at this
  exact this

noncomputable
def Path.trans {X : SSet.{0}} {a b c : Δ[0] ⟶ X} [IsKan X] :
  Path a b → Path b c → Path a c := by
    intro p₀ p₂
    let g := Exists.choose (IsKan.cond _ _ (transHom p₀ p₂))
    have hg := Exists.choose_spec (IsKan.cond _ _ (transHom p₀ p₂))
    refine ⟨?_, ?_, ?_⟩
    · exact D1 ≫ g
    · change d0 ≫ hornD0 ≫ hornInclusion _ _ ≫ g = a
      rw [← hg, transHom_compHorn0]
      exact p₀.hp0
    · have := aux1
      apply_fun (fun a => a ≫ g) at this
      change d1 ≫ D1 ≫ g = d1 ≫ D2 ≫ g at this
      rw [this]
      change d1 ≫ hornD2 ≫ hornInclusion _ _ ≫ g = c
      rw [← hg, transHom_compHorn2]
      exact p₂.hp1

noncomputable
def symmHom {X : SSet.{0}} {a b : Δ[0] ⟶ X} [IsKan X] :
  Path a b → (Λ[2,2] ⟶ X) := by
    rintro ⟨p, h0, h1⟩
    apply HornMapEmbInverse X 1 2
    rintro ⟨j, hj : j ≠ 2⟩
    by_cases j = 1
    exact p
    have : j = 0 := sorry
    exact standardSimplex.map (σ 0) ≫ a

lemma symmHom_compHorn0 {X : SSet.{0}} {a b : Δ[0] ⟶ X} [IsKan X] (p : Path a b) :
  HornD0 ≫ (symmHom p) = p.p := sorry

@[simp]
lemma symmHom_compHorn1 {X : SSet.{0}} {a b : Δ[0] ⟶ X} [IsKan X] (p : Path a b) :
  HornD1 ≫ (symmHom p) = standardSimplex.map (σ 0) ≫ a := sorry

noncomputable
def Path.symm {X : SSet.{0}} {a b : Δ[0] ⟶ X} [IsKan X] :
  Path a b → Path b a := by
    intro p
    let g := Exists.choose (IsKan.cond _ _ (symmHom p))
    have hg := Exists.choose_spec (IsKan.cond _ _ (symmHom p))
    refine ⟨D2 ≫ g, ?_, ?_⟩
    · have := aux2
      apply_fun (fun a => a ≫ g) at this
      change d0 ≫ D2 ≫ g = d1 ≫ HornD0 ≫ hornInclusion _ _ ≫ g at this
      rw [this, ← hg, symmHom_compHorn0]
      exact p.hp1
    · have := aux1
      apply_fun (fun a => a ≫ g) at this
      change d1 ≫ HornD1 ≫ hornInclusion _ _ ≫ g = d1 ≫ D2 ≫ g at this
      rw [← this, ← hg, symmHom_compHorn1]
      have aux := @δ_comp_σ_succ 0 0
      apply_fun (fun x => (standardSimplex.map x) ≫ a) at aux
      change d1 ≫ standardSimplex.map (σ 0) ≫ a = standardSimplex.map (𝟙 ([0] : SimplexCategory)) ≫ a at aux
      rw [aux]
      ext
      change a.app _ ((standardSimplex.map (𝟙 ([0] : SimplexCategory))).app _ _) = _
      dsimp [standardSimplex]
      simp only [OrderHom.id_comp, Hom.mk_toOrderHom]

noncomputable
def ProdObjIso {X Y : SSet} (n) : (X ⨯ Y).obj n ≅ (X.obj n × Y.obj n) :=
  show ((evaluation _ _).obj n).obj (X ⨯ Y) ≅ _ from
  preservesLimitIso _ _ ≪≫ Limits.HasLimit.isoOfNatIso
    (Limits.pairComp X Y ((evaluation SimplexCategoryᵒᵖ Type).obj n))
    ≪≫ (Types.binaryProductIso _ _)

/-
example (X Y : SSet) (n) : (ProdObjIso X Y n).hom ≫ Limits.prod.fst = (Limits.prod.fst (X := X) (Y := Y)).app n := by
  dsimp [ProdObjIso]
  aesop
-/

def Prod (X Y : SSet) : SSet where
  obj n := X.obj n × Y.obj n
  map f a := (X.map f a.1, Y.map f a.2)

@[simp]
def proj1 {X Y : SSet} : (Prod X Y) ⟶ X where
  app _ a := a.1

@[simp]
def proj2 {X Y : SSet} : (Prod X Y) ⟶ Y where
  app _ a := a.2

@[simps! pt]
def binProdCone (X Y : SSet.{0}) : BinaryFan X Y :=
  BinaryFan.mk (proj1) (proj2)

@[simp]
theorem binProdCone_fst (X Y : SSet) : (binProdCone X Y).fst = proj1 :=
  rfl

@[simp]
theorem binProdCone_snd (X Y : SSet) : (binProdCone X Y).snd = proj2 :=
  rfl

@[simps]
def binProdLim (X Y : SSet) : IsLimit (binProdCone X Y) where
  lift (s : BinaryFan X Y) := {
    app := fun n x => ((s.fst).app n x, (s.snd).app n x)
    naturality := fun j k g => by
      ext a
      simp [FunctorToTypes.naturality]
      congr
  }
  fac _ j := Discrete.recOn j fun j => WalkingPair.casesOn j rfl rfl
  uniq s t ht := by
    simp only [← ht ⟨WalkingPair.right⟩, ← ht ⟨WalkingPair.left⟩]
    congr

def binProdLimCone (X Y : SSet) : Limits.LimitCone (pair X Y) :=
  ⟨_, binProdLim X Y⟩

noncomputable def binProdIso (X Y : SSet) : X ⨯ Y ≅ Prod X Y :=
  limit.isoLimitCone (binProdLimCone X Y)

def IHom (X Y : SSet) : SSet where
  obj n := Prod (standardSimplex.obj n.unop) X ⟶ Y
  map {m n} f F := {
    app := fun k a => F.app k ((standardSimplex.map f.unop).app k a.1, a.2)
    naturality := fun j k g => by
      ext a
      exact congr_fun (F.naturality g) (a.1 ≫ f.unop, a.2)
  }
  map_id _ := by
    dsimp only [standardSimplex]
    aesop_cat

example (X Y Z : SSet) (h : X ≅ Z) : (X ⟶ Y) ≅ (Z ⟶ Y) := ((yoneda.obj Y).mapIso h.op).symm

/- easier way? -/
noncomputable def HomIsoProd {X Y : SSet} : (X ⟶ Y) ≅ (Prod Δ[0] X ⟶ Y) :=
  ((yoneda.obj Y).mapIso ((leftUnitor X).symm ≪≫ (binProdIso Δ[0] X)).op).symm

noncomputable
def IHomZero {X Y : SSet} : (X ⟶ Y) ≅ (IHom X Y) _[0] := HomIsoProd ≪≫ (eqToIso rfl)

def bruh (X Y : SSet) : (Δ[0] ⟶ IHom X Y) ≃ (IHom X Y) _[0] := yonedaEquiv

def homotopy {X Y : SSet.{0}} (f g : X ⟶ Y) :=
  Path (yonedaEquiv.invFun (IHomZero.hom f)) (yonedaEquiv.invFun (IHomZero.hom g))

/-
TODO: Define this in terms of paths.

structure homotopy {X Y : SSet.{0}} (f g : X ⟶ Y) where
  F : Δ[1] ⨯ X ⟶ Y
  F0 : (leftUnitor X).inv ≫ (prod.map d0 (𝟙 X)) ≫ F = f
  F1 : (leftUnitor X).inv ≫ (prod.map d1 (𝟙 X)) ≫ F = g
-/

--class HomotopyInvariant {X : SSet.{0}} (motive : ⦃a b : pt ⟶ X⦄ → Path a b → Sort u) where
--  ind : (rfl : (x : pt ⟶ X) → motive (Path.rfl x)) → ⦃x y : pt ⟶ X⦄ → (p : Path x y) → motive p
--  ind_rfl : (rfl : (x : pt ⟶ X) → motive (Path.rfl x)) → ind rfl (Path.rfl x) = rfl x
