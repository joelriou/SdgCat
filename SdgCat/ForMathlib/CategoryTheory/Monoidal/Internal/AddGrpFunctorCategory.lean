import Mathlib.CategoryTheory.Monoidal.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
import SdgCat.ForMathlib.CategoryTheory.Monoidal.Internal.AddMonFunctorCategory

/-!
# `AddGrp (C ⥤ D) ≌ C ⥤ AddGrp D`

When `D` is a Cartesian monoidal category, additive group objects in `C ⥤ D` are the same
thing as functors from `C` into the additive group objects of `D`.

This is formalised as:
* `addGrpFunctorCategoryEquivalence : AddGrp (C ⥤ D) ≌ C ⥤ AddGrp D`
-/

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory MonObj
open scoped AddMonObj

namespace CategoryTheory.Monoidal

variable (C : Type u₁) [Category.{v₁} C]
variable (D : Type u₂) [Category.{v₂} D] [CartesianMonoidalCategory.{v₂} D]

namespace AddGrpFunctorCategoryEquivalence

variable {C D}

private lemma lift_app {F G H : C ⥤ D} (f : F ⟶ G) (g : F ⟶ H) (X : C) :
    (CartesianMonoidalCategory.lift f g).app X =
      CartesianMonoidalCategory.lift (f.app X) (g.app X) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [CartesianMonoidalCategory.lift_fst]
    exact congr_app (CartesianMonoidalCategory.lift_fst f g) X
  · rw [CartesianMonoidalCategory.lift_snd]
    exact congr_app (CartesianMonoidalCategory.lift_snd f g) X

private lemma toUnit_app (F : C ⥤ D) (X : C) :
    (SemiCartesianMonoidalCategory.toUnit F).app X =
      SemiCartesianMonoidalCategory.toUnit (F.obj X) :=
  SemiCartesianMonoidalCategory.toUnit_unique _ _

/-- An additive group object in a functor category sends any object to an additive group
object. -/
@[simps]
def functorObjObj (A : C ⥤ D) [AddGrpObj A] (X : C) : AddGrp D where
  X := A.obj X
  addGrp :=
  { zero := ζ[A].app X
    add := σ[A].app X
    zero_add := congr_app (AddMonObj.zero_add A) X
    add_zero := congr_app (AddMonObj.add_zero A) X
    add_assoc := congr_app (AddMonObj.add_assoc A) X
    neg := (AddGrpObj.neg (X := A)).app X
    left_neg := by
      have h := congr_app (AddGrpObj.left_neg A) X
      simp only [NatTrans.comp_app] at h
      rw [lift_app, toUnit_app] at h
      exact h
    right_neg := by
      have h := congr_app (AddGrpObj.right_neg A) X
      simp only [NatTrans.comp_app] at h
      rw [lift_app, toUnit_app] at h
      exact h }

set_option backward.isDefEq.respectTransparency false in
/-- An additive group object in a functor category induces a functor to the category of additive
group objects. -/
@[simps]
def functorObj (A : C ⥤ D) [AddGrpObj A] : C ⥤ AddGrp D where
  obj := functorObjObj A
  map f :=
    AddGrp.homMk' ((AddMonFunctorCategoryEquivalence.functorObj A).map f)
  map_id X := by ext; dsimp; rw [Functor.map_id]
  map_comp f g := by ext; dsimp; rw [Functor.map_comp]

/-- Functor translating an additive group object in a functor category
to a functor into the category of additive group objects.
-/
@[simps]
def functor : AddGrp (C ⥤ D) ⥤ C ⥤ AddGrp D where
  obj A := functorObj A.X
  map f :=
  { app := fun X =>
      AddGrp.homMk' ((AddMonFunctorCategoryEquivalence.functor.map f.hom).app X) }

/-- A functor to the category of additive group objects can be translated as an additive group
object in the functor category. -/
@[simps]
def inverseObj (F : C ⥤ AddGrp D) : AddGrp (C ⥤ D) where
  X := F ⋙ AddGrp.forget D
  addGrp :=
  { zero := { app X := ζ[(F.obj X).X] }
    add := { app X := σ[(F.obj X).X] }
    zero_add := by
      ext X
      exact AddMonObj.zero_add (F.obj X).X
    add_zero := by
      ext X
      exact AddMonObj.add_zero (F.obj X).X
    add_assoc := by
      ext X
      exact AddMonObj.add_assoc (F.obj X).X
    neg :=
      { app X := AddGrpObj.neg (X := (F.obj X).X)
        naturality := by
          intro X Y f
          exact (AddGrpObj.neg_hom ((F.map f).hom.hom)).symm }
    left_neg := by
      ext X
      simp only [NatTrans.comp_app]
      rw [lift_app, toUnit_app]
      exact AddGrpObj.left_neg (F.obj X).X
    right_neg := by
      ext X
      simp only [NatTrans.comp_app]
      rw [lift_app, toUnit_app]
      exact AddGrpObj.right_neg (F.obj X).X }

/-- Functor translating a functor into the category of additive group objects
to an additive group object in the functor category.
-/
@[simps]
def inverse : (C ⥤ AddGrp D) ⥤ AddGrp (C ⥤ D) where
  obj := inverseObj
  map α :=
    AddGrp.homMk''
      { app := fun X => (α.app X).hom.hom
        naturality := fun _ _ f => congr_arg (fun e => e.hom.hom) (α.naturality f) }
      (by
        ext X
        exact IsAddMonHom.zero_hom (α.app X).hom.hom)
      (by
        ext X
        exact IsAddMonHom.add_hom (α.app X).hom.hom)

/-- The unit for the equivalence `AddGrp (C ⥤ D) ≌ C ⥤ AddGrp D`. -/
@[simps!]
def unitIso : 𝟭 (AddGrp (C ⥤ D)) ≅ functor ⋙ inverse :=
  NatIso.ofComponents (fun A => AddGrp.mkIso (Iso.refl A.X)) (by
    intro X Y f
    ext j
    simp [functor, inverse])

/-- The counit for the equivalence `AddGrp (C ⥤ D) ≌ C ⥤ AddGrp D`. -/
@[simps!]
def counitIso : inverse ⋙ functor ≅ 𝟭 (C ⥤ AddGrp D) :=
  NatIso.ofComponents
    (fun A => NatIso.ofComponents (fun X => Iso.refl (A.obj X)) (by
      intro X Y f
      ext
      simp [functor, inverse]))
    (by
      intro X Y f
      ext j
      simp [functor, inverse])

end AddGrpFunctorCategoryEquivalence

open AddGrpFunctorCategoryEquivalence

/-- When `D` is a Cartesian monoidal category, additive group objects in `C ⥤ D` are the same
thing as functors from `C` into the additive group objects of `D`. -/
@[simps]
def addGrpFunctorCategoryEquivalence : AddGrp (C ⥤ D) ≌ C ⥤ AddGrp D where
  functor := functor
  inverse := inverse
  unitIso := unitIso
  counitIso := counitIso

end CategoryTheory.Monoidal

