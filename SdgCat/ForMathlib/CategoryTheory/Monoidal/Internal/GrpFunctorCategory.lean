import Mathlib.CategoryTheory.Monoidal.Grp
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory

set_option linter.style.header false

/-!
# `Grp (C ⥤ D) ≌ C ⥤ Grp D`

When `D` is a Cartesian monoidal category, group objects in `C ⥤ D` are the same
thing as functors from `C` into the group objects of `D`.

This is formalised as:
* `grpFunctorCategoryEquivalence : Grp (C ⥤ D) ≌ C ⥤ Grp D`
-/

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory MonObj

namespace CategoryTheory.Monoidal

variable (C : Type u₁) [Category.{v₁} C]
variable (D : Type u₂) [Category.{v₂} D] [CartesianMonoidalCategory.{v₂} D]

namespace GrpFunctorCategoryEquivalence

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

/-- A group object in a functor category sends any object to a group object. -/
@[simps]
def functorObjObj (A : C ⥤ D) [GrpObj A] (X : C) : Grp D where
  X := A.obj X
  grp :=
  { one := η[A].app X
    mul := μ[A].app X
    one_mul := congr_app (one_mul A) X
    mul_one := congr_app (mul_one A) X
    mul_assoc := congr_app (mul_assoc A) X
    inv := ι[A].app X
    left_inv := by
      have h := congr_app (GrpObj.left_inv A) X
      simp only [NatTrans.comp_app] at h
      rw [lift_app, toUnit_app] at h
      exact h
    right_inv := by
      have h := congr_app (GrpObj.right_inv A) X
      simp only [NatTrans.comp_app] at h
      rw [lift_app, toUnit_app] at h
      exact h }

set_option backward.isDefEq.respectTransparency false in
/-- A group object in a functor category induces a functor to the category of group objects. -/
@[simps]
def functorObj (A : C ⥤ D) [GrpObj A] : C ⥤ Grp D where
  obj := functorObjObj A
  map f :=
    Grp.homMk' ((MonFunctorCategoryEquivalence.functorObj A).map f)
  map_id X := by ext; dsimp; rw [Functor.map_id]
  map_comp f g := by ext; dsimp; rw [Functor.map_comp]

/-- Functor translating a group object in a functor category
to a functor into the category of group objects.
-/
@[simps]
def functor : Grp (C ⥤ D) ⥤ C ⥤ Grp D where
  obj A := functorObj A.X
  map f :=
  { app := fun X =>
      Grp.homMk' ((MonFunctorCategoryEquivalence.functor.map f.hom).app X) }

/-- A functor to the category of group objects can be translated as a group object
in the functor category. -/
@[simps]
def inverseObj (F : C ⥤ Grp D) : Grp (C ⥤ D) where
  X := F ⋙ Grp.forget D
  grp :=
  { one := { app X := η[(F.obj X).X] }
    mul := { app X := μ[(F.obj X).X] }
    one_mul := by
      ext X
      exact one_mul (F.obj X).X
    mul_one := by
      ext X
      exact mul_one (F.obj X).X
    mul_assoc := by
      ext X
      exact mul_assoc (F.obj X).X
    inv :=
      { app X := ι[(F.obj X).X]
        naturality := by
          intro X Y f
          exact (GrpObj.inv_hom ((F.map f).hom.hom)).symm }
    left_inv := by
      ext X
      simp only [NatTrans.comp_app]
      rw [lift_app, toUnit_app]
      exact GrpObj.left_inv (F.obj X).X
    right_inv := by
      ext X
      simp only [NatTrans.comp_app]
      rw [lift_app, toUnit_app]
      exact GrpObj.right_inv (F.obj X).X }

/-- Functor translating a functor into the category of group objects
to a group object in the functor category.
-/
@[simps]
def inverse : (C ⥤ Grp D) ⥤ Grp (C ⥤ D) where
  obj := inverseObj
  map α :=
    Grp.homMk''
      { app := fun X => (α.app X).hom.hom
        naturality := fun _ _ f => congr_arg (fun e => e.hom.hom) (α.naturality f) }
      (by
        ext X
        exact IsMonHom.one_hom (α.app X).hom.hom)
      (by
        ext X
        exact IsMonHom.mul_hom (α.app X).hom.hom)

/-- The unit for the equivalence `Grp (C ⥤ D) ≌ C ⥤ Grp D`. -/
@[simps!]
def unitIso : 𝟭 (Grp (C ⥤ D)) ≅ functor ⋙ inverse :=
  NatIso.ofComponents (fun A => Grp.mkIso (Iso.refl A.X)) (by
    intro X Y f
    ext j
    simp [functor, inverse])

/-- The counit for the equivalence `Grp (C ⥤ D) ≌ C ⥤ Grp D`. -/
@[simps!]
def counitIso : inverse ⋙ functor ≅ 𝟭 (C ⥤ Grp D) :=
  NatIso.ofComponents
    (fun A => NatIso.ofComponents (fun X => Iso.refl (A.obj X)) (by
      intro X Y f
      ext
      simp [functor, inverse]))
    (by
      intro X Y f
      ext j
      simp [functor, inverse])

end GrpFunctorCategoryEquivalence

open GrpFunctorCategoryEquivalence

/-- When `D` is a Cartesian monoidal category,
group objects in `C ⥤ D` are the same thing
as functors from `C` into the group objects of `D`.
-/
@[simps]
def grpFunctorCategoryEquivalence : Grp (C ⥤ D) ≌ C ⥤ Grp D where
  functor := functor
  inverse := inverse
  unitIso := unitIso
  counitIso := counitIso

end CategoryTheory.Monoidal
