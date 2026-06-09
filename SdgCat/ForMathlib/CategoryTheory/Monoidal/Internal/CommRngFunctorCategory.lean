import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory

/-!
# `CommRingObjCat (C ⥤ D) ≌ C ⥤ CommRingObjCat D`

When `D` is a Cartesian monoidal category, commutative ring objects in `C ⥤ D` are the same
thing as functors from `C` into the commutative ring objects of `D`.

This is formalised as:
* `commRngFunctorCategoryEquivalence :
    CommRingObjCat (C ⥤ D) ≌ C ⥤ CommRingObjCat D`
-/

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory MonObj
open scoped AddMonObj

namespace CategoryTheory.Monoidal

variable (C : Type u₁) [Category.{v₁} C]
variable (D : Type u₂) [Category.{v₂} D] [CartesianMonoidalCategory.{v₂} D]
  [BraidedCategory D]

namespace CommRngFunctorCategoryEquivalence

variable {C D}

omit [BraidedCategory D] in
private lemma lift_app {F G H : C ⥤ D} (f : F ⟶ G) (g : F ⟶ H) (X : C) :
    (CartesianMonoidalCategory.lift f g).app X =
      CartesianMonoidalCategory.lift (f.app X) (g.app X) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [CartesianMonoidalCategory.lift_fst]
    exact congr_app (CartesianMonoidalCategory.lift_fst f g) X
  · rw [CartesianMonoidalCategory.lift_snd]
    exact congr_app (CartesianMonoidalCategory.lift_snd f g) X

omit [BraidedCategory D] in
private lemma toUnit_app (F : C ⥤ D) (X : C) :
    (SemiCartesianMonoidalCategory.toUnit F).app X =
      SemiCartesianMonoidalCategory.toUnit (F.obj X) :=
  SemiCartesianMonoidalCategory.toUnit_unique _ _

/-- A commutative ring object in a functor category sends any object to a commutative ring
object. -/
@[simps]
def functorObjObj (A : C ⥤ D) [CommRingObj A] (X : C) : CommRingObjCat D where
  X := A.obj X
  commRingObj :=
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
      exact h
    add_comm := congr_app (IsCommAddMonObj.add_comm A) X
    one := η[A].app X
    mul := μ[A].app X
    one_mul := congr_app (one_mul A) X
    mul_one := congr_app (mul_one A) X
    mul_assoc := congr_app (mul_assoc A) X
    mul_add := by
      have h := congr_app (RingObj.mul_add A) X
      simp only [NatTrans.comp_app] at h
      rw [lift_app] at h
      exact h
    add_mul := by
      have h := congr_app (RingObj.add_mul A) X
      simp only [NatTrans.comp_app] at h
      rw [lift_app] at h
      exact h
    mul_comm := congr_app (IsCommMonObj.mul_comm A) X }

set_option backward.isDefEq.respectTransparency false in
/-- A commutative ring object in a functor category induces a functor to the category of
commutative ring objects. -/
@[simps]
def functorObj (A : C ⥤ D) [CommRingObj A] : C ⥤ CommRingObjCat D where
  obj := functorObjObj A
  map f :=
    { hom := A.map f
      isRingHom :=
        { zero_hom := by simpa using (ζ[A].naturality f).symm
          add_hom := by simpa [tensorObj_map] using (σ[A].naturality f).symm
          one_hom := by simpa using (η[A].naturality f).symm
          mul_hom := by simpa [tensorObj_map] using (μ[A].naturality f).symm } }
  map_id X := by ext; dsimp; rw [Functor.map_id]
  map_comp f g := by ext; dsimp; rw [Functor.map_comp]

/-- Functor translating a commutative ring object in a functor category to a functor into
commutative ring objects. -/
@[simps]
def functor : CommRingObjCat (C ⥤ D) ⥤ C ⥤ CommRingObjCat D where
  obj A := functorObj A.X
  map f :=
  { app := fun X =>
    { hom := f.hom.app X
      isRingHom :=
        { zero_hom := congr_app (IsAddMonHom.zero_hom f.hom) X
          add_hom := congr_app (IsAddMonHom.add_hom f.hom) X
          one_hom := congr_app (IsMonHom.one_hom f.hom) X
          mul_hom := congr_app (IsMonHom.mul_hom f.hom) X } } }

/-- A functor to the category of commutative ring objects can be translated as a commutative ring
object in the functor category. -/
@[simps]
def inverseObj (F : C ⥤ CommRingObjCat D) : CommRingObjCat (C ⥤ D) where
  X := F ⋙ CommRingObjCat.forget D
  commRingObj :=
  { zero := { app X := ζ[(F.obj X).X] }
    add := { app X := σ[(F.obj X).X] }
    zero_add := by ext X; exact AddMonObj.zero_add (F.obj X).X
    add_zero := by ext X; exact AddMonObj.add_zero (F.obj X).X
    add_assoc := by ext X; exact AddMonObj.add_assoc (F.obj X).X
    neg :=
      { app X := AddGrpObj.neg (X := (F.obj X).X)
        naturality := by
          intro X Y f
          exact (AddGrpObj.neg_hom (F.map f).hom).symm }
    left_neg := by
      ext X
      simp only [NatTrans.comp_app]
      rw [lift_app, toUnit_app]
      exact AddGrpObj.left_neg (F.obj X).X
    right_neg := by
      ext X
      simp only [NatTrans.comp_app]
      rw [lift_app, toUnit_app]
      exact AddGrpObj.right_neg (F.obj X).X
    add_comm := by ext X; exact IsCommAddMonObj.add_comm (F.obj X).X
    one := { app X := η[(F.obj X).X] }
    mul := { app X := μ[(F.obj X).X] }
    one_mul := by ext X; exact one_mul (F.obj X).X
    mul_one := by ext X; exact mul_one (F.obj X).X
    mul_assoc := by ext X; exact mul_assoc (F.obj X).X
    mul_add := by
      ext X
      simp only [NatTrans.comp_app]
      rw [lift_app]
      exact RingObj.mul_add (F.obj X).X
    add_mul := by
      ext X
      simp only [NatTrans.comp_app]
      rw [lift_app]
      exact RingObj.add_mul (F.obj X).X
    mul_comm := by ext X; exact IsCommMonObj.mul_comm (F.obj X).X }

/-- Functor translating a functor into the category of commutative ring objects to a commutative
ring object in the functor category. -/
@[simps]
def inverse : (C ⥤ CommRingObjCat D) ⥤ CommRingObjCat (C ⥤ D) where
  obj := inverseObj
  map α :=
    { hom :=
        { app := fun X => (α.app X).hom
          naturality := fun _ _ f => congr_arg CommRingObjCat.Hom.hom (α.naturality f) }
      isRingHom :=
        { zero_hom := by ext X; exact IsAddMonHom.zero_hom (α.app X).hom
          add_hom := by ext X; exact IsAddMonHom.add_hom (α.app X).hom
          one_hom := by ext X; exact IsMonHom.one_hom (α.app X).hom
          mul_hom := by ext X; exact IsMonHom.mul_hom (α.app X).hom } }

/-- The unit for the equivalence `CommRingObjCat (C ⥤ D) ≌ C ⥤ CommRingObjCat D`. -/
@[simps!]
def unitIso : 𝟭 (CommRingObjCat (C ⥤ D)) ≅ functor ⋙ inverse :=
  NatIso.ofComponents (fun A =>
  { hom := { hom := 𝟙 _, isRingHom := { } }
    inv := { hom := 𝟙 _, isRingHom := { } } })

/-- The counit for the equivalence `CommRingObjCat (C ⥤ D) ≌ C ⥤ CommRingObjCat D`. -/
@[simps!]
def counitIso : inverse ⋙ functor ≅ 𝟭 (C ⥤ CommRingObjCat D) :=
  NatIso.ofComponents (fun A =>
    NatIso.ofComponents (fun X =>
      { hom := { hom := 𝟙 _, isRingHom := { } }
        inv := { hom := 𝟙 _, isRingHom := { } } }))

end CommRngFunctorCategoryEquivalence

open CommRngFunctorCategoryEquivalence

/-- When `D` is a Cartesian monoidal category, commutative ring objects in `C ⥤ D` are the same
thing as functors from `C` into the commutative ring objects of `D`. -/
@[simps]
def commRngFunctorCategoryEquivalence : CommRingObjCat (C ⥤ D) ≌ C ⥤ CommRingObjCat D where
  functor := functor
  inverse := inverse
  unitIso := unitIso
  counitIso := counitIso

end CategoryTheory.Monoidal

