import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory

set_option linter.style.header false

/-!
# `AddMon (C ⥤ D) ≌ C ⥤ AddMon D`

When `D` is a monoidal category, additive monoid objects in `C ⥤ D` are the same
thing as functors from `C` into the additive monoid objects of `D`.

This is formalised as:
* `addMonFunctorCategoryEquivalence : AddMon (C ⥤ D) ≌ C ⥤ AddMon D`
-/

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory MonObj
open scoped AddMonObj

namespace CategoryTheory.Monoidal

variable (C : Type u₁) [Category.{v₁} C]
variable (D : Type u₂) [Category.{v₂} D] [MonoidalCategory.{v₂} D]

namespace AddMonFunctorCategoryEquivalence

variable {C D}

/-- An additive monoid object in a functor category sends any object to an additive monoid
object. -/
@[simps]
def functorObjObj (A : C ⥤ D) [AddMonObj A] (X : C) : AddMon D where
  X := A.obj X
  addMon :=
  { zero := ζ[A].app X
    add := σ[A].app X
    zero_add := congr_app (AddMonObj.zero_add A) X
    add_zero := congr_app (AddMonObj.add_zero A) X
    add_assoc := congr_app (AddMonObj.add_assoc A) X }

set_option backward.isDefEq.respectTransparency false in
/-- An additive monoid object in a functor category induces a functor to the category of
additive monoid objects. -/
@[simps]
def functorObj (A : C ⥤ D) [AddMonObj A] : C ⥤ AddMon D where
  obj := functorObjObj A
  map f :=
    { hom := A.map f
      isAddMonHom_hom :=
        { zero_hom := by simpa using (ζ[A].naturality f).symm
          add_hom := by simpa [tensorObj_map] using (σ[A].naturality f).symm } }
  map_id X := by ext; dsimp; rw [Functor.map_id]
  map_comp f g := by ext; dsimp; rw [Functor.map_comp]

/-- Functor translating an additive monoid object in a functor category
to a functor into the category of additive monoid objects.
-/
@[simps]
def functor : AddMon (C ⥤ D) ⥤ C ⥤ AddMon D where
  obj A := functorObj A.X
  map f :=
  { app := fun X =>
    { hom := f.hom.app X
      isAddMonHom_hom :=
        { zero_hom := congr_app (IsAddMonHom.zero_hom f.hom) X
          add_hom := congr_app (IsAddMonHom.add_hom f.hom) X } } }

/-- A functor to the category of additive monoid objects can be translated as an additive monoid
object in the functor category. -/
@[simps]
def inverseObj (F : C ⥤ AddMon D) : AddMon (C ⥤ D) where
  X := F ⋙ AddMon.forget D
  addMon :=
  { zero := { app X := ζ[(F.obj X).X] }
    add := { app X := σ[(F.obj X).X] } }

/-- Functor translating a functor into the category of additive monoid objects
to an additive monoid object in the functor category.
-/
@[simps]
def inverse : (C ⥤ AddMon D) ⥤ AddMon (C ⥤ D) where
  obj := inverseObj
  map α := .mk'
    { app := fun X => (α.app X).hom
      naturality := fun _ _ f => congr_arg AddMon.Hom.hom (α.naturality f) }

/-- The unit for the equivalence `AddMon (C ⥤ D) ≌ C ⥤ AddMon D`. -/
@[simps!]
def unitIso : 𝟭 (AddMon (C ⥤ D)) ≅ functor ⋙ inverse :=
  NatIso.ofComponents (fun A =>
  { hom := .mk' { app := fun _ => 𝟙 _ }
    inv := .mk' { app := fun _ => 𝟙 _ } })

set_option backward.isDefEq.respectTransparency false in
/-- The counit for the equivalence `AddMon (C ⥤ D) ≌ C ⥤ AddMon D`. -/
@[simps!]
def counitIso : inverse ⋙ functor ≅ 𝟭 (C ⥤ AddMon D) :=
  NatIso.ofComponents (fun A =>
    NatIso.ofComponents (fun X => { hom := { hom := 𝟙 _ }, inv := { hom := 𝟙 _ } }))

end AddMonFunctorCategoryEquivalence

open AddMonFunctorCategoryEquivalence

/-- When `D` is a monoidal category, additive monoid objects in `C ⥤ D` are the same thing as
functors from `C` into the additive monoid objects of `D`. -/
@[simps]
def addMonFunctorCategoryEquivalence : AddMon (C ⥤ D) ≌ C ⥤ AddMon D where
  functor := functor
  inverse := inverse
  unitIso := unitIso
  counitIso := counitIso

end CategoryTheory.Monoidal
