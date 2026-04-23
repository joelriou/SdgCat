import Mathlib.CategoryTheory.Monoidal.Internal.Types.Grp_
import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import Mathlib.CategoryTheory.Sites.CartesianMonoidal

universe u

namespace CategoryTheory

open Limits

variable {J C : Type*} [Category J] [Category C] [CartesianMonoidalCategory C]
  {K : GrothendieckTopology J}

-- the same should be done for `Mon`, `AddMon`, `AddGrp`, `Rng`, `CommRng` in place of `Grp`

def Grp.functorEquivalence : Grp (J ⥤ C) ≌ (J ⥤ Grp C) := sorry

@[simps!]
noncomputable def Grp.functorToTypeEquivalence : Grp (J ⥤ Type u) ≌ (J ⥤ GrpCat.{u}) :=
  Grp.functorEquivalence.trans (Equivalence.congrRight grpTypeEquivalenceGrp)

def Grp.functorToTypeEquivalenceFunctorObjCompForgetIso (P : Grp (J ⥤ Type u)) :
    Grp.functorToTypeEquivalence.functor.obj P ⋙ CategoryTheory.forget _ ≅ P.X :=
  -- should be `Iso.refl _`
  sorry

section

variable (P : ObjectProperty C)

def ObjectProperty.grp : ObjectProperty (Grp C) :=
  P.inverseImage (Grp.forget C)

@[simp]
lemma ObjectProperty.grp_iff (G : Grp C) : P.grp G ↔ P G.X := Iff.rfl

variable [P.IsClosedUnderLimitsOfShape (Discrete PEmpty)]
  [P.IsClosedUnderLimitsOfShape (Discrete WalkingPair)]

def Grp.fullSubcategoryEquivalence : Grp P.FullSubcategory ≌ P.grp.FullSubcategory := sorry

end

instance {A : Type*} [Category A] :
    ObjectProperty.IsClosedUnderIsomorphisms (Presheaf.IsSheaf K (A := A)) where
  of_iso e _ := by rwa [← Presheaf.isSheaf_of_iso_iff e]

lemma GrpCat.isSheaf_iff_forget (P : Jᵒᵖ ⥤ GrpCat.{u}) :
    Presheaf.IsSheaf K P ↔ Presheaf.IsSheaf K (P ⋙ forget _) := by
  sorry

noncomputable def Grp.sheafEquivalence : Grp (Sheaf K (Type u)) ≌ Sheaf K GrpCat.{u} :=
  (fullSubcategoryEquivalence _).trans
    (functorToTypeEquivalence.congrFullSubcategory (by
      ext P
      simp only [ObjectProperty.prop_inverseImage_iff, ObjectProperty.grp_iff]
      rw [← Presheaf.isSheaf_of_iso_iff (Grp.functorToTypeEquivalenceFunctorObjCompForgetIso P),
        GrpCat.isSheaf_iff_forget]))

end CategoryTheory
