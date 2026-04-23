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

noncomputable def Grp.functorToTypeEquivalence : Grp (J ⥤ Type u) ≌ (J ⥤ GrpCat.{u}) :=
  Grp.functorEquivalence.trans (Equivalence.congrRight grpTypeEquivalenceGrp)

section

variable (P : ObjectProperty C)
  [P.IsClosedUnderLimitsOfShape (Discrete PEmpty)]
  [P.IsClosedUnderLimitsOfShape (Discrete WalkingPair)]

def ObjectProperty.grp : ObjectProperty (Grp C) :=
  P.inverseImage (Grp.forget C)

def Grp.fullSubcategoryEquivalence : Grp P.FullSubcategory ≌ P.grp.FullSubcategory := sorry

end

instance {A : Type*} [Category A] :
    ObjectProperty.IsClosedUnderIsomorphisms (Presheaf.IsSheaf K (A := A)) := sorry

noncomputable def Grp.sheafEquivalence : Grp (Sheaf K (Type u)) ≌ Sheaf K GrpCat.{u} :=
  (fullSubcategoryEquivalence _).trans
    (functorToTypeEquivalence.congrFullSubcategory sorry)

end CategoryTheory
