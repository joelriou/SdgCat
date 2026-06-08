/-
Copyright (c) 2026 Ricky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ricky
-/

import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.Types.Grp
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import SdgCat.ForMathlib.CategoryTheory.Monoidal.Internal.GrpFunctorCategory

/-!
# Equivalences for group objects in functor categories and sheaves

This file collects auxiliary equivalences relating group objects in functor categories,
full subcategories, and sheaves of group-valued presheaves.
-/

universe u

namespace CategoryTheory

open Limits

variable {J C : Type*} [Category J] [Category C] [CartesianMonoidalCategory C]
  {K : GrothendieckTopology J}

@[simps!]
noncomputable def Grp.functorToTypeEquivalence : Grp (J ⥤ Type u) ≌ (J ⥤ GrpCat.{u}) :=
  (Monoidal.grpFunctorCategoryEquivalence J (Type u)).trans
    (Equivalence.congrRight grpTypeEquivalenceGrp)

noncomputable def Grp.functorToTypeEquivalenceFunctorObjCompForgetIso (P : Grp (J ⥤ Type u)) :
    Grp.functorToTypeEquivalence.functor.obj P ⋙ CategoryTheory.forget _ ≅ P.X :=
  Iso.refl _

section

variable (P : ObjectProperty C)

def ObjectProperty.grp : ObjectProperty (Grp C) := P.inverseImage (Grp.forget C)

@[simp]
lemma ObjectProperty.grp_iff (G : Grp C) : P.grp G ↔ P G.X := Iff.rfl

variable [P.IsClosedUnderLimitsOfShape (Discrete PEmpty)]
  [P.IsClosedUnderLimitsOfShape (Discrete WalkingPair)]

namespace Grp.FullSubcategoryEquivalence

instance : P.ι.Monoidal := Functor.CoreMonoidal.toMonoidal
  { εIso := Iso.refl _
    μIso := fun _ _ => Iso.refl _ }

abbrev inverseObj (G : P.grp.FullSubcategory) : Grp P.FullSubcategory := by
  let X : P.FullSubcategory := ⟨G.obj.X, G.property⟩
  haveI : GrpObj (P.ι.obj X) := G.obj.grp
  haveI : GrpObj X := (ObjectProperty.fullyFaithfulι (P := P)).grpObj X
  exact ⟨X⟩

private lemma mapObjIso_one (G : P.grp.FullSubcategory) :
    MonObj.one (X := (P.ι.mapGrp.obj (inverseObj P G)).X) ≫ (Iso.refl G.obj.X).hom =
      MonObj.one (X := G.obj.X) := by
  letI : GrpObj (inverseObj P G).X := (inverseObj P G).grp
  change (Functor.LaxMonoidal.ε P.ι ≫
      P.ι.map (MonObj.one (X := (inverseObj P G).X))) ≫
      (Iso.refl G.obj.X).hom = MonObj.one (X := G.obj.X)
  rw [Functor.FullyFaithful.monObj_one, (ObjectProperty.fullyFaithfulι (P := P)).map_preimage,
    ← Category.assoc, Functor.Monoidal.ε_η]
  simp

private lemma mapObjIso_mul (G : P.grp.FullSubcategory) :
    MonObj.mul (X := (P.ι.mapGrp.obj (inverseObj P G)).X) ≫ (Iso.refl G.obj.X).hom =
      MonoidalCategoryStruct.tensorHom (Iso.refl G.obj.X).hom (Iso.refl G.obj.X).hom ≫
        MonObj.mul (X := G.obj.X) := by
  letI : GrpObj (inverseObj P G).X := (inverseObj P G).grp
  change (Functor.LaxMonoidal.μ P.ι (inverseObj P G).X (inverseObj P G).X ≫
      P.ι.map (MonObj.mul (X := (inverseObj P G).X))) ≫
      (Iso.refl G.obj.X).hom =
    MonoidalCategoryStruct.tensorHom (Iso.refl G.obj.X).hom (Iso.refl G.obj.X).hom ≫
      MonObj.mul (X := G.obj.X)
  rw [Functor.FullyFaithful.monObj_mul, (ObjectProperty.fullyFaithfulι (P := P)).map_preimage,
    ← Category.assoc, Functor.Monoidal.μ_δ, Category.id_comp]
  simpa only using IsMonHom.mul_hom (𝟙 G.obj.X)

def mapObjIso (G : P.grp.FullSubcategory) :
    P.ι.mapGrp.obj (inverseObj P G) ≅ G.obj :=
  Grp.mkIso (Iso.refl G.obj.X) (mapObjIso_one P G) (mapObjIso_mul P G)

def forward : Grp P.FullSubcategory ⥤ P.grp.FullSubcategory :=
  P.grp.lift (P.ι.mapGrp) (fun G => G.X.property)

def inverse : P.grp.FullSubcategory ⥤ Grp P.FullSubcategory where
  obj := inverseObj P
  map {G H} f :=
    ((ObjectProperty.fullyFaithfulι (P := P)).mapGrp).preimage
      (X := inverseObj P G) (Y := inverseObj P H)
      ((mapObjIso P G).hom ≫ f.hom ≫ (mapObjIso P H).inv)
  map_id G := by
    apply ((ObjectProperty.fullyFaithfulι (P := P)).mapGrp).map_injective
    simp
  map_comp {G H I} f g := by
    apply ((ObjectProperty.fullyFaithfulι (P := P)).mapGrp).map_injective
    simp [Category.assoc]

def unitIso : 𝟭 (Grp P.FullSubcategory) ≅ forward P ⋙ inverse P :=
  NatIso.ofComponents
    (fun G ↦ ((ObjectProperty.fullyFaithfulι (P := P)).mapGrp).preimageIso
        (mapObjIso P ((forward P).obj G)).symm) (by
      intro X Y f
      apply ((ObjectProperty.fullyFaithfulι (P := P)).mapGrp).map_injective
      simp [inverse, forward])

def counitIso : inverse P ⋙ forward P ≅ 𝟭 P.grp.FullSubcategory :=
  NatIso.ofComponents (fun G => (P.grp).isoMk (mapObjIso P G)) (by
    intro X Y f
    apply ObjectProperty.hom_ext
    ext
    simp [inverse, forward, Category.assoc])

lemma functor_unitIso_comp (G : Grp P.FullSubcategory) :
    (forward P).map ((unitIso P).hom.app G) ≫ (counitIso P).hom.app ((forward P).obj G) =
      𝟙 ((forward P).obj G) := by
  apply ObjectProperty.hom_ext
  ext
  simp [unitIso, counitIso, forward, inverse]

end Grp.FullSubcategoryEquivalence

noncomputable def Grp.fullSubcategoryEquivalence : Grp P.FullSubcategory ≌
    P.grp.FullSubcategory where
  functor := Grp.FullSubcategoryEquivalence.forward P
  inverse := Grp.FullSubcategoryEquivalence.inverse P
  unitIso := Grp.FullSubcategoryEquivalence.unitIso P
  counitIso := Grp.FullSubcategoryEquivalence.counitIso P
  functor_unitIso_comp := Grp.FullSubcategoryEquivalence.functor_unitIso_comp P

end

instance {A : Type*} [Category A] :
    ObjectProperty.IsClosedUnderIsomorphisms (Presheaf.IsSheaf K (A := A)) where
  of_iso e _ := by rwa [← Presheaf.isSheaf_of_iso_iff e]

lemma GrpCat.isSheaf_iff_forget (P : Jᵒᵖ ⥤ GrpCat.{u}) :
    Presheaf.IsSheaf K P ↔ Presheaf.IsSheaf K (P ⋙ forget _) := by
  rw [Presheaf.isSheaf_iff_isLimit, Presheaf.isSheaf_iff_isLimit]
  constructor
  · intro h X S hS
    rcases h S hS with ⟨hlim⟩
    exact ⟨isLimitOfPreserves (forget GrpCat) hlim⟩
  · intro h X S hS
    rcases h S hS with ⟨hlim⟩
    exact ⟨isLimitOfReflects (forget GrpCat) hlim⟩

noncomputable def Grp.sheafEquivalence : Grp (Sheaf K (Type u)) ≌ Sheaf K GrpCat.{u} :=
  (fullSubcategoryEquivalence _).trans
    (functorToTypeEquivalence.congrFullSubcategory (by
      ext P
      simp only [ObjectProperty.prop_inverseImage_iff, ObjectProperty.grp_iff]
      rw [← Presheaf.isSheaf_of_iso_iff (Grp.functorToTypeEquivalenceFunctorObjCompForgetIso P),
        GrpCat.isSheaf_iff_forget]))

end CategoryTheory
