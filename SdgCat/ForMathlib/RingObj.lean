import Mathlib.CategoryTheory.Monoidal.Cartesian.Ring
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian

-- Ring objects: #36913, #37167, #37265, #37263

open Opposite

universe w v u

namespace CategoryTheory

instance : HasForget₂ RingCat.{w} AddGrpCat.{w} where
  forget₂ :=
    { obj X := .of X
      map f := AddGrpCat.ofHom
        { toFun := f.hom, map_zero' := by simp, map_add' := by simp } }

instance : HasForget₂ RingCat.{w} MonCat.{w} where
  forget₂ :=
    { obj X := .of X
      map f := MonCat.ofHom
        { toFun := f.hom, map_one' := by simp, map_mul' := by simp } }


open CartesianMonoidalCategory MonoidalCategory MonoidalClosed

variable {C D : Type*} [Category* C] [Category* D]

namespace Obj

open MonObj

variable [CartesianMonoidalCategory C] [CartesianMonoidalCategory D] (F : C ⥤ D)

variable [BraidedCategory C] [BraidedCategory D]

noncomputable instance (X : C) [Closed X] : (ihom X).Braided := .ofChosenFiniteProducts _

variable [F.Braided]

@[to_additive]
instance (X : C) [MonObj X] [IsCommMonObj X] : IsCommMonObj (F.obj X) where
  mul_comm := by
    rw [Functor.obj.μ_def, ← Functor.LaxBraided.braided_assoc,
      ← F.map_comp, IsCommMonObj.mul_comm]

open Functor MonObj in
instance (R : C) [RingObj R] : RingObj (F.obj R) where
  mul_add := by
    convert (_ ◁ LaxMonoidal.μ F R R ≫ LaxMonoidal.μ F R (R ⊗ R)) ≫= F.congr_map (RingObj.mul_add R)
        using 1
    · simp
    · simp only [obj.μ_def, ← Category.assoc, obj.σ_def, map_comp]
      congr 1
      rw [← cancel_mono (OplaxMonoidal.δ F _ _)]
      simp only [Category.assoc, Monoidal.μ_δ, Category.comp_id, OplaxMonoidal.lift_δ, map_comp,
        comp_lift]
      ext
      · simp only [lift_fst, ← Category.assoc]
        congr 1
        rw [← cancel_mono (OplaxMonoidal.δ F _ _)]
        ext
        · simp [← F.map_comp]
        · simp only [Category.assoc, Monoidal.μ_δ, Category.comp_id, whiskerLeft_snd,
            OplaxMonoidal.δ_snd, ← F.map_comp]
          simp
      · simp only [lift_snd, ← Category.assoc]
        congr 1
        rw [← cancel_mono (OplaxMonoidal.δ F _ _)]
        ext
        · simp [← F.map_comp]
        · simp only [Category.assoc, Monoidal.μ_δ, Category.comp_id, whiskerLeft_snd,
            OplaxMonoidal.δ_snd, ← F.map_comp]
          simp
  add_mul := by
    convert (LaxMonoidal.μ F R R ▷ _ ≫ LaxMonoidal.μ F (R ⊗ R) R) ≫=
      F.congr_map (RingObj.add_mul R) using 1
    · simp
    · simp only [obj.μ_def, obj.σ_def, map_comp, ← Category.assoc]
      congr 1
      rw [← cancel_mono (OplaxMonoidal.δ F _ _)]
      simp only [Category.assoc, Monoidal.μ_δ, Category.comp_id, OplaxMonoidal.lift_δ, map_comp,
        comp_lift]
      ext
      · simp only [lift_fst, ← Category.assoc]
        congr 1
        rw [← cancel_mono (OplaxMonoidal.δ F _ _)]
        ext
        · simp only [Category.assoc, Monoidal.μ_δ, Category.comp_id, whiskerRight_fst,
            OplaxMonoidal.δ_fst, ← F.map_comp]
          simp
        · simp [← F.map_comp]
      · simp only [lift_snd, ← Category.assoc]
        congr 1
        rw [← cancel_mono (OplaxMonoidal.δ F _ _)]
        ext
        · simp only [Category.assoc, Monoidal.μ_δ, Category.comp_id, whiskerRight_fst,
            OplaxMonoidal.δ_fst, ← F.map_comp]
          simp
        · simp [← F.map_comp]

instance (X : C) [CommRingObj X] : CommRingObj (F.obj X) where

open MonObj in
@[to_additive]
instance (X : C) [Closed X] (M : C) [MonObj M] : IsMonHom (MonoidalClosed.curry (snd X M)) where
-- this should probably be generalized to a natural transformation between monoidal functors
-- and this would be the case of `𝟭 C ⟶ ihom X`.
  one_hom := by
    dsimp [Functor.LaxMonoidal.ε, Functor.OplaxMonoidal.η]
    rw [IsIso.eq_inv_comp]
    apply uncurry_injective
    rw [uncurry_ihom_map, uncurry_natural_left, uncurry_natural_left, uncurry_curry,
      whiskerLeft_snd, whiskerLeft_snd_assoc, comp_toUnit_assoc]
    congr
    ext
  mul_hom := by
    dsimp [Functor.LaxMonoidal.μ, Functor.OplaxMonoidal.δ]
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, whiskerLeft_snd,
      uncurry_natural_left, uncurry_natural_left, uncurry_ihom_map]
    dsimp
    rw [← Category.assoc, ← Category.assoc,
      ← whiskerLeft_curry_ihom_ev_app (g := snd X (M ⊗ M)), ← whiskerLeft_comp]
    congr 3
    rw [IsIso.eq_comp_inv]
    ext
    · rw [Category.assoc, prodComparison_fst, tensorHom_fst,
        ← curry_natural_left, ← curry_natural_right, whiskerLeft_snd]
    · rw [Category.assoc, prodComparison_snd, tensorHom_snd,
        ← curry_natural_left, ← curry_natural_right, whiskerLeft_snd]

instance (X : C) [Closed X] (M : C) [RingObj M] : IsRingHom (MonoidalClosed.curry (snd X M)) where

end Obj

section

variable [CartesianMonoidalCategory C] [BraidedCategory C]

namespace RingObj

@[reducible]
def ofRepresentableBy (X : C) (F : Cᵒᵖ ⥤ RingCat.{w})
    (h : (F ⋙ forget _).RepresentableBy X) :
    RingObj X :=
  letI := AddGrpObj.ofRepresentableBy X (F ⋙ forget₂ _ _) h
  letI := MonObj.ofRepresentableBy X (F ⋙ forget₂ _ _) h
  { mul_add := sorry
    add_mul := sorry
    add_comm := sorry }

end RingObj

namespace CommRingObj

@[reducible]
def ofRepresentableBy (X : C) (F : Cᵒᵖ ⥤ CommRingCat.{w})
    (h : (F ⋙ forget _).RepresentableBy X) :
    CommRingObj X :=
  letI := RingObj.ofRepresentableBy X (F ⋙ forget₂ _ _) h
  { mul_comm := sorry }

end CommRingObj

end

end CategoryTheory
