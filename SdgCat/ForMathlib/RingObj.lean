import Mathlib.CategoryTheory.Monoidal.Cartesian.Ring
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian

-- Ring objects: #36913, #37167, #37265, #37263, #37587

open Opposite

universe w v u

@[mk_iff]
structure IsAddMonoidHom {R₁ R₂ : Type*} [AddMonoid R₁] [AddMonoid R₂] (f : R₁ → R₂) : Prop where
  map_zero : f 0 = 0
  map_add (x y : R₁) : f (x + y) = f x + f y

@[to_additive, mk_iff]
structure IsMonoidHom {R₁ R₂ : Type*} [Monoid R₁] [Monoid R₂] (f : R₁ → R₂) : Prop where
  map_one : f 1 = 1
  map_mul (x y : R₁) : f (x * y) = f x * f y

attribute [to_additive existing] isMonoidHom_iff

lemma isAddMonoidHom_comp_iff_of_injective
    {R₁ R₂ R₃ : Type*} [AddMonoid R₁] [AddMonoid R₂] [AddMonoid R₃] (f : R₁ → R₂) (e : R₂ →+ R₃)
    (he : Function.Injective e) :
    IsAddMonoidHom (e ∘ f) ↔ IsAddMonoidHom f := by
  simp [isAddMonoidHom_iff, ← he.eq_iff]

@[to_additive existing]
lemma isMonoidHom_comp_iff_of_injective
    {R₁ R₂ R₃ : Type*} [Monoid R₁] [Monoid R₂] [Monoid R₃] (f : R₁ → R₂) (e : R₂ →* R₃)
    (he : Function.Injective e) :
    IsMonoidHom (e ∘ f) ↔ IsMonoidHom f := by
  simp [isMonoidHom_iff, ← he.eq_iff]

@[mk_iff]
structure IsRingHom {R₁ R₂ : Type*} [Ring R₁] [Ring R₂] (f : R₁ → R₂)
  extends IsMonoidHom f, IsAddMonoidHom f

lemma isRingHom_comp_iff_of_injective
    {R₁ R₂ R₃ : Type*} [Ring R₁] [Ring R₂] [Ring R₃] (f : R₁ → R₂) (e : R₂ →+* R₃)
    (he : Function.Injective e) :
    IsRingHom (e ∘ f) ↔ IsRingHom f := by
  simp [isRingHom_iff, ← isMonoidHom_comp_iff_of_injective f e.toMonoidHom he,
    ← isAddMonoidHom_comp_iff_of_injective f e.toAddMonoidHom he]

lemma RingHom.isRingHom {R₁ R₂ : Type*} [Ring R₁] [Ring R₂] (f : R₁ →+* R₂) : IsRingHom f where
  map_one := by simp
  map_zero := by simp
  map_mul := by simp
  map_add := by simp

namespace CategoryTheory

open CartesianMonoidalCategory MonoidalCategory MonoidalClosed

variable {C D : Type*} [Category* C] [Category* D]
  [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]

section

open MonObj RingObj

attribute [mk_iff] CategoryTheory.IsMonHom CategoryTheory.IsAddMonHom CategoryTheory.IsRingHom

attribute [to_additive existing] CategoryTheory.isMonHom_iff

@[to_additive]
lemma map_one_iff {M₁ M₂ : C} [MonObj M₁] [MonObj M₂] (f : M₁ ⟶ M₂) :
    η ≫ f = η ↔ ∀ (X : C), (1 : X ⟶ M₁) ≫ f = 1 := by
  simp only [Hom.one_def, Category.assoc]
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · simp [hf]
  · rw [← cancel_epi (𝟙 _), Subsingleton.elim (𝟙 _) (toUnit (𝟙_ C)), hf]

@[to_additive]
lemma map_mul_iff {M₁ M₂ : C} [MonObj M₁] [MonObj M₂] (f : M₁ ⟶ M₂) :
    μ ≫ f = (f ⊗ₘ f) ≫ μ ↔ ∀ ⦃X : C⦄ (x y : X ⟶ M₁), (x * y) ≫ f = (x ≫ f) * (y ≫ f) := by
  simp only [Hom.mul_def, Category.assoc]
  refine ⟨fun hf X x y ↦ ?_, fun hf ↦ ?_⟩
  · simpa using lift x y ≫= hf
  · simpa using hf (fst M₁ M₁) (snd M₁ M₁)

@[to_additive]
lemma isMonHom_iff_yoneda {M₁ M₂ : C} [MonObj M₁] [MonObj M₂] (f : M₁ ⟶ M₂) :
    IsMonHom f ↔ ∀ (X : C),
      _root_.IsMonoidHom (R₁ := X ⟶ M₁) (R₂ := X ⟶ M₂) ((yoneda.map f).app (op X)) := by
  simp only [isMonHom_iff, _root_.isMonoidHom_iff, map_one_iff, map_mul_iff, forall_and,
    yoneda_map_app, yoneda_obj_obj, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk]

variable [BraidedCategory C]

lemma isRingHom_iff_yoneda {R₁ R₂ : C} [RingObj R₁] [RingObj R₂] (f : R₁ ⟶ R₂) :
    IsRingHom f ↔ ∀ (X : C),
      _root_.IsRingHom (R₁ := X ⟶ R₁) (R₂ := X ⟶ R₂) ((yoneda.map f).app (op X)) := by
  simp only [isRingHom_iff, _root_.isRingHom_iff, isMonHom_iff_yoneda,
    isAddMonHom_iff_yoneda, forall_and]
  tauto

end


instance : HasForget₂ RingCat.{w} AddGrpCat.{w} where
  forget₂ :=
    { obj X := .of X
      map f := AddGrpCat.ofHom
        { toFun := f.hom, map_zero' := by simp, map_add' := by simp } }

instance : HasForget₂ RingCat.{w} AddMonCat.{w} where
  forget₂ :=
    { obj X := .of X
      map f := AddMonCat.ofHom
        { toFun := f.hom, map_zero' := by simp, map_add' := by simp } }

instance : HasForget₂ RingCat.{w} MonCat.{w} where
  forget₂ :=
    { obj X := .of X
      map f := MonCat.ofHom
        { toFun := f.hom, map_one' := by simp, map_mul' := by simp } }

namespace Obj

open MonObj

variable (F : C ⥤ D) [BraidedCategory C] [BraidedCategory D]

-- to be moved...
noncomputable instance (X : C) [Closed X] : (ihom X).IsRightAdjoint :=
  (ihom.adjunction X).isRightAdjoint

noncomputable instance (X : C) [Closed X] : (ihom X).Monoidal := .ofChosenFiniteProducts _

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

variable [CartesianMonoidalCategory C]

open MonObj

namespace MonObj

@[to_additive]
abbrev ofRepresentableByHomMulEquiv
    {M : C} {F : Cᵒᵖ ⥤ MonCat.{w}} (h : (F ⋙ forget _).RepresentableBy M)
    {X : C} :
    letI := MonObj.ofRepresentableBy M F h
    (X ⟶ M) ≃* F.obj (op X) :=
  letI := MonObj.ofRepresentableBy M F h
  { toEquiv := h.homEquiv
    map_mul' x y := by
      dsimp [HMul.hMul, Mul.mul]
      have h₁ := h.homEquiv_comp (lift x y) (fst _ _)
      have h₂ := h.homEquiv_comp (lift x y) (snd _ _)
      rw [lift_fst] at h₁
      rw [lift_snd] at h₂
      erw [h₁, h₂, h.homEquiv_comp, Equiv.apply_symm_apply]
      apply (F.map (lift x y).op).hom.map_mul }

end MonObj

scoped[CategoryTheory.AddMonObj] attribute [instance] Hom.addMonoid

namespace RingObj

open AddMonObj

attribute [to_additive] IsCommMonObj.ofRepresentableBy

@[reducible]
def ofRepresentableBy [BraidedCategory C] (R : C) (F : Cᵒᵖ ⥤ RingCat.{w})
    (h : (F ⋙ forget _).RepresentableBy R) :
    RingObj R :=
  letI := AddGrpObj.ofRepresentableBy R (F ⋙ forget₂ _ _) h
  letI := MonObj.ofRepresentableBy R (F ⋙ forget₂ _ _) h
  letI e {X : C} : (X ⟶ R) ≃ F.obj (op X) := h.homEquiv
  have map_mul {X : C} (x y : X ⟶ R) : e (x * y) = e x * e y :=
    (MonObj.ofRepresentableByHomMulEquiv (F := F ⋙ forget₂ _ _) h).map_mul x y
  have map_add {X : C} (x y : X ⟶ R) : e (x + y) = e x + e y :=
    (AddMonObj.ofRepresentableByHomAddEquiv (F := F ⋙ forget₂ _ _) h).map_add x y
  have : IsCommAddMonObj R := by
    rw [isCommAddMonObj_iff_isAddCommutative]
    refine fun X ↦ ⟨⟨fun x y ↦ e.injective (by rw [map_add, map_add, add_comm])⟩⟩
  { mul_add := by
      rw [mul_add_iff]
      intro X a b c
      exact e.injective (by simp only [map_mul, map_add, LeftDistribClass.left_distrib])
    add_mul := by
      rw [add_mul_iff]
      intro X a b c
      exact e.injective (by simp only [map_mul, map_add, RightDistribClass.right_distrib]) }

open scoped AddMonObj MonObj RingObj

abbrev ofRepresentableByHomRingEquiv [BraidedCategory C]
    {R : C} {F : Cᵒᵖ ⥤ RingCat.{w}} (h : (F ⋙ forget _).RepresentableBy R)
    {X : C} :
    letI := RingObj.ofRepresentableBy R F h
    (X ⟶ R) ≃+* F.obj (op X) :=
  letI := RingObj.ofRepresentableBy R F h
  { toEquiv := h.homEquiv
    map_add' := (AddMonObj.ofRepresentableByHomAddEquiv (F := F ⋙ forget₂ _ _) h).map_add
    map_mul' := (MonObj.ofRepresentableByHomMulEquiv (F := F ⋙ forget₂ _ _) h).map_mul }

end RingObj

namespace CommRingObj

@[reducible]
def ofRepresentableBy [BraidedCategory C] (R : C) (F : Cᵒᵖ ⥤ CommRingCat.{w})
    (h : (F ⋙ forget _).RepresentableBy R) :
    CommRingObj R :=
  letI := RingObj.ofRepresentableBy R (F ⋙ forget₂ _ _) h
  have : IsCommMonObj R := by
    rw [isCommMonObj_iff_isMulCommutative]
    refine fun X ↦ ⟨⟨fun x y ↦ ?_⟩⟩
    let e : (X ⟶ R) ≃* F.obj (op X) :=
      MonObj.ofRepresentableByHomMulEquiv (F := F ⋙ forget₂ _ RingCat ⋙ forget₂ _ _) h (X := X)
    exact e.injective (by rw [e.map_mul, e.map_mul, mul_comm])
  { }

abbrev ofRepresentableByHomRingEquiv [BraidedCategory C]
    {R : C} {F : Cᵒᵖ ⥤ CommRingCat.{w}} (h : (F ⋙ forget _).RepresentableBy R)
    {X : C} :
    letI := CommRingObj.ofRepresentableBy R F h
    (X ⟶ R) ≃+* F.obj (op X) :=
  RingObj.ofRepresentableByHomRingEquiv (F := F ⋙ forget₂ _ _) h

end CommRingObj

end CategoryTheory
