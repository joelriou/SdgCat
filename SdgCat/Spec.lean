import Mathlib.Algebra.DualNumber
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.CategoryTheory.Comma.CardinalArrow
import Mathlib.CategoryTheory.Limits.Shapes.WideEqualizers
import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import Mathlib.CategoryTheory.Monoidal.Cartesian.Ring
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian

-- Ring objects: #36913, #37167, #37265, #37263

open Opposite

universe w v u

namespace CategoryTheory.Limits

open WalkingParallelFamily in
noncomputable instance {J : Type w} [Finite J] : FinCategory (WalkingParallelFamily J) where
  fintypeObj :=
    Fintype.ofSurjective (Bool.rec .zero .one) (by
      rintro (_ | _)
      · exact ⟨false, rfl⟩
      · exact ⟨true, rfl⟩)
  fintypeHom := by
    rintro (_ | _) (_ | _)
    · have : Subsingleton ((zero : WalkingParallelFamily J) ⟶ zero) := ⟨by rintro ⟨⟩ ⟨⟩; rfl⟩
      apply +allowSynthFailures Fintype.ofSubsingleton (𝟙 _)
    · have : Finite ((zero : WalkingParallelFamily J) ⟶ one) :=
        Finite.of_surjective Hom.line (by rintro ⟨⟩; exact ⟨_, rfl⟩)
      exact Fintype.ofFinite _
    · have : IsEmpty ((one : WalkingParallelFamily J) ⟶ zero) := ⟨by rintro ⟨⟩⟩
      exact Fintype.ofIsEmpty
    · have : Subsingleton ((one : WalkingParallelFamily J) ⟶ one) := ⟨by rintro ⟨⟩ ⟨⟩; rfl⟩
      apply +allowSynthFailures Fintype.ofSubsingleton (𝟙 _)


namespace WalkingMulticospan


variable (J : MulticospanShape)

/-- The bijection `WalkingMulticospan J ≃ J.L ⊕ J.R`. -/
def equiv : WalkingMulticospan J ≃ J.L ⊕ J.R where
  toFun x := match x with
    | left a => Sum.inl a
    | right b => Sum.inr b
  invFun := Sum.elim left right
  left_inv := by rintro (_ | _) <;> rfl
  right_inv := by rintro (_ | _) <;> rfl

/-- The bijection `Arrow (WalkingMulticospan J) ≃ WalkingMulticospan J ⊕ J.R ⊕ J.R`. -/
def arrowEquiv :
    Arrow (WalkingMulticospan J) ≃ WalkingMulticospan J ⊕ J.R ⊕ J.R where
  toFun f := match f.hom with
    | .id x => Sum.inl x
    | .fst a => Sum.inr (Sum.inl a)
    | .snd a => Sum.inr (Sum.inr a)
  invFun :=
    Sum.elim (fun X ↦ Arrow.mk (𝟙 X))
      (Sum.elim (fun a ↦ Arrow.mk (Hom.fst a : left _ ⟶ right _))
        (fun a ↦ Arrow.mk (Hom.snd a : left _ ⟶ right _)))
  left_inv := by rintro ⟨_, _, (_ | _ | _)⟩ <;> rfl
  right_inv := by rintro (_ | _ | _) <;> rfl

variable [Finite J.L] [Finite J.R]

lemma finite_arrow : Finite (Arrow (WalkingMulticospan J)) := by
  have := Finite.of_equiv _ (equiv J).symm
  exact Finite.of_equiv _ (arrowEquiv J).symm

@[implicit_reducible]
noncomputable def finCategory :
    FinCategory (WalkingMulticospan J) :=
  ((Arrow.finite_iff _).1 (finite_arrow J)).some

end WalkingMulticospan

end CategoryTheory.Limits

namespace CategoryTheory

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

variable [CartesianMonoidalCategory C]

open Obj MonObj

@[to_additive]
lemma precomp_mul {M X Y : C} [MonObj M] (x y : Y ⟶ M) (f : X ⟶ Y) :
    f ≫ (x * y) = (f ≫ x) * (f ≫ y) :=
  ((yonedaMonObj M).map f.op).hom.map_mul x y

@[to_additive]
lemma curry_mul {M X Y : C} [MonObj M] [Closed X] (x y : X ⊗ Y ⟶ M) :
    curry (x * y) = curry x * curry y := by
  apply uncurry_injective
  rw [Hom.mul_def, Hom.mul_def, uncurry_curry]
  dsimp
  rw [uncurry_natural_left, uncurry_natural_left, uncurry_ihom_map]
  dsimp
  rw [← Category.assoc, ← Category.assoc]
  rw [← whiskerLeft_curry_ihom_ev_app _ _ (lift x y)]
  congr 2
  ext
  · simp
  · simp only [whiskerLeft_snd, Category.assoc, whiskerLeft_snd_assoc]
    rw [← cancel_mono (Functor.OplaxMonoidal.δ _ _ _)]
    simp only [Category.assoc, Functor.Monoidal.μ_δ, Category.comp_id, comp_lift]
    ext <;> simp [← curry_natural_right]

@[to_additive]
lemma curry'_mul {M X : C} [MonObj M] [Closed X] (x y : X ⟶ M) :
    curry' (x * y) = curry' x * curry' y := by
  simp [curry', precomp_mul, curry_mul]

@[to_additive]
noncomputable def ihomMulHomEquiv (M X : C) [MonObj M] [Closed X] :
    (𝟙_ C ⟶ (X ⟶[C] M)) ≃* (X ⟶ M) :=
  MulEquiv.symm
    { toEquiv := MonoidalClosed.curryHomEquiv'
      map_mul' x y := by simp [curry'_mul] }

def ihomHomRingEquiv [BraidedCategory C]
    (M X : C) [RingObj M] [Closed X] : (𝟙_ C ⟶ (X ⟶[C] M)) ≃+* (X ⟶ M) where
  toEquiv := MonoidalClosed.curryHomEquiv'.symm
  map_mul' := (ihomMulHomEquiv M X).map_mul
  map_add' := (ihomAddHomEquiv M X).map_add

namespace MonoidalClosed

variable [BraidedCategory C]

def ihom.tensor (X₁ X₂ Y₁ Y₂ : C) [Closed X₁] [Closed X₂] [Closed (X₁ ⊗ X₂)] :
    (X₁ ⟶[C] Y₁) ⊗ (X₂ ⟶[C] Y₂) ⟶ ((X₁ ⊗ X₂) ⟶[C] (Y₁ ⊗ Y₂)) :=
  curry (lift ((fst _ _ ⊗ₘ fst _ _) ≫ (ihom.ev X₁).app Y₁)
    ((snd _ _ ⊗ₘ snd _ _) ≫ (ihom.ev X₂).app Y₂))

def ihom.swap {X Y Z : C} [Closed X] [Closed Y] (f : X ⟶ Y ⟶[C] Z) :
    Y ⟶ X ⟶[C] Z :=
  curry ((β_ _ _).hom ≫ uncurry f)

def ihom.swap' {X Y Z : C} [Closed X] [Closed Y] (f : X ⟶ Y ⟶[C] Z) :
    Y ⟶ X ⟶[C] Z :=
  curry ((β_ _ _).inv ≫ uncurry f)

@[simp]
lemma ihom.swap_swap' {X Y Z : C} [Closed X] [Closed Y]
    (f : X ⟶ Y ⟶[C] Z) :
    swap (swap' f) = f := by
  simp [swap, swap']

@[simp]
lemma ihom.swap'_swap {X Y Z : C} [Closed X] [Closed Y]
    (f : X ⟶ Y ⟶[C] Z) :
    swap' (swap f) = f := by
  simp [swap, swap']

@[simps]
def ihom.swapEquiv {X Y Z : C} [Closed X] [Closed Y] :
    (X ⟶ Y ⟶[C] Z) ≃ (Y ⟶ X ⟶[C] Z) where
  toFun := ihom.swap
  invFun := ihom.swap'
  left_inv _ := by simp
  right_inv _ := by simp

end MonoidalClosed

namespace MonObj

open BraidedCategory SymmetricCategory

variable (M₁ M₂ : C) [MonObj M₁] [MonObj M₂] [Closed M₁] [Closed (M₁ ⊗ M₁)]

@[to_additive ihomMapZero₀] def ihomMapOne₀ :
    (M₁ ⟶[C] M₂) ⟶ M₂ := (λ_ _).inv ≫ η[M₁] ▷  _ ≫ (ihom.ev M₁).app M₂

@[to_additive ihomMapZero₁] def ihomMapOne₁ :
    (M₁ ⟶[C] M₂) ⟶ M₂ := toUnit _ ≫ η[M₂]

@[to_additive ihomMapAdd₀] def ihomMapMul₀ :
    (M₁ ⟶[C] M₂) ⟶ ((M₁ ⊗ M₁) ⟶[C] M₂) := (MonoidalClosed.pre μ[M₁]).app M₂

@[to_additive ihomMapAdd₁] def ihomMapMul₁ :
    (M₁ ⟶[C] M₂) ⟶ ((M₁ ⊗ M₁) ⟶[C] M₂) :=
  lift (𝟙 _) (𝟙 _) ≫ ihom.tensor .. ≫ (ihom (M₁ ⊗ M₁)).map μ[M₂]

section

variable [SymmetricCategory C] {M₁ M₂} {X : C} (φ : X ⟶ M₁ ⟶[C] M₂) [Closed X]

-- to be moved
@[reassoc]
theorem braiding_inv_comp_whiskerRight_comp_braiding_hom (X : C) {Y Z : C} (f : Y ⟶ Z) :
    (β_ Y X).inv ≫ f ▷ X ≫ (β_ Z X).hom = X ◁ f := by
  simp

omit [MonObj M₂] [Closed (M₁ ⊗ M₁)] in
@[to_additive (attr := simp)]
lemma curryHomEquiv'_comp_ihomMapOne₀ :
    dsimp% curryHomEquiv' (φ ≫ ihomMapOne₀ M₁ M₂) = η[M₁] ≫ ihom.swap φ := by
  apply uncurry'_injective
  dsimp [ihomMapOne₀, ihom.swap]
  rw [uncurry'_curry', uncurry', uncurry_natural_left, uncurry_curry, uncurry_eq]
  dsimp
  rw [← braiding_naturality_left_assoc, leftUnitor_inv_naturality_assoc,
    whisker_exchange_assoc, ← braiding_inv_comp_whiskerRight_comp_braiding_hom_assoc,
    ← braiding_inv_comp_whiskerRight_comp_braiding_hom_assoc,
    ← braiding_swap_eq_inv_braiding, ← braiding_swap_eq_inv_braiding,
    braiding_tensorUnit_right_assoc, Iso.inv_hom_id_assoc]

omit [MonObj M₁] [Closed (M₁ ⊗ M₁)] in
@[to_additive (attr := simp)]
lemma curryHomEquiv'_comp_ihomMapOne₁ :
    dsimp% curryHomEquiv' (φ ≫ ihomMapOne₁ M₁ M₂) = η[X ⟶[C] M₂] := by
  apply uncurry'_injective
  dsimp [ihomMapOne₁, ihom.swap]
  rw [uncurry'_curry', comp_toUnit_assoc, uncurry', uncurry_natural_left, uncurry_ihom_map]
  dsimp
  simp only [← Category.assoc]
  congr 1
  ext

omit [MonObj M₂] in
@[to_additive (attr := simp)]
lemma swap_comp_ihomMapMul₀ :
    ihom.swap (φ ≫ ihomMapMul₀ M₁ M₂) = μ[M₁] ≫ ihom.swap φ := by
  dsimp [ihom.swap, ihomMapMul₀]
  rw [uncurry_pre_app, ← curry_natural_left,
    ← braiding_inv_comp_whiskerRight_comp_braiding_hom_assoc,
    ← braiding_swap_eq_inv_braiding, symmetry_assoc]

@[to_additive (attr := simp)]
lemma swap_comp_ihomMapMul₁ :
    ihom.swap (φ ≫ ihomMapMul₁ M₁ M₂) = (ihom.swap φ ⊗ₘ ihom.swap φ) ≫ μ[X ⟶[C] M₂] := by
  apply uncurry_injective
  dsimp [ihom.swap, ihomMapMul₁]
  rw [uncurry_curry, uncurry_natural_left, uncurry_natural_left, uncurry_natural_left,
    uncurry_natural_left, uncurry_natural_left, uncurry_ihom_map, uncurry_ihom_map]
  dsimp; simp only [← Category.assoc]; congr 1; simp only [Category.assoc]
  rw [← whiskerLeft_comp_assoc, comp_lift, Category.comp_id]
  sorry

omit [Closed (M₁ ⊗ M₁)] in
@[to_additive]
lemma comp_ihomMapOne₀₁_eq_iff :
    φ ≫ ihomMapOne₀ M₁ M₂ = φ ≫ ihomMapOne₁ M₁ M₂ ↔
      η[M₁] ≫ ihom.swap φ = η[X ⟶[C] M₂] := by
  rw [← curryHomEquiv'.apply_eq_iff_eq]
  dsimp
  rw [curryHomEquiv'_comp_ihomMapOne₀]
  rw [curryHomEquiv'_comp_ihomMapOne₁]

@[to_additive]
lemma comp_ihomMapMul₀₁_eq_iff :
    φ ≫ ihomMapMul₀ M₁ M₂ = φ ≫ ihomMapMul₁ M₁ M₂ ↔
      μ[M₁] ≫ ihom.swap φ = (ihom.swap φ ⊗ₘ ihom.swap φ) ≫ μ[X ⟶[C] M₂] := by
  rw [← ihom.swapEquiv.apply_eq_iff_eq, ihom.swapEquiv_apply, ihom.swapEquiv_apply,
    swap_comp_ihomMapMul₀, swap_comp_ihomMapMul₁]

end

variable {M₁ M₂} in
@[to_additive]
lemma isMonHom_ihomSwap_iff [SymmetricCategory C] {X : C} (φ : X ⟶ M₁ ⟶[C] M₂) [Closed X] :
    IsMonHom (ihom.swap φ) ↔ φ ≫ ihomMapOne₀ M₁ M₂ = φ ≫ ihomMapOne₁ M₁ M₂ ∧
      φ ≫ ihomMapMul₀ M₁ M₂ = φ ≫ ihomMapMul₁ M₁ M₂ := by
  rw [comp_ihomMapOne₀₁_eq_iff, comp_ihomMapMul₀₁_eq_iff]
  exact ⟨fun _ ↦ by simp, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩⟩

open Limits

namespace ihom

@[to_additive (attr := simps)]
def multicospanShape : MulticospanShape where
  L := Unit
  R := Bool
  fst _ := .unit
  snd _ := .unit

@[to_additive]
instance : Finite multicospanShape.L := by dsimp; infer_instance
@[to_additive]
instance : Finite multicospanShape.R := by dsimp; infer_instance

@[to_additive (attr := simps)]
def multicospanIndex : MulticospanIndex multicospanShape C where
  left _ := M₁ ⟶[C] M₂
  right := Bool.rec M₂ ((M₁ ⊗ M₁) ⟶[C] M₂)
  fst b := by
    induction b with
    | false => exact ihomMapOne₀ M₁ M₂
    | true => exact ihomMapMul₀ M₁ M₂
  snd b := by
    induction b with
    | false => exact ihomMapOne₁ M₁ M₂
    | true => exact ihomMapMul₁ M₁ M₂

end ihom

variable [HasFiniteLimits C]

@[to_additive]
instance : HasMultiequalizer (ihom.multicospanIndex M₁ M₂) := by
  letI := WalkingMulticospan.finCategory ihom.multicospanShape
  infer_instance

@[to_additive]
protected noncomputable def ihom : C := multiequalizer (ihom.multicospanIndex M₁ M₂)

namespace ihom

variable {M₁ M₂} in
@[to_additive]
protected noncomputable def «ι» : MonObj.ihom M₁ M₂ ⟶ M₁ ⟶[C] M₂ :=
  Multiequalizer.ι (multicospanIndex M₁ M₂) .unit

@[to_additive (attr := reassoc)]
lemma map_one : ihom.ι ≫ ihomMapOne₀ M₁ M₂ = ihom.ι ≫ ihomMapOne₁ M₁ M₂ :=
  Multiequalizer.condition (multicospanIndex M₁ M₂) false

@[to_additive (attr := reassoc)]
lemma map_mul : ihom.ι ≫ ihomMapMul₀ M₁ M₂ = ihom.ι ≫ ihomMapMul₁ M₁ M₂ :=
  Multiequalizer.condition (multicospanIndex M₁ M₂) true

@[to_additive]
instance : Mono (ihom.ι (M₁ := M₁) (M₂ := M₂)) where
  right_cancellation _ _ h := Multiequalizer.hom_ext _ _ _ (by rintro ⟨⟩; exact h)

variable [SymmetricCategory C]

variable {M₁ M₂} in
@[to_additive]
lemma exists_lift_iff {X : C} {φ : X ⟶ M₁ ⟶[C] M₂} [Closed X] :
    (∃ (ψ : X ⟶ MonObj.ihom M₁ M₂), ψ ≫ ihom.ι = φ) ↔
      IsMonHom (ihom.swap φ) := by
  rw [isMonHom_ihomSwap_iff]
  refine ⟨?_, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  · rintro ⟨ψ, rfl⟩
    simp [map_one, map_mul]
  · exact ⟨Multiequalizer.lift _ _ (fun _ ↦ φ) (by rintro (_ | _) <;> assumption),
      Multiequalizer.lift_ι ..⟩

variable {M₁ M₂} in
@[to_additive]
noncomputable def homEquiv {X : C} [Closed X] :
    (X ⟶ MonObj.ihom M₁ M₂) ≃ { φ : X ⟶ M₁ ⟶[C] M₂ // IsMonHom (ihom.swap φ) } :=
  Equiv.ofBijective (fun f ↦ ⟨f ≫ ihom.ι, exists_lift_iff.1 ⟨_, rfl⟩⟩)
    ⟨fun f₁ f₂ h ↦ by
      rw [Subtype.ext_iff] at h
      rwa [← cancel_mono ihom.ι],
    fun ⟨φ, hφ⟩ ↦ by
      obtain ⟨ψ, rfl⟩ := exists_lift_iff.2 hφ
      exact ⟨ψ, rfl⟩⟩

end ihom

end MonObj

namespace RingObj

open Limits

variable [HasFiniteLimits C] [SymmetricCategory C] (R₁ R₂ : C) [RingObj R₁] [RingObj R₂]
  [Closed R₁] [Closed (R₁ ⊗ R₁)]

protected noncomputable def ihom : C :=
  pullback (Z := R₁ ⟶[C] R₂) AddMonObj.ihom.ι MonObj.ihom.ι

namespace ihom

set_option backward.isDefEq.respectTransparency false in
variable {R₁ R₂} in
noncomputable def «ι» : RingObj.ihom R₁ R₂ ⟶ R₁ ⟶[C] R₂ :=
  pullback.fst _ _ ≫ AddMonObj.ihom.ι
deriving Mono

set_option backward.isDefEq.respectTransparency false in
variable {R₁ R₂} in
lemma exists_lift_iff {X : C} {φ : X ⟶ R₁ ⟶[C] R₂} [Closed X] :
    (∃ (ψ : X ⟶ RingObj.ihom R₁ R₂), ψ ≫ ihom.ι = φ) ↔
      IsRingHom (ihom.swap φ) := by
  have : IsRingHom (ihom.swap φ) ↔ IsAddMonHom (ihom.swap φ) ∧ IsMonHom (ihom.swap φ) :=
    ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ { }⟩
  rw [this, ← AddMonObj.ihom.exists_lift_iff, ← MonObj.ihom.exists_lift_iff]
  constructor
  · rintro ⟨ψ, rfl⟩
    exact ⟨⟨ψ ≫ pullback.fst _ _, by simp [ihom.ι]⟩,
      ⟨ψ ≫ pullback.snd _ _, by simp [ihom.ι, pullback.condition]⟩⟩
  · rintro ⟨⟨ψ₁, rfl⟩, ⟨ψ₂, h⟩⟩
    exact ⟨pullback.lift ψ₁ ψ₂ h.symm, by simp [ihom.ι]⟩

variable {R₁ R₂} in
noncomputable def homEquiv {X : C} [Closed X] :
    (X ⟶ RingObj.ihom R₁ R₂) ≃ { φ : X ⟶ R₁ ⟶[C] R₂ // IsRingHom (ihom.swap φ) } :=
  Equiv.ofBijective (fun f ↦ ⟨f ≫ ihom.ι, exists_lift_iff.1 ⟨_, rfl⟩⟩)
    ⟨fun f₁ f₂ h ↦ by
      rw [Subtype.ext_iff] at h
      rwa [← cancel_mono ihom.ι],
    fun ⟨φ, hφ⟩ ↦ by
      obtain ⟨ψ, rfl⟩ := exists_lift_iff.2 hφ
      exact ⟨ψ, rfl⟩⟩

end ihom

end RingObj

namespace CommRingObj

variable [SymmetricCategory C]

variable (R : C) [CommRingObj R]

abbrev Alg := Under (CommRng.mk R)

namespace Alg

variable {R} in
abbrev mk {R' : C} [CommRingObj R'] (φ : R ⟶ R') [IsRingHom φ] :
    Alg R :=
  Under.mk (Y := .mk R') ⟨φ⟩

open Limits
variable [HasFiniteLimits C] {R} (R₁ R₂ : Alg R)
  [Closed R₁.right.X] [Closed (R₁.right.X ⊗ R₁.right.X)] [Closed R]

protected noncomputable def ihom : C :=
  equalizer (X := RingObj.ihom R₁.right.X R₂.right.X) (Y := R ⟶[C] R₂.right.X)
    (RingObj.ihom.ι ≫ (MonoidalClosed.pre (show R ⟶ R₁.right.X from R₁.hom.hom)).app _)
    (RingObj.ihom.ι ≫ toUnit _ ≫ curryHomEquiv' R₂.hom.hom)

variable {R₁ R₂} in
noncomputable def ihom.ι : Alg.ihom R₁ R₂ ⟶ RingObj.ihom R₁.right.X R₂.right.X :=
  equalizer.ι _ _

instance : Mono (ihom.ι (R₁ := R₁) (R₂ := R₂)) := equalizer.ι_mono

end Alg

end CommRingObj

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

namespace RingObj

variable [BraidedCategory C]

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

variable [BraidedCategory C]

@[reducible]
def ofRepresentableBy (X : C) (F : Cᵒᵖ ⥤ CommRingCat.{w})
    (h : (F ⋙ forget _).RepresentableBy X) :
    CommRingObj X :=
  letI := RingObj.ofRepresentableBy X (F ⋙ forget₂ _ _) h
  { mul_comm := sorry }

end CommRingObj

end CategoryTheory

lemma Ideal.le_ker_iff {α β : Type*} [Ring α] [Ring β] (f : α →+* β)
    (I : Ideal α) :
    I ≤ RingHom.ker f ↔ (∀ i ∈ I, f i = 0) :=
  Iff.rfl

namespace DualNumber

def equiv {R : Type*} : R[ε] ≃ R × R := Equiv.refl _

-- #37049
@[ext]
theorem ringHom_ext {R A : Type*} [CommRing A] [CommRing R]
    {f g : R[ε] →+* A} (h₀ : f.comp (algebraMap R R[ε]) = g.comp (algebraMap R R[ε]))
    (hε : f ε = g ε) : f = g := by
  letI : Algebra R A := by algebraize [f]; exact Algebra.compHom _ (algebraMap R R[ε])
  let φ₁ : R[ε] →ₐ[R] A :=
    { toRingHom := f
      commutes' _ := rfl }
  let φ₂ : R[ε] →ₐ[R] A :=
    { toRingHom := g
      commutes' r := (DFunLike.congr_fun h₀ r).symm }
  have : φ₁ = φ₂ := algHom_ext hε
  exact congr_arg AlgHom.toRingHom this

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

instance algebra [Algebra A B] : Algebra A[ε] B[ε] := by
  letI φ : A[ε] →ₐ[A] B[ε] :=
    lift ⟨⟨{ toRingHom := algebraMap _ _, commutes' _ := rfl }, ε⟩, by simp,
      fun x ↦ (Algebra.commutes _ ε).symm⟩
  exact φ.toAlgebra

example [Algebra A B] : IsScalarTower A A[ε] B[ε] := inferInstance
example [Algebra A B] : IsScalarTower A B B[ε] := inferInstance

def ringHom (f : A →+* B) : A[ε] →+* B[ε] := by
  letI := f.toAlgebra
  exact algebraMap A[ε] B[ε]

@[simp]
lemma ringHom_smul_one (f : A →+* B) (a : A) : ringHom f (a • 1) = f a • 1 := by
  letI := f.toAlgebra
  refine (lift_apply_apply ..).trans ?_
  simp only [TrivSqZeroExt.fst_smul, TrivSqZeroExt.fst_one, smul_eq_mul, mul_one, AlgHom.coe_mk,
    TrivSqZeroExt.snd_smul, TrivSqZeroExt.snd_one, mul_zero, map_zero, zero_mul, add_zero,
    Algebra.algebraMap_eq_smul_one]
  rfl

@[simp]
lemma ringHom_algebraMap_apply (f : A →+* B) (a : A) :
    ringHom f (algebraMap A A[ε] a) = algebraMap B B[ε] (f a) := by
  letI := f.toAlgebra
  dsimp [ringHom]
  rw [← IsScalarTower.algebraMap_apply A A[ε] B[ε] a]
  exact IsScalarTower.algebraMap_apply A B B[ε] a

@[simp]
lemma ringHom_eps (f : A →+* B) : ringHom f ε = ε := by
  letI := f.toAlgebra
  apply lift_apply_eps

variable (A) in
lemma ringHom_id :
    ringHom (.id A) = .id _ := by
  aesop

lemma ringHom_comp (f : A →+* B) (g : B →+* C) :
    ringHom (g.comp f) = (ringHom g).comp (ringHom f) := by
  aesop

end DualNumber

lemma Option.eq₂ {α β : Type*} (f : Option α → β) (hf : ∀ (i : α), f (some i) = f none)
    (i j : Option α) : f i = f j := by
  obtain _ | i := i <;> obtain _ | j := j <;> simp [hf]

namespace DualNumber

open Polynomial

variable (R : Type w) [CommRing R]

open TrivSqZeroExt

-- #37049
@[simp]
lemma ε_pow_two : (ε : R[ε]) ^ 2 = 0 := by simp [pow_two]

@[simps]
noncomputable def toPolynomialQuotient : R[ε] →+* R[X] ⧸ (Ideal.span {(X^2 : R[X])}) where
  toFun z := Ideal.Quotient.mk _ (fst z • 1 + snd z • X)
  map_zero' := by aesop
  map_one' := by aesop
  map_add' x y := by
    simp [add_smul]
    abel
  map_mul' x y := by
    rw [← map_mul, Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.mem_span_singleton']
    refine ⟨-(snd x * snd y) • 1, ?_⟩
    dsimp
    simp only [neg_smul, neg_mul, Algebra.smul_mul_assoc, one_mul, add_smul, mul_add,
      Algebra.mul_smul_comm, mul_one, smul_add, smul_smul, add_mul]
    ring_nf

@[simp]
noncomputable def fromPolynomialQuotient : R[X] ⧸ (Ideal.span {(X^2 : R[X])}) →+* R[ε] :=
  Ideal.Quotient.lift _ (eval₂RingHom (TrivSqZeroExt.inlHom R R) ε) (by
    rw [← Ideal.le_ker_iff]
    simp)

@[simps!]
noncomputable def ringEquiv : R[ε] ≃+* (R[X] ⧸ (Ideal.span {(X^2 : R[X])})) :=
  .ofRingHom (toPolynomialQuotient R) (fromPolynomialQuotient R) (by
    ext : 2
    · ext r
      dsimp
      simp only [eval₂_C, TrivSqZeroExt.inlHom_apply, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl,
        zero_smul, add_zero, ← Polynomial.C_1, Polynomial.smul_C, smul_eq_mul, mul_one]
    · simp) (by aesop)

set_option backward.isDefEq.respectTransparency false in
@[simps!]
noncomputable def algEquiv : R[ε] ≃ₐ[R] R[X] ⧸ (Ideal.span {(X^2 : R[X])}) :=
  AlgEquiv.ofRingEquiv (f := ringEquiv R) (fun r ↦ by
    simp [ringEquiv_apply, zero_smul, map_zero, add_zero,
      Algebra.algebraMap_eq_smul_one]
    rfl)

instance (R : Type w) [CommRing R] (r : R[X]) :
    Algebra.FinitePresentation R (R[X] ⧸ Ideal.span {r}) :=
  Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton _)

instance (R : Type w) [CommRing R] : Algebra.FinitePresentation R R[ε] := .equiv (algEquiv R).symm

set_option backward.isDefEq.respectTransparency false in
instance : letI := Ring.toIntAlgebra ℤ[ε]; Algebra.FinitePresentation ℤ ℤ[ε] :=
  inferInstance

end DualNumber

namespace CategoryTheory

open MonoidalCategory SemiCartesianMonoidalCategory Limits

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [SymmetricCategory C]
  (R : C) [CommRingObj R]

open MonObj

namespace CommRingObj

set_option backward.isDefEq.respectTransparency false in
lemma aeval_comp_apply {γ : Type*} {X Y : C} (f : X ⟶ Y) (g : γ → (Y ⟶ R)) (a : MvPolynomial γ ℤ) :
    MvPolynomial.aeval (R := ℤ) (fun i ↦ f ≫ g i) a =
      f ≫ MvPolynomial.aeval (R := ℤ) g a := by
  have : (MvPolynomial.aeval (R := ℤ) (fun i ↦ f ≫ g i)).toRingHom =
      ((yonedaRingObj R).map f.op).hom.comp ((MvPolynomial.aeval g).toRingHom) := by
    aesop
  exact DFunLike.congr_fun this a

variable (A : Type w) [CommRing A]

/-- Given a ring `A`, and a ring object `R` in a category `C`, this is
the presheaf which sends `X : C` to `A →+* (X ⟶ R)`. -/
@[simps obj map]
def yonedaSpec : Cᵒᵖ ⥤ Type max v w where
  obj X := A →+* (X.unop ⟶ R)
  map f g := ((yonedaRingObj R).map f).hom.comp g

@[simps]
def yonedaSpecFunctor : CommRingCat.{w}ᵒᵖ ⥤ Cᵒᵖ ⥤ Type max v w where
  obj A := yonedaSpec R A.unop
  map φ := { app X g := g.comp φ.unop.hom }

abbrev HasSpec := (yonedaSpec R A).IsRepresentable

variable {A} in
lemma hasSpec_of_ringEquiv {A' : Type w} [CommRing A'] (e : A ≃+* A') [HasSpec R A] :
    HasSpec R A' :=
  ((yonedaSpec R A).representableBy.ofIso
    ((yonedaSpecFunctor R).mapIso e.toCommRingCatIso.op.symm)).isRepresentable

section

variable [HasSpec R A]

noncomputable def Spec : C := (yonedaSpec R A).reprX

noncomputable def yonedaSpecRepresentableBy :
    (yonedaSpec R A).RepresentableBy (Spec R A) :=
  (yonedaSpec R A).representableBy

variable {R A} in
noncomputable abbrev yonedaSpecHomEquiv [HasSpec R A] {X : C} :
    (X ⟶ Spec R A) ≃ (A →+* (X ⟶ R)) :=
  (yonedaSpecRepresentableBy R A).homEquiv

variable {R A} in
@[simp]
lemma yonedaSpecHomEquiv_comp {X Y : C} (g : X ⟶ Y) (y : Y ⟶ Spec R A) :
    yonedaSpecHomEquiv (g ≫ y) =
      ((yonedaRingObj R).map g.op).hom.comp (yonedaSpecHomEquiv y) :=
  (yonedaSpecRepresentableBy R A).homEquiv_comp g y

variable {R A} in
noncomputable def isoSpecOfRepresentableBy {Y : C}
    (h : (yonedaSpec R A).RepresentableBy Y) :
    Y ≅ Spec R A :=
  h.isoReprX

variable {A} in
noncomputable def Spec.eval (a : A) : Spec R A ⟶ R :=
  yoneda.preimage { app X f := yonedaSpecHomEquiv f a }

variable {A} in
@[reassoc]
lemma Spec.comp_eval_apply (a : A) {X : C} (f : X ⟶ Spec R A) :
    f ≫ eval R a = yonedaSpecHomEquiv f a := by
  change (yoneda.map (Spec.eval R a)).app _ f = _
  simp [Spec.eval]

lemma Spec.eval_eq (a : A) :
    eval R a = yonedaSpecHomEquiv (𝟙 _) a := by
  simpa only [Category.id_comp] using Spec.comp_eval_apply R a (𝟙 _)

variable {R A} in
@[reassoc (attr := simp)]
lemma Spec.yonedaSpecHomEquiv_symm_comp_eval {X : C} (f : A →+* (X ⟶ R)) (a : A) :
    yonedaSpecHomEquiv.symm f ≫ Spec.eval R a = f a := by
  simp [Spec.comp_eval_apply]

attribute [local simp] Spec.comp_eval_apply in
noncomputable def Spec.evalRingHom : A →+* (Spec R A ⟶ R) where
  toFun := Spec.eval R
  map_one' := yoneda.map_injective (by cat_disch)
  map_zero' := yoneda.map_injective (by cat_disch)
  map_mul' a b := yoneda.map_injective (by
    ext
    dsimp
    rw [comp_eval_apply, map_mul, ← comp_eval_apply, ← comp_eval_apply, comp_mul])
  map_add' a b := yoneda.map_injective (by
    ext
    dsimp
    rw [comp_eval_apply, map_add, ← comp_eval_apply, ← comp_eval_apply, AddMonObj.comp_add])


variable [Closed (Spec R A)]

noncomputable abbrev Spec.const : R ⟶ Spec R A ⟶[C] R :=
  MonoidalClosed.curry (snd (Spec R A) R)

noncomputable def Spec.evalRingHom' : A →+* (𝟙_ C ⟶ Spec R A ⟶[C] R) :=
  (ihomHomRingEquiv R (Spec R A)).symm.toRingHom.comp (Spec.evalRingHom R A)

end

namespace Spec

variable {γ ρ : Type} {rel : ρ → MvPolynomial γ ℤ}
  {c : Fan (fun (_ : γ) ↦ R)} (hc : IsLimit c)

variable (rel) in
noncomputable def family : Option ρ → MvPolynomial γ ℤ
  | some x => rel x
  | none => 0

variable (rel) in
@[simp] lemma family_none : family rel none = 0 := rfl
@[simp] lemma family_some (x : ρ) : family rel (some x) = rel x := rfl

variable {R} in
noncomputable abbrev trident {X : C}
    (g : MvPolynomial γ ℤ ⧸ Ideal.span (Set.range rel) →+* (X ⟶ R)) :
    Trident (MvPolynomial.aeval c.proj ∘ family rel) :=
  Trident.ofι (Fan.IsLimit.lift hc (fun x ↦ g (Ideal.Quotient.mk _ (.X x))))
    (Option.eq₂ _ (fun x ↦ by
      have : g.comp (Ideal.Quotient.mk _) =
          (MvPolynomial.aeval (fun x ↦ g (Ideal.Quotient.mk _ (.X x)))).toRingHom := by
        aesop
      simpa only [Function.comp_apply, family_some, family_none,
        ← aeval_comp_apply, Fan.IsLimit.fac, map_zero, AddMonObj.comp_zero,
          ← show g (rel x) = 0 by simp [Ideal.Quotient.mk_span_range rel x]] using
        DFunLike.congr_fun this.symm (rel x)))

variable {t : Trident (MvPolynomial.aeval c.proj ∘ family rel)} (ht : IsLimit t)

include t in
variable {R} in
noncomputable abbrev yonedaSpecRepresentableByOfIsLimitAux {X : C} (f : X ⟶ t.pt) :
    MvPolynomial γ ℤ ⧸ Ideal.span (Set.range rel) →+* (X ⟶ R) :=
  Ideal.Quotient.lift _ (MvPolynomial.eval₂Hom (Int.castRingHom _) (fun g ↦ f ≫ t.ι ≫ c.proj g)) (by
    rw [← Ideal.le_ker_iff, Ideal.span_le, Set.range_subset_iff]
    intro r
    simpa [family, ← aeval_comp_apply] using f ≫= t.condition (some r) none)

set_option backward.isDefEq.respectTransparency false
noncomputable def yonedaSpecRepresentableByOfIsLimit :
    (yonedaSpec R ((MvPolynomial γ ℤ) ⧸ Ideal.span (Set.range rel))).RepresentableBy t.pt where
  homEquiv {X} :=
    { toFun f := yonedaSpecRepresentableByOfIsLimitAux f
      invFun g := ht.lift (trident hc g)
      left_inv f := Trident.IsLimit.hom_ext ht (by
        rw [ht.fac]
        exact Fan.IsLimit.hom_ext hc _ _ (fun x ↦ by simp))
      right_inv g := by
        dsimp
        ext x : 2
        · subsingleton
        · simp }
  homEquiv_comp f g := by
    dsimp
    ext x : 2
    · subsingleton
    · cat_disch

instance [HasFiniteLimits C] [Finite γ] [Finite ρ] :
    HasSpec R ((MvPolynomial γ ℤ) ⧸ Ideal.span (Set.range rel)) :=
  (yonedaSpecRepresentableByOfIsLimit R (productIsProduct _) (limit.isLimit _)).isRepresentable

instance (A : Type) [CommRing A] [HasFiniteLimits C] [Algebra.FinitePresentation ℤ A] :
    HasSpec R A := by
  obtain ⟨n, I, e, h⟩ := (Algebra.FinitePresentation.iff (R := ℤ) (A := A)).1 inferInstance
  obtain ⟨α, _, g, rfl⟩ : ∃ (α : Type) (hα : Finite α) (g : α → _),
      I = Ideal.span (Set.range g) := by
    obtain ⟨S, rfl⟩ := h
    refine ⟨Fin S.card, inferInstance, fun i ↦ (Finset.equivFin S).symm i, ?_⟩
    congr
    ext x
    exact ⟨fun hx ↦ ⟨S.equivFin ⟨x, hx⟩, by simp⟩, by aesop⟩
  exact hasSpec_of_ringEquiv R e.toRingEquiv

end Spec

def yonedaSpecIntRepresentableBy :
    (yonedaSpec R ℤ).RepresentableBy (𝟙_ _) where
  homEquiv {X} :=
    { toFun _ := Int.castRingHom _
      invFun _ := toUnit X
      right_inv _ := by dsimp; subsingleton }

instance : HasSpec R ℤ := (yonedaSpecIntRepresentableBy R).isRepresentable

variable (C) in
@[simps]
def yonedaTensorCommRing : CommRng C ⥤ Type max w v where
  obj T := A →+* (𝟙_ C ⟶ T.X)
  map {T₁ T₂} f φ := ((yonedaCommRing.map f).app _).hom.comp φ

def yonedaCommRingObjTensorCommRing : CommRng C ⥤ Type max w v where
  obj T := (CommRng.mk R ⟶ T) × (A →+* (𝟙_ C ⟶ T.X))
  map f x := ⟨x.1 ≫ f, (yonedaTensorCommRing C A).map f x.2⟩

variable {R' : C} [CommRingObj R']

variable {R A} in
/-- The condition that a morphism `R ⟶ R'` of commutative ring objects
and a morphism of rings `f : A →+* (𝟙_ C ⟶ R')` makes `R'` the tensor
product of `R` and `A`. -/
structure TensorCommRingCore (φ : R ⟶ R') [IsRingHom φ] (f : A →+* (𝟙_ C ⟶ R')) where
  corepresentableBy :
    (yonedaCommRingObjTensorCommRing R A).CorepresentableBy (.mk R')
  homEquiv_id_eq :
    corepresentableBy.homEquiv (𝟙 _) = ⟨.mk φ, f⟩

variable {R A} in
structure IsTensorCommRing (φ : R ⟶ R') [IsRingHom φ] (f : A →+* (𝟙_ C ⟶ R')) : Prop where
  nonempty_tensorCommRingCore : Nonempty (TensorCommRingCore φ f)

section

open DualNumber

attribute [local simp] ringHom_id ringHom_comp in
@[simps obj map]
def yonedaDualNumber : Cᵒᵖ ⥤ CommRingCat.{v} where
  obj X := .of (X.unop ⟶ R)[ε]
  map f := CommRingCat.ofHom (DualNumber.ringHom ((yonedaCommRingObj R).map f).hom)

def dualNumber := R ⊗ R

open CartesianMonoidalCategory in
def representableByYonedaDualNumber :
    (yonedaDualNumber R ⋙ forget CommRingCat).RepresentableBy (dualNumber R) where
  homEquiv {X} := homEquivToProd.trans DualNumber.equiv.symm
  homEquiv_comp {X Y} f g := by
    sorry

instance : CommRingObj (dualNumber R) :=
  CommRingObj.ofRepresentableBy _ _ (representableByYonedaDualNumber R)

end

end CommRingObj

namespace SDG

open CommRingObj DualNumber

variable [HasFiniteLimits C]

noncomputable abbrev D₁ : C := Spec R ℤ[ε]

namespace D₁

noncomputable abbrev «ι» : D₁ R ⟶ R := Spec.eval R ε

instance : Mono (D₁.ι R) where
  right_cancellation {X} f₁ f₂ h := by
    obtain ⟨f₁, rfl⟩ := yonedaSpecHomEquiv.symm.surjective f₁
    obtain ⟨f₂, rfl⟩ := yonedaSpecHomEquiv.symm.surjective f₂
    simp only [Spec.yonedaSpecHomEquiv_symm_comp_eval] at h
    simp only [EmbeddingLike.apply_eq_iff_eq]
    ext : 1
    · subsingleton
    · exact h

@[simp]
lemma ι_mul_ι : D₁.ι R * D₁.ι R = 0 := by
  simpa using ((Spec.evalRingHom R ℤ[ε]).map_mul ε ε).symm

end D₁

variable [MonoidalClosed C]

noncomputable def D₁.affineMap : R ⊗ R ⟶ (D₁ R ⟶[C] R) :=
  MonoidalClosed.curry (snd _ _ ≫ fst _ _ + (fst _ _ ≫ D₁.ι R) * snd _ _ ≫ snd _ _)

protected abbrev D₁.Axiom₁ : Prop := IsIso (D₁.affineMap R)

variable (A : Type) [CommRing A] [Algebra.FinitePresentation ℤ A] [HasFiniteLimits C]

def Axiom₁ : Prop :=
  CommRingObj.IsTensorCommRing (Spec.const R A) (Spec.evalRingHom' R A)

lemma D₁.axiom₁_iff : D₁.Axiom₁ R ↔ Axiom₁ R ℤ[ε] := sorry

variable {R} in
def Axiom₂.ν (R' : CommRingObj.Alg R) :
    CommRingObj.Alg.ihom (.mk (Spec.const R A)) R' ⟶ Spec R'.right.X A := by
  sorry

def Axiom₂ : Prop := ∀ (R' : CommRingObj.Alg R), IsIso (Axiom₂.ν A R')

def Axiom₃ (A : Type*) [CommRing A] [HasSpec R A] : Prop :=
  (ihom (Spec R A)).IsLeftAdjoint

end SDG

end CategoryTheory
