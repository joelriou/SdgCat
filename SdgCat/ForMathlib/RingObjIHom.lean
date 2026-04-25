import SdgCat.ForMathlib.Limits
import SdgCat.ForMathlib.RingObj

open Opposite

universe w v u

namespace CategoryTheory

open CartesianMonoidalCategory MonoidalCategory MonoidalClosed

variable {C D : Type*} [Category* C] [Category* D]

variable [CartesianMonoidalCategory C]

open Obj MonObj RingObj

@[to_additive]
lemma precomp_mul {M X Y : C} [MonObj M] (x y : Y ⟶ M) (f : X ⟶ Y) :
    f ≫ (x * y) = (f ≫ x) * (f ≫ y) :=
  ((yonedaMonObj M).map f.op).hom.map_mul x y

open scoped AddMonObj Obj RingObj

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

def ihom.tensor (X₁ X₂ Y₁ Y₂ : C) [Closed X₁] [Closed X₂] [Closed (X₁ ⊗ X₂)] :
    (X₁ ⟶[C] Y₁) ⊗ (X₂ ⟶[C] Y₂) ⟶ ((X₁ ⊗ X₂) ⟶[C] (Y₁ ⊗ Y₂)) :=
  curry (lift ((fst _ _ ⊗ₘ fst _ _) ≫ (ihom.ev X₁).app Y₁)
    ((snd _ _ ⊗ₘ snd _ _) ≫ (ihom.ev X₂).app Y₂))

variable [BraidedCategory C]

@[reassoc]
lemma ihom.whiskerLeft_tensor_comp_ev_app
    (X₁ X₂ Y₁ Y₂ : C) [Closed X₁] [Closed X₂] [Closed (X₁ ⊗ X₂)] :
    dsimp% (X₁ ⊗ X₂) ◁ ihom.tensor X₁ X₂ Y₁ Y₂ ≫ (ihom.ev (X₁ ⊗ X₂)).app (Y₁ ⊗ Y₂) =
      tensorμ _ _ _ _ ≫ ((ihom.ev X₁).app Y₁ ⊗ₘ (ihom.ev X₂).app Y₂) := by
  dsimp [tensor]
  rw [dsimp% MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
  cat_disch

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

variable [CartesianMonoidalCategory D] [SymmetricCategory D]
lemma ihom.swap'_eq_swap {X Y Z : D} [Closed X] [Closed Y] (f : X ⟶ Y ⟶[D] Z) :
    swap' f = swap f := by
  simp [swap, swap', SymmetricCategory.braiding_swap_eq_inv_braiding]

@[simp]
lemma ihom.swap_swap {X Y Z : D} [Closed X] [Closed Y]
    (f : X ⟶ Y ⟶[D] Z) :
    swap (swap f) = f := by
  simp [← ihom.swap'_eq_swap f]

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

omit [MonObj M₁] in
@[to_additive (attr := simp)]
lemma swap_comp_ihomMapMul₁ :
    ihom.swap (φ ≫ ihomMapMul₁ M₁ M₂) = (ihom.swap φ ⊗ₘ ihom.swap φ) ≫ μ[X ⟶[C] M₂] := by
  apply uncurry_injective
  dsimp [ihom.swap, ihomMapMul₁]
  rw [uncurry_curry, uncurry_natural_left, uncurry_natural_left, uncurry_natural_left,
    uncurry_natural_left, uncurry_natural_left, uncurry_ihom_map, uncurry_ihom_map]
  dsimp; simp only [← Category.assoc]; congr 1; simp only [Category.assoc]
  have : (curry (β_ X M₁).hom ⊗ₘ curry (β_ X M₁).hom) ≫
    Functor.LaxMonoidal.μ (ihom X) _ _ =
      curry (lift (lift (snd _ _ ≫ fst _ _) (fst _ _))
        (lift (snd _ _ ≫ snd _ _) (fst _ _))) := by
    rw [← cancel_mono (Functor.OplaxMonoidal.δ (ihom X) _ _),
      Category.assoc, Functor.Monoidal.μ_δ, Category.comp_id]
    ext : 1
    · rw [tensorHom_fst, Category.assoc, Functor.OplaxMonoidal.δ_fst,
        ← curry_natural_right, ← curry_natural_left]
      congr 1
      cat_disch
    · rw [tensorHom_snd, Category.assoc, Functor.OplaxMonoidal.δ_snd,
        ← curry_natural_right, ← curry_natural_left]
      congr 1
      cat_disch
  rw [← whiskerLeft_comp_assoc, comp_lift, Category.comp_id,
    ihom.whiskerLeft_tensor_comp_ev_app]
  rw [curry_natural_right, ← tensorHom_comp_tensorHom, whiskerLeft_comp_assoc]
  nth_rw 2 [← whiskerLeft_comp_assoc]
  rw [Functor.LaxMonoidal.μ_natural]
  rw [whiskerLeft_comp_assoc]
  rw [dsimp% ihom.ev_naturality]
  rw [← whiskerLeft_comp_assoc, this]
  ext : 1
  · simp only [Category.assoc]
    rw [tensorHom_fst, tensorHom_fst, tensorμ_fst_assoc, tensorHom_def'_assoc,
      ← whiskerLeft_comp_assoc, lift_fst,
      whisker_exchange_assoc, ← dsimp% uncurry_eq]
    simp only [← Category.assoc]; congr 1
    cat_disch
  · simp only [Category.assoc]
    rw [tensorHom_snd, tensorHom_snd, tensorμ_snd_assoc, tensorHom_def'_assoc,
      ← whiskerLeft_comp_assoc, lift_snd,
      whisker_exchange_assoc, ← dsimp% uncurry_eq]
    simp only [← Category.assoc]; congr 1
    cat_disch

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

variable {R₁ R₂} in
noncomputable def homEquiv' {X : C} [Closed X] :
    (X ⟶ RingObj.ihom R₁ R₂) ≃ (RingObjCat.mk R₁ ⟶ RingObjCat.mk (X ⟶[C] R₂)) :=
  homEquiv.trans
    { toFun := fun ⟨f, _⟩ ↦ { hom := ihom.swap f }
      invFun f := ⟨ihom.swap f.hom, by simpa using f.isRingHom⟩
      left_inv _ := by aesop
      right_inv _ := by aesop }

end ihom

end RingObj

namespace CommRingObj

variable [SymmetricCategory C]

variable (R : C) [CommRingObj R]

abbrev Alg := Under (CommRingObjCat.mk R)

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

end CategoryTheory
