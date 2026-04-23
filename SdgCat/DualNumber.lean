import SdgCat.ForMathlib.DualNumber
import SdgCat.ForMathlib.RingObjIHom
import SdgCat.Tensor

open Opposite

universe w v u

namespace DualNumber

variable {R : Type*} [CommRing R]

@[simps apply_coe]
def intRingHomEquiv : (ℤ[ε] →+* R) ≃ { x : R // x ^ 2 = 0 } where
  toFun f := ⟨f ε, by simp [← RingHom.map_pow] ⟩
  invFun x := AlgHom.toRingHom (lift ⟨⟨Algebra.algHom ℤ ℤ R, x.val⟩,
    by simpa [pow_two] using x.prop, by simp⟩)
  left_inv f := ringHom_ext (by subsingleton) (by simp)
  right_inv x := by simp

end DualNumber

namespace CategoryTheory

open CartesianMonoidalCategory MonoidalCategory MonObj Limits

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [SymmetricCategory C]
  (R : C) [CommRingObj R] (A : Type w) [CommRing A]

namespace CommRingObj

open DualNumber

attribute [local simp] ringHom_id ringHom_comp in
@[simps obj map]
protected def dualNumber.yoneda : Cᵒᵖ ⥤ CommRingCat.{v} where
  obj X := .of (X.unop ⟶ R)[ε]
  map f := CommRingCat.ofHom (DualNumber.ringHom ((yonedaCommRingObj R).map f).hom)

def dualNumber := R ⊗ R

namespace dualNumber

variable {R} in
def fst : dualNumber R ⟶ R := SemiCartesianMonoidalCategory.fst _ _

variable {R} in
def snd : dualNumber R ⟶ R := SemiCartesianMonoidalCategory.snd _ _

variable {R} in
def hom_ext {T : C} {f g : dualNumber R ⟶ T}
    (h₁ : fst ≫ f = fst ≫ g) (h₂ : snd ≫ f = snd ≫ g) : f = g := sorry

set_option backward.isDefEq.respectTransparency false in
open CartesianMonoidalCategory in
def representableBy :
    (dualNumber.yoneda R ⋙ forget CommRingCat).RepresentableBy (dualNumber R) where
  homEquiv {X} := homEquivToProd
  homEquiv_comp {X Y} f g := by
    dsimp
    erw [homEquivToProd_apply, homEquivToProd_apply]
    apply Prod.ext <;> cat_disch

instance : CommRingObj (dualNumber R) :=
  CommRingObj.ofRepresentableBy _ _ (representableBy R)

variable {R} in
def ringEquiv {X : C} : (X ⟶ dualNumber R) ≃+* (X ⟶ R)[ε] :=
  CommRingObj.ofRepresentableByHomRingEquiv (representableBy R)

variable {R} in
lemma ringEquiv_comp {X Y : C} (f : X ⟶ Y) (g : Y ⟶ dualNumber R) :
    ringEquiv (f ≫ g) =
      DualNumber.ringHom ((yonedaCommRingObj R).map f.op).hom
        (ringEquiv g) :=
  (representableBy R).homEquiv_comp _ _

end dualNumber

def toDualNumber : R ⟶ dualNumber R :=
  dualNumber.ringEquiv.symm (𝟙 R • 1)

namespace dualNumber

variable {R} in
def eps : R ⟶ dualNumber R := lift 0 (𝟙 R)

@[reassoc (attr := simp)]
lemma eps_fst : eps (R := R) ≫ fst = 0 := lift_fst ..

@[reassoc (attr := simp)]
lemma eps_snd : eps (R := R) ≫ snd = 𝟙 R := lift_snd ..

@[reassoc (attr := simp)]
lemma toDualNumber_fst : toDualNumber R ≫ fst = 𝟙 R := sorry

@[reassoc (attr := simp)]
lemma toDualNumber_snd : toDualNumber R ≫ snd = 0 := sorry

variable {R} in
def hom_ext' {T : C} [CommRingObj T] {f g : dualNumber R ⟶ T} [IsRingHom f] [IsRingHom g]
    (h₁ : toDualNumber R ≫ f = toDualNumber R ≫ g) (h₂ : eps ≫ f = eps ≫ g) :
    f = g := by
  sorry

@[ext high]
lemma hom_ext'' {T : CommRng C} {f g : CommRng.mk (dualNumber R) ⟶ T}
    (h₁ : toDualNumber R ≫ f.hom = toDualNumber R ≫ g.hom)
    (h₂ : eps ≫ f.hom = eps ≫ g.hom) : f = g := sorry

set_option backward.isDefEq.respectTransparency false in
include R in
@[simp]
lemma ringEquiv_comp_toDualNumber {X : C} (r : X ⟶ R) :
    ringEquiv (r ≫ toDualNumber R) =
      algebraMap (X ⟶ R) (X ⟶ R)[ε] r := by
  simp [toDualNumber, ringEquiv_comp, yonedaCommRingObj, yonedaRingObj,
    Algebra.algebraMap_eq_smul_one]

instance : IsRingHom (toDualNumber R) := by
  rw [isRingHom_iff_yoneda]
  intro X
  rw [← isRingHom_comp_iff_of_injective _ dualNumber.ringEquiv.toRingHom
    (by exact dualNumber.ringEquiv.injective)]
  convert (algebraMap (X ⟶ R) (X ⟶ R)[ε]).isRingHom
  aesop

def ringHom : ℤ[ε] →+* (𝟙_ C ⟶ dualNumber R) :=
  intRingHomEquiv.symm ⟨ringEquiv.symm ε, ringEquiv.injective (by simp)⟩

namespace tensorCommRingCore

variable {R} {S S' : CommRng C}

def homEquiv :
    (CommRng.mk (dualNumber R) ⟶ S) ≃ (CommRng.mk R ⟶ S) × (ℤ[ε] →+* (𝟙_ C ⟶ S.X)) where
  toFun f :=
    ⟨{ hom := toDualNumber R } ≫ f,
      intRingHomEquiv.symm ⟨ringHom _ ε ≫ f.hom,
        by simp [pow_two, ← MonObj.mul_comp, ← map_mul]⟩⟩
  invFun g :=
    { hom := fst ≫ g.1.hom + snd ≫ ((toUnit _ ≫ g.2 ε) * g.1.hom)
      isRingHom := sorry }
  left_inv f := by
    ext
    · simp [precomp_add, precomp_mul]
    · simp [precomp_add, precomp_mul]
      sorry
  right_inv g := by
    ext : 1
    · ext : 1
      dsimp
      simp [precomp_add, precomp_mul]
    · simp
      simp [precomp_add, precomp_mul]
      sorry

variable (f : CommRng.mk (dualNumber R) ⟶ S)

@[simp]
lemma homEquiv_apply_fst :
    dsimp% (homEquiv f).1.hom = toDualNumber R ≫ f.hom := rfl

@[simp]
lemma homEquiv_apply_snd :
    dsimp% ((homEquiv f).2).1 ε = ringHom _ ε ≫ f.hom :=
  Subtype.ext_iff.1 (intRingHomEquiv.apply_symm_apply ⟨ringHom _ ε ≫ f.hom, _⟩)

lemma homEquiv_comp (g : S ⟶ S') :
    homEquiv (f ≫ g) =
      ((yonedaCommRingObjTensorCommRing R ℤ[ε]).map g) (homEquiv f) := by
  ext : 1
  · change _ = (homEquiv f).1 ≫ g
    cat_disch
  · apply intRingHomEquiv.injective
    ext : 1
    change _ = (homEquiv f).2 ε ≫ g.hom
    simp

end tensorCommRingCore

open tensorCommRingCore in
def tensorCommRingCore : TensorCommRingCore (toDualNumber R) (ringHom R) where
  corepresentableBy :=
    { homEquiv := homEquiv
      homEquiv_comp _ _ := homEquiv_comp _ _ }
  homEquiv_id_eq := by
    sorry

end dualNumber

end CommRingObj

end CategoryTheory
