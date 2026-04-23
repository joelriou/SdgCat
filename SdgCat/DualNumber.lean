import SdgCat.ForMathlib.DualNumber
import SdgCat.Tensor

open Opposite

universe w v u

namespace DualNumber

variable {R : Type*} [CommRing R]

def intRingHomEquiv : (ℤ[ε] →+* R) ≃ { x : R // x^2 = 0 } := sorry

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

def tensorCommRingCore : TensorCommRingCore (toDualNumber R) (ringHom R) where
  corepresentableBy :=
    { homEquiv {S} := by
        refine Equiv.trans ?_ (Equiv.prodCongr (.refl _) intRingHomEquiv.symm)
        sorry
      homEquiv_comp := sorry }
  homEquiv_id_eq := sorry

end dualNumber

end CommRingObj

end CategoryTheory
