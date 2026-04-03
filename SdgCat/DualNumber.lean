import SdgCat.ForMathlib.DualNumber
import SdgCat.Tensor

open Opposite

universe w v u

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

-- this should be part of the `CommRingObj.ofRepresentableBy` API
variable {R} in
def ringEquiv {X : C} : (X ⟶ dualNumber R) ≃+* (X ⟶ R)[ε] where
  toEquiv := (representableBy R).homEquiv
  map_mul' := sorry
  map_add' := sorry

end dualNumber

def toDualNumber : R ⟶ dualNumber R := dualNumber.ringEquiv.symm 1

instance : IsRingHom (toDualNumber R) := sorry

namespace dualNumber

def ringHom : ℤ[ε] →+* (𝟙_ C ⟶ dualNumber R) :=
  AlgHom.toRingHom (DualNumber.lift
    (⟨⟨Algebra.algHom ℤ _ _, ringEquiv.symm ε⟩, by simp [← map_mul]⟩))

def tensorCommRingCore : TensorCommRingCore (toDualNumber R) (ringHom R) := sorry

end dualNumber

end CommRingObj

end CategoryTheory
