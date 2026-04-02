import SdgCat.ForMathlib.DualNumber
import SdgCat.ForMathlib.RingObj

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

end CommRingObj

end CategoryTheory
