import SdgCat.ForMathlib.RingObj

open Opposite

universe w v u

namespace CategoryTheory

open CartesianMonoidalCategory MonoidalCategory MonObj Limits
--open scoped RingObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [SymmetricCategory C]
  (R : C) [CommRingObj R] (A : Type w) [CommRing A]

namespace CommRingObj

variable (C) in
@[simps]
def yonedaTensorCommRing : CommRng C ⥤ Type max w v where
  obj T := A →+* (𝟙_ C ⟶ T.X)
  map {T₁ T₂} f :=
    TypeCat.ofHom (fun φ ↦ ((yonedaCommRing.map f).app _).hom.comp φ)

@[simps]
def yonedaCommRingObjTensorCommRing : CommRng C ⥤ Type max w v where
  obj T := (CommRng.mk R ⟶ T) × (A →+* (𝟙_ C ⟶ T.X))
  map f := TypeCat.ofHom (fun x ↦ ⟨x.1 ≫ f, (yonedaTensorCommRing C A).map f x.2⟩)

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

end CommRingObj

end CategoryTheory
