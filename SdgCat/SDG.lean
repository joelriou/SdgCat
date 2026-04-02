import SdgCat.ForMathlib.RingObjIHom
import SdgCat.DualNumber
import SdgCat.Spec
import SdgCat.Tensor

open Opposite

universe w v u

namespace CategoryTheory

open CartesianMonoidalCategory MonoidalCategory MonObj Limits

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [SymmetricCategory C]
  (R : C) [CommRingObj R] (A : Type w) [CommRing A]

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
