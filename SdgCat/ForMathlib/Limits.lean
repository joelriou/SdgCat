import Mathlib.CategoryTheory.Comma.CardinalArrow
import Mathlib.CategoryTheory.Limits.Shapes.WideEqualizers
import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import Mathlib.Data.Finite.Sum

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
