import SdgCat.ForMathlib.Ideal
import Mathlib.Algebra.DualNumber
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Polynomial.Quotient

namespace DualNumber

/- #37049
@[ext]
theorem ringHom_ext {R A : Type*} [CommRing A] [CommRing R]
    {f g : R[ε] →+* A} (h₀ : f.comp (algebraMap R R[ε]) = g.comp (algebraMap R R[ε]))
    (hε : f ε = g ε) : f = g := by
  letI := f.toAlgebra
  letI : Algebra R A := Algebra.compHom _ (algebraMap R R[ε])
  let φ₁ : R[ε] →ₐ[R] A :=
    { toRingHom := f
      commutes' _ := rfl }
  let φ₂ : R[ε] →ₐ[R] A :=
    { toRingHom := g
      commutes' r := (DFunLike.congr_fun h₀ r).symm }
  have : φ₁ = φ₂ := algHom_ext hε
  exact congr_arg AlgHom.toRingHom this-/

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

@[simp] lemma add_fst (a b : A[ε]) : (a + b).1 = a.1 + b.1 := rfl
@[simp] lemma add_snd (a b : A[ε]) : (a + b).2 = a.2 + b.2 := rfl
@[simp] lemma mul_fst (a b : A[ε]) : (a * b).1 = a.1 * b.1 := rfl
@[simp] lemma mul_snd (a b : A[ε]) : (a * b).2 = a.1 * b.2 + a.2 * b.1 := rfl
@[simp] lemma eps_fst : (ε : A[ε]).1 = 0 := rfl
@[simp] lemma eps_snd : (ε : A[ε]).2 = 1 := rfl

@[simp] lemma algebraMap_eps_snd (a : A) : (algebraMap A A[ε] a).2 = 0 := rfl

@[elab_as_elim]
lemma rec {motive : A[ε] → Prop}
    (h : ∀ (x y : A), motive (x • 1 + y • eps))
    (a : A[ε]) : motive a := by
  obtain ⟨x, y, rfl⟩ : ∃ (x : A) (y : A), a = x • 1 + y • eps :=
    ⟨a.1, a.2, by aesop⟩
  exact h _ _

@[simp]
lemma ringHom_apply_fst (f : A →+* B) (a : A[ε]) :
    (ringHom f a).1 = f a.1 := by
  induction a using DualNumber.rec with
  | h x y => simp [Algebra.smul_def]; rfl

@[simp]
lemma ringHom_apply_snd (f : A →+* B) (a : A[ε]) :
    (ringHom f a).2 = f a.2 := by
  induction a using DualNumber.rec with
  | h x y => simp [Algebra.smul_def]; rfl


variable (A) in
lemma ringHom_id :
    ringHom (.id A) = .id _ := by
  aesop

lemma ringHom_comp (f : A →+* B) (g : B →+* C) :
    ringHom (g.comp f) = (ringHom g).comp (ringHom f) := by
  aesop

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
