import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.FinitePresentation
import SdgCat.ForMathlib.Ideal
import SdgCat.ForMathlib.RingObjIHom

open Opposite

universe w v u

lemma Option.eq₂ {α β : Type*} (f : Option α → β) (hf : ∀ (i : α), f (some i) = f none)
    (i j : Option α) : f i = f j := by
  obtain _ | i := i <;> obtain _ | j := j <;> simp [hf]

namespace CategoryTheory

open CartesianMonoidalCategory MonoidalCategory Limits

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
  map f := TypeCat.ofHom (fun g ↦ ((yonedaRingObj R).map f).hom.comp g)

@[simps]
def yonedaSpecFunctor : CommRingCat.{w}ᵒᵖ ⥤ Cᵒᵖ ⥤ Type max v w where
  obj A := yonedaSpec R A.unop
  map φ := { app X := TypeCat.ofHom (fun g ↦ g.comp φ.unop.hom) }

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
  yoneda.preimage { app X := TypeCat.ofHom (fun f ↦ yonedaSpecHomEquiv f a) }

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

end CommRingObj

end CategoryTheory
