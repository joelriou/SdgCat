import Mathlib.RingTheory.Ideal.Maps

lemma Ideal.le_ker_iff {α β : Type*} [Ring α] [Ring β] (f : α →+* β)
    (I : Ideal α) :
    I ≤ RingHom.ker f ↔ (∀ i ∈ I, f i = 0) :=
  Iff.rfl
