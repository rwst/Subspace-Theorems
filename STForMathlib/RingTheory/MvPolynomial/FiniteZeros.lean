/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.Algebra.MvPolynomial.Equiv

-- Used only inside proofs.
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Ideals of full height have finitely many zeros

In `K[X_s | s ∈ σ]`, `σ` finite, every prime containing an ideal `I` of height `≥ |σ|` is minimal
over `I`: a strictly smaller prime would push the height past `dim K[X] = |σ|`. The zeros `P` of
`I` in `K^σ` give distinct primes `ker (eval P)` over `I`, so they are finitely many. No
Nullstellensatz is needed, since only the points with coordinates in `K` are counted.

## Main statements

* `MvPolynomial.finite_setOf_forall_eval_eq_zero`: an ideal of height `≥ |σ|` has finitely many
  zeros in `K^σ`.
-/

@[expose] public section

namespace MvPolynomial

variable {σ K : Type*} [Field K] [Finite σ]

/-- **Ideals of full height have finitely many zeros.** -/
theorem finite_setOf_forall_eval_eq_zero {I : Ideal (MvPolynomial σ K)}
    (hI : (Nat.card σ : ℕ∞) ≤ I.height) : {P : σ → K | ∀ p ∈ I, eval P p = 0}.Finite := by
  set Z := {P : σ → K | ∀ p ∈ I, eval P p = 0}
  have hinj : Set.InjOn (fun P : σ → K ↦ RingHom.ker (eval P)) Z := by
    intro P _ P' _ h
    funext s
    have hs : X s - C (P s) ∈ RingHom.ker (eval P) := by simp [RingHom.mem_ker]
    rw [show RingHom.ker (eval P) = RingHom.ker (eval P') from h, RingHom.mem_ker] at hs
    simp only [map_sub, eval_X, eval_C, sub_eq_zero] at hs
    exact hs.symm
  refine Set.Finite.of_finite_image
    ((Ideal.finite_minimalPrimes_of_isNoetherianRing _ I).subset ?_) hinj
  rintro _ ⟨P, hP, rfl⟩
  have hprime : (RingHom.ker (eval P)).IsPrime := RingHom.ker_isPrime _
  refine ⟨⟨hprime, fun p hp ↦ hP p hp⟩, fun Q hQ hQP ↦ ?_⟩
  have := hQ.1
  by_contra hne
  have hlt : Q < RingHom.ker (eval P) := lt_of_le_of_ne hQP fun h ↦ hne (h ▸ le_rfl)
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have h2 : (RingHom.ker (eval P)).height ≤ Nat.card σ := by
    have := Ideal.height_le_ringKrullDim_of_isPrime (I := RingHom.ker (eval P))
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
      zero_add] at this
    exact_mod_cast this
  have h3 : (Nat.card σ : ℕ∞) + 1 ≤ Nat.card σ :=
    ((add_le_add_left (hI.trans (Ideal.height_mono hQ.2)) 1).trans h1).trans h2
  have : Nat.card σ + 1 ≤ Nat.card σ := by exact_mod_cast h3
  omega

end MvPolynomial
