/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.StammeringWords
public import Mathlib.RingTheory.PowerSeries.Basic

-- Used only inside proofs.
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Rational power series and eventually periodic coefficients

A power series `f ∈ K⟦X⟧` is **rational** if `Q f = P` for polynomials `P` and `Q ≠ 0`. Eventually
periodic coefficients make `f` rational over any field, since `(1 - X ^ T) f` is a polynomial; over
a finite field the converse holds too. CKMR80 (§2) call this "easy to see"; it is the step of
Theorem 7 of Adamczewski–Bugeaud 2007 from a rational power series back to a periodic sequence.

## Main results

* `PowerSeries.exists_mul_eq_of_isEventuallyPeriodic`: eventually periodic ⇒ rational.
* `PowerSeries.isEventuallyPeriodic_coeff_of_mul_eq`: rational ⇒ eventually periodic, over a
  finite field.

## Implementation notes

For the converse, write `Q = X ^ e Q'` with `Q' (0) ≠ 0`. The residues of `X ^ i` modulo `Q'`
are finitely many, so two agree, and since `X` is prime to `Q'`, `Q'` divides `X ^ T - 1` for some
`T ≥ 1`. Then `X ^ e (X ^ T - 1) f` is a polynomial, and its coefficients beyond its degree say
`f_(n + T) = f_n`.
-/

@[expose] public section

open Polynomial

namespace Polynomial

/-- `Q'` with `Q' (0) ≠ 0` divides `X ^ T - 1` for some `T ≥ 1`, over a finite field. -/
theorem exists_dvd_X_pow_sub_one {K : Type*} [Field K] [Finite K] {Q : K[X]} (hQ : Q ≠ 0)
    (hX : ¬ X ∣ Q) : ∃ T, 0 < T ∧ Q ∣ X ^ T - 1 := by
  have : Finite (degreeLT K Q.natDegree) :=
    Finite.of_equiv _ (degreeLTEquiv K Q.natDegree).toEquiv.symm
  let g : ℕ → degreeLT K Q.natDegree := fun i ↦ ⟨X ^ i % Q, mem_degreeLT.mpr (by
    rw [← degree_eq_natDegree hQ]
    exact EuclideanDomain.mod_lt _ hQ)⟩
  obtain ⟨i, j, hij, hg⟩ := Finite.exists_ne_map_eq_of_infinite g
  have key : ∀ i j, i < j → X ^ i % Q = X ^ j % Q → ∃ T, 0 < T ∧ Q ∣ X ^ T - 1 := by
    intro i j hij h
    refine ⟨j - i, by omega, ?_⟩
    have hdvd : Q ∣ X ^ i * (X ^ (j - i) - 1) := by
      refine ⟨X ^ j / Q - X ^ i / Q, ?_⟩
      have e : X ^ i * (X ^ (j - i) - 1) = (X ^ j : K[X]) - X ^ i := by
        rw [mul_sub, ← pow_add, Nat.add_sub_cancel' hij.le, mul_one]
      rw [e]
      linear_combination (EuclideanDomain.div_add_mod (X ^ j) Q).symm +
        (EuclideanDomain.div_add_mod (X ^ i) Q) - h
    have hcop : IsCoprime Q (X ^ i) :=
      ((irreducible_X.coprime_iff_not_dvd.mpr hX).pow_left).symm
    exact hcop.dvd_of_dvd_mul_left hdvd
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h (congrArg Subtype.val hg)
  · exact key j i h (congrArg Subtype.val hg).symm

end Polynomial

namespace PowerSeries

variable {K : Type*} [Field K] {f : K⟦X⟧}

/-- **Eventually periodic coefficients make a power series rational.** -/
theorem exists_mul_eq_of_isEventuallyPeriodic
    (h : Function.IsEventuallyPeriodic fun n ↦ coeff n f) :
    ∃ P Q : K[X], Q ≠ 0 ∧ (Q : K⟦X⟧) * f = P := by
  obtain ⟨N, T, hT, hper⟩ := h
  refine ⟨trunc (N + T) (((1 - Polynomial.X ^ T : K[X]) : K⟦X⟧) * f),
    1 - Polynomial.X ^ T, fun h ↦ ?_, ?_⟩
  · have := congrArg (Polynomial.coeff · 0) h
    simp [Polynomial.coeff_X_pow, hT.ne] at this
  · ext m
    rw [Polynomial.coeff_coe, coeff_trunc]
    split_ifs with hm
    · rfl
    · simp only [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_pow, Polynomial.coe_X,
        sub_mul, one_mul, map_sub, coeff_X_pow_mul', show T ≤ m by omega, ↓reduceIte]
      have := hper (m - T) (by omega)
      simp only [Nat.sub_add_cancel (show T ≤ m by omega)] at this
      rw [this, sub_self]

/-- **A rational power series over a finite field has eventually periodic coefficients.** -/
theorem isEventuallyPeriodic_coeff_of_mul_eq [Finite K] {P Q : K[X]} (hQ : Q ≠ 0)
    (h : (Q : K⟦X⟧) * f = P) : Function.IsEventuallyPeriodic fun n ↦ coeff n f := by
  obtain ⟨Q', hQeq, hndvd⟩ := Q.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hQ 0
  simp only [map_zero, sub_zero] at hQeq hndvd
  set e := rootMultiplicity 0 Q
  have hQ' : Q' ≠ 0 := by
    rintro rfl
    exact hQ (by rw [hQeq, mul_zero])
  obtain ⟨T, hT, R, hR⟩ := Polynomial.exists_dvd_X_pow_sub_one hQ' hndvd
  have hL : (X ^ (e + T) * f - X ^ e * f : K⟦X⟧) = ((R * P : K[X]) : K⟦X⟧) := by
    have h' : ((Polynomial.X ^ e * Q' : K[X]) : K⟦X⟧) * f = P := by rw [← hQeq]; exact h
    have hR' : ((Polynomial.X ^ T - 1 : K[X]) : K⟦X⟧) = (Q' : K⟦X⟧) * R := by
      rw [hR]; push_cast; ring
    push_cast at h' hR' ⊢
    linear_combination (R : K⟦X⟧) * h' + (X ^ e * f : K⟦X⟧) * hR'
  refine ⟨(R * P).natDegree + 1, T, hT, fun n hn ↦ ?_⟩
  have := congrArg (coeff (n + T + e)) hL
  simp only [map_sub, coeff_X_pow_mul', show e + T ≤ n + T + e by omega,
    show e ≤ n + T + e by omega, ↓reduceIte] at this
  rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)] at this
  rw [show n + T + e - (e + T) = n by omega, show n + T + e - e = n + T by omega] at this
  exact (sub_eq_zero.mp this).symm

end PowerSeries
