/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.MahlerExponent
public import DiophantineApproximation.PolynomialEval

-- Used only inside proofs and in the acceptance criteria.
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Koksma's exponent is at most Mahler's

The first of Layer 1.3's comparisons: `w_n^*(ξ) ≤ w_n(ξ)` for **every** real `ξ`. An approximant
counted by `Real.koksmaExponent` is a real algebraic number `α` of degree at most `n`, carried by
its primitive irreducible minimal polynomial `P`; the mean value theorem turns `P α = 0` and
`|ξ - α| ≤ H(P) ^ (-w-1)` into `|P ξ| ≤ c * H(P) ^ (-w)`, and the constant is absorbed by
`Real.le_mahlerExponent_of_infinite`. That is the whole proof — except for one point, which is
where the mathematics is.

`Real.mahlerSet` asks for `0 < |P ξ|`, and this is not automatic: if `ξ` is itself algebraic of
degree at most `n` then its own minimal polynomial is a Koksma solution — it has conjugate roots
arbitrarily close to nothing, but it is admitted whenever some other root is near `ξ` — and it
has `P ξ = 0`. The way out is that **a primitive irreducible integer polynomial vanishing at `ξ`
is determined up to sign**, so there are at most two of them and they have one height between
them; discarding the finitely many solutions below that height costs nothing, because
`Polynomial.infinite_sep_lt_supNorm` says an infinite set of solutions of bounded degree has
members of arbitrarily large height. So no hypothesis on `ξ` is needed, and the roadmap's
prototype — which carried none — is proved as it stands.

## Main results

* `Polynomial.associated_of_isPrimitive_of_irreducible`: **two primitive irreducible integer
  polynomials with a common root are associated**, hence equal up to sign — for a root in any
  `ℚ`-algebra that is a domain.
* `Polynomial.supNorm_eq_of_isPrimitive_of_irreducible`: they have the same naive height.
* `Real.exists_supNorm_le_of_aeval_eq_zero`: the height of the minimal polynomial of `ξ`, when
  there is one, as a threshold above which every Koksma solution is a Mahler solution.
* `Real.koksmaExponent_le_mahlerExponent`: **`w_n^* ≤ w_n`**, for every real `ξ` and every `n`.

## Implementation notes

⚠ **The exclusion set is a single polynomial, not a finite set that has to be estimated.**
Gauss's lemma in both of its Mathlib forms does it:
`IsPrimitive.Int.irreducible_iff_irreducible_map_cast` moves irreducibility to `ℚ[X]`, where
`minpoly.dvd` identifies both polynomials with the minimal
polynomial of `ξ` up to a unit, and `IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast` brings the
divisibility back to `ℤ[X]`, where primitivity turns the unit into `±1`.

⚠ **The mean value theorem is applied on `[α, ξ]`, and the interval has to be bounded first.**
The constant in `Polynomial.abs_aeval_sub_aeval_le` depends on both endpoints, and `α` is only
known through `|ξ - α| ≤ H(P) ^ (-w-1)`. Integrality is what closes the loop: `H(P) ≥ 1`, so the
right-hand side is at most `1`, so `|α| ≤ |ξ| + 1` and the constant `(n+1)^2 * (|ξ|+1)^n` depends
on `ξ` and `n` alone.

⚠ **The inequality is not an equality and the gap is Wirsing's theorem.** `w_n^* ≤ w_n` is
elementary; the converse bounds `w_n ≤ w_n^* + n - 1`, `w_n ≤ 2 w_n^* - 1` and
`w_n^* ≥ w_n / (w_n - n + 1)` are Wirsing's, and none of them is in this file — see the roadmap's
Layer 1.3 for what the naive nearest-root argument does and does not give.

## References

Y. Bugeaud, *Approximation by Algebraic Numbers*, Cambridge University Press (2004), Lemma A.5
and §3.4.

This is part of Layer 1.3 of the `DiophantineApproximation` roadmap.
-/

public section

open Polynomial
open scoped ENNReal NNReal

namespace Polynomial

/-! ### The minimal polynomial of a real number is rigid -/

/-- **Two primitive irreducible integer polynomials with a common root are associated.**
Over `ℚ` both are associated to the minimal polynomial of the root, so one divides the other;
Gauss's lemma brings that divisibility back to `ℤ[X]`, where irreducibility upgrades it to an
association. The root may lie in any `ℚ`-algebra that is a domain: Layer 1.3 reads this over `ℝ`
and Layer 7.2 over `ℂ`. -/
theorem associated_of_isPrimitive_of_irreducible {A : Type*} [CommRing A] [IsDomain A]
    [Algebra ℚ A] {ξ : A} {P Q : ℤ[X]}
    (hPp : P.IsPrimitive) (hPi : Irreducible P) (hPξ : aeval ξ P = 0)
    (hQp : Q.IsPrimitive) (hQi : Irreducible Q) (hQξ : aeval ξ Q = 0) :
    Associated P Q := by
  have hcast : (Int.castRingHom ℚ) = algebraMap ℤ ℚ := rfl
  have hPQ : aeval ξ (P.map (Int.castRingHom ℚ)) = 0 := by
    rw [hcast, aeval_map_algebraMap]; exact hPξ
  have hQQ : aeval ξ (Q.map (Int.castRingHom ℚ)) = 0 := by
    rw [hcast, aeval_map_algebraMap]; exact hQξ
  have hPne : P.map (Int.castRingHom ℚ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff ((algebraMap ℤ ℚ).injective_int)).2 hPi.ne_zero
  have halg : IsAlgebraic ℚ ξ := ⟨_, hPne, hPQ⟩
  have hint : IsIntegral ℚ ξ := halg.isIntegral
  have hPirr : Irreducible (P.map (Int.castRingHom ℚ)) :=
    (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hPp).1 hPi
  have hQirr : Irreducible (Q.map (Int.castRingHom ℚ)) :=
    (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hQp).1 hQi
  have hassP : Associated (minpoly ℚ ξ) (P.map (Int.castRingHom ℚ)) :=
    (minpoly.irreducible hint).associated_of_dvd hPirr (minpoly.dvd ℚ ξ hPQ)
  have hassQ : Associated (minpoly ℚ ξ) (Q.map (Int.castRingHom ℚ)) :=
    (minpoly.irreducible hint).associated_of_dvd hQirr (minpoly.dvd ℚ ξ hQQ)
  exact hPi.associated_of_dvd hQi
    ((IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast P Q hPp).2 (hassP.symm.trans hassQ).dvd)

/-- **The naive height of the minimal polynomial of an algebraic number is well defined.** -/
theorem supNorm_eq_of_isPrimitive_of_irreducible {A : Type*} [CommRing A] [IsDomain A]
    [Algebra ℚ A] {ξ : A} {P Q : ℤ[X]}
    (hPp : P.IsPrimitive) (hPi : Irreducible P) (hPξ : aeval ξ P = 0)
    (hQp : Q.IsPrimitive) (hQi : Irreducible Q) (hQξ : aeval ξ Q = 0) :
    P.supNorm = Q.supNorm := by
  obtain ⟨u, hu⟩ := associated_of_isPrimitive_of_irreducible hPp hPi hPξ hQp hQi hQξ
  obtain ⟨r, hr, hrC⟩ := Polynomial.isUnit_iff.1 u.isUnit
  have hQ : Q = C r * P := by rw [← hu, ← hrC]; ring
  rw [hQ, supNorm_C_mul]
  rcases Int.isUnit_iff.1 hr with rfl | rfl <;> simp

end Polynomial

namespace Real

variable {n : ℕ} {ξ : ℝ}

/-- **A height above which a Koksma solution cannot vanish at `ξ`.** The primitive irreducible
integer polynomials vanishing at `ξ` are one polynomial and its negative, so their naive heights
are bounded; at a transcendental `ξ` there are none and the bound is vacuous. -/
theorem exists_supNorm_le_of_aeval_eq_zero (ξ : ℝ) :
    ∃ b : ℝ, ∀ P : ℤ[X], P.IsPrimitive → Irreducible P → aeval ξ P = 0 → P.supNorm ≤ b := by
  by_cases h : ∃ P : ℤ[X], P.IsPrimitive ∧ Irreducible P ∧ aeval ξ P = 0
  · obtain ⟨P₀, h1, h2, h3⟩ := h
    exact ⟨P₀.supNorm, fun Q hq1 hq2 hq3 ↦
      (Polynomial.supNorm_eq_of_isPrimitive_of_irreducible hq1 hq2 hq3 h1 h2 h3).le⟩
  · exact ⟨0, fun P h1 h2 h3 ↦ absurd ⟨P, h1, h2, h3⟩ h⟩

/-- **Koksma's exponent is at most Mahler's**, for every real number and every degree bound. An
approximant `α` of order `w` supplies its own minimal polynomial as a near-root of `ξ` of order
`w`, by the mean value theorem on `[α, ξ]`; the value at `ξ` is nonzero for every solution taller
than the minimal polynomial of `ξ`, and there are infinitely many of those. -/
theorem koksmaExponent_le_mahlerExponent (n : ℕ) (ξ : ℝ) :
    koksmaExponent n ξ ≤ mahlerExponent n ξ := by
  rw [koksmaExponent_le_iff]
  intro w hinf
  obtain ⟨b, hb⟩ := exists_supNorm_le_of_aeval_eq_zero ξ
  have hA0 : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 * (|ξ| + 1) ^ n := by positivity
  have hmain := le_mahlerExponent_of_infinite (n := n) (ξ := ξ) (w := (w : ℝ)) hA0 ?_
  · rwa [ENNReal.ofReal_coe_nnreal] at hmain
  refine Set.Infinite.mono ?_ (Polynomial.infinite_sep_lt_supNorm hinf (fun P hP ↦ hP.1) b)
  rintro P ⟨⟨hdeg, hprim, hirr, α, hroot, hpos, hle⟩, hBP⟩
  have hP0 : P ≠ 0 := hirr.ne_zero
  have hH1 : (1 : ℝ) ≤ P.supNorm := Polynomial.one_le_supNorm hP0
  have hne : aeval ξ P ≠ 0 := fun h ↦ absurd (hb P hprim hirr h) (not_le.2 hBP)
  -- the approximant is within distance one of `ξ`, so the interval is bounded by `ξ` alone
  have hexp : -(w : ℝ) - 1 ≤ 0 := by
    have := w.coe_nonneg
    linarith
  have hsmall : |ξ - α| ≤ 1 := hle.trans (Real.rpow_le_one_of_one_le_of_nonpos hH1 hexp)
  have hmax : max 1 (max |α| |ξ|) ≤ |ξ| + 1 := by
    have hα : |α| ≤ |ξ| + 1 := by
      have h1 : |α| - |ξ| ≤ |α - ξ| := abs_sub_abs_le_abs_sub α ξ
      rw [abs_sub_comm α ξ] at h1
      linarith
    exact max_le (by linarith [abs_nonneg ξ]) (max_le hα (by linarith))
  have hstep : |aeval ξ P| ≤ ((n : ℝ) + 1) ^ 2 * (P.supNorm * (|ξ| + 1) ^ n) * |ξ - α| := by
    have h := Polynomial.abs_aeval_sub_aeval_le hdeg α ξ
    rw [hroot, sub_zero] at h
    refine h.trans ?_
    have h1 : (0 : ℝ) ≤ max 1 (max |α| |ξ|) := le_trans zero_le_one (le_max_left _ _)
    gcongr
  refine ⟨hdeg, abs_pos.2 hne, ?_⟩
  have hHpos : (0 : ℝ) < P.supNorm := lt_of_lt_of_le zero_lt_one hH1
  calc |aeval ξ P| ≤ ((n : ℝ) + 1) ^ 2 * (P.supNorm * (|ξ| + 1) ^ n) * |ξ - α| := hstep
    _ ≤ ((n : ℝ) + 1) ^ 2 * (P.supNorm * (|ξ| + 1) ^ n) * P.supNorm ^ (-(w : ℝ) - 1) := by
        gcongr
    _ = ((n : ℝ) + 1) ^ 2 * (|ξ| + 1) ^ n
          * (P.supNorm ^ (1 : ℝ) * P.supNorm ^ (-(w : ℝ) - 1)) := by
        rw [Real.rpow_one]; ring
    _ = ((n : ℝ) + 1) ^ 2 * (|ξ| + 1) ^ n * P.supNorm ^ (-(w : ℝ)) := by
        rw [← Real.rpow_add hHpos]; ring_nf

/-! ### Acceptance criteria -/

/-- **Acceptance test: `w_n^* ≤ w_n`**, with no hypothesis on `ξ`. -/
example (n : ℕ) (ξ : ℝ) : koksmaExponent n ξ ≤ mahlerExponent n ξ :=
  koksmaExponent_le_mahlerExponent n ξ

/-- **Acceptance test: at degree one it is an equality**, which is Layer 1.2. -/
example (ξ : ℝ) : koksmaExponent 1 ξ = mahlerExponent 1 ξ :=
  koksmaExponent_one_eq_mahlerExponent_one ξ

/-- **Acceptance test: the rigidity of the minimal polynomial.** -/
example {ξ : ℝ} {P Q : ℤ[X]} (hPp : P.IsPrimitive) (hPi : Irreducible P) (hPξ : aeval ξ P = 0)
    (hQp : Q.IsPrimitive) (hQi : Irreducible Q) (hQξ : aeval ξ Q = 0) : P.supNorm = Q.supNorm :=
  Polynomial.supNorm_eq_of_isPrimitive_of_irreducible hPp hPi hPξ hQp hQi hQξ

/-- **Rejection test: a Koksma solution need not be a Mahler solution.** The proof cannot simply
feed `P` to `Real.mahlerSet`, because `Real.mahlerSet` asks for `0 < |P ξ|` and an algebraic `ξ`
of degree at most `n` is a root of its own minimal polynomial — which is a Koksma solution for
`ξ` as soon as one of its other roots is close enough. Here `√2` and `X ^ 2 - 2`. -/
example : aeval (Real.sqrt 2) (X ^ 2 - C 2 : ℤ[X]) = 0 := by
  rw [map_sub, map_pow, aeval_X, aeval_C, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

end Real
