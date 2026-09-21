/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.RootLocation
public import DiophantineApproximation.SimultaneousBox

/-!
# Wirsing's system of test points

Wirsing's third inequality runs on one polynomial per height bound `H`, produced by asking an
integer polynomial of degree at most `n` to be *tiny* at `ξ` and merely *bounded* at `n - 1`
further points. This file builds that polynomial and extracts its root near `ξ`.

The points are `Real.testPoint ξ`: the first is `ξ`, and the others are `|ξ| + 2 + j`, which are
at distance at least `2` from `ξ` and at least `1` from each other, and all bounded by
`|ξ| + n + 2`. Nothing else about them matters.

## Main results

* `Real.testPoint`: the points, with `Real.abs_testPoint_le`, `Real.one_le_abs_testPoint_sub` and
  `Real.two_le_abs_sub_testPoint` for the three properties just listed.
* `Real.exists_poly_small_at_testPoints`: **the system has a solution.** For every `w ≥ n` and
  every `H ≥ 1` there is a nonzero integer polynomial of degree at most `n` and naive height at
  most `K H ^ (w - n + 1)`, with `K` depending only on `ξ` and `n`, which is at most `H ^ (-w)` at
  `ξ` and at most `H` at each of the other points.
* `Real.exists_real_root_of_small_at_testPoints`: **the solution has a real root near `ξ`.** If
  the polynomial is small at all `n` points and its height exceeds `(8B + 8) ^ n` times that
  bound, then it has a *real* root `a` with `|ξ - a| H(P) ≤ (2B + 2) ^ n |P ξ|`.

## Implementation notes

⚠ **Pigeonhole replaces Minkowski, and only a constant is lost.** The classical proof asks
Minkowski's linear forms theorem for a polynomial with `|P ξ| ≤ H ^ (-w)`, `|P(x_j)| ≤ H` and
`|P(x_n)| ≤ c H ^ (w - n + 1)`: `n + 1` forms in the `n + 1` coefficients, with the product of the
bounds equal to the determinant. The pigeonhole of `DiophantineApproximation/SimultaneousBox.lean`
controls only the first `n` of those forms and lets the last one be the *coefficient* bound `A`,
which is what the last Minkowski bound was for; the price is the constant `K`, and the exponent
`w - n + 1` is unchanged.

⚠ **The root near `ξ` is real for a counting reason, not an analytic one.** `P` has degree at most
`n` and a root within `1/2` of each of the `n` points, so it has exactly one root there and its
roots are simple. The disc around `ξ` is stable under conjugation, so the root inside it is its
own conjugate. This is the archimedean form of the Krasner argument that the ultrametric
analogues of this layer use.

⚠ **`P` is not assumed primitive or irreducible here.** Both are needed for `koksmaSet`, and both
are arranged later, by passing to an irreducible factor of the primitive part; what this file
produces is only the real root and the inequality it satisfies.

## References

Y. Bugeaud, *Exponents of Diophantine approximation*, in: Dynamics and Analytic Number Theory,
Cambridge University Press (2016), proof of Theorem 2.6, itself following E. Wirsing,
*Approximation mit algebraischen Zahlen beschränkten Grades*, J. reine angew. Math. **206**
(1961), 67–77.

This is part of Layer 1.3 of the `DiophantineApproximation` roadmap.
-/

public section

open Polynomial
open scoped ENNReal NNReal

namespace Real

/-! ### The test points -/

/-- **Wirsing's test points.** The point of index `0` is `ξ` itself; the others are
`|ξ| + 2 + j`. -/
@[expose] def testPoint (ξ : ℝ) {n : ℕ} (j : Fin n) : ℝ :=
  if (j : ℕ) = 0 then ξ else |ξ| + 2 + (j : ℕ)

/-- The test point of index `0` is `ξ`. -/
theorem testPoint_zero {ξ : ℝ} {n : ℕ} {j : Fin n} (hj : (j : ℕ) = 0) : testPoint ξ j = ξ := by
  simp [testPoint, hj]

/-- A test point other than the first is `|ξ| + 2 + j`. -/
theorem testPoint_of_ne_zero {ξ : ℝ} {n : ℕ} {j : Fin n} (hj : (j : ℕ) ≠ 0) :
    testPoint ξ j = |ξ| + 2 + (j : ℕ) := by
  simp only [testPoint]
  exact ite_eq_right_of_eq_false _ _ (eq_false hj)

/-- Every test point is bounded by `|ξ| + n + 2`. -/
theorem abs_testPoint_le (ξ : ℝ) {n : ℕ} (j : Fin n) : |testPoint ξ j| ≤ |ξ| + n + 2 := by
  rcases eq_or_ne (j : ℕ) 0 with hj | hj
  · rw [testPoint_zero hj]
    have : (0 : ℝ) ≤ (n : ℝ) := by positivity
    linarith [le_abs_self ξ, abs_nonneg ξ]
  · have hjn : ((j : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_of_lt j.isLt
    have h0 : (0 : ℝ) ≤ |ξ| + 2 + (j : ℕ) := by positivity
    rw [testPoint_of_ne_zero hj, abs_of_nonneg h0]
    linarith

/-- Distinct test points are at distance at least `1`. -/
theorem one_le_abs_testPoint_sub (ξ : ℝ) {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    1 ≤ |testPoint ξ i - testPoint ξ j| := by
  have habs := abs_nonneg ξ
  have hself := le_abs_self ξ
  rcases eq_or_ne (i : ℕ) 0 with hi | hi
  · have hj : (j : ℕ) ≠ 0 := by
      intro h
      exact hij (Fin.ext (by rw [hi, h]))
    have hj1 : (1 : ℝ) ≤ ((j : ℕ) : ℝ) := by
      have : 1 ≤ (j : ℕ) := Nat.one_le_iff_ne_zero.2 hj
      exact_mod_cast this
    rw [testPoint_zero hi, testPoint_of_ne_zero hj]
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · rcases eq_or_ne (j : ℕ) 0 with hj | hj
    · have hi1 : (1 : ℝ) ≤ ((i : ℕ) : ℝ) := by
        have : 1 ≤ (i : ℕ) := Nat.one_le_iff_ne_zero.2 hi
        exact_mod_cast this
      rw [testPoint_zero hj, testPoint_of_ne_zero hi]
      rw [abs_of_nonneg (by linarith)]
      linarith
    · have hne : ((i : ℕ) : ℝ) ≠ ((j : ℕ) : ℝ) := by
        intro h
        exact hij (Fin.ext (by exact_mod_cast h))
      rw [testPoint_of_ne_zero hi, testPoint_of_ne_zero hj]
      have : |ξ| + 2 + ((i : ℕ) : ℝ) - (|ξ| + 2 + ((j : ℕ) : ℝ)) =
          ((i : ℕ) : ℝ) - ((j : ℕ) : ℝ) := by ring
      rw [this]
      rcases lt_or_gt_of_ne hne with h | h
      · rw [abs_of_nonpos (by linarith)]
        have : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by
          have : (i : ℕ) + 1 ≤ (j : ℕ) := by exact_mod_cast Nat.succ_le_of_lt (by exact_mod_cast h)
          exact_mod_cast this
        linarith
      · rw [abs_of_nonneg (by linarith)]
        have : ((j : ℕ) : ℝ) + 1 ≤ ((i : ℕ) : ℝ) := by
          have : (j : ℕ) + 1 ≤ (i : ℕ) := by exact_mod_cast Nat.succ_le_of_lt (by exact_mod_cast h)
          exact_mod_cast this
        linarith

/-- A test point other than the first is at distance at least `2` from `ξ`. -/
theorem two_le_abs_sub_testPoint (ξ : ℝ) {n : ℕ} {j : Fin n} (hj : (j : ℕ) ≠ 0) :
    2 ≤ |ξ - testPoint ξ j| := by
  have habs := abs_nonneg ξ
  have hself := le_abs_self ξ
  have hj0 : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := by positivity
  rw [testPoint_of_ne_zero hj, abs_sub_comm, abs_of_nonneg (by linarith)]
  linarith

/-! ### The polynomial of Wirsing's system -/

/-- **Wirsing's system has a solution at every height.** There is a constant `K`, depending only
on `ξ` and `n`, such that for every `w ≥ n` and every `H ≥ 1` some nonzero integer polynomial of
degree at most `n` and naive height at most `K H ^ (w - n + 1)` is at most `H ^ (-w)` at `ξ` and
at most `H` at every other test point. -/
theorem exists_poly_small_at_testPoints (ξ : ℝ) {n : ℕ} (hn : 0 < n) :
    ∃ K : ℝ, 0 < K ∧ ∀ w : ℝ, (n : ℝ) ≤ w → ∀ H : ℝ, 1 ≤ H →
      ∃ P : ℤ[X], P ≠ 0 ∧ P.natDegree ≤ n ∧ P.supNorm ≤ K * H ^ (w - n + 1) ∧
        |aeval ξ P| ≤ H ^ (-w) ∧
        ∀ j : Fin n, (j : ℕ) ≠ 0 → |aeval (testPoint ξ j) P| ≤ H := by
  classical
  set B : ℝ := |ξ| + n + 2 with hBdef
  have hB1 : (1 : ℝ) ≤ B := by
    have : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have := abs_nonneg ξ
    rw [hBdef]; linarith
  set T : ℝ := ((n : ℝ) + 1) * B ^ n with hTdef
  have hT1 : (1 : ℝ) ≤ T := by
    have h1 : (1 : ℝ) ≤ B ^ n := one_le_pow₀ hB1
    have h2 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    rw [hTdef]
    nlinarith
  have hTsum : ∀ j : Fin n, (∑ k ∈ Finset.range (n + 1), |testPoint ξ j| ^ k) ≤ T := by
    intro j
    have hb : ∀ k ∈ Finset.range (n + 1), |testPoint ξ j| ^ k ≤ B ^ n := by
      intro k hk
      have hk' : k ≤ n := by have := Finset.mem_range.1 hk; omega
      calc |testPoint ξ j| ^ k ≤ B ^ k := by
            exact pow_le_pow_left₀ (abs_nonneg _) (abs_testPoint_le ξ j) k
        _ ≤ B ^ n := pow_le_pow_right₀ hB1 hk'
    calc (∑ k ∈ Finset.range (n + 1), |testPoint ξ j| ^ k) ≤
          ∑ _k ∈ Finset.range (n + 1), B ^ n := Finset.sum_le_sum hb
      _ = ((n : ℝ) + 1) * B ^ n := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
      _ = T := by rw [hTdef]
  refine ⟨(3 * T) ^ n + 4, by positivity, ?_⟩
  intro w hw H hH
  have hH0 : (0 : ℝ) < H := by linarith
  have hexp : (1 : ℝ) ≤ w - n + 1 := by linarith
  have hHexp : H ≤ H ^ (w - n + 1) := by
    calc H = H ^ (1 : ℝ) := (Real.rpow_one H).symm
      _ ≤ H ^ (w - n + 1) := Real.rpow_le_rpow_of_exponent_le hH hexp
  have hHexp1 : (1 : ℝ) ≤ H ^ (w - n + 1) := le_trans hH hHexp
  set A : ℕ := ⌈(3 * T) ^ n * H ^ (w - n + 1)⌉₊ + ⌈H⌉₊ + 1 with hAdef
  have hAlow : (3 * T) ^ n * H ^ (w - n + 1) ≤ (A : ℝ) := by
    have h1 : (3 * T) ^ n * H ^ (w - n + 1) ≤ (⌈(3 * T) ^ n * H ^ (w - n + 1)⌉₊ : ℝ) :=
      Nat.le_ceil _
    have h2 : ((⌈(3 * T) ^ n * H ^ (w - n + 1)⌉₊ : ℕ) : ℝ) ≤ (A : ℝ) := by
      rw [hAdef]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈H⌉₊]
    linarith
  have hAH : H ≤ (A : ℝ) := by
    have h1 : H ≤ (⌈H⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈H⌉₊ : ℕ) : ℝ) ≤ (A : ℝ) := by
      rw [hAdef]; push_cast
      linarith [Nat.cast_nonneg (α := ℝ) ⌈(3 * T) ^ n * H ^ (w - n + 1)⌉₊]
    linarith
  have hA1 : (1 : ℝ) ≤ (A : ℝ) := le_trans hH hAH
  have hAup : (A : ℝ) ≤ ((3 * T) ^ n + 4) * H ^ (w - n + 1) := by
    have h1 : (⌈(3 * T) ^ n * H ^ (w - n + 1)⌉₊ : ℝ) < (3 * T) ^ n * H ^ (w - n + 1) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have h2 : (⌈H⌉₊ : ℝ) < H + 1 := Nat.ceil_lt_add_one (by linarith)
    have hexpand : ((3 * T) ^ n + 4) * H ^ (w - n + 1) =
        (3 * T) ^ n * H ^ (w - n + 1) + 4 * H ^ (w - n + 1) := by ring
    rw [hAdef, hexpand]
    push_cast
    linarith
  -- the box widths
  set β : Fin n → ℝ := fun j ↦ if (j : ℕ) = 0 then H ^ (-w) else H with hβdef
  have hβ_zero : ∀ j : Fin n, (j : ℕ) = 0 → β j = H ^ (-w) := by
    intro j hj
    simp only [hβdef]
    exact ite_eq_left_of_eq_true _ _ (eq_true hj)
  have hβ_ne : ∀ j : Fin n, (j : ℕ) ≠ 0 → β j = H := by
    intro j hj
    simp only [hβdef]
    exact ite_eq_right_of_eq_false _ _ (eq_false hj)
  have hβ0 : ∀ j, 0 < β j := by
    intro j
    by_cases hj : (j : ℕ) = 0
    · rw [hβ_zero j hj]
      exact Real.rpow_pos_of_pos hH0 _
    · rw [hβ_ne j hj]
      exact hH0
  -- the box count
  have hbox : ∏ j : Fin n,
      (2 * (A : ℝ) * (∑ k ∈ Finset.range (n + 1), |testPoint ξ j| ^ k) / β j + 1) <
      ((A : ℝ) + 1) ^ (n + 1) := by
    set g : Fin n → ℝ := fun j ↦ if (j : ℕ) = 0 then 3 * (A : ℝ) * T * H ^ w
      else 3 * (A : ℝ) * T / H with hgdef
    have hstep : ∀ j : Fin n,
        2 * (A : ℝ) * (∑ k ∈ Finset.range (n + 1), |testPoint ξ j| ^ k) / β j + 1 ≤ g j := by
      intro j
      have hnum : 2 * (A : ℝ) * (∑ k ∈ Finset.range (n + 1), |testPoint ξ j| ^ k) ≤
          2 * (A : ℝ) * T := by
        have := hTsum j
        nlinarith
      by_cases hj : (j : ℕ) = 0
      · have hgj : g j = 3 * (A : ℝ) * T * H ^ w := by
          simp only [hgdef]
          exact ite_eq_left_of_eq_true _ _ (eq_true hj)
        have hinv : H ^ (-w) = (H ^ w)⁻¹ := Real.rpow_neg (le_of_lt hH0) w
        have hHw : (1 : ℝ) ≤ H ^ w := Real.one_le_rpow hH (by linarith)
        have hS0 : (0 : ℝ) ≤ ∑ k ∈ Finset.range (n + 1), |testPoint ξ j| ^ k :=
          Finset.sum_nonneg fun k _ ↦ by positivity
        have hHw0 : (0 : ℝ) < H ^ w := lt_of_lt_of_le zero_lt_one hHw
        have step1 : (2 * (A : ℝ) * (∑ k ∈ Finset.range (n + 1), |testPoint ξ j| ^ k)) * H ^ w
            ≤ (2 * (A : ℝ) * T) * H ^ w := mul_le_mul_of_nonneg_right hnum hHw0.le
        have hAT : (1 : ℝ) ≤ (A : ℝ) * T := by nlinarith [hA1, hT1]
        have step2 : (1 : ℝ) ≤ (A : ℝ) * T * H ^ w := by nlinarith [hAT, hHw]
        rw [hβ_zero j hj, hgj, hinv, div_eq_mul_inv, inv_inv]
        linarith
      · have hgj : g j = 3 * (A : ℝ) * T / H := by
          simp only [hgdef]
          exact ite_eq_right_of_eq_false _ _ (eq_false hj)
        rw [hβ_ne j hj, hgj, div_add' _ _ _ (ne_of_gt hH0), div_le_div_iff_of_pos_right hH0]
        nlinarith
    have hprod : ∏ j : Fin n,
        (2 * (A : ℝ) * (∑ k ∈ Finset.range (n + 1), |testPoint ξ j| ^ k) / β j + 1) ≤
        ∏ j : Fin n, g j := by
      refine Finset.prod_le_prod₀ (fun j _ ↦ ?_) fun j _ ↦ hstep j
      have h1 : (0 : ℝ) ≤ 2 * (A : ℝ) * (∑ k ∈ Finset.range (n + 1), |testPoint ξ j| ^ k) := by
        have : (0 : ℝ) ≤ ∑ k ∈ Finset.range (n + 1), |testPoint ξ j| ^ k :=
          Finset.sum_nonneg fun k _ ↦ by positivity
        nlinarith
      have := div_nonneg h1 (hβ0 j).le
      linarith
    have hj0 : (⟨0, hn⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
    have hgval : ∏ j : Fin n, g j =
        (3 * (A : ℝ) * T * H ^ w) * (3 * (A : ℝ) * T / H) ^ (n - 1) := by
      have hg0 : g ⟨0, hn⟩ = 3 * (A : ℝ) * T * H ^ w := by simp [hgdef]
      have hgerase : ∀ j ∈ (Finset.univ : Finset (Fin n)).erase ⟨0, hn⟩,
          g j = 3 * (A : ℝ) * T / H := by
        intro j hj
        have hjne : (j : ℕ) ≠ 0 := by
          intro h
          exact (Finset.mem_erase.1 hj).1 (Fin.ext (by simpa using h))
        simp only [hgdef]
        exact ite_eq_right_of_eq_false _ _ (eq_false hjne)
      rw [← Finset.mul_prod_erase _ g hj0, hg0, Finset.prod_congr rfl hgerase,
        Finset.prod_const, Finset.card_erase_of_mem hj0, Finset.card_univ, Fintype.card_fin]
    have hfinal : (3 * (A : ℝ) * T * H ^ w) * (3 * (A : ℝ) * T / H) ^ (n - 1) =
        (3 * T) ^ n * H ^ (w - n + 1) * (A : ℝ) ^ n := by
      have hHn : (H : ℝ) ^ (n - 1 : ℕ) = H ^ ((n : ℝ) - 1) := by
        rw [← Real.rpow_natCast H (n - 1), Nat.cast_sub hn, Nat.cast_one]
      have hpow : H ^ w / H ^ ((n : ℝ) - 1) = H ^ (w - n + 1) := by
        rw [← Real.rpow_sub hH0]
        congr 1
        ring
      have hgroup : (3 * (A : ℝ) * T) ^ (n - 1) * (3 * (A : ℝ) * T) = (3 * (A : ℝ) * T) ^ n := by
        rw [← pow_succ]
        congr 1
        omega
      have hsplit : (3 * (A : ℝ) * T) ^ n = (3 * T) ^ n * (A : ℝ) ^ n := by
        rw [← mul_pow]
        congr 1
        ring
      calc (3 * (A : ℝ) * T * H ^ w) * (3 * (A : ℝ) * T / H) ^ (n - 1)
          = (3 * (A : ℝ) * T) ^ (n - 1) * (3 * (A : ℝ) * T) * (H ^ w / H ^ (n - 1 : ℕ)) := by
            rw [div_pow]; ring
        _ = (3 * (A : ℝ) * T) ^ n * (H ^ w / H ^ ((n : ℝ) - 1)) := by rw [hgroup, hHn]
        _ = (3 * (A : ℝ) * T) ^ n * H ^ (w - n + 1) := by rw [hpow]
        _ = (3 * T) ^ n * H ^ (w - n + 1) * (A : ℝ) ^ n := by rw [hsplit]; ring
    refine lt_of_le_of_lt (hprod.trans (le_of_eq hgval)) ?_
    rw [hfinal]
    have hAn0 : (0 : ℝ) < (A : ℝ) ^ n := by positivity
    calc (3 * T) ^ n * H ^ (w - n + 1) * (A : ℝ) ^ n ≤ (A : ℝ) * (A : ℝ) ^ n := by
          exact mul_le_mul_of_nonneg_right hAlow (le_of_lt hAn0)
      _ = (A : ℝ) ^ (n + 1) := by rw [pow_succ]; ring
      _ < ((A : ℝ) + 1) ^ (n + 1) := by
          refine pow_lt_pow_left₀ (by linarith) (by linarith) (by omega)
  obtain ⟨P, hP0, hPdeg, hPsup, hPval⟩ :=
    Polynomial.exists_ne_zero_abs_aeval_le n A (testPoint ξ) β hβ0 hbox
  refine ⟨P, hP0, hPdeg, le_trans hPsup hAup, ?_, ?_⟩
  · have := hPval ⟨0, hn⟩
    rwa [testPoint_zero (show ((⟨0, hn⟩ : Fin n) : ℕ) = 0 from rfl),
      hβ_zero ⟨0, hn⟩ rfl] at this
  · intro j hj
    have := hPval j
    rwa [hβ_ne j hj] at this

/-! ### The real root near `ξ` -/

/-- The complex evaluation of an integer polynomial at a real point is its real evaluation. -/
theorem norm_eval_map_complex (P : ℤ[X]) (x : ℝ) :
    ‖eval ((x : ℝ) : ℂ) (P.map (Int.castRingHom ℂ))‖ = |aeval x P| := by
  have hcomp : (Complex.ofRealHom.comp (Int.castRingHom ℝ)) = Int.castRingHom ℂ := by
    ext c
    simp
  have h := Polynomial.hom_eval₂ P (Int.castRingHom ℝ) Complex.ofRealHom x
  rw [hcomp] at h
  have h2 : eval ((x : ℝ) : ℂ) (P.map (Int.castRingHom ℂ)) =
      eval₂ (Int.castRingHom ℂ) ((x : ℝ) : ℂ) P := eval_map _ _
  have h4 : (Complex.ofRealHom x : ℂ) = ((x : ℝ) : ℂ) := rfl
  rw [h4] at h
  have h3 : aeval x P = eval₂ (Int.castRingHom ℝ) x P := rfl
  rw [h2, h3, ← h]
  change ‖((eval₂ (Int.castRingHom ℝ) x P : ℝ) : ℂ)‖ = |eval₂ (Int.castRingHom ℝ) x P|
  rw [Complex.norm_real, Real.norm_eq_abs]

/-- The distinct test points, seen in `ℂ`, are at distance at least `1`. -/
theorem one_le_norm_testPoint_sub (ξ : ℝ) {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    1 ≤ ‖((testPoint ξ i : ℝ) : ℂ) - ((testPoint ξ j : ℝ) : ℂ)‖ := by
  have h : ((testPoint ξ i : ℝ) : ℂ) - ((testPoint ξ j : ℝ) : ℂ) =
      ((testPoint ξ i - testPoint ξ j : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.norm_real, Real.norm_eq_abs]
  exact one_le_abs_testPoint_sub ξ hij

/-- **The solution of Wirsing's system has a real root near `ξ`.** If `P` has degree at most `n`,
is at most `h` at every test point, and has naive height larger than `(8B + 8) ^ n h`, then `P`
has a real root `a` with `|ξ - a| H(P) ≤ (2B + 2) ^ n |P ξ|`. -/
theorem exists_real_root_of_small_at_testPoints (ξ : ℝ) {n : ℕ} (hn : 0 < n) {B h : ℝ}
    (hB : |ξ| + n + 2 ≤ B) {P : ℤ[X]} (hP0 : P ≠ 0) (hdeg : P.natDegree ≤ n)
    (hsmall : ∀ j : Fin n, |aeval (testPoint ξ j) P| ≤ h)
    (hbig : (8 * B + 8) ^ n * h < P.supNorm) :
    ∃ a : ℝ, aeval a P = 0 ∧ |ξ - a| * P.supNorm ≤ (2 * B + 2) ^ n * |aeval ξ P| := by
  classical
  have hB1 : (1 : ℝ) ≤ B := by
    have h1 : (0 : ℝ) ≤ |ξ| := abs_nonneg ξ
    have h2 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  set q : ℂ[X] := P.map (Int.castRingHom ℂ) with hqdef
  have hinj : Function.Injective (Int.castRingHom ℂ) := fun _ _ hh ↦ Int.cast_injective hh
  have hq0 : q ≠ 0 := (Polynomial.map_ne_zero_iff hinj).2 hP0
  have hqdeg : q.natDegree = P.natDegree := natDegree_map_eq_of_injective hinj P
  have hMlow : P.supNorm ≤ 2 ^ P.natDegree * q.mahlerMeasure :=
    supNorm_le_two_pow_mul_mahlerMeasure P
  have hM0 : 0 ≤ q.mahlerMeasure := mahlerMeasure_nonneg q
  have hpow2 : (2 : ℝ) ^ P.natDegree ≤ 2 ^ n := by
    exact pow_le_pow_right₀ (by norm_num) hdeg
  have hsup2 : P.supNorm ≤ 2 ^ n * q.mahlerMeasure :=
    le_trans hMlow (mul_le_mul_of_nonneg_right hpow2 hM0)
  -- a root near every test point
  have hroot : ∀ j : Fin n, ∃ a ∈ q.roots, ‖a - ((testPoint ξ j : ℝ) : ℂ)‖ < 1 / 2 := by
    intro j
    have hxB : ‖((testPoint ξ j : ℝ) : ℂ)‖ ≤ B := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact le_trans (abs_testPoint_le ξ j) hB
    have hlt : ‖eval ((testPoint ξ j : ℝ) : ℂ) q‖ <
        ((1 / 2 : ℝ) / (2 * B + 2)) ^ n * q.mahlerMeasure := by
      have hval : ‖eval ((testPoint ξ j : ℝ) : ℂ) q‖ = |aeval (testPoint ξ j) P| :=
        norm_eval_map_complex P _
      have hne : (2 * B + 2 : ℝ) ≠ 0 := by positivity
      have hratio : ((1 / 2 : ℝ) / (2 * B + 2)) ^ n * q.mahlerMeasure * (8 * B + 8) ^ n =
          2 ^ n * q.mahlerMeasure := by
        have hexp : ((1 / 2 : ℝ) / (2 * B + 2)) ^ n * (8 * B + 8) ^ n = 2 ^ n := by
          rw [← mul_pow]
          have h5 : (1 / 2 : ℝ) / (2 * B + 2) * (8 * B + 8) = 2 := by field_simp; ring
          rw [h5]
        calc ((1 / 2 : ℝ) / (2 * B + 2)) ^ n * q.mahlerMeasure * (8 * B + 8) ^ n
            = (((1 / 2 : ℝ) / (2 * B + 2)) ^ n * (8 * B + 8) ^ n) * q.mahlerMeasure := by ring
          _ = 2 ^ n * q.mahlerMeasure := by rw [hexp]
      have hpos : (0 : ℝ) < (8 * B + 8) ^ n := by positivity
      rw [hval]
      refine lt_of_mul_lt_mul_right ?_ hpos.le
      rw [hratio]
      calc |aeval (testPoint ξ j) P| * (8 * B + 8) ^ n ≤ h * (8 * B + 8) ^ n :=
            mul_le_mul_of_nonneg_right (hsmall j) hpos.le
        _ < P.supNorm := by linarith [hbig]
        _ ≤ 2 ^ n * q.mahlerMeasure := hsup2
    obtain ⟨a, ha, hlt'⟩ := exists_root_norm_sub_lt (p := q) (x := ((testPoint ξ j : ℝ) : ℂ))
      (ρ := 1 / 2) (B := B) (n := n) (by norm_num) (by norm_num) hB1 hxB
      (by rw [hqdeg]; exact hdeg) hlt
    exact ⟨a, ha, by rwa [norm_sub_rev] at hlt'⟩
  choose f hf hfs using hroot
  obtain ⟨hnd, himg⟩ := roots_toFinset_eq_image (p := q) (m := n) (by rw [hqdeg]; exact hdeg)
    (s := fun j ↦ ((testPoint ξ j : ℝ) : ℂ)) (f := f) (ρ := 1 / 2) le_rfl
    (fun i j hij ↦ one_le_norm_testPoint_sub ξ hij) hf hfs
  set j₀ : Fin n := ⟨0, hn⟩ with hj₀
  have hs₀ : ((testPoint ξ j₀ : ℝ) : ℂ) = ((ξ : ℝ) : ℂ) := by
    rw [testPoint_zero (show ((j₀ : Fin n) : ℕ) = 0 from rfl)]
  set α : ℂ := f j₀ with hαdef
  -- every root is one of the chosen ones
  have hmem : ∀ β ∈ q.roots, ∃ i : Fin n, β = f i := by
    intro β hβ
    have : β ∈ q.roots.toFinset := Multiset.mem_toFinset.2 hβ
    rw [himg] at this
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 this
    exact ⟨i, hi.symm⟩
  -- the root near ξ is unique
  have hunique : ∀ β ∈ q.roots, ‖β - ((ξ : ℝ) : ℂ)‖ < 1 / 2 → β = α := by
    intro β hβ hd
    obtain ⟨i, rfl⟩ := hmem β hβ
    have hi : i = j₀ := by
      by_contra hne
      have h1 : 1 ≤ ‖((testPoint ξ i : ℝ) : ℂ) - ((testPoint ξ j₀ : ℝ) : ℂ)‖ :=
        one_le_norm_testPoint_sub ξ hne
      have h2 : ‖((testPoint ξ i : ℝ) : ℂ) - ((testPoint ξ j₀ : ℝ) : ℂ)‖ ≤
          ‖((testPoint ξ i : ℝ) : ℂ) - f i‖ + ‖f i - ((testPoint ξ j₀ : ℝ) : ℂ)‖ := by
        have : ((testPoint ξ i : ℝ) : ℂ) - ((testPoint ξ j₀ : ℝ) : ℂ) =
            (((testPoint ξ i : ℝ) : ℂ) - f i) + (f i - ((testPoint ξ j₀ : ℝ) : ℂ)) := by ring
        rw [this]
        exact norm_add_le _ _
      have h3 := hfs i
      have h4 : ‖f i - ((testPoint ξ j₀ : ℝ) : ℂ)‖ < 1 / 2 := by rw [hs₀]; exact hd
      have h5 : ‖((testPoint ξ i : ℝ) : ℂ) - f i‖ < 1 / 2 := by rw [norm_sub_rev]; exact h3
      linarith
    rw [hi, hαdef]
  -- the root near ξ is real
  have hαroot : α ∈ q.roots := hf j₀
  have hαd : ‖α - ((ξ : ℝ) : ℂ)‖ < 1 / 2 := by
    have := hfs j₀
    rwa [hs₀] at this
  have hconj : (starRingEnd ℂ) α = α := by
    refine hunique _ (conj_mem_roots_map P hαroot) ?_
    have h1 : (starRingEnd ℂ) α - ((ξ : ℝ) : ℂ) = (starRingEnd ℂ) (α - ((ξ : ℝ) : ℂ)) := by
      simp
    rw [h1, RCLike.norm_conj]
    exact hαd
  have hαre : ((α.re : ℝ) : ℂ) = α := Complex.conj_eq_iff_re.1 hconj
  set a : ℝ := α.re with hadef
  refine ⟨a, ?_, ?_⟩
  · have hz : eval α q = 0 := (isRoot_of_mem_roots hαroot)
    have : ‖eval ((a : ℝ) : ℂ) q‖ = 0 := by rw [hαre, hz, norm_zero]
    rw [norm_eval_map_complex P a] at this
    exact abs_eq_zero.1 this
  · -- the other roots are far from ξ
    have hfar : ∀ β ∈ q.roots, β ≠ α → 1 ≤ ‖((ξ : ℝ) : ℂ) - β‖ := by
      intro β hβ hne
      obtain ⟨i, rfl⟩ := hmem β hβ
      have hi : i ≠ j₀ := fun hh ↦ hne (by rw [hh, hαdef])
      have hine : ((i : ℕ)) ≠ 0 := by
        intro hzero
        apply hi
        apply Fin.ext
        rw [hzero, hj₀]
      have h2 : (2 : ℝ) ≤ ‖((ξ : ℝ) : ℂ) - ((testPoint ξ i : ℝ) : ℂ)‖ := by
        have hcast : ((ξ : ℝ) : ℂ) - ((testPoint ξ i : ℝ) : ℂ) =
            ((ξ - testPoint ξ i : ℝ) : ℂ) := by push_cast; ring
        rw [hcast, Complex.norm_real, Real.norm_eq_abs]
        exact two_le_abs_sub_testPoint ξ hine
      have h3 : ‖((ξ : ℝ) : ℂ) - ((testPoint ξ i : ℝ) : ℂ)‖ ≤
          ‖((ξ : ℝ) : ℂ) - f i‖ + ‖f i - ((testPoint ξ i : ℝ) : ℂ)‖ := by
        have hsp : ((ξ : ℝ) : ℂ) - ((testPoint ξ i : ℝ) : ℂ) =
            (((ξ : ℝ) : ℂ) - f i) + (f i - ((testPoint ξ i : ℝ) : ℂ)) := by ring
        rw [hsp]
        exact norm_add_le _ _
      have h4 := hfs i
      linarith
    have hval := norm_leadingCoeff_mul_pow_mul_le_norm_eval (p := q) (x := ((ξ : ℝ) : ℂ))
      (α := α) (c := 1) zero_le_one le_rfl hαroot hnd hfar
    rw [one_pow, mul_one, norm_eval_map_complex P ξ] at hval
    -- the leading coefficient carries the height
    have hbound : ∀ β ∈ q.roots, ‖β‖ ≤ B + 1 := by
      intro β hβ
      obtain ⟨i, rfl⟩ := hmem β hβ
      have h1 := norm_sub_norm_le (f i) ((testPoint ξ i : ℝ) : ℂ)
      have h2 : ‖((testPoint ξ i : ℝ) : ℂ)‖ ≤ B := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact le_trans (abs_testPoint_le ξ i) hB
      have h3 := hfs i
      linarith
    have hMle : q.mahlerMeasure ≤ ‖q.leadingCoeff‖ * (B + 1) ^ q.natDegree :=
      mahlerMeasure_le_leadingCoeff_mul_pow (by linarith) hbound
    have hMle' : q.mahlerMeasure ≤ ‖q.leadingCoeff‖ * (B + 1) ^ n := by
      refine hMle.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      exact pow_le_pow_right₀ (by linarith) (by rw [hqdeg]; exact hdeg)
    have hsup3 : P.supNorm ≤ (2 * B + 2) ^ n * ‖q.leadingCoeff‖ := by
      have h1 : (2 : ℝ) ^ n * q.mahlerMeasure ≤ 2 ^ n * (‖q.leadingCoeff‖ * (B + 1) ^ n) :=
        mul_le_mul_of_nonneg_left hMle' (by positivity)
      have h2 : (2 : ℝ) ^ n * (‖q.leadingCoeff‖ * (B + 1) ^ n) =
          (2 * B + 2) ^ n * ‖q.leadingCoeff‖ := by
        rw [show (2 * B + 2 : ℝ) = 2 * (B + 1) by ring, mul_pow]
        ring
      linarith [hsup2]
    have hdist : |ξ - a| = ‖((ξ : ℝ) : ℂ) - α‖ := by
      rw [← hαre]
      have : ((ξ : ℝ) : ℂ) - ((a : ℝ) : ℂ) = ((ξ - a : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs]
    rw [hdist]
    calc ‖((ξ : ℝ) : ℂ) - α‖ * P.supNorm
        ≤ ‖((ξ : ℝ) : ℂ) - α‖ * ((2 * B + 2) ^ n * ‖q.leadingCoeff‖) :=
          mul_le_mul_of_nonneg_left hsup3 (norm_nonneg _)
      _ = (2 * B + 2) ^ n * (‖q.leadingCoeff‖ * ‖((ξ : ℝ) : ℂ) - α‖) := by ring
      _ ≤ (2 * B + 2) ^ n * |aeval ξ P| := by
          refine mul_le_mul_of_nonneg_left hval (by positivity)

end Real
