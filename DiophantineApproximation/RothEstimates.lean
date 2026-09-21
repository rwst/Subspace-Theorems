/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.Interval.Finset.Fin

/-!
# The three elementary estimates behind Roth's lemma

Roth's lemma is an induction whose step is one inequality between real numbers, and the
inequality has three separable parts.

*The degrees sum to twice the largest.* With `2 * d j ≤ d (j + 1)` the degrees at least double,
so `∑ j, d j ≤ 2 * d (last)` — which is why the constant `4 m d` of the hypothesis can absorb
`2 (∑ j, d j) log 2`.

*The index of the determinant is quadratic in the index of `P`.* Summing
`max 0 (x - i / e)` over `i < p` with `p ≤ e + 1` gives at least `p * min (x/2) (x²/4)`: for
large `x` all `p` terms survive and the sum is about `p x`, for small `x` only about `x e` of
them do and the sum is about `x² e / 2`. The *square* is the whole reason Roth's lemma has the
exponent `2 ^ (1 - m)`.

*The two ends meet.* `min (x/2) (x²/4) ≤ (c + 1) θ²` with `x > (2 m + 3.5) θ` and `θ < 1/2` is a
contradiction as soon as `c ≤ 2 m + 2`, which is what the constant `2 m` of the conclusion is
chosen for.

## Main results

* `Fin.sum_le_two_mul_last`: the geometric sum of the degrees.
* `Real.le_sum_max_sub_div`: the quadratic lower bound.
* `Real.roth_numeric`: the closing contradiction.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Lemma 6.3.7.

This is part of Layer 2.7 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

namespace Fin

/-- **A sequence that at least doubles sums to at most twice its last term.** -/
theorem sum_le_two_mul_last : ∀ {n : ℕ} (D : Fin (n + 1) → ℝ), (∀ j, 0 ≤ D j) →
    (∀ j : Fin n, 2 * D j.castSucc ≤ D j.succ) → ∑ j, D j ≤ 2 * D (Fin.last n) := by
  intro n
  induction n with
  | zero =>
      intro D hnn _
      rw [Fin.sum_univ_one]
      have h0 : (0 : Fin 1) = Fin.last 0 := rfl
      rw [h0]
      linarith [hnn (Fin.last 0)]
  | succ n ih =>
      intro D hnn h
      rw [Fin.sum_univ_castSucc]
      have hIH := ih (fun j ↦ D j.castSucc) (fun j ↦ hnn _)
        (fun j ↦ by rw [← Fin.succ_castSucc]; exact h j.castSucc)
      have hlast := h (Fin.last n)
      rw [Fin.succ_last] at hlast
      linarith [hnn (Fin.last (n + 1))]

end Fin

namespace Real

/-- The sum of the first `n` natural numbers, as a real number. -/
theorem sum_range_cast_id (n : ℕ) : ∑ i ∈ Finset.range n, (i : ℝ) = n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- The sum of `max 0 (x - i / e)` over a prefix, from below. -/
theorem le_sum_max_sub_div_aux {p e n : ℕ} (hn : n ≤ p) {x : ℝ} :
    (n : ℝ) * x - (n : ℝ) * ((n : ℝ) - 1) / 2 / e
      ≤ ∑ i ∈ Finset.range p, max 0 (x - (i : ℕ) / (e : ℝ)) := by
  have hstep : ∑ i ∈ Finset.range n, (x - (i : ℕ) / (e : ℝ))
      ≤ ∑ i ∈ Finset.range p, max 0 (x - (i : ℕ) / (e : ℝ)) := by
    refine le_trans (Finset.sum_le_sum fun i _ ↦ le_max_right 0 _) ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun i hi ↦ Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hn))
      fun i _ _ ↦ le_max_left _ _
  refine le_trans (le_of_eq ?_) hstep
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  simp only [div_eq_mul_inv, ← Finset.sum_mul, sum_range_cast_id]

/-- **The quadratic lower bound.** -/
theorem le_sum_max_sub_div {p e : ℕ} (hp : 0 < p) (hple : p ≤ e + 1) (he : 1 ≤ e) {x : ℝ}
    (hx : 0 ≤ x) :
    (p : ℝ) * min (x / 2) (x ^ 2 / 4)
      ≤ ∑ i ∈ Finset.range p, max 0 (x - (i : ℕ) / (e : ℝ)) := by
  have hep : (0 : ℝ) < e := by exact_mod_cast he
  have hpp : (0 : ℝ) < p := by exact_mod_cast hp
  have hple' : (p : ℝ) ≤ (e : ℝ) + 1 := by exact_mod_cast hple
  have he' : (1 : ℝ) ≤ e := by exact_mod_cast he
  rcases le_or_gt ((p : ℝ) - 1) (x * e) with hcase | hcase
  · refine le_trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hpp.le) ?_
    refine le_trans ?_ (le_sum_max_sub_div_aux (le_refl p) (e := e) (x := x))
    have hd1 : ((p : ℝ) - 1) / e ≤ x := (div_le_iff₀ hep).mpr hcase
    have hd2 : (p : ℝ) * ((p : ℝ) - 1) / 2 / e = (p : ℝ) * (((p : ℝ) - 1) / e) / 2 := by
      field_simp
    rw [hd2]
    have := mul_le_mul_of_nonneg_left hd1 hpp.le
    linarith
  · set N : ℕ := ⌊x * e⌋₊ with hN
    have hfl : (N : ℝ) ≤ x * e := Nat.floor_le (by positivity)
    have hfl' : x * e < (N : ℝ) + 1 := Nat.lt_floor_add_one _
    have hNp : N + 1 ≤ p := by
      have h1 : (N : ℝ) + 1 < (p : ℝ) := by linarith
      have h2 : N + 1 < p := by exact_mod_cast h1
      omega
    have hkey := le_sum_max_sub_div_aux (n := N + 1) (e := e) hNp (x := x)
    have hkey' : ((N : ℝ) + 1) * x - ((N : ℝ) + 1) * (N : ℝ) / 2 / e
        ≤ ∑ i ∈ Finset.range p, max 0 (x - (i : ℕ) / (e : ℝ)) := by
      refine le_trans (le_of_eq ?_) hkey
      push_cast
      ring
    refine le_trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hpp.le) (le_trans ?_ hkey')
    have h2e : (p : ℝ) ≤ 2 * e := by linarith
    have hNe : (N : ℝ) / e ≤ x := (div_le_iff₀ hep).mpr hfl
    have hA : ((N : ℝ) + 1) * (N : ℝ) / 2 / e = ((N : ℝ) + 1) * ((N : ℝ) / e) / 2 := by
      field_simp
    have hstep1 : ((N : ℝ) + 1) * x / 2
        ≤ ((N : ℝ) + 1) * x - ((N : ℝ) + 1) * (N : ℝ) / 2 / e := by
      rw [hA]
      have := mul_le_mul_of_nonneg_left hNe (by positivity : (0 : ℝ) ≤ (N : ℝ) + 1)
      linarith
    have hstep2 : x * e * x / 2 ≤ ((N : ℝ) + 1) * x / 2 := by
      have := mul_le_mul_of_nonneg_right hfl'.le hx
      linarith
    have hstep3 : (p : ℝ) * (x ^ 2 / 4) ≤ x * e * x / 2 := by
      nlinarith [mul_le_mul_of_nonneg_right h2e (sq_nonneg x)]
    linarith

/-- **The closing contradiction of the inductive step of Roth's lemma.** -/
theorem roth_numeric {mm θ t x s c : ℝ} (hmm : 0 ≤ mm) (hθ0 : 0 < θ) (hθ : θ < 1 / 2)
    (hs : s ≤ θ ^ 2) (hx : x = t - s) (hc : c ≤ 2 * mm + 2)
    (ht : 2 * (mm + 2) * θ < t) (hmin : min (x / 2) (x ^ 2 / 4) ≤ c * θ ^ 2 + s) : False := by
  have hθ2 : θ ^ 2 < θ / 2 := by nlinarith
  have hxlb : (2 * mm + 3.5) * θ < x := by nlinarith
  have hub : c * θ ^ 2 + s ≤ (2 * mm + 3) * θ ^ 2 := by nlinarith
  have hx0 : 0 < x := by nlinarith
  rcases min_cases (x / 2) (x ^ 2 / 4) with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h] at hmin
    have hgap : (0 : ℝ) < (2 * mm + 3) * (θ / 2 - θ ^ 2) :=
      mul_pos (by linarith) (by linarith)
    nlinarith [hgap]
  · rw [h] at hmin
    have hpos : (0 : ℝ) < (2 * mm + 3.5) * θ := mul_pos (by linarith) hθ0
    have hsq : ((2 * mm + 3.5) * θ) ^ 2 < x ^ 2 := by
      rw [sq, sq]
      exact mul_self_lt_mul_self hpos.le hxlb
    have hfin : (2 * mm + 3) * θ ^ 2 * 4 ≤ ((2 * mm + 3.5) * θ) ^ 2 := by
      nlinarith [sq_nonneg θ, mul_nonneg (mul_nonneg hmm hmm) (sq_nonneg θ),
        mul_nonneg hmm (sq_nonneg θ)]
    linarith

end Real
