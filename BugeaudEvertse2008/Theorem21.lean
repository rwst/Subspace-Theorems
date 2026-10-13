/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import BugeaudEvertse2008.Repetitions

-- Used only inside proofs.
import BugeaudEvertse2008.PlaneStep
import BugeaudEvertse2008.Thresholds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Bugeaud–Evertse 2008, Theorem 2.1, with `1/7`

**The complexity of an algebraic irrational number is not `O(n (log n)^η)` for `η < 1/7`**: if
`ξ = ofDigits a` is real algebraic irrational, then `p(n) > C n (log n)^η` for infinitely many `n`,
for every `C` (`Real.frequently_lt_complexity`). BE08 prove this for `η < 1/11`.

Suppose instead `p(n) ≤ c n (log n)^u` for large `n`, `0 ≤ u < 1/7`, and pick `u < v < 1/7`.

* Lemma 6.1 (`Real.exists_approx_of_complexity_le`) gives the points
  `x_n = (b^{t_n}, b^{r_n}, p_n)` with
  `|b^{t_n} ξ - b^{r_n} ξ - p_n| ≤ (b^{t_n})^{-(log t_n)^{-v}}`.
* For large `N` and `ε = (log t_{2N})^{-v}` (`Real.eventually_thresholds`), the `N` points
  `x_n`, `N ≤ n < 2N`, satisfy the approximation with exponent `ε` and lie above the threshold of
  the three-variable step.
* So they lie in `K₂ ε⁻⁴ (1 + log ε⁻¹)²` planes (`Real.exists_planes_of_approx`), each holding
  at most `K₃ ε⁻³ (1 + log ε⁻¹)²` of them (`Real.card_mem_plane_le`).
* Hence `N ≤ K₂ K₃ ε⁻⁷ (1 + log ε⁻¹)⁴`, which is `< N` for large `N` since `7 v < 1`.

The exponent is `1/7` rather than BE08's `1/11` because Evertse–Ferretti 2013's count `δ⁻³` (BE.0)
replaces Evertse–Schlickewei 2002's `δ⁻⁷` in the three-variable step: `7 = 1 + 3 + 3` (classes,
planes per class, points per plane) instead of `11 = 1 + 7 + 3`.

## Main results

* `Real.frequently_lt_complexity`: **Theorem 2.1** with `η < 1/7`.

## References

Y. Bugeaud, J.-H. Evertse, *On two notions of complexity of algebraic numbers*, Acta Arith.
**133** (2008), 221–250, Theorem 2.1 and §7.
-/

@[expose] public section

open Filter Finset

namespace Real

variable {b : ℕ}

/-- **Bugeaud–Evertse 2008, Theorem 2.1, with `1/7` in place of `1/11`.** If the base-`b` digits
`a` of a real algebraic irrational number are given, then for every `η < 1/7` and every `C` the
complexity exceeds `C n (log n)^η` for infinitely many `n`. -/
theorem frequently_lt_complexity (hb : 2 ≤ b) {a : ℕ → Fin b} (hirr : Irrational (ofDigits a))
    (halg : IsAlgebraic ℚ (ofDigits a)) {η : ℝ} (hη : η < 1 / 7) (C : ℝ) :
    ∃ᶠ n : ℕ in atTop, C * n * log n ^ η < Function.complexity a n := by
  classical
  by_contra h
  rw [not_frequently] at h
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp h
  -- `p(n) ≤ c n (log n)^u` with `c = max C 1`, `u = max η 0`
  set u := max η 0 with hudef
  set c := max C 1 with hcdef
  have hu : 0 ≤ u := le_max_right _ _
  have hu7 : u < 1 / 7 := max_lt hη (by norm_num)
  have hp : ∀ n ≥ max n₀ 3, (Function.complexity a n : ℝ) ≤ c * n * log n ^ u := by
    intro n hn
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast (le_max_right _ _).trans hn
    have hlog : 1 ≤ log n := by
      rw [le_log_iff_exp_le (by linarith)]
      have := exp_one_lt_d9
      linarith
    have h1 := not_lt.mp (hn₀ n ((le_max_left _ _).trans hn))
    have h2 : 0 ≤ (n : ℝ) * log n ^ η := by positivity
    calc (Function.complexity a n : ℝ) ≤ C * n * log n ^ η := h1
      _ = C * ((n : ℝ) * log n ^ η) := by ring
      _ ≤ c * ((n : ℝ) * log n ^ η) := by gcongr; exact le_max_left _ _
      _ ≤ c * ((n : ℝ) * log n ^ u) := by
          gcongr
          exact le_max_left _ _
      _ = c * n * log n ^ u := by ring
  -- `u < v < 1/7`
  set v := (u + 1 / 7) / 2 with hvdef
  have huv : u < v := by rw [hvdef]; linarith
  have hv : 0 < v := by linarith
  have hv7 : 7 * v < 1 := by rw [hvdef]; linarith
  set ξ := ofDigits a with hξ
  obtain ⟨Cg, r, t, p, hrt, hgap, hbd, hdvd, hpb, happ⟩ :=
    exists_approx_of_complexity_le hb hu huv (max n₀ 3) hp
  obtain ⟨K₂, hK₂, hT⟩ := exists_planes_of_approx hb halg
  obtain ⟨K₃, hK₃, hPl⟩ := card_mem_plane_le hb halg hirr
  have hbR : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  obtain ⟨N, hN⟩ := (eventually_thresholds (C := Cg) hv hv7 (K := K₂ + K₂ * K₃)
    (by positivity) (log_pos hbR)).exists
  obtain ⟨hε0, hε1, hεle, hthr, hcount⟩ := hN t hgap hbd
  set ε := log (t (2 * N)) ^ (-v) with hε
  have hεinv : 0 ≤ ε⁻¹ := by positivity
  obtain ⟨T, hTcard, hTtop, hTmem⟩ := hT ε hε0 hε1
  -- the points `x_n`, `N ≤ n < 2N`
  set I := Ico N (2 * N) with hI
  have happε : ∀ n ∈ I, |(b : ℝ) ^ t n * ξ - b ^ r n * ξ - p n| ≤ ((b : ℝ) ^ t n) ^ (-ε) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := mem_Ico.mp hn
    refine (happ n).trans (rpow_le_rpow_of_exponent_le (one_le_pow₀ hbR.le) ?_)
    exact neg_le_neg (hεle n hn1 hn2.le)
  have hφ : ∀ n ∈ I, ∃ U ∈ T, ![(b : ℚ) ^ t n, (b : ℚ) ^ r n, (p n : ℚ)] ∈ U := by
    intro n hn
    refine hTmem (r n) (t n) (p n) (hrt n) (hpb n) (happε n hn) ?_
    refine le_trans ?_ (hthr n (mem_Ico.mp hn).1)
    have : 0 ≤ K₂ * K₃ * ε⁻¹ := by positivity
    nlinarith
  choose! φ hφT hφU using hφ
  -- each plane holds few points
  set Y := ε⁻¹ ^ 3 * (1 + log ε⁻¹) ^ 2 with hY
  have hfib : ∀ U ∈ T, (#(I.filter fun n ↦ φ n = U) : ℝ) ≤ K₃ * Y := by
    intro U hU
    have := hPl ε hε0 hε1 r t p hgap U (hTtop U hU) (I.filter fun n ↦ φ n = U)
      (fun n _ ↦ hrt n) (fun n _ ↦ hdvd n) (fun n _ ↦ hpb n)
      (fun n hn ↦ happε n (mem_filter.mp hn).1)
      (fun n hn ↦ by
        obtain ⟨hn, hφn⟩ := mem_filter.mp hn
        rw [← hφn]; exact hφU n hn)
    rw [hY, ← mul_assoc]; exact this
  have hIcard : (N : ℝ) ≤ #T * (K₃ * Y) := by
    have hsum := card_eq_sum_card_fiberwise (s := I) (t := T) (f := φ) hφT
    rw [hI, Nat.card_Ico, show 2 * N - N = N by omega] at hsum
    calc (N : ℝ) = ∑ U ∈ T, (#(I.filter fun n ↦ φ n = U) : ℝ) := by exact_mod_cast hsum
      _ ≤ ∑ _U ∈ T, K₃ * Y := sum_le_sum hfib
      _ = #T * (K₃ * Y) := by rw [sum_const, nsmul_eq_mul]
  -- `N ≤ K₂ K₃ ε⁻⁷ (1 + log ε⁻¹)⁴ < N`
  have hY0 : 0 ≤ K₃ * Y := by positivity
  have hfin : (N : ℝ) ≤ (K₂ + K₂ * K₃) * ε⁻¹ ^ 7 * (1 + log ε⁻¹) ^ 4 := by
    calc (N : ℝ) ≤ #T * (K₃ * Y) := hIcard
      _ ≤ K₂ * ε⁻¹ ^ 4 * (1 + log ε⁻¹) ^ 2 * (K₃ * Y) := by gcongr
      _ = K₂ * K₃ * ε⁻¹ ^ 7 * (1 + log ε⁻¹) ^ 4 := by rw [hY]; ring
      _ ≤ (K₂ + K₂ * K₃) * ε⁻¹ ^ 7 * (1 + log ε⁻¹) ^ 4 := by
          have : 0 ≤ ε⁻¹ ^ 7 * (1 + log ε⁻¹) ^ 4 := by
            have : 0 ≤ log ε⁻¹ := log_nonneg (one_le_inv₀ hε0 |>.mpr hε1)
            positivity
          nlinarith
  linarith

end Real
