/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Stephan2026a.Problems

-- Used only inside proofs.
import DiophantineApproximation.DoublingSequences
import Mathlib.Analysis.Complex.ExponentialBounds
import Stephan2026a.QuantitativeLines
import Stephan2026a.QuantitativePlaneStep
import Stephan2026a.QuantitativeViolators

/-!
# Problem 5.2: `p_T(k) > C k (log k)^η` infinitely often, for every `η < 1/4`

**Problem 5.2 is solved**, along the route of Bugeaud–Evertse 2008, Theorem 2.1. Suppose
`p_T(k) ≤ c k (log k)^u` for all large `k`, with `0 ≤ u < 1/4`, and pick `u < v < 1/4`.

* The complexity bound gives a doubling sequence of repetitions at pairs `(r_n + 2, τ_n + 2)` of
  length `τ_n (log τ_n)^{-v}` (`SteeringWord.exists_violators_of_complexity_le`), hence kernel
  violators `|ε_c - ε_a| ≤ (3^c)^{-ε}` for `N ≤ n < 2N` with `ε = (log τ_{2N})^{-v} / 6`
  (`SteeringWord.abs_eps_sub_le_rpow`).
* The pairs with a large gap `s > ε c / 4` have their kernel points in `K ε⁻⁴ (1 + log ε⁻¹)²`
  planes (`SteeringWord.exists_planes_of_violators`), each carrying at most `12 (1 + log ε⁻¹)` of
  them (`SteeringWord.card_mem_plane_le`).
* The pairs with a small gap have their line points in `K ε⁻³ (1 + log ε⁻¹)²` lines
  (`SteeringWord.exists_lines_of_violators`), each carrying at most three of them
  (`SteeringWord.card_mem_line_le`).

So `N ≤ K' ε⁻⁴ (1 + log ε⁻¹)³`, while `ε⁻¹ = O(N^{v + o(1)})` and `4 v < 1` make the right side
`o(N)` (`Real.eventually_doubling_thresholds` with `(p, q) = (4, 3)`): a contradiction.

The exponent `1/4` is the Evertse–Ferretti count `δ⁻³` of the three-variable step times the
`k ≈ 2/ε` classes of the gap; the coefficient-free gap principles of the plane step cost only a
logarithm. Bugeaud–Evertse's own exponent for algebraic numbers is `1/11` (`1/7` with the same
count, `BugeaudEvertse2008/Theorem21.lean`): their per-plane step costs a second `ε⁻³`. The same
split of the gap brings them to `1/4` as well (`BugeaudEvertse2008/Additions/`), with Liouville's
inequality in place of the integer identities used here.

## Main results

* `SteeringWord.frequently_lt_complexity`: for every `η < 1/4` and `C`,
  `p_T(k) > C k (log k)^η` for infinitely many `k`.
* `SteeringWord.quantitativeSuperlinear`: **Problem 5.2**, with `δ = 1/8`.

## References

R. Stephan, *Superlinear complexity of the `(3/2)^n` steering word*, arXiv:2607.11648, Problem 5.2;
Y. Bugeaud, J.-H. Evertse, *On two notions of complexity of algebraic numbers*, Acta Arith.
**133** (2008), 221–250, Theorem 2.1 and §7.
-/

@[expose] public section

open Filter Finset Real Function

namespace SteeringWord

/-- **Problem 5.2, for every `η < 1/4`.** For every `η < 1/4` and every `C`, the complexity of
the steering word exceeds `C k (log k)^η` for infinitely many `k`. -/
theorem frequently_lt_complexity {η : ℝ} (hη : η < 1 / 4) (C : ℝ) :
    ∃ᶠ k : ℕ in atTop, C * k * log k ^ η < complexity t k := by
  classical
  by_contra h
  rw [not_frequently] at h
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp h
  -- `p(k) ≤ c k (log k)^u` with `c = max C 1`, `u = max η 0`
  set u := max η 0 with hudef
  set c := max C 1 with hcdef
  have hu : 0 ≤ u := le_max_right _ _
  have hu4 : u < 1 / 4 := max_lt hη (by norm_num)
  have hp : ∀ k ≥ max n₀ 3, (complexity t k : ℝ) ≤ c * k * log k ^ u := by
    intro k hk
    have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast (le_max_right _ _).trans hk
    have hlog : 1 ≤ log k := by
      rw [le_log_iff_exp_le (by linarith)]
      have := exp_one_lt_d9
      linarith
    have h1 := not_lt.mp (hn₀ k ((le_max_left _ _).trans hk))
    have h2 : 0 ≤ (k : ℝ) * log k ^ η := by positivity
    calc (complexity t k : ℝ) ≤ C * k * log k ^ η := h1
      _ = C * ((k : ℝ) * log k ^ η) := by ring
      _ ≤ c * ((k : ℝ) * log k ^ η) := by gcongr; exact le_max_left _ _
      _ ≤ c * ((k : ℝ) * log k ^ u) := by
          gcongr
          exact le_max_left _ _
      _ = c * k * log k ^ u := by ring
  -- `u < v < 1/4`
  set v := (u + 1 / 4) / 2 with hvdef
  have huv : u < v := by rw [hvdef]; linarith
  have hv : 0 < v := by linarith
  have hv4 : ((4 : ℕ) : ℝ) * v < 1 := by rw [hvdef]; push_cast; linarith
  obtain ⟨Cg, r, τ, hrτ, hgap, hbd, hrep⟩ := exists_violators_of_complexity_le hu huv (max n₀ 3) hp
  obtain ⟨K₂, hK₂, hT⟩ := exists_planes_of_violators
  obtain ⟨K₄, hK₄, hL⟩ := exists_lines_of_violators
  set Kt : ℝ := 6 * (K₂ + K₄) + (12 * K₂ + 3 * K₄) * 6 ^ 4 * 216 with hKtdef
  have hKt0 : 0 < Kt := by positivity
  have hKt2 : 6 * K₂ ≤ Kt ∧ 6 * K₄ ≤ Kt ∧ (12 * K₂ + 3 * K₄) * 6 ^ 4 * 216 ≤ Kt := by
    have h0 : 0 ≤ (12 * K₂ + 3 * K₄) * 6 ^ 4 * 216 := by positivity
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  -- opaque from here on: unfolding it makes defeq checks on real arithmetic explode
  clear_value Kt
  obtain ⟨N, hN⟩ := (eventually_doubling_thresholds 4 3 (by norm_num) (by norm_num) (C := Cg) hv
    hv4 hKt0 (log_pos (by norm_num : (1 : ℝ) < 3))).exists
  obtain ⟨hε0, hε1, hεle, hthr, hcount⟩ := hN τ hgap hbd
  set ε₀ := log (τ (2 * N)) ^ (-v) with hε₀
  set ε := ε₀ / 6 with hεdef
  have hε : 0 < ε := by positivity
  have hε1' : ε ≤ 1 := by rw [hεdef]; linarith
  have hεinv : ε⁻¹ = 6 * ε₀⁻¹ := by rw [hεdef, inv_div, div_eq_mul_inv]
  have hε₀inv : 1 ≤ ε₀⁻¹ := one_le_inv₀ hε0 |>.mpr hε1
  have hlogε₀ : 0 ≤ log ε₀⁻¹ := log_nonneg hε₀inv
  obtain ⟨T, hTcard, hTtop, hTmem⟩ := hT ε hε hε1'
  obtain ⟨T', hT'card, hT'top, hT'mem⟩ := hL ε hε hε1'
  -- `N ≥ 1`, so the indices `n ≥ N` have `τ_n ≥ 3`
  have hN1 : 1 ≤ N := by
    by_contra h0
    have h0' : N = 0 := by omega
    rw [h0'] at hcount
    have : 0 ≤ Kt * ε₀⁻¹ ^ 4 * (1 + log ε₀⁻¹) ^ 3 := by positivity
    push_cast at hcount
    linarith
  have hτ3 : ∀ n, 1 ≤ n → 3 ≤ τ n := fun n hn ↦ by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have := hgap k
    have := hrτ k
    omega
  -- the pairs `(r_n + 2, τ_n + 2)`, `N ≤ n < 2N`, are kernel violators with exponent `ε`
  set I := Ico N (2 * N) with hI
  have happ : ∀ n ∈ I, |(eps (τ n + 2) : ℝ) - eps (r n + 2)| ≤ ((3 : ℝ) ^ (τ n + 2)) ^ (-ε) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := mem_Ico.mp hn
    refine abs_eps_sub_le_rpow (hrep n) ?_
    have h3 : (3 : ℝ) ≤ τ n := by exact_mod_cast hτ3 n (by omega)
    have hle : ε₀ * τ n ≤ τ n * log (τ n) ^ (-v) := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (hεle n hn1 hn2.le) (by positivity)
    have hceil := Nat.le_ceil ((τ n : ℝ) * log (τ n) ^ (-v))
    push_cast
    rw [hεdef]
    nlinarith
  have hthr' : ∀ n ∈ I, ∀ K : ℝ, 0 ≤ K → 6 * K ≤ Kt → K * ε⁻¹ ≤ ((τ n + 2 : ℕ) : ℝ) * log 3 := by
    intro n hn K hK hKK
    have h := hthr n (mem_Ico.mp hn).1
    have hl3 : 0 < log 3 := log_pos (by norm_num)
    rw [hεinv]
    push_cast
    have : 0 ≤ ε₀⁻¹ := by positivity
    nlinarith
  -- split by the size of the gap
  set big := I.filter fun n ↦ ε / 4 * ((τ n : ℝ) + 2) < (τ n : ℝ) - r n with hbig
  set small := I.filter fun n ↦ ¬ ε / 4 * ((τ n : ℝ) + 2) < (τ n : ℝ) - r n with hsmall
  have hsplit : (N : ℝ) = #big + #small := by
    have h := card_filter_add_card_filter_not (s := I)
      fun n ↦ ε / 4 * ((τ n : ℝ) + 2) < (τ n : ℝ) - r n
    rw [Nat.card_Ico, show 2 * N - N = N by omega] at h
    rw [hbig, hsmall]
    exact_mod_cast h.symm
  -- the large gaps: few planes, few points on each
  have hφ : ∀ n ∈ big, ∃ U ∈ T, (fun i ↦ (kernelPoint (r n + 2) (τ n + 2) i : ℚ)) ∈ U := by
    intro n hn
    have hnI := (mem_filter.mp hn).1
    have := hrτ n
    exact hTmem _ _ (by omega) (by omega) (happ n hnI)
      (hthr' n hnI K₂ hK₂.le hKt2.1)
  choose! φ hφT hφU using hφ
  have hbigc : (#big : ℝ) ≤ #T * (12 * (1 + log ε⁻¹)) := by
    have hsum := card_eq_sum_card_fiberwise (s := big) (t := T) (f := φ) hφT
    have hfib : ∀ U ∈ T, (#(big.filter fun n ↦ φ n = U) : ℝ) ≤ 12 * (1 + log ε⁻¹) :=
      fun U hU ↦ card_mem_plane_le (hTtop U hU) hgap hrτ hε hε1' _ fun n hn ↦ by
        obtain ⟨hnb, hφn⟩ := mem_filter.mp hn
        exact ⟨hφn ▸ hφU n hnb, (mem_filter.mp hnb).2⟩
    calc (#big : ℝ) = ∑ U ∈ T, (#(big.filter fun n ↦ φ n = U) : ℝ) := by exact_mod_cast hsum
      _ ≤ ∑ _U ∈ T, 12 * (1 + log ε⁻¹) := sum_le_sum hfib
      _ = #T * (12 * (1 + log ε⁻¹)) := by rw [sum_const, nsmul_eq_mul]
  -- the small gaps: few lines, at most three points on each
  have hψ : ∀ n ∈ small, ∃ U ∈ T', (fun i ↦ (linePoint (r n + 2) (τ n + 2) i : ℚ)) ∈ U := by
    intro n hn
    obtain ⟨hnI, hns⟩ := mem_filter.mp hn
    have := hrτ n
    refine hT'mem _ _ (by omega) (by omega) (happ n hnI) ?_
      (hthr' n hnI K₄ hK₄.le hKt2.2.1)
    have hs : ((τ n + 2 - (r n + 2) : ℕ) : ℝ) = (τ n : ℝ) - r n := by
      rw [show τ n + 2 - (r n + 2) = τ n - r n by omega, Nat.cast_sub (hrτ n).le]
    rw [hs]
    push_cast
    linarith [not_lt.mp hns]
  choose! ψ hψT hψU using hψ
  have hsmallc : (#small : ℝ) ≤ #T' * 3 := by
    have hsum := card_eq_sum_card_fiberwise (s := small) (t := T') (f := ψ) hψT
    have hfib : ∀ U ∈ T', (#(small.filter fun n ↦ ψ n = U) : ℝ) ≤ 3 :=
      fun U hU ↦ card_mem_line_le (hT'top U hU) hgap hrτ _ fun n hn ↦ by
        obtain ⟨hns, hψn⟩ := mem_filter.mp hn
        exact hψn ▸ hψU n hns
    calc (#small : ℝ) = ∑ U ∈ T', (#(small.filter fun n ↦ ψ n = U) : ℝ) := by
          exact_mod_cast hsum
      _ ≤ ∑ _U ∈ T', (3 : ℝ) := sum_le_sum hfib
      _ = #T' * 3 := by rw [sum_const, nsmul_eq_mul]
  -- `N ≤ Kt ε₀⁻⁴ (1 + log ε₀⁻¹)³ < N`
  have hL1 : 0 ≤ log ε⁻¹ := log_nonneg (one_le_inv₀ hε |>.mpr hε1')
  have hLε : 1 + log ε⁻¹ ≤ 6 * (1 + log ε₀⁻¹) := by
    rw [hεinv, log_mul (by norm_num) (by positivity)]
    have : log 6 ≤ 5 := by
      have := log_le_sub_one_of_pos (show (0 : ℝ) < 6 by norm_num)
      linarith
    linarith
  have hεi1 : 1 ≤ ε⁻¹ := one_le_inv₀ hε |>.mpr hε1'
  set X := ε⁻¹ with hX
  set Λ := 1 + log ε⁻¹ with hΛ
  have hΛ1 : 1 ≤ Λ := by rw [hΛ]; linarith
  clear_value X Λ
  have hfin : (N : ℝ) ≤ (12 * K₂ + 3 * K₄) * X ^ 4 * Λ ^ 3 := by
    have hX3 : X ^ 3 ≤ X ^ 4 := pow_le_pow_right₀ hεi1 (by norm_num)
    have hΛ2 : Λ ^ 2 ≤ Λ ^ 3 := pow_le_pow_right₀ hΛ1 (by norm_num)
    have hb : (#big : ℝ) ≤ 12 * K₂ * X ^ 4 * Λ ^ 3 := by
      calc (#big : ℝ) ≤ #T * (12 * Λ) := hbigc
        _ ≤ K₂ * X ^ 4 * Λ ^ 2 * (12 * Λ) := by gcongr
        _ = 12 * K₂ * X ^ 4 * Λ ^ 3 := by ring
    have hs : (#small : ℝ) ≤ 3 * K₄ * X ^ 4 * Λ ^ 3 := by
      calc (#small : ℝ) ≤ #T' * 3 := hsmallc
        _ ≤ K₄ * X ^ 3 * Λ ^ 2 * 3 := by gcongr
        _ ≤ K₄ * X ^ 4 * Λ ^ 3 * 3 := by gcongr
        _ = 3 * K₄ * X ^ 4 * Λ ^ 3 := by ring
    rw [hsplit]
    linarith
  have hfin' : (N : ℝ) ≤ Kt * ε₀⁻¹ ^ 4 * (1 + log ε₀⁻¹) ^ 3 := by
    have hX' : X ^ 4 = 6 ^ 4 * ε₀⁻¹ ^ 4 := by rw [hεinv, mul_pow]
    have hΛ' : Λ ^ 3 ≤ 216 * (1 + log ε₀⁻¹) ^ 3 := by
      calc Λ ^ 3 ≤ (6 * (1 + log ε₀⁻¹)) ^ 3 := pow_le_pow_left₀ (by linarith) hLε 3
        _ = 216 * (1 + log ε₀⁻¹) ^ 3 := by ring
    have h0 : 0 ≤ (12 * K₂ + 3 * K₄) * 6 ^ 4 * ε₀⁻¹ ^ 4 := by positivity
    have h1 : 0 ≤ ε₀⁻¹ ^ 4 * (1 + log ε₀⁻¹) ^ 3 := by positivity
    calc (N : ℝ) ≤ (12 * K₂ + 3 * K₄) * X ^ 4 * Λ ^ 3 := hfin
      _ = (12 * K₂ + 3 * K₄) * 6 ^ 4 * ε₀⁻¹ ^ 4 * Λ ^ 3 := by rw [hX']; ring
      _ ≤ (12 * K₂ + 3 * K₄) * 6 ^ 4 * ε₀⁻¹ ^ 4 * (216 * (1 + log ε₀⁻¹) ^ 3) := by gcongr
      _ = (12 * K₂ + 3 * K₄) * 6 ^ 4 * 216 * (ε₀⁻¹ ^ 4 * (1 + log ε₀⁻¹) ^ 3) := by ring
      _ ≤ Kt * (ε₀⁻¹ ^ 4 * (1 + log ε₀⁻¹) ^ 3) :=
          mul_le_mul_of_nonneg_right hKt2.2.2 h1
      _ = Kt * ε₀⁻¹ ^ 4 * (1 + log ε₀⁻¹) ^ 3 := by ring
  linarith

/-- **Problem 5.2 is solved**: `p_T(k) ≥ k (log k)^{1/8}` for infinitely many `k`. Every exponent
`η < 1/4` works (`SteeringWord.frequently_lt_complexity`). -/
theorem quantitativeSuperlinear : QuantitativeSuperlinear :=
  ⟨1 / 8, by norm_num, (frequently_lt_complexity (by norm_num : (1 / 8 : ℝ) < 1 / 4) 1).mono
    fun k hk ↦ by rw [one_mul] at hk; exact hk.le⟩

end SteeringWord
