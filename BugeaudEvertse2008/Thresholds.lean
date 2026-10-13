/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- Used only inside proofs.
import BugeaudEvertse2008.Repetitions
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The thresholds (Bugeaud–Evertse 2008, §7)

The proof of Theorem 2.1 works with the points `x_n`, `N ≤ n ≤ 2N`, of Lemma 6.1 and with
`ε = (log t_{2N})^{-v}`. Lemma 6.1 (`Function.exists_repetitions_of_complexity_le`) gives
`2 t_n < t_{n+1}` and `t_n ≤ (2n + 2)^{C(n+1)}`, so `log t_{2N}` lies between `(2N - 1) log 2` and
`C (2N + 1) log (4N + 2)`. For `N` large this gives everything the counting needs
(`Real.eventually_thresholds`):

* `0 < ε ≤ 1`;
* `ε ≤ (log t_n)^{-v}` for `N ≤ n ≤ 2N`, so the approximations of Lemma 6.1 hold with exponent `ε`;
* `K ε⁻¹ ≤ t_n log b` for `n ≥ N`: the threshold of the three-variable step
  (`Real.exists_planes_of_approx`), since `ε⁻¹ = O(N²)` and `t_n ≥ 2^{n-1}`;
* `K ε⁻⁷ (1 + log ε⁻¹)⁴ < N` when `7v < 1`: the count of the planes times the count per plane
  (`Real.card_mem_plane_le`) is smaller than the number of points.

The plane step needs no threshold from here; it handles its own (`Real.card_mem_plane_le`).

## Main results

* `Real.eventually_thresholds`: the inequalities above, for all large `N`.

## References

Y. Bugeaud, J.-H. Evertse, *On two notions of complexity of algebraic numbers*, Acta Arith.
**133** (2008), 221–250, §7.
-/

@[expose] public section

open Filter

namespace Real

/-- **The thresholds of §7.** Let `0 < v`, `7 v < 1`, `K, L > 0`. For all large `N` and every
`t` with `2 t_n < t_{n+1}` and `t_n ≤ (2n + 2)^{C(n+1)}`, the number `ε = (log t_{2N})^{-v}`
satisfies `0 < ε ≤ 1`, `ε ≤ (log t_n)^{-v}` for `N ≤ n ≤ 2N`, `K ε⁻¹ ≤ t_n L` for `n ≥ N`, and
`K ε⁻⁷ (1 + log ε⁻¹)⁴ < N`. -/
theorem eventually_thresholds {C : ℕ} {v : ℝ} (hv : 0 < v) (hv7 : 7 * v < 1) {K L : ℝ}
    (hK : 0 < K) (hL : 0 < L) :
    ∀ᶠ N : ℕ in atTop, ∀ t : ℕ → ℕ, (∀ n, 2 * t n < t (n + 1)) →
      (∀ n, t n ≤ (2 * n + 2) ^ (C * (n + 1))) →
      0 < log (t (2 * N)) ^ (-v) ∧ log (t (2 * N)) ^ (-v) ≤ 1 ∧
      (∀ n, N ≤ n → n ≤ 2 * N → log (t (2 * N)) ^ (-v) ≤ log (t n) ^ (-v)) ∧
      (∀ n, N ≤ n → K * (log (t (2 * N)) ^ (-v))⁻¹ ≤ t n * L) ∧
      K * ((log (t (2 * N)) ^ (-v))⁻¹) ^ 7 * (1 + log (log (t (2 * N)) ^ (-v))⁻¹) ^ 4 < N := by
  -- the exponent `e = (1 + δ)(7v + 4δ) < 1`
  set a := 7 * v with ha
  set δ := (1 - a) / 10 with hδ
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hδ1 : δ ≤ 1 / 10 := by rw [hδ]; linarith
  set e := (1 + δ) * (a + 4 * δ) with he
  have he1 : e < 1 := by
    have : a + 10 * δ = 1 := by rw [hδ]; ring
    rw [he]; nlinarith
  have he0 : 0 ≤ e := by positivity
  set A : ℝ := 18 * (C + 1) / δ with hA
  have hA0 : 0 < A := by positivity
  set K' := K * (1 + v / δ) ^ 4 * A ^ (a + 4 * δ) with hK'
  -- eventually `K' < N^{1-e}` and `K · 18 C N² ≤ 2^N L / 2`
  have hev1 : ∀ᶠ N : ℕ in atTop, K' < (N : ℝ) ^ (1 - e) :=
    ((tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop).eventually_gt_atTop K'
  have hev2 : ∀ᶠ N : ℕ in atTop, K * (18 * C) * (N : ℝ) ^ 2 ≤ 2 ^ N * L / 2 := by
    have hc : 0 < L / (2 * (K * (18 * C) + 1)) := by positivity
    filter_upwards [(isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) 2 one_lt_two).bound hc]
      with N hN
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_pos (by positivity)] at hN
    have h0 : 0 ≤ K * (18 * C) := by positivity
    calc K * (18 * C) * (N : ℝ) ^ 2 ≤ (K * (18 * C) + 1) * (N : ℝ) ^ 2 := by
          have : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
          nlinarith
      _ ≤ (K * (18 * C) + 1) * (L / (2 * (K * (18 * C) + 1)) * 2 ^ N) := by gcongr
      _ = 2 ^ N * L / 2 := by field_simp
  filter_upwards [eventually_ge_atTop 2, hev1, hev2] with N hN h1 h2 t ht hgrow
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  -- `2^n ≤ 2 t_n`
  have hlow : ∀ n, 1 ≤ n → 2 ^ n ≤ 2 * t n := fun n hn ↦ by
    have hd := Nat.two_pow_mul_le_of_doubling ht 1 (n - 1)
    rw [Nat.add_sub_cancel' hn] at hd
    have ht1 : 1 ≤ t 1 := by have := ht 0; rw [zero_add] at this; omega
    calc 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ', Nat.sub_add_cancel hn]
      _ ≤ 2 * (2 ^ (n - 1) * t 1) := Nat.mul_le_mul_left 2 (Nat.le_mul_of_pos_right _ ht1)
      _ ≤ 2 * t n := Nat.mul_le_mul_left 2 hd
  have hlowR : ∀ n, 1 ≤ n → (2 : ℝ) ^ n ≤ 2 * t n := fun n hn ↦ by exact_mod_cast hlow n hn
  have htm : Monotone t := (strictMono_nat_of_lt_succ fun n ↦ by have := ht n; omega).monotone
  have ht2 : ∀ n, 2 ≤ n → (1 : ℝ) < t n := fun n hn ↦ by
    have h4 : (4 : ℝ) ≤ 2 ^ n := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
    have := hlowR n (by omega)
    linarith
  set X := log (t (2 * N)) with hXdef
  have hX1 : 1 ≤ X := by
    have h16 : (16 : ℝ) ≤ 2 ^ (2 * N) := by
      calc (16 : ℝ) = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ (2 * N) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h8 : (8 : ℝ) ≤ t (2 * N) := by have := hlowR (2 * N) (by omega); linarith
    rw [hXdef, le_log_iff_exp_le (by linarith)]
    have := exp_one_lt_d9
    linarith
  have hX0 : 0 < X := by linarith
  have hεinv : (X ^ (-v))⁻¹ = X ^ v := by rw [rpow_neg hX0.le, inv_inv]
  -- `X ≤ C (2N + 1) log (4N + 2)`
  have hXup : X ≤ C * (2 * N + 1) * log (4 * N + 2) := by
    have hg : (t (2 * N) : ℝ) ≤ ((4 * N + 2 : ℝ)) ^ (C * (2 * N + 1)) := by
      have := hgrow (2 * N)
      have : (t (2 * N) : ℝ) ≤ ((2 * (2 * N) + 2 : ℕ) : ℝ) ^ (C * (2 * N + 1)) := by
        exact_mod_cast this
      convert this using 2; push_cast; ring
    calc X ≤ log (((4 * N + 2 : ℝ)) ^ (C * (2 * N + 1))) :=
          log_le_log (by linarith [ht2 (2 * N) (by omega)]) hg
      _ = C * (2 * N + 1) * log (4 * N + 2) := by rw [log_pow]; push_cast; ring
  have hlog42 : 0 ≤ log (4 * N + 2 : ℝ) := log_nonneg (by linarith)
  refine ⟨rpow_pos_of_pos hX0 _, rpow_le_one_of_one_le_of_nonpos hX1 (by linarith),
    fun n hn hn2 ↦ ?_, fun n hn ↦ ?_, ?_⟩
  · -- `ε ≤ (log t_n)^{-v}`
    have hpos : 0 < log (t n : ℝ) := log_pos (ht2 n (by omega))
    refine rpow_le_rpow_of_nonpos hpos (log_le_log (by linarith [ht2 n (by omega)]) ?_)
      (by linarith)
    exact_mod_cast htm hn2
  · -- the threshold of the three-variable step
    rw [hεinv]
    have hC : (0 : ℝ) ≤ C := by positivity
    calc K * X ^ v ≤ K * X := by gcongr; exact rpow_le_self_of_one_le hX1 (by linarith)
      _ ≤ K * (C * (2 * N + 1) * (4 * N + 2)) := by
          gcongr
          refine hXup.trans ?_
          gcongr
          have := log_le_sub_one_of_pos (show (0 : ℝ) < 4 * N + 2 by positivity)
          linarith
      _ = K * C * ((2 * N + 1) * (4 * N + 2)) := by ring
      _ ≤ K * C * (18 * (N : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
      _ = K * (18 * C) * (N : ℝ) ^ 2 := by ring
      _ ≤ 2 ^ N * L / 2 := h2
      _ ≤ 2 ^ n * L / 2 := by gcongr; exact one_le_two
      _ ≤ t n * L := by
          have := hlowR n (by omega)
          nlinarith
  · -- the count
    rw [hεinv, log_rpow hX0]
    have hlogX : log X ≤ X ^ δ / δ := log_le_rpow_div hX0.le hδ0
    have hXδ : 1 ≤ X ^ δ := one_le_rpow hX1 hδ0.le
    have hlogX0 : 0 ≤ log X := log_nonneg hX1
    have hb1 : 1 + v * log X ≤ (1 + v / δ) * X ^ δ := by
      have : v * log X ≤ v / δ * X ^ δ := by
        calc v * log X ≤ v * (X ^ δ / δ) := by gcongr
          _ = v / δ * X ^ δ := by ring
      nlinarith
    -- `X ≤ A N^{1+δ}`
    have hXA : X ≤ A * (N : ℝ) ^ (1 + δ) := by
      have hlog : log (4 * N + 2 : ℝ) ≤ 6 * (N : ℝ) ^ δ / δ := by
        calc log (4 * N + 2 : ℝ) ≤ (4 * N + 2 : ℝ) ^ δ / δ := log_le_rpow_div (by positivity) hδ0
          _ ≤ (6 * N : ℝ) ^ δ / δ := by gcongr; linarith
          _ = (6 : ℝ) ^ δ * (N : ℝ) ^ δ / δ := by rw [mul_rpow (by norm_num) hN0.le]
          _ ≤ 6 * (N : ℝ) ^ δ / δ := by
              gcongr
              exact rpow_le_self_of_one_le (by norm_num) (by linarith)
      have hC : (0 : ℝ) ≤ C := by positivity
      have hNδ : (0 : ℝ) ≤ (N : ℝ) ^ δ := by positivity
      calc X ≤ C * (2 * N + 1) * log (4 * N + 2) := hXup
        _ ≤ C * (3 * N) * (6 * (N : ℝ) ^ δ / δ) := by gcongr; linarith
        _ = 18 * C / δ * (N * (N : ℝ) ^ δ) := by ring
        _ ≤ A * (N * (N : ℝ) ^ δ) := by
            rw [hA]; gcongr; linarith
        _ = A * (N : ℝ) ^ (1 + δ) := by rw [rpow_add hN0, rpow_one]
    have hpow7 : (X ^ v) ^ 7 = X ^ a := by
      rw [← rpow_natCast, ← rpow_mul hX0.le, ha]; push_cast; ring_nf
    have hpow4 : (X ^ δ) ^ 4 = X ^ (4 * δ) := by
      rw [← rpow_natCast, ← rpow_mul hX0.le]; push_cast; ring_nf
    calc K * (X ^ v) ^ 7 * (1 + v * log X) ^ 4
        ≤ K * (X ^ v) ^ 7 * ((1 + v / δ) * X ^ δ) ^ 4 := by
          gcongr
      _ = K * (1 + v / δ) ^ 4 * X ^ (a + 4 * δ) := by
          rw [mul_pow, hpow7, hpow4, rpow_add hX0]; ring
      _ ≤ K * (1 + v / δ) ^ 4 * (A * (N : ℝ) ^ (1 + δ)) ^ (a + 4 * δ) := by
          gcongr
      _ = K' * (N : ℝ) ^ e := by
          rw [mul_rpow hA0.le (by positivity), ← rpow_mul hN0.le, hK', he]; ring
      _ < (N : ℝ) ^ (1 - e) * (N : ℝ) ^ e := by
          gcongr
      _ = N := by rw [← rpow_add hN0, sub_add_cancel, rpow_one]

end Real
