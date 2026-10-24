/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Card

-- Used only inside proofs.
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Order.Interval.Finset.Nat

/-!
# Doubling sequences of positions

**Layer 7.5, the counting** (Bugeaud–Evertse 2008, §7). The repetitions of a sequence of
complexity `p n ≤ c n (log n)^u` (`Function.exists_repetitions_of_complexity_le`) sit at positions
`t_n` with `2 t_n < t_{n+1}` and `t_n ≤ (2n + 2)^{C(n+1)}`. Two facts about such sequences drive
every count of Bugeaud–Evertse type:

* a doubling sequence grows geometrically, so a window `t_{n₀} ≤ t_n ≤ R t_{n₀}` holds at most
  `log R / log 2 + 1` members (`Nat.card_le_of_doubling_window`; for real heights growing by a
  factor `q > 1`, `Real.card_le_of_geometric_window`);
* with `ε = (log t_{2N})^{-v}` the points `N ≤ n < 2N` satisfy every threshold the Subspace
  Theorem asks for, and a count `K ε^{-p} (1 + log ε⁻¹)^q` of subspaces stays below `N` when
  `p v < 1` (`Real.eventually_doubling_thresholds`): `log t_{2N}` lies between `(2N - 1) log 2`
  and `C (2N + 1) log (4N + 2)`.

## Main results

* `Nat.two_pow_mul_le_of_doubling`: `2 t_n < t_{n+1}` gives `2^k t_i ≤ t_{i+k}`.
* `Nat.card_le_of_doubling_window`: a window of ratio `R` holds `≤ log R / log 2 + 1` members.
* `Real.card_le_of_geometric_window`, `Real.card_le_of_forall_mem_window`: the same for real
  heights `g` with `q g_n ≤ g_{n+1}`, `q > 1`: a window `[s, ρ s)` holds `≤ log ρ / log q + 1`
  indices, and windows at the points of a finite set `𝒯` hold `≤ #𝒯 (log ρ / log q + 1)`. This is
  how the interval form of the quantitative Subspace Theorem (`Real.SubspaceIntervalWith`) is
  counted for points of geometrically growing heights; `Real.log_div_log_two_le` bounds the
  factor `log ρ / log 2 + 1` for `ρ = K X`.
* `Real.eventually_doubling_thresholds`: **the thresholds of Bugeaud–Evertse 2008, §7**, for a
  count `K ε^{-p} (1 + log ε⁻¹)^q`.

## References

Y. Bugeaud, J.-H. Evertse, *On two notions of complexity of algebraic numbers*, Acta Arith.
**133** (2008), 221–250, §7.
-/

@[expose] public section

open Filter Finset

/-- **A doubling sequence grows geometrically**: `2^k t_i ≤ t_{i+k}`. -/
theorem Nat.two_pow_mul_le_of_doubling {t : ℕ → ℕ} (ht : ∀ n, 2 * t n < t (n + 1))
    (i k : ℕ) : 2 ^ k * t i ≤ t (i + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc 2 ^ (k + 1) * t i = 2 * (2 ^ k * t i) := by ring
      _ ≤ 2 * t (i + k) := Nat.mul_le_mul_left 2 ih
      _ ≤ t (i + (k + 1)) := (ht (i + k)).le

/-- **A window of a doubling sequence.** The indices `n ≥ n₀` with `t_n ≤ R t_{n₀}` number at most
`log R / log 2 + 1`. -/
theorem Nat.card_le_of_doubling_window {t : ℕ → ℕ} (ht : ∀ n, 2 * t n < t (n + 1)) {n₀ : ℕ}
    (h0 : 0 < t n₀) {R : ℝ} (hR : 1 ≤ R) {J : Finset ℕ}
    (hJ : ∀ n ∈ J, n₀ ≤ n ∧ (t n : ℝ) ≤ R * t n₀) :
    (#J : ℝ) ≤ Real.log R / Real.log 2 + 1 := by
  set D := ⌊Real.log R / Real.log 2⌋₊ with hD
  have hsub : J ⊆ Icc n₀ (n₀ + D) := by
    intro n hn
    obtain ⟨h1, h2⟩ := hJ n hn
    refine mem_Icc.2 ⟨h1, ?_⟩
    have hd := Nat.two_pow_mul_le_of_doubling ht n₀ (n - n₀)
    rw [Nat.add_sub_cancel' h1] at hd
    have hdR : (2 : ℝ) ^ (n - n₀) * t n₀ ≤ R * t n₀ := by
      have : ((2 ^ (n - n₀) * t n₀ : ℕ) : ℝ) ≤ t n := by exact_mod_cast hd
      push_cast at this
      linarith
    have h2R : (2 : ℝ) ^ (n - n₀) ≤ R := le_of_mul_le_mul_right hdR (by exact_mod_cast h0)
    have hlog : ((n - n₀ : ℕ) : ℝ) * Real.log 2 ≤ Real.log R := by
      rw [← Real.log_pow]; exact Real.log_le_log (by positivity) h2R
    have : ((n - n₀ : ℕ) : ℝ) ≤ Real.log R / Real.log 2 := by
      rw [le_div_iff₀ (Real.log_pos one_lt_two)]; exact hlog
    have := Nat.le_floor this
    omega
  have hc := card_le_card hsub
  rw [Nat.card_Icc] at hc
  have hfl := Nat.floor_le (div_nonneg (Real.log_nonneg hR) (Real.log_nonneg one_le_two))
  have : (#J : ℝ) ≤ (D : ℝ) + 1 := by exact_mod_cast (by omega : #J ≤ D + 1)
  linarith

namespace Real

/-- **Geometric growth**: `q g_n ≤ g_{n+1}` with `q ≥ 0` gives `q^k g_i ≤ g_{i+k}`. -/
theorem pow_mul_le_of_geometric {g : ℕ → ℝ} {q : ℝ} (hq : 0 ≤ q) (hg : ∀ n, q * g n ≤ g (n + 1))
    (i k : ℕ) : q ^ k * g i ≤ g (i + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc q ^ (k + 1) * g i = q * (q ^ k * g i) := by ring
      _ ≤ q * g (i + k) := mul_le_mul_of_nonneg_left ih hq
      _ ≤ g (i + (k + 1)) := hg (i + k)

/-- **A window of geometrically growing heights.** Let `g_n > 0` with `q g_n ≤ g_{n+1}`, `q > 1`.
The indices `n` with `s ≤ g_n < ρ s` number at most `⌊log ρ / log q⌋ + 1`. -/
theorem card_le_of_geometric_window {g : ℕ → ℝ} {q : ℝ} (hq : 1 < q) (hg0 : ∀ n, 0 < g n)
    (hg : ∀ n, q * g n ≤ g (n + 1)) {ρ s : ℝ} (hρ : 1 ≤ ρ) {J : Finset ℕ}
    (hJ : ∀ n ∈ J, s ≤ g n ∧ g n < ρ * s) : #J ≤ ⌊log ρ / log q⌋₊ + 1 := by
  rcases J.eq_empty_or_nonempty with rfl | hne
  · simp
  set n₀ := J.min' hne with hn₀
  have hlq : 0 < log q := log_pos hq
  have hsub : J ⊆ Icc n₀ (n₀ + ⌊log ρ / log q⌋₊) := by
    intro n hn
    have h1 : n₀ ≤ n := J.min'_le n hn
    refine mem_Icc.2 ⟨h1, ?_⟩
    have hgeo := pow_mul_le_of_geometric (by linarith) hg n₀ (n - n₀)
    rw [Nat.add_sub_cancel' h1] at hgeo
    have hs : s ≤ g n₀ := (hJ n₀ (J.min'_mem hne)).1
    have hlt : q ^ (n - n₀) * g n₀ < ρ * g n₀ :=
      hgeo.trans_lt ((hJ n hn).2.trans_le (mul_le_mul_of_nonneg_left hs (by linarith)))
    have hqρ : q ^ (n - n₀) < ρ := lt_of_mul_lt_mul_right hlt (hg0 n₀).le
    have hlog : ((n - n₀ : ℕ) : ℝ) * log q < log ρ := by
      rw [← log_pow]
      exact log_lt_log (by positivity) hqρ
    have : ((n - n₀ : ℕ) : ℝ) ≤ log ρ / log q := by
      rw [le_div_iff₀ hlq]
      exact hlog.le
    have := Nat.le_floor this
    omega
  have hc := card_le_card hsub
  rw [Nat.card_Icc] at hc
  omega

/-- **Windows of geometrically growing heights.** Let `g_n > 0` with `q g_n ≤ g_{n+1}`, `q > 1`,
and `ρ ≥ 1`. If every index of `J` has `s ≤ g_n < ρ s` for some `s ∈ 𝒯`, then
`#J ≤ #𝒯 (log ρ / log q + 1)`. -/
theorem card_le_of_forall_mem_window {g : ℕ → ℝ} {q : ℝ} (hq : 1 < q) (hg0 : ∀ n, 0 < g n)
    (hg : ∀ n, q * g n ≤ g (n + 1)) {ρ : ℝ} (hρ : 1 ≤ ρ) (𝒯 : Finset ℝ) {J : Finset ℕ}
    (hJ : ∀ n ∈ J, ∃ s ∈ 𝒯, s ≤ g n ∧ g n < ρ * s) :
    (#J : ℝ) ≤ #𝒯 * (log ρ / log q + 1) := by
  classical
  set D := ⌊log ρ / log q⌋₊ with hD
  have hsub : J ⊆ 𝒯.biUnion fun s ↦ J.filter fun n ↦ s ≤ g n ∧ g n < ρ * s := by
    intro n hn
    obtain ⟨s, hs, h⟩ := hJ n hn
    exact mem_biUnion.2 ⟨s, hs, mem_filter.2 ⟨hn, h⟩⟩
  have hcard : #J ≤ #𝒯 * (D + 1) := (card_le_card hsub).trans <|
    card_biUnion_le_card_mul _ _ _ fun s _ ↦
      card_le_of_geometric_window hq hg0 hg hρ fun n hn ↦ (mem_filter.1 hn).2
  have hfl : (D : ℝ) ≤ log ρ / log q :=
    Nat.floor_le (div_nonneg (log_nonneg hρ) (log_pos hq).le)
  calc (#J : ℝ) ≤ #𝒯 * ((D : ℝ) + 1) := by exact_mod_cast hcard
    _ ≤ #𝒯 * (log ρ / log q + 1) := by gcongr

/-- **The window factor**: `log (K X) / log 2 + 1 ≤ (2 log K + 3) (1 + log X)` for `K, X ≥ 1`. -/
theorem log_div_log_two_le {K X : ℝ} (hK : 1 ≤ K) (hX : 1 ≤ X) :
    log (K * X) / log 2 + 1 ≤ (2 * log K + 3) * (1 + log X) := by
  have hlK := log_nonneg hK
  have hlX := log_nonneg hX
  have hq : 1 / 2 ≤ log (2 : ℝ) := by have := log_two_gt_d9; linarith
  have hq0 : 0 < log (2 : ℝ) := by linarith
  rw [log_mul (by linarith) (by linarith)]
  have : (log K + log X) / log 2 ≤ 2 * (log K + log X) := by
    rw [div_le_iff₀ hq0]
    nlinarith
  nlinarith [mul_nonneg hlK hlX]

/-- **The thresholds of Bugeaud–Evertse 2008, §7.** Let `p, q ≥ 1`, `0 < v`, `p v < 1`,
`K, L > 0`. For all large `N` and every `t` with `2 t_n < t_{n+1}` and
`t_n ≤ (2n + 2)^{C(n+1)}`, the number `ε = (log t_{2N})^{-v}` satisfies `0 < ε ≤ 1`,
`ε ≤ (log t_n)^{-v}` for `N ≤ n ≤ 2N`, `K ε⁻¹ ≤ t_n L` for `n ≥ N`, and
`K ε^{-p} (1 + log ε⁻¹)^q < N`. -/
theorem eventually_doubling_thresholds (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) {C : ℕ} {v : ℝ}
    (hv : 0 < v) (hpv : p * v < 1) {K L : ℝ} (hK : 0 < K) (hL : 0 < L) :
    ∀ᶠ N : ℕ in atTop, ∀ t : ℕ → ℕ, (∀ n, 2 * t n < t (n + 1)) →
      (∀ n, t n ≤ (2 * n + 2) ^ (C * (n + 1))) →
      0 < log (t (2 * N)) ^ (-v) ∧ log (t (2 * N)) ^ (-v) ≤ 1 ∧
      (∀ n, N ≤ n → n ≤ 2 * N → log (t (2 * N)) ^ (-v) ≤ log (t n) ^ (-v)) ∧
      (∀ n, N ≤ n → K * (log (t (2 * N)) ^ (-v))⁻¹ ≤ t n * L) ∧
      K * ((log (t (2 * N)) ^ (-v))⁻¹) ^ p * (1 + log (log (t (2 * N)) ^ (-v))⁻¹) ^ q < N := by
  -- the exponent `e = (1 + δ)(p v + q δ) < 1`
  set a := p * v with ha
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hv1 : v < 1 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    nlinarith
  set δ := (1 - a) / (4 * q) with hδ
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hδ0 : 0 < δ := by rw [hδ]; exact div_pos (by linarith) (by positivity)
  have hqδ : q * δ = (1 - a) / 4 := by rw [hδ]; field_simp
  have hδle : δ ≤ (1 - a) / 4 := by rw [← hqδ]; nlinarith
  set e := (1 + δ) * (a + q * δ) with he
  have he1 : e < 1 := by
    rw [he, hqδ]
    have h1 : (1 + δ) * (a + (1 - a) / 4) ≤ (1 + (1 - a) / 4) * (a + (1 - a) / 4) := by
      gcongr
    nlinarith [mul_pos (show 0 < 1 - a by linarith) (show 0 < 11 - 3 * a by linarith)]
  have he0 : 0 ≤ e := by positivity
  set A : ℝ := 18 * (C + 1) / δ with hA
  have hA0 : 0 < A := by positivity
  set K' := K * (1 + v / δ) ^ q * A ^ (a + q * δ) with hK'
  -- opaque from here on: unfolding them makes defeq checks on real arithmetic explode
  clear_value K' A e δ a
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
    calc K * X ^ v ≤ K * X := by gcongr; exact rpow_le_self_of_one_le hX1 hv1.le
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
    have hpowp : (X ^ v) ^ p = X ^ a := by
      rw [← rpow_natCast, ← rpow_mul hX0.le, ha]; ring_nf
    have hpowq : (X ^ δ) ^ q = X ^ (q * δ) := by
      rw [← rpow_natCast, ← rpow_mul hX0.le]; ring_nf
    have hb0 : 0 ≤ 1 + v * log X := by positivity
    calc K * (X ^ v) ^ p * (1 + v * log X) ^ q
        ≤ K * (X ^ v) ^ p * ((1 + v / δ) * X ^ δ) ^ q := by
          gcongr
      _ = K * (1 + v / δ) ^ q * X ^ (a + q * δ) := by
          rw [mul_pow, hpowp, hpowq, rpow_add hX0]; ring
      _ ≤ K * (1 + v / δ) ^ q * (A * (N : ℝ) ^ (1 + δ)) ^ (a + q * δ) := by
          gcongr
      _ = K' * (N : ℝ) ^ e := by
          rw [mul_rpow hA0.le (by positivity), ← rpow_mul hN0.le, hK', he]; ring
      _ < (N : ℝ) ^ (1 - e) * (N : ℝ) ^ e := by
          gcongr
      _ = N := by rw [← rpow_add hN0, sub_add_cancel, rpow_one]

end Real
