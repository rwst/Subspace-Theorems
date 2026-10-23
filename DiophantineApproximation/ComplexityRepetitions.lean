/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.FactorComplexity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- Used only inside proofs.
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Repetitions from a complexity bound `p n ≤ c n (log n)^u`

**Layer 7.5, the combinatorics, quantitative** (Bugeaud–Evertse 2008, Lemma 6.1, combinatorial
form). If the factor complexity of a sequence is at most `c n (log n)^u`, then for every `v > u`
there are positions `r_n < t_n`, growing at least geometrically (`2 t_n < t_{n+1}`) and at most
like `(2n + 2)^{C (n + 1)}`, such that the `t_n (log t_n)^{-v}` letters after position `t_n`
repeat those after position `r_n`, and the repetition cannot be slid to the left
(`a (r_n - 1) ≠ a (t_n - 1)` when `r_n ≥ 1`). Nothing here refers to a number: the base-`b`
digits of a real number turn it into Bugeaud–Evertse's approximations
(`BugeaudEvertse2008/Repetitions.lean`), and the steering word of `(3/2)^n` into a sequence of
kernel violators (`Stephan2026a/QuantitativeViolators.lean`).

**Bugeaud–Evertse state the lemma for `v < u`; it holds for `v > u`.** The pigeonhole (two equal
factors of length `m` among the first `p m + 1` positions) gives a repetition of length about
`ℓ (log ℓ)^{-u}` after a position `t ≤ ℓ`, i.e. the exponent `c₃ (log t)^{-u}`, which is at least
`(log t)^{-v}` for large `t` only when `v > u`.

The alphabet need not be finite; only the sets of factors of each length are
(`hfin : ∀ m, (factors a m).Finite`, which `Function.finite_factors` gives over a finite alphabet).

## Main results

* `Function.exists_rep_of_complexity_le_nat`: at most `p` factors of length `m` give a
  repetition of length `≥ m / 2` at a distance `P > m / 2`, after a position `R` with
  `R + P ≤ 2 p + m`, that cannot be slid to the left.
* `Function.exists_rep_of_complexity_le_rpow`: one repetition from `p m ≤ c m (log m)^u`.
* `Function.exists_repetitions_of_complexity_le`: **Bugeaud–Evertse 2008, Lemma 6.1,
  combinatorial form**.

## References

Y. Bugeaud, J.-H. Evertse, *On two notions of complexity of algebraic numbers*, Acta Arith.
**133** (2008), 221–250, §6.
-/

@[expose] public section

open Filter Topology

namespace Function

variable {α : Type*} {a : ℕ → α}

/-- **The pigeonhole.** Finitely many, at most `p`, factors of length `m ≥ 1` give a repetition
of length `L ≥ m / 2` at a distance `P > m / 2` after position `R`, with `R + P ≤ 2 p + m`, that
cannot be slid to the left: `R = 0` or `a (R - 1) ≠ a (R - 1 + P)`. -/
theorem exists_rep_of_complexity_le_nat {m p : ℕ} (hfin : (factors a m).Finite) (hm : 1 ≤ m)
    (hp : complexity a m ≤ p) :
    ∃ R P L : ℕ, m ≤ 2 * L ∧ m < 2 * P ∧ R + P ≤ 2 * p + m ∧
      (∀ k, R ≤ k → k < R + L → a (k + P) = a k) ∧ (R = 0 ∨ a (R - 1) ≠ a (R - 1 + P)) := by
  classical
  have hcard : hfin.toFinset.card < (Finset.range (p + 1)).card := by
    rw [Finset.card_range, ← Set.ncard_eq_toFinset_card _ hfin]
    exact Nat.lt_succ_of_le hp
  obtain ⟨x, hx, y, hy, hxy, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
    (f := fun i ↦ factor a i m) (fun i _ ↦ by simp [factors])
  wlog hlt : x < y generalizing x y
  · exact this y hy x hx hxy.symm heq.symm (by omega)
  simp only [Finset.mem_range] at hx hy
  set s := y - x with hs
  have hbase : ∀ i, x ≤ i → i + s < x + m + s → a (i + s) = a i := by
    intro i hi hiL
    have := factor_eq_factor_iff.mp heq (i - x) (by omega)
    rw [show x + (i - x) = i by omega, show y + (i - x) = i + s by omega] at this
    exact this.symm
  -- stretch the period `s` to a multiple `P > m / 2`
  set q := m / (2 * s) with hq
  have hdm := Nat.div_add_mod m (2 * s)
  have hmod := Nat.mod_lt m (show 0 < 2 * s by omega)
  rw [← hq] at hdm
  set P := (q + 1) * s with hP
  have hP1 : m < 2 * P := by rw [hP]; nlinarith
  have hP2 : 2 * P ≤ m + 2 * s := by
    have : 2 * s * q ≤ m := by rw [hq]; exact Nat.mul_div_le m (2 * s)
    rw [hP]; nlinarith
  set E := x + m + s - P with hE
  have hper : ∀ k, x ≤ k → k < E → a (k + P) = a k := fun k hk hkE ↦
    forall_add_mul_eq_of_forall_add_eq hbase (q + 1) k hk (by omega)
  -- slide it to the left
  have hex : ∃ w, ∀ k, w ≤ k → k < E → a (k + P) = a k := ⟨x, hper⟩
  have hspec := Nat.find_spec hex
  have hle : Nat.find hex ≤ x := Nat.find_min' hex hper
  refine ⟨Nat.find hex, P, E - Nat.find hex, by omega, hP1, by omega,
    fun k hk hkL ↦ hspec k hk (by omega), ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · exact Or.inl h0
  · refine Or.inr fun heq' ↦ Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      fun k hk hkE ↦ ?_
    rcases eq_or_lt_of_le hk with rfl | hlt
    · exact heq'.symm
    · exact hspec k (by omega) hkE

/-- **One repetition from `p m ≤ c m (log m)^u`.** For `m ≥ 4` with `log m ≥ 1` and
`6 c 2^v (log m)^{u - v} ≤ 1` there are `r < t` with `m < 2 t ≤ 6 c m (log m)^u` such that the
`t (log t)^{-v}` letters after `t` repeat those after `r`, minimally. -/
theorem exists_rep_of_complexity_le_rpow {c u v : ℝ} (hc : 1 ≤ c) (hu : 0 ≤ u)
    (huv : u < v) {m : ℕ} (hfin : (factors a m).Finite) (hm : 4 ≤ m) (hlog : 1 ≤ Real.log m)
    (hsmall : 6 * c * 2 ^ v * Real.log m ^ (u - v) ≤ 1)
    (hp : (complexity a m : ℝ) ≤ c * m * Real.log m ^ u) :
    ∃ r t : ℕ, r < t ∧ m < 2 * t ∧ (t : ℝ) ≤ 3 * c * m * Real.log m ^ u ∧
      (r = 0 ∨ a (r - 1) ≠ a (t - 1)) ∧
      ∀ i < ⌈t * Real.log t ^ (-v)⌉₊, a (i + t) = a (i + r) := by
  obtain ⟨R, P, L, hL, hP, hRP, hper, hmin⟩ :=
    exists_rep_of_complexity_le_nat hfin (by omega : 1 ≤ m) le_rfl
  have hm4 : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hmR : (0 : ℝ) < m := by linarith
  have hlogpos : 0 < Real.log m := by linarith
  have hpow1 : 1 ≤ Real.log m ^ u := Real.one_le_rpow hlog hu
  set t := R + P with ht
  have ht3 : (t : ℝ) ≤ 3 * c * m * Real.log m ^ u := by
    have h1 : (t : ℝ) ≤ 2 * (complexity a m : ℝ) + m := by rw [ht]; exact_mod_cast hRP
    have h2 : (m : ℝ) ≤ c * m * Real.log m ^ u := by
      have : 1 ≤ c * Real.log m ^ u := by nlinarith
      nlinarith
    linarith
  refine ⟨R, t, by omega, by omega, ht3, ?_, fun i hi ↦ ?_⟩
  · rcases Nat.eq_zero_or_pos R with h0 | hR
    · exact Or.inl h0
    · refine Or.inr ?_
      rw [show t - 1 = R - 1 + P by omega]
      exact hmin.resolve_left (by omega)
  · have hv : 0 < v := hu.trans_lt huv
    have hmt : (m : ℝ) < 2 * t := by exact_mod_cast (show m < 2 * t by omega)
    have hlogt : Real.log m / 2 ≤ Real.log t := by
      have hsq : (m : ℝ) ≤ (t : ℝ) ^ 2 := by nlinarith
      have := Real.log_le_log hmR hsq
      rw [Real.log_pow] at this
      push_cast at this
      linarith
    have hA : Real.log t ^ (-v) ≤ 2 ^ v * Real.log m ^ (-v) := by
      calc Real.log t ^ (-v) ≤ (Real.log m / 2) ^ (-v) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hlogt (by linarith)
        _ = 2 ^ v * Real.log m ^ (-v) := by
            rw [Real.div_rpow hlogpos.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
            field_simp
    have hB : Real.log m ^ u * Real.log m ^ (-v) = Real.log m ^ (u - v) := by
      rw [← Real.rpow_add hlogpos, sub_eq_add_neg]
    have hL' : (m : ℝ) ≤ 2 * L := by exact_mod_cast hL
    have hc0 : (0 : ℝ) ≤ 3 * c * m * Real.log m ^ u :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hmR.le)
        (Real.rpow_nonneg hlogpos.le _)
    have hlen : (t : ℝ) * Real.log t ^ (-v) ≤ L :=
      calc (t : ℝ) * Real.log t ^ (-v)
          ≤ (3 * c * m * Real.log m ^ u) * (2 ^ v * Real.log m ^ (-v)) :=
            mul_le_mul ht3 hA (Real.rpow_nonneg (Real.log_nonneg (by
              exact_mod_cast (show 1 ≤ t by omega))) _) hc0
        _ = (m / 2) * (6 * c * 2 ^ v * Real.log m ^ (u - v)) := by rw [← hB]; ring
        _ ≤ (m / 2) * 1 := by gcongr
        _ ≤ L := by linarith
    have hiL : i < L := lt_of_lt_of_le hi (Nat.ceil_le.mpr hlen)
    have := hper (R + i) (by omega) (by omega)
    rwa [show R + i + P = i + t by omega, add_comm R i] at this

/-- **Bugeaud–Evertse 2008, Lemma 6.1, combinatorial form** (with `v > u`; see the module
docstring). If `p n ≤ c n (log n)^u` for `n ≥ n₀` and the factors are finite in number,
`0 ≤ u < v`, there are positions `r n < t n` with `2 t n < t (n + 1)` and
`t n ≤ (2 n + 2)^{C (n + 1)}` such that the `t n (log t n)^{-v}` letters after `t n` repeat those
after `r n`, and `r n = 0` or `a (r n - 1) ≠ a (t n - 1)`. -/
theorem exists_repetitions_of_complexity_le {c u v : ℝ} (hfin : ∀ m, (factors a m).Finite)
    (hu : 0 ≤ u) (huv : u < v) (n₀ : ℕ)
    (hp : ∀ n ≥ n₀, (complexity a n : ℝ) ≤ c * n * Real.log n ^ u) :
    ∃ (C : ℕ) (r t : ℕ → ℕ), (∀ n, r n < t n) ∧ (∀ n, 2 * t n < t (n + 1)) ∧
      (∀ n, t n ≤ (2 * n + 2) ^ (C * (n + 1))) ∧
      (∀ n, r n = 0 ∨ a (r n - 1) ≠ a (t n - 1)) ∧
      ∀ n, ∀ i < ⌈t n * Real.log (t n) ^ (-v)⌉₊, a (i + t n) = a (i + r n) := by
  -- `c ≥ 1` without loss of generality
  obtain ⟨c, hc1, hp⟩ : ∃ c' : ℝ, 1 ≤ c' ∧
      ∀ n ≥ n₀, (complexity a n : ℝ) ≤ c' * n * Real.log n ^ u :=
    ⟨max c 1, le_max_right _ _, fun n hn ↦ (hp n hn).trans <|
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Nat.cast_nonneg _)) (Real.rpow_nonneg (Real.log_natCast_nonneg n) u)⟩
  have hc0 : 0 < c := by linarith
  -- the lengths `m` that work
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℕ, ∀ m ≥ M₀, n₀ ≤ m ∧ 4 ≤ m ∧ 1 ≤ Real.log m ∧
      6 * c * 2 ^ v * Real.log m ^ (u - v) ≤ 1 := by
    have hlog : Tendsto (fun m : ℕ ↦ Real.log m) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have h0 : Tendsto (fun m : ℕ ↦ Real.log m ^ (u - v)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (y := v - u) (by linarith)).comp hlog
      simpa [Function.comp_def, neg_sub] using this
    have hK : 0 < 6 * c * 2 ^ v := by positivity
    refine eventually_atTop.mp ?_
    filter_upwards [eventually_ge_atTop n₀, eventually_ge_atTop 4, hlog.eventually_ge_atTop 1,
      h0.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (6 * c * 2 ^ v) by positivity))]
      with m h1 h2 h3 h4
    refine ⟨h1, h2, h3, ?_⟩
    rw [lt_div_iff₀ hK] at h4
    linarith
  -- the growth exponent `D = 2 U + E`
  set U := ⌈u⌉₊ with hU
  obtain ⟨E, hE⟩ : ∃ E : ℕ, M₀ ≤ E ∧ 12 * c * ((2 * U + E : ℕ) : ℝ) ^ U ≤ 4 ^ E := by
    have h := (tendsto_pow_const_div_const_pow_of_one_lt U (show (1 : ℝ) < 4 by norm_num)).comp
      (tendsto_add_atTop_nat (2 * U))
    have hF : (0 : ℝ) < 4 ^ (2 * U) := by positivity
    obtain ⟨E, hE⟩ := (eventually_ge_atTop M₀ |>.and (h.eventually (gt_mem_nhds
      (show (0 : ℝ) < 1 / (12 * c * 4 ^ (2 * U)) by positivity)))).exists
    refine ⟨E, hE.1, ?_⟩
    have h2 := hE.2
    simp only [Function.comp_apply] at h2
    rw [div_lt_div_iff₀ (by positivity) (by positivity), pow_add] at h2
    have : 12 * c * ((E + 2 * U : ℕ) : ℝ) ^ U * 4 ^ (2 * U) < 4 ^ E * 4 ^ (2 * U) := by
      linarith
    rw [show 2 * U + E = E + 2 * U by ring]
    exact (lt_of_mul_lt_mul_right this hF.le).le
  set D := 2 * U + E with hD
  set m : ℕ → ℕ := fun k ↦ (2 * k + 2) ^ (D * (k + 1)) with hm
  have hmM : ∀ k, M₀ ≤ m k := fun k ↦
    calc M₀ ≤ D := by omega
      _ ≤ 2 ^ D := (Nat.lt_two_pow_self).le
      _ ≤ 2 ^ (D * (k + 1)) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right _ (by omega))
      _ ≤ m k := Nat.pow_le_pow_left (by omega) _
  have hrep : ∀ k, ∃ r t : ℕ, r < t ∧ m k < 2 * t ∧
      (t : ℝ) ≤ 3 * c * (m k : ℕ) * Real.log (m k : ℕ) ^ u ∧
      (r = 0 ∨ a (r - 1) ≠ a (t - 1)) ∧
      ∀ i < ⌈t * Real.log t ^ (-v)⌉₊, a (i + t) = a (i + r) := fun k ↦ by
    obtain ⟨h1, h2, h3, h4⟩ := hM₀ (m k) (hmM k)
    exact exists_rep_of_complexity_le_rpow hc1 hu huv (hfin _) h2 h3 h4 (hp _ h1)
  choose r t hrt hmt ht3 hmin hrep using hrep
  -- the growth: `12 c m_k (log m_k)^u ≤ m_{k+1}`
  have hgrow : ∀ k, 12 * c * (m k : ℝ) * Real.log (m k) ^ u ≤ m (k + 1) := by
    intro k
    set x : ℝ := 2 * k + 4 with hx
    have hx4 : (4 : ℝ) ≤ x := by rw [hx]; have : (0 : ℝ) ≤ k := k.cast_nonneg; linarith
    have hmk : ((m k : ℕ) : ℝ) = (2 * k + 2 : ℝ) ^ (D * (k + 1)) := by simp [hm]
    have hmk1 : ((m (k + 1) : ℕ) : ℝ) = x ^ D * x ^ (D * (k + 1)) := by
      simp only [hm, hx]; push_cast; rw [← pow_add]; ring_nf
    have hlog1 : 1 ≤ Real.log (m k) := (hM₀ (m k) (hmM k)).2.2.1
    have hlogle : Real.log (m k) ≤ D * x ^ 2 := by
      rw [hmk, Real.log_pow]
      have h1 : Real.log (2 * k + 2 : ℝ) ≤ x := by
        have := Real.log_le_self (show (0 : ℝ) ≤ 2 * k + 2 by positivity); linarith
      have h2 : ((D * (k + 1) : ℕ) : ℝ) ≤ D * x := by push_cast; gcongr; linarith
      have h3 : (0 : ℝ) ≤ Real.log (2 * k + 2 : ℝ) := Real.log_nonneg (by linarith)
      calc ((D * (k + 1) : ℕ) : ℝ) * Real.log (2 * k + 2 : ℝ) ≤ (D * x) * x := by gcongr
        _ = D * x ^ 2 := by ring
    have hlogU : Real.log (m k) ^ u ≤ (D : ℝ) ^ U * x ^ (2 * U) := by
      calc Real.log (m k) ^ u ≤ Real.log (m k) ^ (U : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hlog1 (Nat.le_ceil u)
        _ = Real.log (m k) ^ U := Real.rpow_natCast _ _
        _ ≤ (D * x ^ 2) ^ U := pow_le_pow_left₀ (by linarith) hlogle U
        _ = (D : ℝ) ^ U * x ^ (2 * U) := by rw [mul_pow, pow_mul]
    have hxE : (4 : ℝ) ^ E ≤ x ^ E := pow_le_pow_left₀ (by norm_num) hx4 E
    have hDcast : ((2 * U + E : ℕ) : ℝ) = D := by rw [hD]
    have hE' : 12 * c * (D : ℝ) ^ U ≤ x ^ E := by rw [← hDcast]; linarith [hE.2]
    have hmx : (m k : ℝ) ≤ x ^ (D * (k + 1)) := by
      rw [hmk]; exact pow_le_pow_left₀ (by positivity) (by linarith) _
    have hmk0 : (0 : ℝ) ≤ m k := Nat.cast_nonneg _
    calc 12 * c * (m k : ℝ) * Real.log (m k) ^ u
        ≤ 12 * c * (m k : ℝ) * ((D : ℝ) ^ U * x ^ (2 * U)) := by gcongr
      _ = (12 * c * (D : ℝ) ^ U) * x ^ (2 * U) * m k := by ring
      _ ≤ x ^ E * x ^ (2 * U) * x ^ (D * (k + 1)) := by gcongr
      _ = m (k + 1) := by rw [hmk1, ← pow_add, hD]; ring_nf
  refine ⟨4 * D, r, t, hrt, fun k ↦ ?_, fun k ↦ ?_, hmin, hrep⟩
  · have h1 := hmt (k + 1)
    have h2 := ht3 k
    have h3 := hgrow k
    have : (2 * t k : ℝ) < t (k + 1) := by
      have : ((m (k + 1) : ℕ) : ℝ) < 2 * t (k + 1) := by exact_mod_cast h1
      linarith
    exact_mod_cast this
  · have htm : t k ≤ m (k + 1) := by
      have : (t k : ℝ) ≤ m (k + 1) := by
        have h2 := ht3 k
        have h3 := hgrow k
        have : (0 : ℝ) ≤ c * (m k : ℝ) * Real.log (m k) ^ u :=
          mul_nonneg (mul_nonneg hc0.le (Nat.cast_nonneg _))
            (Real.rpow_nonneg (Real.log_natCast_nonneg _) _)
        linarith
      exact_mod_cast this
    refine htm.trans ?_
    calc m (k + 1) = (2 * (k + 1) + 2) ^ (D * (k + 1 + 1)) := rfl
      _ ≤ ((2 * k + 2) ^ 2) ^ (D * (k + 1 + 1)) := Nat.pow_le_pow_left (by nlinarith) _
      _ = (2 * k + 2) ^ (2 * (D * (k + 1 + 1))) := by rw [← pow_mul]
      _ ≤ (2 * k + 2) ^ (4 * D * (k + 1)) := Nat.pow_le_pow_right (by omega) (by nlinarith)

end Function
