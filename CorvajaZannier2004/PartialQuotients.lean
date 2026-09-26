/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import CorvajaZannier2004.PseudoPisot
public import CorvajaZannier2004.QuadraticIrrational
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Topology.Instances.Real.Lemmas

-- Used only inside proofs.
import ArithmeticHeights.Absolute
import CorvajaZannier2004.Conjugates
import CorvajaZannier2004.GaloisSetting
import CorvajaZannier2004.IntegralPowerSums
import CorvajaZannier2004.MainTheorem
import CorvajaZannier2004.PisotPowers
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Lemma 5 of Corvaja–Zannier: the partial quotients of `αⁿ`

**Lemma 5** (Corvaja–Zannier 2004, p. 10). Let `α > 1` be a real quadratic irrational, not the
square root of a rational number, and `aᵢ(n)` the partial quotients of `αⁿ`. Then either `α` is
a Pisot number, or `log aᵢ(n) / n → 0` for every `i ≥ 1`. For `α` the square root of a rational,
the same holds along the odd `n`.

## Main results

* `Real.cfDen_le_prod`: `qₖ ≤ ∏_{1 ≤ i ≤ k} (aᵢ + 1)`, from the recurrence (4.2).
* `Real.isPisot_of_exp_le_cfQuot`: the heart of the proof — a partial quotient `a_h(n) ≥ e^{δn}`
  with `log q_{h-1}(n) = o(n)`, for infinitely many `n`, makes `α` a Pisot number.
* `Real.isPisot_or_tendsto_log_cfQuot`, `Real.isPisot_or_tendsto_log_cfQuot_odd`: Lemma 5.

## Implementation notes

⚠ **The trace does not vanish, for a simpler reason.** The paper excludes `Tr(q αⁿ) = 0` because
`α` is not the square root of a rational. Here the pseudo-Pisot `q αⁿ` has its conjugate
`q α'ⁿ` inside the unit disc, so `|α'| < 1 < α` and `αⁿ + α'ⁿ ≠ 0`. In particular the square-root
case needs no separate argument: there `q αⁿ` (`n` odd) is never pseudo-Pisot.

## References

P. Corvaja and U. Zannier, Acta Math. **193** (2004), 175–191, Lemma 5.
-/

@[expose] public section

open Filter Topology Module IntermediateField NumberField

namespace Real

variable {α : ℝ}

/-- **The denominators of the convergents** are at most `∏_{1 ≤ i ≤ k} (aᵢ + 1)`. -/
theorem cfDen_le_prod {y : ℝ} (hy : Irrational y) (k : ℕ) :
    cfDen y (k + 2) ≤ ∏ i ∈ Finset.Icc 1 k, (cfQuot y i + 1) ∧
      cfDen y (k + 1) ≤ ∏ i ∈ Finset.Icc 1 k, (cfQuot y i + 1) := by
  induction k with
  | zero => simp [cfDen]
  | succ k ih =>
    have hP : 1 ≤ ∏ i ∈ Finset.Icc 1 k, (cfQuot y i + 1) := by
      have := Finset.prod_pos (s := Finset.Icc 1 k) (f := fun i ↦ cfQuot y i + 1) fun i hi ↦ by
        have := one_le_cfQuot hy (n := i) (Finset.mem_Icc.mp hi).1
        omega
      omega
    have ha := one_le_cfQuot hy (n := k + 1) k.succ_pos
    rw [Finset.prod_Icc_succ_top (by omega)]
    have h0 := cfDen_nonneg hy (k + 2)
    refine ⟨?_, ?_⟩
    · rw [show k + 1 + 2 = k + 3 by ring, show k + 3 = (k + 1) + 2 from rfl, cfDen_succ_succ]
      nlinarith [ih.1, ih.2, cfDen_nonneg hy (k + 1)]
    · rw [show k + 1 + 1 = k + 2 by ring]
      nlinarith [ih.1]

/-- **The heart of Lemma 5.** Let `α > 1` be a quadratic irrational, `h ≥ 1`, `δ > 0`, and `Ξ` an
infinite set of `n` with `αⁿ` irrational, `a_h(αⁿ) ≥ e^{δn}` and `log q_{h-1}(αⁿ) = o(n)`. Then
`α` is a Pisot number. By (4.1), `‖q_{h-1} αⁿ‖ < H(αⁿ)^{-ε} q_{h-1}^{-2-ε}`; the Main Theorem makes
`q_{h-1} αⁿ` pseudo-Pisot for all but finitely many `n ∈ Ξ`, which puts `α'` in the unit disc,
and Lemma 4 makes `α` an algebraic integer. -/
theorem isPisot_of_exp_le_cfQuot (hα : IsQuadraticIrrational α) (h1 : 1 < α) {h : ℕ}
    (hh : 1 ≤ h) {δ : ℝ} (hδ : 0 < δ) {Ξ : Set ℕ} (hΞ : Ξ.Infinite)
    (hirr : ∀ n ∈ Ξ, Irrational (α ^ n))
    (hbig : ∀ n ∈ Ξ, Real.exp (δ * n) ≤ cfQuot (α ^ n) h)
    (hden : ∀ η : ℝ, 0 < η → {n ∈ Ξ | Real.exp (η * n) < cfDen (α ^ n) (h + 1)}.Finite) :
    IsPisot α := by
  classical
  have hα0 : 0 < α := zero_lt_one.trans h1
  have halg : IsAlgebraic ℚ α := hα.isIntegral.isAlgebraic
  set α' := quadConj α with hα'
  -- the conjugates of the powers
  have hpowq : ∀ n ∈ Ξ, IsQuadraticIrrational (α ^ n) ∧ quadConj (α ^ n) = α' ^ n :=
    fun n hn ↦ hα.quadConj_pow (hirr n hn)
  -- the exponents
  set H := NumberField.absMulHeight₁ α with hHdef
  have hH1 : 1 ≤ H := NumberField.one_le_absMulHeight₁ α
  have hH0 : 0 < H := zero_lt_one.trans_le hH1
  have hLH : 0 ≤ Real.log H := Real.log_nonneg hH1
  set ε := δ / (2 * (Real.log H + 1)) with hεdef
  have hε : 0 < ε := by positivity
  have hεH : ε * Real.log H ≤ δ / 2 := by
    rw [hεdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set η := δ / (4 * (1 + ε)) with hηdef
  have hη : 0 < η := by positivity
  -- the Main Theorem, for `Γ = ⟨α⟩`, `δ = 1`, `q = q_{h-1}(n)`
  set u : ℝˣ := Units.mk0 α hα0.ne' with hu
  set Γ := Subgroup.zpowers u with hΓdef
  have hΓ : Γ.FG :=
    (Subgroup.fg_iff _).mpr ⟨{u}, (Subgroup.zpowers_eq_closure u).symm, Set.finite_singleton u⟩
  have hΓalg : ∀ v ∈ Γ, IsAlgebraic ℚ (v : ℝ) := by
    rintro v ⟨k, rfl⟩
    simp only [Units.val_zpow_eq_zpow_val, hu, Units.val_mk0]
    rcases k with k | k
    · simpa using halg.pow k
    · simpa [zpow_negSucc] using (halg.pow (k + 1)).inv
  have hfin := finite_setOf_not_isPseudoPisot hΓ hΓalg isAlgebraic_one one_ne_zero hε
  set q : ℕ → ℤ := fun n ↦ cfDen (α ^ n) (h + 1) with hq
  set g : ℕ → ℤ × Γ := fun n ↦ (q n, ⟨u ^ n, Subgroup.pow_mem _ (Subgroup.mem_zpowers u) n⟩)
    with hg
  have hgval : ∀ n, (((g n).2 : ℝˣ) : ℝ) = α ^ n := fun n ↦ by simp [hg, hu]
  have hginj : g.Injective := fun n₁ n₂ h12 ↦ by
    have := congrArg (fun p : ℤ × Γ ↦ ((p.2 : ℝˣ) : ℝ)) h12
    simp only [hgval] at this
    exact pow_right_injective₀ hα0 h1.ne' this
  have hbad : {n ∈ Ξ | 1 ≤ n ∧ (q n : ℝ) ≤ Real.exp (η * n) ∧
      ¬ IsPseudoPisot (q n * α ^ n)}.Finite := by
    refine (hfin.preimage hginj.injOn).subset fun n hn ↦ ?_
    obtain ⟨hnΞ, hn1, hqn, hPP⟩ := hn
    have hq1 : (1 : ℝ) ≤ q n := by exact_mod_cast one_le_cfDen (hirr n hnΞ) (by omega)
    have hq0 : (0 : ℝ) < q n := zero_lt_one.trans_le hq1
    have hx1 : 1 < α ^ n := one_lt_pow₀ h1 (by omega)
    have hfr : finrank ℚ ℚ⟮α ^ n⟯ = 2 := by
      obtain ⟨a, b, c, ha, hab⟩ := (hpowq n hnΞ).1.2
      rw [adjoin.finrank (hpowq n hnΞ).1.isIntegral, (hpowq n hnΞ).1.minpoly_eq ha hab,
        Polynomial.natDegree_quadratic one_ne_zero]
    have h1' : (((g n).1 : ℤ) : ℝ) = q n := rfl
    have hfr' : finrank ℚ ℚ⟮(((g n).2 : ℝˣ) : ℝ)⟯ = 2 := by rw [hgval n]; exact hfr
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [hgval, h1', one_mul, hfr']
    · rw [abs_of_pos (by positivity)]
      nlinarith
    · exact hPP
    · refine abs_pos.mpr (sub_ne_zero.mpr fun heq ↦ ?_)
      have hirrq : Irrational (q n * α ^ n) := (hirr n hnΞ).intCast_mul (by
        exact_mod_cast hq0.ne')
      exact hirrq.ne_int _ heq
    · -- the approximation (4.1)
      set x := α ^ n with hx
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hh
      have happ := abs_sub_cfNum_div_cfDen_le (hirr n hnΞ) m
      rw [show m + 2 = 1 + m + 1 by ring, show m + 1 = 1 + m by ring] at happ
      have ha := hbig n hnΞ
      have hapos : 0 < Real.exp (δ * n) := Real.exp_pos _
      set p := cfNum x (1 + m + 1)
      have hround : |q n * x - round (q n * x)| ≤ 1 / (q n * Real.exp (δ * n)) := by
        calc |q n * x - round (q n * x)| ≤ |q n * x - p| := round_le _ _
          _ = q n * |x - p / q n| := by
              rw [← abs_of_pos hq0, ← abs_mul, abs_of_pos hq0]
              congr 1
              field_simp
          _ ≤ q n * (1 / ((q n) ^ 2 * cfQuot x (1 + m))) := by gcongr
          _ = 1 / (q n * cfQuot x (1 + m)) := by field_simp
          _ ≤ 1 / (q n * Real.exp (δ * n)) := by gcongr
      refine hround.trans_lt ?_
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      -- `q^{1+ε} ≤ e^{δn/4}` and `H(x)^{-ε} ≥ e^{-δn/2}`
      have hqpow : (q n : ℝ) ^ ((1 : ℝ) + ε) ≤ Real.exp (δ * n / 4) := by
        calc (q n : ℝ) ^ ((1 : ℝ) + ε) ≤ Real.exp (η * n) ^ ((1 : ℝ) + ε) :=
              Real.rpow_le_rpow hq0.le hqn (by positivity)
          _ = Real.exp (δ * n / 4) := by
              rw [← Real.exp_mul, hηdef]
              congr 1
              field_simp
      have hHx : Real.exp (-(δ * n / 2)) ≤ NumberField.absMulHeight₁ x ^ (-ε) := by
        rw [hx, NumberField.absMulHeight₁_pow halg.isIntegral n, ← hHdef,
          ← Real.rpow_natCast, ← Real.rpow_mul hH0.le, Real.rpow_def_of_pos hH0]
        refine Real.exp_le_exp.mpr ?_
        have : Real.log H * (n * -ε) = -(ε * Real.log H * n) := by ring
        rw [this, neg_le_neg_iff]
        nlinarith
      have hsplit : (q n : ℝ) ^ (-((2 : ℕ) : ℝ) - ε) =
          ((q n : ℝ) * (q n : ℝ) ^ ((1 : ℝ) + ε))⁻¹ := by
        rw [← Real.rpow_one_add' hq0.le (by positivity), ← Real.rpow_neg hq0.le]
        congr 1
        push_cast
        ring
      rw [abs_of_pos hq0, hsplit]
      calc 1 / (q n * Real.exp (δ * n))
          < Real.exp (-(δ * n / 2)) * (q n * Real.exp (δ * n / 4))⁻¹ := by
            have e : Real.exp (-(δ * n / 2)) * (q n * Real.exp (δ * n / 4))⁻¹ =
                1 / (q n * Real.exp (δ * n / 4 + δ * n / 2)) := by
              rw [Real.exp_add, Real.exp_neg]
              field_simp
            rw [e]
            exact one_div_lt_one_div_of_lt (by positivity)
              (mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (by nlinarith)) hq0)
        _ ≤ NumberField.absMulHeight₁ x ^ (-ε) * ((q n : ℝ) * (q n : ℝ) ^ ((1 : ℝ) + ε))⁻¹ :=
            mul_le_mul hHx (inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left hqpow hq0.le))
              (by positivity) (Real.rpow_nonneg (zero_le_one.trans
                (NumberField.one_le_absMulHeight₁ _)) _)
  -- infinitely many pseudo-Pisot `q αⁿ`
  have hgood : {n ∈ Ξ | 1 ≤ n ∧ IsPseudoPisot (q n * α ^ n)}.Infinite := by
    have hsmall : {n ∈ Ξ | ¬ (1 ≤ n ∧ (q n : ℝ) ≤ Real.exp (η * n))}.Finite := by
      refine ((Set.finite_Iio 1).union (hden η hη)).subset fun n hn ↦ ?_
      rcases not_and_or.mp hn.2 with h0 | h0
      · exact Or.inl (Set.mem_Iio.mpr (not_le.mp h0))
      · exact Or.inr ⟨hn.1, not_le.mp h0⟩
    refine ((hΞ.sdiff hsmall).sdiff hbad).mono fun n hn ↦ ?_
    obtain ⟨⟨hnΞ, hns⟩, hnb⟩ := hn
    have hns' : 1 ≤ n ∧ (q n : ℝ) ≤ Real.exp (η * n) := by
      by_contra hc
      exact hns ⟨hnΞ, hc⟩
    refine ⟨hnΞ, hns'.1, ?_⟩
    by_contra hc
    exact hnb ⟨hnΞ, hns'.1, hns'.2, hc⟩
  -- the conjugate `q α'ⁿ` lies in the unit disc, so `|α'| < 1`
  have hconj : ∀ n ∈ Ξ, 1 ≤ n → IsPseudoPisot (q n * α ^ n) →
      IsQuadraticIrrational (q n * α ^ n) ∧ quadConj (q n * α ^ n) = q n * α' ^ n ∧
        |(q n : ℝ) * α' ^ n| < 1 := by
    intro n hnΞ hn1 hPP
    have hq0 : (q n : ℚ) ≠ 0 := by
      exact_mod_cast (zero_lt_one.trans_le (one_le_cfDen (hirr n hnΞ) (n := h + 1)
        (by omega))).ne'
    have hmob := (hpowq n hnΞ).1.mob (p := q n) (q := 0) (r := 0) (s := 1) (by simpa using hq0)
    simp only [Rat.cast_intCast, Rat.cast_zero, Rat.cast_one, add_zero, zero_mul, zero_add,
      div_one, (hpowq n hnΞ).2] at hmob
    refine ⟨hmob.1, hmob.2, ?_⟩
    have hmem : ((q n * α' ^ n : ℝ) : ℂ) ∈ (minpoly ℚ (q n * α ^ n)).aroots ℂ := by
      rw [hmob.1.aroots_minpoly, hmob.2]
      simp
    have hne : ((q n * α' ^ n : ℝ) : ℂ) ≠ ((q n * α ^ n : ℝ) : ℂ) := by
      rw [Ne, Complex.ofReal_inj, ← hmob.2]
      exact hmob.1.quadConj_ne
    have := hPP.2.2.1 _ hmem hne
    rwa [Complex.norm_real, Real.norm_eq_abs] at this
  obtain ⟨n₀, ⟨hn₀Ξ, hn₀1, hn₀PP⟩⟩ := hgood.nonempty
  have hα'1 : |α'| < 1 := by
    have h3 := (hconj n₀ hn₀Ξ hn₀1 hn₀PP).2.2
    have hq1 : (1 : ℝ) ≤ q n₀ := by exact_mod_cast one_le_cfDen (hirr n₀ hn₀Ξ) (by omega)
    rw [abs_mul, abs_of_pos (zero_lt_one.trans_le hq1), abs_pow] at h3
    have : |α'| ^ n₀ < 1 := lt_of_le_of_lt (le_mul_of_one_le_left (by positivity) hq1) h3
    exact (pow_lt_one_iff_of_nonneg (abs_nonneg _) (by omega)).mp this
  -- Lemma 4 in a Galois number field containing `α`
  obtain ⟨K, _, _, _, φ, hφ⟩ := exists_isGalois_ringHom_mem_range {(α : ℂ)} (by
    intro z hz
    rw [Finset.mem_singleton.mp hz]
    exact halg.algHom Complex.ofRealHom.toRatAlgHom)
  obtain ⟨a, ha⟩ := hφ _ (Finset.mem_singleton_self _)
  have hφn : ∀ n : ℕ, φ (a ^ n) = ((α ^ n : ℝ) : ℂ) := fun n ↦ by
    rw [map_pow, ha]
    push_cast
    rfl
  have hmin : ∀ n : ℕ, minpoly ℚ (α ^ n) = minpoly ℚ (a ^ n) := fun n ↦ by
    have := minpoly_re_eq φ (y := a ^ n) (by rw [hφn]; exact Complex.ofReal_im _)
    rwa [hφn, Complex.ofReal_re] at this
  set Ξ₁ := {n ∈ Ξ | 1 ≤ n ∧ IsPseudoPisot (q n * α ^ n)} with hΞ₁
  have hint : IsIntegral ℤ a := by
    refine NumberField.isIntegral_of_mul_sum_pow_eq_intCast hgood
      (q := fun n ↦ (q n).toNat) (fun n hn ↦ ?_) (fun η' hη' ↦ ?_) ?_
    · have := one_le_cfDen (hirr n hn.1) (n := h + 1) (by omega)
      simp only [hq]
      omega
    · refine (hden η' hη').subset fun n hn ↦ ⟨hn.1.1, ?_⟩
      have h2 := hn.2
      have hq0 : 0 ≤ q n := (cfDen_nonneg (hirr n hn.1.1) _)
      rwa [show (((q n).toNat : ℕ) : ℝ) = q n by exact_mod_cast Int.toNat_of_nonneg hq0] at h2
    · rintro n ⟨hnΞ, hn1, hPP⟩
      obtain ⟨hqq, hqc, hqlt⟩ := hconj n hnΞ hn1 hPP
      obtain ⟨T, hT⟩ := hPP.2.2.2
      have hq0 : 0 ≤ q n := cfDen_nonneg (hirr n hnΞ) _
      have hqn : (((q n).toNat : ℕ) : K) = (q n : K) := by
        rw [show ((q n).toNat : K) = (((q n).toNat : ℤ) : K) by push_cast; rfl,
          Int.toNat_of_nonneg hq0]
      have hpow : ∑ σ : K ≃ₐ[ℚ] K, σ a ^ n = ∑ σ : K ≃ₐ[ℚ] K, σ (a ^ n) := by simp [map_pow]
      -- `T = q (αⁿ + α'ⁿ)`
      have hTsum : (T : ℂ) = ((q n * α ^ n + q n * α' ^ n : ℝ) : ℂ) := by
        rw [← hT, hqq.aroots_minpoly, hqc]
        simp
      have hsum : φ (∑ σ : K ≃ₐ[ℚ] K, σ (a ^ n)) =
          finrank ℚ⟮a ^ n⟯ K * ((α ^ n + α' ^ n : ℝ) : ℂ) := by
        rw [map_sum_algEquiv, ← hmin, (hpowq n hnΞ).1.aroots_minpoly, (hpowq n hnΞ).2]
        simp
      refine ⟨finrank ℚ⟮a ^ n⟯ K * T, mul_ne_zero ?_ ?_, ?_⟩
      · exact Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
      · -- `|q α'ⁿ| < 1 < q αⁿ`
        intro hT0
        rw [hT0, Int.cast_zero] at hTsum
        have := congrArg Complex.re hTsum
        simp only [Complex.zero_re, Complex.ofReal_re] at this
        have hq1 : (1 : ℝ) ≤ q n := by exact_mod_cast one_le_cfDen (hirr n hnΞ) (by omega)
        have hx1 : 1 < α ^ n := one_lt_pow₀ h1 (by omega)
        have := (abs_lt.mp hqlt).1
        nlinarith
      · rw [hqn, hpow]
        refine φ.injective ?_
        rw [map_mul, hsum, map_intCast, map_intCast]
        push_cast
        rw [hTsum]
        push_cast
        ring
  -- conclusion: `α` is a Pisot number
  have hαint : IsIntegral ℤ α := by
    have h1' : IsIntegral ℤ (φ a) := hint.map φ.toIntAlgHom
    rw [ha] at h1'
    exact (isIntegral_algHom_iff Complex.ofRealHom.toIntAlgHom Complex.ofReal_injective).mp h1'
  refine ⟨h1, hαint, fun z hz hne ↦ ?_⟩
  rw [hα.aroots_minpoly] at hz
  rcases Multiset.mem_cons.mp hz with rfl | hz
  · exact absurd rfl hne
  · rw [Multiset.mem_singleton.mp hz, Complex.norm_real, Real.norm_eq_abs]
    exact hα'1

/-- **Lemma 5 along a set `S` of exponents** at which `αⁿ` is irrational: either `α` is a Pisot
number, or `log aᵢ(αⁿ) / n → 0` along `S` for every `i ≥ 1`. -/
theorem isPisot_or_tendsto_log_cfQuot_of_mem (hα : IsQuadraticIrrational α) (h1 : 1 < α)
    {S : Set ℕ} (hS : ∀ n ∈ S, Irrational (α ^ n)) :
    IsPisot α ∨ ∀ i, 0 < i →
      Tendsto (fun n : ℕ ↦ Real.log (cfQuot (α ^ n) i) / n) (atTop ⊓ 𝓟 S) (𝓝 0) := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hPis, hex⟩ := hcon
  set f : ℕ → ℕ → ℝ := fun i n ↦ Real.log (cfQuot (α ^ n) i) / n with hf
  set h := Nat.find hex with hhdef
  obtain ⟨hh, hnt⟩ := Nat.find_spec hex
  have hmin : ∀ i, 0 < i → i < h → Tendsto (f i) (atTop ⊓ 𝓟 S) (𝓝 0) := fun i hi0 hih ↦ by
    by_contra hc
    exact Nat.find_min hex hih ⟨hi0, hc⟩
  -- `f` is nonnegative on `S`
  have hf0 : ∀ i n, n ∈ S → 0 < i → 0 ≤ f i n := fun i n hn hi ↦ by
    have : (1 : ℝ) ≤ cfQuot (α ^ n) i := by exact_mod_cast one_le_cfQuot (hS n hn) hi
    exact div_nonneg (Real.log_nonneg this) (Nat.cast_nonneg n)
  -- infinitely many `n ∈ S` with `f h n ≥ δ`
  obtain ⟨δ, hδ, hfreq⟩ : ∃ δ > 0, ∃ᶠ n in atTop, n ∈ S ∧ δ ≤ |f h n| := by
    rw [Metric.tendsto_nhds] at hnt
    push Not at hnt
    obtain ⟨δ, hδ, hfr⟩ := hnt
    refine ⟨δ, hδ, frequently_inf_principal.mp (hfr.mono fun n hn ↦ ?_)⟩
    rwa [Real.dist_eq, sub_zero] at hn
  set Ξ := {n | n ∈ S ∧ δ ≤ |f h n|} ∩ {n | 1 ≤ n} with hΞdef
  have hΞ : Ξ.Infinite :=
    (Nat.frequently_atTop_iff_infinite.mp hfreq).sdiff (Set.finite_lt_nat 1) |>.mono
      fun n hn ↦ ⟨hn.1, Nat.one_le_iff_ne_zero.mpr (by simpa using hn.2)⟩
  refine hPis (isPisot_of_exp_le_cfQuot hα h1 hh hδ hΞ (fun n hn ↦ hS n hn.1.1)
    (fun n hn ↦ ?_) (fun η hη ↦ ?_))
  · -- `a_h(n) ≥ e^{δn}`
    obtain ⟨⟨hnS, hnδ⟩, hn1⟩ := hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (hn1 : 1 ≤ n)
    rw [abs_of_nonneg (hf0 h n hnS hh), hf, le_div_iff₀ hn0] at hnδ
    have hapos : (0 : ℝ) < cfQuot (α ^ n) h := by
      exact_mod_cast zero_lt_one.trans_le (one_le_cfQuot (hS n hnS) hh)
    calc Real.exp (δ * n) ≤ Real.exp (Real.log (cfQuot (α ^ n) h)) := Real.exp_le_exp.mpr hnδ
      _ = _ := Real.exp_log hapos
  · -- `q_{h-1}(n) ≤ e^{ηn}` eventually, from `aᵢ(n) = e^{o(n)}` for `1 ≤ i < h`
    set η₁ := η / (2 * h) with hη₁
    have hη₁pos : 0 < η₁ := by positivity
    have hev : ∀ᶠ n in atTop ⊓ 𝓟 S, ∀ i ∈ Finset.Icc 1 (h - 1), f i n < η₁ := by
      rw [eventually_all_finset]
      intro i hi
      obtain ⟨hi1, hih⟩ := Finset.mem_Icc.mp hi
      exact (hmin i hi1 (by omega)).eventually (gt_mem_nhds hη₁pos)
    rw [eventually_inf_principal, eventually_atTop] at hev
    obtain ⟨N, hN⟩ := hev
    obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, (2 : ℝ) ^ h ≤ Real.exp (η * N₀ / 2) := by
      obtain ⟨N₀, hN₀⟩ := exists_nat_gt (2 * h * Real.log 2 / η)
      refine ⟨N₀, ?_⟩
      rw [← Real.exp_log (by positivity : (0 : ℝ) < 2 ^ h), Real.log_pow]
      refine Real.exp_le_exp.mpr ?_
      rw [div_lt_iff₀ hη] at hN₀
      nlinarith
    refine (Set.finite_lt_nat (max N N₀)).subset fun n hn ↦ ?_
    by_contra hge
    rw [Set.mem_ofPred_eq, not_lt, max_le_iff] at hge
    obtain ⟨⟨⟨hnS, -⟩, hn1⟩, hlt⟩ := hn
    have hn1' : 1 ≤ n := hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1'
    have hirr := hS n hnS
    have hbound := hN n hge.1 hnS
    -- each factor `aᵢ + 1 ≤ 2 e^{η₁ n}`
    have hfac : ∀ i ∈ Finset.Icc 1 (h - 1),
        ((cfQuot (α ^ n) i + 1 : ℤ) : ℝ) ≤ 2 * Real.exp (η₁ * n) := by
      intro i hi
      have hai : (1 : ℝ) ≤ cfQuot (α ^ n) i := by
        exact_mod_cast one_le_cfQuot hirr (Finset.mem_Icc.mp hi).1
      have hlog := hbound i hi
      rw [hf, div_lt_iff₀ hn0] at hlog
      have : (cfQuot (α ^ n) i : ℝ) < Real.exp (η₁ * n) := by
        rw [← Real.exp_log (by linarith : (0 : ℝ) < cfQuot (α ^ n) i)]
        exact Real.exp_lt_exp.mpr (by linarith)
      push_cast
      linarith
    have hden := (cfDen_le_prod hirr (h - 1)).1
    rw [show h - 1 + 2 = h + 1 by omega] at hden
    have hden' : (cfDen (α ^ n) (h + 1) : ℝ) ≤ (2 * Real.exp (η₁ * n)) ^ h := by
      calc (cfDen (α ^ n) (h + 1) : ℝ)
          ≤ ((∏ i ∈ Finset.Icc 1 (h - 1), (cfQuot (α ^ n) i + 1) : ℤ) : ℝ) := by
            exact_mod_cast hden
        _ = ∏ i ∈ Finset.Icc 1 (h - 1), ((cfQuot (α ^ n) i + 1 : ℤ) : ℝ) := by push_cast; rfl
        _ ≤ ∏ i ∈ Finset.Icc 1 (h - 1), (2 * Real.exp (η₁ * n)) :=
            Finset.prod_le_prod₀ (fun i hi ↦ by
              have := one_le_cfQuot hirr (n := i) (Finset.mem_Icc.mp hi).1
              positivity) hfac
        _ = (2 * Real.exp (η₁ * n)) ^ (h - 1) := by rw [Finset.prod_const, Nat.card_Icc]; rfl
        _ ≤ (2 * Real.exp (η₁ * n)) ^ h :=
            pow_le_pow_right₀ (by nlinarith [Real.one_le_exp (by positivity : 0 ≤ η₁ * n)])
              (by omega)
    have hexp : (2 * Real.exp (η₁ * n)) ^ h ≤ Real.exp (η * n) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      have h2 : (2 : ℝ) ^ h ≤ Real.exp (η * n / 2) :=
        hN₀.trans (Real.exp_le_exp.mpr (by
          have : (N₀ : ℝ) ≤ n := by exact_mod_cast hge.2
          nlinarith))
      have h3 : Real.exp (h * (η₁ * n)) = Real.exp (η * n / 2) := by
        have hh' : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
        congr 1
        rw [hη₁]
        field_simp
      rw [h3]
      calc (2 : ℝ) ^ h * Real.exp (η * n / 2) ≤ Real.exp (η * n / 2) * Real.exp (η * n / 2) :=
            mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
        _ = Real.exp (η * n) := by rw [← Real.exp_add]; ring_nf
    exact absurd hlt (not_lt.mpr (hden'.trans hexp))

/-- **Lemma 5 of Corvaja–Zannier** (p. 10): for a real quadratic irrational `α > 1`, not the
square root of a rational number, either `α` is a Pisot number or `log aᵢ(αⁿ) / n → 0` for every
`i ≥ 1`. -/
theorem isPisot_or_tendsto_log_cfQuot (hα : IsQuadraticIrrational α) (h1 : 1 < α)
    (hsq : ∀ r : ℚ, α ^ 2 ≠ r) :
    IsPisot α ∨ ∀ i, 0 < i →
      Tendsto (fun n : ℕ ↦ Real.log (cfQuot (α ^ n) i) / n) atTop (𝓝 0) := by
  have hS : ∀ n ∈ {n : ℕ | 0 < n}, Irrational (α ^ n) := fun n hn hq ↦ by
    obtain ⟨r, hr⟩ := hq
    obtain ⟨s, hs⟩ := hα.exists_sq_eq_of_pow_eq hn hr.symm
    exact hsq s hs
  refine (isPisot_or_tendsto_log_cfQuot_of_mem hα h1 hS).imp id fun h i hi ↦
    (h i hi).mono_left (le_inf le_rfl (le_principal_iff.mpr (eventually_gt_atTop 0)))

/-- **Lemma 5 of Corvaja–Zannier** (p. 10), along the odd exponents: for a real quadratic
irrational `α > 1`, either `α` is a Pisot number or `log aᵢ(α²ⁿ⁺¹) / (2n + 1) → 0` for every
`i ≥ 1`. The paper states it for `α` the square root of a rational number; it holds for every
quadratic irrational. -/
theorem isPisot_or_tendsto_log_cfQuot_odd (hα : IsQuadraticIrrational α) (h1 : 1 < α) :
    IsPisot α ∨ ∀ i, 0 < i → Tendsto (fun n : ℕ ↦ Real.log (cfQuot (α ^ (2 * n + 1)) i) /
      ((2 * n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hS : ∀ n ∈ {n : ℕ | Odd n}, Irrational (α ^ n) := by
    rintro n ⟨k, rfl⟩ ⟨r, hr⟩
    obtain ⟨s, hs⟩ := hα.exists_sq_eq_of_pow_eq (by omega) hr.symm
    have hs0 : (s : ℝ) ≠ 0 := by
      rw [← hs]
      exact pow_ne_zero _ (zero_lt_one.trans h1).ne'
    have : α = r / s ^ k := by
      rw [eq_div_iff (pow_ne_zero _ hs0), ← hs, ← pow_mul, hr]
      ring
    exact hα.1 ⟨r / s ^ k, by rw [this]; push_cast; rfl⟩
  have hmap : Tendsto (fun n : ℕ ↦ 2 * n + 1) atTop (atTop ⊓ 𝓟 {n | Odd n}) :=
    tendsto_inf.mpr ⟨tendsto_atTop_mono (f := id) (fun n ↦ by simp only [id]; omega) tendsto_id,
      tendsto_principal.mpr (Eventually.of_forall fun n ↦ ⟨n, by ring⟩)⟩
  exact (isPisot_or_tendsto_log_cfQuot_of_mem hα h1 hS).imp id fun h i hi ↦
    (h i hi).comp hmap

end Real
