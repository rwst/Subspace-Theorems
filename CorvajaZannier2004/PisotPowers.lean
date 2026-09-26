/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import CorvajaZannier2004.PseudoPisot
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs

-- Used only inside proofs.
import ArithmeticHeights.Absolute
import CorvajaZannier2004.Conjugates
import CorvajaZannier2004.GaloisSetting
import CorvajaZannier2004.IntegralPowerSums
import CorvajaZannier2004.MainTheorem
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Order.Filter.Cofinite
import Mathlib.RingTheory.Trace.Basic

/-!
# Theorem 1 of Corvaja–Zannier: Mahler's question on the powers of an algebraic number

**Theorem 1** (Corvaja–Zannier 2004, p. 1). Let `α > 1` be real algebraic and `0 < l < 1`. If
`‖αⁿ‖ < lⁿ` for infinitely many `n`, then some power `α ^ d` is a Pisot number; in particular `α`
is an algebraic integer. This answers a question of Mahler.

## Main results

* `NumberField.map_sum_algEquiv`: in a Galois number field, `∑_σ σ(y)` is `[K : ℚ(y)]` times the
  sum of the conjugates of `y`.
* `exists_isPisot_pow_of_frequently`: Theorem 1.

## Implementation notes

⚠ **Why the trace does not vanish.** The paper applies Lemma 4 to the pseudo-Pisot `αⁿ`, which
"in particular have non-zero integral trace". The trace is `αⁿ` plus conjugates of modulus `< 1`,
so it is positive as soon as `αⁿ` exceeds the number of conjugates; that is how it is proved here,
with the sum over the Galois group in place of the trace.

⚠ **An integral power.** If `αⁿ ∈ ℤ` for some `n ≥ 1`, then `αⁿ` is a rational integer `> 1`,
Pisot by convention, and the Main Theorem is not needed; otherwise `0 < ‖αⁿ‖` for every `n ≥ 1`.

## References

P. Corvaja and U. Zannier, Acta Math. **193** (2004), 175–191, Theorem 1 and its proof, p. 7.
-/

@[expose] public section

open Filter Module IntermediateField NumberField

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]

/-- **The sum over the Galois group is a multiple of the trace**: `φ (∑_σ σ(y))` is
`[K : ℚ(y)]` times the sum of the complex conjugates of `y`. -/
theorem map_sum_algEquiv (φ : K →+* ℂ) (y : K) :
    φ (∑ σ : K ≃ₐ[ℚ] K, σ y) = finrank ℚ⟮y⟯ K * ((minpoly ℚ y).aroots ℂ).sum := by
  rw [← trace_eq_sum_automorphisms, trace_eq_trace_adjoin,
    ← IntermediateField.AdjoinSimple.trace_gen_eq_sum_roots (F := ℂ) y (IsAlgClosed.splits _)]
  have hφ : ∀ s : ℚ, φ (algebraMap ℚ K s) = algebraMap ℚ ℂ s := fun s ↦ by simp
  rw [hφ, nsmul_eq_mul, map_mul, map_natCast]

end NumberField

/-- **Theorem 1 of Corvaja–Zannier** (p. 1), answering a question of Mahler. Let `α > 1` be a real
algebraic number and `0 < l < 1`. If `‖αⁿ‖ < lⁿ` for infinitely many `n`, then some power
`α ^ n`, `n ≥ 1`, is a Pisot number, and `α` is an algebraic integer. -/
theorem exists_isPisot_pow_of_frequently {α l : ℝ} (hα : 1 < α) (halg : IsAlgebraic ℚ α)
    (hl0 : 0 < l) (hl1 : l < 1) (h : ∃ᶠ n : ℕ in atTop, |α ^ n - round (α ^ n)| < l ^ n) :
    (∃ n, 0 < n ∧ IsPisot (α ^ n)) ∧ IsIntegral ℤ α := by
  classical
  have hα0 : 0 < α := zero_lt_one.trans hα
  -- an integral power is a Pisot number
  by_cases hZ : ∃ n, 0 < n ∧ α ^ n = round (α ^ n)
  · obtain ⟨n, hn, hN⟩ := hZ
    have hαN : α ^ n = ((round (α ^ n) : ℚ) : ℝ) := by rw [hN]; push_cast; simp
    have hint : IsIntegral ℤ (α ^ n) := by
      have := isIntegral_algebraMap (R := ℤ) (A := ℝ) (x := round (α ^ n))
      rwa [algebraMap_int_eq, eq_intCast, ← hN] at this
    refine ⟨⟨n, hn, one_lt_pow₀ hα hn.ne', hint, fun z hz hne ↦ ?_⟩, IsIntegral.of_pow hn hint⟩
    rw [hαN, aroots_minpoly_ratCast, Multiset.mem_singleton] at hz
    rw [hαN] at hne
    exact absurd hz hne
  push Not at hZ
  -- a Galois number field containing `α`
  obtain ⟨K, _, _, _, φ, hφ⟩ := exists_isGalois_ringHom_mem_range {(α : ℂ)} (by
    intro x hx
    rw [Finset.mem_singleton.mp hx]
    exact halg.algHom Complex.ofRealHom.toRatAlgHom)
  obtain ⟨a, ha⟩ := hφ _ (Finset.mem_singleton_self _)
  have hφn : ∀ n : ℕ, φ (a ^ n) = ((α ^ n : ℝ) : ℂ) := fun n ↦ by
    rw [map_pow, ha]
    push_cast
    rfl
  have hmin : ∀ n : ℕ, minpoly ℚ (α ^ n) = minpoly ℚ (a ^ n) := fun n ↦ by
    have := minpoly_re_eq φ (y := a ^ n) (by rw [hφn]; exact Complex.ofReal_im _)
    rwa [hφn, Complex.ofReal_re] at this
  -- the exponent `ε`, with `lⁿ ≤ H(αⁿ) ^ (-ε)`
  set H := absMulHeight₁ α with hHdef
  have hH1 : 1 ≤ H := one_le_absMulHeight₁ α
  have hL : Real.log l < 0 := Real.log_neg hl0 hl1
  have hLH : 0 ≤ Real.log H := Real.log_nonneg hH1
  set ε := -Real.log l / (Real.log H + 1) with hεdef
  have hε : 0 < ε := div_pos (neg_pos.mpr hL) (by linarith)
  have hlH : ∀ n : ℕ, l ^ n ≤ absMulHeight₁ (α ^ n) ^ (-ε) := by
    intro n
    have hH0 : 0 < H := zero_lt_one.trans_le hH1
    rw [absMulHeight₁_pow halg.isIntegral n, ← hHdef, ← Real.rpow_natCast H n,
      ← Real.rpow_mul hH0.le, mul_comm, Real.rpow_mul hH0.le, Real.rpow_natCast]
    refine pow_le_pow_left₀ hl0.le ?_ n
    rw [Real.rpow_def_of_pos hH0, ← Real.exp_log hl0]
    refine Real.exp_le_exp.mpr ?_
    have hid : Real.log H * -ε = Real.log l - Real.log l / (Real.log H + 1) := by
      rw [hεdef]
      field_simp
      ring
    rw [hid]
    have : Real.log l / (Real.log H + 1) < 0 := div_neg_of_neg_of_pos hL (by linarith)
    linarith
  -- the Main Theorem, for `Γ = ⟨α⟩`, `δ = 1`, `q = 1`
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
  set g : ℕ → ℤ × Γ := fun n ↦ (1, ⟨u ^ n, Subgroup.pow_mem _ (Subgroup.mem_zpowers u) n⟩)
    with hg
  have hgval : ∀ n, (((g n).2 : ℝˣ) : ℝ) = α ^ n := fun n ↦ by simp [hg, hu]
  have hginj : g.Injective := fun n₁ n₂ h12 ↦ by
    have := congrArg (fun p : ℤ × Γ ↦ ((p.2 : ℝˣ) : ℝ)) h12
    simp only [hgval] at this
    exact pow_right_injective₀ hα0 hα.ne' this
  set F := {n : ℕ | |α ^ n - round (α ^ n)| < l ^ n} with hFdef
  have hF : F.Infinite := Nat.frequently_atTop_iff_infinite.mp h
  have hbad : {n ∈ F | 0 < n ∧ ¬ IsPseudoPisot (α ^ n)}.Finite := by
    refine (hfin.preimage hginj.injOn).subset fun n hn ↦ ?_
    obtain ⟨hnF, hn0, hPP⟩ := hn
    have h1 : (((g n).1 : ℤ) : ℝ) = 1 := by simp [hg]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [hgval, h1, mul_one, one_mul, abs_one, Real.one_rpow]
    · rw [abs_of_pos (pow_pos hα0 n)]
      exact one_lt_pow₀ hα hn0.ne'
    · exact hPP
    · exact abs_pos.mpr (sub_ne_zero.mpr (hZ n hn0))
    · exact hnF.trans_le (hlH n)
  -- infinitely many large pseudo-Pisot powers
  set G := Fintype.card (K ≃ₐ[ℚ] K) with hGdef
  have hsmall : {n : ℕ | α ^ n ≤ G}.Finite := by
    refine (Set.finite_Iic ⌈(G : ℝ) / (α - 1)⌉₊).subset fun n hn ↦ ?_
    have hb := one_add_mul_le_pow (a := α - 1) (by linarith) n
    rw [add_sub_cancel] at hb
    have hn' : α ^ n ≤ G := hn
    have hle : (n : ℝ) ≤ G / (α - 1) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    exact Set.mem_Iic.mpr (Nat.cast_le.mp (hle.trans (Nat.le_ceil _)))
  set Ξ := {n ∈ F | 0 < n ∧ IsPseudoPisot (α ^ n) ∧ (G : ℝ) < α ^ n} with hΞdef
  have hΞ : Ξ.Infinite := by
    refine ((hF.sdiff hbad).sdiff (hsmall.union (Set.finite_le_nat 0))).mono fun n hn ↦ ?_
    obtain ⟨⟨hnF, hnb⟩, hns⟩ := hn
    have hn0 : 0 < n := Nat.pos_of_ne_zero fun h0 ↦ hns (Or.inr (le_of_eq h0))
    refine ⟨hnF, hn0, ?_, lt_of_not_ge fun hle ↦ hns (Or.inl hle)⟩
    by_contra hPP
    exact hnb ⟨hnF, hn0, hPP⟩
  -- Lemma 4: `a` is an algebraic integer
  have hint : IsIntegral ℤ a := by
    refine isIntegral_of_mul_sum_pow_eq_intCast hΞ (q := fun _ ↦ 1) (fun _ _ ↦ one_pos)
      (fun η hη ↦ Set.finite_empty.subset fun n hn ↦ ?_) ?_
    · have h2 := hn.2
      push_cast at h2
      exact absurd h2 (not_lt.mpr (Real.one_le_exp (by positivity)))
    rintro n ⟨-, hn0, hPP, hG⟩
    obtain ⟨T, hT⟩ := hPP.2.2.2
    have hpow : ∑ σ : K ≃ₐ[ℚ] K, σ a ^ n = ∑ σ : K ≃ₐ[ℚ] K, σ (a ^ n) := by simp [map_pow]
    have hsum : φ (∑ σ : K ≃ₐ[ℚ] K, σ (a ^ n)) = ((finrank ℚ⟮a ^ n⟯ K * T : ℤ) : ℂ) := by
      rw [map_sum_algEquiv, ← hmin, hT]
      push_cast
      ring
    refine ⟨finrank ℚ⟮a ^ n⟯ K * T, fun h0 ↦ ?_, ?_⟩
    · -- the sum is positive: `αⁿ` plus conjugates of modulus `< 1`
      rw [h0, Int.cast_zero, map_sum] at hsum
      have hre := congrArg Complex.re hsum
      rw [Complex.re_sum, Complex.zero_re,
        ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : K ≃ₐ[ℚ] K))] at hre
      have hid : (φ ((1 : K ≃ₐ[ℚ] K) (a ^ n))).re = α ^ n := by
        rw [AlgEquiv.one_apply, hφn, Complex.ofReal_re]
      have hterm : ∀ σ : K ≃ₐ[ℚ] K, -1 ≤ (φ (σ (a ^ n))).re := fun σ ↦ by
        by_cases heq : φ (σ (a ^ n)) = ((α ^ n : ℝ) : ℂ)
        · rw [heq, Complex.ofReal_re]
          linarith [pow_pos hα0 n]
        · have hmem : φ (σ (a ^ n)) ∈ (minpoly ℚ (α ^ n)).aroots ℂ := by
            rw [hmin, aroots_minpoly_eq_map φ]
            refine Multiset.mem_map_of_mem _ ((Polynomial.mem_aroots).mpr
              ⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral _), ?_⟩)
            rw [Polynomial.aeval_algEquiv, AlgHom.comp_apply, minpoly.aeval, map_zero]
          have hlt := hPP.2.2.1 _ hmem heq
          linarith [(abs_le.mp ((Complex.abs_re_le_norm _).trans hlt.le)).1]
      have hrest : -(G : ℝ) ≤ ∑ σ ∈ Finset.univ.erase (1 : K ≃ₐ[ℚ] K), (φ (σ (a ^ n))).re :=
        calc -(G : ℝ) ≤ -((Finset.univ.erase (1 : K ≃ₐ[ℚ] K)).card : ℝ) :=
              neg_le_neg (by exact_mod_cast (Finset.card_erase_le).trans_eq Finset.card_univ)
          _ = ∑ σ ∈ Finset.univ.erase (1 : K ≃ₐ[ℚ] K), (-1 : ℝ) := by simp
          _ ≤ _ := Finset.sum_le_sum fun σ _ ↦ hterm σ
      linarith
    · rw [Nat.cast_one, one_mul, hpow]
      exact φ.injective (by rw [hsum, map_intCast])
  -- conclusion
  have hαint : IsIntegral ℤ α := by
    have h1 : IsIntegral ℤ (φ a) := hint.map φ.toIntAlgHom
    rw [ha] at h1
    exact (isIntegral_algHom_iff Complex.ofRealHom.toIntAlgHom Complex.ofReal_injective).mp h1
  obtain ⟨n, -, hn0, hPP, -⟩ := hΞ.nonempty
  exact ⟨⟨n, hn0, one_lt_pow₀ hα hn0.ne', hαint.pow n, hPP.2.2.1⟩, hαint⟩
