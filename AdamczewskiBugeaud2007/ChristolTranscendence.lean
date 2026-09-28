/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import AdamczewskiBugeaud2007.AutomaticComplexity
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.PowerSeries.Basic

-- Used only inside proofs.
import AdamczewskiBugeaud2007.Christol
import AdamczewskiBugeaud2007.RationalPowerSeries
import DiophantineApproximation.DigitExpansions
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination

/-!
# Theorem 7: base-`b` numbers and power series over `𝔽_p` with the same digits

**Adamczewski–Bugeaud 2007, Theorem 7, corrected.** Let `b ≥ 2` and `p` prime, and let `u` be a
sequence with `u_k < min(b, p)`. The power series `∑ u_k X ^ k ∈ 𝔽_p⟦X⟧` and the real number
`∑ u_k / b ^ k` are both algebraic (over `𝔽_p(X)` and `ℚ`) if and only if both are rational.

The proof is the paper's. By Christol's theorem the algebraic power series has a `p`-automatic
coefficient sequence; since `u_k < p` the coefficients determine `u`, so `u` is automatic. Since
`u_k < b`, `u` is a sequence of base-`b` digits, and by Theorem 2 the real number is rational or
transcendental. A rational one has eventually periodic digits, and then the power series is
rational too.

**Theorem 7 as printed is false.** The paper asks only for "a sequence of integers `u`". Let
`z_k = 1` if `k` is a power of `5` and `0` otherwise, and `u_k = z_(k+1) + 2 (1 - z_k)` for
`k ≥ 1`. Then `u_k ∈ {0, 1, 2, 3}` and `∑ u_k / 2 ^ k = 1`. In characteristic `5`, `f = ∑ z_k X ^ k`
satisfies `f ^ 5 = f - X`, and `X (1 - X) ∑ u_k X ^ k = (1 - X) (1 - 2 X) f + 3 X ^ 2 - X`, so the
power series is algebraic; its coefficients vanish exactly at the powers of `5`, so it is not
eventually periodic and not rational. Here `p = 5 > u_k` but `b = 2 ≤ u_k` for some `k`: the proof
breaks where it reads `u` as base-`b` digits.

## Main results

* `Real.isAlgebraic_and_isAlgebraic_iff`: **Theorem 7**, for `u_k < min(b, p)`.
* `exists_counterexample_theorem7`: the counterexample, `b = 2`, `p = 5`, `u_k ≤ 3`.
* `not_forall_theorem7_as_printed`: Theorem 7 without the bound on `u_k` fails.

## Implementation notes

* **Indices start at `k = 0`**, where the paper sums over `k ≥ 1`; with `u_0 = 0` the objects are
  the paper's, and a nonzero `u_0` adds the same constant to both.
* **"Algebraic over `𝔽_p(X)`" is stated over `𝔽_p[X]`**, which is equivalent for an element of the
  domain `𝔽_p⟦X⟧`; "rational" is `Q f = P` with polynomials `P`, `Q ≠ 0`.
* Adamczewski restates the theorem for `b = p` in his habilitation (Lyon, 2010, Théorème 7.1),
  with digits in `{0, …, p - 1}`; that is the case `b = p` here.

## References

B. Adamczewski and Y. Bugeaud, *On the complexity of algebraic numbers I. Expansions in integer
bases*, Ann. of Math. **165** (2007), 547–565, §7; B. Adamczewski, *Une approche arithmétique des
systèmes de numération*, Habilitation, Université Lyon 1, 2010, §7.2.
-/

@[expose] public section

open Polynomial PowerSeries Filter

namespace Real

/-- **Theorem 7 (Adamczewski–Bugeaud 2007), corrected.** For `u_k < min(b, p)`, the power series
`∑ u_k X ^ k ∈ 𝔽_p⟦X⟧` and the real number `∑ u_k / b ^ k` are both algebraic if and only if both
are rational. -/
theorem isAlgebraic_and_isAlgebraic_iff {b p : ℕ} [Fact p.Prime] (hb : 2 ≤ b) {u : ℕ → ℕ}
    (hub : ∀ k, u k < b) (hup : ∀ k, u k < p) :
    IsAlgebraic (ZMod p)[X] (PowerSeries.mk fun k ↦ (u k : ZMod p)) ∧
        IsAlgebraic ℚ (∑' k, (u k : ℝ) / b ^ k) ↔
      (∃ P Q : (ZMod p)[X], Q ≠ 0 ∧
          (Q : (ZMod p)⟦X⟧) * PowerSeries.mk (fun k ↦ (u k : ZMod p)) = P) ∧
        ∑' k, (u k : ℝ) / b ^ k ∈ Set.range ((↑) : ℚ → ℝ) := by
  set F : (ZMod p)⟦X⟧ := PowerSeries.mk fun k ↦ (u k : ZMod p)
  set a : ℕ → Fin b := fun k ↦ ⟨u k, hub k⟩
  have hb0 : (b : ℝ) ≠ 0 := by positivity
  have hξ : ∑' k, (u k : ℝ) / b ^ k = (b : ℚ) • ofDigits a := by
    rw [ofDigits, Rat.smul_def, Rat.cast_natCast, ← tsum_mul_left]
    refine tsum_congr fun k ↦ ?_
    simp only [ofDigitsTerm, a, pow_succ]
    field_simp
  constructor
  · rintro ⟨hF, hα⟩
    -- Christol: `u` is `p`-automatic
    have hautoF := isAutomatic_coeff_of_isAlgebraic hF
    simp only [F, coeff_mk] at hautoF
    have hinj : ∀ k l, (u k : ZMod p) = u l → u k = u l := fun k l h ↦ by
      rwa [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (hup k), Nat.mod_eq_of_lt (hup l)] at h
    have hauto_u : Function.IsAutomatic u :=
      (Function.isAutomatic_comp_iff (g := ((↑) : ℕ → ZMod p)) (a := u)
        (by rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩ h; exact hinj k l h)).mp hautoF
    have hauto : Function.IsAutomatic a :=
      (Function.isAutomatic_comp_iff (g := ((↑) : Fin b → ℕ)) (a := a)
        Fin.val_injective.injOn).mp hauto_u
    -- Theorem 2: the real number is rational, so the digits are eventually periodic
    have hrat : ¬ Irrational (ofDigits a) := fun hirr ↦
      transcendental_ofDigits_of_isAutomatic hb hauto hirr
        (IsAlgebraic.of_smul (mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast
          (show b ≠ 0 by omega))) (hξ ▸ hα))
    have hper : Function.IsEventuallyPeriodic a := by
      by_contra h
      exact hrat (irrational_ofDigits h)
    refine ⟨exists_mul_eq_of_isEventuallyPeriodic ?_, ?_⟩
    · obtain ⟨N, T, hT, h⟩ := hper
      refine ⟨N, T, hT, fun n hn ↦ ?_⟩
      simp only [F, coeff_mk]
      exact congrArg (fun x : Fin b ↦ ((x : ℕ) : ZMod p)) (h n hn)
    · obtain ⟨q, hq⟩ := not_not.mp hrat
      refine ⟨b * q, ?_⟩
      rw [hξ, Rat.smul_def, Rat.cast_mul, Rat.cast_natCast, hq]
  · rintro ⟨⟨P, Q, hQ, h⟩, q, hq⟩
    refine ⟨IsAlgebraic.of_smul (mem_nonZeroDivisors_of_ne_zero hQ) ?_, ?_⟩
    · rw [Algebra.smul_def, algebraMap_polynomial_eq_coe, h, ← algebraMap_polynomial_eq_coe]
      exact isAlgebraic_algebraMap P
    · rw [← hq, ← eq_ratCast (algebraMap ℚ ℝ)]
      exact isAlgebraic_algebraMap q

end Real

/-! ### The counterexample to Theorem 7 as printed -/

/-- The indicator of the powers of `5`. -/
noncomputable def fivePowIndicator (k : ℕ) : ℕ := by
  classical exact if ∃ j, k = 5 ^ j then 1 else 0

/-- The counterexample to Theorem 7 as printed: `u_0 = 0` and `u_k = z_(k+1) + 2 (1 - z_k)`,
with `z` the indicator of the powers of `5`. -/
noncomputable def theorem7Counterexample (k : ℕ) : ℕ :=
  if k = 0 then 0 else fivePowIndicator (k + 1) + 2 * (1 - fivePowIndicator k)

section Counterexample

local notation "z" => fivePowIndicator
local notation "u" => theorem7Counterexample

theorem fivePowIndicator_eq_one_iff {k : ℕ} : z k = 1 ↔ ∃ j, k = 5 ^ j := by
  unfold fivePowIndicator
  split_ifs with h <;> simp [h]

theorem fivePowIndicator_le_one (k : ℕ) : z k ≤ 1 := by
  unfold fivePowIndicator
  split_ifs <;> omega

theorem fivePowIndicator_zero : z 0 = 0 := by
  have : ¬ ∃ j, 0 = 5 ^ j := fun ⟨j, hj⟩ ↦ (pow_ne_zero j (by norm_num : (5 : ℕ) ≠ 0)) hj.symm
  have h := fivePowIndicator_le_one 0
  by_contra h0
  exact this (fivePowIndicator_eq_one_iff.mp (by omega))

theorem fivePowIndicator_one : z 1 = 1 :=
  fivePowIndicator_eq_one_iff.mpr ⟨0, rfl⟩

theorem fivePowIndicator_eq_zero_iff {k : ℕ} : z k = 0 ↔ ¬ ∃ j, k = 5 ^ j := by
  rw [← fivePowIndicator_eq_one_iff]
  have := fivePowIndicator_le_one k
  omega

theorem fivePowIndicator_five_mul (k : ℕ) : z (5 * k) = z k := by
  have : (∃ j, 5 * k = 5 ^ j) ↔ ∃ j, k = 5 ^ j := by
    constructor
    · rintro ⟨j, hj⟩
      rcases j with _ | j
      · omega
      · exact ⟨j, by rw [pow_succ] at hj; omega⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j + 1, by rw [pow_succ]; ring⟩
  have h1 := fivePowIndicator_le_one (5 * k)
  have h2 := fivePowIndicator_le_one k
  by_cases h : ∃ j, k = 5 ^ j
  · rw [fivePowIndicator_eq_one_iff.mpr h, fivePowIndicator_eq_one_iff.mpr (this.mpr h)]
  · rw [fivePowIndicator_eq_zero_iff.mpr h, fivePowIndicator_eq_zero_iff.mpr (mt this.mp h)]

theorem fivePowIndicator_of_not_dvd {m : ℕ} (h5 : ¬ 5 ∣ m) (h1 : m ≠ 1) : z m = 0 := by
  refine fivePowIndicator_eq_zero_iff.mpr ?_
  rintro ⟨j, rfl⟩
  rcases j with _ | j
  · exact h1 rfl
  · exact h5 (dvd_pow_self 5 (Nat.succ_ne_zero j))

theorem theorem7Counterexample_lt (k : ℕ) : u k < 4 := by
  unfold theorem7Counterexample
  have := fivePowIndicator_le_one k
  have := fivePowIndicator_le_one (k + 1)
  split_ifs <;> omega

/-- The zeros of `u` at `k ≥ 1` are exactly the powers of `5`. -/
theorem theorem7Counterexample_eq_zero_iff {k : ℕ} (hk : 1 ≤ k) :
    u k = 0 ↔ ∃ j, k = 5 ^ j := by
  unfold theorem7Counterexample
  simp only [show k ≠ 0 by omega, ↓reduceIte]
  rw [← fivePowIndicator_eq_one_iff]
  have h1 := fivePowIndicator_le_one k
  have h2 := fivePowIndicator_le_one (k + 1)
  have : z k = 1 → z (k + 1) = 0 := by
    rw [fivePowIndicator_eq_one_iff, fivePowIndicator_eq_zero_iff]
    rintro ⟨j, rfl⟩ ⟨i, hi⟩
    rcases i with _ | i
    · simp at hi
    · have h5 : 5 ∣ 5 ^ j + 1 := hi ▸ dvd_pow_self 5 (Nat.succ_ne_zero i)
      rcases j with _ | j
      · omega
      · rw [pow_succ] at h5
        omega
  omega

theorem not_isEventuallyPeriodic_theorem7Counterexample :
    ¬ Function.IsEventuallyPeriodic u := by
  rintro ⟨N, T, hT, h⟩
  set j := N + T
  have hj : N + T < 5 ^ j := Nat.lt_pow_self (by norm_num)
  have h0 : u (5 ^ j) = 0 :=
    (theorem7Counterexample_eq_zero_iff (Nat.one_le_pow _ _ (by norm_num))).mpr ⟨j, rfl⟩
  have h1 : u (5 ^ j + T) = 0 := by rw [h _ (by omega), h0]
  obtain ⟨i, hi⟩ := (theorem7Counterexample_eq_zero_iff (by omega)).mp h1
  have hji : j < i := by
    by_contra hij
    have : 5 ^ i ≤ 5 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have : 5 ^ (j + 1) ≤ 5 ^ i := Nat.pow_le_pow_right (by norm_num) hji
  rw [pow_succ] at this
  omega

theorem hasSum_theorem7Counterexample : HasSum (fun k ↦ (u k : ℝ) / 2 ^ k) 1 := by
  set Z : ℕ → ℝ := fun k ↦ (z k : ℝ) / 2 ^ k
  have hZs : Summable Z := by
    refine Summable.of_nonneg_of_le (fun k ↦ by positivity) (fun k ↦ ?_)
      summable_geometric_two
    simp only [Z, one_div, inv_pow]
    rw [div_eq_mul_inv]
    exact mul_le_of_le_one_left (by positivity) (by exact_mod_cast fivePowIndicator_le_one k)
  have hZ := hZs.hasSum
  have hZ1 : HasSum (fun k ↦ Z (k + 1)) (∑' k, Z k) := by
    have := (hasSum_nat_add_iff' 1).mpr hZ
    simpa [Z, fivePowIndicator_zero] using this
  have h := ((hZ1.mul_left 2).add (summable_geometric_two.hasSum.mul_left 2) |>.sub
    (hZ.mul_left 2)).sub (hasSum_ite_eq 0 (3 : ℝ))
  rw [tsum_geometric_two] at h
  convert h using 1
  · funext k
    simp only [Z, theorem7Counterexample]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [fivePowIndicator_zero, fivePowIndicator_one]
      norm_num
    · simp only [hk.ne', ↓reduceIte]
      have := fivePowIndicator_le_one k
      push_cast [Nat.cast_sub this]
      rw [one_div, inv_pow]
      field_simp
      ring
  · ring

/-- `f = ∑ z_k X ^ k` satisfies `f ^ 5 = f - X` over `𝔽_5`. -/
theorem fivePowSeries_pow_five [Fact (Nat.Prime 5)] :
    (PowerSeries.mk fun k ↦ (z k : ZMod 5)) ^ 5 =
      (PowerSeries.mk fun k ↦ (z k : ZMod 5)) - PowerSeries.X := by
  have h := FiniteField.PowerSeries.expand_card (PowerSeries.mk fun k ↦ (z k : ZMod 5))
  rw [show (PowerSeries.mk fun k ↦ (z k : ZMod 5)) ^ 5 =
      (PowerSeries.mk fun k ↦ (z k : ZMod 5)) ^ Fintype.card (ZMod 5) by rw [ZMod.card], ← h]
  ext m
  rw [PowerSeries.coeff_expand, ZMod.card, map_sub, coeff_mk, PowerSeries.coeff_X]
  by_cases h5 : 5 ∣ m
  · obtain ⟨k, rfl⟩ := h5
    have h1 : 5 * k ≠ 1 := by omega
    simp only [dvd_mul_right, ↓reduceIte, h1, Nat.mul_div_cancel_left k (by norm_num : 0 < 5),
      sub_zero, coeff_mk]
    rw [fivePowIndicator_five_mul]
  · by_cases h1 : m = 1
    · subst h1
      simp [fivePowIndicator_one]
    · simp [h5, h1, fivePowIndicator_of_not_dvd h5 h1]

end Counterexample

/-- **The counterexample to Theorem 7 as printed**: `b = 2`, `p = 5` and `u_k ≤ 3`. The power series
`∑ u_k X ^ k ∈ 𝔽_5⟦X⟧` is algebraic and `∑ u_k / 2 ^ k = 1`, but the power series is not
rational. -/
theorem exists_counterexample_theorem7 :
    ∃ u : ℕ → ℕ, (∀ k, u k < 4) ∧
      IsAlgebraic (ZMod 5)[X] (PowerSeries.mk fun k ↦ (u k : ZMod 5)) ∧
      ∑' k, (u k : ℝ) / 2 ^ k = 1 ∧
      ¬ ∃ P Q : (ZMod 5)[X], Q ≠ 0 ∧
        (Q : (ZMod 5)⟦X⟧) * PowerSeries.mk (fun k ↦ (u k : ZMod 5)) = P := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set z := fivePowIndicator
  set u := theorem7Counterexample
  set f : (ZMod 5)⟦X⟧ := PowerSeries.mk fun k ↦ (z k : ZMod 5)
  set g : (ZMod 5)⟦X⟧ := PowerSeries.mk fun k ↦ (u k : ZMod 5)
  refine ⟨u, theorem7Counterexample_lt, ?_, hasSum_theorem7Counterexample.tsum_eq, ?_⟩
  · -- `f` is integral over `𝔽_5[X]`: `f ^ 5 - f + X = 0`
    have hf : IsIntegral (ZMod 5)[X] f := by
      refine ⟨Polynomial.X ^ 5 - Polynomial.X + Polynomial.C Polynomial.X, by monicity!, ?_⟩
      simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
        Polynomial.eval₂_X, Polynomial.eval₂_C, algebraMap_polynomial_eq_coe, Polynomial.coe_X]
      rw [fivePowSeries_pow_five]
      ring
    -- `g = S - 1 + 2 (X / (1 - X) - f)`, with `S` the shift of `f`
    set S : (ZMod 5)⟦X⟧ := PowerSeries.mk fun k ↦ coeff (k + 1) f
    have hg : g = S - 1 + 2 * (PowerSeries.X * PowerSeries.mk 1 - f) := by
      ext k
      rcases k with _ | k
      · simp [g, S, f, u, z, theorem7Counterexample, fivePowIndicator_zero, fivePowIndicator_one]
      · have := fivePowIndicator_le_one (k + 1)
        simp only [g, S, f, coeff_mk, map_sub, map_add, PowerSeries.coeff_one,
          u, theorem7Counterexample, z]
        simp [Nat.cast_sub this]
    have hS : PowerSeries.X * S = f := by
      rw [← sub_const_eq_X_mul_shift]
      simp [f, z, fivePowIndicator_zero]
    have key : ((Polynomial.X * (1 - Polynomial.X) : (ZMod 5)[X]) : (ZMod 5)⟦X⟧) * g =
        (((1 - Polynomial.X) * (1 - 2 * Polynomial.X) : (ZMod 5)[X]) : (ZMod 5)⟦X⟧) * f +
          ((3 * Polynomial.X ^ 2 - Polynomial.X : (ZMod 5)[X]) : (ZMod 5)⟦X⟧) := by
      have h2 : ((2 : (ZMod 5)[X]) : (ZMod 5)⟦X⟧) = 2 :=
        map_ofNat Polynomial.coeToPowerSeries.ringHom 2
      have h3 : ((3 : (ZMod 5)[X]) : (ZMod 5)⟦X⟧) = 3 :=
        map_ofNat Polynomial.coeToPowerSeries.ringHom 3
      push_cast
      rw [h2, h3]
      linear_combination (PowerSeries.X * (1 - PowerSeries.X)) * hg +
        (1 - PowerSeries.X) * hS +
        2 * PowerSeries.X ^ 2 * mk_one_mul_one_sub_eq_one (S := ZMod 5)
    have hc : (Polynomial.X * (1 - Polynomial.X) : (ZMod 5)[X]) ≠ 0 := by
      refine mul_ne_zero Polynomial.X_ne_zero fun h ↦ ?_
      have := congrArg (Polynomial.coeff · 0) h
      simp at this
    refine IsAlgebraic.of_smul_isIntegral (y := Polynomial.X * (1 - Polynomial.X))
      (by rw [isNilpotent_iff_eq_zero]; exact hc) ?_
    rw [Algebra.smul_def, algebraMap_polynomial_eq_coe, key, ← algebraMap_polynomial_eq_coe,
      ← algebraMap_polynomial_eq_coe]
    exact (isIntegral_algebraMap.mul hf).add isIntegral_algebraMap
  · rintro ⟨P, Q, hQ, h⟩
    have hper := isEventuallyPeriodic_coeff_of_mul_eq hQ h
    refine not_isEventuallyPeriodic_theorem7Counterexample ?_
    obtain ⟨N, T, hT, h⟩ := hper
    refine ⟨N, T, hT, fun n hn ↦ ?_⟩
    have := h n hn
    have hlt : ∀ k, u k < 5 := fun k ↦ (theorem7Counterexample_lt k).trans (by norm_num)
    simp only [coeff_mk, ZMod.natCast_eq_natCast_iff'] at this
    rwa [Nat.mod_eq_of_lt (hlt _), Nat.mod_eq_of_lt (hlt _)] at this

/-- **Theorem 7 as printed is false**: without a bound on the `u_k`, "both algebraic" does not
imply "both rational". -/
theorem not_forall_theorem7_as_printed :
    ¬ ∀ u : ℕ → ℕ,
      IsAlgebraic (ZMod 5)[X] (PowerSeries.mk fun k ↦ (u k : ZMod 5)) ∧
          IsAlgebraic ℚ (∑' k, (u k : ℝ) / 2 ^ k) →
        (∃ P Q : (ZMod 5)[X], Q ≠ 0 ∧
            (Q : (ZMod 5)⟦X⟧) * PowerSeries.mk (fun k ↦ (u k : ZMod 5)) = P) ∧
          ∑' k, (u k : ℝ) / 2 ^ k ∈ Set.range ((↑) : ℚ → ℝ) := by
  intro h
  obtain ⟨u, -, halg, hsum, hnot⟩ := exists_counterexample_theorem7
  refine hnot (h u ⟨halg, ?_⟩).1
  rw [hsum]
  exact isAlgebraic_one
