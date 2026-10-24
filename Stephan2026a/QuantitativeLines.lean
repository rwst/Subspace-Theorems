/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Stephan2026a.QuantitativePlanes

-- Used only inside proofs.
import DiophantineApproximation.DoublingSequences
import Stephan2026a.SubspaceStep

/-!
# Kernel violators with a small gap lie on few lines

**Problem 5.2, step 4.** A pair `2 ≤ a < c` with a small gap `s = c - a ≤ ε c / 4` is counted in
two variables: the point

```text
y = (3^c - 2^s 3^a, 2^c (m_c - m_a)) = (3^a (3^s - 2^s), 2^c M),       N = y₀ - y₁,
```

(`SteeringWord.linePoint`) has size between `3^{c-1}` and `3^c`; its first coordinate is odd and
divisible by `3^a`, its second by `2^c`. With `λ = log 2 / log 3` it solves a system of the
quantitative Subspace Theorem at `∞`, `2` and `3`:

* at `∞` the forms `X₀ - X₁`, `X₁` with exponents `λ - ε`, `1` and constant `3`;
* at `2` the coordinates with exponents `0`, `-λ`;
* at `3` the coordinates with exponents `-(1 - ε/4)`, `0`.

The exponents sum to `-3ε/4`, so Evertse–Ferretti's count puts the points into
`K ε⁻³ (1 + log ε⁻¹)²` lines (`SteeringWord.exists_lines_of_violators`). On one line two points
satisfy `y₀ y₁' = y₀' y₁`; since `y₀'` is odd, `2^{c'} ∣ y₁ < 3^c`, and `3^5 < 2^8` gives
`5 c' < 8 c`: a doubling sequence has at most three points on a line
(`SteeringWord.card_mem_line_le`).

## Main definitions

* `SteeringWord.linePoint a c`: the point `(3^c - 2^s 3^a, 2^c (m_c - m_a))`.
* `SteeringWord.lineForms`, `SteeringWord.lineExp`, `SteeringWord.linePadic`: the system.

## Main results

* `SteeringWord.line_hyps`, `SteeringWord.line_mem`: the system is admissible, and the line
  point of a violator with a small gap solves it.
* `SteeringWord.exists_lines_of_violators`: **the two-variable step**; with `K = 32 · 10²¹`,
  `SteeringWord.exists_lines_of_violators_explicit`.
* `SteeringWord.card_mem_line_le`: **at most three points on a line**.

## References

R. Stephan, *Superlinear complexity of the `(3/2)^n` steering word*, arXiv:2607.11648, Problem 5.2;
J.-H. Evertse, R. G. Ferretti, *A further improvement of the quantitative Subspace Theorem*, Ann.
of Math. **177** (2013), 513–590;
R. Stephan, *The exponent `1/4` in three complexity bounds: integer bases, continued fractions, and
the `(3/2)^n` steering word*, arXiv:2610.30937 (2026), Lemma 5.7.
-/

@[expose] public section

open Finset Real

namespace SteeringWord

/-- **The line point** `(3^c - 2^s 3^a, 2^c (m_c - m_a))`, `s = c - a`, of a pair `a < c`. -/
def linePoint (a c : ℕ) : Fin 2 → ℤ := ![3 ^ c - 2 ^ (c - a) * 3 ^ a, 2 ^ c * (m c - m a)]

variable {a c : ℕ}

/-- `3^c - 2^s 3^a = 3^a (3^s - 2^s)`. -/
theorem three_pow_sub_eq (hac : a ≤ c) :
    (3 : ℤ) ^ c - 2 ^ (c - a) * 3 ^ a = 3 ^ a * (3 ^ (c - a) - 2 ^ (c - a)) := by
  rw [show (3 : ℤ) ^ c = 3 ^ (c - a) * 3 ^ a by rw [← pow_add, Nat.sub_add_cancel hac]]
  ring

/-- `3^{c-1} ≤ 3^c - 2^s 3^a`, as `3 (3^c - 2^s 3^a) ≥ 3^c`, for `a < c`. -/
theorem three_pow_le_three_mul_sub (hac : a < c) :
    (3 : ℤ) ^ c ≤ 3 * (3 ^ c - 2 ^ (c - a) * 3 ^ a) := by
  obtain ⟨t, ht⟩ : ∃ t, c - a = t + 1 := ⟨c - a - 1, by omega⟩
  have hc : (3 : ℤ) ^ c = 3 * (3 ^ t * 3 ^ a) := by
    rw [← pow_add, ← pow_succ', show t + a + 1 = c by omega]
  have h2 : (2 : ℤ) ^ t ≤ 3 ^ t := pow_le_pow_left₀ (by norm_num) (by norm_num) t
  have h3 : (0 : ℤ) < 3 ^ a := by positivity
  rw [ht, pow_succ, hc]
  nlinarith

/-- `3^c - 2^s 3^a` is odd for `a < c`. -/
theorem odd_three_pow_sub (hac : a < c) : Odd ((3 : ℤ) ^ c - 2 ^ (c - a) * 3 ^ a) := by
  obtain ⟨t, ht⟩ : ∃ t, c - a = t + 1 := ⟨c - a - 1, by omega⟩
  rw [ht, pow_succ, show (2 : ℤ) ^ t * 2 * 3 ^ a = 2 * (2 ^ t * 3 ^ a) by ring]
  exact (Odd.pow ⟨1, by norm_num⟩).sub_even (even_two_mul _)

/-- An odd integer is prime to every power of `2`. -/
theorem isCoprime_two_pow_of_odd {y : ℤ} (hy : Odd y) (k : ℕ) : IsCoprime ((2 : ℤ) ^ k) y := by
  obtain ⟨r, rfl⟩ := hy
  exact IsCoprime.pow_left ⟨-r, 1, by ring⟩

/-- **The lines principle.** Two line points `y, y'` with `y₀ y₁' = y₀' y₁` (on one line through
`0`) at pairs `2 ≤ a < c`, `a' < c'` have `5 c' < 8 c`: `2^{c'} ∣ y₁ < 3^c` since `y₀'` is
odd, against `3^5 < 2^8`. -/
theorem five_mul_lt_of_mul_eq {a' c' : ℕ} (ha : 2 ≤ a) (hac : a < c) (hac' : a' < c')
    (h : linePoint a c 0 * linePoint a' c' 1 = linePoint a' c' 0 * linePoint a c 1) :
    5 * c' < 8 * c := by
  have hZ := kernelPoint_two_bounds ha hac
  have hdvd : (2 : ℤ) ^ c' ∣ linePoint a' c' 0 * linePoint a c 1 := by
    rw [← h]
    exact Dvd.dvd.mul_left (Dvd.intro _ rfl) _
  have hdvd' : (2 : ℤ) ^ c' ∣ 2 ^ c * (m c - m a) :=
    (isCoprime_two_pow_of_odd (odd_three_pow_sub hac') c').dvd_of_dvd_mul_left hdvd
  have hle : (2 : ℤ) ^ c' < 3 ^ c := (Int.le_of_dvd hZ.1 hdvd').trans_lt hZ.2
  have hle' : 2 ^ c' < 3 ^ c := by exact_mod_cast hle
  by_contra hcon
  have e1 : 2 ^ (8 * c) ≤ 2 ^ (5 * c') := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e2 : 2 ^ (5 * c') < 3 ^ (5 * c) := by
    rw [pow_mul', pow_mul' 3]
    exact Nat.pow_lt_pow_left hle' (by norm_num)
  have e3 : 3 ^ (5 * c) ≤ 2 ^ (8 * c) := by
    rw [pow_mul, pow_mul 2]
    exact Nat.pow_le_pow_left (by norm_num) _
  exact lt_irrefl _ ((e1.trans_lt e2).trans_le e3)

/-! ### The system -/

/-- **The forms of the two-variable step**: `X₀ - X₁`, `X₁`. -/
def lineForms : Fin 2 → Fin 2 → Fin 3 → ℤ := ![![![1, 0, 0], ![-1, 0, 0]], ![0, ![1, 0, 0]]]

theorem abs_lineForms_le (i j : Fin 2) (m : Fin 3) : |(lineForms i j m : ℝ)| ≤ 1 := by
  fin_cases i <;> fin_cases j <;> fin_cases m <;> simp [lineForms]

theorem one_le_abs_det_lineForms :
    (1 : ℝ) ≤ |(Matrix.of fun i j ↦ quadVal 0 (lineForms i j)).det| := by
  simp [Matrix.det_fin_two, quadVal, lineForms]

/-- **The exponents at `∞`**: `λ - ε`, `1`. -/
noncomputable def lineExp (ε : ℝ) : Fin 2 → ℝ := ![logb 3 2 - ε, 1]

/-- **The exponents at `2` and `3`**: `0`, `-λ` at `2` and `-(1 - ε/4)`, `0` at `3`. -/
noncomputable def linePadic (ε : ℝ) : Nat.Primes → Fin 2 → ℝ := fun l ↦
  if (l : ℕ) = 2 then ![0, -logb 3 2] else ![-(1 - ε / 4), 0]

theorem linePadic_two (ε : ℝ) :
    linePadic ε ⟨2, Nat.prime_two⟩ = (![0, -logb 3 2] : Fin 2 → ℝ) := rfl

theorem linePadic_three (ε : ℝ) :
    linePadic ε ⟨3, Nat.prime_three⟩ = (![-(1 - ε / 4), 0] : Fin 2 → ℝ) := rfl

/-- **The system is admissible**: for `0 < ε ≤ 1` the exponents meet the hypotheses of
`Real.SubspaceBoundWith` with `δ = 3ε/4`. -/
theorem line_hyps {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∀ i, lineExp ε i ≤ 1) ∧ (∃ i, lineExp ε i = 1) ∧
      (∃ i, lineExp ε i ≤ 1 - 3 * ε / 4 / (2 * ((2 : ℕ) : ℝ))) ∧
      (∀ l ∈ ({⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩} : Finset Nat.Primes), ∀ i,
        linePadic ε l i ≤ 0) ∧
      (∀ l ∈ ({⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩} : Finset Nat.Primes), ∃ i,
        linePadic ε l i = 0) ∧
      ∑ i, lineExp ε i + ∑ l ∈ ({⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩} :
        Finset Nat.Primes), ∑ i, linePadic ε l i ≤ -(3 * ε / 4) := by
  have hlam0 : 0 < logb 3 2 := logb_three_two_pos
  have hlam1 : logb 3 2 ≤ 2 / 3 := logb_three_two_le
  refine ⟨fun i ↦ ?_, ⟨1, by simp [lineExp]⟩, ⟨0, by simp [lineExp]; linarith⟩,
    fun l hl i ↦ ?_, fun l hl ↦ ?_, ?_⟩
  · fin_cases i <;> simp [lineExp]; linarith
  · rcases mem_insert.mp hl with rfl | hl
    · rw [linePadic_two]; fin_cases i <;> simp; linarith
    · obtain rfl := Finset.mem_singleton.mp hl
      rw [linePadic_three]; fin_cases i <;> simp; linarith
  · rcases mem_insert.mp hl with rfl | hl
    · exact ⟨0, by rw [linePadic_two]; simp⟩
    · obtain rfl := Finset.mem_singleton.mp hl
      exact ⟨1, by rw [linePadic_three]; simp⟩
  · rw [sum_pair (ι := Nat.Primes) prime_two_ne_prime_three, linePadic_two, linePadic_three]
    simp only [lineExp, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith

/-- **The line point of a violator with a small gap solves the system**: for `0 < ε ≤ 1`, a pair
`2 ≤ a < c` with `|ε_c - ε_a| ≤ (3^c)^{-ε}` and `c - a ≤ ε c / 4` has a nonzero line point of
size `Y` with `(c - 1) log 3 ≤ log Y ≤ c log 3`, which solves the inequalities of
`Real.SubspaceBoundWith` for `lineForms`, the constant `3` and the exponents `lineExp ε`,
`linePadic ε`. -/
theorem line_mem {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {a c : ℕ} (ha : 2 ≤ a) (hac : a < c)
    (happ : |(eps c : ℝ) - eps a| ≤ ((3 : ℝ) ^ c) ^ (-ε)) (hgap : ((c - a : ℕ) : ℝ) ≤ ε / 4 * c) :
    linePoint a c ≠ 0 ∧
      (∀ i, |∑ j, quadVal 0 (lineForms i j) * (linePoint a c j : ℝ)| ≤
        3 * (⨆ j, |(linePoint a c j : ℝ)|) ^ lineExp ε i) ∧
      (∀ l ∈ ({⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩} : Finset Nat.Primes), ∀ i,
        ((padicNorm (l : ℕ) (linePoint a c i : ℚ) : ℚ) : ℝ) ≤
          (⨆ j, |(linePoint a c j : ℝ)|) ^ linePadic ε l i) ∧
      (c : ℝ) * log 3 - log 3 ≤ log (⨆ j, |(linePoint a c j : ℝ)|) ∧
      log (⨆ j, |(linePoint a c j : ℝ)|) ≤ c * log 3 := by
  set lam := logb 3 2 with hlam
  have hlam0 : 0 < lam := logb_three_two_pos
  have hlam1 : lam ≤ 2 / 3 := logb_three_two_le
  set s := c - a with hs
  have hsa : (s : ℝ) + a = c := by rw [hs]; exact_mod_cast Nat.sub_add_cancel hac.le
  set y := linePoint a c with hy
  have hZ := kernelPoint_two_bounds ha hac
  have hY0 := three_pow_le_three_mul_sub hac
  have hY0' : (3 : ℤ) ^ c - 2 ^ (c - a) * 3 ^ a ≤ 3 ^ c := by
    have : (0 : ℤ) < 2 ^ (c - a) * 3 ^ a := by positivity
    linarith
  -- the size `3^c / 3 ≤ Y ≤ 3^c`
  set Y := ⨆ k, |(y k : ℝ)| with hYdef
  have hY1 : (3 : ℝ) ^ c ≤ 3 * Y := by
    have h0 : |(y 0 : ℝ)| ≤ Y := le_ciSup (f := fun k ↦ |(y k : ℝ)|)
      (Set.finite_range _).bddAbove 0
    have : (3 : ℝ) ^ c ≤ 3 * (y 0 : ℝ) := by
      change (3 : ℝ) ^ c ≤ 3 * (((3 : ℤ) ^ c - 2 ^ (c - a) * 3 ^ a : ℤ) : ℝ)
      exact_mod_cast hY0
    have := le_abs_self (y 0 : ℝ)
    linarith
  have hY2 : Y ≤ (3 : ℝ) ^ c := by
    refine ciSup_le fun i ↦ ?_
    fin_cases i
    · change |(((3 : ℤ) ^ c - 2 ^ (c - a) * 3 ^ a : ℤ) : ℝ)| ≤ 3 ^ c
      have hpos : (0 : ℤ) < 3 ^ c - 2 ^ (c - a) * 3 ^ a := by
        have : (0 : ℤ) < 3 ^ c := by positivity
        linarith
      rw [abs_of_pos (by exact_mod_cast hpos)]
      exact_mod_cast hY0'
    · change |((2 ^ c * (m c - m a) : ℤ) : ℝ)| ≤ 3 ^ c
      rw [abs_of_pos (by exact_mod_cast hZ.1)]
      exact_mod_cast hZ.2.le
  have hYpos : 0 < Y := by
    have : (0 : ℝ) < 3 ^ c := by positivity
    linarith
  have hpow : ∀ z : ℝ, ((3 : ℝ) ^ c) ^ z = (3 : ℝ) ^ (c * z) := fun z ↦ by
    rw [← rpow_natCast, ← rpow_mul (by norm_num)]
  have h3 : ∀ n : ℕ, (3 : ℝ) ^ n = (3 : ℝ) ^ (n : ℝ) := fun n ↦ (rpow_natCast 3 n).symm
  have hle : ∀ z w : ℝ, z ≤ w → (3 : ℝ) ^ z ≤ (3 : ℝ) ^ w := fun z w h ↦
    rpow_le_rpow_of_exponent_le (by norm_num) h
  -- `(3^c)^z ≤ 3 Y^z` for `z ≤ 1`
  have hcY : ∀ z : ℝ, z ≤ 1 → ((3 : ℝ) ^ c) ^ z ≤ 3 * Y ^ z := fun z hz ↦ by
    rcases le_or_gt 0 z with hz0 | hz0
    · calc ((3 : ℝ) ^ c) ^ z ≤ (3 * Y) ^ z := rpow_le_rpow (by positivity) hY1 hz0
        _ = 3 ^ z * Y ^ z := mul_rpow (by norm_num) hYpos.le
        _ ≤ 3 * Y ^ z := by
            gcongr
            exact rpow_le_self_of_one_le (by norm_num) hz
    · have : ((3 : ℝ) ^ c) ^ z ≤ Y ^ z := rpow_le_rpow_of_nonpos hYpos hY2 hz0.le
      have : 0 ≤ Y ^ z := by positivity
      linarith
  have hinf : ∀ i, |∑ j, quadVal 0 (lineForms i j) * y j| ≤ 3 * Y ^ lineExp ε i := by
    intro i
    fin_cases i
    · change |∑ j, quadVal 0 (lineForms 0 j) * (y j : ℝ)| ≤ 3 * Y ^ (lam - ε)
      have hN : ∑ j, quadVal 0 (lineForms 0 j) * (y j : ℝ) = kernelNum a c := by
        simp [lineForms, quadVal, y, linePoint, kernelNum, Fin.sum_univ_two]
        ring
      rw [hN, kernelNum_eq_real hac.le, abs_mul, abs_of_pos (by positivity)]
      refine le_trans ?_ (hcY _ (by linarith))
      calc (2 : ℝ) ^ c * |(eps c : ℝ) - eps a| ≤ 2 ^ c * ((3 : ℝ) ^ c) ^ (-ε) :=
            mul_le_mul_of_nonneg_left happ (by positivity)
        _ = ((3 : ℝ) ^ c) ^ (lam - ε) := by
            rw [hpow, hpow, two_pow_eq_three_rpow, ← rpow_add (by norm_num)]
            congr 1
            ring
    · change |∑ j, quadVal 0 (lineForms 1 j) * (y j : ℝ)| ≤ 3 * Y ^ (1 : ℝ)
      have h1 : ∑ j, quadVal 0 (lineForms 1 j) * (y j : ℝ) = ((2 ^ c * (m c - m a) : ℤ) : ℝ) := by
        simp [lineForms, quadVal, y, linePoint, Fin.sum_univ_two]
      rw [h1, rpow_one, abs_of_pos (by exact_mod_cast hZ.1)]
      have : ((2 ^ c * (m c - m a) : ℤ) : ℝ) ≤ 3 ^ c := by exact_mod_cast hZ.2.le
      linarith
  have hpad : ∀ l ∈ ({⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩} : Finset Nat.Primes), ∀ i,
      ((padicNorm (l : ℕ) (y i : ℚ) : ℚ) : ℝ) ≤ Y ^ linePadic ε l i := by
    intro l hl i
    rcases mem_insert.mp hl with rfl | hl
    · have := Fact.mk Nat.prime_two
      rw [linePadic_two]
      fin_cases i
      · change ((padicNorm 2 (y 0 : ℚ) : ℚ) : ℝ) ≤ Y ^ (0 : ℝ)
        rw [rpow_zero]
        exact padicNorm_intCast_le_one 2 _
      · change ((padicNorm 2 (y 1 : ℚ) : ℚ) : ℝ) ≤ Y ^ (-lam)
        calc ((padicNorm 2 (y 1 : ℚ) : ℚ) : ℝ) ≤ (1 / 2 : ℝ) ^ c :=
              padicNorm_intCast_le_of_dvd (by
                change ((2 : ℕ) : ℤ) ^ c ∣ 2 ^ c * (m c - m a)
                exact_mod_cast dvd_mul_right _ _)
          _ = ((3 : ℝ) ^ c) ^ (-lam) := by
              rw [one_div_pow, one_div, two_pow_eq_three_rpow, ← rpow_neg (by norm_num),
                hpow]
              congr 1
              ring
          _ ≤ Y ^ (-lam) := rpow_le_rpow_of_nonpos hYpos hY2 (by linarith)
    · obtain rfl := Finset.mem_singleton.mp hl
      have := Fact.mk Nat.prime_three
      rw [linePadic_three]
      fin_cases i
      · change ((padicNorm 3 (y 0 : ℚ) : ℚ) : ℝ) ≤ Y ^ (-(1 - ε / 4))
        calc ((padicNorm 3 (y 0 : ℚ) : ℚ) : ℝ) ≤ (1 / 3 : ℝ) ^ a :=
              padicNorm_intCast_le_of_dvd (by
                change ((3 : ℕ) : ℤ) ^ a ∣ 3 ^ c - 2 ^ (c - a) * 3 ^ a
                rw [three_pow_sub_eq hac.le]
                exact_mod_cast dvd_mul_right _ _)
          _ = (3 : ℝ) ^ (-(a : ℝ)) := by
              rw [one_div_pow, one_div, h3, ← rpow_neg (by norm_num)]
          _ ≤ (3 : ℝ) ^ (c * (-(1 - ε / 4))) := hle _ _ (by nlinarith)
          _ = ((3 : ℝ) ^ c) ^ (-(1 - ε / 4)) := (hpow _).symm
          _ ≤ Y ^ (-(1 - ε / 4)) := rpow_le_rpow_of_nonpos hYpos hY2 (by linarith)
      · change ((padicNorm 3 (y 1 : ℚ) : ℚ) : ℝ) ≤ Y ^ (0 : ℝ)
        rw [rpow_zero]
        exact padicNorm_intCast_le_one 3 _
  have hy0 : y ≠ 0 := fun h ↦ by
    have := congrFun h 1
    have h1 : (0 : ℤ) < y 1 := hZ.1
    rw [this] at h1
    exact lt_irrefl 0 h1
  have hlogY : (c : ℝ) * log 3 - log 3 ≤ log Y := by
    have := log_le_log (by positivity) hY1
    rw [log_mul (by norm_num) hYpos.ne', log_pow] at this
    linarith
  have hlogY' : log Y ≤ c * log 3 := by
    have := log_le_log hYpos hY2
    rwa [log_pow] at this
  exact ⟨hy0, hinf, hpad, hlogY, hlogY'⟩

/-- **The two-variable step**, with `K = 32 · 10²¹`: for `0 < ε ≤ 1` the line points of the
pairs `2 ≤ a < c` with `|ε_c - ε_a| ≤ (3^c)^{-ε}`, a small gap `c - a ≤ ε c / 4` and
`K ε⁻¹ ≤ c log 3` lie in at most `K ε⁻³ (1 + log ε⁻¹)²` proper subspaces of `ℚ²`. -/
theorem exists_lines_of_violators_explicit {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ T : Finset (Submodule ℚ (Fin 2 → ℚ)),
      (#T : ℝ) ≤ 32 * 10 ^ 21 * ε⁻¹ ^ 3 * (1 + log ε⁻¹) ^ 2 ∧ (∀ U ∈ T, U ≠ ⊤) ∧
      ∀ a c : ℕ, 2 ≤ a → a < c → |(eps c : ℝ) - eps a| ≤ ((3 : ℝ) ^ c) ^ (-ε) →
        ((c - a : ℕ) : ℝ) ≤ ε / 4 * c → 32 * 10 ^ 21 * ε⁻¹ ≤ c * log 3 →
        ∃ U ∈ T, (fun i ↦ (linePoint a c i : ℚ)) ∈ U := by
  classical
  have hBE : SubspaceBoundWith 0 {⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩} 3 2 (10 ^ 21) :=
    subspaceBoundWith_two_three_two
  set K₀ : ℝ := 10 ^ 21 with hK₀def
  have hK₀ : 0 < K₀ := by positivity
  set δ := 3 * ε / 4 with hδ
  have hδpos : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by rw [hδ]; linarith
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := line_hyps hε hε1
  obtain ⟨T, hTcard, hTtop, hTmem⟩ := hBE lineForms 1 le_rfl abs_lineForms_le 1 one_pos le_rfl
    one_le_abs_det_lineForms 3 (by norm_num) (lineExp ε) (linePadic ε) δ hδpos hδ1 h1 h2 h3 h4
    h5 h6
  refine ⟨T, ?_, hTtop, ?_⟩
  · -- the count
    have hεinv : 1 ≤ ε⁻¹ := one_le_inv₀ hε |>.mpr hε1
    have hδinv : δ⁻¹ ≤ 2 * ε⁻¹ := by
      rw [hδ, inv_div]
      rw [div_le_iff₀ (by positivity)]
      field_simp
      linarith
    have hδinv1 : 1 ≤ δ⁻¹ := one_le_inv₀ hδpos |>.mpr hδ1
    have hlogδ : 1 + log δ⁻¹ ≤ 2 * (1 + log ε⁻¹) := by
      have : log δ⁻¹ ≤ log (2 * ε⁻¹) := log_le_log (by positivity) hδinv
      rw [log_mul (by norm_num) (by positivity)] at this
      have := log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      have := log_nonneg hεinv
      linarith
    have hlogδ0 : 0 ≤ 1 + log δ⁻¹ := by have := log_nonneg hδinv1; linarith
    refine hTcard.trans ?_
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, rpow_natCast]
    calc K₀ * δ⁻¹ ^ 3 * (1 + log δ⁻¹) ^ 2
        ≤ K₀ * (2 * ε⁻¹) ^ 3 * (2 * (1 + log ε⁻¹)) ^ 2 := by gcongr
      _ = 32 * K₀ * ε⁻¹ ^ 3 * (1 + log ε⁻¹) ^ 2 := by ring
  · intro a c ha hac happ hgap hthr
    obtain ⟨hy0, hinf, hpad, hlogY, -⟩ := line_mem hε hε1 ha hac happ hgap
    have hthr' : K₀ * δ⁻¹ * (1 + log 1 + log 3 + log (1 : ℝ)⁻¹) ≤
        log (⨆ k, |(linePoint a c k : ℝ)|) := by
      simp only [log_one, inv_one, add_zero]
      have hl3 : 1 + log 3 ≤ 3 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
        linarith
      have hl30 : 0 < log 3 := log_pos (by norm_num)
      have hc3 : (3 : ℝ) ≤ c := by exact_mod_cast (by omega : 3 ≤ c)
      have hδ' : δ⁻¹ = 4 / 3 * ε⁻¹ := by rw [hδ]; field_simp
      rw [hδ']
      have h0 : 0 ≤ K₀ * ε⁻¹ := by positivity
      have hA : K₀ * (4 / 3 * ε⁻¹) * (1 + log 3) ≤ 4 * (K₀ * ε⁻¹) := by
        nlinarith [mul_le_mul_of_nonneg_left hl3 h0]
      have hB : 3 * log 3 ≤ c * log 3 := mul_le_mul_of_nonneg_right hc3 hl30.le
      linarith
    exact hTmem _ hy0 hinf hpad hthr'

/-- **The two-variable step.** There is `K > 0` such that for `0 < ε ≤ 1` the line points of the
pairs `2 ≤ a < c` with `|ε_c - ε_a| ≤ (3^c)^{-ε}`, a small gap `c - a ≤ ε c / 4` and
`K ε⁻¹ ≤ c log 3` lie in at most `K ε⁻³ (1 + log ε⁻¹)²` proper subspaces of `ℚ²`.
First proved as Lemma 5.7 of Stephan's *The exponent `1/4` in three complexity bounds* (2026,
arXiv:2610.30937). -/
theorem exists_lines_of_violators :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ T : Finset (Submodule ℚ (Fin 2 → ℚ)),
      (#T : ℝ) ≤ K * ε⁻¹ ^ 3 * (1 + log ε⁻¹) ^ 2 ∧ (∀ U ∈ T, U ≠ ⊤) ∧
      ∀ a c : ℕ, 2 ≤ a → a < c → |(eps c : ℝ) - eps a| ≤ ((3 : ℝ) ^ c) ^ (-ε) →
        ((c - a : ℕ) : ℝ) ≤ ε / 4 * c → K * ε⁻¹ ≤ c * log 3 →
        ∃ U ∈ T, (fun i ↦ (linePoint a c i : ℚ)) ∈ U :=
  ⟨32 * 10 ^ 21, by positivity, fun _ hε hε1 ↦ exists_lines_of_violators_explicit hε hε1⟩

/-- **At most three points on a line.** Let `2 τ_n < τ_{n+1}` and `ρ_n < τ_n`. The indices `n`
whose line point at `(ρ_n + 2, τ_n + 2)` lies on a proper subspace of `ℚ²` number at most
three: they lie in the window `τ_n ≤ 4 τ_{n₁}` of the first of them.
Lemma 5.7 of Stephan's *The exponent `1/4` in three complexity bounds* (2026, arXiv:2610.30937). -/
theorem card_mem_line_le {U : Submodule ℚ (Fin 2 → ℚ)} (hU : U ≠ ⊤) {ρ τ : ℕ → ℕ}
    (hτ : ∀ n, 2 * τ n < τ (n + 1)) (hρτ : ∀ n, ρ n < τ n) (J : Finset ℕ)
    (hJ : ∀ n ∈ J, (fun i ↦ (linePoint (ρ n + 2) (τ n + 2) i : ℚ)) ∈ U) :
    (#J : ℝ) ≤ 3 := by
  classical
  obtain ⟨w, hw0, hwU⟩ := exists_ne_zero_forall_sum_mul_eq_zero hU
  rcases J.eq_empty_or_nonempty with rfl | hJne
  · simp
  have hτpos : ∀ n, 0 < τ n := fun n ↦ by have := hρτ n; omega
  set n₁ := J.min' hJne with hn₁
  have hn₁J : n₁ ∈ J := J.min'_mem hJne
  have hrel : ∀ n ∈ J, w 0 * (linePoint (ρ n + 2) (τ n + 2) 0 : ℚ)
      + w 1 * (linePoint (ρ n + 2) (τ n + 2) 1 : ℚ) = 0 := fun n hn ↦ by
    simpa [Fin.sum_univ_two] using hwU _ (hJ n hn)
  have hR : ∀ n ∈ J, n₁ ≤ n ∧ (τ n : ℝ) ≤ 2 ^ 2 * τ n₁ := fun n hn ↦ by
    refine ⟨J.min'_le n hn, ?_⟩
    have h1 := hrel n₁ hn₁J
    have h2 := hrel n hn
    set y₀ := (linePoint (ρ n₁ + 2) (τ n₁ + 2) 0 : ℚ)
    set y₁ := (linePoint (ρ n₁ + 2) (τ n₁ + 2) 1 : ℚ)
    set y₀' := (linePoint (ρ n + 2) (τ n + 2) 0 : ℚ)
    set y₁' := (linePoint (ρ n + 2) (τ n + 2) 1 : ℚ)
    have e0 : w 0 * (y₀ * y₁' - y₀' * y₁) = 0 := by linear_combination y₁' * h1 - y₁ * h2
    have e1 : w 1 * (y₀ * y₁' - y₀' * y₁) = 0 := by linear_combination y₀ * h2 - y₀' * h1
    have hq : y₀ * y₁' = y₀' * y₁ := by
      by_cases h0 : w 0 = 0
      · have h1' : w 1 ≠ 0 := fun h ↦ hw0 (by ext i; fin_cases i <;> simp [h0, h])
        exact sub_eq_zero.mp ((mul_eq_zero.mp e1).resolve_left h1')
      · exact sub_eq_zero.mp ((mul_eq_zero.mp e0).resolve_left h0)
    have hz : linePoint (ρ n₁ + 2) (τ n₁ + 2) 0 * linePoint (ρ n + 2) (τ n + 2) 1 =
        linePoint (ρ n + 2) (τ n + 2) 0 * linePoint (ρ n₁ + 2) (τ n₁ + 2) 1 := by
      have hq' := hq
      simp only [y₀, y₁, y₀', y₁'] at hq'
      exact_mod_cast hq'
    have := hρτ n
    have := hρτ n₁
    have h5 := five_mul_lt_of_mul_eq (by omega) (by omega) (by omega) hz
    have := hτpos n₁
    have : τ n ≤ 4 * τ n₁ := by omega
    have : (τ n : ℝ) ≤ 4 * τ n₁ := by exact_mod_cast this
    linarith
  have hc := Nat.card_le_of_doubling_window hτ (hτpos n₁) (by norm_num) hR
  rw [log_pow, mul_div_assoc, div_self (log_pos one_lt_two).ne'] at hc
  push_cast at hc
  linarith

end SteeringWord
