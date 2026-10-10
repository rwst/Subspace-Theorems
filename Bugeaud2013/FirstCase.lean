/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Bugeaud2013.Stammering

-- Used only inside proofs.
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# The first case in the proof of Bugeaud 2013, Theorem 3.1

In the first case the preperiod `w_n = ℓ` is constant along infinitely many `n`, and the relation
`x · v_n = 0` of the first Subspace application becomes, with `N = M + 1 = w_n + r_n`,

```text
Y₁ q_{M+1} + Y₂ q_M + Y₃ p_{M+1} + Y₄ p_M = 0
```

for a fixed non-zero rational `Y` and `M → ∞`. Writing `p_ℓ = q_ℓ α - e_ℓ`, this reads
`q_{M+1} (Y₁ + Y₃ α) + q_M (Y₂ + Y₄ α) = Y₃ e_{M+1} + Y₄ e_M`. Hence `D = Y₂ + Y₄ α ≠ 0`, and
`β = -(Y₁ + Y₃ α) / D ∈ ℚ(α)` satisfies `|β q_{M+1} - q_M| ≤ K / q_{M+1}`: this is (3.8), obtained
here without passing to the limit. As `q_M / q_{M+1}` is in lowest terms, `β` is irrational. Two
three-variable Subspace applications, at `(q_{M+1}, q_M, p_{M+1})` and `(q_{M+1}, q_M, p_M)`, give
`y₁ + y₂ β + y₃ α = 0` and `z₁ + z₂ β + z₃ α β = 0` ((3.10), (3.12)); eliminating `β` makes `α`
a root of a non-zero rational quadratic.

## Main results

* `Nat.exists_rel_of_prod_le_div`: the three-variable Subspace step, for points of height `Q n`
  at which the product of the forms is at most `K / Q n`.
* `Nat.false_of_first_case`: **the first case**: such a relation is impossible for algebraic `α`
  that is not a root of a non-zero rational polynomial of degree at most `2`.
-/

@[expose] public section

open Filter

namespace Nat

/-- **A three-variable Subspace step.** For integer points `X n` with first coordinate `Q n → ∞`
and all coordinates at most `Q n`, at which the product of three linearly independent forms with
algebraic coefficients is at most `K / Q n`, a non-zero rational relation `y · X n = 0` holds for
infinitely many `n`. -/
theorem exists_rel_of_prod_le_div {c : Fin 3 → Fin 3 → ℝ} (hc : ∀ i k, IsAlgebraic ℚ (c i k))
    (hind : LinearIndependent ℝ c) (X : ℕ → Fin 3 → ℤ) {Q : ℕ → ℝ}
    (hQ : Tendsto Q atTop atTop) (hX0 : ∀ n, ((X n 0 : ℤ) : ℝ) = Q n)
    (hXle : ∀ n i, |((X n i : ℤ) : ℝ)| ≤ Q n) {K : ℝ}
    (hprod : ∀ n, (∏ i, |∑ k, c i k * (X n k : ℝ)|) ≤ K / Q n) :
    ∃ y : Fin 3 → ℚ, y ≠ 0 ∧ ∃ᶠ n in atTop, ∑ i, (y i : ℝ) * (X n i : ℝ) = 0 := by
  refine Real.exists_ne_zero_frequently_sum_eq_zero hc hind (ε := 1 / 2) (by norm_num) X ?_
  filter_upwards [hQ.eventually_ge_atTop (max (K ^ 2) 1)] with n hn
  have hQ1 : 1 ≤ Q n := le_trans (le_max_right _ _) hn
  have hH : (⨆ i, |((X n i : ℤ) : ℝ)|) = Q n := by
    refine le_antisymm (ciSup_le (hXle n)) ?_
    rw [← hX0 n]
    exact (le_abs_self _).trans
      (le_ciSup (f := fun i ↦ |((X n i : ℤ) : ℝ)|) (Set.finite_range _).bddAbove (0 : Fin 3))
  refine ⟨fun h ↦ ?_, ?_⟩
  · have h0 := hX0 n
    rw [h] at h0
    simp only [Pi.zero_apply, Int.cast_zero] at h0
    linarith
  · rw [hH]
    exact (hprod n).trans (div_le_rpow_neg_half hQ1 (le_trans (le_max_left _ _) hn))

theorem linearIndependent_formsBeta₁ {α β : ℝ} (hβ : β ≠ 0) :
    LinearIndependent ℝ (![![β, -1, 0], ![α, 0, -1], ![0, 1, 0]] : Fin 3 → Fin 3 → ℝ) :=
  Matrix.linearIndependent_rows_of_det_ne_zero
    (A := Matrix.of ![![β, -1, 0], ![α, 0, -1], ![0, 1, 0]])
    (by rw [Matrix.det_fin_three]; simp [hβ])

theorem linearIndependent_formsBeta₂ {α β : ℝ} (hβ : β ≠ 0) :
    LinearIndependent ℝ (![![β, -1, 0], ![0, α, -1], ![0, 1, 0]] : Fin 3 → Fin 3 → ℝ) :=
  Matrix.linearIndependent_rows_of_det_ne_zero
    (A := Matrix.of ![![β, -1, 0], ![0, α, -1], ![0, 1, 0]])
    (by rw [Matrix.det_fin_three]; simp [hβ])

theorem isAlgebraic_formsBeta₁ {α β : ℝ} (hα : IsAlgebraic ℚ α) (hβ : IsAlgebraic ℚ β) :
    ∀ i k, IsAlgebraic ℚ ((![![β, -1, 0], ![α, 0, -1], ![0, 1, 0]] : Fin 3 → Fin 3 → ℝ) i k) := by
  intro i k
  fin_cases i <;> fin_cases k <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
    first
    | exact hα
    | exact hβ
    | exact isAlgebraic_zero
    | exact isAlgebraic_one
    | exact isAlgebraic_one.neg

theorem isAlgebraic_formsBeta₂ {α β : ℝ} (hα : IsAlgebraic ℚ α) (hβ : IsAlgebraic ℚ β) :
    ∀ i k, IsAlgebraic ℚ ((![![β, -1, 0], ![0, α, -1], ![0, 1, 0]] : Fin 3 → Fin 3 → ℝ) i k) := by
  intro i k
  fin_cases i <;> fin_cases k <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
    first
    | exact hα
    | exact hβ
    | exact isAlgebraic_zero
    | exact isAlgebraic_one
    | exact isAlgebraic_one.neg

theorem prod_formsBeta₁ (α β : ℝ) (x : Fin 3 → ℝ) :
    (∏ i, |∑ k, (![![β, -1, 0], ![α, 0, -1], ![0, 1, 0]] : Fin 3 → Fin 3 → ℝ) i k * x k|) =
      |β * x 0 - x 1| * |α * x 0 - x 2| * |x 1| := by
  simp only [Fin.prod_univ_three, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring_nf

theorem prod_formsBeta₂ (α β : ℝ) (x : Fin 3 → ℝ) :
    (∏ i, |∑ k, (![![β, -1, 0], ![0, α, -1], ![0, 1, 0]] : Fin 3 → Fin 3 → ℝ) i k * x k|) =
      |β * x 0 - x 1| * |α * x 1 - x 2| * |x 1| := by
  simp only [Fin.prod_univ_three, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring_nf

variable {a : ℕ → ℕ}

section Positive

variable (ha : ∀ n, 1 ≤ a (n + 1))
include ha

/-- **The first case** of the proof of Theorem 3.1. If `α` is algebraic and not a root of a
non-zero rational polynomial of degree `≤ 2`, then no non-zero rational relation
`Y₁ q_{M+1} + Y₂ q_M + Y₃ p_{M+1} + Y₄ p_M = 0` holds along a sequence `M → ∞`. -/
theorem false_of_first_case (halg : IsAlgebraic ℚ (contFrac a))
    (hq : ∀ A B C : ℚ, (A : ℝ) * contFrac a ^ 2 + B * contFrac a + C = 0 →
      A = 0 ∧ B = 0 ∧ C = 0)
    {M : ℕ → ℕ} (hM : Tendsto M atTop atTop) {Y : Fin 4 → ℚ} (hY : Y ≠ 0)
    (hrel : ∀ n, (Y 0 : ℝ) * contDen a (M n + 1) + Y 1 * contDen a (M n) +
      Y 2 * contNum a (M n + 1) + Y 3 * contNum a (M n) = 0) : False := by
  set α := contFrac a
  have hlin (s t : ℚ) (h : (s : ℝ) * α + t = 0) : s = 0 ∧ t = 0 := by
    obtain ⟨-, h1, h2⟩ := hq 0 s t (by push_cast; linarith)
    exact ⟨h1, h2⟩
  have hα0 : 0 < α := contFrac_pos ha
  have hαabs : |α| ≤ 1 := by rw [abs_of_pos hα0]; exact (contFrac_lt_one ha).le
  -- the errors `e_ℓ = q_ℓ α - p_ℓ`
  set e : ℕ → ℝ := fun ℓ ↦ (contDen a ℓ : ℝ) * α - contNum a ℓ with he
  set Q : ℕ → ℝ := fun n ↦ (contDen a (M n + 1) : ℝ) with hQdef
  have hQ : Tendsto Q atTop atTop :=
    tendsto_contDen_comp ha (tendsto_atTop_mono (fun n ↦ Nat.le_succ (M n)) hM)
  have hQ1 (n : ℕ) : 1 ≤ Q n := by
    change (1 : ℝ) ≤ (contDen a (M n + 1) : ℝ); exact_mod_cast one_le_contDen ha (M n + 1)
  have hQ0 (n : ℕ) : 0 < Q n := by linarith [hQ1 n]
  have hqM (n : ℕ) : (contDen a (M n) : ℝ) ≤ Q n := contDen_mono_real ha (Nat.le_succ _)
  have hqM0 (n : ℕ) : (0 : ℝ) ≤ contDen a (M n) := Nat.cast_nonneg _
  have heM (n : ℕ) : |e (M n)| ≤ 1 / Q n := abs_contDen_mul_contFrac_sub_le ha (M n)
  have heM1 (n : ℕ) : |e (M n + 1)| ≤ 1 / Q n :=
    (abs_contDen_mul_contFrac_sub_le ha (M n + 1)).trans
      (one_div_le_one_div_of_le (hQ0 n) (contDen_mono_real ha (Nat.le_succ _)))
  have hinvQ (n : ℕ) : 1 / Q n ≤ 1 := (div_le_one (hQ0 n)).2 (hQ1 n)
  -- the relation in terms of the errors
  have hstar (n : ℕ) : Q n * ((Y 0 : ℝ) + Y 2 * α) + (contDen a (M n) : ℝ) * ((Y 1 : ℝ) + Y 3 * α)
      = Y 2 * e (M n + 1) + Y 3 * e (M n) := by
    simp only [hQdef, he]; linear_combination hrel n
  -- `D = Y₂ + Y₄ α ≠ 0`
  set D : ℝ := (Y 1 : ℝ) + Y 3 * α with hDdef
  have hD : D ≠ 0 := by
    intro hD0
    obtain ⟨h3, h1⟩ := hlin (Y 3) (Y 1) (by rw [hDdef] at hD0; linarith)
    have hS : (Y 0 : ℝ) + Y 2 * α = 0 := by
      refine eq_zero_of_frequently_abs_le_div (L := |(Y 2 : ℝ)|) hQ
        (Eventually.frequently (Eventually.of_forall fun n ↦ ?_))
      have h := hstar n
      rw [hD0, h3] at h
      push_cast at h
      rw [le_div_iff₀ (hQ0 n), mul_comm, ← abs_of_pos (hQ0 n), ← abs_mul,
        show Q n * ((Y 0 : ℝ) + Y 2 * α) = Y 2 * e (M n + 1) by linarith, abs_mul]
      exact (mul_le_mul_of_nonneg_left ((heM1 n).trans (hinvQ n)) (abs_nonneg _)).trans_eq
        (mul_one _)
    obtain ⟨h2, h0⟩ := hlin (Y 2) (Y 0) (by linarith)
    exact hY (funext fun i ↦ by fin_cases i <;> assumption)
  -- the number `β`
  set β : ℝ := -((Y 0 : ℝ) + Y 2 * α) / D with hβdef
  have hβD : β * D = -((Y 0 : ℝ) + Y 2 * α) := by rw [hβdef]; field_simp
  have hβid (n : ℕ) : D * ((contDen a (M n) : ℝ) - β * Q n) =
      Y 2 * e (M n + 1) + Y 3 * e (M n) := by
    linear_combination hstar n - Q n * hβD
  set Kβ : ℝ := (|(Y 2 : ℝ)| + |(Y 3 : ℝ)|) / |D|
  have hDpos : 0 < |D| := abs_pos.2 hD
  have hKβ : 0 ≤ Kβ := by positivity
  have hβbd (n : ℕ) : |β * Q n - contDen a (M n)| ≤ Kβ / Q n := by
    have h' : D * (β * Q n - contDen a (M n)) = -(Y 2 * e (M n + 1) + Y 3 * e (M n)) := by
      linear_combination -(hβid n)
    have hb : |D| * |β * Q n - contDen a (M n)| ≤
        (|(Y 2 : ℝ)| + |(Y 3 : ℝ)|) * (1 / Q n) := by
      rw [← abs_mul, h', abs_neg]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, add_mul]
      gcongr
      exacts [heM1 n, heM n]
    rw [show Kβ / Q n = ((|(Y 2 : ℝ)| + |(Y 3 : ℝ)|) * (1 / Q n)) / |D| by
      simp only [Kβ]; field_simp]
    rw [le_div_iff₀ hDpos, mul_comm]
    exact hb
  -- `β` is irrational, since `q_M / q_{M+1}` is in lowest terms
  have hβrat (c : ℚ) : β ≠ c := by
    intro hc
    have hden : (0 : ℝ) < c.den := by exact_mod_cast c.den_pos
    obtain ⟨n, hn⟩ := (hQ.eventually_gt_atTop (c.den * Kβ + c.den)).exists
    set z : ℤ := c.num * contDen a (M n + 1) - c.den * contDen a (M n) with hzdef
    have hzβ : (z : ℝ) = c.den * (β * Q n - contDen a (M n)) := by
      rw [hc, hzdef, Rat.cast_def, hQdef]
      push_cast
      field_simp
    have hz : |(z : ℝ)| < 1 := by
      rw [hzβ, abs_mul, abs_of_pos hden]
      calc (c.den : ℝ) * |β * Q n - contDen a (M n)| ≤ c.den * (Kβ / Q n) :=
            mul_le_mul_of_nonneg_left (hβbd n) hden.le
        _ = c.den * Kβ / Q n := by ring
        _ < 1 := by
            rw [div_lt_one (hQ0 n)]
            nlinarith
    have hz0 : z = 0 := Int.abs_lt_one_iff.mp (by exact_mod_cast hz)
    have hdvd : (contDen a (M n + 1) : ℤ) ∣ (c.den : ℤ) * contDen a (M n) :=
      ⟨c.num, by rw [hzdef] at hz0; linarith⟩
    have hcop : IsCoprime (contDen a (M n + 1) : ℤ) (contDen a (M n) : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr (coprime_contDen_succ a (M n)).symm
    have hle := Int.le_of_dvd (by exact_mod_cast c.den_pos) (hcop.dvd_of_dvd_mul_right hdvd)
    have : Q n ≤ c.den := by change (contDen a (M n + 1) : ℝ) ≤ c.den; exact_mod_cast hle
    nlinarith
  have hβ0 : β ≠ 0 := by simpa using hβrat 0
  have hβalg : IsAlgebraic ℚ β := by
    have hnum : IsAlgebraic ℚ ((Y 0 : ℝ) + Y 2 * α) :=
      (isAlgebraic_ratCast _).add ((isAlgebraic_ratCast _).mul halg)
    have hden : IsAlgebraic ℚ D := (isAlgebraic_ratCast _).add ((isAlgebraic_ratCast _).mul halg)
    rw [hβdef, div_eq_mul_inv]
    exact hnum.neg.mul hden.inv
  -- the Subspace step at `(q_{M+1}, q_M, p_{M+1})`: `y₁ + y₂ β + y₃ α = 0`
  obtain ⟨y, hy0, hyrel⟩ := exists_rel_of_prod_le_div (isAlgebraic_formsBeta₁ halg hβalg)
    (linearIndependent_formsBeta₁ hβ0)
    (fun n ↦ ![contDen a (M n + 1), contDen a (M n), contNum a (M n + 1)]) hQ
    (fun n ↦ by simp [Q]) (fun n i ↦ by
      fin_cases i
      · simp [Q]
      · simpa using hqM n
      · simpa [Q] using contNum_le_contDen_real ha (M n + 1))
    (K := Kβ) (fun n ↦ by
      rw [prod_formsBeta₁]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, Int.cast_natCast]
      have h2 : |α * Q n - contNum a (M n + 1)| ≤ 1 / Q n := by
        rw [mul_comm]; exact heM1 n
      calc |β * Q n - contDen a (M n)| * |α * Q n - contNum a (M n + 1)| *
            |(contDen a (M n) : ℝ)|
          ≤ (Kβ / Q n) * (1 / Q n) * Q n := by
            gcongr
            · exact hβbd n
            · rw [abs_of_nonneg (hqM0 n)]; exact hqM n
        _ = Kβ / Q n := by field_simp)
  have hT : (y 0 : ℝ) + y 1 * β + y 2 * α = 0 := by
    refine eq_zero_of_frequently_abs_le_div (L := |(y 1 : ℝ)| * Kβ + |(y 2 : ℝ)|) hQ
      (hyrel.mono fun n hn ↦ ?_)
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Int.cast_natCast] at hn
    have hid : Q n * ((y 0 : ℝ) + y 1 * β + y 2 * α) =
        y 1 * (β * Q n - contDen a (M n)) + y 2 * e (M n + 1) := by
      simp only [he]; linear_combination hn
    rw [le_div_iff₀ (hQ0 n), mul_comm, ← abs_of_pos (hQ0 n), ← abs_mul, hid]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 : |β * Q n - contDen a (M n)| ≤ Kβ := (hβbd n).trans (_root_.div_le_self hKβ (hQ1 n))
    have h2 : |e (M n + 1)| ≤ 1 := (heM1 n).trans (hinvQ n)
    have m1 : |(y 1 : ℝ)| * |β * Q n - contDen a (M n)| ≤ |(y 1 : ℝ)| * Kβ :=
      mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    have m2 : |(y 2 : ℝ)| * |e (M n + 1)| ≤ |(y 2 : ℝ)| * 1 :=
      mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    linarith
  -- the Subspace step at `(q_{M+1}, q_M, p_M)`: `z₁ + z₂ β + z₃ α β = 0`
  obtain ⟨z, hz0, hzrel⟩ := exists_rel_of_prod_le_div (isAlgebraic_formsBeta₂ halg hβalg)
    (linearIndependent_formsBeta₂ hβ0)
    (fun n ↦ ![contDen a (M n + 1), contDen a (M n), contNum a (M n)]) hQ
    (fun n ↦ by simp [Q]) (fun n i ↦ by
      fin_cases i
      · simp [Q]
      · simpa using hqM n
      · simpa using (contNum_le_contDen_real ha (M n)).trans (hqM n))
    (K := Kβ) (fun n ↦ by
      rw [prod_formsBeta₂]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, Int.cast_natCast]
      have h2 : |α * contDen a (M n) - contNum a (M n)| ≤ 1 / Q n := by
        rw [mul_comm]; exact heM n
      calc |β * Q n - contDen a (M n)| * |α * contDen a (M n) - contNum a (M n)| *
            |(contDen a (M n) : ℝ)|
          ≤ (Kβ / Q n) * (1 / Q n) * Q n := by
            gcongr
            · exact hβbd n
            · rw [abs_of_nonneg (hqM0 n)]; exact hqM n
        _ = Kβ / Q n := by field_simp)
  have hU : (z 0 : ℝ) + z 1 * β + z 2 * (α * β) = 0 := by
    refine eq_zero_of_frequently_abs_le_div
      (L := |(z 1 : ℝ)| * Kβ + |(z 2 : ℝ)| * (Kβ + 1)) hQ (hzrel.mono fun n hn ↦ ?_)
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Int.cast_natCast] at hn
    have hid : Q n * ((z 0 : ℝ) + z 1 * β + z 2 * (α * β)) =
        z 1 * (β * Q n - contDen a (M n)) +
          z 2 * (α * (β * Q n - contDen a (M n)) + e (M n)) := by
      simp only [he]; linear_combination hn
    rw [le_div_iff₀ (hQ0 n), mul_comm, ← abs_of_pos (hQ0 n), ← abs_mul, hid]
    have h1 : |β * Q n - contDen a (M n)| ≤ Kβ := (hβbd n).trans (_root_.div_le_self hKβ (hQ1 n))
    have h2 : |e (M n)| ≤ 1 := (heM n).trans (hinvQ n)
    have h3 : |α * (β * Q n - contDen a (M n)) + e (M n)| ≤ Kβ + 1 := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul]
      have : |α| * |β * Q n - contDen a (M n)| ≤ 1 * Kβ :=
        mul_le_mul hαabs h1 (abs_nonneg _) zero_le_one
      linarith
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have m1 : |(z 1 : ℝ)| * |β * Q n - contDen a (M n)| ≤ |(z 1 : ℝ)| * Kβ :=
      mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    have m2 : |(z 2 : ℝ)| * |α * (β * Q n - contDen a (M n)) + e (M n)| ≤
        |(z 2 : ℝ)| * (Kβ + 1) :=
      mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
    linarith
  -- eliminate `β`
  have hy1 : y 1 ≠ 0 := by
    intro h1
    rw [h1] at hT
    push_cast at hT
    obtain ⟨h2, h0⟩ := hlin (y 2) (y 0) (by linarith)
    exact hy0 (funext fun i ↦ by fin_cases i <;> assumption)
  obtain ⟨hA, hB, -⟩ := hq (-(z 2 * y 2)) (-(z 1 * y 2 + z 2 * y 0)) (z 0 * y 1 - z 1 * y 0)
    (by push_cast; linear_combination (y 1 : ℝ) * hU - ((z 1 : ℝ) + z 2 * α) * hT)
  by_cases hz2 : z 2 = 0
  · rw [hz2] at hU
    push_cast at hU
    by_cases hz1 : z 1 = 0
    · rw [hz1] at hU
      push_cast at hU
      have hz00 : z 0 = 0 := by exact_mod_cast (by linarith : (z 0 : ℝ) = 0)
      exact hz0 (funext fun i ↦ by fin_cases i <;> assumption)
    · refine hβrat (-(z 0) / z 1) ?_
      have : (z 1 : ℝ) ≠ 0 := by exact_mod_cast hz1
      push_cast
      field_simp
      linarith
  · have hy2 : y 2 = 0 := by
      rcases _root_.mul_eq_zero.mp (neg_eq_zero.mp hA) with h | h
      · exact absurd h hz2
      · exact h
    rw [hy2] at hB
    have hy00 : y 0 = 0 := by
      have : z 2 * y 0 = 0 := by simpa using hB
      rcases _root_.mul_eq_zero.mp this with h | h
      · exact absurd h hz2
      · exact h
    rw [hy00, hy2] at hT
    push_cast at hT
    have : (y 1 : ℝ) ≠ 0 := by exact_mod_cast hy1
    exact hβ0 (by
      rcases _root_.mul_eq_zero.mp (show (y 1 : ℝ) * β = 0 by linarith) with h | h
      · exact absurd h this
      · exact h)

end Positive

end Nat
