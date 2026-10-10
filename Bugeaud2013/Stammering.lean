/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Bugeaud2013.Claim
public import Bugeaud2013.Subspace

-- Used only inside proofs.
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# The proof of Bugeaud 2013, Theorem 3.1

Let `α = [0; a₁, a₂, …]` with `q_ℓ ≤ 2^{K ℓ}` and normalized lengths `(w_n, u_n, v_n)` of
Condition `(♠)` (`Nat.SpadeData`). If `α` is algebraic, then it satisfies a non-trivial
quadratic equation over `ℚ` (`Nat.false_of_spadeData`, in `Bugeaud2013/Theorem31.lean`). This
file holds the two Subspace applications at the points `v_n`.

The proof follows the paper.

* **The first Subspace application** (`Nat.exists_spade_relation`): the four forms
  `α² X₁ - α (X₂ + X₃) + X₄`, `α X₁ - X₂`, `α X₁ - X₃`, `X₁` at `v_n = (A, B₂, B₃, C)` have
  product at most `96 · 2^{-u_n} ≤ |v_n|^{-ε}`, so a relation `x · v_n = 0` holds infinitely often.
* **First case** (`Nat.false_of_first_case`): `w_n = ℓ` infinitely often. The relation becomes
  `Y₁ q_{N} + Y₂ q_{N-1} + Y₃ p_N + Y₄ p_{N-1} = 0` with `N → ∞`; the number
  `β = lim q_{N-1} / q_N` lies in `ℚ(α)`, is irrational, and two three-variable applications give
  `y₁ + y₂ β + y₃ α = 0` and `z₁ + z₂ β + z₃ α β = 0`, whence a quadratic equation for `α`. The
  paper shifts `α` to make `w_n = 0`; here the shift is absorbed in `Y`, which also covers
  `ℓ ≥ 1` directly. The estimate `|β q_N - q_{N-1}| ≤ K / q_N` comes straight from the relation and
  (2.2), without the paper's limit argument (3.8).
* **Second case**: `w_n → ∞`. The Claim (`Nat.claim`) gives `x₁ = x₄ = 0`, `x₂ = -x₃`, so
  `B₂ = B₃`; a three-variable application (`Nat.exists_spade_relation_three`) and the Claim again
  give `t₁ + t₂ α + t₃ α² = 0`.

## Main results

* `Nat.le_rpow_of_le_ninetySix`: the product bound `96 · 2^{-u}` is at most `|v_n|^{-ε}`.
* `Nat.exists_spade_relation`, `Nat.exists_spade_relation_three`: the two Subspace steps at
  `v_n`. The first case is `Bugeaud2013/FirstCase.lean`, the assembly
  `Bugeaud2013/Theorem31.lean`.
-/

@[expose] public section

open Filter

namespace Nat

/-- `96 / 2^u ≤ 2^{-u/2}` for `u ≥ 14`. -/
theorem ninetySix_div_two_pow_le {u : ℕ} (hu : 14 ≤ u) :
    (96 : ℝ) / 2 ^ u ≤ (2 : ℝ) ^ (-(u : ℝ) / 2) := by
  have h7 : (96 : ℝ) ≤ (2 : ℝ) ^ ((u : ℝ) / 2) := by
    have hu' : (14 : ℝ) ≤ u := by exact_mod_cast hu
    calc (96 : ℝ) ≤ 2 ^ ((7 : ℕ) : ℝ) := by rw [Real.rpow_natCast]; norm_num
      _ ≤ 2 ^ ((u : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
  rw [show -(u : ℝ) / 2 = (u : ℝ) / 2 - u by ring, Real.rpow_sub (by norm_num), Real.rpow_natCast]
  exact div_le_div_of_nonneg_right h7 (by positivity)

/-- `2^{-m ε} ≤ H^{-ε}` for `0 < H ≤ 2^m`, `ε ≥ 0`. -/
theorem two_rpow_neg_le {H : ℝ} (hH : 0 < H) {m : ℕ} (h : H ≤ 2 ^ m) {ε : ℝ} (hε : 0 ≤ ε) :
    (2 : ℝ) ^ (-((m : ℝ) * ε)) ≤ H ^ (-ε) := by
  calc (2 : ℝ) ^ (-((m : ℝ) * ε)) = ((2 : ℝ) ^ m) ^ (-ε) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; ring_nf
    _ ≤ H ^ (-ε) := Real.rpow_le_rpow_of_nonpos hH h (by linarith)

/-- `K / q ≤ q^{-1/2}` for `q ≥ max(K², 1)`. -/
theorem div_le_rpow_neg_half {K q : ℝ} (hq1 : 1 ≤ q) (hq : K ^ 2 ≤ q) :
    K / q ≤ q ^ (-(1 / 2 : ℝ)) := by
  have hq0 : 0 < q := by linarith
  rw [Real.rpow_neg hq0.le, ← Real.sqrt_eq_rpow, div_le_iff₀ hq0]
  have hs : K ≤ √q := Real.le_sqrt_of_sq_le hq
  have hsq : √q * √q = q := Real.mul_self_sqrt hq0.le
  have hs0 : 0 < √q := Real.sqrt_pos.2 hq0
  calc K ≤ √q := hs
    _ = (√q)⁻¹ * (√q * √q) := by rw [← mul_assoc, inv_mul_cancel₀ hs0.ne', one_mul]
    _ = (√q)⁻¹ * q := by rw [hsq]

/-- A rational number is algebraic over `ℚ`. -/
theorem isAlgebraic_ratCast (c : ℚ) : IsAlgebraic ℚ (c : ℝ) := by
  simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℝ) c

variable {a : ℕ → ℕ}

section Positive

variable (ha : ∀ n, 1 ≤ a (n + 1))
include ha

/-- **The bound feeding the Subspace Theorem.** If `P ≤ 96 · 2^{-u}`, `u ≥ 14`,
`w + r ≤ (C + 1) u` and `1 ≤ H ≤ q_w q_{w+r}` (the height of the point), then
`P ≤ H^{-ε}` with `ε = 1 / (4 (K + 1) (C + 1))`, where `q_ℓ ≤ 2^{K ℓ}`. -/
theorem le_rpow_of_le_ninetySix {K : ℕ} (hK : ∀ ℓ, (contDen a ℓ : ℝ) ≤ 2 ^ (K * ℓ))
    {j r u C : ℕ} (hu : 14 ≤ u) (hC : j + 1 + r ≤ (C + 1) * u) {H : ℝ} (hH1 : 1 ≤ H)
    (hH : H ≤ contDen a (j + 1) * contDen a (j + 1 + r)) {P : ℝ} (hP : P ≤ 96 / 2 ^ u) :
    P ≤ H ^ (-(1 / (4 * ((K : ℝ) + 1) * ((C : ℝ) + 1)))) := by
  set m : ℕ := 2 * (K + 1) * ((C + 1) * u)
  have hq1 : (contDen a (j + 1) : ℝ) ≤ contDen a (j + 1 + r) := contDen_mono_real ha (by omega)
  have hHm : H ≤ 2 ^ m := by
    calc H ≤ (contDen a (j + 1 + r) : ℝ) * contDen a (j + 1 + r) :=
          hH.trans (mul_le_mul_of_nonneg_right hq1 (Nat.cast_nonneg _))
      _ ≤ (2 : ℝ) ^ (K * (j + 1 + r)) * 2 ^ (K * (j + 1 + r)) :=
          mul_le_mul (hK _) (hK _) (Nat.cast_nonneg _) (by positivity)
      _ = 2 ^ (2 * (K * (j + 1 + r))) := by rw [← pow_add]; ring_nf
      _ ≤ 2 ^ m := by
          refine pow_le_pow_right₀ (by norm_num) ?_
          have : K * (j + 1 + r) ≤ (K + 1) * ((C + 1) * u) :=
            Nat.mul_le_mul (Nat.le_succ K) hC
          simp only [m]
          linarith
  have hε : (0 : ℝ) ≤ 1 / (4 * ((K : ℝ) + 1) * ((C : ℝ) + 1)) := by positivity
  have h2 := two_rpow_neg_le (by linarith) hHm hε
  have hmε : -((m : ℝ) * (1 / (4 * ((K : ℝ) + 1) * ((C : ℝ) + 1)))) = -(u : ℝ) / 2 := by
    simp only [m]; push_cast; field_simp; ring
  rw [hmε] at h2
  exact hP.trans ((ninetySix_div_two_pow_le hu).trans h2)

omit ha in
/-- The coefficients of the four forms of the first Subspace application are algebraic. -/
theorem isAlgebraic_formsFour (halg : IsAlgebraic ℚ (contFrac a)) :
    ∀ i k, IsAlgebraic ℚ ((![![contFrac a ^ 2, -contFrac a, -contFrac a, 1],
      ![contFrac a, -1, 0, 0], ![contFrac a, 0, -1, 0], ![1, 0, 0, 0]] :
        Fin 4 → Fin 4 → ℝ) i k) := by
  intro i k
  fin_cases i <;> fin_cases k <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons] <;>
    first
    | exact halg
    | exact halg.neg
    | exact halg.pow 2
    | exact isAlgebraic_zero
    | exact isAlgebraic_one
    | exact isAlgebraic_one.neg

omit ha in
/-- The four forms of the first Subspace application are linearly independent. -/
theorem linearIndependent_formsFour (α : ℝ) :
    LinearIndependent ℝ (![![α ^ 2, -α, -α, 1], ![α, -1, 0, 0], ![α, 0, -1, 0], ![1, 0, 0, 0]] :
      Fin 4 → Fin 4 → ℝ) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h (k : Fin 4) := congrFun hg k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply] at h
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2 h3
  have e0 : g 0 = 0 := by linarith
  have e1 : g 1 = 0 := by rw [e0] at h1; linarith
  have e2 : g 2 = 0 := by rw [e0] at h2; linarith
  have e3 : g 3 = 0 := by rw [e0, e1, e2] at h0; linarith
  intro i
  fin_cases i
  exacts [e0, e1, e2, e3]

omit ha in
theorem prod_formsFour (α : ℝ) (x : Fin 4 → ℝ) :
    (∏ i, |∑ k, (![![α ^ 2, -α, -α, 1], ![α, -1, 0, 0], ![α, 0, -1, 0], ![1, 0, 0, 0]] :
      Fin 4 → Fin 4 → ℝ) i k * x k|) =
      |α ^ 2 * x 0 - α * (x 1 + x 2) + x 3| * |α * x 0 - x 1| * |α * x 0 - x 2| * |x 0| := by
  simp only [Fin.prod_univ_four, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring_nf

omit ha in
/-- The facts about `(j, r, u) = (w_n - 1, u_n + v_n, u_n)` used at a single `n`. -/
private theorem spadeData_at {w u v : ℕ → ℕ} {C : ℕ} (hd : SpadeData a w u v C) (n : ℕ) :
    (∀ m, w n - 1 + 1 < m → m ≤ w n - 1 + 1 + u n → a (m + (u n + v n)) = a m) ∧
      w n - 1 + 1 + (u n + v n) ≤ (C + 1) * u n := by
  have h1 := hd.one_le n
  have h2 := hd.le n
  refine ⟨fun m hm1 hm2 ↦ hd.rep n m (by omega) (by omega), ?_⟩
  rw [add_mul, one_mul]
  omega

/-- **The first Subspace application** (Bugeaud 2013, (3.5)): a non-zero rational relation
`x · v_n = 0` holds for infinitely many `n`. -/
theorem exists_spade_relation (halg : IsAlgebraic ℚ (contFrac a)) {K : ℕ}
    (hK : ∀ ℓ, (contDen a ℓ : ℝ) ≤ 2 ^ (K * ℓ)) {w u v : ℕ → ℕ} {C : ℕ}
    (hd : SpadeData a w u v C) :
    ∃ x : Fin 4 → ℚ, x ≠ 0 ∧ ∃ᶠ n in atTop,
      ∑ i, (x i : ℝ) * (spadeVec a (w n - 1) (u n + v n) i : ℝ) = 0 := by
  refine Real.exists_ne_zero_frequently_sum_eq_zero (isAlgebraic_formsFour halg)
    (linearIndependent_formsFour _)
    (ε := 1 / (4 * ((K : ℝ) + 1) * ((C : ℝ) + 1))) (by positivity) _ ?_
  filter_upwards [hd.tendsto.eventually_ge_atTop 14] with n hn
  obtain ⟨hrep, hC⟩ := spadeData_at hd n
  have hr : 1 ≤ u n + v n := by omega
  have hA0 := spadeVec_zero_ne ha (w n - 1) hr
  refine ⟨fun h ↦ hA0 (congrFun h 0), ?_⟩
  rw [prod_formsFour]
  refine le_rpow_of_le_ninetySix ha hK hn hC ?_ (iSup_abs_spadeVec_le ha _ _)
    (spade_prod_four_le ha (by omega) (by omega) hrep)
  refine le_trans ?_ (le_ciSup (Set.finite_range _).bddAbove (0 : Fin 4))
  have : (1 : ℤ) ≤ |spadeVec a (w n - 1) (u n + v n) 0| := Int.one_le_abs hA0
  exact_mod_cast this

omit ha in
/-- The coefficients of the three forms of the last Subspace application are algebraic. -/
theorem isAlgebraic_formsThree (halg : IsAlgebraic ℚ (contFrac a)) :
    ∀ i k, IsAlgebraic ℚ ((![![contFrac a ^ 2, -(2 * contFrac a), 1], ![contFrac a, -1, 0],
      ![1, 0, 0]] : Fin 3 → Fin 3 → ℝ) i k) := by
  have h2 : IsAlgebraic ℚ (2 * contFrac a) := by
    simpa using (isAlgebraic_ratCast 2).mul halg
  intro i k
  fin_cases i <;> fin_cases k <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
    first
    | exact halg
    | exact h2.neg
    | exact halg.pow 2
    | exact isAlgebraic_zero
    | exact isAlgebraic_one
    | exact isAlgebraic_one.neg

omit ha in
theorem linearIndependent_formsThree (α : ℝ) :
    LinearIndependent ℝ (![![α ^ 2, -(2 * α), 1], ![α, -1, 0], ![1, 0, 0]] :
      Fin 3 → Fin 3 → ℝ) :=
  Matrix.linearIndependent_rows_of_det_ne_zero
    (A := Matrix.of ![![α ^ 2, -(2 * α), 1], ![α, -1, 0], ![1, 0, 0]])
    (by rw [Matrix.det_fin_three]; norm_num)

omit ha in
theorem prod_formsThree (α : ℝ) (x : Fin 3 → ℝ) :
    (∏ i, |∑ k, (![![α ^ 2, -(2 * α), 1], ![α, -1, 0], ![1, 0, 0]] :
      Fin 3 → Fin 3 → ℝ) i k * x k|) =
      |α ^ 2 * x 0 - α * (x 1 + x 1) + x 2| * |α * x 0 - x 1| * |x 0| := by
  simp only [Fin.prod_univ_three, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring_nf

/-- **The last Subspace application** (Bugeaud 2013, (3.17)): if `B₂ = B₃` at every `v_n`, a
non-zero rational relation `t₁ A + t₂ B₂ + t₃ C = 0` holds for infinitely many `n`. -/
theorem exists_spade_relation_three (halg : IsAlgebraic ℚ (contFrac a)) {K : ℕ}
    (hK : ∀ ℓ, (contDen a ℓ : ℝ) ≤ 2 ^ (K * ℓ)) {w u v : ℕ → ℕ} {C : ℕ}
    (hd : SpadeData a w u v C)
    (hB : ∀ n, spadeVec a (w n - 1) (u n + v n) 1 = spadeVec a (w n - 1) (u n + v n) 2) :
    ∃ t : Fin 3 → ℚ, t ≠ 0 ∧ ∃ᶠ n in atTop,
      (t 0 : ℝ) * (spadeVec a (w n - 1) (u n + v n) 0 : ℝ) +
        t 1 * (spadeVec a (w n - 1) (u n + v n) 1 : ℝ) +
        t 2 * (spadeVec a (w n - 1) (u n + v n) 3 : ℝ) = 0 := by
  set X : ℕ → Fin 3 → ℤ := fun n ↦ ![spadeVec a (w n - 1) (u n + v n) 0,
    spadeVec a (w n - 1) (u n + v n) 1, spadeVec a (w n - 1) (u n + v n) 3]
  suffices hev : ∀ᶠ n in atTop, X n ≠ 0 ∧
      (∏ i, |∑ k, (![![contFrac a ^ 2, -(2 * contFrac a), 1], ![contFrac a, -1, 0],
        ![1, 0, 0]] : Fin 3 → Fin 3 → ℝ) i k * (X n k : ℝ)|) ≤
        (⨆ i, |(X n i : ℝ)|) ^ (-(1 / (4 * ((K : ℝ) + 1) * ((C : ℝ) + 1)))) by
    obtain ⟨t, ht, hfr⟩ := Real.exists_ne_zero_frequently_sum_eq_zero
      (isAlgebraic_formsThree halg) (linearIndependent_formsThree _) (by positivity) X hev
    refine ⟨t, ht, hfr.mono fun n hn ↦ ?_⟩
    simpa [X, Fin.sum_univ_three] using hn
  filter_upwards [hd.tendsto.eventually_ge_atTop 14] with n hn
  obtain ⟨hrep, hC⟩ := spadeData_at hd n
  have hr : 1 ≤ u n + v n := by omega
  have hA0 := spadeVec_zero_ne ha (w n - 1) hr
  refine ⟨fun h ↦ hA0 (congrFun h 0), ?_⟩
  rw [prod_formsThree]
  have hP := spade_prod_three_le ha (by omega) (by omega) hrep
  rw [show ((spadeVec a (w n - 1) (u n + v n) 2 : ℤ) : ℝ) = spadeVec a (w n - 1) (u n + v n) 1 by
    rw [hB n]] at hP
  refine le_rpow_of_le_ninetySix ha hK hn hC ?_ ?_ hP
  · refine le_trans ?_ (le_ciSup (Set.finite_range _).bddAbove (0 : Fin 3))
    have : (1 : ℤ) ≤ |spadeVec a (w n - 1) (u n + v n) 0| := Int.one_le_abs hA0
    exact_mod_cast this
  · refine ciSup_le fun i ↦ ?_
    fin_cases i
    · exact abs_spadeVec_le ha _ _ 0
    · exact abs_spadeVec_le ha _ _ 1
    · exact abs_spadeVec_le ha _ _ 3

end Positive

end Nat
