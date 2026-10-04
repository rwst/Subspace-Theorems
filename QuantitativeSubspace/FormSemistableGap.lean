/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.FormIntervalTheorem

-- Used only inside proofs.
import Mathlib.Combinatorics.Pigeonhole

/-!
# EF13 Theorem 8.1 and the semistable gap

J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative Subspace Theorem*,
Ann. of Math. **177** (2013), 513–590, Theorem 8.1.

* `Real.exists_cover_of_not_chain`: a set of reals `> 1` without an `ω`-chain of length `M`
  (`log q_{i+1} ≥ ω log q_i`) lies in `M - 1` intervals `[a, a^{2ω}]`.
* `Real.exists_subchain`: the pigeonhole step, a chain of length `K m + 1` coloured by `K`
  colours has a monochromatic subchain of length `m + 1`.
* The size conditions on `Q` of §§9–13 and the two thresholds of §14 from `log Q ≥ log C₂`:
  `FormSystem.sqrt_pow_le_absDet_mul`, …, `FormSystem.thetaOne_lt`, `FormSystem.thetaTwo_lt`.
* The parameters `gapEps` (`ε`), `gapBlocks` (`m`), `gapRatio` (`ω = 4m/ε`), `gapIntervals`
  (`(n - 1)(m - 1)`) and `gapThreshold` (`log C₂`, linear in `log H_L`).
* **Theorem 8.1**: `FormSystem.exists_intervals`.
* `NumberField.semistableGap`: `SemistableGap K Ω` for `K : Type` and `Ω` algebraically closed,
  the hypothesis of Thm 16.1 (Q3.5), Prop. 17.5 (Q3.6) and Lemmas 18.1–18.4 (Q3.7), which all
  assume `IsAlgClosed Ω`; pass `semistableGap K Ω`.

## Implementation notes

The constants are this file's, not EF13's: `ε = δ/(40 n² 2ⁿ)` (EF13: `δ/(11 n² 2^{n-1})`),
`m` from the explicit count of Prop. 13.6, intervals `[a, a^{2ω}]` with `ω = 4m/ε` (EF13:
`[Q_h, Q_h^{ω₂})`, `ω₂ = m₂^{5/2}`), and `C₂ = exp(gapThreshold)`. The exponent `2ω` instead of
`ω` comes from the covering: the infimum of the exceptional set need not be exceptional.

This is milestone Q4.1d of `QuantitativeSubspace/README.md`.
-/

@[expose] public section

open Finset Module Real

namespace Real

/-- An `ω`-chain of length `M` in `S`: `q_0, …, q_{M-1} ∈ S` with `ω log q_i ≤ log q_{i+1}`. -/
def IsLogChain (S : Set ℝ) (ω : ℝ) {M : ℕ} (q : Fin M → ℝ) : Prop :=
  (∀ i, q i ∈ S) ∧ ∀ i j : Fin M, (i : ℕ) + 1 = j → ω * Real.log (q i) ≤ Real.log (q j)

/-- **The covering of EF13 (8.10).** A set `S` of reals `> 1`, bounded below away from `1`, with
no `ω`-chain of length `M ≥ 1` lies in `M - 1` intervals `[a_i, a_i^{2ω}]`, `a_i > 1`. -/
theorem exists_cover_of_not_chain {ω : ℝ} (hω : 0 ≤ ω) {T : ℝ} (hT : 1 < T) :
    ∀ (M : ℕ) (S : Set ℝ), (∀ q ∈ S, T ≤ q) →
      (∀ q : Fin (M + 1) → ℝ, ¬ IsLogChain S ω q) →
      ∃ a : Fin M → ℝ, (∀ i, 1 < a i) ∧ ∀ q ∈ S, ∃ i, a i ≤ q ∧ q ≤ a i ^ (2 * ω) := by
  intro M
  induction M with
  | zero =>
    intro S _ hS
    refine ⟨Fin.elim0, fun i ↦ i.elim0, fun q hq ↦ ?_⟩
    exact absurd ⟨fun _ ↦ hq, fun i j hij ↦ by omega⟩ (hS fun _ ↦ q)
  | succ M ih =>
    intro S hST hS
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exact ⟨fun _ ↦ T, fun _ ↦ hT, fun q hq ↦ hq.elim⟩
    have hbdd : BddBelow S := ⟨T, hST⟩
    set q₀ := sInf S
    have hq₀T : T ≤ q₀ := le_csInf hne hST
    have hq₀ : 1 < q₀ := hT.trans_le hq₀T
    -- a point `s₀ ∈ S` with `s₀ < q₀²`
    obtain ⟨s₀, hs₀S, hs₀⟩ := exists_lt_of_csInf_lt hne
      (show q₀ < q₀ ^ 2 by nlinarith)
    have hs₀1 : 1 < s₀ := hT.trans_le (hST s₀ hs₀S)
    set S' := {q ∈ S | ω * Real.log s₀ ≤ Real.log q}
    have hS' : ∀ q : Fin (M + 1) → ℝ, ¬ IsLogChain S' ω q := by
      intro q hq
      refine hS (Fin.cons s₀ q) ⟨fun i ↦ ?_, fun i j hij ↦ ?_⟩
      · refine Fin.cases hs₀S (fun i ↦ (hq.1 i).1) i
      · obtain ⟨j, rfl⟩ : ∃ j' : Fin (M + 1), j = j'.succ :=
          ⟨j.pred (by intro h; rw [h] at hij; simp at hij), by simp⟩
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
        · have : j = 0 := Fin.ext (by simp at hij; omega)
          subst this
          simpa using (hq.1 0).2
        · simpa using hq.2 i j (by simpa using hij)
    obtain ⟨a, ha1, ha⟩ := ih S' (fun q hq ↦ hST q hq.1) hS'
    refine ⟨Fin.cons q₀ a, fun i ↦ Fin.cases hq₀ ha1 i, fun q hq ↦ ?_⟩
    by_cases hq' : ω * Real.log s₀ ≤ Real.log q
    · obtain ⟨i, hi⟩ := ha q ⟨hq, hq'⟩
      exact ⟨i.succ, by simpa using hi⟩
    · refine ⟨0, by simpa using csInf_le hbdd hq, ?_⟩
      simp only [Fin.cons_zero]
      have hq1 : 0 < q := zero_lt_one.trans (hT.trans_le (hST q hq))
      rw [← Real.log_le_log_iff hq1 (Real.rpow_pos_of_pos (zero_lt_one.trans hq₀) _),
        Real.log_rpow (zero_lt_one.trans hq₀)]
      have h1 : Real.log s₀ ≤ 2 * Real.log q₀ := by
        rw [← Real.log_rpow (zero_lt_one.trans hq₀)]
        exact Real.log_le_log (zero_lt_one.trans hs₀1) (by exact_mod_cast hs₀.le)
      nlinarith [mul_le_mul_of_nonneg_left h1 hω]

/-- Along an `ω`-chain of reals `> 1` with `ω ≥ 1`, `ω log q_i ≤ log q_j` for all `i < j`. -/
theorem IsLogChain.mul_log_le {S : Set ℝ} {ω : ℝ} (hω1 : 1 ≤ ω) (hS1 : ∀ q ∈ S, 1 < q) {M : ℕ}
    {q : Fin M → ℝ} (hq : IsLogChain S ω q) {i j : Fin M} (hij : i < j) :
    ω * Real.log (q i) ≤ Real.log (q j) := by
  have key : ∀ t : ℕ, ∀ j : Fin M, (j : ℕ) = i + t + 1 →
      ω * Real.log (q i) ≤ Real.log (q j) := by
    intro t
    induction t with
    | zero => exact fun j hj ↦ hq.2 i j (by omega)
    | succ t ih =>
      intro j hj
      have hj' : (i : ℕ) + t + 1 < M := by omega
      set j' : Fin M := ⟨i + t + 1, hj'⟩
      have h1 := ih j' rfl
      have h2 : 0 ≤ Real.log (q j') := (Real.log_pos (hS1 _ (hq.1 j'))).le
      have h3 := hq.2 j' j (by simp [j']; omega)
      nlinarith
  exact key (j - i - 1) j (by have := Fin.lt_def.mp hij; omega)

/-- **Pigeonhole for chains.** An `ω`-chain of length `K m + 1` coloured by at most `K` colours
has a monochromatic `ω`-subchain of length `m + 1`. -/
theorem exists_subchain {S : Set ℝ} {ω : ℝ} (hω1 : 1 ≤ ω) (hS1 : ∀ q ∈ S, 1 < q) {K m : ℕ}
    {q : Fin (K * m + 1) → ℝ} (hq : IsLogChain S ω q) (col : Fin (K * m + 1) → ℕ)
    (t : Finset ℕ) (hcol : ∀ i, col i ∈ t) (ht : #t ≤ K) :
    ∃ c ∈ t, ∃ g : Fin (m + 1) → Fin (K * m + 1), (∀ a, col (g a) = c) ∧
      IsLogChain S ω (q ∘ g) := by
  classical
  obtain ⟨c, hc, hcard⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := (univ : Finset (Fin (K * m + 1)))) (fun i _ ↦ hcol i)
    (show #t * m < #(univ : Finset (Fin (K * m + 1))) by
      rw [card_univ, Fintype.card_fin]
      have := Nat.mul_le_mul_right m ht
      omega)
  set Fc := {x ∈ (univ : Finset (Fin (K * m + 1))) | col x = c}
  set e := Fc.orderEmbOfFin rfl
  set g : Fin (m + 1) → Fin (K * m + 1) := fun a ↦ e (Fin.castLE hcard a)
  refine ⟨c, hc, g, fun a ↦ ?_, fun a ↦ hq.1 _, fun a b hab ↦ ?_⟩
  · have := Fc.orderEmbOfFin_mem rfl (Fin.castLE hcard a)
    exact (mem_filter.mp this).2
  · refine hq.mul_log_le hω1 hS1 (e.strictMono ?_)
    rw [Fin.lt_def]
    simp only [Fin.val_castLE]
    omega

end Real

/-! ### The size conditions on `Q` -/

namespace NumberField.FormSystem

variable {K : Type*} [Field K] [NumberField K] {n : ℕ} (L : FormSystem K (Fin n))

theorem one_le_absFormHeight : 1 ≤ L.absFormHeight :=
  Real.one_le_rpow L.one_le_mulFormHeight (by positivity)

theorem log_mulFormHeight :
    Real.log L.mulFormHeight = finrank ℚ K * Real.log L.absFormHeight := by
  have hd : (finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  rw [absFormHeight, Real.log_rpow (zero_lt_one.trans_le L.one_le_mulFormHeight),
    mul_inv_cancel_left₀ hd]

/-- `X ≤ Q^a` from `log X ≤ a log Q`. -/
private theorem le_rpow_of_log_le {X a Q : ℝ} (hX : 0 < X) (hQ : 0 < Q)
    (h : Real.log X ≤ a * Real.log Q) : X ≤ Q ^ a := by
  rwa [← Real.log_le_log_iff hX (Real.rpow_pos_of_pos hQ _), Real.log_rpow hQ]

private theorem log_le_self' {x : ℝ} (hx : 0 < x) : Real.log x ≤ x := by
  have := Real.log_le_sub_one_of_pos hx
  linarith

private theorem log_two_le_one : Real.log 2 ≤ 1 := by
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  linarith

variable {L} {R : ℕ}

/-- `C(r, n) ≤ Rⁿ` for `r ≤ R`. -/
private theorem choose_le_pow {R : ℕ} (hR : #L.forms ≤ R) :
    ((L.forms.card.choose n : ℕ) : ℝ) ≤ (R : ℝ) ^ n := by
  exact_mod_cast (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left hR n)

/-- Lemma 9.4's `√n^n ≤ Δ_L Q^δ`, from `(n² + Rⁿ log H_L)/δ ≤ log Q`. -/
theorem sqrt_pow_le_absDet_mul (hn : 1 ≤ n) {R : ℕ} (hR : #L.forms ≤ R) {δ Q : ℝ} (hδ : 0 < δ)
    (hQ : 1 < Q) (h : (n ^ 2 + R ^ n * Real.log L.absFormHeight) / δ ≤ Real.log Q) :
    √n ^ n ≤ L.absDet * Q ^ δ := by
  have hQ0 : 0 < Q := zero_lt_one.trans hQ
  have hH := L.one_le_absFormHeight
  have hℓ := Real.log_nonneg hH
  have hΔ := Real.log_le_log (Real.rpow_pos_of_pos (zero_lt_one.trans_le hH) _)
    L.absFormHeight_rpow_le_absDet
  rw [Real.log_rpow (zero_lt_one.trans_le hH), Fintype.card_fin] at hΔ
  have hC := choose_le_pow (L := L) hR
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.log_le_log_iff (by positivity) (mul_pos L.absDet_pos (Real.rpow_pos_of_pos hQ0 _)),
    Real.log_mul L.absDet_pos.ne' (Real.rpow_pos_of_pos hQ0 _).ne', Real.log_rpow hQ0,
    Real.log_pow, Real.log_sqrt hn0.le]
  have h1 : Real.log n / 2 ≤ n := by linarith [log_le_self' hn0]
  have h2 := (div_le_iff₀ hδ).mp h
  have h3 : (n : ℝ) * (Real.log n / 2) ≤ n * n := mul_le_mul_of_nonneg_left h1 hn0.le
  have h4 : ((L.forms.card.choose n : ℕ) : ℝ) * Real.log L.absFormHeight ≤
      (R : ℝ) ^ n * Real.log L.absFormHeight := mul_le_mul_of_nonneg_right hC hℓ
  nlinarith

/-- (9.x) `n H_L^{C(r,n)} ≤ Q^{1/3n}`, from `3n² + 3n Rⁿ log H_L ≤ log Q`. -/
theorem mul_rpow_le_rpow_one_div (hn : 1 ≤ n) {R : ℕ} (hR : #L.forms ≤ R) {Q : ℝ} (hQ : 1 < Q)
    (h : 3 * n ^ 2 + 3 * n * R ^ n * Real.log L.absFormHeight ≤ Real.log Q) :
    n * L.absFormHeight ^ ((L.forms.card.choose n : ℕ) : ℝ) ≤ Q ^ (1 / (3 * n) : ℝ) := by
  have hQ0 : 0 < Q := zero_lt_one.trans hQ
  have hH := L.one_le_absFormHeight
  have hℓ := Real.log_nonneg hH
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine le_rpow_of_log_le (by positivity) hQ0 ?_
  rw [Real.log_mul hn0.ne' (Real.rpow_pos_of_pos (zero_lt_one.trans_le hH) _).ne',
    Real.log_rpow (zero_lt_one.trans_le hH)]
  have h4 : ((L.forms.card.choose n : ℕ) : ℝ) * Real.log L.absFormHeight ≤
      (R : ℝ) ^ n * Real.log L.absFormHeight := mul_le_mul_of_nonneg_right (choose_le_pow hR) hℓ
  have h5 := log_le_self' hn0
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
  nlinarith

/-- `√2^{n(n-1)} Δ_L ≤ Q^{1/6}`, from `3n² + 6 log H_L ≤ log Q`. -/
theorem sqrt_two_pow_mul_absDet_le {Q : ℝ} (hQ : 1 < Q)
    (h : 3 * n ^ 2 + 6 * Real.log L.absFormHeight ≤ Real.log Q) :
    √2 ^ (n * (n - 1)) * L.absDet ≤ Q ^ (1 / 6 : ℝ) := by
  have hQ0 : 0 < Q := zero_lt_one.trans hQ
  refine le_rpow_of_log_le (mul_pos (by positivity) L.absDet_pos) hQ0 ?_
  rw [Real.log_mul (by positivity) L.absDet_pos.ne', Real.log_pow,
    Real.log_sqrt zero_le_two]
  have h1 := Real.log_le_log L.absDet_pos L.absDet_le_absFormHeight
  have h2 : ((n * (n - 1) : ℕ) : ℝ) ≤ n ^ 2 := by
    exact_mod_cast (Nat.mul_le_mul_left n (Nat.sub_le n 1)).trans_eq (sq n).symm
  have h3 := log_two_le_one
  have h4 : ((n * (n - 1) : ℕ) : ℝ) * (Real.log 2 / 2) ≤ n ^ 2 * (1 / 2) :=
    mul_le_mul h2 (by linarith) (by positivity [Real.log_nonneg one_le_two]) (by positivity)
  nlinarith

/-- `3^{n³} ≤ Q^{1/2}`, from `4n³ ≤ log Q`. -/
theorem three_pow_le_rpow {Q : ℝ} (hQ : 1 < Q) (h : 4 * n ^ 3 ≤ Real.log Q) :
    (3 : ℝ) ^ (n ^ 3) ≤ Q ^ (1 / 2 : ℝ) := by
  refine le_rpow_of_log_le (by positivity) (zero_lt_one.trans hQ) ?_
  rw [Real.log_pow]
  have h1 : Real.log 3 ≤ 2 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)]
  have h2 : ((n ^ 3 : ℕ) : ℝ) * Real.log 3 ≤ n ^ 3 * 2 := by
    push_cast
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  nlinarith

/-- (11.21)'s condition `(3^{n³} 2^{n(n-1)/2} H_L)^{2ⁿ} ≤ Q^{δ/n(n-1)}`, from
`n² 2ⁿ (3n³ + log H_L)/δ ≤ log Q`. -/
theorem pow_le_rpow_of_eleven (hn : 2 ≤ n) {δ Q : ℝ} (hδ : 0 < δ) (hQ : 1 < Q)
    (h : n ^ 2 * 2 ^ n * (3 * n ^ 3 + Real.log L.absFormHeight) / δ ≤ Real.log Q) :
    (3 ^ (n ^ 3) * (√2 ^ (n * (n - 1)) * L.absFormHeight)) ^ (2 ^ n) ≤
      Q ^ (δ / (n * (n - 1))) := by
  have hQ0 : 0 < Q := zero_lt_one.trans hQ
  have hH := L.one_le_absFormHeight
  have hℓ := Real.log_nonneg hH
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnn : (0 : ℝ) < n * (n - 1) := by nlinarith
  refine le_rpow_of_log_le (by positivity) hQ0 ?_
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_sqrt zero_le_two, div_mul_eq_mul_div, le_div_iff₀ hnn]
  have h1 : Real.log 3 ≤ 2 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)]
  have h2 := log_two_le_one
  have hl2 := Real.log_nonneg (one_le_two : (1 : ℝ) ≤ 2)
  have h3 : ((n * (n - 1) : ℕ) : ℝ) ≤ n ^ 2 := by
    exact_mod_cast (Nat.mul_le_mul_left n (Nat.sub_le n 1)).trans_eq (sq n).symm
  have h4 : ((n ^ 3 : ℕ) : ℝ) * Real.log 3 ≤ 2 * n ^ 3 := by
    push_cast
    nlinarith [show (0 : ℝ) ≤ n ^ 3 by positivity]
  have h5 : ((n * (n - 1) : ℕ) : ℝ) * (Real.log 2 / 2) ≤ n ^ 3 := by
    have : (n : ℝ) ^ 2 ≤ n ^ 3 := by nlinarith
    nlinarith [show (0 : ℝ) ≤ ((n * (n - 1) : ℕ) : ℝ) by positivity]
  have hin : ((n ^ 3 : ℕ) : ℝ) * Real.log 3 + (((n * (n - 1) : ℕ) : ℝ) * (Real.log 2 / 2) +
      Real.log L.absFormHeight) ≤ 3 * n ^ 3 + Real.log L.absFormHeight := by linarith
  have h6 := (div_le_iff₀ hδ).mp h
  have h7 : (n : ℝ) * (n - 1) ≤ n ^ 2 := by nlinarith
  have h8 : (0 : ℝ) ≤ 3 * n ^ 3 + Real.log L.absFormHeight := by positivity
  have h9 : ((2 ^ n : ℕ) : ℝ) = 2 ^ n := by push_cast; ring
  rw [h9]
  calc (2 : ℝ) ^ n * (((n ^ 3 : ℕ) : ℝ) * Real.log 3 + (((n * (n - 1) : ℕ) : ℝ) *
        (Real.log 2 / 2) + Real.log L.absFormHeight)) * (n * (n - 1))
      ≤ 2 ^ n * (3 * n ^ 3 + Real.log L.absFormHeight) * n ^ 2 := by
        gcongr
    _ = n ^ 2 * 2 ^ n * (3 * n ^ 3 + Real.log L.absFormHeight) := by ring
    _ ≤ Real.log Q * δ := h6
    _ = δ * Real.log Q := by ring

/-- Lemma 10.3's condition `(2^{3n²} H_L)^{3n Rⁿ} ≤ Q^δ`, from
`3n Rⁿ (3n² + log H_L)/δ ≤ log Q`. -/
theorem pow_le_rpow_of_ten {R : ℕ} {δ Q : ℝ} (hδ : 0 < δ) (hQ : 1 < Q)
    (h : 3 * n * R ^ n * (3 * n ^ 2 + Real.log L.absFormHeight) / δ ≤ Real.log Q) :
    (2 ^ (3 * n ^ 2) * L.absFormHeight) ^ (3 * n * R ^ n) ≤ Q ^ δ := by
  have hQ0 : 0 < Q := zero_lt_one.trans hQ
  have hH := L.one_le_absFormHeight
  have hℓ := Real.log_nonneg hH
  refine le_rpow_of_log_le (by positivity) hQ0 ?_
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have h2 := log_two_le_one
  have h6 := (div_le_iff₀ hδ).mp h
  have h3 : ((3 * n ^ 2 : ℕ) : ℝ) * Real.log 2 ≤ 3 * n ^ 2 := by
    push_cast
    nlinarith [show (0 : ℝ) ≤ n ^ 2 by positivity]
  have h4 : ((3 * n * R ^ n : ℕ) : ℝ) = 3 * n * R ^ n := by push_cast; ring
  rw [h4]
  calc (3 * n * R ^ n : ℝ) * (((3 * n ^ 2 : ℕ) : ℝ) * Real.log 2 + Real.log L.absFormHeight)
      ≤ 3 * n * R ^ n * (3 * n ^ 2 + Real.log L.absFormHeight) := by gcongr
    _ ≤ Real.log Q * δ := h6
    _ = δ * Real.log Q := by ring

/-- The common bounds behind `hΘ₁`, `hΘ₂`: for `1 ≤ p < n`, `N = C(n, p)`, `#matSet ≤ Rⁿ`. -/
private theorem coeff_bounds (hR : #L.forms ≤ R) {p : ℕ} (hp : 1 ≤ p) (hpn : p < n) :
    (1 : ℝ) ≤ Fintype.card (Set.powersetCard (Fin n) p) ∧
      (Fintype.card (Set.powersetCard (Fin n) p) : ℝ) ≤ 2 ^ n ∧
      Real.log (p.factorial : ℕ) ≤ n ^ 2 ∧ (2 * p * #L.matSet : ℝ) ≤ 2 * n * R ^ n := by
  have hNσ : Fintype.card (Set.powersetCard (Fin n) p) = n.choose p := by
    rw [← Nat.card_eq_fintype_card, Set.powersetCard.card, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hNσ]
    exact_mod_cast Nat.choose_pos hpn.le
  · rw [hNσ]
    exact_mod_cast Nat.choose_le_two_pow n p
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt hpn
    have h1 : (p.factorial : ℝ) ≤ (n : ℝ) ^ n := by
      exact_mod_cast (Nat.factorial_le_pow p).trans
        ((Nat.pow_le_pow_left hpn.le p).trans (Nat.pow_le_pow_right (by omega) hpn.le))
    calc Real.log (p.factorial : ℕ) ≤ Real.log ((n : ℝ) ^ n) :=
          Real.log_le_log (by exact_mod_cast Nat.factorial_pos p) h1
      _ = n * Real.log n := by rw [Real.log_pow]
      _ ≤ n * n := mul_le_mul_of_nonneg_left (log_le_self' hn0) hn0.le
      _ = n ^ 2 := by ring
  · have h1 : #L.matSet ≤ R ^ n :=
      (L.card_matSet_le.trans_eq (by rw [Fintype.card_fin])).trans (Nat.pow_le_pow_left hR n)
    have h2 : (p : ℝ) ≤ n := by exact_mod_cast hpn.le
    have h3 : (#L.matSet : ℝ) ≤ (R : ℝ) ^ n := by exact_mod_cast h1
    have : (2 * p : ℝ) ≤ 2 * n := by linarith
    calc (2 * p * #L.matSet : ℝ) ≤ 2 * n * R ^ n :=
          mul_le_mul this h3 (Nat.cast_nonneg _) (by positivity)

/-- The coefficient `Y` of Prop. 13.6 (iii) is at most `[K:ℚ] (2·2ⁿ + n² + 2n Rⁿ log H_L)`. -/
private theorem Y_le (hR : #L.forms ≤ R) {p : ℕ} (hp : 1 ≤ p) (hpn : p < n) :
    (finrank ℚ K : ℝ) / 2 * Fintype.card (Set.powersetCard (Fin n) p) +
        finrank ℚ K * Real.log (Fintype.card (Set.powersetCard (Fin n) p)) +
        finrank ℚ K * Real.log (p.factorial : ℕ) +
        2 * p * #L.matSet * Real.log L.mulFormHeight ≤
      finrank ℚ K * (2 * 2 ^ n + n ^ 2 + 2 * n * R ^ n * Real.log L.absFormHeight) := by
  obtain ⟨hN1, hN, hfac, hmat⟩ := coeff_bounds hR hp hpn
  have hℓ := Real.log_nonneg L.one_le_absFormHeight
  have hd : (0 : ℝ) ≤ finrank ℚ K := Nat.cast_nonneg _
  have hlN := log_le_self' (zero_lt_one.trans_le hN1)
  rw [log_mulFormHeight]
  have h1 : (2 * p * #L.matSet : ℝ) * (finrank ℚ K * Real.log L.absFormHeight) ≤
      2 * n * R ^ n * (finrank ℚ K * Real.log L.absFormHeight) :=
    mul_le_mul_of_nonneg_right hmat (mul_nonneg hd hℓ)
  have h2 : (finrank ℚ K : ℝ) * Real.log (Fintype.card (Set.powersetCard (Fin n) p)) ≤
      finrank ℚ K * 2 ^ n := mul_le_mul_of_nonneg_left (hlN.trans hN) hd
  have h3 : (finrank ℚ K : ℝ) * Real.log (p.factorial : ℕ) ≤ finrank ℚ K * n ^ 2 :=
    mul_le_mul_of_nonneg_left hfac hd
  have h4 : (finrank ℚ K : ℝ) / 2 * Fintype.card (Set.powersetCard (Fin n) p) ≤
      finrank ℚ K * 2 ^ n := by nlinarith
  nlinarith

/-- The constant term of the threshold for Prop. 12.1 (`hΘ₁`). -/
noncomputable def thetaOneA (n m : ℕ) (ε : ℝ) : ℝ :=
  2 ^ n + 2 ^ n * (m / ε) ^ m * (20 * m ^ 3 + m + 2 * m ^ 2 * (2 * 2 ^ n + n ^ 2))

/-- The coefficient of `log H_L` in the threshold for Prop. 12.1 (`hΘ₁`). -/
noncomputable def thetaOneB (n m R : ℕ) (ε : ℝ) : ℝ :=
  2 ^ n * (m / ε) ^ m * (2 * m ^ 2 * (2 * n * R ^ n))

/-- `hΘ₁` of `false_of_chain` from `(3Rⁿ/δ)(A + B log H_L + 1) ≤ log Q_0`. -/
theorem thetaOne_lt (hR : #L.forms ≤ R) (hR1 : 1 ≤ R) {p : ℕ} (hp : 1 ≤ p) (hpn : p < n)
    {m : ℕ} {ε δ Q : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (h : 3 * R ^ n / δ * (thetaOneA n m ε + thetaOneB n m R ε * Real.log L.absFormHeight + 1) ≤
      Real.log Q) :
    (finrank ℚ K : ℝ) * Real.log (Fintype.card (Set.powersetCard (Fin n) p)) +
      ((Fintype.card (Set.powersetCard (Fin n) p) : ℝ) - 1) * (m / ε) ^ m *
        (20 * m ^ 3 * finrank ℚ K + m / 2 + 2 * m ^ 2 *
          ((finrank ℚ K : ℝ) / 2 * Fintype.card (Set.powersetCard (Fin n) p) +
            finrank ℚ K * Real.log (Fintype.card (Set.powersetCard (Fin n) p)) +
            finrank ℚ K * Real.log (p.factorial : ℕ) +
            2 * p * #L.matSet * Real.log L.mulFormHeight)) <
      Real.log Q * (finrank ℚ K * δ / (3 * R ^ n)) := by
  obtain ⟨hN1, hN, -, -⟩ := coeff_bounds hR hp hpn
  have hY := Y_le hR hp hpn
  have hℓ := Real.log_nonneg L.one_le_absFormHeight
  have hd : (1 : ℝ) ≤ finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hR0 : (0 : ℝ) < (R : ℝ) ^ n := by positivity
  have hμ : (0 : ℝ) ≤ (m / ε) ^ m := by positivity
  set d : ℝ := (finrank ℚ K : ℝ)
  set N : ℝ := (Fintype.card (Set.powersetCard (Fin n) p) : ℝ)
  set ℓ := Real.log L.absFormHeight
  set μ := ((m : ℝ) / ε) ^ m
  set Yb := 2 * 2 ^ n + (n : ℝ) ^ 2 + 2 * n * R ^ n * ℓ
  have hYb : 0 ≤ Yb := by positivity
  have hlN : Real.log N ≤ 2 ^ n := (log_le_self' (zero_lt_one.trans_le hN1)).trans hN
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have e1 : (m : ℝ) / 2 ≤ m * d := by nlinarith
  have hinner : 20 * m ^ 3 * d + m / 2 + 2 * m ^ 2 *
      (d / 2 * N + d * Real.log N + d * Real.log (p.factorial : ℕ) +
        2 * p * #L.matSet * Real.log L.mulFormHeight) ≤
      d * (20 * m ^ 3 + m + 2 * m ^ 2 * Yb) := by
    have := mul_le_mul_of_nonneg_left hY (by positivity : (0 : ℝ) ≤ 2 * m ^ 2)
    nlinarith
  have hinner0 : 0 ≤ d * (20 * m ^ 3 + m + 2 * m ^ 2 * Yb) := by positivity
  have hLHS : d * Real.log N + (N - 1) * μ * (20 * m ^ 3 * d + m / 2 + 2 * m ^ 2 *
      (d / 2 * N + d * Real.log N + d * Real.log (p.factorial : ℕ) +
        2 * p * #L.matSet * Real.log L.mulFormHeight)) ≤
      d * (thetaOneA n m ε + thetaOneB n m R ε * ℓ) := by
    have h1 : d * Real.log N ≤ d * 2 ^ n := mul_le_mul_of_nonneg_left hlN (by linarith)
    have h2 : (N - 1) * μ ≤ 2 ^ n * μ := mul_le_mul_of_nonneg_right (by linarith) hμ
    have h3 : (N - 1) * μ * (20 * m ^ 3 * d + m / 2 + 2 * m ^ 2 *
        (d / 2 * N + d * Real.log N + d * Real.log (p.factorial : ℕ) +
          2 * p * #L.matSet * Real.log L.mulFormHeight)) ≤
        2 ^ n * μ * (d * (20 * m ^ 3 + m + 2 * m ^ 2 * Yb)) :=
      (mul_le_mul_of_nonneg_left hinner (mul_nonneg (by linarith) hμ)).trans
        (mul_le_mul_of_nonneg_right h2 hinner0)
    have e : d * (thetaOneA n m ε + thetaOneB n m R ε * ℓ) =
        d * 2 ^ n + 2 ^ n * μ * (d * (20 * m ^ 3 + m + 2 * m ^ 2 * Yb)) := by
      simp only [thetaOneA, thetaOneB, Yb, μ]
      ring
    linarith
  have hRHS : d * (thetaOneA n m ε + thetaOneB n m R ε * ℓ + 1) ≤
      Real.log Q * (d * δ / (3 * R ^ n)) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hδ] at h
    have := mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ d)
    rw [mul_div_assoc', le_div_iff₀ (by positivity)]
    linarith
  nlinarith

/-- The constant term of the threshold for the product formula (`hΘ₂`). -/
noncomputable def thetaTwoA (n : ℕ) (ε : ℝ) : ℝ :=
  5 * 2 ^ n + 2 * n ^ 2 + 1 + 2 ^ n * (2 ^ n / ε + 1)

/-- The coefficient of `log H_L` in the threshold for the product formula (`hΘ₂`). -/
noncomputable def thetaTwoB (n R : ℕ) : ℝ := 4 * n * R ^ n

/-- `hΘ₂` of `false_of_chain` from `(2n 2ⁿ/δ)(1 + 2A + 2B log H_L) ≤ log Q_0`, with
`40 n² 2ⁿ ε ≤ δ`. -/
theorem thetaTwo_lt (hR : #L.forms ≤ R) {p : ℕ} (hp : 1 ≤ p) (hpn : p < n) {m : ℕ}
    (hm1 : 1 ≤ m) {ε δ Q : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hεδ : 40 * n ^ 2 * 2 ^ n * ε ≤ δ)
    (h : 2 * n * 2 ^ n / δ * (1 + 2 * thetaTwoA n ε + 2 * thetaTwoB n R *
      Real.log L.absFormHeight) ≤ Real.log Q) :
    1 / 2 + 2 * m * (((finrank ℚ K : ℝ) / 2 * Fintype.card (Set.powersetCard (Fin n) p) +
        finrank ℚ K * Real.log (Fintype.card (Set.powersetCard (Fin n) p)) +
        finrank ℚ K * Real.log (p.factorial : ℕ) +
        2 * p * #L.matSet * Real.log L.mulFormHeight) +
      (finrank ℚ K * Real.log (p.factorial : ℕ) +
        2 * p * #L.matSet * Real.log L.mulFormHeight) +
      finrank ℚ K * (2 * Fintype.card (Set.powersetCard (Fin n) p) * Real.log 2 +
        Real.log 2 + Real.log (Fintype.card (Set.powersetCard (Fin n) p)) +
        Real.log ((Fintype.card (Set.powersetCard (Fin n) p) - 1) *
          ((Fintype.card (Set.powersetCard (Fin n) p) - 1) / ε + 1)))) <
      Real.log Q * (finrank ℚ K * m *
        (δ / (n * Fintype.card (Set.powersetCard (Fin n) p)) - 10 * n * ε)) := by
  obtain ⟨hN1, hN, hfac, hmat⟩ := coeff_bounds hR hp hpn
  have hY := Y_le hR hp hpn
  have hℓ := Real.log_nonneg L.one_le_absFormHeight
  have hd : (1 : ℝ) ≤ finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt hpn
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  rw [log_mulFormHeight] at hY ⊢
  set d : ℝ := (finrank ℚ K : ℝ)
  set N : ℝ := (Fintype.card (Set.powersetCard (Fin n) p) : ℝ)
  set ℓ := Real.log L.absFormHeight
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  -- `Z ≤ d (A + B ℓ)`
  have hY₂ : d * Real.log (p.factorial : ℕ) + 2 * p * #L.matSet * (d * ℓ) ≤
      d * (n ^ 2 + 2 * n * R ^ n * ℓ) := by
    have h1 := mul_le_mul_of_nonneg_left hfac (by linarith : (0 : ℝ) ≤ d)
    have h2 := mul_le_mul_of_nonneg_right hmat (mul_nonneg (by linarith : (0 : ℝ) ≤ d) hℓ)
    nlinarith
  have hl2 := log_two_le_one
  have hlN : Real.log N ≤ 2 ^ n := (log_le_self' (zero_lt_one.trans_le hN1)).trans hN
  have hG0 : 0 ≤ (N - 1) * ((N - 1) / ε + 1) :=
    mul_nonneg (by linarith) (by have : 0 ≤ (N - 1) / ε := div_nonneg (by linarith) hε.le
                                 linarith)
  have hG : Real.log ((N - 1) * ((N - 1) / ε + 1)) ≤ 2 ^ n * (2 ^ n / ε + 1) := by
    refine (Real.log_le_self hG0).trans (mul_le_mul (by linarith) ?_ (by
      have : 0 ≤ (N - 1) / ε := div_nonneg (by linarith) hε.le
      linarith) h2n.le)
    have : (N - 1) / ε ≤ 2 ^ n / ε := div_le_div_of_nonneg_right (by linarith) hε.le
    linarith
  have hlog2N : 2 * N * Real.log 2 ≤ 2 * 2 ^ n := by
    have := mul_le_mul hN hl2 (Real.log_nonneg one_le_two) h2n.le
    linarith
  have hZ : (d / 2 * N + d * Real.log N + d * Real.log (p.factorial : ℕ) +
        2 * p * #L.matSet * (d * ℓ)) + (d * Real.log (p.factorial : ℕ) +
        2 * p * #L.matSet * (d * ℓ)) + d * (2 * N * Real.log 2 + Real.log 2 + Real.log N +
        Real.log ((N - 1) * ((N - 1) / ε + 1))) ≤ d * (thetaTwoA n ε + thetaTwoB n R * ℓ) := by
    have h3 : 2 * N * Real.log 2 + Real.log 2 + Real.log N +
        Real.log ((N - 1) * ((N - 1) / ε + 1)) ≤
          2 * 2 ^ n + 1 + 2 ^ n + 2 ^ n * (2 ^ n / ε + 1) := by linarith
    have h4 := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ d)
    have e : d * (thetaTwoA n ε + thetaTwoB n R * ℓ) = d * (2 * 2 ^ n + n ^ 2 +
        2 * n * R ^ n * ℓ) + d * (n ^ 2 + 2 * n * R ^ n * ℓ) +
        d * (2 * 2 ^ n + 1 + 2 ^ n + 2 ^ n * (2 ^ n / ε + 1)) := by
      simp only [thetaTwoA, thetaTwoB]
      ring
    linarith
  -- `β ≥ δ / (2 n 2ⁿ)`
  have hβ : δ / (2 * n * 2 ^ n) ≤ δ / (n * N) - 10 * n * ε := by
    have h1 : δ / (n * 2 ^ n) ≤ δ / (n * N) :=
      div_le_div_of_nonneg_left hδ.le (by positivity) (mul_le_mul_of_nonneg_left hN hn0.le)
    have h2 : 10 * n * ε ≤ δ / (4 * n * 2 ^ n) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have e1 : δ / (n * 2 ^ n) = δ / (2 * n * 2 ^ n) + δ / (4 * n * 2 ^ n) +
        δ / (4 * n * 2 ^ n) := by
      field_simp
      ring
    have h5 : 0 ≤ δ / (4 * n * 2 ^ n) := by positivity
    linarith
  -- assemble
  have hTA : 0 ≤ thetaTwoA n ε := by unfold thetaTwoA; positivity
  have hTB : 0 ≤ thetaTwoB n R := by unfold thetaTwoB; positivity
  set T := 1 + 2 * thetaTwoA n ε + 2 * thetaTwoB n R * ℓ with hT_def
  have hδ2 : 0 < δ / (2 * n * 2 ^ n) := by positivity
  have hT : T ≤ Real.log Q * (δ / (2 * n * 2 ^ n)) := by
    have h1 := mul_le_mul_of_nonneg_right h hδ2.le
    have e : 2 * n * 2 ^ n / δ * T * (δ / (2 * n * 2 ^ n)) = T := by field_simp
    linarith
  have hT1 : 1 ≤ T := by
    have : 0 ≤ 2 * thetaTwoB n R * ℓ := by positivity
    linarith
  have hlogQ : 0 ≤ Real.log Q := by
    by_contra hneg
    have : Real.log Q * (δ / (2 * n * 2 ^ n)) < 0 :=
      mul_neg_of_neg_of_pos (not_le.mp hneg) hδ2
    linarith
  have hT2 : T ≤ Real.log Q * (δ / (n * N) - 10 * n * ε) :=
    hT.trans (mul_le_mul_of_nonneg_left hβ hlogQ)
  have hdm : (1 : ℝ) ≤ d * m := by nlinarith
  have hmZ := mul_le_mul_of_nonneg_left hZ (by positivity : (0 : ℝ) ≤ 2 * m)
  have h5 : 1 / 2 + 2 * m * (d * (thetaTwoA n ε + thetaTwoB n R * ℓ)) < d * m * T := by
    have e : d * m * T = d * m + d * m * (2 * thetaTwoA n ε + 2 * thetaTwoB n R * ℓ) := by
      rw [hT_def]; ring
    have e2 : 2 * m * (d * (thetaTwoA n ε + thetaTwoB n R * ℓ)) =
        d * m * (2 * thetaTwoA n ε + 2 * thetaTwoB n R * ℓ) := by ring
    linarith
  have h6 : d * m * T ≤ Real.log Q * (d * m * (δ / (n * N) - 10 * n * ε)) := by
    have := mul_le_mul_of_nonneg_left hT2 (by linarith : (0 : ℝ) ≤ d * m)
    linarith [show d * m * (Real.log Q * (δ / (n * N) - 10 * n * ε)) =
      Real.log Q * (d * m * (δ / (n * N) - 10 * n * ε)) by ring]
  linarith

/-! ### The parameters of Theorem 8.1 -/

/-- EF13's `ε` of (14.1), here `δ / (40 n² 2ⁿ)`. -/
noncomputable def gapEps (n : ℕ) (δ : ℝ) : ℝ := δ / (40 * n ^ 2 * 2 ^ n)

/-- One less than the number `m` of blocks of the auxiliary polynomial: Prop. 13.6 needs
`2 (Rⁿ (n/ε + 2)ⁿ + 1) ≤ e^{mε²/2}`. -/
noncomputable def gapChain (n R : ℕ) (δ : ℝ) : ℕ :=
  ⌈2 / gapEps n δ ^ 2 * Real.log (2 * ((R : ℝ) ^ n * (n / gapEps n δ + 2) ^ n + 1))⌉₊

/-- The number `m` of blocks of the auxiliary polynomial (EF13 (14.1)). -/
noncomputable def gapBlocks (n R : ℕ) (δ : ℝ) : ℕ := gapChain n R δ + 1

/-- The ratio `ω = 4m/ε` of consecutive `log Q_h` in the chain (EF13 (14.4)). -/
noncomputable def gapRatio (n R : ℕ) (δ : ℝ) : ℝ := 4 * (gapBlocks n R δ : ℝ) / gapEps n δ

/-- The number of exceptional intervals in Theorem 8.1: `(n - 1)(m - 1)`. -/
noncomputable def gapIntervals (n R : ℕ) (δ : ℝ) : ℕ := (n - 1) * gapChain n R δ

/-- **The threshold `log C₂`** of Theorem 8.1, a function of `n`, `R`, `δ` and `ℓ = log H_L`. -/
noncomputable def gapThreshold (n R : ℕ) (δ ℓ : ℝ) : ℝ :=
  (n ^ 2 + R ^ n * ℓ) / δ + (3 * n ^ 2 + 3 * n * R ^ n * ℓ) + (3 * n ^ 2 + 6 * ℓ) +
    4 * n ^ 3 + n ^ 2 * 2 ^ n * (3 * n ^ 3 + ℓ) / δ +
    3 * n * R ^ n * (3 * n ^ 2 + ℓ) / δ +
    3 * R ^ n / δ * (thetaOneA n (gapBlocks n R δ) (gapEps n δ) +
      thetaOneB n (gapBlocks n R δ) R (gapEps n δ) * ℓ + 1) +
    2 * n * 2 ^ n / δ * (1 + 2 * thetaTwoA n (gapEps n δ) + 2 * thetaTwoB n R * ℓ)

theorem gapEps_pos {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) : 0 < gapEps n δ := by
  have : (0 : ℝ) < n := by exact_mod_cast hn
  unfold gapEps; positivity

theorem gapEps_le_one {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ1 : δ ≤ 1) : gapEps n δ ≤ 1 := by
  unfold gapEps
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ one_le_two
  have h3 : (1 : ℝ) ≤ 40 * n ^ 2 * 2 ^ n := by nlinarith
  rw [div_le_one (by linarith)]
  linarith

theorem mul_gapEps {n : ℕ} (hn : 1 ≤ n) (δ : ℝ) : 40 * n ^ 2 * 2 ^ n * gapEps n δ = δ := by
  have h1 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold gapEps
  field_simp

/-- Prop. 13.6's condition on `m = gapBlocks` for `#matSet ≤ Rⁿ`. -/
theorem two_mul_le_exp_gapBlocks {n R : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) {s : ℕ}
    (hs : s ≤ R ^ n) :
    2 * (s * (n / gapEps n δ + 2) ^ n + 1) ≤
      Real.exp (gapBlocks n R δ * gapEps n δ ^ 2 / 2) := by
  have hε := gapEps_pos hn hδ
  set ε := gapEps n δ
  set X := 2 * ((R : ℝ) ^ n * (n / ε + 2) ^ n + 1)
  have hX : 0 < X := by positivity
  have h1 : 2 * (s * (n / ε + 2) ^ n + 1) ≤ X := by
    have : (s : ℝ) ≤ (R : ℝ) ^ n := by exact_mod_cast hs
    have : (s : ℝ) * (n / ε + 2) ^ n ≤ (R : ℝ) ^ n * (n / ε + 2) ^ n :=
      mul_le_mul_of_nonneg_right this (by positivity)
    linarith
  refine h1.trans ?_
  rw [← Real.exp_log hX, Real.exp_le_exp]
  have h2 : 2 / ε ^ 2 * Real.log X ≤ gapChain n R δ := Nat.le_ceil _
  have h3 : (gapChain n R δ : ℝ) ≤ gapBlocks n R δ := by
    unfold gapBlocks; push_cast; linarith
  have h4 := h2.trans h3
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at h4
  nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ X by
    have : (0 : ℝ) ≤ (R : ℝ) ^ n * (n / ε + 2) ^ n := by positivity
    linarith)]

/-- The eight terms of `gapThreshold` are each at most `gapThreshold`. -/
theorem terms_le_gapThreshold {n R : ℕ} {δ ℓ : ℝ} (hn : 1 ≤ n) (hδ : 0 < δ) (hℓ : 0 ≤ ℓ) :
    (n ^ 2 + R ^ n * ℓ) / δ ≤ gapThreshold n R δ ℓ ∧
    3 * n ^ 2 + 3 * n * R ^ n * ℓ ≤ gapThreshold n R δ ℓ ∧
    3 * n ^ 2 + 6 * ℓ ≤ gapThreshold n R δ ℓ ∧ 4 * n ^ 3 ≤ gapThreshold n R δ ℓ ∧
    n ^ 2 * 2 ^ n * (3 * n ^ 3 + ℓ) / δ ≤ gapThreshold n R δ ℓ ∧
    3 * n * R ^ n * (3 * n ^ 2 + ℓ) / δ ≤ gapThreshold n R δ ℓ ∧
    3 * R ^ n / δ * (thetaOneA n (gapBlocks n R δ) (gapEps n δ) +
      thetaOneB n (gapBlocks n R δ) R (gapEps n δ) * ℓ + 1) ≤ gapThreshold n R δ ℓ ∧
    2 * n * 2 ^ n / δ * (1 + 2 * thetaTwoA n (gapEps n δ) + 2 * thetaTwoB n R * ℓ) ≤
      gapThreshold n R δ ℓ := by
  have hε := gapEps_pos hn hδ
  have t1 : 0 ≤ (n ^ 2 + R ^ n * ℓ : ℝ) / δ := by positivity
  have t2 : 0 ≤ (3 * n ^ 2 + 3 * n * R ^ n * ℓ : ℝ) := by positivity
  have t3 : 0 ≤ (3 * n ^ 2 + 6 * ℓ : ℝ) := by positivity
  have t4 : 0 ≤ (4 * n ^ 3 : ℝ) := by positivity
  have t5 : 0 ≤ (n ^ 2 * 2 ^ n * (3 * n ^ 3 + ℓ) : ℝ) / δ := by positivity
  have t6 : 0 ≤ (3 * n * R ^ n * (3 * n ^ 2 + ℓ) : ℝ) / δ := by positivity
  have t7 : 0 ≤ 3 * (R : ℝ) ^ n / δ * (thetaOneA n (gapBlocks n R δ) (gapEps n δ) +
      thetaOneB n (gapBlocks n R δ) R (gapEps n δ) * ℓ + 1) := by
    unfold thetaOneA thetaOneB; positivity
  have t8 : 0 ≤ 2 * (n : ℝ) * 2 ^ n / δ * (1 + 2 * thetaTwoA n (gapEps n δ) +
      2 * thetaTwoB n R * ℓ) := by
    unfold thetaTwoA thetaTwoB; positivity
  unfold gapThreshold
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

end NumberField.FormSystem

/-! ### EF13 Theorem 8.1 -/

namespace NumberField.FormSystem

variable {K : Type} [Field K] [NumberField K] {n : ℕ} {Ω : Type*} [Field Ω] [Algebra K Ω]
  [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω] (L : FormSystem K (Fin n)) (c : FormExponent K (Fin n))

/-- **EF13 Theorem 8.1.** Let `(L, c)` satisfy (8.3), (8.4), (8.8), (8.9) (`IsNormalSemistable`),
`n ≥ 2`, with at most `R ≥ n` distinct forms, and `0 < δ ≤ 1`. Then the `Q ≥ C₂`,
`log C₂ = gapThreshold n R δ (log H_L)`, with a nonzero point of height `≤ Q^{-δ}`
(`λ_1(Q) ≤ Q^{-δ}`) lie in `gapIntervals n R δ = (n - 1)(m - 1)` intervals `[a, a^{2ω}]`,
`ω = gapRatio n R δ = 4m/ε`. EF13 have `m₂` intervals `[Q_h, Q_h^{ω₂})` with their own constants. -/
theorem exists_intervals (hLs : L.IsNormalSemistable c Ω) (hn : 2 ≤ n) {R : ℕ}
    (hR : #L.forms ≤ R) (hnR : n ≤ R) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ a : Fin (gapIntervals n R δ) → ℝ, (∀ i, 1 < a i) ∧ ∀ (Q : ℝ) (hQ : 1 < Q),
      Real.exp (gapThreshold n R δ (Real.log L.absFormHeight)) ≤ Q →
      L.successiveInf (c.weight (zero_lt_one.trans hQ)) Ω 1 ≤ Q ^ (-δ) →
      ∃ i, a i ≤ Q ∧ Q ≤ a i ^ (2 * gapRatio n R δ) := by
  classical
  obtain ⟨v₀, hL₀, hc₀⟩ := hLs.exists_v₀
  have hn1 : 1 ≤ n := by omega
  have hε := gapEps_pos hn1 hδ
  have hε1 := gapEps_le_one hn1 hδ1
  have hεδ := mul_gapEps hn1 δ
  have hℓ := Real.log_nonneg L.one_le_absFormHeight
  set Θ := gapThreshold n R δ (Real.log L.absFormHeight) with hΘ
  obtain ⟨T1, T2, T3, T4, T5, T6, T7, T8⟩ := terms_le_gapThreshold (R := R) hn1 hδ hℓ
  have hΘpos : 0 < Θ := lt_of_lt_of_le (by positivity) T4
  set S : Set ℝ := {Q | ∃ hQ : 1 < Q, Real.exp Θ ≤ Q ∧
    L.successiveInf (c.weight (zero_lt_one.trans hQ)) Ω 1 ≤ Q ^ (-δ)} with hS
  have hS1 : ∀ q ∈ S, 1 < q := fun q ⟨hq, _⟩ ↦ hq
  have hlogS : ∀ q ∈ S, Θ ≤ Real.log q := fun q ⟨hq, hqT, _⟩ ↦
    (Real.le_log_iff_exp_le (zero_lt_one.trans hq)).mpr hqT
  have hm1 : 1 ≤ gapBlocks n R δ := by unfold gapBlocks; omega
  have hω1 : 1 ≤ gapRatio n R δ := by
    unfold gapRatio
    rw [le_div_iff₀ hε]
    have : (1 : ℝ) ≤ gapBlocks n R δ := by exact_mod_cast hm1
    linarith
  have hnochain : ∀ q : Fin ((n - 1) * gapChain n R δ + 1) → ℝ,
      ¬ Real.IsLogChain S (gapRatio n R δ) q := by
    intro q hq
    have hk : ∀ i, ∃ k, 0 < k ∧ k < n ∧
        L.successiveInf (c.weight (zero_lt_one.trans (hS1 _ (hq.1 i)))) Ω k ≤
          q i ^ (-(δ / (n - 1))) *
            L.successiveInf (c.weight (zero_lt_one.trans (hS1 _ (hq.1 i)))) Ω (k + 1) := by
      intro i
      obtain ⟨hQi, -, h1i⟩ := hq.1 i
      exact L.exists_successiveInf_le (Ω := Ω) c hn hLs.sum_eq_zero hQi.le h1i
        (sqrt_pow_le_absDet_mul hn1 hR hδ hQi (T1.trans (hlogS _ (hq.1 i))))
    choose col hcol0 hcoln hcolgap using hk
    obtain ⟨k₀, hk₀, g, hg, hq'⟩ := Real.exists_subchain hω1 hS1 hq col (Finset.Ioo 0 n)
      (fun i ↦ Finset.mem_Ioo.2 ⟨hcol0 i, hcoln i⟩) (by simp)
    obtain ⟨hk0, hkn⟩ := Finset.mem_Ioo.1 hk₀
    have hQg : ∀ a, 1 < q (g a) := fun a ↦ hS1 _ (hq.1 (g a))
    have hlg : ∀ a, Θ ≤ Real.log (q (g a)) := fun a ↦ hlogS _ (hq.1 (g a))
    have hmat : #L.matSet ≤ R ^ n :=
      (L.card_matSet_le.trans_eq (by rw [Fintype.card_fin])).trans (Nat.pow_le_pow_left hR n)
    refine L.false_of_chain c hLs hL₀ hc₀ hn hR hnR hδ hε hε1 (m := gapBlocks n R δ) hm1
      (two_mul_le_exp_gapBlocks hn1 hδ hmat) ⟨k₀, hkn⟩ hk0 (Q := q ∘ g) (fun a ↦ hQg a)
      (fun i j hij ↦ hq'.2 i j hij) (fun a ↦ ?_)
      (fun a ↦ mul_rpow_le_rpow_one_div hn1 hR (hQg a) (T2.trans (hlg a)))
      (fun a ↦ sqrt_two_pow_mul_absDet_le (hQg a) (T3.trans (hlg a)))
      (fun a ↦ three_pow_le_rpow (hQg a) (T4.trans (hlg a)))
      (fun a ↦ pow_le_rpow_of_eleven hn hδ (hQg a) (T5.trans (hlg a)))
      (fun a ↦ pow_le_rpow_of_ten hδ (hQg a) (T6.trans (hlg a)))
      rfl rfl rfl rfl rfl rfl ?_ ?_
    · have := hcolgap (g a)
      rw [hg a] at this
      exact this
    · exact thetaOne_lt hR (by omega) (p := n - k₀) (by omega) (by omega) hε hδ
        (T7.trans (hlg _))
    · exact thetaTwo_lt hR (p := n - k₀) (by omega) (by omega) hm1 hε hδ hεδ.le
        (T8.trans (hlg _))
  obtain ⟨a, ha1, ha⟩ := Real.exists_cover_of_not_chain (by linarith)
    (Real.one_lt_exp_iff.mpr hΘpos)
    ((n - 1) * gapChain n R δ) S (fun q ⟨_, hqT, _⟩ ↦ hqT) hnochain
  exact ⟨a, ha1, fun Q hQ hQT h1 ↦ ha Q ⟨hQ, hQT, h1⟩⟩


omit [IsAlgClosed Ω] in
/-- A nonzero point of height `≤ λ` gives `λ_1 ≤ λ`. -/
theorem successiveInf_one_le_of_absMulHeight_le (a : FormWeight K (Fin n)) {x : Fin n → Ω}
    (hx : x ≠ 0) {lam : ℝ} (h0 : 0 ≤ lam) (hxl : L.absMulHeight a x ≤ lam) :
    L.successiveInf a Ω 1 ≤ lam := by
  refine heightInf_le h0 ?_
  have hmem : x ∈ heightSpace Ω (L.absMulHeight a) lam := Submodule.subset_span hxl
  have := Submodule.finrank_mono ((Submodule.span_singleton_le_iff_mem x _).mpr hmem)
  rwa [finrank_span_singleton hx] at this

variable (K Ω) in
/-- **The semistable gap**: EF13 Theorem 8.1, qualitatively. This discharges the hypothesis
`SemistableGap K Ω` of Thm 16.1 (Q3.5), Prop. 17.5 (Q3.6) and Lemmas 18.1–18.4 (Q3.7). -/
theorem _root_.NumberField.semistableGap : SemistableGap K Ω := by
  intro n L c hn hsa hsf hsup hv₀ hU δ hδ hδ1
  have hLs : L.IsNormalSemistable c Ω := ⟨hsa, hsf, hsup, hv₀, hU⟩
  obtain ⟨a, ha1, ha⟩ :=
    L.exists_intervals c hLs hn (le_max_right n #L.forms) (le_max_left n #L.forms) hδ hδ1
  have hpos : ∀ i, 0 ≤ a i ^ (2 * gapRatio n (max n #L.forms) δ) := fun i ↦
    Real.rpow_nonneg (zero_le_one.trans (ha1 i).le) _
  refine ⟨Real.exp (gapThreshold n (max n #L.forms) δ (Real.log L.absFormHeight)) +
    ∑ i, a i ^ (2 * gapRatio n (max n #L.forms) δ) + 1, fun Q hQ hQ₀ x hx ↦ ?_⟩
  by_contra hle
  rw [not_lt] at hle
  have hsum : 0 ≤ ∑ i, a i ^ (2 * gapRatio n (max n #L.forms) δ) :=
    Finset.sum_nonneg fun i _ ↦ hpos i
  have hexp := Real.exp_pos (gapThreshold n (max n #L.forms) δ (Real.log L.absFormHeight))
  have hQ1 : 1 < Q := by linarith
  have h1 := L.successiveInf_one_le_of_absMulHeight_le (c.weight (zero_lt_one.trans hQ1)) hx
    (Real.rpow_nonneg (zero_le_one.trans hQ) _) hle
  obtain ⟨i, -, hi⟩ := ha Q hQ1 (by linarith) h1
  have := Finset.single_le_sum (fun j _ ↦ hpos j) (Finset.mem_univ i)
  linarith

end NumberField.FormSystem
