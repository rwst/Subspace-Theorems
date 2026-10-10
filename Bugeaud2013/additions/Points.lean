/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Bugeaud2013.additions.Liouville2

/-!
# The points of §3 and the subspaces of dimension at most two

The argument for the exponent `δ` uses of the points `v_n = (A, B₂, B₃, C)` of Bugeaud's §3 only a
list of inequalities, collected in `Real.CFPoint`: with `H = q_w q_{w+r}` and `Q = q_w`,

* `|v_i| ≤ H` and `H ≤ (A + 1)⁴ |v₀|` (the head of the continued fraction is rigid);
* `|L₁(v)| ≤ 24 H^{-1-ε}`, `Q² / 2H ≤ |L₂(v)| ≤ min (2 Q² / H) (3 H^{-ε/2})`, `|L₃(v)| ≤ 2 H / Q²`;
* Bugeaud's Claim: `Q |z₀ + (z₁ + z₂) α + z₃ α²| ≤ 12 (A + 1)² ∑ |zᵢ|` whenever `z ⊥ v`.

The heights of the points used grow at least doubly exponentially (`Real.Doubling`). This file
shows that a subspace of `ℚ⁴` of dimension at most `2` contains `O(log ε⁻¹)` of them
(`Real.card_mem_le_of_finrank_le_two`): two of its points determine the others, whose height is
at most a power `ε⁻¹ O(1)` of theirs (`Real.rpow_le_of_mem_span_pair`).

## Main definitions

* `Real.formL1`, `Real.formL2`, `Real.formL3`: the forms `α² x₀ - α (x₁ + x₂) + x₃`, `α x₀ - x₁`,
  `α x₀ - x₂`.
* `Real.CFPoint`: the inequalities at one point.
* `Real.Doubling`: `log H k ≥ 1` and `log H (k + 1) ≥ 2 log H k`.
* `Real.LiouvilleQuad α c D`: Liouville's inequality for `b₀ + b₁ α + b₂ α²`.

## Main results

* `Real.rpow_le_of_mem_span_pair`: a point in the span of two others has height at most
  `twoConst c D · H_b^{4D+4}` to the power `1 / ε`.
* `Real.Doubling.card_le`: the doubling count.
* `Real.card_mem_le_of_finrank_le_two`: **the planes**.
-/

@[expose] public section

open Finset Module

namespace Real

/-- `α² x₀ - α (x₁ + x₂) + x₃`, the paper's `P_n(α)`. -/
noncomputable def formL1 (α : ℝ) (v : Fin 4 → ℤ) : ℝ := α ^ 2 * v 0 - α * (v 1 + v 2) + v 3

/-- `α x₀ - x₁`. -/
noncomputable def formL2 (α : ℝ) (v : Fin 4 → ℤ) : ℝ := α * v 0 - v 1

/-- `α x₀ - x₂`. -/
noncomputable def formL3 (α : ℝ) (v : Fin 4 → ℤ) : ℝ := α * v 0 - v 2

/-- An integer point as a rational one. -/
def ptQ {n : ℕ} (v : Fin n → ℤ) : Fin n → ℚ := fun i ↦ v i

/-- **The inequalities at a point of §3**, for the height `H = q_w q_{w+r}` and `Q = q_w`. -/
structure CFPoint (α A ε : ℝ) (v : Fin 4 → ℤ) (H Q : ℝ) : Prop where
  abs_le : ∀ i, |(v i : ℝ)| ≤ H
  head : H ≤ (A + 1) ^ 4 * |(v 0 : ℝ)|
  one_le_Q : 1 ≤ Q
  sq_le : Q ^ 2 ≤ H
  L1_le : |formL1 α v| ≤ 24 * H ^ (-1 - ε)
  L2_le : |formL2 α v| ≤ 2 * Q ^ 2 / H
  L2_le_eps : |formL2 α v| ≤ 3 * H ^ (-(ε / 2))
  le_L2 : Q ^ 2 / (2 * H) ≤ |formL2 α v|
  L3_le : |formL3 α v| ≤ 2 * H / Q ^ 2
  claim : ∀ z : Fin 4 → ℝ, ∑ i, z i * v i = 0 →
    Q * |z 0 + (z 1 + z 2) * α + z 3 * α ^ 2| ≤ 12 * (A + 1) ^ 2 * ∑ i, |z i|

/-- **Liouville's inequality for `b₀ + b₁ α + b₂ α²`** with constants `c` and `D`. -/
def LiouvilleQuad (α c : ℝ) (D : ℕ) : Prop :=
  ∀ (b : Fin 3 → ℤ) (M : ℝ), b ≠ 0 → (∀ i, |(b i : ℝ)| ≤ M) → c ≤ |quadVal α b| * M ^ D

/-- **Doubly exponential growth** of the heights. -/
structure Doubling (H : ℕ → ℝ) : Prop where
  one_le_log : ∀ k, 1 ≤ log (H k)
  two_mul_log_le : ∀ k, 2 * log (H k) ≤ log (H (k + 1))

variable {α A ε : ℝ} {v : Fin 4 → ℤ} {H Q : ℝ}

namespace CFPoint

theorem one_le_H (p : CFPoint α A ε v H Q) : 1 ≤ H := by
  have := p.one_le_Q
  nlinarith [p.sq_le]

theorem H_pos (p : CFPoint α A ε v H Q) : 0 < H := lt_of_lt_of_le one_pos p.one_le_H

theorem v0_ne_zero (p : CFPoint α A ε v H Q) : v 0 ≠ 0 := by
  intro h
  have := p.head
  rw [h, Int.cast_zero, abs_zero, mul_zero] at this
  linarith [p.H_pos]

theorem one_le_abs_v0 (p : CFPoint α A ε v H Q) : 1 ≤ |(v 0 : ℝ)| := by
  have : (1 : ℤ) ≤ |v 0| := Int.one_le_abs p.v0_ne_zero
  exact_mod_cast this

theorem abs_formL1_le (p : CFPoint α A ε v H Q) (hα : |α| ≤ 1) : |formL1 α v| ≤ 4 * H := by
  have h0 := p.abs_le 0
  have h1 := p.abs_le 1
  have h2 := p.abs_le 2
  have h3 := p.abs_le 3
  have hα2 : |α ^ 2| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hα
  unfold formL1
  calc |α ^ 2 * v 0 - α * (v 1 + v 2) + v 3|
      ≤ |α ^ 2| * |(v 0 : ℝ)| + |α| * (|(v 1 : ℝ)| + |(v 2 : ℝ)|) + |(v 3 : ℝ)| := by
        refine (abs_add_le _ _).trans (add_le_add_left ((abs_sub _ _).trans ?_) _)
        rw [abs_mul, abs_mul]
        exact add_le_add_right (mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)) _
    _ ≤ 1 * H + 1 * (H + H) + H := by gcongr
    _ = 4 * H := by ring

theorem abs_formL2_le (p : CFPoint α A ε v H Q) (hα : |α| ≤ 1) : |formL2 α v| ≤ 2 * H := by
  have h0 := p.abs_le 0
  have h1 := p.abs_le 1
  unfold formL2
  calc |α * v 0 - v 1| ≤ |α| * |(v 0 : ℝ)| + |(v 1 : ℝ)| := by
        rw [← abs_mul]; exact abs_sub _ _
    _ ≤ 1 * H + H := by gcongr
    _ = 2 * H := by ring

/-- `L₁(v)` as `b₀ + b₁ α + b₂ α²`. -/
theorem formL1_eq (α : ℝ) (v : Fin 4 → ℤ) :
    formL1 α v = quadVal α ![v 3, -(v 1 + v 2), v 0] := by
  simp only [formL1, quadVal, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  push_cast
  ring

/-- **Liouville at `L₁(v)`**: `c ≤ |L₁(v)| (2 H)^D`. -/
theorem le_abs_formL1 (p : CFPoint α A ε v H Q) {c : ℝ} {D : ℕ} (hL : LiouvilleQuad α c D) :
    c ≤ |formL1 α v| * (2 * H) ^ D := by
  rw [formL1_eq]
  refine hL _ _ (fun h ↦ p.v0_ne_zero (by simpa using congrFun h 2)) fun i ↦ ?_
  have h0 := p.abs_le 0
  have h1 := p.abs_le 1
  have h2 := p.abs_le 2
  have h3 := p.abs_le 3
  have hH := p.H_pos
  fin_cases i
  · simp only [Fin.zero_eta, Matrix.cons_val_zero]; linarith
  · simp only [Fin.mk_one, Matrix.cons_val_one]
    push_cast
    rw [abs_neg]
    exact (abs_add_le _ _).trans (by linarith)
  · simp only [Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    linarith

theorem ne_zero_formL1 (p : CFPoint α A ε v H Q) {c : ℝ} {D : ℕ} (hc : 0 < c)
    (hL : LiouvilleQuad α c D) : formL1 α v ≠ 0 := by
  intro h
  have := p.le_abs_formL1 hL
  rw [h, abs_zero, zero_mul] at this
  linarith

end CFPoint

/-! ### Two points determine the others -/

/-- The constant of `Real.rpow_le_of_mem_span_pair`. -/
noncomputable def twoConst (c : ℝ) (D : ℕ) : ℝ := 1 + (120 * 4 ^ D / c) ^ 2 + 96 * 2 ^ D / c

theorem one_le_twoConst {c : ℝ} (hc : 0 < c) (D : ℕ) : 1 ≤ twoConst c D := by
  unfold twoConst
  have : 0 ≤ 96 * 2 ^ D / c := by positivity
  nlinarith [sq_nonneg (120 * 4 ^ D / c)]

/-- The coefficients of `L₁(x) L₂(y) - L₁(y) L₂(x)`, which is of degree `2` in `α`. -/
def detCoeff (x y : Fin 4 → ℤ) : Fin 3 → ℤ :=
  ![x 1 * y 3 - x 3 * y 1, x 2 * y 1 - x 1 * y 2 + x 3 * y 0 - x 0 * y 3, x 0 * y 2 - x 2 * y 0]

theorem quadVal_detCoeff (α : ℝ) (x y : Fin 4 → ℤ) :
    quadVal α (detCoeff x y) = formL1 α x * formL2 α y - formL1 α y * formL2 α x := by
  simp only [quadVal, detCoeff, formL1, formL2, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  push_cast
  ring

/-- **A point in the span of two others.** If `v_n = s v_a + t v_b` with `H_a ≤ H_b`, then
`H_n^ε ≤ twoConst c D · H_b^{4D+4}`. If `L₁(v_a) L₂(v_b) ≠ L₁(v_b) L₂(v_a)`, Cramer's rule with the
small forms `L₁, L₂` at `v_n` bounds `1 ≤ |v_{n,0}|`; otherwise `L₂ / L₁` is the same at the three
points, against `|L₂(v_n)| ≥ 1 / 2H_n`. -/
theorem rpow_le_of_mem_span_pair {c : ℝ} {D : ℕ} (hc : 0 < c) (hL : LiouvilleQuad α c D)
    (hα : |α| ≤ 1) (hε : 0 < ε) {va vb vn : Fin 4 → ℤ} {Ha Hb Hn Qa Qb Qn : ℝ}
    (pa : CFPoint α A ε va Ha Qa) (pb : CFPoint α A ε vb Hb Qb) (pn : CFPoint α A ε vn Hn Qn)
    (hab : Ha ≤ Hb) {s t : ℝ} (hst : ∀ i, (vn i : ℝ) = s * va i + t * vb i) :
    Hn ^ ε ≤ twoConst c D * Hb ^ (4 * D + 4) := by
  have hHa := pa.one_le_H
  have hHb := pb.one_le_H
  have hHn := pn.one_le_H
  have hHn0 : 0 < Hn := pn.H_pos
  set l1a := formL1 α va
  set l2a := formL2 α va
  set l1b := formL1 α vb
  set l2b := formL2 α vb
  set l1n := formL1 α vn
  set l2n := formL2 α vn
  have e1 : l1n = s * l1a + t * l1b := by
    simp only [l1n, l1a, l1b, formL1, hst]; ring
  have e2 : l2n = s * l2a + t * l2b := by
    simp only [l2n, l2a, l2b, formL2, hst]; ring
  have hpow : 1 ≤ Hb ^ (4 * D + 4) := one_le_pow₀ hHb
  have hT : 0 ≤ (120 * 4 ^ D / c) ^ 2 := sq_nonneg _
  have hT' : 0 ≤ 96 * 2 ^ D / c := by positivity
  set E := Hn ^ ε with hE
  have hE0 : 0 < E := Real.rpow_pos_of_pos hHn0 ε
  set F := Hn ^ (ε / 2) with hF
  have hF0 : 0 < F := Real.rpow_pos_of_pos hHn0 _
  have hFE : E = F ^ 2 := by
    rw [hE, hF, ← Real.rpow_natCast, ← Real.rpow_mul hHn0.le]; norm_num
  have hL1n : |l1n| ≤ 24 / (Hn * E) := by
    have := pn.L1_le
    rwa [show -1 - ε = -1 + -ε by ring, Real.rpow_add hHn0, Real.rpow_neg_one,
      Real.rpow_neg hHn0.le, ← mul_inv, ← div_eq_mul_inv] at this
  have hL2n : |l2n| ≤ 3 / F := by
    have := pn.L2_le_eps
    rwa [Real.rpow_neg hHn0.le, ← div_eq_mul_inv] at this
  by_cases hD : l1a * l2b - l1b * l2a = 0
  · -- `L₂ / L₁` is the same at `v_a` and `v_n`
    have key : l2n * l1a = l2a * l1n := by rw [e1, e2]; linear_combination t * hD
    have h1 := pa.le_abs_formL1 hL
    have h2 : 1 / (2 * Hn) ≤ |l2n| := by
      refine le_trans ?_ pn.le_L2
      gcongr
      nlinarith [pn.one_le_Q]
    have h4 : |l2a| ≤ 2 * Ha := pa.abs_formL2_le hα
    have h5 : |l1a| / (2 * Hn) ≤ 2 * Ha * (24 / (Hn * E)) := by
      calc |l1a| / (2 * Hn) = 1 / (2 * Hn) * |l1a| := by ring
        _ ≤ |l2n| * |l1a| := mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
        _ = |l2a| * |l1n| := by rw [← abs_mul, ← abs_mul, key]
        _ ≤ 2 * Ha * (24 / (Hn * E)) := mul_le_mul h4 hL1n (abs_nonneg _) (by positivity)
    have h6 : |l1a| ≤ 96 * Ha / E := by
      rw [div_le_iff₀ (by positivity)] at h5
      rw [le_div_iff₀ hE0]
      have : 2 * Ha * (24 / (Hn * E)) * (2 * Hn) * E = 96 * Ha := by field_simp; ring
      nlinarith
    have h7 : c ≤ 96 * Ha / E * (2 * Ha) ^ D :=
      h1.trans (mul_le_mul_of_nonneg_right h6 (by positivity))
    have h8 : E ≤ 96 * 2 ^ D / c * Ha ^ (D + 1) := by
      rw [mul_pow, div_mul_eq_mul_div, le_div_iff₀ hE0] at h7
      rw [div_mul_eq_mul_div, le_div_iff₀ hc]
      calc E * c ≤ 96 * Ha * (2 ^ D * Ha ^ D) := by linarith [mul_comm E c]
        _ = 96 * 2 ^ D * Ha ^ (D + 1) := by ring
    have h9 : Ha ^ (D + 1) ≤ Hb ^ (4 * D + 4) :=
      (pow_le_pow_left₀ (by linarith) hab _).trans (pow_le_pow_right₀ hHb (by omega))
    calc E ≤ 96 * 2 ^ D / c * Ha ^ (D + 1) := h8
      _ ≤ 96 * 2 ^ D / c * Hb ^ (4 * D + 4) := mul_le_mul_of_nonneg_left h9 hT'
      _ ≤ twoConst c D * Hb ^ (4 * D + 4) := by
          unfold twoConst
          nlinarith
  · -- Cramer's rule
    set Dv := l1a * l2b - l1b * l2a
    have hDq : quadVal α (detCoeff va vb) = Dv := quadVal_detCoeff α va vb
    have hb0 : detCoeff va vb ≠ 0 := by
      intro h
      rw [h] at hDq
      simp [quadVal] at hDq
      exact hD hDq.symm
    have hcoef : ∀ i, |(detCoeff va vb i : ℝ)| ≤ 4 * Hb ^ 2 := by
      have a0 := pa.abs_le 0; have a1 := pa.abs_le 1; have a2 := pa.abs_le 2
      have a3 := pa.abs_le 3
      have b0 := pb.abs_le 0; have b1 := pb.abs_le 1; have b2 := pb.abs_le 2
      have b3 := pb.abs_le 3
      have m (i j : Fin 4) : |(va i : ℝ) * vb j| ≤ Hb ^ 2 := by
        rw [abs_mul, sq]
        exact mul_le_mul ((pa.abs_le i).trans hab) (pb.abs_le j) (abs_nonneg _) (by linarith)
      intro i
      fin_cases i
      · simp only [detCoeff, Fin.zero_eta, Matrix.cons_val_zero]
        push_cast
        obtain ⟨p1, p2⟩ := abs_le.1 (m 1 3)
        obtain ⟨q1, q2⟩ := abs_le.1 (m 3 1)
        exact abs_le.2 ⟨by linarith, by linarith⟩
      · simp only [detCoeff, Fin.mk_one, Matrix.cons_val_one]
        push_cast
        obtain ⟨p1, p2⟩ := abs_le.1 (m 2 1)
        obtain ⟨q1, q2⟩ := abs_le.1 (m 1 2)
        obtain ⟨r1, r2⟩ := abs_le.1 (m 3 0)
        obtain ⟨s1, s2⟩ := abs_le.1 (m 0 3)
        exact abs_le.2 ⟨by linarith, by linarith⟩
      · simp only [detCoeff, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons,
          Matrix.head_cons]
        push_cast
        obtain ⟨p1, p2⟩ := abs_le.1 (m 0 2)
        obtain ⟨q1, q2⟩ := abs_le.1 (m 2 0)
        exact abs_le.2 ⟨by linarith, by linarith⟩
    have hLv := hL _ _ hb0 hcoef
    rw [hDq] at hLv
    -- Cramer
    have cs : s * Dv = l1n * l2b - l2n * l1b := by rw [e1, e2]; ring
    have ct : t * Dv = l1a * l2n - l2a * l1n := by rw [e1, e2]; ring
    have hv0 : Dv * vn 0 = (s * Dv) * va 0 + (t * Dv) * vb 0 := by rw [hst 0]; ring
    have b1a : |l1a| ≤ 4 * Hb := (pa.abs_formL1_le hα).trans (by linarith)
    have b2a : |l2a| ≤ 2 * Hb := (pa.abs_formL2_le hα).trans (by linarith)
    have b1b : |l1b| ≤ 4 * Hb := pb.abs_formL1_le hα
    have b2b : |l2b| ≤ 2 * Hb := pb.abs_formL2_le hα
    have va0 : |(va 0 : ℝ)| ≤ Hb := (pa.abs_le 0).trans hab
    have vb0 : |(vb 0 : ℝ)| ≤ Hb := pb.abs_le 0
    have hL1n' : |l1n| ≤ 24 / F := by
      refine hL1n.trans ?_
      rw [div_le_div_iff₀ (by positivity) hF0]
      have hFE' : F ≤ E := by
        rw [hF, hE]
        exact Real.rpow_le_rpow_of_exponent_le hHn (by linarith)
      have : F ≤ Hn * E := by nlinarith
      linarith
    have hsD : |s * Dv| ≤ 2 * Hb * (24 / F) + 4 * Hb * (3 / F) := by
      rw [cs]
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_mul]
      have m1 := mul_le_mul hL1n' b2b (abs_nonneg _) (div_nonneg (by norm_num) hF0.le)
      have m2 := mul_le_mul hL2n b1b (abs_nonneg _) (div_nonneg (by norm_num) hF0.le)
      linarith
    have htD : |t * Dv| ≤ 4 * Hb * (3 / F) + 2 * Hb * (24 / F) := by
      rw [ct]
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_mul]
      have m1 := mul_le_mul b1a hL2n (abs_nonneg _) (by linarith)
      have m2 := mul_le_mul b2a hL1n' (abs_nonneg _) (by linarith)
      linarith
    have hDle : |Dv| ≤ 120 * Hb ^ 2 / F := by
      have h1 : |Dv| * 1 ≤ |Dv| * |(vn 0 : ℝ)| :=
        mul_le_mul_of_nonneg_left pn.one_le_abs_v0 (abs_nonneg _)
      have h2 : |Dv| * |(vn 0 : ℝ)| ≤ |s * Dv| * |(va 0 : ℝ)| + |t * Dv| * |(vb 0 : ℝ)| := by
        rw [← abs_mul, hv0, ← abs_mul, ← abs_mul]; exact abs_add_le _ _
      have h3 : |s * Dv| * |(va 0 : ℝ)| ≤ (2 * Hb * (24 / F) + 4 * Hb * (3 / F)) * Hb :=
        mul_le_mul hsD va0 (abs_nonneg _) (by positivity)
      have h4 : |t * Dv| * |(vb 0 : ℝ)| ≤ (4 * Hb * (3 / F) + 2 * Hb * (24 / F)) * Hb :=
        mul_le_mul htD vb0 (abs_nonneg _) (by positivity)
      have : (2 * Hb * (24 / F) + 4 * Hb * (3 / F)) * Hb +
          (4 * Hb * (3 / F) + 2 * Hb * (24 / F)) * Hb = 120 * Hb ^ 2 / F := by
        field_simp; ring
      linarith
    have h7 : c ≤ 120 * Hb ^ 2 / F * (4 * Hb ^ 2) ^ D :=
      hLv.trans (mul_le_mul_of_nonneg_right hDle (by positivity))
    have h8 : F ≤ 120 * 4 ^ D / c * Hb ^ (2 * D + 2) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hF0] at h7
      rw [div_mul_eq_mul_div, le_div_iff₀ hc]
      calc F * c ≤ 120 * Hb ^ 2 * (4 * Hb ^ 2) ^ D := by linarith
        _ = 120 * 4 ^ D * Hb ^ (2 * D + 2) := by ring
    have h9 : E ≤ (120 * 4 ^ D / c) ^ 2 * Hb ^ (4 * D + 4) := by
      rw [hFE]
      calc F ^ 2 ≤ (120 * 4 ^ D / c * Hb ^ (2 * D + 2)) ^ 2 := pow_le_pow_left₀ hF0.le h8 2
        _ = (120 * 4 ^ D / c) ^ 2 * Hb ^ (4 * D + 4) := by ring
    have hsplit : twoConst c D * Hb ^ (4 * D + 4) = (120 * 4 ^ D / c) ^ 2 * Hb ^ (4 * D + 4) +
        (1 + 96 * 2 ^ D / c) * Hb ^ (4 * D + 4) := by unfold twoConst; ring
    have := mul_nonneg (by positivity : (0 : ℝ) ≤ 1 + 96 * 2 ^ D / c) (zero_le_one.trans hpow)
    linarith

/-! ### The doubling count -/

namespace Doubling

variable {H : ℕ → ℝ}

theorem pow_mul_le (h : Doubling H) {b k : ℕ} (hbk : b ≤ k) :
    (2 : ℝ) ^ (k - b) * log (H b) ≤ log (H k) := by
  induction k, hbk using Nat.le_induction with
  | base => simp
  | succ k hbk ih =>
    rw [show k + 1 - b = (k - b) + 1 by omega, pow_succ]
    have := h.two_mul_log_le k
    nlinarith

theorem log_mono (h : Doubling H) {b k : ℕ} (hbk : b ≤ k) : log (H b) ≤ log (H k) := by
  have h1 := h.pow_mul_le hbk
  have h2 : (1 : ℝ) ≤ 2 ^ (k - b) := one_le_pow₀ (by norm_num)
  have h3 := h.one_le_log b
  nlinarith

/-- **The doubling count**: at most `log₂ M + 1` indices `k ≥ b` have `log H_k ≤ M log H_b`. -/
theorem card_le (h : Doubling H) (I : Finset ℕ) (b : ℕ) {M : ℝ} (hM : 1 ≤ M) :
    (#{k ∈ I | b ≤ k ∧ log (H k) ≤ M * log (H b)} : ℝ) ≤ logb 2 M + 1 := by
  have hl0 : 0 ≤ logb 2 M := Real.logb_nonneg (by norm_num) hM
  have hsub : {k ∈ I | b ≤ k ∧ log (H k) ≤ M * log (H b)} ⊆
      Finset.Icc b (b + ⌊logb 2 M⌋₊) := by
    intro k hk
    simp only [Finset.mem_filter] at hk
    obtain ⟨-, hbk, hk⟩ := hk
    have h1 := h.pow_mul_le hbk
    have hb1 := h.one_le_log b
    have h2 : (2 : ℝ) ^ (k - b) ≤ M := by
      by_contra hlt
      push Not at hlt
      nlinarith
    have h3 : ((k - b : ℕ) : ℝ) ≤ logb 2 M := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith), Real.rpow_natCast]
      exact h2
    have h4 : k - b ≤ ⌊logb 2 M⌋₊ := Nat.le_floor h3
    simp only [Finset.mem_Icc]
    omega
  calc (#{k ∈ I | b ≤ k ∧ log (H k) ≤ M * log (H b)} : ℝ)
      ≤ #(Finset.Icc b (b + ⌊logb 2 M⌋₊)) := by exact_mod_cast Finset.card_le_card hsub
    _ = ⌊logb 2 M⌋₊ + 1 := by
        rw [Nat.card_Icc, show b + ⌊logb 2 M⌋₊ + 1 - b = ⌊logb 2 M⌋₊ + 1 by omega]
        push_cast; ring
    _ ≤ logb 2 M + 1 := by linarith [Nat.floor_le hl0]

end Doubling

/-! ### The planes -/

/-- The ratio of the logarithmic heights in a plane: `(log twoConst + 4 D + 4) / ε`. -/
noncomputable def planeRatio (c : ℝ) (D : ℕ) (ε : ℝ) : ℝ := (log (twoConst c D) + 4 * D + 4) / ε

/-- **The number of points in a plane**: `2 (log₂ planeRatio + 1)`. -/
noncomputable def planeBound (c : ℝ) (D : ℕ) (ε : ℝ) : ℝ := 2 * (logb 2 (planeRatio c D ε) + 1)

theorem one_le_planeRatio {c : ℝ} (hc : 0 < c) (D : ℕ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    1 ≤ planeRatio c D ε := by
  rw [planeRatio, le_div_iff₀ hε]
  have := Real.log_nonneg (one_le_twoConst hc D)
  have : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  linarith

theorem planeBound_nonneg {c : ℝ} (hc : 0 < c) (D : ℕ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 ≤ planeBound c D ε := by
  have := Real.logb_nonneg (b := 2) (by norm_num) (one_le_planeRatio hc D hε hε1)
  rw [planeBound]; positivity

/-- From `H_n^ε ≤ twoConst · H_b^{4D+4}` to `log H_n ≤ planeRatio · log H_b`. -/
theorem log_le_planeRatio_mul {c : ℝ} (hc : 0 < c) {D : ℕ} (hε : 0 < ε) {Hn Hb : ℝ}
    (hHn : 1 ≤ Hn) (hHb1 : 1 ≤ Hb) (hHb : 1 ≤ log Hb)
    (h : Hn ^ ε ≤ twoConst c D * Hb ^ (4 * D + 4)) :
    log Hn ≤ planeRatio c D ε * log Hb := by
  have hHb0 : 0 < Hb := by linarith
  have hT := one_le_twoConst hc D
  have h1 := Real.log_le_log (by positivity) h
  rw [Real.log_rpow (by linarith), Real.log_mul (by positivity) (by positivity),
    Real.log_pow] at h1
  have hlT := Real.log_nonneg hT
  rw [planeRatio, div_mul_eq_mul_div, le_div_iff₀ hε]
  push_cast at h1
  nlinarith

variable {c : ℝ} {D : ℕ} {Hs Qs : ℕ → ℝ} {vs : ℕ → Fin 4 → ℤ}

/-- Rational coefficients in a span give real coefficients on the coordinates. -/
theorem exists_real_of_mem_span_pair {x y z : Fin 4 → ℤ}
    (h : ptQ z ∈ Submodule.span ℚ (Set.range ![ptQ x, ptQ y])) :
    ∃ s t : ℝ, ∀ i, (z i : ℝ) = s * x i + t * y i := by
  obtain ⟨f, hf⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).1 h
  refine ⟨f 0, f 1, fun i ↦ ?_⟩
  have := congrFun hf i
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, ptQ] at this
  exact_mod_cast this.symm

open scoped Classical in
/-- **A subspace of dimension at most `2` holds at most `planeBound c D ε` points.** -/
theorem card_mem_le_of_finrank_le_two (hc : 0 < c) (hL : LiouvilleQuad α c D) (hα : |α| ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hdbl : Doubling Hs) (I : Finset ℕ)
    (hpt : ∀ k ∈ I, CFPoint α A ε (vs k) (Hs k) (Qs k)) (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : finrank ℚ P ≤ 2) :
    (#{k ∈ I | ptQ (vs k) ∈ P} : ℝ) ≤ planeBound c D ε := by
  classical
  set M := planeRatio c D ε
  have hM := one_le_planeRatio hc D hε hε1
  set K0 := {k ∈ I | ptQ (vs k) ∈ P}
  rcases K0.eq_empty_or_nonempty with h0 | hne
  · rw [h0, Finset.card_empty, Nat.cast_zero]; exact planeBound_nonneg hc D hε hε1
  have hHmono {a b : ℕ} (ha : a ∈ I) (hb : b ∈ I) (hab : a ≤ b) : Hs a ≤ Hs b := by
    have := hdbl.log_mono hab
    exact (Real.log_le_log_iff (hpt a ha).H_pos (hpt b hb).H_pos).1 this
  set a := K0.min' hne
  have ha : a ∈ K0 := K0.min'_mem hne
  have haI : a ∈ I := (Finset.mem_filter.1 ha).1
  have hpa := hpt a haI
  have hva : ptQ (vs a) ≠ 0 := fun h ↦ hpa.v0_ne_zero (by
    have := congrFun h 0
    simpa [ptQ] using this)
  set L := ℚ ∙ ptQ (vs a)
  have hsplit := Finset.card_filter_add_card_filter_not (s := K0) (fun k ↦ ptQ (vs k) ∈ L)
  -- the line through `v_a`
  have hK1 : ({k ∈ K0 | ptQ (vs k) ∈ L} : Finset ℕ) ⊆
      {k ∈ I | a ≤ k ∧ log (Hs k) ≤ M * log (Hs a)} := by
    intro k hk
    simp only [Finset.mem_filter, K0] at hk ⊢
    obtain ⟨⟨hkI, hkP⟩, hkL⟩ := hk
    refine ⟨hkI, K0.min'_le k (Finset.mem_filter.2 ⟨hkI, hkP⟩), ?_⟩
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hkL
    refine log_le_planeRatio_mul hc hε (hpt k hkI).one_le_H hpa.one_le_H (hdbl.one_le_log a)
      (rpow_le_of_mem_span_pair hc hL hα hε hpa hpa (hpt k hkI) le_rfl (s := r) (t := 0)
        fun i ↦ ?_)
    have := congrFun hr i
    simp only [Pi.smul_apply, smul_eq_mul, ptQ] at this
    have : (vs k i : ℝ) = (r : ℝ) * vs a i := by exact_mod_cast this.symm
    rw [this]; ring
  have hc1 := (Nat.cast_le (α := ℝ)).2 (Finset.card_le_card hK1)
  have hb1 := hdbl.card_le I a hM
  -- the rest
  set K2 := ({k ∈ K0 | ptQ (vs k) ∉ L} : Finset ℕ)
  have hc2 : (#K2 : ℝ) ≤ logb 2 M + 1 := by
    rcases K2.eq_empty_or_nonempty with h2 | hne2
    · rw [h2, Finset.card_empty, Nat.cast_zero]
      linarith [Real.logb_nonneg (b := 2) (by norm_num) hM]
    set b := K2.min' hne2
    have hb : b ∈ K2 := K2.min'_mem hne2
    simp only [K2, Finset.mem_filter, K0] at hb
    obtain ⟨⟨hbI, hbP⟩, hbL⟩ := hb
    have hab : a ≤ b := K0.min'_le b (Finset.mem_filter.2 ⟨hbI, hbP⟩)
    have hpb := hpt b hbI
    -- `P` is spanned by `v_a, v_b`
    have hli : LinearIndependent ℚ ![ptQ (vs a), ptQ (vs b)] := by
      rw [LinearIndependent.pair_iff' hva]
      intro r hr
      exact hbL (Submodule.mem_span_singleton.2 ⟨r, hr⟩)
    have hspan : Submodule.span ℚ (Set.range ![ptQ (vs a), ptQ (vs b)]) = P := by
      refine Submodule.eq_of_le_of_finrank_le ?_ ?_
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        fin_cases i
        · exact (Finset.mem_filter.1 ha).2
        · exact hbP
      · rw [finrank_span_eq_card hli, Fintype.card_fin]; exact hP
    have hsub : K2 ⊆ {k ∈ I | b ≤ k ∧ log (Hs k) ≤ M * log (Hs b)} := by
      intro k hk
      have hkb : b ≤ k := K2.min'_le k hk
      simp only [K2, Finset.mem_filter, K0] at hk
      obtain ⟨⟨hkI, hkP⟩, -⟩ := hk
      simp only [Finset.mem_filter]
      refine ⟨hkI, hkb, ?_⟩
      rw [← hspan] at hkP
      obtain ⟨s, t, hst⟩ := exists_real_of_mem_span_pair hkP
      exact log_le_planeRatio_mul hc hε (hpt k hkI).one_le_H hpb.one_le_H (hdbl.one_le_log b)
        (rpow_le_of_mem_span_pair hc hL hα hε hpa hpb (hpt k hkI) (hHmono haI hbI hab) hst)
    exact ((Nat.cast_le (α := ℝ)).2 (Finset.card_le_card hsub)).trans (hdbl.card_le I b hM)
  have : (#K0 : ℝ) = #({k ∈ K0 | ptQ (vs k) ∈ L} : Finset ℕ) + #K2 := by
    rw [← hsplit]; push_cast; ring
  rw [this, planeBound]
  linarith

end Real
