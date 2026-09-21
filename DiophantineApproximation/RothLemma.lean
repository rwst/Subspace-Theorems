/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.DisjointVariables
public import DiophantineApproximation.RothBaseCase
public import DiophantineApproximation.RothDecomposition
public import DiophantineApproximation.RothDeterminant
public import DiophantineApproximation.RothEstimates
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Roth's lemma

**Roth's lemma** (Bombieri–Gubler, Lemma 6.3.7): for a nonzero `P` in `m` variables over a number
field, with `degreeOf j P ≤ d j`, degrees that drop by a factor at least `σ ≤ 1/2` at each step,
and a point `ξ` whose coordinates are high enough against the height of `P`, the index of `P` at
`ξ` is at most `2 m σ ^ (2 ^ (1 - m))`.

The proof is the induction the roadmap describes, and this file is only its bookkeeping: the
decomposition and the determinant identity are `DiophantineApproximation/RothDecomposition.lean`,
the three estimates on the determinant are `DiophantineApproximation/RothDeterminant.lean`, the
one-variable case is `DiophantineApproximation/RothBaseCase.lean`, and the real inequalities are
`DiophantineApproximation/RothEstimates.lean`.

## Main results

* `MvPolynomial.rothProp`: the induction, in the normalization in which the separated variable is
  `X 0` and the degrees **increase**.
* `MvPolynomial.index_le_of_degree_ratio`: Roth's lemma in the book's normalization, with
  decreasing degrees and the exponent `(1 / 2) ^ (m - 1)`.

## Implementation notes

⚠ **The parameter of the induction is `θ`, not `σ`.** Written with `σ` the inductive step would
have to replace `σ` by `√σ`, a real power; written with `θ` and `σ = θ ^ (2 ^ m)` it replaces `θ`
by `θ ^ 2` and *leaves `σ` alone*, so the hypotheses on the degrees carry over unchanged and no
`Real.rpow` appears anywhere inside the induction. The book's statement is recovered once, at the
end, by taking `θ = σ ^ ((1 / 2) ^ (m - 1))`.

⚠ **The reduction to `θ < 1/2` is what makes the constant uniform.** At `θ ≥ 1/2` the conclusion
`index ≤ 2 m θ` is free, because the index of a polynomial of partial degrees at most `d` is at
most the number of variables; so the inductive step may assume `θ < 1/2`, and it is that
assumption — through `θ ^ 2 < θ / 2` — that closes the two cases of the quadratic estimate with
room to spare. Without it the base case would have to be carried at the sharper constant `1`.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Lemma 6.3.7 and Lemma 6.3.9.

This is Layer 2.7 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Finset Height AdmissibleAbsValues

open scoped ENNReal

namespace MvPolynomial

/-- **The constant of Roth's lemma** in `m + 1` variables. -/
def rothConst (m : ℕ) : ℝ := 2 * (m + 1)

theorem rothConst_le (m : ℕ) : rothConst m ≤ 2 * m + 2 := le_of_eq (by rw [rothConst]; ring)

theorem rothConst_nonneg (m : ℕ) : 0 ≤ rothConst m := by
  rw [rothConst]
  positivity

theorem rothConst_succ (m : ℕ) : rothConst (m + 1) = 2 * (m + 2) := by
  rw [rothConst]
  push_cast
  ring

/-- **The statement of Roth's lemma in `m + 1` variables**, in the normalization in which the
separated variable is `X 0` and the degrees increase. -/
def RothProp (K : Type*) [Field K] [NumberField K] (m : ℕ) : Prop :=
  ∀ θ : ℝ, 0 < θ → θ ^ 2 ^ m ≤ 1 / 2 →
    ∀ d : Fin (m + 1) → ℕ, (∀ j, 1 ≤ d j) →
      (∀ j : Fin m, (d j.castSucc : ℝ) ≤ θ ^ 2 ^ m * d j.succ) →
      ∀ P : MvPolynomial (Fin (m + 1)) K, P ≠ 0 → (∀ j, P.degreeOf j ≤ d j) →
        ∀ ξ : Fin (m + 1) → K,
          (∀ j, P.logHeight + 4 * (m + 1) * d (Fin.last m) * totalWeight K
                  ≤ θ ^ 2 ^ m * (d j * logHeight₁ (ξ j))) →
          index (fun j ↦ (d j : ℝ)) ξ P ≤ ENNReal.ofReal (rothConst m * θ)

variable {K : Type*} [Field K] [NumberField K]

/-- **Roth's lemma in one variable.** -/
theorem rothProp_zero : RothProp K 0 := by
  let _ : Unique (Fin (0 + 1)) := ⟨⟨0⟩, fun j ↦ Fin.ext (by omega)⟩
  intro θ hθ0 hθ1 d hd1 _ P hP hdeg ξ hheight
  simp only [pow_zero, pow_one] at hθ1 hheight
  have hlast : (Fin.last 0 : Fin (0 + 1)) = default := Fin.ext (by omega)
  have hfun : (fun j : Fin (0 + 1) ↦ (d j : ℝ))
      = fun _ : Fin (0 + 1) ↦ ((d default : ℕ) : ℝ) :=
    funext fun j ↦ by rw [show j = default from Fin.ext (by omega)]
  rw [hfun]
  refine le_trans (index_le_base hP (hd1 default) (hdeg default) ξ hθ0 ?_) ?_
  · have h := hheight default
    rw [hlast] at h
    push_cast at h ⊢
    linarith
  · refine ENNReal.ofReal_le_ofReal ?_
    rw [rothConst]
    push_cast
    linarith

/-- **The height of the determinant of the matrix of Hasse derivatives**, in the form the
induction consumes: `p` times the height of `P` plus `p` times `4 d`, where `d` is the largest
degree. The three contributions are `log p!` from the Leibniz expansion, `2 (∑ j, d j) p log 2`
from the multiplications and the differentiations, and nothing else. -/
theorem logHeight_det_le_roth {m p : ℕ} {d : Fin (m + 2) → ℕ} {P : MvPolynomial (Fin (m + 2)) K}
    (hP : P ≠ 0) (hdeg : ∀ j, P.degreeOf j ≤ d j)
    (hdd : ∀ j : Fin (m + 1), 2 * (d j.castSucc : ℝ) ≤ d j.succ)
    (hple : p ≤ d 0 + 1) (ρ : Fin p → Fin p → (Fin (m + 2) →₀ ℕ)) :
    (Matrix.of fun i j ↦ hasseDeriv (ρ i j) P).det.logHeight
      ≤ p * (P.logHeight + 4 * (d (Fin.last (m + 1)) : ℝ) * totalWeight K) := by
  have hmono : Monotone fun j ↦ (d j : ℝ) := Fin.monotone_iff_le_succ.mpr fun j ↦ by
    have h := hdd j
    have h0 : (0 : ℝ) ≤ (d j.castSucc : ℝ) := Nat.cast_nonneg _
    linarith
  set M : ℝ := (d (Fin.last (m + 1)) : ℝ) with hM
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hd0M : (d 0 : ℝ) ≤ M := hmono (Fin.zero_le _)
  have hDsum : ∑ j, (d j : ℝ) ≤ 2 * M :=
    Fin.sum_le_two_mul_last _ (fun j ↦ Nat.cast_nonneg _) hdd
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have hplereal : (p : ℝ) ≤ M + 1 := by
    have hpd : (p : ℝ) ≤ (d 0 : ℝ) + 1 := by exact_mod_cast hple
    linarith
  have hlogp : Real.log p ≤ M := by
    rcases Nat.eq_zero_or_pos p with rfl | hpp
    · simpa using hM0
    · refine le_trans (Real.log_le_log (by exact_mod_cast hpp) hplereal) ?_
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < M + 1 by linarith)
      linarith
  have hfact : Real.log (p.factorial : ℝ) ≤ (p : ℝ) * M := by
    have h1 : ((p.factorial : ℕ) : ℝ) ≤ ((p ^ p : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_le_pow p
    refine le_trans (Real.log_le_log (by exact_mod_cast p.factorial_pos) h1) ?_
    rw [Nat.cast_pow, Real.log_pow]
    exact mul_le_mul_of_nonneg_left hlogp hp0
  have hlog2' : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hA : 2 * (∑ j, (d j : ℝ)) * p * Real.log 2 ≤ 4 * M * p * Real.log 2 := by
    nlinarith [hDsum, mul_nonneg hp0 hlog2']
  have hB : 4 * M * p * Real.log 2 ≤ 4 * M * p * 0.6931471808 := by
    nlinarith [Real.log_two_lt_d9, mul_nonneg hM0 hp0]
  have hkey : Real.log (p.factorial : ℝ) + 2 * (∑ j, (d j : ℝ)) * p * Real.log 2
      ≤ 4 * (p : ℝ) * M := by
    nlinarith [hfact, hA, hB, mul_nonneg hp0 hM0]
  have htw : (0 : ℝ) ≤ (totalWeight K : ℝ) := Nat.cast_nonneg _
  refine le_trans (logHeight_det_hasseDeriv_le hP hdeg ρ) ?_
  nlinarith [hkey, htw]

/-- A weighted sum of an order against weights bounded below. -/
theorem _root_.Finsupp.sum_div_le_degree_div {σ : Type*} (μ : σ →₀ ℕ) {D : σ → ℝ} {e : ℝ}
    (he : 0 < e) (hD : ∀ l, e ≤ D l) :
    (μ.sum fun l k ↦ (k : ℝ) / D l) ≤ ((μ.degree : ℕ) : ℝ) / e := by
  have hDpos : ∀ l, 0 < D l := fun l ↦ lt_of_lt_of_le he (hD l)
  rw [Finsupp.degree_apply, Nat.cast_sum, Finset.sum_div, Finsupp.sum]
  refine Finset.sum_le_sum fun l _ ↦ ?_
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) he (hD l)

/-- **The inductive step of Roth's lemma.** -/
theorem rothProp_succ {m : ℕ} (ih : RothProp K m) : RothProp K (m + 1) := by
  intro θ hθ0 hθ1 d hd1 hratio P hP hdeg ξ hheight
  set s : ℝ := θ ^ 2 ^ (m + 1) with hsdef
  obtain ⟨dr, hdrf⟩ : ∃ dr : Fin (m + 2) → ℝ, dr = fun j ↦ (d j : ℝ) := ⟨_, rfl⟩
  have hdr : ∀ j, dr j = (d j : ℝ) := fun j ↦ by rw [hdrf]
  rw [← hdrf]
  have hdrpos : ∀ j, 0 < dr j := fun j ↦ by
    rw [hdr]
    exact_mod_cast hd1 j
  have hdrnn : ∀ j, 0 ≤ dr j := fun j ↦ (hdrpos j).le
  have hθlt1 : θ < 1 := by
    by_contra hc
    push Not at hc
    exact absurd hθ1 (by nlinarith [one_le_pow₀ hc (n := 2 ^ (m + 1))])
  have hs0 : 0 < s := by
    rw [hsdef]
    positivity
  have hsθ2 : s ≤ θ ^ 2 := by
    rw [hsdef]
    exact pow_le_pow_of_le_one hθ0.le hθlt1.le
      (by simpa using Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) (show 1 ≤ m + 1 by omega))
  have hshalf : s ≤ 1 / 2 := hθ1
  have hdd : ∀ j : Fin (m + 1), 2 * dr j.castSucc ≤ dr j.succ := by
    intro j
    have h := hratio j
    have h2 : s * dr j.succ ≤ (1 / 2) * dr j.succ :=
      mul_le_mul_of_nonneg_right hshalf (hdrnn _)
    rw [hdr, hdr]
    rw [hdr] at h2
    linarith
  have hTcard : index dr ξ P ≤ ((m + 2 : ℕ) : ℝ≥0∞) := by
    have h := index_le_card hdrpos hP (fun j ↦ by rw [hdr]; exact_mod_cast hdeg j) ξ
    simpa using h
  rcases le_or_gt (1 / 2 : ℝ) θ with hbig | hsmall
  · refine le_trans hTcard ?_
    rw [← ENNReal.ofReal_natCast, rothConst_succ]
    refine ENNReal.ofReal_le_ofReal ?_
    push_cast
    nlinarith
  by_contra hcon
  push Not at hcon
  have hTne : index dr ξ P ≠ ⊤ := ne_top_of_le_ne_top (by simp) hTcard
  set t : ℝ := (index dr ξ P).toReal with htdef
  have hTeq : index dr ξ P = ENNReal.ofReal t := (ENNReal.ofReal_toReal hTne).symm
  have ht0 : 0 ≤ t := ENNReal.toReal_nonneg
  have htlb : rothConst (m + 1) * θ < t := by
    by_contra hle
    push Not at hle
    have hbad : index dr ξ P ≤ ENNReal.ofReal (rothConst (m + 1) * θ) := by
      rw [hTeq]
      exact ENNReal.ofReal_le_ofReal hle
    exact absurd hbad (not_le.mpr hcon)
  obtain ⟨p, f, g, hp0, hple, hfind, hgind, hdecomp⟩ := exists_tensor_decomposition hP
  obtain ⟨μ, hμord, hWf0⟩ := exists_genWronskian_ne_zero hfind
  obtain ⟨ν, hνord, hWg0⟩ := exists_genWronskian_ne_zero hgind
  set Wf := genWronskian μ f with hWfd
  set Wg := genWronskian ν g with hWgd
  set U := (hasseDerivMatrix μ ν P).det with hUd
  have hple' : p ≤ d 0 + 1 := le_trans hple (Nat.add_le_add_right (hdeg 0) 1)
  have hUeq : U = rename Fin.succ Wf * rename (lastVar (m + 1)) Wg :=
    det_hasseDerivMatrix f g hdecomp μ ν
  have hrenWf0 : rename (Fin.succ : Fin (m + 1) → Fin (m + 2)) Wf ≠ 0 :=
    fun h ↦ hWf0 (rename_injective _ (Fin.succ_injective _) (by rw [h, map_zero]))
  have hrenWg0 : rename (lastVar (m + 1)) Wg ≠ 0 :=
    fun h ↦ hWg0 (rename_injective _ (lastVar_injective _) (by rw [h, map_zero]))
  have hU0 : U ≠ 0 := by
    rw [hUeq]
    exact mul_ne_zero hrenWf0 hrenWg0
  have hdisj : Disjoint (Set.range (Fin.succ : Fin (m + 1) → Fin (m + 2)))
      (Set.range (lastVar (m + 1))) := by
    rw [range_lastVar, Set.disjoint_singleton_right]
    exact zero_notMem_range_succ
  have hEdeg : ∀ (i j : Fin p) (l : Fin (m + 2)),
      (hasseDerivMatrix μ ν P i j).degreeOf l ≤ d l := fun i j l ↦
    le_trans (le_trans (degreeOf_hasseDeriv_le _ _ _) (Nat.sub_le _ _)) (hdeg l)
  have hUdeg : ∀ l, U.degreeOf l ≤ p * d l := fun l ↦
    degreeOf_det_le _ l fun i j ↦ hEdeg i j l
  have hWfdeg : ∀ j : Fin (m + 1), Wf.degreeOf j ≤ p * d j.succ := by
    intro j
    have h1 : U.degreeOf j.succ = (rename Fin.succ Wf).degreeOf j.succ
        + (rename (lastVar (m + 1)) Wg).degreeOf j.succ := by
      rw [hUeq, degreeOf_mul_eq hrenWf0 hrenWg0]
    rw [degreeOf_rename_eq_zero (notMem_range_lastVar (Fin.succ_ne_zero j)),
      degreeOf_rename_of_injective (Fin.succ_injective _), add_zero] at h1
    rw [← h1]
    exact hUdeg j.succ
  have hWgdeg : Wg.degreeOf default ≤ p * d 0 := by
    have hdf : (default : Fin 1) = 0 := Subsingleton.elim _ _
    have h2 : (rename (lastVar (m + 1)) Wg).degreeOf 0 = Wg.degreeOf 0 :=
      degreeOf_rename_of_injective (lastVar_injective (m + 1)) (0 : Fin 1)
    have h1 : U.degreeOf 0 = (rename (Fin.succ : Fin (m + 1) → Fin (m + 2)) Wf).degreeOf 0
        + (rename (lastVar (m + 1)) Wg).degreeOf 0 := by
      rw [hUeq, degreeOf_mul_eq hrenWf0 hrenWg0]
    rw [degreeOf_rename_eq_zero zero_notMem_range_succ, zero_add, h2] at h1
    rw [hdf, ← h1]
    exact hUdeg 0
  have hdd' : ∀ j : Fin (m + 1), 2 * (d j.castSucc : ℝ) ≤ (d j.succ : ℝ) := fun j ↦ by
    rw [← hdr, ← hdr]
    exact hdd j
  have hUheight : U.logHeight
      ≤ p * (P.logHeight + 4 * (d (Fin.last (m + 1)) : ℝ) * totalWeight K) :=
    logHeight_det_le_roth hP hdeg hdd' hple'
      (fun i j ↦ (μ i).mapDomain Fin.succ + (ν j).mapDomain (lastVar (m + 1)))
  have hsplit : Wf.logHeight + Wg.logHeight = U.logHeight := by
    rw [hUeq]
    exact (logHeight_rename_mul_rename_of_disjoint (Fin.succ_injective _)
      (lastVar_injective _) hdisj hWf0 hWg0).symm
  have hWfh : Wf.logHeight ≤ U.logHeight := by
    have h := MvPolynomial.logHeight_nonneg Wg
    linarith [hsplit]
  have hWgh : Wg.logHeight ≤ U.logHeight := by
    have h := MvPolynomial.logHeight_nonneg Wf
    linarith [hsplit]
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp0
  have htw : (0 : ℝ) ≤ (totalWeight K : ℝ) := Nat.cast_nonneg _
  have hpow : (θ ^ 2) ^ 2 ^ m = s := by
    rw [hsdef, ← pow_mul, pow_succ]
    ring_nf
  have hmono : Monotone dr := Fin.monotone_iff_le_succ.mpr fun j ↦ by
    have h := hdd j
    have h0 := hdrnn j.castSucc
    linarith
  have hIHf : index (fun j : Fin (m + 1) ↦ ((p * d j.succ : ℕ) : ℝ)) (fun j ↦ ξ j.succ) Wf
      ≤ ENNReal.ofReal (rothConst m * θ ^ 2) := by
    refine ih (θ ^ 2) (by positivity) (by rw [hpow]; exact hθ1) (fun j ↦ p * d j.succ)
      (fun j ↦ Nat.mul_pos hp0 (hd1 j.succ)) (fun j ↦ ?_) Wf hWf0 hWfdeg
      (fun j ↦ ξ j.succ) (fun j ↦ ?_)
    · rw [hpow]
      have h := hratio j.succ
      rw [← Fin.succ_castSucc] at h
      push_cast
      nlinarith [h, hpr]
    · rw [hpow, Fin.succ_last]
      have hh := mul_le_mul_of_nonneg_left (hheight j.succ) hpr.le
      push_cast at hh ⊢
      nlinarith [hWfh, hUheight, hh]
  have hIHg : index (fun _ : Fin 1 ↦ ((p * d 0 : ℕ) : ℝ)) (fun _ ↦ ξ 0) Wg
      ≤ ENNReal.ofReal s := by
    refine index_le_base hWg0 (Nat.mul_pos hp0 (hd1 0)) hWgdeg (fun _ ↦ ξ 0) hs0 ?_
    have hh := mul_le_mul_of_nonneg_left (hheight 0) hpr.le
    have hd0M : (d 0 : ℝ) ≤ (d (Fin.last (m + 1)) : ℝ) := by
      rw [← hdr, ← hdr]
      exact hmono (Fin.zero_le _)
    have hmm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    push_cast at hh ⊢
    have hWgU : Wg.logHeight ≤ (p : ℝ) * P.logHeight
        + 4 * (p : ℝ) * (d (Fin.last (m + 1)) : ℝ) * (totalWeight K : ℝ) := by
      nlinarith [hWgh, hUheight]
    have hA : 4 * ((p : ℝ) * (d 0 : ℝ)) * (totalWeight K : ℝ)
        ≤ 4 * ((p : ℝ) * (d (Fin.last (m + 1)) : ℝ)) * (totalWeight K : ℝ) := by
      have h1 : (0 : ℝ) ≤ 4 * (p : ℝ) * (totalWeight K : ℝ) := by positivity
      nlinarith [hd0M, h1]
    have hB : (8 : ℝ) * (p : ℝ) * (d (Fin.last (m + 1)) : ℝ) * (totalWeight K : ℝ)
        ≤ 4 * ((m : ℝ) + 1 + 1) * ((p : ℝ) * (d (Fin.last (m + 1)) : ℝ))
          * (totalWeight K : ℝ) := by
      have h2 : (0 : ℝ) ≤ (p : ℝ) * (d (Fin.last (m + 1)) : ℝ) * (totalWeight K : ℝ) := by
        positivity
      nlinarith [hmm, h2]
    linarith [hWgU, hA, hB, hh]
  have hcastf : (fun j : Fin (m + 1) ↦ ((p * d j.succ : ℕ) : ℝ))
      = fun j : Fin (m + 1) ↦ (p : ℝ) * dr j.succ := by
    funext j
    rw [hdr]
    push_cast
    ring
  have hcastg : (fun _ : Fin 1 ↦ ((p * d 0 : ℕ) : ℝ)) = fun _ : Fin 1 ↦ (p : ℝ) * dr 0 := by
    funext j
    rw [hdr]
    push_cast
    ring
  rw [hcastf] at hIHf
  rw [hcastg] at hIHg
  have hUup : index (fun l ↦ (p : ℝ) * dr l) ξ U
      ≤ ENNReal.ofReal (rothConst m * θ ^ 2 + s) := by
    rw [hUeq, index_mul _ (fun l ↦ mul_nonneg hpr.le (hdrnn l)) ξ,
      index_rename (Fin.succ_injective _), index_rename (lastVar_injective _),
      ENNReal.ofReal_add (mul_nonneg (rothConst_nonneg m) (sq_nonneg θ)) hs0.le]
    exact add_le_add hIHf hIHg
  have hdr0succ : dr 0 ≤ s * dr (Fin.succ 0) := by
    have h := hratio 0
    rw [Fin.castSucc_zero] at h
    rw [hdr, hdr]
    exact h
  have hμbound : ∀ i : Fin p, ((μ i).sum fun l k ↦ (k : ℝ) / dr l.succ) ≤ s := by
    intro i
    have hminw : ∀ l : Fin (m + 1), dr (Fin.succ 0) ≤ dr l.succ := fun l ↦
      hmono (Fin.succ_le_succ_iff.mpr (Fin.zero_le l))
    refine le_trans (Finsupp.sum_div_le_degree_div (μ i) (hdrpos _) hminw) ?_
    rw [div_le_iff₀ (hdrpos _)]
    have h1 : (((μ i).degree : ℕ) : ℝ) ≤ ((i : ℕ) : ℝ) := by exact_mod_cast hμord i
    have hi : ((i : ℕ) : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast i.isLt
    have h2 : (p : ℝ) ≤ dr 0 + 1 := by
      rw [hdr]
      exact_mod_cast hple'
    linarith [hdr0succ]
  have hνbound : ∀ j : Fin p, ((ν j).sum fun _ k ↦ (k : ℝ) / dr 0) ≤ ((j : ℕ) : ℝ) / dr 0 := by
    intro j
    refine le_trans (Finsupp.sum_div_le_degree_div (ν j) (hdrpos 0) fun _ ↦ le_refl _) ?_
    have h1 : (((ν j).degree : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hνord j
    gcongr
    exact hdrnn 0
  have hweight : ∀ i j : Fin p,
      (((μ i).mapDomain Fin.succ + (ν j).mapDomain (lastVar (m + 1))).sum
          fun l k ↦ (k : ℝ) / dr l)
        ≤ s + ((j : ℕ) : ℝ) / dr 0 := by
    intro i j
    rw [Finsupp.sum_add_index' (fun l ↦ by simp) (fun l k₁ k₂ ↦ by push_cast; ring),
      sum_mapDomain_div (Fin.succ_injective _), sum_mapDomain_div (lastVar_injective _)]
    exact add_le_add (hμbound i) (hνbound j)
  have hentry : ∀ i j : Fin p,
      index dr ξ P - ENNReal.ofReal (s + ((j : ℕ) : ℝ) / dr 0)
        ≤ index dr ξ (hasseDerivMatrix μ ν P i j) := by
    intro i j
    rw [tsub_le_iff_right, hasseDerivMatrix_apply]
    exact le_trans (index_le_hasseDeriv_add dr hdrnn ξ P
        ((μ i).mapDomain Fin.succ + (ν j).mapDomain (lastVar (m + 1))))
      (add_le_add le_rfl (ENNReal.ofReal_le_ofReal (hweight i j)))
  have hlow : ∑ j : Fin p, (index dr ξ P - ENNReal.ofReal (s + ((j : ℕ) : ℝ) / dr 0))
      ≤ index dr ξ U := by
    rw [hUd]
    exact le_index_det dr hdrnn ξ _ hentry
  have hSum : ∑ j : Fin p, (index dr ξ P - ENNReal.ofReal (s + ((j : ℕ) : ℝ) / dr 0))
      = ENNReal.ofReal (∑ j : Fin p, max 0 (t - s - ((j : ℕ) : ℝ) / dr 0)) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun j _ ↦ le_max_left _ _]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hnn : (0 : ℝ) ≤ s + ((j : ℕ) : ℝ) / dr 0 :=
      add_nonneg hs0.le (div_nonneg (Nat.cast_nonneg _) (hdrnn 0))
    have hcg : t - (s + ((j : ℕ) : ℝ) / dr 0) = t - s - ((j : ℕ) : ℝ) / dr 0 := by ring
    rw [hTeq, ← ENNReal.ofReal_sub _ hnn, hcg]
    rcases le_or_gt 0 (t - s - ((j : ℕ) : ℝ) / dr 0) with hge | hlt
    · rw [max_eq_right hge]
    · rw [max_eq_left hlt.le, ENNReal.ofReal_of_nonpos hlt.le, ENNReal.ofReal_zero]
  have hcomb : (p : ℝ)⁻¹ * (∑ j : Fin p, max 0 (t - s - ((j : ℕ) : ℝ) / dr 0))
      ≤ rothConst m * θ ^ 2 + s := by
    have h1 : ENNReal.ofReal ((p : ℝ)⁻¹)
        * ENNReal.ofReal (∑ j : Fin p, max 0 (t - s - ((j : ℕ) : ℝ) / dr 0))
        ≤ ENNReal.ofReal (rothConst m * θ ^ 2 + s) := by
      calc ENNReal.ofReal ((p : ℝ)⁻¹)
            * ENNReal.ofReal (∑ j : Fin p, max 0 (t - s - ((j : ℕ) : ℝ) / dr 0))
          ≤ ENNReal.ofReal ((p : ℝ)⁻¹) * index dr ξ U := by
            gcongr
            exact hSum ▸ hlow
        _ = index (fun l ↦ (p : ℝ) * dr l) ξ U :=
            (index_const_mul_weights dr hpr hdrnn ξ U).symm
        _ ≤ ENNReal.ofReal (rothConst m * θ ^ 2 + s) := hUup
    rw [← ENNReal.ofReal_mul (by positivity)] at h1
    refine (ENNReal.ofReal_le_ofReal_iff ?_).mp h1
    exact add_nonneg (mul_nonneg (rothConst_nonneg m) (sq_nonneg θ)) hs0.le
  have hrc : rothConst (m + 1) * θ = 2 * ((m : ℝ) + 2) * θ := by
    rw [rothConst_succ]
  rw [hrc] at htlb
  have hts : (0 : ℝ) ≤ t - s := by
    have h2 : θ ^ 2 < θ := by nlinarith
    have hmm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    nlinarith [htlb, hsθ2, hθ0]
  have hS : (p : ℝ) * min ((t - s) / 2) ((t - s) ^ 2 / 4)
      ≤ ∑ j : Fin p, max 0 (t - s - ((j : ℕ) : ℝ) / dr 0) := by
    have heq : ∑ j : Fin p, max 0 (t - s - ((j : ℕ) : ℝ) / dr 0)
        = ∑ j ∈ Finset.range p, max 0 (t - s - (j : ℝ) / ((d 0 : ℕ) : ℝ)) := by
      rw [← Fin.sum_univ_eq_sum_range (fun j ↦ max 0 (t - s - (j : ℝ) / ((d 0 : ℕ) : ℝ))) p]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [hdr]
    rw [heq]
    exact Real.le_sum_max_sub_div hp0 hple' (hd1 0) hts
  have hmin : min ((t - s) / 2) ((t - s) ^ 2 / 4) ≤ rothConst m * θ ^ 2 + s := by
    refine le_of_mul_le_mul_left ?_ hpr
    refine le_trans hS ?_
    have h := mul_le_mul_of_nonneg_left hcomb hpr.le
    rw [← mul_assoc, mul_inv_cancel₀ hpr.ne', one_mul] at h
    exact h
  exact Real.roth_numeric (Nat.cast_nonneg m) hθ0 hsmall hsθ2 rfl (rothConst_le m) htlb hmin


theorem rothConst_le_two_mul (m : ℕ) : rothConst m ≤ 2 * ((m : ℝ) + 1) :=
  le_of_eq (by rw [rothConst])

/-- **Roth's lemma, in the normalization of the induction**: the separated variable is `X 0`, the
degrees increase, and the parameter is `θ` with `σ = θ ^ (2 ^ m)`. -/
theorem rothProp_of (m : ℕ) : RothProp K m := by
  induction m with
  | zero => exact rothProp_zero
  | succ m ih => exact rothProp_succ ih

/-- **Roth's lemma** (Bombieri–Gubler, Lemma 6.3.7). For a nonzero polynomial in `m + 1`
variables over a number field whose partial degrees are bounded by `d`, whose degrees drop by a
factor at least `σ ≤ 1 / 2` at every step, and whose point `ξ` has coordinates high enough
against the height of `P`, the index is at most `2 (m + 1) σ ^ ((1 / 2) ^ m)`.

Heights are the relative ones of Mathlib, so the constant term `4 (m + 1) d 0` of the hypothesis
carries the factor `totalWeight K`; dividing every height by `totalWeight K = [K : ℚ]` gives the
statement in absolute logarithmic heights. -/
theorem index_le_of_degree_ratio {m : ℕ} {d : Fin (m + 1) → ℕ} (hd1 : ∀ j, 1 ≤ d j)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1 / 2)
    (hratio : ∀ j : Fin m, (d j.succ : ℝ) ≤ σ * d j.castSucc)
    {P : MvPolynomial (Fin (m + 1)) K} (hP : P ≠ 0) (hdeg : ∀ j, P.degreeOf j ≤ d j)
    (ξ : Fin (m + 1) → K)
    (hheight : ∀ j, P.logHeight + 4 * (m + 1) * d 0 * totalWeight K
        ≤ σ * (d j * logHeight₁ (ξ j))) :
    index (fun j ↦ (d j : ℝ)) ξ P
      ≤ ENNReal.ofReal (2 * ((m : ℝ) + 1) * σ ^ ((1 / 2 : ℝ) ^ m)) := by
  set θ : ℝ := σ ^ ((1 / 2 : ℝ) ^ m) with hθdef
  have hθ0 : 0 < θ := Real.rpow_pos_of_pos hσ0 _
  have hθpow : θ ^ 2 ^ m = σ := by
    rw [hθdef, ← Real.rpow_natCast (σ ^ ((1 / 2 : ℝ) ^ m)) (2 ^ m), ← Real.rpow_mul hσ0.le]
    rw [show ((1 / 2 : ℝ) ^ m) * ((2 ^ m : ℕ) : ℝ) = 1 by
      push_cast
      rw [div_pow, one_pow, div_mul_cancel₀]
      positivity]
    exact Real.rpow_one σ
  have hkey := rothProp_of (K := K) m θ hθ0 (by rw [hθpow]; exact hσ1)
    (fun j ↦ d j.rev) (fun j ↦ hd1 _) (fun j ↦ ?_) (rename Fin.rev P)
    (fun h ↦ hP (rename_injective _ Fin.rev_injective (by rw [h, map_zero]))) (fun j ↦ ?_)
    (fun j ↦ ξ j.rev) (fun j ↦ ?_)
  · rw [index_rename Fin.rev_injective] at hkey
    simp only [Fin.rev_rev] at hkey
    refine le_trans hkey (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (rothConst_le_two_mul m) hθ0.le
  · rw [hθpow]
    have h := hratio j.rev
    rw [← Fin.rev_castSucc, ← Fin.rev_succ] at h
    exact h
  · have h := hdeg j.rev
    have h2 : (rename Fin.rev P).degreeOf j = P.degreeOf j.rev := by
      have := degreeOf_rename_of_injective (p := P) Fin.rev_injective j.rev
      rwa [Fin.rev_rev] at this
    rw [h2]
    exact h
  · rw [hθpow, Fin.rev_last, logHeight_rename_of_injective Fin.rev_injective]
    exact hheight j.rev

/-! ### Acceptance criteria -/

section Acceptance

/-- **Acceptance test: in one variable the lemma reads `index ≤ 2 σ`.** The exponent
`(1 / 2) ^ 0` is `1`, so the conclusion is linear in `σ` and the lemma is Bombieri–Gubler's
Lemma 6.3.9 at a worse constant. -/
example {d : Fin 1 → ℕ} (hd1 : ∀ j, 1 ≤ d j) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1 / 2)
    {P : MvPolynomial (Fin 1) K} (hP : P ≠ 0) (hdeg : ∀ j, P.degreeOf j ≤ d j) (ξ : Fin 1 → K)
    (hheight : ∀ j, P.logHeight + 4 * (((0 : ℕ) : ℝ) + 1) * (d 0 : ℝ) * (totalWeight K : ℝ)
        ≤ σ * ((d j : ℝ) * logHeight₁ (ξ j))) :
    index (fun j ↦ (d j : ℝ)) ξ P ≤ ENNReal.ofReal (2 * σ) := by
  simpa using index_le_of_degree_ratio hd1 hσ0 hσ1 (fun j ↦ j.elim0) hP hdeg ξ hheight

/-- **Acceptance test: in two variables the exponent is a square root.** This is the case that
fixes the shape of the induction: the quadratic lower bound on the index of the determinant
turns `σ` into `√σ`, and every further variable squares the exponent again. -/
example {d : Fin 2 → ℕ} (hd1 : ∀ j, 1 ≤ d j) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1 / 2)
    (hratio : ∀ j : Fin 1, (d j.succ : ℝ) ≤ σ * (d j.castSucc : ℝ))
    {P : MvPolynomial (Fin 2) K} (hP : P ≠ 0) (hdeg : ∀ j, P.degreeOf j ≤ d j) (ξ : Fin 2 → K)
    (hheight : ∀ j, P.logHeight + 4 * (((1 : ℕ) : ℝ) + 1) * (d 0 : ℝ) * (totalWeight K : ℝ)
        ≤ σ * ((d j : ℝ) * logHeight₁ (ξ j))) :
    index (fun j ↦ (d j : ℝ)) ξ P ≤ ENNReal.ofReal (4 * Real.sqrt σ) := by
  refine le_trans (index_le_of_degree_ratio hd1 hσ0 hσ1 hratio hP hdeg ξ hheight)
    (le_of_eq (congrArg ENNReal.ofReal ?_))
  rw [Real.sqrt_eq_rpow]
  norm_num

/-- **Rejection test: the closing inequality needs `θ < 1/2`.** At `θ = 1` every other hypothesis
of `Real.roth_numeric` holds and there is no contradiction, so the reduction to small `θ` — free
because the index of a polynomial of partial degrees at most `d` is at most the number of
variables — is what the uniform constant `2 m` rests on. -/
example : (0 : ℝ) ≤ 0 ∧ (0 : ℝ) < 1 ∧ (1 : ℝ) ≤ (1 : ℝ) ^ 2 ∧ (3.5 : ℝ) = 4.5 - 1
    ∧ (2 : ℝ) ≤ 2 * 0 + 2 ∧ 2 * ((0 : ℝ) + 2) * 1 < 4.5
    ∧ min ((3.5 : ℝ) / 2) ((3.5 : ℝ) ^ 2 / 4) ≤ 2 * (1 : ℝ) ^ 2 + 1 := by
  norm_num

/-- **Rejection test: the `min` of `Real.le_sum_max_sub_div` is not decoration.** With `p = 3`,
`e = 2` and `x = 1/2` the sum is `1/2`, which is *less* than the linear half `p x / 2 = 3/4`;
only the quadratic half `p x ^ 2 / 4 = 3/16` survives. -/
example :
    (∑ i ∈ Finset.range 3, max 0 ((1 : ℝ) / 2 - (i : ℕ) / (2 : ℝ)) < 3 * ((1 : ℝ) / 2) / 2)
      ∧ 3 * ((1 : ℝ) / 2) ^ 2 / 4
          ≤ ∑ i ∈ Finset.range 3, max 0 ((1 : ℝ) / 2 - (i : ℕ) / (2 : ℝ)) := by
  norm_num [Finset.sum_range_succ]

end Acceptance

end MvPolynomial
