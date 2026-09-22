/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.AuxiliaryPolynomial
public import DiophantineApproximation.HeightTransport
public import DiophantineApproximation.MvPolynomialEvalBound
public import DiophantineApproximation.RothLemma

/-!
# Steps I and II of Roth's proof

Step I is Layer 2.6: for `m + 1` variables, `|S|` target points and a multidegree `d` with every
`d j` large, the index theorem produces a nonzero `P` over `K` with `degreeOf j P ≤ d j`, with
index at least `(1/2 − ε)(m + 1)` at every target point, and with
`h(P) ≤ [K : ℚ] ∑ j, C₁ j d j`. In Roth's theorem the target points are the diagonals
`(α v, …, α v)`; with moving targets (Layer 3.8) the `j`-th coordinate is the target of `β j`. The
feasibility hypothesis is Lemma 6.3.5, `V_{m+1}((1/2 − ε)(m + 1)) ≤ exp (−6 (m + 1) ε²)`, and it
is what fixes the number of variables: `r |S| exp (−6 (m + 1) ε²) < 1/2`.

Step II is Layer 2.7: `P` may well vanish at `β`, and Roth's lemma says it cannot vanish *much* —
the index of `P` at `β` is at most `2 (m + 1) σ ^ (1/2)^m`, which is `2 (m + 1) ε` at
`σ = ε ^ 2^m`. So some Hasse derivative `∂_μ P` with `∑ j, μ j / d j < 3 (m + 1) ε` survives at
`β`; that derivative is the `Q` the rest of the proof works with. Differentiating costs
`(1/2 − ε)(m + 1) − 3 (m + 1) ε = (1/2 − 4ε)(m + 1)` in the index at the targets and a factor
`2 ^ (∑ j, d j)` in the height, which is the whole of Lemma 6.4.7.

## Main results

* `NumberField.exists_auxiliary_deriv`: **Steps I and II** (Bombieri–Gubler 6.4.5–6.4.7), with the
  three conclusions Step III consumes — `Q(β) ≠ 0`, the index at every target, and the height.

## Implementation notes

⚠ **The `D₀` of the index theorem is existential and comes first.** It depends on `ε`, on the
number of variables and on the targets, but on nothing that is chosen later; so the statement is
`∃ D₀, ∀ d ≥ D₀, …` and the caller picks `D` large enough afterwards. The largeness conditions on
`d` that Roth's lemma needs — the ratios and the height — are hypotheses, because they involve the
heights of the `β j` and those are not known here.

⚠ **The index of `Q` at a target is `(1/2 − 4ε)(m + 1)`, not the book's `(1/2 − 3ε)(m + 1)`.**
Roth's lemma is quoted through the infimum, so a strict inequality is needed to produce an order,
and `2 (m + 1) ε < 3 (m + 1) ε` is the cheapest one. Since `ε` is at the caller's disposal the
constant is immaterial, and nothing downstream sees it.

⚠ **The height bound is `[K : ℚ] ∑ j, (C₁ j + log 2) d j`, with `C₁` a hypothesis.** The index
theorem's constant is `r / (1 − r ∑ V)` times a sum of volumes; under the feasibility hypothesis
the first factor is at most `2r` and the volumes sum to less than `1 / (2r)`, so the two cancel and
only the heights of the targets survive. That cancellation is why `m` may be taken as large as the
feasibility demands without the height of `P` growing with it.

⚠ **`C₁` is indexed by the coordinate, and that is the whole of Layer 3.8's change here.** The
heights of the targets enter `h(P)` as `∑ j, h(α j) d j`, the book's (6.11): the target of `β j`
is weighed by `d j ≈ D / h(β j)`. With one constant for all coordinates the bound is
`C₁ ∑ j, d j = O(D / L)`; with moving targets it is `∑ j, C₁ j d j`, which is `o(D)` exactly when
`h(α j) = o(h(β j))`.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
§6.4.5 to §6.4.7.

This is part of Layer 3.2 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Height MeasureTheory MvPolynomial Module

namespace NumberField

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]

/-- **Steps I and II of Roth's proof** (Bombieri–Gubler 6.4.5–6.4.7): the auxiliary polynomial of
Layer 2.6, differentiated until it survives at `β` by Layer 2.7. The index is taken at the point
`tgt a` for every `a`, and `C₁ j` bounds the heights of the `j`-th coordinates of those points; in
Roth's theorem the points are diagonal and `C₁` is constant, and in Layer 3.8 they are not. -/
theorem exists_auxiliary_deriv {A : Type*} [Fintype A] {m : ℕ} (tgt : A → Fin (m + 1) → F)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (hfeas : (finrank K F : ℝ) * (Fintype.card A : ℝ)
      * Real.exp (-(6 * ((m : ℝ) + 1) * ε ^ 2)) < 1 / 2)
    {C₁ : Fin (m + 1) → ℝ} (hC₁0 : ∀ j, 0 ≤ C₁ j)
    (hC₁ : ∀ a j, absLogHeight₁ (tgt a j) + Real.log 2 + 1 ≤ C₁ j) :
    ∃ D₀ : ℕ, ∀ d : Fin (m + 1) → ℕ, (∀ j, D₀ ≤ d j) → ∀ β : Fin (m + 1) → K,
      (∀ j : Fin m, (d j.succ : ℝ) ≤ ε ^ (2 ^ m) * (d j.castSucc : ℝ)) →
      (∀ j, (totalWeight K : ℝ) * ∑ i, C₁ i * (d i : ℝ)
            + 4 * ((m : ℝ) + 1) * (d 0 : ℝ) * (totalWeight K : ℝ)
          ≤ ε ^ (2 ^ m) * ((d j : ℝ) * logHeight₁ (β j))) →
      ∃ Q : MvPolynomial (Fin (m + 1)) K, eval β Q ≠ 0 ∧ (∀ j, Q.degreeOf j ≤ d j) ∧
        (∀ a, ENNReal.ofReal ((1 / 2 - 4 * ε) * ((m : ℝ) + 1))
          ≤ index (fun j ↦ (d j : ℝ)) (tgt a) (Q.map (algebraMap K F))) ∧
        Real.log Q.mulHeight ≤ (totalWeight K : ℝ) * ∑ i, (C₁ i + Real.log 2) * (d i : ℝ) := by
  classical
  have hr0 : (0 : ℝ) ≤ (finrank K F : ℝ) := Nat.cast_nonneg _
  set e := (Fintype.equivFin A).symm with hedef
  set V : ℝ := cubeSimplexVolume (m + 1) ((1 / 2 - ε) * ((m + 1 : ℕ) : ℝ)) with hVdef
  have hV0 : (0 : ℝ) ≤ V := cubeSimplexVolume_nonneg _ _
  have hVexp : V ≤ Real.exp (-(6 * ((m : ℝ) + 1) * ε ^ 2)) := by
    have h := cubeSimplexVolume_le_exp_neg (m + 1) hε0.le
    rw [hVdef]
    push_cast at h ⊢
    exact h
  have hsumV : (∑ _k : Fin (Fintype.card A), V) = (Fintype.card A : ℝ) * V := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  have hfeas2 : (finrank K F : ℝ) * (∑ _k : Fin (Fintype.card A), V) < 1 / 2 := by
    rw [hsumV]
    calc (finrank K F : ℝ) * ((Fintype.card A : ℝ) * V)
        ≤ (finrank K F : ℝ) * ((Fintype.card A : ℝ)
            * Real.exp (-(6 * ((m : ℝ) + 1) * ε ^ 2))) := by gcongr
      _ = (finrank K F : ℝ) * (Fintype.card A : ℝ)
            * Real.exp (-(6 * ((m : ℝ) + 1) * ε ^ 2)) := by ring
      _ < 1 / 2 := hfeas
  obtain ⟨D₀, hD₀⟩ := MvPolynomial.exists_ne_zero_le_index_logHeight_le (K := K) (F := F)
    (α := fun k : Fin (Fintype.card A) ↦ tgt (e k))
    (t := fun _ : Fin (Fintype.card A) ↦ (1 / 2 - ε) * ((m + 1 : ℕ) : ℝ))
    (fun _ ↦ by positivity) (by rw [← hVdef]; linarith) (δ := 1) one_pos
  refine ⟨max D₀ 1, fun d hd β hratio hheight ↦ ?_⟩
  have hd1 : ∀ j, 1 ≤ d j := fun j ↦ le_trans (le_max_right D₀ 1) (hd j)
  obtain ⟨P, hP0, hPdeg, hPindex, hPheight⟩ := hD₀ d fun j ↦ le_trans (le_max_left D₀ 1) (hd j)
  rw [← hVdef] at hPheight
  -- the height of the auxiliary polynomial
  have hCd0 : (0 : ℝ) ≤ ∑ i, C₁ i * (d i : ℝ) :=
    Finset.sum_nonneg fun i _ ↦ mul_nonneg (hC₁0 i) (Nat.cast_nonneg _)
  have hPh : Real.log P.mulHeight ≤ (totalWeight K : ℝ) * ∑ i, C₁ i * (d i : ℝ) := by
    have hstep1 : (∑ k : Fin (Fintype.card A), ∑ j : Fin (m + 1),
          V * (absLogHeight₁ (tgt (e k) j) + Real.log 2 + 1) * (d j : ℝ))
        ≤ ((Fintype.card A : ℝ) * V) * ∑ i, C₁ i * (d i : ℝ) := by
      calc (∑ k : Fin (Fintype.card A), ∑ j : Fin (m + 1),
            V * (absLogHeight₁ (tgt (e k) j) + Real.log 2 + 1) * (d j : ℝ))
          ≤ ∑ _k : Fin (Fintype.card A), ∑ j : Fin (m + 1), V * (C₁ j * (d j : ℝ)) := by
            refine Finset.sum_le_sum fun k _ ↦ Finset.sum_le_sum fun j _ ↦ ?_
            rw [← mul_assoc]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hC₁ (e k) j) hV0) (Nat.cast_nonneg _)
        _ = ∑ _k : Fin (Fintype.card A), V * ∑ j : Fin (m + 1), C₁ j * (d j : ℝ) :=
            Finset.sum_congr rfl fun k _ ↦ (Finset.mul_sum _ _ _).symm
        _ = ((Fintype.card A : ℝ) * V) * ∑ i, C₁ i * (d i : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
            ring
    have hcoef : (finrank K F : ℝ)
        / (1 - (finrank K F : ℝ) * ∑ _k : Fin (Fintype.card A), V)
        ≤ 2 * (finrank K F : ℝ) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have hstep2 : (finrank K F : ℝ)
        / (1 - (finrank K F : ℝ) * ∑ _k : Fin (Fintype.card A), V)
        * (∑ k : Fin (Fintype.card A), ∑ j : Fin (m + 1),
            V * (absLogHeight₁ (tgt (e k) j) + Real.log 2 + 1) * (d j : ℝ))
        ≤ ∑ i, C₁ i * (d i : ℝ) := by
      calc (finrank K F : ℝ) / (1 - (finrank K F : ℝ) * ∑ _k : Fin (Fintype.card A), V)
            * (∑ k : Fin (Fintype.card A), ∑ j : Fin (m + 1),
              V * (absLogHeight₁ (tgt (e k) j) + Real.log 2 + 1) * (d j : ℝ))
          ≤ (2 * (finrank K F : ℝ)) * (((Fintype.card A : ℝ) * V) * ∑ i, C₁ i * (d i : ℝ)) := by
            refine mul_le_mul hcoef hstep1 ?_ (by positivity)
            refine Finset.sum_nonneg fun k _ ↦ Finset.sum_nonneg fun j _ ↦ ?_
            have h3 : (0 : ℝ) ≤ absLogHeight₁ (tgt (e k) j) := absLogHeight₁_nonneg _
            have h4 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
            exact mul_nonneg (mul_nonneg hV0 (by linarith)) (Nat.cast_nonneg _)
        _ = (2 * ((finrank K F : ℝ) * ((Fintype.card A : ℝ) * V))) * ∑ i, C₁ i * (d i : ℝ) := by
            ring
        _ ≤ 1 * ∑ i, C₁ i * (d i : ℝ) := by
            refine mul_le_mul_of_nonneg_right ?_ hCd0
            rw [← hsumV]
            linarith
        _ = ∑ i, C₁ i * (d i : ℝ) := one_mul _
    have hfr : (0 : ℝ) < (finrank ℚ K : ℝ) := by
      exact_mod_cast Module.finrank_pos
    rw [div_le_iff₀ hfr] at hPheight
    calc Real.log P.mulHeight ≤ _ * (finrank ℚ K : ℝ) := hPheight
      _ ≤ (∑ i, C₁ i * (d i : ℝ)) * (finrank ℚ K : ℝ) :=
          mul_le_mul_of_nonneg_right hstep2 hfr.le
      _ = (totalWeight K : ℝ) * ∑ i, C₁ i * (d i : ℝ) := by
          rw [totalWeight_eq_finrank]
          ring
  -- Roth's lemma
  have hσ0 : (0 : ℝ) < ε ^ 2 ^ m := pow_pos hε0 _
  have hσ1 : ε ^ 2 ^ m ≤ 1 / 2 := by
    calc ε ^ 2 ^ m ≤ ε ^ 1 :=
          pow_le_pow_of_le_one hε0.le (by linarith) Nat.one_le_two_pow
      _ = ε := pow_one _
      _ ≤ 1 / 2 := hε1.le
  have hPidx := MvPolynomial.index_le_of_degree_ratio hd1 hσ0 hσ1 hratio hP0 hPdeg β
    (fun j ↦ by
      rw [MvPolynomial.logHeight_eq_log_mulHeight]
      have := hheight j
      linarith)
  have hexpid : (ε ^ 2 ^ m : ℝ) ^ ((1 / 2 : ℝ) ^ m) = ε := by
    have h2 : (((2 ^ m : ℕ) : ℝ)) * ((1 / 2 : ℝ) ^ m) = 1 := by
      push_cast
      rw [← mul_pow]
      norm_num
    rw [← Real.rpow_natCast ε (2 ^ m), ← Real.rpow_mul hε0.le, h2, Real.rpow_one]
  rw [hexpid] at hPidx
  -- a derivative that survives at `β`
  have hexμ : ∃ μ : Fin (m + 1) →₀ ℕ, eval β (hasseDeriv μ P) ≠ 0 ∧
      (μ.sum fun j k ↦ (k : ℝ) / d j) < 3 * ((m : ℝ) + 1) * ε := by
    by_contra hcon
    push Not at hcon
    have hge := MvPolynomial.le_index (fun j ↦ (d j : ℝ)) (α := β) (P := P)
      (c := ENNReal.ofReal (3 * ((m : ℝ) + 1) * ε))
      fun μ hμ ↦ ENNReal.ofReal_le_ofReal (hcon μ hμ)
    have h2 := le_trans hge hPidx
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
    nlinarith
  obtain ⟨μ, hμne, hμw⟩ := hexμ
  have hμw0 : (0 : ℝ) ≤ μ.sum fun j k ↦ (k : ℝ) / d j :=
    Finset.sum_nonneg fun j _ ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  refine ⟨hasseDeriv μ P, hμne, fun j ↦ ?_, fun a ↦ ?_, ?_⟩
  · exact le_trans (le_trans (degreeOf_hasseDeriv_le μ P j) (Nat.sub_le _ _)) (hPdeg j)
  · -- the index at the target drops by at most the weight of `μ`
    have hmap : (hasseDeriv μ P).map (algebraMap K F) = hasseDeriv μ (P.map (algebraMap K F)) :=
      map_hasseDeriv _ μ P
    have hPa : ENNReal.ofReal ((1 / 2 - ε) * ((m + 1 : ℕ) : ℝ))
        ≤ index (fun j ↦ (d j : ℝ)) (tgt a) (P.map (algebraMap K F)) := by
      have h := hPindex (e.symm a)
      rwa [Equiv.apply_symm_apply] at h
    have hdrop := MvPolynomial.index_le_hasseDeriv_add (fun j ↦ (d j : ℝ))
      (fun j ↦ Nat.cast_nonneg _) (tgt a) (P.map (algebraMap K F)) μ
    rw [hmap]
    have hchain : ENNReal.ofReal ((1 / 2 - ε) * ((m + 1 : ℕ) : ℝ))
        ≤ index (fun j ↦ (d j : ℝ)) (tgt a) (hasseDeriv μ (P.map (algebraMap K F)))
          + ENNReal.ofReal (μ.sum fun j k ↦ (k : ℝ) / d j) := le_trans hPa hdrop
    rw [← tsub_le_iff_right, ← ENNReal.ofReal_sub _ hμw0] at hchain
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hchain
    push_cast
    nlinarith
  · -- the height of the derivative
    have hCle : (1 : ℝ) ≤ 2 ^ ∑ i, d i := one_le_pow₀ (by norm_num)
    have hQle : (hasseDeriv μ P).mulHeight
        ≤ (2 ^ ∑ i, d i : ℝ) ^ totalWeight K * P.mulHeight ^ 1 := by
      refine MvPolynomial.mulHeight_le_pow_of_forall_iSup_le hP0 hCle (fun v _ ↦ ?_) fun v hv ↦ ?_
      · rw [pow_one]
        refine le_trans (iSup_coeff_hasseDeriv_le v μ P) ?_
        refine mul_le_mul_of_nonneg_right ?_ (Real.iSup_nonneg fun _ ↦ v.nonneg _)
        exact pow_le_pow_right₀ one_le_two (totalDegree_le_sum hPdeg)
      · rw [pow_one]
        exact iSup_coeff_hasseDeriv_le_of_isNonarchimedean
          (AdmissibleAbsValues.isNonarchimedean v hv) μ P
    rw [pow_one] at hQle
    have hlog := Real.log_le_log (MvPolynomial.mulHeight_pos _) hQle
    rw [Real.log_mul (by positivity) (MvPolynomial.mulHeight_pos P).ne', ← Real.rpow_natCast
      ((2 : ℝ) ^ ∑ i, d i) (totalWeight K), Real.log_rpow (by positivity), Real.log_pow] at hlog
    have hcast : ((∑ i, d i : ℕ) : ℝ) = ∑ i, (d i : ℝ) := by push_cast; ring
    rw [hcast] at hlog
    have hsplit : ∑ i, (C₁ i + Real.log 2) * (d i : ℝ)
        = ∑ i, C₁ i * (d i : ℝ) + Real.log 2 * ∑ i, (d i : ℝ) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hsplit]
    rw [totalWeight_eq_finrank] at hPh hlog ⊢
    nlinarith [hlog, hPh]

end NumberField

end
