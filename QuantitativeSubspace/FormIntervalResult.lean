/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.FormSemistableGap

-- Used only inside proofs.
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The interval result

J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative Subspace Theorem*,
Ann. of Math. **177** (2013), 513–590, Prop. 18.5 and Theorem 2.3.

Let `T = T(L, c)` be the destabilizing subspace (EF13 (2.21)), `k = dim T`, `m = n - k`. Q3.5's
quotient system `L''` on `Ωⁿ / T`, with the normalized exponents `d` of EF13 (18.12)
(`quotNormExp`), satisfies (8.3), (8.4) and (8.9) (Q3.7). A point `x ∉ T` with
`H_{L,c,Q}(x) ≤ Δ_L^{1/n} Q^{-δ}` gives the nonzero point `φ'' x` with
`H_{L'',d,Q'}(φ'' x) ≤ Q'^{-δ/2n}`, `Q' = Q^{n/m}` (Prop. 18.5). For `m ≥ 2`, Theorem 8.1 for
`(L'', d)` puts `Q'` into finitely many intervals; for `m = 1`, `d = 0` and the height on the
quotient is bounded below (EF13 Lemma 7.1), so `Q` is small. Finally the intervals and the range
between `C₀ = max(H_L^{1/R}, n^{1/δ})` and the threshold are cut into intervals `[b, b^{ω₀})`,
`ω₀ = δ⁻¹ log 3R`.

## Main results

* `NumberField.FormSystem.mulRatioProd_minorSet_rpow_le_of_isDestabilizing`,
  `absFormHeight_quotSystem_le_of_isDestabilizing`: EF13 Lemmas 18.1 and 18.4 for `T(L, c)`,
  including `T = 0`.
* `NumberField.FormSystem.absMulHeight_quotNormExp_le_rpow`: EF13 Prop. 18.5.
* `NumberField.FormSystem.isNormalSemistable_comp`, `exists_intervals_of_fin_eq_zero`: (8.8) is
  no restriction (EF13 Lemma 7.3), so Theorem 8.1 needs only `d_{v₀} = 0` at one finite place.
* `NumberField.FormSystem.false_of_card_eq_one`: the case `n - k = 1`.
* `NumberField.FormSystem.exists_intervals_of_isDestabilizing`: EF13 (18.23).
* `Real.exists_cut`: an interval `[a, a^θ]` is covered by `⌊log θ / log ω⌋ + 1` intervals
  `[b, b^ω)`.
* `NumberField.FormSystem.exists_intervals_cover`: **EF13 Theorem 2.3**.

## Implementation notes

* Hypotheses: `Σ_v Σ_i c_iv = 0` instead of EF13's (2.8) at every place, and (2.9).
* Prop. 18.5 has `Q'^{-δ/2n}` instead of EF13's `Q'^{-99δ/100n}`; Theorem 8.1 is applied with
  `δ / 2n` and `Rⁿ` forms (EF13: `99δ/100n` and `n Rⁿ`, Q3.7 gives `R^{k+1}`).
* EF13 (18.20) `Σ_v θ_v < 0` is used as `≤ 0`, which holds also for `T = 0`.
* The count `intervalCount n R δ` and the threshold `quotThreshold n R δ (log H_L)` are explicit
  but are not EF13's `m₀` and `C₂'`. The count takes the largest over the possible `n - k` of
  the cut intervals of Theorem 8.1, and bounds `log C / log C₀` by `intervalBound n R δ`, using
  `log C₀ ≥ log 2 / δ` and `log C₀ ≥ log H_L / R`.

This is milestone Q4.1e of `QuantitativeSubspace/README.md`.
-/

@[expose] public section

open Finset Module Matrix

namespace NumberField.FormSystem

variable {K : Type} [Field K] [NumberField K] {n k m : ℕ} (L : FormSystem K (Fin n))
  (c : FormExponent K (Fin n))

/-! ### Lemmas 18.1 and 18.4 for the destabilizing subspace -/

section Destabilizing

/-- For `k = 0` the only minor is the empty determinant `1`. -/
theorem minorSet_of_isEmpty (G : Matrix (Fin n) (Fin 0) K) : L.minorSet G = {1} := by
  ext x
  simp only [minorSet, mem_filter, mem_image, mem_singleton]
  constructor
  · rintro ⟨⟨B, -, rfl⟩, -⟩
    exact Matrix.det_isEmpty
  · rintro rfl
    exact ⟨⟨fun i ↦ i.elim0, Fintype.mem_piFinset.2 fun i ↦ i.elim0, Matrix.det_isEmpty⟩,
      one_ne_zero⟩

theorem mulRatioProd_one : mulRatioProd ({1} : Finset K) = 1 := by
  simp [mulRatioProd, localRatio]

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω]
  (S : Splitting K n k m)

/-- **EF13 Lemma 18.1** for the destabilizing subspace `T = T(L, c)`, including `T = 0`. -/
theorem mulRatioProd_minorSet_rpow_le_of_isDestabilizing {T : Submodule Ω (Fin n → Ω)}
    (hT : Submodule.IsDestabilizing (L.subspaceWeight c) ⊤ T)
    (hST : (Submodule.span K (Set.range S.incl.col)).extendPi Ω = T) :
    mulRatioProd (L.minorSet S.incl) ^ ((finrank ℚ K : ℝ))⁻¹ ≤
      (2 * L.absFormHeight) ^ ((4 * #L.forms) ^ n) := by
  obtain ⟨r, F, hF, -⟩ := L.exists_isWeightFiltration_top c (Ω := Ω)
  have hw := L.isSupermodularWeight_subspaceWeight c (Ω := Ω)
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := by
    refine Nat.exists_eq_add_one.2 (Nat.pos_of_ne_zero fun hr ↦ ?_)
    have h0 := hF.zero
    rw [← hr, hF.top] at h0
    exact (bot_le.trans_lt hT.lt).ne' h0
  have hTF : T = F s := hT.unique (hF.isDestabilizing hw)
  have hH : 1 ≤ 2 * L.absFormHeight := by
    have := Real.one_le_rpow L.one_le_mulFormHeight
      (by positivity : (0 : ℝ) ≤ ((finrank ℚ K : ℝ))⁻¹)
    rw [← absFormHeight] at this
    linarith
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · have hk : k = 0 := by
      have h := congrArg (fun U : Submodule Ω (Fin n → Ω) ↦ finrank Ω U)
        (hST.trans (hTF.trans hF.zero))
      rwa [Submodule.finrank_extendPi, finrank_span_eq_card (linearIndependent_incl S),
        Fintype.card_fin, finrank_bot] at h
    subst hk
    rw [minorSet_of_isEmpty, mulRatioProd_one, Real.one_rpow]
    exact one_le_pow₀ hH
  · exact L.mulRatioProd_minorSet_rpow_le (semistableGap K Ω) c hF hs (by omega)
      (linearIndependent_incl S) (hST.trans hTF)

/-- **EF13 Lemma 18.4** for the destabilizing subspace: `H_{L''} ≤ (2 H_L)^{(8R)ⁿ}`. -/
theorem absFormHeight_quotSystem_le_of_isDestabilizing {T : Submodule Ω (Fin n → Ω)}
    (hT : Submodule.IsDestabilizing (L.subspaceWeight c) ⊤ T)
    (hST : (Submodule.span K (Set.range S.incl.col)).extendPi Ω = T) (hm : 0 < m) :
    (L.quotSystem S c).absFormHeight ≤ (2 * L.absFormHeight) ^ ((8 * #L.forms) ^ n) :=
  L.absFormHeight_quotSystem_le_of_ratio S c (by have := S.card_eq; omega)
    (L.mulRatioProd_minorSet_rpow_le_of_isDestabilizing c S hT hST)

/-- **EF13 (18.5)** for the destabilizing subspace:
`H_{L'',c'',Q}(φ'' x) ≤ n (2 H_L)^{(4R)ⁿ} H_{L,c,Q}(x)`. -/
theorem absMulHeight_quotSystem_le_of_isDestabilizing {T : Submodule Ω (Fin n → Ω)}
    (hT : Submodule.IsDestabilizing (L.subspaceWeight c) ⊤ T)
    (hST : (Submodule.span K (Set.range S.incl.col)).extendPi Ω = T) {Q : ℝ} (hQ : 1 ≤ Q)
    (x : Fin n → Ω) :
    (L.quotSystem S c).absMulHeight ((L.quotExp S c).weight (zero_lt_one.trans_le hQ))
        (S.projLin Ω x) ≤
      n * (2 * L.absFormHeight) ^ ((4 * #L.forms) ^ n) *
        L.absMulHeight (c.weight (zero_lt_one.trans_le hQ)) x := by
  refine (L.absMulHeight_quotSystem_le S c hQ x).trans ?_
  gcongr
  · exact L.absMulHeight_nonneg _ _
  · exact L.mulRatioProd_minorSet_rpow_le_of_isDestabilizing c S hT hST

end Destabilizing

/-! ### EF13 Prop. 18.5 -/

section Prop185

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω]
  (S : Splitting K n k m)

omit [NumberField K] [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω] in
/-- `T = ker φ''` when `T` is spanned by the columns of `φ'`. -/
theorem ker_projLin_eq {T : Submodule Ω (Fin n → Ω)}
    (hST : (Submodule.span K (Set.range S.incl.col)).extendPi Ω = T) :
    LinearMap.ker (S.projLin Ω) = T := by
  rw [S.ker_projLin, range_inclLin_eq_extendPi, hST]

/-- **The key estimate of EF13 Prop. 18.5**: with `Q' = Q^{n/m}`, `m = n - dim T`,
`H_{L'',d,Q'}(φ'' x) ≤ n (2 H_L)^{(4R)ⁿ} H_{L,c,Q}(x)` for the normalized exponents `d` of
(18.12), when `Σ_v Σ_i c_iv = 0` (EF13 (2.8)). The factor `Q^{Σ_v θ_v}` of EF13 is at most `1`
because `w(T) ≥ 0` (EF13 (18.20), with `≤` in place of `<`). -/
theorem absMulHeight_quotNormExp_le (hc : c.sum = 0) {T : Submodule Ω (Fin n → Ω)}
    (hT : Submodule.IsDestabilizing (L.subspaceWeight c) ⊤ T)
    (hST : (Submodule.span K (Set.range S.incl.col)).extendPi Ω = T) (hm : 0 < m) {Q : ℝ}
    (hQ : 1 ≤ Q) (x : Fin n → Ω) :
    (L.quotSystem S c).absMulHeight ((L.quotNormExp S c).weight
        (Real.rpow_pos_of_pos (zero_lt_one.trans_le hQ) ((n : ℝ) / m))) (S.projLin Ω x) ≤
      n * (2 * L.absFormHeight) ^ ((4 * #L.forms) ^ n) *
        L.absMulHeight (c.weight (zero_lt_one.trans_le hQ)) x := by
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (by have := S.card_eq; omega)
  set w := L.subspaceWeight (Ω := Ω) c
  rw [quotNormExp, FormExponent.weight_divConst _ (div_pos hn' hm') hQ0,
    absMulHeight_center _ _ hQ0]
  have hsum : (L.quotExp S c).sum = w ⊤ - w T := by
    rw [← subspaceWeight_top (L.quotSystem S c) (L.quotExp S c) (Ω := Ω),
      subspaceWeight_quotSystem, Submodule.comap_top, ker_projLin_eq S hST]
  have htop : w ⊤ = 0 := (subspaceWeight_top L c).trans hc
  -- `w(T) ≥ 0`, since `μ(T, Ωⁿ) ≤ μ(0, Ωⁿ) = 0`
  have hwT : 0 ≤ w T := by
    have h := hT.le ⊥ (bot_le.trans_lt hT.lt)
    have h0 : Submodule.weightSlope w ⊥ ⊤ = 0 := by
      have hbot : w ⊥ = 0 := subspaceWeight_bot L c
      rw [Submodule.weightSlope, htop, hbot, sub_zero, zero_div]
    rw [h0, Submodule.weightSlope_le_iff hT.lt, zero_mul, htop] at h
    linarith
  have hQθ : Q ^ ((L.quotExp S c).sum / m) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hQ (div_nonpos_of_nonpos_of_nonneg
      (by rw [hsum, htop]; linarith) (Nat.cast_nonneg _))
  refine le_trans ?_ (L.absMulHeight_quotSystem_le_of_isDestabilizing c S hT hST hQ x)
  calc _ ≤ 1 * (L.quotSystem S c).absMulHeight ((L.quotExp S c).weight hQ0) (S.projLin Ω x) := by
        gcongr
        exact (L.quotSystem S c).absMulHeight_nonneg _ _
    _ = _ := one_mul _

end Prop185

/-! ### Theorem 8.1 without the normalization (8.8) -/

section Normalize

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (L' : FormSystem K (Fin m))
  (d : FormExponent K (Fin m))

theorem det_inv_fin_ne_zero (v₀ : FinitePlace K) : ((L'.fin v₀)⁻¹).det ≠ 0 :=
  (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.2 (L'.fin_det_ne_zero v₀))).ne_zero

omit [Algebra.IsAlgebraic K Ω] in
/-- **EF13 (8.8) is no restriction**: composing with `(L^{(v₀)})⁻¹` at a finite place `v₀` with
`d_{v₀} = 0` puts `X_1, …, X_m` at `v₀` (EF13 Lemma 7.3). -/
theorem isNormalSemistable_comp (hsa : ∀ v, ∑ i, d.arch v i = 0)
    (hsf : ∀ v, ∑ i, d.fin v i = 0) (hsup : (∑ v, ⨆ i, d.arch v i) + ∑ᶠ v, ⨆ i, d.fin v i ≤ 1)
    {v₀ : FinitePlace K} (hv₀ : d.fin v₀ = 0)
    (hU : ∀ U : Submodule Ω (Fin m → Ω), U ≠ ⊤ → L'.subspaceWeight d U ≤ 0) :
    (L'.comp _ (L'.det_inv_fin_ne_zero v₀)).IsNormalSemistable d Ω where
  sum_arch := hsa
  sum_fin := hsf
  sum_iSup_le := hsup
  exists_v₀ := ⟨v₀, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (L'.fin_det_ne_zero v₀)), hv₀⟩
  subspaceWeight_le U hU' := by
    rw [subspaceWeight_comp]
    refine hU _ fun h ↦ hU' ?_
    have := congrArg (Submodule.comap (compEquiv (Ω := Ω) _
      (L'.det_inv_fin_ne_zero v₀)).toLinearMap) h
    rwa [Submodule.comap_map_eq_of_injective (LinearEquiv.injective _), Submodule.comap_top]
      at this

theorem card_forms_comp_le (P : Matrix (Fin m) (Fin m) K) (hP : P.det ≠ 0) :
    #(L'.comp P hP).forms ≤ #L'.forms := by
  classical
  refine (card_le_card fun f hf ↦ ?_).trans (card_image_le (f := fun g ↦ Matrix.vecMul g P))
  obtain ⟨g, hg, rfl⟩ := L'.exists_of_mem_forms_comp P hP hf
  exact mem_image_of_mem _ hg

theorem absFormHeight_comp_le (P : Matrix (Fin m) (Fin m) K) (hP : P.det ≠ 0) :
    (L'.comp P hP).absFormHeight ≤ L'.absFormHeight :=
  Real.rpow_le_rpow ((L'.comp P hP).one_le_mulFormHeight.trans' zero_le_one)
    (L'.mulFormHeight_comp_le P hP) (by positivity)

end Normalize

end NumberField.FormSystem

/-! ### Cutting intervals -/

namespace Real

/-- The number `⌊log θ / log ω⌋ + 1` of intervals `[b, b^ω)` that cover an interval `[a, a^θ]`. -/
noncomputable def cutCount (θ ω : ℝ) : ℕ := ⌊Real.log θ / Real.log ω⌋₊ + 1

theorem cutCount_mono {θ θ' ω : ℝ} (hθ : 0 < θ) (hθθ' : θ ≤ θ') (hω : 1 < ω) :
    cutCount θ ω ≤ cutCount θ' ω := by
  unfold cutCount
  gcongr
  exact (Real.log_pos hω).le

/-- **Cutting an interval** (EF13, end of §18): `[a, a^θ]` is covered by the intervals
`[a^{ω^j}, a^{ω^{j+1}})`, `j < cutCount θ ω`. -/
theorem exists_cut {a θ ω Q : ℝ} (ha : 1 < a) (hω : 1 < ω) (h1 : a ≤ Q) (h2 : Q ≤ a ^ θ) :
    ∃ j < cutCount θ ω, a ^ (ω ^ j) ≤ Q ∧ Q < (a ^ (ω ^ j)) ^ ω := by
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hla : 0 < Real.log a := Real.log_pos ha
  have hlω : 0 < Real.log ω := Real.log_pos hω
  have hQ0 : 0 < Q := ha0.trans_le h1
  set t := Real.log Q / Real.log a
  have hat : a ^ t = Q := by
    rw [Real.rpow_def_of_pos ha0, mul_div_cancel₀ _ hla.ne', Real.exp_log hQ0]
  have ht1 : 1 ≤ t := (one_le_div hla).2 (Real.log_le_log ha0 h1)
  have htθ : t ≤ θ := by
    rw [← hat] at h2
    exact (Real.rpow_le_rpow_left_iff ha).1 h2
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  set j := ⌊Real.log t / Real.log ω⌋₊
  have hlt : 0 ≤ Real.log t / Real.log ω := div_nonneg (Real.log_nonneg ht1) hlω.le
  have hj1 : (j : ℝ) * Real.log ω ≤ Real.log t :=
    (le_div_iff₀ hlω).1 (Nat.floor_le hlt)
  have hj2 : Real.log t < (j + 1) * Real.log ω :=
    (div_lt_iff₀ hlω).1 (Nat.lt_floor_add_one _)
  have hωj : ω ^ j ≤ t := by
    rw [← Real.exp_log ht0, ← Real.exp_log (pow_pos (zero_lt_one.trans hω) j), Real.log_pow]
    exact Real.exp_le_exp.2 hj1
  have hωj1 : t < ω ^ (j + 1) := by
    rw [← Real.exp_log ht0, ← Real.exp_log (pow_pos (zero_lt_one.trans hω) (j + 1)),
      Real.log_pow]
    push_cast
    exact Real.exp_lt_exp.2 hj2
  refine ⟨j, Nat.lt_succ_of_le (Nat.floor_le_floor ?_), ?_, ?_⟩
  · exact div_le_div_of_nonneg_right (Real.log_le_log ht0 htθ) hlω.le
  · rw [← hat]
    exact Real.rpow_le_rpow_of_exponent_le ha.le hωj
  · rw [← hat, ← Real.rpow_mul ha0.le, ← pow_succ]
    exact Real.rpow_lt_rpow_of_exponent_lt ha hωj1

end Real

namespace NumberField.FormSystem

/-! ### Theorem 8.1 for the normalized quotient -/

/-- The threshold of Theorem 8.1 grows with `log H_L`. -/
theorem gapThreshold_mono {n R : ℕ} {δ ℓ ℓ' : ℝ} (hn : 1 ≤ n)
    (hδ : 0 < δ) (hℓ : ℓ ≤ ℓ') : gapThreshold n R δ ℓ ≤ gapThreshold n R δ ℓ' := by
  have hε := gapEps_pos hn hδ
  unfold gapThreshold thetaOneB thetaTwoB
  gcongr

section Transfer

variable {K : Type} [Field K] [NumberField K] {m : ℕ} {Ω : Type*} [Field Ω] [Algebra K Ω]
  [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω] (L' : FormSystem K (Fin m)) (d : FormExponent K (Fin m))

/-- **EF13 Theorem 8.1 without (8.8)**: (8.3), (8.4), (8.9) and `d_{v₀} = 0` at one finite place
suffice, by `isNormalSemistable_comp`. The hypothesis `λ_1(Q) ≤ Q^{-δ}` is replaced by a nonzero
point of height `≤ Q^{-δ}`. -/
theorem exists_intervals_of_fin_eq_zero (hm : 2 ≤ m) {R : ℕ} (hR : #L'.forms ≤ R) (hmR : m ≤ R)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hsa : ∀ v, ∑ i, d.arch v i = 0)
    (hsf : ∀ v, ∑ i, d.fin v i = 0) (hsup : (∑ v, ⨆ i, d.arch v i) + ∑ᶠ v, ⨆ i, d.fin v i ≤ 1)
    {v₀ : FinitePlace K} (hv₀ : d.fin v₀ = 0)
    (hU : ∀ U : Submodule Ω (Fin m → Ω), U ≠ ⊤ → L'.subspaceWeight d U ≤ 0) :
    ∃ a : Fin (gapIntervals m R δ) → ℝ, (∀ i, 1 < a i) ∧ ∀ (Q : ℝ) (hQ : 1 < Q),
      Real.exp (gapThreshold m R δ (Real.log L'.absFormHeight)) ≤ Q →
      ∀ y : Fin m → Ω, y ≠ 0 → L'.absMulHeight (d.weight (zero_lt_one.trans hQ)) y ≤ Q ^ (-δ) →
      ∃ i, a i ≤ Q ∧ Q ≤ a i ^ (2 * gapRatio m R δ) := by
  set P := (L'.fin v₀)⁻¹
  have hP := L'.det_inv_fin_ne_zero v₀
  have hu : IsUnit (L'.fin v₀).det := isUnit_iff_ne_zero.2 (L'.fin_det_ne_zero v₀)
  set L₀ := L'.comp P hP
  obtain ⟨a, ha1, ha⟩ := L₀.exists_intervals d (L'.isNormalSemistable_comp d hsa hsf hsup hv₀ hU)
    hm ((L'.card_forms_comp_le P hP).trans hR) hmR hδ hδ1
  refine ⟨a, ha1, fun Q hQ hthr y hy hyQ ↦ ha Q hQ (le_trans ?_ hthr) ?_⟩
  · exact Real.exp_le_exp.2 (gapThreshold_mono (by omega) hδ (Real.log_le_log
      (zero_lt_one.trans_le L₀.one_le_absFormHeight) (L'.absFormHeight_comp_le P hP)))
  · set z := (L'.fin v₀).map (algebraMap K Ω) *ᵥ y
    have hPz : P.map (algebraMap K Ω) *ᵥ z = y := by
      rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu,
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
    have hz : z ≠ 0 := fun h ↦ hy (by rw [← hPz, h, Matrix.mulVec_zero])
    refine L₀.successiveInf_one_le_of_absMulHeight_le _ hz
      (Real.rpow_nonneg (zero_lt_one.trans hQ).le _) ?_
    rwa [absMulHeight_comp, hPz]

end Transfer

/-! ### The threshold -/

/-- **The threshold `log C`** of the interval result before cutting, a function of `n`, `R`, `δ`
and `ℓ = log H_L`: it covers Theorem 8.1 for every quotient `(L'', d)` (`n - k` variables,
`Rⁿ` forms, `δ / 2n`, `H_{L''} ≤ (2 H_L)^{(8R)ⁿ}`), the constant of Prop. 18.5 and the case
`n - k = 1`. -/
noncomputable def quotThreshold (n R : ℕ) (δ ℓ : ℝ) : ℝ :=
  (∑ p ∈ Icc 1 n, gapThreshold p (R ^ n) (δ / (2 * n)) ((8 * R) ^ n * (Real.log 2 + ℓ))) +
    2 * n / δ * (Real.log n + (4 * R) ^ n * (Real.log 2 + ℓ) + ℓ) +
    2 * n / δ * ((8 * R) ^ n * R ^ n * (Real.log 2 + ℓ)) + 1

theorem gapThreshold_nonneg {n R : ℕ} {δ ℓ : ℝ} (hn : 1 ≤ n) (hδ : 0 < δ) (hℓ : 0 ≤ ℓ) :
    0 ≤ gapThreshold n R δ ℓ :=
  le_trans (by positivity) (terms_le_gapThreshold (R := R) hn hδ hℓ).1

theorem terms_le_quotThreshold {n R p : ℕ} {δ ℓ : ℝ} (hp : 1 ≤ p) (hpn : p ≤ n) (hδ : 0 < δ)
    (hℓ : 0 ≤ ℓ) :
    gapThreshold p (R ^ n) (δ / (2 * n)) ((8 * R) ^ n * (Real.log 2 + ℓ)) ≤
        quotThreshold n R δ ℓ ∧
      2 * n / δ * (Real.log n + (4 * R) ^ n * (Real.log 2 + ℓ) + ℓ) ≤ quotThreshold n R δ ℓ ∧
      2 * n / δ * ((8 * R) ^ n * R ^ n * (Real.log 2 + ℓ)) < quotThreshold n R δ ℓ := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have hδ' : 0 < δ / (2 * n) := by positivity
  have hl2 : 0 ≤ Real.log 2 + ℓ := by have := Real.log_nonneg one_le_two; linarith
  have hln : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hg : ∀ q ∈ Icc 1 n,
      0 ≤ gapThreshold q (R ^ n) (δ / (2 * n)) ((8 * R) ^ n * (Real.log 2 + ℓ)) :=
    fun q hq ↦ gapThreshold_nonneg (mem_Icc.1 hq).1 hδ' (by positivity)
  have h1 := single_le_sum hg (mem_Icc.2 ⟨hp, hpn⟩)
  have h2 := sum_nonneg hg
  have t2 : 0 ≤ 2 * n / δ * (Real.log n + (4 * R) ^ n * (Real.log 2 + ℓ) + ℓ) := by positivity
  have t3 : 0 ≤ 2 * n / δ * ((8 * R) ^ n * R ^ n * (Real.log 2 + ℓ)) := by positivity
  unfold quotThreshold
  refine ⟨by linarith, by linarith, by linarith⟩

theorem quotThreshold_mono {n R : ℕ} {δ ℓ ℓ' : ℝ} (hn : 1 ≤ n) (hδ : 0 < δ) (hℓ : ℓ ≤ ℓ') :
    quotThreshold n R δ ℓ ≤ quotThreshold n R δ ℓ' := by
  have : (0 : ℝ) < n := Nat.cast_pos.2 hn
  unfold quotThreshold
  gcongr with p hp
  · exact gapThreshold_mono (mem_Icc.1 hp).1 (by positivity) (by gcongr)

/-- The threshold is affine in `ℓ = log H_L`. -/
theorem quotThreshold_eq (n R : ℕ) (δ ℓ : ℝ) :
    quotThreshold n R δ ℓ =
      quotThreshold n R δ 0 + ℓ * (quotThreshold n R δ 1 - quotThreshold n R δ 0) := by
  have hg : ∀ (p : ℕ) (x : ℝ), gapThreshold p (R ^ n) (δ / (2 * n)) x =
      gapThreshold p (R ^ n) (δ / (2 * n)) 0 +
        x * (gapThreshold p (R ^ n) (δ / (2 * n)) 1 - gapThreshold p (R ^ n) (δ / (2 * n)) 0) :=
    fun p x ↦ by unfold gapThreshold; ring
  simp only [quotThreshold]
  rw [sum_congr rfl fun p _ ↦ hg p ((8 * R) ^ n * (Real.log 2 + ℓ)),
    sum_congr rfl fun p _ ↦ hg p ((8 * R) ^ n * (Real.log 2 + 0)),
    sum_congr rfl fun p _ ↦ hg p ((8 * R) ^ n * (Real.log 2 + 1)), sum_add_distrib,
    sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum]
  ring

theorem quotThreshold_pos {n R : ℕ} {δ ℓ : ℝ} (hn : 1 ≤ n) (hδ : 0 < δ) (hℓ : 0 ≤ ℓ) :
    0 < quotThreshold n R δ ℓ := by
  have hl2 : 0 ≤ Real.log 2 + ℓ := by have := Real.log_nonneg one_le_two; linarith
  exact lt_of_le_of_lt (by positivity) (terms_le_quotThreshold (R := R) le_rfl hn hδ hℓ).2.2

/-- **The exponent `ω₀ = δ⁻¹ log 3R`** of Theorem 2.3. -/
noncomputable def cutRatio (R : ℕ) (δ : ℝ) : ℝ := Real.log (3 * R) / δ

theorem one_lt_cutRatio {R : ℕ} (hR : 2 ≤ R) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    1 < cutRatio R δ := by
  have h6 : (6 : ℝ) ≤ 3 * R := by
    have : (2 : ℝ) ≤ R := by exact_mod_cast hR
    linarith
  have h1 : 1 < Real.log (3 * R) := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    linarith [Real.exp_one_lt_d9]
  rw [cutRatio, lt_div_iff₀ hδ]
  linarith

/-- A bound for `log C / log C₀`, `log C = quotThreshold n R δ (log H_L)` the threshold and
`C₀ = max(H_L^{1/R}, n^{1/δ})`: `log C₀ ≥ log 2 / δ` and `log C₀ ≥ log H_L / R`. -/
noncomputable def intervalBound (n R : ℕ) (δ : ℝ) : ℝ :=
  quotThreshold n R δ 0 * δ / Real.log 2 + R * (quotThreshold n R δ 1 - quotThreshold n R δ 0)

/-- **The number of intervals** in Theorem 2.3: `[C₀, C)` and the intervals `[a, a^{2ω}]` of
Theorem 8.1 for the quotient, all cut into intervals `[b, b^{ω₀})`. Only the quotient by `T`
occurs, of dimension `p = n - dim T`, so the count takes the largest over `1 ≤ p ≤ n`. -/
noncomputable def intervalCount (n R : ℕ) (δ : ℝ) : ℕ :=
  Real.cutCount (intervalBound n R δ) (cutRatio R δ) +
    (Icc 1 n).sup fun p ↦ gapIntervals p (R ^ n) (δ / (2 * n)) *
      Real.cutCount (2 * gapRatio p (R ^ n) (δ / (2 * n))) (cutRatio R δ)

/-! ### EF13 (18.23): the reduction to Theorem 8.1 -/

section Reduction

variable {K : Type} [Field K] [NumberField K] {n k m : ℕ} {Ω : Type*} [Field Ω] [Algebra K Ω]
  [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω] (L : FormSystem K (Fin n))
  (c : FormExponent K (Fin n)) (S : Splitting K n k m)

omit [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω] in
theorem sum_quotNormExp_arch (hm : 0 < m) (v : InfinitePlace K) :
    ∑ t, (L.quotNormExp S c).arch v t = 0 := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  simp only [quotNormExp, FormExponent.divConst, ← sum_div, FormExponent.sum_center_arch,
    zero_div]

omit [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω] in
theorem sum_quotNormExp_fin (hm : 0 < m) (v : FinitePlace K) :
    ∑ t, (L.quotNormExp S c).fin v t = 0 := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  simp only [quotNormExp, FormExponent.divConst, ← sum_div, FormExponent.sum_center_fin,
    zero_div]

omit [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω] in
theorem quotNormExp_fin_eq_zero {v : FinitePlace K} (hv : c.fin v = 0) :
    (L.quotNormExp S c).fin v = 0 := by
  funext t
  simp [quotNormExp_fin, hv]

/-- **EF13 Prop. 18.5**: if `H_{L,c,Q}(x) ≤ Δ_L^{1/n} Q^{-δ}` and `Q` is large, then
`H_{L'',d,Q'}(φ'' x) ≤ Q'^{-δ/2n}`, `Q' = Q^{n/m}` (EF13: `Q'^{-99δ/100n}`). -/
theorem absMulHeight_quotNormExp_le_rpow (hc : c.sum = 0) {T : Submodule Ω (Fin n → Ω)}
    (hT : Submodule.IsDestabilizing (L.subspaceWeight c) ⊤ T)
    (hST : (Submodule.span K (Set.range S.incl.col)).extendPi Ω = T) (hm : 0 < m) {R : ℕ}
    (hR : #L.forms ≤ R) {δ : ℝ} (hδ : 0 < δ) {Q : ℝ} (hQ : 1 ≤ Q)
    (hthr : 2 * n / δ * (Real.log n + (4 * R) ^ n * (Real.log 2 + Real.log L.absFormHeight) +
      Real.log L.absFormHeight) ≤ Real.log Q) {x : Fin n → Ω}
    (hx : L.absMulHeight (c.weight (zero_lt_one.trans_le hQ)) x ≤
      L.absDet ^ ((n : ℝ)⁻¹) * Q ^ (-δ)) :
    (L.quotSystem S c).absMulHeight ((L.quotNormExp S c).weight
        (Real.rpow_pos_of_pos (zero_lt_one.trans_le hQ) ((n : ℝ) / m))) (S.projLin Ω x) ≤
      (Q ^ ((n : ℝ) / m)) ^ (-(δ / (2 * n))) := by
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hkm := S.card_eq
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have hm' : (1 : ℝ) ≤ m := Nat.one_le_cast.2 hm
  have hmn : (m : ℝ) ≤ n := Nat.cast_le.2 (by omega)
  have hH : 1 ≤ L.absFormHeight := L.one_le_absFormHeight
  set ℓ := Real.log L.absFormHeight
  have hℓ : 0 ≤ ℓ := Real.log_nonneg hH
  have hΔ : 0 < L.absDet := L.absDet_pos
  set A := (n : ℝ) * (2 * L.absFormHeight) ^ ((4 * #L.forms) ^ n)
  have hA : 0 < A := by positivity
  set B := A * L.absDet ^ ((n : ℝ)⁻¹)
  have hB : 0 < B := by positivity
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  set Q' := Q ^ ((n : ℝ) / m)
  have hQ'0 : 0 < Q' := by positivity
  have hQQ' : Real.log Q ≤ Real.log Q' := by
    rw [Real.log_rpow hQ0]
    exact le_mul_of_one_le_left hlogQ ((one_le_div (by linarith)).2 hmn)
  have h2H : Real.log (2 * L.absFormHeight) = Real.log 2 + ℓ :=
    Real.log_mul two_ne_zero (by positivity)
  have hl2 : 0 ≤ Real.log 2 + ℓ := by rw [← h2H]; exact Real.log_nonneg (by linarith)
  have hlogB : Real.log B ≤ Real.log n + (4 * R) ^ n * (Real.log 2 + ℓ) + ℓ := by
    rw [Real.log_mul hA.ne' (by positivity), Real.log_mul hn.ne' (by positivity), Real.log_pow,
      Real.log_rpow hΔ, h2H]
    have h1 : (((4 * #L.forms) ^ n : ℕ) : ℝ) ≤ (4 * R) ^ n := by
      exact_mod_cast Nat.pow_le_pow_left (by omega) n
    have h2 : (n : ℝ)⁻¹ * Real.log L.absDet ≤ ℓ := by
      have h3 := Real.log_le_log hΔ L.absDet_le_absFormHeight
      have h4 : (n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      have h5 : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right h1 hl2]
  have hX : Real.log n + (4 * R) ^ n * (Real.log 2 + ℓ) + ℓ ≤ δ / (2 * n) * Real.log Q := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    rw [div_mul_eq_mul_div, div_le_iff₀ hδ] at hthr
    linarith
  have hBQ : B ≤ Q' ^ (δ / (2 * n)) := by
    rw [Real.rpow_def_of_pos hQ'0, ← Real.exp_log hB]
    refine Real.exp_le_exp.2 ?_
    have : δ / (2 * n) * Real.log Q ≤ δ / (2 * n) * Real.log Q' := by gcongr
    linarith
  have hQd : Q ^ (-δ) ≤ Q' ^ (-(δ / n)) := by
    rw [← Real.rpow_mul hQ0.le]
    refine Real.rpow_le_rpow_of_exponent_le hQ ?_
    have : (n : ℝ) / m * (-(δ / n)) = -(δ / m) := by field_simp
    rw [this, neg_le_neg_iff]
    exact div_le_self hδ.le hm'
  calc _ ≤ A * L.absMulHeight (c.weight hQ0) x :=
        L.absMulHeight_quotNormExp_le c S hc hT hST hm hQ x
    _ ≤ A * (L.absDet ^ ((n : ℝ)⁻¹) * Q ^ (-δ)) := by gcongr
    _ = B * Q ^ (-δ) := by ring
    _ ≤ Q' ^ (δ / (2 * n)) * Q' ^ (-(δ / n)) := by gcongr
    _ = Q' ^ (-(δ / (2 * n))) := by
      rw [← Real.rpow_add hQ'0]
      congr 1
      field_simp
      ring

/-- `log H_{L''} ≤ (8R)ⁿ log (2 H_L)` (EF13 Lemma 18.4). -/
theorem log_absFormHeight_quotSystem_le {T : Submodule Ω (Fin n → Ω)}
    (hT : Submodule.IsDestabilizing (L.subspaceWeight c) ⊤ T)
    (hST : (Submodule.span K (Set.range S.incl.col)).extendPi Ω = T) (hm : 0 < m) {R : ℕ}
    (hR : #L.forms ≤ R) :
    Real.log (L.quotSystem S c).absFormHeight ≤
      (8 * R) ^ n * (Real.log 2 + Real.log L.absFormHeight) := by
  have hH : 1 ≤ L.absFormHeight := L.one_le_absFormHeight
  have h2H : 1 ≤ 2 * L.absFormHeight := by linarith
  have h := (L.absFormHeight_quotSystem_le_of_isDestabilizing c S hT hST hm).trans
    (pow_le_pow_right₀ h2H (Nat.pow_le_pow_left (by omega : 8 * #L.forms ≤ 8 * R) n))
  refine (Real.log_le_log (zero_lt_one.trans_le (L.quotSystem S c).one_le_absFormHeight) h).trans
    (le_of_eq ?_)
  rw [Real.log_pow, Real.log_mul two_ne_zero (by positivity)]
  push_cast
  ring

/-- **The case `n - k = 1`** (EF13, proof of Theorem 2.3): then `d = 0`, so the heights on the
quotient are bounded below independently of `Q'` (EF13 Lemma 7.1), and a point of height
`≤ Q'^{-δ/2n}` forces `Q'` to be small. -/
theorem false_of_card_eq_one (S : Splitting K n k 1) {T : Submodule Ω (Fin n → Ω)}
    (hT : Submodule.IsDestabilizing (L.subspaceWeight c) ⊤ T)
    (hST : (Submodule.span K (Set.range S.incl.col)).extendPi Ω = T) {R : ℕ}
    (hR : #L.forms ≤ R) {δ : ℝ} (hδ : 0 < δ) {Q : ℝ} (hQ : 1 ≤ Q)
    (hthr : 2 * n / δ * ((8 * R) ^ n * R ^ n * (Real.log 2 + Real.log L.absFormHeight)) <
      Real.log Q) {y : Fin 1 → Ω} (hy : y ≠ 0)
    (hyQ : (L.quotSystem S c).absMulHeight ((L.quotNormExp S c).weight
        (Real.rpow_pos_of_pos (zero_lt_one.trans_le hQ) ((n : ℝ) / (1 : ℕ)))) y ≤
      (Q ^ ((n : ℝ) / (1 : ℕ))) ^ (-(δ / (2 * n)))) : False := by
  have hkm := S.card_eq
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  set L'' := L.quotSystem S c
  set d := L.quotNormExp S c
  set Q' := Q ^ ((n : ℝ) / (1 : ℕ))
  have hQ' : 1 ≤ Q' := Real.one_le_rpow hQ (by positivity)
  have hQ'0 : 0 < Q' := zero_lt_one.trans_le hQ'
  have hda : ∀ v t, d.arch v t = 0 := fun v t ↦ by
    rw [quotNormExp_arch, Fin.sum_univ_one, Subsingleton.elim t 0]
    simp
  have hdf : ∀ v t, d.fin v t = 0 := fun v t ↦ by
    rw [quotNormExp_fin, Fin.sum_univ_one, Subsingleton.elim t 0]
    simp
  have hlow := L''.le_absMulHeight_weight d hQ' hy (Ω := Ω)
  simp only [hda, hdf, ciSup_const, sum_const_zero, finsum_zero, add_zero, neg_zero,
    Real.rpow_zero, mul_one, Fintype.card_fin, Nat.choose_one_right, Nat.cast_one, inv_one,
    one_mul] at hlow
  have h := hlow.trans hyQ
  -- take logarithms: `δ/2n log Q' ≤ r log H_{L''}`
  have hH'' : 1 ≤ L''.absFormHeight := L''.one_le_absFormHeight
  have hH''0 : 0 < L''.absFormHeight := zero_lt_one.trans_le hH''
  have hlog := Real.log_le_log (by positivity) h
  rw [Real.log_rpow hH''0, Real.log_rpow hQ'0] at hlog
  have hlH := L.log_absFormHeight_quotSystem_le c S hT hST one_pos hR
  have hlH0 : 0 ≤ Real.log L''.absFormHeight := Real.log_nonneg hH''
  have hr : ((#L''.forms : ℕ) : ℝ) ≤ (R : ℝ) ^ n := by
    have h1 := L.card_forms_quotSystem_le S c
    have h2 : #L.forms ^ (k + 1) ≤ R ^ n :=
      (Nat.pow_le_pow_left hR _).trans (Nat.pow_le_pow_right (by have := L.le_card_forms; omega)
        (by omega))
    exact_mod_cast h1.trans h2
  have hQQ' : Real.log Q ≤ Real.log Q' := by
    rw [Real.log_rpow hQ0, Nat.cast_one, div_one]
    exact le_mul_of_one_le_left (Real.log_nonneg hQ) (by exact_mod_cast (show 1 ≤ n by omega))
  have hkey : δ / (2 * n) * Real.log Q' ≤ (R : ℝ) ^ n * ((8 * R) ^ n *
      (Real.log 2 + Real.log L.absFormHeight)) := by
    calc δ / (2 * n) * Real.log Q' ≤ (#L''.forms : ℝ) * Real.log L''.absFormHeight := by
          linarith
      _ ≤ (R : ℝ) ^ n * ((8 * R) ^ n * (Real.log 2 + Real.log L.absFormHeight)) := by
          gcongr
  have hthr' : (8 * R) ^ n * R ^ n * (Real.log 2 + Real.log L.absFormHeight) <
      δ / (2 * n) * Real.log Q := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hδ] at hthr
    linarith
  have : δ / (2 * n) * Real.log Q ≤ δ / (2 * n) * Real.log Q' := by gcongr
  nlinarith

/-- **EF13 (18.23)** for a splitting adapted to the destabilizing subspace `T`: the `Q` above the
threshold with a point `x ∉ T`, `H_{L,c,Q}(x) ≤ Δ_L^{1/n} Q^{-δ}`, lie in the intervals
`[a, a^{2ω}]` of Theorem 8.1 for `(L'', d)` with `n - k` variables, `Rⁿ` forms and `δ / 2n`,
rescaled by `Q = Q'^{(n-k)/n}`. -/
theorem exists_intervals_of_splitting (hc : c.sum = 0)
    (hsup : (∑ v, ⨆ i, c.arch v i) + ∑ᶠ v, ⨆ i, c.fin v i ≤ 1) {R : ℕ} (hR : #L.forms ≤ R)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {T : Submodule Ω (Fin n → Ω)}
    (hT : Submodule.IsDestabilizing (L.subspaceWeight c) ⊤ T)
    (hST : (Submodule.span K (Set.range S.incl.col)).extendPi Ω = T) (hm : 0 < m) :
    ∃ a : Fin (gapIntervals m (R ^ n) (δ / (2 * n))) → ℝ, (∀ i, 1 < a i) ∧
      ∀ (Q : ℝ) (hQ : 1 ≤ Q), Real.exp (quotThreshold n R δ (Real.log L.absFormHeight)) ≤ Q →
      ∀ x : Fin n → Ω, x ∉ T → L.absMulHeight (c.weight (zero_lt_one.trans_le hQ)) x ≤
        L.absDet ^ ((n : ℝ)⁻¹) * Q ^ (-δ) →
      ∃ i, a i ≤ Q ∧ Q ≤ a i ^ (2 * gapRatio m (R ^ n) (δ / (2 * n))) := by
  have hkm := S.card_eq
  have hnR := L.le_card_forms.trans hR
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have hℓ : 0 ≤ Real.log L.absFormHeight := Real.log_nonneg L.one_le_absFormHeight
  have hterms := terms_le_quotThreshold (R := R) hm (by omega : m ≤ n) hδ hℓ
  have hlog : ∀ Q, Real.exp (quotThreshold n R δ (Real.log L.absFormHeight)) ≤ Q →
      quotThreshold n R δ (Real.log L.absFormHeight) ≤ Real.log Q := fun Q hQ ↦
    (Real.le_log_iff_exp_le ((Real.exp_pos _).trans_le hQ)).2 hQ
  have hproj : ∀ x ∉ T, S.projLin Ω x ≠ 0 := fun x hx h ↦
    hx (by rw [← ker_projLin_eq S hST]; exact h)
  -- the height on the quotient (EF13 Prop. 18.5)
  have key : ∀ (Q : ℝ) (hQ : 1 ≤ Q), Real.exp (quotThreshold n R δ (Real.log L.absFormHeight)) ≤ Q →
      ∀ x : Fin n → Ω, L.absMulHeight (c.weight (zero_lt_one.trans_le hQ)) x ≤
        L.absDet ^ ((n : ℝ)⁻¹) * Q ^ (-δ) →
      (L.quotSystem S c).absMulHeight ((L.quotNormExp S c).weight
        (Real.rpow_pos_of_pos (zero_lt_one.trans_le hQ) ((n : ℝ) / m))) (S.projLin Ω x) ≤
      (Q ^ ((n : ℝ) / m)) ^ (-(δ / (2 * n))) := fun Q hQ hthr x hx ↦
    L.absMulHeight_quotNormExp_le_rpow c S hc hT hST hm hR hδ hQ
      (hterms.2.1.trans (hlog Q hthr)) hx
  rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | hm2
  · refine ⟨fun _ ↦ 2, fun _ ↦ one_lt_two, fun Q hQ hthr x hx hxQ ↦ ?_⟩
    exact (L.false_of_card_eq_one c S hT hST hR hδ hQ (hterms.2.2.trans_le (hlog Q hthr))
      (hproj x hx) (key Q hQ hthr x hxQ)).elim
  -- `m ≥ 2`: Theorem 8.1 for `(L'', d)`
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : FinitePlace K, c.fin v₀ = 0 := by
    obtain ⟨v, hv⟩ := c.finite_setOf_fin_ne_zero.infinite_compl.nonempty
    exact ⟨v, not_not.1 hv⟩
  have hR'' : #(L.quotSystem S c).forms ≤ R ^ n :=
    (L.card_forms_quotSystem_le S c).trans ((Nat.pow_le_pow_left hR _).trans
      (Nat.pow_le_pow_right (by omega) (by omega)))
  have hmR'' : m ≤ R ^ n := (by omega : m ≤ R).trans (Nat.le_self_pow (by omega) R)
  have hδ' : 0 < δ / (2 * n) := by positivity
  have hδ'1 : δ / (2 * n) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    linarith
  have hsup' : (∑ v, ⨆ t, (L.quotNormExp S c).arch v t) +
      ∑ᶠ v, ⨆ t, (L.quotNormExp S c).fin v t ≤ 1 := by
    have := L.sum_iSup_quotNormExp_le S c hm
    rw [hc, zero_div, sub_zero] at this
    exact this.trans hsup
  have hT' : Submodule.IsDestabilizing (L.subspaceWeight c) ⊤ (LinearMap.ker (S.projLin Ω)) := by
    rwa [ker_projLin_eq S hST]
  obtain ⟨a, ha1, ha⟩ := (L.quotSystem S c).exists_intervals_of_fin_eq_zero (L.quotNormExp S c)
    hm2 hR'' hmR'' hδ' hδ'1 (L.sum_quotNormExp_arch c S hm) (L.sum_quotNormExp_fin c S hm)
    hsup' (L.quotNormExp_fin_eq_zero c S hv₀)
    (fun U hU ↦ L.subspaceWeight_quotNormExp_nonpos S c hm hT' hU)
  have hmn : (0 : ℝ) < (m : ℝ) / n := by
    have : (0 : ℝ) < m := Nat.cast_pos.2 hm
    positivity
  refine ⟨fun i ↦ a i ^ ((m : ℝ) / n), fun i ↦ Real.one_lt_rpow (ha1 i) hmn,
    fun Q hQ hthr x hx hxQ ↦ ?_⟩
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hlQ := hlog Q hthr
  have hQ1 : 1 < Q := by
    rw [← Real.exp_zero]
    have hl2 : 0 ≤ Real.log 2 + Real.log L.absFormHeight := by
      have := Real.log_nonneg one_le_two; linarith
    exact (Real.exp_lt_exp.2 (lt_of_le_of_lt (by positivity) hterms.2.2)).trans_le hthr
  set Q' := Q ^ ((n : ℝ) / m)
  have hQ' : 1 < Q' := Real.one_lt_rpow hQ1 (by positivity)
  have hQQ' : Real.log Q ≤ Real.log Q' := by
    rw [Real.log_rpow hQ0]
    refine le_mul_of_one_le_left (Real.log_nonneg hQ) ((one_le_div (Nat.cast_pos.2 hm)).2 ?_)
    exact_mod_cast (show m ≤ n by omega)
  have hQ'Q : Q' ^ ((m : ℝ) / n) = Q := by
    rw [← Real.rpow_mul hQ0.le, div_mul_div_cancel₀ (Nat.cast_pos.2 hm).ne', div_self hn.ne',
      Real.rpow_one]
  obtain ⟨i, h1, h2⟩ := ha Q' hQ' (by
      rw [← Real.exp_log (zero_lt_one.trans hQ')]
      refine Real.exp_le_exp.2 (le_trans ?_ (hterms.1.trans (hlQ.trans hQQ')))
      exact gapThreshold_mono (by omega) hδ'
        (L.log_absFormHeight_quotSystem_le c S hT hST hm hR))
    (S.projLin Ω x) (hproj x hx) (key Q hQ hthr x hxQ)
  refine ⟨i, ?_, ?_⟩
  · rw [← hQ'Q]
    exact Real.rpow_le_rpow (zero_lt_one.trans (ha1 i)).le h1 hmn.le
  · rw [← hQ'Q, ← Real.rpow_mul (zero_lt_one.trans (ha1 i)).le, mul_comm,
      Real.rpow_mul (zero_lt_one.trans (ha1 i)).le]
    exact Real.rpow_le_rpow (zero_lt_one.trans hQ').le h2 hmn.le

/-- **EF13 (18.23)**: for the destabilizing subspace `T = T(L, c)` of dimension `k`, the `Q` above
the threshold with a point `x ∉ T`, `H_{L,c,Q}(x) ≤ Δ_L^{1/n} Q^{-δ}`, lie in
`gapIntervals (n - k) Rⁿ (δ / 2n)` intervals `[a, a^{2ω}]`, `ω = gapRatio (n - k) Rⁿ (δ / 2n)`. -/
theorem exists_intervals_of_isDestabilizing (hc : c.sum = 0)
    (hsup : (∑ v, ⨆ i, c.arch v i) + ∑ᶠ v, ⨆ i, c.fin v i ≤ 1) {R : ℕ} (hR : #L.forms ≤ R)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {T : Submodule Ω (Fin n → Ω)}
    (hT : Submodule.IsDestabilizing (L.subspaceWeight c) ⊤ T) :
    ∃ a : Fin (gapIntervals (n - finrank Ω T) (R ^ n) (δ / (2 * n))) → ℝ, (∀ i, 1 < a i) ∧
      ∀ (Q : ℝ) (hQ : 1 ≤ Q), Real.exp (quotThreshold n R δ (Real.log L.absFormHeight)) ≤ Q →
      ∀ x : Fin n → Ω, x ∉ T → L.absMulHeight (c.weight (zero_lt_one.trans_le hQ)) x ≤
        L.absDet ^ ((n : ℝ)⁻¹) * Q ^ (-δ) →
      ∃ i, a i ≤ Q ∧ Q ≤ a i ^ (2 * gapRatio (n - finrank Ω T) (R ^ n) (δ / (2 * n))) := by
  obtain ⟨S, hS⟩ := Splitting.exists_range_inclLin
    (L.isDefinedOver_of_isDestabilizing c hT Submodule.isDefinedOver_top)
  have hm : 0 < n - finrank Ω T := by
    have := Submodule.finrank_lt hT.lt.ne
    rw [Module.finrank_fin_fun] at this
    omega
  exact L.exists_intervals_of_splitting c S hc hsup hR hδ hδ1 hT
    ((range_inclLin_eq_extendPi S).symm.trans hS) hm

/-- **EF13 Theorem 2.3**: let `n ≥ 2`, `(L, c)` with `Σ_v Σ_i c_iv = 0` (2.8) and
`Σ_v max_i c_iv ≤ 1` (2.9), at most `R` distinct forms, `0 < δ ≤ 1`, and `T = T(L, c)` the
destabilizing subspace (2.21). Then there is a set of at most `intervalCount n R δ` reals
`b ≥ C₀ = max(H_L^{1/R}, n^{1/δ})` such that every `Q ≥ C₀` with a point `x ∉ T`,
`H_{L,c,Q}(x) ≤ Δ_L^{1/n} Q^{-δ}` (2.24), lies in one of the intervals `[b, b^{ω₀})`,
`ω₀ = δ⁻¹ log 3R` (2.25). The count is not EF13's `m₀`. -/
theorem exists_intervals_cover (hn : 2 ≤ n) (hc : c.sum = 0)
    (hsup : (∑ v, ⨆ i, c.arch v i) + ∑ᶠ v, ⨆ i, c.fin v i ≤ 1) {R : ℕ} (hR : #L.forms ≤ R)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {T : Submodule Ω (Fin n → Ω)}
    (hT : Submodule.IsDestabilizing (L.subspaceWeight c) ⊤ T) :
    ∃ s : Finset ℝ, #s ≤ intervalCount n R δ ∧
      (∀ b ∈ s, max (L.absFormHeight ^ ((R : ℝ)⁻¹)) ((n : ℝ) ^ δ⁻¹) ≤ b) ∧
      ∀ (Q : ℝ) (hQ : 1 ≤ Q), max (L.absFormHeight ^ ((R : ℝ)⁻¹)) ((n : ℝ) ^ δ⁻¹) ≤ Q →
      ∀ x : Fin n → Ω, x ∉ T → L.absMulHeight (c.weight (zero_lt_one.trans_le hQ)) x ≤
        L.absDet ^ ((n : ℝ)⁻¹) * Q ^ (-δ) →
      ∃ b ∈ s, b ≤ Q ∧ Q < b ^ cutRatio R δ := by
  classical
  have hnR := L.le_card_forms.trans hR
  have hR0 : (0 : ℝ) < R := Nat.cast_pos.2 (by omega)
  have hH : 1 ≤ L.absFormHeight := L.one_le_absFormHeight
  set ℓ := Real.log L.absFormHeight
  have hℓ : 0 ≤ ℓ := Real.log_nonneg hH
  set C₀ := max (L.absFormHeight ^ ((R : ℝ)⁻¹)) ((n : ℝ) ^ δ⁻¹)
  set ω₀ := cutRatio R δ
  have hω₀ : 1 < ω₀ := one_lt_cutRatio (by omega) hδ hδ1
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hC₀ : 1 < C₀ := lt_max_of_lt_right (Real.one_lt_rpow hn1 (inv_pos.2 hδ))
  have hC₀0 : 0 < C₀ := zero_lt_one.trans hC₀
  -- `log C₀ ≥ log 2 / δ` and `log C₀ ≥ ℓ / R`
  have hlC₀n : Real.log 2 / δ ≤ Real.log C₀ := by
    calc Real.log 2 / δ ≤ Real.log n / δ := by
          gcongr
          exact_mod_cast (show 2 ≤ n from hn)
      _ = Real.log ((n : ℝ) ^ δ⁻¹) := by rw [Real.log_rpow (by linarith), div_eq_inv_mul]
      _ ≤ Real.log C₀ := Real.log_le_log (by positivity) (le_max_right _ _)
  have hlC₀H : ℓ / R ≤ Real.log C₀ := by
    calc ℓ / R = Real.log (L.absFormHeight ^ ((R : ℝ)⁻¹)) := by
          rw [Real.log_rpow (by linarith), div_eq_inv_mul]
      _ ≤ Real.log C₀ := Real.log_le_log (by positivity) (le_max_left _ _)
  have hl2 : 0 < Real.log 2 / δ := div_pos (Real.log_pos one_lt_two) hδ
  have hlC₀ : 0 < Real.log C₀ := hl2.trans_le hlC₀n
  have hm : 0 < n - finrank Ω T := by
    have := Submodule.finrank_lt hT.lt.ne
    rw [Module.finrank_fin_fun] at this
    omega
  set m := n - finrank Ω T
  obtain ⟨a, ha1, ha⟩ := L.exists_intervals_of_isDestabilizing c hc hsup hR hδ hδ1 hT
  set N₀ := Real.cutCount (intervalBound n R δ) ω₀
  set N₁ := Real.cutCount (2 * gapRatio m (R ^ n) (δ / (2 * n))) ω₀
  set s := ((range N₀).image fun j ↦ C₀ ^ (ω₀ ^ j)) ∪
    ((univ ×ˢ range N₁).image fun p : Fin (gapIntervals m (R ^ n) (δ / (2 * n))) × ℕ ↦
      max (a p.1 ^ (ω₀ ^ p.2)) C₀)
  refine ⟨s, ?_, ?_, ?_⟩
  · refine (card_union_le _ _).trans (add_le_add (card_image_le.trans (card_range _).le) ?_)
    refine card_image_le.trans ?_
    rw [card_product, card_range, card_univ, Fintype.card_fin]
    exact le_sup (f := fun p ↦ gapIntervals p (R ^ n) (δ / (2 * n)) *
      Real.cutCount (2 * gapRatio p (R ^ n) (δ / (2 * n))) ω₀) (mem_Icc.2 ⟨hm, by omega⟩)
  · intro b hb
    rcases mem_union.1 hb with h | h
    · obtain ⟨j, -, rfl⟩ := mem_image.1 h
      exact Real.self_le_rpow_of_one_le hC₀.le (one_le_pow₀ hω₀.le)
    · obtain ⟨p, -, rfl⟩ := mem_image.1 h
      exact le_max_right _ _
  intro Q hQ hC₀Q x hx hxQ
  set Θ := quotThreshold n R δ ℓ
  by_cases hΘ : Real.exp Θ ≤ Q
  · obtain ⟨i, h1, h2⟩ := ha Q hQ hΘ x hx hxQ
    obtain ⟨j, hj, h3, h4⟩ := Real.exists_cut (ha1 i) hω₀ h1 h2
    refine ⟨max (a i ^ (ω₀ ^ j)) C₀, mem_union_right _ (mem_image.2 ⟨(i, j),
      mem_product.2 ⟨mem_univ _, mem_range.2 hj⟩, rfl⟩), max_le h3 hC₀Q, h4.trans_le ?_⟩
    exact Real.rpow_le_rpow (Real.rpow_nonneg (zero_lt_one.trans (ha1 i)).le _)
      (le_max_left _ _) (by linarith)
  · rw [not_le] at hΘ
    have hΘ0 : 0 < Θ := quotThreshold_pos (by omega) hδ hℓ
    have hQθ : Q ≤ C₀ ^ (Θ / Real.log C₀) := by
      rw [Real.rpow_def_of_pos hC₀0, mul_div_cancel₀ _ hlC₀.ne']
      exact hΘ.le
    obtain ⟨j, hj, h3, h4⟩ := Real.exists_cut hC₀ hω₀ hC₀Q hQθ
    refine ⟨C₀ ^ (ω₀ ^ j), mem_union_left _ (mem_image.2 ⟨j, mem_range.2 (hj.trans_le ?_), rfl⟩),
      h3, h4⟩
    refine Real.cutCount_mono (div_pos hΘ0 hlC₀) ?_ hω₀
    -- `log C / log C₀ ≤ intervalBound n R δ`
    have hA : 0 ≤ quotThreshold n R δ 0 := (quotThreshold_pos (by omega) hδ le_rfl).le
    have hB : 0 ≤ quotThreshold n R δ 1 - quotThreshold n R δ 0 :=
      sub_nonneg.2 (quotThreshold_mono (by omega) hδ zero_le_one)
    have h1 : quotThreshold n R δ 0 / Real.log C₀ ≤ quotThreshold n R δ 0 * δ / Real.log 2 :=
      calc quotThreshold n R δ 0 / Real.log C₀ ≤ quotThreshold n R δ 0 / (Real.log 2 / δ) :=
            div_le_div_of_nonneg_left hA hl2 hlC₀n
        _ = quotThreshold n R δ 0 * δ / Real.log 2 := by
            rw [div_div_eq_mul_div]
    have h2 : ℓ / Real.log C₀ ≤ R := by
      rw [div_le_iff₀ hlC₀]
      rw [div_le_iff₀ hR0] at hlC₀H
      linarith
    have h3 : Θ / Real.log C₀ = quotThreshold n R δ 0 / Real.log C₀ +
        ℓ / Real.log C₀ * (quotThreshold n R δ 1 - quotThreshold n R δ 0) := by
      rw [show Θ = _ from quotThreshold_eq n R δ ℓ]
      field_simp
    rw [h3, intervalBound]
    gcongr

end Reduction

end NumberField.FormSystem
