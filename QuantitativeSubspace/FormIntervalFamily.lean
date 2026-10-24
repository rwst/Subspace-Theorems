/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.FormIntervalResult
public import QuantitativeSubspace.FormWeightType

/-!
# The interval result for a set of exponents

J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative Subspace Theorem*,
Ann. of Math. **177** (2013), 513–590, Theorem 2.3, §18.

EF13 Theorem 2.3 is stated for one tuple of exponents `c`. Here the forms `L` are fixed and `c`
runs through a set `𝒞` of exponents, all vanishing outside a finite set `S₁` of places, with
`Σ_i c_iv = 0` at every place and a common bound `c_iv ≤ γ_v`, `Σ_v γ_v ≤ 1`. The Roth machinery
of §§13–14 takes its exponents block by block (`FormSystem.false_of_chain_family`), so Theorem 8.1
holds for all of `𝒞` with the same intervals (`FormSystem.exists_intervals_family`). The reduction
of §18 needs one quotient system for all exponents at once: it depends on `c` only through
`T = T(L, c)` and the rows `I_v(T)` selected at the places of `S₁`. Grouping `𝒞` by these, with
at most `(n + 1) (2^{2ⁿ})^{#S₁}` subspaces `T` (`FormSystem.exists_finset_isDestabilizing`) and
at most `(nⁿ)^{#S₁}` selections for each, gives the interval result for all of `𝒞` with a number
of intervals independent of `#𝒞`.

## Main results

* `NumberField.FormSystem.quotSystem_congr`: the quotient system depends on `c` only through the
  selected rows.
* `NumberField.FormSystem.quotNormExp_vec_le`, `quotNormExp_vec_eq_zero`: the normalized exponents
  on the quotient are bounded by `max_i c_iv` and vanish where `c` does.
* `NumberField.FormSystem.exists_intervals_of_fin_eq_zero_family`: Theorem 8.1 for a set of
  exponents without (8.8).
* `NumberField.FormSystem.exists_intervals_of_splitting_family`: EF13 (18.23) for a set of
  exponents with one quotient system.
* `NumberField.FormSystem.exists_intervals_cover_of_isDestabilizing_family`: Theorem 2.3 for a set
  of exponents with the same destabilizing subspace.
* `NumberField.FormSystem.exists_intervals_cover_family`: **EF13 Theorem 2.3 for a set of
  exponents**.
-/

@[expose] public section

open Finset Module Matrix

namespace NumberField.FormSystem

variable {K : Type} [Field K] [NumberField K] {n k m : ℕ}

/-! ### The quotient system and the selected rows -/

section Congr

variable (S : Splitting K n k m) (A : Matrix (Fin n) (Fin n) K) {c c' : Fin n → ℝ}

omit [NumberField K] in
theorem _root_.NumberField.Splitting.compSel_congr (h : S.sel A c = S.sel A c') :
    S.compSel A c = S.compSel A c' := by
  have : S.complSet A c = S.complSet A c' := by simp only [Splitting.complSet, h]
  simp only [Splitting.compSel, this]

omit [NumberField K] in
/-- `L''^{(v)}` depends on the exponents only through the selected rows `I_v(T)`. -/
theorem _root_.NumberField.Splitting.quotMat_congr (h : S.sel A c = S.sel A c') :
    S.quotMat A c = S.quotMat A c' := by
  unfold Splitting.quotMat Splitting.coeffMat Splitting.restrictMat
  rw [h, S.compSel_congr A h]

variable (L : FormSystem K (Fin n)) {c c' : FormExponent K (Fin n)}

/-- **The quotient system depends on the exponents only through the selected rows**: if `c` and
`c'` select the same rows `I_v(T)` at every place, then `L''` is the same for both. -/
theorem quotSystem_congr (h : ∀ v, S.sel (L.mat v) (c.vec v) = S.sel (L.mat v) (c'.vec v)) :
    L.quotSystem S c = L.quotSystem S c' := by
  have ha : ∀ v, S.quotMat (L.arch v) (c.arch v) = S.quotMat (L.arch v) (c'.arch v) :=
    fun v ↦ S.quotMat_congr _ (h (.inl v))
  have hf : ∀ v, S.quotMat (L.fin v) (c.fin v) = S.quotMat (L.fin v) (c'.fin v) :=
    fun v ↦ S.quotMat_congr _ (h (.inr v))
  simp only [quotSystem, ha, hf]

/-- With `Σ_i c_iv = 0`, the normalized exponents `d_tv` on the quotient are at most `max_i c_iv`
(EF13 (18.14) at one place). -/
theorem quotNormExp_vec_le (c : FormExponent K (Fin n)) (hm : 0 < m)
    {v : InfinitePlace K ⊕ FinitePlace K} (h0 : ∑ i, c.vec v i = 0) (t : Fin m) :
    (L.quotNormExp S c).vec v t ≤ ⨆ i, c.vec v i := by
  rcases v with v | v
  · change (L.quotNormExp S c).arch v t ≤ ⨆ i, c.arch v i
    have h0' : ∑ i, c.arch v i = 0 := h0
    have := le_iSup_sub_mean _ _ _ hm S.card_eq (sum_selEquiv S (L.arch v) (c.arch v)) t
    rw [h0', zero_div, sub_zero] at this
    rw [quotNormExp_arch]
    exact this
  · change (L.quotNormExp S c).fin v t ≤ ⨆ i, c.fin v i
    have h0' : ∑ i, c.fin v i = 0 := h0
    have := le_iSup_sub_mean _ _ _ hm S.card_eq (sum_selEquiv S (L.fin v) (c.fin v)) t
    rw [h0', zero_div, sub_zero] at this
    rw [quotNormExp_fin]
    exact this

/-- The normalized exponents on the quotient vanish where `c` does. -/
theorem quotNormExp_vec_eq_zero (c : FormExponent K (Fin n))
    {v : InfinitePlace K ⊕ FinitePlace K} (h : c.vec v = 0) : (L.quotNormExp S c).vec v = 0 := by
  funext t
  rcases v with v | v
  · have h' : c.arch v = 0 := h
    change (L.quotNormExp S c).arch v t = 0
    simp [quotNormExp_arch, h']
  · have h' : c.fin v = 0 := h
    change (L.quotNormExp S c).fin v t = 0
    simp [quotNormExp_fin, h']

end Congr

/-! ### Theorem 8.1 for a set of exponents without (8.8) -/

section Transfer

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω]
  (L' : FormSystem K (Fin m))

/-- **EF13 Theorem 8.1 for a set of exponents, without (8.8)**: (8.3), (8.4), (8.9) and
`d_{v₀} = 0` at a common finite place `v₀` suffice. The hypothesis `λ_1(Q) ≤ Q^{-δ}` is replaced
by a nonzero point of height `≤ Q^{-δ}`. -/
theorem exists_intervals_of_fin_eq_zero_family (𝒟 : Set (FormExponent K (Fin m))) (hm : 2 ≤ m)
    {R : ℕ} (hR : #L'.forms ≤ R) (hmR : m ≤ R) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsa : ∀ d ∈ 𝒟, ∀ v, ∑ i, d.arch v i = 0) (hsf : ∀ d ∈ 𝒟, ∀ v, ∑ i, d.fin v i = 0)
    (hsup : ∀ d ∈ 𝒟, (∑ v, ⨆ i, d.arch v i) + ∑ᶠ v, ⨆ i, d.fin v i ≤ 1)
    {v₀ : FinitePlace K} (hv₀ : ∀ d ∈ 𝒟, d.fin v₀ = 0)
    (hU : ∀ d ∈ 𝒟, ∀ U : Submodule Ω (Fin m → Ω), U ≠ ⊤ → L'.subspaceWeight d U ≤ 0)
    {γ : InfinitePlace K ⊕ FinitePlace K → ℝ} (hγc : ∀ d ∈ 𝒟, ∀ v i, d.vec v i ≤ γ v)
    (hγ0 : ∀ v, 0 ≤ γ v) (hγs : (Function.support fun v : FinitePlace K ↦ γ (.inr v)).Finite)
    (hγ : (∑ v, γ (.inl v)) + ∑ᶠ v, γ (.inr v) ≤ 1) (hγ₀ : γ (.inr v₀) = 0)
    (S₁ : Finset (InfinitePlace K ⊕ FinitePlace K)) (hS₁ : ∀ d ∈ 𝒟, ∀ v ∉ S₁, d.vec v = 0)
    (hS₁R : #S₁ ≤ R ^ m) :
    ∃ a : Fin (gapIntervals m R δ) → ℝ, (∀ i, 1 < a i) ∧ ∀ d ∈ 𝒟, ∀ (Q : ℝ) (hQ : 1 < Q),
      Real.exp (gapThreshold m R δ (Real.log L'.absFormHeight)) ≤ Q →
      ∀ y : Fin m → Ω, y ≠ 0 → L'.absMulHeight (d.weight (zero_lt_one.trans hQ)) y ≤ Q ^ (-δ) →
      ∃ i, a i ≤ Q ∧ Q ≤ a i ^ (2 * gapRatio m R δ) := by
  set P := (L'.fin v₀)⁻¹
  have hP := L'.det_inv_fin_ne_zero v₀
  have hu : IsUnit (L'.fin v₀).det := isUnit_iff_ne_zero.2 (L'.fin_det_ne_zero v₀)
  set L₀ := L'.comp P hP
  obtain ⟨a, ha1, ha⟩ := L₀.exists_intervals_family 𝒟
    (fun d hd ↦ L'.isNormalSemistable_comp d (hsa d hd) (hsf d hd) (hsup d hd) (hv₀ d hd)
      (hU d hd)) (v₀ := v₀) (Matrix.mul_nonsing_inv _ hu) hv₀ hγc hγ0 hγs hγ hγ₀ S₁ hS₁ hm
    ((L'.card_forms_comp_le P hP).trans hR) hmR hS₁R hδ hδ1
  refine ⟨a, ha1, fun d hd Q hQ hthr y hy hyQ ↦ ha d hd Q hQ (le_trans ?_ hthr) ?_⟩
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

/-! ### The reduction for a set of exponents -/

section Reduction

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω]
  (L : FormSystem K (Fin n))

/-- **EF13 (18.23) for a set of exponents with one quotient system**: let every `c ∈ 𝒞` have
`Σ_i c_iv = 0` at every place and (2.9), `c_iv ≤ γ_v` with `Σ_v γ_v ≤ 1`, and vanish outside `S₁`,
`#S₁ ≤ Rⁿ`, and let `T` be the destabilizing subspace and `L''` the quotient system for every
`c ∈ 𝒞`. Then the `Q` above the threshold with a point `x ∉ T`,
`H_{L,c,Q}(x) ≤ Δ_L^{1/n} Q^{-δ}` for some `c ∈ 𝒞`, lie in the same intervals as for one exponent
(`exists_intervals_of_splitting`). -/
theorem exists_intervals_of_splitting_family (S : Splitting K n k m)
    (𝒞 : Set (FormExponent K (Fin n))) (hc0 : ∀ c ∈ 𝒞, ∀ v, ∑ i, c.vec v i = 0)
    (hsup : ∀ c ∈ 𝒞, (∑ v, ⨆ i, c.arch v i) + ∑ᶠ v, ⨆ i, c.fin v i ≤ 1)
    {γ : InfinitePlace K ⊕ FinitePlace K → ℝ} (hγc : ∀ c ∈ 𝒞, ∀ v i, c.vec v i ≤ γ v)
    (hγ0 : ∀ v, 0 ≤ γ v) (hγ : (∑ v, γ (.inl v)) + ∑ᶠ v, γ (.inr v) ≤ 1)
    (S₁ : Finset (InfinitePlace K ⊕ FinitePlace K)) (hS₁ : ∀ c ∈ 𝒞, ∀ v ∉ S₁, c.vec v = 0)
    (hγS : ∀ v ∉ S₁, γ v = 0) {R : ℕ} (hR : #L.forms ≤ R) (hS₁R : #S₁ ≤ R ^ n)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {T : Submodule Ω (Fin n → Ω)}
    (hT : ∀ c ∈ 𝒞, Submodule.IsDestabilizing (L.subspaceWeight c) ⊤ T)
    (hST : (Submodule.span K (Set.range S.incl.col)).extendPi Ω = T) (hm : 0 < m)
    (L'' : FormSystem K (Fin m)) (hsys : ∀ c ∈ 𝒞, L.quotSystem S c = L'') :
    ∃ a : Fin (gapIntervals m (R ^ n) (δ / (2 * n))) → ℝ, (∀ i, 1 < a i) ∧ ∀ c ∈ 𝒞,
      ∀ (Q : ℝ) (hQ : 1 ≤ Q), Real.exp (quotThreshold n R δ (Real.log L.absFormHeight)) ≤ Q →
      ∀ x : Fin n → Ω, x ∉ T → L.absMulHeight (c.weight (zero_lt_one.trans_le hQ)) x ≤
        L.absDet ^ ((n : ℝ)⁻¹) * Q ^ (-δ) →
      ∃ i, a i ≤ Q ∧ Q ≤ a i ^ (2 * gapRatio m (R ^ n) (δ / (2 * n))) := by
  classical
  have hkm := S.card_eq
  have hnR := L.le_card_forms.trans hR
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hℓ : 0 ≤ Real.log L.absFormHeight := Real.log_nonneg L.one_le_absFormHeight
  have hterms := terms_le_quotThreshold (R := R) hm (by omega : m ≤ n) hδ hℓ
  have hlog : ∀ Q, Real.exp (quotThreshold n R δ (Real.log L.absFormHeight)) ≤ Q →
      quotThreshold n R δ (Real.log L.absFormHeight) ≤ Real.log Q := fun Q hQ ↦
    (Real.le_log_iff_exp_le ((Real.exp_pos _).trans_le hQ)).2 hQ
  have hproj : ∀ x ∉ T, S.projLin Ω x ≠ 0 := fun x hx h ↦
    hx (by rw [← ker_projLin_eq S hST]; exact h)
  have hcsum : ∀ c ∈ 𝒞, c.sum = 0 := fun c hc ↦ by
    have ha : ∀ v, ∑ i, c.arch v i = 0 := fun v ↦ hc0 c hc (.inl v)
    have hf : ∀ v, ∑ i, c.fin v i = 0 := fun v ↦ hc0 c hc (.inr v)
    simp [FormExponent.sum, ha, hf]
  -- the height on the quotient (EF13 Prop. 18.5)
  have key : ∀ c ∈ 𝒞, ∀ (Q : ℝ) (hQ : 1 ≤ Q),
      Real.exp (quotThreshold n R δ (Real.log L.absFormHeight)) ≤ Q →
      ∀ x : Fin n → Ω, L.absMulHeight (c.weight (zero_lt_one.trans_le hQ)) x ≤
        L.absDet ^ ((n : ℝ)⁻¹) * Q ^ (-δ) →
      (L.quotSystem S c).absMulHeight ((L.quotNormExp S c).weight
        (Real.rpow_pos_of_pos (zero_lt_one.trans_le hQ) ((n : ℝ) / m))) (S.projLin Ω x) ≤
      (Q ^ ((n : ℝ) / m)) ^ (-(δ / (2 * n))) := fun c hc Q hQ hthr x hx ↦
    L.absMulHeight_quotNormExp_le_rpow c S (hcsum c hc) (hT c hc) hST hm hR hδ hQ
      (hterms.2.1.trans (hlog Q hthr)) hx
  rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | hm2
  · refine ⟨fun _ ↦ 2, fun _ ↦ one_lt_two, fun c hc Q hQ hthr x hx hxQ ↦ ?_⟩
    exact (L.false_of_card_eq_one c S (hT c hc) hST hR hδ hQ
      (hterms.2.2.trans_le (hlog Q hthr)) (hproj x hx) (key c hc Q hQ hthr x hxQ)).elim
  rcases 𝒞.eq_empty_or_nonempty with rfl | ⟨c₁, hc₁⟩
  · exact ⟨fun _ ↦ 2, fun _ ↦ one_lt_two, fun c hc ↦ hc.elim⟩
  -- `m ≥ 2`: Theorem 8.1 for `L''` and the normalized exponents `d` of all `c ∈ 𝒞`
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : FinitePlace K, (.inr v₀ : InfinitePlace K ⊕ FinitePlace K) ∉ S₁ :=
    (Set.Finite.preimage Sum.inr_injective.injOn S₁.finite_toSet).infinite_compl.nonempty
  have hγs : (Function.support fun v : FinitePlace K ↦ γ (.inr v)).Finite :=
    (Set.Finite.preimage Sum.inr_injective.injOn S₁.finite_toSet).subset fun v hv ↦
      not_not.1 fun h ↦ hv (hγS _ h)
  have hR'' : #L''.forms ≤ R ^ n := by
    rw [← hsys c₁ hc₁]
    exact (L.card_forms_quotSystem_le S c₁).trans ((Nat.pow_le_pow_left hR _).trans
      (Nat.pow_le_pow_right (by omega) (by omega)))
  have hmR'' : m ≤ R ^ n := (by omega : m ≤ R).trans (Nat.le_self_pow (by omega) R)
  have hδ' : 0 < δ / (2 * n) := by positivity
  have hδ'1 : δ / (2 * n) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    linarith
  have hS₁R' : #S₁ ≤ (R ^ n) ^ m := hS₁R.trans (Nat.le_self_pow (by omega) _)
  obtain ⟨a, ha1, ha⟩ := L''.exists_intervals_of_fin_eq_zero_family
    ((fun c ↦ L.quotNormExp S c) '' 𝒞) hm2 hR'' hmR'' hδ' hδ'1
    (by rintro _ ⟨c, -, rfl⟩; exact L.sum_quotNormExp_arch c S hm)
    (by rintro _ ⟨c, -, rfl⟩; exact L.sum_quotNormExp_fin c S hm)
    (by
      rintro _ ⟨c, hc, rfl⟩
      have := L.sum_iSup_quotNormExp_le S c hm
      rw [hcsum c hc, zero_div, sub_zero] at this
      exact this.trans (hsup c hc))
    (v₀ := v₀) (by rintro _ ⟨c, hc, rfl⟩; exact L.quotNormExp_fin_eq_zero c S (hS₁ c hc _ hv₀))
    (by
      rintro _ ⟨c, hc, rfl⟩ U hU
      rw [← hsys c hc]
      exact L.subspaceWeight_quotNormExp_nonpos S c hm (by rw [ker_projLin_eq S hST]; exact hT c hc)
        hU)
    (γ := γ)
    (by
      rintro _ ⟨c, hc, rfl⟩ v t
      exact (quotNormExp_vec_le S L c hm (hc0 c hc v) t).trans (ciSup_le (hγc c hc v)))
    hγ0 hγs hγ (hγS _ hv₀) S₁
    (by rintro _ ⟨c, hc, rfl⟩ v hv; exact quotNormExp_vec_eq_zero S L c (hS₁ c hc v hv)) hS₁R'
  have hmn : (0 : ℝ) < (m : ℝ) / n := by
    have : (0 : ℝ) < m := Nat.cast_pos.2 hm
    positivity
  refine ⟨fun i ↦ a i ^ ((m : ℝ) / n), fun i ↦ Real.one_lt_rpow (ha1 i) hmn,
    fun c hc Q hQ hthr x hx hxQ ↦ ?_⟩
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
  have hH'' := L.log_absFormHeight_quotSystem_le c S (hT c hc) hST hm hR
  rw [hsys c hc] at hH''
  have hkey := key c hc Q hQ hthr x hxQ
  rw [hsys c hc] at hkey
  obtain ⟨i, h1, h2⟩ := ha _ ⟨c, hc, rfl⟩ Q' hQ' (by
      rw [← Real.exp_log (zero_lt_one.trans hQ')]
      refine Real.exp_le_exp.2 (le_trans ?_ (hterms.1.trans (hlQ.trans hQQ')))
      exact gapThreshold_mono (by omega) hδ' hH'')
    (S.projLin Ω x) (hproj x hx) hkey
  refine ⟨i, ?_, ?_⟩
  · rw [← hQ'Q]
    exact Real.rpow_le_rpow (zero_lt_one.trans (ha1 i)).le h1 hmn.le
  · rw [← hQ'Q, ← Real.rpow_mul (zero_lt_one.trans (ha1 i)).le, mul_comm,
      Real.rpow_mul (zero_lt_one.trans (ha1 i)).le]
    exact Real.rpow_le_rpow (zero_lt_one.trans hQ').le h2 hmn.le

/-- **EF13 Theorem 2.3 for a set of exponents with one destabilizing subspace `T`**: grouping `𝒞`
by the rows selected at the places of `S₁`, the `Q ≥ C₀` with a point `x ∉ T`,
`H_{L,c,Q}(x) ≤ Δ_L^{1/n} Q^{-δ}` for some `c ∈ 𝒞`, lie in at most
`(nⁿ)^{#S₁} intervalCount n R δ` intervals `[b, b^{ω₀})`. -/
theorem exists_intervals_cover_of_isDestabilizing_family (hn : 2 ≤ n)
    (𝒞 : Set (FormExponent K (Fin n))) (hc0 : ∀ c ∈ 𝒞, ∀ v, ∑ i, c.vec v i = 0)
    (hsup : ∀ c ∈ 𝒞, (∑ v, ⨆ i, c.arch v i) + ∑ᶠ v, ⨆ i, c.fin v i ≤ 1)
    {γ : InfinitePlace K ⊕ FinitePlace K → ℝ} (hγc : ∀ c ∈ 𝒞, ∀ v i, c.vec v i ≤ γ v)
    (hγ0 : ∀ v, 0 ≤ γ v) (hγ : (∑ v, γ (.inl v)) + ∑ᶠ v, γ (.inr v) ≤ 1)
    (S₁ : Finset (InfinitePlace K ⊕ FinitePlace K)) (hS₁ : ∀ c ∈ 𝒞, ∀ v ∉ S₁, c.vec v = 0)
    (hγS : ∀ v ∉ S₁, γ v = 0) {R : ℕ} (hR : #L.forms ≤ R) (hS₁R : #S₁ ≤ R ^ n)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {T : Submodule Ω (Fin n → Ω)}
    (hT : ∀ c ∈ 𝒞, Submodule.IsDestabilizing (L.subspaceWeight c) ⊤ T) :
    ∃ s : Finset ℝ, #s ≤ (n ^ n) ^ #S₁ * intervalCount n R δ ∧
      (∀ b ∈ s, max (L.absFormHeight ^ ((R : ℝ)⁻¹)) ((n : ℝ) ^ δ⁻¹) ≤ b) ∧
      ∀ c ∈ 𝒞, ∀ (Q : ℝ) (hQ : 1 ≤ Q), max (L.absFormHeight ^ ((R : ℝ)⁻¹)) ((n : ℝ) ^ δ⁻¹) ≤ Q →
      ∀ x : Fin n → Ω, x ∉ T → L.absMulHeight (c.weight (zero_lt_one.trans_le hQ)) x ≤
        L.absDet ^ ((n : ℝ)⁻¹) * Q ^ (-δ) →
      ∃ b ∈ s, b ≤ Q ∧ Q < b ^ cutRatio R δ := by
  classical
  rcases 𝒞.eq_empty_or_nonempty with rfl | ⟨c₁, hc₁⟩
  · exact ⟨∅, by simp, by simp, fun c hc ↦ hc.elim⟩
  obtain ⟨S, hS⟩ := Splitting.exists_range_inclLin
    (L.isDefinedOver_of_isDestabilizing c₁ (hT c₁ hc₁) Submodule.isDefinedOver_top)
  have hST := (range_inclLin_eq_extendPi S).symm.trans hS
  have hm : 0 < n - finrank Ω T := by
    have := Submodule.finrank_lt (hT c₁ hc₁).lt.ne
    rw [Module.finrank_fin_fun] at this
    omega
  set key : FormExponent K (Fin n) → S₁ → (Fin (finrank Ω T) ↪ Fin n) :=
    fun c v ↦ S.sel (L.mat v.1) (c.vec v.1) with hkey
  have hσ : ∀ σ : S₁ → (Fin (finrank Ω T) ↪ Fin n), ∃ s : Finset ℝ,
      #s ≤ intervalCount n R δ ∧
      (∀ b ∈ s, max (L.absFormHeight ^ ((R : ℝ)⁻¹)) ((n : ℝ) ^ δ⁻¹) ≤ b) ∧
      ∀ c ∈ 𝒞, key c = σ → ∀ (Q : ℝ) (hQ : 1 ≤ Q),
        max (L.absFormHeight ^ ((R : ℝ)⁻¹)) ((n : ℝ) ^ δ⁻¹) ≤ Q →
        ∀ x : Fin n → Ω, x ∉ T → L.absMulHeight (c.weight (zero_lt_one.trans_le hQ)) x ≤
          L.absDet ^ ((n : ℝ)⁻¹) * Q ^ (-δ) →
        ∃ b ∈ s, b ≤ Q ∧ Q < b ^ cutRatio R δ := by
    intro σ
    set 𝒞σ : Set (FormExponent K (Fin n)) := {c | c ∈ 𝒞 ∧ key c = σ} with h𝒞σ
    rcases 𝒞σ.eq_empty_or_nonempty with h | ⟨c₀, hc₀, hc₀σ⟩
    · refine ⟨∅, by simp, by simp, fun c hc hcσ ↦ ?_⟩
      have : c ∈ 𝒞σ := ⟨hc, hcσ⟩
      rw [h] at this
      exact this.elim
    have hsys : ∀ c ∈ 𝒞σ, L.quotSystem S c = L.quotSystem S c₀ := by
      rintro c ⟨hc, hcσ⟩
      refine quotSystem_congr S L fun v ↦ ?_
      by_cases hv : v ∈ S₁
      · exact (congrFun hcσ ⟨v, hv⟩).trans (congrFun hc₀σ ⟨v, hv⟩).symm
      · rw [hS₁ c hc v hv, hS₁ c₀ hc₀ v hv]
    obtain ⟨a, ha1, ha⟩ := L.exists_intervals_of_splitting_family S 𝒞σ (fun c hc ↦ hc0 c hc.1)
      (fun c hc ↦ hsup c hc.1) (fun c hc ↦ hγc c hc.1) hγ0 hγ S₁ (fun c hc ↦ hS₁ c hc.1) hγS hR
      hS₁R hδ hδ1 (fun c hc ↦ hT c hc.1) hST hm _ hsys
    obtain ⟨s, hs, hsge, hsQ⟩ := L.exists_cover_of_intervals hn hR hδ hδ1 hm (by omega)
      (fun Q hQ ↦ ∃ c ∈ 𝒞σ, ∃ x : Fin n → Ω, x ∉ T ∧
        L.absMulHeight (c.weight (zero_lt_one.trans_le hQ)) x ≤ L.absDet ^ ((n : ℝ)⁻¹) * Q ^ (-δ))
      a ha1 fun Q hQ hΘ ⟨c, hc, x, hx, hxQ⟩ ↦ ha c hc Q hQ hΘ x hx hxQ
    exact ⟨s, hs, hsge, fun c hc hcσ Q hQ hC₀Q x hx hxQ ↦
      hsQ Q hQ hC₀Q ⟨c, ⟨hc, hcσ⟩, x, hx, hxQ⟩⟩
  choose s hs hsge hsQ using hσ
  have hTn : finrank Ω T ≤ n := (Submodule.finrank_le T).trans_eq (Module.finrank_fin_fun Ω)
  refine ⟨univ.biUnion s, ?_, ?_, fun c hc Q hQ hC₀Q x hx hxQ ↦ ?_⟩
  · calc #(univ.biUnion s) ≤ ∑ σ, #(s σ) := card_biUnion_le
      _ ≤ ∑ _σ : S₁ → (Fin (finrank Ω T) ↪ Fin n), intervalCount n R δ :=
          sum_le_sum fun σ _ ↦ hs σ
      _ = Fintype.card (S₁ → (Fin (finrank Ω T) ↪ Fin n)) * intervalCount n R δ := by
          rw [sum_const, card_univ, smul_eq_mul]
      _ ≤ (n ^ n) ^ #S₁ * intervalCount n R δ := by
          refine Nat.mul_le_mul_right _ ?_
          rw [Fintype.card_fun, Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin,
            Fintype.card_coe]
          exact Nat.pow_le_pow_left ((Nat.descFactorial_le_pow _ _).trans
            (Nat.pow_le_pow_right (by omega) hTn)) _
  · intro b hb
    obtain ⟨σ, -, hb⟩ := mem_biUnion.1 hb
    exact hsge σ b hb
  · obtain ⟨b, hb, h⟩ := hsQ (key c) c hc rfl Q hQ hC₀Q x hx hxQ
    exact ⟨b, mem_biUnion.2 ⟨key c, mem_univ _, hb⟩, h⟩

/-- **EF13 Theorem 2.3 for a set of exponents.** Let `n ≥ 2`, `L` with at most `R` distinct forms,
and `𝒞` a set of exponents `c` with `Σ_i c_iv = 0` at every place and (2.9), with a common bound
`c_iv ≤ γ_v`, `Σ_v γ_v ≤ 1`, all vanishing outside a set `S₁` of at most `Rⁿ` places. Then there
are at most `J = (n + 1) (2^{2ⁿ})^{#S₁}` proper subspaces `T` and at most
`J (nⁿ)^{#S₁} intervalCount n R δ` reals `b ≥ C₀ = max(H_L^{1/R}, n^{1/δ})` such that for every
`c ∈ 𝒞` the destabilizing subspace `T(L, c)` is one of the `T`, and every `Q ≥ C₀` with a point
`x ∉ T(L, c)`, `H_{L,c,Q}(x) ≤ Δ_L^{1/n} Q^{-δ}`, lies in one of the intervals `[b, b^{ω₀})`,
`ω₀ = δ⁻¹ log 3R`. Neither count depends on `𝒞`. -/
theorem exists_intervals_cover_family (hn : 2 ≤ n) (𝒞 : Set (FormExponent K (Fin n)))
    (hc0 : ∀ c ∈ 𝒞, ∀ v, ∑ i, c.vec v i = 0)
    (hsup : ∀ c ∈ 𝒞, (∑ v, ⨆ i, c.arch v i) + ∑ᶠ v, ⨆ i, c.fin v i ≤ 1)
    {γ : InfinitePlace K ⊕ FinitePlace K → ℝ} (hγc : ∀ c ∈ 𝒞, ∀ v i, c.vec v i ≤ γ v)
    (hγ0 : ∀ v, 0 ≤ γ v) (hγ : (∑ v, γ (.inl v)) + ∑ᶠ v, γ (.inr v) ≤ 1)
    (S₁ : Finset (InfinitePlace K ⊕ FinitePlace K)) (hS₁ : ∀ c ∈ 𝒞, ∀ v ∉ S₁, c.vec v = 0)
    (hγS : ∀ v ∉ S₁, γ v = 0) {R : ℕ} (hR : #L.forms ≤ R) (hS₁R : #S₁ ≤ R ^ n)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ 𝒯 : Finset (Submodule Ω (Fin n → Ω)), #𝒯 ≤ (n + 1) * (2 ^ 2 ^ n) ^ #S₁ ∧
      (∀ T ∈ 𝒯, T ≠ ⊤) ∧ ∃ s : Finset ℝ,
        #s ≤ (n + 1) * (2 ^ 2 ^ n) ^ #S₁ * ((n ^ n) ^ #S₁ * intervalCount n R δ) ∧
        (∀ b ∈ s, max (L.absFormHeight ^ ((R : ℝ)⁻¹)) ((n : ℝ) ^ δ⁻¹) ≤ b) ∧
        ∀ c ∈ 𝒞, ∃ T ∈ 𝒯, Submodule.IsDestabilizing (L.subspaceWeight c) ⊤ T ∧
          ∀ (Q : ℝ) (hQ : 1 ≤ Q), max (L.absFormHeight ^ ((R : ℝ)⁻¹)) ((n : ℝ) ^ δ⁻¹) ≤ Q →
          ∀ x : Fin n → Ω, x ∉ T → L.absMulHeight (c.weight (zero_lt_one.trans_le hQ)) x ≤
            L.absDet ^ ((n : ℝ)⁻¹) * Q ^ (-δ) →
          ∃ b ∈ s, b ≤ Q ∧ Q < b ^ cutRatio R δ := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨𝒯, h𝒯, h𝒯mem⟩ := exists_finset_isDestabilizing (L := L) (Ω := Ω) (S₁ := S₁) 𝒞 hS₁
  have hT : ∀ T : Submodule Ω (Fin n → Ω), ∃ s : Finset ℝ,
      #s ≤ (n ^ n) ^ #S₁ * intervalCount n R δ ∧
      (∀ b ∈ s, max (L.absFormHeight ^ ((R : ℝ)⁻¹)) ((n : ℝ) ^ δ⁻¹) ≤ b) ∧
      ∀ c ∈ 𝒞, Submodule.IsDestabilizing (L.subspaceWeight c) ⊤ T → ∀ (Q : ℝ) (hQ : 1 ≤ Q),
        max (L.absFormHeight ^ ((R : ℝ)⁻¹)) ((n : ℝ) ^ δ⁻¹) ≤ Q →
        ∀ x : Fin n → Ω, x ∉ T → L.absMulHeight (c.weight (zero_lt_one.trans_le hQ)) x ≤
          L.absDet ^ ((n : ℝ)⁻¹) * Q ^ (-δ) →
        ∃ b ∈ s, b ≤ Q ∧ Q < b ^ cutRatio R δ := by
    intro T
    obtain ⟨s, hs, hsge, hsQ⟩ := L.exists_intervals_cover_of_isDestabilizing_family hn
      {c | c ∈ 𝒞 ∧ Submodule.IsDestabilizing (L.subspaceWeight c) ⊤ T}
      (fun c hc ↦ hc0 c hc.1) (fun c hc ↦ hsup c hc.1) (fun c hc ↦ hγc c hc.1) hγ0 hγ S₁
      (fun c hc ↦ hS₁ c hc.1) hγS hR hS₁R hδ hδ1 (fun c hc ↦ hc.2)
    exact ⟨s, hs, hsge, fun c hc hcT ↦ hsQ c ⟨hc, hcT⟩⟩
  choose s hs hsge hsQ using hT
  refine ⟨𝒯.filter (· ≠ ⊤), (card_filter_le _ _).trans h𝒯, fun T hT ↦ (mem_filter.1 hT).2,
    𝒯.biUnion s, ?_, ?_, fun c hc ↦ ?_⟩
  · calc #(𝒯.biUnion s) ≤ ∑ T ∈ 𝒯, #(s T) := card_biUnion_le
      _ ≤ ∑ _T ∈ 𝒯, (n ^ n) ^ #S₁ * intervalCount n R δ := sum_le_sum fun T _ ↦ hs T
      _ = #𝒯 * ((n ^ n) ^ #S₁ * intervalCount n R δ) := by rw [sum_const, smul_eq_mul]
      _ ≤ _ := Nat.mul_le_mul_right _ h𝒯
  · intro b hb
    obtain ⟨T, -, hb⟩ := mem_biUnion.1 hb
    exact hsge T b hb
  · obtain ⟨T, hTd, -⟩ := L.exists_isDestabilizing_top (Ω := Ω) c
    refine ⟨T, mem_filter.2 ⟨h𝒯mem c hc T hTd, hTd.lt.ne⟩, hTd, fun Q hQ hC₀Q x hx hxQ ↦ ?_⟩
    obtain ⟨b, hb, h⟩ := hsQ T c hc hTd Q hQ hC₀Q x hx hxQ
    exact ⟨b, mem_biUnion.2 ⟨T, h𝒯mem c hc T hTd, hb⟩, h⟩

end Reduction

end NumberField.FormSystem
