/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.FormSemistable

/-!
# The successive infima of a twisted height as `Q → ∞`

J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative Subspace Theorem*,
Ann. of Math. **177** (2013), 513–590, Theorem 16.1.

Let `0 = T_0 < T_1 < ⋯ < T_r = Ωⁿ` be the filtration of `(L, c)` (EF13 Lemma 15.4), `d_l = dim T_l`
and `μ_l = μ(T_l, T_{l-1})`. EF13 Theorem 16.1: for every `δ > 0` and `Q` large,

```text
Q^{-μ_l - δ} ≤ λ_i(Q) ≤ Q^{-μ_l + δ}   (d_{l-1} < i ≤ d_l),     (16.2)
T_{d_l}(Q) = T_l.                                                (16.3)
```

The proof is EF13's induction on the length of the filtration, done here as an induction on `n`:
the system `(L', c')` induced on `T_{r-1}` carries the filtration `T_0 < ⋯ < T_{r-1}`
(Lemma 16.2 (i)), and the system `(L'', c'')` on `Ωⁿ / T_{r-1}` is semistable (Lemma 16.2 (ii)),
so EF13 Lemma 16.4 bounds `H_{L,c,Q}` from below off `T_{r-1}` (Lemma 16.3 (ii)). The last
infimum is bounded above through Minkowski's theorem (EF13 Prop. 9.2), applied to `L` and, for
the lower bound of the product of the first `d_{r-1}` infima, to `L'`.

Lemma 16.4 rests on EF13 Theorem 8.1 (Q4.1). It enters as the hypothesis
`NumberField.SemistableGap K Ω`.

## Main definitions

* `NumberField.FormSystem.qHeight L c Q`: `H_{L,c,max(Q,1)}`, a height for every real `Q`.

## Main results

* `NumberField.FormSystem.eventually_successiveInf`: EF13 Theorem 16.1.

## Implementation notes

The induction proves, for every `δ > 0` and eventually in `Q`, three statements about the
filtration: the upper bounds `λ_i ≤ Q^{-μ_l + δ}` for `i ≤ d_l`, the lower bounds
`λ_i ≥ Q^{-μ_l - δ}` for `i > d_{l-1}`, and the stability `T(λ) = T_l` for
`Q^{-μ_l + δ} ≤ λ ≤ Q^{-μ_{l+1} - δ}`. The last statement replaces (16.16): it transfers through
`φ'` up to the constants of Lemma 16.3 (i), and gives (16.3) at the end.

This is milestone Q3.5 of `QuantitativeSubspace/README.md`.
-/

@[expose] public section

open Module Finset Matrix Filter Submodule

namespace Submodule.IsWeightFiltration

variable {k M M' : Type*} [Field k] [AddCommGroup M] [Module k M] [AddCommGroup M']
  [Module k M'] {w : Submodule k M → ℝ} {w' : Submodule k M' → ℝ} {V : Submodule k M} {r : ℕ}
  {T : ℕ → Submodule k M}

/-- **Transport of a filtration** to the source of an injective map onto `V`. -/
theorem comap_of_injective (h : IsWeightFiltration w V r T) (φ : M' →ₗ[k] M)
    (hφ : Function.Injective φ) (hV : LinearMap.range φ = V) (hw : ∀ U, w' U = w (U.map φ)) :
    IsWeightFiltration w' ⊤ r fun l ↦ (T l).comap φ := by
  have hmap : ∀ l ≤ r, ((T l).comap φ).map φ = T l := fun l hl ↦ by
    rw [map_comap_eq, hV, inf_eq_right.2 (h.le_top hl)]
  have hfr : ∀ U : Submodule k M', finrank k (U.map φ) = finrank k U := fun U ↦
    (Submodule.equivMapOfInjective φ hφ U).finrank_eq.symm
  have hs : ∀ l l', l ≤ r → l' ≤ r → weightSlope w' ((T l).comap φ) ((T l').comap φ) =
      weightSlope w (T l) (T l') := fun l l' hl hl' ↦ by
    simp only [weightSlope, hw, ← hfr ((T l).comap φ), ← hfr ((T l').comap φ)]
    rw [hmap l hl, hmap l' hl']
  refine ⟨?_, ?_, fun l hl ↦ ?_, fun l hl ↦ ?_, fun l hl U _ ↦ ?_⟩
  · rw [h.zero, comap_bot, LinearMap.ker_eq_bot.2 hφ]
  · refine eq_top_iff.2 fun x _ ↦ ?_
    rw [mem_comap, h.top, ← hV]
    exact LinearMap.mem_range_self φ x
  · refine lt_of_le_of_ne (comap_mono (h.lt l hl).le) fun he ↦ (h.lt l hl).ne ?_
    simpa [hmap l hl.le, hmap (l + 1) hl] using congrArg (Submodule.map φ) he
  · rw [hs _ _ (by omega) (by omega), hs _ _ (by omega) (by omega)]
    exact h.slope_lt l hl
  · rw [hs _ _ hl.le (by omega), hw U, hw ((T l).comap φ), ← hfr U, ← hfr ((T l).comap φ),
      hmap l hl.le]
    exact h.le l hl _ (by rw [← hV]; exact LinearMap.map_le_range)

end Submodule.IsWeightFiltration

namespace NumberField

/-! ### Successive infima under injective maps -/

section Infima

variable {Ω : Type*} [Field Ω] {k n : ℕ}

theorem heightSpace_mono_of_le {h₁ h₂ : (Fin n → Ω) → ℝ} (hle : ∀ x, h₂ x ≤ h₁ x) (lam : ℝ) :
    heightSpace Ω h₁ lam ≤ heightSpace Ω h₂ lam :=
  span_mono fun x (hx : h₁ x ≤ lam) ↦ (hle x).trans hx

/-- Points of height below `θ` off `W` give `T(λ) ≤ W` for `λ < θ`. -/
theorem heightSpace_le_of_forall_notMem {h : (Fin n → Ω) → ℝ} {W : Submodule Ω (Fin n → Ω)}
    {θ : ℝ} (hW : ∀ x ∉ W, θ ≤ h x) {lam : ℝ} (hlam : lam < θ) : heightSpace Ω h lam ≤ W :=
  span_le.2 fun x (hx : h x ≤ lam) ↦ by
    by_contra hxW
    exact (hlam.trans_le (hW x hxW)).not_ge hx

/-- **`λ_i ≥ θ` for `i > dim W`** if every point off `W` has height at least `θ`. -/
theorem le_heightInf_of_forall_notMem {h : (Fin n → Ω) → ℝ} {W : Submodule Ω (Fin n → Ω)}
    {θ : ℝ} (hW : ∀ x ∉ W, θ ≤ h x) {i : ℕ} (hi : finrank Ω W < i) (hin : i ≤ n) :
    θ ≤ heightInf Ω h i := by
  by_contra hlt
  push Not at hlt
  obtain ⟨mu, h₁, h₂⟩ := exists_between hlt
  have := le_finrank_heightSpace (h := h) (by simpa using hin) h₁
  have h3 := Submodule.finrank_mono (heightSpace_le_of_forall_notMem hW h₂)
  omega

variable (φ : (Fin k → Ω) →ₗ[Ω] (Fin n → Ω))

/-- `h₁ ∘ φ ≤ C h₂` gives `λ_i(h₁) ≤ C λ_i(h₂)` for an injective `φ`. -/
theorem heightInf_le_mul_of_comp (hφ : Function.Injective φ) {h₁ : (Fin n → Ω) → ℝ}
    {h₂ : (Fin k → Ω) → ℝ} {C : ℝ} (hC : 0 < C) (hle : ∀ y, h₁ (φ y) ≤ C * h₂ y) {i : ℕ}
    (hi : i ≤ k) : heightInf Ω h₁ i ≤ C * heightInf Ω h₂ i := by
  rw [← div_le_iff₀' hC]
  refine le_of_forall_gt_imp_ge_of_dense fun mu hmu ↦ ?_
  obtain ⟨y, hy, hyle⟩ := exists_linearIndependent_of_heightInf_lt (h := h₂) (by simpa using hi)
    hmu
  rw [div_le_iff₀' hC]
  exact heightInf_le_of_linearIndependent (hy.map' φ (LinearMap.ker_eq_bot.2 hφ))
    (mul_nonneg hC.le ((heightInf_nonneg _).trans hmu.le))
    fun j ↦ (hle (y j)).trans (mul_le_mul_of_nonneg_left (hyle j) hC.le)

/-- `λ_i(h') ≤ C λ_i(h)` for `h' ≤ C h ∘ φ`, `φ` injective onto `W`, if `λ_i(h)` is below a bound
`θ` for the heights off `W`. -/
theorem heightInf_le_mul_of_lt {W : Submodule Ω (Fin n → Ω)}
    (hW : LinearMap.range φ = W) {h : (Fin n → Ω) → ℝ} {h' : (Fin k → Ω) → ℝ} {C θ : ℝ}
    (hC : 0 < C) (hle : ∀ y, h' y ≤ C * h (φ y)) (hθ : ∀ x ∉ W, θ ≤ h x) {i : ℕ}
    (hin : i ≤ n) (hlt : heightInf Ω h i < θ) : heightInf Ω h' i ≤ C * heightInf Ω h i := by
  have key : ∀ mu, heightInf Ω h i < mu → mu < θ → heightInf Ω h' i ≤ C * mu := by
    intro mu h₁ h₂
    obtain ⟨x, hx, hxle⟩ := exists_linearIndependent_of_heightInf_lt (h := h) (by simpa using hin)
      h₁
    have hmem : ∀ j, x j ∈ LinearMap.range φ := fun j ↦ by
      rw [hW]
      by_contra hj
      exact ((h₂.trans_le (hθ _ hj)).trans_le (hxle j)).false
    choose y hy using hmem
    have hy' : φ ∘ y = x := funext hy
    have hyli : LinearIndependent Ω y := LinearIndependent.of_comp φ (hy' ▸ hx)
    refine heightInf_le_of_linearIndependent hyli (mul_nonneg hC.le
      ((heightInf_nonneg _).trans h₁.le)) fun j ↦ (hle (y j)).trans ?_
    rw [hy j]
    exact mul_le_mul_of_nonneg_left (hxle j) hC.le
  by_contra hcon
  push Not at hcon
  obtain ⟨mu, h₁, h₂⟩ := exists_between (lt_min hlt ((lt_div_iff₀' hC).2 hcon))
  have := key mu h₁ (h₂.trans_le (min_le_left _ _))
  have h3 := (lt_div_iff₀' hC).1 (h₂.trans_le (min_le_right _ _))
  linarith

/-- `T_h(λ) ≤ φ(T_{h'}(C λ))` for `h' ≤ C h ∘ φ`, `φ` onto `W`, if `λ` is below a bound for the
heights off `W`. -/
theorem heightSpace_le_map {W : Submodule Ω (Fin n → Ω)} (hW : LinearMap.range φ = W)
    {h : (Fin n → Ω) → ℝ} {h' : (Fin k → Ω) → ℝ} {C θ : ℝ} (hC : 0 < C)
    (hle : ∀ y, h' y ≤ C * h (φ y)) (hθ : ∀ x ∉ W, θ ≤ h x) {lam : ℝ} (hlam : lam < θ) :
    heightSpace Ω h lam ≤ (heightSpace Ω h' (C * lam)).map φ := by
  refine span_le.2 fun x (hx : h x ≤ lam) ↦ ?_
  have hxW : x ∈ LinearMap.range φ := by
    rw [hW]
    by_contra hj
    exact ((hlam.trans_le (hθ _ hj)).trans_le hx).false
  obtain ⟨y, rfl⟩ := hxW
  exact ⟨y, mem_heightSpace ((hle y).trans (mul_le_mul_of_nonneg_left hx hC.le)), rfl⟩

/-- `φ(T_{h'}(λ)) ≤ T_h(C λ)` for `h ∘ φ ≤ C h'`. -/
theorem map_heightSpace_le {h : (Fin n → Ω) → ℝ} {h' : (Fin k → Ω) → ℝ} {C : ℝ} (hC : 0 < C)
    (hle : ∀ y, h (φ y) ≤ C * h' y) (lam : ℝ) :
    (heightSpace Ω h' lam).map φ ≤ heightSpace Ω h (C * lam) := by
  rw [heightSpace, map_span, span_le]
  rintro _ ⟨y, hy, rfl⟩
  exact mem_heightSpace ((hle y).trans (mul_le_mul_of_nonneg_left hy hC.le))

omit φ in
theorem heightInf_zero (h : (Fin n → Ω) → ℝ) : heightInf Ω h 0 = 0 := by
  simp only [heightInf, zero_le, and_true]
  exact csInf_Ici

omit φ in
/-- `T(λ) = Ωⁿ` beyond the last infimum. -/
theorem heightSpace_eq_top {h : (Fin n → Ω) → ℝ} {lam : ℝ} (hlt : heightInf Ω h n < lam) :
    heightSpace Ω h lam = ⊤ := by
  refine Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) ?_)
  have := le_finrank_heightSpace (h := h) (by simp) hlt
  simpa using this

end Infima

/-! ### Eventual inequalities -/

/-- `C Q^a ≤ Q^b` for `Q` large, if `a < b`. -/
theorem eventually_mul_rpow_le (C : ℝ) {a b : ℝ} (hab : a < b) :
    ∀ᶠ Q : ℝ in atTop, C * Q ^ a ≤ Q ^ b := by
  filter_upwards [(tendsto_rpow_atTop (sub_pos.2 hab)).eventually_ge_atTop C,
    eventually_gt_atTop 0] with Q hQ hQ0
  calc C * Q ^ a ≤ Q ^ (b - a) * Q ^ a :=
        mul_le_mul_of_nonneg_right hQ (Real.rpow_pos_of_pos hQ0 _).le
    _ = Q ^ b := by rw [← Real.rpow_add hQ0]; ring_nf

/-- The top infimum from a lower bound for the others (pure arithmetic): if
`λ P ≤ C₀ Q^{-α}`, `P ≥ D Q^{-β} θ^N`, `θ = Q^{-μ-ε} / C₃` and `α - β = (N + 1) μ`, then
`λ ≤ (C₀ C₃^N / D) Q^{-μ + N ε}`. -/
theorem le_of_mul_le_of_le {lam P C₀ D C₃ Q α β μ ε : ℝ} {N : ℕ} (hQ : 0 < Q) (hD : 0 < D)
    (hC₃ : 0 < C₃) (hlam : 0 ≤ lam) (h1 : P * lam ≤ C₀ * Q ^ (-α))
    (h2 : D * Q ^ (-β) * (Q ^ (-μ - ε) / C₃) ^ N ≤ P) (hαβ : α - β = (N + 1) * μ) :
    lam ≤ C₀ * C₃ ^ N / D * Q ^ (-μ + N * ε) := by
  have hθ : (Q ^ (-μ - ε) / C₃) ^ N = Q ^ (-(N * (μ + ε))) / C₃ ^ N := by
    rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hQ.le]
    ring_nf
  rw [hθ] at h2
  have hpos : 0 < D * Q ^ (-β) * (Q ^ (-(N * (μ + ε))) / C₃ ^ N) := by positivity
  have h3 : D * Q ^ (-β) * (Q ^ (-(N * (μ + ε))) / C₃ ^ N) * lam ≤ C₀ * Q ^ (-α) :=
    (mul_le_mul_of_nonneg_right h2 hlam).trans h1
  rw [← le_div_iff₀' hpos] at h3
  refine h3.trans (le_of_eq ?_)
  have hexp : Q ^ (-μ + N * ε) = Q ^ (-α) / (Q ^ (-β) * Q ^ (-(N * (μ + ε)))) := by
    rw [← Real.rpow_add hQ, ← Real.rpow_sub hQ]
    congr 1
    linear_combination hαβ
  rw [hexp]
  field_simp

namespace FormSystem

variable {K : Type*} [Field K] [NumberField K] {Ω : Type*} [Field Ω] [Algebra K Ω]
  [Algebra.IsAlgebraic K Ω]

/-- **`H_{L,c,Q}` for every real `Q`**, with `Q` replaced by `max Q 1`. -/
noncomputable def qHeight {ι : Type*} [Fintype ι] [DecidableEq ι] (L : FormSystem K ι)
    (c : FormExponent K ι) (Q : ℝ) (x : ι → Ω) : ℝ :=
  L.absMulHeight (c.weight (zero_lt_one.trans_le (le_max_right Q 1))) x

theorem qHeight_of_one_le {ι : Type*} [Fintype ι] [DecidableEq ι] (L : FormSystem K ι)
    (c : FormExponent K ι) {Q : ℝ} (hQ : 1 ≤ Q) :
    L.qHeight (Ω := Ω) c Q = L.absMulHeight (c.weight (zero_lt_one.trans_le hQ)) := by
  funext x
  rw [qHeight, c.weight_congr (max_eq_left hQ)]

/-- **EF13 Prop. 9.2, upper bound**, for `qHeight`: `(λ₁ ⋯ λ_m) λ_{m+1} ≤ C₀ Q^{-α}`. -/
theorem prod_heightInf_le [IsAlgClosed Ω] {m : ℕ} (L : FormSystem K (Fin (m + 1)))
    (c : FormExponent K (Fin (m + 1))) {Q : ℝ} (hQ : 1 ≤ Q) :
    (∏ i ∈ range m, heightInf Ω (L.qHeight c Q) (i + 1)) * heightInf Ω (L.qHeight c Q) (m + 1) ≤
      √2 ^ ((m + 1) * m) * (L.absDet * Q ^ (-c.sum)) := by
  have h := L.prod_successiveInf_weight_le (Ω := Ω) (Nat.succ_pos m) c (zero_lt_one.trans_le hQ)
  rw [Fin.prod_univ_castSucc] at h
  simp only [successiveInf, Fin.val_castSucc, Fin.val_last, Nat.add_sub_cancel] at h
  rw [qHeight_of_one_le L c hQ, ← Fin.prod_univ_eq_prod_range (fun i ↦ heightInf Ω
    (L.absMulHeight (c.weight (zero_lt_one.trans_le hQ))) (i + 1)) m]
  exact h

theorem prod_heightInf_le' [IsAlgClosed Ω] {n m : ℕ} (hn : n = m + 1) (L : FormSystem K (Fin n))
    (c : FormExponent K (Fin n)) {Q : ℝ} (hQ : 1 ≤ Q) :
    (∏ i ∈ range m, heightInf Ω (L.qHeight c Q) (i + 1)) * heightInf Ω (L.qHeight c Q) n ≤
      √2 ^ (n * m) * L.absDet * Q ^ (-c.sum) := by
  subst hn
  rw [mul_assoc]
  exact prod_heightInf_le L c hQ

/-- **EF13 Prop. 9.2, lower bound**, for `qHeight`: `λ₁ ⋯ λ_k ≥ B Q^{-α}`. -/
theorem exists_le_prod_heightInf [IsAlgClosed Ω] {k : ℕ} (L : FormSystem K (Fin k))
    (c : FormExponent K (Fin k)) :
    ∃ B, 0 < B ∧ ∀ (Q : ℝ), 1 ≤ Q →
      B * Q ^ (-c.sum) ≤ ∏ i ∈ range k, heightInf Ω (L.qHeight c Q) (i + 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨1, one_pos, fun Q _ ↦ ?_⟩
    simp [FormExponent.sum]
  refine ⟨(√k ^ k)⁻¹ * L.absDet, mul_pos (inv_pos.2 (pow_pos (Real.sqrt_pos.2
    (Nat.cast_pos.2 hk)) _)) L.absDet_pos, fun Q hQ ↦ ?_⟩
  have h := L.le_prod_successiveInf_weight (Ω := Ω) hk c (zero_lt_one.trans_le hQ)
  rw [qHeight_of_one_le L c hQ, ← Fin.prod_univ_eq_prod_range (fun i ↦ heightInf Ω
    (L.absMulHeight (c.weight (zero_lt_one.trans_le hQ))) (i + 1)) k, mul_assoc]
  exact h

variable {n : ℕ} (L : FormSystem K (Fin n)) (c : FormExponent K (Fin n))

/-- The bounds of EF13 Theorem 16.1 for the filtration `T` of length `r`, at `δ` and `Q`:
the upper bounds `λ_i ≤ Q^{-μ_l + δ}` (`i ≤ d_{l+1}`), the lower bounds `λ_i ≥ Q^{-μ_l - δ}`
(`i > d_l`), and `T(λ) = T_{l+1}` for `Q^{-μ_l + δ} ≤ λ ≤ Q^{-μ_{l+1} - δ}`, with
`μ_l = μ(T_{l+1}, T_l)` (`l < r`, indexing from `0`). -/
structure InfimaBounds (r : ℕ) (T : ℕ → Submodule Ω (Fin n → Ω)) (δ Q : ℝ) : Prop where
  upper : ∀ l < r, ∀ i ≤ finrank Ω (T (l + 1)), heightInf Ω (L.qHeight c Q) i ≤
    Q ^ (-weightSlope (L.subspaceWeight c) (T l) (T (l + 1)) + δ)
  lower : ∀ l < r, ∀ i, finrank Ω (T l) < i → i ≤ n →
    Q ^ (-weightSlope (L.subspaceWeight c) (T l) (T (l + 1)) - δ) ≤
      heightInf Ω (L.qHeight c Q) i
  space : ∀ l < r, ∀ lam, Q ^ (-weightSlope (L.subspaceWeight c) (T l) (T (l + 1)) + δ) ≤ lam →
    (l + 1 < r → lam ≤ Q ^ (-weightSlope (L.subspaceWeight c) (T (l + 1)) (T (l + 2)) - δ)) →
    heightSpace Ω (L.qHeight c Q) lam = T (l + 1)

omit [Algebra.IsAlgebraic K Ω] in
/-- `μ_{L''}(Ω^m, U) = μ_L(Ωⁿ, φ''⁻¹ U)`: EF13 Lemma 16.2 (ii) for slopes. -/
theorem weightSlope_quotSystem {k m : ℕ} (S : Splitting K n k m) (U : Submodule Ω (Fin m → Ω)) :
    weightSlope ((L.quotSystem S c).subspaceWeight (L.quotExp S c)) U ⊤ =
      weightSlope (L.subspaceWeight c) (U.comap (S.projLin Ω)) ⊤ := by
  have hdim := Submodule.finrank_comap_eq (S.projLin Ω) U (S.projLin_surjective Ω)
  rw [S.finrank_ker_projLin] at hdim
  have hn : n = k + m := S.card_eq.symm
  simp only [weightSlope, subspaceWeight_quotSystem, finrank_top, Module.finrank_fin_fun, hdim]
  rw [Submodule.comap_top]
  congr 1
  · ring
  · rw [hn]
    push_cast
    ring

/-- **The induction of EF13 Theorem 16.1**: the bounds `InfimaBounds` hold for every `δ > 0`
once `Q` is large. -/
theorem eventually_infimaBounds [IsAlgClosed Ω] (hgap : SemistableGap K Ω) :
    ∀ (n : ℕ) (L : FormSystem K (Fin n)) (c : FormExponent K (Fin n)) (r : ℕ)
      (T : ℕ → Submodule Ω (Fin n → Ω)), IsWeightFiltration (L.subspaceWeight c) ⊤ r T →
      ∀ δ, 0 < δ → ∀ᶠ Q in atTop, L.InfimaBounds c r T δ Q := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro L c r T hT δ hδ
  set w := L.subspaceWeight (Ω := Ω) c
  have hw : IsSupermodularWeight w := L.isSupermodularWeight_subspaceWeight c
  rcases r with _ | s
  · exact Eventually.of_forall fun Q ↦ ⟨fun l hl ↦ absurd hl (Nat.not_lt_zero _),
      fun l hl ↦ absurd hl (Nat.not_lt_zero _), fun l hl ↦ absurd hl (Nat.not_lt_zero _)⟩
  set μ : ℕ → ℝ := fun l ↦ weightSlope w (T l) (T (l + 1))
  have hTs : IsDestabilizing w ⊤ (T s) := hT.isDestabilizing hw
  have hTsK : (T s).IsDefinedOver K :=
    L.isDefinedOver_of_isWeightFiltration c hT isDefinedOver_top (Nat.le_succ s)
  set k := finrank Ω (T s)
  have hkn : k < n := by
    have := Submodule.finrank_lt_finrank_of_lt hTs.lt
    simpa using this
  obtain ⟨S, hS⟩ := Splitting.exists_range_inclLin hTsK
  set φ := S.inclLin Ω
  set π := S.projLin Ω
  have hφ : Function.Injective φ := S.inclLin_injective Ω
  have hker : LinearMap.ker π = T s := by rw [S.ker_projLin, hS]
  have hTop : T (s + 1) = ⊤ := hT.top
  -- The system on `T_s` and its filtration.
  have hw' : ∀ U, (L.restrictSystem S c).subspaceWeight (L.restrictExp S c) U = w (U.map φ) :=
    L.subspaceWeight_restrictSystem S c
  have hT' := hT.restrict.comap_of_injective φ hφ hS hw'
  have hmapT : ∀ l ≤ s, ((T l).comap φ).map φ = T l := fun l hl ↦ by
    rw [map_comap_eq, hS, inf_eq_right.2 (hT.mono hl (Nat.le_succ s))]
  have hdim : ∀ l ≤ s, finrank Ω ((T l).comap φ) = finrank Ω (T l) := fun l hl ↦ by
    conv_rhs => rw [← hmapT l hl]
    exact (Submodule.equivMapOfInjective φ hφ _).finrank_eq
  have hslope' : ∀ l < s, weightSlope ((L.restrictSystem S c).subspaceWeight (L.restrictExp S c))
      ((T l).comap φ) ((T (l + 1)).comap φ) = μ l := fun l hl ↦ by
    simp only [weightSlope, hw', hmapT l hl.le, hmapT (l + 1) hl, hdim l hl.le, hdim (l + 1) hl, μ]
  have hIH := ih k hkn (L.restrictSystem S c) (L.restrictExp S c) s _ hT'
  -- The system on `Ωⁿ / T_s` is semistable, of slope `μ_s`.
  have hm : 0 < n - k := by omega
  have h16 : ∀ U : Submodule Ω (Fin (n - k) → Ω), U < ⊤ →
      weightSlope ((L.quotSystem S c).subspaceWeight (Ω := Ω) (L.quotExp S c)) ⊥ ⊤ ≤
        weightSlope ((L.quotSystem S c).subspaceWeight (L.quotExp S c)) U ⊤ := by
    intro U hU
    rw [L.weightSlope_quotSystem c S, L.weightSlope_quotSystem c S, Submodule.comap_bot, hker]
    refine hTs.le _ (lt_top_iff_ne_top.2 fun h ↦ hU.ne ?_)
    rw [← Submodule.map_comap_eq_of_surjective (S.projLin_surjective Ω) U, h, Submodule.map_top,
      LinearMap.range_eq_top.2 (S.projLin_surjective Ω)]
  have hμs'' : (L.quotExp S c).sum / ((n - k : ℕ) : ℝ) = μ s := by
    rw [← weightSlope_bot_top (L.quotSystem S c) (L.quotExp S c) (Ω := Ω),
      L.weightSlope_quotSystem c S, Submodule.comap_bot, hker]
    simp only [μ, hTop]
    rfl
  -- Lemma 16.3, and Prop. 9.2 for the system on `T_s`.
  obtain ⟨C₁, hC₁, hH₁⟩ := L.exists_absMulHeight_restrictSystem_le S c (Ω := Ω)
  obtain ⟨C₂, hC₂, hH₂⟩ := L.exists_absMulHeight_le_restrictSystem S c (Ω := Ω)
  obtain ⟨C₃, hC₃, hH₃⟩ := L.exists_absMulHeight_quotSystem_le S c (Ω := Ω)
  obtain ⟨B₀, hB₀, hprod'⟩ :=
    exists_le_prod_heightInf (Ω := Ω) (L.restrictSystem S c) (L.restrictExp S c)
  have hc'sum : (L.restrictExp S c).sum = w (T s) := by
    rw [← subspaceWeight_top (L.restrictSystem S c) (L.restrictExp S c) (Ω := Ω), hw' ⊤,
      Submodule.map_top, hS]
  have hcsum : c.sum = w ⊤ := (subspaceWeight_top L c).symm
  have hμs : c.sum - w (T s) = (n - k : ℝ) * μ s := by
    have := weightSlope_mul (w := w) hTs.lt
    rw [finrank_top, Module.finrank_fin_fun] at this
    simp only [μ, hTop]
    rw [hcsum, ← this]
    ring
  have hanti : ∀ l ≤ s, μ s ≤ μ l := fun l hl ↦ hT.weightSlope_anti hl (Nat.lt_succ_self s)
  -- The choice of `δ'`.
  set gap : ℝ := if s = 0 then 1 else μ (s - 1) - μ s
  have hgap0 : 0 < gap := by
    by_cases hs0 : s = 0
    · simp [gap, hs0]
    · have := hT.slope_lt (s - 1) (by omega)
      rw [show s - 1 + 1 = s by omega, show s - 1 + 2 = s + 1 by omega] at this
      simp only [gap, hs0, ↓reduceIte, μ, show s - 1 + 1 = s by omega]
      linarith
  set δ' := min (δ / (2 * (n + 1))) (gap / 4)
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hδ' : 0 < δ' := lt_min (div_pos hδ (by positivity)) (by positivity)
  have hnδ' : (n : ℝ) * δ' < δ / 2 := by
    calc (n : ℝ) * δ' ≤ n * (δ / (2 * (n + 1))) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) (Nat.cast_nonneg _)
      _ < δ / 2 := by
          rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  have hδ'δ : δ' < δ / 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    nlinarith
  have hδ'gap : δ' ≤ gap / 4 := min_le_right _ _
  obtain ⟨Q₁₆, hQ₁₆⟩ := exists_lt_absMulHeight_of_semistable (L.quotSystem S c) (L.quotExp S c)
    hgap hm h16 hδ'
  obtain ⟨m₀, hm₀⟩ : ∃ m₀, n = m₀ + 1 := ⟨n - 1, by omega⟩
  have hkm₀ : k ≤ m₀ := by omega
  set N := m₀ - k
  set C₀ := √2 ^ (n * m₀) * L.absDet
  set D := B₀ * C₁⁻¹ ^ k
  have hD : 0 < D := by positivity
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast (show N ≤ n by omega)
  have hαβ : c.sum - w (T s) = (N + 1) * μ s := by
    rw [hμs]
    have : (n : ℝ) - k = N + 1 := by
      simp only [N]
      rw [Nat.cast_sub hkm₀, hm₀]
      push_cast
      ring
    rw [this]
  -- The eventual inequalities in `Q`.
  have e1 : ∀ᶠ Q : ℝ in atTop, (C₃ + 1) * Q ^ (-μ s - δ) ≤ Q ^ (-μ s - δ') :=
    eventually_mul_rpow_le _ (by linarith)
  have e2 : ∀ᶠ Q : ℝ in atTop, ∀ l ∈ range s, C₂ * Q ^ (-μ l + δ') ≤ Q ^ (-μ l + δ) :=
    (eventually_all_finset _).2 fun l _ ↦ eventually_mul_rpow_le _ (by linarith)
  have e3 : ∀ᶠ Q : ℝ in atTop, ∀ l ∈ range s, C₁ * Q ^ (-μ l - δ) ≤ Q ^ (-μ l - δ') :=
    (eventually_all_finset _).2 fun l _ ↦ eventually_mul_rpow_le _ (by linarith)
  have e3' : ∀ᶠ Q : ℝ in atTop, ∀ l ∈ range s,
      C₁ * Q ^ (-μ (l + 1) - δ) ≤ Q ^ (-μ (l + 1) - δ') :=
    (eventually_all_finset _).2 fun l _ ↦ eventually_mul_rpow_le _ (by linarith)
  have e3'' : ∀ᶠ Q : ℝ in atTop, ∀ l ∈ range s,
      C₂⁻¹ * Q ^ (-μ (l + 1) - δ) ≤ Q ^ (-μ (l + 1) - δ') :=
    (eventually_all_finset _).2 fun l _ ↦ eventually_mul_rpow_le _ (by linarith)
  have e5 : ∀ᶠ Q : ℝ in atTop, ∀ l ∈ range s, C₁⁻¹ * Q ^ (-μ l + δ') ≤ Q ^ (-μ l + δ) :=
    (eventually_all_finset _).2 fun l _ ↦ eventually_mul_rpow_le _ (by linarith)
  have e4 : ∀ᶠ Q : ℝ in atTop, s ≠ 0 →
      (C₂ * C₃ + 1) * Q ^ (-μ (s - 1) + δ') ≤ Q ^ (-μ s - δ') := by
    by_cases hs0 : s = 0
    · exact Eventually.of_forall fun Q h ↦ absurd hs0 h
    · have hg : gap = μ (s - 1) - μ s := by simp [gap, hs0]
      filter_upwards [eventually_mul_rpow_le (C₂ * C₃ + 1)
        (show -μ (s - 1) + δ' < -μ s - δ' by linarith)] with Q hQ _ using hQ
  have e6 : ∀ᶠ Q : ℝ in atTop, C₀ * C₃ ^ N / D * Q ^ (-μ s + N * δ') ≤ Q ^ (-μ s + δ / 2) :=
    eventually_mul_rpow_le _ (by nlinarith)
  filter_upwards [hIH δ' hδ', eventually_ge_atTop (max Q₁₆ 1), eventually_gt_atTop 1, e1, e2,
    e3, e3', e3'', e4, e5, e6] with Q hIB hQ₀ hQ1 he1 he2 he3 he3' he3'' he4 he5 he6
  have hQ : 1 ≤ Q := hQ1.le
  have hQ0 : 0 < Q := zero_lt_one.trans hQ1
  set H := L.qHeight (Ω := Ω) c Q
  set H' := (L.restrictSystem S c).qHeight (Ω := Ω) (L.restrictExp S c) Q
  have hH₁' : ∀ y, H' y ≤ C₁ * H (φ y) := fun y ↦ by
    simp only [H, H', qHeight_of_one_le _ _ hQ]
    exact hH₁ Q hQ y
  have hH₂' : ∀ y, H (φ y) ≤ C₂ * H' y := fun y ↦ by
    simp only [H, H', qHeight_of_one_le _ _ hQ]
    exact hH₂ Q hQ y
  -- (16.13): heights off `T_s` are at least `θ`.
  set θ := Q ^ (-μ s - δ') / C₃
  have hθpos : 0 < θ := div_pos (Real.rpow_pos_of_pos hQ0 _) hC₃
  have hθ : ∀ x ∉ T s, θ ≤ H x := by
    intro x hx
    have hπx : π x ≠ 0 := fun h ↦ hx (hker ▸ LinearMap.mem_ker.2 h)
    have h1 := hQ₁₆ Q hQ ((le_max_left _ _).trans hQ₀) (π x) hπx
    rw [hμs''] at h1
    have h2 := hH₃ Q hQ x
    simp only [H, qHeight_of_one_le _ _ hQ]
    rw [div_le_iff₀ hC₃]
    linarith
  have hlowtop : ∀ i, k < i → i ≤ n → θ ≤ heightInf Ω H i := fun i hi hin ↦
    le_heightInf_of_forall_notMem hθ hi hin
  have hupk : ∀ i ≤ k, heightInf Ω H i ≤ C₂ * heightInf Ω H' i := fun i hi ↦
    heightInf_le_mul_of_comp φ hφ hC₂ hH₂' hi
  have hlamk : heightInf Ω H k < θ := by
    rcases Nat.eq_zero_or_pos s with hs0 | hs0
    · have : k = 0 := by simp [k, hs0, hT.zero]
      rw [this, heightInf_zero]
      exact hθpos
    · have h1 := hIB.upper (s - 1) (by omega) k (by
        rw [show s - 1 + 1 = s by omega, hdim s le_rfl])
      rw [hslope' (s - 1) (by omega)] at h1
      have h2 := he4 (by omega)
      have hpos := Real.rpow_pos_of_pos hQ0 (-μ (s - 1) + δ')
      calc heightInf Ω H k ≤ C₂ * heightInf Ω H' k := hupk k le_rfl
        _ ≤ C₂ * Q ^ (-μ (s - 1) + δ') := mul_le_mul_of_nonneg_left h1 hC₂.le
        _ < θ := by
          rw [lt_div_iff₀ hC₃]
          nlinarith
  have hlamlt : ∀ i ≤ k, heightInf Ω H i < θ := fun i hi ↦
    (heightInf_mono hi (by simpa using hkn.le)).trans_lt hlamk
  have hlowk : ∀ i ≤ k, heightInf Ω H' i ≤ C₁ * heightInf Ω H i := fun i hi ↦
    heightInf_le_mul_of_lt φ hS hC₁ hH₁' hθ (hi.trans hkn.le) (hlamlt i hi)
  -- The top infimum, through Prop. 9.2 for `L` and `L'`.
  have htop : heightInf Ω H n ≤ Q ^ (-μ s + δ / 2) := by
    have h1 := prod_heightInf_le' (Ω := Ω) hm₀ L c hQ
    have h2 : D * Q ^ (-w (T s)) * θ ^ N ≤ ∏ i ∈ range m₀, heightInf Ω H (i + 1) := by
      rw [← prod_range_mul_prod_Ico _ hkm₀]
      refine mul_le_mul ?_ ?_ (pow_nonneg hθpos.le _)
        (prod_nonneg fun i _ ↦ heightInf_nonneg _)
      · calc D * Q ^ (-w (T s)) = C₁⁻¹ ^ k * (B₀ * Q ^ (-(L.restrictExp S c).sum)) := by
              rw [hc'sum]
              ring
          _ ≤ C₁⁻¹ ^ k * ∏ i ∈ range k, heightInf Ω H' (i + 1) :=
              mul_le_mul_of_nonneg_left (hprod' Q hQ) (by positivity)
          _ = ∏ i ∈ range k, (C₁⁻¹ * heightInf Ω H' (i + 1)) := by
              rw [prod_mul_distrib, prod_const, card_range]
          _ ≤ ∏ i ∈ range k, heightInf Ω H (i + 1) :=
              Finset.prod_le_prod₀ (fun i _ ↦ mul_nonneg (inv_nonneg.2 hC₁.le) (heightInf_nonneg _))
                fun i hi ↦ by
                  rw [inv_mul_le_iff₀ hC₁]
                  exact hlowk (i + 1) (by simp at hi; omega)
      · calc θ ^ N = ∏ i ∈ Ico k m₀, θ := by rw [prod_const, Nat.card_Ico]
          _ ≤ ∏ i ∈ Ico k m₀, heightInf Ω H (i + 1) :=
              Finset.prod_le_prod₀ (fun _ _ ↦ hθpos.le) fun i hi ↦ by
                rw [mem_Ico] at hi
                exact hlowtop (i + 1) (by omega) (by omega)
    have h3 := le_of_mul_le_of_le hQ0 hD hC₃ (heightInf_nonneg _) h1 h2 hαβ
    exact h3.trans he6
  have hθs : Q ^ (-μ s - δ) < θ := by
    have hpos := Real.rpow_pos_of_pos hQ0 (-μ s - δ)
    rw [lt_div_iff₀ hC₃]
    nlinarith
  have hslope2 : ∀ l, l + 1 < s → weightSlope ((L.restrictSystem S c).subspaceWeight
      (L.restrictExp S c)) ((T (l + 1)).comap φ) ((T (l + 2)).comap φ) = μ (l + 1) :=
    fun l hl ↦ hslope' (l + 1) hl
  refine ⟨fun l hl i hi ↦ ?_, fun l hl i hi hin ↦ ?_, fun l hl lam hlam hlam' ↦ ?_⟩
  · -- The upper bounds.
    rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
    · have hik : i ≤ k := hi.trans (Submodule.finrank_mono (hT.mono (Nat.succ_le_of_lt hl)
        (Nat.le_succ s)))
      have h1 := hIB.upper l hl i (by rw [hdim (l + 1) hl]; exact hi)
      rw [hslope' l hl] at h1
      calc heightInf Ω H i ≤ C₂ * heightInf Ω H' i := hupk i hik
        _ ≤ C₂ * Q ^ (-μ l + δ') := mul_le_mul_of_nonneg_left h1 hC₂.le
        _ ≤ Q ^ (-μ l + δ) := he2 l (mem_range.2 hl)
    · have hin : i ≤ n := by
        rw [hTop, finrank_top, Module.finrank_fin_fun] at hi
        exact hi
      calc heightInf Ω H i ≤ heightInf Ω H n := heightInf_mono hin (by simp)
        _ ≤ Q ^ (-μ l + δ / 2) := htop
        _ ≤ Q ^ (-μ l + δ) := Real.rpow_le_rpow_of_exponent_le hQ (by linarith)
  · -- The lower bounds.
    by_cases hik : i ≤ k
    · have hlk : l < s := by
        by_contra h
        have : l = s := by omega
        subst this
        exact absurd hi (not_lt.2 hik)
      have h1 := hIB.lower l hlk i (by rw [hdim l hlk.le]; exact hi) hik
      rw [hslope' l hlk] at h1
      have h2 := hlowk i hik
      calc Q ^ (-μ l - δ) ≤ C₁⁻¹ * Q ^ (-μ l - δ') := by
            rw [le_inv_mul_iff₀ hC₁]
            exact he3 l (mem_range.2 hlk)
        _ ≤ C₁⁻¹ * heightInf Ω H' i := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hC₁.le)
        _ ≤ heightInf Ω H i := by
            rw [inv_mul_le_iff₀ hC₁]
            exact h2
    · push Not at hik
      have hls := hanti l (by omega)
      calc Q ^ (-μ l - δ) ≤ Q ^ (-μ s - δ) :=
            Real.rpow_le_rpow_of_exponent_le hQ (by linarith)
        _ ≤ θ := hθs.le
        _ ≤ heightInf Ω H i := hlowtop i hik hin
  · -- The spaces `T(λ)`.
    rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
    · have hlam2 := hlam' (by omega)
      have hls := hanti (l + 1) (by omega)
      have hlamθ : lam < θ := lt_of_le_of_lt (hlam2.trans
        (Real.rpow_le_rpow_of_exponent_le hQ (by linarith))) hθs
      have hlamQ : C₂ * Q ^ (-μ l + δ') ≤ lam := (he2 l (mem_range.2 hl)).trans hlam
      have hA := hIB.space l hl (C₁ * lam) (by
          rw [hslope' l hl, ← inv_mul_le_iff₀ hC₁]
          exact (he5 l (mem_range.2 hl)).trans hlam)
        (fun hl1 ↦ by
          rw [hslope2 l hl1]
          exact (mul_le_mul_of_nonneg_left hlam2 hC₁.le).trans (he3' l (mem_range.2 hl)))
      have hB := hIB.space l hl (lam / C₂) (by
          rw [hslope' l hl, le_div_iff₀ hC₂, mul_comm]
          exact hlamQ)
        (fun hl1 ↦ by
          rw [hslope2 l hl1, div_eq_inv_mul]
          exact (mul_le_mul_of_nonneg_left hlam2 (inv_nonneg.2 hC₂.le)).trans
            (he3'' l (mem_range.2 hl)))
      refine le_antisymm ?_ ?_
      · calc heightSpace Ω H lam ≤ (heightSpace Ω H' (C₁ * lam)).map φ :=
              heightSpace_le_map φ hS hC₁ hH₁' hθ hlamθ
          _ = T (l + 1) := by rw [hA, hmapT (l + 1) hl]
      · calc T (l + 1) = (heightSpace Ω H' (lam / C₂)).map φ := by rw [hB, hmapT (l + 1) hl]
          _ ≤ heightSpace Ω H (C₂ * (lam / C₂)) := map_heightSpace_le φ hC₂ hH₂' _
          _ = heightSpace Ω H lam := by rw [mul_div_cancel₀ _ hC₂.ne']
    · rw [hTop]
      refine heightSpace_eq_top (htop.trans_lt (lt_of_lt_of_le ?_ hlam))
      exact Real.rpow_lt_rpow_of_exponent_lt hQ1 (by linarith)

theorem InfimaBounds.mono {r : ℕ} {T : ℕ → Submodule Ω (Fin n → Ω)} {δ δ' Q : ℝ} (hQ : 1 ≤ Q)
    (h : L.InfimaBounds c r T δ Q) (hδ : δ ≤ δ') (l : ℕ) (hl : l < r) (i : ℕ)
    (hi₁ : finrank Ω (T l) < i) (hi₂ : i ≤ finrank Ω (T (l + 1))) (hin : i ≤ n) :
    Q ^ (-weightSlope (L.subspaceWeight c) (T l) (T (l + 1)) - δ') ≤
        heightInf Ω (L.qHeight c Q) i ∧
      heightInf Ω (L.qHeight c Q) i ≤
        Q ^ (-weightSlope (L.subspaceWeight c) (T l) (T (l + 1)) + δ') :=
  ⟨(Real.rpow_le_rpow_of_exponent_le hQ (by linarith)).trans (h.lower l hl i hi₁ hin),
    (h.upper l hl i hi₂).trans (Real.rpow_le_rpow_of_exponent_le hQ (by linarith))⟩

/-- `T_n = Ωⁿ`. -/
theorem heightFlag_eq_top (h : (Fin n → Ω) → ℝ) : heightFlag Ω h n = ⊤ :=
  eq_top_iff.2 (le_iInf₂ fun _ hlam ↦ (heightSpace_eq_top hlam).ge)

/-- **EF13 Theorem 16.1**: let `0 = T_0 < ⋯ < T_r = Ωⁿ` be the filtration of `(L, c)`,
`d_l = dim T_l` and `μ_l = μ(T_{l+1}, T_l)` (indexing from `0`). For every `δ > 0` there is `Q₀`
such that for `Q ≥ Q₀`, `Q^{-μ_l - δ} ≤ λ_i(Q) ≤ Q^{-μ_l + δ}` for `d_l < i ≤ d_{l+1}` (16.2) and
`T_{d_{l+1}}(Q) = T_{l+1}` (16.3). The hypothesis `SemistableGap K Ω` is the qualitative EF13
Theorem 8.1. -/
theorem eventually_successiveInf [IsAlgClosed Ω] (hgap : SemistableGap K Ω) {r : ℕ}
    {T : ℕ → Submodule Ω (Fin n → Ω)} (hT : IsWeightFiltration (L.subspaceWeight c) ⊤ r T)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ Q₀, ∀ (Q : ℝ) (hQ : 1 ≤ Q), Q₀ ≤ Q → ∀ l < r,
      (∀ i, finrank Ω (T l) < i → i ≤ finrank Ω (T (l + 1)) →
        Q ^ (-weightSlope (L.subspaceWeight c) (T l) (T (l + 1)) - δ) ≤
            L.successiveInf (c.weight (zero_lt_one.trans_le hQ)) Ω i ∧
          L.successiveInf (c.weight (zero_lt_one.trans_le hQ)) Ω i ≤
            Q ^ (-weightSlope (L.subspaceWeight c) (T l) (T (l + 1)) + δ)) ∧
      L.infFlag (c.weight (zero_lt_one.trans_le hQ)) Ω (finrank Ω (T (l + 1))) = T (l + 1) := by
  set μ : ℕ → ℝ := fun l ↦ weightSlope (L.subspaceWeight c) (T l) (T (l + 1))
  have key : ∀ l ∈ range r, ∀ᶠ Q : ℝ in atTop,
      (∀ i, finrank Ω (T l) < i → i ≤ finrank Ω (T (l + 1)) →
        Q ^ (-μ l - δ) ≤ heightInf Ω (L.qHeight c Q) i ∧
          heightInf Ω (L.qHeight c Q) i ≤ Q ^ (-μ l + δ)) ∧
      heightFlag Ω (L.qHeight c Q) (finrank Ω (T (l + 1))) = T (l + 1) := by
    intro l hl
    rw [mem_range] at hl
    by_cases hl1 : l + 1 < r
    · have hgap' : 0 < μ l - μ (l + 1) := by
        have := hT.slope_lt l (by omega)
        simp only [μ]
        linarith
      set δ₀ := min δ ((μ l - μ (l + 1)) / 4)
      have hδ₀ : 0 < δ₀ := lt_min hδ (by linarith)
      have hδ₀δ : δ₀ ≤ δ := min_le_left _ _
      have hδ₀g : δ₀ ≤ (μ l - μ (l + 1)) / 4 := min_le_right _ _
      filter_upwards [eventually_infimaBounds hgap n L c r T hT δ₀ hδ₀, eventually_gt_atTop 1]
        with Q hIB hQ1
      have hQ : 1 ≤ Q := hQ1.le
      have hdn : finrank Ω (T (l + 1)) ≤ n := by
        have := Submodule.finrank_le (T (l + 1))
        simpa using this
      refine ⟨fun i hi₁ hi₂ ↦ hIB.mono L c hQ hδ₀δ l hl i hi₁ hi₂ (hi₂.trans hdn), ?_⟩
      set lam := Q ^ (-(μ l + μ (l + 1)) / 2)
      have h₁ : Q ^ (-μ l + δ₀) < lam := Real.rpow_lt_rpow_of_exponent_lt hQ1 (by linarith)
      have h₂ : lam < Q ^ (-μ (l + 1) - δ₀) := Real.rpow_lt_rpow_of_exponent_lt hQ1 (by linarith)
      have hd : finrank Ω (T (l + 1)) < n := by
        have := Submodule.finrank_lt_finrank_of_lt ((hT.lt (l + 1) hl1).trans_le
          (hT.le_top (by omega)))
        simpa using this
      rw [← heightSpace_eq_heightFlag (by simpa using hd)
        ((hIB.upper l hl _ le_rfl).trans_lt h₁) (h₂.trans_le (hIB.lower (l + 1) hl1 _
          (Nat.lt_succ_self _) (by omega)))]
      exact hIB.space l hl lam h₁.le fun _ ↦ h₂.le
    · have hlr : l + 1 = r := by omega
      filter_upwards [eventually_infimaBounds hgap n L c r T hT δ hδ, eventually_gt_atTop 1]
        with Q hIB hQ1
      have hQ : 1 ≤ Q := hQ1.le
      have hdn : finrank Ω (T (l + 1)) = n := by
        rw [hlr, hT.top, finrank_top, Module.finrank_fin_fun]
      refine ⟨fun i hi₁ hi₂ ↦ hIB.mono L c hQ le_rfl l hl i hi₁ hi₂ (hi₂.trans hdn.le), ?_⟩
      rw [hdn, heightFlag_eq_top, hlr, hT.top]
  obtain ⟨Q₀, hQ₀⟩ := Filter.eventually_atTop.1 ((eventually_all_finset _).2 key)
  refine ⟨Q₀, fun Q hQ hQQ l hl ↦ ?_⟩
  obtain ⟨h₁, h₂⟩ := hQ₀ Q hQQ l (mem_range.2 hl)
  rw [qHeight_of_one_le L c hQ] at h₁ h₂
  exact ⟨h₁, h₂⟩

end FormSystem

end NumberField
