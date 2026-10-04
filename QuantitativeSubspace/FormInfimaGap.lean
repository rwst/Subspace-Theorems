/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.FormDavenport
public import QuantitativeSubspace.FormQuotientHeight

/-!
# The gap among the successive infima and the height of `T_k(Q)`

J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative Subspace Theorem*,
Ann. of Math. **177** (2013), 513–590, Lemmas 9.3, 9.4 and 10.3.

Let `(L, c)` satisfy EF13's conditions (8.3), (8.4), (8.8), (8.9) (`IsNormalSemistable`), and
let `λ_1 ≤ ⋯ ≤ λ_n` be the successive infima of `H_{L,c,Q}` with `λ_1 ≤ Q^{-δ}`. For `Q` large
against `H_L`:

* Lemma 9.3: `Q^{-p-1/2} ≤ λ_{i_1} ⋯ λ_{i_p} ≤ Q^{n-p+1/2}` for distinct indices.
* Lemma 9.4: there is `0 < k < n` with `λ_k ≤ Q^{-δ/(n-1)} λ_{k+1}`.
* Lemma 10.3: `H₂(T_k(Q)) ≥ Q^{δ/3Rⁿ}`.

The proof of Lemma 10.3 differs from EF13's. EF13 bound the determinants `θ_w` of the forms of
weight `w(T)` at near-minimal points `g_1, …, g_k ∈ T = T_k(Q)` over a field `E` containing them.
Here the work stays over `K`: the system `L'` that `L` induces on `T` (Q3.5's `restrictSystem`,
through a splitting with `φ'(Ω^k) = T`) has the same infima `λ_1, …, λ_k` up to a factor `n`, and
`w(T)` as its total exponent. Prop. 9.2 for `L'` and `w(T) ≤ 0` give `Δ_{L'} ≪ λ_1 ⋯ λ_k`, and
`Δ_{L'}` is a product of the minors `θ` of Q3.7, bounded below by EF13 (10.2).

## Main results

* `NumberField.FormSystem.IsNormalSemistable`: EF13 (8.3), (8.4), (8.8), (8.9).
* `NumberField.FormSystem.rpow_le_successiveInf_one`: the lower bound for `λ_1` (Lemma 7.1).
* `NumberField.FormSystem.rpow_le_prod_successiveInf`, `prod_successiveInf_le_rpow`: Lemma 9.3.
* `NumberField.FormSystem.exists_successiveInf_le`: Lemma 9.4.
* `NumberField.FormSystem.one_le_mulDet_restrictSystem_mul`: `Δ_{L'}` against the minors (10.2).
* `NumberField.FormSystem.rpow_le_mul_arakelovMulHeight`: the main inequality of Lemma 10.3,
  `Q^δ ≤ (k^{k/2} nᵏ 2^{n(n-1)/2} H_L)ⁿ (C(n,k) H_L H₂(V)^{1/[K:ℚ]})^{n Rᵏ}`.
* `NumberField.FormSystem.rpow_le_arakelovMulHeight_infFlag`: Lemma 10.3, relative to `K`.

This is milestone Q4.1a of `QuantitativeSubspace/README.md`.
-/

@[expose] public section

open Module Finset Matrix Submodule

namespace NumberField

/-! ### The infimum over a finite set of absolute values -/

section Inf

variable {K : Type*} [Field K] [NumberField K] {s : Finset K}

theorem hasFiniteMulSupport_apply_of_mem {θ : FinitePlace K → K} (h0 : 0 ∉ s)
    (hθ : ∀ v, θ v ∈ s) : (fun v : FinitePlace K ↦ v (θ v)).HasFiniteMulSupport :=
  (finite_setOf_exists_ne_one h0).subset fun v hv ↦ ⟨θ v, hθ v, hv⟩

/-- **The lower half of EF13 (10.2)** at chosen elements: if `θ_v ∈ s` at every place, then
`∏_v M_v / ∏_v (M_v / m_v) ≤ ∏_v ‖θ_v‖_v`. -/
theorem mulSupProd_div_mulRatioProd_le (hs : s.Nonempty) (h0 : 0 ∉ s)
    {θa : InfinitePlace K → K} {θf : FinitePlace K → K} (ha : ∀ v, θa v ∈ s)
    (hf : ∀ v, θf v ∈ s) :
    mulSupProd s / mulRatioProd s ≤
      (∏ v : InfinitePlace K, v (θa v) ^ v.mult) * ∏ᶠ v : FinitePlace K, v (θf v) := by
  have : Nonempty s := hs.coe_sort
  have hM := hasFiniteMulSupport_iSup_finset hs h0
  have hR := hasFiniteMulSupport_localRatio hs h0
  have hle : ∀ f : AbsoluteValue K ℝ, ∀ x ∈ s,
      (⨆ e : s, f e) / localRatio s (fun x ↦ f x) ≤ f x := fun f x hx ↦ by
    have hm := iInf_finset_pos hs h0 f
    have hM0 : 0 < ⨆ e : s, f e := hm.trans_le
      ((ciInf_le_ciSup (Finite.bddBelow_range _) (Finite.bddAbove_range _) :
        (⨅ e : s, f e) ≤ ⨆ e : s, f e))
    rw [localRatio, div_div_cancel₀ hM0.ne']
    exact iInf_finset_le _ hx
  have hdiv : mulSupProd s / mulRatioProd s =
      (∏ v : InfinitePlace K, ((⨆ e : s, v e) / localRatio s (fun x ↦ v x)) ^ v.mult) *
        ∏ᶠ v : FinitePlace K, (⨆ e : s, v e) / localRatio s (fun x ↦ v x) := by
    rw [mulSupProd, mulRatioProd, finprod_div_distrib hM hR, mul_div_mul_comm,
      ← prod_div_distrib]
    simp only [div_pow]
  rw [hdiv]
  refine prod_places_le (fun v ↦ div_nonneg (iSup_finset_nonneg v.1) (localRatio_nonneg v.1))
    (fun v ↦ div_nonneg (iSup_finset_nonneg v.1) (localRatio_nonneg v.1))
    ((hM.union hR).subset (Function.mulSupport_div _ _))
    (hasFiniteMulSupport_apply_of_mem h0 hf) (fun v ↦ hle v.1 _ (ha v)) (fun v ↦ hle v.1 _ (hf v))

end Inf

namespace FormSystem

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

/-- **EF13's standing assumptions (8.3), (8.4), (8.8), (8.9)** on `(L, c)`: the exponents sum to
`0` at every place, `Σ_v max_i c_iv ≤ 1`, there is a finite place `v₀` with `L^{(v₀)} = (X_i)`
and `c_{v₀} = 0`, and `w(U) ≤ 0` for every proper subspace `U` of `Ωⁿ`. -/
structure IsNormalSemistable (L : FormSystem K (Fin n)) (c : FormExponent K (Fin n))
    (Ω : Type*) [Field Ω] [Algebra K Ω] : Prop where
  sum_arch : ∀ v, ∑ i, c.arch v i = 0
  sum_fin : ∀ v, ∑ i, c.fin v i = 0
  sum_iSup_le : (∑ v, ⨆ i, c.arch v i) + ∑ᶠ v, ⨆ i, c.fin v i ≤ 1
  exists_v₀ : ∃ v₀ : FinitePlace K, L.fin v₀ = 1 ∧ c.fin v₀ = 0
  subspaceWeight_le : ∀ U : Submodule Ω (Fin n → Ω), U ≠ ⊤ → L.subspaceWeight c U ≤ 0

namespace IsNormalSemistable

variable {L : FormSystem K (Fin n)} {c : FormExponent K (Fin n)} {Ω : Type*} [Field Ω]
  [Algebra K Ω]

theorem sum_eq_zero (h : L.IsNormalSemistable c Ω) : c.sum = 0 := by
  simp [FormExponent.sum, h.sum_arch, h.sum_fin]

/-- (8.8) puts `X_1, …, X_n` among the forms. -/
theorem hasUnitForms (h : L.IsNormalSemistable c Ω) : L.HasUnitForms := fun i ↦ by
  obtain ⟨v₀, hv₀, -⟩ := h.exists_v₀
  have := L.fin_mem_forms v₀ i
  rw [hv₀] at this
  convert this using 1
  funext j
  simp [one_apply, Pi.single_apply, eq_comm]

end IsNormalSemistable

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω]
  (L : FormSystem K (Fin n)) (c : FormExponent K (Fin n))

/-! ### EF13 Lemmas 9.3 and 9.4 -/

omit [IsAlgClosed Ω] in
/-- **The lower bound for `λ_1`** (EF13 Lemma 7.1, proof of Lemma 9.3): under (8.4),
`λ_1 ≥ n⁻¹ H_L^{-C(r,n)} Q^{-1}`, `r` the number of forms of `L`. -/
theorem rpow_le_successiveInf_one (hn : 0 < n)
    (hc : (∑ v, ⨆ i, c.arch v i) + ∑ᶠ v, ⨆ i, c.fin v i ≤ 1) {Q : ℝ} (hQ : 1 ≤ Q) :
    (n : ℝ)⁻¹ * L.absFormHeight ^ (-((L.forms.card.choose n : ℕ) : ℝ)) * Q⁻¹ ≤
      L.successiveInf (c.weight (zero_lt_one.trans_le hQ)) Ω 1 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine le_heightInf_of_forall_notMem (W := ⊥) (fun x hx ↦ ?_) (by simp) hn
  have h := L.le_absMulHeight_weight c hQ (Ω := Ω) (x := x) (by simpa using hx)
  simp only [Fintype.card_fin] at h
  have hH : 0 ≤ L.absFormHeight := Real.rpow_nonneg (zero_le_one.trans L.one_le_mulFormHeight) _
  refine le_trans (mul_le_mul_of_nonneg_left ?_ (by positivity)) h
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le hQ (neg_le_neg hc)

omit [IsAlgClosed Ω] in
/-- `λ_1 ≥ Q^{-1-1/3n}` once `n H_L^{C(r,n)} ≤ Q^{1/3n}` (EF13, proof of Lemma 9.3). -/
theorem rpow_le_successiveInf_one' (hn : 0 < n)
    (hc : (∑ v, ⨆ i, c.arch v i) + ∑ᶠ v, ⨆ i, c.fin v i ≤ 1) {Q : ℝ} (hQ : 1 ≤ Q)
    (hQ₁ : n * L.absFormHeight ^ ((L.forms.card.choose n : ℕ) : ℝ) ≤ Q ^ (1 / (3 * n) : ℝ)) :
    Q ^ (-(1 + 1 / (3 * n)) : ℝ) ≤ L.successiveInf (c.weight (zero_lt_one.trans_le hQ)) Ω 1 := by
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hH : 0 < L.absFormHeight :=
    Real.rpow_pos_of_pos (zero_lt_one.trans_le L.one_le_mulFormHeight) _
  refine le_trans ?_ (L.rpow_le_successiveInf_one c hn hc hQ (Ω := Ω))
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 hn
  rw [Real.rpow_neg hH.le, ← mul_inv, ← mul_inv, Real.rpow_neg hQ0.le, Real.rpow_add hQ0,
    Real.rpow_one, mul_comm Q]
  gcongr

omit [IsAlgClosed Ω] in
/-- The product of the successive infima from `1` to `n`, as `Fin n`-indexed. -/
theorem prod_successiveInf_le_mul_pow {a : FormWeight K (Fin n)} {m : ℕ} (hm : n = m + 1) :
    ∏ i : Fin n, L.successiveInf a Ω (i + 1) ≤
      L.successiveInf a Ω 1 * L.successiveInf a Ω n ^ m := by
  subst hm
  rw [Fin.prod_univ_succ]
  simp only [Fin.val_zero, zero_add, Fin.val_succ]
  refine mul_le_mul_of_nonneg_left ?_ (heightInf_nonneg _)
  calc ∏ i : Fin m, L.successiveInf a Ω (i + 1 + 1)
      ≤ ∏ _i : Fin m, L.successiveInf a Ω (m + 1) :=
        prod_le_prod₀ (fun i _ ↦ heightInf_nonneg _) fun i _ ↦
          heightInf_mono (by omega) (by simp)
    _ = _ := by rw [prod_const, card_univ, Fintype.card_fin]

/-- **EF13 Lemma 9.4**: under (8.3), if `λ_1 ≤ Q^{-δ}` and `n^{n/2} ≤ Δ_L Q^δ`, there is
`0 < k < n` with `λ_k ≤ Q^{-δ/(n-1)} λ_{k+1}`. -/
theorem exists_successiveInf_le (hn : 2 ≤ n) (hc : c.sum = 0) {Q δ : ℝ} (hQ : 1 ≤ Q)
    (h1 : L.successiveInf (c.weight (zero_lt_one.trans_le hQ)) Ω 1 ≤ Q ^ (-δ))
    (hΔ : √n ^ n ≤ L.absDet * Q ^ δ) :
    ∃ k, 0 < k ∧ k < n ∧ L.successiveInf (c.weight (zero_lt_one.trans_le hQ)) Ω k ≤
      Q ^ (-(δ / (n - 1))) * L.successiveInf (c.weight (zero_lt_one.trans_le hQ)) Ω (k + 1) := by
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  set a := c.weight hQ0
  set lam := fun i ↦ L.successiveInf a Ω i with hlam
  have hpos : ∀ i, 0 < i → i ≤ n → 0 < lam i := fun i hi hin ↦ by
    have := L.successiveInf_pos a (Ω := Ω) ⟨i - 1, by omega⟩
    simpa [Nat.sub_add_cancel hi] using this
  -- `λ_n ≥ 1`
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hlow := L.le_prod_successiveInf_weight (Ω := Ω) (by omega) c hQ0
  rw [hc, neg_zero, Real.rpow_zero, mul_one] at hlow
  have hprod := L.prod_successiveInf_le_mul_pow (Ω := Ω) (a := a) hm
  have hn1 : 1 ≤ lam n ^ m := by
    have hs : 0 < √(n : ℝ) ^ n := pow_pos (Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < n))) _
    have h2 : (√n ^ n)⁻¹ * L.absDet ≤ Q ^ (-δ) * lam n ^ m :=
      hlow.trans (hprod.trans (mul_le_mul_of_nonneg_right h1 (pow_nonneg (heightInf_nonneg _) _)))
    rw [inv_mul_le_iff₀ hs] at h2
    have h3 : √(n : ℝ) ^ n ≤ √n ^ n * (Q ^ (-δ) * lam n ^ m) * Q ^ δ := by
      calc √(n : ℝ) ^ n ≤ L.absDet * Q ^ δ := hΔ
        _ ≤ _ := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hQ0.le _)
    have h4 : √(n : ℝ) ^ n * (Q ^ (-δ) * lam n ^ m) * Q ^ δ = √n ^ n * lam n ^ m := by
      rw [Real.rpow_neg hQ0.le]
      field_simp
    rw [h4] at h3
    by_contra hlt
    push Not at hlt
    nlinarith
  have hln : 1 ≤ lam n := by
    by_contra hlt
    push Not at hlt
    have := pow_lt_one₀ (hpos n (by omega) le_rfl).le hlt (by omega : m ≠ 0)
    linarith
  -- the telescoping product
  by_contra H
  push Not at H
  set θ := δ / (n - 1) with hθ
  have key : ∀ j, 1 ≤ j → j < n → Q ^ (-(j * θ)) * lam (j + 1) < lam 1 := by
    intro j hj1 hjn
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simpa using H 1 one_pos hjn
      have h' := ih hj (by omega)
      have hH := H (j + 1) (by omega) hjn
      calc Q ^ (-(((j + 1 : ℕ) : ℝ) * θ)) * lam (j + 1 + 1)
          = Q ^ (-(j * θ)) * (Q ^ (-θ) * lam (j + 1 + 1)) := by
            rw [← mul_assoc, ← Real.rpow_add hQ0]
            push_cast
            ring_nf
        _ < Q ^ (-(j * θ)) * lam (j + 1) :=
            mul_lt_mul_of_pos_left hH (Real.rpow_pos_of_pos hQ0 _)
        _ < lam 1 := h'
  have hk := key m (by omega) (by omega)
  have hmθ : (m : ℝ) * θ = δ := by
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    rw [hθ, hm]
    push_cast
    rw [add_sub_cancel_right]
    field_simp
  rw [hmθ, ← hm] at hk
  have : Q ^ (-δ) ≤ Q ^ (-δ) * lam n := le_mul_of_one_le_right (Real.rpow_nonneg hQ0.le _) hln
  linarith

omit [IsAlgClosed Ω] in
theorem rpow_mul_card_le_prod_successiveInf (hn : 0 < n)
    (hc : (∑ v, ⨆ i, c.arch v i) + ∑ᶠ v, ⨆ i, c.fin v i ≤ 1) {Q : ℝ} (hQ : 1 ≤ Q)
    (hQ₁ : n * L.absFormHeight ^ ((L.forms.card.choose n : ℕ) : ℝ) ≤ Q ^ (1 / (3 * n) : ℝ))
    (s : Finset (Fin n)) :
    Q ^ (-(1 + 1 / (3 * n)) * #s : ℝ) ≤
      ∏ i ∈ s, L.successiveInf (c.weight (zero_lt_one.trans_le hQ)) Ω (i + 1) := by
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have h1 := L.rpow_le_successiveInf_one' c hn hc hQ hQ₁ (Ω := Ω)
  calc Q ^ (-(1 + 1 / (3 * n)) * #s : ℝ) = ∏ _i ∈ s, Q ^ (-(1 + 1 / (3 * n)) : ℝ) := by
        rw [prod_const, ← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]
    _ ≤ _ := prod_le_prod₀ (fun _ _ ↦ Real.rpow_nonneg hQ0.le _) fun i _ ↦
        h1.trans (heightInf_mono (by omega) (by simp))

omit [IsAlgClosed Ω] in
/-- **EF13 Lemma 9.3, lower bound**: `Q^{-p-1/2} ≤ ∏_{i ∈ s} λ_i`, `p = #s`, under (8.4) and
`n H_L^{C(r,n)} ≤ Q^{1/3n}`. -/
theorem rpow_le_prod_successiveInf (hn : 0 < n)
    (hc : (∑ v, ⨆ i, c.arch v i) + ∑ᶠ v, ⨆ i, c.fin v i ≤ 1) {Q : ℝ} (hQ : 1 ≤ Q)
    (hQ₁ : n * L.absFormHeight ^ ((L.forms.card.choose n : ℕ) : ℝ) ≤ Q ^ (1 / (3 * n) : ℝ))
    (s : Finset (Fin n)) :
    Q ^ (-(#s + 1 / 2) : ℝ) ≤
      ∏ i ∈ s, L.successiveInf (c.weight (zero_lt_one.trans_le hQ)) Ω (i + 1) := by
  refine le_trans (Real.rpow_le_rpow_of_exponent_le hQ ?_)
    (L.rpow_mul_card_le_prod_successiveInf c hn hc hQ hQ₁ s (Ω := Ω))
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hsn : (#s : ℝ) ≤ n := by exact_mod_cast (card_le_univ s).trans (by simp)
  have : (#s : ℝ) / (3 * n) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have e : (1 + 1 / (3 * n)) * (#s : ℝ) = #s + #s / (3 * n) := by ring
  linarith

/-- **EF13 Lemma 9.3, upper bound**: `∏_{i ∈ s} λ_i ≤ Q^{n-p+1/2}`, `p = #s`, under (8.3),
(8.4), `n H_L^{C(r,n)} ≤ Q^{1/3n}` and `2^{n(n-1)/2} Δ_L ≤ Q^{1/6}`. -/
theorem prod_successiveInf_le_rpow (hn : 0 < n) (hc₀ : c.sum = 0)
    (hc : (∑ v, ⨆ i, c.arch v i) + ∑ᶠ v, ⨆ i, c.fin v i ≤ 1) {Q : ℝ} (hQ : 1 ≤ Q)
    (hQ₁ : n * L.absFormHeight ^ ((L.forms.card.choose n : ℕ) : ℝ) ≤ Q ^ (1 / (3 * n) : ℝ))
    (hQ₂ : √2 ^ (n * (n - 1)) * L.absDet ≤ Q ^ (1 / 6 : ℝ)) (s : Finset (Fin n)) :
    ∏ i ∈ s, L.successiveInf (c.weight (zero_lt_one.trans_le hQ)) Ω (i + 1) ≤
      Q ^ ((n - #s + 1 / 2) : ℝ) := by
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  set lam := fun i : Fin n ↦ L.successiveInf (c.weight hQ0) Ω (i + 1)
  have hup := L.prod_successiveInf_weight_le (Ω := Ω) hn c hQ0
  rw [hc₀, neg_zero, Real.rpow_zero, mul_one] at hup
  have hlow := L.rpow_mul_card_le_prod_successiveInf c hn hc hQ hQ₁ sᶜ (Ω := Ω)
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hsc : (#sᶜ : ℝ) = n - #s := by
    rw [card_compl, Fintype.card_fin, Nat.cast_sub (by simpa using card_le_univ s)]
  rw [hsc] at hlow
  have hP := prod_mul_prod_compl s lam
  set e : ℝ := -(1 + 1 / (3 * n)) * (n - #s)
  have hpos : 0 < Q ^ e := Real.rpow_pos_of_pos hQ0 _
  have hmain : (∏ i ∈ s, lam i) * Q ^ e ≤ Q ^ (1 / 6 : ℝ) :=
    calc (∏ i ∈ s, lam i) * Q ^ e
        ≤ (∏ i ∈ s, lam i) * ∏ i ∈ sᶜ, lam i :=
          mul_le_mul_of_nonneg_left hlow (prod_nonneg fun _ _ ↦ heightInf_nonneg _)
      _ ≤ Q ^ (1 / 6 : ℝ) := by rw [hP]; exact hup.trans hQ₂
  rw [← le_div_iff₀ hpos, div_eq_mul_inv, ← Real.rpow_neg hQ0.le, ← Real.rpow_add hQ0] at hmain
  refine hmain.trans (Real.rpow_le_rpow_of_exponent_le hQ ?_)
  have hsn : (#s : ℝ) ≤ n := by exact_mod_cast (card_le_univ s).trans (by simp)
  have : ((n : ℝ) - #s) / (3 * n) ≤ 1 / 3 := by
    rw [div_le_iff₀ (by positivity)]
    linarith [(Nat.cast_nonneg #s : (0 : ℝ) ≤ #s)]
  have e' : -e = (n - #s) + (n - #s) / (3 * n) := by simp only [e]; ring
  linarith

/-! ### EF13 Lemma 10.3 -/

section Lemma103

variable {k m : ℕ} (S : Splitting K n k m) {Q : ℝ} (hQ : 1 ≤ Q)

omit [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω] in
/-- A point off `T_k = ⋂_{λ > λ_k} T(λ)` has height at least `λ_{k+1}`, at a jump
`λ_k < λ_{k+1}`. -/
theorem le_of_notMem_heightFlag {h : (Fin n → Ω) → ℝ} {k : ℕ} (hkn : k < n)
    (hgap : heightInf Ω h k < heightInf Ω h (k + 1)) {x : Fin n → Ω}
    (hx : x ∉ heightFlag Ω h k) : heightInf Ω h (k + 1) ≤ h x := by
  by_contra hlt
  push Not at hlt
  obtain ⟨μ, h₁, h₂⟩ := exists_between (max_lt hlt hgap)
  refine hx ?_
  rw [← heightSpace_eq_heightFlag (by simpa using hkn) ((le_max_right _ _).trans_lt h₁) h₂]
  exact mem_heightSpace ((le_max_left _ _).trans h₁.le)

omit [IsAlgClosed Ω] in
include hQ in
/-- **`H_{L',c',Q}(y) ≤ n H_{L,c,Q}(φ' y)`**: the forms of `L'` are forms of `L` composed with
`φ'`, with the same exponents. -/
theorem absMulHeight_restrictSystem_le (y : Fin k → Ω) :
    (L.restrictSystem S c).absMulHeight ((L.restrictExp S c).weight (zero_lt_one.trans_le hQ))
      y ≤ n * L.absMulHeight (c.weight (zero_lt_one.trans_le hQ)) (S.inclLin Ω y) := by
  have hsel : ∀ {p : ℕ} (σ : Fin p ↪ Fin n) (f : AbsoluteValue K ℝ) i j,
      f (Splitting.selMat (K := K) σ i j) ≤ 1 := fun σ f i j ↦ by
    simp only [Splitting.selMat, submatrix_apply, id_eq, one_apply]
    split_ifs <;> simp
  have h := absMulHeight_le_of_mul_eq (L₂ := L.restrictSystem S c) (L₁ := L) (Φ₂ := 1)
    (Φ₁ := S.incl) (a₂ := (L.restrictExp S c).weight (zero_lt_one.trans_le hQ))
    (a₁ := c.weight (zero_lt_one.trans_le hQ))
    (Ma := fun v ↦ Splitting.selMat (S.sel (L.arch v) (c.arch v)))
    (Mf := fun v ↦ Splitting.selMat (S.sel (L.fin v) (c.fin v))) (B := fun _ ↦ 1)
    (B' := fun _ ↦ 1)
    (fun v ↦ by rw [Matrix.mul_one, Splitting.selMat_mul]; rfl)
    (fun v ↦ by rw [Matrix.mul_one, Splitting.selMat_mul]; rfl)
    (fun v i j hij ↦ by rw [← Splitting.le_of_selMat_ne_zero hij]; rfl)
    (fun v i j hij ↦ by rw [← Splitting.le_of_selMat_ne_zero hij]; rfl)
    (fun _ ↦ zero_lt_one) (fun _ ↦ zero_lt_one) (fun v i j ↦ hsel _ v.1 i j)
    (fun v i j ↦ hsel _ v.1 i j) (by simp [Function.HasFiniteMulSupport]) (Ω := Ω) y
  simpa [Matrix.map_one _ (map_zero _) (map_one _), Splitting.inclLin_apply] using h

omit [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω] in
/-- `w(T) = Σ c'`: the total exponent of the induced system is the weight of `T = φ'(Ω^k)`. -/
theorem sum_restrictExp {T : Submodule Ω (Fin n → Ω)} (hS : LinearMap.range (S.inclLin Ω) = T) :
    (L.restrictExp S c).sum = L.subspaceWeight c T := by
  rw [← subspaceWeight_top (L.restrictSystem S c) (L.restrictExp S c) (Ω := Ω),
    subspaceWeight_restrictSystem, Submodule.map_top, hS]

/-- The determinant of `L'` at every place is one of the minors `θ` of EF13 (18.1) for the
columns of `φ'`. -/
theorem det_restrictMat_mem_minorSet (A : Matrix (Fin n) (Fin n) K) (hA : A.det ≠ 0)
    (hAf : ∀ i, A i ∈ L.forms) (c' : Fin n → ℝ) :
    (S.restrictMat A c').det ∈ L.minorSet S.incl := by
  have h := S.restrictMat_det_ne_zero c' hA
  rw [restrictMat_eq S c'] at h ⊢
  exact L.det_mem_minorSet (fun s ↦ hAf _) h

omit [NumberField K] [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω] in
/-- `φ'(Ω^k)` is the extension of the span of the columns of `φ'`. -/
theorem range_inclLin_eq_extendPi :
    LinearMap.range (S.inclLin Ω) = (span K (Set.range S.incl.col)).extendPi Ω := by
  rw [Splitting.inclLin, Matrix.range_mulVecLin, Submodule.extendPi_span, ← Set.range_comp]
  rfl

omit [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω] in
/-- **The determinant of `L'` against the minors** (EF13 (10.2)):
`1 ≤ Δ_{L'} (C(n,k)^{[K:ℚ]} H_L H₂(V))^{#θ - 1}`, relative to `K`, `V` the span of the columns
of `φ'`, when `L` contains `X_1, …, X_n`. -/
theorem one_le_mulDet_restrictSystem_mul (hL : L.HasUnitForms) (hkn : k ≤ n) :
    1 ≤ (L.restrictSystem S c).mulDet * ((n.choose k : ℝ) ^ finrank ℚ K * L.mulFormHeight *
      (span K (Set.range S.incl.col)).arakelovMulHeight) ^ (#(L.minorSet S.incl) - 1) := by
  set s := L.minorSet S.incl
  have hs := L.minorSet_nonempty (linearIndependent_incl S)
  have h0 := L.zero_notMem_minorSet (G := S.incl)
  have : Nonempty s := hs.coe_sort
  have hsup : ∀ f : AbsoluteValue K ℝ, 0 < ⨆ e : s, f e := fun f ↦
    (iInf_finset_pos hs h0 f).trans_le
      (ciInf_le_ciSup (Finite.bddBelow_range _) (Finite.bddAbove_range _))
  have hMpos : 0 < mulSupProd s := by
    refine mul_pos (prod_pos fun v _ ↦ pow_pos (hsup v.1) _) ?_
    rw [finprod_eq_prod _ (hasFiniteMulSupport_iSup_finset hs h0)]
    exact prod_pos fun v _ ↦ hsup v.1
  have h1 : mulSupProd s / mulRatioProd s ≤ (L.restrictSystem S c).mulDet :=
    mulSupProd_div_mulRatioProd_le hs h0
      (fun v ↦ L.det_restrictMat_mem_minorSet S _ (L.arch_det_ne_zero v) (L.arch_mem_forms v) _)
      (fun v ↦ L.det_restrictMat_mem_minorSet S _ (L.fin_det_ne_zero v) (L.fin_mem_forms v) _)
  have h2 := mulRatioProd_le hs h0
  have h3 := L.mulSupProd_minorSet_le hL hkn (linearIndependent_incl S)
  have hR := one_le_mulRatioProd hs h0
  have hs1 : #s = #s - 1 + 1 := (Nat.sub_add_cancel (card_pos.2 hs)).symm
  have h4 : (mulSupProd s ^ (#s - 1))⁻¹ ≤ (L.restrictSystem S c).mulDet := by
    refine le_trans (le_of_eq ?_) ((div_le_div_of_nonneg_left hMpos.le
      (zero_lt_one.trans_le hR) h2).trans h1)
    conv_rhs => rw [hs1, pow_succ', ← div_div, div_self hMpos.ne', one_div]
  have hD := (L.restrictSystem S c).mulDet_pos
  rw [inv_le_iff_one_le_mul₀ (pow_pos hMpos _)] at h4
  refine h4.trans ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hMpos.le h3 _) hD.le

end Lemma103

/-- **The product of the first `k` infima** (EF13, proof of Lemma 10.3): if
`λ_1 ≤ ⋯ ≤ λ_n`, `λ_k ≤ q λ_{k+1}` with `0 ≤ q` and `λ_1 ⋯ λ_n ≤ C` with `C ≥ 1`, then
`(λ_1 ⋯ λ_k)^n ≤ q^{k(n-k)} Cⁿ`. -/
theorem prod_range_pow_le {lam : ℕ → ℝ} {n k : ℕ} (hkn : k ≤ n) (h0 : ∀ i, 0 ≤ lam i)
    (hmono : ∀ i j, 1 ≤ i → i ≤ j → j ≤ n → lam i ≤ lam j) {q C : ℝ} (hq : 0 ≤ q)
    (hgap : lam k ≤ q * lam (k + 1)) (hC : 1 ≤ C) (hprod : ∏ i ∈ range n, lam (i + 1) ≤ C) :
    (∏ i ∈ range k, lam (i + 1)) ^ n ≤ q ^ (k * (n - k)) * C ^ n := by
  set P := ∏ i ∈ range k, lam (i + 1)
  set U := ∏ i ∈ Ico k n, lam (i + 1)
  have hP0 : 0 ≤ P := prod_nonneg fun i _ ↦ h0 _
  have hPU : P * U ≤ C := by rwa [prod_range_mul_prod_Ico _ hkn]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [P, range_zero, prod_empty, one_pow, zero_mul, pow_zero, one_mul]
    exact one_le_pow₀ hC
  have hPk : P ≤ lam k ^ k := by
    calc P ≤ ∏ _i ∈ range k, lam k :=
          prod_le_prod₀ (fun i _ ↦ h0 _) fun i hi ↦ hmono _ _ (by omega)
            (by have := mem_range.1 hi; omega) hkn
      _ = lam k ^ k := by rw [prod_const, card_range]
  have hU : lam (k + 1) ^ (n - k) ≤ U := by
    calc lam (k + 1) ^ (n - k) = ∏ _i ∈ Ico k n, lam (k + 1) := by rw [prod_const, Nat.card_Ico]
      _ ≤ U := prod_le_prod₀ (fun i _ ↦ h0 _) fun i hi ↦ by
          have := mem_Ico.1 hi
          exact hmono _ _ (by omega) (by omega) (by omega)
  have hn : n = k + (n - k) := by omega
  calc P ^ n = P ^ k * P ^ (n - k) := by rw [← pow_add, ← hn]
    _ ≤ P ^ k * ((q * lam (k + 1)) ^ k) ^ (n - k) := by
        refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hP0 ?_ _) (pow_nonneg hP0 _)
        exact hPk.trans (pow_le_pow_left₀ (h0 _) hgap _)
    _ = q ^ (k * (n - k)) * (P * lam (k + 1) ^ (n - k)) ^ k := by ring
    _ ≤ q ^ (k * (n - k)) * (P * U) ^ k := by
        gcongr
        exact mul_nonneg hP0 (pow_nonneg (h0 _) _)
    _ ≤ q ^ (k * (n - k)) * C ^ k := by
        gcongr
        exact mul_nonneg hP0 (prod_nonneg fun i _ ↦ h0 _)
    _ ≤ q ^ (k * (n - k)) * C ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hC hkn) (pow_nonneg hq _)

/-- `k (n - k) ≥ n - 1` for `0 < k < n`. -/
theorem sub_one_le_mul_sub {n k : ℕ} (hk0 : 0 < k) (hkn : k < n) :
    (n : ℝ) - 1 ≤ k * (n - k) := by
  have : (n - 1 : ℕ) ≤ k * (n - k) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨l, rfl⟩ : ∃ l, n = j + 1 + l + 1 := ⟨n - (j + 1) - 1, by omega⟩
    simp only [show j + 1 + l + 1 - (j + 1) = l + 1 by omega, show j + 1 + l + 1 - 1 = j + l + 1
      by omega]
    nlinarith
  have h := (Nat.cast_le (α := ℝ)).2 this
  push_cast [Nat.cast_sub hkn.le, Nat.cast_sub (by omega : 1 ≤ n)] at h
  exact h

omit [IsAlgClosed Ω] in
/-- A gap `λ_k ≤ Q^{-δ/(n-1)} λ_{k+1}` with `Q > 1`, `δ > 0` is strict. -/
theorem successiveInf_lt_of_le {a : FormWeight K (Fin n)} {k : ℕ} (hk0 : 0 < k) (hkn : k < n)
    {Q δ : ℝ} (hQ : 1 < Q) (hδ : 0 < δ) (hpos : 0 < L.successiveInf a Ω (k + 1))
    (hgap : L.successiveInf a Ω k ≤ Q ^ (-(δ / (n - 1))) * L.successiveInf a Ω (k + 1)) :
    L.successiveInf a Ω k < L.successiveInf a Ω (k + 1) := by
  have hn1 : (0 : ℝ) < n - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
    linarith
  have hq1 : Q ^ (-(δ / (n - 1))) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hQ (neg_lt_zero.2 (div_pos hδ hn1))
  exact hgap.trans_lt (by nlinarith)

/-- **EF13 Lemma 10.3, the main inequality**: let `(L, c)` satisfy (8.3), (8.4), (8.8), (8.9),
`r ≤ R` forms, `Q > 1`, `δ > 0`, `0 < k < n` with `λ_k ≤ Q^{-δ/(n-1)} λ_{k+1}`, and let `φ'` map
onto `T = T_k(Q)`. With `V` the span of the columns of `φ'` and `h = H₂(V)^{1/[K:ℚ]}`,
`Q^δ ≤ (k^{k/2} nᵏ 2^{n(n-1)/2} H_L)ⁿ (C(n,k) H_L h)^{n Rᵏ}`. -/
theorem rpow_le_mul_arakelovMulHeight (hLs : L.IsNormalSemistable c Ω) {R : ℕ}
    (hR : #L.forms ≤ R) {k m : ℕ} (S : Splitting K n k m) (hk0 : 0 < k) (hkn : k < n)
    {Q δ : ℝ} (hQ : 1 < Q) (hδ : 0 < δ)
    (hgap : L.successiveInf (c.weight (zero_lt_one.trans hQ)) Ω k ≤
      Q ^ (-(δ / (n - 1))) * L.successiveInf (c.weight (zero_lt_one.trans hQ)) Ω (k + 1))
    (hS : LinearMap.range (S.inclLin Ω) = L.infFlag (c.weight (zero_lt_one.trans hQ)) Ω k) :
    Q ^ δ ≤ (√k ^ k * n ^ k * (√2 ^ (n * (n - 1)) * L.absFormHeight)) ^ n *
      (n.choose k * L.absFormHeight *
        (span K (Set.range S.incl.col)).arakelovMulHeight ^ ((finrank ℚ K : ℝ)⁻¹)) ^
          (n * R ^ k) := by
  have hQ1 : 1 ≤ Q := hQ.le
  have hQ0 : 0 < Q := zero_lt_one.trans hQ
  set a := c.weight hQ0
  set lam : ℕ → ℝ := fun i ↦ L.successiveInf a Ω i with hlam
  have hn : 0 < n := by omega
  have hpos : ∀ i, 0 < i → i ≤ n → 0 < lam i := fun i hi hin ↦ by
    have := L.successiveInf_pos a (Ω := Ω) ⟨i - 1, by omega⟩
    simpa [Nat.sub_add_cancel hi] using this
  set θ := δ / (n - 1) with hθdef
  have hn1 : (0 : ℝ) < n - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
    linarith
  have hlt : lam k < lam (k + 1) :=
    L.successiveInf_lt_of_le hk0 hkn hQ hδ (hpos (k + 1) (by omega) (by omega)) hgap
  set T := L.infFlag a Ω k
  have hTk : finrank Ω T = k := finrank_heightFlag (by simpa using hkn) hlt
  have hTne : T ≠ ⊤ := fun h ↦ by
    rw [h, finrank_top, Module.finrank_fin_fun] at hTk
    omega
  set L' := L.restrictSystem S c
  set c' := L.restrictExp S c
  set a' := c'.weight hQ0
  have hc' : c'.sum ≤ 0 := by
    rw [L.sum_restrictExp c S hS]
    exact hLs.subspaceWeight_le T hTne
  -- the infima of `L'`
  have hle : ∀ y, L'.absMulHeight a' y ≤ n * L.absMulHeight a (S.inclLin Ω y) :=
    L.absMulHeight_restrictSystem_le c S hQ1
  have hθoff : ∀ x ∉ T, lam (k + 1) ≤ L.absMulHeight a x := fun x hx ↦
    le_of_notMem_heightFlag hkn hlt hx
  have hinf : ∀ i : Fin k, L'.successiveInf a' Ω (i + 1) ≤ n * lam (i + 1) := fun i ↦
    heightInf_le_mul_of_lt (S.inclLin Ω) hS (Nat.cast_pos.2 hn) hle hθoff (by omega)
      ((heightInf_mono (by omega) (by simp; omega)).trans_lt hlt)
  have hP' := L'.le_prod_successiveInf_weight (Ω := Ω) hk0 c' hQ0
  set P := ∏ i : Fin k, lam (i + 1)
  have hprod' : ∏ i : Fin k, L'.successiveInf a' Ω (i + 1) ≤ (n : ℝ) ^ k * P := by
    calc _ ≤ ∏ i : Fin k, ((n : ℝ) * lam (i + 1)) :=
          prod_le_prod₀ (fun i _ ↦ heightInf_nonneg _) fun i _ ↦ hinf i
      _ = _ := by rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
  have hsk : 0 < √(k : ℝ) ^ k := pow_pos (Real.sqrt_pos.2 (Nat.cast_pos.2 hk0)) _
  have hΔ' : L'.absDet ≤ √k ^ k * n ^ k * P := by
    have h1 : L'.absDet ≤ L'.absDet * Q ^ (-c'.sum) :=
      le_mul_of_one_le_right L'.absDet_pos.le (Real.one_le_rpow hQ1 (neg_nonneg.2 hc'))
    have h2 := hP'.trans hprod'
    rw [inv_mul_le_iff₀ hsk] at h2
    exact h1.trans (h2.trans_eq (by ring))
  -- `P^n ≤ Q^{-δ} (2^{n(n-1)/2} H_L)^n`
  have hH1 : 1 ≤ L.absFormHeight := Real.one_le_rpow L.one_le_mulFormHeight (by positivity)
  set C₁ := √2 ^ (n * (n - 1)) * L.absFormHeight
  have hC₁ : 1 ≤ C₁ :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (Real.one_le_sqrt.2 one_le_two)) hH1
  have hup := L.prod_successiveInf_weight_le (Ω := Ω) hn c hQ0
  rw [hLs.sum_eq_zero, neg_zero, Real.rpow_zero, mul_one] at hup
  have hup' : ∏ i ∈ range n, lam (i + 1) ≤ C₁ := by
    rw [← Fin.prod_univ_eq_prod_range (fun i ↦ lam (i + 1))]
    exact hup.trans (mul_le_mul_of_nonneg_left L.absDet_le_absFormHeight (by positivity))
  have hPn := prod_range_pow_le (lam := lam) hkn.le (fun i ↦ heightInf_nonneg _)
    (fun i j _ hij hj ↦ heightInf_mono hij (by simpa using hj)) (Real.rpow_nonneg hQ0.le _)
    hgap hC₁ hup'
  rw [← Fin.prod_univ_eq_prod_range (fun i ↦ lam (i + 1))] at hPn
  have hqpow : (Q ^ (-θ)) ^ (k * (n - k)) ≤ Q ^ (-δ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]
    refine Real.rpow_le_rpow_of_exponent_le hQ1 ?_
    have h1 := sub_one_le_mul_sub hk0 hkn
    have h2 : θ * (n - 1) = δ := by rw [hθdef]; field_simp
    push_cast [Nat.cast_sub hkn.le]
    nlinarith
  set A := √(k : ℝ) ^ k * n ^ k * C₁
  have hA : L'.absDet ^ n ≤ A ^ n * Q ^ (-δ) :=
    calc L'.absDet ^ n ≤ (√k ^ k * n ^ k * P) ^ n := pow_le_pow_left₀ L'.absDet_pos.le hΔ' n
      _ = (√k ^ k * n ^ k) ^ n * P ^ n := by ring
      _ ≤ (√k ^ k * n ^ k) ^ n * ((Q ^ (-θ)) ^ (k * (n - k)) * C₁ ^ n) := by gcongr
      _ ≤ (√k ^ k * n ^ k) ^ n * (Q ^ (-δ) * C₁ ^ n) := by gcongr
      _ = A ^ n * Q ^ (-δ) := by ring
  -- the minors
  have hone := L.one_le_mulDet_restrictSystem_mul c S hLs.hasUnitForms hkn.le
  set V' := span K (Set.range S.incl.col)
  set d := finrank ℚ K
  have hd0 : d ≠ 0 := finrank_pos.ne'
  set h := V'.arakelovMulHeight ^ ((d : ℝ)⁻¹)
  have hh1 : 1 ≤ h := Real.one_le_rpow V'.one_le_arakelovMulHeight (by positivity)
  set B := (n.choose k : ℝ) * L.absFormHeight * h
  have hB1 : 1 ≤ B := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
    (by exact_mod_cast Nat.choose_pos hkn.le) hH1) hh1
  have hMeq : (n.choose k : ℝ) ^ d * L.mulFormHeight * V'.arakelovMulHeight = B ^ d := by
    rw [mul_pow, mul_pow, absFormHeight, Real.rpow_inv_natCast_pow
      (zero_le_one.trans L.one_le_mulFormHeight) hd0, Real.rpow_inv_natCast_pow
      (zero_le_one.trans V'.one_le_arakelovMulHeight) hd0]
  have hDeq : L'.mulDet = L'.absDet ^ d := by
    rw [absDet, Real.rpow_inv_natCast_pow L'.mulDet_pos.le hd0]
  rw [hMeq, hDeq, ← pow_mul, mul_comm d, pow_mul, ← mul_pow] at hone
  have hone' : 1 ≤ L'.absDet * B ^ (#(L.minorSet S.incl) - 1) := by
    by_contra hlt'
    push Not at hlt'
    exact (pow_lt_one₀ (mul_nonneg L'.absDet_pos.le (pow_nonneg (zero_le_one.trans hB1) _))
      hlt' hd0).not_ge hone
  have hcard : #(L.minorSet S.incl) - 1 ≤ R ^ k :=
    (Nat.sub_le _ _).trans ((L.card_minorSet_le _).trans (Nat.pow_le_pow_left hR k))
  have hQδ : 0 < Q ^ δ := Real.rpow_pos_of_pos hQ0 _
  calc Q ^ δ = Q ^ δ * 1 ^ n := by rw [one_pow, mul_one]
    _ ≤ Q ^ δ * (L'.absDet * B ^ (#(L.minorSet S.incl) - 1)) ^ n := by gcongr
    _ = Q ^ δ * L'.absDet ^ n * B ^ (n * (#(L.minorSet S.incl) - 1)) := by
        rw [mul_pow, ← pow_mul, mul_comm (#(L.minorSet S.incl) - 1)]
        ring
    _ ≤ Q ^ δ * (A ^ n * Q ^ (-δ)) * B ^ (n * R ^ k) := by
        gcongr
    _ = A ^ n * B ^ (n * R ^ k) := by
        rw [Real.rpow_neg hQ0.le]
        field_simp

/-- The constant of EF13 Lemma 10.3: `k^{k/2} nᵏ 2^{n(n-1)/2} H ≤ 2^{3n²} H`. -/
theorem sqrt_pow_mul_pow_mul_le {n k : ℕ} (hkn : k ≤ n) {H : ℝ} (hH : 0 ≤ H) :
    √(k : ℝ) ^ k * n ^ k * (√2 ^ (n * (n - 1)) * H) ≤ 2 ^ (3 * n ^ 2) * H := by
  have h2n : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast n.lt_two_pow_self.le
  have hpow : ∀ x : ℝ, 0 ≤ x → x ≤ n → x ^ k ≤ 2 ^ (n ^ 2) := fun x hx0 hx ↦
    calc x ^ k ≤ (2 ^ n : ℝ) ^ k := pow_le_pow_left₀ hx0 (hx.trans h2n) _
      _ ≤ (2 ^ n : ℝ) ^ n := pow_le_pow_right₀ (one_le_pow₀ one_le_two) hkn
      _ = 2 ^ (n ^ 2) := by rw [← pow_mul, sq]
  have hk : √(k : ℝ) ≤ n := by
    refine (Real.sqrt_le_sqrt (by exact_mod_cast hkn : (k : ℝ) ≤ n)).trans ?_
    exact Real.sqrt_le_iff.2 ⟨Nat.cast_nonneg _, by exact_mod_cast Nat.le_self_pow two_ne_zero n⟩
  have hs : √(2 : ℝ) ^ (n * (n - 1)) ≤ 2 ^ (n ^ 2) :=
    (pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩) _).trans
      (pow_le_pow_right₀ one_le_two (by rw [sq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)))
  calc √(k : ℝ) ^ k * n ^ k * (√2 ^ (n * (n - 1)) * H)
      ≤ 2 ^ (n ^ 2) * 2 ^ (n ^ 2) * (2 ^ (n ^ 2) * H) := by
        gcongr
        · exact hpow _ (Real.sqrt_nonneg _) hk
        · exact hpow _ (Nat.cast_nonneg _) le_rfl
    _ = 2 ^ (3 * n ^ 2) * H := by ring

/-- **EF13 Lemma 10.3**, relative to `K`: under (8.3), (8.4), (8.8), (8.9), with `r ≤ R` forms,
`n ≤ R`, `Q > 1`, `δ > 0`, a gap `λ_k ≤ Q^{-δ/(n-1)} λ_{k+1}` at `0 < k < n`, and `Q` large,
`(2^{3n²} H_L)^{3nRⁿ} ≤ Q^δ`, the subspace `V ⊆ Kⁿ` with `V ⊗ Ω = T_k(Q)` has
`H₂(V)^{1/[K:ℚ]} ≥ Q^{δ/3Rⁿ}`. EF13's `λ_1 ≤ Q^{-δ}` is only used to find the gap. -/
theorem rpow_le_arakelovMulHeight_infFlag (hLs : L.IsNormalSemistable c Ω) {R : ℕ}
    (hR : #L.forms ≤ R) (hnR : n ≤ R) {k : ℕ} (hk0 : 0 < k) (hkn : k < n) {Q δ : ℝ}
    (hQ : 1 < Q) (hδ : 0 < δ)
    (hgap : L.successiveInf (c.weight (zero_lt_one.trans hQ)) Ω k ≤
      Q ^ (-(δ / (n - 1))) * L.successiveInf (c.weight (zero_lt_one.trans hQ)) Ω (k + 1))
    (hbig : (2 ^ (3 * n ^ 2) * L.absFormHeight) ^ (3 * n * R ^ n) ≤ Q ^ δ)
    {V : Submodule K (Fin n → K)}
    (hV : V.extendPi Ω = L.infFlag (c.weight (zero_lt_one.trans hQ)) Ω k) :
    Q ^ (δ / (3 * R ^ n)) ≤ V.arakelovMulHeight ^ ((finrank ℚ K : ℝ)⁻¹) := by
  have hQ0 : 0 < Q := zero_lt_one.trans hQ
  set a := c.weight hQ0
  set T := L.infFlag a Ω k
  have hpos : 0 < L.successiveInf a Ω (k + 1) := by
    have := L.successiveInf_pos a (Ω := Ω) ⟨k, hkn⟩
    simpa using this
  have hlt := L.successiveInf_lt_of_le hk0 hkn hQ hδ hpos hgap
  have hTk : finrank Ω T = k := finrank_heightFlag (by simpa using hkn) hlt
  have hTK : T.IsDefinedOver K := hV ▸ Submodule.isDefinedOver_extendPi V
  obtain ⟨S, hS⟩ := Splitting.exists_range_inclLin hTK
  revert S
  rw [hTk]
  intro S hS
  have hVS : span K (Set.range S.incl.col) = V :=
    Submodule.extendPi_injective (Ω := Ω) (by rw [← range_inclLin_eq_extendPi, hS, hV])
  have hmain := L.rpow_le_mul_arakelovMulHeight c hLs hR S hk0 hkn hQ hδ hgap hS
  rw [hVS] at hmain
  set d := finrank ℚ K
  set h := V.arakelovMulHeight ^ ((d : ℝ)⁻¹)
  have hh1 : 1 ≤ h := Real.one_le_rpow V.one_le_arakelovMulHeight (by positivity)
  have hH1 : 1 ≤ L.absFormHeight := Real.one_le_rpow L.one_le_mulFormHeight (by positivity)
  set X : ℝ := 2 ^ (3 * n ^ 2) * L.absFormHeight
  have hX1 : 1 ≤ X := one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) hH1
  have hR2 : 2 ≤ R := by omega
  have hRk : n * R ^ k ≤ R ^ n :=
    calc n * R ^ k ≤ R * R ^ k := Nat.mul_le_mul_right _ hnR
      _ = R ^ (k + 1) := by ring
      _ ≤ R ^ n := Nat.pow_le_pow_right (by omega) hkn
  have hexp : n + n * R ^ k ≤ n * R ^ n := by
    have : 1 + R ^ k ≤ R ^ n := by
      have h1 : 2 * R ^ k ≤ R ^ (k + 1) := by
        rw [pow_succ, mul_comm]
        exact Nat.mul_le_mul_left _ hR2
      have h2 : R ^ (k + 1) ≤ R ^ n := Nat.pow_le_pow_right (by omega) hkn
      have h3 : 1 ≤ R ^ k := Nat.one_le_pow _ _ (by omega)
      omega
    nlinarith
  have hA : √(k : ℝ) ^ k * n ^ k * (√2 ^ (n * (n - 1)) * L.absFormHeight) ≤ X :=
    sqrt_pow_mul_pow_mul_le hkn.le (zero_le_one.trans hH1)
  have hC : (n.choose k : ℝ) * L.absFormHeight ≤ X := by
    refine mul_le_mul_of_nonneg_right ?_ (zero_le_one.trans hH1)
    calc (n.choose k : ℝ) ≤ 2 ^ n := by exact_mod_cast n.choose_le_two_pow k
      _ ≤ 2 ^ (3 * n ^ 2) := pow_le_pow_right₀ one_le_two (by nlinarith)
  by_contra hcon
  push Not at hcon
  -- `h^{n Rᵏ} ≤ Q^{δ/3}`
  have hh : h ^ (n * R ^ k) ≤ Q ^ (δ / 3) := by
    calc h ^ (n * R ^ k) ≤ (Q ^ (δ / (3 * R ^ n))) ^ (n * R ^ k) :=
          pow_le_pow_left₀ (zero_le_one.trans hh1) hcon.le _
      _ = Q ^ (δ / (3 * R ^ n) * (n * R ^ k : ℕ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]
      _ ≤ Q ^ (δ / 3) := by
          refine Real.rpow_le_rpow_of_exponent_le hQ.le ?_
          have hRn : (0 : ℝ) < R ^ n := by positivity
          have hRk' : ((n * R ^ k : ℕ) : ℝ) ≤ R ^ n := by exact_mod_cast hRk
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  have hXn : X ^ (n * R ^ n) ≤ Q ^ (δ / 3) := by
    have h1 : (X ^ (n * R ^ n)) ^ 3 ≤ (Q ^ (δ / 3)) ^ 3 := by
      rw [← pow_mul, ← Real.rpow_natCast (Q ^ (δ / 3)), ← Real.rpow_mul hQ0.le]
      convert hbig using 2
      · ring
      · push_cast; ring
    exact (pow_le_pow_iff_left₀ (pow_nonneg (zero_le_one.trans hX1) _)
      (Real.rpow_nonneg hQ0.le _) (by norm_num)).1 h1
  have hbound : Q ^ δ ≤ X ^ (n * R ^ n) * Q ^ (δ / 3) :=
    calc Q ^ δ ≤ _ := hmain
      _ ≤ X ^ n * (X * h) ^ (n * R ^ k) := by
          gcongr
      _ = X ^ (n + n * R ^ k) * h ^ (n * R ^ k) := by rw [mul_pow, pow_add]; ring
      _ ≤ X ^ (n * R ^ n) * Q ^ (δ / 3) := by
          gcongr
  have : Q ^ δ ≤ Q ^ (δ / 3) * Q ^ (δ / 3) :=
    hbound.trans (mul_le_mul_of_nonneg_right hXn (Real.rpow_nonneg hQ0.le _))
  rw [← Real.rpow_add hQ0] at this
  have := (Real.rpow_le_rpow_left_iff hQ).1 this
  linarith

end FormSystem

end NumberField
