/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.FormInducedSystem
public import QuantitativeSubspace.FormMinkowski

/-!
# The semistable case of the limit of the successive infima

J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative Subspace Theorem*,
Ann. of Math. **177** (2013), 513–590, Lemma 16.4 and the reductions of §8 it uses
(Lemmas 7.2, 7.3 and the remark after 7.3).

EF13 Lemma 16.4: if `μ(Ωⁿ, U) ≥ μ(Ωⁿ, 0)` for every proper subspace `U` (16.11), then for every
`δ > 0` and `Q` large, `H_{L,c,Q}(x) ≥ Q^{-μ(Ωⁿ, 0) - δ}` for all `x ≠ 0`. EF13 reduces this to
Theorem 8.1 by normalizing `(L, c)`: shift the exponents at each place to sum `0` (8.3), divide
them so that `Σ_v max_i c_iv ≤ 1` (8.4), and change coordinates so that `L^{(v₀)}` is the identity
at a finite place `v₀` with `c_{v₀} = 0` (8.8). Then (16.11) becomes `w(U) ≤ 0` (8.9).

Theorem 8.1 is proved in EF13 §§9–14, which is milestone Q4.1 of
`QuantitativeSubspace/README.md`. Its qualitative content is the hypothesis
`NumberField.SemistableGap` here: under (8.1)–(8.9), `H_{L,c,Q}(x) > Q^{-δ}` for all `x ≠ 0` once
`Q` is large.

## Main definitions

* `NumberField.SemistableGap K Ω`: the qualitative EF13 Theorem 8.1.
* `NumberField.FormExponent.center`, `NumberField.FormExponent.divConst`: the normalizations
  (8.3), (8.4).

## Main results

* `NumberField.FinitePlace.infinite`: a number field has infinitely many finite places.
* `NumberField.FormSystem.subspaceWeight_top`: `w(Ωⁿ) = Σ_v Σ_i c_iv`.
* `NumberField.FormSystem.subspaceWeight_center`, `NumberField.FormSystem.subspaceWeight_divConst`:
  the weight under the normalizations (EF13 Lemma 7.2 (ii)).
* `NumberField.FormSystem.exists_lt_absMulHeight_of_semistable`: EF13 Lemma 16.4, the lower
  bound, from `NumberField.SemistableGap`.

This is part of milestone Q3.5 of `QuantitativeSubspace/README.md`.
-/

@[expose] public section

open Module Finset Matrix

namespace NumberField

/-! ### Infinitely many finite places -/

namespace FinitePlace

variable {K : Type*} [Field K] [NumberField K]

/-- Some finite place divides `p > 1`, by the product formula. -/
theorem exists_apply_natCast_lt_one {p : ℕ} (hp : 1 < p) : ∃ v : FinitePlace K, v p < 1 := by
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h := prod_abs_eq_one hp0
  have harch : ∏ w : InfinitePlace K, w (p : K) ^ w.mult = (p : ℝ) ^ finrank ℚ K := by
    simp [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]
  by_contra hall
  push Not at hall
  have hsupp := FinitePlace.hasFiniteMulSupport hp0
  have h1 : 1 ≤ ∏ᶠ w : FinitePlace K, w (p : K) := by
    rw [finprod_eq_prod _ hsupp]
    exact Finset.one_le_prod₀ fun w _ ↦ hall w
  have h2 : (1 : ℝ) < (p : ℝ) ^ finrank ℚ K :=
    one_lt_pow₀ (by exact_mod_cast hp) Module.finrank_pos.ne'
  rw [harch] at h
  nlinarith

/-- A number field has infinitely many finite places: distinct primes are divisible by distinct
places. -/
instance infinite : Infinite (FinitePlace K) := by
  have : Infinite {p : ℕ // p.Prime} := Nat.infinite_setOfPred_prime.to_subtype
  choose f hf using fun p : {p : ℕ // p.Prime} ↦ exists_apply_natCast_lt_one (K := K) p.2.one_lt
  refine Infinite.of_injective f fun p q hpq ↦ Subtype.ext ?_
  by_contra hne
  have hcop : Nat.Coprime p q := (Nat.coprime_primes p.2 q.2).2 hne
  have hbez := Nat.gcd_eq_gcd_ab p q
  rw [hcop.gcd_eq_one, Nat.cast_one] at hbez
  set v := f p
  have hv : v (q : K) < 1 := hpq ▸ hf q
  have h1 : v (((p : ℤ) * Nat.gcdA p q + (q : ℤ) * Nat.gcdB p q : ℤ) : K) < 1 := by
    have hnv : IsNonarchimedean v.1 := fun a b ↦ FinitePlace.add_le v a b
    push_cast
    refine (hnv _ _).trans_lt (max_lt ?_ ?_)
    · rw [map_mul]
      calc v.1 (p : K) * v.1 (Nat.gcdA p q : K) ≤ v.1 (p : K) * 1 :=
            mul_le_mul_of_nonneg_left (apply_intCast_le_one v _) (apply_nonneg _ _)
        _ < 1 := by rw [mul_one]; exact hf p
    · rw [map_mul]
      calc v.1 (q : K) * v.1 (Nat.gcdB p q : K) ≤ v.1 (q : K) * 1 :=
            mul_le_mul_of_nonneg_left (apply_intCast_le_one v _) (apply_nonneg _ _)
        _ < 1 := by rw [mul_one]; exact hv
  rw [← hbez, Int.cast_one, map_one] at h1
  exact lt_irrefl _ h1

end FinitePlace

/-! ### Normalizing the exponents -/

namespace FormExponent

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} (c : FormExponent K ι)

/-- The finite places where `c` does not vanish. -/
noncomputable def finSupport : Finset (FinitePlace K) := c.finite_setOf_fin_ne_zero.toFinset

theorem mem_finSupport {v : FinitePlace K} (h : c.fin v ≠ 0) : v ∈ c.finSupport := by
  simpa [finSupport] using h

/-- A sum over the finite places of a function of `c_v` vanishing at `0`. -/
theorem finsum_eq_sum (g : (ι → ℝ) → ℝ) (hg : g 0 = 0) {s : Finset (FinitePlace K)}
    (hs : ∀ v, c.fin v ≠ 0 → v ∈ s) : ∑ᶠ v, g (c.fin v) = ∑ v ∈ s, g (c.fin v) := by
  refine finsum_eq_sum_of_support_subset _ fun v hv ↦ hs v fun h ↦ hv ?_
  simp [h, hg]

/-- **The exponents centered at each place** (EF13 (8.3)): `c_iv - (Σ_j c_jv) / n`. -/
noncomputable def center [Fintype ι] : FormExponent K ι where
  arch v i := c.arch v i - (∑ j, c.arch v j) / Fintype.card ι
  fin v i := c.fin v i - (∑ j, c.fin v j) / Fintype.card ι
  finite_setOf_fin_ne_zero := c.finite_setOf_fin_ne_zero.subset fun v hv h ↦ hv <| by
    funext i
    simp [h]

/-- **The exponents divided by `s`** (EF13 (8.4)). -/
noncomputable def divConst (s : ℝ) : FormExponent K ι where
  arch v i := c.arch v i / s
  fin v i := c.fin v i / s
  finite_setOf_fin_ne_zero := c.finite_setOf_fin_ne_zero.subset fun v hv h ↦ hv <| by
    funext i
    simp [h]

theorem sum_center_arch [Fintype ι] [Nonempty ι] (v : InfinitePlace K) :
    ∑ i, c.center.arch v i = 0 := by
  have : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp only [center, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
  field_simp
  ring

theorem sum_center_fin [Fintype ι] [Nonempty ι] (v : FinitePlace K) :
    ∑ i, c.center.fin v i = 0 := by
  have : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp only [center, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
  field_simp
  ring

theorem center_fin_eq_zero [Fintype ι] {v : FinitePlace K} (h : c.fin v = 0) :
    c.center.fin v = 0 := by
  funext i
  simp [center, h]

theorem divConst_fin_eq_zero {s : ℝ} {v : FinitePlace K} (h : c.fin v = 0) :
    (c.divConst s).fin v = 0 := by
  funext i
  simp [divConst, h]

/-- `(Q^s)^{c/s} = Q^c`. -/
theorem weight_divConst {s : ℝ} (hs : 0 < s) {Q : ℝ} (hQ : 0 < Q) :
    (c.divConst s).weight (Real.rpow_pos_of_pos hQ s) = c.weight hQ := by
  simp only [weight, divConst]
  congr 1 <;> funext v i <;> rw [← Real.rpow_mul hQ.le] <;> congr 1 <;> field_simp

/-- `Σ_v max_i (c_iv / s) = (Σ_v max_i c_iv) / s`. -/
theorem sum_iSup_divConst [Nonempty ι] {s : ℝ} (hs : 0 < s) :
    (∑ v, ⨆ i, (c.divConst s).arch v i) + ∑ᶠ v, ⨆ i, (c.divConst s).fin v i =
      ((∑ v, ⨆ i, c.arch v i) + ∑ᶠ v, ⨆ i, c.fin v i) / s := by
  have hdiv : ∀ f : ι → ℝ, ⨆ i, f i / s = (⨆ i, f i) / s := fun f ↦ by
    simp only [div_eq_mul_inv]
    exact (Real.iSup_mul_of_nonneg (inv_nonneg.2 hs.le) f).symm
  have hs' : ∀ v, (c.divConst s).fin v ≠ 0 → v ∈ c.finSupport := fun v hv ↦
    c.mem_finSupport fun h ↦ hv (c.divConst_fin_eq_zero h)
  rw [(c.divConst s).finsum_eq_sum (fun f ↦ ⨆ i, f i) (by simp) hs',
    c.finsum_eq_sum (fun f ↦ ⨆ i, f i) (by simp) fun v hv ↦ c.mem_finSupport hv]
  simp only [divConst, hdiv, add_div, sum_div]

theorem sum_divConst [Fintype ι] {s : ℝ} : (c.divConst s).sum = c.sum / s := by
  have hs' : ∀ v, (c.divConst s).fin v ≠ 0 → v ∈ c.finSupport := fun v hv ↦
    c.mem_finSupport fun h ↦ hv (c.divConst_fin_eq_zero h)
  rw [sum, sum, (c.divConst s).finsum_eq_sum (fun f ↦ ∑ i, f i) (by simp) hs',
    c.finsum_eq_sum (fun f ↦ ∑ i, f i) (by simp) fun v hv ↦ c.mem_finSupport hv]
  simp only [divConst, ← sum_div, add_div]

theorem weight_congr {Q Q' : ℝ} (h : Q = Q') (hQ : 0 < Q) (hQ' : 0 < Q') :
    c.weight hQ = c.weight hQ' := by
  subst h
  rfl

end FormExponent

namespace FormSystem

variable {K : Type*} [Field K] [NumberField K] {n : ℕ} (L : FormSystem K (Fin n))
  (c : FormExponent K (Fin n)) {Ω : Type*} [Field Ω] [Algebra K Ω]

/-- **The weight of the whole space** is `Σ_v Σ_i c_iv`. -/
theorem subspaceWeight_top : L.subspaceWeight (Ω := Ω) c ⊤ = c.sum := by
  rw [subspaceWeight_eq_sum_of_subset L c c.finSupport (fun v hv ↦ c.mem_finSupport hv),
    FormExponent.sum, c.finsum_eq_sum (fun f ↦ ∑ i, f i) (by simp)
      (fun v hv ↦ c.mem_finSupport hv)]
  have hcard : Fintype.card (Fin n) = finrank Ω (Fin n → Ω) := by simp
  congr 1
  · exact sum_congr rfl fun v _ ↦
      Submodule.formWeight_top _ _ (iInf_ker_matrixForms (L.arch_det_ne_zero v)) hcard
  · exact sum_congr rfl fun v _ ↦
      Submodule.formWeight_top _ _ (iInf_ker_matrixForms (L.fin_det_ne_zero v)) hcard

theorem subspaceWeight_bot : L.subspaceWeight (Ω := Ω) c ⊥ = 0 := by
  simp [subspaceWeight, Submodule.formWeight_bot]

/-- **EF13 Lemma 7.2 (ii)** for the centered exponents:
`w_{L,c'}(U) = w_{L,c}(U) - dim U · α / n`, `α = Σ_v Σ_i c_iv`. -/
theorem subspaceWeight_center (U : Submodule Ω (Fin n → Ω)) :
    L.subspaceWeight c.center U = L.subspaceWeight c U - finrank Ω U * (c.sum / n) := by
  have hs' : ∀ v, c.center.fin v ≠ 0 → v ∈ c.finSupport := fun v hv ↦
    c.mem_finSupport fun h ↦ hv (c.center_fin_eq_zero h)
  rw [subspaceWeight_eq_sum_of_subset L c.center c.finSupport hs',
    subspaceWeight_eq_sum_of_subset L c c.finSupport (fun v hv ↦ c.mem_finSupport hv),
    FormExponent.sum, c.finsum_eq_sum (fun f ↦ ∑ i, f i) (by simp)
      (fun v hv ↦ c.mem_finSupport hv)]
  have ha : ∀ v, Submodule.formWeight (matrixForms (Ω := Ω) (L.arch v)) (c.center.arch v) U =
      Submodule.formWeight (matrixForms (L.arch v)) (c.arch v) U -
        (∑ j, c.arch v j) / n * finrank Ω U := fun v ↦ by
    have := Submodule.formWeight_sub_const (matrixForms (Ω := Ω) (L.arch v)) (c.arch v)
      (iInf_ker_matrixForms (L.arch_det_ne_zero v)) ((∑ j, c.arch v j) / n) U
    simpa [FormExponent.center] using this
  have hf : ∀ v, Submodule.formWeight (matrixForms (Ω := Ω) (L.fin v)) (c.center.fin v) U =
      Submodule.formWeight (matrixForms (L.fin v)) (c.fin v) U -
        (∑ j, c.fin v j) / n * finrank Ω U := fun v ↦ by
    have := Submodule.formWeight_sub_const (matrixForms (Ω := Ω) (L.fin v)) (c.fin v)
      (iInf_ker_matrixForms (L.fin_det_ne_zero v)) ((∑ j, c.fin v j) / n) U
    simpa [FormExponent.center] using this
  rw [sum_congr rfl fun v _ ↦ ha v, sum_congr rfl fun v _ ↦ hf v, sum_sub_distrib,
    sum_sub_distrib, ← sum_mul, ← sum_mul, ← sum_div, ← sum_div]
  ring

/-- **EF13 Lemma 7.2 (ii)** for the divided exponents: `w_{L,c/s}(U) = w_{L,c}(U) / s`. -/
theorem subspaceWeight_divConst {s : ℝ} (hs : 0 < s) (U : Submodule Ω (Fin n → Ω)) :
    L.subspaceWeight (c.divConst s) U = L.subspaceWeight c U / s := by
  have hs' : ∀ v, (c.divConst s).fin v ≠ 0 → v ∈ c.finSupport := fun v hv ↦
    c.mem_finSupport fun h ↦ hv (c.divConst_fin_eq_zero h)
  rw [subspaceWeight_eq_sum_of_subset L (c.divConst s) c.finSupport hs',
    subspaceWeight_eq_sum_of_subset L c c.finSupport (fun v hv ↦ c.mem_finSupport hv)]
  have ha : ∀ v, Submodule.formWeight (matrixForms (Ω := Ω) (L.arch v)) ((c.divConst s).arch v)
      U = Submodule.formWeight (matrixForms (L.arch v)) (c.arch v) U / s := fun v ↦ by
    have := Submodule.formWeight_div_const (matrixForms (Ω := Ω) (L.arch v)) (c.arch v)
      (iInf_ker_matrixForms (L.arch_det_ne_zero v)) hs U
    simpa [FormExponent.divConst] using this
  have hf : ∀ v, Submodule.formWeight (matrixForms (Ω := Ω) (L.fin v)) ((c.divConst s).fin v)
      U = Submodule.formWeight (matrixForms (L.fin v)) (c.fin v) U / s := fun v ↦ by
    have := Submodule.formWeight_div_const (matrixForms (Ω := Ω) (L.fin v)) (c.fin v)
      (iInf_ker_matrixForms (L.fin_det_ne_zero v)) hs U
    simpa [FormExponent.divConst] using this
  rw [sum_congr rfl fun v _ ↦ ha v, sum_congr rfl fun v _ ↦ hf v, ← sum_div, ← sum_div, add_div]

variable [Algebra.IsAlgebraic K Ω]

/-- **EF13 Lemma 7.2 (i)** for the centered exponents: `H_{L,c',Q} = Q^{α/n} H_{L,c,Q}`. -/
theorem absMulHeight_center {Q : ℝ} (hQ : 0 < Q) (x : Fin n → Ω) :
    L.absMulHeight (c.center.weight hQ) x = Q ^ (c.sum / n) * L.absMulHeight (c.weight hQ) x := by
  have hθ : (Function.support fun v : FinitePlace K ↦ (∑ j, c.fin v j) / n).Finite :=
    c.finite_setOf_fin_ne_zero.subset fun v hv h ↦ hv (by simp [h])
  rw [L.absMulHeight_weight_of_sub hθ (c := c) (d := c.center)
    (θa := fun v ↦ (∑ j, c.arch v j) / n) (fun v i ↦ by simp [FormExponent.center])
    (fun v i ↦ by simp [FormExponent.center]) hQ x]
  congr 2
  rw [FormExponent.sum, c.finsum_eq_sum (fun f ↦ ∑ i, f i) (by simp)
      (fun v hv ↦ c.mem_finSupport hv),
    c.finsum_eq_sum (fun f ↦ (∑ i, f i) / n) (by simp) (fun v hv ↦ c.mem_finSupport hv),
    add_div, sum_div, sum_div]

end FormSystem

/-! ### EF13 Lemma 16.4 -/

/-- `Q^{-δ} < κ` for `Q` large. -/
theorem exists_rpow_neg_lt {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) :
    ∃ Q₀, ∀ Q, Q₀ ≤ Q → Q ^ (-δ) < κ :=
  Filter.eventually_atTop.1 ((tendsto_rpow_neg_atTop hδ).eventually (gt_mem_nhds hκ))

/-- **The qualitative content of EF13 Theorem 8.1** (proved in Q4.1): if `n ≥ 2` and `(L, c)`
satisfies (8.3) `Σ_i c_iv = 0`, (8.4) `Σ_v max_i c_iv ≤ 1`, (8.8) `L^{(v₀)} = (X_1, …, X_n)` and
`c_{v₀} = 0` at a finite place `v₀`, and (8.9) `w(U) ≤ 0` for every proper subspace `U`, then for
every `0 < δ ≤ 1` there are no nonzero points with `H_{L,c,Q}(x) ≤ Q^{-δ}` once `Q` is large. EF13
(8.10)–(8.11) bound the exceptional `Q` by finitely many intervals `[Q_h, Q_h^{ω₂})`. -/
def SemistableGap (K : Type*) [Field K] [NumberField K] (Ω : Type*) [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] : Prop :=
  ∀ (n : ℕ) (L : FormSystem K (Fin n)) (c : FormExponent K (Fin n)), 2 ≤ n →
    (∀ v, ∑ i, c.arch v i = 0) → (∀ v, ∑ i, c.fin v i = 0) →
    (∑ v, ⨆ i, c.arch v i) + ∑ᶠ v, ⨆ i, c.fin v i ≤ 1 →
    (∃ v₀ : FinitePlace K, L.fin v₀ = 1 ∧ c.fin v₀ = 0) →
    (∀ U : Submodule Ω (Fin n → Ω), U ≠ ⊤ → L.subspaceWeight c U ≤ 0) →
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ Q₀ : ℝ, ∀ (Q : ℝ) (hQ : 1 ≤ Q), Q₀ ≤ Q →
      ∀ x : Fin n → Ω, x ≠ 0 → Q ^ (-δ) < L.absMulHeight (c.weight (zero_lt_one.trans_le hQ)) x

namespace FormSystem

variable {K : Type*} [Field K] [NumberField K] {n : ℕ} (L : FormSystem K (Fin n))
  (c : FormExponent K (Fin n)) {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]

omit [Algebra.IsAlgebraic K Ω] in
/-- `μ(Ωⁿ, 0) = α / n`. -/
theorem weightSlope_bot_top :
    Submodule.weightSlope (L.subspaceWeight (Ω := Ω) c) ⊥ ⊤ = c.sum / n := by
  rw [Submodule.weightSlope, subspaceWeight_top, subspaceWeight_bot, finrank_top, finrank_bot,
    Module.finrank_fin_fun]
  simp

/-- **EF13 Lemma 16.4**, the lower bound, from the qualitative Theorem 8.1: if
`μ(Ωⁿ, U) ≥ μ(Ωⁿ, 0)` for every proper `U` (16.11), then for `δ > 0` and `Q` large,
`H_{L,c,Q}(x) > Q^{-μ(Ωⁿ, 0) - δ}` for every `x ≠ 0`. -/
theorem exists_lt_absMulHeight_of_semistable (hgap : SemistableGap K Ω) (hn : 0 < n)
    (h16 : ∀ U : Submodule Ω (Fin n → Ω), U < ⊤ →
      Submodule.weightSlope (L.subspaceWeight (Ω := Ω) c) ⊥ ⊤ ≤
        Submodule.weightSlope (L.subspaceWeight c) U ⊤)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ Q₀, ∀ (Q : ℝ) (hQ : 1 ≤ Q), Q₀ ≤ Q → ∀ x : Fin n → Ω, x ≠ 0 →
      Q ^ (-(c.sum / n) - δ) < L.absMulHeight (c.weight (zero_lt_one.trans_le hQ)) x := by
  set μ := c.sum / n
  rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn2
  · -- One variable: EF13 Lemma 7.1, with `θ = α`.
    set κ := (Fintype.card (Fin 1) : ℝ)⁻¹ *
      L.absFormHeight ^ (-((L.forms.card.choose (Fintype.card (Fin 1)) : ℕ) : ℝ))
    have hκ : 0 < κ := mul_pos (by simp)
      (Real.rpow_pos_of_pos (zero_lt_one.trans_le (Real.one_le_rpow L.one_le_mulFormHeight
        (by positivity))) _)
    have hθ : (∑ v, ⨆ i, c.arch v i) + ∑ᶠ v, ⨆ i, c.fin v i = c.sum := by
      simp [FormExponent.sum, ciSup_unique]
    obtain ⟨Q₀, hQ₀⟩ := exists_rpow_neg_lt hκ hδ
    refine ⟨Q₀, fun Q hQ hQ₀Q x hx ↦ ?_⟩
    have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
    have h := L.le_absMulHeight_weight c hQ hx
    rw [hθ] at h
    calc Q ^ (-μ - δ) = Q ^ (-δ) * Q ^ (-c.sum) := by
          rw [← Real.rpow_add hQ0]
          simp [μ]
          ring_nf
      _ < κ * Q ^ (-c.sum) := mul_lt_mul_of_pos_right (hQ₀ Q hQ₀Q) (Real.rpow_pos_of_pos hQ0 _)
      _ ≤ _ := h
  -- Normalize: center the exponents (8.3), divide them (8.4), and move to `v₀` (8.8).
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set c₁ := c.center
  set θ := (∑ v, ⨆ i, c₁.arch v i) + ∑ᶠ v, ⨆ i, c₁.fin v i
  set s := max θ 1
  have hs : 0 < s := zero_lt_one.trans_le (le_max_right _ _)
  set c₂ := c₁.divConst s
  obtain ⟨v₀, hv₀⟩ := c.finite_setOf_fin_ne_zero.infinite_compl.nonempty
  have hv₀ : c.fin v₀ = 0 := by simpa using hv₀
  set A := L.fin v₀
  have hA : A.det ≠ 0 := L.fin_det_ne_zero v₀
  set P := A⁻¹
  have hP : P.det ≠ 0 := (Matrix.isUnit_nonsing_inv_det A (Ne.isUnit hA)).ne_zero
  set L₃ := L.comp P hP
  have hL₃ : L₃.fin v₀ = 1 := Matrix.mul_nonsing_inv A (Ne.isUnit hA)
  have hc₂v₀ : c₂.fin v₀ = 0 := c₁.divConst_fin_eq_zero (c.center_fin_eq_zero hv₀)
  have harch : ∀ v, ∑ i, c₂.arch v i = 0 := fun v ↦ by
    simp only [c₂, FormExponent.divConst, ← sum_div, c.sum_center_arch v, zero_div, c₁]
  have hfin : ∀ v, ∑ i, c₂.fin v i = 0 := fun v ↦ by
    simp only [c₂, FormExponent.divConst, ← sum_div, c.sum_center_fin v, zero_div, c₁]
  have hmax : (∑ v, ⨆ i, c₂.arch v i) + ∑ᶠ v, ⨆ i, c₂.fin v i ≤ 1 := by
    rw [c₁.sum_iSup_divConst hs, div_le_one hs]
    exact le_max_left _ _
  have hμ := L.weightSlope_bot_top c (Ω := Ω)
  have hw : ∀ U : Submodule Ω (Fin n → Ω), U ≠ ⊤ → L₃.subspaceWeight c₂ U ≤ 0 := by
    intro U hU
    set V := U.map (compEquiv (Ω := Ω) P hP).toLinearMap
    have hfr : finrank Ω V = finrank Ω U := (compEquiv P hP).finrank_map_eq U
    have hUlt : finrank Ω U < n := by
      have := Submodule.finrank_lt hU
      simpa using this
    have hV : V < ⊤ := Submodule.lt_top_of_finrank_lt_finrank (by
      rw [hfr, Module.finrank_fin_fun]
      exact hUlt)
    have h1 := (Submodule.le_weightSlope_iff hV).1 (hμ ▸ h16 V hV)
    rw [finrank_top, Module.finrank_fin_fun, subspaceWeight_top] at h1
    rw [subspaceWeight_comp, L.subspaceWeight_divConst c₁ hs, L.subspaceWeight_center c]
    refine div_nonpos_of_nonpos_of_nonneg ?_ hs.le
    have hsum : c.sum = n * μ := by simp only [μ]; field_simp
    rw [hsum, mul_div_cancel_left₀ _ hn0] at h1
    change L.subspaceWeight c V - (finrank Ω V : ℝ) * μ ≤ 0
    linarith
  obtain ⟨Q₀, hQ₀⟩ := hgap n L₃ c₂ hn2 harch hfin hmax ⟨v₀, hL₃, hc₂v₀⟩ hw (min (δ / s) 1)
    (lt_min (div_pos hδ hs) one_pos) (min_le_right _ _)
  refine ⟨(max Q₀ 1) ^ s⁻¹, fun Q hQ hQQ x hx ↦ ?_⟩
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hQs : 1 ≤ Q ^ s := Real.one_le_rpow hQ hs.le
  have hQ₀s : Q₀ ≤ Q ^ s := by
    refine (le_max_left Q₀ 1).trans ?_
    rw [← Real.rpow_inv_rpow (zero_le_one.trans (le_max_right Q₀ 1)) hs.ne']
    exact Real.rpow_le_rpow (Real.rpow_nonneg (zero_le_one.trans (le_max_right Q₀ 1)) _) hQQ hs.le
  set y := A.map (algebraMap K Ω) *ᵥ x
  have hy : y ≠ 0 := mulVec_ne_zero_of_det_ne_zero hA hx
  have h := hQ₀ (Q ^ s) hQs hQ₀s y hy
  have hPy : P.map (algebraMap K Ω) *ᵥ y = x := by
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.nonsing_inv_mul A (Ne.isUnit hA),
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  have hw2 : c₂.weight (zero_lt_one.trans_le hQs) = c₁.weight hQ0 :=
    (c₂.weight_congr rfl _ _).trans (c₁.weight_divConst hs hQ0)
  rw [absMulHeight_comp, hPy, hw2, L.absMulHeight_center c hQ0] at h
  have h3 : Q ^ (-δ) ≤ (Q ^ s) ^ (-min (δ / s) 1) := by
    rw [← Real.rpow_mul hQ0.le]
    refine Real.rpow_le_rpow_of_exponent_le hQ ?_
    have : s * min (δ / s) 1 ≤ δ := by
      calc s * min (δ / s) 1 ≤ s * (δ / s) := mul_le_mul_of_nonneg_left (min_le_left _ _) hs.le
        _ = δ := by field_simp
    linarith
  have hμpos : 0 < Q ^ (-μ) := Real.rpow_pos_of_pos hQ0 _
  have hμμ : Q ^ μ * Q ^ (-μ) = 1 := by rw [← Real.rpow_add hQ0]; simp
  calc Q ^ (-μ - δ) = Q ^ (-δ) * Q ^ (-μ) := by rw [← Real.rpow_add hQ0]; ring_nf
    _ < Q ^ μ * L.absMulHeight (c.weight hQ0) x * Q ^ (-μ) :=
        mul_lt_mul_of_pos_right (h3.trans_lt h) hμpos
    _ = L.absMulHeight (c.weight (zero_lt_one.trans_le hQ)) x := by
        rw [mul_comm (Q ^ μ), mul_assoc, hμμ, mul_one]

end FormSystem

end NumberField
