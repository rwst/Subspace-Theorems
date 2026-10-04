/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.FormIntervalResult
public import DiophantineApproximation.ThresholdHeights
public import DiophantineApproximation.SystemDomain

-- Used only inside proofs.
import DiophantineApproximation.LocalExtension
import DiophantineApproximation.SubspaceAuxiliary
import DiophantineApproximation.SubspaceGap

/-!
# The interval result for approximation domains

J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative Subspace Theorem*,
Ann. of Math. **177** (2013), 513–590, §5: (5.1)–(5.10), Lemmas 5.1, 5.2 and Theorem 3.3.

An approximation domain of Layer 6.1 (`NumberField.approxDomain`) is given by forms `L_i^{(v)}` on
`Kⁱ` at the infinite places and at the places of `Sfin`, exponents `c_iv` and a level `Q`:
`|L_i^{(v)}(x)|_v ≤ Q ^ {c_iv}` there, and integrality elsewhere. EF13 (5.1)–(5.3) turn this into
a system in the sense of EF13 §2: the forms of `L` at the places of `S`, the coordinates
`X_1, …, X_n` elsewhere, and the centered exponents

```text
c'_iv = (c_iv - (1/n) Σ_j c_jv) · mult v / κ   (v infinite),
c'_iv = (c_iv - (1/n) Σ_j c_jv) / κ            (v ∈ Sfin),       c'_iv = 0 elsewhere,
```

which sum to `0` at every place (EF13 (2.8)). For `κ` at least the spread
`M = approxSupWeight - approxWeight / n = Σ_v mult v · max_i (c_iv - (1/n) Σ_j c_jv)` they satisfy
EF13 (2.9) (`domainExponent_sup_le_spread`; `M ≤ 2 · absolute weight`,
`domainExponent_sup_le`). Lemma 5.1: at the level `Q' = Q ^ {κ / [K : ℚ]}`, a nonzero point of
the domain at level `Q` has `H_{L,c',Q'}(x) ≤ Q ^ {W / (n [K : ℚ])}`, `W` the weight of `c`
(`absMulHeight_domainSystem_le`).

Theorem 2.3 for this system (`NumberField.FormSystem.exists_intervals_cover`) is then an interval
result for the domains, in the shape of Layer 6.1's
`NumberField.exists_forall_mem_interval_approxDomain`, which Q0.3's assembly
(`NumberField.exists_finset_submodule_of_forall_interval`) takes: with `κ = 2A ≥ M`, the level
`Q' = Q ^ {2A / [K : ℚ]}` and `δ' = ε / 4nA`, a point of the domain has
`H_{L,c',Q'}(x) ≤ Q'^{-2δ'} ≤ Δ_L^{1/n} Q'^{-δ'}` above a threshold linear in the height of the
forms, and an interval `[b, b^{ω₀})` of `Q'` is an interval `[t, ω₀ t)` of `log Q` (EF13
Lemma 5.2).

## Main definitions

* `NumberField.domainMatrix`: the matrix of the forms of `L` at a place, reindexed by
  `ι ≃ Fin n`.
* `NumberField.domainSystem`: the system of EF13 (5.1)–(5.3), a `FormSystem K (Fin n)`.
* `NumberField.domainExponent`: the centered exponents `c'`.
* `NumberField.domainDelta`, `NumberField.domainThreshold`: `δ' = ε / 4nA` and the threshold.
* `NumberField.domainComap`: the points of `Kⁱ` in a subspace of `Ωⁿ`.

## Main results

* `NumberField.domainExponent_sum`: EF13 (2.8) in sum, `Σ_v Σ_i c'_iv = 0`.
* `NumberField.domainExponent_sup_le_spread`: EF13 (5.5), `Σ_v max_i c'_iv ≤ M / κ`, `M` the
  spread; `NumberField.domainExponent_sup_le`: the cruder `≤ 2 A / κ`, `A` the absolute weight.
* `NumberField.absMulHeight_domainSystem_le`: **EF13 Lemma 5.1** for approximation domains.
* `NumberField.card_forms_domainSystem_le`: EF13 (5.6), at most `s + n` distinct forms.
* `NumberField.log_absFormHeight_domainSystem_le`: EF13 (5.10),
  `log H_L ≤ log n! + n · formLogHeight / [K : ℚ]`.
* `NumberField.exists_forall_mem_interval_approxDomain_ef`: **EF13 Theorem 3.3** for approximation
  domains: one proper subspace and `intervalCount n (s + n) δ'` intervals of ratio
  `cutRatio (s + n) δ'`.

## Implementation notes

⚠ **The level, not the height of the point.** EF13 take `Q = H(x) ^ {1 + ε/n}` for a solution of
their system (3.7), which involves `‖x‖_v`. The approximation domain has no `‖x‖_v` and asks for
integrality off `S`, so Lemma 5.1 holds at any level `Q`, with the coordinates contributing at
most `1` off `S`.

⚠ **The forms are indexed by `Fin n`**, as Theorem 2.3 needs (its quotient systems live on
`Fin (n - k)`); `ι ≃ Fin n` transports the domain.

⚠ **The exceptional subspace is taken over `AlgebraicClosure K`**, where Theorem 2.3
lives; its `K`-points are a proper subspace of `Kⁱ` (`domainComap_ne_top`).

This is milestone Q4.2a–c of `QuantitativeSubspace/README.md`.
-/

@[expose] public section

open Finset Module Matrix

namespace NumberField

variable {K : Type} [Field K] {ι : Type*} [Fintype ι] {n : ℕ}

/-! ### The system -/

section System

variable [DecidableEq ι] (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) (e : ι ≃ Fin n)

/-- **The forms of an approximation domain at a place**, reindexed by `ι ≃ Fin n`: the row `i` is
the coefficient vector of `L_{e⁻¹ i}^{(v)}`. -/
noncomputable def domainMatrix (v : AbsoluteValue K ℝ) : Matrix (Fin n) (Fin n) K :=
  (formMatrix L v).reindex e e

theorem domainMatrix_apply (v : AbsoluteValue K ℝ) (i j : Fin n) :
    domainMatrix L e v i j = L v (e.symm i) (Pi.single (e.symm j) 1) := by
  rw [domainMatrix, reindex_apply, submatrix_apply, formMatrix_apply]

theorem domainMatrix_mulVec (v : AbsoluteValue K ℝ) (x : ι → K) :
    domainMatrix L e v *ᵥ (x ∘ e.symm) = fun i ↦ L v (e.symm i) x := by
  rw [domainMatrix, reindex_apply, submatrix_mulVec_equiv, Equiv.symm_symm, Function.comp_assoc,
    Equiv.symm_comp_self, Function.comp_id, formMatrix, LinearMap.toMatrix'_mulVec]
  rfl

theorem det_domainMatrix_ne_zero {v : AbsoluteValue K ℝ} (hL : LinearIndependent K (L v)) :
    (domainMatrix L e v).det ≠ 0 := by
  rw [domainMatrix, det_reindex_self]
  exact (isUnit_det_formMatrix hL).ne_zero

variable [NumberField K] (Sfin : Finset (FinitePlace K))

open scoped Classical in
/-- **The system of an approximation domain** (EF13 (5.1)–(5.3)): the forms of `L` at the
infinite places and at the places of `Sfin`, the coordinates at the other finite places. -/
noncomputable def domainSystem (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) : FormSystem K (Fin n) where
  arch w := domainMatrix L e w.1
  arch_det_ne_zero w := det_domainMatrix_ne_zero L e (hLInf w)
  fin v := if v ∈ Sfin then domainMatrix L e v.1 else 1
  fin_det_ne_zero v := by
    split_ifs with hv
    · exact det_domainMatrix_ne_zero L e (hLFin v hv)
    · simp
  finite_range_fin := by
    refine (((Sfin.image fun v ↦ domainMatrix L e v.1) ∪ {1} : Finset _).finite_toSet).subset ?_
    rintro _ ⟨v, rfl⟩
    by_cases hv : v ∈ Sfin
    · simp only [hv, ite_true, coe_union, coe_image, coe_singleton, Set.mem_union,
        Set.mem_image, mem_coe]
      exact Or.inl ⟨v, hv, rfl⟩
    · simp [hv]

end System

/-- A finite place has local degree `1` over its own field. -/
theorem FinitePlace.localDegree_self [NumberField K] (v : FinitePlace K) : v.localDegree K = 1 := by
  have h := FinitePlace.sum_localDegree (F := K) v
  rw [finrank_self] at h
  have hv : v ∈ FinitePlace.placesOverFinset K v := by
    rw [FinitePlace.mem_placesOverFinset]
    exact ⟨by ext x; rfl⟩
  have h1 := single_le_sum (f := fun w : FinitePlace K ↦ w.localDegree K)
    (fun w _ ↦ Nat.zero_le _) hv
  have h0 := v.localDegree_pos (K := K)
  omega

/-! ### The exponents -/

section Exponent

/-- The values centered at their mean sum to `0`. -/
theorem sum_sub_mean (a : ι → ℝ) (e : ι ≃ Fin n) :
    ∑ i : Fin n, (a (e.symm i) - (∑ j, a j) / n) = 0 := by
  rw [sum_sub_distrib, e.symm.sum_comp a, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [← e.symm.sum_comp a]; simp
  · field_simp
    ring

/-- A value centered at the mean is at most twice the `ℓ¹` norm. -/
theorem iSup_sub_mean_mul_le (a : ι → ℝ) (e : ι ≃ Fin n) {t : ℝ} (ht : 0 ≤ t) :
    ⨆ i : Fin n, (a (e.symm i) - (∑ j, a j) / n) * t ≤ 2 * t * ∑ j, |a j| := by
  have hS : 0 ≤ ∑ j, |a j| := sum_nonneg fun j _ ↦ abs_nonneg _
  refine Real.iSup_le (fun i ↦ ?_) (by positivity)
  have h1 : |a (e.symm i)| ≤ ∑ j, |a j| :=
    single_le_sum (f := fun j ↦ |a j|) (fun j _ ↦ abs_nonneg _) (mem_univ _)
  have h2 : |(∑ j, a j) / n| ≤ ∑ j, |a j| := by
    rw [abs_div, Nat.abs_cast]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using hS
    · refine div_le_of_le_mul₀ (Nat.cast_nonneg _) hS ?_
      calc |∑ j, a j| ≤ ∑ j, |a j| := abs_sum_le_sum_abs _ _
        _ ≤ (∑ j, |a j|) * n := le_mul_of_one_le_right hS (Nat.one_le_cast.2 hn)
  calc (a (e.symm i) - (∑ j, a j) / n) * t ≤ |a (e.symm i) - (∑ j, a j) / n| * t :=
        mul_le_mul_of_nonneg_right (le_abs_self _) ht
    _ ≤ (|a (e.symm i)| + |(∑ j, a j) / n|) * t := by gcongr; exact abs_sub _ _
    _ ≤ 2 * t * ∑ j, |a j| := by nlinarith

/-- A value centered at the mean is at most the largest value centered at the mean. -/
theorem iSup_sub_mean_mul_le_iSup [Nonempty ι] (a : ι → ℝ) (e : ι ≃ Fin n) {t : ℝ}
    (ht : 0 ≤ t) :
    ⨆ i : Fin n, (a (e.symm i) - (∑ j, a j) / n) * t ≤ ((⨆ j, a j) - (∑ j, a j) / n) * t := by
  have : Nonempty (Fin n) := ⟨e (Classical.arbitrary ι)⟩
  exact ciSup_le fun i ↦ mul_le_mul_of_nonneg_right
    (sub_le_sub_right (le_ciSup (Set.finite_range a).bddAbove _) _) ht

variable [NumberField K] (Sfin : Finset (FinitePlace K)) (c : AbsoluteValue K ℝ → ι → ℝ)
  (e : ι ≃ Fin n) (κ : ℝ)

open scoped Classical in
/-- **The centered exponents** of EF13 (5.2), in the normalization of `FormExponent`: at a place
`v` of `S`, `(c_iv - (1/n) Σ_j c_jv) / κ`, times `mult v` at an infinite place; `0` elsewhere. -/
noncomputable def domainExponent : FormExponent K (Fin n) where
  arch w i := (c w.1 (e.symm i) - (∑ j, c w.1 j) / n) * w.mult / κ
  fin v i := if v ∈ Sfin then (c v.1 (e.symm i) - (∑ j, c v.1 j) / n) / κ else 0
  finite_setOf_fin_ne_zero := Sfin.finite_toSet.subset fun v hv ↦ by
    by_contra h
    rw [Finset.mem_coe] at h
    exact hv (funext fun i ↦ by simp [h])

/-- **EF13 (2.8) in sum**: the centered exponents sum to `0`. -/
theorem domainExponent_sum : (domainExponent Sfin c e κ).sum = 0 := by
  classical
  have harch : ∀ w : InfinitePlace K, ∑ i, (domainExponent Sfin c e κ).arch w i = 0 := by
    intro w
    simp only [domainExponent, ← sum_div, ← sum_mul, sum_sub_mean, zero_mul, zero_div]
  have hfin : ∀ v : FinitePlace K, ∑ i, (domainExponent Sfin c e κ).fin v i = 0 := by
    intro v
    by_cases hv : v ∈ Sfin
    · simp only [domainExponent, hv, ite_true, ← sum_div, sum_sub_mean, zero_div]
    · simp [domainExponent, hv]
  simp [FormExponent.sum, harch, hfin]

/-- **EF13 (5.5)**: the largest centered exponents sum to at most `2 A / κ`, `A` the absolute
weight of `c`. -/
theorem domainExponent_sup_le (hκ : 0 < κ) :
    (∑ w, ⨆ i, (domainExponent Sfin c e κ).arch w i) +
        ∑ᶠ v, ⨆ i, (domainExponent Sfin c e κ).fin v i ≤
      2 * approxAbsWeight Sfin c / κ := by
  classical
  have harch : ∀ w : InfinitePlace K, ⨆ i, (domainExponent Sfin c e κ).arch w i ≤
      2 * (w.mult * ∑ j, |c w.1 j|) / κ := by
    intro w
    have h := iSup_sub_mean_mul_le (c w.1) e (t := w.mult / κ) (by positivity)
    simp only [domainExponent, mul_div_assoc]
    refine h.trans_eq ?_
    ring
  have hfin : ∀ v ∈ Sfin, ⨆ i, (domainExponent Sfin c e κ).fin v i ≤
      2 * (∑ j, |c v.1 j|) / κ := by
    intro v hv
    have h := iSup_sub_mean_mul_le (c v.1) e (t := κ⁻¹) (by positivity)
    simp only [domainExponent, hv, ite_true, div_eq_mul_inv]
    refine h.trans_eq ?_
    ring
  have hsupp : (fun v ↦ ⨆ i, (domainExponent Sfin c e κ).fin v i).support ⊆ Sfin := by
    intro v hv
    by_contra h
    rw [Finset.mem_coe] at h
    exact hv (by simp [domainExponent, h])
  rw [finsum_eq_sum_of_support_subset _ hsupp, approxAbsWeight, mul_add, add_div, mul_sum,
    mul_sum, sum_div, sum_div]
  exact add_le_add (sum_le_sum fun w _ ↦ harch w) (sum_le_sum fun v hv ↦ hfin v hv)

/-- **EF13 (5.5), sharp**: the largest centered exponents sum to at most `M / κ`, with
`M = approxSupWeight - approxWeight / n` the spread `∑_v mult v · max_i (c_iv - (1/n) ∑_j c_jv)`.
EF13 take `κ = M`; for the exponents of a normalized system `M ≍ [E : K]`, while the absolute
weight is `≍ n [E : K]`. -/
theorem domainExponent_sup_le_spread [Nonempty ι] (hκ : 0 < κ) :
    (∑ w, ⨆ i, (domainExponent Sfin c e κ).arch w i) +
        ∑ᶠ v, ⨆ i, (domainExponent Sfin c e κ).fin v i ≤
      (approxSupWeight Sfin c - approxWeight Sfin c / n) / κ := by
  classical
  have harch : ∀ w : InfinitePlace K, ⨆ i, (domainExponent Sfin c e κ).arch w i ≤
      ((⨆ j, c w.1 j) - (∑ j, c w.1 j) / n) * (w.mult / κ) := by
    intro w
    have h := iSup_sub_mean_mul_le_iSup (c w.1) e (t := w.mult / κ) (by positivity)
    simp only [domainExponent, mul_div_assoc]
    exact h
  have hfin : ∀ v ∈ Sfin, ⨆ i, (domainExponent Sfin c e κ).fin v i ≤
      ((⨆ j, c v.1 j) - (∑ j, c v.1 j) / n) * κ⁻¹ := by
    intro v hv
    have h := iSup_sub_mean_mul_le_iSup (c v.1) e (t := κ⁻¹) (by positivity)
    simp only [domainExponent, hv, ite_true, div_eq_mul_inv]
    exact h
  have hsupp : (fun v ↦ ⨆ i, (domainExponent Sfin c e κ).fin v i).support ⊆ Sfin := by
    intro v hv
    by_contra h
    rw [Finset.mem_coe] at h
    exact hv (by simp [domainExponent, h])
  have hM : approxSupWeight Sfin c - approxWeight Sfin c / n =
      ∑ w : InfinitePlace K, (w.mult : ℝ) * ((⨆ j, c w.1 j) - (∑ j, c w.1 j) / n) +
        ∑ v ∈ Sfin, ((⨆ j, c v.1 j) - (∑ j, c v.1 j) / n) := by
    rw [approxSupWeight, approxWeight]
    simp only [mul_sub, sum_sub_distrib, add_div, sum_div, mul_div_assoc]
    ring
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  refine (add_le_add (sum_le_sum fun w _ ↦ harch w) (sum_le_sum fun v hv ↦ hfin v hv)).trans_eq ?_
  rw [hM, div_eq_inv_mul, mul_add, mul_sum, mul_sum]
  congr 1 <;> exact sum_congr rfl fun _ _ ↦ by ring

end Exponent

/-! ### EF13 Lemma 5.1 -/

section Lemma51

variable [NumberField K] {Sfin : Finset (FinitePlace K)} {c : AbsoluteValue K ℝ → ι → ℝ}
  (e : ι ≃ Fin n) {κ Q : ℝ}

variable (K κ) in
/-- The level `Q ^ {κ / [K : ℚ]}` of the twisted height for the domain at level `Q`. -/
theorem domainLevel_pos (hQ : 0 < Q) : 0 < Q ^ (κ / finrank ℚ K) := Real.rpow_pos_of_pos hQ _

/-- At an infinite place the weight of the centered exponents at the level `Q ^ {κ / [K : ℚ]}`
is `Q ^ {c_iv - (1/n) Σ_j c_jv}`. -/
theorem domainExponent_weight_arch (hκ : 0 < κ) (hQ : 0 < Q) (w : InfinitePlace K) (i : Fin n) :
    ((domainExponent Sfin c e κ).weight (domainLevel_pos K κ hQ)).arch w i =
      Q ^ (c w.1 (e.symm i) - (∑ j, c w.1 j) / n) := by
  have hm : (w.mult : ℝ) ≠ 0 := by exact_mod_cast w.mult_pos.ne'
  have hd : (finrank ℚ K : ℝ) ≠ 0 := by exact_mod_cast finrank_pos.ne'
  change (Q ^ (κ / finrank ℚ K)) ^ ((c w.1 (e.symm i) - (∑ j, c w.1 j) / n) * w.mult / κ *
    finrank ℚ K / w.mult) = _
  rw [← Real.rpow_mul hQ.le]
  congr 1
  field_simp

/-- At a finite place of `Sfin` the weight is `Q ^ {c_iv - (1/n) Σ_j c_jv}`. -/
theorem domainExponent_weight_fin_of_mem (hκ : 0 < κ) (hQ : 0 < Q) {v : FinitePlace K}
    (hv : v ∈ Sfin) (i : Fin n) :
    ((domainExponent Sfin c e κ).weight (domainLevel_pos K κ hQ)).fin v i =
      Q ^ (c v.1 (e.symm i) - (∑ j, c v.1 j) / n) := by
  classical
  have hd : (finrank ℚ K : ℝ) ≠ 0 := by exact_mod_cast finrank_pos.ne'
  change (Q ^ (κ / finrank ℚ K)) ^ ((domainExponent Sfin c e κ).fin v i * finrank ℚ K) = _
  rw [← Real.rpow_mul hQ.le]
  simp only [domainExponent, hv, ite_true]
  congr 1
  field_simp

/-- At a finite place outside `Sfin` the weight is `1`. -/
theorem domainExponent_weight_fin_of_notMem (hQ : 0 < Q) {v : FinitePlace K} (hv : v ∉ Sfin)
    (i : Fin n) :
    ((domainExponent Sfin c e κ).weight (domainLevel_pos K κ hQ)).fin v i = 1 := by
  classical
  change (Q ^ (κ / finrank ℚ K)) ^ ((domainExponent Sfin c e κ).fin v i * finrank ℚ K) = _
  simp [domainExponent, hv]

omit [NumberField K] in
private theorem map_algebraMap_self' (M : Matrix (Fin n) (Fin n) K) :
    M.map (algebraMap K K) = M := by
  ext
  simp

variable [DecidableEq ι] {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
  (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
  (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1))

/-- **The local factor at an infinite place** of a point of the domain is at most
`Q ^ {(1/n) Σ_j c_jv}`. -/
theorem archFactor_domainSystem_le (hκ : 0 < κ) (hQ : 0 < Q) {x : ι → K}
    (hx : x ∈ approxDomain Sfin L c Q) (w : InfinitePlace K) :
    (domainSystem L e Sfin hLInf hLFin).archFactor
        ((domainExponent Sfin c e κ).weight (domainLevel_pos K κ hQ)) w (x ∘ e.symm) ≤
      Q ^ ((∑ j, c w.1 j) / n) := by
  have hw : w.comap (algebraMap K K) = w := by rw [Algebra.algebraMap_self]; rfl
  rw [FormSystem.archFactor, hw, map_algebraMap_self']
  refine Real.iSup_le (fun i ↦ ?_) (Real.rpow_nonneg hQ.le _)
  rw [domainExponent_weight_arch e hκ hQ, div_le_iff₀ (Real.rpow_pos_of_pos hQ _),
    ← Real.rpow_add hQ, add_sub_cancel]
  change w ((domainMatrix L e w.1 *ᵥ (x ∘ e.symm)) i) ≤ _
  rw [domainMatrix_mulVec]
  exact hx.1 w (e.symm i)

/-- **The local factor at a finite place of `Sfin`** is at most `Q ^ {(1/n) Σ_j c_jv}`. -/
theorem finFactor_domainSystem_le_of_mem (hκ : 0 < κ) (hQ : 0 < Q) {x : ι → K}
    (hx : x ∈ approxDomain Sfin L c Q) {v : FinitePlace K} (hv : v ∈ Sfin) :
    (domainSystem L e Sfin hLInf hLFin).finFactor
        ((domainExponent Sfin c e κ).weight (domainLevel_pos K κ hQ)) v (x ∘ e.symm) ≤
      Q ^ ((∑ j, c v.1 j) / n) := by
  classical
  rw [FormSystem.finFactor, FinitePlace.under_self, map_algebraMap_self',
    FinitePlace.localDegree_self]
  refine Real.iSup_le (fun i ↦ ?_) (Real.rpow_nonneg hQ.le _)
  rw [pow_one, domainExponent_weight_fin_of_mem e hκ hQ hv,
    div_le_iff₀ (Real.rpow_pos_of_pos hQ _), ← Real.rpow_add hQ, add_sub_cancel]
  change v (((if v ∈ Sfin then domainMatrix L e v.1 else 1) *ᵥ (x ∘ e.symm)) i) ≤ _
  simp only [hv, ite_true, domainMatrix_mulVec]
  exact hx.2.1 v hv (e.symm i)

/-- **The local factor at a finite place outside `Sfin`** is at most `1`: the point is integral
there. -/
theorem finFactor_domainSystem_le_of_notMem (hQ : 0 < Q) {x : ι → K}
    (hx : x ∈ approxDomain Sfin L c Q) {v : FinitePlace K} (hv : v ∉ Sfin) :
    (domainSystem L e Sfin hLInf hLFin).finFactor
        ((domainExponent Sfin c e κ).weight (domainLevel_pos K κ hQ)) v (x ∘ e.symm) ≤ 1 := by
  classical
  rw [FormSystem.finFactor, FinitePlace.under_self, map_algebraMap_self',
    FinitePlace.localDegree_self]
  refine Real.iSup_le (fun i ↦ ?_) zero_le_one
  rw [pow_one, domainExponent_weight_fin_of_notMem e hQ hv, div_one]
  change v (((if v ∈ Sfin then domainMatrix L e v.1 else 1) *ᵥ (x ∘ e.symm)) i) ≤ _
  simp only [hv, ite_false, one_mulVec, Function.comp_apply]
  exact hx.2.2 v hv (e.symm i)

/-- **EF13 Lemma 5.1, relative to `K`**: a nonzero point of the domain at level `Q` has twisted
height at most `Q ^ {W / n}` at the level `Q ^ {κ / [K : ℚ]}`, `W` the weight of `c`. -/
theorem mulHeight_domainSystem_le (hκ : 0 < κ) (hQ : 0 < Q) {x : ι → K} (hx0 : x ≠ 0)
    (hx : x ∈ approxDomain Sfin L c Q) :
    (domainSystem L e Sfin hLInf hLFin).mulHeight
        ((domainExponent Sfin c e κ).weight (domainLevel_pos K κ hQ)) (x ∘ e.symm) ≤
      Q ^ (approxWeight Sfin c / n) := by
  classical
  set L' := domainSystem L e Sfin hLInf hLFin
  set a := (domainExponent Sfin c e κ).weight (domainLevel_pos K κ hQ)
  have hy : x ∘ e.symm ≠ 0 := fun h ↦ hx0 (funext fun j ↦ by simpa using congrFun h (e j))
  have harch : ∏ w, L'.archFactor a w (x ∘ e.symm) ^ w.mult ≤
      Q ^ (∑ w : InfinitePlace K, w.mult * ((∑ j, c w.1 j) / n)) := by
    rw [Real.rpow_sum_of_pos hQ]
    refine prod_le_prod₀ (fun w _ ↦ pow_nonneg (L'.archFactor_nonneg a w _) _) fun w _ ↦ ?_
    rw [mul_comm, Real.rpow_mul_natCast hQ.le]
    exact pow_le_pow_left₀ (L'.archFactor_nonneg a w _)
      (archFactor_domainSystem_le e hLInf hLFin hκ hQ hx w) _
  set g : FinitePlace K → ℝ := fun v ↦ if v ∈ Sfin then Q ^ ((∑ j, c v.1 j) / n) else 1
  have hgsupp : Function.mulSupport g ⊆ Sfin := fun v hv ↦ by
    by_contra h
    rw [mem_coe] at h
    exact hv (by simp [g, h])
  have hfin : ∏ᶠ v, L'.finFactor a v (x ∘ e.symm) ≤ Q ^ (∑ v ∈ Sfin, (∑ j, c v.1 j) / n) := by
    calc ∏ᶠ v, L'.finFactor a v (x ∘ e.symm) ≤ ∏ᶠ v, g v :=
          finprod_le_finprod₀ (L'.hasFiniteMulSupport_finFactor a hy)
            (fun v ↦ L'.finFactor_nonneg a v _) (Sfin.finite_toSet.subset hgsupp) fun v ↦ by
              by_cases hv : v ∈ Sfin
              · simpa [g, hv] using finFactor_domainSystem_le_of_mem e hLInf hLFin hκ hQ hx hv
              · simpa [g, hv] using finFactor_domainSystem_le_of_notMem e hLInf hLFin hQ hx hv
      _ = ∏ v ∈ Sfin, Q ^ ((∑ j, c v.1 j) / n) := by
          rw [finprod_eq_prod_of_mulSupport_subset g hgsupp]
          exact prod_congr rfl fun v hv ↦ by simp [g, hv]
      _ = _ := (Real.rpow_sum_of_pos hQ _ _).symm
  rw [FormSystem.mulHeight]
  calc (∏ w, L'.archFactor a w (x ∘ e.symm) ^ w.mult) * ∏ᶠ v, L'.finFactor a v (x ∘ e.symm)
      ≤ Q ^ (∑ w : InfinitePlace K, w.mult * ((∑ j, c w.1 j) / n)) *
          Q ^ (∑ v ∈ Sfin, (∑ j, c v.1 j) / n) :=
        mul_le_mul harch hfin (finprod_nonneg fun v ↦ L'.finFactor_nonneg a v _)
          (Real.rpow_nonneg hQ.le _)
    _ = Q ^ (approxWeight Sfin c / n) := by
        rw [← Real.rpow_add hQ, approxWeight, add_div, sum_div, sum_div]
        simp only [mul_div_assoc]

/-- **EF13 Lemma 5.1** for approximation domains: a nonzero point `x` of the domain at level `Q`
has `H_{L,c',Q'}(x) ≤ Q ^ {W / (n [K : ℚ])}`, `Q' = Q ^ {κ / [K : ℚ]}` and `W` the weight of `c`. -/
theorem absMulHeight_domainSystem_le {Ω : Type*} [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (hκ : 0 < κ) (hQ : 0 < Q) {x : ι → K} (hx0 : x ≠ 0)
    (hx : x ∈ approxDomain Sfin L c Q) :
    (domainSystem L e Sfin hLInf hLFin).absMulHeight
        ((domainExponent Sfin c e κ).weight (domainLevel_pos K κ hQ))
        (algebraMap K Ω ∘ (x ∘ e.symm)) ≤
      Q ^ (approxWeight Sfin c / (n * finrank ℚ K)) := by
  rw [FormSystem.absMulHeight_algebraMap]
  calc _ ≤ (Q ^ (approxWeight Sfin c / n)) ^ ((finrank ℚ K : ℝ))⁻¹ :=
        Real.rpow_le_rpow (FormSystem.mulHeight_nonneg _ _ _)
          (mulHeight_domainSystem_le e hLInf hLFin hκ hQ hx0 hx) (by positivity)
    _ = _ := by
        rw [← Real.rpow_mul hQ.le]
        congr 1
        ring

end Lemma51

/-! ### The forms and their height (EF13 (5.6), (5.10)) -/

section Heights

variable [DecidableEq ι] [NumberField K] {Sfin : Finset (FinitePlace K)}
  {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} (e : ι ≃ Fin n)
  (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
  (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1))

/-- The coefficient vector of a form on `Kⁱ`, reindexed by `ι ≃ Fin n`. -/
private noncomputable def coeffVec (ℓ : Dual K (ι → K)) : Fin n → K :=
  fun j ↦ ℓ (Pi.single (e.symm j) 1)

/-- Every form of the system is the coefficient vector of a form of `L` at a place of `S`, or a
row of the identity. -/
private theorem mem_forms_domainSystem {g : Fin n → K}
    (hg : g ∈ (domainSystem L e Sfin hLInf hLFin).forms) :
    (∃ q : (InfinitePlace K ⊕ Sfin) × ι, coeffVec e (L (sPlace Sfin q.1) q.2) = g) ∨
      ∃ i : Fin n, (1 : Matrix (Fin n) (Fin n) K) i = g := by
  classical
  rw [FormSystem.forms, Set.Finite.mem_toFinset] at hg
  rcases hg with ⟨w, i, rfl⟩ | ⟨v, i, rfl⟩
  · refine Or.inl ⟨(.inl w, e.symm i), funext fun j ↦ ?_⟩
    change _ = domainMatrix L e w.1 i j
    rw [domainMatrix_apply]
    rfl
  · by_cases hv : v ∈ Sfin
    · refine Or.inl ⟨(.inr ⟨v, hv⟩, e.symm i), funext fun j ↦ ?_⟩
      change _ = (if v ∈ Sfin then domainMatrix L e v.1 else 1) i j
      simp only [hv, ite_true, domainMatrix_apply]
      rfl
    · refine Or.inr ⟨i, ?_⟩
      change _ = (if v ∈ Sfin then domainMatrix L e v.1 else 1) i
      simp only [hv, ite_false]

/-- **EF13 (5.6)**: the system has at most `s + n` distinct forms, `s` the number of distinct
forms of `L` at the places of `S`. -/
theorem card_forms_domainSystem_le :
    #(domainSystem L e Sfin hLInf hLFin).forms ≤ formCount Sfin L + n := by
  classical
  set f : (InfinitePlace K ⊕ Sfin) × ι → Dual K (ι → K) := fun q ↦ L (sPlace Sfin q.1) q.2
  have hsub : (domainSystem L e Sfin hLInf hLFin).forms ⊆
      (univ.image f).image (coeffVec e) ∪ univ.image fun i : Fin n ↦ (1 : Matrix _ _ K) i := by
    intro g hg
    rcases mem_forms_domainSystem e hLInf hLFin hg with ⟨q, rfl⟩ | ⟨i, rfl⟩
    · exact mem_union_left _ (mem_image_of_mem _ (mem_image_of_mem _ (mem_univ q)))
    · exact mem_union_right _ (mem_image_of_mem _ (mem_univ i))
  calc #(domainSystem L e Sfin hLInf hLFin).forms
      ≤ #((univ.image f).image (coeffVec e) ∪ univ.image fun i : Fin n ↦ (1 : Matrix _ _ K) i) :=
        card_le_card hsub
    _ ≤ #((univ.image f).image (coeffVec e)) + #(univ.image fun i : Fin n ↦ (1 : Matrix _ _ K) i) :=
        card_union_le _ _
    _ ≤ #(univ.image f) + n := add_le_add card_image_le (card_image_le.trans (by simp))
    _ = formCount Sfin L + n := by
        rw [formCount, ← Set.ncard_coe_finset, coe_image, coe_univ, Set.image_univ]

/-- The entries of the forms of `L` at the places of `S`, completed by `1`. -/
private noncomputable def entryVec (Sfin : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) :
    ((InfinitePlace K ⊕ Sfin) × ι × ι) ⊕ Unit → K :=
  Sum.elim (fun t ↦ formMatrix L (sPlace Sfin t.1) t.2.1 t.2.2) fun _ ↦ 1

/-- An entry of a form of the system is at most the largest entry of `entryVec`. -/
private theorem apply_le_iSup_entryVec (v : AbsoluteValue K ℝ) {g : Fin n → K}
    (hg : g ∈ (domainSystem L e Sfin hLInf hLFin).forms) (j : Fin n) :
    v (g j) ≤ ⨆ r, v (entryVec Sfin L r) := by
  have hle : ∀ r, v (entryVec Sfin L r) ≤ ⨆ r, v (entryVec Sfin L r) :=
    fun r ↦ le_ciSup (f := fun r ↦ v (entryVec Sfin L r)) (Finite.bddAbove_range _) r
  have h1 : 1 ≤ ⨆ r, v (entryVec Sfin L r) := by simpa [entryVec] using hle (.inr ())
  rcases mem_forms_domainSystem e hLInf hLFin hg with ⟨q, rfl⟩ | ⟨i, rfl⟩
  · refine (le_of_eq ?_).trans (hle (.inl (q.1, q.2, e.symm j)))
    simp [entryVec, coeffVec, formMatrix_apply]
  · rw [Matrix.one_apply]
    split_ifs
    · simpa using h1
    · simpa using zero_le_one.trans h1

/-- The largest determinant of the system at a place is at most `C (max entry)ⁿ`. -/
private theorem iSup_detSet_le (v : AbsoluteValue K ℝ) {C : ℝ}
    (hdet : ∀ M : Matrix (Fin n) (Fin n) K, (∀ i j, v (M i j) ≤ ⨆ r, v (entryVec Sfin L r)) →
      v M.det ≤ C * (⨆ r, v (entryVec Sfin L r)) ^ n) (hC : 0 ≤ C) :
    (⨆ d : (domainSystem L e Sfin hLInf hLFin).detSet, v d) ≤
      C * (⨆ r, v (entryVec Sfin L r)) ^ n := by
  classical
  refine Real.iSup_le (fun ⟨d, hd⟩ ↦ ?_)
    (mul_nonneg hC (pow_nonneg (Real.iSup_nonneg fun _ ↦ v.nonneg _) _))
  obtain ⟨M, hM, rfl⟩ := mem_image.1 hd
  exact hdet (Matrix.of M) fun i j ↦
    apply_le_iSup_entryVec e hLInf hLFin v (Fintype.mem_piFinset.1 hM i) j

/-- **EF13 (5.10)**, relative to `K`: `H_L ≤ n!^{[K:ℚ]} H(entries)ⁿ`. -/
theorem log_mulFormHeight_domainSystem_le :
    Real.log (domainSystem L e Sfin hLInf hLFin).mulFormHeight ≤
      finrank ℚ K * Real.log n.factorial + n * formLogHeight Sfin L := by
  classical
  set L' := domainSystem L e Sfin hLInf hLFin
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace K) := inferInstance
  have hd₀ : (L'.arch w₀).det ∈ L'.detSet := L'.det_arch_mem_detSet w₀
  have hx : (fun d : L'.detSet ↦ (d : K)) ≠ 0 := fun h ↦
    L'.arch_det_ne_zero w₀ (by simpa using congrFun h ⟨_, hd₀⟩)
  have hy : entryVec Sfin L ≠ 0 := fun h ↦ by simpa [entryVec] using congrFun h (.inr ())
  have hY : Height.mulHeight (fun d : L'.detSet ↦ (d : K)) = L'.mulFormHeight := by
    rw [NumberField.mulHeight_eq hx]
    rfl
  have hC : (1 : ℝ) ≤ n.factorial := by exact_mod_cast n.factorial_pos
  have key := Height.mulHeight_le_pow_mul_pow (x := fun d : L'.detSet ↦ (d : K))
    (y := entryVec Sfin L) (D := n) hC hy
    (fun v _ ↦ iSup_detSet_le e hLInf hLFin v (fun M hM ↦ by
      simpa [prod_const] using AbsoluteValue.apply_det_le_factorial_mul_prod v M hM)
      (by positivity))
    fun v hv ↦ by
      simpa using iSup_detSet_le e hLInf hLFin v (C := 1) (fun M hM ↦ by
        simpa [prod_const] using AbsoluteValue.apply_det_le_prod_of_isNonarchimedean
          (Height.AdmissibleAbsValues.isNonarchimedean v hv) M
          (fun _ ↦ Real.iSup_nonneg fun _ ↦ v.nonneg _) hM) zero_le_one
  rw [hY, NumberField.totalWeight_eq_finrank] at key
  have hlogy : Real.log (Height.mulHeight (entryVec Sfin L)) ≤ formLogHeight Sfin L :=
    log_mulHeight_sum_elim_one_le _
  calc Real.log L'.mulFormHeight
      ≤ Real.log ((n.factorial : ℝ) ^ finrank ℚ K *
          Height.mulHeight (entryVec Sfin L) ^ n) :=
        Real.log_le_log (zero_lt_one.trans_le L'.one_le_mulFormHeight) key
    _ = finrank ℚ K * Real.log n.factorial + n * Real.log (Height.mulHeight (entryVec Sfin L)) := by
        rw [Real.log_mul (by positivity) (pow_ne_zero _ (Height.mulHeight_pos _).ne'),
          Real.log_pow, Real.log_pow]
    _ ≤ _ := by gcongr

/-- **EF13 (5.10)**: `log H_L ≤ log n! + n · formLogHeight / [K : ℚ]`. -/
theorem log_absFormHeight_domainSystem_le :
    Real.log (domainSystem L e Sfin hLInf hLFin).absFormHeight ≤
      Real.log n.factorial + n * formLogHeight Sfin L / finrank ℚ K := by
  have hd : (0 : ℝ) < finrank ℚ K := by exact_mod_cast finrank_pos
  have h := log_mulFormHeight_domainSystem_le e hLInf hLFin
  rw [FormSystem.log_mulFormHeight] at h
  have h' : Real.log (domainSystem L e Sfin hLInf hLFin).absFormHeight ≤
      (finrank ℚ K * Real.log n.factorial + n * formLogHeight Sfin L) / finrank ℚ K :=
    (le_div_iff₀ hd).2 (by linarith)
  refine h'.trans_eq ?_
  field_simp

end Heights

/-! ### The interval result (EF13 Theorem 3.3) -/

section Interval

/-- **The exponent `δ' = ε / 4nA`** of Theorem 2.3 for the system of a domain of weight `≤ -ε`
and spread `≤ 2A`. -/
noncomputable def domainDelta (n : ℕ) (ε A : ℝ) : ℝ := ε / (4 * n * A)

/-- **The threshold** of the interval result for approximation domains, in `log Q`:
`[K:ℚ] / 2A · (ℓ + log n / δ' + C(s + n, n) ℓ / (n δ'))` with `ℓ = log n! + n F / [K:ℚ]`, `F` the
logarithmic height of the forms. It is linear in `F`. -/
noncomputable def domainThreshold (n d s : ℕ) (ε A F : ℝ) : ℝ :=
  d / (2 * A) * ((Real.log n.factorial + n * F / d) + Real.log n / domainDelta n ε A +
    ((s + n).choose n : ℝ) * (Real.log n.factorial + n * F / d) / (n * domainDelta n ε A))

/-- The weight is at least minus the absolute weight. -/
theorem neg_approxWeight_le_approxAbsWeight [NumberField K] (Sfin : Finset (FinitePlace K))
    (c : AbsoluteValue K ℝ → ι → ℝ) : -approxWeight Sfin c ≤ approxAbsWeight Sfin c := by
  rw [approxWeight, approxAbsWeight, neg_add, ← sum_neg_distrib, ← sum_neg_distrib]
  refine add_le_add (sum_le_sum fun w _ ↦ ?_) (sum_le_sum fun v _ ↦ ?_)
  · rw [← mul_neg, ← sum_neg_distrib]
    exact mul_le_mul_of_nonneg_left (sum_le_sum fun i _ ↦ neg_le_abs _) (Nat.cast_nonneg _)
  · rw [← sum_neg_distrib]
    exact sum_le_sum fun i _ ↦ neg_le_abs _

variable (K) (e : ι ≃ Fin n) {Ω : Type*} [Field Ω] [Algebra K Ω]

/-- **The points of `Kⁱ` in a subspace of `Ωⁿ`**, through `ι ≃ Fin n`. -/
def domainComap (T : Submodule Ω (Fin n → Ω)) : Submodule K (ι → K) where
  carrier := {x | algebraMap K Ω ∘ (x ∘ e.symm) ∈ T}
  add_mem' {x y} hx hy := by
    have : algebraMap K Ω ∘ ((x + y) ∘ e.symm) =
        algebraMap K Ω ∘ (x ∘ e.symm) + algebraMap K Ω ∘ (y ∘ e.symm) := by
      funext j; simp
    simpa [this] using T.add_mem hx hy
  zero_mem' := by
    have : algebraMap K Ω ∘ ((0 : ι → K) ∘ e.symm) = 0 := by funext j; simp
    change _ ∈ T
    rw [this]
    exact T.zero_mem
  smul_mem' a x hx := by
    have : algebraMap K Ω ∘ ((a • x) ∘ e.symm) =
        algebraMap K Ω a • algebraMap K Ω ∘ (x ∘ e.symm) := by
      funext j; simp
    simpa [this] using T.smul_mem (algebraMap K Ω a) hx

omit [Fintype ι] in
theorem mem_domainComap {T : Submodule Ω (Fin n → Ω)} {x : ι → K} :
    x ∈ domainComap K e T ↔ algebraMap K Ω ∘ (x ∘ e.symm) ∈ T := Iff.rfl

omit [Fintype ι] in
/-- The `K`-points of a proper subspace of `Ωⁿ` form a proper subspace of `Kⁱ`. -/
theorem domainComap_ne_top {T : Submodule Ω (Fin n → Ω)} (hT : T ≠ ⊤) :
    domainComap K e T ≠ ⊤ := by
  classical
  intro htop
  apply hT
  rw [eq_top_iff, ← (Pi.basisFun Ω (Fin n)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  have hmem : (Pi.single (e.symm j) 1 : ι → K) ∈ domainComap K e T :=
    htop ▸ Submodule.mem_top
  rw [mem_domainComap] at hmem
  have hj : Pi.basisFun Ω (Fin n) j = algebraMap K Ω ∘ (Pi.single (e.symm j) 1 ∘ e.symm) := by
    funext k
    rw [Pi.basisFun_apply]
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk, e.symm.injective.ne hk]
  rw [SetLike.mem_coe, hj]
  exact hmem

open scoped Classical in
/-- **EF13 Theorem 3.3 for approximation domains** (with Lemmas 5.1 and 5.2), in the shape of Layer
6.1's `NumberField.exists_forall_mem_interval_approxDomain`. Let `L` be forms on `Kⁱ`, `#ι ≥ 2`,
independent at the infinite places and at the places of `Sfin`, with at most `s` distinct forms,
and let `c` have weight `≤ -ε` and spread `approxSupWeight - approxWeight / n ≤ 2A`, with
`ε ≤ 4nA`. Then there is one proper subspace `W`
(the `K`-points of EF13's `T(L', c')` over `AlgebraicClosure K`) and at most
`intervalCount n (s + n) δ'` reals `t ≥ X₀`, `δ' = ε / 4nA`, such that for every level `Q` with
`log Q ≥ X₀` the domain at level `Q` lies in `W`, or `log Q` lies in one of the intervals
`[t, ω₀ t)`, `ω₀ = cutRatio (s + n) δ'`. The threshold `X₀ ≥ domainThreshold` is linear in the
height of the forms. -/
theorem exists_forall_mem_interval_approxDomain_ef [Nontrivial ι] [DecidableEq ι] [NumberField K]
    {Sfin : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) {c : AbsoluteValue K ℝ → ι → ℝ}
    {ε : ℝ} (hε : 0 < ε) (hc : approxWeight Sfin c ≤ -ε) {A : ℝ}
    (hεA : ε ≤ 4 * Fintype.card ι * A)
    (hA : approxSupWeight Sfin c - approxWeight Sfin c / Fintype.card ι ≤ 2 * A) {s : ℕ}
    (hs : formCount Sfin L ≤ s) {X₀ : ℝ}
    (hX₀ : domainThreshold (Fintype.card ι) (finrank ℚ K) s ε A (formLogHeight Sfin L) ≤ X₀) :
    ∃ T : Finset (Submodule K (ι → K)), #T ≤ 1 ∧ (∀ W ∈ T, W ≠ ⊤) ∧
      ∃ 𝒯 : Finset ℝ,
        #𝒯 ≤ FormSystem.intervalCount (Fintype.card ι) (s + Fintype.card ι)
          (domainDelta (Fintype.card ι) ε A) ∧
        (∀ t ∈ 𝒯, X₀ ≤ t) ∧ ∀ Q : ℝ, 1 < Q → X₀ ≤ Real.log Q →
          (∃ W ∈ T, approxDomain Sfin L c Q ⊆ W) ∨
            ∃ t ∈ 𝒯, t ≤ Real.log Q ∧ Real.log Q <
              FormSystem.cutRatio (s + Fintype.card ι) (domainDelta (Fintype.card ι) ε A) * t := by
  set n := Fintype.card ι with hn
  have hn2 : 2 ≤ n := Fintype.one_lt_card
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  set e := Fintype.equivFin ι
  set d := finrank ℚ K with hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast finrank_pos
  have hA0 : 0 < A := by
    by_contra h
    push Not at h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hn0.le h]
  set κ := 2 * A with hκ
  have hκ0 : 0 < κ := by positivity
  set L' := domainSystem L e Sfin hLInf hLFin
  set c' := domainExponent Sfin c e κ
  set δ' := domainDelta n ε A with hδ'
  have hδ'0 : 0 < δ' := by rw [hδ', domainDelta]; positivity
  have hδ'1 : δ' ≤ 1 := by
    rw [hδ', domainDelta, div_le_one (by positivity)]
    linarith
  have hR'2 : 2 ≤ s + n := by omega
  set Ω := AlgebraicClosure K
  obtain ⟨T, hT, -⟩ := L'.exists_isDestabilizing_top (Ω := Ω) c'
  have hR : #L'.forms ≤ s + n := (card_forms_domainSystem_le e hLInf hLFin).trans (by omega)
  have hsup : (∑ w, ⨆ i, c'.arch w i) + ∑ᶠ v, ⨆ i, c'.fin v i ≤ 1 :=
    (domainExponent_sup_le_spread Sfin c e κ hκ0).trans (by rw [div_le_one hκ0]; linarith)
  obtain ⟨S, hScard, hSge, hS⟩ := L'.exists_intervals_cover c' hn2 (domainExponent_sum Sfin c e κ)
    hsup hR hδ'0 hδ'1 hT
  -- the logarithmic height `ℓ` of the forms bounds `log H_{L'}`
  set ℓ := Real.log n.factorial + n * formLogHeight Sfin L / d with hℓ
  have hH1 : 1 ≤ L'.absFormHeight := L'.one_le_absFormHeight
  have hlH0 : 0 ≤ Real.log L'.absFormHeight := Real.log_nonneg hH1
  have hlHℓ : Real.log L'.absFormHeight ≤ ℓ := log_absFormHeight_domainSystem_le e hLInf hLFin
  have hℓ0 : 0 ≤ ℓ := hlH0.trans hlHℓ
  set C : ℝ := ((s + n).choose n : ℝ) with hCdef
  have hC0 : 0 ≤ C := Nat.cast_nonneg _
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  set M := κ / d with hM
  have hM0 : 0 < M := by positivity
  -- above the threshold
  have hthr : ∀ Q : ℝ, X₀ ≤ Real.log Q →
      ℓ + Real.log n / δ' + C * ℓ / (n * δ') ≤ M * Real.log Q := by
    intro Q hQ
    have h1 : M * domainThreshold n d s ε A (formLogHeight Sfin L) =
        ℓ + Real.log n / δ' + C * ℓ / (n * δ') := by
      rw [domainThreshold, ← hδ', ← hℓ, ← hCdef, hM, hκ]
      field_simp
    rw [← h1]
    exact mul_le_mul_of_nonneg_left (hX₀.trans hQ) hM0.le
  have hterm1 : 0 ≤ Real.log n / δ' := div_nonneg hlogn hδ'0.le
  have hterm2 : 0 ≤ C * ℓ / (n * δ') := by positivity
  set W := domainComap K e T with hW
  refine ⟨{W}, (card_singleton W).le, ?_, S.image fun b ↦ max X₀ (Real.log b / M),
    card_image_le.trans hScard, fun t ht ↦ ?_, fun Q hQ hXQ ↦ ?_⟩
  · intro W' hW'
    rw [mem_singleton] at hW'
    rw [hW']
    exact domainComap_ne_top K e hT.lt.ne
  · obtain ⟨b, -, rfl⟩ := mem_image.1 ht
    exact le_max_left _ _
  by_cases hsub : approxDomain Sfin L c Q ⊆ W
  · exact Or.inl ⟨W, mem_singleton_self W, hsub⟩
  right
  obtain ⟨x, hx, hxW⟩ := Set.not_subset.1 hsub
  have hx0 : x ≠ 0 := by rintro rfl; exact hxW W.zero_mem
  have hQ0 : 0 < Q := zero_lt_one.trans hQ
  set Q' := Q ^ M with hQ'
  have hQ'0 : 0 < Q' := Real.rpow_pos_of_pos hQ0 _
  have hQ'1 : 1 ≤ Q' := Real.one_le_rpow hQ.le hM0.le
  have hlQ' : Real.log Q' = M * Real.log Q := Real.log_rpow hQ0 _
  have hthrQ := hthr Q hXQ
  -- `Q' ≥ C₀`
  have hC₀ : max (L'.absFormHeight ^ (((s + n : ℕ) : ℝ)⁻¹)) ((n : ℝ) ^ δ'⁻¹) ≤ Q' := by
    refine max_le ?_ ?_
    · rw [← Real.log_le_log_iff (by positivity) hQ'0, Real.log_rpow (by positivity), hlQ']
      have hR'1 : (1 : ℝ) ≤ ((s + n : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ s + n)
      calc ((s + n : ℕ) : ℝ)⁻¹ * Real.log L'.absFormHeight ≤ Real.log L'.absFormHeight :=
            mul_le_of_le_one_left hlH0 (inv_le_one_of_one_le₀ hR'1)
        _ ≤ M * Real.log Q := by linarith
    · rw [← Real.log_le_log_iff (by positivity) hQ'0, Real.log_rpow hn0, hlQ']
      rw [inv_mul_eq_div]
      linarith
  -- Lemma 5.1 and the determinant
  have hLem := absMulHeight_domainSystem_le (Ω := Ω) e hLInf hLFin hκ0 hQ0 hx0 hx
  have hH : L'.absMulHeight (c'.weight (zero_lt_one.trans_le hQ'1)) (algebraMap K Ω ∘ (x ∘ e.symm))
      ≤ L'.absDet ^ ((n : ℝ)⁻¹) * Q' ^ (-δ') := by
    refine hLem.trans ?_
    have h2 : Q ^ (approxWeight Sfin c / (n * d)) ≤ Q' ^ (-δ') * Q' ^ (-δ') := by
      rw [← Real.rpow_add hQ'0, hQ', ← Real.rpow_mul hQ0.le]
      refine Real.rpow_le_rpow_of_exponent_le hQ.le ?_
      have key : M * (-δ' + -δ') = -ε / (n * d) := by
        rw [hM, hκ, hδ', domainDelta]
        field_simp
        ring
      rw [key]
      exact div_le_div_of_nonneg_right hc (by positivity)
    refine h2.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hQ'0.le _))
    -- `Q'^{-δ'} ≤ Δ^{1/n}`
    have hΔ0 := L'.absDet_pos
    rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_rpow hQ'0,
      Real.log_rpow hΔ0, hlQ']
    have hΔ : (1 - (#L'.forms).choose n : ℝ) * Real.log L'.absFormHeight ≤ Real.log L'.absDet := by
      have h := L'.absFormHeight_rpow_le_absDet
      rw [Fintype.card_fin] at h
      rw [← Real.log_rpow (by positivity)]
      exact Real.log_le_log (by positivity) h
    have hCr : ((#L'.forms).choose n : ℝ) ≤ C := Nat.cast_le.2 (Nat.choose_le_choose n hR)
    have hlow : -(C * ℓ) ≤ Real.log L'.absDet := by
      refine le_trans ?_ hΔ
      nlinarith
    have hδlog : C * ℓ / n ≤ δ' * (M * Real.log Q) := by
      have h3 : C * ℓ / (n * δ') ≤ M * Real.log Q := by linarith
      calc C * ℓ / n = δ' * (C * ℓ / (n * δ')) := by field_simp
        _ ≤ δ' * (M * Real.log Q) := mul_le_mul_of_nonneg_left h3 hδ'0.le
    have h4 : -(C * ℓ / n) ≤ Real.log L'.absDet / n := by
      rw [← neg_div]
      exact div_le_div_of_nonneg_right hlow hn0.le
    rw [inv_mul_eq_div]
    linarith
  have hyT : algebraMap K Ω ∘ (x ∘ e.symm) ∉ T := hxW
  obtain ⟨b, hb, hbQ, hQb⟩ := hS Q' hQ'1 hC₀ _ hyT hH
  have hb1 : 1 < b := by
    have := hSge b hb
    exact (Real.one_lt_rpow (by exact_mod_cast (by omega : 1 < n)) (inv_pos.2 hδ'0)).trans_le
      ((le_max_right _ _).trans this)
  have hb0 : 0 < b := zero_lt_one.trans hb1
  have hρ : 0 ≤ FormSystem.cutRatio (s + n) δ' :=
    (zero_lt_one.trans (FormSystem.one_lt_cutRatio hR'2 hδ'0 hδ'1)).le
  have hlb : Real.log b ≤ M * Real.log Q := by
    rw [← hlQ']; exact Real.log_le_log hb0 hbQ
  have hlb2 : M * Real.log Q < FormSystem.cutRatio (s + n) δ' * Real.log b := by
    rw [← hlQ', ← Real.log_rpow hb0]; exact Real.log_lt_log hQ'0 hQb
  refine ⟨max X₀ (Real.log b / M), mem_image_of_mem _ hb, max_le hXQ ?_, ?_⟩
  · rw [div_le_iff₀ hM0]; linarith
  · calc Real.log Q < FormSystem.cutRatio (s + n) δ' * (Real.log b / M) := by
          rw [mul_div_assoc', lt_div_iff₀ hM0]; linarith
      _ ≤ FormSystem.cutRatio (s + n) δ' * max X₀ (Real.log b / M) :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) hρ

end Interval

end NumberField
