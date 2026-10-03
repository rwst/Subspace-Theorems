/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.GeneralizedRothLemma
public import DiophantineApproximation.IndexRename
public import QuantitativeSubspace.RothLemma

/-!
# Evertse's generalized Roth lemma (Evertse 1996, Lemma 24)

J.-H. Evertse, *An improvement of the quantitative Subspace theorem*, Compositio Math. **101**
(1996), Lemma 24: Roth's lemma of `QuantitativeSubspace/RothLemma.lean` for polynomials in `m`
blocks of `N ≥ 2` variables, along hyperplanes `V_h ⊂ K^N` in place of points of `ℙ¹`. It is
Bombieri–Gubler's Lemma 7.5.19 (`MvPolynomial.formIndex_le_of_degree_ratio`, Layer 5.3 of
`DiophantineApproximation`) with Evertse's Roth lemma in place of Bombieri–Gubler's, and it is
stated in the same language, so that it can replace Layer 5.3 in the Subspace proofs.

* `MvPolynomial.formIndex_le_index`: the index along forms `M h` is at most the index at any
  point `α` on all the hyperplanes `M h = 0`. Each generator `∏ h, M h ^ j h` of `I(t; d; M)`
  vanishes at `α` to index `∑ h, j h / d h`, and the index at a point is a valuation.
* `MvPolynomial.formIndex_le_of_sq_lt_ratio`: **Evertse's Lemma 24.** If
  `d h / d (h + 1) > m² / θ`, `P ≠ 0` is multihomogeneous of multidegree at most `d`, and every
  form has `d h · h(M h) > n B` with `n + 1` the block size and
  `B = max(1, m²/θ)^m ([K : ℚ] h(ℙ¹) |d| + m (h(P) + [K : ℚ] (|d| log 2 + m log |d| + m)))`
  the bound of `MvPolynomial.exists_mul_logHeight_le`, then the index of `P` along the forms is
  at most `θ`. Evertse's conclusion is index `< mΘ`, so his `Θ` is `θ / m` here, and his
  conditions read `d h / d (h + 1) ≥ 2m³ / θ` and
  `d h h(V_h) ≥ (N - 1) (3m³/θ)^m (|d| + h(F))` in absolute heights.

The proof is Bombieri–Gubler's reduction, which is also Evertse's (after Schmidt): normalize one
coordinate `i₀ h` of every form, keep a second coordinate `i₁ h` that carries a `1 / n` of its
height, and eliminate the other variables (`MvPolynomial.exists_elimination`), which neither
raises the height nor lowers the index. The result `Q` lives on the coordinates `i₀, i₁`, and on
`(ℙ¹)^m` its index along the truncated forms is at most its index at their common zero
`α_h = (-c_h, 1)`. Renaming to `Fin m × Fin 2` and padding the multidegree up to `d` with powers
of the coordinate where `α` is `1` (as Evertse does with `X_{h1}^{a_h}`) changes neither index nor
height, and Roth's lemma bounds that index by `θ`, since `h(α_h) = h(c_h) ≥ h(M h) / n`.

## Implementation notes

⚠ **Evertse's Lemma 26 (the grid form) is not restated here.** It is Lemma 24 followed by a
Combinatorial-Nullstellensatz argument on a grid of each `V_h`, and that second half is already
Layers 5.5 and 5.6 of `DiophantineApproximation`
(`MvPolynomial.exists_linSubst_hasseDeriv_ne_zero_of_formIndex_le` and
`MvPolynomial.exists_eval_hasseDeriv_ne_zero`), which take the index along the forms as input.
Replacing `MvPolynomial.formIndex_le_of_degree_ratio` by the theorem below is the whole change.

⚠ **The height theory is that of the Roth lemma**, on the ring of `(ℙ¹)^m`,
`MvPolynomial (Fin m × Fin 2) K` with blocks `Prod.fst`: the abstract
`MvPolynomial.MultiprojectiveHeight` `H`, whose `H.botBound 1` is `h(ℙ¹)`.

This is Layer Q1.5 of the `QuantitativeSubspace` roadmap.
-/

@[expose] public section

open Finset Height AdmissibleAbsValues

open scoped ENNReal

namespace MvPolynomial

section Index

variable {K κ ι : Type*} [Field K] [Fintype κ] [Fintype ι]

omit [Fintype κ] in
/-- A nonzero coefficient of a linear form on one block sits at a single variable of that
block. -/
theorem exists_eq_single_of_coeff_blockForm_ne_zero {M : κ → ι → K} {h : κ}
    {ν : κ × ι →₀ ℕ} (hν : (blockForm M h).coeff ν ≠ 0) :
    ∃ i, ν = Finsupp.single (h, i) 1 := by
  classical
  by_contra hcon
  push Not at hcon
  refine hν ?_
  rw [blockForm, coeff_sum]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [coeff_C_mul, coeff_X]
  simp [(hcon i).symm]

omit [Fintype κ] in
/-- A linear form on block `h` that vanishes at `α` vanishes there to index at least `1 / d h`. -/
theorem ofReal_inv_le_index_blockForm {d : κ → ℝ} {M : κ → ι → K} {α : κ × ι → K} {h : κ}
    (hα : ∑ i, M h i * α (h, i) = 0) :
    ENNReal.ofReal (d h)⁻¹ ≤ index (fun s ↦ d s.1) α (blockForm M h) := by
  classical
  refine le_index _ fun μ hμ ↦ ?_
  have hμ0 : hasseDeriv μ (blockForm M h) ≠ 0 := fun h0 ↦ hμ (by rw [h0, map_zero])
  obtain ⟨ν, hν⟩ := exists_coeff_ne_zero hμ0
  rw [hasseDeriv_coeff] at hν
  obtain ⟨i, hi⟩ := exists_eq_single_of_coeff_blockForm_ne_zero (right_ne_zero_of_mul hν)
  have hμne : μ ≠ 0 := by
    rintro rfl
    refine hμ ?_
    rw [hasseDeriv_zero_apply, blockForm, map_sum]
    simpa using hα
  have hμle : μ ≤ Finsupp.single (h, i) 1 := hi ▸ le_add_self
  obtain rfl : μ = Finsupp.single (h, i) 1 := by
    refine le_antisymm hμle fun s ↦ ?_
    by_cases hs : s = (h, i)
    · subst hs
      obtain ⟨t, ht⟩ := Finsupp.ne_iff.mp hμne
      have ht' := hμle t
      rw [Finsupp.single_apply] at ht' ⊢
      split_ifs at ht' with hts
      · subst hts
        simp only [ite_true]
        exact Nat.one_le_iff_ne_zero.mpr ht
      · exact absurd (Nat.le_zero.mp ht') ht
    · simp [Ne.symm hs]
  rw [Finsupp.sum_single_index (by simp), Nat.cast_one, one_div]

/-- **The index along the forms is at most the index at a point on all of them.** If `α` lies on
every hyperplane `M h = 0`, then `P ∈ I(t; d; M)` vanishes at `α` to index at least `t`, because
the index at a point is a valuation and each `M h` vanishes there to index `1 / d h`. -/
theorem formIndex_le_index {d : κ → ℝ} (hd : ∀ h, 0 ≤ d h) {M : κ → ι → K} {α : κ × ι → K}
    (hα : ∀ h, ∑ i, M h i * α (h, i) = 0) (P : MvPolynomial (κ × ι) K) :
    formIndex d M P ≤ index (fun s ↦ d s.1) α P := by
  classical
  have hd' : ∀ s : κ × ι, 0 ≤ d s.1 := fun s ↦ hd s.1
  refine iSup_le fun t ↦ iSup_le fun ht ↦ ?_
  refine Submodule.span_induction (p := fun Q _ ↦ ENNReal.ofReal t ≤ index _ α Q) ?_ ?_ ?_ ?_ ht
  · rintro _ ⟨j, hj, rfl⟩
    rw [index_prod _ hd']
    calc ENNReal.ofReal t ≤ ENNReal.ofReal (∑ h, (j h : ℝ) / d h) := ENNReal.ofReal_le_ofReal hj
      _ = ∑ h, (j h : ℝ≥0∞) * ENNReal.ofReal (d h)⁻¹ := by
        rw [ENNReal.ofReal_sum_of_nonneg fun h _ ↦ div_nonneg (Nat.cast_nonneg _) (hd h)]
        refine Finset.sum_congr rfl fun h _ ↦ ?_
        rw [div_eq_mul_inv, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ ∑ h, index (fun s ↦ d s.1) α (blockForm M h ^ j h) := by
        refine Finset.sum_le_sum fun h _ ↦ ?_
        rw [index_pow _ hd']
        gcongr
        exact ofReal_inv_le_index_blockForm (hα h)
  · simp
  · intro x y _ _ hx hy
    exact (le_min hx hy).trans (le_index_add _ hd' α x y)
  · intro a x _ hx
    rw [smul_eq_mul, index_mul _ hd']
    exact hx.trans le_add_self

end Index

section Main

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]

/-- **Evertse's generalized Roth lemma** (Evertse 1996, Lemma 24, with the Roth lemma of
`MvPolynomial.exists_mul_logHeight_le`). Let `P ≠ 0` be multihomogeneous of multidegree at most
`d` in `m` blocks of `n + 1 ≥ 2` variables, `d` decreasing with `d h / d (h + 1) > m² / θ`, and
let `M h` be nonzero linear forms with `n B < d h · h(M h)` for every `h`, where
`B = max(1, m²/θ)^m ([K : ℚ] max(h(ℙ¹), 0) |d| + m (h(P) + [K : ℚ] (|d| log 2 + m log |d| + m)))`.
Then the index of `P` along the forms is at most `θ`.

This is `MvPolynomial.formIndex_le_of_degree_ratio` (Bombieri–Gubler 7.5.19) with Evertse's
ratio `m² / θ` in place of Bombieri–Gubler's `σ⁻¹` and conclusion `θ` in place of
`2 (m + 1) σ ^ ((1 / 2) ^ m)`. -/
theorem formIndex_le_of_sq_lt_ratio [CharZero K] [AdmissibleAbsValues K] {m n : ℕ}
    (H : MultiprojectiveHeight (K := K) (Prod.fst : Fin m × Fin 2 → Fin m))
    (hn : 1 ≤ n) (hcard : Fintype.card ι = n + 1) {d : Fin m → ℕ} (hd : ∀ h, 0 < d h)
    (hanti : Antitone d) {θ : ℝ} (hθ : 0 < θ)
    (hratio : ∀ i j : Fin m, (i : ℕ) + 1 = j → (m : ℝ) ^ 2 < θ * (d i / d j))
    {r : Fin m → ℕ} {P : MvPolynomial (Fin m × ι) K} (hP0 : P ≠ 0)
    (hP : IsMultiHomogeneous r P) (hrd : ∀ h, r h ≤ d h)
    {M : Fin m → ι → K} (hM : ∀ h, M h ≠ 0)
    (hheight : ∀ h, (n : ℝ) * (max 1 ((m : ℝ) ^ 2 / θ) ^ m *
      (totalWeight K * max (H.botBound 1) 0 * (∑ i, d i : ℕ) + m * (P.logHeight +
        totalWeight K * ((∑ i, d i : ℕ) * Real.log 2 + m * Real.log (∑ i, d i : ℕ) + m)))) <
      d h * Height.logHeight (M h)) :
    formIndex (fun h ↦ (d h : ℝ)) M P ≤ ENNReal.ofReal θ := by
  classical
  -- Normalize one coordinate of every form and pick the second coordinate (Bombieri–Gubler).
  obtain ⟨i₀, hi₀⟩ := exists_forall_apply_ne_zero hM
  obtain ⟨N, hNeq, hN1, hNH⟩ : ∃ N : Fin m → ι → K,
      formIndex (fun h ↦ (d h : ℝ)) N P = formIndex (fun h ↦ (d h : ℝ)) M P ∧
        (∀ h, N h (i₀ h) = 1) ∧ (∀ h, Height.logHeight (N h) = Height.logHeight (M h)) :=
    ⟨fun h i ↦ (M h (i₀ h))⁻¹ * M h i, formIndex_smul (fun h ↦ inv_ne_zero (hi₀ h)) P,
      fun h ↦ inv_mul_cancel₀ (hi₀ h),
      fun h ↦ Height.logHeight_smul_eq_logHeight (M h) (inv_ne_zero (hi₀ h))⟩
  have hN0 : ∀ h, N h (i₀ h) ≠ 0 := fun h ↦ by rw [hN1 h]; exact one_ne_zero
  have hchoice : ∀ h, ∃ i₁, i₁ ≠ i₀ h ∧
      Height.logHeight (N h) ≤ (n : ℝ) * Height.logHeight₁ (N h i₁) := by
    intro h
    have hcarde : #(univ.erase (i₀ h)) = n := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcard]
      omega
    have hnee : (univ.erase (i₀ h)).Nonempty := by
      rw [← Finset.card_pos, hcarde]
      omega
    obtain ⟨i₁, hi₁ne, hi₁le⟩ :=
      Height.exists_logHeight_le_mul_logHeight₁_div (N h) (i₀ h) (hN0 h) hnee
    exact ⟨i₁, hi₁ne, by rwa [hcarde, hN1 h, div_one] at hi₁le⟩
  choose i₁ hi₁ne hi₁le using hchoice
  -- Eliminate the other variables.
  obtain ⟨T, hTmem⟩ : ∃ T : Finset (Fin m × ι),
      ∀ t : Fin m × ι, t ∈ T ↔ (t.2 ≠ i₀ t.1 ∧ t.2 ≠ i₁ t.1) :=
    ⟨univ.filter (fun t ↦ t.2 ≠ i₀ t.1 ∧ t.2 ≠ i₁ t.1), fun t ↦ by simp⟩
  obtain ⟨k, Q, -, hQ0, hQcoeff, hQsupp, ⟨r', hr', hQhom⟩, hidx⟩ :=
    exists_elimination (d := fun h ↦ (d h : ℝ)) (fun _ ↦ Nat.cast_nonneg _) (i₀ := i₀) T
      (fun t htT ↦ ((hTmem t).mp htT).1) N hN0 r P hP0 hP
  -- The common zero `α` of the truncated forms.
  set c : Fin m → K := fun h ↦ N h (i₁ h) with hc
  set α : Fin m × ι → K := fun p ↦
    if p.2 = i₀ p.1 then -c p.1 else if p.2 = i₁ p.1 then 1 else 0 with hαdef
  have hα : ∀ h, ∑ i, zeroOut T N h i * α (h, i) = 0 := by
    intro h
    rw [Finset.sum_eq_add (i₀ h) (i₁ h) (hi₁ne h).symm]
    · rw [zeroOut_apply_of_notMem N (fun hc ↦ ((hTmem _).mp hc).1 rfl),
        zeroOut_apply_of_notMem N (fun hc ↦ ((hTmem _).mp hc).2 rfl), hN1 h]
      simp [hαdef, hc, hi₁ne h]
    · intro i _ hi
      rw [zeroOut_apply_of_mem N ((hTmem _).mpr ⟨hi.1, hi.2⟩), zero_mul]
    · simp
    · simp
  have h1 := formIndex_le_index (fun h ↦ Nat.cast_nonneg (d h)) hα Q
  -- Rename to `(ℙ¹)^m`.
  set e : Fin m × Fin 2 → Fin m × ι := fun p ↦ (p.1, if p.2 = 0 then i₀ p.1 else i₁ p.1) with hedef
  have he : Function.Injective e := by
    rintro ⟨h, j⟩ ⟨h', j'⟩ hhj
    simp only [hedef, Prod.mk.injEq] at hhj
    obtain ⟨rfl, hj⟩ := hhj
    refine Prod.ext rfl ?_
    fin_cases j <;> fin_cases j' <;> simp_all [Ne.symm (hi₁ne h)]
  obtain ⟨Q₂, rfl⟩ : ∃ Q₂, rename e Q₂ = Q := by
    refine exists_rename_eq_of_vars_subset_range Q e he fun s hs ↦ ?_
    obtain ⟨ν, hν, hsν⟩ := (mem_vars_iff_mem_support s).mp hs
    by_cases h0 : s.2 = i₀ s.1
    · exact ⟨(s.1, 0), Prod.ext rfl (by simp [hedef, h0])⟩
    by_cases h1 : s.2 = i₁ s.1
    · exact ⟨(s.1, 1), Prod.ext rfl (by simp [hedef, h1])⟩
    exact absurd (hQsupp s ((hTmem s).mpr ⟨h0, h1⟩) ν hν) (Finsupp.mem_support_iff.mp hsν)
  rw [index_rename he] at h1
  set α₂ : Fin m × Fin 2 → K := fun p ↦ α (e p) with hα₂def
  have hα₂ : ∀ p : Fin m × Fin 2, α₂ p = ![-c p.1, 1] p.2 := by
    rintro ⟨h, j⟩
    fin_cases j <;> simp [hα₂def, hαdef, hedef, hi₁ne h]
  change formIndex _ _ _ ≤ index (fun j : Fin m × Fin 2 ↦ (d j.1 : ℝ)) α₂ Q₂ at h1
  have hd₂ : ∀ j : Fin m × Fin 2, (0 : ℝ) ≤ d j.1 := fun j ↦ Nat.cast_nonneg _
  -- Pad the multidegree up to `d` with the coordinate where `α₂` is `1`.
  set a : Fin m × Fin 2 →₀ ℕ := ∑ h, Finsupp.single (h, 1) (d h - r' h) with hadef
  set F : MvPolynomial (Fin m × Fin 2) K := Q₂ * monomial a 1 with hFdef
  have hQ₂0 : Q₂ ≠ 0 := by
    rintro rfl
    exact hQ0 (map_zero _)
  have hF0 : F ≠ 0 := mul_ne_zero hQ₂0 (by simp)
  have hmono : index (fun j : Fin m × Fin 2 ↦ (d j.1 : ℝ)) α₂ (monomial a 1) = 0 := by
    refine le_antisymm ?_ bot_le
    refine (index_le _ (μ := 0) ?_).trans (by simp)
    rw [hasseDeriv_zero_apply, hadef, monomial_sum_one, map_prod]
    refine Finset.prod_ne_zero_iff.mpr fun h _ ↦ ?_
    rw [eval_monomial, one_mul, Finsupp.prod_single_index (by simp), hα₂]
    simp
  have hFidx : index (fun j : Fin m × Fin 2 ↦ (d j.1 : ℝ)) α₂ F =
      index (fun j : Fin m × Fin 2 ↦ (d j.1 : ℝ)) α₂ Q₂ := by
    rw [hFdef, index_mul _ hd₂, hmono, add_zero]
  have hQ₂hom : IsWeightedHomogeneous (multiWeight (Prod.fst : Fin m × Fin 2 → Fin m)) Q₂ r' := by
    intro ν hν
    have hν' : (rename e Q₂).coeff (ν.mapDomain e) ≠ 0 := by
      rwa [coeff_rename_mapDomain e he]
    have := (isMultiHomogeneous_iff.mp hQhom) hν'
    change Finsupp.weight (multiWeight Prod.fst) _ = _ at this
    rw [weight_multiWeight_eq_mapDomain, ← Finsupp.mapDomain_comp] at this
    rw [weight_multiWeight_eq_mapDomain]
    exact this
  have hF : IsWeightedHomogeneous (multiWeight (Prod.fst : Fin m × Fin 2 → Fin m)) F d := by
    have hmon : IsWeightedHomogeneous (multiWeight (Prod.fst : Fin m × Fin 2 → Fin m))
        (monomial a (1 : K)) (d - r') := by
      refine isWeightedHomogeneous_monomial _ _ _ ?_
      rw [weight_multiWeight_eq_mapDomain, hadef, Finsupp.mapDomain_finsetSum]
      funext h
      rw [Finsupp.finsetSum_apply, Finset.sum_eq_single h
        (fun h' _ hh' ↦ by
          rw [Finsupp.mapDomain_single, Finsupp.single_apply]
          exact ite_eq_right_iff.mpr fun hc ↦ absurd hc hh') (by simp),
        Finsupp.mapDomain_single, Finsupp.single_eq_same]
      rfl
    have := hQ₂hom.mul hmon
    convert this using 1
    funext h
    simp [Nat.add_sub_cancel' ((hr' h).trans (hrd h))]
  -- The height does not grow.
  have hFh : F.logHeight ≤ P.logHeight := by
    refine logHeight_le_of_coeff_subfamily fun ν hν ↦ ?_
    have hν' := mem_support_iff.mp hν
    rw [hFdef, coeff_mul_monomial'] at hν'
    have ha : a ≤ ν := by
      by_contra ha
      simp [ha] at hν'
    simp only [ha, ite_true, mul_one] at hν'
    have hQν : (rename e Q₂).coeff ((ν - a).mapDomain e) ≠ 0 := by
      rwa [coeff_rename_mapDomain e he]
    refine ⟨(ν - a).mapDomain e + k, mem_support_iff.mpr ?_, ?_⟩
    · rw [← hQcoeff _ hQν]
      exact hQν
    · rw [← hQcoeff _ hQν, coeff_rename_mapDomain e he, hFdef, coeff_mul_monomial']
      simp only [ha, ite_true, mul_one]
  -- The height of the point.
  have hαh : ∀ k, Height.logHeight (fun s : {s : Fin m × Fin 2 // s.1 = k} ↦ α₂ s) =
      logHeight₁ (c k) := by
    intro k
    let E : {s : Fin m × Fin 2 // s.1 = k} ≃ Fin 2 :=
      ⟨fun s ↦ s.1.2, fun j ↦ ⟨(k, j), rfl⟩, fun ⟨⟨h, j⟩, hh⟩ ↦ by subst hh; rfl, fun j ↦ rfl⟩
    have hE : (fun s : {s : Fin m × Fin 2 // s.1 = k} ↦ α₂ s) = ![-c k, 1] ∘ E := by
      funext ⟨⟨h, j⟩, hh⟩
      subst hh
      exact hα₂ _
    rw [hE, logHeight_comp_equiv, ← logHeight₁_eq_logHeight, logHeight₁_neg]
  -- Roth's lemma.
  have hnot : ¬ indexIdeal Prod.fst d F θ ≤ pointIdeal Prod.fst α₂ := by
    intro hFP
    have h2 : ∀ i : Fin m, #(univ.filter fun s : Fin m × Fin 2 ↦ s.1 = i) = 2 := by
      intro i
      rw [Finset.card_filter, Fintype.sum_prod_type]
      simp [apply_ite Finset.card]
    obtain ⟨k, hk⟩ := exists_mul_logHeight_le (fun h ↦ ⟨(h, 0), rfl⟩) H h2 hd hanti hF hF0
      hθ hratio (fun h ↦ ⟨(h, 1), rfl, by simp [hα₂]⟩) hFP
    rw [hαh k] at hk
    change _ ≤ _ * (_ + _ * (F.logHeight + _)) at hk
    have hk' := hheight k
    rw [← hNH k] at hk'
    have hnk := mul_le_mul_of_nonneg_left (hi₁le k) (Nat.cast_nonneg (d k))
    change _ ≤ _ * (_ * logHeight₁ (c k)) at hnk
    have hnB := mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg n)
    have hFP' : (n : ℝ) * (max 1 ((m : ℝ) ^ 2 / θ) ^ m *
        (totalWeight K * max (H.botBound 1) 0 * (∑ i, d i : ℕ) + m * (F.logHeight +
          totalWeight K * ((∑ i, d i : ℕ) * Real.log 2 + m * Real.log (∑ i, d i : ℕ) + m)))) ≤
        (n : ℝ) * (max 1 ((m : ℝ) ^ 2 / θ) ^ m *
        (totalWeight K * max (H.botBound 1) 0 * (∑ i, d i : ℕ) + m * (P.logHeight +
          totalWeight K * ((∑ i, d i : ℕ) * Real.log 2 + m * Real.log (∑ i, d i : ℕ) + m)))) := by
      gcongr
    have : (n : ℝ) * ((d k : ℝ) * logHeight₁ (c k)) = (d k : ℝ) * ((n : ℝ) * logHeight₁ (c k)) := by
      ring
    linarith
  rw [indexIdeal_le_pointIdeal_iff hF] at hnot
  push Not at hnot
  obtain ⟨κ, hκ, hne⟩ := hnot
  have hsum : (κ.sum fun j k ↦ (k : ℝ) / d j.1) =
      Finsupp.weight (fun s : Fin m × Fin 2 ↦ ((d s.1 : ℝ))⁻¹) κ := by
    rw [Finsupp.weight_apply]
    refine Finsupp.sum_congr fun j _ ↦ ?_
    rw [nsmul_eq_mul, div_eq_mul_inv]
  calc formIndex (fun h ↦ (d h : ℝ)) M P = formIndex (fun h ↦ (d h : ℝ)) N P := hNeq.symm
    _ ≤ _ := hidx
    _ ≤ _ := h1
    _ = index (fun j : Fin m × Fin 2 ↦ (d j.1 : ℝ)) α₂ F := hFidx.symm
    _ ≤ _ := index_le _ hne
    _ ≤ ENNReal.ofReal θ := ENNReal.ofReal_le_ofReal (hsum ▸ hκ)

end Main

end MvPolynomial
