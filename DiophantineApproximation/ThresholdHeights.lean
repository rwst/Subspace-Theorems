/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.ParametricSubspace
public import DiophantineApproximation.FundamentalInequality
import DiophantineApproximation.GeneralizedRothLemma

/-!
# The thresholds of the parametric Subspace Theorem, bounded by heights

The threshold `NumberField.parametricThreshold` of the interval form of Layer 6.1 is a formula in
local invariants of the forms: determinants and inverse matrices at the places of `S`, maximal
minors, and least heights of vectors in pattern spaces. This file bounds them by the heights of
the entries of the matrices of the forms.

## Main results

* `NumberField.logHeight₁_det_le`: the height of a determinant against the heights of the
  entries.
* `NumberField.logHeight₁_inv_apply_le`: the same for the entries of the inverse matrix
  (Cramer's rule).
* `NumberField.apply_le_exp_logHeight₁` and `NumberField.exp_neg_logHeight₁_le_apply`: the value
  of a nonzero element at one place of `S` lies between `H(x) ^ (-1)` and `H(x)`.
* `NumberField.formLogHeight`: the sum of the logarithmic heights of the entries of the matrices
  of the forms at the places of `S`. Everything below is bounded in terms of it, through
  `detLogBound` (the height of a determinant) and `invSizeBound` (the local size of an inverse).
* `NumberField.approxConst_le` and `NumberField.inv_le_approxConst`: the comparison constant of
  Layer 4.1 from both sides.
* `NumberField.pointHeightConst_le`, `NumberField.minimaThreshold_le`,
  `NumberField.rankThreshold_le` and `NumberField.wedgeWeightConst_le`: the constants of the
  minima bounds, of Lemma 7.5.12 and of the wedge weight.
* `NumberField.auxHeightConst_le` and `NumberField.sum_log_mulHeight₁_refFamily_le`: the constant
  of the auxiliary polynomial and the heights of the reference family of Layer 5.6.
* `NumberField.formLogHeight_wedgeForms_le`: the entries of the wedge forms are minors, so their
  height is bounded by that of the forms.
* `NumberField.kappaFactor_pow_le_normalKappa`: the constant `κ` of Lemma 7.5.21 from below.
* `NumberField.patternConst_le` and `NumberField.patternHeightBound_le`: the constants of the
  pattern vectors. A pattern space is the kernel of `patternMatrix` (`mem_patternSpace_iff`),
  built from the columns of the inverse matrices, so Siegel's lemma over `K`
  (`exists_ne_zero_mem_ker_absMulHeight_le`) bounds its least height (`patternHeight_le`).

This is part of Q0.2e of the `QuantitativeSubspace` roadmap.
-/

@[expose] public section

open Finset Module Height

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

section Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The height of a determinant**: if every entry of an `N × N` matrix has logarithmic height at
most `h`, the determinant has logarithmic height at most `d log N! + N! N h`. -/
theorem logHeight₁_det_le (M : Matrix n n K) {h : ℝ} (hM : ∀ i j, logHeight₁ (M i j) ≤ h) :
    logHeight₁ M.det ≤ totalWeight K * Real.log (Fintype.card n).factorial
      + (Fintype.card n).factorial * (Fintype.card n * h) := by
  rw [Matrix.det_apply]
  refine (logHeight₁_sum_le _ _).trans ?_
  rw [Finset.card_univ, Fintype.card_perm]
  refine add_le_add le_rfl ?_
  have hσ : ∀ σ : Equiv.Perm n,
      logHeight₁ (Equiv.Perm.sign σ • ∏ i, M (σ i) i) ≤ Fintype.card n * h := by
    intro σ
    have hsign : logHeight₁ (Equiv.Perm.sign σ • ∏ i, M (σ i) i)
        = logHeight₁ (∏ i, M (σ i) i) := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> rw [h1] <;> simp
    rw [hsign]
    refine (logHeight₁_prod_le _ _).trans ?_
    calc ∑ i, logHeight₁ (M (σ i) i) ≤ ∑ _i : n, h := Finset.sum_le_sum fun i _ ↦ hM _ _
      _ = Fintype.card n * h := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc ∑ σ : Equiv.Perm n, logHeight₁ (Equiv.Perm.sign σ • ∏ i, M (σ i) i)
      ≤ ∑ _σ : Equiv.Perm n, (Fintype.card n * h : ℝ) := Finset.sum_le_sum fun σ _ ↦ hσ σ
    _ = (Fintype.card n).factorial * (Fintype.card n * h) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]

/-- **Cramer's rule, in heights**: if every entry of an `N × N` matrix has logarithmic height at
most `h ≥ 0`, every entry of its inverse has logarithmic height at most
`2 (d log N! + N! N h)`. -/
theorem logHeight₁_inv_apply_le (M : Matrix n n K) {h : ℝ} (h0 : 0 ≤ h)
    (hM : ∀ i j, logHeight₁ (M i j) ≤ h) (i j : n) :
    logHeight₁ (M⁻¹ i j) ≤ 2 * (totalWeight K * Real.log (Fintype.card n).factorial
      + (Fintype.card n).factorial * (Fintype.card n * h)) := by
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  refine (logHeight₁_mul_le _ _).trans ?_
  rw [logHeight₁_inv, two_mul]
  refine add_le_add (logHeight₁_det_le M hM) ?_
  rw [Matrix.adjugate_apply]
  refine logHeight₁_det_le _ fun a b ↦ ?_
  rw [Matrix.updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]
    split_ifs
    · rw [logHeight₁_one]; exact h0
    · rw [logHeight₁_zero]; exact h0
  · exact hM a b

end Matrix

/-- **The value at an infinite place is at most the height.** -/
theorem InfinitePlace.apply_le_exp_logHeight₁ (w : InfinitePlace K) (x : K) :
    w x ≤ Real.exp (logHeight₁ x) := by
  rw [logHeight₁_eq_log_mulHeight₁, Real.exp_log (mulHeight₁_pos x)]
  exact (le_max_left _ _).trans (InfinitePlace.max_apply_one_le_mulHeight₁ w x)

/-- **The value at a finite place is at most the height.** -/
theorem FinitePlace.apply_le_exp_logHeight₁ (v : FinitePlace K) (x : K) :
    v x ≤ Real.exp (logHeight₁ x) := by
  rw [logHeight₁_eq_log_mulHeight₁, Real.exp_log (mulHeight₁_pos x)]
  exact (le_max_left _ _).trans (FinitePlace.max_apply_one_le_mulHeight₁ v x)

/-- **Liouville's inequality at an infinite place**: a nonzero element is at least the inverse of
its height there. -/
theorem InfinitePlace.exp_neg_logHeight₁_le_apply (w : InfinitePlace K) {x : K} (hx : x ≠ 0) :
    Real.exp (-logHeight₁ x) ≤ w x := by
  rw [Real.exp_neg, logHeight₁_eq_log_mulHeight₁, Real.exp_log (mulHeight₁_pos x)]
  have h := inv_mulHeight₁_le_prod_min_one_apply {w} (∅ : Finset (FinitePlace K)) hx
  rw [Finset.prod_singleton, Finset.prod_empty, mul_one] at h
  refine h.trans ((pow_le_of_le_one (le_min zero_le_one (w.1.nonneg x)) (min_le_left _ _)
    w.mult_ne_zero).trans (min_le_right _ _))

/-- **Liouville's inequality at a finite place**: a nonzero element is at least the inverse of its
height there. -/
theorem FinitePlace.exp_neg_logHeight₁_le_apply (v : FinitePlace K) {x : K} (hx : x ≠ 0) :
    Real.exp (-logHeight₁ x) ≤ v x := by
  rw [Real.exp_neg, logHeight₁_eq_log_mulHeight₁, Real.exp_log (mulHeight₁_pos x)]
  have h := inv_mulHeight₁_le_prod_min_one_apply (∅ : Finset (InfinitePlace K)) {v} hx
  rw [Finset.prod_singleton, Finset.prod_empty, one_mul] at h
  exact h.trans (min_le_right _ _)

/-- **The value at a place of `S` is at most the height.** -/
theorem sPlace_apply_le_exp_logHeight₁ {Sfin : Finset (FinitePlace K)}
    (t : InfinitePlace K ⊕ ↥Sfin) (x : K) : sPlace Sfin t x ≤ Real.exp (logHeight₁ x) := by
  rcases t with w | v
  · exact w.apply_le_exp_logHeight₁ x
  · exact (v : FinitePlace K).apply_le_exp_logHeight₁ x

/-- **Liouville's inequality at a place of `S`.** -/
theorem exp_neg_logHeight₁_le_sPlace_apply {Sfin : Finset (FinitePlace K)}
    (t : InfinitePlace K ⊕ ↥Sfin) {x : K} (hx : x ≠ 0) :
    Real.exp (-logHeight₁ x) ≤ sPlace Sfin t x := by
  rcases t with w | v
  · exact w.exp_neg_logHeight₁_le_apply hx
  · exact (v : FinitePlace K).exp_neg_logHeight₁_le_apply hx

/-- **The height of a tuple completed by `1`** is at most the product of the heights of its
entries. -/
theorem log_mulHeight_sum_elim_one_le {α : Type*} [Fintype α] (x : α → K) :
    Real.log (mulHeight (Sum.elim x fun _ : Unit ↦ (1 : K))) ≤ ∑ a, logHeight₁ (x a) := by
  classical
  have h := mulHeight_le_prod_mulHeight₁_div (Sum.elim x fun _ : Unit ↦ (1 : K)) (.inr ())
    one_ne_zero
  rw [Finset.prod_erase _ (by simp [mulHeight₁_one]), Fintype.prod_sum_type] at h
  simp only [Sum.elim_inl, Sum.elim_inr, div_one, mulHeight₁_one, Finset.prod_const_one,
    mul_one] at h
  simp_rw [logHeight₁_eq_log_mulHeight₁]
  rw [← Real.log_prod (fun a _ ↦ (mulHeight₁_pos _).ne')]
  exact Real.log_le_log (mulHeight_pos _) h

/-- The logarithmic height of a natural number is at most `d log n`. -/
theorem logHeight₁_natCast_le (n : ℕ) : logHeight₁ (n : K) ≤ totalWeight K * Real.log n := by
  have h := logHeight₁_sum_le (Finset.range n) fun _ ↦ (1 : K)
  simpa [logHeight₁_one] using h

/-- The logarithmic height of an integer is at most `d log |k|`. -/
theorem logHeight₁_intCast_le (k : ℤ) :
    logHeight₁ (k : K) ≤ totalWeight K * Real.log |(k : ℝ)| := by
  have h : logHeight₁ (k : K) = logHeight₁ ((k.natAbs : ℕ) : K) := by
    rcases Int.natAbs_eq k with h | h
    · conv_lhs => rw [h]
      simp
    · conv_lhs => rw [h]
      simp
  have hk : ((k.natAbs : ℕ) : ℝ) = |(k : ℝ)| := by
    rw [← Int.cast_abs, ← Int.cast_natCast, Int.natCast_natAbs]
  rw [h, ← hk]
  exact logHeight₁_natCast_le k.natAbs

section Forms

open NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The bound of Cramer's rule** for `N × N` matrices with entries of logarithmic height at
most `h`: `d log N! + N! N h`, the bound on the logarithmic height of the determinant. -/
noncomputable def detLogBound (K : Type*) [Field K] [NumberField K] (N : ℕ) (h : ℝ) : ℝ :=
  totalWeight K * Real.log N.factorial + N.factorial * (N * h)

theorem detLogBound_nonneg (N : ℕ) {h : ℝ} (h0 : 0 ≤ h) : 0 ≤ detLogBound K N h :=
  add_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (Real.log_nonneg (Nat.one_le_cast.2 (Nat.factorial_pos N)))) (by positivity)

variable (Sfin : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → ι → Dual K (ι → K))

/-- **The logarithmic height of a system of forms at the places of `S`**: the sum of the
logarithmic heights of the entries of its matrices at the places of `S`. -/
noncomputable def formLogHeight : ℝ :=
  ∑ t : (InfinitePlace K ⊕ ↥Sfin) × ι × ι,
    logHeight₁ (formMatrix L (sPlace Sfin t.1) t.2.1 t.2.2)

theorem formLogHeight_nonneg : 0 ≤ formLogHeight Sfin L :=
  Finset.sum_nonneg fun _ _ ↦ zero_le_logHeight₁ _

variable {Sfin L}

theorem logHeight₁_formMatrix_le (t : InfinitePlace K ⊕ ↥Sfin) (j i : ι) :
    logHeight₁ (formMatrix L (sPlace Sfin t) j i) ≤ formLogHeight Sfin L := by
  have h := Finset.single_le_sum (f := fun t : (InfinitePlace K ⊕ ↥Sfin) × ι × ι ↦
    logHeight₁ (formMatrix L (sPlace Sfin t.1) t.2.1 t.2.2))
    (fun _ _ ↦ zero_le_logHeight₁ _) (Finset.mem_univ (t, j, i))
  exact h

theorem logHeight₁_det_formMatrix_le (t : InfinitePlace K ⊕ ↥Sfin) :
    logHeight₁ (formMatrix L (sPlace Sfin t)).det
      ≤ detLogBound K (Fintype.card ι) (formLogHeight Sfin L) :=
  logHeight₁_det_le _ (logHeight₁_formMatrix_le t)

theorem logHeight₁_inv_formMatrix_le (t : InfinitePlace K ⊕ ↥Sfin) (j i : ι) :
    logHeight₁ ((formMatrix L (sPlace Sfin t))⁻¹ j i)
      ≤ 2 * detLogBound K (Fintype.card ι) (formLogHeight Sfin L) :=
  logHeight₁_inv_apply_le _ (formLogHeight_nonneg Sfin L) (logHeight₁_formMatrix_le t) j i

/-- **The determinant of the forms at a place of `S`, from above.** -/
theorem sPlace_det_le (t : InfinitePlace K ⊕ ↥Sfin) :
    sPlace Sfin t (LinearMap.det (LinearMap.pi (L (sPlace Sfin t))))
      ≤ Real.exp (detLogBound K (Fintype.card ι) (formLogHeight Sfin L)) := by
  rw [← LinearMap.det_toMatrix']
  exact (sPlace_apply_le_exp_logHeight₁ t _).trans
    (Real.exp_le_exp.2 (logHeight₁_det_formMatrix_le t))

/-- **The determinant of independent forms at a place of `S`, from below.** -/
theorem exp_neg_le_sPlace_det (t : InfinitePlace K ⊕ ↥Sfin)
    (hL : LinearIndependent K (L (sPlace Sfin t))) :
    Real.exp (-detLogBound K (Fintype.card ι) (formLogHeight Sfin L))
      ≤ sPlace Sfin t (LinearMap.det (LinearMap.pi (L (sPlace Sfin t)))) := by
  have h0 := LinearMap.det_pi_ne_zero hL
  rw [← LinearMap.det_toMatrix'] at h0 ⊢
  exact (Real.exp_le_exp.2 (neg_le_neg (logHeight₁_det_formMatrix_le t))).trans
    (exp_neg_logHeight₁_le_sPlace_apply t h0)

omit [DecidableEq ι] in
/-- **The local size of the inverse of the forms at a place of `S`**:
`invFormBound ≤ N (1 + N ^ 2 exp (2 detLogBound))`. -/
theorem invFormBound_le [DecidableEq ι] (t : InfinitePlace K ⊕ ↥Sfin) :
    invFormBound (sPlace Sfin t) (L (sPlace Sfin t)) ≤ Fintype.card ι *
      (1 + Fintype.card ι ^ 2 *
        Real.exp (2 * detLogBound K (Fintype.card ι) (formLogHeight Sfin L))) := by
  obtain rfl : ‹DecidableEq ι› = fun a b ↦ Classical.propDecidable (a = b) :=
    Subsingleton.elim _ _
  classical
  rw [invFormBound]
  refine mul_le_mul_of_nonneg_left (add_le_add_right ?_ _) (Nat.cast_nonneg _)
  have hb : ∀ p : ι × ι, sPlace Sfin t
      ((LinearMap.toMatrix' (LinearMap.pi (L (sPlace Sfin t))))⁻¹ p.1 p.2)
        ≤ Real.exp (2 * detLogBound K (Fintype.card ι) (formLogHeight Sfin L)) := fun p ↦
    (sPlace_apply_le_exp_logHeight₁ t _).trans
      (Real.exp_le_exp.2 (logHeight₁_inv_formMatrix_le t p.1 p.2))
  refine (Finset.sum_le_sum fun p _ ↦ hb p).trans_eq ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul, sq, Nat.cast_mul]

/-- **The determinants of independent forms at the infinite places, from below.** -/
theorem exp_neg_pow_le_prod_det (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1)) :
    Real.exp (-detLogBound K (Fintype.card ι) (formLogHeight Sfin L)) ^ finrank ℚ K
      ≤ ∏ w : InfinitePlace K, w (LinearMap.det (LinearMap.pi (L w.1))) ^ w.mult := by
  rw [← InfinitePlace.sum_mult_eq, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun w _ ↦
    pow_le_pow_left₀ (Real.exp_pos _).le (exp_neg_le_sPlace_det (Sfin := Sfin) (.inl w) (hLInf w)) _

/-- **The determinants of the forms at the infinite places, from above.** -/
theorem prod_det_le_exp_pow :
    ∏ w : InfinitePlace K, w (LinearMap.det (LinearMap.pi (L w.1))) ^ w.mult
      ≤ Real.exp (detLogBound K (Fintype.card ι) (formLogHeight Sfin L)) ^ finrank ℚ K := by
  rw [← InfinitePlace.sum_mult_eq, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod₀ (fun w _ ↦ pow_nonneg (w.1.nonneg _) _) fun w _ ↦
    pow_le_pow_left₀ (w.1.nonneg _) (sPlace_det_le (Sfin := Sfin) (.inl w)) _

/-- **The determinants of independent forms at the finite places of `S`, from below.** -/
theorem exp_neg_pow_le_prod_det_finite (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) :
    Real.exp (-detLogBound K (Fintype.card ι) (formLogHeight Sfin L)) ^ #Sfin
      ≤ ∏ v ∈ Sfin, v (LinearMap.det (LinearMap.pi (L v.1))) := by
  rw [← Finset.prod_const]
  exact Finset.prod_le_prod₀ (fun _ _ ↦ (Real.exp_pos _).le) fun v hv ↦
    exp_neg_le_sPlace_det (.inr ⟨v, hv⟩) (hLFin v hv)

/-- **The determinants of the forms at the finite places of `S`, from above.** -/
theorem prod_det_finite_le_exp_pow :
    ∏ v ∈ Sfin, v (LinearMap.det (LinearMap.pi (L v.1)))
      ≤ Real.exp (detLogBound K (Fintype.card ι) (formLogHeight Sfin L)) ^ #Sfin := by
  rw [← Finset.prod_const]
  exact Finset.prod_le_prod₀ (fun v _ ↦ v.1.nonneg _) fun v hv ↦ sPlace_det_le (.inr ⟨v, hv⟩)

open scoped Classical in
omit [DecidableEq ι] in
/-- The covolume of `𝓞 K` is at least `2 ^ (-r₂)`. -/
theorem inv_two_pow_le_covolume :
    (2⁻¹ : ℝ) ^ nrComplexPlaces K ≤ ZLattice.covolume (mixedEmbedding.integerLattice K) := by
  rw [mixedEmbedding.covolume_integerLattice]
  refine le_mul_of_one_le_right (by positivity) (Real.one_le_sqrt.2 ?_)
  exact_mod_cast Int.one_le_abs (discr_ne_zero K)

open scoped Classical in
omit [DecidableEq ι] in
/-- The covolume of `𝓞 K` is at most `√|D_K|`. -/
theorem covolume_le_sqrt :
    ZLattice.covolume (mixedEmbedding.integerLattice K) ≤ √|(discr K : ℝ)| := by
  rw [mixedEmbedding.covolume_integerLattice]
  exact mul_le_of_le_one_left (Real.sqrt_nonneg _) (pow_le_one₀ (by norm_num) (by norm_num))

open scoped Classical in
/-- **The comparison constant from above**: `approxConst ≤ (2 π) ^ (d N) exp (D) ^ (d + |Sfin|)`
with `D = detLogBound`. -/
theorem approxConst_le (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) :
    approxConst Sfin L ≤ (2 * Real.pi) ^ (finrank ℚ K * Fintype.card ι) *
      Real.exp (detLogBound K (Fintype.card ι) (formLogHeight Sfin L)) ^ (finrank ℚ K + #Sfin) := by
  set E := Real.exp (detLogBound K (Fintype.card ι) (formLogHeight Sfin L)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have h1 := exp_neg_pow_le_prod_det (Sfin := Sfin) hLInf
  have h2 := exp_neg_pow_le_prod_det_finite hLFin
  rw [Real.exp_neg, ← hE] at h1 h2
  have hden : (2⁻¹ : ℝ) ^ (nrComplexPlaces K * Fintype.card ι) * (E⁻¹ ^ finrank ℚ K * E⁻¹ ^ #Sfin)
      ≤ ZLattice.covolume (mixedEmbedding.integerLattice K) ^ Fintype.card ι *
        (∏ w : InfinitePlace K, w (LinearMap.det (LinearMap.pi (L w.1))) ^ w.mult) *
          ∏ v ∈ Sfin, v (LinearMap.det (LinearMap.pi (L v.1))) := by
    rw [pow_mul, mul_assoc]
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) inv_two_pow_le_covolume _)
      (mul_le_mul h1 h2 (by positivity) ((pow_pos (inv_pos.2 hE0) _).le.trans h1))
      (by positivity) (pow_nonneg (ZLattice.covolume_pos _ _).le _)
  rw [approxConst]
  refine (div_le_div_of_nonneg_left (by positivity) (by positivity) hden).trans ?_
  have hr := card_add_two_mul_card_eq_rank K
  have hle : (nrRealPlaces K + nrComplexPlaces K) * Fintype.card ι
      ≤ finrank ℚ K * Fintype.card ι := Nat.mul_le_mul_right _ (by omega)
  have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  calc 2 ^ (nrRealPlaces K * Fintype.card ι) * Real.pi ^ (nrComplexPlaces K * Fintype.card ι) /
        ((2⁻¹ : ℝ) ^ (nrComplexPlaces K * Fintype.card ι) * (E⁻¹ ^ finrank ℚ K * E⁻¹ ^ #Sfin))
      = 2 ^ ((nrRealPlaces K + nrComplexPlaces K) * Fintype.card ι) *
          Real.pi ^ (nrComplexPlaces K * Fintype.card ι) * E ^ (finrank ℚ K + #Sfin) := by
        rw [inv_pow, inv_pow, inv_pow, pow_add, add_mul, pow_add]
        field_simp
    _ ≤ 2 ^ (finrank ℚ K * Fintype.card ι) * Real.pi ^ (finrank ℚ K * Fintype.card ι) *
          E ^ (finrank ℚ K + #Sfin) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul (pow_le_pow_right₀ one_le_two hle)
          (pow_le_pow_right₀ hpi (Nat.mul_le_mul_right _ (by omega))) (by positivity)
          (by positivity)) (by positivity)
    _ = _ := by rw [mul_pow]

open scoped Classical in
/-- **The comparison constant from below**: `approxConst ≥ (√|D_K| ^ N exp (D) ^ (d + |Sfin|))⁻¹`
with `D = detLogBound`. -/
theorem inv_le_approxConst (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) :
    (√|(discr K : ℝ)| ^ Fintype.card ι *
      Real.exp (detLogBound K (Fintype.card ι) (formLogHeight Sfin L)) ^ (finrank ℚ K + #Sfin))⁻¹
        ≤ approxConst Sfin L := by
  set E := Real.exp (detLogBound K (Fintype.card ι) (formLogHeight Sfin L)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hden : ZLattice.covolume (mixedEmbedding.integerLattice K) ^ Fintype.card ι *
        (∏ w : InfinitePlace K, w (LinearMap.det (LinearMap.pi (L w.1))) ^ w.mult) *
          ∏ v ∈ Sfin, v (LinearMap.det (LinearMap.pi (L v.1)))
      ≤ √|(discr K : ℝ)| ^ Fintype.card ι * E ^ (finrank ℚ K + #Sfin) := by
    rw [pow_add, ← mul_assoc]
    exact mul_le_mul (mul_le_mul (pow_le_pow_left₀ (ZLattice.covolume_pos _ _).le
      covolume_le_sqrt _) prod_det_le_exp_pow
        (Finset.prod_nonneg fun w _ ↦ pow_nonneg (w.1.nonneg _) _) (by positivity))
      prod_det_finite_le_exp_pow (Finset.prod_nonneg fun v _ ↦ v.1.nonneg _) (by positivity)
  have hden0 : 0 < ZLattice.covolume (mixedEmbedding.integerLattice K) ^ Fintype.card ι *
        (∏ w : InfinitePlace K, w (LinearMap.det (LinearMap.pi (L w.1))) ^ w.mult) *
          ∏ v ∈ Sfin, v (LinearMap.det (LinearMap.pi (L v.1))) :=
    mul_pos (mul_pos (pow_pos (ZLattice.covolume_pos _ _) _) (Finset.prod_pos fun w _ ↦
      pow_pos (w.pos_iff.2 (LinearMap.det_pi_ne_zero (hLInf w))) _))
      (Finset.prod_pos fun v hv ↦ FinitePlace.pos_iff.2 (LinearMap.det_pi_ne_zero (hLFin v hv)))
  rw [approxConst, inv_eq_one_div]
  refine (div_le_div_of_nonneg_left zero_le_one hden0 hden).trans
    (div_le_div_of_nonneg_right ?_ hden0.le)
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
    (one_le_pow₀ (by linarith [Real.pi_gt_three]))

/-- **The bound on the local size of the inverse of the forms**:
`N (1 + N ^ 2 exp (2 detLogBound K N h))`. -/
noncomputable def invSizeBound (K : Type*) [Field K] [NumberField K] (N : ℕ) (h : ℝ) : ℝ :=
  N * (1 + N ^ 2 * Real.exp (2 * detLogBound K N h))

theorem invSizeBound_nonneg (N : ℕ) (h : ℝ) : 0 ≤ invSizeBound K N h := by
  unfold invSizeBound
  positivity

omit [DecidableEq ι] [NumberField K] in
theorem invFormBound_nonneg (v : AbsoluteValue K ℝ) (l : ι → Dual K (ι → K)) :
    0 ≤ invFormBound v l :=
  mul_nonneg (Nat.cast_nonneg _)
    (add_nonneg zero_le_one (Finset.sum_nonneg fun _ _ ↦ v.nonneg _))

/-- **The constant of the height of a point of a dilated domain, bounded by heights**. -/
theorem pointHeightConst_le :
    pointHeightConst Sfin L ≤
      ((1 + Fintype.card (InfinitePlace K) * invSizeBound K (Fintype.card ι) (formLogHeight Sfin L))
        * (1 + #Sfin * invSizeBound K (Fintype.card ι) (formLogHeight Sfin L)))
          ^ (finrank ℚ K + #Sfin) := by
  set B := invSizeBound K (Fintype.card ι) (formLogHeight Sfin L)
  have hInf : ∑ w : InfinitePlace K, invFormBound w.1 (L w.1)
      ≤ Fintype.card (InfinitePlace K) * B := by
    refine (Finset.sum_le_sum fun w _ ↦
      invFormBound_le (L := L) (Sfin := Sfin) (.inl w)).trans_eq ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rfl
  have hFin : ∑ v : {v : FinitePlace K // v ∈ Sfin}, invFormBound v.1.1 (L v.1.1)
      ≤ #Sfin * B := by
    refine (Finset.sum_le_sum fun v _ ↦ invFormBound_le (L := L) (.inr v)).trans_eq ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    rfl
  have h0 : ∀ a : AbsoluteValue K ℝ, 0 ≤ invFormBound a (L a) := fun a ↦ invFormBound_nonneg _ _
  refine pow_le_pow_left₀ (mul_nonneg (add_nonneg zero_le_one (Finset.sum_nonneg fun _ _ ↦ h0 _))
    (add_nonneg zero_le_one (Finset.sum_nonneg fun _ _ ↦ h0 _))) ?_ _
  exact mul_le_mul (add_le_add_right hInf _) (add_le_add_right hFin _)
    (add_nonneg zero_le_one (Finset.sum_nonneg fun _ _ ↦ h0 _))
    (add_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) (invSizeBound_nonneg _ _)))

open scoped Classical in
/-- The inverse of the comparison constant, bounded by heights. -/
theorem inv_approxConst_le (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) :
    (approxConst Sfin L)⁻¹ ≤ √|(discr K : ℝ)| ^ Fintype.card ι *
      Real.exp (detLogBound K (Fintype.card ι) (formLogHeight Sfin L)) ^ (finrank ℚ K + #Sfin) :=
  inv_le_of_inv_le₀ (mul_pos (pow_pos (Real.sqrt_pos.2 (abs_pos.2
    (by exact_mod_cast discr_ne_zero K))) _) (pow_pos (Real.exp_pos _) _))
    (inv_le_approxConst hLInf hLFin)

open scoped Classical in
/-- **The level of the minima bounds, bounded by heights.** -/
theorem minimaThreshold_le (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) :
    minimaThreshold Sfin L ≤ max (max 1
      (((1 + Fintype.card (InfinitePlace K) *
          invSizeBound K (Fintype.card ι) (formLogHeight Sfin L))
        * (1 + #Sfin * invSizeBound K (Fintype.card ι) (formLogHeight Sfin L)))
          ^ (finrank ℚ K + #Sfin)))
      (max (2 ^ (finrank ℚ K * Fintype.card ι) *
        (∏ v ∈ Sfin, (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) ^ Fintype.card ι) *
          (√|(discr K : ℝ)| ^ Fintype.card ι *
            Real.exp (detLogBound K (Fintype.card ι) (formLogHeight Sfin L))
              ^ (finrank ℚ K + #Sfin))) 1) := by
  refine max_le_max (max_le_max le_rfl pointHeightConst_le) (max_le_max ?_ le_rfl)
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (inv_approxConst_le hLInf hLFin) (by positivity)

open scoped Classical in
/-- The numerator of the rank threshold, `(d N)! c_K ^ (d N) approxConst`, bounded by heights. -/
theorem factorial_mul_pow_mul_approxConst_le
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) :
    (finrank ℚ K * Fintype.card ι).factorial *
      integralBasisHouse K ^ (finrank ℚ K * Fintype.card ι) * approxConst Sfin L
    ≤ (finrank ℚ K * Fintype.card ι).factorial *
      reducedBasisBound K ^ (finrank ℚ K * Fintype.card ι) *
        ((2 * Real.pi) ^ (finrank ℚ K * Fintype.card ι) *
          Real.exp (detLogBound K (Fintype.card ι) (formLogHeight Sfin L))
            ^ (finrank ℚ K + #Sfin)) := by
  have hc := one_le_integralBasisHouse (K := K)
  have hR : 0 ≤ reducedBasisBound K := by unfold reducedBasisBound; positivity
  exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith)
    (integralBasisHouse_le K) _) (by positivity)) (approxConst_le hLInf hLFin)
    (approxConst_pos hLInf hLFin).le (mul_nonneg (by positivity) (pow_nonneg hR _))

open scoped Classical in
/-- **The rank threshold, bounded by heights.** -/
theorem rankThreshold_le (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) {η : ℝ} (hη : 0 < η) :
    rankThreshold Sfin L η ≤ 2 * max 1 (((finrank ℚ K * Fintype.card ι).factorial *
      reducedBasisBound K ^ (finrank ℚ K * Fintype.card ι) *
        ((2 * Real.pi) ^ (finrank ℚ K * Fintype.card ι) *
          Real.exp (detLogBound K (Fintype.card ι) (formLogHeight Sfin L))
            ^ (finrank ℚ K + #Sfin)) / 2 ^ (finrank ℚ K * Fintype.card ι)) ^ η⁻¹) := by
  have hc := one_le_integralBasisHouse (K := K)
  refine mul_le_mul_of_nonneg_left (max_le_max le_rfl ?_) zero_le_two
  refine Real.rpow_le_rpow (div_nonneg (mul_nonneg (mul_nonneg (by positivity)
    (pow_nonneg (by linarith) _)) (approxConst_pos hLInf hLFin).le) (by positivity)) ?_
    (inv_nonneg.2 hη.le)
  exact div_le_div_of_nonneg_right (factorial_mul_pow_mul_approxConst_le hLInf hLFin)
    (by positivity)

open scoped Classical in
/-- **The constant of the wedge weight, bounded by heights.** -/
theorem wedgeWeightConst_le (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) {C : ℝ} (hC : 0 ≤ C) (p : ℕ) :
    wedgeWeightConst Sfin L C p ≤
      max (max (C ^ (Fintype.card (Set.powersetCard ι p) * finrank ℚ K) *
        (2 ^ (finrank ℚ K * Fintype.card ι) *
          (∏ v ∈ Sfin, (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) ^ Fintype.card ι) *
            (√|(discr K : ℝ)| ^ Fintype.card ι *
              Real.exp (detLogBound K (Fintype.card ι) (formLogHeight Sfin L))
                ^ (finrank ℚ K + #Sfin))) ^ ((Fintype.card ι - 1).choose (p - 1))) 1 ^
        (Fintype.card ι ^ 2) *
      ((finrank ℚ K * Fintype.card ι).factorial *
        reducedBasisBound K ^ (finrank ℚ K * Fintype.card ι) *
          ((2 * Real.pi) ^ (finrank ℚ K * Fintype.card ι) *
            Real.exp (detLogBound K (Fintype.card ι) (formLogHeight Sfin L))
              ^ (finrank ℚ K + #Sfin)) / 2 ^ (finrank ℚ K * Fintype.card ι))) 1 := by
  have hc := one_le_integralBasisHouse (K := K)
  have hA := approxConst_pos hLInf hLFin
  have hX : 2 ^ (finrank ℚ K * Fintype.card ι) *
        (∏ v ∈ Sfin, (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) ^ Fintype.card ι) /
          approxConst Sfin L
      ≤ 2 ^ (finrank ℚ K * Fintype.card ι) *
        (∏ v ∈ Sfin, (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) ^ Fintype.card ι) *
          (√|(discr K : ℝ)| ^ Fintype.card ι *
            Real.exp (detLogBound K (Fintype.card ι) (formLogHeight Sfin L))
              ^ (finrank ℚ K + #Sfin)) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_approxConst_le hLInf hLFin) (by positivity)
  rw [wedgeWeightConst, inv_div]
  refine max_le_max (mul_le_mul ?_ ?_ ?_ ?_) le_rfl
  · exact pow_le_pow_left₀ (zero_le_one.trans (le_max_right _ _)) (max_le_max
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (div_nonneg (by positivity) hA.le) hX _)
        (pow_nonneg hC _)) le_rfl) _
  · exact div_le_div_of_nonneg_right (factorial_mul_pow_mul_approxConst_le hLInf hLFin)
      (by positivity)
  · exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (by linarith) _))
      hA.le) (by positivity)
  · exact pow_nonneg (zero_le_one.trans (le_max_right _ _)) _

/-- The sum of the logarithmic heights of the entries of the inverse matrices at `S`. -/
theorem sum_logHeight₁_inv_formMatrix_le :
    ∑ q : (InfinitePlace K ⊕ ↥Sfin) × ι × ι,
        logHeight₁ ((formMatrix L (sPlace Sfin q.1))⁻¹ q.2.1 q.2.2)
      ≤ (Fintype.card (InfinitePlace K) + #Sfin) * Fintype.card ι ^ 2 *
          (2 * detLogBound K (Fintype.card ι) (formLogHeight Sfin L)) := by
  refine (Finset.sum_le_sum fun q _ ↦ logHeight₁_inv_formMatrix_le q.1 q.2.1 q.2.2).trans_eq ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod, Fintype.card_prod,
    Fintype.card_sum, Fintype.card_coe]
  push_cast
  ring

/-- **The constant of the auxiliary polynomial, bounded by heights.** -/
theorem auxHeightConst_le :
    auxHeightConst Sfin L ≤ 2⁻¹ * Real.log |(discr K : ℝ)|
      + ((finrank ℚ K : ℝ) / 2 * Fintype.card ι + totalWeight K * Real.log (Fintype.card ι)
        + (Fintype.card (InfinitePlace K) + #Sfin) * Fintype.card ι ^ 2 *
          (2 * detLogBound K (Fintype.card ι) (formLogHeight Sfin L))) := by
  rw [auxHeightConst]
  gcongr
  exact (log_mulHeight_sum_elim_one_le _).trans sum_logHeight₁_inv_formMatrix_le

/-- **The heights of the reference family, bounded by heights**: the entries of the inverse
matrices, and the integers up to `B`. -/
theorem sum_log_mulHeight₁_refFamily_le (B : ℕ) :
    ∑ θ, Real.log (mulHeight₁ (refFamily L Sfin B θ))
      ≤ (Fintype.card (InfinitePlace K) + #Sfin) * Fintype.card ι ^ 2 *
          (2 * detLogBound K (Fintype.card ι) (formLogHeight Sfin L))
        + (2 * B + 1) * (totalWeight K * Real.log B) := by
  rw [Fintype.sum_sum_type]
  refine add_le_add sum_logHeight₁_inv_formMatrix_le ?_
  have hk : ∀ k : ↥(Finset.Icc (-(B : ℤ)) (B : ℤ)),
      Real.log (mulHeight₁ (refFamily L Sfin B (.inr k))) ≤ totalWeight K * Real.log B := by
    rintro ⟨k, hk⟩
    rw [Finset.mem_Icc] at hk
    refine (logHeight₁_intCast_le k).trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    rcases eq_or_ne k 0 with rfl | h0
    · simpa using Real.log_natCast_nonneg B
    · refine Real.log_le_log (abs_pos.2 (by exact_mod_cast h0)) ?_
      rw [abs_le]
      constructor <;> exact_mod_cast (by omega)
  refine (Finset.sum_le_sum fun k _ ↦ hk k).trans_eq ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_coe, Int.card_Icc]
  congr 1
  have : ((B : ℤ) + 1 - -(B : ℤ)).toNat = 2 * B + 1 := by omega
  rw [this]
  push_cast
  ring

/-- **The constant of the pattern vectors, bounded by heights.** -/
theorem patternConst_le :
    patternConst Sfin L ≤ Fintype.card ι * (1 + (Fintype.card (InfinitePlace K) + #Sfin) *
      invSizeBound K (Fintype.card ι) (formLogHeight Sfin L)) := by
  set B := invSizeBound K (Fintype.card ι) (formLogHeight Sfin L)
  have hInf : ∑ w : InfinitePlace K, invFormBound w.1 (L w.1)
      ≤ Fintype.card (InfinitePlace K) * B := by
    refine (Finset.sum_le_sum fun w _ ↦
      invFormBound_le (L := L) (Sfin := Sfin) (.inl w)).trans_eq ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rfl
  have hFin : ∑ v : {v : FinitePlace K // v ∈ Sfin}, invFormBound v.1.1 (L v.1.1)
      ≤ #Sfin * B := by
    refine (Finset.sum_le_sum fun v _ ↦ invFormBound_le (L := L) (.inr v)).trans_eq ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    rfl
  rw [patternConst]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  linarith

end Forms

section Wedge

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

omit [NumberField K] in
/-- **The matrix of the wedge forms consists of the `p`-minors** of the matrix of the forms. -/
theorem formMatrix_wedgeForms_apply (L : AbsoluteValue K ℝ → ι → Dual K (ι → K))
    (v : AbsoluteValue K ℝ) (p : ℕ) [DecidableEq (Set.powersetCard ι p)]
    (T U : Set.powersetCard ι p) :
    formMatrix (fun v ↦ exteriorPower.wedgeForms (L v) p) v T U =
      (Matrix.of fun a b ↦ formMatrix L v (Set.powersetCard.ofFinEmbEquiv.symm T a)
        (Set.powersetCard.ofFinEmbEquiv.symm U b)).det := by
  rw [formMatrix_apply, exteriorPower.wedgeForms_eq_sum, Finset.sum_eq_single U
    (fun b _ hb ↦ by rw [Pi.single_eq_of_ne hb, mul_zero]) (fun h ↦ (h (Finset.mem_univ _)).elim),
    Pi.single_eq_same, mul_one, exteriorPower.wedgeFormCoeff, exteriorPower.plucker_apply]
  simp [formMatrix_apply]

/-- **The height of the wedge forms**: the entries of their matrices are `p`-minors, so their
logarithmic height is at most `|S| binom(N, p) ^ 2 detLogBound K p h` for the height `h` of the
forms. -/
theorem formLogHeight_wedgeForms_le (Sfin : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) (p : ℕ)
    [DecidableEq (Set.powersetCard ι p)] :
    formLogHeight Sfin (fun v ↦ exteriorPower.wedgeForms (L v) p) ≤
      (Fintype.card (InfinitePlace K) + #Sfin) * Fintype.card (Set.powersetCard ι p) ^ 2 *
        detLogBound K p (formLogHeight Sfin L) := by
  rw [formLogHeight]
  have hb : ∀ t : (InfinitePlace K ⊕ ↥Sfin) × Set.powersetCard ι p × Set.powersetCard ι p,
      logHeight₁ (formMatrix (fun v ↦ exteriorPower.wedgeForms (L v) p) (sPlace Sfin t.1)
        t.2.1 t.2.2) ≤ detLogBound K p (formLogHeight Sfin L) := fun t ↦ by
    rw [formMatrix_wedgeForms_apply]
    have h := logHeight₁_det_le (Matrix.of fun a b ↦
      formMatrix L (sPlace Sfin t.1) (Set.powersetCard.ofFinEmbEquiv.symm t.2.1 a)
        (Set.powersetCard.ofFinEmbEquiv.symm t.2.2 b)) fun a b ↦ logHeight₁_formMatrix_le t.1 _ _
    rwa [Fintype.card_fin] at h
  refine (Finset.sum_le_sum fun t _ ↦ hb t).trans_eq ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod, Fintype.card_prod,
    Fintype.card_sum, Fintype.card_coe]
  push_cast
  ring

/-- The coefficients of the wedges of the forms are `n`-minors of their matrices. -/
theorem logHeight₁_wedgeFormCoeff_le {Sfin : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} (t : InfinitePlace K ⊕ ↥Sfin) (n : ℕ)
    (s u : Set.powersetCard ι n) :
    logHeight₁ (exteriorPower.wedgeFormCoeff (L (sPlace Sfin t)) n s u)
      ≤ detLogBound K n (formLogHeight Sfin L) := by
  have h := logHeight₁_det_le (Matrix.of fun a b ↦
    formMatrix L (sPlace Sfin t) (Set.powersetCard.ofFinEmbEquiv.symm s a)
      (Set.powersetCard.ofFinEmbEquiv.symm u b)) fun a b ↦ logHeight₁_formMatrix_le t _ _
  rw [Fintype.card_fin, ← detLogBound] at h
  rw [exteriorPower.wedgeFormCoeff, exteriorPower.plucker_apply]
  convert h using 4
  ext a b
  simp [formMatrix_apply]

/-- The height of the coefficient tuple of a wedge of the forms. -/
theorem mulHeight_wedgeFormCoeff_le {Sfin : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} (t : InfinitePlace K ⊕ ↥Sfin) (n : ℕ)
    (s : Set.powersetCard ι n) :
    mulHeight (exteriorPower.wedgeFormCoeff (L (sPlace Sfin t)) n s)
      ≤ Real.exp (detLogBound K n (formLogHeight Sfin L))
          ^ Fintype.card (Set.powersetCard ι n) := by
  set a := exteriorPower.wedgeFormCoeff (L (sPlace Sfin t)) n s
  have h1 : mulHeight a ≤ mulHeight (Sum.elim a fun _ : Unit ↦ (1 : K)) :=
    mulHeight_comp_le Sum.inl (Sum.elim a fun _ : Unit ↦ (1 : K))
  have h2 := log_mulHeight_sum_elim_one_le a
  rw [← Real.exp_nat_mul, mul_comm]
  refine h1.trans ?_
  rw [← Real.exp_log (mulHeight_pos _)]
  refine Real.exp_le_exp.2 (h2.trans ?_)
  refine (Finset.sum_le_sum fun u _ ↦ logHeight₁_wedgeFormCoeff_le t n s u).trans_eq ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

/-- **The factor of the lower bound for `normalKappa`**:
`min 1 (exp (-E) ^ d / (M ^ d exp (E) ^ M))`. -/
noncomputable def kappaFactor (K : Type*) [Field K] [NumberField K] (M : ℕ) (E : ℝ) : ℝ :=
  min 1 (Real.exp (-E) ^ totalWeight K / ((M : ℝ) ^ totalWeight K * Real.exp E ^ M))

theorem kappaFactor_nonneg (M : ℕ) (E : ℝ) : 0 ≤ kappaFactor K M E :=
  le_min zero_le_one (by positivity)

theorem kappaFactor_le_one (M : ℕ) (E : ℝ) : kappaFactor K M E ≤ 1 := min_le_left _ _

/-- One factor of `normalKappa`, bounded below. -/
theorem kappaFactor_le_min {Sfin : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} (t : InfinitePlace K ⊕ ↥Sfin)
    (hL : LinearIndependent K (L (sPlace Sfin t))) {n : ℕ} (s : Set.powersetCard ι n) {m : ℕ}
    (hm : m ≤ totalWeight K) :
    kappaFactor K (Fintype.card (Set.powersetCard ι n)) (detLogBound K n (formLogHeight Sfin L))
      ≤ min 1 ((⨆ u, sPlace Sfin t (exteriorPower.wedgeFormCoeff (L (sPlace Sfin t)) n s u)) ^ m
        / ((Fintype.card (Set.powersetCard ι n) : ℝ) ^ totalWeight K
          * mulHeight (exteriorPower.wedgeFormCoeff (L (sPlace Sfin t)) n s))) := by
  set a := exteriorPower.wedgeFormCoeff (L (sPlace Sfin t)) n s
  set E := detLogBound K n (formLogHeight Sfin L)
  have hM : 0 < Fintype.card (Set.powersetCard ι n) := Fintype.card_pos_iff.2 ⟨s⟩
  obtain ⟨u, hu⟩ := Function.ne_iff.mp (exteriorPower.wedgeCoeff_ne_zero hL s)
  have hlow : Real.exp (-E) ≤ ⨆ u, sPlace Sfin t (a u) :=
    ((Real.exp_le_exp.2 (neg_le_neg (logHeight₁_wedgeFormCoeff_le t n s u))).trans
      (exp_neg_logHeight₁_le_sPlace_apply t hu)).trans (Finite.le_ciSup_of_le u le_rfl)
  have he1 : Real.exp (-E) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2
    ((zero_le_logHeight₁ _).trans (logHeight₁_wedgeFormCoeff_le t n s u)))
  refine min_le_min le_rfl (div_le_div₀ (pow_nonneg ((Real.exp_pos _).le.trans hlow) _) ?_
    (mul_pos (pow_pos (by exact_mod_cast hM) _) (mulHeight_pos _)) ?_)
  · exact (pow_le_pow_of_le_one (Real.exp_pos _).le he1 hm).trans
      (pow_le_pow_left₀ (Real.exp_pos _).le hlow _)
  · exact mul_le_mul_of_nonneg_left (mulHeight_wedgeFormCoeff_le t n s) (by positivity)

open scoped Classical in
/-- **The constant `κ` of Lemma 7.5.21, bounded below by heights**:
`κ ≥ kappaFactor ^ (|S| M)` with `M = binom(N, n)` and `E = detLogBound K n h`. -/
theorem kappaFactor_pow_le_normalKappa {Sfin : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} (n : ℕ)
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) :
    kappaFactor K (Fintype.card (Set.powersetCard ι n)) (detLogBound K n (formLogHeight Sfin L))
        ^ ((Fintype.card (InfinitePlace K) + #Sfin) * Fintype.card (Set.powersetCard ι n))
      ≤ normalKappa n Sfin L := by
  set y := kappaFactor K (Fintype.card (Set.powersetCard ι n))
    (detLogBound K n (formLogHeight Sfin L))
  set M := Fintype.card (Set.powersetCard ι n)
  have hy0 : 0 ≤ y := kappaFactor_nonneg _ _
  have hy1 : y ≤ 1 := kappaFactor_le_one _ _
  have hmult : ∀ w : InfinitePlace K, w.mult ≤ totalWeight K := fun w ↦ by
    rw [totalWeight_eq_sum_mult]
    exact Finset.single_le_sum (f := fun w : InfinitePlace K ↦ w.mult)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ w)
  have hone : 1 ≤ totalWeight K := by
    rw [totalWeight_eq_finrank]
    exact finrank_pos
  have hInf : y ^ (Fintype.card (InfinitePlace K) * M) ≤
      ∏ p : InfinitePlace K × Set.powersetCard ι n,
        min 1 ((⨆ t, p.1 (exteriorPower.wedgeFormCoeff (L p.1.1) n p.2 t)) ^ p.1.mult
          / ((M : ℝ) ^ totalWeight K
            * mulHeight (exteriorPower.wedgeFormCoeff (L p.1.1) n p.2))) := by
    have h := Finset.prod_le_prod₀ (s := (Finset.univ : Finset (InfinitePlace K ×
      Set.powersetCard ι n))) (fun _ _ ↦ hy0) fun p _ ↦
        kappaFactor_le_min (Sfin := Sfin) (.inl p.1) (hLInf p.1) p.2 (hmult p.1)
    rwa [Finset.prod_const, Finset.card_univ, Fintype.card_prod] at h
  have hFin : y ^ (#Sfin * M) ≤
      ∏ p ∈ Sfin ×ˢ (Finset.univ : Finset (Set.powersetCard ι n)),
        min 1 ((⨆ t, p.1 (exteriorPower.wedgeFormCoeff (L p.1.1) n p.2 t))
          / ((M : ℝ) ^ totalWeight K
            * mulHeight (exteriorPower.wedgeFormCoeff (L p.1.1) n p.2))) := by
    have hc : #Sfin * M = #(Sfin ×ˢ (Finset.univ : Finset (Set.powersetCard ι n))) := by
      rw [Finset.card_product, Finset.card_univ]
    rw [hc, ← Finset.prod_const]
    refine Finset.prod_le_prod₀ (fun _ _ ↦ hy0) fun p hp ↦ ?_
    have h := kappaFactor_le_min (Sfin := Sfin) (L := L)
      (.inr ⟨p.1, (Finset.mem_product.1 hp).1⟩) (hLFin p.1 (Finset.mem_product.1 hp).1) p.2 hone
    rw [pow_one] at h
    exact h
  rw [normalKappa]
  refine le_min ((pow_le_pow_of_le_one hy0 hy1 ?_).trans hInf)
    ((pow_le_pow_of_le_one hy0 hy1 ?_).trans hFin)
  · exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  · exact Nat.mul_le_mul_right _ (Nat.le_add_left _ _)

end Wedge

section Pattern

open scoped Matrix

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

omit [NumberField K] in
/-- **The span of some of the forms, as a kernel**: `ζ` is a combination of the coefficient
vectors of the forms `l i`, `i ∈ T`, exactly when `ζ M⁻¹` vanishes outside `T`, for the matrix
`M` of the forms. -/
theorem mem_span_vec_iff {l : ι → Dual K (ι → K)} (hl : LinearIndependent K l) (T : Finset ι)
    (ζ : ι → K) :
    ζ ∈ Submodule.span K (Set.range fun i : {i : ι // i ∈ T} ↦ (l i.1).vec) ↔
      ∀ j ∉ T, (ζ ᵥ* (LinearMap.toMatrix' (LinearMap.pi l))⁻¹) j = 0 := by
  set M := LinearMap.toMatrix' (LinearMap.pi l)
  have hdet : IsUnit M.det := by
    rw [LinearMap.det_toMatrix']
    exact isUnit_iff_ne_zero.mpr (LinearMap.det_pi_ne_zero hl)
  have hrow : ∀ i, (l i).vec = M i := fun i ↦ by
    funext k
    simp [M, Module.Dual.vec, LinearMap.toMatrix'_apply]
  constructor
  · intro hζ
    obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hζ
    set β' : ι → K := fun i ↦ if h : i ∈ T then β ⟨i, h⟩ else 0 with hβ'
    have hζ' : ζ = β' ᵥ* M := by
      rw [← hβ, Matrix.vecMul_eq_sum, ← Finset.sum_subset (Finset.subset_univ T)
        (fun i _ hi ↦ by simp [β', hi]), ← Finset.sum_coe_sort T]
      exact Finset.sum_congr rfl fun i _ ↦ by simp [β', i.2, hrow]
    intro j hj
    rw [hζ', Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv M hdet, Matrix.vecMul_one]
    simp [β', hj]
  · intro h
    have hζ : ζ = (ζ ᵥ* M⁻¹) ᵥ* M := by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul M hdet, Matrix.vecMul_one]
    refine (Submodule.mem_span_range_iff_exists_fun K).mpr ⟨fun i ↦ (ζ ᵥ* M⁻¹) i.1, ?_⟩
    conv_rhs => rw [hζ, Matrix.vecMul_eq_sum]
    simp_rw [hrow]
    rw [Finset.sum_coe_sort T (fun i ↦ (ζ ᵥ* M⁻¹) i • M i)]
    exact Finset.sum_subset (Finset.subset_univ T) fun i _ hi ↦ by rw [h i hi, zero_smul]

variable (Sfin : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → ι → Dual K (ι → K))

/-- **The matrix whose kernel is a pattern space**: its row `(v, j)` is the `j`-th column of the
inverse of the matrix of the forms at `v` when `j` is not in the pattern at `v`, and zero
otherwise. -/
noncomputable def patternMatrix
    (p : (InfinitePlace K → Finset ι) × ({w : FinitePlace K // w ∈ Sfin} → Finset ι)) :
    Matrix ((InfinitePlace K ⊕ ↥Sfin) × ι) ι K :=
  Matrix.of fun q k ↦
    if q.2 ∈ Sum.elim p.1 p.2 q.1 then 0 else (formMatrix L (sPlace Sfin q.1))⁻¹ k q.2

variable {Sfin L}

theorem patternMatrix_mulVec_apply
    (p : (InfinitePlace K → Finset ι) × ({w : FinitePlace K // w ∈ Sfin} → Finset ι))
    (ζ : ι → K) (t : InfinitePlace K ⊕ ↥Sfin) (j : ι) :
    (patternMatrix Sfin L p *ᵥ ζ) (t, j) =
      if j ∈ Sum.elim p.1 p.2 t then 0 else (ζ ᵥ* (formMatrix L (sPlace Sfin t))⁻¹) j := by
  simp only [Matrix.mulVec, dotProduct, patternMatrix, Matrix.of_apply, Matrix.vecMul]
  split_ifs <;> simp [mul_comm]

/-- **A pattern space is the kernel of its matrix.** -/
theorem mem_patternSpace_iff
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1))
    (p : (InfinitePlace K → Finset ι) × ({w : FinitePlace K // w ∈ Sfin} → Finset ι))
    (ζ : ι → K) : ζ ∈ patternSpace Sfin L p ↔ patternMatrix Sfin L p *ᵥ ζ = 0 := by
  simp only [patternSpace, Submodule.mem_inf, Submodule.mem_iInf]
  constructor
  · rintro ⟨h1, h2⟩
    funext ⟨t, j⟩
    rw [patternMatrix_mulVec_apply, Pi.zero_apply]
    split_ifs with hj
    · rfl
    rcases t with w | v
    · exact (mem_span_vec_iff (hLInf w) (p.1 w) ζ).1 (h1 w) j hj
    · exact (mem_span_vec_iff (hLFin v.1 v.2) (p.2 v) ζ).1 (h2 v) j hj
  · intro h
    refine ⟨fun w ↦ (mem_span_vec_iff (hLInf w) _ ζ).2 fun j hj ↦ ?_,
      fun v ↦ (mem_span_vec_iff (hLFin v.1 v.2) _ ζ).2 fun j hj ↦ ?_⟩
    · have := congrFun h (.inl w, j)
      simpa [patternMatrix_mulVec_apply, hj, formMatrix, sPlace] using this
    · have := congrFun h (.inr v, j)
      simpa [patternMatrix_mulVec_apply, hj, formMatrix, sPlace] using this

/-- The entries of the matrix of a pattern have logarithmic height at most `2 detLogBound`. -/
theorem logHeight₁_patternMatrix_le
    (p : (InfinitePlace K → Finset ι) × ({w : FinitePlace K // w ∈ Sfin} → Finset ι))
    (q : (InfinitePlace K ⊕ ↥Sfin) × ι) (k : ι) :
    logHeight₁ (patternMatrix Sfin L p q k)
      ≤ 2 * detLogBound K (Fintype.card ι) (formLogHeight Sfin L) := by
  simp only [patternMatrix, Matrix.of_apply]
  split_ifs
  · rw [logHeight₁_zero]
    exact mul_nonneg zero_le_two
      (detLogBound_nonneg _ (formLogHeight_nonneg Sfin L))
  · exact logHeight₁_inv_formMatrix_le q.1 k q.2

variable (Sfin L) in
/-- **The logarithmic bound on the least height of a pattern vector**:
`log |D_K| / 2 + N (d log N / 2 + |S| N ^ 2 · 2 detLogBound)`. -/
noncomputable def patternLogBound : ℝ :=
  2⁻¹ * Real.log |(discr K : ℝ)| + Fintype.card ι *
    ((finrank ℚ K : ℝ) / 2 * Real.log (Fintype.card ι)
      + (Fintype.card (InfinitePlace K) + #Sfin) * Fintype.card ι ^ 2 *
        (2 * detLogBound K (Fintype.card ι) (formLogHeight Sfin L)))

theorem patternLogBound_nonneg : 0 ≤ patternLogBound Sfin L := by
  have hD : 0 ≤ detLogBound K (Fintype.card ι) (formLogHeight Sfin L) :=
    detLogBound_nonneg _ (formLogHeight_nonneg Sfin L)
  have hDK : 0 ≤ Real.log |(discr K : ℝ)| := Real.log_nonneg (by
    exact_mod_cast Int.one_le_abs (discr_ne_zero K))
  have hN : 0 ≤ Real.log (Fintype.card ι) := Real.log_natCast_nonneg _
  unfold patternLogBound
  positivity

/-- **The height of a pattern space**: its least nonzero vector has logarithmic height at most
`patternLogBound`, by Siegel's lemma over `K` on the kernel description. -/
theorem patternHeight_le [Nonempty ι]
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1))
    (p : (InfinitePlace K → Finset ι) × ({w : FinitePlace K // w ∈ Sfin} → Finset ι)) :
    patternHeight Sfin L p ≤ Real.exp (patternLogBound Sfin L) := by
  rw [patternLogBound]
  set D := detLogBound K (Fintype.card ι) (formLogHeight Sfin L)
  set N := Fintype.card ι
  set d := finrank ℚ K
  rcases eq_or_ne (patternSpace Sfin L p) ⊥ with hbot | hbot
  · have hempty : {ζ : ι → K | ζ ∈ patternSpace Sfin L p ∧ ζ ≠ 0} = ∅ := by
      ext ζ
      simp only [hbot, Submodule.mem_bot, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
        iff_false, not_and]
      exact fun h h' ↦ h' h
    rw [patternHeight, hempty, Set.image_empty, Real.sInf_empty]
    exact (Real.exp_pos _).le
  obtain ⟨ζ, hζ, hζ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  set e := Fintype.equivFin ((InfinitePlace K ⊕ ↥Sfin) × ι)
  set B : Matrix (Fin (Fintype.card ((InfinitePlace K ⊕ ↥Sfin) × ι))) ι K :=
    (patternMatrix Sfin L p).submatrix e.symm id with hB
  have hBker : ∀ x : ι → K, B *ᵥ x = 0 ↔ patternMatrix Sfin L p *ᵥ x = 0 := fun x ↦ by
    constructor
    · intro h
      funext q
      have := congrFun h (e q)
      simpa [hB, Matrix.mulVec, dotProduct] using this
    · intro h
      funext i
      have := congrFun h (e.symm i)
      simpa [hB, Matrix.mulVec, dotProduct] using this
  have hrank : B.rank < N := by
    have hpos : 0 < finrank K (LinearMap.ker B.mulVecLin) := by
      refine Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨ζ, ?_⟩, fun h ↦ hζ0 (congrArg Subtype.val h)⟩
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, hBker]
      exact (mem_patternSpace_iff hLInf hLFin p ζ).1 hζ
    rw [Matrix.finrank_ker_mulVecLin] at hpos
    omega
  obtain ⟨x, hx0, hxker, -, hxle⟩ := exists_ne_zero_mem_ker_absMulHeight_le B hrank
  have hxmem : x ∈ patternSpace Sfin L p :=
    (mem_patternSpace_iff hLInf hLFin p x).2 ((hBker x).1 hxker)
  have hle : patternHeight Sfin L p ≤ mulHeight x :=
    csInf_le ⟨0, by rintro _ ⟨y, -, rfl⟩; exact (mulHeight_pos y).le⟩ ⟨x, ⟨hxmem, hx0⟩, rfl⟩
  refine hle.trans ?_
  rw [← Real.exp_log (mulHeight_pos x)]
  refine Real.exp_le_exp.2 ?_
  -- the height of the matrix
  set R := Matrix.mulHeight B with hR
  have hHB : Real.log R ≤
      (Fintype.card (InfinitePlace K) + #Sfin) * N ^ 2 * (2 * D) := by
    have h1 : R ≤ mulHeight (Sum.elim (fun q : Fin (Fintype.card ((InfinitePlace K ⊕ ↥Sfin) × ι))
        × ι ↦ B q.1 q.2) fun _ : Unit ↦ (1 : K)) :=
      mulHeight_comp_le Sum.inl (Sum.elim (fun q : Fin (Fintype.card ((InfinitePlace K ⊕ ↥Sfin)
        × ι)) × ι ↦ B q.1 q.2) fun _ : Unit ↦ (1 : K))
    refine (Real.log_le_log (mulHeight_pos _) h1).trans
      ((log_mulHeight_sum_elim_one_le _).trans ?_)
    refine (Finset.sum_le_sum fun q _ ↦ logHeight₁_patternMatrix_le p (e.symm q.1) q.2).trans_eq ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_prod, Fintype.card_sum, Fintype.card_coe]
    push_cast
    ring
  have hR1 : 1 ≤ R := one_le_mulHeight _
  have hd : (0 : ℝ) < d := by exact_mod_cast finrank_pos
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Fintype.card_pos
  have hDK : (0 : ℝ) < |(discr K : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero K)
  -- Siegel's bound, in logarithms
  have hlogabs : Real.log (absMulHeight x) = (d : ℝ)⁻¹ * Real.log (mulHeight x) := by
    rw [absMulHeight_eq x, Real.log_rpow (mulHeight_pos x)]
  have hb : 0 < √(N : ℝ) * R ^ (d : ℝ)⁻¹ :=
    mul_pos (Real.sqrt_pos.2 (by linarith)) (Real.rpow_pos_of_pos (by linarith) _)
  have hlogb : Real.log (√(N : ℝ) * R ^ (d : ℝ)⁻¹)
      = Real.log N / 2 + (d : ℝ)⁻¹ * Real.log R := by
    rw [Real.log_mul (Real.sqrt_pos.2 (by linarith)).ne' (Real.rpow_pos_of_pos (by linarith) _).ne',
      Real.log_sqrt (by linarith), Real.log_rpow (by linarith)]
  have hlogb0 : 0 ≤ Real.log N / 2 + (d : ℝ)⁻¹ * Real.log R :=
    add_nonneg (div_nonneg (Real.log_nonneg hN) zero_le_two)
      (mul_nonneg (inv_nonneg.2 hd.le) (Real.log_nonneg hR1))
  have habs0 : 0 < absMulHeight x := by
    rw [absMulHeight_eq x]
    exact Real.rpow_pos_of_pos (mulHeight_pos x) _
  have hsieg := Real.log_le_log habs0 hxle
  rw [hlogabs, Real.log_mul (Real.rpow_pos_of_pos hDK _).ne' (Real.rpow_pos_of_pos hb _).ne',
    Real.log_rpow hDK, Real.log_rpow hb, hlogb] at hsieg
  -- the exponent `rank / (N - rank)` is at most `N`
  have hrk : (B.rank : ℝ) < N := by exact_mod_cast hrank
  have he : (B.rank : ℝ) / (N - B.rank) ≤ N := by
    have h1 : (1 : ℝ) ≤ N - B.rank := by
      have : B.rank + 1 ≤ N := hrank
      have : (B.rank : ℝ) + 1 ≤ N := by exact_mod_cast this
      linarith
    exact (div_le_self (Nat.cast_nonneg _) h1).trans hrk.le
  have he0 : 0 ≤ (B.rank : ℝ) / (N - B.rank) :=
    div_nonneg (Nat.cast_nonneg _) (by linarith)
  have hmain : Real.log (mulHeight x) ≤ 2⁻¹ * Real.log |(discr K : ℝ)|
      + d * (N * (Real.log N / 2 + (d : ℝ)⁻¹ * Real.log R)) := by
    have h2 := mul_le_mul_of_nonneg_left hsieg hd.le
    rw [← mul_assoc, mul_inv_cancel₀ hd.ne', one_mul] at h2
    refine h2.trans_eq' ?_ |>.trans ?_
    · rfl
    rw [mul_add, ← mul_assoc, mul_inv, ← mul_assoc, mul_comm (d : ℝ) 2⁻¹, mul_assoc 2⁻¹,
      mul_inv_cancel₀ hd.ne', mul_one]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right he hlogb0) hd.le)
  refine hmain.trans (add_le_add le_rfl ?_)
  have : (d : ℝ) * (N * (Real.log N / 2 + (d : ℝ)⁻¹ * Real.log R))
      = N * ((d : ℝ) / 2 * Real.log N + Real.log R) := by
    field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hHB) (by linarith)

open scoped Classical in
/-- **The bound on the heights of the pattern vectors, by heights**: at most the number of
patterns times `exp patternLogBound`. -/
theorem patternHeightBound_le [Nonempty ι]
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) :
    patternHeightBound Sfin L ≤ Fintype.card ((InfinitePlace K → Finset ι) ×
      ({w : FinitePlace K // w ∈ Sfin} → Finset ι)) * Real.exp (patternLogBound Sfin L) := by
  rw [patternHeightBound]
  refine (Finset.sum_le_sum fun p _ ↦ max_le (Real.one_le_exp patternLogBound_nonneg)
    (patternHeight_le hLInf hLFin p)).trans_eq ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Pattern

end NumberField
