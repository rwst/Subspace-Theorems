/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.MultiprojectiveHeight

-- Used only inside proofs.
import ForMathlib.Data.Nat.Choose.MultinomialSum
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.NumberTheory.Height.MvPolynomial

/-!
# Polynomial heights of natural combinations

The height bound of the product theorem (`MvPolynomial.productTheorem_height`) takes a bound
`h_m(∑_r a_r r) ≤ B(∑_r a_r)` for the polynomial heights of the natural combinations of a finite
family `R`. This file proves such a bound in terms of the height of the family of coefficients:
if the supports of the `r ∈ R` lie in a finite set `M` of monomials, then
`h_m(∑_r a_r r) ≤ h(R) + [K : ℚ] (log ∑_r a_r + log (∑_{m ∈ M} 1/C(δ, m))^{1/2})`,
with `h(R)` the (relative, logarithmic) height of the tuple of all coefficients `r_m`.

## Main statements

* `MvPolynomial.coeffTuple`: the tuple of coefficients of a family.
* `MvPolynomial.bombieriNorm_sum_nsmul_le`: the local bound at an archimedean place.
* `MvPolynomial.bombieriLogHeight_sum_nsmul_le`: the global bound.
* `MvPolynomial.logHeight_le_of_forall_eq_natCast_mul`: `h(x) ≤ h(y) + [K : ℚ] log N` when the
  entries of `x` are multiples `c y_j` with `c ∈ ℕ`, `c ≤ N`.
* `MvPolynomial.log_sqrt_sum_inv_blockMultinomial_le`: Rémond's Lemma 5.2,
  `log (∑_{μ ∈ M_δ} 1/C(δ, μ))^{1/2} ≤ |√n| = ∑_i √n_i`, from `Finset.sum_inv_multinomial_le`.
-/

@[expose] public section

open Finset Height Height.AdmissibleAbsValues

variable {σ ι K : Type*}

namespace MvPolynomial

variable [Fintype σ] [Fintype ι] [DecidableEq ι] [Field K]

/-- The tuple of coefficients `r_m` of a family `R`, indexed by `R × M`. -/
def coeffTuple (R : Finset (MvPolynomial σ K)) (M : Finset (σ →₀ ℕ)) : R × M → K :=
  fun p ↦ p.1.1.coeff p.2.1

omit [Fintype σ] [Fintype ι] [DecidableEq ι] in
/-- Every coefficient `r_m` of a member of `R` is bounded by the maximum over the nonzero entries
of the tuple of coefficients, when `M` contains the supports. -/
theorem apply_coeff_le_iSup (v : AbsoluteValue K ℝ) {R : Finset (MvPolynomial σ K)}
    {M : Finset (σ →₀ ℕ)} (hM : ∀ r ∈ R, r.support ⊆ M) {r : MvPolynomial σ K} (hr : r ∈ R)
    (m : σ →₀ ℕ) :
    v (r.coeff m) ≤ ⨆ i : (coeffTuple R M).support, v (coeffTuple R M i) := by
  by_cases hm : r.coeff m = 0
  · rw [hm, v.map_zero]
    exact Real.iSup_nonneg_of_nonnegHomClass ..
  · have hmM : m ∈ M := hM r hr (mem_support_iff.mpr hm)
    exact le_ciSup_of_le (Set.finite_range _).bddAbove ⟨(⟨r, hr⟩, ⟨m, hmM⟩), hm⟩ le_rfl

/-- **The local bound at an archimedean place.** If the supports of the `r ∈ R` lie in `M` and
all coefficients satisfy `|r_m|_v ≤ C`, then
`‖∑_r a_r r‖_{v,2} ≤ (∑_r a_r) (∑_{m ∈ M} 1/C(δ, m))^{1/2} C`. -/
theorem bombieriNorm_sum_nsmul_le (b : σ → ι) (v : AbsoluteValue K ℝ)
    {R : Finset (MvPolynomial σ K)} {M : Finset (σ →₀ ℕ)} (hM : ∀ r ∈ R, r.support ⊆ M)
    (a : MvPolynomial σ K → ℕ) {C : ℝ} (hC : ∀ r ∈ R, ∀ m, v (r.coeff m) ≤ C) (hC0 : 0 ≤ C) :
    bombieriNorm b v (∑ r ∈ R, a r • r) ≤
      (∑ r ∈ R, a r : ℝ) * √(∑ m ∈ M, 1 / (blockMultinomial b m : ℝ)) * C := by
  classical
  set A : ℝ := ∑ r ∈ R, (a r : ℝ)
  have hA : 0 ≤ A := sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
  -- Each coefficient of the combination is at most `A C`.
  have hcoeff : ∀ m, v ((∑ r ∈ R, a r • r).coeff m) ≤ A * C := by
    intro m
    rw [coeff_sum, sum_mul]
    refine (v.sum_le _ _).trans (sum_le_sum fun r hr ↦ ?_)
    rw [coeff_smul, nsmul_eq_mul, map_mul]
    exact mul_le_mul (v.apply_nat_le_self _) (hC r hr m) (v.nonneg _) (Nat.cast_nonneg _)
  have hsupp : (∑ r ∈ R, a r • r).support ⊆ M := by
    intro m hm
    obtain ⟨r, hr, hm'⟩ := Finset.mem_biUnion.mp (support_sum hm)
    refine hM r hr (mem_support_iff.mpr fun h ↦ mem_support_iff.mp hm' ?_)
    rw [coeff_smul, h, smul_zero]
  rw [bombieriNorm, show A * √(∑ m ∈ M, 1 / (blockMultinomial b m : ℝ)) * C =
    √(∑ m ∈ M, (A * C) ^ 2 / (blockMultinomial b m : ℝ)) by
      simp_rw [div_eq_mul_one_div ((A * C) ^ 2), ← mul_sum]
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg hA hC0)]
      ring]
  refine Real.sqrt_le_sqrt ((sum_le_sum_of_subset_of_nonneg hsupp fun _ _ _ ↦ ?_).trans
    (sum_le_sum fun m _ ↦ ?_))
  · positivity
  · gcongr
    exact hcoeff m

/-- **The polynomial height of a natural combination.** If the supports of the `r ∈ R` lie in
`M`, then for every nonzero `∑_r a_r r`,
`h_m(∑_r a_r r) ≤ h(R) + [K : ℚ] (log ∑_r a_r + log (∑_{m ∈ M} 1/C(δ, m))^{1/2})`, where `h(R)`
is the height of the tuple of coefficients. -/
theorem bombieriLogHeight_sum_nsmul_le [AdmissibleAbsValues K] (b : σ → ι)
    {R : Finset (MvPolynomial σ K)} {M : Finset (σ →₀ ℕ)} (hM : ∀ r ∈ R, r.support ⊆ M)
    (a : MvPolynomial σ K → ℕ) (hP : ∑ r ∈ R, a r • r ≠ 0) :
    bombieriLogHeight b (∑ r ∈ R, a r • r) ≤
      logHeight (coeffTuple R M) + totalWeight K *
        (Real.log (∑ r ∈ R, a r : ℝ) + Real.log √(∑ m ∈ M, 1 / (blockMultinomial b m : ℝ))) := by
  classical
  set P := ∑ r ∈ R, a r • r
  set x := coeffTuple R M
  set y : x.support → K := fun i ↦ x i
  set A : ℝ := ∑ r ∈ R, (a r : ℝ)
  set c : ℝ := ∑ m ∈ M, 1 / (blockMultinomial b m : ℝ)
  -- A nonzero coefficient of `P` comes from a nonzero coefficient `r_m` with `a_r ≠ 0`.
  obtain ⟨m, hm⟩ := ne_zero_iff.mp hP
  obtain ⟨r, hr, hrm⟩ : ∃ r ∈ R, (a r • r).coeff m ≠ 0 := by
    by_contra! h
    exact hm (by rw [coeff_sum]; exact sum_eq_zero h)
  have hrm' : r.coeff m ≠ 0 := fun h ↦ hrm (by rw [coeff_smul, h, smul_zero])
  have har : a r ≠ 0 := fun h ↦ hrm (by simp [h])
  have hmM : m ∈ M := hM r hr (mem_support_iff.mpr hrm')
  have hy : y ≠ 0 := fun h ↦ hrm' (congrFun h ⟨(⟨r, hr⟩, ⟨m, hmM⟩), hrm'⟩)
  have hA : 1 ≤ A := by
    have : (1 : ℝ) ≤ a r := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr har)
    exact this.trans (single_le_sum (fun _ _ ↦ Nat.cast_nonneg _) hr)
  have hc : 0 < c := sum_pos (fun m _ ↦ by have := blockMultinomial_pos b m; positivity)
    ⟨m, hmM⟩
  have hX : ∀ v : AbsoluteValue K ℝ, 0 ≤ ⨆ i, v (y i) := fun v ↦
    Real.iSup_nonneg_of_nonnegHomClass ..
  have hle : ∀ v : AbsoluteValue K ℝ, ∀ r' ∈ R, ∀ m', v (r'.coeff m') ≤ ⨆ i, v (y i) :=
    fun v r' hr' m' ↦ apply_coeff_le_iSup v hM hr' m'
  have : Nonempty x.support := ⟨⟨(⟨r, hr⟩, ⟨m, hmM⟩), hrm'⟩⟩
  have : Nonempty P.support := ⟨⟨m, mem_support_iff.mpr hm⟩⟩
  -- Finiteness of the supports of the nonarchimedean factors.
  have hFy : (fun v : nonarchAbsVal ↦ ⨆ i, v.val (y i)).HasFiniteMulSupport := by
    exact .iSup fun i ↦ hasFiniteMulSupport i.prop
  have hFP : (fun v : nonarchAbsVal ↦ ⨆ m : P.support, v.val (P.coeff m)).HasFiniteMulSupport := by
    exact .iSup fun m ↦ hasFiniteMulSupport (mem_support_iff.mp m.prop)
  -- The archimedean part.
  have harch : (archAbsVal.map fun v ↦ bombieriNorm b v P).prod ≤
      (A * √c) ^ totalWeight K * (archAbsVal.map fun v ↦ ⨆ i, v (y i)).prod := by
    rw [totalWeight, ← Multiset.prod_replicate, ← Multiset.map_const', ← Multiset.prod_map_mul]
    exact Multiset.prod_map_le_prod_map₀ _ _
      (fun v _ ↦ Real.sqrt_nonneg _) fun v _ ↦ bombieriNorm_sum_nsmul_le b v hM a (hle v) (hX v)
  -- The nonarchimedean part.
  have hnonarch : ∏ᶠ v : nonarchAbsVal, ⨆ m : P.support, v.val (P.coeff m) ≤
      ∏ᶠ v : nonarchAbsVal, ⨆ i, v.val (y i) := by
    refine finprod_le_finprod₀ hFP (fun _ ↦ Real.iSup_nonneg_of_nonnegHomClass ..) hFy
      fun v ↦ ciSup_le fun m ↦ ?_
    have hv : IsNonarchimedean v.val := isNonarchimedean _ v.prop
    change v.val (P.coeff m) ≤ _
    rw [coeff_sum]
    refine (hv.apply_sum_le).trans (Real.iSup_le (fun r' ↦ ?_) (hX v.val))
    rw [coeff_smul]
    exact (IsNonarchimedean.nsmul_le hv (by simp)).trans (hle v.val r'.1 r'.2 m)
  -- Positivity of the left-hand side.
  have hpos : 0 < (archAbsVal.map fun v ↦ bombieriNorm b v P).prod *
      ∏ᶠ v : nonarchAbsVal, ⨆ m : P.support, v.val (P.coeff m) := by
    have hm' : m ∈ P.support := mem_support_iff.mpr hm
    refine mul_pos (Multiset.prod_pos fun z hz ↦ ?_) ?_
    · obtain ⟨v, -, rfl⟩ := Multiset.mem_map.mp hz
      refine Real.sqrt_pos.mpr (sum_pos' (fun _ _ ↦ by positivity) ⟨m, hm', ?_⟩)
      have := blockMultinomial_pos b m
      have : 0 < v (P.coeff m) := v.pos hm
      positivity
    · rw [finprod_eq_prod _ hFP]
      exact prod_pos fun v _ ↦ lt_of_lt_of_le (v.val.pos hm)
        (le_ciSup (f := fun m' : P.support ↦ v.val (P.coeff m'))
          (Set.finite_range _).bddAbove ⟨m, hm'⟩)
  have hy' : logHeight x = logHeight y := logHeight_eq_logHeight_restrict_support x
  rw [bombieriLogHeight_of_ne_zero b hP, hy', logHeight_eq_log_mulHeight, mulHeight_eq hy]
  have hAc : 0 < A * √c := mul_pos (by linarith) (Real.sqrt_pos.mpr hc)
  have hmy : 0 < (archAbsVal.map fun v ↦ ⨆ i, v (y i)).prod *
      ∏ᶠ v : nonarchAbsVal, ⨆ i, v.val (y i) := by
    rw [← mulHeight_eq hy]
    exact mulHeight_pos y
  calc Real.log ((archAbsVal.map fun v ↦ bombieriNorm b v P).prod *
        ∏ᶠ v : nonarchAbsVal, ⨆ m : P.support, v.val (P.coeff m))
      ≤ Real.log ((A * √c) ^ totalWeight K * ((archAbsVal.map fun v ↦ ⨆ i, v (y i)).prod *
          ∏ᶠ v : nonarchAbsVal, ⨆ i, v.val (y i))) := by
        refine Real.log_le_log hpos ?_
        rw [← mul_assoc]
        exact mul_le_mul harch hnonarch
          (finprod_nonneg fun _ ↦ Real.iSup_nonneg_of_nonnegHomClass ..)
          (mul_nonneg (pow_nonneg hAc.le _) (Multiset.prod_map_nonneg fun v _ ↦ hX v))
    _ = _ := by
        rw [Real.log_mul (pow_pos hAc _).ne' hmy.ne', Real.log_pow,
          Real.log_mul (by linarith) (Real.sqrt_pos.mpr hc).ne']
        ring

section Tuple

variable {I J : Type*} [Finite I] [Finite J]

omit [Fintype σ] [Fintype ι] [DecidableEq ι] in
/-- **Heights of tuples of multiples.** If every nonzero entry of `x` is `c · y_j` for a natural
number `c ≤ N`, then `H(x) ≤ N^{[K : ℚ]} H(y)`. -/
theorem mulHeight_le_of_forall_eq_natCast_mul [AdmissibleAbsValues K] {x : I → K} {y : J → K}
    {N : ℕ} (hN : 1 ≤ N) (h : ∀ i, x i ≠ 0 → ∃ j, ∃ c : ℕ, c ≤ N ∧ x i = c * y j) :
    mulHeight x ≤ (N : ℝ) ^ totalWeight K * mulHeight y := by
  have hN' : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr hN
  rcases eq_or_ne x 0 with rfl | hx
  · rw [mulHeight_zero]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hN') (one_le_mulHeight y)
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
  rw [Pi.zero_apply] at hi₀
  obtain ⟨j₀, c₀, -, hc₀⟩ := h i₀ hi₀
  have hyj₀ : y j₀ ≠ 0 := fun h0 ↦ hi₀ (by rw [hc₀, h0, mul_zero])
  rw [mulHeight_eq_mulHeight_restrict_support x, mulHeight_eq_mulHeight_restrict_support y]
  set x' : x.support → K := fun i ↦ x i
  set y' : y.support → K := fun j ↦ y j
  have : Nonempty x.support := ⟨⟨i₀, hi₀⟩⟩
  have : Nonempty y.support := ⟨⟨j₀, hyj₀⟩⟩
  have hx' : x' ≠ 0 := fun h0 ↦ hi₀ (congrFun h0 ⟨i₀, hi₀⟩)
  have hy' : y' ≠ 0 := fun h0 ↦ hyj₀ (congrFun h0 ⟨j₀, hyj₀⟩)
  -- Each entry of `x'` is a bounded multiple of an entry of `y'`.
  have h' : ∀ i : x.support, ∃ j : y.support, ∃ c : ℕ, c ≤ N ∧ x' i = c * y' j := by
    intro i
    obtain ⟨j, c, hc, hxj⟩ := h i i.prop
    have hyj : y j ≠ 0 := fun h0 ↦ i.prop (by rw [hxj, h0, mul_zero])
    exact ⟨⟨j, hyj⟩, c, hc, hxj⟩
  have hY : ∀ v : AbsoluteValue K ℝ, 0 ≤ ⨆ j, v (y' j) := fun v ↦
    Real.iSup_nonneg_of_nonnegHomClass ..
  have hFx : (fun v : nonarchAbsVal ↦ ⨆ i, v.val (x' i)).HasFiniteMulSupport :=
    .iSup fun i ↦ hasFiniteMulSupport i.prop
  have hFy : (fun v : nonarchAbsVal ↦ ⨆ j, v.val (y' j)).HasFiniteMulSupport :=
    .iSup fun j ↦ hasFiniteMulSupport j.prop
  rw [mulHeight_eq hx', mulHeight_eq hy', ← mul_assoc]
  refine mul_le_mul ?_ ?_ (finprod_nonneg fun _ ↦ Real.iSup_nonneg_of_nonnegHomClass ..)
    (mul_nonneg (by positivity) (Multiset.prod_map_nonneg fun v _ ↦ hY v))
  · -- The archimedean part.
    rw [totalWeight, ← Multiset.prod_replicate, ← Multiset.map_const', ← Multiset.prod_map_mul]
    refine Multiset.prod_map_le_prod_map₀ _ _
      (fun v _ ↦ Real.iSup_nonneg_of_nonnegHomClass ..) fun v _ ↦ ciSup_le fun i ↦ ?_
    obtain ⟨j, c, hc, hxj⟩ := h' i
    rw [hxj, map_mul]
    exact mul_le_mul ((v.apply_nat_le_self c).trans (Nat.cast_le.mpr hc))
      (le_ciSup (f := fun j ↦ v (y' j)) (Set.finite_range _).bddAbove j) (v.nonneg _)
      (by positivity)
  · -- The nonarchimedean part.
    refine finprod_le_finprod₀ hFx (fun _ ↦ Real.iSup_nonneg_of_nonnegHomClass ..) hFy
      fun v ↦ ciSup_le fun i ↦ ?_
    have hv : IsNonarchimedean v.val := isNonarchimedean _ v.prop
    obtain ⟨j, c, -, hxj⟩ := h' i
    change v.val (x' i) ≤ _
    rw [hxj, map_mul]
    refine (mul_le_of_le_one_left (v.val.nonneg _)
      (IsNonarchimedean.apply_natCast_le_one (by simp) (by simp) hv)).trans ?_
    exact le_ciSup (f := fun j ↦ v.val (y' j)) (Set.finite_range _).bddAbove j

omit [Fintype σ] [Fintype ι] [DecidableEq ι] in
/-- **Heights of tuples of multiples.** If every nonzero entry of `x` is `c · y_j` for a natural
number `c ≤ N`, then `h(x) ≤ h(y) + [K : ℚ] log N`. -/
theorem logHeight_le_of_forall_eq_natCast_mul [AdmissibleAbsValues K] {x : I → K} {y : J → K}
    {N : ℕ} (hN : 1 ≤ N) (h : ∀ i, x i ≠ 0 → ∃ j, ∃ c : ℕ, c ≤ N ∧ x i = c * y j) :
    logHeight x ≤ logHeight y + totalWeight K * Real.log N := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight, ← Real.log_pow, add_comm,
    ← Real.log_mul (pow_pos hN' _).ne' (mulHeight_pos y).ne']
  exact Real.log_le_log (mulHeight_pos x) (mulHeight_le_of_forall_eq_natCast_mul hN h)

end Tuple

section BlockMultinomial

/-- **Rémond's Lemma 5.2, block form.** With `n_i + 1` variables in block `i`, the inverses of the
multinomial coefficients `C(δ, μ)` of the monomials of multidegree `δ` sum to at most
`e^{2 |√n|}`, where `|√n| = ∑_i √n_i`. -/
theorem sum_inv_blockMultinomial_le (b : σ → ι) (δ : ι → ℕ) :
    ∑ μ ∈ blockMonomials b δ, 1 / (blockMultinomial b μ : ℝ) ≤
      Real.exp (2 * ∑ i, √((#({s | b s = i} : Finset σ) : ℝ) - 1)) := by
  classical
  rw [sum_blockMonomials, mul_sum, Real.exp_sum]
  have hblock : ∀ f ∈ Fintype.piFinset fun i ↦ ({s | b s = i} : Finset σ).finsuppAntidiag (δ i),
      1 / (blockMultinomial b (∑ i, f i) : ℝ) =
        ∏ i, ((Nat.multinomial {s | b s = i} (f i) : ℕ) : ℝ)⁻¹ := by
    intro f hf
    rw [Fintype.mem_piFinset] at hf
    have hsupp : ∀ j, (f j).support ⊆ ({s | b s = j} : Finset σ) :=
      fun j ↦ (mem_finsuppAntidiag.mp (hf j)).2
    rw [blockMultinomial, Nat.cast_prod, one_div, ← prod_inv_distrib]
    refine prod_congr rfl fun i _ ↦ ?_
    rw [Nat.multinomial_congr fun s hs ↦ ?_]
    rw [sum_apply_of_support_subset b hsupp s]
    simp only [mem_filter, mem_univ, true_and] at hs
    rw [hs]
  rw [sum_congr rfl hblock]
  refine (prod_univ_sum (t := fun i ↦ ({s | b s = i} : Finset σ).finsuppAntidiag (δ i))
    (f := fun i m ↦ ((Nat.multinomial {s | b s = i} m : ℕ) : ℝ)⁻¹)).symm.trans_le ?_
  refine Finset.prod_le_prod₀ (fun i _ ↦ ?_) (fun i _ ↦ sum_inv_multinomial_le _ _)
  exact sum_nonneg fun _ _ ↦ by positivity

/-- **Rémond's Lemma 5.2, logarithmic form.**
`log (∑_{μ ∈ M_δ} 1/C(δ, μ))^{1/2} ≤ |√n| = ∑_i √n_i`. -/
theorem log_sqrt_sum_inv_blockMultinomial_le (b : σ → ι) (δ : ι → ℕ) :
    Real.log √(∑ μ ∈ blockMonomials b δ, 1 / (blockMultinomial b μ : ℝ)) ≤
      ∑ i, √((#({s | b s = i} : Finset σ) : ℝ) - 1) := by
  set X := ∑ μ ∈ blockMonomials b δ, 1 / (blockMultinomial b μ : ℝ)
  have hX : 0 ≤ X := sum_nonneg fun _ _ ↦ by positivity
  have hs : 0 ≤ ∑ i, √((#({s | b s = i} : Finset σ) : ℝ) - 1) :=
    sum_nonneg fun _ _ ↦ Real.sqrt_nonneg _
  rcases hX.eq_or_lt with h0 | hpos
  · rw [← h0, Real.sqrt_zero, Real.log_zero]
    exact hs
  rw [Real.log_sqrt hX, div_le_iff₀ two_pos, Real.log_le_iff_le_exp hpos, mul_comm]
  exact sum_inv_blockMultinomial_le b δ

end BlockMultinomial

end MvPolynomial
