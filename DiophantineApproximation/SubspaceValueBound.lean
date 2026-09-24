/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.MvHasseDerivHeight
public import DiophantineApproximation.MvPolynomialEvalBound
public import DiophantineApproximation.SmallPoint
public import DiophantineApproximation.SubspaceAuxiliary

/-!
# The value of the auxiliary polynomial at the small point

Step VI of Bombieri–Gubler's proof of Theorem 7.5.13 bounds, at every place of `K`, the value at
the small point `X` of the derivative `T` produced by Layer 5.5, and multiplies the bounds by the
product formula. This file is the local half: the bound at one absolute value.

At a place of `S` the bound is read in the coordinates of the forms. Writing `A` for the matrix
of the forms at that place and `M` for its inverse, the value is

```text
T(X) = ∑ J, (blockSubst M T).coeff J * ∏ (h, j), L_j (x h) ^ J (h, j),
```

and each factor `L_j (x h)` is bounded by the inequalities defining the approximation domain,
`|L_j (x h)|_v ≤ Z * Q h ^ c j`. What makes the product small is the vanishing pattern of Layer
5.2: a surviving `J` has `∑ h, J (h, j) / d h` within `Δ` of a common value `mean` for every `j`.
With `d h * log (Q h)` pinned to `D` up to `log (Q h)`, the exponent of the product is

```text
D * (mean * ∑ j, c j + Δ * ∑ j, |c j|) + (∑ h, log (Q h)) * ∑ j, |c j|,
```

and summing that over the places of `S` with their weights turns `∑ j, c j` into the weight of
the system of exponents, which is negative. That is the whole of the book's chain of estimates in
7.5.26, and everything else in it is a constant times `∑ h, d h`.

## Main results

* `MvPolynomial.apply_eval_le_of_forall_support`: the value of a polynomial at a point, with a
  bound valid on the support, and its nonarchimedean companion.
* `MvPolynomial.eval_blockSubst` and `MvPolynomial.eval_eq_eval_blockSubst`: evaluating a
  substituted polynomial is evaluating it at the transformed point — the expansion of a value in
  the coordinates of the forms.
* `MvPolynomial.abs_sum_mul_sub_le`: `∑ h, J h * q h` is `D` times `∑ h, J h / d h` up to
  `∑ h, q h`, in both directions, which is what lets an exponent of either sign be estimated.
* `MvPolynomial.prod_pow_apply_le`: **the monomial of the expansion**, bounded by
  `Z ^ (∑ h, d h)` times the exponential of the displayed expression.
* `MvPolynomial.apply_eval_le_expansion` and
  `MvPolynomial.apply_eval_le_expansion_of_isNonarchimedean`: **the value at the small point at a
  place of `S`**, archimedean and nonarchimedean.
* `MvPolynomial.apply_eval_hasseDeriv_le_place`,
  `MvPolynomial.apply_eval_hasseDeriv_le_place_of_isNonarchimedean` and
  `MvPolynomial.apply_eval_hasseDeriv_le_of_isNonarchimedean`: the same for the Hasse derivative
  of a multihomogeneous polynomial, read against the local factor of the polynomial itself, at a
  place of `S` and at a place outside it.

## Implementation notes

⚠ **The pattern is used as a two-sided bound on one number per coordinate.** Layer 5.2 states
its conclusion as "the coefficient vanishes unless every `∑ h, J (h, i) / d h` lies in an
interval around `m / (n + 1)`". Only the width of that interval enters here, through
`|ρ j - mean| ≤ Δ`; which of the two ends is the wider one is the caller's business.

⚠ **The multidegree is what bounds `∑ p, J p`.** The grid constant `Z` is raised to the total
degree of the surviving monomial, and that is at most `∑ h, d h` because the polynomial is
multihomogeneous — not because each exponent is at most `d h`, which would give a factor
`card ι` too many.

⚠ **`D` is never assumed to be an integer, and `d h` is never assumed to be `⌈D / q h⌉`.** The
two inequalities `D ≤ d h * q h ≤ D + q h` are all that the estimate uses, and they are what the
caller has to arrange.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
7.5.26.

This is part of Layer 5.6 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Finset

noncomputable section

namespace MvPolynomial


section Support

variable {σ K : Type*} [Fintype σ] [Field K]

/-- **The value at a point, with a bound valid on the support.** -/
theorem apply_eval_le_of_forall_support (v : AbsoluteValue K ℝ) {P : MvPolynomial σ K}
    (x : σ → K) {G N : ℝ} (hG : 0 ≤ G)
    (hsupp : ∀ ν ∈ P.support, ∏ j, v (x j) ^ ν j ≤ G) (hN : (#P.support : ℝ) ≤ N) :
    v (eval x P) ≤ N * (⨆ ν, v (P.coeff ν)) * G := by
  have hiSup : ∀ ν : σ →₀ ℕ, v (P.coeff ν) ≤ ⨆ μ, v (P.coeff μ) :=
    fun ν ↦ le_ciSup (Finsupp.bddAbove_range_apply P.coeff v) ν
  have hnn : (0 : ℝ) ≤ (⨆ ν, v (P.coeff ν)) * G :=
    mul_nonneg (Real.iSup_nonneg fun _ ↦ v.nonneg _) hG
  rw [eval_eq', mul_assoc]
  calc v (∑ ν ∈ P.support, P.coeff ν * ∏ j, x j ^ ν j)
      ≤ ∑ ν ∈ P.support, v (P.coeff ν * ∏ j, x j ^ ν j) := v.sum_le _ _
    _ ≤ ∑ _ν ∈ P.support, (⨆ μ, v (P.coeff μ)) * G := by
        refine Finset.sum_le_sum fun ν hν ↦ ?_
        rw [map_mul, map_prod]
        simp only [map_pow]
        exact mul_le_mul (hiSup ν) (hsupp ν hν)
          (Finset.prod_nonneg fun j _ ↦ by positivity)
          (Real.iSup_nonneg fun _ ↦ v.nonneg _)
    _ = (#P.support : ℝ) * ((⨆ μ, v (P.coeff μ)) * G) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ N * ((⨆ μ, v (P.coeff μ)) * G) := mul_le_mul_of_nonneg_right hN hnn

/-- **The same at a nonarchimedean absolute value**, with no cardinality factor. -/
theorem apply_eval_le_of_forall_support_of_isNonarchimedean {v : AbsoluteValue K ℝ}
    (hv : IsNonarchimedean v) {P : MvPolynomial σ K} (x : σ → K) {G : ℝ} (hG : 0 ≤ G)
    (hsupp : ∀ ν ∈ P.support, ∏ j, v (x j) ^ ν j ≤ G) :
    v (eval x P) ≤ (⨆ ν, v (P.coeff ν)) * G := by
  have hiSup : ∀ ν : σ →₀ ℕ, v (P.coeff ν) ≤ ⨆ μ, v (P.coeff μ) :=
    fun ν ↦ le_ciSup (Finsupp.bddAbove_range_apply P.coeff v) ν
  have hnn : (0 : ℝ) ≤ (⨆ ν, v (P.coeff ν)) * G :=
    mul_nonneg (Real.iSup_nonneg fun _ ↦ v.nonneg _) hG
  rcases eq_or_ne P 0 with rfl | hP0
  · rw [map_zero, AbsoluteValue.map_zero]
    exact hnn
  rw [eval_eq']
  obtain ⟨ν, hν, hle⟩ :=
    hv.finset_image_add_of_nonempty (fun ν ↦ P.coeff ν * ∏ j, x j ^ ν j)
      (support_nonempty.mpr hP0)
  refine le_trans hle ?_
  rw [map_mul, map_prod]
  simp only [map_pow]
  exact mul_le_mul (hiSup ν) (hsupp ν hν) (Finset.prod_nonneg fun j _ ↦ by positivity)
    (Real.iSup_nonneg fun _ ↦ v.nonneg _)

end Support

section Eval

variable {κ ι R : Type*} [CommRing R] [Fintype ι]

/-- **Evaluating a block-substituted polynomial is evaluating it at the transformed point.** -/
theorem eval_blockSubst (A : Matrix ι ι R) (x : κ × ι → R) (P : MvPolynomial (κ × ι) R) :
    eval x (blockSubst A P) = eval (fun p : κ × ι ↦ ∑ i, A p.2 i * x (p.1, i)) P := by
  have h : ((aeval x : MvPolynomial (κ × ι) R →ₐ[R] R).comp (blockSubst A))
      = aeval (fun p : κ × ι ↦ ∑ i, A p.2 i * x (p.1, i)) := by
    refine MvPolynomial.algHom_ext fun p ↦ ?_
    obtain ⟨h, j⟩ := p
    rw [AlgHom.comp_apply, blockSubst_X, map_sum, aeval_X]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [map_mul, aeval_C, aeval_X]; simp
  have h2 := congrArg (fun f ↦ f P) h
  simpa [aeval_eq_eval] using h2

variable [DecidableEq ι]

/-- **The expansion of a value in the coordinates of the forms.** -/
theorem eval_eq_eval_blockSubst {A M : Matrix ι ι R} (hMA : M * A = 1) (x : κ × ι → R)
    (P : MvPolynomial (κ × ι) R) :
    eval x P = eval (fun p : κ × ι ↦ ∑ i, A p.2 i * x (p.1, i)) (blockSubst M P) := by
  conv_lhs => rw [← blockSubst_blockSubst hMA P]
  rw [eval_blockSubst]

end Eval



section Pattern

variable {K κ ι : Type*} [Field K] [Fintype κ] [Fintype ι]

/-- One coordinate of the exponent: the weighted sum `∑ h, J (h, j) * q h` is `D` times the
ratio `∑ h, J (h, j) / d h`, up to `∑ h, q h`. -/
theorem abs_sum_mul_sub_le {q : κ → ℝ} (hq : ∀ h, 0 < q h) {d : κ → ℕ} (hd : ∀ h, 0 < d h)
    {D : ℝ} (hdq : ∀ h, D ≤ (d h : ℝ) * q h)
    (hdq' : ∀ h, ((d h : ℝ)) * q h ≤ D + q h) {J : κ → ℕ} (hJ : ∀ h, J h ≤ d h) (a : ℝ) :
    a * ∑ h, (J h : ℝ) * q h
      ≤ a * (D * ∑ h, (J h : ℝ) / (d h : ℝ)) + |a| * ∑ h, q h := by
  have hdpos : ∀ h, (0 : ℝ) < (d h : ℝ) := fun h ↦ by exact_mod_cast hd h
  have hratio0 : ∀ h, (0 : ℝ) ≤ (J h : ℝ) / (d h : ℝ) := fun h ↦
    div_nonneg (Nat.cast_nonneg _) (hdpos h).le
  have hratio1 : ∀ h, (J h : ℝ) / (d h : ℝ) ≤ 1 := fun h ↦
    (div_le_one (hdpos h)).mpr (by exact_mod_cast hJ h)
  have hsplit : ∀ h, ((J h : ℝ) / (d h : ℝ)) * ((d h : ℝ) * q h) = (J h : ℝ) * q h := fun h ↦ by
    have hr : ((J h : ℝ) / (d h : ℝ)) * ((d h : ℝ) * q h)
        = (J h : ℝ) * q h * ((d h : ℝ) / (d h : ℝ)) := by ring
    rw [hr, div_self (hdpos h).ne', mul_one]
  have hlow : D * ∑ h, (J h : ℝ) / (d h : ℝ) ≤ ∑ h, (J h : ℝ) * q h := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun h _ ↦ ?_
    rw [← hsplit h, mul_comm D]
    exact mul_le_mul_of_nonneg_left (hdq h) (hratio0 h)
  have hhigh : ∑ h, (J h : ℝ) * q h ≤ D * ∑ h, (J h : ℝ) / (d h : ℝ) + ∑ h, q h := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun h _ ↦ ?_
    rw [← hsplit h]
    calc ((J h : ℝ) / (d h : ℝ)) * ((d h : ℝ) * q h)
        ≤ ((J h : ℝ) / (d h : ℝ)) * (D + q h) :=
          mul_le_mul_of_nonneg_left (hdq' h) (hratio0 h)
      _ = D * ((J h : ℝ) / (d h : ℝ)) + ((J h : ℝ) / (d h : ℝ)) * q h := by ring
      _ ≤ D * ((J h : ℝ) / (d h : ℝ)) + q h := by
          nlinarith [mul_le_mul_of_nonneg_right (hratio1 h) (hq h).le]
  have hqsum : (0 : ℝ) ≤ ∑ h, q h := Finset.sum_nonneg fun h _ ↦ (hq h).le
  rcases le_or_gt 0 a with ha | ha
  · rw [abs_of_nonneg ha]
    nlinarith [mul_le_mul_of_nonneg_left hhigh ha]
  · rw [abs_of_neg ha]
    nlinarith [mul_le_mul_of_nonpos_left hlow ha.le]


/-- **The monomial of the expansion at a point of the domains.** -/
theorem prod_pow_apply_le (v : AbsoluteValue K ℝ) {Z : ℝ} (hZ : 1 ≤ Z)
    {c : ι → ℝ} {q : κ → ℝ} (hq : ∀ h, 0 < q h) {d : κ → ℕ} (hd : ∀ h, 0 < d h)
    {D : ℝ} (hD : 0 ≤ D) (hdq : ∀ h, D ≤ (d h : ℝ) * q h)
    (hdq' : ∀ h, ((d h : ℝ)) * q h ≤ D + q h)
    {w : κ × ι → K} (hw : ∀ p : κ × ι, v (w p) ≤ Z * Real.exp (c p.2 * q p.1))
    {J : κ × ι →₀ ℕ} (hJ : ∀ h, ∑ j, J (h, j) ≤ d h)
    {Δ mean : ℝ} (hJc : ∀ j, |(∑ h, (J (h, j) : ℝ) / (d h : ℝ)) - mean| ≤ Δ) :
    ∏ p, v (w p) ^ J p
      ≤ Z ^ (∑ h, d h) * Real.exp (D * (mean * ∑ j, c j + Δ * ∑ j, |c j|)
          + (∑ h, q h) * ∑ j, |c j|) := by
  have hZ0 : (0 : ℝ) < Z := lt_of_lt_of_le zero_lt_one hZ
  have h1 : ∏ p, v (w p) ^ J p ≤ ∏ p : κ × ι, (Z * Real.exp (c p.2 * q p.1)) ^ J p :=
    Finset.prod_le_prod₀ (fun p _ ↦ pow_nonneg (v.nonneg _) _)
      (fun p _ ↦ pow_le_pow_left₀ (v.nonneg _) (hw p) _)
  have h2 : ∏ p : κ × ι, (Z * Real.exp (c p.2 * q p.1)) ^ J p
      = Z ^ (∑ p : κ × ι, J p) * Real.exp (∑ p : κ × ι, c p.2 * q p.1 * (J p : ℝ)) := by
    rw [Finset.prod_congr rfl (fun p (_ : p ∈ (univ : Finset (κ × ι))) ↦ mul_pow Z _ (J p)),
      Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Real.exp_sum]
    refine congrArg (fun r ↦ Z ^ (∑ p : κ × ι, J p) * r) (Finset.prod_congr rfl fun p _ ↦ ?_)
    rw [← Real.exp_nat_mul]
    ring_nf
  have h3 : ∑ p : κ × ι, (J p) ≤ ∑ h, d h := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_le_sum fun h _ ↦ hJ h
  have h5 : ∑ p : κ × ι, c p.2 * q p.1 * (J p : ℝ)
      = ∑ j, c j * ∑ h, (J (h, j) : ℝ) * q h := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ ↦ by ring
  have hterm : ∀ j, c j * ∑ h, (J (h, j) : ℝ) * q h
      ≤ c j * (D * ∑ h, (J (h, j) : ℝ) / (d h : ℝ)) + |c j| * ∑ h, q h := fun j ↦
    abs_sum_mul_sub_le hq hd hdq hdq' (J := fun h ↦ J (h, j))
      (fun h ↦ le_trans (Finset.single_le_sum (f := fun j' ↦ J (h, j'))
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)) (hJ h)) (c j)
  have hmean : ∀ j, c j * (∑ h, (J (h, j) : ℝ) / (d h : ℝ)) ≤ c j * mean + |c j| * Δ := by
    intro j
    have hd1 : c j * ((∑ h, (J (h, j) : ℝ) / (d h : ℝ)) - mean) ≤ |c j| * Δ := by
      calc c j * ((∑ h, (J (h, j) : ℝ) / (d h : ℝ)) - mean)
          ≤ |c j * ((∑ h, (J (h, j) : ℝ) / (d h : ℝ)) - mean)| := le_abs_self _
        _ = |c j| * |(∑ h, (J (h, j) : ℝ) / (d h : ℝ)) - mean| := abs_mul _ _
        _ ≤ |c j| * Δ := mul_le_mul_of_nonneg_left (hJc j) (abs_nonneg _)
    nlinarith [hd1]
  have h6 : ∑ j, c j * ∑ h, (J (h, j) : ℝ) * q h
      ≤ D * (mean * ∑ j, c j + Δ * ∑ j, |c j|) + (∑ h, q h) * ∑ j, |c j| := by
    calc ∑ j, c j * ∑ h, (J (h, j) : ℝ) * q h
        ≤ ∑ j, (c j * (D * ∑ h, (J (h, j) : ℝ) / (d h : ℝ)) + |c j| * ∑ h, q h) :=
          Finset.sum_le_sum fun j _ ↦ hterm j
      _ = D * ∑ j, c j * (∑ h, (J (h, j) : ℝ) / (d h : ℝ)) + (∑ h, q h) * ∑ j, |c j| := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
          congr 1
          · exact Finset.sum_congr rfl fun j _ ↦ by ring
          · exact Finset.sum_congr rfl fun j _ ↦ by ring
      _ ≤ D * ∑ j, (c j * mean + |c j| * Δ) + (∑ h, q h) * ∑ j, |c j| := by
          have hsum := mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun j (_ : j ∈ (univ : Finset ι)) ↦ hmean j) hD
          linarith
      _ = D * (mean * ∑ j, c j + Δ * ∑ j, |c j|) + (∑ h, q h) * ∑ j, |c j| := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
          ring
  refine le_trans h1 (le_trans (le_of_eq h2) ?_)
  refine mul_le_mul (pow_le_pow_right₀ hZ h3) ?_ (Real.exp_nonneg _)
    (pow_nonneg hZ0.le _)
  rw [Real.exp_le_exp, h5]
  exact h6

end Pattern


/-! ### The expansion in the coordinates of the forms -/

section Expansion

variable {K κ ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Nonempty ι]

omit [DecidableEq κ] in
/-- **The value at the small point, expanded in the coordinates of the forms.** -/
theorem apply_eval_le_expansion (v : AbsoluteValue K ℝ) {A M : Matrix ι ι K} (hMA : M * A = 1)
    {T : MvPolynomial (κ × ι) K} {X : κ × ι → K}
    {Z : ℝ} (hZ : 1 ≤ Z) {c : ι → ℝ} {q : κ → ℝ} (hq : ∀ h, 0 < q h)
    {d : κ → ℕ} (hd : ∀ h, 0 < d h) {D : ℝ} (hD : 0 ≤ D)
    (hdq : ∀ h, D ≤ (d h : ℝ) * q h) (hdq' : ∀ h, ((d h : ℝ)) * q h ≤ D + q h)
    (hX : ∀ (h : κ) (j : ι), v (∑ i, A j i * X (h, i)) ≤ Z * Real.exp (c j * q h))
    {Δ mean : ℝ}
    (hJdeg : ∀ J ∈ (blockSubst M T).support, ∀ h, ∑ j, J (h, j) ≤ d h)
    (hJc : ∀ J ∈ (blockSubst M T).support, ∀ j,
      |(∑ h, (J (h, j) : ℝ) / (d h : ℝ)) - mean| ≤ Δ)
    (hTsupp : ∀ ν ∈ T.support, ∑ t, ν t ≤ ∑ h, d h)
    {N : ℝ} (hN : (#(blockSubst M T).support : ℝ) ≤ N) :
    v (eval X T)
      ≤ N * ((#T.support : ℝ) * ((⨆ ν, v (T.coeff ν))
          * ((Fintype.card ι : ℝ) * ((⨆ p : ι × ι, v (M p.1 p.2)) ⊔ 1)) ^ (∑ h, d h)))
        * (Z ^ (∑ h, d h) * Real.exp (D * (mean * ∑ j, c j + Δ * ∑ j, |c j|)
            + (∑ h, q h) * ∑ j, |c j|)) := by
  have hZ0 : (0 : ℝ) < Z := lt_of_lt_of_le zero_lt_one hZ
  set w : κ × ι → K := fun p ↦ ∑ i, A p.2 i * X (p.1, i) with hwdef
  set G : ℝ := Z ^ (∑ h, d h) * Real.exp (D * (mean * ∑ j, c j + Δ * ∑ j, |c j|)
      + (∑ h, q h) * ∑ j, |c j|) with hGdef
  have hG0 : 0 ≤ G := by
    rw [hGdef]
    positivity
  have hsupp : ∀ J ∈ (blockSubst M T).support, ∏ p, v (w p) ^ J p ≤ G := by
    intro J hJ
    exact prod_pow_apply_le v hZ hq hd hD hdq hdq' (fun p ↦ hX p.1 p.2) (hJdeg J hJ) (hJc J hJ)
  have hmain := apply_eval_le_of_forall_support v (P := blockSubst M T) w hG0 hsupp hN
  rw [eval_eq_eval_blockSubst hMA X T]
  refine le_trans hmain ?_
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (le_trans (by positivity) hN))
    hG0
  exact iSup_coeff_blockSubst_le v M hTsupp

omit [DecidableEq κ] [Nonempty ι] in
/-- **The value at the small point, at a nonarchimedean absolute value of `S`.** -/
theorem apply_eval_le_expansion_of_isNonarchimedean {v : AbsoluteValue K ℝ}
    (hv : IsNonarchimedean v) {A M : Matrix ι ι K} (hMA : M * A = 1)
    {T : MvPolynomial (κ × ι) K} {X : κ × ι → K}
    {Z : ℝ} (hZ : 1 ≤ Z) {c : ι → ℝ} {q : κ → ℝ} (hq : ∀ h, 0 < q h)
    {d : κ → ℕ} (hd : ∀ h, 0 < d h) {D : ℝ} (hD : 0 ≤ D)
    (hdq : ∀ h, D ≤ (d h : ℝ) * q h) (hdq' : ∀ h, ((d h : ℝ)) * q h ≤ D + q h)
    (hX : ∀ (h : κ) (j : ι), v (∑ i, A j i * X (h, i)) ≤ Z * Real.exp (c j * q h))
    {Δ mean : ℝ}
    (hJdeg : ∀ J ∈ (blockSubst M T).support, ∀ h, ∑ j, J (h, j) ≤ d h)
    (hJc : ∀ J ∈ (blockSubst M T).support, ∀ j,
      |(∑ h, (J (h, j) : ℝ) / (d h : ℝ)) - mean| ≤ Δ)
    (hTsupp : ∀ ν ∈ T.support, ∑ t, ν t ≤ ∑ h, d h) :
    v (eval X T)
      ≤ (⨆ ν, v (T.coeff ν)) * ((⨆ p : ι × ι, v (M p.1 p.2)) ⊔ 1) ^ (∑ h, d h)
        * (Z ^ (∑ h, d h) * Real.exp (D * (mean * ∑ j, c j + Δ * ∑ j, |c j|)
            + (∑ h, q h) * ∑ j, |c j|)) := by
  have hZ0 : (0 : ℝ) < Z := lt_of_lt_of_le zero_lt_one hZ
  set w : κ × ι → K := fun p ↦ ∑ i, A p.2 i * X (p.1, i) with hwdef
  set G : ℝ := Z ^ (∑ h, d h) * Real.exp (D * (mean * ∑ j, c j + Δ * ∑ j, |c j|)
      + (∑ h, q h) * ∑ j, |c j|) with hGdef
  have hG0 : 0 ≤ G := by
    rw [hGdef]
    positivity
  have hsupp : ∀ J ∈ (blockSubst M T).support, ∏ p, v (w p) ^ J p ≤ G := by
    intro J hJ
    exact prod_pow_apply_le v hZ hq hd hD hdq hdq' (fun p ↦ hX p.1 p.2) (hJdeg J hJ) (hJc J hJ)
  have hmain :=
    apply_eval_le_of_forall_support_of_isNonarchimedean hv (P := blockSubst M T) w hG0 hsupp
  rw [eval_eq_eval_blockSubst hMA X T]
  refine le_trans hmain ?_
  exact mul_le_mul_of_nonneg_right (iSup_coeff_blockSubst_le_of_isNonarchimedean hv M hTsupp) hG0

end Expansion

/-! ### The value of the derivative at the small point -/

section Place

variable {K : Type*} [Field K] {κ ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ] [Nonempty ι]

omit [DecidableEq ι] [DecidableEq κ] [Nonempty ι] in
/-- The total degree of a multihomogeneous polynomial is the sum of the block degrees. -/
theorem IsMultiHomogeneous.totalDegree_le {d : κ → ℕ} {P : MvPolynomial (κ × ι) K}
    (hP : IsMultiHomogeneous d P) : P.totalDegree ≤ ∑ h, d h := by
  refine Finset.sup_le fun ν hν ↦ ?_
  rw [Finsupp.sum_fintype _ _ fun _ ↦ rfl, Fintype.sum_prod_type]
  exact le_of_eq (Finset.sum_congr rfl fun h _ ↦ hP (mem_support_iff.mp hν) h)

omit [DecidableEq ι] [DecidableEq κ] [Nonempty ι] in
/-- A multihomogeneous polynomial has partial degrees at most the block degrees. -/
theorem IsMultiHomogeneous.card_support_le {d : κ → ℕ} {P : MvPolynomial (κ × ι) K}
    (hP : IsMultiHomogeneous d P) : #P.support ≤ ∏ p : κ × ι, (d p.1 + 1) :=
  MvPolynomial.card_support_le fun p ↦ hP.degreeOf_le p.1 p.2

variable {ρ : Type*} [Fintype ρ] [Nonempty ρ]

omit [DecidableEq κ] in
/-- **The value of the derivative at the small point, at an absolute value of `S`.** -/
theorem apply_eval_hasseDeriv_le_place (v : AbsoluteValue K ℝ) {A M : Matrix ι ι K}
    (hMA : M * A = 1) {d : κ → ℕ} (hd : ∀ h, 0 < d h) {P : MvPolynomial (κ × ι) K}
    (hP : IsMultiHomogeneous d P) (I : κ × ι →₀ ℕ) {X : κ × ι → K}
    {Pb : ℝ} (hPb : 1 ≤ Pb) (hW : (⨆ p : ι × ι, v (M p.1 p.2)) ⊔ 1 ≤ Pb)
    {cc : ι → ℝ} {q : κ → ℝ} (hq : ∀ h, 0 < q h) {D : ℝ} (hD : 0 ≤ D)
    (hdq : ∀ h, D ≤ (d h : ℝ) * q h) (hdq' : ∀ h, ((d h : ℝ)) * q h ≤ D + q h)
    (hX : ∀ (h : κ) (j : ι), v (∑ i, A j i * X (h, i))
      ≤ (Fintype.card ρ : ℝ) * Pb * Real.exp (cc j * q h))
    {Δ mean : ℝ}
    (hJc : ∀ J ∈ (blockSubst M (hasseDeriv I P)).support, ∀ j,
      |(∑ h, (J (h, j) : ℝ) / (d h : ℝ)) - mean| ≤ Δ) :
    v (eval X (hasseDeriv I P))
      ≤ ((∏ p : κ × ι, ((d p.1 : ℝ) + 1)) ^ 2
          * (2 * Fintype.card ι * Fintype.card ρ : ℝ) ^ (∑ h, d h))
        * (⨆ ν, v (P.coeff ν))
        * (Pb ^ (2 * ∑ h, d h)
          * Real.exp (D * (mean * ∑ j, cc j + Δ * ∑ j, |cc j|) + (∑ h, q h) * ∑ j, |cc j|)) := by
  classical
  set Dsum := ∑ h, d h with hDsum
  set T := hasseDeriv I P with hTdef
  set Nbox : ℝ := ∏ p : κ × ι, ((d p.1 : ℝ) + 1) with hNbox
  have hPb0 : (0 : ℝ) < Pb := lt_of_lt_of_le zero_lt_one hPb
  have hcardι : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hT : IsMultiHomogeneous (fun h ↦ d h - ∑ i, I (h, i)) T := hP.hasseDeriv I
  have hTle : ∀ h, d h - ∑ i, I (h, i) ≤ d h := fun h ↦ Nat.sub_le _ _
  have hTsupp : ∀ ν ∈ T.support, ∑ t, ν t ≤ Dsum := by
    intro ν hν
    rw [Fintype.sum_prod_type]
    exact Finset.sum_le_sum fun h _ ↦
      le_trans (le_of_eq (hT (mem_support_iff.mp hν) h)) (hTle h)
  have hJdeg : ∀ J ∈ (blockSubst M T).support, ∀ h, ∑ j, J (h, j) ≤ d h := by
    intro J hJ h
    exact le_trans (le_of_eq ((hT.blockSubst M) (mem_support_iff.mp hJ) h)) (hTle h)
  have hNbox0 : (1 : ℝ) ≤ Nbox := by
    rw [hNbox]
    refine Finset.one_le_prod₀ fun p _ ↦ ?_
    have : (0 : ℝ) ≤ (d p.1 : ℝ) := Nat.cast_nonneg _
    linarith
  have hnat : ∀ Pq : MvPolynomial (κ × ι) K,
      IsMultiHomogeneous (fun h ↦ d h - ∑ i, I (h, i)) Pq → (#Pq.support : ℝ) ≤ Nbox := by
    intro Pq hPq
    have h0 : #Pq.support ≤ ∏ p : κ × ι, (d p.1 + 1) :=
      le_trans hPq.card_support_le (Finset.prod_le_prod fun p _ ↦ by omega)
    have h1 : (#Pq.support : ℝ) ≤ ((∏ p : κ × ι, (d p.1 + 1) : ℕ) : ℝ) := by exact_mod_cast h0
    refine le_trans h1 (le_of_eq ?_)
    rw [hNbox, Nat.cast_prod]
    exact Finset.prod_congr rfl fun p _ ↦ by push_cast; ring
  have hN : (#(blockSubst M T).support : ℝ) ≤ Nbox := hnat _ (hT.blockSubst M)
  have hNT : (#T.support : ℝ) ≤ Nbox := hnat _ hT
  have hcardρ : (1 : ℝ) ≤ (Fintype.card ρ : ℝ) := by exact_mod_cast Fintype.card_pos
  have hZ : (1 : ℝ) ≤ (Fintype.card ρ : ℝ) * Pb := by nlinarith
  have hmain := apply_eval_le_expansion v hMA hZ hq hd hD hdq hdq' hX hJdeg hJc hTsupp hN
  refine le_trans hmain ?_
  set S : ℝ := ⨆ ν, v (P.coeff ν) with hS
  have hS0 : 0 ≤ S := Real.iSup_nonneg fun _ ↦ v.nonneg _
  set gain : ℝ := Real.exp (D * (mean * ∑ j, cc j + Δ * ∑ j, |cc j|) + (∑ h, q h) * ∑ j, |cc j|)
    with hgain
  have hgain0 : 0 ≤ gain := Real.exp_nonneg _
  have hW0 : (0 : ℝ) ≤ (⨆ p : ι × ι, v (M p.1 p.2)) ⊔ 1 := le_trans zero_le_one le_sup_right
  have hSupT : (⨆ ν, v (T.coeff ν)) ≤ 2 ^ Dsum * S := by
    refine le_trans (iSup_coeff_hasseDeriv_le v I P) ?_
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hP.totalDegree_le) hS0
  have hcard0 : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := by positivity
  have hc1 : (0 : ℝ) ≤ (Fintype.card ι : ℝ) * ((⨆ p : ι × ι, v (M p.1 p.2)) ⊔ 1) :=
    mul_nonneg hcard0 hW0
  have hpow : ((Fintype.card ι : ℝ) * ((⨆ p : ι × ι, v (M p.1 p.2)) ⊔ 1)) ^ Dsum
      ≤ ((Fintype.card ι : ℝ) * Pb) ^ Dsum :=
    pow_le_pow_left₀ hc1 (mul_le_mul_of_nonneg_left hW hcard0) _
  have hbc : (⨆ ν, v (T.coeff ν))
        * ((Fintype.card ι : ℝ) * ((⨆ p : ι × ι, v (M p.1 p.2)) ⊔ 1)) ^ Dsum
      ≤ (2 ^ Dsum * S) * ((Fintype.card ι : ℝ) * Pb) ^ Dsum :=
    mul_le_mul hSupT hpow (pow_nonneg hc1 _) (by positivity)
  have habc : (#T.support : ℝ)
        * ((⨆ ν, v (T.coeff ν))
          * ((Fintype.card ι : ℝ) * ((⨆ p : ι × ι, v (M p.1 p.2)) ⊔ 1)) ^ Dsum)
      ≤ Nbox * ((2 ^ Dsum * S) * ((Fintype.card ι : ℝ) * Pb) ^ Dsum) :=
    mul_le_mul hNT hbc
      (mul_nonneg (Real.iSup_nonneg fun _ ↦ v.nonneg _) (pow_nonneg hc1 _))
      (le_trans zero_le_one hNbox0)
  have hstep : Nbox * ((#T.support : ℝ) * ((⨆ ν, v (T.coeff ν))
        * ((Fintype.card ι : ℝ) * ((⨆ p : ι × ι, v (M p.1 p.2)) ⊔ 1)) ^ Dsum))
      * (((Fintype.card ρ : ℝ) * Pb) ^ Dsum * gain)
      ≤ Nbox * (Nbox * ((2 ^ Dsum * S) * ((Fintype.card ι : ℝ) * Pb) ^ Dsum))
        * (((Fintype.card ρ : ℝ) * Pb) ^ Dsum * gain) := by
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left habc ?_) ?_
    · linarith
    · positivity
  refine le_trans hstep (le_of_eq ?_)
  rw [mul_pow ((Fintype.card ι : ℝ)) Pb, mul_pow ((Fintype.card ρ : ℝ)) Pb,
    mul_pow (2 * (Fintype.card ι : ℝ)) ((Fintype.card ρ : ℝ)),
    mul_pow (2 : ℝ) ((Fintype.card ι : ℝ)), Nat.two_mul, pow_add]
  ring

omit [DecidableEq κ] [Nonempty ι] [Nonempty ρ] in
/-- **The value of the derivative at the small point, at a nonarchimedean absolute value of
`S`.** -/
theorem apply_eval_hasseDeriv_le_place_of_isNonarchimedean {v : AbsoluteValue K ℝ}
    (hv : IsNonarchimedean v) {A M : Matrix ι ι K}
    (hMA : M * A = 1) {d : κ → ℕ} (hd : ∀ h, 0 < d h) {P : MvPolynomial (κ × ι) K}
    (hP : IsMultiHomogeneous d P) (I : κ × ι →₀ ℕ) {X : κ × ι → K}
    {Pb : ℝ} (hPb : 1 ≤ Pb) (hW : (⨆ p : ι × ι, v (M p.1 p.2)) ⊔ 1 ≤ Pb)
    {cc : ι → ℝ} {q : κ → ℝ} (hq : ∀ h, 0 < q h) {D : ℝ} (hD : 0 ≤ D)
    (hdq : ∀ h, D ≤ (d h : ℝ) * q h) (hdq' : ∀ h, ((d h : ℝ)) * q h ≤ D + q h)
    (hX : ∀ (h : κ) (j : ι), v (∑ i, A j i * X (h, i)) ≤ Pb * Real.exp (cc j * q h))
    {Δ mean : ℝ}
    (hJc : ∀ J ∈ (blockSubst M (hasseDeriv I P)).support, ∀ j,
      |(∑ h, (J (h, j) : ℝ) / (d h : ℝ)) - mean| ≤ Δ) :
    v (eval X (hasseDeriv I P))
      ≤ (⨆ ν, v (P.coeff ν))
        * (Pb ^ (2 * ∑ h, d h)
          * Real.exp (D * (mean * ∑ j, cc j + Δ * ∑ j, |cc j|) + (∑ h, q h) * ∑ j, |cc j|)) := by
  classical
  set Dsum := ∑ h, d h with hDsum
  set T := hasseDeriv I P with hTdef
  have hPb0 : (0 : ℝ) < Pb := lt_of_lt_of_le zero_lt_one hPb
  have hT : IsMultiHomogeneous (fun h ↦ d h - ∑ i, I (h, i)) T := hP.hasseDeriv I
  have hTle : ∀ h, d h - ∑ i, I (h, i) ≤ d h := fun h ↦ Nat.sub_le _ _
  have hTsupp : ∀ ν ∈ T.support, ∑ t, ν t ≤ Dsum := by
    intro ν hν
    rw [Fintype.sum_prod_type]
    exact Finset.sum_le_sum fun h _ ↦
      le_trans (le_of_eq (hT (mem_support_iff.mp hν) h)) (hTle h)
  have hJdeg : ∀ J ∈ (blockSubst M T).support, ∀ h, ∑ j, J (h, j) ≤ d h := by
    intro J hJ h
    exact le_trans (le_of_eq ((hT.blockSubst M) (mem_support_iff.mp hJ) h)) (hTle h)
  have hmain := apply_eval_le_expansion_of_isNonarchimedean hv hMA hPb hq hd hD hdq hdq' hX
    hJdeg hJc hTsupp
  refine le_trans hmain ?_
  set S : ℝ := ⨆ ν, v (P.coeff ν) with hS
  have hS0 : 0 ≤ S := Real.iSup_nonneg fun _ ↦ v.nonneg _
  set gain : ℝ := Real.exp (D * (mean * ∑ j, cc j + Δ * ∑ j, |cc j|) + (∑ h, q h) * ∑ j, |cc j|)
    with hgain
  have hgain0 : 0 ≤ gain := Real.exp_nonneg _
  have hW0 : (0 : ℝ) ≤ (⨆ p : ι × ι, v (M p.1 p.2)) ⊔ 1 := le_trans zero_le_one le_sup_right
  have hSupT : (⨆ ν, v (T.coeff ν)) ≤ S := iSup_coeff_hasseDeriv_le_of_isNonarchimedean hv I P
  have hpow : ((⨆ p : ι × ι, v (M p.1 p.2)) ⊔ 1) ^ Dsum ≤ Pb ^ Dsum :=
    pow_le_pow_left₀ hW0 hW _
  have hstep : (⨆ ν, v (T.coeff ν)) * ((⨆ p : ι × ι, v (M p.1 p.2)) ⊔ 1) ^ Dsum
      * (Pb ^ Dsum * gain) ≤ S * Pb ^ Dsum * (Pb ^ Dsum * gain) := by
    refine mul_le_mul_of_nonneg_right (mul_le_mul hSupT hpow (pow_nonneg hW0 _) hS0) ?_
    positivity
  refine le_trans hstep (le_of_eq ?_)
  rw [Nat.two_mul, pow_add]
  ring

omit [DecidableEq ι] [DecidableEq κ] [Nonempty ι] [Nonempty ρ] in
/-- **The value of the derivative at the small point, at a place outside `S`**, where the point
is integral. -/
theorem apply_eval_hasseDeriv_le_of_isNonarchimedean {v : AbsoluteValue K ℝ}
    (hv : IsNonarchimedean v) {d : κ → ℕ} {P : MvPolynomial (κ × ι) K}
    (hP : IsMultiHomogeneous d P) (I : κ × ι →₀ ℕ) {X : κ × ι → K}
    {Pb : ℝ} (hPb : 1 ≤ Pb) (hXle : ∀ p, v (X p) ≤ Pb) :
    v (eval X (hasseDeriv I P)) ≤ (⨆ ν, v (P.coeff ν)) * Pb ^ (2 * ∑ h, d h) := by
  classical
  set Dsum := ∑ h, d h with hDsum
  set T := hasseDeriv I P with hTdef
  have hPb0 : (0 : ℝ) < Pb := lt_of_lt_of_le zero_lt_one hPb
  have hT : IsMultiHomogeneous (fun h ↦ d h - ∑ i, I (h, i)) T := hP.hasseDeriv I
  have hTle : ∀ h, d h - ∑ i, I (h, i) ≤ d h := fun h ↦ Nat.sub_le _ _
  have hTsupp : ∀ ν ∈ T.support, ∑ t, ν t ≤ Dsum := by
    intro ν hν
    rw [Fintype.sum_prod_type]
    exact Finset.sum_le_sum fun h _ ↦
      le_trans (le_of_eq (hT (mem_support_iff.mp hν) h)) (hTle h)
  have hsupp : ∀ ν ∈ T.support, ∏ p, v (X p) ^ ν p ≤ Pb ^ Dsum := by
    intro ν hν
    calc ∏ p, v (X p) ^ ν p ≤ ∏ p : κ × ι, Pb ^ ν p :=
          Finset.prod_le_prod₀ (fun p _ ↦ pow_nonneg (v.nonneg _) _)
            (fun p _ ↦ pow_le_pow_left₀ (v.nonneg _) (hXle p) _)
      _ = Pb ^ (∑ p : κ × ι, ν p) := Finset.prod_pow_eq_pow_sum _ _ _
      _ ≤ Pb ^ Dsum := pow_le_pow_right₀ hPb (hTsupp ν hν)
  have hmain := apply_eval_le_of_forall_support_of_isNonarchimedean hv (P := T) X
    (pow_nonneg hPb0.le _) hsupp
  refine le_trans hmain ?_
  set S : ℝ := ⨆ ν, v (P.coeff ν) with hS
  have hS0 : 0 ≤ S := Real.iSup_nonneg fun _ ↦ v.nonneg _
  have hSupT : (⨆ ν, v (T.coeff ν)) ≤ S := iSup_coeff_hasseDeriv_le_of_isNonarchimedean hv I P
  calc (⨆ ν, v (T.coeff ν)) * Pb ^ Dsum ≤ S * Pb ^ Dsum :=
        mul_le_mul_of_nonneg_right hSupT (pow_nonneg hPb0.le _)
    _ ≤ S * Pb ^ (2 * Dsum) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hPb (by omega)) hS0



end Place

end MvPolynomial

end

end
