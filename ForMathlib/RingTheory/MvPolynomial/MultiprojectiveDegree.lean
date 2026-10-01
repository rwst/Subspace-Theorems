/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.RingTheory.MvPolynomial.AgreeAbove
public import ForMathlib.RingTheory.MvPolynomial.HilbertPolynomial
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Data.Finset.Finsupp

-- Used only inside proofs.
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Sub.Prod

/-!
# The top form of a multigraded Hilbert polynomial

The multigraded Hilbert polynomial `H_I` of a multihomogeneous ideal has nonnegative top
coefficients. More precisely, for `|α|` equal to its total degree, `α! · [T^α] H_I` is a natural
number: it counts the cones of type `α` in a decomposition of the standard monomials
(`MvPolynomial.coeff_hilbertPoly_mul_factorial`). These numbers are the multiprojective degrees of
`V(I)` (G. Rémond, *Élimination multihomogène*, Chapter 5 of Nesterenko–Philippon (eds.),
*Introduction to algebraic independence theory*, LNM 1752 (2001), Theorem 2.10 and §2.3).

The proof is a *Stanley decomposition* of the standard monomials. If every generator `g` of the
upper set of leading monomials has coordinates `≤ k`, whether a monomial `c` is standard depends
only on its truncation `min(c, k)`. The monomials with a given truncation `a` form the cone
`a + ℕ^{V}`, where `V` is the set of variables with `a s = k`. In multidegree `d` that cone has
`∏ i, C(d i - |a|_i + N_i - 1, N_i - 1)` points, with `N_i` the number of variables of `V` in the
`i`-th block, for `d` large. This is a polynomial in `d` of total degree `∑ (N_i - 1)` whose top
form is the monomial `∏ i, T_i^{N_i - 1} / (N_i - 1)!` (`MvPolynomial.agreeAbove_conePoly`).
Positive top forms cannot cancel in a sum.

The second half is the degree formula for hypersurface sections (Evertse 1995, Lemma 1(iv)). By
`MvPolynomial.hilbertPoly_sup_span_singleton_of_isPrime`, `H_{𝔭 + (g)}(T) = H_𝔭(T) - H_𝔭(T - e)`,
and to first order `P(T) - P(T - e) = ∑ i, e i ∂_i P` (`MvPolynomial.agreeAbove_sub_shiftPoly`).
So `d_β(𝔭 + (g)) = ∑ i, e i d_{β + ε_i}(𝔭)`, and with the positivity above the dimension drops by
exactly one when `g` has positive degree in every block.

## Main definitions

* `MvPolynomial.conePoly b V w`: the polynomial counting the points of a cone.
* `MvPolynomial.coneType b V`: its top exponent, `i ↦ N_i - 1`.
* `MvPolynomial.dirDeriv e`: the derivative `∑ i, e i ∂_i`.
* `MvPolynomial.multidegree b I α`: the degree `d_α(I) = α! · [T^α] H_I`.

## Main statements

* `MvPolynomial.exists_hilbertPoly_eq_sum_conePoly`: the Hilbert polynomial is a sum of cone
  polynomials; `MvPolynomial.exists_hilbertPoly_eq_sum_conePoly_lex` with the cones made of
  standard monomials for a chosen lexicographic order.
* `MvPolynomial.totalDegree_eq_sup_of_eq_sum_conePoly`: the top coefficients of a sum of cone
  polynomials count cones.
* `MvPolynomial.coeff_hilbertPoly_mul_factorial`: `α! · [T^α] H_I` is the number of cones of type
  `α`, in every degree `|α| ≥ deg H_I`.
* `MvPolynomial.coeff_hilbertPoly_nonneg`: the top coefficients are nonnegative, and
  `MvPolynomial.exists_multidegree_eq_natCast`: the top degrees are natural numbers.
* `MvPolynomial.agreeAbove_sub_shiftPoly`: the top part of `P(T) - P(T - e)` is `∑ i, e i ∂_i P`.
* `MvPolynomial.multidegree_sup_span_singleton_of_isPrime`: Evertse's Lemma 1(iv).
* `MvPolynomial.totalDegree_hilbertPoly_sup_span_singleton`: a hypersurface section of positive
  degree in every block drops the dimension by exactly one.
-/

@[expose] public section

open Finset

variable {σ ι K : Type*}

namespace MvPolynomial

section TopForms

theorem aeval_ascPochhammer (i : ι) (n : ℕ) :
    (Polynomial.aeval (X i + 1 : MvPolynomial ι ℚ) (ascPochhammer ℚ n)).totalDegree ≤ n ∧
      AgreeAbove n (Polynomial.aeval (X i + 1 : MvPolynomial ι ℚ) (ascPochhammer ℚ n))
        (X i ^ n) := by
  induction n with
  | zero => simpa using AgreeAbove.refl 0 (1 : MvPolynomial ι ℚ)
  | succ n ih =>
    have hlin : Polynomial.aeval (X i + 1 : MvPolynomial ι ℚ) (Polynomial.X + (n : Polynomial ℚ)) =
        X i + C (1 + n : ℚ) := by
      rw [map_add, Polynomial.aeval_X, map_natCast, C_add, map_natCast, add_assoc, map_one]
    rw [ascPochhammer_succ_right, map_mul, hlin, pow_succ]
    exact ⟨(totalDegree_mul _ _).trans (add_le_add ih.1 (totalDegree_X_add_C_le_one i _)),
      ih.2.mul (agreeAbove_X_add_C i _) ih.1 (totalDegree_pow_le_of_le_one
        (totalDegree_X_le_one i) n) (totalDegree_X_add_C_le_one i _) (totalDegree_X_le_one i)⟩

theorem totalDegree_binomPoly_le (n : ℕ) (i : ι) : (binomPoly n i).totalDegree ≤ n :=
  (totalDegree_C_mul_le _ _).trans (aeval_ascPochhammer i n).1

/-- The top form of `C(T_i + n, n)` is `T_i^n / n!`. -/
theorem agreeAbove_binomPoly (n : ℕ) (i : ι) :
    AgreeAbove n (binomPoly n i) (C ((n.factorial : ℚ)⁻¹) * X i ^ n) :=
  (aeval_ascPochhammer i n).2.C_mul _

theorem totalDegree_shiftPoly_le (a : ι → ℕ) (P : MvPolynomial ι ℚ) :
    (shiftPoly a P).totalDegree ≤ P.totalDegree := by
  refine totalDegree_aeval_le (fun i ↦ ?_) P
  rw [sub_eq_add_neg, ← C_neg]
  exact totalDegree_X_add_C_le_one i _

/-- Translation does not change the top form. -/
theorem agreeAbove_shiftPoly (a : ι → ℕ) (P : MvPolynomial ι ℚ) :
    AgreeAbove P.totalDegree (shiftPoly a P) P := by
  refine agreeAbove_aeval (fun i ↦ ?_) (fun i ↦ ?_) P
  · rw [sub_eq_add_neg, ← C_neg]
    exact agreeAbove_X_add_C i _
  · rw [sub_eq_add_neg, ← C_neg]
    exact totalDegree_X_add_C_le_one i _

end TopForms

section Cones

variable [Fintype ι] [DecidableEq ι]

/-- The number of variables of `V` in the `i`-th block, minus one: the exponent of `T_i` in the
top form of `conePoly b V w`. -/
noncomputable def coneType (b : σ → ι) (V : Finset σ) : ι →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i ↦ #{s ∈ V | b s = i} - 1

/-- The polynomial `∏ i, C(T_i - w_i + N_i - 1, N_i - 1)`, with `N_i` the number of variables of
`V` in the `i`-th block. For `d ≥ w` it counts the monomials of multidegree `d` in a cone
`a + ℕ^V` with `|a| = w`. -/
noncomputable def conePoly (b : σ → ι) (V : Finset σ) (w : ι → ℕ) : MvPolynomial ι ℚ :=
  shiftPoly w (∏ i, binomPoly (#{s ∈ V | b s = i} - 1) i)

omit [DecidableEq ι] in
theorem prod_C_mul_X_pow (c : ι → ℚ) (n : ι → ℕ) :
    ∏ i, C (c i) * X i ^ n i = monomial (Finsupp.equivFunOnFinite.symm n) (∏ i, c i) := by
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Finset.prod_mul_distrib,
    map_prod]
  simp

/-- The top form of a cone polynomial is `∏ i, T_i^{N_i - 1} / (N_i - 1)!`. -/
theorem agreeAbove_conePoly (b : σ → ι) (V : Finset σ) (w : ι → ℕ) :
    AgreeAbove (coneType b V).degree (conePoly b V w)
      (monomial (coneType b V) (∏ i, ((coneType b V i).factorial : ℚ)⁻¹)) ∧
      (conePoly b V w).totalDegree ≤ (coneType b V).degree := by
  set P := ∏ i, binomPoly (#{s ∈ V | b s = i} - 1) i
  have hdeg : (coneType b V).degree = ∑ i, (#{s ∈ V | b s = i} - 1) := by
    rw [Finsupp.degree_eq_sum]
    simp [coneType]
  have hP : P.totalDegree ≤ (coneType b V).degree :=
    hdeg ▸ (totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun i _ ↦
      totalDegree_binomPoly_le _ i)
  refine ⟨?_, (totalDegree_shiftPoly_le w P).trans hP⟩
  refine ((agreeAbove_shiftPoly w P).mono hP).trans ?_
  have := AgreeAbove.prod (s := univ) (fun i _ ↦ agreeAbove_binomPoly
    (#{s ∈ V | b s = i} - 1) i) (fun i _ ↦ totalDegree_binomPoly_le _ i)
    (fun i _ ↦ (totalDegree_C_mul_le _ _).trans
      (totalDegree_pow_le_of_le_one (totalDegree_X_le_one i) _))
  rw [prod_C_mul_X_pow, ← hdeg] at this
  exact this

theorem eval_conePoly (b : σ → ι) (V : Finset σ) {w d : ι → ℕ} (hwd : w ≤ d) :
    eval (fun i ↦ (d i : ℚ)) (conePoly b V w) =
      ∏ i, ((d i - w i + (#{s ∈ V | b s = i} - 1)).choose (#{s ∈ V | b s = i} - 1) : ℚ) := by
  rw [conePoly, eval_shiftPoly]
  have : (fun i ↦ (d i : ℚ) - (w i : ℚ)) = fun i ↦ ((d i - w i : ℕ) : ℚ) := by
    funext i
    rw [Nat.cast_sub (hwd i)]
  rw [this, map_prod]
  exact Finset.prod_congr rfl fun i _ ↦ eval_binomPoly _ i (fun i ↦ d i - w i)

end Cones

section Difference

variable [Fintype ι]

/-- The derivative `∑ i, e i ∂_i` in the direction `e`. -/
noncomputable def dirDeriv (e : ι → ℕ) : MvPolynomial ι ℚ →ₗ[ℚ] MvPolynomial ι ℚ :=
  ∑ i, (e i : ℚ) • (pderiv i).toLinearMap

theorem dirDeriv_apply (e : ι → ℕ) (P : MvPolynomial ι ℚ) :
    dirDeriv e P = ∑ i, (e i : ℚ) • pderiv i P := by
  simp [dirDeriv]

theorem coeff_dirDeriv (e : ι → ℕ) (P : MvPolynomial ι ℚ) (β : ι →₀ ℕ) :
    (dirDeriv e P).coeff β = ∑ i, (e i : ℚ) * (P.coeff (β + Finsupp.single i 1) * (β i + 1)) := by
  rw [dirDeriv_apply, coeff_sum]
  simp [coeff_pderiv]

omit [Fintype ι] in
theorem totalDegree_pderiv_le (i : ι) (P : MvPolynomial ι ℚ) :
    (pderiv i P).totalDegree ≤ P.totalDegree - 1 :=
  totalDegree_le_of_forall_coeff_eq_zero fun α hα ↦ by
    rw [coeff_pderiv, coeff_eq_zero_of_totalDegree_lt_degree, zero_mul]
    rw [map_add, Finsupp.degree_single]
    omega

theorem totalDegree_dirDeriv_le (e : ι → ℕ) (P : MvPolynomial ι ℚ) :
    (dirDeriv e P).totalDegree ≤ P.totalDegree - 1 := by
  rw [dirDeriv_apply]
  exact (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ ↦
    (totalDegree_smul_le _ _).trans (totalDegree_pderiv_le i P))

omit [Fintype ι] in
theorem shiftPoly_mul (a : ι → ℕ) (P Q : MvPolynomial ι ℚ) :
    shiftPoly a (P * Q) = shiftPoly a P * shiftPoly a Q :=
  map_mul _ _ _

omit [Fintype ι] in
theorem shiftPoly_X (a : ι → ℕ) (i : ι) : shiftPoly a (X i) = X i - C (a i : ℚ) :=
  aeval_X _ _

omit [Fintype ι] in
theorem shiftPoly_smul (a : ι → ℕ) (c : ℚ) (P : MvPolynomial ι ℚ) :
    shiftPoly a (c • P) = c • shiftPoly a P :=
  map_smul (aeval fun i ↦ X i - C (a i : ℚ)) c P

omit [Fintype ι] in
theorem shiftPoly_sum {τ : Type*} (a : ι → ℕ) (s : Finset τ) (f : τ → MvPolynomial ι ℚ) :
    shiftPoly a (∑ t ∈ s, f t) = ∑ t ∈ s, shiftPoly a (f t) :=
  map_sum (aeval fun i ↦ X i - C (a i : ℚ)) f s

theorem agreeAbove_sub_shiftPoly_monomial (e : ι → ℕ) (v : ι →₀ ℕ) :
    AgreeAbove (v.degree - 1) (monomial v 1 - shiftPoly e (monomial v 1))
      (dirDeriv e (monomial v 1)) := by
  classical
  induction h : v.degree generalizing v with
  | zero =>
    have hv : v = 0 := by
      ext s
      have := (Finsupp.degree_eq_zero_iff v).mp h
      simp [this]
    subst hv
    have h1 : shiftPoly e (1 : MvPolynomial ι ℚ) = 1 := map_one _
    have h0 : monomial (0 : ι →₀ ℕ) (1 : ℚ) = 1 := rfl
    rw [h0, h1, sub_self, dirDeriv_apply]
    simpa using AgreeAbove.refl 0 (0 : MvPolynomial ι ℚ)
  | succ k ih =>
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra hne
      push Not at hne
      have : v = 0 := Finsupp.ext hne
      simp [this] at h
    set w := v - Finsupp.single i 1
    have hv : v = w + Finsupp.single i 1 :=
      (tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi))).symm
    have hw : w.degree = k := by
      have := congrArg Finsupp.degree hv
      rw [map_add, Finsupp.degree_single, h] at this
      omega
    have hXw : (monomial w (1 : ℚ)).totalDegree ≤ k :=
      (totalDegree_monomial_le _ _).trans (by rw [← hw, Finsupp.degree_apply]; rfl)
    rw [hv, monomial_add_single, pow_one]
    have hΔ : monomial w (1 : ℚ) * X i - shiftPoly e (monomial w 1 * X i) =
        (monomial w 1 - shiftPoly e (monomial w 1)) * X i +
          C (e i : ℚ) * shiftPoly e (monomial w 1) := by
      rw [shiftPoly_mul, shiftPoly_X]
      ring
    have hD : dirDeriv e (monomial w (1 : ℚ) * X i) =
        dirDeriv e (monomial w 1) * X i + C (e i : ℚ) * monomial w 1 := by
      simp only [dirDeriv_apply, Derivation.leibniz, pderiv_X, smul_add, Finset.sum_add_distrib,
        Finset.sum_mul]
      rw [add_comm]
      congr 1
      · exact Finset.sum_congr rfl fun x _ ↦ by rw [smul_mul_assoc, mul_comm, smul_eq_mul]
      · simp [Pi.single_apply, smul_eq_C_mul]
    rw [hΔ, hD]
    refine AgreeAbove.add ?_ ((agreeAbove_shiftPoly e _).mono hXw |>.C_mul _)
    rcases k with _ | k
    · rw [(ih w hw).eq_of_zero]
    · have ih' := ih w hw
      simp only [Nat.add_sub_cancel] at ih' ⊢
      have hD' : (dirDeriv e (monomial w (1 : ℚ))).totalDegree ≤ k :=
        (totalDegree_dirDeriv_le e _).trans (by omega)
      exact ih'.mul (AgreeAbove.refl 1 (X i)) (ih'.totalDegree_le hD') hD'
        (totalDegree_X_le_one i) (totalDegree_X_le_one i)

/-- **Taylor's formula to first order.** The top part of `P(T) - P(T - e)` is `∑ i, e i ∂_i P`. -/
theorem agreeAbove_sub_shiftPoly (e : ι → ℕ) (P : MvPolynomial ι ℚ) :
    AgreeAbove (P.totalDegree - 1) (P - shiftPoly e P) (dirDeriv e P) := by
  have key : ∀ v ∈ P.support, AgreeAbove (P.totalDegree - 1)
      (monomial v (P.coeff v) - shiftPoly e (monomial v (P.coeff v)))
      (dirDeriv e (monomial v (P.coeff v))) := by
    intro v hv
    have hm : monomial v (P.coeff v) = P.coeff v • monomial v (1 : ℚ) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hm, shiftPoly_smul, ← smul_sub, map_smul]
    have hdeg : v.degree ≤ P.totalDegree := by
      rw [Finsupp.degree_apply]
      exact le_totalDegree hv
    exact ((agreeAbove_sub_shiftPoly_monomial e v).mono (by omega)).smul _
  have := AgreeAbove.sum key
  rwa [Finset.sum_sub_distrib, ← shiftPoly_sum, ← map_sum, ← P.as_sum] at this

omit [Fintype ι] in
theorem totalDegree_sub_shiftPoly_le [Finite ι] (e : ι → ℕ) (P : MvPolynomial ι ℚ) :
    (P - shiftPoly e P).totalDegree ≤ P.totalDegree - 1 :=
  have := Fintype.ofFinite ι
  (agreeAbove_sub_shiftPoly e P).totalDegree_le (totalDegree_dirDeriv_le e P)

/-- The coefficients of `P(T) - P(T - e)` in degree `≥ deg P - 1`. -/
theorem coeff_sub_shiftPoly (e : ι → ℕ) (P : MvPolynomial ι ℚ) {β : ι →₀ ℕ}
    (hβ : P.totalDegree - 1 ≤ β.degree) :
    (P - shiftPoly e P).coeff β =
      ∑ i, (e i : ℚ) * (P.coeff (β + Finsupp.single i 1) * (β i + 1)) := by
  rw [agreeAbove_sub_shiftPoly e P β hβ, coeff_dirDeriv]

end Difference

section Truncation

/-- The truncation `min(c, k)` of a monomial, coordinatewise. -/
noncomputable def truncate (k : ℕ) (c : σ →₀ ℕ) : σ →₀ ℕ :=
  Finsupp.mapRange (fun n ↦ min n k) (by simp) c

theorem truncate_apply (k : ℕ) (c : σ →₀ ℕ) (s : σ) : truncate k c s = min (c s) k :=
  Finsupp.mapRange_apply

/-- A monomial with coordinates `≤ k` divides `c` iff it divides the truncation of `c`. -/
theorem le_truncate_iff {k : ℕ} {g c : σ →₀ ℕ} (hg : ∀ s, g s ≤ k) :
    g ≤ truncate k c ↔ g ≤ c := by
  simp only [Finsupp.le_def, truncate_apply]
  exact forall_congr' fun s ↦ ⟨fun h ↦ h.trans (min_le_left _ _), fun h ↦ le_min h (hg s)⟩

variable [Fintype σ]

/-- The monomials with all coordinates `≤ k`. -/
noncomputable def box (k : ℕ) : Finset (σ →₀ ℕ) :=
  (univ : Finset σ).finsupp fun _ ↦ range (k + 1)

theorem mem_box {k : ℕ} {a : σ →₀ ℕ} : a ∈ box k ↔ ∀ s, a s ≤ k := by
  simp [box, Finset.mem_finsupp_iff]

theorem truncate_mem_box (k : ℕ) (c : σ →₀ ℕ) : truncate k c ∈ box k :=
  mem_box.mpr fun s ↦ by
    rw [truncate_apply]
    exact min_le_right _ _

/-- The variables that are free in the cone of monomials with truncation `a`. -/
def coneVars (k : ℕ) (a : σ →₀ ℕ) : Finset σ := {s | a s = k}

theorem truncate_eq_iff {k : ℕ} {a c : σ →₀ ℕ} (ha : a ∈ box k) :
    truncate k c = a ↔ a ≤ c ∧ (c - a).support ⊆ coneVars k a := by
  rw [mem_box] at ha
  simp only [Finsupp.ext_iff, truncate_apply, Finsupp.le_def, Finset.subset_iff,
    Finsupp.mem_support_iff, Finsupp.tsub_apply, coneVars, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · intro h
    exact ⟨fun s ↦ by have := h s; have := ha s; omega,
      fun s hs ↦ by have := h s; have := ha s; omega⟩
  · rintro ⟨h₁, h₂⟩ s
    have := h₁ s
    have := ha s
    by_cases hs : c s - a s = 0
    · omega
    · have := h₂ hs
      omega

end Truncation

section Count

variable [Fintype σ] [DecidableEq σ] [Fintype ι] [DecidableEq ι]

/-- The monomials of multidegree `e` supported in `V`, counted with the blocks of `V`. -/
theorem card_filter_support_subset (b : σ → ι) (V : Finset σ) (e : ι → ℕ) :
    #((blockMonomials b e).filter (·.support ⊆ V)) =
      ∏ i, (#{s ∈ V | b s = i} + e i - 1).choose (e i) := by
  set b' : σ → Option ι := fun s ↦ if s ∈ V then some (b s) else none
  set e' : Option ι → ℕ := fun o ↦ o.elim 0 e
  have hnone : ({s | b' s = none} : Finset σ) = ({s | s ∉ V} : Finset σ) := by
    ext s
    by_cases hs : s ∈ V <;> simp [b', hs]
  have hsome : ∀ i, ({s | b' s = some i} : Finset σ) = {s ∈ V | b s = i} := by
    intro i
    ext s
    by_cases hs : s ∈ V <;> simp [b', hs]
  have hset : (blockMonomials b e).filter (·.support ⊆ V) = blockMonomials b' e' := by
    ext x
    rw [Finset.mem_filter, mem_blockMonomials, mem_blockMonomials, funext_iff, funext_iff]
    simp only [weight_multiWeight_apply, Option.forall, e', Option.elim, hnone, hsome]
    have hzero : x.support ⊆ V ↔ ∑ s with s ∉ V, x s = 0 := by
      rw [Finset.sum_eq_zero_iff, Finset.subset_iff]
      simp only [Finsupp.mem_support_iff, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h s hs ↦ by_contra fun h' ↦ hs (h h'), fun h s hs ↦ by_contra fun h' ↦ hs (h s h')⟩
    have hblock : x.support ⊆ V → ∀ i, ∑ s with b s = i, x s = ∑ s ∈ V with b s = i, x s := by
      intro h i
      rw [Finset.sum_filter, Finset.sum_filter]
      refine (Finset.sum_subset (Finset.subset_univ V) fun s _ hs ↦ ?_).symm
      have : x s = 0 := by
        by_contra h'
        exact hs (h (Finsupp.mem_support_iff.mpr h'))
      simp [this]
    rw [hzero]
    constructor
    · rintro ⟨h, hV⟩
      refine ⟨hV, fun i ↦ ?_⟩
      rw [← hblock (hzero.mpr hV) i, h i]
    · rintro ⟨hV, h⟩
      refine ⟨fun i ↦ ?_, hV⟩
      rw [hblock (hzero.mpr hV) i, h i]
  rw [hset, card_blockMonomials, Fintype.prod_option]
  simp [e', hsome]

omit [Fintype σ] [DecidableEq σ] [Fintype ι] in
theorem weight_mono' {b : σ → ι} {a c : σ →₀ ℕ} (h : a ≤ c) :
    Finsupp.weight (multiWeight b) c =
      Finsupp.weight (multiWeight b) (c - a) + Finsupp.weight (multiWeight b) a := by
  rw [← map_add, tsub_add_cancel_of_le h]

/-- The monomials of multidegree `d` with truncation `a` are the translates by `a` of the
monomials of multidegree `d - |a|` supported in the free variables of `a`. -/
theorem card_filter_truncate_eq (b : σ → ι) {k : ℕ} {a : σ →₀ ℕ} (ha : a ∈ box k) {d : ι → ℕ}
    (hd : Finsupp.weight (multiWeight b) a ≤ d) :
    #((blockMonomials b d).filter (truncate k · = a)) =
      #((blockMonomials b (d - Finsupp.weight (multiWeight b) a)).filter
        (·.support ⊆ coneVars k a)) := by
  refine Finset.card_nbij' (· - a) (· + a) ?_ ?_ ?_ ?_
  · intro c hc
    rw [Finset.mem_coe, Finset.mem_filter, mem_blockMonomials, truncate_eq_iff ha] at hc
    rw [Finset.mem_coe, Finset.mem_filter, mem_blockMonomials]
    obtain ⟨hcw, hac, hsupp⟩ := hc
    refine ⟨?_, hsupp⟩
    rw [← hcw, weight_mono' hac, add_tsub_cancel_right]
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_filter, mem_blockMonomials] at hx
    rw [Finset.mem_coe, Finset.mem_filter, mem_blockMonomials, truncate_eq_iff ha,
      add_tsub_cancel_right, map_add, hx.1, tsub_add_cancel_of_le hd]
    exact ⟨rfl, le_add_self, hx.2⟩
  · intro c hc
    rw [Finset.mem_coe, Finset.mem_filter, truncate_eq_iff ha] at hc
    exact tsub_add_cancel_of_le hc.2.1
  · intro x _
    exact add_tsub_cancel_right x a

theorem card_filter_truncate_eq_zero (b : σ → ι) {k : ℕ} {a : σ →₀ ℕ} (ha : a ∈ box k)
    {d : ι → ℕ} (hd : ¬Finsupp.weight (multiWeight b) a ≤ d) :
    #((blockMonomials b d).filter (truncate k · = a)) = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro c hc h
  rw [mem_blockMonomials] at hc
  rw [truncate_eq_iff ha] at h
  exact hd (hc ▸ weight_mono h.1)

/-- **Stanley decomposition.** If every monomial of `G` has coordinates `≤ k`, the standard
monomials for `G` are the disjoint union of the cones of the standard truncations. -/
theorem card_filter_forall_not_le_eq_sum (b : σ → ι) {G : Finset (σ →₀ ℕ)} {k : ℕ}
    (hk : ∀ g ∈ G, ∀ s, g s ≤ k) (d : ι → ℕ) :
    #((blockMonomials b d).filter fun c ↦ ∀ g ∈ G, ¬g ≤ c) =
      ∑ a ∈ (box k).filter (fun a ↦ ∀ g ∈ G, ¬g ≤ a),
        #((blockMonomials b d).filter (truncate k · = a)) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := truncate k)]
  · refine Finset.sum_congr rfl fun a ha ↦ ?_
    rw [Finset.filter_filter]
    refine congrArg _ (Finset.filter_congr fun c _ ↦ ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩)
    intro g hg hgc
    exact (Finset.mem_filter.mp ha).2 g hg (h ▸ (le_truncate_iff (hk g hg)).mpr hgc)
  · intro c hc
    rw [Finset.mem_coe, Finset.mem_filter] at hc ⊢
    exact ⟨truncate_mem_box k c, fun g hg hgc ↦ hc.2 g hg ((le_truncate_iff (hk g hg)).mp hgc)⟩

omit [DecidableEq σ] [Fintype ι] in
theorem weight_le_of_mem_box (b : σ → ι) {k : ℕ} {a : σ →₀ ℕ} (ha : a ∈ box k) (i : ι) :
    Finsupp.weight (multiWeight b) a i ≤ k * Fintype.card σ := by
  rw [weight_multiWeight_apply]
  calc ∑ s with b s = i, a s ≤ ∑ s, a s := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ ≤ ∑ _ : σ, k := Finset.sum_le_sum fun s _ ↦ mem_box.mp ha s
    _ = k * Fintype.card σ := by simp [mul_comm]

/-- For `d` large, the number of monomials of multidegree `d` with truncation `a` is the value
of a cone polynomial, or zero if the free variables of `a` miss a block. -/
theorem card_filter_truncate_eq_eval (b : σ → ι) {k : ℕ} {a : σ →₀ ℕ} (ha : a ∈ box k)
    {d : ι → ℕ} (hd : ∀ i, k * Fintype.card σ < d i) :
    (#((blockMonomials b d).filter (truncate k · = a)) : ℚ) =
      if ∀ i, ∃ s ∈ coneVars k a, b s = i then
        eval (fun i ↦ (d i : ℚ)) (conePoly b (coneVars k a) (Finsupp.weight (multiWeight b) a))
      else 0 := by
  have hw : Finsupp.weight (multiWeight b) a ≤ d :=
    fun i ↦ (weight_le_of_mem_box b ha i).trans (hd i).le
  rw [card_filter_truncate_eq b ha hw, card_filter_support_subset]
  split_ifs with hV
  · rw [eval_conePoly _ _ hw, Nat.cast_prod]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    obtain ⟨s, hs, hsi⟩ := hV i
    have : 0 < #{s ∈ coneVars k a | b s = i} := Finset.card_pos.mpr ⟨s, by simp [hs, hsi]⟩
    rw [Pi.sub_apply, show #{s ∈ coneVars k a | b s = i} + (d i -
      Finsupp.weight (multiWeight b) a i) - 1 = d i - Finsupp.weight (multiWeight b) a i +
        (#{s ∈ coneVars k a | b s = i} - 1) by omega, Nat.choose_symm_add]
  · push Not at hV
    obtain ⟨i, hi⟩ := hV
    have h0 : #{s ∈ coneVars k a | b s = i} = 0 :=
      Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun s hs hsi ↦ hi s hs hsi)
    have hpos : 0 < d i - Finsupp.weight (multiWeight b) a i := by
      have := weight_le_of_mem_box b ha i
      have := hd i
      omega
    rw [Nat.cast_eq_zero]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [h0, Pi.sub_apply, zero_add]
    exact Nat.choose_eq_zero_of_lt (Nat.sub_lt hpos Nat.one_pos)

end Count

section HilbertPolynomial

variable [Field K] [Finite σ] [Fintype ι] [DecidableEq ι]

/-- **The Hilbert polynomial is a sum of cone polynomials**, for the lexicographic order of a
given order on the variables. Every cone `a + ℕ^{V a}` meets every block and consists of standard
monomials. A set `T` of variables meeting every block, all of whose monomials are standard, is the
set of free variables of one of the cones. -/
theorem exists_hilbertPoly_eq_sum_conePoly_lex [LinearOrder σ] {b : σ → ι}
    (hb : Function.Surjective b) {I : Ideal (MvPolynomial σ K)}
    (hI : I.IsWeightedHomogeneous (multiWeight b)) :
    ∃ (A : Finset (σ →₀ ℕ)) (V : (σ →₀ ℕ) → Finset σ), (∀ a ∈ A, ∀ i, ∃ s ∈ V a, b s = i) ∧
      (∀ a ∈ A, ∀ c : σ →₀ ℕ, c.support ⊆ V a → a + c ∉ leadingMonomials MonomialOrder.lex I) ∧
      (∀ T : Finset σ, (∀ i, ∃ s ∈ T, b s = i) →
        (∀ c : σ →₀ ℕ, c.support ⊆ T → c ∉ leadingMonomials MonomialOrder.lex I) →
          ∃ a ∈ A, V a = T) ∧
      hilbertPoly b I = ∑ a ∈ A, conePoly b (V a) (Finsupp.weight (multiWeight b) a) := by
  classical
  have := Fintype.ofFinite σ
  obtain ⟨G, hG⟩ := exists_finset_leadingMonomials (MonomialOrder.lex (σ := σ)) I
  set k := ∑ g ∈ G, ∑ s, g s + 1
  have hk : ∀ g ∈ G, ∀ s, g s ≤ k := fun g hg s ↦ Nat.le_succ_of_le
    ((Finset.single_le_sum (f := fun s ↦ g s) (fun s _ ↦ Nat.zero_le _) (Finset.mem_univ s)).trans
      (Finset.single_le_sum (f := fun g ↦ ∑ s, g s) (fun _ _ ↦ Nat.zero_le _) hg))
  have hstd : ∀ c, c ∉ leadingMonomials MonomialOrder.lex I ↔ ∀ g ∈ G, ¬g ≤ c := by
    intro c
    rw [hG]
    push Not
    rfl
  refine ⟨((box k).filter fun a ↦ ∀ g ∈ G, ¬g ≤ a).filter
    fun a ↦ ∀ i, ∃ s ∈ coneVars k a, b s = i, coneVars k,
    fun a ha ↦ (Finset.mem_filter.mp ha).2, fun a ha c hc ↦ ?_, fun T hTb hT ↦ ?_, ?_⟩
  · obtain ⟨⟨hbox, ha⟩, -⟩ := Finset.mem_filter.mp ha |>.imp_left Finset.mem_filter.mp
    have htr : truncate k (a + c) = a := by
      rw [truncate_eq_iff hbox, add_tsub_cancel_left]
      exact ⟨le_self_add, hc⟩
    rw [hstd]
    intro g hg hgc
    exact ha g hg (htr ▸ (le_truncate_iff (hk g hg)).mpr hgc)
  · set a : σ →₀ ℕ := Finsupp.onFinset T (fun s ↦ if s ∈ T then k else 0) fun s hs ↦ by
      by_contra h
      simp [h] at hs
    have happ : ∀ s, a s = if s ∈ T then k else 0 := fun s ↦ Finsupp.onFinset_apply
    have hV : coneVars k a = T := by
      ext s
      simp only [coneVars, Finset.mem_filter, Finset.mem_univ, true_and, happ]
      split_ifs with hs <;> simp [hs, k]
    refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨mem_box.mpr fun s ↦ ?_, ?_⟩,
      hV ▸ hTb⟩, hV⟩
    · rw [happ]
      split_ifs <;> simp
    · refine (hstd a).mp (hT a fun s hs ↦ ?_)
      by_contra h
      simp [happ, h] at hs
  · refine hilbertPoly_eq_of_forall_le hb hI (d₀ := fun _ ↦ k * Fintype.card σ + 1)
      fun d hd ↦ ?_
    have hd' : ∀ i, k * Fintype.card σ < d i := fun i ↦ hd i
    rw [hilbertFunction_eq_card_filter MonomialOrder.lex b hI d]
    have hfilter : ((blockMonomials b d).filter (· ∉ leadingMonomials MonomialOrder.lex I)) =
        (blockMonomials b d).filter fun c ↦ ∀ g ∈ G, ¬g ≤ c :=
      Finset.filter_congr fun c _ ↦ hstd c
    rw [hfilter, card_filter_forall_not_le_eq_sum b hk, Nat.cast_sum, map_sum]
    conv_rhs => rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun a ha ↦ ?_
    exact card_filter_truncate_eq_eval b (Finset.mem_filter.mp ha).1 hd'

/-- **The Hilbert polynomial is a sum of cone polynomials.** Every cone meets every block. -/
theorem exists_hilbertPoly_eq_sum_conePoly {b : σ → ι} (hb : Function.Surjective b)
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsWeightedHomogeneous (multiWeight b)) :
    ∃ (A : Finset (σ →₀ ℕ)) (V : (σ →₀ ℕ) → Finset σ), (∀ a ∈ A, ∀ i, ∃ s ∈ V a, b s = i) ∧
      hilbertPoly b I = ∑ a ∈ A, conePoly b (V a) (Finsupp.weight (multiWeight b) a) := by
  have := Fintype.ofFinite σ
  let : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  obtain ⟨A, V, hV, -, -, hH⟩ := exists_hilbertPoly_eq_sum_conePoly_lex hb hI
  exact ⟨A, V, hV, hH⟩

omit [Finite σ] in
/-- **The top coefficients of a sum of cone polynomials count cones.** The total degree is the
largest cone type, and for `|α| ≥` the total degree, `α! · [T^α]` is the number of cones of type
`α`. -/
theorem totalDegree_eq_sup_of_eq_sum_conePoly {τ : Type*} {b : σ → ι} {P : MvPolynomial ι ℚ}
    {A : Finset τ} {V : τ → Finset σ} {w : τ → ι → ℕ}
    (hP : P = ∑ a ∈ A, conePoly b (V a) (w a)) :
    P.totalDegree = A.sup (fun a ↦ (coneType b (V a)).degree) ∧
      ∀ α : ι →₀ ℕ, P.totalDegree ≤ α.degree →
        P.coeff α * ∏ i, ((α i).factorial : ℚ) = #(A.filter fun a ↦ coneType b (V a) = α) := by
  have hQ := fun a (_ : a ∈ A) ↦ (agreeAbove_conePoly b (V a) (w a)).1
  have hdeg := fun a (_ : a ∈ A) ↦ (agreeAbove_conePoly b (V a) (w a)).2
  have htot : P.totalDegree = A.sup (fun a ↦ (coneType b (V a)).degree) := by
    rw [hP]
    exact totalDegree_sum_of_agreeAbove hQ hdeg fun a _ ↦
      Finset.prod_pos fun i _ ↦ inv_pos.mpr (Nat.cast_pos.mpr (Nat.factorial_pos _))
  refine ⟨htot, fun α hα ↦ ?_⟩
  have hα' : ∀ a ∈ A, (coneType b (V a)).degree ≤ α.degree := fun a ha ↦
    (Finset.le_sup (f := fun a ↦ (coneType b (V a)).degree) ha).trans (htot ▸ hα)
  rw [hP, coeff_sum_of_agreeAbove hQ hα', Finset.sum_mul]
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  rw [(Finset.mem_filter.mp ha).2, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun i _ ↦
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

/-- **The top coefficients of the Hilbert polynomial count cones.** In a decomposition of the
standard monomials into cones meeting every block, the total degree of `H_I` is the largest cone
type, and for `|α| ≥ deg H_I`, `α! · [T^α] H_I` is the number of cones of type `α`. -/
theorem coeff_hilbertPoly_mul_factorial {b : σ → ι} (hb : Function.Surjective b)
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsWeightedHomogeneous (multiWeight b)) :
    ∃ (A : Finset (σ →₀ ℕ)) (V : (σ →₀ ℕ) → Finset σ),
      (hilbertPoly b I).totalDegree = A.sup (fun a ↦ (coneType b (V a)).degree) ∧
      ∀ α : ι →₀ ℕ, (hilbertPoly b I).totalDegree ≤ α.degree →
        (hilbertPoly b I).coeff α * ∏ i, ((α i).factorial : ℚ) =
          #(A.filter fun a ↦ coneType b (V a) = α) := by
  obtain ⟨A, V, -, hH⟩ := exists_hilbertPoly_eq_sum_conePoly hb hI
  exact ⟨A, V, totalDegree_eq_sup_of_eq_sum_conePoly hH⟩

omit [Fintype ι] in
/-- **The top coefficients of the Hilbert polynomial are nonnegative.** -/
theorem coeff_hilbertPoly_nonneg [Finite ι] {b : σ → ι} (hb : Function.Surjective b)
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsWeightedHomogeneous (multiWeight b))
    {α : ι →₀ ℕ} (hα : (hilbertPoly b I).totalDegree ≤ α.degree) :
    0 ≤ (hilbertPoly b I).coeff α := by
  have := Fintype.ofFinite ι
  obtain ⟨A, V, -, h⟩ := coeff_hilbertPoly_mul_factorial hb hI
  have hpos : (0 : ℚ) < ∏ i, ((α i).factorial : ℚ) :=
    Finset.prod_pos fun i _ ↦ Nat.cast_pos.mpr (Nat.factorial_pos _)
  have := h α hα
  have hnn : (0 : ℚ) ≤ (hilbertPoly b I).coeff α * ∏ i, ((α i).factorial : ℚ) :=
    this ▸ Nat.cast_nonneg _
  exact nonneg_of_mul_nonneg_left hnn hpos

/-- The *multiprojective degree* `d_α(I) = α! · [T^α] H_I`. For `|α| = deg H_I` it is a natural
number (`MvPolynomial.exists_multidegree_eq_natCast`), the degree of type `α` of `V(I)`. -/
noncomputable def multidegree (b : σ → ι) (I : Ideal (MvPolynomial σ K)) (α : ι →₀ ℕ) : ℚ :=
  (∏ i, ((α i).factorial : ℚ)) * (hilbertPoly b I).coeff α

theorem exists_multidegree_eq_natCast {b : σ → ι} (hb : Function.Surjective b)
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsWeightedHomogeneous (multiWeight b))
    {α : ι →₀ ℕ} (hα : (hilbertPoly b I).totalDegree ≤ α.degree) :
    ∃ n : ℕ, multidegree b I α = n := by
  obtain ⟨A, V, -, h⟩ := coeff_hilbertPoly_mul_factorial hb hI
  exact ⟨_, (mul_comm _ _).trans (h α hα)⟩

omit [DecidableEq ι] in
theorem prod_factorial_add_single (β : ι →₀ ℕ) (i : ι) :
    ∏ j, (((β + Finsupp.single i 1 : ι →₀ ℕ) j).factorial : ℚ) =
      (∏ j, ((β j).factorial : ℚ)) * (β i + 1) := by
  classical
  have : ∀ j, (((β + Finsupp.single i 1 : ι →₀ ℕ) j).factorial : ℚ) =
      ((β j).factorial : ℚ) * if j = i then (β i + 1 : ℚ) else 1 := by
    intro j
    by_cases hj : j = i
    · subst hj
      simp [Nat.factorial_succ, mul_comm]
    · simp [hj]
  rw [Finset.prod_congr rfl fun j _ ↦ this j, Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp

variable {J : Ideal (MvPolynomial σ K)} {b : σ → ι} {g : MvPolynomial σ K} {e : ι → ℕ}

/-- **The degrees of a section by a nonzerodivisor.** For a multihomogeneous ideal `J` and a
nonzero multihomogeneous `g` of multidegree `e` with `(J : g) = J`, in every degree
`|β| ≥ deg H_J - 1`: `d_β(J + (g)) = ∑ i, e i · d_{β + ε_i}(J)`. -/
theorem multidegree_sup_span_singleton_of_colon_eq (hb : Function.Surjective b)
    (hJ : J.IsWeightedHomogeneous (multiWeight b))
    (hg : IsWeightedHomogeneous (multiWeight b) g e) (hg0 : g ≠ 0) (hcol : J.colon {g} = J)
    {β : ι →₀ ℕ} (hβ : (hilbertPoly b J).totalDegree - 1 ≤ β.degree) :
    multidegree b (J ⊔ Ideal.span {g}) β =
      ∑ i, (e i : ℚ) * multidegree b J (β + Finsupp.single i 1) := by
  rw [multidegree, hilbertPoly_sup_span_singleton_of_colon_eq hb hJ hg hg0 hcol,
    coeff_sub_shiftPoly e _ hβ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [multidegree, prod_factorial_add_single]
  ring

omit [Fintype ι] in
/-- A section by a nonzerodivisor has dimension at most `dim V(J) - 1`. -/
theorem totalDegree_hilbertPoly_sup_span_singleton_le_of_colon_eq [Finite ι]
    (hb : Function.Surjective b) (hJ : J.IsWeightedHomogeneous (multiWeight b))
    (hg : IsWeightedHomogeneous (multiWeight b) g e) (hg0 : g ≠ 0) (hcol : J.colon {g} = J) :
    (hilbertPoly b (J ⊔ Ideal.span {g})).totalDegree ≤ (hilbertPoly b J).totalDegree - 1 := by
  have := Fintype.ofFinite ι
  rw [hilbertPoly_sup_span_singleton_of_colon_eq hb hJ hg hg0 hcol]
  exact totalDegree_sub_shiftPoly_le e _

omit [Fintype ι] in
/-- **A section by a nonzerodivisor drops the dimension by exactly one** when it has positive
degree in every block and `V(J)` has positive dimension. -/
theorem totalDegree_hilbertPoly_sup_span_singleton_of_colon_eq [Finite ι]
    (hb : Function.Surjective b) (hJ : J.IsWeightedHomogeneous (multiWeight b))
    (hg : IsWeightedHomogeneous (multiWeight b) g e) (hg0 : g ≠ 0) (hcol : J.colon {g} = J)
    (he : ∀ i, 0 < e i) (hpos : 1 ≤ (hilbertPoly b J).totalDegree) :
    (hilbertPoly b (J ⊔ Ideal.span {g})).totalDegree = (hilbertPoly b J).totalDegree - 1 := by
  have := Fintype.ofFinite ι
  refine le_antisymm
    (totalDegree_hilbertPoly_sup_span_singleton_le_of_colon_eq hb hJ hg hg0 hcol) ?_
  set H := hilbertPoly b J
  have hne : H.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    simp [totalDegree, h] at hpos
  obtain ⟨α, hα, hαdeg⟩ := Finset.exists_mem_eq_sup _ hne fun s ↦ s.sum fun _ e ↦ e
  have hαdeg' : α.degree = H.totalDegree := by
    rw [Finsupp.degree_apply, totalDegree, hαdeg]
    rfl
  have hαpos : 0 < H.coeff α :=
    lt_of_le_of_ne (coeff_hilbertPoly_nonneg hb hJ hαdeg'.ge) (mem_support_iff.mp hα).symm
  obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
    by_contra h
    push Not at h
    have : α = 0 := Finsupp.ext h
    rw [this, map_zero] at hαdeg'
    omega
  set β := α - Finsupp.single i 1
  have hβα : β + Finsupp.single i 1 = α :=
    tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi))
  have hβdeg : β.degree = H.totalDegree - 1 := by
    have := congrArg Finsupp.degree hβα
    rw [map_add, Finsupp.degree_single] at this
    omega
  have hcoeff := coeff_sub_shiftPoly e H (β := β) hβdeg.ge
  have hterm : ∀ j ∈ (univ : Finset ι),
      0 ≤ (e j : ℚ) * (H.coeff (β + Finsupp.single j 1) * (β j + 1)) := by
    intro j _
    refine mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (coeff_hilbertPoly_nonneg hb hJ
      (?_ : H.totalDegree ≤ _)) (by positivity))
    rw [map_add, Finsupp.degree_single, hβdeg]
    omega
  have hlt : 0 < (H - shiftPoly e H).coeff β := by
    rw [hcoeff]
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum hterm (Finset.mem_univ i))
    rw [hβα]
    exact mul_pos (Nat.cast_pos.mpr (he i)) (mul_pos hαpos (by positivity))
  rw [hilbertPoly_sup_span_singleton_of_colon_eq hb hJ hg hg0 hcol, ← hβdeg, Finsupp.degree_apply]
  exact le_totalDegree (mem_support_iff.mpr hlt.ne')


variable {𝔭 : Ideal (MvPolynomial σ K)} [𝔭.IsPrime]

/-- **The degrees of a hypersurface section** (Evertse 1995, Lemma 1(iv)). For a
multihomogeneous prime `𝔭` and a multihomogeneous `g ∉ 𝔭` of multidegree `e`, in every degree
`|β| ≥ deg H_𝔭 - 1`: `d_β(𝔭 + (g)) = ∑ i, e i · d_{β + ε_i}(𝔭)`. -/
theorem multidegree_sup_span_singleton_of_isPrime (hb : Function.Surjective b)
    (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b))
    (hg : IsWeightedHomogeneous (multiWeight b) g e) (hg𝔭 : g ∉ 𝔭) {β : ι →₀ ℕ}
    (hβ : (hilbertPoly b 𝔭).totalDegree - 1 ≤ β.degree) :
    multidegree b (𝔭 ⊔ Ideal.span {g}) β =
      ∑ i, (e i : ℚ) * multidegree b 𝔭 (β + Finsupp.single i 1) :=
  multidegree_sup_span_singleton_of_colon_eq hb h𝔭 hg (fun h ↦ hg𝔭 (h ▸ 𝔭.zero_mem))
    (Ideal.colon_singleton_eq_of_isPrime hg𝔭) hβ

omit [Fintype ι] in
/-- A hypersurface section of `V(𝔭)` has dimension at most `dim V(𝔭) - 1`. -/
theorem totalDegree_hilbertPoly_sup_span_singleton_le [Finite ι] (hb : Function.Surjective b)
    (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b))
    (hg : IsWeightedHomogeneous (multiWeight b) g e) (hg𝔭 : g ∉ 𝔭) :
    (hilbertPoly b (𝔭 ⊔ Ideal.span {g})).totalDegree ≤ (hilbertPoly b 𝔭).totalDegree - 1 :=
  totalDegree_hilbertPoly_sup_span_singleton_le_of_colon_eq hb h𝔭 hg
    (fun h ↦ hg𝔭 (h ▸ 𝔭.zero_mem)) (Ideal.colon_singleton_eq_of_isPrime hg𝔭)

omit [Fintype ι] in
/-- **A hypersurface section drops the dimension by exactly one.** If `g ∉ 𝔭` has positive
degree in every block and `V(𝔭)` has positive dimension, then
`dim V(𝔭 + (g)) = dim V(𝔭) - 1`. -/
theorem totalDegree_hilbertPoly_sup_span_singleton [Finite ι] (hb : Function.Surjective b)
    (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b))
    (hg : IsWeightedHomogeneous (multiWeight b) g e) (hg𝔭 : g ∉ 𝔭) (he : ∀ i, 0 < e i)
    (hpos : 1 ≤ (hilbertPoly b 𝔭).totalDegree) :
    (hilbertPoly b (𝔭 ⊔ Ideal.span {g})).totalDegree = (hilbertPoly b 𝔭).totalDegree - 1 :=
  totalDegree_hilbertPoly_sup_span_singleton_of_colon_eq hb h𝔭 hg
    (fun h ↦ hg𝔭 (h ▸ 𝔭.zero_mem)) (Ideal.colon_singleton_eq_of_isPrime hg𝔭) he hpos

end HilbertPolynomial

end MvPolynomial
