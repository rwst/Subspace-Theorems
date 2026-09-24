/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.FormIndex
public import DiophantineApproximation.SmallPoint

/-!
# From the index along the forms to a derivative surviving on the product

Layer 5.3 bounds the **index** of the auxiliary polynomial along the forms `M h` cutting out the
subspaces `V(Q h)`, and Layer 5.5 asks for a Hasse derivative `∂_I P` of small order that does
**not vanish identically** on the product `V(Q 1) × ⋯ × V(Q m)`. This file is the bridge between
the two, Bombieri–Gubler's "it follows that there is `I` with `(I/d) ≤ m η / 2` such that `∂_I P`
does not vanish identically on the product space" at the end of 7.5.22.

The two statements live in different coordinate systems. The index is the weighted order of `P`
read in the coordinates in which the forms are variables
(`MvPolynomial.formIndex_eq_weightedOrder`),
and counts only the exponents of those variables; the nonvanishing is about Hasse derivatives
in the *original* coordinates, whose order is counted in all of them. Passing between the two is
the chain rule for a linear substitution — and, as in Layers 5.2 and 5.5, it is not needed. The
change of coordinates is itself a block-wise linear parametrization
(`MvPolynomial.substFormInv_eq_linSubst`), so the shift commutes with it, and
`MvPolynomial.exists_coeff_ne_zero_of_coeff_linSubst_ne_zero` turns a surviving coefficient in
one system into a surviving coefficient in the other **with the same degree in every block**.
Since the two orders are then equal block by block, they have the same weighted order, and that
is all the argument uses.

## Main definitions

* `MvPolynomial.zeroCoords`: setting a set of variables to zero.
* `MvPolynomial.formCoordInv`: the matrix of `MvPolynomial.substFormInv`.

## Main results

* `MvPolynomial.exists_eval_ne_zero_of_coeff_ne_zero`: a polynomial with a monomial avoiding a
  set of variables does not vanish identically on the coordinate subspace they cut out.
* `MvPolynomial.substFormInv_eq_linSubst`: **the change of coordinates is a parametrization**.
* `MvPolynomial.exists_linSubst_hasseDeriv_ne_zero_of_formIndex_le`: **the bridge.** If the index
  of `P` along the forms is at most `t ≥ 0`, then some Hasse derivative of `P` of block-weighted
  order at most `t` does not vanish identically on the product of the spans.

## Implementation notes

⚠ **The transverse part of a monomial is its own derivative order.** The monomial `ν` of the
transformed polynomial realizing the index is differentiated exactly along the variables that the
index sees, `J := ν.filter (fun p ↦ p.2 = i₀ p.1)`; the binomial factor of that Hasse derivative
is a product of `Nat.choose (ν p) (ν p)` and `Nat.choose (ν p) 0`, so it is `1` and no
characteristic hypothesis is needed. What *is* needed is that `K` be infinite, to pass from a
nonzero polynomial to a point where it does not vanish.

⚠ **The hypothesis `0 ≤ t` is not decoration.** For `t < 0` the bound `formIndex ≤ ENNReal.ofReal t`
reads `formIndex = 0`, which every nonzero polynomial satisfies, while the conclusion asks for a
nonnegative sum to be at most `t`; the statement is false there and true, as stated, everywhere
the caller uses it.

⚠ **The spanning hypothesis is one-sided.** The family `y h` has only to *span* the kernel of
`M h`; it need not be a basis, and the parameter type `ρ` is unrelated to `ι`. Layer 5.6 feeds it
a basis drawn from the approximation domain, which is what makes the point it produces small.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
7.5.22 and 7.5.23.

This is part of Layer 5.6 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

noncomputable section

open Finset

open scoped ENNReal

namespace MvPolynomial

section ZeroCoords

variable {σ K : Type*} [Field K] {s : σ → Prop} [DecidablePred s]

/-- Setting the variables in `s` to zero. -/
def zeroCoords (s : σ → Prop) [DecidablePred s] :
    MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
  aeval fun j ↦ if s j then 0 else X j

theorem zeroCoords_monomial_of_forall {ν : σ →₀ ℕ} (hν : ∀ j, s j → ν j = 0) (a : K) :
    zeroCoords s (monomial ν a) = monomial ν a := by
  rw [zeroCoords, aeval_monomial, MvPolynomial.algebraMap_eq, monomial_eq]
  refine congrArg (fun q ↦ C a * q) (Finsupp.prod_congr fun j hj ↦ ?_)
  have hsj : ¬ s j := fun h ↦ (Finsupp.mem_support_iff.mp hj) (hν j h)
  simp only [hsj, ite_false]

theorem zeroCoords_monomial_of_exists {ν : σ →₀ ℕ} {j : σ} (hj : s j) (hν : ν j ≠ 0) (a : K) :
    zeroCoords s (monomial ν a) = 0 := by
  rw [zeroCoords, aeval_monomial]
  refine mul_eq_zero_of_right _ ?_
  refine Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hν) ?_
  simp only [hj, ite_true]
  exact zero_pow hν

theorem coeff_zeroCoords (P : MvPolynomial σ K) {μ : σ →₀ ℕ} (hμ : ∀ j, s j → μ j = 0) :
    (zeroCoords s P).coeff μ = P.coeff μ := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [map_sum, coeff_sum]
  rw [Finset.sum_eq_single μ]
  · by_cases hm : μ ∈ P.support
    · rw [zeroCoords_monomial_of_forall hμ, coeff_monomial, ite_eq_left rfl]
    · rw [notMem_support_iff.mp hm]
      simp
  · intro ν _ hne
    by_cases hall : ∀ j, s j → ν j = 0
    · rw [zeroCoords_monomial_of_forall hall, coeff_monomial, ite_eq_right hne]
    · push Not at hall
      obtain ⟨j, hj, hjν⟩ := hall
      rw [zeroCoords_monomial_of_exists hj hjν]
      simp
  · intro hm
    rw [notMem_support_iff.mp hm]
    simp

theorem eval_zeroCoords (u : σ → K) (P : MvPolynomial σ K) :
    eval u (zeroCoords s P) = eval (fun j ↦ if s j then 0 else u j) P := by
  have key : ((aeval u : MvPolynomial σ K →ₐ[K] K).comp (zeroCoords s))
      = aeval (fun j ↦ if s j then (0 : K) else u j) := by
    refine MvPolynomial.algHom_ext fun j ↦ ?_
    rw [AlgHom.comp_apply, zeroCoords, aeval_X, aeval_X]
    by_cases h : s j <;> simp [h]
  have h2 := congrArg (fun f ↦ f P) key
  simpa [aeval_eq_eval] using h2

variable [Infinite K]

omit [DecidablePred s] in
/-- **A polynomial with a monomial avoiding the variables of `s` does not vanish identically on
the coordinate subspace they cut out.** -/
theorem exists_eval_ne_zero_of_coeff_ne_zero {P : MvPolynomial σ K} {μ : σ →₀ ℕ}
    (hμ : ∀ j, s j → μ j = 0) (hcoeff : P.coeff μ ≠ 0) :
    ∃ w : σ → K, (∀ j, s j → w j = 0) ∧ eval w P ≠ 0 := by
  classical
  have hne : zeroCoords s P ≠ 0 := fun h ↦ hcoeff (by rw [← coeff_zeroCoords P hμ, h]; simp)
  have : ∃ u : σ → K, eval u (zeroCoords s P) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hne (MvPolynomial.funext fun u ↦ by rw [hc u, map_zero])
  obtain ⟨u, hu⟩ := this
  refine ⟨fun j ↦ if s j then 0 else u j, fun j hj ↦ by simp only [hj, ite_true], ?_⟩
  rwa [eval_zeroCoords] at hu

end ZeroCoords

section FormCoord

variable {K κ ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- The matrix of `MvPolynomial.substFormInv`: the `l`-th coordinate of the image of the `i`-th
basis vector of the block. -/
def formCoordInv (i₀ : κ → ι) (M : κ → ι → K) (h : κ) (l i : ι) : K :=
  if i = i₀ h then (M h (i₀ h))⁻¹ * (if l = i₀ h then 1 else -(M h l))
  else if l = i then 1 else 0

omit [Fintype ι] in
theorem formCoordInv_of_eq (i₀ : κ → ι) (M : κ → ι → K) (h : κ) (l : ι) :
    formCoordInv i₀ M h l (i₀ h) = (M h (i₀ h))⁻¹ * (if l = i₀ h then 1 else -(M h l)) := by
  simp [formCoordInv]

omit [Fintype ι] in
theorem formCoordInv_of_ne (i₀ : κ → ι) (M : κ → ι → K) (h : κ) (l : ι) {i : ι}
    (hi : i ≠ i₀ h) : formCoordInv i₀ M h l i = if l = i then 1 else 0 := by
  simp [formCoordInv, hi]

/-- **The inverse change of coordinates is a block-wise linear parametrization.** -/
theorem substFormInv_eq_linSubst (i₀ : κ → ι) (M : κ → ι → K) :
    substFormInv i₀ M = linSubst (formCoordInv i₀ M) := by
  refine MvPolynomial.algHom_ext fun p ↦ ?_
  obtain ⟨h, i⟩ := p
  rw [linSubst_X]
  rcases eq_or_ne i (i₀ h) with rfl | hi
  · rw [substFormInv_X_self, ← Finset.add_sum_erase _ _ (Finset.mem_univ (i₀ h))]
    have hsum : ∑ l ∈ univ.erase (i₀ h), C (formCoordInv i₀ M h l (i₀ h)) * X ((h, l) : κ × ι)
        = -(C (M h (i₀ h))⁻¹ * ∑ i ∈ univ.erase (i₀ h), C (M h i) * X ((h, i) : κ × ι)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun l hl ↦ ?_
      have hl' : l ≠ i₀ h := (Finset.mem_erase.mp hl).1
      rw [formCoordInv_of_eq]
      simp only [hl', ite_false, C_mul, C_neg]
      ring
    rw [hsum, formCoordInv_of_eq, ite_eq_left (rfl : i₀ h = i₀ h), mul_one]
    ring
  · rw [substFormInv_X_of_ne i₀ M hi, Finset.sum_eq_single i]
    · rw [formCoordInv_of_ne i₀ M h i hi, ite_eq_left (rfl : i = i), C_1, one_mul]
    · intro l _ hl
      rw [formCoordInv_of_ne i₀ M h l hi, ite_eq_right hl, C_0, zero_mul]
    · intro hc
      exact absurd (Finset.mem_univ i) hc

end FormCoord

section Bridge

variable {K κ ι ρ : Type*} [Field K] [Infinite K] [Fintype κ] [Fintype ι] [DecidableEq ι]
  [Fintype ρ]

omit [DecidableEq ι] in
/-- **From the index along the forms to a derivative that survives on the product of the
kernels.** -/
theorem exists_linSubst_hasseDeriv_ne_zero_of_formIndex_le
    {d : κ → ℝ} (hd : ∀ h, 0 ≤ d h) {M : κ → ι → K} (hM : ∀ h, M h ≠ 0)
    {y : κ → ρ → ι → K}
    (hy : ∀ (h : κ) (x : ι → K), ∑ i, M h i * x i = 0 →
      x ∈ Submodule.span K (Set.range (y h)))
    {P : MvPolynomial (κ × ι) K} (hP : P ≠ 0) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : formIndex d M P ≤ ENNReal.ofReal t) :
    ∃ I : κ × ι →₀ ℕ, ∑ h, (∑ i, (I (h, i) : ℝ)) / d h ≤ t ∧
      linSubst y (hasseDeriv I P) ≠ 0 := by
  classical
  obtain ⟨i₀, hi₀⟩ := exists_forall_apply_ne_zero hM
  set Q := substFormInv i₀ M P with hQdef
  have hQ0 : Q ≠ 0 := fun h ↦ hP (substFormInv_injective hi₀ (by rw [hQdef] at h; rw [h, map_zero]))
  obtain ⟨ν, hν, hweq⟩ := exists_coeff_ne_zero_weightedOrder_eq (formWeight i₀ d) hQ0
  have hνt : ∑ h, (ν (h, i₀ h) : ℝ) / d h ≤ t := by
    have h1 : ENNReal.ofReal (∑ h, (ν (h, i₀ h) : ℝ) / d h) ≤ ENNReal.ofReal t := by
      rw [← weight_formWeight hd i₀ ν, ← hweq, ← formIndex_eq_weightedOrder hd hi₀ P]
      exact ht
    exact (ENNReal.ofReal_le_ofReal_iff ht0).mp h1
  set J : κ × ι →₀ ℕ := ν.filter (fun p ↦ p.2 = i₀ p.1) with hJdef
  have hJapply : ∀ p : κ × ι, J p = if p.2 = i₀ p.1 then ν p else 0 := fun p ↦ by
    rw [hJdef, Finsupp.filter_apply]
  have hJle : J ≤ ν := by
    rw [Finsupp.le_def]
    intro p
    rw [hJapply p]
    split
    · exact le_rfl
    · exact Nat.zero_le _
  have hJsum : ∀ h : κ, ∑ i, J (h, i) = ν (h, i₀ h) := fun h ↦ by
    rw [Finset.sum_eq_single (i₀ h)]
    · rw [hJapply, ite_eq_left (rfl : i₀ h = i₀ h)]
    · intro i _ hi
      rw [hJapply, ite_eq_right hi]
    · intro hc
      exact absurd (Finset.mem_univ (i₀ h)) hc
  have hsub0 : ∀ p : κ × ι, p.2 = i₀ p.1 → (ν - J) p = 0 := fun p hp ↦ by
    rw [Finsupp.tsub_apply, hJapply p, ite_eq_left hp, Nat.sub_self]
  have hcoeff : (hasseDeriv J Q).coeff (ν - J) ≠ 0 := by
    rw [hasseDeriv_coeff, tsub_add_cancel_of_le hJle]
    have hone : (J.prod fun j k ↦ ((ν - J) j + k).choose k) = 1 := by
      rw [Finsupp.prod]
      refine Finset.prod_eq_one fun j hj ↦ ?_
      have hjne : J j ≠ 0 := Finsupp.mem_support_iff.mp hj
      have hjp : j.2 = i₀ j.1 := by
        by_contra hc
        exact hjne (by rw [hJapply j, ite_eq_right hc])
      rw [hsub0 j hjp, Nat.zero_add, Nat.choose_self]
    rw [hone, Nat.cast_one, one_mul]
    exact hν
  obtain ⟨w', hw'0, hw'⟩ :=
    exists_eval_ne_zero_of_coeff_ne_zero (s := fun p : κ × ι ↦ p.2 = i₀ p.1)
      (P := hasseDeriv J Q) hsub0 hcoeff
  have hshift : (shift w' Q).coeff J ≠ 0 := by rw [coeff_shift]; exact hw'
  set pt : κ × ι → K := fun p ↦ ∑ l, w' (p.1, l) * formCoordInv i₀ M p.1 l p.2 with hptdef
  have hsl : shift w' Q = linSubst (formCoordInv i₀ M) (shift pt P) := by
    rw [hQdef, substFormInv_eq_linSubst, shift_linSubst]
  obtain ⟨I, hI, hIdeg⟩ :=
    exists_coeff_ne_zero_of_coeff_linSubst_ne_zero (formCoordInv i₀ M) (shift pt P)
      (by rw [← hsl]; exact hshift)
  refine ⟨I, ?_, ?_⟩
  · refine le_trans (le_of_eq (Finset.sum_congr rfl fun h _ ↦ ?_)) hνt
    congr 1
    rw [← Nat.cast_sum, ← hIdeg h, hJsum h]
  · have hev : eval pt (hasseDeriv I P) ≠ 0 := by rw [← coeff_shift]; exact hI
    have hker : ∀ h : κ, ∑ i, M h i * pt (h, i) = 0 := by
      intro h
      have h1 : eval pt (blockForm M h) = eval w' (substFormInv i₀ M (blockForm M h)) := by
        rw [substFormInv_eq_linSubst, eval_linSubst]
      rw [substFormInv_blockForm hi₀] at h1
      have h2 : eval pt (blockForm M h) = ∑ i, M h i * pt (h, i) := by
        rw [blockForm, map_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by rw [map_mul, eval_C, eval_X]
      rw [h2] at h1
      rw [h1, eval_X, hw'0 (h, i₀ h) rfl]
    have hmem : ∀ h : κ, ∃ u : ρ → K, ∀ i, ∑ l, u l * y h l i = pt (h, i) := by
      intro h
      obtain ⟨u, hu⟩ := Submodule.mem_span_range_iff_exists_fun K |>.mp
        (hy h (fun i ↦ pt (h, i)) (hker h))
      refine ⟨u, fun i ↦ ?_⟩
      have := congrFun hu i
      simpa using this
    choose u hu using hmem
    intro hzero
    have h3 := eval_linSubst y (fun p : κ × ρ ↦ u p.1 p.2) (hasseDeriv I P)
    rw [hzero, map_zero] at h3
    exact hev (by simpa [hu] using h3.symm)

end Bridge

end MvPolynomial



end

end
