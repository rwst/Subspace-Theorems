/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.BoxMonomial
public import DiophantineApproximation.PolynomialIndex

/-!
# The index under renaming, and the index of a sum, a product and a determinant

Roth's lemma factors a polynomial in `m + 1` variables through two polynomials in disjoint
variable sets: a generalized Wronskian in the first `m` variables and one in the last. Both come
back into `MvPolynomial (Fin (m + 1)) K` along `MvPolynomial.rename`, and the induction is
applied to them *before* the renaming. This file is the dictionary: a Hasse derivative commutes
with an injective renaming, and so does the index.

It also collects the three shapes of the index that the determinant of a matrix of derivatives
needs — a finite sum, a finite product and the bound `index ≤ card σ` that says a polynomial of
partial degrees at most `d` cannot vanish to weighted order more than the number of variables.

## Main results

* `MvPolynomial.hasseDeriv_rename`: `∂_(mapDomain e μ) (rename e P) = rename e (∂_μ P)`.
* `MvPolynomial.hasseDeriv_rename_eq_zero`: an order that is not carried by `e` kills a renamed
  polynomial, and `MvPolynomial.degreeOf_rename_eq_zero`: a variable outside the range does not
  occur.
* `MvPolynomial.index_rename`: the index of a renamed polynomial, against renamed weights and a
  renamed point.
* `MvPolynomial.le_index_sum` and `MvPolynomial.index_prod`: the valuation properties of Layer
  2.3 over a `Finset`.
* `MvPolynomial.index_le_card`: with `degreeOf j P ≤ d j` the index is at most the number of
  variables.

## Implementation notes

⚠ **The bound `index ≤ card σ` is a statement about the *translate*, and it needs Layer 2.6's
`MvPolynomial.hasseDeriv_eq_zero_of_lt` rather than a degree bound on `MvPolynomial.taylorAt`.**
A monomial `μ` occurring in the translate has `coeff μ (taylorAt α P) = eval α (∂_μ P)`, and the
right-hand side vanishes as soon as `μ j` exceeds `degreeOf j P` in one variable. So the support
of the translate lies in the same box as the support of `P`, with no statement about the degrees
of `taylorAt α P` proved along the way.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Definition 6.3.2 and Lemma 6.3.7.

This is part of Layer 2.7 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Finsupp Function

open scoped ENNReal

namespace MvPolynomial

/-! ### Hasse derivatives and renaming -/

section Rename

variable {σ τ R : Type*} [CommSemiring R] {e : σ → τ}

omit [CommSemiring R] in
/-- An exponent whose support is not carried by `e` has a coordinate off the range of `e`. -/
theorem exists_ne_zero_notMem_range {n : τ →₀ ℕ}
    (hn : ¬ ((n.support : Set τ) ⊆ Set.range e)) : ∃ j, n j ≠ 0 ∧ j ∉ Set.range e := by
  by_contra h
  refine hn fun j hj ↦ ?_
  by_contra hjr
  exact h ⟨j, Finsupp.mem_support_iff.mp (Finset.mem_coe.mp hj), hjr⟩

/-- A coefficient of a renamed polynomial vanishes unless its exponent is carried by `e`. -/
theorem coeff_rename_eq_zero_of_not_subset {P : MvPolynomial σ R} {n : τ →₀ ℕ}
    (hn : ¬ ((n.support : Set τ) ⊆ Set.range e)) : (rename e P).coeff n = 0 := by
  classical
  refine coeff_rename_eq_zero _ _ _ fun u hu ↦ absurd (fun t ht ↦ ?_) hn
  rw [← hu] at ht
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp (mapDomain_support (Finset.mem_coe.mp ht))
  exact ⟨a, rfl⟩

/-- **A Hasse derivative commutes with an injective renaming**, once the order is renamed too. -/
theorem hasseDeriv_rename (he : Injective e) (μ : σ →₀ ℕ) (P : MvPolynomial σ R) :
    hasseDeriv (μ.mapDomain e) (rename e P) = rename e (hasseDeriv μ P) := by
  classical
  refine MvPolynomial.ext _ _ fun n ↦ ?_
  by_cases hn : (n.support : Set τ) ⊆ Set.range e
  · obtain ⟨n', rfl⟩ : ∃ n' : σ →₀ ℕ, n'.mapDomain e = n :=
      ⟨comapDomain e n (he.injOn), mapDomain_comapDomain e he n hn⟩
    rw [hasseDeriv_coeff, coeff_rename_mapDomain _ he, hasseDeriv_coeff,
      ← mapDomain_add, coeff_rename_mapDomain _ he]
    congr 1
    rw [Finsupp.prod_mapDomain_index_inj he]
    exact congrArg _ (Finsupp.prod_congr fun j _ ↦
      congrArg (fun t ↦ (t + μ j).choose (μ j)) (Finsupp.mapDomain_apply_of_injective he n' j))
  · obtain ⟨j, hj, hjr⟩ := exists_ne_zero_notMem_range hn
    have hns : ¬ (((n + μ.mapDomain e).support : Set τ) ⊆ Set.range e) := fun hs ↦
      hjr (hs (by simp only [Finset.mem_coe, Finsupp.mem_support_iff, Finsupp.add_apply]; omega))
    rw [hasseDeriv_coeff, coeff_rename_eq_zero_of_not_subset hns, mul_zero,
      coeff_rename_eq_zero_of_not_subset hn]

/-- **A variable outside the range of the renaming does not occur in a renamed polynomial.** -/
theorem degreeOf_rename_eq_zero {j : τ} (hj : j ∉ Set.range e) (P : MvPolynomial σ R) :
    (rename e P).degreeOf j = 0 := by
  rw [← Nat.le_zero, degreeOf_le_iff]
  intro ν hν
  by_contra hc
  refine absurd ?_ hj
  have hsub : (ν.support : Set τ) ⊆ Set.range e := by
    by_contra hs
    exact absurd (coeff_rename_eq_zero_of_not_subset hs) (mem_support_iff.mp hν)
  exact hsub (Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr (by omega)))

/-- **An order not carried by `e` kills a renamed polynomial.** -/
theorem hasseDeriv_rename_eq_zero {ρ : τ →₀ ℕ} {j : τ} (hj : ρ j ≠ 0) (hrange : j ∉ Set.range e)
    (P : MvPolynomial σ R) : hasseDeriv ρ (rename e P) = 0 := by
  refine MvPolynomial.ext _ _ fun n ↦ ?_
  have hns : ¬ (((n + ρ).support : Set τ) ⊆ Set.range e) := fun hs ↦
    hrange (hs (by simp only [Finset.mem_coe, Finsupp.mem_support_iff, Finsupp.add_apply]; omega))
  rw [hasseDeriv_coeff, coeff_rename_eq_zero_of_not_subset hns, mul_zero]
  simp

end Rename

/-! ### The index under renaming -/

section IndexRename

variable {σ τ R : Type*} [CommRing R] {e : σ → τ}

omit [CommRing R] in
/-- The weight of a renamed order against the original weights. -/
theorem sum_mapDomain_div (he : Injective e) (d : τ → ℝ) (μ : σ →₀ ℕ) :
    ((μ.mapDomain e).sum fun j k ↦ (k : ℝ) / d j) = μ.sum fun j k ↦ (k : ℝ) / d (e j) :=
  sum_mapDomain_index_inj he

/-- **The index of a renamed polynomial.** -/
theorem index_rename (he : Injective e) (d : τ → ℝ) (ξ : τ → R) (Q : MvPolynomial σ R) :
    index d ξ (rename e Q) = index (fun j ↦ d (e j)) (fun j ↦ ξ (e j)) Q := by
  classical
  refine le_antisymm (le_iInf fun μ ↦ le_iInf fun hμ ↦ ?_) (le_index d fun ρ hρ ↦ ?_)
  · refine le_of_le_of_eq (index_le d (μ := μ.mapDomain e) ?_) (by rw [sum_mapDomain_div he])
    rwa [hasseDeriv_rename he, eval_rename]
  · by_cases hs : (ρ.support : Set τ) ⊆ Set.range e
    · obtain ⟨μ, rfl⟩ : ∃ μ : σ →₀ ℕ, μ.mapDomain e = ρ :=
        ⟨comapDomain e ρ (he.injOn), mapDomain_comapDomain e he ρ hs⟩
      rw [sum_mapDomain_div he]
      refine index_le (fun j ↦ d (e j)) ?_
      rwa [hasseDeriv_rename he, eval_rename] at hρ
    · obtain ⟨j, hj, hjr⟩ := exists_ne_zero_notMem_range hs
      exact absurd (by rw [hasseDeriv_rename_eq_zero hj hjr, map_zero]) hρ

end IndexRename

/-! ### The index of a sum, a product and a determinant -/

section Shapes

variable {σ R : Type*} [CommRing R] (d : σ → ℝ)

/-- The index is unchanged by a sign. -/
theorem index_neg (α : σ → R) (P : MvPolynomial σ R) : index d α (-P) = index d α P := by
  have h : ∀ Q : MvPolynomial σ R, index d α (-Q) ≤ index d α Q := fun Q ↦
    le_index d fun μ hμ ↦ index_le d (μ := μ)
      (by rw [map_neg, map_neg]; exact neg_ne_zero.mpr hμ)
  refine le_antisymm (h P) ?_
  have hb := h (-P)
  rwa [neg_neg] at hb

/-- **The ultrametric inequality over a `Finset`.** -/
theorem le_index_sum (hd : ∀ j, 0 ≤ d j) (α : σ → R) {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial σ R) {c : ℝ≥0∞} (h : ∀ a ∈ s, c ≤ index d α (f a)) :
    c ≤ index d α (∑ a ∈ s, f a) := by
  classical
  induction s using Finset.induction with
  | empty => simp [index_zero, le_top]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      refine le_trans (le_min (h a (Finset.mem_insert_self a s))
        (ih fun b hb ↦ h b (Finset.mem_insert_of_mem hb)))
        (le_index_add d hd α _ _)

/-- **The index of a finite product is the sum of the indices.** -/
theorem index_prod [NoZeroDivisors R] [Nontrivial R] (hd : ∀ j, 0 ≤ d j) (α : σ → R)
    {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial σ R) :
    index d α (∏ a ∈ s, f a) = ∑ a ∈ s, index d α (f a) := by
  classical
  induction s using Finset.induction with
  | empty => simp [index_eq_weightedOrder d hd, map_one, weightedOrder_one]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, index_mul d hd, ih]

end Shapes

/-! ### The index is at most the number of variables -/

section Card

variable {σ R : Type*} [Fintype σ] [CommRing R] {d : σ → ℝ}

/-- **A polynomial of partial degrees at most `d` has index at most the number of variables.**
The bound is what keeps the conclusion of Roth's lemma non-vacuous once the parameter `σ` of the
lemma is close to `1`. -/
theorem index_le_card (hd : ∀ j, 0 < d j) {P : MvPolynomial σ R} (hP : P ≠ 0)
    (hdeg : ∀ j, (P.degreeOf j : ℝ) ≤ d j) (α : σ → R) :
    index d α P ≤ (Fintype.card σ : ℝ≥0∞) := by
  classical
  have ht : taylorAt α P ≠ 0 := fun h ↦ hP (taylorAt_eq_zero_iff.mp h)
  obtain ⟨μ, hμ⟩ : ∃ μ, (taylorAt α P).coeff μ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact ht (MvPolynomial.ext _ _ fun ν ↦ by simp [hc ν])
  have hne : eval α (hasseDeriv μ P) ≠ 0 := by rwa [← coeff_taylorAt]
  have hbound : ∀ j, (μ j : ℝ) ≤ d j := fun j ↦ by
    by_contra hlt
    exact hne (by rw [hasseDeriv_eq_zero_of_lt (j := j)
      (by exact_mod_cast lt_of_le_of_lt (hdeg j) (not_le.mp hlt)), map_zero])
  refine le_trans (index_le d hne) ?_
  rw [← ENNReal.ofReal_natCast]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (μ.sum fun j k ↦ (k : ℝ) / d j) = ∑ j ∈ μ.support, (μ j : ℝ) / d j := rfl
    _ ≤ ∑ _j ∈ μ.support, (1 : ℝ) :=
        Finset.sum_le_sum fun j _ ↦ (div_le_one (hd j)).mpr (hbound j)
    _ ≤ (Fintype.card σ : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        exact_mod_cast Finset.card_le_univ μ.support

end Card

end MvPolynomial
