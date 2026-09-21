/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.BoxMonomial
public import DiophantineApproximation.CountingVolume
public import DiophantineApproximation.PolynomialIndex

/-!
# The vanishing conditions behind the index

"`P` has index at least `t` at `α` for the weights `d`" is a **finite system of linear
conditions** on the coefficients of `P`, once the partial degrees of `P` are bounded by `d`:
`∂_μ P` must vanish at `α` for every `μ` of weight `∑ j, μ j / d j < t`. This file turns the
index into that system and counts it.

Two things make the system finite. A derivative of an order that leaves the box vanishes
identically (`MvPolynomial.hasseDeriv_eq_zero_of_lt`), so only orders inside the box carry a
condition; and the orders inside the box of weight less than `t` are counted by Layer 2.5's
lattice-point comparison, since they are exactly the lattice points of
`MeasureTheory.latticePoints` with a strict inequality.

## Main results

* `MvPolynomial.eval_hasseDeriv_eq_sum`: the condition, as a linear form in the coefficients on
  the box, with `MvPolynomial.hasseDerivRow` for its row.
* `MvPolynomial.le_index_of_forall_eval_eq_zero`: the conditions imply the bound on the index.
* `MvPolynomial.card_boxOrder_le_card_latticePoints`: the number of conditions per point, by
  Layer 2.5.
* `MvPolynomial.degreeOf_map_le`: partial degrees do not grow under a ring homomorphism, which
  is what lets a polynomial over `K` be tested against points of an extension `F`.

## Implementation notes

⚠ **Only the orders inside the box carry a condition, and that is a theorem rather than a
convention.** The index is an infimum over *all* orders `μ`, and the ones with `μ j > d j` are
not in the coefficient space of the auxiliary polynomial. They need no condition:
`MvPolynomial.hasseDeriv_eq_zero_of_lt` says that a polynomial whose partial degree in `j` is at
most `d j` is killed by any derivative of order greater than `d j` in `j`. So the system imposed
by Layer 2.6 is indexed by the box and nothing is lost.

⚠ **The weight of an order is a `Finsupp.sum` in the definition of the index and a `Finset.sum`
in Layer 2.5's counting, and the two are the same number.** Off the support of `μ` the summand
`μ j / d j` is `0 / d j = 0`, so `Finsupp.sum_of_support_subset` moves the sum onto `univ` with
no hypothesis on `d` at all — not even that it is nonzero.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Definition 6.3.2 and Lemma 6.3.4.

This is part of Layer 2.6 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace MvPolynomial

/-! ### The conditions as linear forms -/

section Conditions

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {R : Type*} [CommRing R]

/-- **A Hasse derivative evaluated at a point is a linear form in the coefficients on the box**,
with `MvPolynomial.hasseDerivRow` for its row. -/
theorem eval_hasseDeriv_eq_sum {d : σ → ℕ} {Q : MvPolynomial σ R} (hQ : ∀ j, Q.degreeOf j ≤ d j)
    (α : σ → R) (μ : σ →₀ ℕ) :
    eval α (hasseDeriv μ Q)
      = ∑ I : (∀ j, Fin (d j + 1)), hasseDerivRow d α μ I * Q.coeff (boxMonomial d I) := by
  classical
  set w : (σ →₀ ℕ) → R := fun ν ↦
    ((μ.prod fun j k ↦ (ν j).choose k : ℕ) : R) * (∏ j, α j ^ (ν j - μ j)) * Q.coeff ν with hw
  have hL : eval α (hasseDeriv μ Q) = ∑ ν ∈ Q.support, w ν := by
    rw [hasseDeriv_apply, map_sum]
    refine Finset.sum_congr rfl fun ν _ ↦ ?_
    rw [eval_monomial, hw]
    have hprod : ((ν - μ).prod fun j e ↦ α j ^ e) = ∏ j, α j ^ (ν j - μ j) := by
      rw [Finsupp.prod_of_support_subset _ (Finset.subset_univ _) _ (by simp)]
      exact Finset.prod_congr rfl fun j _ ↦ by rw [Finsupp.tsub_apply]
    rw [hprod]
    ring
  have hR : ∑ I : (∀ j, Fin (d j + 1)), w (boxMonomial d I) = ∑ ν ∈ Q.support, w ν := by
    rw [← Finset.sum_image (g := boxMonomial d) (f := w) fun a _ b _ h ↦ boxMonomial_injective h]
    refine (Finset.sum_subset (fun ν hν ↦ ?_) fun ν _ hν ↦ ?_).symm
    · obtain ⟨I, rfl⟩ := mem_range_boxMonomial_of_mem_support hQ hν
      exact Finset.mem_image.mpr ⟨I, Finset.mem_univ I, rfl⟩
    · simp [hw, notMem_support_iff.mp hν]
  rw [hL, ← hR]
  refine Finset.sum_congr rfl fun I _ ↦ ?_
  rw [hw, hasseDerivRow]
  simp only [boxMonomial_apply]

omit [Fintype σ] [DecidableEq σ] in
/-- **Partial degrees do not grow under a ring homomorphism.** -/
theorem degreeOf_map_le {S : Type*} [CommRing S] (f : R →+* S) (P : MvPolynomial σ R) (j : σ) :
    (P.map f).degreeOf j ≤ P.degreeOf j := by
  rw [degreeOf_le_iff]
  exact fun ν hν ↦ degreeOf_le_iff.mp le_rfl ν (support_map_subset f P hν)

end Conditions

/-! ### From the conditions to the index -/

section Index

variable {σ : Type*} {R : Type*} [CommRing R]

/-- **The conditions imply the bound on the index**: if every Hasse derivative of weight less
than `t` vanishes at `α`, then the index of `P` at `α` is at least `t`. -/
theorem le_index_of_forall_eval_eq_zero (d : σ → ℝ) (α : σ → R) (P : MvPolynomial σ R) {t : ℝ}
    (h : ∀ μ : σ →₀ ℕ, (μ.sum fun j k ↦ (k : ℝ) / d j) < t → eval α (hasseDeriv μ P) = 0) :
    ENNReal.ofReal t ≤ index d α P :=
  le_index d fun μ hμ ↦ ENNReal.ofReal_le_ofReal (not_lt.mp fun hlt ↦ hμ (h μ hlt))

end Index

/-! ### Counting the conditions -/

section Counting

open MeasureTheory

variable {m : ℕ}

/-- The weight of an order of the box, as a sum over all the variables. -/
theorem sum_weight_boxMonomial (d : Fin m → ℕ) (I : ∀ j, Fin (d j + 1)) :
    ((boxMonomial d I).sum fun j k ↦ (k : ℝ) / (d j : ℝ))
      = ∑ j, ((I j : ℕ) : ℝ) / (d j : ℝ) := by
  rw [Finsupp.sum_of_support_subset _ (Finset.subset_univ _) _ (by simp)]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [boxMonomial_apply]

/-- **The conditions attached to one point are counted by Layer 2.5.** -/
theorem card_boxOrder_le_card_latticePoints (d : Fin m → ℕ) (t : ℝ) :
    Fintype.card {I : ∀ j, Fin (d j + 1) // ∑ j, ((I j : ℕ) : ℝ) / (d j : ℝ) < t}
      ≤ (latticePoints d t).card := by
  classical
  rw [← Finset.card_univ]
  refine Finset.card_le_card_of_injOn (fun I ↦ fun j ↦ ((I : ∀ j, Fin (d j + 1)) j : ℕ))
    (fun I _ ↦ mem_latticePoints.mpr ⟨fun j ↦ Nat.lt_succ_iff.mp (I.1 j).isLt, I.2.le⟩)
    fun I _ J _ h ↦ Subtype.ext (funext fun j ↦ Fin.ext (congrFun h j))

end Counting

/-! ### Acceptance criteria -/

section Acceptance

/-- **Acceptance test: the condition of order `0` is evaluation.** The system of Lemma 6.3.4
begins with "`P` vanishes at `α`", and this is that row read back. -/
example {σ : Type*} [Fintype σ] [DecidableEq σ] {R : Type*} [CommRing R] {d : σ → ℕ}
    {Q : MvPolynomial σ R} (hQ : ∀ j, Q.degreeOf j ≤ d j) (α : σ → R) :
    eval α Q
      = ∑ I : (∀ j, Fin (d j + 1)), (∏ j, α j ^ (I j : ℕ)) * Q.coeff (boxMonomial d I) := by
  have h := eval_hasseDeriv_eq_sum hQ α 0
  rw [hasseDeriv_zero_apply] at h
  rw [h]
  exact Finset.sum_congr rfl fun I _ ↦ by simp [hasseDerivRow]

/-- **Acceptance test: an order that leaves the box carries no condition.** -/
example {σ : Type*} {R : Type*} [CommRing R] {d : σ → ℕ} {Q : MvPolynomial σ R}
    (hQ : ∀ j, Q.degreeOf j ≤ d j) {μ : σ →₀ ℕ} {j : σ} (hj : d j < μ j) (α : σ → R) :
    eval α (hasseDeriv μ Q) = 0 := by
  rw [hasseDeriv_eq_zero_of_lt (lt_of_le_of_lt (hQ j) hj), map_zero]

end Acceptance

end MvPolynomial

end
