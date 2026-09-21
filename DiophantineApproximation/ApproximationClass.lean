/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Card

/-!
# Approximation classes

**Mahler's reduction** (Bombieri–Gubler 6.4.2–6.4.4) sorts the solutions of a Diophantine
inequality by *where* they are well approximated, so that the ones that are left behave alike at
every place. It is a partition of a set into finitely many classes, and nothing in it is about
places, heights or number fields: a family of maps `φ a : X → ℝ` whose values are nonnegative and
sum to at most `1` sends a point of `X` to a point of the unit simplex, the simplex is cut into
half-open cells of side `1/N`, and two points lie in the same class when they land in the same
cell.

Three statements come out of it, and Layers 3.2, 3.7 and 5.1 each use them for a different `φ`.

*The classes are finitely many.* A cell that meets the simplex carries a label `c : A → ℕ` with
`∑ a, c a ≤ N`, and there are `(N + |A|).choose |A|` of those — the book's Lemma 6.4.3. Only the
count of Layer 3.7 needs the exact value; the proof of Roth's theorem needs finiteness alone.

*An infinite set has an infinite class.* Pigeonhole, and the reason the reduction is allowed.

*The class pins every coordinate at once.* For a family `f` of numbers in `(0, 1]` whose product
is `< 1`, the profile `log (f a) / log (∏ b, f b)` is a point of the simplex, and the cell
containing it traps each `f a` between two powers of that product — the book's (6.9). This is
what a consumer wants: `|A|` unrelated quantities are replaced by one quantity raised to `|A|`
exponents, each known to within `1/N`.

## Main results

* `Set.ncard_setOf_sum_le`: **Lemma 6.4.3**, the number of labels, `(N + |A|).choose |A|`.
* `Set.Infinite.exists_cellIndex_eq`: an infinite set has an infinite approximation class.
* `Real.le_rpow_cellIndex_div` and `Real.rpow_cellIndex_add_one_div_lt`: the two halves of (6.9).
* `Real.one_sub_card_div_lt_sum_cellIndex_div`: the book's (6.10), the lower bound on the label of
  a cell whose point lies *on* the hyperplane `∑ a, y a = 1`.

## Implementation notes

⚠ **The cell is indexed by its scaled south-west corner**, `c a = ⌊N * y a⌋₊`, and not by the
corner itself: the label is a tuple of natural numbers, which is what makes the count a binomial
coefficient and the pigeonhole a statement about a finite set. The book writes `λ = (⌊N x⌋/N)`
and carries the division; here the division appears only in the estimates that use it.

⚠ **The count is of labels, not of nonempty classes**, and the two differ: a label with
`∑ a, c a ≤ N` need not be attained. This is the direction the applications use — an upper bound
on the number of classes — and it is the direction the book proves.

⚠ **The index type `A` is arbitrary**, and over a number field it is *not* a set of places: the
roadmap's convention is two typed finsets, `Sinf : Finset (InfinitePlace K)` and
`Sfin : Finset (FinitePlace K)`, so a consumer instantiates `A` with the disjoint union of their
coercions to types. Nothing here knows that, which is the point of stating it abstractly — Layer
5.1 uses the same lemmas with `A` a set of *forms*.

⚠ **`∑ a, φ a x ≤ 1` is enough for everything except (6.10)**, which needs the point to lie on
the hyperplane. The book's profile does lie on it, so the distinction costs nothing there; it is
stated as it is so that the pigeonhole can be used for a family that is only subadditive.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
6.4.2–6.4.4.

This is part of Layer 3.1 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Finset

namespace Set

/-- The tuples `c : A → ℕ` with `∑ a, c a ≤ N` — the labels of the cells of side `1/N` that meet
the unit simplex — are finitely many. -/
theorem finite_setOf_sum_le (A : Type*) [Fintype A] (N : ℕ) :
    {c : A → ℕ | ∑ a, c a ≤ N}.Finite := by
  classical
  refine Set.Finite.subset (Finset.finite_toSet
    (Fintype.piFinset fun _ : A ↦ Finset.range (N + 1))) fun c hc ↦ ?_
  have hc' : ∑ a, c a ≤ N := hc
  simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_range]
  exact fun a ↦ Nat.lt_succ_of_le
    ((Finset.single_le_sum (f := c) (fun i _ ↦ Nat.zero_le (c i)) (Finset.mem_univ a)).trans hc')

/-- **Lemma 6.4.3**: there are `(N + |A|).choose |A|` labels of cells of side `1/N`, one for each
solution in natural numbers of `∑ a, c a ≤ N`. -/
theorem ncard_setOf_sum_le (A : Type*) [Fintype A] (N : ℕ) :
    {c : A → ℕ | ∑ a, c a ≤ N}.ncard = (N + Fintype.card A).choose (Fintype.card A) := by
  classical
  have hfin := finite_setOf_sum_le A N
  have hbij : hfin.toFinset.card
      = #(Finset.finsuppAntidiag (Finset.univ : Finset (Option A)) N) := by
    refine Finset.card_nbij'
      (fun c ↦ Finsupp.equivFunOnFinite.symm fun o ↦ o.elim (N - ∑ a, c a) c)
      (fun F a ↦ F (some a)) (fun c hc ↦ ?_) (fun F hF ↦ ?_) (fun c hc ↦ ?_) fun F hF ↦ ?_
    · have hc' : ∑ a, c a ≤ N := by simpa using hc
      simp only [Finset.mem_coe, Finset.mem_finsuppAntidiag]
      refine ⟨?_, Finset.subset_univ _⟩
      rw [Fintype.sum_option]
      simpa [Finsupp.coe_equivFunOnFinite_symm] using Nat.sub_add_cancel hc'
    · have hF' : F none + ∑ a, F (some a) = N := by simpa using hF
      have hle : ∑ a, F (some a) ≤ N := hF' ▸ Nat.le_add_left _ _
      simpa using hle
    · funext a
      simp
    · have hF' : F none + ∑ a, F (some a) = N := by simpa using hF
      have hnone : N - ∑ a, F (some a) = F none := by rw [← hF', Nat.add_sub_cancel]
      refine Finsupp.ext fun o ↦ ?_
      cases o with
      | none => simpa using hnone
      | some a => simp
  rw [Set.ncard_eq_toFinset_card _ hfin, hbij, Finset.card_finsuppAntidiag_nat_eq_choose,
    Finset.card_univ, Fintype.card_option,
    show Fintype.card A + 1 + N - 1 = N + Fintype.card A from by omega,
    ← Nat.choose_symm (Nat.le_add_left (Fintype.card A) N), Nat.add_sub_cancel]

/-- **Pigeonhole for an infinite set.** If `f` maps `X` into a finite set `T`, then some fibre of
`f` meets `X` in an infinite set. -/
theorem Infinite.exists_infinite_fiber {ι γ : Type*} {X : Set ι} (hX : X.Infinite) {f : ι → γ}
    {T : Set γ} (hT : T.Finite) (hf : ∀ x ∈ X, f x ∈ T) :
    ∃ c ∈ T, {x ∈ X | f x = c}.Infinite := by
  by_contra h
  push Not at h
  refine hX (Set.Finite.subset (hT.biUnion fun c hc ↦ h c hc) fun x hx ↦ ?_)
  exact Set.mem_biUnion (hf x hx) ⟨hx, rfl⟩

end Set

namespace Real

variable {A : Type*}

/-- The label of the half-open cell of side `1/N` containing `y`: its south-west corner, scaled
by `N`. -/
noncomputable def cellIndex (N : ℕ) (y : A → ℝ) (a : A) : ℕ := ⌊(N : ℝ) * y a⌋₊

theorem cellIndex_apply (N : ℕ) (y : A → ℝ) (a : A) :
    cellIndex N y a = ⌊(N : ℝ) * y a⌋₊ := rfl

/-- The south-west corner of the cell of `y` is at most `y`. -/
theorem cellIndex_div_le {N : ℕ} (hN : 0 < N) {y : A → ℝ} {a : A} (hy : 0 ≤ y a) :
    (cellIndex N y a : ℝ) / N ≤ y a := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [div_le_iff₀ hN']
  rw [cellIndex_apply]
  calc (⌊(N : ℝ) * y a⌋₊ : ℝ) ≤ (N : ℝ) * y a :=
        Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) hy)
  _ = y a * N := mul_comm _ _

/-- `y` is below the north-east corner of its cell. -/
theorem lt_cellIndex_add_one_div {N : ℕ} (hN : 0 < N) (y : A → ℝ) (a : A) :
    y a < ((cellIndex N y a : ℝ) + 1) / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [lt_div_iff₀ hN', cellIndex_apply, mul_comm]
  exact Nat.lt_floor_add_one ((N : ℝ) * y a)

/-- **The label of a cell that meets the unit simplex** solves `∑ a, c a ≤ N`. -/
theorem sum_cellIndex_le [Fintype A] {N : ℕ} {y : A → ℝ} (hy : ∀ a, 0 ≤ y a)
    (hsum : ∑ a, y a ≤ 1) : ∑ a, cellIndex N y a ≤ N := by
  have key : ((∑ a, cellIndex N y a : ℕ) : ℝ) ≤ (N : ℝ) := by
    push_cast
    calc ∑ a, (cellIndex N y a : ℝ)
        ≤ ∑ a, (N : ℝ) * y a :=
          Finset.sum_le_sum fun a _ ↦ Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) (hy a))
      _ = (N : ℝ) * ∑ a, y a := by rw [Finset.mul_sum]
      _ ≤ (N : ℝ) * 1 := by
          exact mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (N : ℝ) := mul_one _
  exact_mod_cast key

/-- **The book's (6.10).** A point *on* the hyperplane `∑ a, y a = 1` has a label whose sum is
larger than `N - |A|`. -/
theorem one_sub_card_div_lt_sum_cellIndex_div [Fintype A] {N : ℕ} (hN : 0 < N) {y : A → ℝ}
    (hsum : ∑ a, y a = 1) :
    1 - (Fintype.card A : ℝ) / N < ∑ a, (cellIndex N y a : ℝ) / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hlt : ∑ a, y a < ∑ a, ((cellIndex N y a : ℝ) + 1) / N :=
    Finset.sum_lt_sum_of_nonempty
      (by
        rcases isEmpty_or_nonempty A with h | h
        · exfalso
          simp only [Finset.univ_eq_empty, Finset.sum_empty] at hsum
          exact absurd hsum (by norm_num)
        · exact Finset.univ_nonempty)
      fun a _ ↦ lt_cellIndex_add_one_div hN y a
  have hsplit : ∑ a, ((cellIndex N y a : ℝ) + 1) / N
      = (∑ a, (cellIndex N y a : ℝ) / N) + (Fintype.card A : ℝ) / N := by
    simp only [add_div]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one_div]
  rw [hsum, hsplit] at hlt
  linarith

variable [Fintype A]

/-- The normalized logarithmic profile of a family `f` of numbers in `(0, 1]` whose product is
`< 1`: the point of the unit simplex whose `a`-th coordinate is `log (f a) / log (∏ b, f b)`. -/
noncomputable def logProfile (f : A → ℝ) (a : A) : ℝ := log (f a) / log (∏ b, f b)

theorem logProfile_apply (f : A → ℝ) (a : A) :
    logProfile f a = log (f a) / log (∏ b, f b) := rfl

theorem log_prod_neg {f : A → ℝ} (hpos : ∀ a, 0 < f a) (hprod : ∏ b, f b < 1) :
    log (∏ b, f b) < 0 :=
  Real.log_neg (Finset.prod_pos fun a _ ↦ hpos a) hprod

/-- The profile is nonnegative: both logarithms are `≤ 0`. -/
theorem logProfile_nonneg {f : A → ℝ} (hpos : ∀ a, 0 < f a) (hf : ∀ a, f a ≤ 1)
    (hprod : ∏ b, f b < 1) (a : A) : 0 ≤ logProfile f a :=
  div_nonneg_iff.mpr <| Or.inr ⟨Real.log_nonpos (hpos a).le (hf a),
    (log_prod_neg hpos hprod).le⟩

/-- **The profile lies on the hyperplane.** -/
theorem sum_logProfile {f : A → ℝ} (hpos : ∀ a, 0 < f a) (hprod : ∏ b, f b < 1) :
    ∑ a, logProfile f a = 1 := by
  have hlog : log (∏ b, f b) = ∑ a, log (f a) :=
    Real.log_prod fun a _ ↦ (hpos a).ne'
  simp only [logProfile_apply]
  rw [show (∑ a, log (f a) / log (∏ b, f b)) = (∑ a, log (f a)) / log (∏ b, f b) from
    (Finset.sum_div _ _ _).symm, ← hlog]
  exact div_self (log_prod_neg hpos hprod).ne

/-- **The upper half of the book's (6.9).** -/
theorem le_rpow_cellIndex_div {N : ℕ} (hN : 0 < N) {f : A → ℝ} (hpos : ∀ a, 0 < f a)
    (hf : ∀ a, f a ≤ 1) (hprod : ∏ b, f b < 1) (a : A) :
    f a ≤ (∏ b, f b) ^ ((cellIndex N (logProfile f) a : ℝ) / N) := by
  have hprod0 : 0 < ∏ b, f b := Finset.prod_pos fun b _ ↦ hpos b
  have hL : log (∏ b, f b) < 0 := log_prod_neg hpos hprod
  rw [← Real.log_le_log_iff (hpos a) (Real.rpow_pos_of_pos hprod0 _), Real.log_rpow hprod0]
  have hcell := cellIndex_div_le (y := logProfile f) hN (logProfile_nonneg hpos hf hprod a)
  rw [logProfile_apply, le_div_iff_of_neg hL] at hcell
  exact hcell

/-- **The lower half of the book's (6.9).** -/
theorem rpow_cellIndex_add_one_div_lt {N : ℕ} (hN : 0 < N) {f : A → ℝ} (hpos : ∀ a, 0 < f a)
    (hprod : ∏ b, f b < 1) (a : A) :
    (∏ b, f b) ^ (((cellIndex N (logProfile f) a : ℝ) + 1) / N) < f a := by
  have hprod0 : 0 < ∏ b, f b := Finset.prod_pos fun b _ ↦ hpos b
  have hL : log (∏ b, f b) < 0 := log_prod_neg hpos hprod
  rw [← Real.log_lt_log_iff (Real.rpow_pos_of_pos hprod0 _) (hpos a), Real.log_rpow hprod0]
  have hcell := lt_cellIndex_add_one_div hN (logProfile f) a
  rw [logProfile_apply, div_lt_iff_of_neg hL] at hcell
  exact hcell

end Real

namespace Set

/-- **Lemma 6.4.3, in the form the applications quote**: at most `(N + |A|).choose |A|` of the
classes of size `1/N` are nonempty. -/
theorem ncard_image_cellIndex_le {ι A : Type*} [Fintype A] {X : Set ι} (φ : A → ι → ℝ)
    (hφ0 : ∀ a, ∀ x ∈ X, 0 ≤ φ a x) (hφ1 : ∀ x ∈ X, ∑ a, φ a x ≤ 1) (N : ℕ) :
    ((fun x ↦ Real.cellIndex N fun a ↦ φ a x) '' X).ncard
      ≤ (N + Fintype.card A).choose (Fintype.card A) := by
  rw [← ncard_setOf_sum_le A N]
  refine Set.ncard_le_ncard ?_ (finite_setOf_sum_le A N)
  rintro c ⟨x, hx, rfl⟩
  exact Real.sum_cellIndex_le (fun a ↦ hφ0 a x hx) (hφ1 x hx)

/-- **An infinite set has an infinite approximation class.** For any `N`, one of the finitely many
cells of side `1/N` contains the profile of infinitely many points of `X`; the class is named by
its label, which solves `∑ a, c a ≤ N`. -/
theorem Infinite.exists_cellIndex_eq {ι A : Type*} [Fintype A] {X : Set ι} (hX : X.Infinite)
    (φ : A → ι → ℝ) (hφ0 : ∀ a, ∀ x ∈ X, 0 ≤ φ a x) (hφ1 : ∀ x ∈ X, ∑ a, φ a x ≤ 1) (N : ℕ) :
    ∃ c : A → ℕ, (∑ a, c a ≤ N) ∧ {x ∈ X | Real.cellIndex N (fun a ↦ φ a x) = c}.Infinite := by
  obtain ⟨c, hc, hinf⟩ := hX.exists_infinite_fiber (f := fun x ↦ Real.cellIndex N fun a ↦ φ a x)
    (T := {c : A → ℕ | ∑ a, c a ≤ N}) (finite_setOf_sum_le A N)
    fun x hx ↦ Real.sum_cellIndex_le (fun a ↦ hφ0 a x hx) (hφ1 x hx)
  exact ⟨c, hc, hinf⟩

end Set

/-!
### Acceptance criteria

The formula is checked against a hand count, the hypothesis that the point lies in the simplex is
shown to be load-bearing, and the upper half of (6.9) is shown to be attained.
-/

/-- **Acceptance test: at `N = 0` there is exactly one class**, the one the formula counts. -/
example : {c : Fin 2 → ℕ | ∑ a, c a ≤ 0} = {0} := by
  ext c
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Fin.sum_univ_two, Nat.le_zero,
    Nat.add_eq_zero_iff]
  constructor
  · rintro ⟨h0, h1⟩
    funext a
    fin_cases a <;> assumption
  · rintro rfl
    exact ⟨rfl, rfl⟩

example : {c : Fin 2 → ℕ | ∑ a, c a ≤ 0}.ncard = (0 + Fintype.card (Fin 2)).choose 2 := by
  rw [Set.ncard_setOf_sum_le]
  norm_num

/-- **Rejection test: the classes are the cells of the simplex, not of the cube.** The constant
family `y a = 1` has every coordinate in `[0, 1]`, and its label at `N = 1` sums to `2`: without
`∑ a, y a ≤ 1` the labels are not the `(N + |A|).choose |A|` solutions of `∑ a, c a ≤ N` but the
`(N + 1) ^ |A|` cells of the cube, which at `N = 1` and `|A| = 2` is `4` against `3`. -/
example : ¬ ∑ a, Real.cellIndex 1 (fun _ : Fin 2 ↦ (1 : ℝ)) a ≤ 1 := by
  norm_num [Real.cellIndex_apply, Fin.sum_univ_two]

/-- **Acceptance test: the upper half of (6.9) is attained**, so its exponent is not off by one.
For the constant family `f = 1/4` in one coordinate the profile is `1`, the label at `N = 2` is
`2`, and the bound `f a ≤ (∏ b, f b) ^ (c a / N)` holds with equality. -/
example : (∏ _b : Fin 1, (1 / 4 : ℝ)) ^
    ((Real.cellIndex 2 (Real.logProfile fun _ : Fin 1 ↦ (1 / 4 : ℝ)) 0 : ℝ) / 2) = 1 / 4 := by
  have hp : (∏ _b : Fin 1, (1 / 4 : ℝ)) = 1 / 4 := by simp
  have hlog : Real.log (1 / 4 : ℝ) ≠ 0 := by
    have : Real.log (1 / 4 : ℝ) < 0 := Real.log_neg (by norm_num) (by norm_num)
    exact this.ne
  have hprof : Real.logProfile (fun _ : Fin 1 ↦ (1 / 4 : ℝ)) 0 = 1 := by
    rw [Real.logProfile_apply, hp]
    exact div_self hlog
  rw [hp, Real.cellIndex_apply, hprof]
  norm_num [Real.rpow_one]
