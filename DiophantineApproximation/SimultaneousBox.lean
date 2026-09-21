/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.PolynomialSupNorm

-- Used only inside proofs.
import Mathlib.Data.Fintype.Pi

/-!
# The box principle at several points

Layer 1.3's first box principle, in `DiophantineApproximation/BoxPrinciple.lean`, asks an integer
polynomial of degree at most `n` to be small at a *single* point. Wirsing's third inequality needs
one that is small at `ξ` **and** of prescribed size at `n - 1` further points, so that the
polynomial it produces has a root near each of them and therefore exactly one root near `ξ`.

This file is that pigeonhole. The `m` linear forms `P ↦ P(t j)` are evaluated on the
`(A + 1) ^ (n + 1)` integer polynomials with coefficients in `[0, A]`; the value of the `j`-th
form lies in an interval of length `2 A T j`, where `T j = ∑_{k ≤ n} |t j| ^ k`, which is cut into
`⌊2 A T j / β j⌋₊ + 1` boxes of length `β j`. As soon as the product of the box counts is smaller
than `(A + 1) ^ (n + 1)`, two of the polynomials share a box in every coordinate, and their
difference is small at every `t j` at once.

## Main results

* `Polynomial.abs_sub_lt_one_of_floor_eq`: the pigeonhole step, in the half-open form
  `⌊u⌋₊ = ⌊v⌋₊ → |u - v| < 1`.
* `Polynomial.exists_ne_zero_abs_aeval_le`: **the box principle at `m` points**. The hypothesis
  is one inequality between real numbers, `∏ (2 A T j / β j + 1) < (A + 1) ^ (n + 1)`, and the
  conclusion is a nonzero integer polynomial of degree at most `n` and naive height at most `A`
  with `|P (t j)| ≤ β j` for every `j`.

## Implementation notes

⚠ **No clamping is needed here, unlike in `BoxPrinciple`.** There the box count had to be pushed
down to `(H + 1) ^ (n + 1) - 1`, because the height bound `H` was prescribed and the count had to
beat it by one; the index was therefore `min ⌊u⌋₊ (N - 1)` and the pigeonhole step was the closed
`|u - v| ≤ 1`. Here the coefficient bound `A` is chosen by the caller, so one spare box per
coordinate costs nothing: the index is the plain `⌊u⌋₊`, the boxes are half-open, and the
pigeonhole step is the strict `|u - v| < 1`.

⚠ **The hypothesis is stated with real division and a `+ 1` per coordinate, not with the
`Nat.floor` that the proof uses.** `(⌊x⌋₊ + 1 : ℝ) ≤ x + 1` is the only bridge, and stating the
hypothesis on the right of it keeps every caller in real arithmetic, where the product of the
bounds `β j` is what it has to control.

## References

Y. Bugeaud, *Exponents of Diophantine approximation*, in: Dynamics and Analytic Number Theory,
Cambridge University Press (2016), Theorem 2.6 — where Minkowski's linear forms theorem is used
for the same purpose, and where a constant is all that the pigeonhole loses.

This is part of Layer 1.3 of the `DiophantineApproximation` roadmap.
-/

public section

open scoped ENNReal NNReal

namespace Polynomial

/-- **The pigeonhole step.** Two nonnegative reals with the same integer part are at distance
less than one. -/
theorem abs_sub_lt_one_of_floor_eq {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h : ⌊u⌋₊ = ⌊v⌋₊) : |u - v| < 1 := by
  have h1 := Nat.floor_le hu
  have h2 := Nat.lt_floor_add_one u
  have h3 := Nat.floor_le hv
  have h4 := Nat.lt_floor_add_one v
  rw [h] at h1 h2
  rw [abs_sub_lt_iff]
  constructor <;> linarith

/-- **The box principle at `m` points.** If the product of the box counts
`2 A T j / β j + 1`, where `T j = ∑_{k ≤ n} |t j| ^ k`, is smaller than the number
`(A + 1) ^ (n + 1)` of integer polynomials of degree at most `n` with coefficients in `[0, A]`,
then some nonzero integer polynomial of degree at most `n` and naive height at most `A` satisfies
`|P (t j)| ≤ β j` simultaneously for every `j`. -/
theorem exists_ne_zero_abs_aeval_le {m : ℕ} (n A : ℕ) (t β : Fin m → ℝ) (hβ : ∀ j, 0 < β j)
    (hbox : ∏ j : Fin m,
        (2 * (A : ℝ) * (∑ k ∈ Finset.range (n + 1), |t j| ^ k) / β j + 1) <
      ((A : ℝ) + 1) ^ (n + 1)) :
    ∃ P : ℤ[X], P ≠ 0 ∧ P.natDegree ≤ n ∧ P.supNorm ≤ (A : ℝ) ∧
      ∀ j, |aeval (t j) P| ≤ β j := by
  classical
  set T : Fin m → ℝ := fun j ↦ ∑ k ∈ Finset.range (n + 1), |t j| ^ k with hTdef
  have hT0 : ∀ j, 0 ≤ T j := fun j ↦ Finset.sum_nonneg fun k _ ↦ by positivity
  set D : Finset (Fin (n + 1) → ℕ) :=
    Fintype.piFinset fun _ : Fin (n + 1) ↦ Finset.range (A + 1) with hDdef
  set e : (Fin (n + 1) → ℕ) → ℕ → ℤ :=
    fun a i ↦ if h : i < n + 1 then (a ⟨i, h⟩ : ℤ) else 0 with hedef
  set L : Fin m → (Fin (n + 1) → ℕ) → ℝ :=
    fun j a ↦ ∑ k ∈ Finset.range (n + 1), (e a k : ℝ) * (t j) ^ k with hLdef
  set N : Fin m → ℕ := fun j ↦ ⌊2 * (A : ℝ) * T j / β j⌋₊ + 1 with hNdef
  set u : Fin m → (Fin (n + 1) → ℕ) → ℝ :=
    fun j a ↦ (L j a + (A : ℝ) * T j) / β j with hudef
  have hcard : D.card = (A + 1) ^ (n + 1) := by
    rw [hDdef, Fintype.card_piFinset]
    simp
  have hzero : ∀ (a : Fin (n + 1) → ℕ) (i : ℕ), ¬ i < n + 1 → e a i = 0 := by
    intro a i h
    simp only [hedef]
    exact dite_eq_right_of_eq_false (eq_false h)
  have hcoeff : ∀ a ∈ D, ∀ i, 0 ≤ e a i ∧ e a i ≤ (A : ℤ) := by
    intro a ha i
    by_cases h : i < n + 1
    · have hmem : a ⟨i, h⟩ ∈ Finset.range (A + 1) := Fintype.mem_piFinset.1 ha ⟨i, h⟩
      have h2 : a ⟨i, h⟩ ≤ A := by have := Finset.mem_range.1 hmem; omega
      have he : e a i = (a ⟨i, h⟩ : ℤ) := by
        simp only [hedef]
        exact dite_eq_left_of_eq_true (eq_true h)
      rw [he]
      exact ⟨by positivity, by exact_mod_cast h2⟩
    · rw [hzero a i h]
      exact ⟨le_rfl, by positivity⟩
  have hL : ∀ (j : Fin m), ∀ a ∈ D, |L j a| ≤ (A : ℝ) * T j := by
    intro j a ha
    have hstep : |L j a| ≤ ∑ k ∈ Finset.range (n + 1), (A : ℝ) * |t j| ^ k := by
      refine le_trans (by simpa only [hLdef] using
        Finset.abs_sum_le_sum_abs (fun k ↦ (e a k : ℝ) * (t j) ^ k) (Finset.range (n + 1))) ?_
      refine Finset.sum_le_sum fun k _ ↦ ?_
      obtain ⟨h1, h2⟩ := hcoeff a ha k
      rw [abs_mul, abs_pow]
      have hb : |(e a k : ℝ)| ≤ (A : ℝ) := by
        rw [abs_of_nonneg (by exact_mod_cast h1)]
        exact_mod_cast h2
      exact mul_le_mul_of_nonneg_right hb (by positivity)
    rw [hTdef, Finset.mul_sum]
    exact hstep
  have hu0 : ∀ (j : Fin m), ∀ a ∈ D, 0 ≤ u j a := by
    intro j a ha
    have h := abs_le.1 (hL j a ha)
    exact div_nonneg (by linarith [h.1]) (hβ j).le
  have hidx : ∀ (j : Fin m), ∀ a ∈ D, ⌊u j a⌋₊ < N j := by
    intro j a ha
    have h := abs_le.1 (hL j a ha)
    have hnum : L j a + (A : ℝ) * T j ≤ 2 * (A : ℝ) * T j := by linarith [h.2]
    have hle : u j a ≤ 2 * (A : ℝ) * T j / β j := by
      simp only [hudef]
      gcongr
      exact (hβ j).le
    have hmono := Nat.floor_le_floor hle
    have hNj : N j = ⌊2 * (A : ℝ) * T j / β j⌋₊ + 1 := rfl
    omega
  set E : Finset (Fin m → ℕ) := Fintype.piFinset fun j ↦ Finset.range (N j) with hEdef
  have hEcard : E.card = ∏ j : Fin m, N j := by
    rw [hEdef, Fintype.card_piFinset]
    simp
  have hlt : E.card < D.card := by
    have hcastle : ((∏ j : Fin m, N j : ℕ) : ℝ) ≤
        ∏ j : Fin m, (2 * (A : ℝ) * T j / β j + 1) := by
      rw [Nat.cast_prod]
      refine Finset.prod_le_prod₀ (fun j _ ↦ by positivity) fun j _ ↦ ?_
      have h0 : (0 : ℝ) ≤ 2 * (A : ℝ) * T j / β j :=
        div_nonneg (mul_nonneg (by positivity) (hT0 j)) (hβ j).le
      have hfl : (⌊2 * (A : ℝ) * T j / β j⌋₊ : ℝ) ≤ 2 * (A : ℝ) * T j / β j := Nat.floor_le h0
      have hNj : N j = ⌊2 * (A : ℝ) * T j / β j⌋₊ + 1 := rfl
      rw [hNj]
      push_cast
      linarith
    have hfin : ((∏ j : Fin m, N j : ℕ) : ℝ) < (((A + 1) ^ (n + 1) : ℕ) : ℝ) := by
      refine lt_of_le_of_lt hcastle ?_
      push_cast
      exact hbox
    rw [hEcard, hcard]
    exact_mod_cast hfin
  obtain ⟨a, ha, b, hb, hab, hg⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (f := fun a ↦ fun j ↦ ⌊u j a⌋₊) hlt
      (fun a ha ↦ Finset.mem_coe.2 (Fintype.mem_piFinset.2
        fun j ↦ Finset.mem_range.2 (hidx j a ha)))
  have hdiff : ∀ j : Fin m, |L j a - L j b| ≤ β j := by
    intro j
    have hfl : ⌊u j a⌋₊ = ⌊u j b⌋₊ := congrFun hg j
    have h1 := abs_sub_lt_one_of_floor_eq (hu0 j a ha) (hu0 j b hb) hfl
    have h2 : u j a - u j b = (L j a - L j b) / β j := by
      simp only [hudef, ← sub_div]
      congr 1
      ring
    rw [h2, abs_div, abs_of_pos (hβ j), div_lt_one (hβ j)] at h1
    exact h1.le
  set P₀ : ℤ[X] := ∑ k ∈ Finset.range (n + 1), monomial k (e a k - e b k) with hP₀def
  have hPc : ∀ i, P₀.coeff i = e a i - e b i := by
    intro i
    rw [hP₀def, finsetSum_coeff]
    simp only [coeff_monomial]
    rw [Finset.sum_ite_eq' (Finset.range (n + 1)) i fun k ↦ e a k - e b k]
    by_cases hi : i ∈ Finset.range (n + 1)
    · exact ite_eq_left_of_eq_true _ _ (eq_true hi)
    · have hni : ¬ i < n + 1 := fun h ↦ hi (Finset.mem_range.2 h)
      rw [hzero a i hni, hzero b i hni, sub_zero, ite_self]
  refine ⟨P₀, ?_, ?_, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := Function.ne_iff.1 hab
    refine fun h0 ↦ hk ?_
    have hik : ((k : ℕ)) < n + 1 := k.isLt
    have hc := hPc (k : ℕ)
    rw [h0, coeff_zero] at hc
    have he : e a (k : ℕ) = (a k : ℤ) := by
      simp only [hedef]
      exact dite_eq_left_of_eq_true (eq_true hik)
    have he' : e b (k : ℕ) = (b k : ℤ) := by
      simp only [hedef]
      exact dite_eq_left_of_eq_true (eq_true hik)
    rw [he, he'] at hc
    omega
  · refine natDegree_le_iff_coeff_eq_zero.2 fun q hq ↦ ?_
    have hni : ¬ q < n + 1 := by omega
    rw [hPc q, hzero a q hni, hzero b q hni, sub_zero]
  · refine supNorm_le_of_forall fun i ↦ ?_
    obtain ⟨h1, h2⟩ := hcoeff a ha i
    obtain ⟨h3, h4⟩ := hcoeff b hb i
    rw [hPc i, Int.norm_eq_abs]
    push_cast
    rw [abs_le]
    have c1 : (0 : ℝ) ≤ (e a i : ℝ) := by exact_mod_cast h1
    have c2 : (e a i : ℝ) ≤ (A : ℝ) := by exact_mod_cast h2
    have c3 : (0 : ℝ) ≤ (e b i : ℝ) := by exact_mod_cast h3
    have c4 : (e b i : ℝ) ≤ (A : ℝ) := by exact_mod_cast h4
    constructor <;> linarith
  · intro j
    have hval : aeval (t j) P₀ = L j a - L j b := by
      rw [hP₀def, map_sum, hLdef]
      simp only [aeval_monomial, eq_intCast, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      push_cast
      ring
    rw [hval]
    exact hdiff j

/-! ### Acceptance criteria -/

/-- **Acceptance test: the box principle at `m` points.** -/
example {m : ℕ} (n A : ℕ) (t β : Fin m → ℝ) (hβ : ∀ j, 0 < β j)
    (hbox : ∏ j : Fin m,
        (2 * (A : ℝ) * (∑ k ∈ Finset.range (n + 1), |t j| ^ k) / β j + 1) <
      ((A : ℝ) + 1) ^ (n + 1)) :
    ∃ P : ℤ[X], P ≠ 0 ∧ P.natDegree ≤ n ∧ P.supNorm ≤ (A : ℝ) ∧
      ∀ j, |aeval (t j) P| ≤ β j :=
  exists_ne_zero_abs_aeval_le n A t β hβ hbox

end Polynomial
