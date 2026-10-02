/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.WedgeDomainAt
public import DiophantineApproximation.ExponentGrid

/-!
# Grids of the minima at one place

The exponents `NumberField.wedgeExponentAt` of the wedge domain at one place `w₀`
(`WedgeDomainAt.lean`) move with the level `Q`, and Layer 6.1 rounds them to a grid so that only
finitely many systems of exponents occur. They are the sums of the exponents of the domain plus
`logb Q C` at every infinite place, plus at `w₀` alone `a` times

```text
∑_{t ∈ T} logb Q μ (π⁻¹ t) + [T in the top block] · logb Q (μ (k - 1) / μ k),
```

a function of the `#ι` numbers `logb Q μ i`, of `logb Q C`, of the jump, and of **one** bijection
`π`. Rounding those `#ι + 2` numbers (Evertse 1996, Lemma 18; Evertse–Schlickewei 2002,
Lemma 18.1) gives the **grid of the minima** `NumberField.minimaGrid`, and there are at most
`(#ι)! (2 m + 1) ^ (#ι + 2)` of them: singly exponential in `#ι`, and independent of the number of
infinite places. An entry at `w₀` collects `a (p + 1) + 1` roundings, but `w₀` carries
`mult w₀ = [K : ℚ] / a` in the weight, so the total cost in the weight is `[K : ℚ] (p + 2)` meshes
per subset, as if every infinite place had collected `p + 2`.

## Main definitions

* `NumberField.minimaGrid`: the integers of a grid system, from a bijection `π`, a constant `z`, a
  jump `j` and integers `b` for the minima.
* `NumberField.minimaGridSet`: the grids of the minima with bounded integers.

## Main results

* `NumberField.le_gridExponent_minimaGrid`, `NumberField.gridExponent_minimaGrid_le`: rounding the
  minima up dominates the wedge exponents, and costs at most one mesh, plus `a (p + 1)` at `w₀`.
* `NumberField.approxWeight_gridExponent_minimaGrid_le`: the cost in the weight is
  `γ [K : ℚ] binom(#ι, p) (p + 2)`.
* `NumberField.sum_mult_abs_minimaGrid_le`: the entries of a grid, weighted by the multiplicities,
  are bounded by those of the integers at one place.
* `NumberField.ncard_minimaGridSet_le`: there are at most `(#ι)! (2 m + 1) ^ (#ι + 2)` grids of the
  minima.

## References

J.-H. Evertse, "An improvement of the quantitative subspace theorem", *Compositio Mathematica*
**101** (1996), 225–311, Lemma 18 and (6.53).

J.-H. Evertse and H. P. Schlickewei, "A quantitative version of the absolute subspace theorem",
*J. reine angew. Math.* **548** (2002), 21–127, Lemmas 17.2 and 18.1.

This is part of Layer 6.1 of the `DiophantineApproximation` roadmap, and items Q1.7 and Q1.8c of
the `QuantitativeSubspace` roadmap.
-/

@[expose] public section

open Finset Module NumberField

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [LinearOrder ι]

open scoped Classical in
/-- **The grid of the minima at `w₀`**: at every infinite place the integer `z`, and at `w₀` in
addition `a` times `∑_{t ∈ T} b (π⁻¹ t)`, plus `j` if `T` lies in the top block `{k, …}` of `π`.
It rounds the corrections of `NumberField.wedgeExponentAt` when `z`, `b` and `j` round `logb Q C`,
the `logb Q μ i` and `logb Q (μ (k - 1) / μ k)`. -/
noncomputable def minimaGrid (w₀ : InfinitePlace K) (a k p : ℕ) (π : Fin (Fintype.card ι) ≃ ι)
    (z j : ℤ) (b : Fin (Fintype.card ι) → ℤ) : InfinitePlace K → Set.powersetCard ι p → ℤ :=
  fun w T ↦ z + if w = w₀ then a * (∑ t ∈ (T : Finset ι), b (π.symm t) +
    if ∀ t ∈ (T : Finset ι), k ≤ (π.symm t : ℕ) then j else 0) else 0

variable (K ι) in
/-- **The grids of the minima at `w₀` with integers in `[-m, m]`**, for one `k` and one `p`. -/
def minimaGridSet (w₀ : InfinitePlace K) (a k p : ℕ) (m : ℤ) :
    Set (InfinitePlace K → Set.powersetCard ι p → ℤ) :=
  {g | ∃ (π : Fin (Fintype.card ι) ≃ ι) (z j : ℤ) (b : Fin (Fintype.card ι) → ℤ),
      |z| ≤ m ∧ |j| ≤ m ∧ (∀ i, |b i| ≤ m) ∧ g = minimaGrid w₀ a k p π z j b}

/-- `γ ⌈x / γ⌉` lies in `[x, x + γ)`. -/
private theorem le_mul_ceil_div {γ : ℝ} (hγ : 0 < γ) (x : ℝ) : x ≤ γ * ⌈x / γ⌉ := by
  have h := Int.le_ceil (x / γ)
  rw [div_le_iff₀ hγ] at h
  linarith

private theorem mul_ceil_div_le {γ : ℝ} (hγ : 0 < γ) (x : ℝ) : γ * ⌈x / γ⌉ ≤ x + γ := by
  have h := (Int.ceil_lt_add_one (x / γ)).le
  have h2 := mul_le_mul_of_nonneg_left h hγ.le
  rw [mul_add, mul_div_cancel₀ _ hγ.ne', mul_one] at h2
  exact h2

/-- **A number in `[-G, G]` rounds to an integer in `[-⌈G / γ⌉, ⌈G / γ⌉]`.** -/
theorem abs_ceil_div_le {γ G x : ℝ} (hγ : 0 < γ) (hx : |x| ≤ G) : |⌈x / γ⌉| ≤ ⌈G / γ⌉ := by
  rw [abs_le]
  have habs := abs_le.1 hx
  constructor
  · have h1 : (-G) / γ ≤ x / γ := by gcongr; exact habs.1
    have h2 : ⌈(-G) / γ⌉ ≤ ⌈x / γ⌉ := Int.ceil_mono h1
    have h3 : -⌈G / γ⌉ ≤ ⌈(-G) / γ⌉ := by
      rw [neg_div, Int.ceil_neg, neg_le_neg_iff]
      exact Int.floor_le_ceil _
    omega
  · exact Int.ceil_mono (by gcongr; exact habs.2)

section Round

variable {c : AbsoluteValue K ℝ → ι → ℝ} {w₀ : InfinitePlace K} {a : ℕ}
  {π : Fin (Fintype.card ι) ≃ ι} {μ : ℕ → ℝ} {C Q γ : ℝ} {k p : ℕ}

omit [NumberField K] in
open scoped Classical in
/-- The correction of the wedge exponent at an infinite place, as a sum of logarithms. -/
private theorem wedgeExponentAt_eq (hμ : ∀ j < Fintype.card ι, 0 < μ j)
    (hk : 0 < k) (hkN : k < Fintype.card ι) (w : InfinitePlace K) (T : Set.powersetCard ι p) :
    wedgeExponentAt c w₀ a π μ C Q k p w.1 T = ∑ t ∈ (T : Finset ι), c w.1 t + (Real.logb Q C
      + if w = w₀ then (∑ t ∈ (T : Finset ι), Real.logb Q (μ (π.symm t))
        + if ∀ t ∈ (T : Finset ι), k ≤ (π.symm t : ℕ)
          then Real.logb Q (μ (k - 1) / μ k) else 0) * a else 0) := by
  have hprod : ∀ t ∈ (T : Finset ι), μ (π.symm t) ≠ 0 := fun t _ ↦ (hμ _ (π.symm t).2).ne'
  have hprod0 : (∏ t ∈ (T : Finset ι), μ (π.symm t)) ≠ 0 := Finset.prod_ne_zero_iff.2 hprod
  have hratio : μ (k - 1) / μ k ≠ 0 := div_ne_zero (hμ _ (by omega)).ne' (hμ _ hkN).ne'
  have hww : w.1 = w₀.1 ↔ w = w₀ := Subtype.ext_iff.symm
  simp only [wedgeExponentAt, InfinitePlace.not_isNonarchimedean w, ↓reduceIte, hww]
  by_cases hw : w = w₀
  · simp only [hw, ↓reduceIte]
    congr 3
    split_ifs with hT
    · rw [Real.logb_mul hprod0 hratio, Real.logb_prod _ _ hprod]
    · rw [mul_one, Real.logb_prod _ _ hprod, add_zero]
  · simp only [hw, ↓reduceIte]

open scoped Classical in
/-- The rounding of the corrections, as a sum of roundings. -/
private theorem gridExponent_minimaGrid_eq (w : InfinitePlace K) (T : Set.powersetCard ι p)
    (z j : ℤ) (b : Fin (Fintype.card ι) → ℤ) :
    gridExponent (fun v (T : Set.powersetCard ι p) ↦ ∑ t ∈ (T : Finset ι), c v t) γ
        (minimaGrid w₀ a k p π z j b) w.1 T
      = ∑ t ∈ (T : Finset ι), c w.1 t + (γ * z + if w = w₀ then
        (∑ t ∈ (T : Finset ι), γ * b (π.symm t)
          + if ∀ t ∈ (T : Finset ι), k ≤ (π.symm t : ℕ) then γ * j else 0) * a else 0) := by
  rw [gridExponent_infinitePlace, minimaGrid]
  by_cases hw : w = w₀
  · simp only [hw, ↓reduceIte]
    split_ifs <;> push_cast <;> rw [← Finset.mul_sum] <;> ring
  · simp only [hw, ↓reduceIte]
    push_cast
    ring

open scoped Classical in
/-- **Rounding the minima up dominates the wedge exponents**: with `z`, `b`, `j` the roundings
up of `logb Q C`, of the `logb Q μ i` and of the jump, the grid exponent is at least the wedge
exponent at every infinite place. -/
theorem le_gridExponent_minimaGrid (hγ : 0 < γ)
    (hμ : ∀ j < Fintype.card ι, 0 < μ j) (hk : 0 < k) (hkN : k < Fintype.card ι)
    (w : InfinitePlace K) (T : Set.powersetCard ι p) :
    wedgeExponentAt c w₀ a π μ C Q k p w.1 T
      ≤ gridExponent (fun v (T : Set.powersetCard ι p) ↦ ∑ t ∈ (T : Finset ι), c v t) γ
        (minimaGrid w₀ a k p π ⌈Real.logb Q C / γ⌉
          ⌈Real.logb Q (μ (k - 1) / μ k) / γ⌉ fun i ↦ ⌈Real.logb Q (μ i) / γ⌉) w.1 T := by
  rw [wedgeExponentAt_eq hμ hk hkN, gridExponent_minimaGrid_eq]
  by_cases hw : w = w₀
  · simp only [hw, ↓reduceIte]
    refine add_le_add le_rfl (add_le_add (le_mul_ceil_div hγ _) ?_)
    refine mul_le_mul_of_nonneg_right (add_le_add
      (Finset.sum_le_sum fun t _ ↦ le_mul_ceil_div hγ _) ?_) (Nat.cast_nonneg a)
    split_ifs
    · exact le_mul_ceil_div hγ _
    · exact le_rfl
  · simp only [hw, ↓reduceIte, add_zero]
    exact add_le_add le_rfl (le_mul_ceil_div hγ _)

open scoped Classical in
/-- **Rounding the minima up costs at most one mesh**, and `a (p + 1)` more at `w₀`. -/
theorem gridExponent_minimaGrid_le (hγ : 0 < γ)
    (hμ : ∀ j < Fintype.card ι, 0 < μ j) (hk : 0 < k) (hkN : k < Fintype.card ι)
    (w : InfinitePlace K) (T : Set.powersetCard ι p) :
    gridExponent (fun v (T : Set.powersetCard ι p) ↦ ∑ t ∈ (T : Finset ι), c v t) γ
        (minimaGrid w₀ a k p π ⌈Real.logb Q C / γ⌉
          ⌈Real.logb Q (μ (k - 1) / μ k) / γ⌉ fun i ↦ ⌈Real.logb Q (μ i) / γ⌉) w.1 T
      ≤ wedgeExponentAt c w₀ a π μ C Q k p w.1 T +
        (γ + if w = w₀ then γ * (((p : ℝ) + 1) * a) else 0) := by
  rw [wedgeExponentAt_eq hμ hk hkN, gridExponent_minimaGrid_eq]
  have hz := mul_ceil_div_le hγ (Real.logb Q C)
  by_cases hw : w = w₀
  · simp only [hw, ↓reduceIte]
    have hsum := Finset.sum_le_sum fun t (_ : t ∈ (T : Finset ι)) ↦
      mul_ceil_div_le hγ (Real.logb Q (μ (π.symm t)))
    rw [Finset.sum_add_distrib, Finset.sum_const, Set.powersetCard.card_eq T, nsmul_eq_mul]
      at hsum
    have hj : (if ∀ t ∈ (T : Finset ι), k ≤ (π.symm t : ℕ)
          then γ * ⌈Real.logb Q (μ (k - 1) / μ k) / γ⌉ else 0)
        ≤ (if ∀ t ∈ (T : Finset ι), k ≤ (π.symm t : ℕ)
          then Real.logb Q (μ (k - 1) / μ k) else 0) + γ := by
      split_ifs
      · exact mul_ceil_div_le hγ _
      · linarith
    have hmain : (∑ t ∈ (T : Finset ι), γ * ⌈Real.logb Q (μ (π.symm t)) / γ⌉ +
          if ∀ t ∈ (T : Finset ι), k ≤ (π.symm t : ℕ)
            then γ * ⌈Real.logb Q (μ (k - 1) / μ k) / γ⌉ else 0) * a
        ≤ (∑ t ∈ (T : Finset ι), Real.logb Q (μ (π.symm t)) +
          if ∀ t ∈ (T : Finset ι), k ≤ (π.symm t : ℕ)
            then Real.logb Q (μ (k - 1) / μ k) else 0) * a + γ * (((p : ℝ) + 1) * a) :=
      calc _ ≤ (∑ t ∈ (T : Finset ι), Real.logb Q (μ (π.symm t)) + p * γ +
              ((if ∀ t ∈ (T : Finset ι), k ≤ (π.symm t : ℕ)
                then Real.logb Q (μ (k - 1) / μ k) else 0) + γ)) * a :=
            mul_le_mul_of_nonneg_right (add_le_add hsum hj) (Nat.cast_nonneg a)
        _ = _ := by ring
    linarith
  · simp only [hw, ↓reduceIte, add_zero]
    linarith

end Round

/-- **The cost of a rounding in the weight**, place by place: if `f` exceeds `g` by at most `ε w`
at each infinite place and not at all at the places of `Sfin`, the weight of `f` exceeds that of
`g` by at most `#ρ ∑_w mult w · ε w`. -/
theorem approxWeight_le_add_of_le {ρ : Type*} [Fintype ρ] {Sfin : Finset (FinitePlace K)}
    {f g : AbsoluteValue K ℝ → ρ → ℝ} {ε : InfinitePlace K → ℝ}
    (hinf : ∀ (w : InfinitePlace K) (i : ρ), f w.1 i ≤ g w.1 i + ε w)
    (hfin : ∀ v ∈ Sfin, ∀ i : ρ, f v.1 i ≤ g v.1 i) :
    approxWeight Sfin f ≤
      approxWeight Sfin g + Fintype.card ρ * ∑ w : InfinitePlace K, (w.mult : ℝ) * ε w := by
  have h1 : ∀ w : InfinitePlace K, (w.mult : ℝ) * ∑ i, f w.1 i
      ≤ (w.mult : ℝ) * ∑ i, g w.1 i + Fintype.card ρ * ((w.mult : ℝ) * ε w) := by
    intro w
    have hsum : ∑ i, f w.1 i ≤ ∑ i, g w.1 i + Fintype.card ρ * ε w := by
      have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hinf w i)
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
      exact this
    have hm : (0 : ℝ) ≤ (w.mult : ℝ) := Nat.cast_nonneg _
    nlinarith [hsum]
  have hA := Finset.sum_le_sum (fun w (_ : w ∈ Finset.univ) ↦ h1 w)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hA
  have hB : ∑ v ∈ Sfin, ∑ i, f v.1 i ≤ ∑ v ∈ Sfin, ∑ i, g v.1 i :=
    Finset.sum_le_sum fun v hv ↦ Finset.sum_le_sum fun i _ ↦ hfin v hv i
  rw [approxWeight, approxWeight]
  linarith

open scoped Classical in
/-- **The cost of rounding the minima in the weight**: `γ [K : ℚ] binom(#ι, p) (p + 2)`, the
place `w₀` carrying `mult w₀ a (p + 1) = [K : ℚ] (p + 1)` of it. -/
theorem approxWeight_gridExponent_minimaGrid_le {Sfin : Finset (FinitePlace K)}
    {c : AbsoluteValue K ℝ → ι → ℝ} {w₀ : InfinitePlace K} {a : ℕ}
    (ha : a * w₀.mult = finrank ℚ K) {π : Fin (Fintype.card ι) ≃ ι} {μ : ℕ → ℝ} {C Q γ : ℝ}
    {k p : ℕ} (hγ : 0 < γ) (hμ : ∀ j < Fintype.card ι, 0 < μ j) (hk : 0 < k)
    (hkN : k < Fintype.card ι) :
    approxWeight Sfin (gridExponent (fun v (T : Set.powersetCard ι p) ↦ ∑ t ∈ (T : Finset ι),
        c v t) γ (minimaGrid w₀ a k p π ⌈Real.logb Q C / γ⌉
          ⌈Real.logb Q (μ (k - 1) / μ k) / γ⌉ fun i ↦ ⌈Real.logb Q (μ i) / γ⌉))
      ≤ approxWeight Sfin (wedgeExponentAt c w₀ a π μ C Q k p) +
        γ * (finrank ℚ K * Fintype.card (Set.powersetCard ι p) * (p + 2)) := by
  have hna : ∀ v : FinitePlace K, IsNonarchimedean v.1 := fun v a b ↦ v.add_le a b
  refine (approxWeight_le_add_of_le (fun w T ↦ gridExponent_minimaGrid_le hγ hμ hk hkN w T)
    fun v _ T ↦ le_of_eq ?_).trans (le_of_eq ?_)
  · rw [gridExponent_of_forall_ne _ _ (fun w hcc ↦ InfinitePlace.not_isNonarchimedean w
      (by rw [hcc]; exact hna v)) T]
    simp only [wedgeExponentAt, hna v, ↓reduceIte, add_zero]
  · have hsum : ∑ w : InfinitePlace K, (w.mult : ℝ) * (γ + if w = w₀ then
        γ * (((p : ℝ) + 1) * a) else 0) = γ * (finrank ℚ K * (p + 2)) := by
      simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      have hd : ∑ w : InfinitePlace K, (w.mult : ℝ) = finrank ℚ K := by
        exact_mod_cast InfinitePlace.sum_mult_eq
      have ha' : (a : ℝ) * w₀.mult = finrank ℚ K := by exact_mod_cast ha
      rw [← Finset.sum_mul, hd]
      linear_combination γ * (p + 1) * ha'
    rw [hsum]
    ring

open scoped Classical in
/-- **The entries of a grid of the minima, weighted by the multiplicities**: at most
`[K : ℚ] binom(#ι, p) m'` in total if `|z| + |∑ b + j| ≤ m'` for every subset. -/
theorem sum_mult_abs_minimaGrid_le {w₀ : InfinitePlace K} {a k p : ℕ}
    (ha : a * w₀.mult = finrank ℚ K) {π : Fin (Fintype.card ι) ≃ ι} {z j : ℤ}
    {b : Fin (Fintype.card ι) → ℤ} {m' : ℝ}
    (hm : ∀ T : Set.powersetCard ι p, |(z : ℝ)| + |(((∑ t ∈ (T : Finset ι), b (π.symm t) +
      if ∀ t ∈ (T : Finset ι), k ≤ (π.symm t : ℕ) then j else 0 : ℤ)) : ℝ)| ≤ m') :
    ∑ w : InfinitePlace K, (w.mult : ℝ) * ∑ T, |(minimaGrid w₀ a k p π z j b w T : ℝ)|
      ≤ finrank ℚ K * Fintype.card (Set.powersetCard ι p) * m' := by
  set S : Set.powersetCard ι p → ℝ := fun T ↦ |(((∑ t ∈ (T : Finset ι), b (π.symm t) +
      if ∀ t ∈ (T : Finset ι), k ≤ (π.symm t : ℕ) then j else 0 : ℤ)) : ℝ)| with hS
  have hle : ∀ w T, |(minimaGrid w₀ a k p π z j b w T : ℝ)| ≤
      |(z : ℝ)| + if w = w₀ then a * S T else 0 := by
    intro w T
    rw [minimaGrid]
    by_cases hw : w = w₀
    · simp only [hw, ↓reduceIte]
      rw [Int.cast_add, Int.cast_mul, Int.cast_natCast]
      refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [abs_mul, Nat.abs_cast]
    · simp [hw]
  have hd : ∑ w : InfinitePlace K, (w.mult : ℝ) = finrank ℚ K := by
    exact_mod_cast InfinitePlace.sum_mult_eq
  have ha' : (a : ℝ) * w₀.mult = finrank ℚ K := by exact_mod_cast ha
  calc ∑ w : InfinitePlace K, (w.mult : ℝ) * ∑ T, |(minimaGrid w₀ a k p π z j b w T : ℝ)|
      ≤ ∑ w : InfinitePlace K, (w.mult : ℝ) * ∑ T, (|(z : ℝ)| + if w = w₀ then a * S T else 0) :=
        Finset.sum_le_sum fun w _ ↦ mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun T _ ↦ hle w T) (Nat.cast_nonneg _)
    _ = finrank ℚ K * ∑ T, (|(z : ℝ)| + S T) := by
        have h1 : ∀ w : InfinitePlace K, (w.mult : ℝ) *
            ∑ T, (|(z : ℝ)| + if w = w₀ then a * S T else 0) =
            w.mult * (Fintype.card (Set.powersetCard ι p) * |(z : ℝ)|) +
              if w = w₀ then (w₀.mult : ℝ) * (a * ∑ T, S T) else 0 := by
          intro w
          rw [Finset.sum_add_distrib]
          by_cases hw : w = w₀
          · subst hw
            simp only [↓reduceIte, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
              ← Finset.mul_sum]
            ring
          · simp only [hw, ↓reduceIte, Finset.sum_const_zero, Finset.sum_const,
              Finset.card_univ, nsmul_eq_mul]
            ring
        rw [Finset.sum_congr rfl fun w _ ↦ h1 w]
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [← Finset.sum_mul, hd]
        linear_combination (∑ T, S T) * ha'
    _ ≤ finrank ℚ K * ∑ _T : Set.powersetCard ι p, m' :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun T _ ↦ hm T) (Nat.cast_nonneg _)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

omit [NumberField K] [Fintype ι] [LinearOrder ι] in
open scoped Classical in
/-- **The rounded integers stay in a box**: if `|xc| ≤ 1`, the `|x i| ≤ B` and `|y| ≤ 2 B`, the
rounding `z` of `xc` and the rounded sum `∑_{t ∈ T} b (π⁻¹ t) + [top] j` of `p ≤ N` of the `x i`
and of `y` have `|z| + |∑ b + j| ≤ (1 + B N + 2 B) / γ + N + 2`. -/
theorem abs_ceil_add_abs_sum_ceil_le {N : ℕ} {γ B xc y : ℝ} (hγ : 0 < γ) (hB : 0 ≤ B)
    (hxc : |xc| ≤ 1) {x : Fin N → ℝ} (hx : ∀ i, |x i| ≤ B) (hy : |y| ≤ 2 * B) {p : ℕ}
    (hpN : p ≤ N) (f : ι → Fin N) (T : Finset ι) (hT : T.card = p) (P : Prop) [Decidable P] :
    |((⌈xc / γ⌉ : ℤ) : ℝ)| + |(((∑ t ∈ T, ⌈x (f t) / γ⌉ + if P then ⌈y / γ⌉ else 0 : ℤ)) : ℝ)|
      ≤ (1 + B * N + 2 * B) / γ + N + 2 := by
  have hz1 := le_mul_ceil_div hγ xc
  have hz2 := mul_ceil_div_le hγ xc
  have hxc' := abs_le.1 hxc
  have hγz : |γ * ((⌈xc / γ⌉ : ℤ) : ℝ)| ≤ 1 + γ := by
    rw [abs_le]; constructor <;> linarith
  set X : ℝ := ∑ t ∈ T, x (f t) + if P then y else 0 with hX
  have hXB : |X| ≤ B * N + 2 * B := by
    have h1 : |∑ t ∈ T, x (f t)| ≤ B * N := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun t _ ↦ hx (f t)).trans ?_
      rw [Finset.sum_const, hT, nsmul_eq_mul, mul_comm]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hpN) hB
    have h2 : |(if P then y else 0)| ≤ 2 * B := by
      split_ifs
      · exact hy
      · simpa using hB
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  have hS1 : X ≤ γ * (((∑ t ∈ T, ⌈x (f t) / γ⌉ + if P then ⌈y / γ⌉ else 0 : ℤ)) : ℝ) := by
    push_cast
    rw [mul_add, Finset.mul_sum, hX]
    refine add_le_add (Finset.sum_le_sum fun t _ ↦ le_mul_ceil_div hγ _) ?_
    split_ifs
    · exact le_mul_ceil_div hγ _
    · simp
  have hS2 : γ * (((∑ t ∈ T, ⌈x (f t) / γ⌉ + if P then ⌈y / γ⌉ else 0 : ℤ)) : ℝ) ≤
      X + (p + 1) * γ := by
    push_cast
    rw [mul_add, Finset.mul_sum, hX]
    have h1 : ∑ t ∈ T, γ * (⌈x (f t) / γ⌉ : ℝ) ≤ ∑ t ∈ T, x (f t) + p * γ := by
      have := Finset.sum_le_sum fun t (_ : t ∈ T) ↦ mul_ceil_div_le hγ (x (f t))
      rwa [Finset.sum_add_distrib, Finset.sum_const, hT, nsmul_eq_mul] at this
    have h2 : (γ * if P then (⌈y / γ⌉ : ℝ) else 0) ≤ (if P then y else 0) + γ := by
      split_ifs
      · exact mul_ceil_div_le hγ _
      · simp only [mul_zero, zero_add]; exact hγ.le
    linarith
  have hpN' : (p : ℝ) ≤ N := by exact_mod_cast hpN
  have hγS : |γ * (((∑ t ∈ T, ⌈x (f t) / γ⌉ + if P then ⌈y / γ⌉ else 0 : ℤ)) : ℝ)| ≤
      B * N + 2 * B + (N + 1) * γ := by
    have hX' := abs_le.1 hXB
    rw [abs_le]; constructor <;> nlinarith
  rw [abs_mul, abs_of_pos hγ] at hγz hγS
  rw [div_add' _ _ _ hγ.ne', div_add' _ _ _ hγ.ne', le_div_iff₀ hγ]
  nlinarith

/-- **The number of grids of the minima**: at most `(#ι)! (2 m + 1) ^ (#ι + 2)` — one bijection,
and `#ι + 2` integers. -/
theorem ncard_minimaGridSet_le (w₀ : InfinitePlace K) (a k p : ℕ) (m : ℤ) :
    (minimaGridSet K ι w₀ a k p m).ncard
      ≤ (Fintype.card ι).factorial * (2 * m + 1).toNat ^ (Fintype.card ι + 2) := by
  classical
  set P := (Finset.univ : Finset (Fin (Fintype.card ι) ≃ ι)) ×ˢ
    (Finset.Icc (-m) m ×ˢ (Finset.Icc (-m) m ×ˢ
      Fintype.piFinset fun _ : Fin (Fintype.card ι) ↦ Finset.Icc (-m) m)) with hP
  have hsub : minimaGridSet K ι w₀ a k p m
      ⊆ ↑(P.image fun q ↦ minimaGrid w₀ a k p q.1 q.2.1 q.2.2.1 q.2.2.2) := by
    rintro g ⟨π, z, j, b, hz, hj, hb, rfl⟩
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨(π, z, j, b), ?_, rfl⟩)
    simp only [hP, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, Fintype.mem_piFinset,
      true_and]
    exact ⟨abs_le.1 hz, abs_le.1 hj, fun i ↦ abs_le.1 (hb i)⟩
  refine (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans ?_
  rw [Set.ncard_coe_finset]
  refine Finset.card_image_le.trans (le_of_eq ?_)
  rw [hP, Finset.card_product, Finset.card_product, Finset.card_product, Finset.card_univ,
    Fintype.card_equiv (Fintype.equivFin ι).symm, Fintype.card_fin,
    Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Int.card_Icc,
    show m + 1 - -m = 2 * m + 1 by ring, pow_add, pow_two]
  ring

/-- There are finitely many grids of the minima with bounded integers. -/
theorem finite_minimaGridSet (w₀ : InfinitePlace K) (a k p : ℕ) (m : ℤ) :
    (minimaGridSet K ι w₀ a k p m).Finite := by
  classical
  refine Set.Finite.subset (Finset.finite_toSet (((Finset.univ : Finset
      (Fin (Fintype.card ι) ≃ ι)) ×ˢ (Finset.Icc (-m) m ×ˢ (Finset.Icc (-m) m ×ˢ
      Fintype.piFinset fun _ : Fin (Fintype.card ι) ↦ Finset.Icc (-m) m))).image
      fun q ↦ minimaGrid w₀ a k p q.1 q.2.1 q.2.2.1 q.2.2.2)) ?_
  rintro g ⟨π, z, j, b, hz, hj, hb, rfl⟩
  refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨(π, z, j, b), ?_, rfl⟩)
  simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, Fintype.mem_piFinset, true_and]
  exact ⟨abs_le.1 hz, abs_le.1 hj, fun i ↦ abs_le.1 (hb i)⟩

end NumberField
