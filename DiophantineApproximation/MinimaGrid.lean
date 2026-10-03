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
`π`. Rounding the `#ι` numbers `logb Q μ i` (Evertse 1996, Lemma 18; Evertse–Schlickewei 2002,
Lemma 18.1) gives the **grid of the minima** `NumberField.minimaGrid`, and there are at most
`(#ι)! (2 m + 1) ^ #ι` of them: singly exponential in `#ι`, and independent of the number of
infinite places. The constant and the jump take no integers of their own: for
`0 ≤ logb Q C ≤ γ` the constant rounds to `1`, and the top block, of `p = #ι - k` indices,
contains `k`, so its sum plus the jump is the sum with `k - 1` in place of `k`, rounded by
`b (k - 1) - b k` (`NumberField.minimaJump`). An entry at `w₀` collects `a p + 1` roundings, but
`w₀` carries `mult w₀ = [K : ℚ] / a` in the weight, so the total cost in the weight is
`[K : ℚ] (p + 1)` meshes per subset, as if every infinite place had collected `p + 1`.

## Main definitions

* `NumberField.minimaGrid`: the integers of a grid system, from a bijection `π`, a constant `z`, a
  jump `j` and integers `b` for the minima.
* `NumberField.minimaJump`: the jump `b (k - 1) - b k` of the grids that occur.
* `NumberField.minimaGridSet`: the grids of the minima with bounded integers.

## Main results

* `NumberField.le_gridExponent_minimaGrid`, `NumberField.gridExponent_minimaGrid_le`: rounding the
  minima up dominates the wedge exponents, and costs at most one mesh, plus `a p` at `w₀`.
* `NumberField.approxWeight_gridExponent_minimaGrid_le`: the cost in the weight is
  `γ [K : ℚ] binom(#ι, p) (p + 1)`.
* `NumberField.sum_mult_abs_minimaGrid_le`: the entries of a grid, weighted by the multiplicities,
  are bounded by those of the integers at one place.
* `NumberField.ncard_minimaGridSet_le`: there are at most `(#ι)! (2 m + 1) ^ #ι` grids of the
  minima.

## References

J.-H. Evertse, "An improvement of the quantitative subspace theorem", *Compositio Mathematica*
**101** (1996), 225–311, Lemma 18 and (6.53).

J.-H. Evertse and H. P. Schlickewei, "A quantitative version of the absolute subspace theorem",
*J. reine angew. Math.* **548** (2002), 21–127, Lemmas 17.2 and 18.1.

This is part of Layer 6.1 of the `DiophantineApproximation` roadmap, and items Q1.7, Q1.8c and Q1.9b
of the `QuantitativeSubspace` roadmap.
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

/-- **The jump of a grid of the minima**, `b (k - 1) - b k` (`0` if `k` is out of range): the
top block `{k, …}` of size `p = #ι - k` contains `k`, so rounding `logb Q μ (k - 1)` and the
`logb Q μ i` of the top block other than `k` rounds the top block's sum plus the jump, and the
jump needs no integer of its own. -/
def minimaJump {n : ℕ} (k : ℕ) (b : Fin n → ℤ) : ℤ :=
  if h : 0 < k ∧ k < n then b ⟨k - 1, by omega⟩ - b ⟨k, h.2⟩ else 0

variable (K ι) in
/-- **The grids of the minima at `w₀` with integers in `[-m, m]`**, for one `k` and one `p`: the
constant is `1` and the jump is `NumberField.minimaJump`, so a grid is a bijection and `#ι`
integers. -/
def minimaGridSet (w₀ : InfinitePlace K) (a k p : ℕ) (m : ℤ) :
    Set (InfinitePlace K → Set.powersetCard ι p → ℤ) :=
  {g | ∃ (π : Fin (Fintype.card ι) ≃ ι) (b : Fin (Fintype.card ι) → ℤ),
      (∀ i, |b i| ≤ m) ∧ g = minimaGrid w₀ a k p π 1 (minimaJump k b) b}

omit [NumberField K] [LinearOrder ι] in
/-- **The top block contains `k`**: a `p`-subset `T` with `π⁻¹ t ≥ k` for all `t ∈ T`, where
`k + p = #ι`, contains `π k`. -/
theorem mem_of_forall_le {k p : ℕ} (hkN : k < Fintype.card ι) (hkp : k + p = Fintype.card ι)
    (π : Fin (Fintype.card ι) ≃ ι) {T : Finset ι} (hT : T.card = p)
    (htop : ∀ t ∈ T, k ≤ (π.symm t : ℕ)) : π ⟨k, hkN⟩ ∈ T := by
  classical
  by_contra h
  have hsub : T.image (fun t ↦ (π.symm t : ℕ)) ⊆ Finset.Ico (k + 1) (Fintype.card ι) := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hx
    refine Finset.mem_Ico.2 ⟨?_, (π.symm t).2⟩
    rcases (htop t ht).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      refine h ?_
      have : π.symm t = ⟨k, hkN⟩ := Fin.ext heq.symm
      rw [← this, Equiv.apply_symm_apply]
      exact ht
  have hinj : Set.InjOn (fun t ↦ (π.symm t : ℕ)) T := fun x _ y _ hxy ↦
    π.symm.injective (Fin.ext hxy)
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Nat.card_Ico] at this
  omega

omit [NumberField K] in
open scoped Classical in
/-- On the top block, the rounded sum plus the jump is the sum over the top block with `k`
replaced by `k - 1`. -/
theorem sum_add_minimaJump_eq {k p : ℕ} (hk : 0 < k) (hkN : k < Fintype.card ι)
    (hkp : k + p = Fintype.card ι) (π : Fin (Fintype.card ι) ≃ ι) {T : Finset ι} (hT : T.card = p)
    (htop : ∀ t ∈ T, k ≤ (π.symm t : ℕ)) {M : Type*} [AddCommGroup M]
    (b : Fin (Fintype.card ι) → M) :
    ∑ t ∈ T, b (π.symm t) + (b ⟨k - 1, by omega⟩ - b ⟨k, hkN⟩)
      = ∑ t ∈ T.erase (π ⟨k, hkN⟩), b (π.symm t) + b ⟨k - 1, by omega⟩ := by
  rw [← Finset.add_sum_erase T _ (mem_of_forall_le hkN hkp π hT htop), Equiv.symm_apply_apply]
  abel

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

omit [NumberField K] in
open scoped Classical in
/-- **The rounded minima on a subset**: with `b i = ⌈logb Q μ i / γ⌉` and the jump
`NumberField.minimaJump`, the sum over `T` of the `γ b` plus `γ j` on the top block lies between
the sum of the `logb Q μ` plus the jump and that plus `p γ`. -/
private theorem minima_bracket (Q : ℝ) (hγ : 0 < γ) (hμ : ∀ j < Fintype.card ι, 0 < μ j)
    (hk : 0 < k) (hkN : k < Fintype.card ι) (hkp : k + p = Fintype.card ι)
    (T : Set.powersetCard ι p) :
    (∑ t ∈ (T : Finset ι), Real.logb Q (μ (π.symm t)) +
        if ∀ t ∈ (T : Finset ι), k ≤ (π.symm t : ℕ) then Real.logb Q (μ (k - 1) / μ k) else 0)
      ≤ ∑ t ∈ (T : Finset ι), γ * ⌈Real.logb Q (μ (π.symm t)) / γ⌉ +
        (if ∀ t ∈ (T : Finset ι), k ≤ (π.symm t : ℕ)
          then γ * (minimaJump k fun i : Fin (Fintype.card ι) ↦ ⌈Real.logb Q (μ i) / γ⌉) else 0) ∧
    (∑ t ∈ (T : Finset ι), γ * ⌈Real.logb Q (μ (π.symm t)) / γ⌉ +
        if ∀ t ∈ (T : Finset ι), k ≤ (π.symm t : ℕ)
          then γ * (minimaJump k fun i : Fin (Fintype.card ι) ↦ ⌈Real.logb Q (μ i) / γ⌉) else 0)
      ≤ (∑ t ∈ (T : Finset ι), Real.logb Q (μ (π.symm t)) +
        if ∀ t ∈ (T : Finset ι), k ≤ (π.symm t : ℕ) then Real.logb Q (μ (k - 1) / μ k) else 0)
        + p * γ := by
  set x : Fin (Fintype.card ι) → ℝ := fun i ↦ Real.logb Q (μ i) with hx
  set b : Fin (Fintype.card ι) → ℤ := fun i ↦ ⌈Real.logb Q (μ i) / γ⌉ with hb
  have hT := Set.powersetCard.card_eq T
  have hlo : ∀ i, x i ≤ γ * b i := fun i ↦ le_mul_ceil_div hγ _
  have hhi : ∀ i, γ * b i ≤ x i + γ := fun i ↦ mul_ceil_div_le hγ _
  change (∑ t ∈ (T : Finset ι), x (π.symm t) + _) ≤ ∑ t ∈ (T : Finset ι), γ * (b (π.symm t) : ℝ)
      + _ ∧ (∑ t ∈ (T : Finset ι), γ * (b (π.symm t) : ℝ) + _) ≤ _
  by_cases htop : ∀ t ∈ (T : Finset ι), k ≤ (π.symm t : ℕ)
  · have hmem := mem_of_forall_le hkN hkp π hT htop
    have hX : (∑ t ∈ (T : Finset ι), x (π.symm t) + Real.logb Q (μ (k - 1) / μ k))
        = ∑ t ∈ (T : Finset ι).erase (π ⟨k, hkN⟩), x (π.symm t) + x ⟨k - 1, by omega⟩ := by
      rw [Real.logb_div (hμ _ (by omega)).ne' (hμ _ hkN).ne', ← sum_add_minimaJump_eq hk hkN hkp π
        hT htop x]
    have hY : (∑ t ∈ (T : Finset ι), γ * (b (π.symm t) : ℝ) + γ * (minimaJump k b : ℝ))
        = ∑ t ∈ (T : Finset ι).erase (π ⟨k, hkN⟩), γ * (b (π.symm t) : ℝ)
          + γ * b ⟨k - 1, by omega⟩ := by
      rw [minimaJump, dite_eq_left ⟨hk, hkN⟩, ← sum_add_minimaJump_eq hk hkN hkp π hT htop
        (fun i ↦ γ * (b i : ℝ))]
      push_cast
      ring
    rw [ite_eq_left htop, ite_eq_left htop, hX, hY]
    have hcard := Finset.card_erase_add_one hmem
    rw [hT] at hcard
    have hs1 := Finset.sum_le_sum fun t (_ : t ∈ (T : Finset ι).erase (π ⟨k, hkN⟩)) ↦
      hlo (π.symm t)
    have hs2 := Finset.sum_le_sum fun t (_ : t ∈ (T : Finset ι).erase (π ⟨k, hkN⟩)) ↦
      hhi (π.symm t)
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hs2
    have hc : (((T : Finset ι).erase (π ⟨k, hkN⟩)).card : ℝ) + 1 = p := by exact_mod_cast hcard
    have h1 := hlo ⟨k - 1, by omega⟩
    have h2 := hhi ⟨k - 1, by omega⟩
    constructor
    · linarith
    · nlinarith
  · simp only [htop, ↓reduceIte, add_zero]
    have hs1 := Finset.sum_le_sum fun t (_ : t ∈ (T : Finset ι)) ↦ hlo (π.symm t)
    have hs2 := Finset.sum_le_sum fun t (_ : t ∈ (T : Finset ι)) ↦ hhi (π.symm t)
    rw [Finset.sum_add_distrib, Finset.sum_const, hT, nsmul_eq_mul] at hs2
    exact ⟨hs1, by linarith⟩

open scoped Classical in
/-- **Rounding the minima up dominates the wedge exponents**: with the constant `1`, which
dominates `logb Q C ≤ γ`, the `b i = ⌈logb Q μ i / γ⌉` and the jump `NumberField.minimaJump`, the
grid exponent is at least the wedge exponent at every infinite place. -/
theorem le_gridExponent_minimaGrid (hγ : 0 < γ)
    (hμ : ∀ j < Fintype.card ι, 0 < μ j) (hk : 0 < k) (hkN : k < Fintype.card ι)
    (hkp : k + p = Fintype.card ι) (hC : Real.logb Q C ≤ γ)
    (w : InfinitePlace K) (T : Set.powersetCard ι p) :
    wedgeExponentAt c w₀ a π μ C Q k p w.1 T
      ≤ gridExponent (fun v (T : Set.powersetCard ι p) ↦ ∑ t ∈ (T : Finset ι), c v t) γ
        (minimaGrid w₀ a k p π 1
          (minimaJump k fun i : Fin (Fintype.card ι) ↦ ⌈Real.logb Q (μ i) / γ⌉)
          fun i ↦ ⌈Real.logb Q (μ i) / γ⌉) w.1 T := by
  rw [wedgeExponentAt_eq hμ hk hkN, gridExponent_minimaGrid_eq]
  have hz : Real.logb Q C ≤ γ * ((1 : ℤ) : ℝ) := by rw [Int.cast_one, mul_one]; exact hC
  by_cases hw : w = w₀
  · simp only [hw, ↓reduceIte]
    refine add_le_add le_rfl (add_le_add hz ?_)
    exact mul_le_mul_of_nonneg_right (minima_bracket Q hγ hμ hk hkN hkp T).1 (Nat.cast_nonneg a)
  · simp only [hw, ↓reduceIte, add_zero]
    exact add_le_add le_rfl hz

open scoped Classical in
/-- **Rounding the minima up costs at most one mesh**, and `a p` more at `w₀`, if
`0 ≤ logb Q C`. -/
theorem gridExponent_minimaGrid_le (hγ : 0 < γ)
    (hμ : ∀ j < Fintype.card ι, 0 < μ j) (hk : 0 < k) (hkN : k < Fintype.card ι)
    (hkp : k + p = Fintype.card ι) (hC : 0 ≤ Real.logb Q C)
    (w : InfinitePlace K) (T : Set.powersetCard ι p) :
    gridExponent (fun v (T : Set.powersetCard ι p) ↦ ∑ t ∈ (T : Finset ι), c v t) γ
        (minimaGrid w₀ a k p π 1
          (minimaJump k fun i : Fin (Fintype.card ι) ↦ ⌈Real.logb Q (μ i) / γ⌉)
          fun i ↦ ⌈Real.logb Q (μ i) / γ⌉) w.1 T
      ≤ wedgeExponentAt c w₀ a π μ C Q k p w.1 T +
        (γ + if w = w₀ then γ * ((p : ℝ) * a) else 0) := by
  rw [wedgeExponentAt_eq hμ hk hkN, gridExponent_minimaGrid_eq]
  have hz : γ * ((1 : ℤ) : ℝ) ≤ Real.logb Q C + γ := by rw [Int.cast_one, mul_one]; linarith
  by_cases hw : w = w₀
  · simp only [hw, ↓reduceIte]
    have h := mul_le_mul_of_nonneg_right (minima_bracket (π := π) Q hγ hμ hk hkN hkp T).2
      (Nat.cast_nonneg a)
    nlinarith
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
/-- **The cost of rounding the minima in the weight**: `γ [K : ℚ] binom(#ι, p) (p + 1)`, the
place `w₀` carrying `mult w₀ a p = [K : ℚ] p` of it. -/
theorem approxWeight_gridExponent_minimaGrid_le {Sfin : Finset (FinitePlace K)}
    {c : AbsoluteValue K ℝ → ι → ℝ} {w₀ : InfinitePlace K} {a : ℕ}
    (ha : a * w₀.mult = finrank ℚ K) {π : Fin (Fintype.card ι) ≃ ι} {μ : ℕ → ℝ} {C Q γ : ℝ}
    {k p : ℕ} (hγ : 0 < γ) (hμ : ∀ j < Fintype.card ι, 0 < μ j) (hk : 0 < k)
    (hkN : k < Fintype.card ι) (hkp : k + p = Fintype.card ι) (hC : 0 ≤ Real.logb Q C) :
    approxWeight Sfin (gridExponent (fun v (T : Set.powersetCard ι p) ↦ ∑ t ∈ (T : Finset ι),
        c v t) γ (minimaGrid w₀ a k p π 1
          (minimaJump k fun i : Fin (Fintype.card ι) ↦ ⌈Real.logb Q (μ i) / γ⌉)
          fun i ↦ ⌈Real.logb Q (μ i) / γ⌉))
      ≤ approxWeight Sfin (wedgeExponentAt c w₀ a π μ C Q k p) +
        γ * (finrank ℚ K * Fintype.card (Set.powersetCard ι p) * (p + 1)) := by
  have hna : ∀ v : FinitePlace K, IsNonarchimedean v.1 := fun v a b ↦ v.add_le a b
  refine (approxWeight_le_add_of_le
    (fun w T ↦ gridExponent_minimaGrid_le hγ hμ hk hkN hkp hC w T)
    fun v _ T ↦ le_of_eq ?_).trans (le_of_eq ?_)
  · rw [gridExponent_of_forall_ne _ _ (fun w hcc ↦ InfinitePlace.not_isNonarchimedean w
      (by rw [hcc]; exact hna v)) T]
    simp only [wedgeExponentAt, hna v, ↓reduceIte, add_zero]
  · have hsum : ∑ w : InfinitePlace K, (w.mult : ℝ) * (γ + if w = w₀ then
        γ * ((p : ℝ) * a) else 0) = γ * (finrank ℚ K * (p + 1)) := by
      simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      have hd : ∑ w : InfinitePlace K, (w.mult : ℝ) = finrank ℚ K := by
        exact_mod_cast InfinitePlace.sum_mult_eq
      have ha' : (a : ℝ) * w₀.mult = finrank ℚ K := by exact_mod_cast ha
      rw [← Finset.sum_mul, hd]
      linear_combination γ * p * ha'
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

omit [NumberField K] in
open scoped Classical in
/-- **The rounded integers stay in a box**: if the `|b i| ≤ m`, the sum `∑_{t ∈ T} b (π⁻¹ t)` over
a `p`-subset, plus the jump `NumberField.minimaJump` on the top block, is at most `p m` in absolute
value: on the top block it is a sum of `p` of the `b i` too. -/
theorem abs_sum_add_minimaJump_le {k p : ℕ} (hk : 0 < k) (hkN : k < Fintype.card ι)
    (hkp : k + p = Fintype.card ι) (π : Fin (Fintype.card ι) ≃ ι) {m : ℤ}
    {b : Fin (Fintype.card ι) → ℤ} (hb : ∀ i, |b i| ≤ m) (T : Finset ι) (hT : T.card = p) :
    |∑ t ∈ T, b (π.symm t) + if ∀ t ∈ T, k ≤ (π.symm t : ℕ) then minimaJump k b else 0|
      ≤ p * m := by
  by_cases htop : ∀ t ∈ T, k ≤ (π.symm t : ℕ)
  · have hmem := mem_of_forall_le hkN hkp π hT htop
    rw [ite_eq_left htop, minimaJump, dite_eq_left ⟨hk, hkN⟩,
      sum_add_minimaJump_eq hk hkN hkp π hT htop b]
    have hcard := Finset.card_erase_add_one hmem
    have h1 : |∑ t ∈ T.erase (π ⟨k, hkN⟩), b (π.symm t)| ≤ (T.erase (π ⟨k, hkN⟩)).card * m :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        ((Finset.sum_le_card_nsmul _ _ _ fun t _ ↦ hb _).trans (by rw [nsmul_eq_mul]))
    refine (abs_add_le _ _).trans ?_
    have h2 := hb ⟨k - 1, by omega⟩
    have : ((T.erase (π ⟨k, hkN⟩)).card : ℤ) + 1 = p := by rw [← hT]; exact_mod_cast hcard
    rw [← this, add_mul, one_mul]
    linarith
  · simp only [htop, ↓reduceIte, add_zero]
    refine (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_card_nsmul _ _ _ fun t _ ↦ hb _).trans ?_)
    rw [nsmul_eq_mul, hT]

/-- **The number of grids of the minima**: at most `(#ι)! (2 m + 1) ^ #ι` — one bijection, and
`#ι` integers for the minima; the constant and the jump cost nothing. -/
theorem ncard_minimaGridSet_le (w₀ : InfinitePlace K) (a k p : ℕ) (m : ℤ) :
    (minimaGridSet K ι w₀ a k p m).ncard
      ≤ (Fintype.card ι).factorial * (2 * m + 1).toNat ^ Fintype.card ι := by
  classical
  set P := (Finset.univ : Finset (Fin (Fintype.card ι) ≃ ι)) ×ˢ
      Fintype.piFinset (fun _ : Fin (Fintype.card ι) ↦ Finset.Icc (-m) m) with hP
  have hsub : minimaGridSet K ι w₀ a k p m
      ⊆ ↑(P.image fun q ↦ minimaGrid w₀ a k p q.1 1 (minimaJump k q.2) q.2) := by
    rintro g ⟨π, b, hb, rfl⟩
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨(π, b), ?_, rfl⟩)
    simp only [hP, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, Fintype.mem_piFinset,
      true_and]
    exact fun i ↦ abs_le.1 (hb i)
  refine (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans ?_
  rw [Set.ncard_coe_finset]
  refine Finset.card_image_le.trans (le_of_eq ?_)
  rw [hP, Finset.card_product, Finset.card_univ,
    Fintype.card_equiv (Fintype.equivFin ι).symm, Fintype.card_fin,
    Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Int.card_Icc,
    show m + 1 - -m = 2 * m + 1 by ring]

/-- There are finitely many grids of the minima with bounded integers. -/
theorem finite_minimaGridSet (w₀ : InfinitePlace K) (a k p : ℕ) (m : ℤ) :
    (minimaGridSet K ι w₀ a k p m).Finite := by
  classical
  refine Set.Finite.subset (Finset.finite_toSet (((Finset.univ : Finset
      (Fin (Fintype.card ι) ≃ ι)) ×ˢ
      Fintype.piFinset fun _ : Fin (Fintype.card ι) ↦ Finset.Icc (-m) m).image
      fun q ↦ minimaGrid w₀ a k p q.1 1 (minimaJump k q.2) q.2)) ?_
  rintro g ⟨π, b, hb, rfl⟩
  refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨(π, b), ?_, rfl⟩)
  simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, Fintype.mem_piFinset, true_and]
  exact fun i ↦ abs_le.1 (hb i)

end NumberField
