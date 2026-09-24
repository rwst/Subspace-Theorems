/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.ApproximationDomain
public import Mathlib.NumberTheory.Height.NumberField

/-!
# Systems of exponents on a grid

Step IX of Bombieri–Gubler's proof of the Subspace Theorem replaces the exponents of a wedge
domain — which move with the level `Q` — by exponents drawn from a fixed finite set, at the cost
of enlarging the domain by an arbitrarily small amount. This file is the device, stated for an
arbitrary index type and an arbitrary system of exponents: given a reference system `cT`, a mesh
`γ` and integers `g w T` attached to the infinite places, the **grid system**
`gridExponent cT γ g` is `cT` corrected at each infinite place by `γ` times an integer, and
`roundExponent cT e γ` is the family of integers that rounds `e` up to that grid.

Two properties make it work: a grid system dominates the system it rounds, by at most one mesh;
and for a system confined to a box, the integers are bounded, so there are finitely many grid
systems in play. Beside them the file carries the two monotonicity statements about approximation
domains that Layer 6.1 uses: the domain grows with its exponents, and so does the weight.

## Main results

* `NumberField.approxDomain_subset_of_le`: the domain grows with its exponents.
* `NumberField.approxWeight_le_of_le`: the weight of a system that exceeds another by at most `ε`
  at the infinite places and not at all at the places of `Sfin`.
* `NumberField.gridExponent`, `NumberField.roundExponent`: the grid and the rounding.
* `NumberField.le_gridExponent_roundExponent`, `NumberField.gridExponent_roundExponent_le`:
  rounding up dominates, and costs at most one mesh.
* `NumberField.abs_roundExponent_le`, `NumberField.finite_setOf_abs_le`: the rounded integers of a
  system confined to a box are bounded, and there are finitely many bounded families.

## Implementation notes

⚠ **The correction is attached to the infinite places, not to absolute values.** A system of
exponents is a function of an arbitrary `AbsoluteValue K ℝ`, of which there are infinitely many,
and a domain reads it at the infinite places and at the places of `Sfin` only. If the correction
were defined by rounding at every absolute value the systems in play would not be finite in
number, so `gridExponent` is indexed by a function on `InfinitePlace K` and selects with
`∑ w, if w.1 = v then … else 0`, which is the integer at an infinite place and `0` elsewhere.

⚠ **Nothing is rounded at the finite places.** The exponents of the wedge domain differ from their
reference values only at the archimedean places — a nonarchimedean local bound is exact — so
`gridExponent` leaves the other places alone and `approxWeight_le_of_le` asks for equality there.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
7.5.32 (Step IX).

This is part of Layer 6.1 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Finset Module NumberField NumberField.mixedEmbedding

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

variable {ρ : Type*}

section Grid

variable [Fintype ρ] {Sfin : Finset (FinitePlace K)}
  {L : AbsoluteValue K ℝ → ρ → Dual K (ρ → K)} {f g : AbsoluteValue K ℝ → ρ → ℝ} {Q : ℝ}

omit [Fintype ρ] in
/-- **An approximation domain grows with its exponents**, at a level at least `1`. -/
theorem approxDomain_subset_of_le (hQ : 1 ≤ Q)
    (hinf : ∀ (w : InfinitePlace K) (i : ρ), f w.1 i ≤ g w.1 i)
    (hfin : ∀ v ∈ Sfin, ∀ i : ρ, f v.1 i ≤ g v.1 i) :
    approxDomain Sfin L f Q ⊆ approxDomain Sfin L g Q := by
  rintro x ⟨h1, h2, h3⟩
  exact ⟨fun w i ↦ (h1 w i).trans (Real.rpow_le_rpow_of_exponent_le hQ (hinf w i)),
    fun v hv i ↦ (h2 v hv i).trans (Real.rpow_le_rpow_of_exponent_le hQ (hfin v hv i)),
    h3⟩

/-- **The weight of a system of exponents that exceeds another by at most `ε` at the infinite
places and not at all at the places of `Sfin`.** -/
theorem approxWeight_le_of_le {ε : ℝ}
    (hinf : ∀ (w : InfinitePlace K) (i : ρ), f w.1 i ≤ g w.1 i + ε)
    (hfin : ∀ v ∈ Sfin, ∀ i : ρ, f v.1 i ≤ g v.1 i) :
    approxWeight Sfin f ≤ approxWeight Sfin g + ε * (finrank ℚ K * Fintype.card ρ) := by
  have hmult : ∑ w : InfinitePlace K, (w.mult : ℝ) = finrank ℚ K := by
    rw [← Nat.cast_sum, ← NumberField.totalWeight_eq_sum_mult K,
      NumberField.totalWeight_eq_finrank]
  have h1 : ∀ w : InfinitePlace K, (w.mult : ℝ) * ∑ i, f w.1 i
      ≤ (w.mult : ℝ) * ∑ i, g w.1 i + (w.mult : ℝ) * (ε * Fintype.card ρ) := by
    intro w
    have hsum : ∑ i, f w.1 i ≤ ∑ i, g w.1 i + ε * Fintype.card ρ := by
      have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hinf w i)
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
      linarith [this]
    have hm : (0 : ℝ) ≤ (w.mult : ℝ) := Nat.cast_nonneg _
    nlinarith [hsum]
  have h2 : ∀ v ∈ Sfin, ∑ i, f v.1 i ≤ ∑ i, g v.1 i :=
    fun v hv ↦ Finset.sum_le_sum fun i _ ↦ hfin v hv i
  have hA : ∑ w : InfinitePlace K, (w.mult : ℝ) * ∑ i, f w.1 i
      ≤ (∑ w : InfinitePlace K, (w.mult : ℝ) * ∑ i, g w.1 i)
        + ε * (finrank ℚ K * Fintype.card ρ) := by
    have := Finset.sum_le_sum (fun w (_ : w ∈ Finset.univ) ↦ h1 w)
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hmult] at this
    calc ∑ w : InfinitePlace K, (w.mult : ℝ) * ∑ i, f w.1 i
        ≤ (∑ w : InfinitePlace K, (w.mult : ℝ) * ∑ i, g w.1 i)
          + finrank ℚ K * (ε * Fintype.card ρ) := this
      _ = _ := by ring
  have hB : ∑ v ∈ Sfin, ∑ i, f v.1 i ≤ ∑ v ∈ Sfin, ∑ i, g v.1 i :=
    Finset.sum_le_sum h2
  rw [approxWeight, approxWeight]
  linarith

end Grid

section GridExponent

variable {γ : ℝ} {cT e : AbsoluteValue K ℝ → ρ → ℝ}

open scoped Classical in
/-- **A system of exponents on a grid**: the sums of the original exponents over each `p`-subset,
corrected at each infinite place by an integer multiple of the mesh `γ`. Every wedge domain of
large level is contained in one of these, and there are finitely many with bounded integers. -/
noncomputable def gridExponent (cT : AbsoluteValue K ℝ → ρ → ℝ) (γ : ℝ)
    (g : InfinitePlace K → ρ → ℤ) : AbsoluteValue K ℝ → ρ → ℝ :=
  fun v T ↦ cT v T + γ * ∑ w : InfinitePlace K, if w.1 = v then (g w T : ℝ) else 0

open scoped Classical in
/-- The value of a grid system at an infinite place. -/
theorem gridExponent_infinitePlace (cT : AbsoluteValue K ℝ → ρ → ℝ)
    (g : InfinitePlace K → ρ → ℤ) (w₀ : InfinitePlace K) (T : ρ) :
    gridExponent cT γ g w₀.1 T = cT w₀.1 T + γ * (g w₀ T : ℝ) := by
  have hsum : (∑ w : InfinitePlace K, if w.1 = w₀.1 then (g w T : ℝ) else 0) = (g w₀ T : ℝ) := by
    rw [Finset.sum_eq_single w₀ (fun w _ hw ↦ ?_) (fun h ↦ absurd (Finset.mem_univ w₀) h)]
    · simp
    · simp only [ite_eq_right_iff]
      exact fun hc ↦ absurd (Subtype.ext hc) hw
  rw [gridExponent, hsum]

open scoped Classical in
/-- The value of a grid system at an absolute value that is no infinite place — at a finite place,
for one — where the correction is absent. -/
theorem gridExponent_of_forall_ne (cT : AbsoluteValue K ℝ → ρ → ℝ)
    (g : InfinitePlace K → ρ → ℤ) {v : AbsoluteValue K ℝ} (hv : ∀ w : InfinitePlace K, w.1 ≠ v)
    (T : ρ) : gridExponent cT γ g v T = cT v T := by
  have hsum : (∑ w : InfinitePlace K, if w.1 = v then (g w T : ℝ) else 0) = 0 := by
    refine Finset.sum_eq_zero fun w _ ↦ ?_
    simp only [ite_eq_right_iff]
    exact fun hc ↦ absurd hc (hv w)
  rw [gridExponent, hsum, mul_zero, add_zero]

open scoped Classical in
/-- **Rounding a system of exponents up to the grid**: at each infinite place, the multiple of
the mesh `γ` just above the deviation from the sums of the original exponents. -/
noncomputable def roundExponent (cT e : AbsoluteValue K ℝ → ρ → ℝ) (γ : ℝ) :
    InfinitePlace K → ρ → ℤ :=
  fun w T ↦ ⌈(e w.1 T - cT w.1 T) / γ⌉

/-- **Rounding up dominates.** -/
theorem le_gridExponent_roundExponent (hγ : 0 < γ) (w : InfinitePlace K) (T : ρ) :
    e w.1 T ≤ gridExponent cT γ (roundExponent cT e γ) w.1 T := by
  rw [gridExponent_infinitePlace, roundExponent]
  have h := Int.le_ceil ((e w.1 T - cT w.1 T) / γ)
  have := (div_le_iff₀ hγ).1 h
  linarith

/-- **Rounding up costs at most one mesh.** -/
theorem gridExponent_roundExponent_le (hγ : 0 < γ) (w : InfinitePlace K) (T : ρ) :
    gridExponent cT γ (roundExponent cT e γ) w.1 T ≤ e w.1 T + γ := by
  rw [gridExponent_infinitePlace, roundExponent]
  have h := Int.ceil_lt_add_one ((e w.1 T - cT w.1 T) / γ)
  have h2 : γ * ((⌈(e w.1 T - cT w.1 T) / γ⌉ : ℤ) : ℝ)
      ≤ γ * ((e w.1 T - cT w.1 T) / γ + 1) :=
    mul_le_mul_of_nonneg_left h.le hγ.le
  rw [mul_add, mul_div_cancel₀ _ hγ.ne', mul_one] at h2
  linarith

omit [NumberField K] in
/-- **The rounded exponents of a system confined to a box are bounded integers.** -/
theorem abs_roundExponent_le {G : ℝ} (hγ : 0 < γ)
    (h : ∀ (w : InfinitePlace K) (T : ρ), |e w.1 T - cT w.1 T| ≤ G)
    (w : InfinitePlace K) (T : ρ) : |roundExponent cT e γ w T| ≤ ⌈G / γ⌉ := by
  rw [roundExponent, abs_le]
  have habs := abs_le.1 (h w T)
  constructor
  · have h1 : (-G) / γ ≤ (e w.1 T - cT w.1 T) / γ := by
      gcongr
      exact habs.1
    have h2 : ⌈(-G) / γ⌉ ≤ ⌈(e w.1 T - cT w.1 T) / γ⌉ := Int.ceil_mono h1
    have h3 : -⌈G / γ⌉ ≤ ⌈(-G) / γ⌉ := by
      rw [neg_div, Int.ceil_neg, neg_le_neg_iff]
      exact Int.floor_le_ceil _
    omega
  · refine Int.ceil_mono ?_
    gcongr
    exact habs.2

/-- **There are finitely many grids with bounded integers.** -/
theorem finite_setOf_abs_le (σ : Type*) [Finite σ] (m : ℤ) :
    {g : InfinitePlace K → σ → ℤ | ∀ w T, |g w T| ≤ m}.Finite := by
  refine Set.Finite.subset (Set.Finite.pi fun w ↦ Set.Finite.pi fun T ↦ Set.finite_Icc (-m) m) ?_
  intro g hg
  simp only [Set.mem_pi, Set.mem_univ, forall_const]
  exact fun w ↦ fun T ↦ Set.mem_Icc.2 (abs_le.1 (hg w T))

end GridExponent

end NumberField
