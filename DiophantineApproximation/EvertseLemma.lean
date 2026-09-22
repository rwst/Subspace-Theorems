/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

-- Used only inside proofs.
import DiophantineApproximation.RationalPlaces
import DiophantineApproximation.SIntegerApproximation
import Mathlib.Algebra.BigOperators.Field
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Evertse's lemma

For a number field `K`, a finite set `Sfin` of finite places, linearly independent forms `L v i`
on `Kⁱ` at every infinite place and every place of `Sfin`, and a basis `x 1, …, x (n+1)` of `Kⁱ`
with `v (L v i (x j)) ≤ ν v i * μ v j`, `μ v` nondecreasing, there are vectors

```text
y j = x j + ∑_{l < j} ξ j l • x l,     ξ j l an Sfin-integer,
```

and bijections `π v` from the vectors to the forms with

```text
v (L v (π v i) (y j)) ≤ C ν v (π v i) min (μ v i) (μ v j)    at the infinite places,
v (L v (π v i) (y j)) ≤   ν v (π v i) min (μ v i) (μ v j)    at the places of Sfin,
```

`C` depending only on `K` and `#ι` (Evertse; Bombieri–Gubler, Lemma 7.5.29). It is the step that
replaces Mahler's theorem on compound convex bodies and Davenport's lemma in Schmidt's proof.

The proof is the book's induction, run over any field with a family of absolute values that
admits simultaneous approximation by a subring, `AbsoluteValue.exists_evertse_of_approx`: remove
the last vector, remove the form whose restriction to the span of the others depends on the
remaining forms with the largest coefficient (7.38), apply the induction, and correct the last
vector by an approximation to the solution of the system (7.40). For a number field the
approximation is `NumberField.exists_forall_apply_add_le`, from `SIntegerApproximation.lean`.

## Main results

* `AbsoluteValue.exists_evertse_of_approx`: the lemma for any places admitting simultaneous
  approximation by a subring `R`, with `P` the places carrying a constant and `N` the
  nonarchimedean places carrying none.
* `NumberField.exists_evertse`: **Evertse's lemma** over a number field, with a weight `ν v i` per
  form.
* `NumberField.exists_evertse_unweighted`: the book's statement, `ν = 1`.

## Implementation notes

⚠ **The constant depends on neither the forms nor `Sfin`.** Bombieri–Gubler let `C` depend on
`K`, `S` and the forms. Their proof gives a constant depending on `K` and the dimension only: the
coefficients of (7.38) are at most `1` at every place, and the approximation constant is the
book's `A_v`, which depends on `K` alone once the finite places are handled exactly. This is not
cosmetic: 7.5.30 applies the lemma to the forms `Q ^ (-c v i) L v i`, which change with `Q`, and
needs one `C` for all of them. Here `C` is chosen before the forms, `Sfin` and the vectors.

⚠ **The forms carry weights instead of being rescaled.** Over `K` the forms `Q ^ (-c v i) L v i`
of 7.5.30 do not have coefficients in `K`, and at a finite place `Q ^ (-c v i)` is not a value of
`v` in general. So the lemma takes a positive weight `ν v i` per form, the hypothesis
`v (L v i (x j)) ≤ ν v i * μ v j` and the conclusion with `ν v (π v i)`; the book's statement is
`ν = 1`, and 7.5.30 takes `ν v i = Q ^ c v i`. In the reduction (7.38) the removed form maximizes
`v (α k) * ν v k` rather than `v (α k)`, which is the rescaled choice without the rescaling.

⚠ **The bijections are chosen from the top, the vectors from the bottom.** The form paired with
the last vector is chosen first, from a relation among the restrictions of all the forms to the
span of the other vectors; the vectors are built from the first upwards. The induction removes
the last vector and one form, so after reindexing by `Fin.succAbove` the smaller instance has the
same shape, and the ambient space never changes: the forms stay forms on `E`, and "restricted to
the span" is "independent rows of values on the first `m` vectors".

⚠ **One estimate serves both kinds of place.** The inductive step is proved once, for a place
whose sums of `n` terms are at most `τ n` times a common bound; `τ n = n` at an infinite place and
`τ n = 1` at a finite one, where the constants that appear collapse to `1`.

⚠ **Four acceptance tests, over `ℚ` in two variables with the standard basis.** For the forms
`± (2/5) X₀ + X₁` at `∞` and `μ = (2/5, 1)`, the constant `9/5` suffices, and `1` does not, for
any real `ξ`: the constant at the infinite places is genuinely larger than at the finite ones. For
`X₀ ± ε X₁` and `μ = (1, ε)` decreasing, no constant works for all `ε`: the minima must be sorted.
And at the `2`-adic place, for `4 X₀ + X₁`, `4 X₀ + 3 X₁` and `μ = (1/4, 1)`, no coefficient
integral at `2` works: the lemma produces `Sfin`-integers, not algebraic integers. The book's
`0 < μ v j` is not assumed; nonnegativity follows from the bounds.

⚠ **The approximation lemma is stated without completions.** With coefficients in `K`, the
solutions `γ v j` of (7.40) lie in `K`, so the book's use of `O_S` as a lattice in `∏_{v ∈ S} K_v`
is replaced by `NumberField.exists_forall_apply_add_le`, which is about `K` alone.

## References

J.-H. Evertse, *An improvement of the quantitative subspace theorem*, Compositio Math. **101**
(1996), 225–311.
E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
7.5.27–7.5.29.

This is Layer 4.4 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Module

section Core

variable {K : Type*} [Field K] {E : Type*} [AddCommGroup E] [Module K E]

namespace AbsoluteValue

/-- A sum of `n` terms is at most `n` times a common bound. -/
private theorem apply_sum_fin_le_mul (v : AbsoluteValue K ℝ) {n : ℕ} (f : Fin n → K) {b : ℝ}
    (h : ∀ i, v (f i) ≤ b) : v (∑ i, f i) ≤ n * b := by
  calc v (∑ i, f i) ≤ ∑ i, v (f i) := v.sum_le _ _
    _ ≤ ∑ _i : Fin n, b := Finset.sum_le_sum fun i _ ↦ h i
    _ = n * b := by simp

/-- A nonarchimedean sum is at most a common nonnegative bound. -/
private theorem apply_sum_fin_le_of_isNonarchimedean {v : AbsoluteValue K ℝ}
    (hv : IsNonarchimedean v)
    {n : ℕ} (f : Fin n → K) {b : ℝ} (hb : 0 ≤ b) (h : ∀ i, v (f i) ≤ b) :
    v (∑ i, f i) ≤ b :=
  Finset.sum_induction f (fun y ↦ v y ≤ b) (fun a c ha hc ↦ (hv a c).trans (max_le ha hc))
    (by simpa using hb) fun i _ ↦ h i

/-- **The reduction at one place** (the book's (7.38)): of `m + 1` independent rows, restricted to
their first `m` coordinates, one — `k₀`, chosen to maximize `v (α k) * ν k` over a relation `α` —
is a combination of the others with coefficients `β i`, `v (β i) * ν i ≤ ν k₀`, and the others
stay independent. -/
private theorem exists_reduction {m : ℕ} (v : AbsoluteValue K ℝ) {a : Fin (m + 1) → Fin (m + 1) → K}
    (ha : LinearIndependent K a) {ν : Fin (m + 1) → ℝ} (hν : ∀ k, 0 < ν k) :
    ∃ k₀ : Fin (m + 1), ∃ β : Fin m → K,
      (∀ j : Fin m, a k₀ j.castSucc = ∑ i, β i * a (k₀.succAbove i) j.castSucc) ∧
      (∀ i, v (β i) * ν (k₀.succAbove i) ≤ ν k₀) ∧
      LinearIndependent K fun i (j : Fin m) ↦ a (k₀.succAbove i) j.castSucc := by
  set ρ : (Fin (m + 1) → K) →ₗ[K] (Fin m → K) := LinearMap.funLeft K K Fin.castSucc with hρ
  set r : Fin (m + 1) → Fin m → K := fun k j ↦ a k j.castSucc with hr
  have hr' : r = ρ ∘ a := rfl
  have hnot : ¬ LinearIndependent K r := fun h ↦ by
    have := h.fintype_card_le_finrank
    simp at this
  obtain ⟨α, hα, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.1 hnot
  obtain ⟨k₀, -, hk₀⟩ := Finset.exists_max_image Finset.univ (fun k ↦ v (α k) * ν k)
    Finset.univ_nonempty
  have hα₀ : α k₀ ≠ 0 := by
    intro h0
    have h1 := hk₀ i₀ (Finset.mem_univ _)
    rw [h0, map_zero, zero_mul] at h1
    have : 0 < v (α i₀) * ν i₀ := mul_pos (v.pos hi₀) (hν i₀)
    linarith
  have hv₀ : 0 < v (α k₀) := v.pos hα₀
  have hrel : ∀ j : Fin m, a k₀ j.castSucc =
      ∑ i, -α (k₀.succAbove i) / α k₀ * a (k₀.succAbove i) j.castSucc := by
    intro j
    have hj := congrFun hα j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hr] at hj
    rw [Fin.sum_univ_succAbove _ k₀] at hj
    have : ∑ i, -α (k₀.succAbove i) / α k₀ * a (k₀.succAbove i) j.castSucc =
        -(∑ i, α (k₀.succAbove i) * a (k₀.succAbove i) j.castSucc) / α k₀ := by
      rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [this, eq_div_iff hα₀]
    linear_combination hj
  refine ⟨k₀, fun i ↦ -α (k₀.succAbove i) / α k₀, hrel, fun i ↦ ?_, ?_⟩
  · simp only
    rw [map_div₀, v.map_neg, div_mul_eq_mul_div, div_le_iff₀ hv₀]
    have := hk₀ (k₀.succAbove i) (Finset.mem_univ _)
    linarith
  · refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ (by simp)
    have htop : Submodule.span K (Set.range r) = ⊤ := by
      rw [hr', Set.range_comp, Submodule.span_image,
        ha.span_eq_top_of_card_eq_finrank (by simp), Submodule.map_top,
        LinearMap.range_eq_top]
      exact LinearMap.funLeft_surjective_of_injective K K _ (Fin.castSucc_injective m)
    rw [← htop]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    rcases Fin.eq_self_or_eq_succAbove k₀ k with rfl | ⟨i, rfl⟩
    · have : r k = ∑ i, (-α (k.succAbove i) / α k) • r (k.succAbove i) := by
        funext j
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hr]
        exact hrel j
      rw [this]
      exact Submodule.sum_mem _ fun i _ ↦
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · exact Submodule.subset_span ⟨i, rfl⟩

/-- **The system (7.40)**: if `m` forms have independent rows of values on `x`, and `x` lies in the
span of `y`, then the values of the forms at any vector are a combination of their values on
`y`. -/
private theorem exists_solve {m : ℕ} (L : Fin m → E →ₗ[K] K) {x y : Fin m → E}
    (hxy : ∀ j, x j ∈ Submodule.span K (Set.range y))
    (hL : LinearIndependent K fun i j ↦ L i (x j)) (x₀ : E) :
    ∃ γ : Fin m → K, ∀ i, L i x₀ = ∑ j, γ j * L i (y j) := by
  classical
  set M : Matrix (Fin m) (Fin m) K := Matrix.of fun i j ↦ L i (x j)
  have hM : IsUnit M := Matrix.linearIndependent_rows_iff_isUnit.1 hL
  obtain ⟨c, hc⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hM fun i ↦ L i x₀
  have hu : ∑ j, c j • x j ∈ Submodule.span K (Set.range y) :=
    Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (hxy j)
  obtain ⟨γ, hγ⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hu
  refine ⟨γ, fun i ↦ ?_⟩
  have h1 := congrFun hc i
  simp only [Matrix.mulVec, dotProduct, M, Matrix.of_apply] at h1
  have h2 := congrArg (L i) hγ
  simp only [map_sum, map_smul, smul_eq_mul] at h2
  rw [← h1, h2]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- **The estimates of the inductive step at one place**, for a place whose sums of `n` terms are
at most `τ n` times a common bound: `τ n = n` at an archimedean place and `τ n = 1` at a
nonarchimedean one. The three conclusions are the bounds for the removed form on the old vectors,
for the kept forms on the new vector, and for the removed form on the new vector. -/
private theorem step_bounds (v : AbsoluteValue K ℝ) (τ : ℕ → ℝ) (hτ0 : ∀ n, 0 ≤ τ n)
    (hτ : ∀ (n : ℕ) (f : Fin n → K) (b : ℝ), 0 ≤ b → (∀ i, v (f i) ≤ b) → v (∑ i, f i) ≤ τ n * b)
    {m : ℕ} {Av Cv : ℝ} (hAv : 0 ≤ Av) (hCv : 0 ≤ Cv)
    {L₀ : E →ₗ[K] K} {L' : Fin m → E →ₗ[K] K} {β : Fin m → K} {V : Submodule K E}
    (hrel : ∀ u ∈ V, L₀ u = ∑ i, β i * L' i u)
    {y' : Fin m → E} (hy'V : ∀ j, y' j ∈ V) {x₀ : E} {γ ξ : Fin m → K}
    (hγ : ∀ i, L' i x₀ = ∑ j, γ j * L' i (y' j)) (hξ : ∀ j, v (ξ j + γ j) ≤ Av)
    {ν₀ μ₀ : ℝ} {ν' μ' : Fin m → ℝ} (hν₀ : 0 < ν₀) (hν' : ∀ i, 0 < ν' i)
    (hμ' : ∀ j, 0 ≤ μ' j) (hμ₀ : ∀ j, μ' j ≤ μ₀)
    (hβ : ∀ i, v (β i) * ν' i ≤ ν₀)
    (hL'y' : ∀ i j, v (L' i (y' j)) ≤ Cv * ν' i * min (μ' i) (μ' j))
    (hL₀x₀ : v (L₀ x₀) ≤ ν₀ * μ₀) (hL'x₀ : ∀ i, v (L' i x₀) ≤ ν' i * μ₀) :
    (∀ j, v (L₀ (y' j)) ≤ τ m * Cv * ν₀ * μ' j) ∧
    (∀ i, v (L' i (x₀ + ∑ j, ξ j • y' j)) ≤ τ m * Av * Cv * ν' i * μ' i) ∧
    v (L₀ (x₀ + ∑ j, ξ j • y' j)) ≤
      τ 2 * max 1 (τ m * (τ 2 * max (τ m * Av * Cv) 1)) * ν₀ * μ₀ := by
  have hμ₀0 : 0 ≤ μ₀ := by
    rcases eq_or_ne m 0 with rfl | hm
    · exact (mul_nonneg_iff_of_pos_left hν₀).1 ((v.nonneg _).trans hL₀x₀)
    · exact (hμ' ⟨0, Nat.pos_of_ne_zero hm⟩).trans (hμ₀ _)
  -- the vectors `y' j` and the removed form
  have ha : ∀ j, v (L₀ (y' j)) ≤ τ m * Cv * ν₀ * μ' j := by
    intro j
    rw [hrel _ (hy'V j), mul_assoc, mul_assoc]
    refine hτ m _ _ (mul_nonneg hCv (mul_nonneg hν₀.le (hμ' j))) fun i ↦ ?_
    rw [map_mul]
    calc v (β i) * v (L' i (y' j)) ≤ v (β i) * (Cv * ν' i * μ' j) :=
          mul_le_mul_of_nonneg_left ((hL'y' i j).trans (mul_le_mul_of_nonneg_left
            (min_le_right _ _) (mul_nonneg hCv (hν' i).le))) (v.nonneg _)
      _ = Cv * (v (β i) * ν' i) * μ' j := by ring
      _ ≤ Cv * ν₀ * μ' j :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hβ i) hCv) (hμ' j)
      _ = Cv * (ν₀ * μ' j) := by ring
  -- the new vector and the forms kept
  have hsum : ∀ i, L' i (x₀ + ∑ j, ξ j • y' j) = ∑ j, (ξ j + γ j) * L' i (y' j) := by
    intro i
    simp only [map_add, map_sum, map_smul, smul_eq_mul, hγ i, add_mul, Finset.sum_add_distrib]
    ring
  have hb : ∀ i, v (L' i (x₀ + ∑ j, ξ j • y' j)) ≤ τ m * Av * Cv * ν' i * μ' i := by
    intro i
    rw [hsum i, mul_assoc, mul_assoc, mul_assoc]
    refine hτ m _ _ (by have := hν' i; have := hμ' i; positivity) fun j ↦ ?_
    rw [map_mul]
    calc v (ξ j + γ j) * v (L' i (y' j)) ≤ Av * (Cv * ν' i * μ' i) :=
          mul_le_mul (hξ j) ((hL'y' i j).trans (mul_le_mul_of_nonneg_left
            (min_le_left _ _) (mul_nonneg hCv (hν' i).le))) (v.nonneg _) hAv
      _ = Av * (Cv * (ν' i * μ' i)) := by ring
  -- the new vector and the removed form
  refine ⟨ha, hb, ?_⟩
  set y₀ := x₀ + ∑ j, ξ j • y' j with hy₀
  have hV : y₀ - x₀ ∈ V := by
    rw [hy₀, add_sub_cancel_left]
    exact V.sum_mem fun j _ ↦ V.smul_mem _ (hy'V j)
  set D := max (τ m * Av * Cv) 1 with hD
  have hD0 : 0 ≤ D := le_max_of_le_right zero_le_one
  have hdiff : ∀ i, v (L' i y₀ - L' i x₀) ≤ τ 2 * D * ν' i * μ₀ := by
    intro i
    have h2 : L' i y₀ - L' i x₀ = ∑ k : Fin 2, ![L' i y₀, -L' i x₀] k := by
      simp [sub_eq_add_neg]
    rw [h2, mul_assoc, mul_assoc]
    refine hτ 2 _ _ (by have := hν' i; positivity) fun k ↦ ?_
    fin_cases k
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      calc v (L' i y₀) ≤ τ m * Av * Cv * ν' i * μ' i := hb i
        _ ≤ D * ν' i * μ₀ :=
            mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _) (hν' i).le) (hμ₀ i)
              (hμ' i) (mul_nonneg hD0 (hν' i).le)
        _ = D * (ν' i * μ₀) := by ring
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        v.map_neg]
      calc v (L' i x₀) ≤ ν' i * μ₀ := hL'x₀ i
        _ ≤ D * (ν' i * μ₀) := by
            have := hν' i
            exact le_mul_of_one_le_left (by positivity) (le_max_right _ _)
  have hlast : L₀ y₀ = ∑ k : Fin 2, ![L₀ x₀, ∑ i, β i * (L' i y₀ - L' i x₀)] k := by
    have := hrel _ hV
    simp only [map_sub, mul_sub, Finset.sum_sub_distrib] at this
    simp only [Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, mul_sub, Finset.sum_sub_distrib]
    linear_combination this
  rw [hlast, mul_assoc, mul_assoc]
  refine hτ 2 _ _ (by positivity) fun k ↦ ?_
  fin_cases k
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    calc v (L₀ x₀) ≤ ν₀ * μ₀ := hL₀x₀
      _ ≤ max 1 (τ m * (τ 2 * D)) * (ν₀ * μ₀) :=
          le_mul_of_one_le_left (by positivity) (le_max_left _ _)
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    calc v (∑ i, β i * (L' i y₀ - L' i x₀)) ≤ τ m * (τ 2 * D * (ν₀ * μ₀)) := by
          refine hτ m _ _ (mul_nonneg (mul_nonneg (hτ0 2) hD0) (mul_nonneg hν₀.le hμ₀0))
            fun i ↦ ?_
          rw [map_mul]
          calc v (β i) * v (L' i y₀ - L' i x₀) ≤ v (β i) * (τ 2 * D * ν' i * μ₀) :=
                mul_le_mul_of_nonneg_left (hdiff i) (v.nonneg _)
            _ = τ 2 * D * (v (β i) * ν' i) * μ₀ := by ring
            _ ≤ τ 2 * D * ν₀ * μ₀ :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hβ i)
                  (mul_nonneg (hτ0 2) hD0)) hμ₀0
            _ = τ 2 * D * (ν₀ * μ₀) := by ring
      _ = τ m * (τ 2 * D) * (ν₀ * μ₀) := by ring
      _ ≤ max 1 (τ m * (τ 2 * D)) * (ν₀ * μ₀) := by
          gcongr
          exact le_max_right _ _

/-- **Evertse's lemma for any places admitting simultaneous approximation** (the induction of
Bombieri–Gubler, Lemma 7.5.29). Let `R ⊆ K` be a subring, `P` and `N` sets of absolute values,
`N` nonarchimedean, such that for all targets `γ v` some `ξ ∈ R` has `v (ξ + γ v) ≤ A` on `P` and
`≤ 1` on `N`. For `m` vectors `x j` and forms `L v k` whose values have independent rows at every
place, bounded by `ν v k * μ v j` with `μ v` monotone, there are vectors `y j`, with `y j - x j` an
`R`-combination of the `x l` with `l < j`, and bijections `π v` of `Fin m`, with
`v (L v (π v i) (y j)) ≤ C * ν v (π v i) * min (μ v i) (μ v j)` on `P` and the same without `C` on
`N`. The constant depends only on `A` and `m`. -/
theorem exists_evertse_of_approx {A : ℝ} (hA : 0 ≤ A) (m : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (R : Subring K) (P N : Set (AbsoluteValue K ℝ)), (∀ v ∈ N, IsNonarchimedean v) →
    (∀ γ : AbsoluteValue K ℝ → K, ∃ ξ ∈ R, (∀ v ∈ P, v (ξ + γ v) ≤ A) ∧
      ∀ v ∈ N, v (ξ + γ v) ≤ 1) →
    ∀ (x : Fin m → E) (L : AbsoluteValue K ℝ → Fin m → E →ₗ[K] K)
      (μ ν : AbsoluteValue K ℝ → Fin m → ℝ),
    (∀ v ∈ P ∪ N, LinearIndependent K fun k j ↦ L v k (x j)) → (∀ v, Monotone (μ v)) →
    (∀ v k, 0 < ν v k) → (∀ v ∈ P ∪ N, ∀ k j, v (L v k (x j)) ≤ ν v k * μ v j) →
    ∃ y : Fin m → E, (∀ j, y j - x j ∈ Submodule.span R (x '' Set.Iio j)) ∧
      (∀ j, x j ∈ Submodule.span K (Set.range y)) ∧
      ∃ π : AbsoluteValue K ℝ → Equiv.Perm (Fin m),
        (∀ v ∈ P, ∀ i j, v (L v (π v i) (y j)) ≤ C * ν v (π v i) * min (μ v i) (μ v j)) ∧
        ∀ v ∈ N, ∀ i j, v (L v (π v i) (y j)) ≤ ν v (π v i) * min (μ v i) (μ v j) := by
  induction m with
  | zero =>
    exact ⟨1, one_pos, fun R P N _ _ x L μ ν _ _ _ _ ↦
      ⟨x, fun j ↦ j.elim0, fun j ↦ j.elim0, fun _ ↦ 1, fun _ _ i ↦ i.elim0,
        fun _ _ i ↦ i.elim0⟩⟩
  | succ m ih =>
    obtain ⟨C, hC, ih⟩ := ih
    set C' : ℝ := max C (max (m * C) (max (m * A * C)
      (2 * max 1 (m * (2 * max (m * A * C) 1))))) with hC'
    refine ⟨C', lt_max_of_lt_left hC, ?_⟩
    intro R P N hN happrox x L μ ν hL hμ hν hLx
    classical
    have hμ0 : ∀ v ∈ P ∪ N, ∀ j, 0 ≤ μ v j := fun v hv j ↦
      (mul_nonneg_iff_of_pos_left (hν v 0)).1 ((v.nonneg _).trans (hLx v hv 0 j))
    have hred : ∀ v : AbsoluteValue K ℝ, ∃ k₀ : Fin (m + 1), ∃ β : Fin m → K, v ∈ P ∪ N →
        (∀ j : Fin m, L v k₀ (x j.castSucc) =
          ∑ i, β i * L v (k₀.succAbove i) (x j.castSucc)) ∧
        (∀ i, v (β i) * ν v (k₀.succAbove i) ≤ ν v k₀) ∧
        LinearIndependent K fun i (j : Fin m) ↦ L v (k₀.succAbove i) (x j.castSucc) := by
      intro v
      by_cases hv : v ∈ P ∪ N
      · obtain ⟨k₀, β, h⟩ := exists_reduction v (hL v hv) (hν v)
        exact ⟨k₀, β, fun _ ↦ h⟩
      · exact ⟨0, 0, fun h ↦ (hv h).elim⟩
    choose k₀ β hred using hred
    set x' : Fin m → E := fun j ↦ x j.castSucc with hx'
    set L' : AbsoluteValue K ℝ → Fin m → E →ₗ[K] K := fun v i ↦ L v ((k₀ v).succAbove i)
      with hL'
    obtain ⟨y', hy'x, hxy', π', hπ'P, hπ'N⟩ := ih R P N hN happrox x' L'
      (fun v j ↦ μ v j.castSucc) (fun v i ↦ ν v ((k₀ v).succAbove i))
      (fun v hv ↦ (hred v hv).2.2) (fun v ↦ (hμ v).comp Fin.strictMono_castSucc.monotone)
      (fun v i ↦ hν v _) (fun v hv i j ↦ hLx v hv _ _)
    -- the span of the first `m` vectors
    set V := Submodule.span K (Set.range x') with hV
    have hy'V : ∀ j, y' j ∈ V := by
      intro j
      have h1 : y' j - x' j ∈ V :=
        Submodule.span_mono (Set.image_subset_range _ _)
          (Submodule.span_le_restrictScalars R K (x' '' Set.Iio j) (hy'x j))
      have h2 : x' j ∈ V := Submodule.subset_span ⟨j, rfl⟩
      simpa using V.add_mem h1 h2
    have hrelV : ∀ v ∈ P ∪ N, ∀ u ∈ V, L v (k₀ v) u = ∑ i, β v i * L' v i u := by
      intro v hv u hu
      induction hu using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨j, rfl⟩ := hz
        exact (hred v hv).1 j
      | zero => simp
      | add a b _ _ ha hb => simp only [map_add, ha, hb, mul_add, Finset.sum_add_distrib]
      | smul c a _ ha =>
        simp only [map_smul, smul_eq_mul, ha, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by ring
    -- solving for the last vector
    have hsolve : ∀ v : AbsoluteValue K ℝ, ∃ γ : Fin m → K, v ∈ P ∪ N →
        ∀ i, L' v (π' v i) (x (Fin.last m)) = ∑ j, γ j * L' v (π' v i) (y' j) := by
      intro v
      by_cases hv : v ∈ P ∪ N
      · obtain ⟨γ, h⟩ := exists_solve (fun i ↦ L' v (π' v i)) hxy'
          ((hred v hv).2.2.comp _ (π' v).injective) (x (Fin.last m))
        exact ⟨γ, fun _ ↦ h⟩
      · exact ⟨0, fun h ↦ (hv h).elim⟩
    choose γ hγ using hsolve
    choose ξ hξR hξP hξN using fun j : Fin m ↦ happrox fun v ↦ γ v j
    -- the new vectors and bijections
    set y : Fin (m + 1) → E :=
      Fin.snoc (α := fun _ ↦ E) y' (x (Fin.last m) + ∑ j, ξ j • y' j) with hy
    set π : AbsoluteValue K ℝ → Equiv.Perm (Fin (m + 1)) := fun v ↦
      finSuccEquivLast.trans ((Equiv.optionCongr (π' v)).trans (finSuccEquiv' (k₀ v)).symm)
      with hπ
    have hπc : ∀ v i, π v i.castSucc = (k₀ v).succAbove (π' v i) := by
      intro v i; simp [hπ]
    have hπl : ∀ v, π v (Fin.last m) = k₀ v := by
      intro v; simp [hπ]
    have hyc : ∀ j, y j.castSucc = y' j := fun j ↦ by simp [hy]
    have hyl : y (Fin.last m) = x (Fin.last m) + ∑ j, ξ j • y' j := by simp [hy]
    have hrelπ : ∀ v ∈ P ∪ N, ∀ u ∈ V,
        L v (k₀ v) u = ∑ i, β v (π' v i) * L' v (π' v i) u := fun v hv u hu ↦ by
      rw [hrelV v hv u hu]
      exact (Equiv.sum_comp (π' v) fun i ↦ β v i * L' v i u).symm
    refine ⟨y, ?_, ?_, π, ?_, ?_⟩
    · intro j
      refine Fin.lastCases ?_ (fun j ↦ ?_) j
      · rw [hyl, add_sub_cancel_left]
        refine Submodule.sum_mem _ fun j _ ↦ ?_
        have hmem : y' j ∈ Submodule.span R (x '' Set.Iio (Fin.last m)) := by
          have h1 : y' j - x' j ∈ Submodule.span R (x '' Set.Iio (Fin.last m)) := by
            refine Submodule.span_mono ?_ (hy'x j)
            rintro _ ⟨l, -, rfl⟩
            exact ⟨l.castSucc, Fin.castSucc_lt_last l, rfl⟩
          have h2 : x' j ∈ Submodule.span R (x '' Set.Iio (Fin.last m)) :=
            Submodule.subset_span ⟨j.castSucc, Fin.castSucc_lt_last j, rfl⟩
          simpa using Submodule.add_mem _ h1 h2
        exact Submodule.smul_mem _ (⟨ξ j, hξR j⟩ : R) hmem
      · rw [hyc]
        refine Submodule.span_mono ?_ (hy'x j)
        rintro _ ⟨l, hl, rfl⟩
        exact ⟨l.castSucc, Fin.castSucc_lt_castSucc_iff.2 hl, rfl⟩
    · have hsub : Submodule.span K (Set.range y') ≤ Submodule.span K (Set.range y) := by
        refine Submodule.span_mono ?_
        rintro _ ⟨j, rfl⟩
        exact ⟨j.castSucc, hyc j⟩
      intro j
      refine Fin.lastCases ?_ (fun j ↦ ?_) j
      · have : x (Fin.last m) = y (Fin.last m) - ∑ j, ξ j • y' j := by rw [hyl]; abel
        rw [this]
        refine Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩) ?_
        exact Submodule.sum_mem _ fun j _ ↦
          Submodule.smul_mem _ _ (hsub (Submodule.subset_span ⟨j, rfl⟩))
      · exact hsub (hxy' j)
    · intro v hvP i j
      have hv : v ∈ P ∪ N := Or.inl hvP
      obtain ⟨ha, hb, hc⟩ := step_bounds v (fun n ↦ n) (fun n ↦ Nat.cast_nonneg n)
        (fun n f b _ h ↦ apply_sum_fin_le_mul v f h) hA hC.le
        (L₀ := L v (k₀ v)) (L' := fun i ↦ L' v (π' v i)) (β := fun i ↦ β v (π' v i))
        (hrelπ v hv) hy'V (hγ v hv) (fun j ↦ hξP j v hvP)
        (ν' := fun i ↦ ν v ((k₀ v).succAbove (π' v i))) (μ' := fun j ↦ μ v j.castSucc)
        (hν v _) (fun i ↦ hν v _) (fun j ↦ hμ0 v hv _) (fun j ↦ hμ v (Fin.le_last _))
        (fun i ↦ (hred v hv).2.1 (π' v i)) (fun i j ↦ hπ'P v hvP i j)
        (hLx v hv _ _) (fun i ↦ hLx v hv _ _)
      have hνk : 0 ≤ ν v (k₀ v) := (hν v _).le
      refine Fin.lastCases ?_ (fun i ↦ ?_) i <;> refine Fin.lastCases ?_ (fun j ↦ ?_) j
      · rw [hπl, hyl, min_self]
        refine hc.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hνk)
          (hμ0 v hv _))
        push_cast
        exact le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
      · rw [hπl, hyc, min_eq_right (hμ v (Fin.le_last _))]
        refine (ha j).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hνk)
          (hμ0 v hv _))
        exact le_max_of_le_right (le_max_left _ _)
      · rw [hπc, hyl, min_eq_left (hμ v (Fin.le_last _))]
        refine (hb i).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_
          (hν v _).le) (hμ0 v hv _))
        exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
      · rw [hπc, hyc]
        refine (hπ'P v hvP i j).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (hν v _).le)
          (le_min (hμ0 v hv _) (hμ0 v hv _)))
    · intro v hvN i j
      have hv : v ∈ P ∪ N := Or.inr hvN
      obtain ⟨ha, hb, hc⟩ := step_bounds v (fun _ ↦ 1) (fun _ ↦ zero_le_one)
        (fun n f b hb h ↦ by
          rw [one_mul]; exact apply_sum_fin_le_of_isNonarchimedean (hN v hvN) f hb h)
        zero_le_one zero_le_one
        (L₀ := L v (k₀ v)) (L' := fun i ↦ L' v (π' v i)) (β := fun i ↦ β v (π' v i))
        (hrelπ v hv) hy'V (hγ v hv) (fun j ↦ hξN j v hvN)
        (ν' := fun i ↦ ν v ((k₀ v).succAbove (π' v i))) (μ' := fun j ↦ μ v j.castSucc)
        (hν v _) (fun i ↦ hν v _) (fun j ↦ hμ0 v hv _) (fun j ↦ hμ v (Fin.le_last _))
        (fun i ↦ (hred v hv).2.1 (π' v i)) (fun i j ↦ by rw [one_mul]; exact hπ'N v hvN i j)
        (hLx v hv _ _) (fun i ↦ hLx v hv _ _)
      simp only [one_mul, max_self] at ha hb hc
      refine Fin.lastCases ?_ (fun i ↦ ?_) i <;> refine Fin.lastCases ?_ (fun j ↦ ?_) j
      · rw [hπl, hyl, min_self]
        exact hc
      · rw [hπl, hyc, min_eq_right (hμ v (Fin.le_last _))]
        exact ha j
      · rw [hπc, hyl, min_eq_left (hμ v (Fin.le_last _))]
        exact hb i
      · rw [hπc, hyc]
        exact hπ'N v hvN i j

end AbsoluteValue

end Core

/-- **Independent forms have independent rows of values on a spanning family.** -/
theorem LinearIndependent.apply_of_span_eq_top {K V κ : Type*} [Field K] [AddCommGroup V]
    [Module K V] {l : κ → Dual K V} (hl : LinearIndependent K l) {n : ℕ} {x : Fin n → V}
    (hx : Submodule.span K (Set.range x) = ⊤) : LinearIndependent K fun k j ↦ l k (x j) := by
  set Φ : Dual K V →ₗ[K] (Fin n → K) := LinearMap.pi fun j ↦ Dual.eval K V (x j) with hΦ
  have hker : LinearMap.ker Φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro φ hφ
    exact LinearMap.ext_on_range hx fun j ↦ by simpa [hΦ] using congrFun hφ j
  exact hl.map' Φ hker

namespace NumberField

variable (K : Type*) [Field K] [NumberField K] (ι : Type*) [Fintype ι]

/-- **Evertse's lemma** (Evertse; Bombieri–Gubler, Lemma 7.5.29, with a weight per form). There is
a constant `C`, depending only on `K` and `#ι`, such that: for forms `L v` independent at every
infinite place and every place of `Sfin`, and a basis `x` of `Kⁱ` with
`v (L v i (x j)) ≤ ν v i * μ v j`, `ν > 0` and `μ v` nondecreasing, there are `Sfin`-integers
`ξ j l` and bijections `π v` such that the vectors `y j = x j + ∑_{l < j} ξ j l • x l` satisfy
`v (L v (π v i) (y j)) ≤ C * ν v (π v i) * min (μ v i) (μ v j)` at the infinite places and the same
without `C` at the places of `Sfin`. -/
theorem exists_evertse : ∃ C : ℝ, 0 < C ∧
    ∀ (Sfin : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)),
    (∀ w : InfinitePlace K, LinearIndependent K (L w.1)) →
    (∀ v ∈ Sfin, LinearIndependent K (L v.1)) →
    ∀ (x : Fin (Fintype.card ι) → ι → K), LinearIndependent K x →
    ∀ (μ : AbsoluteValue K ℝ → Fin (Fintype.card ι) → ℝ) (ν : AbsoluteValue K ℝ → ι → ℝ),
    (∀ v, Monotone (μ v)) → (∀ v i, 0 < ν v i) →
    (∀ (w : InfinitePlace K) i j, w (L w.1 i (x j)) ≤ ν w.1 i * μ w.1 j) →
    (∀ v ∈ Sfin, ∀ i j, v (L v.1 i (x j)) ≤ ν v.1 i * μ v.1 j) →
    ∃ ξ : Fin (Fintype.card ι) → Fin (Fintype.card ι) → K,
      (∀ i j, ∀ v : FinitePlace K, v ∉ Sfin → v (ξ i j) ≤ 1) ∧
      ∃ π : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι,
        (∀ (w : InfinitePlace K) i j,
          w (L w.1 (π w.1 i) (x j + ∑ l ∈ Finset.Iio j, ξ j l • x l)) ≤
            C * ν w.1 (π w.1 i) * min (μ w.1 i) (μ w.1 j)) ∧
        ∀ v ∈ Sfin, ∀ i j,
          v (L v.1 (π v.1 i) (x j + ∑ l ∈ Finset.Iio j, ξ j l • x l)) ≤
            ν v.1 (π v.1 i) * min (μ v.1 i) (μ v.1 j) := by
  classical
  obtain ⟨A, hA, happ⟩ := exists_forall_apply_add_le (K := K)
  obtain ⟨C, hC, hcore⟩ :=
    AbsoluteValue.exists_evertse_of_approx (K := K) (E := ι → K) hA (Fintype.card ι)
  refine ⟨C, hC, fun Sfin L hLInf hLFin x hx μ ν hμ hν hInf hFin ↦ ?_⟩
  set e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm with he
  -- the `Sfin`-integers
  let R : Subring K :=
    { carrier := {z | ∀ v : FinitePlace K, v ∉ Sfin → v z ≤ 1}
      mul_mem' := fun {a b} ha hb v hv ↦ by
        rw [map_mul]
        calc v a * v b ≤ 1 * 1 := mul_le_mul (ha v hv) (hb v hv) (apply_nonneg _ _) zero_le_one
          _ = 1 := one_mul 1
      one_mem' := fun v _ ↦ by rw [map_one]
      add_mem' := fun {a b} ha hb v hv ↦ (v.add_le a b).trans (max_le (ha v hv) (hb v hv))
      zero_mem' := fun v _ ↦ by rw [map_zero]; exact zero_le_one
      neg_mem' := fun {a} ha v hv ↦ by
        rw [FinitePlace.coe_apply, AbsoluteValue.map_neg, ← FinitePlace.coe_apply]
        exact ha v hv }
  set P : Set (AbsoluteValue K ℝ) := Set.range fun w : InfinitePlace K ↦ w.1 with hP
  set N : Set (AbsoluteValue K ℝ) := (fun v : FinitePlace K ↦ v.1) '' (Sfin : Set _) with hN
  have hNna : ∀ v ∈ N, IsNonarchimedean v := by
    rintro _ ⟨u, -, rfl⟩ a b
    exact u.add_le a b
  have happrox : ∀ γ : AbsoluteValue K ℝ → K, ∃ ξ ∈ R, (∀ v ∈ P, v (ξ + γ v) ≤ A) ∧
      ∀ v ∈ N, v (ξ + γ v) ≤ 1 := by
    intro γ
    obtain ⟨ξ, h1, h2, h3⟩ := happ Sfin γ
    refine ⟨ξ, h1, ?_, ?_⟩
    · rintro _ ⟨w, rfl⟩
      exact h3 w
    · rintro _ ⟨u, hu, rfl⟩
      exact h2 u hu
  have hspan : Submodule.span K (Set.range x) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [finrank_span_eq_card hx]; simp)
  have hrows : ∀ v ∈ P ∪ N, LinearIndependent K fun k j ↦ L v (e k) (x j) := by
    rintro _ (⟨w, rfl⟩ | ⟨u, hu, rfl⟩)
    · exact ((hLInf w).comp e e.injective).apply_of_span_eq_top hspan
    · exact ((hLFin u hu).comp e e.injective).apply_of_span_eq_top hspan
  have hbd : ∀ v ∈ P ∪ N, ∀ k j, v (L v (e k) (x j)) ≤ ν v (e k) * μ v j := by
    rintro _ (⟨w, rfl⟩ | ⟨u, hu, rfl⟩) k j
    · exact hInf w (e k) j
    · exact hFin u hu (e k) j
  obtain ⟨y, hyx, -, π, hπP, hπN⟩ := hcore R P N hNna happrox x (fun v k ↦ L v (e k)) μ
    (fun v k ↦ ν v (e k)) hrows hμ (fun v k ↦ hν v _) hbd
  -- the coefficients of `y j` in the `x l`, `l < j`
  have hcoef : ∀ j, ∃ c : Fin (Fintype.card ι) → K,
      (∀ l, ∀ v : FinitePlace K, v ∉ Sfin → v (c l) ≤ 1) ∧
        y j = x j + ∑ l ∈ Finset.Iio j, c l • x l := by
    intro j
    obtain ⟨f, hf, hfx⟩ := (Finsupp.mem_span_image_iff_linearCombination R).1 (hyx j)
    refine ⟨fun l ↦ (f l : K), fun l ↦ (f l).2, ?_⟩
    have hsum : ∑ l ∈ Finset.Iio j, (f l : K) • x l = ∑ l, (f l : K) • x l :=
      Finset.sum_subset (Finset.subset_univ _) fun l _ hl ↦ by
        rw [(Finsupp.mem_supported' R f).1 hf l (by simpa using hl)]
        simp
    rw [hsum, ← sub_eq_iff_eq_add', ← hfx, Finsupp.linearCombination_apply,
      Finsupp.sum_fintype _ _ (by simp)]
    rfl
  choose ξ hξ hyξ using hcoef
  refine ⟨ξ, fun i j v hv ↦ hξ i j v hv, fun v ↦ (π v).trans e, fun w i j ↦ ?_,
    fun v hv i j ↦ ?_⟩
  · rw [← hyξ j]
    exact hπP w.1 ⟨w, rfl⟩ i j
  · rw [← hyξ j]
    exact hπN v.1 ⟨v, hv, rfl⟩ i j

/-- **Evertse's lemma in the book's form** (Bombieri–Gubler, Lemma 7.5.29): the weights are `1`. -/
theorem exists_evertse_unweighted : ∃ C : ℝ, 0 < C ∧
    ∀ (Sfin : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)),
    (∀ w : InfinitePlace K, LinearIndependent K (L w.1)) →
    (∀ v ∈ Sfin, LinearIndependent K (L v.1)) →
    ∀ (x : Fin (Fintype.card ι) → ι → K), LinearIndependent K x →
    ∀ μ : AbsoluteValue K ℝ → Fin (Fintype.card ι) → ℝ, (∀ v, Monotone (μ v)) →
    (∀ (w : InfinitePlace K) i j, w (L w.1 i (x j)) ≤ μ w.1 j) →
    (∀ v ∈ Sfin, ∀ i j, v (L v.1 i (x j)) ≤ μ v.1 j) →
    ∃ ξ : Fin (Fintype.card ι) → Fin (Fintype.card ι) → K,
      (∀ i j, ∀ v : FinitePlace K, v ∉ Sfin → v (ξ i j) ≤ 1) ∧
      ∃ π : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι,
        (∀ (w : InfinitePlace K) i j,
          w (L w.1 (π w.1 i) (x j + ∑ l ∈ Finset.Iio j, ξ j l • x l)) ≤
            C * min (μ w.1 i) (μ w.1 j)) ∧
        ∀ v ∈ Sfin, ∀ i j,
          v (L v.1 (π v.1 i) (x j + ∑ l ∈ Finset.Iio j, ξ j l • x l)) ≤
            min (μ v.1 i) (μ v.1 j) := by
  obtain ⟨C, hC, h⟩ := exists_evertse K ι
  refine ⟨C, hC, fun Sfin L hLInf hLFin x hx μ hμ hInf hFin ↦ ?_⟩
  obtain ⟨ξ, hξ, π, hπInf, hπFin⟩ := h Sfin L hLInf hLFin x hx μ (fun _ _ ↦ 1) hμ
    (fun _ _ ↦ one_pos) (fun w i j ↦ by rw [one_mul]; exact hInf w i j)
    (fun v hv i j ↦ by rw [one_mul]; exact hFin v hv i j)
  refine ⟨ξ, hξ, π, fun w i j ↦ ?_, fun v hv i j ↦ ?_⟩
  · simpa using hπInf w i j
  · simpa using hπFin v hv i j

end NumberField

section Tests

open NumberField

/-- The form `a X₀ + b X₁` on `ℚ²`. -/
private def form2 (a b : ℚ) : Dual ℚ (Fin 2 → ℚ) := a • LinearMap.proj 0 + b • LinearMap.proj 1

private theorem form2_apply (a b : ℚ) (z : Fin 2 → ℚ) : form2 a b z = a * z 0 + b * z 1 := by
  simp [form2]

/-- The standard basis of `ℚ²`, indexed as Evertse's lemma indexes its vectors. -/
private def basis2 : Fin (Fintype.card (Fin 2)) → Fin 2 → ℚ := ![![1, 0], ![0, 1]]

private theorem basis2_zero : basis2 0 = ![1, 0] := rfl

private theorem basis2_one : basis2 1 = ![0, 1] := rfl

/-- The second vector of the lemma, corrected by `ξ` times the first. -/
private theorem basis2_one_add (ξ : Fin (Fintype.card (Fin 2)) → ℚ) :
    basis2 1 + ∑ l ∈ Finset.Iio 1, ξ l • basis2 l = ![ξ 0, 1] := by
  have hI : Finset.Iio (1 : Fin (Fintype.card (Fin 2))) = {0} := by decide
  rw [hI, Finset.sum_singleton, basis2_zero, basis2_one]
  funext k
  fin_cases k <;> simp

private theorem basis2_zero_add (ξ : Fin (Fintype.card (Fin 2)) → ℚ) :
    basis2 0 + ∑ l ∈ Finset.Iio 0, ξ l • basis2 l = ![1, 0] := by
  have hI : Finset.Iio (0 : Fin (Fintype.card (Fin 2))) = ∅ := by decide
  rw [hI, Finset.sum_empty, add_zero, basis2_zero]

/-- A bijection `Fin 2 ≃ Fin 2` is the identity or the swap. -/
private theorem equiv_fin_two_cases (π : Fin (Fintype.card (Fin 2)) ≃ Fin 2) :
    (π 0 = 0 ∧ π 1 = 1) ∨ (π 0 = 1 ∧ π 1 = 0) := by
  have h01 : π 0 ≠ π 1 := π.injective.ne (by decide)
  generalize π 0 = a at h01 ⊢
  generalize π 1 = b at h01 ⊢
  fin_cases a <;> fin_cases b <;> simp_all

private theorem fin_card_two_cases (j : Fin (Fintype.card (Fin 2))) : j = 0 ∨ j = 1 := by
  revert j; decide

private theorem infinitePlace_rat_apply (w : InfinitePlace ℚ) (x : ℚ) : w x = |(x : ℝ)| := by
  rw [Subsingleton.elim w Rat.infinitePlace, Rat.infinitePlace_apply, Rat.cast_abs]

/-- **Conformance: over `ℚ`, the constant `9/5` suffices for the forms `± (2/5) X₀ + X₁`.** With
the standard basis, `μ = (2/5, 1)`, `ξ = -2` and `π` the identity, the corrected vector is
`y₁ = (-2, 1)`, at which the two forms are `1/5` and `9/5`; every bound of the conclusion holds with
the constant `9/5`. By the next test the constant cannot be `1`, so for these data the best constant
lies in `(1, 9/5]`. -/
example : ∃ (ξ : Fin (Fintype.card (Fin 2)) → Fin (Fintype.card (Fin 2)) → ℚ)
      (π : AbsoluteValue ℚ ℝ → Fin (Fintype.card (Fin 2)) ≃ Fin 2),
      ∀ (w : InfinitePlace ℚ) i j,
        w (![form2 (2/5) 1, form2 (-2/5) 1] (π w.1 i)
          (basis2 j + ∑ l ∈ Finset.Iio j, ξ j l • basis2 l)) ≤
          9 / 5 * min ((![2/5, 1] : Fin (Fintype.card (Fin 2)) → ℝ) i) (![2/5, 1] j) := by
  refine ⟨fun _ _ ↦ -2, fun _ ↦ finCongr (Fintype.card_fin 2), fun w i j ↦ ?_⟩
  rw [infinitePlace_rat_apply]
  rcases fin_card_two_cases i with rfl | rfl <;> rcases fin_card_two_cases j with rfl | rfl
  · rw [basis2_zero_add]
    change |((form2 (2/5) 1 ![1, 0] : ℚ) : ℝ)| ≤ 9 / 5 * min (2 / 5 : ℝ) (2 / 5)
    norm_num [form2_apply]
  · rw [basis2_one_add]
    change |((form2 (2/5) 1 ![-2, 1] : ℚ) : ℝ)| ≤ 9 / 5 * min (2 / 5 : ℝ) 1
    norm_num [form2_apply, abs_le]
  · rw [basis2_zero_add]
    change |((form2 (-2/5) 1 ![1, 0] : ℚ) : ℝ)| ≤ 9 / 5 * min (1 : ℝ) (2 / 5)
    norm_num [form2_apply, abs_le]
  · rw [basis2_one_add]
    change |((form2 (-2/5) 1 ![-2, 1] : ℚ) : ℝ)| ≤ 9 / 5 * min (1 : ℝ) 1
    norm_num [form2_apply, abs_le]

/-- **Rejection: the constant at the infinite places is not `1`.** Over `ℚ`, the forms
`± (2/5) X₀ + X₁`, the standard basis and `μ = (2/5, 1)` satisfy the hypotheses with `ν = 1`, and
no coefficient `ξ` — rational or not — makes `y₁ = x₁ + ξ x₀` satisfy the conclusion with constant
`1`: one form would have to be at most `2/5` at `y₁` and the other at most `1`, which puts `ξ` in
`[-7/2, -3/2]` and in `[0, 5]`, or in `[3/2, 7/2]` and in `[-5, 0]`. At the places of `Sfin` the
constant is `1`; at an infinite place the triangle inequality in (7.38) costs a factor. -/
example : (∀ (w : InfinitePlace ℚ) i j, w (![form2 (2/5) 1, form2 (-2/5) 1] i (basis2 j)) ≤
      (![2/5, 1] : Fin (Fintype.card (Fin 2)) → ℝ) j) ∧
    ¬ ∃ (ξ : Fin (Fintype.card (Fin 2)) → Fin (Fintype.card (Fin 2)) → ℚ)
      (π : AbsoluteValue ℚ ℝ → Fin (Fintype.card (Fin 2)) ≃ Fin 2),
      ∀ (w : InfinitePlace ℚ) i j,
        w (![form2 (2/5) 1, form2 (-2/5) 1] (π w.1 i)
          (basis2 j + ∑ l ∈ Finset.Iio j, ξ j l • basis2 l)) ≤
          min ((![2/5, 1] : Fin (Fintype.card (Fin 2)) → ℝ) i) (![2/5, 1] j) := by
  refine ⟨fun w i j ↦ ?_, ?_⟩
  · rw [infinitePlace_rat_apply]
    rcases fin_card_two_cases j with rfl | rfl <;>
      rcases (by revert i; decide : i = 0 ∨ i = 1) with rfl | rfl <;>
      norm_num [form2_apply, basis2_zero, basis2_one]
  rintro ⟨ξ, π, h⟩
  have h0 := h Rat.infinitePlace 0 1
  have h1 := h Rat.infinitePlace 1 1
  rw [basis2_one_add, infinitePlace_rat_apply] at h0 h1
  rcases equiv_fin_two_cases (π Rat.infinitePlace.1) with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
    simp only [ha, hb, form2_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1 <;>
    push_cast at h0 h1 <;>
    generalize (ξ 1 0 : ℝ) = t at h0 h1 <;>
    norm_num [abs_le] at h0 h1 <;>
    linarith [h0.1, h0.2, h1.1, h1.2]

/-- **Rejection: the minima have to be nondecreasing.** Over `ℚ`, with the forms `X₀ ± ε X₁`, the
standard basis and `μ = (1, ε)` decreasing, every hypothesis but monotonicity holds, and no
constant survives: the first vector is not corrected, so the form paired with the second index is
`1` at it, against the bound `C min (μ 1, μ 0) = C ε`. -/
example (C : ℝ) : ∃ ε : ℚ, 0 < ε ∧
    (∀ (w : InfinitePlace ℚ) i j, w (![form2 1 ε, form2 1 (-ε)] i (basis2 j)) ≤
      (![1, (ε : ℝ)] : Fin (Fintype.card (Fin 2)) → ℝ) j) ∧
    ¬ ∃ (ξ : Fin (Fintype.card (Fin 2)) → Fin (Fintype.card (Fin 2)) → ℚ)
      (π : AbsoluteValue ℚ ℝ → Fin (Fintype.card (Fin 2)) ≃ Fin 2),
      ∀ (w : InfinitePlace ℚ) i j,
        w (![form2 1 ε, form2 1 (-ε)] (π w.1 i)
          (basis2 j + ∑ l ∈ Finset.Iio j, ξ j l • basis2 l)) ≤
          C * min ((![1, (ε : ℝ)] : Fin (Fintype.card (Fin 2)) → ℝ) i) (![1, (ε : ℝ)] j) := by
  have hn : (0 : ℝ) < ⌈C⌉₊ + 1 := by positivity
  refine ⟨1 / (⌈C⌉₊ + 1), by positivity, fun w i j ↦ ?_, ?_⟩
  · rw [infinitePlace_rat_apply]
    rcases fin_card_two_cases j with rfl | rfl <;>
      rcases (by revert i; decide : i = 0 ∨ i = 1) with rfl | rfl <;>
      simp [form2_apply, basis2_zero, basis2_one, abs_of_pos hn]
  rintro ⟨ξ, π, h⟩
  have h10 := h Rat.infinitePlace 1 0
  rw [basis2_zero_add, infinitePlace_rat_apply] at h10
  have hval : ∀ k, ![form2 1 (1 / (⌈C⌉₊ + 1)), form2 1 (-(1 / (⌈C⌉₊ + 1)))] k ![1, 0] = 1 := by
    intro k
    rcases (by revert k; decide : k = 0 ∨ k = 1) with rfl | rfl <;> simp [form2_apply]
  rw [hval] at h10
  have hε : (((1 / (⌈C⌉₊ + 1) : ℚ) : ℝ)) ≤ 1 := by
    push_cast
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg ⌈C⌉₊ : (0 : ℝ) ≤ ⌈C⌉₊)]
  change _ ≤ C * min (((1 / (⌈C⌉₊ + 1) : ℚ) : ℝ)) 1 at h10
  rw [min_eq_left hε, Rat.cast_one, abs_one] at h10
  have hC : C * (((1 / (⌈C⌉₊ + 1) : ℚ) : ℝ)) < 1 := by
    push_cast
    rw [mul_one_div, div_lt_one (by positivity)]
    linarith [Nat.le_ceil C]
  linarith

/-- The `2`-adic place of `ℚ`. -/
private theorem finitePlace_two_apply (x : ℚ) :
    Rat.finitePlace (⟨2, Nat.prime_two⟩ : Nat.Primes) x = ((padicNorm 2 x : ℚ) : ℝ) :=
  Rat.finitePlace_apply _ x

/-- **Rejection: the coefficients need denominators at the places of `Sfin`.** At the `2`-adic place
of `ℚ`, the forms `4 X₀ + X₁` and `4 X₀ + 3 X₁`, the standard basis and `μ = (1/4, 1)` satisfy the
hypotheses, and no coefficient integral at `2` meets the bound `min (μ 0, μ 1) = 1/4` at
`y₁ = x₁ + ξ x₀`: the paired form is `4 ξ + 1` or `4 ξ + 3`, of value `1`. So the lemma produces
`Sfin`-integers, not algebraic integers. -/
example : (∀ i j, Rat.finitePlace (⟨2, Nat.prime_two⟩ : Nat.Primes)
      (![form2 4 1, form2 4 3] i (basis2 j)) ≤
      (![1 / 4, 1] : Fin (Fintype.card (Fin 2)) → ℝ) j) ∧
    ¬ ∃ (ξ : Fin (Fintype.card (Fin 2)) → Fin (Fintype.card (Fin 2)) → ℚ)
      (π : AbsoluteValue ℚ ℝ → Fin (Fintype.card (Fin 2)) ≃ Fin 2),
      (∀ i j, ∀ v : FinitePlace ℚ, v (ξ i j) ≤ 1) ∧
      ∀ i j, Rat.finitePlace (⟨2, Nat.prime_two⟩ : Nat.Primes)
        (![form2 4 1, form2 4 3] (π (Rat.finitePlace (⟨2, Nat.prime_two⟩ : Nat.Primes)).1 i)
          (basis2 j + ∑ l ∈ Finset.Iio j, ξ j l • basis2 l)) ≤
          min ((![1 / 4, 1] : Fin (Fintype.card (Fin 2)) → ℝ) i) (![1 / 4, 1] j) := by
  set v := Rat.finitePlace (⟨2, Nat.prime_two⟩ : Nat.Primes) with hv
  have h2 : v 2 = 1 / 2 := by
    have := padicNorm.padicNorm_p_of_prime (p := 2)
    rw [Nat.cast_ofNat] at this
    rw [hv, finitePlace_two_apply, this]
    norm_num
  have h4 : v 4 = 1 / 4 := by
    rw [show (4 : ℚ) = 2 * 2 by norm_num, map_mul, h2]
    norm_num
  have h3 : v 3 = 1 := by
    rw [hv, finitePlace_two_apply]
    have := padicNorm.padicNorm_of_prime_of_ne (p := 2) (q := 3) (by decide)
    exact_mod_cast congrArg (fun q : ℚ ↦ (q : ℝ)) this
  refine ⟨fun i j ↦ ?_, ?_⟩
  · rcases fin_card_two_cases j with rfl | rfl <;>
      rcases (by revert i; decide : i = 0 ∨ i = 1) with rfl | rfl <;>
      simp [form2_apply, basis2_zero, basis2_one, h3, h4]
  rintro ⟨ξ, π, hint, h⟩
  have h01 := h 0 1
  rw [basis2_one_add] at h01
  change _ ≤ min (1 / 4 : ℝ) 1 at h01
  rw [min_eq_left (by norm_num)] at h01
  have hξ4 : v (4 * ξ 1 0) ≤ 1 / 4 := by
    rw [map_mul, h4]
    have := hint 1 0 v
    nlinarith [apply_nonneg v (ξ 1 0)]
  -- the value of the paired form is `4 ξ + c` with `v c = 1`
  have key : ∀ c : ℚ, v c = 1 → v (4 * ξ 1 0 + c) ≤ 1 / 4 → False := by
    intro c hc hle
    have : v c ≤ max (v (4 * ξ 1 0 + c)) (v (-(4 * ξ 1 0))) := by
      have := v.add_le (4 * ξ 1 0 + c) (-(4 * ξ 1 0))
      rwa [add_neg_cancel_comm] at this
    rw [FinitePlace.coe_apply v (-(4 * ξ 1 0)), AbsoluteValue.map_neg,
      ← FinitePlace.coe_apply] at this
    rw [hc] at this
    have := this.trans (max_le hle hξ4)
    norm_num at this
  rcases equiv_fin_two_cases (π v.1) with ⟨ha, -⟩ | ⟨ha, -⟩ <;>
    simp only [ha, form2_apply, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one] at h01
  · exact key 1 (map_one v) h01
  · exact key 3 h3 h01

end Tests
