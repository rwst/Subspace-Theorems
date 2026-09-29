/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Evertse1984.PlaceProd
public import Mathlib.Algebra.Polynomial.Homogenize
public import Mathlib.NumberTheory.Height.NumberField

-- Used only inside proofs.
import Mathlib.NumberTheory.Height.MvPolynomial

/-!
# Evertse's Lemma 1: the size of `f(r)` at a set of places

**Lemma 1** (Evertse 1984, p. 235). Let `K` have degree `D` and let `f ∈ K[X]` have degree `m`.
There is `C > 0` such that for every set `T` of places and every `r ∈ ℤ` with `r ≠ 0` and
`f(r) ≠ 0`,

```text
C⁻¹ |r| ^ (-D m) ≤ (∏_v max(1, ‖f(r)‖_v))⁻¹ ≤ ∏_{v ∈ T} ‖f(r)‖_v
                 ≤ ∏_v max(1, ‖f(r)‖_v) ≤ C |r| ^ (D m).
```

The product `∏_v max(1, ‖α‖_v)` over all places is Mathlib's `mulHeight₁ α`. The two inner
inequalities hold for every `α ≠ 0` (`NumberField.placeProd_le_mulHeight₁` and, applied to
`α⁻¹`, `NumberField.inv_mulHeight₁_le_placeProd`). The outer ones are
`H(f(x)) ≤ C · H(x) ^ m` (`Polynomial.exists_pos_forall_mulHeight₁_eval_le`, Mathlib's bound for
homogeneous polynomial maps applied to the homogenization of `f`) together with `H(r) = |r| ^ D`
for a nonzero integer `r` (`NumberField.mulHeight₁_intCast`). Here `max(|r|, 1)` replaces `|r|`,
so that `r = 0` needs no exception.

## Main results

* `Polynomial.exists_pos_forall_mulHeight₁_eval_le`: `H(f(x)) ≤ C · H(x) ^ deg f`.
* `NumberField.mulHeight₁_intCast`: `H(r) = max(|r|, 1) ^ [K : ℚ]`.
* `NumberField.placeProd_le_mulHeight₁`, `NumberField.inv_mulHeight₁_le_placeProd`.
* `NumberField.exists_pos_forall_placeProd_eval_intCast`: **Lemma 1**.

## References

J.-H. Evertse, *On sums of `S`-units and linear recurrences*, Compositio Math. **53** (1984),
225–244, Lemma 1.
-/

@[expose] public section

open IsDedekindDomain Height Module Polynomial

namespace Polynomial

variable {K : Type*} [Field K] [AdmissibleAbsValues K]

/-- **The height of a value of a polynomial**: `H(f(x)) ≤ C · H(x) ^ deg f`. -/
theorem exists_pos_forall_mulHeight₁_eval_le (f : K[X]) :
    ∃ C > 0, ∀ x : K, mulHeight₁ (f.eval x) ≤ C * mulHeight₁ x ^ f.natDegree := by
  obtain ⟨C, hC, h⟩ := mulHeight_eval_le' (isHomogeneous_toTupleMvPolynomial f)
  refine ⟨C, hC, fun x ↦ ?_⟩
  have hx := h ![x, 1]
  have hval : (fun j ↦ MvPolynomial.eval ![x, 1] (f.toTupleMvPolynomial j)) = ![f.eval x, 1] := by
    funext j
    fin_cases j
    · simp [toTupleMvPolynomial, eval_homogenize le_rfl]
    · simp [toTupleMvPolynomial]
  rwa [hval, ← mulHeight₁_eq_mulHeight, ← mulHeight₁_eq_mulHeight] at hx

end Polynomial

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **The height of an integer** in a number field of degree `D` is `max(|r|, 1) ^ D`. -/
theorem mulHeight₁_intCast (r : ℤ) : mulHeight₁ (r : K) = max |(r : ℝ)| 1 ^ finrank ℚ K := by
  rw [NumberField.mulHeight₁_eq]
  have hfin : ∏ᶠ v : FinitePlace K, max (v (r : K)) 1 = 1 := by
    refine finprod_eq_one_of_forall_eq_one fun v ↦ max_eq_right ?_
    have hv : IsNonarchimedean (v ·) := FinitePlace.add_le v
    exact hv.apply_intCast_le_one (map_zero_le v 1) (map_one v) (map_neg_eq_map v)
  have hinf : ∀ v : InfinitePlace K, v (r : K) = |(r : ℝ)| := fun v ↦ by
    rw [← v.norm_embedding_eq, map_intCast, Complex.norm_intCast]
  simp only [hfin, mul_one, hinf]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]

variable (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Set (AbsoluteValue K ℝ))

/-- **The product over the places of `T` is at most the height**: every factor is at most
`max(‖α‖_v, 1)`, and the factors of the height are at least `1`. -/
theorem placeProd_le_mulHeight₁ (α : K) : placeProd S T (fun v ↦ v α) ≤ mulHeight₁ α := by
  classical
  set x : Fin 2 → K := ![α, 1] with hx
  have hx0 : x ≠ 0 := fun h ↦ one_ne_zero (congrFun h 1)
  set M : AbsoluteValue K ℝ → ℝ := fun v ↦ ⨆ i, v (x i) with hM
  have hM1 : ∀ v : AbsoluteValue K ℝ, 1 ≤ M v := fun v ↦
    (le_of_eq (by simp [hx])).trans (le_ciSup (f := fun i ↦ v (x i)) (Finite.bddAbove_range _) 1)
  have hind : ∀ v, T.mulIndicator (fun v ↦ v α) v ≤ M v := fun v ↦ by
    by_cases hv : v ∈ T
    · rw [Set.mulIndicator_of_mem hv]
      exact le_ciSup (f := fun i ↦ v (x i)) (Finite.bddAbove_range _) 0
    · rw [Set.mulIndicator_of_notMem hv]; exact hM1 v
  have hind0 : ∀ v, 0 ≤ T.mulIndicator (fun v ↦ v α) v := fun v ↦ by
    by_cases hv : v ∈ T
    · rw [Set.mulIndicator_of_mem hv]; exact apply_nonneg _ _
    · rw [Set.mulIndicator_of_notMem hv]; exact zero_le_one
  rw [mulHeight₁_eq_mulHeight, NumberField.mulHeight_eq hx0, finprod_iSup_eq]
  unfold placeProd
  have hfin := hasFiniteMulSupport_iSup_mk hx0
  have hS : ∏ P ∈ S, M (FinitePlace.mk P).1 ≤
      ∏ᶠ P : HeightOneSpectrum (𝓞 K), ⨆ i, FinitePlace.mk P (x i) := by
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := S ∪ hfin.toFinset) (by
      intro P hP
      rw [Finset.coe_union]
      exact Or.inr (Finset.mem_coe.mpr ((Set.Finite.mem_toFinset hfin).mpr hP)))]
    exact Finset.prod_le_prod_of_subset_of_one_le₀ Finset.subset_union_left
      (fun P _ ↦ zero_le_one.trans (hM1 _)) fun P _ _ ↦ hM1 _
  refine mul_le_mul (Finset.prod_le_prod₀ (fun w _ ↦ pow_nonneg (hind0 _) _) fun w _ ↦
    pow_le_pow_left₀ (hind0 _) (hind _) _) ((Finset.prod_le_prod₀ (fun P _ ↦ hind0 _)
      fun P _ ↦ hind _).trans hS) (Finset.prod_nonneg fun P _ ↦ hind0 _)
    (Finset.prod_nonneg fun w _ ↦ pow_nonneg (zero_le_one.trans (hM1 _)) _)

/-- **The product over the places of `T` is at least the inverse of the height**, for `α ≠ 0`:
the upper bound applied to `α⁻¹`. -/
theorem inv_mulHeight₁_le_placeProd {α : K} (hα : α ≠ 0) :
    (mulHeight₁ α)⁻¹ ≤ placeProd S T (fun v ↦ v α) := by
  have hprod : placeProd S T (fun v ↦ v α) * placeProd S T (fun v ↦ v α⁻¹) = 1 := by
    rw [← placeProd_mul]
    have : (fun v : AbsoluteValue K ℝ ↦ v α * v α⁻¹) = fun _ ↦ 1 := by
      funext v; rw [← map_mul, mul_inv_cancel₀ hα, map_one]
    rw [this]
    simp [placeProd]
  have hpos : 0 < placeProd S T (fun v ↦ v α) :=
    placeProd_pos S T fun v _ ↦ v.pos hα
  have hle := placeProd_le_mulHeight₁ S T α⁻¹
  rw [mulHeight₁_inv] at hle
  rw [inv_le_iff_one_le_mul₀ (mulHeight₁_pos α), ← hprod]
  exact mul_le_mul_of_nonneg_left hle hpos.le

/-- **Evertse's Lemma 1.** For `f ∈ K[X]` there is `C > 0` such that for every set `T` of places
and every integer `r` with `f(r) ≠ 0`, the product of `‖f(r)‖_v` over the places of `T` in
`S∞ ∪ S` lies between `(C · max(|r|, 1) ^ (D m))⁻¹` and `C · max(|r|, 1) ^ (D m)`, where
`D = [K : ℚ]` and `m = deg f`. -/
theorem exists_pos_forall_placeProd_eval_intCast (f : K[X]) :
    ∃ C > 0, ∀ (T : Set (AbsoluteValue K ℝ)) (r : ℤ), f.eval (r : K) ≠ 0 →
      (C * max |(r : ℝ)| 1 ^ (finrank ℚ K * f.natDegree))⁻¹ ≤
          placeProd S T (fun v ↦ v (f.eval (r : K))) ∧
        placeProd S T (fun v ↦ v (f.eval (r : K))) ≤
          C * max |(r : ℝ)| 1 ^ (finrank ℚ K * f.natDegree) := by
  obtain ⟨C, hC, h⟩ := f.exists_pos_forall_mulHeight₁_eval_le (K := K)
  have hH : ∀ r : ℤ, mulHeight₁ (f.eval (r : K)) ≤
      C * max |(r : ℝ)| 1 ^ (finrank ℚ K * f.natDegree) := fun r ↦ by
    rw [pow_mul, ← mulHeight₁_intCast]; exact h _
  refine ⟨C, hC, fun T r hr ↦ ⟨?_, (placeProd_le_mulHeight₁ S T _).trans (hH r)⟩⟩
  exact (inv_anti₀ (mulHeight₁_pos _) (hH r)).trans (inv_mulHeight₁_le_placeProd S T hr)

end NumberField
