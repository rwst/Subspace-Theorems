/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.NumberTheory.Height.NumberField

-- Used only inside proofs.
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# The fundamental inequality

Let `K` be a number field and `x ≠ 0` an element of it. Pick any set of infinite places and any
set of finite places of `K` and multiply the local factors of `x` over them, the infinite ones
weighted by `InfinitePlace.mult`. The **fundamental inequality** says that the result is trapped
between the multiplicative height of `x` and its reciprocal:

```text
(mulHeight₁ x)⁻¹ ≤ (∏ v ∈ S∞, |x|_v ^ mult v) * ∏ v ∈ S₀, |x|_v ≤ mulHeight₁ x.
```

Both bounds are sharp — at `K = ℚ`, `x = 2` the empty set of finite places and the one infinite
place give the right-hand equality, and the `2`-adic place alone gives the left-hand one.

The same bookkeeping in the form Liouville's inequality uses replaces each local factor by
`min 1 |x|_v` and takes *all* places: then the product is exactly `(mulHeight₁ x)⁻¹`, because
`min 1 t * max t 1 = t` turns the product formula into the definition of the height. Cutting the
product down to a finite set of places can only increase it, since every factor is at most `1`,
and that is the fundamental inequality in the shape Layer 0.4's second half consumes.

## Main results

* `NumberField.prod_apply_le_mulHeight₁` and `NumberField.inv_mulHeight₁_le_prod_apply`: the two
  halves of the fundamental inequality. Bombieri–Gubler (1.8).
* `NumberField.prod_min_one_apply_eq_inv_mulHeight₁`: over *all* places the truncated product is
  the reciprocal of the height, on the nose.
* `NumberField.inv_mulHeight₁_le_prod_min_one_apply`: the truncated product over a finite set of
  places is at least `(mulHeight₁ x)⁻¹`, and `NumberField.finprod_min_one_le_prod` is the finite
  half of it on its own.
* `NumberField.FinitePlace.hasFiniteMulSupport_max_one` and
  `NumberField.FinitePlace.hasFiniteMulSupport_min_one`: the two truncations of `v ↦ |x|_v` still
  have finite multiplicative support, which is what makes the `finprod`s above meaningful.

## Implementation notes

⚠ **The lower bound needs no product formula.** The obvious route — the complementary product is
the reciprocal, by the product formula, and the upper bound applies to it — runs into the
complement of a `Finset` of finite places, which is not a `Finset`. Replacing `x` by `x⁻¹` avoids
it: the product over the *same* two sets is inverted, and `Height.mulHeight₁_inv` says the bound
is unchanged. The product formula enters only in
`NumberField.prod_min_one_apply_eq_inv_mulHeight₁`, where the products do run over all places.

⚠ **`min` is written `min 1 t` and `max` is written `max t 1`.** The first is the truncation
Liouville's inequality takes, the second is the one `Height.mulHeight₁_eq` is stated with;
`min_mul_max` multiplies them in that order only after a `max_comm`, and keeping both spellings
as they are found avoids rewriting the height of a whole number field into a nonstandard form.

⚠ **Two `finprod`-versus-`Finset.prod` comparisons are needed and Mathlib has neither.** A
subproduct of factors `≥ 1` is at most the whole `finprod`, and a subproduct of factors `≤ 1` is
at least it. Both are `finprod_le_finprod₀` against the function that is `f` on the `Finset` and
`1` off it, which is the same device `DiophantineApproximation/SAdicHeight.lean` uses.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
(1.8) and Lemma 1.5.18.

This is the first half of Layer 0.4 of the `DiophantineApproximation` roadmap.
-/

public section

open Height

namespace NumberField

/-!
### Comparing a `Finset.prod` with a `finprod`
-/

section Finprod

variable {α : Type*}

private theorem hasFiniteMulSupport_mulIndicator (s : Finset α) (f : α → ℝ) :
    Function.HasFiniteMulSupport ((s : Set α).mulIndicator f) := by
  refine Set.Finite.subset s.finite_toSet fun a ha ↦ ?_
  simp only [Function.mem_mulSupport, Set.mulIndicator_apply_ne_one] at ha
  exact ha.1

private theorem finprod_mulIndicator_eq_prod (s : Finset α) (f : α → ℝ) :
    (∏ᶠ a, (s : Set α).mulIndicator f a) = ∏ a ∈ s, f a := by
  rw [← finprod_mem_def, finprod_mem_coe_finset]

/-- A subproduct of factors `≥ 1` is at most the whole `finprod`. -/
private theorem prod_le_finprod_of_one_le {f : α → ℝ} (s : Finset α) (hf : ∀ a, 1 ≤ f a)
    (hfin : Function.HasFiniteMulSupport f) : ∏ a ∈ s, f a ≤ ∏ᶠ a, f a := by
  rw [← finprod_mulIndicator_eq_prod s f]
  exact finprod_le_finprod₀ (hasFiniteMulSupport_mulIndicator s f)
    (fun a ↦ le_trans zero_le_one (Set.one_le_mulIndicator (fun b _ ↦ hf b) a)) hfin
    (Set.mulIndicator_le_self' fun b _ ↦ hf b)

/-- A subproduct of factors `≤ 1` is at least the whole `finprod`. -/
private theorem finprod_le_prod_of_le_one {f : α → ℝ} (s : Finset α) (hf0 : ∀ a, 0 ≤ f a)
    (hf : ∀ a, f a ≤ 1) (hfin : Function.HasFiniteMulSupport f) : ∏ᶠ a, f a ≤ ∏ a ∈ s, f a := by
  rw [← finprod_mulIndicator_eq_prod s f]
  exact finprod_le_finprod₀ hfin hf0 (hasFiniteMulSupport_mulIndicator s f)
    (Set.le_mulIndicator (fun _ _ ↦ le_rfl) fun b _ ↦ hf b)

end Finprod

variable {K : Type*} [Field K] [NumberField K]

/-- **Truncating from below keeps the finite multiplicative support.** -/
theorem FinitePlace.hasFiniteMulSupport_max_one {x : K} (hx : x ≠ 0) :
    Function.HasFiniteMulSupport fun v : FinitePlace K ↦ max (v x) 1 :=
  Set.Finite.subset (FinitePlace.hasFiniteMulSupport hx) fun v hv ↦ by
    simp only [Function.mem_mulSupport] at hv ⊢
    exact fun h ↦ hv (by rw [h, max_self])

/-- **Truncating from above keeps the finite multiplicative support.** -/
theorem FinitePlace.hasFiniteMulSupport_min_one {x : K} (hx : x ≠ 0) :
    Function.HasFiniteMulSupport fun v : FinitePlace K ↦ min 1 (v x) :=
  Set.Finite.subset (FinitePlace.hasFiniteMulSupport hx) fun v hv ↦ by
    simp only [Function.mem_mulSupport] at hv ⊢
    exact fun h ↦ hv (by rw [h, min_self])

/-!
### The fundamental inequality
-/

variable (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))

/-- **The fundamental inequality, upper bound** (Bombieri–Gubler (1.8)). The product of the local
factors of `x` over any set of places is at most the height of `x`. -/
theorem prod_apply_le_mulHeight₁ {x : K} (hx : x ≠ 0) :
    (∏ v ∈ Sinf, v x ^ v.mult) * ∏ v ∈ Sfin, v x ≤ mulHeight₁ x := by
  rw [mulHeight₁_eq]
  have hinf : (∏ v ∈ Sinf, v x ^ v.mult) ≤ ∏ v : InfinitePlace K, max (v x) 1 ^ v.mult :=
    calc (∏ v ∈ Sinf, v x ^ v.mult) ≤ ∏ v ∈ Sinf, max (v x) 1 ^ v.mult :=
          Finset.prod_le_prod₀ (fun v _ ↦ pow_nonneg (apply_nonneg _ _) _)
            fun v _ ↦ pow_le_pow_left₀ (apply_nonneg _ _) (le_max_left _ _) _
      _ ≤ ∏ v : InfinitePlace K, max (v x) 1 ^ v.mult :=
          Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
            (fun v _ ↦ pow_nonneg (le_trans (apply_nonneg _ _) (le_max_left _ _)) _)
            fun v _ _ ↦ one_le_pow₀ (le_max_right _ _)
  have hfin : (∏ v ∈ Sfin, v x) ≤ ∏ᶠ v : FinitePlace K, max (v x) 1 :=
    calc (∏ v ∈ Sfin, v x) ≤ ∏ v ∈ Sfin, max (v x) 1 :=
          Finset.prod_le_prod₀ (fun v _ ↦ apply_nonneg _ _) fun v _ ↦ le_max_left _ _
      _ ≤ ∏ᶠ v : FinitePlace K, max (v x) 1 :=
          prod_le_finprod_of_one_le _ (fun _ ↦ le_max_right _ _)
            (FinitePlace.hasFiniteMulSupport_max_one hx)
  exact mul_le_mul hinf hfin (Finset.prod_nonneg fun v _ ↦ apply_nonneg _ _)
    (Finset.prod_nonneg fun v _ ↦ pow_nonneg (le_trans (apply_nonneg _ _) (le_max_left _ _)) _)

/-- The product of the local factors of a nonzero `x` over any set of places is positive. -/
theorem prod_apply_pos {x : K} (hx : x ≠ 0) :
    0 < (∏ v ∈ Sinf, v x ^ v.mult) * ∏ v ∈ Sfin, v x :=
  mul_pos (Finset.prod_pos fun _ _ ↦ pow_pos (InfinitePlace.pos_iff.mpr hx) _)
    (Finset.prod_pos fun _ _ ↦ FinitePlace.pos_iff.mpr hx)

/-- **The fundamental inequality, lower bound** (Bombieri–Gubler (1.8)). The product of the local
factors of `x` over any set of places is at least the reciprocal of the height of `x`. -/
theorem inv_mulHeight₁_le_prod_apply {x : K} (hx : x ≠ 0) :
    (mulHeight₁ x)⁻¹ ≤ (∏ v ∈ Sinf, v x ^ v.mult) * ∏ v ∈ Sfin, v x := by
  have h := prod_apply_le_mulHeight₁ Sinf Sfin (inv_ne_zero hx)
  rw [mulHeight₁_inv] at h
  have heq : (∏ v ∈ Sinf, v x⁻¹ ^ v.mult) * ∏ v ∈ Sfin, v x⁻¹
      = ((∏ v ∈ Sinf, v x ^ v.mult) * ∏ v ∈ Sfin, v x)⁻¹ := by
    rw [mul_inv, ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib]
    refine congrArg₂ _ (Finset.prod_congr rfl fun v _ ↦ ?_)
      (Finset.prod_congr rfl fun v _ ↦ map_inv₀ _ _)
    rw [map_inv₀, inv_pow]
  rw [heq] at h
  exact (inv_le_comm₀ (prod_apply_pos Sinf Sfin hx) (mulHeight₁_pos x)).mp h

/-!
### The truncated product
-/

/-- **The truncated local factors of `x` multiply to the reciprocal of its height.** This is the
product formula read through `min 1 t * max t 1 = t`, and it is the form Liouville's inequality
starts from. -/
theorem prod_min_one_apply_eq_inv_mulHeight₁ {x : K} (hx : x ≠ 0) :
    ((∏ v : InfinitePlace K, min 1 (v x) ^ v.mult) * ∏ᶠ v : FinitePlace K, min 1 (v x))
      = (mulHeight₁ x)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  have hAC : ((∏ v : InfinitePlace K, min 1 (v x) ^ v.mult)
      * ∏ v : InfinitePlace K, max (v x) 1 ^ v.mult) = ∏ v : InfinitePlace K, v x ^ v.mult := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ ↦ ?_
    rw [← mul_pow, max_comm, min_mul_max, one_mul]
  have hBD : ((∏ᶠ v : FinitePlace K, min 1 (v x)) * ∏ᶠ v : FinitePlace K, max (v x) 1)
      = ∏ᶠ v : FinitePlace K, v x := by
    rw [← finprod_mul_distrib (FinitePlace.hasFiniteMulSupport_min_one hx)
      (FinitePlace.hasFiniteMulSupport_max_one hx)]
    exact finprod_congr fun v ↦ by rw [max_comm, min_mul_max, one_mul]
  calc ((∏ v : InfinitePlace K, min 1 (v x) ^ v.mult) * ∏ᶠ v : FinitePlace K, min 1 (v x))
        * mulHeight₁ x
      = ((∏ v : InfinitePlace K, min 1 (v x) ^ v.mult)
          * ∏ v : InfinitePlace K, max (v x) 1 ^ v.mult)
        * ((∏ᶠ v : FinitePlace K, min 1 (v x)) * ∏ᶠ v : FinitePlace K, max (v x) 1) := by
        rw [mulHeight₁_eq]; ring
    _ = (∏ v : InfinitePlace K, v x ^ v.mult) * ∏ᶠ v : FinitePlace K, v x := by rw [hAC, hBD]
    _ = 1 := prod_abs_eq_one hx

/-- **The truncated finite part of the height is at most any of its finite subproducts.** Every
factor being at most `1`, dropping the places outside `Sfin` can only increase the product. -/
theorem finprod_min_one_le_prod {x : K} (hx : x ≠ 0) :
    (∏ᶠ v : FinitePlace K, min 1 (v x)) ≤ ∏ v ∈ Sfin, min 1 (v x) :=
  finprod_le_prod_of_le_one _ (fun _ ↦ le_min zero_le_one (apply_nonneg _ _))
    (fun _ ↦ min_le_left _ _) (FinitePlace.hasFiniteMulSupport_min_one hx)

/-- **The fundamental inequality in truncated form.** Cutting the product of
`NumberField.prod_min_one_apply_eq_inv_mulHeight₁` down to a finite set of places can only
increase it, every factor being at most `1`. -/
theorem inv_mulHeight₁_le_prod_min_one_apply {x : K} (hx : x ≠ 0) :
    (mulHeight₁ x)⁻¹
      ≤ (∏ v ∈ Sinf, min 1 (v x) ^ v.mult) * ∏ v ∈ Sfin, min 1 (v x) := by
  rw [← prod_min_one_apply_eq_inv_mulHeight₁ hx]
  have hle0 : ∀ v : InfinitePlace K, 0 ≤ min 1 (v x) :=
    fun _ ↦ le_min zero_le_one (apply_nonneg _ _)
  have hinf : (∏ v : InfinitePlace K, min 1 (v x) ^ v.mult)
      ≤ ∏ v ∈ Sinf, min 1 (v x) ^ v.mult :=
    Finset.prod_le_prod_of_subset_of_le_one₀ (Finset.subset_univ _)
      (fun v _ ↦ pow_nonneg (hle0 v) _) fun v _ _ ↦ pow_le_one₀ (hle0 v) (min_le_left _ _)
  have hfin : (∏ᶠ v : FinitePlace K, min 1 (v x)) ≤ ∏ v ∈ Sfin, min 1 (v x) :=
    finprod_min_one_le_prod Sfin hx
  exact mul_le_mul hinf hfin (finprod_nonneg fun _ ↦ le_min zero_le_one (apply_nonneg _ _))
    (Finset.prod_nonneg fun v _ ↦ pow_nonneg (hle0 v) _)

/-! ### Acceptance criteria -/

/-- **Conformance: at the empty set of places the fundamental inequality is
`Height.one_le_mulHeight₁`.** Both products are empty, so the statement reads `1 ≤ mulHeight₁ x`,
and the bound is therefore not vacuous at the bottom end. -/
example {x : K} (hx : x ≠ 0) : (1 : ℝ) ≤ mulHeight₁ x := by
  simpa using prod_apply_le_mulHeight₁ (K := K) ∅ ∅ hx

/-- **Conformance: the truncated identity is the product formula.** Multiplied out against the
height it says exactly that all the local factors of `x` multiply to `1`. -/
example {x : K} (hx : x ≠ 0) :
    ((∏ v : InfinitePlace K, min 1 (v x) ^ v.mult) * ∏ᶠ v : FinitePlace K, min 1 (v x))
      * mulHeight₁ x = 1 := by
  rw [prod_min_one_apply_eq_inv_mulHeight₁ hx, inv_mul_cancel₀ (mulHeight₁_ne_zero x)]

/-- **Rejection test: `x ≠ 0` is needed for the lower bound.** At `x = 0` the height is `1`, so
the left-hand side is `1`, while every local factor vanishes and the product is `0`. The upper
bound survives at `x = 0`; the lower one does not. -/
example : ¬ ((mulHeight₁ (0 : K))⁻¹ ≤ (∏ v : InfinitePlace K, v (0 : K) ^ v.mult)
    * ∏ v ∈ (∅ : Finset (FinitePlace K)), v (0 : K)) := by
  obtain ⟨v₀⟩ := (inferInstance : Nonempty (InfinitePlace K))
  rw [Finset.prod_eq_zero (Finset.mem_univ v₀) (by simp [zero_pow v₀.mult_ne_zero])]
  simp

end NumberField
