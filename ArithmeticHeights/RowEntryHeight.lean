/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.Hadamard
public import ArithmeticHeights.Matrix
public import ArithmeticHeights.Nonarchimedean
public import ArithmeticHeights.RowSpace

-- Used only inside proofs: the finiteness of the support of the finite-place factor of a height.
import all Mathlib.NumberTheory.Height.Basic

/-!
# The height of a row space against the heights of the rows

The Arakelov height of the row space of a matrix is at most the product of the Arakelov heights of
its rows:

`H_Ar^row(A) ≤ ∏ᵢ H_Ar(Aᵢ)`,

and each row is in turn bounded by the height of the *entries*, `H_Ar(Aᵢ) ≤ √N · H(A)` with
`N` the number of columns. Together these turn the row-space bound of Layer 5.4 — which is what
Bombieri–Vaaler prove — into the bound in terms of the entries of `A` that applications quote.

The inequality is one bound per place, assembled by the product formula. At an **infinite** place
the local factor of the minor tuple is a Gram determinant, by Layer 3.4's Cauchy–Binet identity,
and the bound is Hadamard's inequality; at a **finite** place the local factor is the sup norm of
the minors, and the bound is the Leibniz formula together with the ultrametric inequality. Neither
half needs the two-block Fischer inequality: the fully split form is all that is used.

## Main results

* `exteriorPower.iSup_plucker_le_prod`: the nonarchimedean half, `maxₛ v(pₛ) ≤ ∏ᵢ maxⱼ v(Xᵢⱼ)`.
* `Matrix.sum_sq_plucker_row_le_prod`: the archimedean half at an infinite place of a number
  field, `∑ₛ v(pₛ)² ≤ ∏ᵢ ∑ⱼ v(Aᵢⱼ)²` — Hadamard's inequality, read through the embedding.
* `Matrix.arakelovMulHeight_plucker_row_le_prod`: the assembled global inequality for the tuple of
  maximal minors, and `Matrix.arakelovMulHeight_span_range_row_le_prod` for the row space itself.
* `Matrix.arakelovMulHeight_row_le` and `Matrix.arakelovMulHeight_span_range_row_le_pow`: the
  passage to the height of the entries, where the `√N` of Layer 5.5 is produced. The exponent
  there is the rank of `A`, not its number of rows, and the statement carries no hypothesis.

## Implementation notes

⚠ **The archimedean half is Hadamard's inequality at a complex place, not at a real one.** The
local factor at an infinite place `v` is `∑ₛ v(pₛ)²` with `v x = ‖σ x‖` for the embedding `σ`
attached to `v`, so the Gram matrix that Cauchy–Binet produces is `σA (σA)ᴴ` — the conjugate
transpose — whatever the kind of `v`. Layer 3.4's `Matrix.det_mul_transpose_self_le_prod` is an
inequality in an *ordered* field and does not apply. What is used here is
`Matrix.sum_sq_norm_plucker_row_le_prod`, the Hermitian form, which Layer 3.4 deduces from the
real one by realification; a real place needs no separate treatment, since there the embedding
lands in `ℝ` and the two Gram matrices agree.

⚠ **The two halves are bounded by products over the rows, and the product formula then has to
cross a `Finset.prod` with a `finprod`.** At the infinite places that is `Finset.prod_comm`; at
the finite places it is `finprod_prod_comm`, which needs each row's factor to have finite
multiplicative support — and, on the other side, `finprod_le_finprod₀` needs the *product over the
rows* to have finite multiplicative support as well, which is `Function.hasFiniteMulSupport_prod`.

⚠ **Every row of a matrix with a nonzero Plücker point is nonzero**, and that is what lets the
displayed formula for the Arakelov height be used on both sides. The junk value `1` at the zero
tuple is not an obstruction in the other direction either: if the minors all vanish the left-hand
side is `1` and the right-hand side is a product of numbers `≥ 1`.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
2.9.8 and the proof of Corollary 2.9.9, where `H_Ar^row(A) ≤ ∏ₘ H_Ar(A_m)` and
`H_Ar(A_m) ≤ √N H(A)` are the two steps from the row-space bound to the entry bound.
W. M. Schmidt, "On heights of algebraic subspaces and diophantine approximations",
*Annals of Mathematics* **85** (1967), 430–472, §2 Lemma 2. E. Bombieri and J. Vaaler,
"On Siegel's lemma", *Inventiones Mathematicae* **73** (1983), 11–32, Theorem 9.

This is Layer 5.5 (infrastructure) of the `ArithmeticHeights` roadmap.
-/

public section

open Finset Matrix Module NumberField Real

namespace Function

/-- A finite product of functions with finite multiplicative support has finite multiplicative
support. -/
theorem hasFiniteMulSupport_prod {α β M : Type*} [CommMonoid M] (s : Finset β) (f : β → α → M)
    (h : ∀ b ∈ s, (f b).HasFiniteMulSupport) :
    (fun a ↦ ∏ b ∈ s, f b a).HasFiniteMulSupport := by
  classical
  induction s using Finset.induction with
  | empty => simp [Function.HasFiniteMulSupport]
  | insert b s hb ih =>
      have h1 := (h b (Finset.mem_insert_self b s)).mul
        (ih fun c hc ↦ h c (Finset.mem_insert_of_mem hc))
      simp only [Finset.prod_insert hb]
      exact h1

end Function

namespace exteriorPower

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [LinearOrder ι] {k : ℕ}

/-- **The nonarchimedean half.** At a nonarchimedean absolute value the largest maximal minor of a
family of `k` vectors is at most the product of the largest entries of the vectors: the Leibniz
formula writes each minor as a sum of products of one entry from each vector, a sum is no larger
than its largest term, and the permutation is a bijection of the rows. -/
theorem iSup_plucker_le_prod {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v)
    (X : Fin k → (ι → K)) :
    (⨆ s : Set.powersetCard ι k, v (plucker k X s)) ≤ ∏ i, ⨆ j, v (X i j) := by
  have hnn : ∀ i, (0 : ℝ) ≤ ⨆ j, v (X i j) := fun i ↦ Real.iSup_nonneg fun j ↦ v.nonneg _
  refine Real.iSup_le (fun s ↦ ?_) (Finset.prod_nonneg fun i _ ↦ hnn i)
  rw [plucker_apply, Matrix.det_apply']
  refine (hv.apply_sum_le_sup Finset.univ_nonempty).trans (Finset.sup'_le _ _ fun σ _ ↦ ?_)
  rw [map_mul]
  have h1 : v ((Equiv.Perm.sign σ : ℤ) : K) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp
  rw [h1, one_mul, map_prod]
  calc ∏ i, v (Matrix.of (fun i j ↦ X i (Set.powersetCard.ofFinEmbEquiv.symm s j)) (σ i) i)
      ≤ ∏ i, ⨆ j, v (X (σ i) j) :=
        Finset.prod_le_prod₀ (fun i _ ↦ v.nonneg _) fun i _ ↦ Finite.le_ciSup_of_le _ le_rfl
    _ = ∏ i, ⨆ j, v (X i j) := Equiv.prod_comp σ fun i ↦ ⨆ j, v (X i j)

end exteriorPower

namespace Matrix

open exteriorPower

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [LinearOrder ι] {m : ℕ}

omit [NumberField K] in
/-- **The archimedean half.** At an infinite place the local factor of the tuple of maximal minors
is the Gram determinant of the rows read through the embedding, and the bound is Hadamard's
inequality in its Hermitian form — which covers a real place as well, the embedding there landing
in `ℝ`. -/
theorem sum_sq_plucker_row_le_prod (v : InfinitePlace K) (A : Matrix (Fin m) ι K) :
    ∑ s : Set.powersetCard ι m, v (plucker m A.row s) ^ 2 ≤ ∏ i, ∑ j, v (A i j) ^ 2 := by
  have h := Matrix.sum_sq_norm_plucker_row_le_prod (A.map v.embedding)
  simpa only [Matrix.plucker_row_map, Matrix.map_apply, InfinitePlace.norm_embedding_eq] using h

omit [NumberField K] in
/-- A matrix with a nonzero Plücker point has no zero row. -/
theorem row_ne_zero_of_plucker_row_ne_zero {A : Matrix (Fin m) ι K}
    (h0 : plucker m A.row ≠ 0) (i : Fin m) : A i ≠ 0 := by
  intro hi
  apply h0
  funext s
  rw [Pi.zero_apply, Matrix.plucker_row_eq_det_submatrix]
  refine Matrix.det_eq_zero_of_row_eq_zero i fun j ↦ ?_
  rw [Matrix.submatrix_apply]
  exact congrFun hi _

/-- **The Arakelov height of the tuple of maximal minors is at most the product of the Arakelov
heights of the rows.** This is Bombieri–Gubler 2.9.8: the two local bounds above, assembled over
all places. No hypothesis is needed — if the minors all vanish the left-hand side is the junk
value `1`, and every factor on the right is at least `1`. -/
theorem arakelovMulHeight_plucker_row_le_prod (A : Matrix (Fin m) ι K) :
    NumberField.arakelovMulHeight (plucker m A.row)
      ≤ ∏ i, NumberField.arakelovMulHeight (A i) := by
  classical
  rcases eq_or_ne (plucker m A.row) 0 with h0 | h0
  · rw [h0, NumberField.arakelovMulHeight_zero]
    exact Finset.one_le_prod₀ fun _ _ ↦ NumberField.one_le_arakelovMulHeight _
  have hrow : ∀ i, A i ≠ 0 := row_ne_zero_of_plucker_row_ne_zero h0
  have hfinp : (fun v : FinitePlace K ↦
      ⨆ s : Set.powersetCard ι m, v (plucker m A.row s)).HasFiniteMulSupport :=
    Height.hasFiniteMulSupport_iSup_nonarchAbsVal h0
  have hfini : ∀ i, (fun v : FinitePlace K ↦ ⨆ j, v (A i j)).HasFiniteMulSupport :=
    fun i ↦ Height.hasFiniteMulSupport_iSup_nonarchAbsVal (hrow i)
  have hexp : (∏ i, NumberField.arakelovMulHeight (A i))
      = (∏ i, ∏ v : InfinitePlace K, (∑ j, v (A i j) ^ 2) ^ (v.mult / 2 : ℝ))
        * ∏ i, ∏ᶠ v : FinitePlace K, ⨆ j, v (A i j) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ ↦ NumberField.arakelovMulHeight_eq (hrow i)
  rw [NumberField.arakelovMulHeight_eq h0, hexp]
  refine mul_le_mul ?_ ?_ ?_ ?_
  · rw [Finset.prod_comm]
    refine Finset.prod_le_prod₀ (fun v _ ↦ by positivity) fun v _ ↦ ?_
    rw [Real.finsetProd_rpow _ _ (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ by positivity) _]
    exact Real.rpow_le_rpow (Finset.sum_nonneg fun s _ ↦ by positivity)
      (sum_sq_plucker_row_le_prod v A) (by positivity)
  · rw [← finprod_prod_comm Finset.univ (fun (v : FinitePlace K) i ↦ ⨆ j, v (A i j))
      fun i _ ↦ hfini i]
    refine finprod_le_finprod₀ hfinp (fun v ↦ Real.iSup_nonneg fun _ ↦ apply_nonneg _ _)
      (Function.hasFiniteMulSupport_prod _ _ fun i _ ↦ hfini i) fun v ↦ ?_
    exact iSup_plucker_le_prod (NumberField.FinitePlace.add_le v) A.row
  · exact _root_.finprod_nonneg fun v ↦ Real.iSup_nonneg fun _ ↦ apply_nonneg _ _
  · positivity

/-- **The Arakelov height of the row space is at most the product of the Arakelov heights of the
rows.** The rows must be independent for the row space to have the minors of `A` as its Plücker
coordinates; that is the only role of the hypothesis. -/
theorem arakelovMulHeight_span_range_row_le_prod {A : Matrix (Fin m) ι K}
    (hA : LinearIndependent K A.row) :
    (Submodule.span K (Set.range A.row)).arakelovMulHeight
      ≤ ∏ i, NumberField.arakelovMulHeight (A i) := by
  rw [Matrix.arakelovMulHeight_span_range_row hA]
  refine le_trans (le_of_eq ?_) (arakelovMulHeight_plucker_row_le_prod A)
  exact congrArg _ (funext fun s ↦ (Matrix.plucker_row_eq_det_submatrix A s).symm)

/-- **2.9.8 with no hypothesis at all.** A dependent family of rows spans the row space of one of
its independent subfamilies, by `Matrix.exists_submatrix_row_linearIndependent`, and the rows it
drops contribute factors at least `1`; so the inequality holds for every matrix. -/
theorem arakelovMulHeight_span_range_row_le_prod' (A : Matrix (Fin m) ι K) :
    (Submodule.span K (Set.range A.row)).arakelovMulHeight
      ≤ ∏ i, NumberField.arakelovMulHeight (A i) := by
  classical
  obtain ⟨R, f, hR, hind, hspan⟩ := Matrix.exists_submatrix_row_linearIndependent A
  have hinj : Function.Injective f := fun a b hab ↦
    hind.injective (funext fun j ↦ by simp [Matrix.submatrix_apply, hab])
  rw [← hspan]
  refine (arakelovMulHeight_span_range_row_le_prod hind).trans ?_
  calc ∏ i : Fin R, NumberField.arakelovMulHeight ((A.submatrix f id) i)
      = ∏ i : Fin R, NumberField.arakelovMulHeight (A (f i)) := rfl
    _ = ∏ i ∈ Finset.univ.image f, NumberField.arakelovMulHeight (A i) :=
        (Finset.prod_image (f := fun i ↦ NumberField.arakelovMulHeight (A i))
          hinj.injOn).symm
    _ ≤ ∏ i, NumberField.arakelovMulHeight (A i) := by
        rw [← Finset.prod_sdiff (Finset.subset_univ (Finset.univ.image f))]
        exact le_mul_of_one_le_left
          (Finset.prod_nonneg fun i _ ↦ (NumberField.arakelovMulHeight_pos _).le)
          (Finset.one_le_prod₀ fun i _ ↦ NumberField.one_le_arakelovMulHeight _)

omit [Fintype ι] [LinearOrder ι] in
/-- A row of a matrix has height at most the height of the matrix, which is the height of the
tuple of *all* its entries. -/
theorem mulHeight_row_le [Finite ι] (A : Matrix (Fin m) ι K) (i : Fin m) :
    Height.mulHeight (A i) ≤ Matrix.mulHeight A := by
  rw [Matrix.mulHeight]
  exact Height.mulHeight_comp_le (fun j ↦ (i, j)) fun q : Fin m × ι ↦ A q.1 q.2

omit [LinearOrder ι] in
/-- **A row in the Arakelov normalization against the height of the entries.** The constant is
`N ^ (d / 2)` with `N` the number of columns and `d = [K : ℚ]`, which is `√N` in the absolute
normalization — the `√N` that Layer 5.5 puts in place of the `N` of the classical Siegel lemma. -/
theorem arakelovMulHeight_row_le [Nonempty ι] (A : Matrix (Fin m) ι K) (i : Fin m) :
    NumberField.arakelovMulHeight (A i)
      ≤ (Fintype.card ι : ℝ) ^ ((Height.totalWeight K : ℝ) / 2) * Matrix.mulHeight A :=
  (NumberField.arakelovMulHeight_le_mulHeight (A i)).trans
    (mul_le_mul_of_nonneg_left (mulHeight_row_le A i) (by positivity))

/-- **The row-space height against the height of the entries**, the form Layer 5.5 consumes: with
`R = rank A`, `N` columns and `d = [K : ℚ]`, `H_Ar^row(A) ≤ (N ^ (d / 2) · H(A)) ^ R`.

The exponent is the **rank** and not the number of rows: the bound is paid on a maximal
independent family of rows, `Matrix.exists_submatrix_row_linearIndependent`, which spans the same
row space. No hypothesis on `A` is needed. -/
theorem arakelovMulHeight_span_range_row_le_pow [Nonempty ι] (A : Matrix (Fin m) ι K) :
    (Submodule.span K (Set.range A.row)).arakelovMulHeight
      ≤ ((Fintype.card ι : ℝ) ^ ((Height.totalWeight K : ℝ) / 2) * Matrix.mulHeight A) ^ A.rank
    := by
  obtain ⟨R, f, hR, hind, hspan⟩ := Matrix.exists_submatrix_row_linearIndependent A
  rw [← hspan, hR]
  refine (arakelovMulHeight_span_range_row_le_prod hind).trans ?_
  calc ∏ i : Fin R, NumberField.arakelovMulHeight ((A.submatrix f id) i)
      ≤ ∏ _i : Fin R, (Fintype.card ι : ℝ) ^ ((Height.totalWeight K : ℝ) / 2)
          * Matrix.mulHeight A :=
        Finset.prod_le_prod₀ (fun i _ ↦ (NumberField.arakelovMulHeight_pos _).le)
          fun i _ ↦ arakelovMulHeight_row_le A (f i)
    _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Matrix

namespace Submodule

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- **2.9.8 for an arbitrary finite family.** The height of the span is at most the product of the
Arakelov heights of the generators, whatever the index type and whatever their dependences. This
is the form Layer 5.6 consumes, its generators being indexed by a product rather than by
`Fin m`. -/
theorem arakelovMulHeight_span_range_le_prod {μ : Type*} [Fintype μ] (v : μ → (ι → K)) :
    (Submodule.span K (Set.range v)).arakelovMulHeight
      ≤ ∏ i, NumberField.arakelovMulHeight (v i) := by
  let e : Fin (Fintype.card μ) ≃ μ := (Fintype.equivFin μ).symm
  have hrange :
      Set.range (Matrix.of fun l ↦ v (e l) : Matrix (Fin (Fintype.card μ)) ι K).row
        = Set.range v := by
    rw [show (Matrix.of fun l ↦ v (e l) : Matrix (Fin (Fintype.card μ)) ι K).row = v ∘ e from rfl,
      Set.range_comp, e.range_eq_univ, Set.image_univ]
  rw [← hrange]
  exact (Matrix.arakelovMulHeight_span_range_row_le_prod' _).trans
    (le_of_eq (Equiv.prod_comp e fun i ↦ NumberField.arakelovMulHeight (v i)))

end Submodule

end
