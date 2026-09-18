/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.Plucker
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Data.Fintype.Order
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

-- Used only inside proofs.
import Mathlib.Basic.Real.Pointwise
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The height of a subspace at a nonarchimedean place

At a finite place `v` the local factor of the height of a `k`-dimensional subspace of `Kⁿ` is the
**Gauss norm** `‖p‖ᵥ = maxₛ |pₛ|ᵥ` of its tuple of Plücker coordinates — the same quantity in both
normalizations of Layer 0, since the sup norm and the ℓ² norm differ only at the infinite places.
This file proves that local factor **submodular**:

`‖p(A;B;C)‖ᵥ · ‖p(A)‖ᵥ ≤ ‖p(A;B)‖ᵥ · ‖p(A;C)‖ᵥ`,

for three families of vectors stacked in the four ways the milestone of Layer 3.6 needs. With the
archimedean half — Koteljanskii's inequality, in `ArithmeticHeights/Submodular.lean` — it gives
Bombieri–Gubler's Theorem 2.8.13, which that file then assembles.

## Main results

* `exteriorPower.iSup_plucker_append_append_mul_le`: the submodular inequality at any
  nonarchimedean absolute value, and `NumberField.FinitePlace.iSup_plucker_append_mul_le` the same
  at a finite place of a number field.
* `exteriorPower.iSup_plucker_append_le`: **submultiplicativity**, `‖p(B;C)‖ᵥ ≤ ‖p(B)‖ᵥ ‖p(C)‖ᵥ`,
  the nonarchimedean counterpart of the generalized Hadamard inequality of Layer 3.4. It is what
  the submodular inequality reduces to.
* `exteriorPower.exists_integral_basis`: **local normalization.** A family with a nonzero Plücker
  point has a change of basis making it integral at `v`, with the minor on a largest Plücker
  coordinate equal to the identity matrix. These are the rows of an `Oᵥ`-basis of the saturated
  lattice `span X ∩ Oᵥⁿ`, and the statement holds at any absolute value, nonarchimedean or not.
* `exteriorPower.apply_det_le_iSup_plucker`: every `k × k` minor on an arbitrary list of columns,
  repetitions and reorderings allowed, is bounded by the largest Plücker coordinate.
* `exteriorPower.plucker_mul` and `exteriorPower.plucker_append_mul`: how the Plücker coordinates
  move under a change of basis, in the general block-triangular form that covers both scaling a
  block and adding one block into another.

## Implementation notes

The archimedean proof of submodularity does not transfer: it projects the later blocks orthogonally
to the first, and there is no orthogonal projection at a finite place. What replaces it is local
normalization, and the shape of the argument is entirely different — the inequality is *deduced
from submultiplicativity*, twice, rather than proved by a determinant identity.

Normalize `A`: let `s₀` be a set of columns where `‖p(A)‖ᵥ` is attained and replace `A` by
`(A_{s₀})⁻¹ A`. Cramer's rule writes each entry of the result as a ratio of a `p × p` minor of `A`
to the maximal one, so the normalized family is integral and its minor on `s₀` is the identity;
its Plücker norm is therefore exactly `1`. This is the `Oᵥ`-basis of the saturated lattice
`span A ∩ Oᵥⁿ` — obtained without any structure theory of modules over the valuation ring, which
Mathlib could not supply in the form needed. Then reduce `B` and `C` modulo `A`, a row operation
that changes no Plücker coordinate of the stacks, so that their `s₀`-columns vanish. Now

`‖p(A;B;C)‖ ≤ ‖p(A)‖ ‖p(B;C)‖ = ‖p(B;C)‖ ≤ ‖p(B)‖ ‖p(C)‖ ≤ ‖p(A;B)‖ ‖p(A;C)‖`,

the first two steps by submultiplicativity and the last because, with `A`'s minor on `s₀` the
identity and `B`'s columns there zero, the minor of `(A;B)` on `s₀ ∪ t` is block triangular and
equals the minor of `B` on `t`.

Submultiplicativity itself is where the nonarchimedean hypothesis enters, and it enters once:
after both families are normalized to integral bases the stack is integral, so every one of its
minors lies in the valuation ring. That is the Leibniz formula and the ultrametric inequality for a
finite sum — **no expansion along a block of rows is needed**, which is worth saying because
`ArithmeticHeights/Laplace.lean` proves that expansion and derives the same submultiplicativity
from it by a different route. Neither route subsumes the other: this one reaches the submodular
inequality, which the expansion alone does not.

Nothing here is specific to a number field until the last section. The statements are proved for an
arbitrary `AbsoluteValue K ℝ` with `IsNonarchimedean`, and `NumberField.FinitePlace` is fed to them
through `NumberField.FinitePlace.isNonarchimedean_val`.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Theorem 2.8.13 and §1.3 for the local Gauss norms.

W. M. Schmidt, *Diophantine Approximation*, Lecture Notes in Mathematics 785, Springer (1980),
Chapter I, Lemma 8A.

T. Struppeck and J. D. Vaaler, *Inequalities for heights of algebraic subspaces and the
Thue–Siegel principle*, in *Analytic Number Theory* (Allerton Park, 1989), Birkhäuser (1990),
493–528.

This is Layer 3.6 of the `ArithmeticHeights` roadmap.
-/
public section

namespace exteriorPower

open Matrix

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [LinearOrder ι] {k : ℕ}

/-- A `k × k` minor read off an arbitrary list of `k` columns is, up to sign, a Plücker
coordinate — and it vanishes outright when a column repeats. -/
private theorem det_submatrix_eq_zero_or_eq_or_eq_neg (X : Fin k → (ι → R)) (f : Fin k → ι) :
    (Matrix.of fun i j ↦ X i (f j)).det = 0 ∨
      ∃ s : Set.powersetCard ι k, (Matrix.of fun i j ↦ X i (f j)).det = plucker k X s ∨
        (Matrix.of fun i j ↦ X i (f j)).det = -plucker k X s := by
  classical
  by_cases hf : Function.Injective f
  · right
    have hcard : (Finset.image f Finset.univ).card = k := by
      rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
    set s : Set.powersetCard ι k := ⟨Finset.image f Finset.univ, by simpa using hcard⟩ with hs
    have hmem (i : Fin k) : f i ∈ (s : Finset ι) := by simp [hs]
    let e : Fin k ≃ (s : Finset ι) :=
      Equiv.ofBijective (fun i ↦ ⟨f i, hmem i⟩)
        ⟨fun i j hij ↦ hf (congrArg Subtype.val hij), by
          rintro ⟨x, hx⟩
          simp only [hs, Finset.mem_image, Finset.mem_univ, true_and] at hx
          obtain ⟨i, hi⟩ := hx
          exact ⟨i, by simp [hi]⟩⟩
    set σ : Equiv.Perm (Fin k) :=
      e.trans (Set.powersetCard.orderIsoOfFin s).symm.toEquiv with hσ
    refine ⟨s, ?_⟩
    have hcoe (j : Fin k) : Set.powersetCard.ofFinEmbEquiv.symm s j
        = ((Set.powersetCard.orderIsoOfFin s j : (s : Finset ι)) : ι) := rfl
    have hfσ (j : Fin k) : Set.powersetCard.ofFinEmbEquiv.symm s (σ j) = f j := by
      rw [hcoe, hσ]
      simp only [Equiv.trans_apply, OrderIso.coe_toEquiv, OrderIso.apply_symm_apply, e]
      rfl
    have hsub : (Matrix.of fun i j ↦ X i (f j)) =
        (Matrix.of fun i j ↦ X i (Set.powersetCard.ofFinEmbEquiv.symm s j)).submatrix id σ := by
      ext i j
      simp [hfσ j]
    rw [hsub, Matrix.det_permute', ← plucker_apply]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp
  · left
    rw [Function.not_injective_iff] at hf
    obtain ⟨i, j, hfij, hij⟩ := hf
    exact Matrix.det_zero_of_column_eq hij fun l ↦ by simp [hfij]

/-- **Left multiplication multiplies the Plücker coordinates by a determinant.** Changing the
basis of the span by `g` scales the whole coordinate tuple by `det g`. -/
theorem plucker_mul (g : Matrix (Fin k) (Fin k) R) (X : Fin k → (ι → R)) :
    plucker k (fun i ↦ (g * Matrix.of X) i) = g.det • plucker k X := by
  funext s
  rw [plucker_apply, Pi.smul_apply, smul_eq_mul, plucker_apply, ← Matrix.det_mul]
  congr 1

variable {p q : ℕ}

/-- **A block-triangular change of basis on a two-block family.** Replacing the first block by
`g A` and the second by `x A + h B` — a change of basis inside each block, together with an
arbitrary addition of the first block into the second — multiplies the Plücker coordinates by
`det g * det h`. Taking `x = 0` gives the two blocks scaled independently; taking `g = 1`, `h = 1`
gives the row operations that add multiples of the first block to the second, which change nothing
at all. -/
theorem plucker_append_mul (g : Matrix (Fin p) (Fin p) R) (h : Matrix (Fin q) (Fin q) R)
    (x : Matrix (Fin q) (Fin p) R) (A : Fin p → (ι → R)) (B : Fin q → (ι → R)) :
    plucker (p + q) (Fin.append (fun i ↦ (g * Matrix.of A) i)
        (fun i ↦ (x * Matrix.of A + h * Matrix.of B) i))
      = (g.det * h.det) • plucker (p + q) (Fin.append A B) := by
  classical
  set G : Matrix (Fin (p + q)) (Fin (p + q)) R :=
    Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g 0 x h) with hG
  have hdet : G.det = g.det * h.det := by
    rw [hG, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₁₂]
  have hentry (i : Fin (p + q)) (j : ι) : (G * Matrix.of (Fin.append A B)) i j
      = (∑ a, Matrix.fromBlocks g 0 x h (finSumFinEquiv.symm i) (Sum.inl a) * A a j) +
        ∑ b, Matrix.fromBlocks g 0 x h (finSumFinEquiv.symm i) (Sum.inr b) * B b j := by
    rw [Matrix.mul_apply, Fin.sum_univ_add]
    simp [hG]
  have hfam : Fin.append (fun i ↦ (g * Matrix.of A) i)
      (fun i ↦ (x * Matrix.of A + h * Matrix.of B) i)
      = fun i ↦ (G * Matrix.of (Fin.append A B)) i := by
    funext i j
    induction i using Fin.addCases with
    | left a => rw [Fin.append_left, hentry]; simp [Matrix.mul_apply]
    | right b =>
        rw [Fin.append_right, hentry]
        simp [Matrix.mul_apply, Matrix.add_apply]
  rw [hfam, plucker_mul, hdet]

variable {K : Type*} [Field K]

/-- **Every minor is bounded by the largest Plücker coordinate.** The `k × k` minor of a family
of `k` vectors on an arbitrary list of `k` columns — repetitions allowed, and in any order — is at
most the largest Plücker coordinate of the family, at every absolute value. -/
theorem apply_det_le_iSup_plucker (v : AbsoluteValue K ℝ) (X : Fin k → (ι → K)) (f : Fin k → ι) :
    v ((Matrix.of fun i j ↦ X i (f j)).det) ≤ ⨆ s : Set.powersetCard ι k, v (plucker k X s) := by
  have hnn : (0 : ℝ) ≤ ⨆ s : Set.powersetCard ι k, v (plucker k X s) :=
    Real.iSup_nonneg fun s ↦ v.nonneg _
  rcases det_submatrix_eq_zero_or_eq_or_eq_neg X f with h | ⟨s, h | h⟩
  · rw [h]
    simpa using hnn
  · rw [h]
    exact Finite.le_ciSup_of_le s le_rfl
  · rw [h, v.map_neg]
    exact Finite.le_ciSup_of_le s le_rfl

/-! ### Normalization at a nonarchimedean place -/

section Nonarchimedean

variable {v : AbsoluteValue K ℝ}

/-- The largest Plücker coordinate is nonnegative, degenerate cases included. -/
theorem iSup_plucker_nonneg (v : AbsoluteValue K ℝ) (X : Fin k → (ι → K)) :
    0 ≤ ⨆ s : Set.powersetCard ι k, v (plucker k X s) :=
  Real.iSup_nonneg fun _ ↦ v.nonneg _

/-- A determinant whose entries lie in the valuation ring lies in the valuation ring. The Leibniz
formula writes it as a sum of products, and at a nonarchimedean place a sum is no larger than its
largest term: no expansion along a block of rows is involved. -/
private theorem apply_det_le_one (hv : IsNonarchimedean v) {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n K} (hM : ∀ i j, v (M i j) ≤ 1) : v M.det ≤ 1 := by
  rw [Matrix.det_apply']
  refine (hv.apply_sum_le_sup Finset.univ_nonempty).trans (Finset.sup'_le _ _ fun σ _ ↦ ?_)
  rw [map_mul]
  have h1 : v ((Equiv.Perm.sign σ : ℤ) : K) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp
  rw [h1, one_mul, map_prod]
  exact Finset.prod_le_one₀ (fun i _ ↦ v.nonneg _) fun i _ ↦ hM _ _

/-- Every Plücker coordinate of an integral family is integral. -/
theorem iSup_plucker_le_one (hv : IsNonarchimedean v) {X : Fin k → (ι → K)}
    (hX : ∀ i j, v (X i j) ≤ 1) : (⨆ s : Set.powersetCard ι k, v (plucker k X s)) ≤ 1 := by
  refine Real.iSup_le (fun s ↦ ?_) zero_le_one
  rw [plucker_apply]
  exact apply_det_le_one hv fun i j ↦ hX _ _

/-- **Local normalization at a nonarchimedean place.** A family with a nonzero Plücker point has a
change of basis `g` making every entry of `g X` integral, whose minor on the columns of a largest
Plücker coordinate is the identity matrix, and whose determinant has absolute value the reciprocal
of that largest coordinate.

The rows of `g X` are an `Oᵥ`-basis of the saturated lattice `span X ∩ Oᵥⁿ`, produced by Cramer's
rule rather than by the structure theory of modules over the valuation ring: the entries of
`(X_{s₀})⁻¹ X` are ratios of `k × k` minors of `X` to the largest one, so they are integral exactly
because `s₀` maximises. -/
theorem exists_integral_basis (v : AbsoluteValue K ℝ) {X : Fin k → (ι → K)}
    (hX : plucker k X ≠ 0) :
    ∃ (g : Matrix (Fin k) (Fin k) K) (s₀ : Set.powersetCard ι k),
      (∀ i j, v ((g * Matrix.of X) i j) ≤ 1) ∧
        (Matrix.of fun i j ↦ (g * Matrix.of X) i (Set.powersetCard.ofFinEmbEquiv.symm s₀ j)) = 1 ∧
          v g.det * (⨆ s : Set.powersetCard ι k, v (plucker k X s)) = 1 := by
  classical
  obtain ⟨s₁, hs₁⟩ := Function.ne_iff.mp hX
  have : Nonempty (Set.powersetCard ι k) := ⟨s₁⟩
  obtain ⟨s₀, hs₀⟩ : ∃ s, v (plucker k X s) = ⨆ s : Set.powersetCard ι k, v (plucker k X s) :=
    exists_eq_ciSup_of_finite
  set M : Matrix (Fin k) (Fin k) K :=
    Matrix.of fun i j ↦ X i (Set.powersetCard.ofFinEmbEquiv.symm s₀ j) with hM
  have hvdet : v M.det = ⨆ s : Set.powersetCard ι k, v (plucker k X s) := by
    rw [hM, ← plucker_apply, hs₀]
  have hpos : 0 < ⨆ s : Set.powersetCard ι k, v (plucker k X s) :=
    lt_of_lt_of_le (v.pos hs₁) (Finite.le_ciSup_of_le s₁ le_rfl)
  have hne : M.det ≠ 0 := by
    intro h
    rw [h, map_zero] at hvdet
    exact hpos.ne' hvdet.symm
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hne
  refine ⟨M⁻¹, s₀, fun i j ↦ ?_, ?_, ?_⟩
  · have hmv : (M.adjugate * Matrix.of X) i j = (M.adjugate *ᵥ fun l ↦ X l j) i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    have h1 : (M⁻¹ * Matrix.of X) i j = M.det⁻¹ * (M.updateCol i fun l ↦ X l j).det := by
      rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul,
        hmv, ← Matrix.cramer_eq_adjugate_mulVec, Matrix.cramer_apply]
    have h2 : M.updateCol i (fun l ↦ X l j)
        = Matrix.of fun l m ↦
            X l (Function.update (⇑(Set.powersetCard.ofFinEmbEquiv.symm s₀)) i j m) := by
      ext l m
      rcases eq_or_ne m i with rfl | hm
      · simp
      · simp [hm, hM]
    rw [h1, h2, map_mul, map_inv₀, hvdet, inv_mul_le_iff₀ hpos, mul_one]
    exact apply_det_le_iSup_plucker v X _
  · have h3 : (Matrix.of fun i j ↦
        (M⁻¹ * Matrix.of X) i (Set.powersetCard.ofFinEmbEquiv.symm s₀ j)) = M⁻¹ * M := by
      ext i j
      simp [Matrix.mul_apply, hM]
    rw [h3, Matrix.nonsing_inv_mul _ hunit]
  · rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, map_inv₀, hvdet,
      inv_mul_cancel₀ hpos.ne']

/-! ### Submultiplicativity -/

variable {p q r : ℕ}

/-- A family with a linearly dependent block has a vanishing Plücker point. -/
private theorem plucker_append_eq_zero_left {B : Fin q → (ι → K)} {C : Fin r → (ι → K)}
    (hB : plucker q B = 0) : plucker (q + r) (Fin.append B C) = 0 := by
  rw [plucker_eq_zero_iff] at hB ⊢
  exact fun h ↦ hB (by
    simpa [Function.comp_def] using h.comp (Fin.castAdd r) (Fin.castAdd_injective _ _))

private theorem plucker_append_eq_zero_right {B : Fin q → (ι → K)} {C : Fin r → (ι → K)}
    (hC : plucker r C = 0) : plucker (q + r) (Fin.append B C) = 0 := by
  rw [plucker_eq_zero_iff] at hC ⊢
  exact fun h ↦ hC (by
    simpa [Function.comp_def] using h.comp (Fin.natAdd q) (Fin.natAdd_injective _ _))

private theorem iSup_plucker_eq_zero {X : Fin k → (ι → K)} (hX : plucker k X = 0) :
    (⨆ s : Set.powersetCard ι k, v (plucker k X s)) = 0 := by
  have h : ∀ s : Set.powersetCard ι k, v (plucker k X s) = 0 := by simp [hX]
  exact le_antisymm (Real.iSup_le (fun s ↦ (h s).le) le_rfl) (iSup_plucker_nonneg v X)

omit [Fintype ι] [LinearOrder ι] in
private theorem append_apply_le_one {B : Fin q → (ι → K)} {C : Fin r → (ι → K)}
    (hB : ∀ i j, v (B i j) ≤ 1) (hC : ∀ i j, v (C i j) ≤ 1) (i : Fin (q + r)) (j : ι) :
    v (Fin.append B C i j) ≤ 1 := by
  induction i using Fin.addCases with
  | left a => rw [Fin.append_left]; exact hB a j
  | right b => rw [Fin.append_right]; exact hC b j

/-- Two blocks scaled independently. -/
theorem plucker_append_mul_left_right (g : Matrix (Fin p) (Fin p) K)
    (h : Matrix (Fin q) (Fin q) K) (A : Fin p → (ι → K)) (B : Fin q → (ι → K)) :
    plucker (p + q) (Fin.append (fun i ↦ (g * Matrix.of A) i) (fun i ↦ (h * Matrix.of B) i))
      = (g.det * h.det) • plucker (p + q) (Fin.append A B) := by
  simpa using plucker_append_mul g h 0 A B

/-- **Row operations across the cut change nothing.** Adding multiples of the rows of the first
block to the rows of the second leaves every Plücker coordinate of the stack alone. -/
theorem plucker_append_add (x : Matrix (Fin q) (Fin p) K) (A : Fin p → (ι → K))
    (B : Fin q → (ι → K)) :
    plucker (p + q) (Fin.append A (fun i ↦ (x * Matrix.of A + Matrix.of B) i))
      = plucker (p + q) (Fin.append A B) := by
  have key := plucker_append_mul 1 1 x A B
  simp only [Matrix.det_one, one_mul, Matrix.one_mul, one_smul] at key
  exact key

/-- **The Plücker norm is submultiplicative at a nonarchimedean place.** Stacking two families
multiplies their largest Plücker coordinates at most: `‖p(B;C)‖ᵥ ≤ ‖p(B)‖ᵥ ‖p(C)‖ᵥ`.

Both families are first replaced by integral bases of their saturated lattices, after which the
stack is integral and every one of its minors lies in the valuation ring — the Leibniz formula and
nothing else. -/
theorem iSup_plucker_append_le (hv : IsNonarchimedean v) (B : Fin q → (ι → K))
    (C : Fin r → (ι → K)) :
    (⨆ s : Set.powersetCard ι (q + r), v (plucker (q + r) (Fin.append B C) s)) ≤
      (⨆ s : Set.powersetCard ι q, v (plucker q B s)) *
        (⨆ s : Set.powersetCard ι r, v (plucker r C s)) := by
  rcases eq_or_ne (plucker q B) 0 with hB0 | hB0
  · rw [iSup_plucker_eq_zero (plucker_append_eq_zero_left hB0), iSup_plucker_eq_zero hB0,
      zero_mul]
  rcases eq_or_ne (plucker r C) 0 with hC0 | hC0
  · rw [iSup_plucker_eq_zero (plucker_append_eq_zero_right hC0), iSup_plucker_eq_zero hC0,
      mul_zero]
  obtain ⟨g, -, hgint, -, hgdet⟩ := exists_integral_basis v hB0
  obtain ⟨h, -, hhint, -, hhdet⟩ := exists_integral_basis v hC0
  have hkey : (⨆ s : Set.powersetCard ι (q + r),
      v (plucker (q + r) (Fin.append (fun i ↦ (g * Matrix.of B) i)
        (fun i ↦ (h * Matrix.of C) i)) s)) ≤ 1 :=
    iSup_plucker_le_one hv (append_apply_le_one hgint hhint)
  rw [plucker_append_mul_left_right] at hkey
  have hconst : ∀ s : Set.powersetCard ι (q + r),
      v (((g.det * h.det) • plucker (q + r) (Fin.append B C)) s)
        = (v g.det * v h.det) * v (plucker (q + r) (Fin.append B C) s) := by
    intro s
    simp [smul_eq_mul, map_mul, mul_assoc]
  simp only [hconst] at hkey
  rw [← Real.mul_iSup_of_nonneg (by positivity)] at hkey
  have hab : 0 < v g.det * v h.det := by
    have h1 : v g.det ≠ 0 := left_ne_zero_of_mul_eq_one hgdet
    have h2 : v h.det ≠ 0 := left_ne_zero_of_mul_eq_one hhdet
    exact mul_pos ((v.nonneg _).lt_of_ne' h1) ((v.nonneg _).lt_of_ne' h2)
  refine le_of_mul_le_mul_right ?_ hab
  calc (⨆ s : Set.powersetCard ι (q + r), v (plucker (q + r) (Fin.append B C) s)) *
        (v g.det * v h.det) ≤ 1 := by rw [mul_comm]; exact hkey
    _ = (⨆ s : Set.powersetCard ι q, v (plucker q B s)) *
          (⨆ s : Set.powersetCard ι r, v (plucker r C s)) * (v g.det * v h.det) := by
        rw [show (⨆ s : Set.powersetCard ι q, v (plucker q B s)) *
              (⨆ s : Set.powersetCard ι r, v (plucker r C s)) * (v g.det * v h.det)
            = (v g.det * (⨆ s : Set.powersetCard ι q, v (plucker q B s))) *
              (v h.det * (⨆ s : Set.powersetCard ι r, v (plucker r C s))) from by ring,
          hgdet, hhdet, one_mul]

/-! ### Submodularity -/

/-- The first block scaled alone. -/
theorem plucker_append_mul_left (g : Matrix (Fin p) (Fin p) K) (A : Fin p → (ι → K))
    (B : Fin q → (ι → K)) :
    plucker (p + q) (Fin.append (fun i ↦ (g * Matrix.of A) i) B)
      = g.det • plucker (p + q) (Fin.append A B) := by
  have key := plucker_append_mul g 1 0 A B
  simp only [Matrix.det_one, mul_one, Matrix.zero_mul, zero_add, Matrix.one_mul] at key
  exact key

private theorem iSup_plucker_of_eq_smul {c : K} {X Y : Fin k → (ι → K)}
    (h : plucker k X = c • plucker k Y) :
    (⨆ s : Set.powersetCard ι k, v (plucker k X s))
      = v c * ⨆ s : Set.powersetCard ι k, v (plucker k Y s) := by
  rw [Real.mul_iSup_of_nonneg (v.nonneg c)]
  exact iSup_congr fun s ↦ by rw [h]; simp [smul_eq_mul, map_mul]

/-- With the first block normalized so that its minor on `s₀` is the identity, and the second block
reduced so that its `s₀`-columns vanish, every Plücker coordinate of the second block alone is a
minor of the stack — so the stack has the larger Plücker norm. -/
private theorem iSup_plucker_le_iSup_plucker_append {A : Fin p → (ι → K)} {B : Fin q → (ι → K)}
    {s₀ : Set.powersetCard ι p}
    (hA : (Matrix.of fun i j ↦ A i (Set.powersetCard.ofFinEmbEquiv.symm s₀ j)) = 1)
    (hB : ∀ i j, B i (Set.powersetCard.ofFinEmbEquiv.symm s₀ j) = 0) :
    (⨆ s : Set.powersetCard ι q, v (plucker q B s)) ≤
      ⨆ s : Set.powersetCard ι (p + q), v (plucker (p + q) (Fin.append A B) s) := by
  have hA' (a b : Fin p) :
      A a (Set.powersetCard.ofFinEmbEquiv.symm s₀ b) = (1 : Matrix (Fin p) (Fin p) K) a b := by
    rw [← hA]
    rfl
  refine Real.iSup_le (fun s ↦ ?_) (iSup_plucker_nonneg v _)
  set f : Fin (p + q) → ι := Fin.append (⇑(Set.powersetCard.ofFinEmbEquiv.symm s₀))
      (⇑(Set.powersetCard.ofFinEmbEquiv.symm s)) with hf
  have hblock : (Matrix.of fun i j ↦ Fin.append A B i (f j))
      = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1
          (Matrix.of fun i j ↦ A i (Set.powersetCard.ofFinEmbEquiv.symm s j)) 0
          (Matrix.of fun i j ↦ B i (Set.powersetCard.ofFinEmbEquiv.symm s j))) := by
    ext i j
    induction i using Fin.addCases with
    | left a =>
        induction j using Fin.addCases with
        | left b => simp [hf, hA']
        | right b => simp [hf]
    | right a =>
        induction j using Fin.addCases with
        | left b => simp [hf, hB]
        | right b => simp [hf]
  have hdet : (Matrix.of fun i j ↦ Fin.append A B i (f j)).det
      = (Matrix.of fun i j ↦ B i (Set.powersetCard.ofFinEmbEquiv.symm s j)).det := by
    rw [hblock, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]
  rw [plucker_apply, ← hdet]
  exact apply_det_le_iSup_plucker v _ f

omit [Fintype ι] [LinearOrder ι] in
/-- The arithmetic that turns the normalized inequality into the general one. -/
private theorem mul_le_mul_of_normalized {a nA nAB nAC nABC : ℝ} (ha : 0 < a) (hnA : a * nA = 1)
    (hnA' : 0 ≤ nA) (key : a * nABC ≤ a * nAB * (a * nAC)) : nABC * nA ≤ nAB * nAC := by
  have key2 : nABC ≤ a * (nAB * nAC) := by
    refine le_of_mul_le_mul_left ?_ ha
    calc a * nABC ≤ a * nAB * (a * nAC) := key
      _ = a * (a * (nAB * nAC)) := by ring
  calc nABC * nA ≤ a * (nAB * nAC) * nA := mul_le_mul_of_nonneg_right key2 hnA'
    _ = a * nA * (nAB * nAC) := by ring
    _ = nAB * nAC := by rw [hnA, one_mul]

/-- The submodular inequality once the first block has been normalized: its Plücker norm is `1`
and its minor on `s₀` is the identity matrix. Reducing the other two blocks against it — a row
operation, which changes no Plücker coordinate — makes their `s₀`-columns vanish, and then two
applications of submultiplicativity and two of `iSup_plucker_le_iSup_plucker_append` close the
chain. -/
private theorem iSup_plucker_submodular_normalized (hv : IsNonarchimedean v)
    {A : Fin p → (ι → K)} {s₀ : Set.powersetCard ι p}
    (hA : (Matrix.of fun i j ↦ A i (Set.powersetCard.ofFinEmbEquiv.symm s₀ j)) = 1)
    (hAone : (⨆ s : Set.powersetCard ι p, v (plucker p A s)) = 1)
    (B : Fin q → (ι → K)) (C : Fin r → (ι → K)) :
    (⨆ s : Set.powersetCard ι (p + (q + r)),
          v (plucker (p + (q + r)) (Fin.append A (Fin.append B C)) s))
      ≤ (⨆ s : Set.powersetCard ι (p + q), v (plucker (p + q) (Fin.append A B) s)) *
          (⨆ s : Set.powersetCard ι (p + r), v (plucker (p + r) (Fin.append A C) s)) := by
  classical
  have hA' (a b : Fin p) :
      A a (Set.powersetCard.ofFinEmbEquiv.symm s₀ b) = (1 : Matrix (Fin p) (Fin p) K) a b := by
    rw [← hA]
    rfl
  have hAmul {m : ℕ} (X : Matrix (Fin m) (Fin p) K) (i : Fin m) (j : Fin p) :
      (X * Matrix.of A) i (Set.powersetCard.ofFinEmbEquiv.symm s₀ j) = X i j := by
    simp [Matrix.mul_apply, hA', Matrix.one_apply]
  set xB : Matrix (Fin q) (Fin p) K :=
    Matrix.of fun i j ↦ B i (Set.powersetCard.ofFinEmbEquiv.symm s₀ j) with hxB
  set xC : Matrix (Fin r) (Fin p) K :=
    Matrix.of fun i j ↦ C i (Set.powersetCard.ofFinEmbEquiv.symm s₀ j) with hxC
  set B' : Fin q → (ι → K) := fun i ↦ ((-xB) * Matrix.of A + Matrix.of B) i with hB'
  set C' : Fin r → (ι → K) := fun i ↦ ((-xC) * Matrix.of A + Matrix.of C) i with hC'
  have hB'0 (i : Fin q) (j : Fin p) :
      B' i (Set.powersetCard.ofFinEmbEquiv.symm s₀ j) = 0 := by
    rw [hB']
    simp [Matrix.add_apply, hAmul, hxB]
  have hC'0 (i : Fin r) (j : Fin p) :
      C' i (Set.powersetCard.ofFinEmbEquiv.symm s₀ j) = 0 := by
    rw [hC']
    simp [Matrix.add_apply, hAmul, hxC]
  have hpB : plucker (p + q) (Fin.append A B') = plucker (p + q) (Fin.append A B) := by
    rw [hB']
    exact plucker_append_add (-xB) A B
  have hpC : plucker (p + r) (Fin.append A C') = plucker (p + r) (Fin.append A C) := by
    rw [hC']
    exact plucker_append_add (-xC) A C
  have hpBC : plucker (p + (q + r)) (Fin.append A (Fin.append B' C'))
      = plucker (p + (q + r)) (Fin.append A (Fin.append B C)) := by
    have hx : Fin.append B' C' = fun i ↦
        ((-(Matrix.of (Fin.append (fun i ↦ xB i) (fun i ↦ xC i)))) * Matrix.of A
          + Matrix.of (Fin.append B C)) i := by
      funext i j
      induction i using Fin.addCases with
      | left a => simp [hB', Matrix.add_apply, Matrix.mul_apply]
      | right b => simp [hC', Matrix.add_apply, Matrix.mul_apply]
    rw [hx]
    exact plucker_append_add _ A (Fin.append B C)
  calc (⨆ s : Set.powersetCard ι (p + (q + r)),
        v (plucker (p + (q + r)) (Fin.append A (Fin.append B C)) s))
      = ⨆ s : Set.powersetCard ι (p + (q + r)),
          v (plucker (p + (q + r)) (Fin.append A (Fin.append B' C')) s) := by rw [hpBC]
    _ ≤ (⨆ s : Set.powersetCard ι p, v (plucker p A s)) *
          ⨆ s : Set.powersetCard ι (q + r), v (plucker (q + r) (Fin.append B' C') s) :=
        iSup_plucker_append_le hv A (Fin.append B' C')
    _ = ⨆ s : Set.powersetCard ι (q + r), v (plucker (q + r) (Fin.append B' C') s) := by
        rw [hAone, one_mul]
    _ ≤ (⨆ s : Set.powersetCard ι q, v (plucker q B' s)) *
          ⨆ s : Set.powersetCard ι r, v (plucker r C' s) := iSup_plucker_append_le hv B' C'
    _ ≤ (⨆ s : Set.powersetCard ι (p + q), v (plucker (p + q) (Fin.append A B') s)) *
          ⨆ s : Set.powersetCard ι (p + r), v (plucker (p + r) (Fin.append A C') s) :=
        mul_le_mul (iSup_plucker_le_iSup_plucker_append hA hB'0)
          (iSup_plucker_le_iSup_plucker_append hA hC'0) (iSup_plucker_nonneg v C')
          (iSup_plucker_nonneg v _)
    _ = _ := by rw [hpB, hpC]

/-- **The Plücker norm is submodular at a nonarchimedean place.** For three families of vectors
stacked in the four ways that matter,

`‖p(A;B;C)‖ᵥ · ‖p(A)‖ᵥ ≤ ‖p(A;B)‖ᵥ · ‖p(A;C)‖ᵥ`.

This is the nonarchimedean half of the submodularity of the height of a subspace, and the
counterpart of `NumberField.InfinitePlace.sum_sq_plucker_append_mul_le`. Unlike the archimedean
half it is not Koteljanskii's inequality: there is no orthogonal projection at a finite place.
What replaces it is the normalization of `A` to an integral basis of its saturated lattice, after
which `‖p(A)‖ᵥ = 1`, the other two blocks can be reduced so that their columns on `A`'s pivot set
vanish, and the whole statement collapses to submultiplicativity applied twice. -/
theorem iSup_plucker_append_append_mul_le (hv : IsNonarchimedean v) (A : Fin p → (ι → K))
    (B : Fin q → (ι → K)) (C : Fin r → (ι → K)) :
    (⨆ s : Set.powersetCard ι (p + (q + r)),
          v (plucker (p + (q + r)) (Fin.append A (Fin.append B C)) s)) *
        (⨆ s : Set.powersetCard ι p, v (plucker p A s))
      ≤ (⨆ s : Set.powersetCard ι (p + q), v (plucker (p + q) (Fin.append A B) s)) *
          (⨆ s : Set.powersetCard ι (p + r), v (plucker (p + r) (Fin.append A C) s)) := by
  rcases eq_or_ne (plucker p A) 0 with hA0 | hA0
  · rw [iSup_plucker_eq_zero hA0, mul_zero]
    exact mul_nonneg (iSup_plucker_nonneg v _) (iSup_plucker_nonneg v _)
  obtain ⟨g, s₀, -, hgid, hgdet⟩ := exists_integral_basis v hA0
  have ha : 0 < v g.det := (v.nonneg _).lt_of_ne' (left_ne_zero_of_mul_eq_one hgdet)
  have hAone : (⨆ s : Set.powersetCard ι p, v (plucker p (fun i ↦ (g * Matrix.of A) i) s)) = 1 := by
    rw [iSup_plucker_of_eq_smul (plucker_mul g A)]
    exact hgdet
  have key := iSup_plucker_submodular_normalized hv hgid hAone B C
  rw [iSup_plucker_of_eq_smul (plucker_append_mul_left g A B),
    iSup_plucker_of_eq_smul (plucker_append_mul_left g A C),
    iSup_plucker_of_eq_smul (plucker_append_mul_left g A (Fin.append B C))] at key
  exact mul_le_mul_of_normalized ha hgdet (iSup_plucker_nonneg v A) key

end Nonarchimedean

end exteriorPower

/-! ### The finite places of a number field -/

namespace NumberField.FinitePlace

open exteriorPower

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [LinearOrder ι] {p q r : ℕ}

omit [Fintype ι] [LinearOrder ι] in
/-- A finite place is nonarchimedean, read as a statement about the underlying absolute value. -/
theorem isNonarchimedean_val (v : FinitePlace K) : IsNonarchimedean (v.val : K → ℝ) :=
  fun x y ↦ by simpa only [← coe_apply] using v.add_le x y

/-- **The finite local factor of the height of a subspace is submodular.** At a finite place `v` of
a number field, the local factor `maxₛ v(pₛ)` of the tuple of Plücker coordinates — the quantity
both normalizations of Layer 0 take at a finite place — obeys the inequality of the milestone for
three families of vectors stacked in the four ways that matter.

This is the finite half of the submodularity of the Arakelov height of a subspace; the archimedean
half is `NumberField.InfinitePlace.sum_sq_plucker_append_mul_le`. -/
theorem iSup_plucker_append_mul_le (v : FinitePlace K) (a : Fin p → (ι → K))
    (b : Fin q → (ι → K)) (c : Fin r → (ι → K)) :
    (⨆ s : Set.powersetCard ι (p + (q + r)),
          v (plucker (p + (q + r)) (Fin.append a (Fin.append b c)) s)) *
        (⨆ s : Set.powersetCard ι p, v (plucker p a s))
      ≤ (⨆ s : Set.powersetCard ι (p + q), v (plucker (p + q) (Fin.append a b) s)) *
          (⨆ s : Set.powersetCard ι (p + r), v (plucker (p + r) (Fin.append a c) s)) := by
  simpa only [← coe_apply] using
    exteriorPower.iSup_plucker_append_append_mul_le (isNonarchimedean_val v) a b c

end NumberField.FinitePlace

end
