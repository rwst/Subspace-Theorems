/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.CauchyBinet
public import Mathlib.Data.Matrix.ColumnRowPartitioned

-- Used only inside proofs: the lexicographic order on a sum type, the criterion for a vanishing
-- determinant, and the definiteness of the dot product over an ordered ring.
import Mathlib.Data.Sum.Order
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# The generalized Hadamard inequality

Cut the rows of a matrix into two blocks. The Gram determinant of the whole is at most the product
of the Gram determinants of the blocks:

`det (A Aᵀ) ≤ det (A₁ A₁ᵀ) · det (A₂ A₂ᵀ)`.

Through the Cauchy–Binet identity of Layer 3.4 this says that the ℓ² norm of the tuple of maximal
minors of `A` is at most the product of the ℓ² norms of the tuples of the two blocks — the
archimedean local factor of the Arakelov height of the row space is submultiplicative under cutting
the rows. Iterating down to one row per block gives **Hadamard's inequality**, that the Gram
determinant is at most the product of the squared lengths of the rows, which is the form Layer 5.5
uses to replace the row-space height by the heights of the individual rows.

This is Schmidt's §2 Lemma 2, Bombieri–Vaaler (2.6), and the Fischer inequality of
Bombieri–Gubler's Remark 2.8.9. Everything here is proved over an arbitrary ordered field: the
statements are about determinants, not about norms, and nothing analytic enters.

## Main results

* `Matrix.det_mul_transpose_self_fromRows_le`: the inequality itself, for the two blocks of
  `Matrix.fromRows`. `Matrix.det_mul_transpose_self_le_mul` is the same statement for a matrix whose
  rows are indexed by `Fin (p + q)`, cut at `p`.
* `Matrix.det_mul_transpose_self_le_prod`: **Hadamard's inequality**, the fully split case
  `det (A Aᵀ) ≤ ∏ᵢ ‖Aᵢ‖²`, by induction on the number of rows.
* `Matrix.det_mul_transpose_self_le_det_add`: adding a Gram matrix to a Gram matrix does not
  decrease the determinant — Minkowski's monotonicity, in the only case needed.
* `Matrix.det_mul_transpose_self_submatrix_le`: deleting columns does not increase the Gram
  determinant.

## Implementation notes

Neither Fischer's inequality nor Hadamard's is in Mathlib, and neither is the determinant
monotonicity on the positive semidefinite order that the textbook proof of Fischer runs through
(Schur complement, then `0 ≼ S ≼ G₂₂ ⇒ det S ≤ det G₂₂`). The route taken here replaces that
monotonicity by **Cauchy–Binet over a doubled column index**, which is elementary: if `V` and `W`
have orthogonal row spaces then `(V + W) (V + W)ᵀ = V Vᵀ + W Wᵀ` is the Gram matrix of the single
matrix `Matrix.fromCols V W`, whose maximal minors indexed by the columns of the first copy are
exactly those of `V`, so its sum of squares of minors is a sub-sum of the whole — and a sum of
squares only grows when terms are added. That is `Matrix.det_mul_transpose_self_submatrix_le`
followed by `Matrix.det_mul_transpose_self_le_det_add`.

The doubled index is `ι ⊕ₗ ι`, the lexicographic sum: the plain `ι ⊕ ι` carries Mathlib's
componentwise order, which is not linear, and `exteriorPower.plucker` needs a linear order on the
column type to say which minor a set of columns names. Only the order matters, never which order:
the determinants in the statement do not see it.

With that in hand the proof is the classical one. Project the second block orthogonally to the
first — possible exactly when `det (A₁ A₁ᵀ) ≠ 0`, and when it is `0` both sides vanish, by the
Gram criterion — which is a row operation of determinant `1`, so it changes no Gram determinant;
the Gram matrix becomes block diagonal, so its determinant factors; and the projected block has the
smaller Gram determinant by the monotonicity above.

## References

W. M. Schmidt, "On heights of algebraic subspaces and diophantine approximations",
*Annals of Mathematics* **85** (1967), 430–472, §2 Lemma 2. E. Bombieri and J. Vaaler,
"On Siegel's lemma", *Inventiones Mathematicae* **73** (1983), 11–32, equation (2.6).
E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Remark 2.8.9, where it is the Fischer inequality, and 2.9.8 for the use made of it.

This is Layer 3.4 of the `ArithmeticHeights` roadmap, the companion of
`ArithmeticHeights.CauchyBinet`.
-/

public section

namespace Matrix

open Module exteriorPower

/-!
### Deleting columns
-/

section Submatrix

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [LinearOrder ι] {q : ℕ}

/-- **The maximal minors of a column submatrix are maximal minors of the matrix.** For an order
embedding of the column index the increasing enumerations agree, so no sign appears. -/
theorem plucker_row_submatrix {κ : Type*} [Fintype κ] [LinearOrder κ]
    (B : Matrix (Fin q) κ R) (f : ι ↪o κ) (s : Set.powersetCard ι q) :
    plucker q (B.submatrix id f).row s
      = plucker q B.row ⟨(s : Finset ι).map f.toEmbedding, Set.powersetCard.mem_iff.2 (by
          simp [Set.powersetCard.card_eq s])⟩ := by
  rw [plucker_apply, plucker_apply, Set.powersetCard.ofFinEmbEquiv_symm_apply,
    Set.powersetCard.ofFinEmbEquiv_symm_apply]
  congr 1
  funext i j
  simp only [Matrix.of_apply, Matrix.submatrix_apply, Matrix.row]
  congr 1
  exact congrFun (Finset.orderEmbOfFin_unique _
    (fun x ↦ Finset.mem_map_of_mem _ (Finset.orderEmbOfFin_mem _ _ x))
    (f.strictMono.comp (Finset.orderEmbOfFin _ _).strictMono)) j

end Submatrix

/-!
### Monotonicity of the Gram determinant
-/

section Monotone

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {q : ℕ}

/-- **Deleting columns does not increase the Gram determinant.** By Cauchy–Binet each side is a sum
of squares of maximal minors, and the minors on the left are some of the minors on the right. -/
theorem det_mul_transpose_self_submatrix_le {κ : Type*} [Fintype κ] [LinearOrder κ]
    (B : Matrix (Fin q) κ K) (f : ι ↪o κ) :
    ((B.submatrix id f) * (B.submatrix id f)ᵀ).det ≤ (B * Bᵀ).det := by
  classical
  rw [det_mul_transpose_self_eq_sum_sq, det_mul_transpose_self_eq_sum_sq]
  set F : Set.powersetCard ι q → Set.powersetCard κ q := fun s ↦
    ⟨(s : Finset ι).map f.toEmbedding, Set.powersetCard.mem_iff.2 (by
      simp [Set.powersetCard.card_eq s])⟩ with hFdef
  have hF : Function.Injective F := fun s t h ↦
    Subtype.ext (Finset.map_injective _ (congrArg Subtype.val h))
  calc ∑ s : Set.powersetCard ι q, plucker q (B.submatrix id f).row s ^ 2
      = ∑ s : Set.powersetCard ι q, plucker q B.row (F s) ^ 2 :=
        Finset.sum_congr rfl fun s _ ↦ by rw [plucker_row_submatrix]
    _ = ∑ t ∈ Finset.image F Finset.univ, plucker q B.row t ^ 2 :=
        (Finset.sum_image (f := fun t ↦ plucker q B.row t ^ 2) fun x _ y _ h ↦ hF h).symm
    _ ≤ ∑ t : Set.powersetCard κ q, plucker q B.row t ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ ↦ sq_nonneg _

/-- **Minkowski's monotonicity, in the case needed.** Adding a Gram matrix to a Gram matrix does not
decrease the determinant: the sum is the Gram matrix of the two matrices side by side, and deleting
the second block of columns is the previous lemma. -/
theorem det_mul_transpose_self_le_det_add (V W : Matrix (Fin q) ι K) :
    (V * Vᵀ).det ≤ (V * Vᵀ + W * Wᵀ).det := by
  set B : Matrix (Fin q) (ι ⊕ₗ ι) K := Matrix.of fun i j ↦ Sum.elim (V i) (W i) (ofLex j) with hB
  have h1 : B.submatrix id (OrderEmbedding.ofStrictMono (⇑toLex ∘ Sum.inl)
      Sum.Lex.inl_strictMono) = V := rfl
  have h2 : B * Bᵀ = V * Vᵀ + W * Wᵀ := by
    ext i j
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply,
      show (∑ c : ι ⊕ₗ ι, B i c * Bᵀ c j) = ∑ c : ι ⊕ ι, B i (toLex c) * Bᵀ (toLex c) j from
        Fintype.sum_equiv (toLex (α := ι ⊕ ι)) _ _ fun c ↦ rfl, Fintype.sum_sum_type]
    rfl
  have h := det_mul_transpose_self_submatrix_le B
    (OrderEmbedding.ofStrictMono (⇑toLex ∘ Sum.inl) Sum.Lex.inl_strictMono)
  rwa [h1, h2] at h

end Monotone

/-!
### The generalized Hadamard inequality
-/

section Hadamard

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {p q : ℕ}

/-- **The generalized Hadamard inequality**, also called the Fischer inequality: cutting the rows of
a matrix into two blocks can only increase the product of the Gram determinants. Equivalently, by
Cauchy–Binet, the ℓ² norm of the tuple of maximal minors is submultiplicative under cutting the
rows. -/
theorem det_mul_transpose_self_fromRows_le (A : Matrix (Fin p) ι K) (B : Matrix (Fin q) ι K) :
    ((fromRows A B) * (fromRows A B)ᵀ).det ≤ (A * Aᵀ).det * (B * Bᵀ).det := by
  rcases eq_or_ne (A * Aᵀ).det 0 with hA | hA
  · -- The first block is degenerate: both sides vanish.
    rw [hA, zero_mul]
    refine le_of_eq ?_
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hA
    have hx : (c ᵥ* A) ᵥ* Aᵀ = 0 := by rw [Matrix.vecMul_vecMul]; exact hc
    have h2 : (c ᵥ* A) ⬝ᵥ (c ᵥ* A) = 0 := by
      nth_rewrite 2 [← Matrix.mulVec_transpose]
      rw [Matrix.dotProduct_mulVec, hx, zero_dotProduct]
    have hcA : c ᵥ* A = 0 := dotProduct_self_eq_zero.1 h2
    refine Matrix.exists_vecMul_eq_zero_iff.1 ⟨Sum.elim c 0, ?_, ?_⟩
    · exact fun h ↦ hc0 (funext fun i ↦ congrFun h (Sum.inl i))
    · rw [← Matrix.vecMul_vecMul, Matrix.vecMul_fromRows]
      simp [hcA]
  · -- Project the second block orthogonally to the first.
    have hAu : IsUnit (A * Aᵀ).det := isUnit_iff_ne_zero.2 hA
    set X : Matrix (Fin q) (Fin p) K := B * Aᵀ * (A * Aᵀ)⁻¹ with hX
    set B' : Matrix (Fin q) ι K := B - X * A with hB'
    have hXA : X * (A * Aᵀ) = B * Aᵀ := by
      rw [hX, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAu, Matrix.mul_one]
    have hB'A : B' * Aᵀ = 0 := by
      rw [hB', Matrix.sub_mul, Matrix.mul_assoc, hXA, sub_self]
    have hAB' : A * B'ᵀ = 0 := by
      have h := congrArg Matrix.transpose hB'A
      rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] at h
    -- The projection is a row operation of determinant `1`.
    have hUdet : (fromBlocks (1 : Matrix (Fin p) (Fin p) K) 0 (-X) 1).det = 1 := by
      rw [Matrix.det_fromBlocks_zero₁₂]
      simp
    have hUM : (fromBlocks (1 : Matrix (Fin p) (Fin p) K) 0 (-X) 1) * fromRows A B
        = fromRows A B' := by
      rw [Matrix.fromBlocks_mul_fromRows, Matrix.one_mul, Matrix.zero_mul, add_zero,
        Matrix.one_mul, Matrix.neg_mul, hB']
      congr 1
      abel
    have key : ((fromRows A B') * (fromRows A B')ᵀ).det = (A * Aᵀ).det * (B' * B'ᵀ).det := by
      rw [Matrix.transpose_fromRows, Matrix.fromRows_mul_fromCols, hAB',
        Matrix.det_fromBlocks_zero₁₂]
    have hdetM : ((fromRows A B) * (fromRows A B)ᵀ).det
        = ((fromRows A B') * (fromRows A B')ᵀ).det := by
      rw [← hUM, Matrix.transpose_mul, ← Matrix.mul_assoc,
        Matrix.mul_assoc _ (fromRows A B) _, Matrix.det_mul, Matrix.det_mul,
        Matrix.det_transpose, hUdet, one_mul, mul_one]
    -- The projected block has the smaller Gram determinant.
    have hBeq : B = B' + X * A := by rw [hB']; abel
    have hY1 : B' * (X * A)ᵀ = 0 := by
      rw [Matrix.transpose_mul, ← Matrix.mul_assoc, hB'A, Matrix.zero_mul]
    have hY2 : (X * A) * B'ᵀ = 0 := by rw [Matrix.mul_assoc, hAB', Matrix.mul_zero]
    have hsplit : B * Bᵀ = B' * B'ᵀ + (X * A) * (X * A)ᵀ := by
      conv_lhs => rw [hBeq]
      rw [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hY1, hY2]
      abel
    calc ((fromRows A B) * (fromRows A B)ᵀ).det = (A * Aᵀ).det * (B' * B'ᵀ).det := by
          rw [hdetM, key]
      _ ≤ (A * Aᵀ).det * (B * Bᵀ).det := by
          refine mul_le_mul_of_nonneg_left ?_ (det_mul_transpose_self_nonneg A)
          rw [hsplit]
          exact det_mul_transpose_self_le_det_add B' (X * A)

/-- The generalized Hadamard inequality for a matrix whose rows are indexed by `Fin (p + q)`, cut
into the first `p` and the last `q`. -/
theorem det_mul_transpose_self_le_mul (A : Matrix (Fin (p + q)) ι K) :
    (A * Aᵀ).det
      ≤ ((A.submatrix (Fin.castAdd q) id) * (A.submatrix (Fin.castAdd q) id)ᵀ).det *
          ((A.submatrix (Fin.natAdd p) id) * (A.submatrix (Fin.natAdd p) id)ᵀ).det := by
  have hfr : fromRows (A.submatrix (Fin.castAdd q) id) (A.submatrix (Fin.natAdd p) id)
      = A.submatrix finSumFinEquiv id := by
    ext (i | i) j <;> rfl
  have hre : (A.submatrix finSumFinEquiv id) * (A.submatrix finSumFinEquiv id)ᵀ
      = (A * Aᵀ).submatrix finSumFinEquiv finSumFinEquiv := by
    ext i j
    simp [Matrix.mul_apply]
  have h := det_mul_transpose_self_fromRows_le (A.submatrix (Fin.castAdd q) id)
    (A.submatrix (Fin.natAdd p) id)
  rwa [hfr, hre, Matrix.det_submatrix_equiv_self] at h

/-- **Hadamard's inequality.** The Gram determinant of the rows is at most the product of their
squared lengths: the fully split case of the generalized inequality, by induction on the number of
rows. This is the form Layer 5.5 uses to trade the height of the row space for the heights of the
individual rows. -/
theorem det_mul_transpose_self_le_prod {m : ℕ} (A : Matrix (Fin m) ι K) :
    (A * Aᵀ).det ≤ ∏ i, A.row i ⬝ᵥ A.row i := by
  induction m with
  | zero => simp
  | succ m ih =>
      set A' : Matrix (Fin m) ι K := A.submatrix Fin.castSucc id with hA'
      set a : Matrix (Fin 1) ι K := A.submatrix (fun _ ↦ Fin.last m) id with ha
      have hfr : fromRows A' a = A.submatrix finSumFinEquiv id := by
        ext (i | i) j
        · rfl
        · have hi : i = 0 := Subsingleton.elim _ _
          subst hi
          rfl
      have hre : (A.submatrix finSumFinEquiv id) * (A.submatrix finSumFinEquiv id)ᵀ
          = (A * Aᵀ).submatrix finSumFinEquiv finSumFinEquiv := by
        ext i j
        simp [Matrix.mul_apply]
      have h1 : (a * aᵀ).det = A.row (Fin.last m) ⬝ᵥ A.row (Fin.last m) := by
        rw [Matrix.det_fin_one]
        rfl
      calc (A * Aᵀ).det = ((fromRows A' a) * (fromRows A' a)ᵀ).det := by
            rw [hfr, hre, Matrix.det_submatrix_equiv_self]
        _ ≤ (A' * A'ᵀ).det * (a * aᵀ).det := det_mul_transpose_self_fromRows_le A' a
        _ ≤ (∏ i : Fin m, A'.row i ⬝ᵥ A'.row i) * (a * aᵀ).det := by
            refine mul_le_mul_of_nonneg_right (ih A') ?_
            rw [h1]
            exact Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _
        _ = ∏ i : Fin (m + 1), A.row i ⬝ᵥ A.row i := by
            rw [Fin.prod_univ_castSucc, h1]
            rfl

end Hadamard

end Matrix

section Examples

open Matrix exteriorPower

/-- **Acceptance test.** For the `2 × 3` matrix whose maximal minors are `1`, `3` and `−2`, the Gram
determinant is `14`, while cutting the two rows apart gives `5 · 10 = 50`: the inequality is strict
here, and the gap `50 − 14 = 36` is the square of the inner product `6` of the two rows. -/
example : ((Matrix.of ![![1, 0, 2], ![0, 1, 3]] : Matrix (Fin 2) (Fin 3) ℚ) *
      (Matrix.of ![![1, 0, 2], ![0, 1, 3]] : Matrix (Fin 2) (Fin 3) ℚ)ᵀ).det
    ≤ ∏ i, (Matrix.of ![![1, 0, 2], ![0, 1, 3]] : Matrix (Fin 2) (Fin 3) ℚ).row i ⬝ᵥ
        (Matrix.of ![![1, 0, 2], ![0, 1, 3]] : Matrix (Fin 2) (Fin 3) ℚ).row i :=
  Matrix.det_mul_transpose_self_le_prod _

/-- **Rejection test: the inequality goes one way only.** Orthogonal rows make it an equality, so no
reverse inequality with a constant better than `1` is available; and the example above is strict, so
it is not an identity either. -/
example : ((Matrix.of ![![1, 0], ![0, 1]] : Matrix (Fin 2) (Fin 2) ℚ) *
      (Matrix.of ![![1, 0], ![0, 1]] : Matrix (Fin 2) (Fin 2) ℚ)ᵀ).det = 1 ∧
    ((Matrix.of ![![1, 0, 2], ![0, 1, 3]] : Matrix (Fin 2) (Fin 3) ℚ) *
      (Matrix.of ![![1, 0, 2], ![0, 1, 3]] : Matrix (Fin 2) (Fin 3) ℚ)ᵀ).det ≠
    ∏ i, (Matrix.of ![![1, 0, 2], ![0, 1, 3]] : Matrix (Fin 2) (Fin 3) ℚ).row i ⬝ᵥ
        (Matrix.of ![![1, 0, 2], ![0, 1, 3]] : Matrix (Fin 2) (Fin 3) ℚ).row i := by
  constructor
  · rw [Matrix.det_fin_two]
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
  · rw [Matrix.det_fin_two]
    norm_num [Matrix.mul_apply, dotProduct, Fin.sum_univ_succ, Fin.prod_univ_succ]

/-- **Conformance.** The two statements of the milestone's second half: the two-block inequality and
its fully split consequence. -/
example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {ι : Type*} [Fintype ι]
    [LinearOrder ι] {p q m : ℕ} (A : Matrix (Fin p) ι K) (B : Matrix (Fin q) ι K)
    (C : Matrix (Fin m) ι K) :
    ((Matrix.fromRows A B) * (Matrix.fromRows A B)ᵀ).det ≤ (A * Aᵀ).det * (B * Bᵀ).det ∧
      (C * Cᵀ).det ≤ ∏ i, C.row i ⬝ᵥ C.row i :=
  ⟨Matrix.det_mul_transpose_self_fromRows_le A B, Matrix.det_mul_transpose_self_le_prod C⟩

end Examples

end
