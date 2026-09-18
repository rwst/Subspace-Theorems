/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.Duality
public import ArithmeticHeights.Hadamard
public import ArithmeticHeights.Nonarchimedean

-- Used only inside proofs: the finiteness of a pointwise product's multiplicative support and the
-- restriction of a supremum to the nonzero coordinates.
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Order.Hom.Lattice

/-!
# Submodularity of the height of a subspace

The height of a subspace is submodular on the subspace lattice:
`h_Ar(V + W) + h_Ar(V ∩ W) ≤ h_Ar(V) + h_Ar(W)`. Bombieri–Gubler state this as Theorem 2.8.13
without proof and make no use of it; Schmidt's Lemma 8A and Struppeck–Vaaler prove it
independently. It is nonetheless the structural theorem about subspace heights, and the two
product bounds `H(V ∩ W) ≤ H(V) · H(W)` and `H(V + W) ≤ H(V) · H(W)` are all that replaces the
monotonicity a height on a lattice does *not* have.

**The milestone is proved.** `Submodule.arakelovMulHeight_sup_mul_arakelovMulHeight_inf_le` is the
inequality itself, with the two product bounds `Submodule.arakelovMulHeight_inf_le_mul` and
`Submodule.arakelovMulHeight_sup_le_mul` and the logarithmic form
`Submodule.arakelovLogHeight_sup_add_arakelovLogHeight_inf_le` beside it. Four things go into it.

**The normalization is part of the statement.** The inequality is about the *Arakelov* height, the
ℓ² norm at the archimedean places, and it is **false** for `Submodule.mulHeight`, the sup-norm
height that Mathlib's `Height.mulHeight` and the rest of this library default to. The lines
`ℚ · (1, 1, 1)` and `ℚ · (1, -1, 0)` in `ℚ³` have sup-norm height `1` each, meet in `0`, and span
a plane of sup-norm height `2`; so `H(V + W) · H(V ∩ W) = 2 > 1 = H(V) · H(W)`, which refutes the
submodularity and the product bound for the sum at once, and — transported through the duality
theorem of Layer 3.5 — the product bound for the intersection as well. All of this is
machine-checked among the worked examples. In the ℓ² normalization the same pair gives an
*equality*: the two rows are orthogonal, and `6 = 3 · 2`.

**The archimedean half is proved here,** as `Matrix.det_mul_transpose_self_fromRows_mul_le` over an
ordered field and `Matrix.det_mul_conjTranspose_self_fromRows_mul_le` over `ℝ` or `ℂ`. Cut the
rows of a matrix into three blocks `A`, `B`, `C`: then

`det (M Mᵀ) · det (A Aᵀ) ≤ det ((A;B) (A;B)ᵀ) · det ((A;C) (A;C)ᵀ)`,

which is **Koteljanskii's inequality** for the Gram matrix — the submodular generalization of the
Fischer inequality of Layer 3.4, which is the case of an empty first block. Through Cauchy–Binet
this says that the archimedean local factor `∑ₛ v(pₛ)²` of the tuple of Plücker coordinates is
submodular, which is `NumberField.InfinitePlace.sum_sq_plucker_append_mul_le`.

**The finite half is proved in `ArithmeticHeights/Nonarchimedean.lean`,** as
`NumberField.FinitePlace.iSup_plucker_append_mul_le`: the same inequality for the Gauss norms
`‖p(·)‖ᵥ = maxₛ |det(·)ₛ|ᵥ`. Its proof has nothing in common with the archimedean one — there is no
orthogonal projection at a finite place — and instead normalizes `A` to an integral basis of its
saturated lattice `span A ∩ Oᵥⁿ`, after which `‖p(A)‖ᵥ = 1` and the inequality collapses to
submultiplicativity applied twice. `ArithmeticHeights/Laplace.lean` reaches that
submultiplicativity a second way, through the Grassmann–Plücker comultiplication
`p(B;C) = ∑ ± p(B) ⊗ p(C)` and the ultrametric inequality.

**The reduction is proved:** `Submodule.exists_append_span_eq` produces one triple of families
`u`, `b`, `c` whose four appendings span `V ⊓ W`, `V`, `W` and `V ⊔ W`, so that the four heights of
the milestone are the heights of four Plücker vectors built from the *same* three families — the
only way a place-by-place comparison of them can get started. The comparison itself is
`NumberField.arakelovMulHeight_mul_le_of_forall_le`, which turns a bound at every place into a
bound on the heights.

## Main results

* `Matrix.det_mul_transpose_self_fromRows_mul_le`: **Koteljanskii's inequality** for Gram
  determinants over an ordered field, and
  `Matrix.det_mul_conjTranspose_self_fromRows_mul_le` over `ℝ` or `ℂ`, which is the form an
  infinite place of a number field needs.
* `Matrix.det_mul_conjTranspose_self_fromRows_le`: the **Hermitian generalized Hadamard
  inequality**, the companion of Layer 3.4's `Matrix.det_mul_transpose_self_fromRows_le` at a
  complex place. It is proved here because Layer 3.6 is what first needs it.
* `NumberField.InfinitePlace.sum_sq_plucker_append_mul_le`: the archimedean local factor of the
  height of a subspace is submodular, in the Plücker coordinates of three appended families.
* `Submodule.exists_append_span_eq`: **adapted families** for a pair of subspaces, the reduction
  of the milestone to a statement about four Plücker vectors of one triple of families. With it,
  `Submodule.span_range_append` and `LinearIndependent.append`, which are about `Fin.append` and
  hold over any ring.
* `Submodule.arakelovMulHeight_sup_mul_arakelovMulHeight_inf_le`: **the milestone**, with
  `Submodule.arakelovMulHeight_inf_le_mul`, `Submodule.arakelovMulHeight_sup_le_mul` and
  `Submodule.arakelovLogHeight_sup_add_arakelovLogHeight_inf_le`.
* `NumberField.arakelovMulHeight_mul_le_of_forall_le`: a comparison of local factors at every
  place, archimedean and finite, is a comparison of Arakelov heights. The four tuples may be
  indexed by four different types, which is what the milestone needs.

## Implementation notes

Koteljanskii's inequality is usually derived from Fischer's by way of the Schur complement and the
monotonicity of the determinant on the positive semidefinite order — neither of which is in
Mathlib, as Layer 3.4 already recorded. The route here is the geometric one: project the second
and third blocks orthogonally to the first, which is a row operation of determinant `1`, so it
changes no Gram determinant, and makes the Gram matrix block diagonal. The Gram determinant of the
first block then factors out of all four terms and the inequality is Fischer's for the two
projected blocks. This is the argument `Matrix.det_mul_transpose_self_fromRows_le` already runs
for two blocks, so the file's private splitting lemma is shared with it in spirit and proved once
for an arbitrary second row index, since the second block here is itself a stack.

The Hermitian half is a parallel development rather than a specialization: `ℂ` is not an ordered
field, and `Matrix.det_mul_transpose_self_eq_sum_sq` becomes
`Matrix.det_mul_conjTranspose_self_eq_sum`, a sum of `p * star p`. The order comes from
`open scoped ComplexOrder`, whose `RCLike.toIsStrictOrderedRing` makes every step of the ordered
proof available verbatim; the four Gram determinants in the statement are real and nonnegative,
so the inequality in `K` says exactly what the inequality in `ℝ` would.

`Fin.append` rather than `Matrix.fromRows` is what the Plücker coordinates need, since
`exteriorPower.plucker` indexes a family by `Fin k`; the two are the same stack up to
`finSumFinEquiv`, which the Gram determinant does not see, and the conversion is the only index
bookkeeping in the file.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Theorem 2.8.13, and Remark 2.8.9 for the Fischer inequality it generalizes. W. M. Schmidt,
*Diophantine Approximation*, LNM 785, Ch. I, Lemma 8A. T. Struppeck and J. D. Vaaler,
"Inequalities for heights of algebraic subspaces and the Thue–Siegel principle", in *Analytic
Number Theory* (Allerton Park, 1989), Birkhäuser (1990). D. M. Koteljanskii, "A property of
sign-symmetric matrices", *Uspekhi Mat. Nauk* **8** (1953), 163–167, for the determinant
inequality.

This is Layer 3.6 of the `ArithmeticHeights` roadmap, the submodularity that Layer 3.5's duality
and Layer 3.4's Fischer inequality make possible; its finite-place half is
`ArithmeticHeights/Nonarchimedean.lean` and the second route to that half is
`ArithmeticHeights/Laplace.lean`.
-/

public section

namespace Matrix

open Module exteriorPower

/-!
### Splitting off a block of rows
-/

section Gram

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {p : ℕ}

omit [Fintype ι] in
private theorem fromRows_sub {m₁ m₂ : Type*} (A₁ B₁ : Matrix m₁ ι R) (A₂ B₂ : Matrix m₂ ι R) :
    fromRows A₁ A₂ - fromRows B₁ B₂ = fromRows (A₁ - B₁) (A₂ - B₂) := by
  ext (i | i) j <;> simp

/-- **Splitting off a block of rows orthogonal to the rest.** If `D'` differs from `D` by a
multiple of `A` and is orthogonal to `A`, the Gram determinant of `A` stacked on `D` factors: the
passage from `D` to `D'` is a row operation of determinant `1`, and the Gram matrix of `A` stacked
on `D'` is block diagonal. -/
private theorem det_gram_fromRows_eq {A : Matrix (Fin p) ι R} {ρ : Type*} [Fintype ρ]
    [DecidableEq ρ] {D D' : Matrix ρ ι R} {X : Matrix ρ (Fin p) R} (hD' : D' = D - X * A)
    (hD'A : D' * Aᵀ = 0) :
    ((fromRows A D) * (fromRows A D)ᵀ).det = (A * Aᵀ).det * (D' * D'ᵀ).det := by
  have hAD' : A * D'ᵀ = 0 := by
    have h := congrArg Matrix.transpose hD'A
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] at h
  have hUdet : (fromBlocks (1 : Matrix (Fin p) (Fin p) R) 0 (-X) 1).det = 1 := by
    rw [Matrix.det_fromBlocks_zero₁₂]
    simp
  have hUM : (fromBlocks (1 : Matrix (Fin p) (Fin p) R) 0 (-X) 1) * fromRows A D
      = fromRows A D' := by
    rw [Matrix.fromBlocks_mul_fromRows, Matrix.one_mul, Matrix.zero_mul, add_zero,
      Matrix.one_mul, Matrix.neg_mul, hD']
    congr 1
    abel
  have key : ((fromRows A D') * (fromRows A D')ᵀ).det = (A * Aᵀ).det * (D' * D'ᵀ).det := by
    rw [Matrix.transpose_fromRows, Matrix.fromRows_mul_fromCols, hAD',
      Matrix.det_fromBlocks_zero₁₂]
  rw [← key, ← hUM, Matrix.transpose_mul, ← Matrix.mul_assoc,
    Matrix.mul_assoc _ (fromRows A D) _, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    hUdet, one_mul, mul_one]

end Gram

/-!
### Koteljanskii's inequality
-/

section Nonneg

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- `Matrix.det_mul_transpose_self_nonneg` for an arbitrary finite row index: the Gram determinant
of a matrix over an ordered field is nonnegative. Reindexing the rows by an equivalence conjugates
the Gram matrix, so its determinant does not change. -/
private theorem det_mul_transpose_self_nonneg' {ρ : Type*} [Fintype ρ] [DecidableEq ρ]
    (M : Matrix ρ ι K) : 0 ≤ (M * Mᵀ).det := by
  classical
  let e : ρ ≃ Fin (Fintype.card ρ) := Fintype.equivFin ρ
  have hre : ((M.submatrix e.symm id) * (M.submatrix e.symm id)ᵀ)
      = (M * Mᵀ).submatrix e.symm e.symm := by
    ext i j
    simp [Matrix.mul_apply]
  have h := det_mul_transpose_self_nonneg (M.submatrix e.symm id)
  rwa [hre, Matrix.det_submatrix_equiv_self] at h

end Nonneg

section Koteljanskii

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {p q r : ℕ}

/-- **Koteljanskii's inequality for Gram determinants** — the archimedean local form of the
submodularity of the height of a subspace. Cut the rows of a matrix into three blocks: the Gram
determinant of all three blocks, times the Gram determinant of the first, is at most the product
of the Gram determinants of the first block taken with each of the other two.

With an empty first block this is the generalized Hadamard inequality
`Matrix.det_mul_transpose_self_fromRows_le`, which is what the proof reduces it to, after
projecting the second and third blocks orthogonally to the first. -/
theorem det_mul_transpose_self_fromRows_mul_le (A : Matrix (Fin p) ι K) (B : Matrix (Fin q) ι K)
    (C : Matrix (Fin r) ι K) :
    ((fromRows A (fromRows B C)) * (fromRows A (fromRows B C))ᵀ).det * (A * Aᵀ).det ≤
      ((fromRows A B) * (fromRows A B)ᵀ).det * ((fromRows A C) * (fromRows A C)ᵀ).det := by
  rcases eq_or_ne (A * Aᵀ).det 0 with hA | hA
  · rw [hA, mul_zero]
    exact mul_nonneg (det_mul_transpose_self_nonneg' _) (det_mul_transpose_self_nonneg' _)
  have hAu : IsUnit (A * Aᵀ).det := isUnit_iff_ne_zero.2 hA
  -- The orthogonal projections of the second and third blocks onto the row space of the first.
  have hproj : ∀ {s : ℕ} (D : Matrix (Fin s) ι K),
      (D - D * Aᵀ * (A * Aᵀ)⁻¹ * A) * Aᵀ = 0 := fun D ↦ by
    rw [Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAu,
      Matrix.mul_one, sub_self]
  have hsub : fromRows (B - B * Aᵀ * (A * Aᵀ)⁻¹ * A) (C - C * Aᵀ * (A * Aᵀ)⁻¹ * A)
      = fromRows B C - fromRows (B * Aᵀ * (A * Aᵀ)⁻¹) (C * Aᵀ * (A * Aᵀ)⁻¹) * A := by
    rw [Matrix.fromRows_mul, fromRows_sub]
  have hperp : (fromRows (B - B * Aᵀ * (A * Aᵀ)⁻¹ * A) (C - C * Aᵀ * (A * Aᵀ)⁻¹ * A)) * Aᵀ = 0 := by
    rw [Matrix.fromRows_mul, hproj B, hproj C, Matrix.fromRows_zero]
  have h1 := det_gram_fromRows_eq (A := A) (D := B) rfl (hproj B)
  have h2 := det_gram_fromRows_eq (A := A) (D := C) rfl (hproj C)
  have h3 := det_gram_fromRows_eq (A := A) (D := fromRows B C) hsub hperp
  have h4 := det_mul_transpose_self_fromRows_le (B - B * Aᵀ * (A * Aᵀ)⁻¹ * A)
    (C - C * Aᵀ * (A * Aᵀ)⁻¹ * A)
  have hnn : 0 ≤ (A * Aᵀ).det * (A * Aᵀ).det := mul_self_nonneg _
  rw [h1, h2, h3]
  calc (A * Aᵀ).det *
        ((fromRows (B - B * Aᵀ * (A * Aᵀ)⁻¹ * A) (C - C * Aᵀ * (A * Aᵀ)⁻¹ * A)) *
          (fromRows (B - B * Aᵀ * (A * Aᵀ)⁻¹ * A) (C - C * Aᵀ * (A * Aᵀ)⁻¹ * A))ᵀ).det *
          (A * Aᵀ).det
      = (A * Aᵀ).det * (A * Aᵀ).det *
          ((fromRows (B - B * Aᵀ * (A * Aᵀ)⁻¹ * A) (C - C * Aᵀ * (A * Aᵀ)⁻¹ * A)) *
            (fromRows (B - B * Aᵀ * (A * Aᵀ)⁻¹ * A) (C - C * Aᵀ * (A * Aᵀ)⁻¹ * A))ᵀ).det := by
        ring
    _ ≤ (A * Aᵀ).det * (A * Aᵀ).det *
          (((B - B * Aᵀ * (A * Aᵀ)⁻¹ * A) * (B - B * Aᵀ * (A * Aᵀ)⁻¹ * A)ᵀ).det *
            ((C - C * Aᵀ * (A * Aᵀ)⁻¹ * A) * (C - C * Aᵀ * (A * Aᵀ)⁻¹ * A)ᵀ).det) :=
        mul_le_mul_of_nonneg_left h4 hnn
    _ = (A * Aᵀ).det * ((B - B * Aᵀ * (A * Aᵀ)⁻¹ * A) * (B - B * Aᵀ * (A * Aᵀ)⁻¹ * A)ᵀ).det *
          ((A * Aᵀ).det * ((C - C * Aᵀ * (A * Aᵀ)⁻¹ * A) *
            (C - C * Aᵀ * (A * Aᵀ)⁻¹ * A)ᵀ).det) := by ring

end Koteljanskii

/-!
### The Hermitian companion, for a complex place
-/

section Hermitian

open scoped ComplexOrder

variable {R : Type*} [CommRing R] [StarRing R] {ι : Type*} [Fintype ι] [LinearOrder ι] {p : ℕ}

omit [LinearOrder ι] in
/-- The Hermitian form of the splitting lemma above. -/
private theorem det_gram_conjTranspose_fromRows_eq {A : Matrix (Fin p) ι R} {ρ : Type*}
    [Fintype ρ] [DecidableEq ρ] {D D' : Matrix ρ ι R} {X : Matrix ρ (Fin p) R}
    (hD' : D' = D - X * A) (hD'A : D' * Aᴴ = 0) :
    ((fromRows A D) * (fromRows A D)ᴴ).det = (A * Aᴴ).det * (D' * D'ᴴ).det := by
  have hAD' : A * D'ᴴ = 0 := by
    have h := congrArg Matrix.conjTranspose hD'A
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] at h
  have hUdet : (fromBlocks (1 : Matrix (Fin p) (Fin p) R) 0 (-X) 1).det = 1 := by
    rw [Matrix.det_fromBlocks_zero₁₂]
    simp
  have hUM : (fromBlocks (1 : Matrix (Fin p) (Fin p) R) 0 (-X) 1) * fromRows A D
      = fromRows A D' := by
    rw [Matrix.fromBlocks_mul_fromRows, Matrix.one_mul, Matrix.zero_mul, add_zero,
      Matrix.one_mul, Matrix.neg_mul, hD']
    congr 1
    abel
  have key : ((fromRows A D') * (fromRows A D')ᴴ).det = (A * Aᴴ).det * (D' * D'ᴴ).det := by
    rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromRows_mul_fromCols,
      hAD', Matrix.det_fromBlocks_zero₁₂]
  rw [← key, ← hUM, Matrix.conjTranspose_mul, ← Matrix.mul_assoc,
    Matrix.mul_assoc _ (fromRows A D) _, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_conjTranspose, hUdet, one_mul, star_one, mul_one]

variable {K : Type*} [RCLike K] {q r : ℕ}

/-- The Gram determinant of a matrix over `ℝ` or `ℂ`, paired against its conjugate transpose, is
nonnegative — for an arbitrary finite row index, since the blocks below are stacked. -/
private theorem det_mul_conjTranspose_self_nonneg' {ρ : Type*} [Fintype ρ] [DecidableEq ρ]
    (M : Matrix ρ ι K) : 0 ≤ (M * Mᴴ).det := by
  classical
  let e : ρ ≃ Fin (Fintype.card ρ) := Fintype.equivFin ρ
  have hre : ((M.submatrix e.symm id) * (M.submatrix e.symm id)ᴴ)
      = (M * Mᴴ).submatrix e.symm e.symm := by
    ext i j
    simp [Matrix.mul_apply]
  have h : 0 ≤ ((M.submatrix e.symm id) * (M.submatrix e.symm id)ᴴ).det := by
    rw [det_mul_conjTranspose_self_eq_sum]
    exact Finset.sum_nonneg fun s _ ↦ mul_star_self_nonneg _
  rwa [hre, Matrix.det_submatrix_equiv_self] at h

/-- **Deleting columns does not increase the Gram determinant**, at a complex place: the Hermitian
form of `Matrix.det_mul_transpose_self_submatrix_le`. -/
private theorem det_mul_conjTranspose_self_submatrix_le {κ : Type*} [Fintype κ] [LinearOrder κ]
    (B : Matrix (Fin q) κ K) (f : ι ↪o κ) :
    ((B.submatrix id f) * (B.submatrix id f)ᴴ).det ≤ (B * Bᴴ).det := by
  classical
  rw [det_mul_conjTranspose_self_eq_sum, det_mul_conjTranspose_self_eq_sum]
  set F : Set.powersetCard ι q → Set.powersetCard κ q := fun s ↦
    ⟨(s : Finset ι).map f.toEmbedding, Set.powersetCard.mem_iff.2 (by
      simp [Set.powersetCard.card_eq s])⟩ with hFdef
  have hF : Function.Injective F := fun s t h ↦
    Subtype.ext (Finset.map_injective _ (congrArg Subtype.val h))
  calc ∑ s : Set.powersetCard ι q, plucker q (B.submatrix id f).row s *
        star (plucker q (B.submatrix id f).row s)
      = ∑ s : Set.powersetCard ι q, plucker q B.row (F s) * star (plucker q B.row (F s)) :=
        Finset.sum_congr rfl fun s _ ↦ by rw [plucker_row_submatrix]
    _ = ∑ t ∈ Finset.image F Finset.univ, plucker q B.row t * star (plucker q B.row t) :=
        (Finset.sum_image (f := fun t ↦ plucker q B.row t * star (plucker q B.row t))
          fun x _ y _ h ↦ hF h).symm
    _ ≤ ∑ t : Set.powersetCard κ q, plucker q B.row t * star (plucker q B.row t) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun _ _ _ ↦ mul_star_self_nonneg _

/-- Adding a Gram matrix to a Gram matrix does not decrease the determinant, at a complex place:
the Hermitian form of `Matrix.det_mul_transpose_self_le_det_add`. -/
private theorem det_mul_conjTranspose_self_le_det_add (V W : Matrix (Fin q) ι K) :
    (V * Vᴴ).det ≤ (V * Vᴴ + W * Wᴴ).det := by
  set B : Matrix (Fin q) (ι ⊕ₗ ι) K := Matrix.of fun i j ↦ Sum.elim (V i) (W i) (ofLex j) with hB
  have h1 : B.submatrix id (OrderEmbedding.ofStrictMono (⇑toLex ∘ Sum.inl)
      Sum.Lex.inl_strictMono) = V := rfl
  have h2 : B * Bᴴ = V * Vᴴ + W * Wᴴ := by
    ext i j
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply,
      show (∑ c : ι ⊕ₗ ι, B i c * Bᴴ c j) = ∑ c : ι ⊕ ι, B i (toLex c) * Bᴴ (toLex c) j from
        Fintype.sum_equiv (toLex (α := ι ⊕ ι)) _ _ fun c ↦ rfl, Fintype.sum_sum_type]
    rfl
  have h := det_mul_conjTranspose_self_submatrix_le B
    (OrderEmbedding.ofStrictMono (⇑toLex ∘ Sum.inl) Sum.Lex.inl_strictMono)
  rwa [h1, h2] at h

/-- **The generalized Hadamard inequality at a complex place**: the Hermitian form of
`Matrix.det_mul_transpose_self_fromRows_le`. -/
theorem det_mul_conjTranspose_self_fromRows_le (A : Matrix (Fin p) ι K)
    (B : Matrix (Fin q) ι K) :
    ((fromRows A B) * (fromRows A B)ᴴ).det ≤ (A * Aᴴ).det * (B * Bᴴ).det := by
  rcases eq_or_ne (A * Aᴴ).det 0 with hA | hA
  · rw [hA, zero_mul]
    refine le_of_eq ?_
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hA
    have hx : (c ᵥ* A) ᵥ* Aᴴ = 0 := by rw [Matrix.vecMul_vecMul]; exact hc
    have h2 : (c ᵥ* A) ⬝ᵥ star (c ᵥ* A) = 0 := by
      rw [Matrix.star_vecMul, Matrix.dotProduct_mulVec, hx, zero_dotProduct]
    have hcA : c ᵥ* A = 0 := dotProduct_self_star_eq_zero.1 h2
    refine Matrix.exists_vecMul_eq_zero_iff.1 ⟨Sum.elim c 0, ?_, ?_⟩
    · exact fun h ↦ hc0 (funext fun i ↦ congrFun h (Sum.inl i))
    · rw [← Matrix.vecMul_vecMul, Matrix.vecMul_fromRows]
      simp [hcA]
  · have hAu : IsUnit (A * Aᴴ).det := isUnit_iff_ne_zero.2 hA
    have hXA : B * Aᴴ * (A * Aᴴ)⁻¹ * (A * Aᴴ) = B * Aᴴ := by
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAu, Matrix.mul_one]
    have hB'A : (B - B * Aᴴ * (A * Aᴴ)⁻¹ * A) * Aᴴ = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, hXA, sub_self]
    have hsplit : B * Bᴴ = (B - B * Aᴴ * (A * Aᴴ)⁻¹ * A) * (B - B * Aᴴ * (A * Aᴴ)⁻¹ * A)ᴴ +
        (B * Aᴴ * (A * Aᴴ)⁻¹ * A) * (B * Aᴴ * (A * Aᴴ)⁻¹ * A)ᴴ := by
      have hY1 : (B - B * Aᴴ * (A * Aᴴ)⁻¹ * A) * (B * Aᴴ * (A * Aᴴ)⁻¹ * A)ᴴ = 0 := by
        rw [Matrix.conjTranspose_mul, ← Matrix.mul_assoc, hB'A, Matrix.zero_mul]
      have hY2 : (B * Aᴴ * (A * Aᴴ)⁻¹ * A) * (B - B * Aᴴ * (A * Aᴴ)⁻¹ * A)ᴴ = 0 := by
        have h := congrArg Matrix.conjTranspose hY1
        rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.conjTranspose_zero] at h
      conv_lhs => rw [show B = (B - B * Aᴴ * (A * Aᴴ)⁻¹ * A) + B * Aᴴ * (A * Aᴴ)⁻¹ * A by abel]
      rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hY1, hY2]
      abel
    calc ((fromRows A B) * (fromRows A B)ᴴ).det
        = (A * Aᴴ).det * ((B - B * Aᴴ * (A * Aᴴ)⁻¹ * A) *
            (B - B * Aᴴ * (A * Aᴴ)⁻¹ * A)ᴴ).det :=
          det_gram_conjTranspose_fromRows_eq rfl hB'A
      _ ≤ (A * Aᴴ).det * (B * Bᴴ).det := by
          refine mul_le_mul_of_nonneg_left ?_ (det_mul_conjTranspose_self_nonneg' A)
          rw [hsplit]
          exact det_mul_conjTranspose_self_le_det_add _ _

/-- **Koteljanskii's inequality at a complex place**: the Hermitian form of
`Matrix.det_mul_transpose_self_fromRows_mul_le`. -/
theorem det_mul_conjTranspose_self_fromRows_mul_le (A : Matrix (Fin p) ι K)
    (B : Matrix (Fin q) ι K) (C : Matrix (Fin r) ι K) :
    ((fromRows A (fromRows B C)) * (fromRows A (fromRows B C))ᴴ).det * (A * Aᴴ).det ≤
      ((fromRows A B) * (fromRows A B)ᴴ).det * ((fromRows A C) * (fromRows A C)ᴴ).det := by
  rcases eq_or_ne (A * Aᴴ).det 0 with hA | hA
  · rw [hA, mul_zero]
    exact mul_nonneg (det_mul_conjTranspose_self_nonneg' _) (det_mul_conjTranspose_self_nonneg' _)
  have hAu : IsUnit (A * Aᴴ).det := isUnit_iff_ne_zero.2 hA
  have hproj : ∀ {s : ℕ} (D : Matrix (Fin s) ι K),
      (D - D * Aᴴ * (A * Aᴴ)⁻¹ * A) * Aᴴ = 0 := fun D ↦ by
    rw [Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAu,
      Matrix.mul_one, sub_self]
  have hsub : fromRows (B - B * Aᴴ * (A * Aᴴ)⁻¹ * A) (C - C * Aᴴ * (A * Aᴴ)⁻¹ * A)
      = fromRows B C - fromRows (B * Aᴴ * (A * Aᴴ)⁻¹) (C * Aᴴ * (A * Aᴴ)⁻¹) * A := by
    rw [Matrix.fromRows_mul, fromRows_sub]
  have hperp : (fromRows (B - B * Aᴴ * (A * Aᴴ)⁻¹ * A) (C - C * Aᴴ * (A * Aᴴ)⁻¹ * A)) * Aᴴ = 0 := by
    rw [Matrix.fromRows_mul, hproj B, hproj C, Matrix.fromRows_zero]
  have h1 := det_gram_conjTranspose_fromRows_eq (A := A) (D := B) rfl (hproj B)
  have h2 := det_gram_conjTranspose_fromRows_eq (A := A) (D := C) rfl (hproj C)
  have h3 := det_gram_conjTranspose_fromRows_eq (A := A) (D := fromRows B C) hsub hperp
  have h4 := det_mul_conjTranspose_self_fromRows_le (B - B * Aᴴ * (A * Aᴴ)⁻¹ * A)
    (C - C * Aᴴ * (A * Aᴴ)⁻¹ * A)
  have hnn : 0 ≤ (A * Aᴴ).det * (A * Aᴴ).det :=
    mul_nonneg (det_mul_conjTranspose_self_nonneg' A) (det_mul_conjTranspose_self_nonneg' A)
  rw [h1, h2, h3]
  calc (A * Aᴴ).det *
        ((fromRows (B - B * Aᴴ * (A * Aᴴ)⁻¹ * A) (C - C * Aᴴ * (A * Aᴴ)⁻¹ * A)) *
          (fromRows (B - B * Aᴴ * (A * Aᴴ)⁻¹ * A) (C - C * Aᴴ * (A * Aᴴ)⁻¹ * A))ᴴ).det *
          (A * Aᴴ).det
      = (A * Aᴴ).det * (A * Aᴴ).det *
          ((fromRows (B - B * Aᴴ * (A * Aᴴ)⁻¹ * A) (C - C * Aᴴ * (A * Aᴴ)⁻¹ * A)) *
            (fromRows (B - B * Aᴴ * (A * Aᴴ)⁻¹ * A) (C - C * Aᴴ * (A * Aᴴ)⁻¹ * A))ᴴ).det := by
        ring
    _ ≤ (A * Aᴴ).det * (A * Aᴴ).det *
          (((B - B * Aᴴ * (A * Aᴴ)⁻¹ * A) * (B - B * Aᴴ * (A * Aᴴ)⁻¹ * A)ᴴ).det *
            ((C - C * Aᴴ * (A * Aᴴ)⁻¹ * A) * (C - C * Aᴴ * (A * Aᴴ)⁻¹ * A)ᴴ).det) :=
        mul_le_mul_of_nonneg_left h4 hnn
    _ = (A * Aᴴ).det * ((B - B * Aᴴ * (A * Aᴴ)⁻¹ * A) * (B - B * Aᴴ * (A * Aᴴ)⁻¹ * A)ᴴ).det *
          ((A * Aᴴ).det * ((C - C * Aᴴ * (A * Aᴴ)⁻¹ * A) *
            (C - C * Aᴴ * (A * Aᴴ)⁻¹ * A)ᴴ).det) := by ring

end Hermitian

end Matrix

/-!
### Adapted families for a pair of subspaces
-/

section Adapted

private theorem Fin.append_eq_elim_comp {M : Type*} {k m : ℕ} (u : Fin k → M) (b : Fin m → M) :
    Fin.append u b = Sum.elim u b ∘ finSumFinEquiv.symm := by
  funext i
  induction i using Fin.addCases with
  | left i => simp
  | right i => simp

/-- The span of two families appended is the sum of their spans. -/
theorem Submodule.span_range_append {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {k m : ℕ} (u : Fin k → M) (b : Fin m → M) :
    Submodule.span R (Set.range (Fin.append u b))
      = Submodule.span R (Set.range u) ⊔ Submodule.span R (Set.range b) := by
  rw [Fin.append_eq_elim_comp, Set.range_comp, Equiv.range_eq_univ, Set.image_univ,
    Set.Sum.elim_range, Submodule.span_union]

/-- Two linearly independent families with disjoint spans stay independent when appended. -/
theorem LinearIndependent.append {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {k m : ℕ}
    {u : Fin k → M} {b : Fin m → M} (hu : LinearIndependent R u) (hb : LinearIndependent R b)
    (h : Disjoint (Submodule.span R (Set.range u)) (Submodule.span R (Set.range b))) :
    LinearIndependent R (Fin.append u b) := by
  rw [Fin.append_eq_elim_comp]
  exact (hu.sum_type hb h).comp _ finSumFinEquiv.symm.injective

namespace Submodule

variable {K : Type*} [Field K] {ι : Type*} [Finite ι]

/-- **Adapted families for a pair of subspaces.** Given `V` and `W`, there are three linearly
independent families — `u` spanning `V ⊓ W`, and `b`, `c` extending it to `V` and to `W` — whose
four appendings are linearly independent and span the four subspaces of the milestone:
`V ⊓ W`, `V`, `W` and `V ⊔ W`.

This is the reduction the submodularity of the height runs through: with
`Submodule.mulHeight_span_range` and its Arakelov and absolute companions, the four heights of the
milestone become the heights of the four Plücker vectors `plucker k u`,
`plucker (k + m) (Fin.append u b)`, `plucker (k + n) (Fin.append u c)` and
`plucker (k + (m + n)) (Fin.append u (Fin.append b c))` — four tuples built from *one* triple of
families, which is what makes a place-by-place comparison of them possible at all, and the shape
`NumberField.InfinitePlace.sum_sq_plucker_append_mul_le` above is stated in.

The construction is lattice-theoretic: a complement `C` of `V ⊓ W` in the whole space cuts `V` and
`W` into `V ⊓ W` and the pieces `C ⊓ V`, `C ⊓ W`, which are independent because they lie in `C`.
The modular law is what makes `(V ⊓ W) ⊔ (C ⊓ V) = V`. -/
theorem exists_append_span_eq (V W : Submodule K (ι → K)) :
    ∃ (k m n : ℕ) (u : Fin k → (ι → K)) (b : Fin m → (ι → K)) (c : Fin n → (ι → K)),
      LinearIndependent K u ∧ LinearIndependent K (Fin.append u b) ∧
        LinearIndependent K (Fin.append u c) ∧
        LinearIndependent K (Fin.append u (Fin.append b c)) ∧
        span K (Set.range u) = V ⊓ W ∧ span K (Set.range (Fin.append u b)) = V ∧
        span K (Set.range (Fin.append u c)) = W ∧
        span K (Set.range (Fin.append u (Fin.append b c))) = V ⊔ W := by
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨C, hC⟩ := (V ⊓ W).exists_isCompl
  -- The two pieces cut off by the complement, and the lattice identities they satisfy.
  have hV : (V ⊓ W) ⊔ (C ⊓ V) = V := by
    rw [← sup_inf_assoc_of_le C (inf_le_left : V ⊓ W ≤ V), hC.sup_eq_top, top_inf_eq]
  have hW : (V ⊓ W) ⊔ (C ⊓ W) = W := by
    rw [← sup_inf_assoc_of_le C (inf_le_right : V ⊓ W ≤ W), hC.sup_eq_top, top_inf_eq]
  have hdV : Disjoint (V ⊓ W) (C ⊓ V) := hC.disjoint.mono_right inf_le_left
  have hdW : Disjoint (V ⊓ W) (C ⊓ W) := hC.disjoint.mono_right inf_le_left
  have hdVW : Disjoint (C ⊓ V) (C ⊓ W) := by
    refine disjoint_iff.2 (le_bot_iff.1 ?_)
    calc (C ⊓ V) ⊓ (C ⊓ W)
        ≤ (V ⊓ W) ⊓ C :=
          le_inf (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))
            (inf_le_left.trans inf_le_left)
      _ ≤ ⊥ := hC.disjoint.le_bot
  have hdsup : Disjoint (V ⊓ W) ((C ⊓ V) ⊔ (C ⊓ W)) :=
    hC.disjoint.mono_right (sup_le inf_le_left inf_le_left)
  -- Bases of the three pieces.
  set bU := Module.finBasis K (V ⊓ W : Submodule K (ι → K)) with hbU
  set bV := Module.finBasis K (C ⊓ V : Submodule K (ι → K)) with hbV
  set bW := Module.finBasis K (C ⊓ W : Submodule K (ι → K)) with hbW
  have hu : LinearIndependent K fun i ↦ ((bU i : ι → K)) := linearIndependent_coe_basis bU
  have hb : LinearIndependent K fun i ↦ ((bV i : ι → K)) := linearIndependent_coe_basis bV
  have hc : LinearIndependent K fun i ↦ ((bW i : ι → K)) := linearIndependent_coe_basis bW
  have hsu : span K (Set.range fun i ↦ ((bU i : ι → K))) = V ⊓ W := span_range_coe_basis bU
  have hsb : span K (Set.range fun i ↦ ((bV i : ι → K))) = C ⊓ V := span_range_coe_basis bV
  have hsc : span K (Set.range fun i ↦ ((bW i : ι → K))) = C ⊓ W := span_range_coe_basis bW
  have hbc : LinearIndependent K (Fin.append (fun i ↦ ((bV i : ι → K)))
      fun i ↦ ((bW i : ι → K))) := hb.append hc (by rw [hsb, hsc]; exact hdVW)
  have hsbc : span K (Set.range (Fin.append (fun i ↦ ((bV i : ι → K)))
      fun i ↦ ((bW i : ι → K)))) = (C ⊓ V) ⊔ (C ⊓ W) := by
    rw [span_range_append, hsb, hsc]
  refine ⟨_, _, _, _, _, _, hu, hu.append hb (by rw [hsu, hsb]; exact hdV),
    hu.append hc (by rw [hsu, hsc]; exact hdW),
    hu.append hbc (by rw [hsu, hsbc]; exact hdsup), hsu, ?_, ?_, ?_⟩
  · rw [span_range_append, hsu, hsb, hV]
  · rw [span_range_append, hsu, hsc, hW]
  · rw [span_range_append, hsu, hsbc, sup_sup_distrib_left, hV, hW]

end Submodule

end Adapted


namespace NumberField.InfinitePlace

open Matrix exteriorPower

open scoped ComplexOrder

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [LinearOrder ι] {p q r : ℕ}

omit [LinearOrder ι] in
/-- Reindexing the rows by an equivalence conjugates the Gram matrix, so it leaves the Gram
determinant alone. This is what makes `Fin.append` and `Matrix.fromRows` interchangeable below. -/
private theorem det_gram_eq_of_rowEquiv {S : Type*} [CommRing S] [StarRing S] {ρ ρ' : Type*}
    [Fintype ρ] [DecidableEq ρ] [Fintype ρ'] [DecidableEq ρ'] (M : Matrix ρ ι S)
    (N : Matrix ρ' ι S) (e : ρ' ≃ ρ) (h : ∀ i, N i = M (e i)) :
    (N * Nᴴ).det = (M * Mᴴ).det := by
  have hN : N = M.submatrix e id := by
    ext i j
    rw [h i]
    rfl
  have hG : (M.submatrix e id) * (M.submatrix e id)ᴴ = (M * Mᴴ).submatrix e e := by
    ext i j
    simp [Matrix.mul_apply]
  rw [hN, hG, Matrix.det_submatrix_equiv_self]

/-- The archimedean local factor of a family of vectors, read as a Gram determinant. -/
private theorem det_map_embedding_gram_append (v : InfinitePlace K) (a : Fin p → (ι → K))
    (b : Fin q → (ι → K)) :
    ((fromRows ((Matrix.of a).map v.embedding) ((Matrix.of b).map v.embedding)) *
        (fromRows ((Matrix.of a).map v.embedding) ((Matrix.of b).map v.embedding))ᴴ).det
      = ((∑ s : Set.powersetCard ι (p + q),
          v (plucker (p + q) (Fin.append a b) s) ^ 2 : ℝ) : ℂ) := by
  refine Eq.trans (det_gram_eq_of_rowEquiv _ _ finSumFinEquiv fun i ↦ ?_)
    (det_map_embedding_mul_conjTranspose_self v (Matrix.of (Fin.append a b)))
  cases i with
  | inl i => funext j; simp
  | inr i => funext j; simp

/-- **The archimedean local factor of the height of a subspace is submodular.** At an infinite
place `v` of a number field, the local factor `∑ₛ v(pₛ)²` of the tuple of Plücker coordinates —
the quantity the ℓ² normalization of Layer 0.1 raises to the power `mult v / 2` — obeys the
inequality of the milestone for three families of vectors stacked in the three ways that matter:
all three, the first, the first with the second, the first with the third.

This is Koteljanskii's inequality, transported to an infinite place through Cauchy–Binet: at a
real place the conjugate transpose is the transpose, so the statement covers both kinds of place.
It is the archimedean half of the submodularity of the Arakelov height of a subspace; the
finite places are not settled here. -/
theorem sum_sq_plucker_append_mul_le (v : InfinitePlace K) (a : Fin p → (ι → K))
    (b : Fin q → (ι → K)) (c : Fin r → (ι → K)) :
    (∑ s : Set.powersetCard ι (p + (q + r)),
          v (plucker (p + (q + r)) (Fin.append a (Fin.append b c)) s) ^ 2) *
        (∑ s : Set.powersetCard ι p, v (plucker p a s) ^ 2)
      ≤ (∑ s : Set.powersetCard ι (p + q), v (plucker (p + q) (Fin.append a b) s) ^ 2) *
          (∑ s : Set.powersetCard ι (p + r), v (plucker (p + r) (Fin.append a c) s) ^ 2) := by
  have key := Matrix.det_mul_conjTranspose_self_fromRows_mul_le ((Matrix.of a).map v.embedding)
    ((Matrix.of b).map v.embedding) ((Matrix.of c).map v.embedding)
  have hA := det_map_embedding_mul_conjTranspose_self v (Matrix.of a)
  have hAB := det_map_embedding_gram_append v a b
  have hAC := det_map_embedding_gram_append v a c
  have hABC : ((fromRows ((Matrix.of a).map v.embedding)
        (fromRows ((Matrix.of b).map v.embedding) ((Matrix.of c).map v.embedding))) *
      (fromRows ((Matrix.of a).map v.embedding)
        (fromRows ((Matrix.of b).map v.embedding) ((Matrix.of c).map v.embedding)))ᴴ).det
      = ((∑ s : Set.powersetCard ι (p + (q + r)),
          v (plucker (p + (q + r)) (Fin.append a (Fin.append b c)) s) ^ 2 : ℝ) : ℂ) := by
    refine Eq.trans (det_gram_eq_of_rowEquiv _ _
        ((Equiv.sumCongr (Equiv.refl (Fin p)) finSumFinEquiv).trans finSumFinEquiv) fun i ↦ ?_)
      (det_map_embedding_mul_conjTranspose_self v (Matrix.of (Fin.append a (Fin.append b c))))
    cases i with
    | inl i => funext j; simp
    | inr i =>
        cases i with
        | inl i => funext j; simp
        | inr i => funext j; simp
  rw [hABC, hA, hAB, hAC] at key
  exact_mod_cast key

end NumberField.InfinitePlace


/-!
### The milestone

The two halves meet. At an infinite place the local factor is the ℓ² norm of the Plücker vector
and its submodularity is Koteljanskii's inequality, proved above; at a finite place it is the
Gauss norm and its submodularity is proved in `ArithmeticHeights/Nonarchimedean.lean` by
normalizing the common block to an integral basis of its saturated lattice. The Arakelov height is
the product of the local factors over all places, so it is submodular too.
-/

namespace NumberField

open Finset

variable {K : Type*} [Field K] [NumberField K]

/-- The finite places at which the local factor of a nonzero tuple differs from `1` are finitely
many: Mathlib has this one coordinate at a time, and the largest of finitely many coordinates is
`1` wherever all the nonzero ones are. -/
private lemma hasFiniteMulSupport_iSup {κ : Type*} [Finite κ] {x : κ → K} (hx : x ≠ 0) :
    (fun v : FinitePlace K ↦ ⨆ i, v (x i)).HasFiniteMulSupport := by
  have : Nonempty {j // x j ≠ 0} := by
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
    exact ⟨⟨i₀, hi₀⟩⟩
  simp_rw [Finite.iSup_eq_iSup_subtype hx]
  exact Function.HasFiniteMulSupport.iSup fun i ↦ FinitePlace.hasFiniteMulSupport i.prop

private lemma iSup_apply_nonneg {κ : Type*} (v : FinitePlace K) (x : κ → K) :
    0 ≤ ⨆ i, v (x i) :=
  Real.iSup_nonneg_of_nonnegHomClass v x

/-- **A comparison at every place is a comparison of Arakelov heights.** If the archimedean local
factors of `x₁, x₂` are dominated by those of `y₁, y₂` at every infinite place, and the finite
local factors at every finite place, then the same holds for the heights. The four tuples may be
indexed by four different types, which is what the milestone needs: its four Plücker vectors are
indexed by the `k`-element subsets for four different `k`.

This is the Arakelov-height counterpart of the product formula argument, and belongs with the
definition in Layer 0.1; it is stated here because Layer 3.6 is the first consumer. -/
theorem arakelovMulHeight_mul_le_of_forall_le {κ₁ κ₂ κ₃ κ₄ : Type*} [Fintype κ₁] [Fintype κ₂]
    [Fintype κ₃] [Fintype κ₄] {x₁ : κ₁ → K} {x₂ : κ₂ → K} {y₁ : κ₃ → K} {y₂ : κ₄ → K}
    (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0) (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0)
    (harch : ∀ v : InfinitePlace K,
      (∑ i, v (x₁ i) ^ 2) * (∑ i, v (x₂ i) ^ 2) ≤ (∑ i, v (y₁ i) ^ 2) * (∑ i, v (y₂ i) ^ 2))
    (hfin : ∀ v : FinitePlace K,
      (⨆ i, v (x₁ i)) * (⨆ i, v (x₂ i)) ≤ (⨆ i, v (y₁ i)) * (⨆ i, v (y₂ i))) :
    arakelovMulHeight x₁ * arakelovMulHeight x₂
      ≤ arakelovMulHeight y₁ * arakelovMulHeight y₂ := by
  have harchprod : (∏ v : InfinitePlace K, (∑ i, v (x₁ i) ^ 2) ^ (v.mult / 2 : ℝ)) *
      (∏ v : InfinitePlace K, (∑ i, v (x₂ i) ^ 2) ^ (v.mult / 2 : ℝ))
      ≤ (∏ v : InfinitePlace K, (∑ i, v (y₁ i) ^ 2) ^ (v.mult / 2 : ℝ)) *
        (∏ v : InfinitePlace K, (∑ i, v (y₂ i) ^ 2) ^ (v.mult / 2 : ℝ)) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun v _ ↦ by positivity) fun v _ ↦ ?_
    rw [← Real.mul_rpow (by positivity) (by positivity),
      ← Real.mul_rpow (by positivity) (by positivity)]
    exact Real.rpow_le_rpow (by positivity) (harch v) (by positivity)
  have hfinprod : (∏ᶠ v : FinitePlace K, ⨆ i, v (x₁ i)) *
      (∏ᶠ v : FinitePlace K, ⨆ i, v (x₂ i))
      ≤ (∏ᶠ v : FinitePlace K, ⨆ i, v (y₁ i)) * ∏ᶠ v : FinitePlace K, ⨆ i, v (y₂ i) := by
    rw [← finprod_mul_distrib (hasFiniteMulSupport_iSup hx₁) (hasFiniteMulSupport_iSup hx₂),
      ← finprod_mul_distrib (hasFiniteMulSupport_iSup hy₁) (hasFiniteMulSupport_iSup hy₂)]
    exact finprod_le_finprod₀
      (Function.HasFiniteMulSupport.mul (hasFiniteMulSupport_iSup hx₁)
        (hasFiniteMulSupport_iSup hx₂))
      (fun v ↦ mul_nonneg (iSup_apply_nonneg v x₁) (iSup_apply_nonneg v x₂))
      (Function.HasFiniteMulSupport.mul (hasFiniteMulSupport_iSup hy₁)
        (hasFiniteMulSupport_iSup hy₂)) hfin
  rw [arakelovMulHeight_eq hx₁, arakelovMulHeight_eq hx₂, arakelovMulHeight_eq hy₁,
    arakelovMulHeight_eq hy₂]
  calc (∏ v : InfinitePlace K, (∑ i, v (x₁ i) ^ 2) ^ (v.mult / 2 : ℝ)) *
        (∏ᶠ v : FinitePlace K, ⨆ i, v (x₁ i)) *
        ((∏ v : InfinitePlace K, (∑ i, v (x₂ i) ^ 2) ^ (v.mult / 2 : ℝ)) *
          ∏ᶠ v : FinitePlace K, ⨆ i, v (x₂ i))
      = ((∏ v : InfinitePlace K, (∑ i, v (x₁ i) ^ 2) ^ (v.mult / 2 : ℝ)) *
          ∏ v : InfinitePlace K, (∑ i, v (x₂ i) ^ 2) ^ (v.mult / 2 : ℝ)) *
          ((∏ᶠ v : FinitePlace K, ⨆ i, v (x₁ i)) * ∏ᶠ v : FinitePlace K, ⨆ i, v (x₂ i)) := by
        ring
    _ ≤ ((∏ v : InfinitePlace K, (∑ i, v (y₁ i) ^ 2) ^ (v.mult / 2 : ℝ)) *
          ∏ v : InfinitePlace K, (∑ i, v (y₂ i) ^ 2) ^ (v.mult / 2 : ℝ)) *
          ((∏ᶠ v : FinitePlace K, ⨆ i, v (y₁ i)) * ∏ᶠ v : FinitePlace K, ⨆ i, v (y₂ i)) :=
        mul_le_mul harchprod hfinprod
          (mul_nonneg (finprod_nonneg fun v ↦ iSup_apply_nonneg v x₁)
            (finprod_nonneg fun v ↦ iSup_apply_nonneg v x₂))
          (by positivity)
    _ = (∏ v : InfinitePlace K, (∑ i, v (y₁ i) ^ 2) ^ (v.mult / 2 : ℝ)) *
          (∏ᶠ v : FinitePlace K, ⨆ i, v (y₁ i)) *
          ((∏ v : InfinitePlace K, (∑ i, v (y₂ i) ^ 2) ^ (v.mult / 2 : ℝ)) *
            ∏ᶠ v : FinitePlace K, ⨆ i, v (y₂ i)) := by ring

end NumberField

namespace Submodule

open exteriorPower

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- **Submodularity of the height of a subspace** — Bombieri–Gubler, Theorem 2.8.13; Schmidt,
Lemma 8A; Struppeck–Vaaler. In the Arakelov normalization,

`H_Ar(V + W) · H_Ar(V ∩ W) ≤ H_Ar(V) · H_Ar(W)`,

equivalently `h_Ar(V + W) + h_Ar(V ∩ W) ≤ h_Ar(V) + h_Ar(W)` in logarithmic form.

⚠ The statement is **false** for `Submodule.mulHeight`: see the refutation at the end of this
file. Submodularity is a property of the ℓ² normalization. -/
theorem arakelovMulHeight_sup_mul_arakelovMulHeight_inf_le (V W : Submodule K (ι → K)) :
    (V ⊔ W).arakelovMulHeight * (V ⊓ W).arakelovMulHeight
      ≤ V.arakelovMulHeight * W.arakelovMulHeight := by
  obtain ⟨k, m, n, u, b, c, hu, hub, huc, hubc, hsu, hsub, hsuc, hsubc⟩ :=
    Submodule.exists_append_span_eq V W
  rw [← hsubc, ← hsu, ← hsub, ← hsuc, arakelovMulHeight_span_range hu,
    arakelovMulHeight_span_range hub, arakelovMulHeight_span_range huc,
    arakelovMulHeight_span_range hubc]
  exact NumberField.arakelovMulHeight_mul_le_of_forall_le (plucker_ne_zero hubc)
    (plucker_ne_zero hu) (plucker_ne_zero hub) (plucker_ne_zero huc)
    (fun v ↦ NumberField.InfinitePlace.sum_sq_plucker_append_mul_le v u b c)
    (fun v ↦ NumberField.FinitePlace.iSup_plucker_append_mul_le v u b c)

/-- **The product bound for the intersection**, `H_Ar(V ∩ W) ≤ H_Ar(V) · H_Ar(W)`: submodularity
together with `1 ≤ H_Ar`. -/
theorem arakelovMulHeight_inf_le_mul (V W : Submodule K (ι → K)) :
    (V ⊓ W).arakelovMulHeight ≤ V.arakelovMulHeight * W.arakelovMulHeight :=
  le_trans (le_mul_of_one_le_left (arakelovMulHeight_pos _).le
    (one_le_arakelovMulHeight (V ⊔ W))) (arakelovMulHeight_sup_mul_arakelovMulHeight_inf_le V W)

/-- **The product bound for the sum**, `H_Ar(V + W) ≤ H_Ar(V) · H_Ar(W)`. -/
theorem arakelovMulHeight_sup_le_mul (V W : Submodule K (ι → K)) :
    (V ⊔ W).arakelovMulHeight ≤ V.arakelovMulHeight * W.arakelovMulHeight :=
  le_trans (le_mul_of_one_le_right (arakelovMulHeight_pos _).le
    (one_le_arakelovMulHeight (V ⊓ W))) (arakelovMulHeight_sup_mul_arakelovMulHeight_inf_le V W)

/-- The logarithmic form of submodularity: `h_Ar` is a submodular function on the subspace
lattice. -/
theorem arakelovLogHeight_sup_add_arakelovLogHeight_inf_le (V W : Submodule K (ι → K)) :
    (V ⊔ W).arakelovLogHeight + (V ⊓ W).arakelovLogHeight
      ≤ V.arakelovLogHeight + W.arakelovLogHeight := by
  simp only [arakelovLogHeight_eq_log_arakelovMulHeight,
    ← Real.log_mul (arakelovMulHeight_ne_zero _) (arakelovMulHeight_ne_zero _)]
  exact Real.log_le_log (mul_pos (arakelovMulHeight_pos _) (arakelovMulHeight_pos _))
    (arakelovMulHeight_sup_mul_arakelovMulHeight_inf_le V W)

end Submodule

section Examples

open Matrix Submodule exteriorPower

/-- The two lines of the refutation: `ℚ · (1, 1, 1)` and `ℚ · (1, -1, 0)` in `ℚ³`, as the rows of
one matrix. -/
private def refutingMatrix : Matrix (Fin 2) (Fin 3) ℚ := Matrix.of ![![1, 1, 1], ![1, -1, 0]]

private theorem ne_zero_one_one_one : ![(1 : ℚ), 1, 1] ≠ 0 :=
  fun h ↦ by simpa using congrFun h 0

private theorem ne_zero_one_neg_one_zero : ![(1 : ℚ), -1, 0] ≠ 0 :=
  fun h ↦ by simpa using congrFun h 0

private theorem ne_zero_one_one_neg_two : ![(1 : ℚ), 1, -2] ≠ 0 :=
  fun h ↦ by simpa using congrFun h 0

private theorem mulHeight_one_one_one : Height.mulHeight ![(1 : ℚ), 1, 1] = 1 := by
  have hx : ![(1 : ℚ), 1, 1] = ((↑) : ℤ → ℚ) ∘ ![(1 : ℤ), 1, 1] := by
    funext i
    fin_cases i <;> simp
  have hs : (⨆ i, |![(1 : ℤ), 1, 1] i|) = 1 :=
    le_antisymm (ciSup_le fun i ↦ by fin_cases i <;> simp) (Finite.le_ciSup_of_le 0 (by simp))
  rw [hx, Rat.mulHeight_eq_max_abs_of_gcd_eq_one (by decide), hs]
  norm_num

private theorem mulHeight_one_neg_one_zero : Height.mulHeight ![(1 : ℚ), -1, 0] = 1 := by
  have hx : ![(1 : ℚ), -1, 0] = ((↑) : ℤ → ℚ) ∘ ![(1 : ℤ), -1, 0] := by
    funext i
    fin_cases i <;> simp
  have hs : (⨆ i, |![(1 : ℤ), -1, 0] i|) = 1 :=
    le_antisymm (ciSup_le fun i ↦ by fin_cases i <;> simp) (Finite.le_ciSup_of_le 0 (by simp))
  rw [hx, Rat.mulHeight_eq_max_abs_of_gcd_eq_one (by decide), hs]
  norm_num

private theorem mulHeight_one_one_neg_two : Height.mulHeight ![(1 : ℚ), 1, -2] = 2 := by
  have hx : ![(1 : ℚ), 1, -2] = ((↑) : ℤ → ℚ) ∘ ![(1 : ℤ), 1, -2] := by
    funext i
    fin_cases i <;> simp
  have hs : (⨆ i, |![(1 : ℤ), 1, -2] i|) = 2 :=
    le_antisymm (ciSup_le fun i ↦ by fin_cases i <;> simp) (Finite.le_ciSup_of_le 2 (by simp))
  rw [hx, Rat.mulHeight_eq_max_abs_of_gcd_eq_one (by decide), hs]
  norm_num

/-- The kernel of the refuting matrix is the line `ℚ · (1, 1, -2)`. -/
private theorem ker_refutingMatrix :
    LinearMap.ker refutingMatrix.mulVecLin = span ℚ {![(1 : ℚ), 1, -2]} := by
  refine le_antisymm (fun x hx ↦ ?_) ?_
  · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx
    have h0 : x 0 + (x 1 + x 2) = 0 := by
      have := congrFun hx 0
      simpa [refutingMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using this
    have h1 : x 0 + -x 1 = 0 := by
      have := congrFun hx 1
      simpa [refutingMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using this
    refine mem_span_singleton.2 ⟨x 0, ?_⟩
    funext i
    fin_cases i
    · simp
    · simp
      linarith
    · simp
      linarith
  · rw [span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker,
      Matrix.mulVecLin_apply]
    funext i
    fin_cases i <;>
      norm_num [refutingMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The row space of the refuting matrix is the sum of the two lines. -/
private theorem span_range_row_refutingMatrix :
    span ℚ (Set.range refutingMatrix.row) =
      span ℚ {![(1 : ℚ), 1, 1]} ⊔ span ℚ {![(1 : ℚ), -1, 0]} := by
  have hrange : Set.range refutingMatrix.row = {![(1 : ℚ), 1, 1], ![(1 : ℚ), -1, 0]} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  rw [hrange, Set.insert_eq, Submodule.span_union]

/-- The two lines meet in `⊥`. -/
private theorem inf_refuting :
    span ℚ {![(1 : ℚ), 1, 1]} ⊓ span ℚ {![(1 : ℚ), -1, 0]} = ⊥ := by
  refine le_antisymm (fun x hx ↦ ?_) bot_le
  obtain ⟨hxa, hxb⟩ := hx
  obtain ⟨c, rfl⟩ := mem_span_singleton.1 hxa
  obtain ⟨d, hd⟩ := mem_span_singleton.1 hxb
  have h2 : c = 0 := by
    have := congrFun hd 2
    simpa using this.symm
  simp [h2]

/-- **Rejection test: the height of a subspace is not submodular.** The lines `ℚ · (1, 1, 1)` and
`ℚ · (1, -1, 0)` in `ℚ³` both have height `1`, they meet in `0`, and they span a plane of height
`2` — the height of the line `ℚ · (1, 1, -2)` that the plane annihilates, by Corollary 2.8.12 of
Layer 3.5. So `H(V + W) · H(V ∩ W) = 2 > 1 = H(V) · H(W)`: the milestone's inequality is **false**
in the sup-norm normalization of `Submodule.mulHeight`, and so is its corollary for the sum. -/
example :
    ¬ ((span ℚ {![(1 : ℚ), 1, 1]} ⊔ span ℚ {![(1 : ℚ), -1, 0]}).mulHeight *
          (span ℚ {![(1 : ℚ), 1, 1]} ⊓ span ℚ {![(1 : ℚ), -1, 0]}).mulHeight ≤
        (span ℚ {![(1 : ℚ), 1, 1]}).mulHeight * (span ℚ {![(1 : ℚ), -1, 0]}).mulHeight) ∧
      ¬ ((span ℚ {![(1 : ℚ), 1, 1]} ⊔ span ℚ {![(1 : ℚ), -1, 0]}).mulHeight ≤
        (span ℚ {![(1 : ℚ), 1, 1]}).mulHeight * (span ℚ {![(1 : ℚ), -1, 0]}).mulHeight) := by
  have hsup : (span ℚ {![(1 : ℚ), 1, 1]} ⊔ span ℚ {![(1 : ℚ), -1, 0]}).mulHeight = 2 := by
    rw [← span_range_row_refutingMatrix, ← Matrix.mulHeight_ker_mulVecLin, ker_refutingMatrix,
      Submodule.mulHeight_span_singleton ne_zero_one_one_neg_two, mulHeight_one_one_neg_two]
  have hprod : (span ℚ {![(1 : ℚ), 1, 1]}).mulHeight *
      (span ℚ {![(1 : ℚ), -1, 0]}).mulHeight = 1 := by
    rw [Submodule.mulHeight_span_singleton ne_zero_one_one_one,
      Submodule.mulHeight_span_singleton ne_zero_one_neg_one_zero, mulHeight_one_one_one,
      mulHeight_one_neg_one_zero]
    norm_num
  rw [hsup, hprod, inf_refuting, Submodule.mulHeight_bot]
  norm_num

/-- **Rejection test: the corollary for the intersection fails too.** Transporting the pair above
through the duality theorem of Layer 3.5 turns the two lines into two planes of height `1` whose
intersection is the transported annihilator of their span, of height `2`. So
`H(V ∩ W) = 2 > 1 = H(V) · H(W)`. -/
example :
    ¬ (((span ℚ {![(1 : ℚ), 1, 1]}).dualAnnihilator.comap
            (Module.piEquiv (Fin 3) ℚ ℚ).toLinearMap ⊓
          (span ℚ {![(1 : ℚ), -1, 0]}).dualAnnihilator.comap
            (Module.piEquiv (Fin 3) ℚ ℚ).toLinearMap).mulHeight ≤
        ((span ℚ {![(1 : ℚ), 1, 1]}).dualAnnihilator.comap
              (Module.piEquiv (Fin 3) ℚ ℚ).toLinearMap).mulHeight *
            ((span ℚ {![(1 : ℚ), -1, 0]}).dualAnnihilator.comap
              (Module.piEquiv (Fin 3) ℚ ℚ).toLinearMap).mulHeight) := by
  have hinf : ((span ℚ {![(1 : ℚ), 1, 1]}).dualAnnihilator.comap
        (Module.piEquiv (Fin 3) ℚ ℚ).toLinearMap ⊓
      (span ℚ {![(1 : ℚ), -1, 0]}).dualAnnihilator.comap
        (Module.piEquiv (Fin 3) ℚ ℚ).toLinearMap).mulHeight = 2 := by
    rw [← Submodule.comap_inf, ← Submodule.dualAnnihilator_sup_eq,
      Submodule.mulHeight_comap_piEquiv_dualAnnihilator, ← span_range_row_refutingMatrix,
      ← Matrix.mulHeight_ker_mulVecLin, ker_refutingMatrix,
      Submodule.mulHeight_span_singleton ne_zero_one_one_neg_two, mulHeight_one_one_neg_two]
  have hprod : ((span ℚ {![(1 : ℚ), 1, 1]}).dualAnnihilator.comap
        (Module.piEquiv (Fin 3) ℚ ℚ).toLinearMap).mulHeight *
      ((span ℚ {![(1 : ℚ), -1, 0]}).dualAnnihilator.comap
        (Module.piEquiv (Fin 3) ℚ ℚ).toLinearMap).mulHeight = 1 := by
    rw [Submodule.mulHeight_comap_piEquiv_dualAnnihilator,
      Submodule.mulHeight_comap_piEquiv_dualAnnihilator,
      Submodule.mulHeight_span_singleton ne_zero_one_one_one,
      Submodule.mulHeight_span_singleton ne_zero_one_neg_one_zero, mulHeight_one_one_one,
      mulHeight_one_neg_one_zero]
    norm_num
  rw [hinf, hprod]
  norm_num

/-- **Acceptance test: the same pair satisfies the inequality in the ℓ² normalization, with
equality.** The two rows are orthogonal, so the Gram determinant of the pair is the product of
their squared lengths, `6 = 3 · 2`; by Cauchy–Binet the left side is the sum of the squares of the
three maximal minors, `4 + 1 + 1`. The archimedean local factor of the Arakelov height therefore
obeys the inequality here — it is the sup norm that fails, and the failure is a failure of the
normalization and not of the mathematics. -/
example : (refutingMatrix * refutingMatrixᵀ).det = 6 ∧
    ∏ i, refutingMatrix.row i ⬝ᵥ refutingMatrix.row i = 6 := by
  constructor
  · rw [Matrix.det_fin_two]
    norm_num [refutingMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
  · norm_num [refutingMatrix, Matrix.row, dotProduct, Fin.sum_univ_succ, Fin.prod_univ_succ]

/-- **Conformance: the milestone unwound.** For any pair of subspaces of a number field there is
one adapted triple of families whose four Plücker vectors carry the four Arakelov heights of the
milestone, and at every place — infinite and finite — those four tuples satisfy the local form of
the inequality. Taking the product over all places is
`NumberField.arakelovMulHeight_mul_le_of_forall_le`, and the result is
`Submodule.arakelovMulHeight_sup_mul_arakelovMulHeight_inf_le`. -/
example {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [LinearOrder ι]
    (V W : Submodule K (ι → K)) :
    ∃ (k m n : ℕ) (u : Fin k → (ι → K)) (b : Fin m → (ι → K)) (c : Fin n → (ι → K)),
      (V ⊓ W).arakelovMulHeight = NumberField.arakelovMulHeight (plucker k u) ∧
        V.arakelovMulHeight = NumberField.arakelovMulHeight (plucker (k + m) (Fin.append u b)) ∧
        W.arakelovMulHeight = NumberField.arakelovMulHeight (plucker (k + n) (Fin.append u c)) ∧
        (V ⊔ W).arakelovMulHeight = NumberField.arakelovMulHeight
            (plucker (k + (m + n)) (Fin.append u (Fin.append b c))) ∧
        (∀ v : NumberField.InfinitePlace K,
          (∑ s : Set.powersetCard ι (k + (m + n)),
                v (plucker (k + (m + n)) (Fin.append u (Fin.append b c)) s) ^ 2) *
              (∑ s : Set.powersetCard ι k, v (plucker k u s) ^ 2)
            ≤ (∑ s : Set.powersetCard ι (k + m), v (plucker (k + m) (Fin.append u b) s) ^ 2) *
              (∑ s : Set.powersetCard ι (k + n), v (plucker (k + n) (Fin.append u c) s) ^ 2)) ∧
        ∀ v : NumberField.FinitePlace K,
          (⨆ s : Set.powersetCard ι (k + (m + n)),
                v (plucker (k + (m + n)) (Fin.append u (Fin.append b c)) s)) *
              (⨆ s : Set.powersetCard ι k, v (plucker k u s))
            ≤ (⨆ s : Set.powersetCard ι (k + m), v (plucker (k + m) (Fin.append u b) s)) *
              ⨆ s : Set.powersetCard ι (k + n), v (plucker (k + n) (Fin.append u c) s) := by
  obtain ⟨k, m, n, u, b, c, hu, hub, huc, hubc, hsu, hsub, hsuc, hsubc⟩ :=
    Submodule.exists_append_span_eq V W
  exact ⟨k, m, n, u, b, c, by rw [← hsu, Submodule.arakelovMulHeight_span_range hu],
    by rw [← hsub, Submodule.arakelovMulHeight_span_range hub],
    by rw [← hsuc, Submodule.arakelovMulHeight_span_range huc],
    by rw [← hsubc, Submodule.arakelovMulHeight_span_range hubc],
    fun v ↦ NumberField.InfinitePlace.sum_sq_plucker_append_mul_le v u b c,
    fun v ↦ NumberField.FinitePlace.iSup_plucker_append_mul_le v u b c⟩

end Examples

end
