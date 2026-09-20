/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.RowEntryHeight

/-!
# Restriction of scalars for a linear system, and the row space over a subfield

Let `F / K` be a finite extension of number fields of degree `r` and let `A` be an `M × N` matrix
with entries in `F`. A vector `x ∈ K ^ N` solves `A x = 0` exactly when it solves the `r M × N`
system over `K` obtained by writing each entry of `A` in a `K`-basis of `F`. That system is
`Matrix.restrictScalars`, and this file proves the inequality Layer 5.6 needs about the height of
its row space:

`H_Ar^row(restrictScalars e A) ≤ ∏ᵢ H_Ar(Aᵢ) ^ r`,

all heights **absolute**, the left-hand side computed over `K` and the right-hand side over `F`.

The proof is Bombieri and Gubler's. Over a field `L` containing all `r` conjugates of `F` over `K`,
the matrix of conjugates

`Ã = (σ_u (A i j))_{(i,u), j}`

is `Ω · restrictScalars e A` with `Ω` the block-diagonal matrix of the `r × r` matrix
`(σ_u (e t))`, which is invertible because the discriminant of a separable extension does not
vanish. So `Ã` and `restrictScalars e A` have the same row space over `L`, which is the base
change of the row space over `K`; the absolute height of a subspace does not change under base
change; and 2.9.8 over `L` bounds it by `∏_{i,u} H_Ar(σ_u (A i)) = ∏ᵢ H_Ar(Aᵢ) ^ r`, the absolute
Arakelov height being invariant under an embedding.

## Main definitions

* `Matrix.restrictScalars`: the `r M × N` system over `K` equivalent to `A x = 0` on `K ^ N`.
* `Matrix.mulVecRestrict`: the `K`-linear map `x ↦ A x` on `K`-rational vectors, so that the
  solution space is a kernel stated without reference to a basis of `F / K`.
* `Matrix.conjugate`, `Matrix.embMatrix`, `Matrix.blockEmbMatrix`: the matrix of conjugates and
  the two matrices of embeddings that relate it to `Matrix.restrictScalars`.

## Main results

* `Matrix.ker_mulVecLin_restrictScalars`: the two solution spaces agree.
* `Submodule.arakelovMulHeight_span_range_comp_algebraMap_rpow`: the absolute Arakelov height of a
  subspace does not change under base change.
* `Matrix.arakelovMulHeight_span_restrictScalars_rpow_le'`: the displayed inequality, with no
  auxiliary field in the statement.
* `Matrix.finrank_range_mulVecRestrict_le` and `Matrix.le_finrank_ker_mulVecRestrict`: the
  `K`-rank of the descended system is at most `r · rank A`, so its solution space has dimension
  at least `N − r · rank A`. Added for Layer 5.7.

## Implementation notes

⚠ **The auxiliary field is built inside the proof and never appears in a statement.** It is the
compositum of the images of the `r` embeddings `F →ₐ[K] AlgebraicClosure K`, an
`IntermediateField` of the algebraic closure, finite over `K` because a finite supremum of finite
intermediate fields is finite, hence a number field. Taking a normal closure would do as well and
costs more: nothing below uses normality, only that all `r` conjugates are present.

⚠ **The invertibility of the matrix of embeddings is the non-vanishing of the discriminant**, and
that statement lives in Mathlib only over an algebraically closed field
(`Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two`). The determinant is therefore computed in
the algebraic closure and pulled back along the injection of the auxiliary field, which is where
`RingHom.map_det` is used.

⚠ **2.9.8 is needed for a family indexed by a product**, the rows of `restrictScalars e A` being
indexed by `Fin m × Fin r`, and Layer 5.5 states it for `Fin m` and for an independent family.
`Submodule.arakelovMulHeight_span_range_le_prod` of Layer 5.5 is the form used here: any finite
index type, no hypothesis on the family.

⚠ **The rank of the descended system is bounded by the rank of `A`, not by its number of rows.**
Counting rows — `Matrix.rank_le_card_height` on `restrictScalars e A` — gives `r M`, which is what
Layer 5.6 first used and is strictly weaker as soon as the rows of `A` are dependent. The sharp
bound needs no basis of `F / K` at all: the image of `K ^ N` under `A` lies in the `F`-column
space of `A`, of `F`-dimension `rank A`, whose `K`-dimension is `r · rank A`. That is
`Module.finrank_mul_finrank` on `Submodule.restrictScalars`, and it is the whole of
`Matrix.finrank_range_mulVecRestrict_le`.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
the proof of Theorem 2.9.19, where the matrix called `Ω` here is theirs and the identity
`Ã = Ω A'` is their (2.30).

This is Layer 5.6 (infrastructure) of the `ArithmeticHeights` roadmap.
-/

public section

open Finset Matrix Module NumberField Real exteriorPower

namespace Matrix

/-!
### Restriction of scalars
-/

section Defs

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {ι : Type*} [Fintype ι] {m r : ℕ}

/-- **Restriction of scalars for a linear system.** Writing each entry of `A` in the `K`-basis `e`
of `F` turns the `M × N` system over `F` into an `r M × N` system over `K` with the same
`K`-rational solutions. The rows are indexed by `Fin m × Fin r`: the row `(i, t)` is the `t`-th
coordinate of the `i`-th row of `A`. -/
@[expose] def restrictScalars (e : Basis (Fin r) K F) (A : Matrix (Fin m) ι F) :
    Matrix (Fin m × Fin r) ι K :=
  Matrix.of fun p j ↦ e.repr (A p.1 j) p.2

omit [Fintype ι] in
theorem restrictScalars_apply (e : Basis (Fin r) K F) (A : Matrix (Fin m) ι F)
    (p : Fin m × Fin r) (j : ι) :
    restrictScalars e A p j = e.repr (A p.1 j) p.2 := rfl

/-- The `K`-linear map `x ↦ A x` on `K`-rational vectors, for `A` a matrix over `F`. Its kernel is
the object Layer 5.6 is about, and it mentions no basis of `F / K`. -/
@[expose] noncomputable def mulVecRestrict (A : Matrix (Fin m) ι F) :
    (ι → K) →ₗ[K] (Fin m → F) :=
  (LinearMap.restrictScalars K A.mulVecLin).comp ((Algebra.linearMap K F).compLeft ι)

theorem mulVecRestrict_apply (A : Matrix (Fin m) ι F) (x : ι → K) :
    mulVecRestrict A x = A.mulVec fun j ↦ algebraMap K F (x j) := rfl

/-- The `(i, t)`-th coordinate of the restricted system is the `t`-th coordinate of the `i`-th
coordinate of `A x`. -/
theorem mulVec_restrictScalars (e : Basis (Fin r) K F) (A : Matrix (Fin m) ι F) (x : ι → K) :
    (restrictScalars e A).mulVec x
      = fun p ↦ e.repr (A.mulVec (fun j ↦ algebraMap K F (x j)) p.1) p.2 := by
  funext q
  have h : A.mulVec (fun j ↦ algebraMap K F (x j)) q.1 = ∑ j, x j • A q.1 j := by
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [Algebra.smul_def, mul_comm]
  rw [h, map_sum]
  simp only [map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.mulVec, dotProduct, restrictScalars_apply]
  exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _

/-- **The two solution spaces agree.** -/
theorem ker_mulVecLin_restrictScalars (e : Basis (Fin r) K F) (A : Matrix (Fin m) ι F) :
    LinearMap.ker (restrictScalars e A).mulVecLin
      = LinearMap.ker (mulVecRestrict (K := K) A) := by
  ext x
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, mulVecRestrict_apply,
    mulVec_restrictScalars e A x]
  constructor
  · intro h
    funext i
    refine (map_eq_zero_iff e.repr e.repr.injective).1 ?_
    ext t
    simpa using congrFun h (i, t)
  · intro h
    funext p
    rw [h]
    simp

end Defs

/-!
### The rank of the restricted system
-/

section Rank

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [FiniteDimensional K F]
variable {ι : Type*} [Fintype ι] {m : ℕ}

/-- **The `K`-rank of the restricted system is at most `r` times the `F`-rank of `A`.** The image
of `K ^ N` under `A` lies in the `F`-column space of `A`, an `F`-space of dimension `rank A`,
which as a `K`-space has dimension `r · rank A`. The crude bound `r M` — one for each row of
`Matrix.restrictScalars` — is what `Matrix.rank_le_card_height` gives and is strictly weaker
whenever `A` is not of full rank. -/
theorem finrank_range_mulVecRestrict_le (A : Matrix (Fin m) ι F) :
    finrank K (LinearMap.range (mulVecRestrict (K := K) A)) ≤ finrank K F * A.rank := by
  have hle : LinearMap.range (mulVecRestrict (K := K) A)
      ≤ (LinearMap.range A.mulVecLin).restrictScalars K := by
    rintro _ ⟨x, rfl⟩
    exact ⟨fun j ↦ algebraMap K F (x j), rfl⟩
  refine (Submodule.finrank_mono hle).trans (le_of_eq ?_)
  exact (Module.finrank_mul_finrank K F ↥(LinearMap.range A.mulVecLin)).symm

/-- **The `K`-rational solution space is at least `N − r · rank A`-dimensional.** This is the
hypothesis Layers 5.6 and 5.7 need in their sharp form: what has to be small is not the number of
rows of `A` but its rank. -/
theorem le_finrank_ker_mulVecRestrict (A : Matrix (Fin m) ι F) :
    Fintype.card ι - finrank K F * A.rank
      ≤ finrank K (LinearMap.ker (mulVecRestrict (K := K) A)) := by
  have h := LinearMap.finrank_range_add_finrank_ker (mulVecRestrict (K := K) A)
  rw [Module.finrank_fintype_fun_eq_card] at h
  have := finrank_range_mulVecRestrict_le (K := K) A
  omega

end Rank

/-!
### The matrix of conjugates
-/

section Conjugate

variable {K F L : Type*} [Field K] [Field F] [Field L] [Algebra K F] [Algebra K L]
variable {ι : Type*} [Fintype ι] {m r : ℕ}

/-- **The matrix of conjugates**: the row `(i, u)` is the `u`-th conjugate of the `i`-th row of
`A`. This is Bombieri–Gubler's `Ã`. -/
@[expose] def conjugate (σ : Fin r → (F →ₐ[K] L)) (A : Matrix (Fin m) ι F) :
    Matrix (Fin m × Fin r) ι L :=
  Matrix.of fun p j ↦ σ p.2 (A p.1 j)

/-- The matrix of the embeddings on a basis, `(σ_u (e t))`. Its determinant is a square root of
the discriminant of `F / K` in that basis, so it is invertible. -/
@[expose] noncomputable def embMatrix (e : Basis (Fin r) K F) (σ : Fin r → (F →ₐ[K] L)) :
    Matrix (Fin r) (Fin r) L :=
  Matrix.of fun u t ↦ σ u (e t)

/-- `m` copies of `Matrix.embMatrix` down the diagonal: Bombieri–Gubler's `Ω`. -/
@[expose] noncomputable def blockEmbMatrix (e : Basis (Fin r) K F) (σ : Fin r → (F →ₐ[K] L))
    (m : ℕ) : Matrix (Fin m × Fin r) (Fin m × Fin r) L :=
  Matrix.of fun p q ↦ if p.1 = q.1 then embMatrix e σ p.2 q.2 else 0

omit [Fintype ι] in
theorem det_blockEmbMatrix (e : Basis (Fin r) K F) (σ : Fin r → (F →ₐ[K] L)) :
    (blockEmbMatrix e σ m).det = (embMatrix e σ).det ^ m := by
  have h : blockEmbMatrix e σ m
      = (Matrix.blockDiagonal fun _ : Fin m ↦ embMatrix e σ).submatrix
          (Equiv.prodComm (Fin m) (Fin r)) (Equiv.prodComm (Fin m) (Fin r)) := by
    ext p q
    simp [blockEmbMatrix, Matrix.blockDiagonal_apply, Equiv.prodComm]
  rw [h, Matrix.det_submatrix_equiv_self, Matrix.det_blockDiagonal, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

omit [Fintype ι] in
/-- **Bombieri–Gubler's (2.30):** the matrix of conjugates is the block matrix of embeddings times
the restriction of scalars. -/
theorem conjugate_eq_blockEmbMatrix_mul (e : Basis (Fin r) K F) (σ : Fin r → (F →ₐ[K] L))
    (A : Matrix (Fin m) ι F) :
    conjugate σ A = blockEmbMatrix e σ m * (restrictScalars e A).map (algebraMap K L) := by
  ext p j
  have hbasis : σ p.2 (A p.1 j)
      = ∑ t, σ p.2 (e t) * algebraMap K L (e.repr (A p.1 j) t) := by
    conv_lhs => rw [← e.sum_repr (A p.1 j)]
    rw [map_sum]
    exact Finset.sum_congr rfl fun t _ ↦ by rw [map_smul, Algebra.smul_def, mul_comm]
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [blockEmbMatrix, Matrix.of_apply, ite_mul, zero_mul, Matrix.map_apply,
    restrictScalars_apply, conjugate, embMatrix]
  rw [Finset.sum_eq_single p.1 (fun b _ hb ↦ by simp [Ne.symm hb]) (by simp)]
  simpa using hbasis

omit [Fintype ι] in
/-- **The conjugates and the restriction of scalars have the same row space over `L`.** -/
theorem span_range_row_conjugate (e : Basis (Fin r) K F) (σ : Fin r → (F →ₐ[K] L))
    (hM : IsUnit (embMatrix e σ).det) (A : Matrix (Fin m) ι F) :
    Submodule.span L (Set.range (conjugate σ A).row)
      = Submodule.span L (Set.range ((restrictScalars e A).map (algebraMap K L)).row) := by
  rw [conjugate_eq_blockEmbMatrix_mul e]
  exact Matrix.span_range_row_mul (by rw [det_blockEmbMatrix]; exact hM.pow m) _

end Conjugate

end Matrix

/-!
### Base change of a subspace
-/

namespace Submodule

section BaseChange

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {ι : Type*}

/-- The image of a `K`-span lies in the `L`-span of the image. -/
theorem comp_algebraMap_mem_span {μ : Type*} {v : μ → (ι → K)} {x : ι → K}
    (hx : x ∈ Submodule.span K (Set.range v)) :
    (algebraMap K L ∘ x) ∈ Submodule.span L (Set.range fun l ↦ algebraMap K L ∘ v l) := by
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨l, rfl⟩ := hy; exact Submodule.subset_span ⟨l, rfl⟩
  | zero =>
      rw [show (algebraMap K L ∘ (0 : ι → K)) = 0 from funext fun j ↦ by simp]
      exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
      rw [show (algebraMap K L ∘ (y + z))
        = (algebraMap K L ∘ y) + (algebraMap K L ∘ z) from funext fun j ↦ by simp]
      exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
      rw [show (algebraMap K L ∘ (c • y))
        = algebraMap K L c • (algebraMap K L ∘ y) from funext fun j ↦ by simp [Algebra.smul_def]]
      exact Submodule.smul_mem _ _ hy

/-- **Base change of a span.** Two families with the same `K`-span have the same `L`-span after
base change, so the base change of a subspace may be computed from any family that spans it. -/
theorem span_range_comp_algebraMap_eq {μ ν : Type*} {v : μ → (ι → K)} {w : ν → (ι → K)}
    (h : Submodule.span K (Set.range v) = Submodule.span K (Set.range w)) :
    Submodule.span L (Set.range fun l ↦ algebraMap K L ∘ v l)
      = Submodule.span L (Set.range fun l ↦ algebraMap K L ∘ w l) := by
  refine le_antisymm ?_ ?_ <;> rw [Submodule.span_le] <;> rintro _ ⟨l, rfl⟩
  · exact comp_algebraMap_mem_span (h ▸ Submodule.subset_span ⟨l, rfl⟩)
  · exact comp_algebraMap_mem_span (h ▸ Submodule.subset_span ⟨l, rfl⟩)

end BaseChange

section Height

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
variable {ι : Type*} [Fintype ι] [LinearOrder ι] {k : ℕ}

/-- **Base change does not change the absolute Arakelov height of a subspace.** The Plücker point
of the base change is the image of the Plücker point, by `exteriorPower.plucker_comp_ringHom`, and
the absolute height of a tuple is invariant under an embedding. -/
theorem arakelovMulHeight_span_range_comp_algebraMap_rpow {v : Fin k → (ι → K)}
    (hv : LinearIndependent K v) :
    (Submodule.span L (Set.range fun l ↦ algebraMap K L ∘ v l)).arakelovMulHeight
        ^ (finrank ℚ L : ℝ)⁻¹
      = (Submodule.span K (Set.range v)).arakelovMulHeight ^ (finrank ℚ K : ℝ)⁻¹ := by
  have hp : plucker k (fun l ↦ algebraMap K L ∘ v l) = algebraMap K L ∘ plucker k v :=
    plucker_comp_ringHom _ k v
  have hind : LinearIndependent L (fun l ↦ algebraMap K L ∘ v l) := by
    by_contra hcon
    have h0 := (plucker_eq_zero_iff k _).2 hcon
    rw [hp] at h0
    exact plucker_ne_zero hv (funext fun s ↦ FaithfulSMul.algebraMap_injective K L
      (by simpa using congrFun h0 s))
  rw [Submodule.arakelovMulHeight_span_range hind, Submodule.arakelovMulHeight_span_range hv, hp]
  exact NumberField.arakelovMulHeight_rpow_comp (algebraMap K L) (plucker k v)

end Height

end Submodule

/-!
### The row space of the restricted system against the rows of `A`
-/

namespace Matrix

section Relative

variable {K F L : Type*} [Field K] [Field F] [Field L]
  [NumberField K] [NumberField F] [NumberField L] [Algebra K F] [Algebra K L]
variable {ι : Type*} [Fintype ι] [LinearOrder ι] {m r : ℕ}

/-- **2.9.8 over a finite extension, with the conjugates given.** -/
theorem arakelovMulHeight_span_restrictScalars_rpow_le
    (e : Basis (Fin r) K F) (σ : Fin r → (F →ₐ[K] L)) (hM : IsUnit (embMatrix e σ).det)
    (A : Matrix (Fin m) ι F) :
    (Submodule.span K (Set.range (restrictScalars e A).row)).arakelovMulHeight
        ^ (finrank ℚ K : ℝ)⁻¹
      ≤ ∏ i, (NumberField.arakelovMulHeight (A i) ^ (finrank ℚ F : ℝ)⁻¹) ^ r := by
  set B := restrictScalars e A with hBdef
  set W := Submodule.span K (Set.range B.row) with hWdef
  set b := Module.finBasis K W with hbdef
  set v : Fin (finrank K W) → (ι → K) := fun l ↦ ((b l : ι → K)) with hvdef
  have hvind : LinearIndependent K v := Submodule.linearIndependent_coe_basis b
  have hvspan : Submodule.span K (Set.range v) = W := Submodule.span_range_coe_basis b
  have hbc : Submodule.span L (Set.range fun l ↦ algebraMap K L ∘ v l)
      = Submodule.span L (Set.range (B.map (algebraMap K L)).row) :=
    Submodule.span_range_comp_algebraMap_eq (v := v) (w := B.row) (by rw [hvspan])
  calc W.arakelovMulHeight ^ (finrank ℚ K : ℝ)⁻¹
      = (Submodule.span L (Set.range fun l ↦ algebraMap K L ∘ v l)).arakelovMulHeight
          ^ (finrank ℚ L : ℝ)⁻¹ := by
        rw [Submodule.arakelovMulHeight_span_range_comp_algebraMap_rpow hvind, hvspan]
    _ = (Submodule.span L (Set.range (conjugate σ A).row)).arakelovMulHeight
          ^ (finrank ℚ L : ℝ)⁻¹ := by rw [hbc, span_range_row_conjugate e σ hM]
    _ ≤ (∏ p, NumberField.arakelovMulHeight (conjugate σ A p)) ^ (finrank ℚ L : ℝ)⁻¹ :=
        Real.rpow_le_rpow (Submodule.arakelovMulHeight_pos _).le
          (Submodule.arakelovMulHeight_span_range_le_prod _) (by positivity)
    _ = ∏ p, NumberField.arakelovMulHeight (conjugate σ A p) ^ (finrank ℚ L : ℝ)⁻¹ :=
        (Real.finsetProd_rpow _ _ (fun p _ ↦ (NumberField.arakelovMulHeight_pos _).le) _).symm
    _ = ∏ i, (NumberField.arakelovMulHeight (A i) ^ (finrank ℚ F : ℝ)⁻¹) ^ r := by
        rw [Fintype.prod_prod_type]
        refine Finset.prod_congr rfl fun i _ ↦ ?_
        have hstep : ∀ t : Fin r,
            NumberField.arakelovMulHeight (conjugate σ A (i, t)) ^ (finrank ℚ L : ℝ)⁻¹
              = NumberField.arakelovMulHeight (A i) ^ (finrank ℚ F : ℝ)⁻¹ := fun t ↦
          NumberField.arakelovMulHeight_rpow_comp (σ t).toRingHom (A i)
        rw [Finset.prod_congr rfl fun t _ ↦ hstep t, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]

end Relative

section Exists

variable {K F : Type*} [Field K] [Field F] [NumberField K] [NumberField F] [Algebra K F]
variable {ι : Type*} [Fintype ι] [LinearOrder ι] {m r : ℕ}

open IntermediateField in
/-- **2.9.8 over a finite extension** (Bombieri–Gubler, inside the proof of Theorem 2.9.19): the
absolute Arakelov height of the row space of the restricted system is at most the product of the
`r`-th powers of the absolute Arakelov heights of the rows of `A`. The field carrying the
conjugates is constructed in the proof. -/
theorem arakelovMulHeight_span_restrictScalars_rpow_le'
    (e : Basis (Fin r) K F) (A : Matrix (Fin m) ι F) :
    (Submodule.span K (Set.range (restrictScalars e A).row)).arakelovMulHeight
        ^ (finrank ℚ K : ℝ)⁻¹
      ≤ ∏ i, (NumberField.arakelovMulHeight (A i) ^ (finrank ℚ F : ℝ)⁻¹) ^ r := by
  classical
  have : IsScalarTower ℚ K F := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have : Module.Finite K F := Module.Finite.of_restrictScalars_finite ℚ K F
  have hcard : Fintype.card (F →ₐ[K] AlgebraicClosure K) = r := by
    rw [AlgHom.card K F (AlgebraicClosure K), Module.finrank_eq_card_basis e, Fintype.card_fin]
  let τ : Fin r ≃ (F →ₐ[K] AlgebraicClosure K) := (Fintype.equivFinOfCardEq hcard).symm
  have hfr : ∀ i : Fin r, FiniteDimensional K ↥((τ i).fieldRange) := fun i ↦
    (AlgEquiv.ofInjectiveField (τ i)).toLinearEquiv.finiteDimensional
  let L : IntermediateField K (AlgebraicClosure K) := ⨆ i : Fin r, (τ i).fieldRange
  have : FiniteDimensional K ↥L := inferInstance
  have : IsScalarTower ℚ K ↥L := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have : FiniteDimensional ℚ ↥L := Module.Finite.trans K ↥L
  have : NumberField ↥L := ⟨⟩
  let σ : Fin r → (F →ₐ[K] ↥L) := fun i ↦ (τ i).codRestrict L.toSubalgebra
    (fun x ↦ le_iSup (fun i : Fin r ↦ ((τ i).fieldRange : IntermediateField K _)) i ⟨x, rfl⟩)
  have hσ : ∀ i x, algebraMap ↥L (AlgebraicClosure K) (σ i x) = τ i x := fun i x ↦ rfl
  have hdet : (embMatrix e τ).det ≠ 0 := by
    have h2 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two K (AlgebraicClosure K) (⇑e) τ
    have hd : Algebra.discr K (⇑e) ≠ 0 := Algebra.discr_not_zero_of_basis K e
    have ht : embMatrix e τ
        = (Algebra.embeddingsMatrixReindex K (AlgebraicClosure K) (⇑e) τ)ᵀ := by
      ext u t
      simp [embMatrix, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix]
    rw [ht, Matrix.det_transpose]
    intro h0
    rw [h0] at h2
    exact hd ((map_eq_zero_iff _ (algebraMap K (AlgebraicClosure K)).injective).1
      (by simpa using h2))
  have hM : IsUnit (embMatrix e σ).det := by
    have hmap : (embMatrix e σ).map (algebraMap ↥L (AlgebraicClosure K)) = embMatrix e τ := by
      ext u t
      simp [embMatrix, hσ]
    have hval : algebraMap ↥L (AlgebraicClosure K) (embMatrix e σ).det = (embMatrix e τ).det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap]
    refine isUnit_iff_ne_zero.2 fun h0 ↦ hdet ?_
    rw [← hval, h0, map_zero]
  exact arakelovMulHeight_span_restrictScalars_rpow_le e σ hM A

end Exists

end Matrix

end
