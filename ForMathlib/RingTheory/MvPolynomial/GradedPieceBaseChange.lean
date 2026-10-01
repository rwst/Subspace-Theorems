/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.RingTheory.MvPolynomial.BaseChange
public import ForMathlib.RingTheory.MvPolynomial.GradedPiece
public import ForMathlib.RingTheory.TensorProduct.IsBaseChangeQuotient

-- Used only inside proofs.
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree

/-!
# Graded pieces under extension of the coefficients

For an `R`-algebra `R'` and a multihomogeneous ideal `I` of `R[X]`, the graded piece
`(R'[X]/I R'[X])_k` is the base change `R' ⊗_R (R[X]/I)_k`
(`MvPolynomial.gradedPiece.isBaseChange`). No flatness is needed: the tensor product is right
exact, and the homogeneous elements of `I R'[X]` of multidegree `k` are spanned by the images of
those of `I`.

With `isLocalizedModule_iff_isBaseChange` this covers localization of the coefficients, and with
`IsBaseChange.basis` it gives bases of `(R'[X]/I R'[X])_k` from bases of `(R[X]/I)_k`.
-/

@[expose] public section

namespace MvPolynomial

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι}
  {R R' : Type*} [CommRing R] [CommRing R'] [Algebra R R']

omit [Fintype σ] [Fintype ι] in
theorem IsWeightedHomogeneous.map_algebraMap {f : MvPolynomial σ R} {a : ι → ℕ}
    (hf : IsWeightedHomogeneous (multiWeight b) f a) :
    IsWeightedHomogeneous (multiWeight b) (map (algebraMap R R') f) a := fun c hc ↦
  hf fun h0 ↦ hc (by rw [coeff_map, h0, map_zero])

namespace gradedPiece

variable (b R R') in
/-- The map `R[X]_k → R'[X]_k` of the multihomogeneous parts. -/
noncomputable def polyMap (k : ι → ℕ) :
    weightedHomogeneousSubmodule R (multiWeight b) k →ₗ[R]
      weightedHomogeneousSubmodule R' (multiWeight b) k where
  toFun f := ⟨map (algebraMap R R') f, IsWeightedHomogeneous.map_algebraMap f.2⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' r f := Subtype.ext (map_smul (mapAlgHom (Algebra.ofId R R')) r (f : MvPolynomial σ R))

omit [Fintype σ] [Fintype ι] in
@[simp]
theorem coe_polyMap (k : ι → ℕ) (f : weightedHomogeneousSubmodule R (multiWeight b) k) :
    (polyMap b R R' k f : MvPolynomial σ R') = map (algebraMap R R') (f : MvPolynomial σ R) :=
  rfl

variable (b R) in
/-- The monomial basis of `R[X]_k`. -/
noncomputable def monomialBasis (k : ι → ℕ) :
    Module.Basis (blockMonomials b k) R (weightedHomogeneousSubmodule R (multiWeight b) k) :=
  (Module.Basis.span ((basisMonomials σ R).linearIndependent.comp
    (fun c : blockMonomials b k ↦ (c : σ →₀ ℕ)) Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (by
      rw [gradedPiece.weightedHomogeneousSubmodule_eq_span]
      congr 1
      ext p
      simp))

theorem coe_monomialBasis (k : ι → ℕ) (c : blockMonomials b k) :
    (monomialBasis b R k c : MvPolynomial σ R) = monomial (c : σ →₀ ℕ) 1 := by
  rw [monomialBasis, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply, Module.Basis.span_apply]
  rfl

omit [Fintype σ] [Fintype ι] in
/-- `R[X]_k → R'[X]_k` is a base change. -/
theorem isBaseChange_polyMap [Finite σ] [Finite ι] (k : ι → ℕ) :
    IsBaseChange R' (polyMap b R R' k) := by
  have := Fintype.ofFinite σ
  have := Fintype.ofFinite ι
  have h := IsBaseChange.comp_equiv (monomialBasis b R k).repr _
    (IsBaseChange.of_basis R (monomialBasis b R' k))
  convert h
  refine (monomialBasis b R k).ext fun c ↦ ?_
  apply Subtype.ext
  simp [coe_monomialBasis]

omit [Fintype σ] [Fintype ι] in
/-- The multidegree-`k` elements of `I R'[X]` are spanned by the images of those of `I`. -/
theorem span_polyMap_image [Finite ι] (I : Ideal (MvPolynomial σ R))
    (hI : I.IsWeightedHomogeneous (multiWeight b)) (k : ι → ℕ) :
    Submodule.span R' (polyMap b R R' k ''
        ((I.restrictScalars R).comap (weightedHomogeneousSubmodule R (multiWeight b) k).subtype :
          Set _)) =
      ((I.map (map (algebraMap R R'))).restrictScalars R').comap
        (weightedHomogeneousSubmodule R' (multiWeight b) k).subtype := by
  refine le_antisymm (Submodule.span_le.mpr ?_) fun y hy ↦ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact Ideal.mem_map_of_mem (map (algebraMap R R')) hx
  have hy' : (y : MvPolynomial σ R') ∈ (Submodule.span R' (polyMap b R R' k ''
      ((I.restrictScalars R).comap (weightedHomogeneousSubmodule R (multiWeight b) k).subtype :
        Set _))).map (weightedHomogeneousSubmodule R' (multiWeight b) k).subtype := by
    rw [Submodule.map_span, ← Set.image_comp]
    have := weightedHomogeneousComponent_mem_span_homogImage (algebraMap R R') I hI hy k
    rw [Submodule.subtype_apply,
      ((mem_weightedHomogeneousSubmodule _ _ _ _).mp y.2).weightedHomogeneousComponent_same] at this
    convert this using 2
    ext z
    simp only [Set.mem_image, Function.comp_apply, homogImage, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, ⟨hx, x.2⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hxk⟩, rfl⟩
      exact ⟨⟨x, hxk⟩, hx, rfl⟩
  obtain ⟨z, hz, hzy⟩ := hy'
  rwa [← Subtype.ext hzy]

omit [Fintype σ] in
variable (b R') in
/-- The map `(R[X]/I)_k → (R'[X]/I R'[X])_k`. -/
noncomputable def baseChangeMap (I : Ideal (MvPolynomial σ R))
    (hI : I.IsWeightedHomogeneous (multiWeight b)) (k : ι → ℕ) :
    gradedPiece b I k →ₗ[R] gradedPiece b (I.map (map (algebraMap R R'))) k :=
  ((Submodule.quotEquivOfEq _ _ (span_polyMap_image I hI k)).toLinearMap.restrictScalars R).comp
    (IsBaseChange.quotientMap R' (polyMap b R R' k) _)

omit [Fintype σ] in
theorem baseChangeMap_mk (I : Ideal (MvPolynomial σ R))
    (hI : I.IsWeightedHomogeneous (multiWeight b)) {k : ι → ℕ}
    (f : weightedHomogeneousSubmodule R (multiWeight b) k) :
    baseChangeMap b R' I hI k (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (polyMap b R R' k f) :=
  rfl

omit [Fintype σ] in
/-- **Graded pieces commute with extension of the coefficients**:
`(R'[X]/I R'[X])_k = R' ⊗_R (R[X]/I)_k` for a multihomogeneous ideal `I`. -/
theorem isBaseChange [Finite σ] (I : Ideal (MvPolynomial σ R))
    (hI : I.IsWeightedHomogeneous (multiWeight b)) (k : ι → ℕ) :
    IsBaseChange R' (baseChangeMap b R' I hI k) :=
  ((isBaseChange_polyMap k).quotient _).comp (IsBaseChange.ofEquiv _)

end gradedPiece

end MvPolynomial
