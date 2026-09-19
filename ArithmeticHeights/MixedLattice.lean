/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.CauchyBinet
public import ArithmeticHeights.NormProd
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.Complex

/-!
# The mixed space of tuples, and the archimedean local factor as a determinant

For a number field `K` and a finite index type `ι`, the euclidean mixed space of `ι`-tuples is
`mixedPi K ι = PiLp 2 (fun _ : ι ↦ euclidean.mixedSpace K)`: the real carrier `(K ⊗ ℝ)ⁱ` of `Kⁱ`,
with the inner product for which the image of `(𝓞 K)ⁱ` is a lattice of the covolume Mathlib's
`covolume_integerLattice` computes. This file gives that space its trace form, attaches to a
matrix `Y` over the mixed space the `ℝ`-linear map of tuple spaces it defines, and identifies the
determinant of the associated Gram endomorphism `Y Yᴴ` with the archimedean local factor of the
Arakelov height of the Plücker point of `Y`.

That last identification is **Schmidt's Lemma 4**, and it is the archimedean half of the covolume
identity of Layer 4.3.

## Main definitions

* `NumberField.mixedEmbedding.mixedTrace`: the real trace functional on the mixed space, the sum
  of the real coordinates and of the real parts of the complex ones.
* `NumberField.mixedEmbedding.mixedPi`: the euclidean mixed space of `ι`-tuples.
* `NumberField.mixedEmbedding.toMixedPi`: the identification of `ι → mixedSpace K` with it.
* `NumberField.mixedEmbedding.mixedPiMap`: the `ℝ`-linear map `mixedPi K κ → mixedPi K ι` a matrix
  `Y : Matrix κ ι (mixedSpace K)` defines, acting by `u ↦ Yᵀ *ᵥ u`.
* `NumberField.mixedEmbedding.mixedPiEnd`: the endomorphism `Y Yᴴ` of `mixedPi K κ`.

## Main results

* `NumberField.mixedEmbedding.inner_euclidean`: `⟪a, b⟫ = mixedTrace (star a * b)`. The inner
  product of the euclidean mixed space is a trace form, so multiplication by an element of the
  mixed space has `star` for its adjoint.
* `NumberField.mixedEmbedding.inner_mixedPiMap`: `⟪Y x, Y y⟫ = ⟪(Y Yᴴ) x, y⟫`, the statement that
  `mixedPiEnd Y` is the Gram operator of `mixedPiMap Y`.
* `NumberField.mixedEmbedding.det_mixedPiEnd`: its determinant is `Algebra.norm ℝ (det (Y Yᴴ))`.
* `NumberField.mixedEmbedding.norm_mixedSpace`: the algebra norm on the mixed space is
  `∏_{w real} z_w · ∏_{w complex} |z_w|²`.
* `NumberField.mixedEmbedding.norm_det_gram`: **Schmidt's Lemma 4**, the composite
  `Algebra.norm ℝ (det (ι(Y) ι(Y)ᴴ)) = ∏_{v | ∞} (∑ₛ v(pₛ)²)^{mult v}` for `p` the Plücker point
  of a matrix `Y` over `K`.

## Implementation notes

⚠ **The archimedean half is Cauchy–Binet over the commutative star ring `mixedSpace K`, not a
place-by-place computation.** The mixed space is a product of copies of `ℝ` and `ℂ`, hence a
commutative `ℝ`-algebra with a star operation — the identity on the real factors and complex
conjugation on the complex ones. Over it, `Matrix.det_mul_conjTranspose_self_eq_sum` of Layer 3.4
computes `det (Y Yᴴ)` as `∑ₛ pₛ · star pₛ` in one step, and `exteriorPower.plucker_map` identifies
`p` with the mixed embedding of the Plücker point over `K`. The descent to `ℝ` is then
`LinearMap.det_restrictScalars`: the real determinant of a `mixedSpace K`-linear endomorphism is
the algebra norm of its mixed determinant. **Nothing is ever decomposed by place**, and the
`2^{−r₂}` of the milestone never appears here — it enters only through the covolume of `𝓞 K`.

⚠ **The adjoint is never constructed.** `ZLattice.det_gram_of_inner` asks only for *some* operator
`A` with `⟪f x, f y⟫ = ⟪A x, y⟫`, and `mixedPiEnd Y` is that operator by a one-line matrix identity
(`sum_star_mulVec`) together with the trace-form description of the inner product. So
`LinearMap.adjoint` and its finite-dimensional hypotheses stay out of the development.

⚠ **Instance search on this space is expensive**, because `mixedPi K ι` is a `PiLp` over a `WithLp`
of a product of two `PiLp`s, and the index types of the last two are subtypes of `InfinitePlace K`
that only a classical `Fintype` instance sees. The `Prop`-valued instances (`BorelSpace`,
`FiniteDimensional`) are therefore declared once here rather than rediscovered at every use site;
without them the elaboration of the covolume identity exceeds the default heartbeat budget.

## References

W. M. Schmidt, "On heights of algebraic subspaces and diophantine approximations", *Annals of
Mathematics* **85** (1967), 430–472, §3, Lemma 4, which is `norm_det_gram` composed with the
covolume of `𝓞 K`.

This is Layer 4.3 of the `ArithmeticHeights` roadmap, the archimedean half of the number-field
case.
-/

public section

noncomputable section

namespace NumberField.mixedEmbedding

open Module MeasureTheory Matrix NumberField.InfinitePlace
open scoped ComplexConjugate

variable (K : Type*) [Field K] [NumberField K]

open scoped Classical in
/-- The **real trace functional** on the mixed space: the sum of the real coordinates and of the
real parts of the complex ones. It is the functional for which the euclidean inner product of the
mixed space is `⟪a, b⟫ = mixedTrace (star a * b)`, so that multiplication by an element of the
mixed space has `star` for its adjoint. -/
@[expose] def mixedTrace : mixedSpace K →ₗ[ℝ] ℝ where
  toFun z := (∑ w, z.1 w) + ∑ w, (z.2 w).re
  map_add' a b := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Complex.add_re, Finset.sum_add_distrib]
    ring
  map_smul' c a := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Complex.real_smul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, RingHom.id_apply,
      mul_add, Finset.mul_sum]

variable {K}

omit [NumberField K] in
@[simp] theorem star_fst (z : mixedSpace K) (w : {w : InfinitePlace K // IsReal w}) :
    (star z).1 w = z.1 w := rfl

omit [NumberField K] in
@[simp] theorem star_snd (z : mixedSpace K) (w : {w : InfinitePlace K // IsComplex w}) :
    (star z).2 w = conj (z.2 w) := rfl

open scoped Classical in
/-- **The inner product of the euclidean mixed space is a trace form.** -/
theorem inner_euclidean (a b : euclidean.mixedSpace K) :
    inner ℝ a b = mixedTrace K (star (euclidean.toMixed K a) * (euclidean.toMixed K b)) := by
  rw [show (inner ℝ a b : ℝ) = inner ℝ a.ofLp.1 b.ofLp.1 + inner ℝ a.ofLp.2 b.ofLp.2 from rfl,
    PiLp.inner_apply, PiLp.inner_apply]
  simp only [mixedTrace, LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_mul, Prod.snd_mul,
    Pi.mul_apply, star_fst, star_snd, RCLike.inner_apply, Complex.inner, conj_trivial]
  congr 1
  · exact Finset.sum_congr rfl fun w _ ↦ by rw [mul_comm]; rfl
  · exact Finset.sum_congr rfl fun w _ ↦ by rw [mul_comm]; rfl

variable (K)

open scoped Classical in
/-- The mixed space of `ι`-tuples, as a euclidean space: this is the ambient in which the lattice
of integral points of a subspace of `Kⁱ` lives. -/
abbrev mixedPi (ι : Type*) := PiLp 2 (fun _ : ι ↦ euclidean.mixedSpace K)

open scoped Classical in
/-- Reading a tuple of mixed-space points as a point of the euclidean tuple space. -/
@[expose] def toMixedPi (ι : Type*) : (ι → mixedSpace K) ≃ₗ[ℝ] mixedPi K ι :=
  (LinearEquiv.piCongrRight fun _ ↦ (euclidean.toMixed K).symm.toLinearEquiv).trans
    (WithLp.linearEquiv 2 ℝ (∀ _ : ι, euclidean.mixedSpace K)).symm

open scoped Classical in
/-- The Borel structure of the euclidean tuple space, declared once so that instance search does
not have to rediscover it through the nested `WithLp` structure at every use site. -/
instance instBorelSpaceMixedPi (ι : Type*) [Finite ι] : BorelSpace (mixedPi K ι) := by
  let _ : Fintype ι := Fintype.ofFinite ι
  infer_instance

open scoped Classical in
/-- The euclidean tuple space is finite-dimensional, declared once for the same reason. -/
instance instFiniteDimensionalMixedPi (ι : Type*) [Finite ι] :
    FiniteDimensional ℝ (mixedPi K ι) := by
  let _ : Fintype ι := Fintype.ofFinite ι
  infer_instance

variable {K}

open scoped Classical in
@[simp] theorem toMixedPi_apply {ι : Type*} (u : ι → mixedSpace K) :
    toMixedPi K ι u = (WithLp.linearEquiv 2 ℝ (∀ _ : ι, euclidean.mixedSpace K)).symm
      (fun l ↦ (euclidean.toMixed K).symm (u l)) := rfl

open scoped Classical in
/-- **The inner product of the euclidean tuple space is the sum of the local trace forms.** -/
theorem inner_toMixedPi {ι : Type*} [Fintype ι] (u v : ι → mixedSpace K) :
    inner ℝ (toMixedPi K ι u) (toMixedPi K ι v) = ∑ l, mixedTrace K (star (u l) * v l) := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [inner_euclidean]
  congr 1

section Matrices

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

omit [NumberField K] [DecidableEq κ] in
/-- **The mixed-space identity behind the adjoint.** Pairing two images of the matrix `Y` against
the trace form is pairing against the Gram matrix `Y Yᴴ`. -/
theorem sum_star_mulVec (Y : Matrix κ ι (mixedSpace K)) (u v : κ → mixedSpace K) :
    ∑ l, star ((Yᵀ *ᵥ u) l) * ((Yᵀ *ᵥ v) l) = ∑ j, star ((((Y * Yᴴ)ᵀ) *ᵥ u) j) * v j := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum, star_star]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  exact Finset.sum_congr rfl fun l _ ↦ by ring

open scoped Classical in
/-- The `ℝ`-linear map of euclidean tuple spaces attached to a matrix over the mixed space. -/
@[expose] def mixedPiMap (Y : Matrix κ ι (mixedSpace K)) : mixedPi K κ →ₗ[ℝ] mixedPi K ι :=
  (toMixedPi K ι).toLinearMap ∘ₗ (LinearMap.restrictScalars ℝ (Matrix.toLin' Yᵀ)) ∘ₗ
    (toMixedPi K κ).symm.toLinearMap

open scoped Classical in
/-- The self-adjoint endomorphism `Y Yᴴ` attached to a matrix over the mixed space. -/
@[expose] def mixedPiEnd (Y : Matrix κ ι (mixedSpace K)) : mixedPi K κ →ₗ[ℝ] mixedPi K κ :=
  (toMixedPi K κ).toLinearMap ∘ₗ (LinearMap.restrictScalars ℝ (Matrix.toLin' ((Y * Yᴴ)ᵀ))) ∘ₗ
    (toMixedPi K κ).symm.toLinearMap

open scoped Classical in
/-- **The Gram form of `Y` is pairing against `Y Yᴴ`.** -/
theorem inner_mixedPiMap (Y : Matrix κ ι (mixedSpace K)) (x y : mixedPi K κ) :
    inner ℝ (mixedPiMap Y x) (mixedPiMap Y y) = inner ℝ (mixedPiEnd Y x) y := by
  set u := (toMixedPi K κ).symm x with hu
  set v := (toMixedPi K κ).symm y with hv
  have hx : x = toMixedPi K κ u := by rw [hu]; simp
  have hy : y = toMixedPi K κ v := by rw [hv]; simp
  rw [mixedPiMap, mixedPiEnd]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearMap.coe_restrictScalars, Matrix.toLin'_apply, ← hu, ← hv]
  rw [inner_toMixedPi, hy, inner_toMixedPi, ← map_sum, ← map_sum, sum_star_mulVec]

open scoped Classical in
/-- **The determinant of the Gram endomorphism is the algebra norm of `det (Y Yᴴ)`.** -/
theorem det_mixedPiEnd (Y : Matrix κ ι (mixedSpace K)) :
    LinearMap.det (mixedPiEnd Y) = Algebra.norm ℝ (Y * Yᴴ).det := by
  rw [mixedPiEnd, LinearMap.det_conj, LinearMap.det_restrictScalars, LinearMap.det_toLin',
    Matrix.det_transpose]

end Matrices

section Archimedean

open exteriorPower

variable {ι : Type*} [Fintype ι] [LinearOrder ι] {m : ℕ}

open scoped Classical in
/-- **The algebra norm on the mixed space.** -/
theorem norm_mixedSpace (z : mixedSpace K) :
    Algebra.norm ℝ z = (∏ w, z.1 w) * ∏ w, Complex.normSq (z.2 w) := by
  rw [Algebra.norm_prod, Algebra.norm_pi, Algebra.norm_pi]
  congr 1
  · refine Finset.prod_congr rfl fun w _ ↦ ?_
    have h := Algebra.norm_algebraMap (R := ℝ) (S := ℝ) (z.1 w)
    rwa [Module.finrank_self, pow_one, Algebra.algebraMap_self_apply] at h
  · exact Finset.prod_congr rfl fun w _ ↦ Algebra.norm_complex_apply _

open scoped Classical in
/-- **Schmidt's Lemma 4, the local content.** The algebra norm of the Gram determinant of the
mixed embedding of a matrix over `K` is the archimedean local factor of the Arakelov height of its
Plücker point, with each infinite place weighted by its multiplicity. -/
theorem norm_det_gram (Y : Matrix (Fin m) ι K) :
    Algebra.norm ℝ ((Y.map (mixedEmbedding K)) * (Y.map (mixedEmbedding K))ᴴ).det
      = ∏ w : InfinitePlace K,
        (∑ s : Set.powersetCard ι m, w (plucker m Y.row s) ^ 2) ^ w.mult := by
  classical
  set p : Set.powersetCard ι m → K := plucker m Y.row with hp
  set z : mixedSpace K := ∑ s, (mixedEmbedding K (p s)) * star (mixedEmbedding K (p s)) with hz
  have hdet : ((Y.map (mixedEmbedding K)) * (Y.map (mixedEmbedding K))ᴴ).det = z := by
    rw [Matrix.det_mul_conjTranspose_self_eq_sum, hz]
    exact Finset.sum_congr rfl fun s _ ↦ by rw [Matrix.plucker_row_map]
  have h1 : ∀ w : {w : InfinitePlace K // IsReal w},
      z.1 w = ∑ s : Set.powersetCard ι m, w.1 (p s) ^ 2 := by
    intro w
    rw [hz]
    simp only [Prod.fst_sum, Finset.sum_apply, Prod.fst_mul, Pi.mul_apply, star_fst]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    have hw : w.1 (p s) = ‖(mixedEmbedding K (p s)).1 ⟨w.1, w.2⟩‖ := by
      rw [← normAtPlace_apply_of_isReal w.2, normAtPlace_apply]
    rw [hw, Real.norm_eq_abs, sq_abs, sq]
  have h2 : ∀ w : {w : InfinitePlace K // IsComplex w},
      Complex.normSq (z.2 w) = (∑ s : Set.powersetCard ι m, w.1 (p s) ^ 2) ^ 2 := by
    intro w
    have hzw : z.2 w = ((∑ s : Set.powersetCard ι m, w.1 (p s) ^ 2 : ℝ) : ℂ) := by
      rw [hz]
      simp only [Prod.snd_sum, Finset.sum_apply, Prod.snd_mul, Pi.mul_apply, star_snd]
      push_cast
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      have hw : w.1 (p s) = ‖(mixedEmbedding K (p s)).2 ⟨w.1, w.2⟩‖ := by
        rw [← normAtPlace_apply_of_isComplex w.2, normAtPlace_apply]
      rw [hw, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [hzw, Complex.normSq_ofReal, sq]
  rw [hdet, norm_mixedSpace, InfinitePlace.prod_eq_prod_mul_prod]
  congr 1
  · exact Finset.prod_congr rfl fun w _ ↦ by rw [h1 w, InfinitePlace.mult_isReal, pow_one]
  · exact Finset.prod_congr rfl fun w _ ↦ by rw [h2 w, InfinitePlace.mult_isComplex]

end Archimedean

end NumberField.mixedEmbedding

end

end
