/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.FieldMinkowski
public import QuantitativeSubspace.TwistedSubspaceHeight
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- Used only inside proofs.
import ArithmeticHeights.Extension
import Mathlib.NumberTheory.NumberField.Discriminant.Basic

/-!
# Minkowski's theorem for a twisted height over a number field

D. Roy and J. L. Thunder, *An absolute Siegel's lemma*, J. reine angew. Math. **476** (1996),
1–26, Lemma 5.2: for a twist `A` of `Kⁿ` there is a basis `x₁, …, xₙ` of `Kⁿ` with

```text
∏ᵢ H_A(xᵢ)  ≤  c(K, n) · |det A|_𝔸,
```

heights relative to `K`. RT deduce it from Bombieri–Vaaler's adelic Minkowski theorem; here it is
`NumberField.prod_successiveMinimum_pow_mul_measure_le` of `DiophantineApproximation`, applied to

* the **lattice** of the points `x` with `A_v x ∈ 𝒪_vⁿ` at every finite place `v`, which is the
  approximation module of `DiophantineApproximation/ApproximationDomain.lean` for the rows of the
  finite components, at level `1` with exponents `0`, so that its covolume is
  `∏_v |det A_v|_v · covol(𝒪_K)ⁿ` (`NumberField.covolume_approxLattice`);
* the **body** `{z : ‖A_w z_w‖_∞ ≤ 1 at every infinite place w}`, the preimage of the unit box of
  `ApproximationVolume.lean` under the `mixedSpace K`-linear map of the archimedean components, of
  volume `(2^{r₁} π^{r₂})ⁿ / ∏_φ |det A_φ|`.

A point of the lattice in `μ` times the body has twisted height at most `(√n μ)^d`: its finite
factors are at most `1`, and the ℓ² norm of `A_φ x` is at most `√n` times its largest coordinate.
With `covol(𝒪_K) = 2^{-r₂} √|D_K|` the constant is `((2/π)^{r₂} √|D_K| · √n^d)ⁿ`, stated as the
cleaner `(√|D_K| · √n^d)ⁿ`.

## Main results

* `NumberField.Twist.exists_linearIndependent_prod_mulHeight_le`: RT96 Lemma 5.2, relative to `K`.
* `NumberField.Twist.exists_linearIndependent_prod_absMulHeight_le`: the same for the absolute
  heights, against `|det A|_𝔸`.

## Implementation notes

⚠ **The constant is `c(K)ⁿ · n^{dn/2}`, not `c(K)ⁿ`.** The factor `n^{dn/2}` is the price of the
box inside the ℓ² ball, as in RT's own volume estimate (their `(r + 1)^{d/r}` in Thm 5.1). It is
harmless where the lemma is used, RT96 Prop. 5.3: there `n = r + 1` and the bound is taken to the
power `2 / (r (r + 1))`, which sends `n^{dn/2}` to `1` as `r → ∞`.

⚠ **The infinite components are not `K`-rational**, so the body is not an approximation body:
its matrix over the mixed space has the real parts of the components at the real places (where
`arch_conjugate` makes them real) and the components themselves at the complex places, through
the chosen embedding `w.embedding`. A complex embedding `φ` of `K` reads the coordinate of its
place `w = mk φ` directly when `φ = w.embedding`, and conjugated otherwise, with the same norm.

This is milestone Q2.2b of `QuantitativeSubspace/README.md`.
-/

@[expose] public section

open Finset Function Module Matrix NumberField.mixedEmbedding NumberField.InfinitePlace
  MeasureTheory

namespace NumberField.Twist

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (A : Twist K ι)

open scoped Pointwise

/-! ### The lattice: the finite components -/

open scoped Classical in
/-- The rows of the finite components as linear forms, indexed by absolute values as the forms
of an approximation domain are; the coordinate forms at an absolute value that is not a finite
place. -/
noncomputable def finForms (a : AbsoluteValue K ℝ) (i : ι) : Dual K (ι → K) :=
  if h : IsFinitePlace a then (LinearMap.proj i).comp (Matrix.toLin' (A.fin ⟨a, h⟩))
  else LinearMap.proj i

theorem finForms_apply (v : FinitePlace K) (i : ι) (x : ι → K) :
    A.finForms v.1 i x = (A.fin v *ᵥ x) i := by
  unfold finForms
  split_ifs with h
  · rfl
  · exact absurd v.2 h

theorem linearIndependent_finForms (v : FinitePlace K) :
    LinearIndependent K (A.finForms v.1) := by
  set ψ : Dual K (ι → K) →ₗ[K] (ι → K) :=
    LinearMap.pi fun j ↦ Module.Dual.eval K (ι → K) (Pi.single j 1)
  have hrows : LinearIndependent K fun i ↦ A.fin v i :=
    Matrix.linearIndependent_rows_iff_isUnit.2
      ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (A.fin_det_ne_zero v)))
  refine LinearIndependent.of_comp ψ ?_
  convert hrows using 1
  funext i j
  simp [ψ, finForms_apply]

/-- The finite places at which the twist is not the identity. -/
noncomputable def badFinset : Finset (FinitePlace K) :=
  A.finite_setOf_fin_ne_one.toFinset

theorem fin_eq_one_of_notMem {v : FinitePlace K} (hv : v ∉ A.badFinset) : A.fin v = 1 := by
  by_contra h
  exact hv ((Set.Finite.mem_toFinset _).2 h)

/-- **The lattice of a twist**: the points `x` of `Kⁿ` with `A_v x` integral at every finite place
`v`, as the approximation module of the rows of the finite components, at level `1`. -/
noncomputable def lattice : Submodule (𝓞 K) (ι → K) :=
  approxModule A.badFinset A.finForms 0 1

theorem apply_le_one_of_mem_lattice {x : ι → K} (hx : x ∈ A.lattice) (v : FinitePlace K)
    (i : ι) : v ((A.fin v *ᵥ x) i) ≤ 1 := by
  by_cases hv : v ∈ A.badFinset
  · have := hx.1 v hv i
    rwa [finForms_apply, Pi.zero_apply, Pi.zero_apply, Real.rpow_zero] at this
  · rw [A.fin_eq_one_of_notMem hv, Matrix.one_mulVec]
    exact hx.2 v hv i

private theorem hL : ∀ v ∈ A.badFinset, LinearIndependent K (A.finForms v.1) :=
  fun v _ ↦ A.linearIndependent_finForms v

open scoped Classical in
instance discreteTopology_lattice : DiscreteTopology A.lattice.mixedImage :=
  discreteTopology_approxLattice (hL A) 0 one_ne_zero

open scoped Classical in
instance isZLattice_lattice : IsZLattice ℝ A.lattice.mixedImage :=
  have : DiscreteTopology (approxLattice A.badFinset A.finForms 0 1) := A.discreteTopology_lattice
  isZLattice_approxLattice (hL A) 0 one_ne_zero

private theorem floorValue_one (v : FinitePlace K) : v.floorValue 1 = 1 := by
  simp [FinitePlace.floorValue]

theorem hasFiniteMulSupport_apply_det_fin :
    (fun v : FinitePlace K ↦ v (A.fin v).det).HasFiniteMulSupport :=
  A.finite_setOf_fin_ne_one.subset fun v hv h ↦ hv (by simp [h])

open scoped Classical in
/-- **The covolume of the lattice of a twist**: `∏_v |det A_v|_v` times that of `(𝓞 K)ⁿ`. -/
theorem covolume_lattice :
    ZLattice.covolume A.lattice.mixedImage =
      (∏ᶠ v : FinitePlace K, v (A.fin v).det) *
        ZLattice.covolume (mixedEmbedding.integerLattice K) ^ Fintype.card ι := by
  have := covolume_approxLattice (hL A) 0 one_pos
  rw [approxLattice] at this
  rw [lattice, this]
  congr 1
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := A.badFinset) fun v hv ↦ by
    by_contra h
    exact hv (by simp [A.fin_eq_one_of_notMem h])]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  have hpi : LinearMap.pi (A.finForms v.1) = Matrix.toLin' (A.fin v) := by
    ext x i
    simp [finForms_apply]
  simp [hpi, LinearMap.det_toLin', floorValue_one]

/-! ### The body: the infinite components -/

/-- At a real embedding the component of a twist is real. -/
theorem ofReal_re_arch {φ : K →+* ℂ} (hφ : ComplexEmbedding.IsReal φ) (i j : ι) :
    (((A.arch φ i j).re : ℝ) : ℂ) = A.arch φ i j := by
  have h := congrFun (congrFun (A.arch_conjugate φ) i) j
  rw [ComplexEmbedding.isReal_iff.mp hφ] at h
  exact Complex.conj_eq_iff_re.mp h.symm

/-- The infinite components assembled into a matrix over the mixed space: real parts at the real
places, the components at `w.embedding` at the complex places. -/
noncomputable def mixedMatrix : Matrix ι ι (mixedSpace K) :=
  Matrix.of fun i j ↦ ((fun w ↦ (A.arch w.1.embedding i j).re), fun w ↦ A.arch w.1.embedding i j)

theorem placeHom_mixedMatrix (w : InfinitePlace K) (i j : ι) :
    placeHom w (A.mixedMatrix i j) = A.arch w.embedding i j := by
  by_cases hw : IsReal w
  · simpa [placeHom, hw, mixedMatrix] using A.ofReal_re_arch (isReal_iff.mp hw) i j
  · simp [placeHom, hw, mixedMatrix]

/-- The `ℝ`-linear map of the infinite components on `(K ⊗ ℝ)ⁿ`. -/
noncomputable def mixedMap : (ι → mixedSpace K) →ₗ[ℝ] (ι → mixedSpace K) :=
  (Matrix.toLin' A.mixedMatrix).restrictScalars ℝ

theorem placeHom_mixedMap (w : InfinitePlace K) (x : ι → K) (i : ι) :
    placeHom w (A.mixedMap (fun j ↦ mixedEmbedding K (x j)) i) =
      (A.arch w.embedding *ᵥ (w.embedding ∘ x)) i := by
  simp [mixedMap, Matrix.mulVec, dotProduct, map_sum, placeHom_mixedMatrix,
    placeHom_mixedEmbedding]

/-- A complex embedding reads the coordinate of its place, conjugated or not. -/
theorem norm_arch_mulVec (φ : K →+* ℂ) (x : ι → K) (i : ι) :
    ‖(A.arch φ *ᵥ (φ ∘ x)) i‖ =
      normAtPlace (InfinitePlace.mk φ) (A.mixedMap (fun j ↦ mixedEmbedding K (x j)) i) := by
  rw [normAtPlace_eq_norm_placeHom, placeHom_mixedMap]
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · rw [h]
  · rw [h, A.arch_conjugate]
    have : (ComplexEmbedding.conjugate φ ∘ x) = starRingEnd ℂ ∘ (φ ∘ x) := rfl
    rw [this, ← RingHom.map_mulVec, Complex.norm_conj]

/-- The absolute determinant of the map of the infinite components is the archimedean part of
`|det A|_𝔸`. -/
theorem abs_det_mixedMap :
    |LinearMap.det A.mixedMap| = ∏ φ : K →+* ℂ, ‖(A.arch φ).det‖ := by
  have hdet : ∀ w : InfinitePlace K, placeHom w A.mixedMatrix.det = (A.arch w.embedding).det :=
    fun w ↦ by
      rw [RingHom.map_det]
      congr 1
      ext i j
      simp [RingHom.mapMatrix_apply, placeHom_mixedMatrix]
  have hφ : ∀ φ : K →+* ℂ, ‖(A.arch (InfinitePlace.mk φ).embedding).det‖ = ‖(A.arch φ).det‖ := by
    intro φ
    rcases InfinitePlace.embedding_mk_eq φ with h | h
    · rw [h]
    · rw [h, A.arch_conjugate, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Complex.norm_conj]
  rw [mixedMap, LinearMap.det_restrictScalars, LinearMap.det_toLin',
    abs_algebraNorm_eq_norm, mixedEmbedding.norm_apply]
  simp_rw [normAtPlace_eq_norm_placeHom, hdet]
  rw [← prod_embeddings_eq (fun w : InfinitePlace K ↦ ‖(A.arch w.embedding).det‖)]
  exact Finset.prod_congr rfl fun φ _ ↦ hφ φ

theorem det_mixedMap_ne_zero : LinearMap.det A.mixedMap ≠ 0 := by
  rw [← abs_pos, abs_det_mixedMap]
  exact Finset.prod_pos fun φ _ ↦ norm_pos_iff.mpr (A.arch_det_ne_zero φ)

open scoped Classical in
/-- **The body of a twist**: the points of `(K ⊗ ℝ)ⁿ` that the infinite components send into the
unit ball of the sup norm. -/
noncomputable def body : Set (ι → mixedSpace K) :=
  A.mixedMap ⁻¹' Metric.closedBall 0 1

open scoped Classical in
omit [DecidableEq ι] in
/-- The unit ball of the sup norm on `(K ⊗ ℝ)ⁿ` is a product of unit boxes. -/
theorem pi_mixedBox_one :
    (Set.univ.pi fun _ : ι ↦ mixedBox (K := K) fun _ ↦ 1) =
      Metric.closedBall (0 : ι → mixedSpace K) 1 := by
  ext z
  simp only [Set.mem_pi, Set.mem_univ, true_implies, mixedBox, Set.mem_ofPred_eq,
    mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one, norm_eq_sup'_normAtPlace,
    Finset.sup'_le_iff, Finset.mem_univ, true_implies]

open scoped Classical in
theorem convex_body : Convex ℝ A.body :=
  (convex_closedBall 0 1).linear_preimage A.mixedMap

open scoped Classical in
theorem neg_mem_body {z : ι → mixedSpace K} (hz : z ∈ A.body) : -z ∈ A.body := by
  simpa [body] using hz

open scoped Classical in
theorem isClosed_body : IsClosed A.body :=
  Metric.isClosed_closedBall.preimage (LinearMap.continuous_of_finiteDimensional _)

open scoped Classical in
theorem body_mem_nhds_zero : A.body ∈ nhds 0 := by
  refine (LinearMap.continuous_of_finiteDimensional A.mixedMap).continuousAt.preimage_mem_nhds ?_
  rw [map_zero]
  exact Metric.closedBall_mem_nhds 0 one_pos

open scoped Classical in
theorem isBounded_body : Bornology.IsBounded A.body := by
  set e := LinearMap.equivOfDetNeZero A.mixedMap A.det_mixedMap_ne_zero
  have : A.body = e.symm '' Metric.closedBall 0 1 := by
    rw [body, LinearEquiv.image_symm_eq_preimage]
    rfl
  rw [this]
  exact (LinearMap.toContinuousLinearMap e.symm.toLinearMap).lipschitzWith.isBounded_image
    Metric.isBounded_closedBall

open scoped Classical in
/-- **The volume of the body**: `(2^{r₁} π^{r₂})ⁿ / ∏_φ |det A_φ|`. -/
theorem volume_body :
    (volume A.body).toReal =
      (2 ^ nrRealPlaces K * Real.pi ^ nrComplexPlaces K) ^ Fintype.card ι /
        ∏ φ : K →+* ℂ, ‖(A.arch φ).det‖ := by
  rw [body, ← pi_mixedBox_one, Measure.addHaar_preimage_linearMap _ A.det_mixedMap_ne_zero,
    volume_pi_pi]
  simp_rw [volume_mixedBox _ fun _ ↦ zero_le_one, one_pow, Finset.prod_const_one, mul_one]
  rw [Finset.prod_const, Finset.card_univ, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_ofReal (by positivity), abs_inv,
    abs_det_mixedMap, inv_mul_eq_div]

/-! ### Heights of the points of the lattice in a dilate of the body -/

open scoped Classical in
/-- A point of `μ` times the body has archimedean factors at most `√n μ`. -/
theorem archFactor_le_of_mem_smul_body {x : ι → K} {μ : ℝ} (hμ : 0 ≤ μ)
    (hx : (fun j ↦ mixedEmbedding K (x j)) ∈ μ • A.body) (φ : K →+* ℂ) :
    A.archFactor φ x ≤ √(Fintype.card ι) * μ := by
  obtain ⟨b, hb, hbx⟩ := Set.mem_smul_set.mp hx
  have hb' : A.mixedMap b ∈ Set.univ.pi fun _ : ι ↦ mixedBox (K := K) fun _ ↦ 1 := by
    rw [pi_mixedBox_one]; exact hb
  have hcoord : ∀ i, ‖(A.arch φ *ᵥ (φ ∘ x)) i‖ ≤ μ := by
    intro i
    rw [norm_arch_mulVec, ← hbx, map_smul, Pi.smul_apply, normAtPlace_smul, abs_of_nonneg hμ]
    exact mul_le_of_le_one_right hμ (hb' i (Set.mem_univ i) _)
  have hφ : φ.comp (algebraMap K K) = φ := by rw [Algebra.algebraMap_self, RingHom.comp_id]
  rw [archFactor, hφ, EuclideanSpace.norm_eq, ← Real.sqrt_sq hμ,
    ← Real.sqrt_mul (Nat.cast_nonneg _)]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ‖(WithLp.toLp 2 (A.arch φ *ᵥ (φ ∘ x)) : EuclideanSpace ℂ ι) i‖ ^ 2
      ≤ ∑ _i : ι, μ ^ 2 :=
        Finset.sum_le_sum fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hcoord i) 2
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- A point of the lattice has finite factors at most `1`. -/
theorem finFactor_le_one_of_mem_lattice {x : ι → K} (hx : x ∈ A.lattice) (v : FinitePlace K) :
    A.finFactor v x ≤ 1 := by
  rw [finFactor, FinitePlace.under_self, Algebra.algebraMap_self]
  refine Real.iSup_le (fun i ↦ ?_) zero_le_one
  simpa using A.apply_le_one_of_mem_lattice hx v i

open scoped Classical in
/-- **A point of the lattice in `μ` times the body has twisted height at most `(√n μ)^d`.** -/
theorem mulHeight_le_of_mem_lattice {x : ι → K} (hx0 : x ≠ 0) (hx : x ∈ A.lattice) {μ : ℝ}
    (hμ : 0 ≤ μ) (hxB : (fun j ↦ mixedEmbedding K (x j)) ∈ μ • A.body) :
    A.mulHeight x ≤ (√(Fintype.card ι) * μ) ^ finrank ℚ K := by
  have hf := A.hasFiniteMulSupport_finFactor (E := K) hx0
  have hfin : ∏ᶠ v : FinitePlace K, A.finFactor v x ≤ 1 := by
    rw [finprod_eq_prod_of_mulSupport_subset _ (Set.Finite.coe_toFinset hf).symm.subset]
    exact Finset.prod_le_one₀ (fun v _ ↦ A.finFactor_nonneg v x)
      fun v _ ↦ A.finFactor_le_one_of_mem_lattice hx v
  rw [mulHeight]
  calc (∏ φ : K →+* ℂ, A.archFactor φ x) * ∏ᶠ v : FinitePlace K, A.finFactor v x
      ≤ (∏ _φ : K →+* ℂ, √(Fintype.card ι) * μ) * 1 :=
        mul_le_mul (Finset.prod_le_prod₀ (fun φ _ ↦ A.archFactor_nonneg φ x)
          fun φ _ ↦ A.archFactor_le_of_mem_smul_body hμ hxB φ) hfin
          (finprod_nonneg fun v ↦ A.finFactor_nonneg v x)
          (Finset.prod_nonneg fun _ _ ↦ by positivity)
    _ = _ := by rw [mul_one, Finset.prod_const, Finset.card_univ, Embeddings.card]

/-! ### RT96 Lemma 5.2 -/

private theorem two_pow_mul_le (K : Type*) [Field K] [NumberField K] :
    (2 : ℝ) ^ finrank ℚ K * (2⁻¹) ^ nrComplexPlaces K ≤
      2 ^ nrRealPlaces K * Real.pi ^ nrComplexPlaces K := by
  rw [← card_add_two_mul_card_eq_rank, pow_add, pow_mul, mul_assoc, ← mul_pow]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) ?_ _) (by positivity)
  linarith [Real.two_le_pi]

/-- **Minkowski's theorem for a twisted height over `K`** (RT96 Lemma 5.2): `Kⁿ` has a basis
`x₁, …, xₙ` with `∏ H_A(xᵢ) ≤ (√|D_K| · √n^d)ⁿ · |det A|_𝔸`, heights and `|det A|_𝔸` relative
to `K`. -/
theorem exists_linearIndependent_prod_mulHeight_le :
    ∃ x : Fin (Fintype.card ι) → ι → K, LinearIndependent K x ∧
      ∏ k, A.mulHeight (x k) ≤
        (√|(discr K : ℝ)| * √(Fintype.card ι) ^ finrank ℚ K) ^ Fintype.card ι *
          ((∏ φ : K →+* ℂ, ‖(A.arch φ).det‖) * ∏ᶠ v : FinitePlace K, v (A.fin v).det) := by
  classical
  have hB₂ : (interior A.body).Nonempty :=
    ⟨0, mem_interior_iff_mem_nhds.2 A.body_mem_nhds_zero⟩
  obtain ⟨x, hxind, hx⟩ := exists_linearIndependent_mem_smul_successiveMinimum A.lattice
    A.convex_body (fun _ ↦ A.neg_mem_body) hB₂ A.isBounded_body A.isClosed_body
  have hup := prod_successiveMinimum_pow_mul_measure_le A.lattice volume A.convex_body
    (fun _ ↦ A.neg_mem_body) hB₂ A.isBounded_body
  rw [A.volume_body, covolume_lattice, covolume_integerLattice] at hup
  refine ⟨x, hxind, ?_⟩
  have hμ : ∀ k, 0 ≤ successiveMinimum A.lattice A.body k := successiveMinimum_nonneg _ _
  have hH : ∏ k, A.mulHeight (x k) ≤ (√(Fintype.card ι) ^ finrank ℚ K) ^ Fintype.card ι *
      (∏ i ∈ Finset.range (Fintype.card ι), successiveMinimum A.lattice A.body i) ^
        finrank ℚ K := by
    calc ∏ k, A.mulHeight (x k)
        ≤ ∏ k : Fin (Fintype.card ι),
            (√(Fintype.card ι) * successiveMinimum A.lattice A.body k) ^ finrank ℚ K :=
          Finset.prod_le_prod₀ (fun k _ ↦ A.mulHeight_nonneg _) fun k _ ↦
            A.mulHeight_le_of_mem_lattice (hxind.ne_zero k) (hx k).1 (hμ k) (hx k).2
      _ = _ := by
          rw [Finset.prod_pow, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
            Fintype.card_fin, mul_pow, ← pow_mul, ← pow_mul, mul_comm (Fintype.card ι),
            Fin.prod_univ_eq_prod_range (fun i ↦ successiveMinimum A.lattice A.body i)]
  have hk := two_pow_mul_le K
  have hD : 0 < ∏ φ : K →+* ℂ, ‖(A.arch φ).det‖ :=
    Finset.prod_pos fun φ _ ↦ norm_pos_iff.mpr (A.arch_det_ne_zero φ)
  have hP : 0 ≤ ∏ᶠ v : FinitePlace K, v (A.fin v).det := finprod_nonneg fun v ↦ apply_nonneg _ _
  have hc : (0 : ℝ) < 2 ^ nrRealPlaces K * Real.pi ^ nrComplexPlaces K := by positivity
  rw [pow_mul] at hup
  generalize ∏ φ : K →+* ℂ, ‖(A.arch φ).det‖ = D at hD hup ⊢
  generalize ∏ᶠ v : FinitePlace K, v (A.fin v).det = P at hP hup ⊢
  generalize (2 : ℝ) ^ nrRealPlaces K * Real.pi ^ nrComplexPlaces K = c at hc hup hk
  generalize (∏ i ∈ Finset.range (Fintype.card ι), successiveMinimum A.lattice A.body i) ^
    finrank ℚ K = m at hup hH
  generalize ∏ k, A.mulHeight (x k) = H at hH ⊢
  generalize Fintype.card ι = n at hup hH ⊢
  have hs : 0 ≤ √(n : ℝ) ^ finrank ℚ K := by positivity
  have h1 : m * c ^ n ≤ (2 ^ finrank ℚ K) ^ n * (P * (2⁻¹ ^ nrComplexPlaces K *
      √|(discr K : ℝ)|) ^ n) * D := by
    calc m * c ^ n = m * (c ^ n / D) * D := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hup hD.le
  have h2 : (2 ^ finrank ℚ K * 2⁻¹ ^ nrComplexPlaces K / c) ^ n ≤ 1 :=
    pow_le_one₀ (by positivity) ((div_le_one hc).2 hk)
  calc H ≤ (√(n : ℝ) ^ finrank ℚ K) ^ n * m := hH
    _ ≤ (√|(discr K : ℝ)| * √(n : ℝ) ^ finrank ℚ K) ^ n * (D * P) *
          (2 ^ finrank ℚ K * 2⁻¹ ^ nrComplexPlaces K / c) ^ n := by
        rw [div_pow, ← mul_div_assoc, le_div_iff₀ (pow_pos hc n), mul_assoc]
        calc (√(n : ℝ) ^ finrank ℚ K) ^ n * (m * c ^ n)
            ≤ (√(n : ℝ) ^ finrank ℚ K) ^ n * ((2 ^ finrank ℚ K) ^ n * (P * (2⁻¹ ^
                nrComplexPlaces K * √|(discr K : ℝ)|) ^ n) * D) :=
              mul_le_mul_of_nonneg_left h1 (pow_nonneg hs n)
          _ = _ := by ring
    _ ≤ (√|(discr K : ℝ)| * √(n : ℝ) ^ finrank ℚ K) ^ n * (D * P) * 1 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := mul_one _

section Absolute

variable {ι : Type*} [Fintype ι] [LinearOrder ι] (A : Twist K ι)
  (Ω : Type*) [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]

/-- **Minkowski's theorem for a twisted height, absolutely** (RT96 Lemma 5.2): `Kⁿ` has a basis
`x₁, …, xₙ` whose absolute twisted heights satisfy
`∏ H_A(xᵢ) ≤ (|D_K|^{1/(2d)} · √n)ⁿ · |det A|_𝔸`. -/
theorem exists_linearIndependent_prod_absMulHeight_le :
    ∃ x : Fin (Fintype.card ι) → ι → K, LinearIndependent K x ∧
      ∏ k, A.absMulHeight (algebraMap K Ω ∘ x k) ≤
        (√|(discr K : ℝ)| ^ ((finrank ℚ K : ℝ))⁻¹ * √(Fintype.card ι)) ^ Fintype.card ι *
          A.absDet := by
  obtain ⟨x, hx, h⟩ := A.exists_linearIndependent_prod_mulHeight_le
  refine ⟨x, hx, ?_⟩
  have hd : finrank ℚ K ≠ 0 := Module.finrank_pos.ne'
  have hR : 0 ≤ (∏ φ : K →+* ℂ, ‖(A.arch φ).det‖) * ∏ᶠ v : FinitePlace K, v (A.fin v).det :=
    mul_nonneg (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
      (finprod_nonneg fun v ↦ apply_nonneg _ _)
  have hC : 0 ≤ √|(discr K : ℝ)| * √(Fintype.card ι) ^ finrank ℚ K := by positivity
  simp_rw [absMulHeight_algebraMap]
  rw [Real.finsetProd_rpow _ _ fun k _ ↦ A.mulHeight_nonneg _, absDet]
  calc (∏ k, A.mulHeight (x k)) ^ ((finrank ℚ K : ℝ))⁻¹
      ≤ ((√|(discr K : ℝ)| * √(Fintype.card ι) ^ finrank ℚ K) ^ Fintype.card ι *
          ((∏ φ : K →+* ℂ, ‖(A.arch φ).det‖) * ∏ᶠ v : FinitePlace K, v (A.fin v).det)) ^
          ((finrank ℚ K : ℝ))⁻¹ :=
        Real.rpow_le_rpow (Finset.prod_nonneg fun k _ ↦ A.mulHeight_nonneg _) h (by positivity)
    _ = _ := by
        have hpow : ((√|(discr K : ℝ)| * √(Fintype.card ι) ^ finrank ℚ K) ^ Fintype.card ι) ^
            ((finrank ℚ K : ℝ))⁻¹ =
            (√|(discr K : ℝ)| ^ ((finrank ℚ K : ℝ))⁻¹ * √(Fintype.card ι)) ^ Fintype.card ι := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hC, mul_comm (Fintype.card ι : ℝ),
            Real.rpow_mul hC, Real.rpow_natCast,
            Real.mul_rpow (Real.sqrt_nonneg _) (by positivity),
            Real.pow_rpow_inv_natCast (Real.sqrt_nonneg _) hd]
        rw [Real.mul_rpow (pow_nonneg hC _) hR, hpow]

end Absolute

end NumberField.Twist
