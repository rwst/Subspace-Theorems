/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.FinitePlaceValues
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

-- Used only inside proofs.
import ArithmeticHeights.FinitePlaceIdeal
import ArithmeticHeights.MixedLattice
import ArithmeticHeights.PseudoBasis
import DiophantineApproximation.SAdicHeight
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
import Mathlib.NumberTheory.NumberField.ProductFormula

/-!
# The covolume of an `𝓞 K`-lattice, read at the finite places

For a number field `K` and a finitely generated `𝓞 K`-submodule `Λ` of `Kⁱ` spanning it over `K`,
the image of `Λ` under the mixed embedding is a lattice in `(K ⊗ ℝ)ⁱ = ι → mixedSpace K`, and

```text
covol Λ  =  (∏ᶠ_{v ∤ ∞} B v)⁻¹ · covol (𝓞 K) ^ #ι,
```

where `B v` is the largest value of `v` on the determinants `det (x 1, …, x #ι)` of tuples of
vectors of `Λ`. The factor `(∏ᶠ B v)⁻¹` is the generalized index of `Λ` in `(𝓞 K)ⁱ` —
generalized because `Λ` need not lie in `(𝓞 K)ⁱ` — and the statement computes it one place at a
time without ever forming a quotient.

## Main definitions

* `Submodule.mixedImage`: an `𝓞 K`-submodule of `Kⁱ` read in `ι → mixedSpace K`.

## Main results

* `Submodule.covolume_mixedImage`: the display above.
* `Submodule.discreteTopology_mixedImage` and `Submodule.isZLattice_mixedImage`: the image is a
  lattice.
* `Submodule.exists_integral_pseudoBasis`: `Λ = ⊕ J i • y i` for a `K`-basis `y` and nonzero
  integral ideals `J i`.
* `Submodule.exists_basis_mixedImage_of_pseudoBasis`: the covolume of such a lattice is
  `|N (det y)| ∏ N (J i)` times that of `(𝓞 K)ⁱ`.
* `NumberField.mixedEmbedding.abs_algebraNorm_eq_norm`: the real norm of the mixed space is, up to
  sign, Mathlib's `mixedEmbedding.norm`, the product of the local norms.
* `NumberField.mixedEmbedding.instBorelSpacePi` and
  `NumberField.mixedEmbedding.instIsAddHaarMeasurePi`: the Borel structure and the Haar measure of
  `ι → mixedSpace K`.

## Implementation notes

⚠ **The covolume is read from maximal determinants, and a pseudo-basis enters only the proof.** For
`Λ = ⊕ J i • y i` the covolume is `|N (det y)| ∏ N (J i)` times that of `(𝓞 K)ⁱ` — the ideal
lattices of Mathlib's `fractionalIdealLatticeBasis` in the coordinates, then the `mixedSpace
K`-linear map of `y` — and at each finite place `v (det y) ∏ max_k v (g i k)` is the largest value
of `v` on the determinants of tuples of `Λ`, for generators `g i` of `J i`. The product formula
and `NumberField.FinitePlace.finprod_iSup_eq_inv_absNorm` then turn the two norms into
`(∏ᶠ B v)⁻¹`. So a caller who knows `Λ` only through local conditions — Layer 4.1's approximation
module — never sees a pseudo-basis, a localization or an index.

⚠ **The ambient is `ι → mixedSpace K`, not `ArithmeticHeights`' euclidean `mixedPi K ι`.** Layer
4.1's body is cut out by `normAtPlace`, which lives on `mixedSpace K`, and its volume is a product
of Lebesgue measures there. Mathlib's instance search does not find the Borel structure and the
Haar property of the product measure on `ι → mixedSpace K` — it fails on the `∀ i`-instances of
the factors, which it finds one at a time — so both are declared here, once, from the factors'.

⚠ **The determinant of the change of variables is one algebra norm.** The map `z ↦ yᵀ z` is
`mixedSpace K`-linear, so its real determinant is `Algebra.norm ℝ (det y)` by
`LinearMap.det_restrictScalars`; no place is looked at separately.

## References

E. Steinitz, "Rechteckige Systeme und Moduln in algebraischen Zahlkörpern", *Mathematische
Annalen* **71** (1911), 328–354, for the pseudo-basis. E. Bombieri and W. Gubler, *Heights in
Diophantine Geometry*, Cambridge University Press (2006), Lemma 7.5.7, whose finite-place volumes
this replaces.

This is Layer 4.1 (infrastructure) of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Module NumberField NumberField.mixedEmbedding NumberField.InfinitePlace Matrix
open scoped nonZeroDivisors

namespace NumberField.mixedEmbedding

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

/-- The real norm on the mixed space, up to sign, is the product of the local norms. -/
theorem abs_algebraNorm_eq_norm (z : mixedSpace K) :
    |Algebra.norm ℝ z| = mixedEmbedding.norm z := by
  classical
  rw [norm_mixedSpace, mixedEmbedding.norm_apply, prod_eq_prod_mul_prod, abs_mul,
    Finset.abs_prod, abs_of_nonneg (Finset.prod_nonneg fun w _ ↦ Complex.normSq_nonneg _)]
  congr 1
  · refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [normAtPlace_apply_of_isReal w.2, mult_isReal, pow_one, Real.norm_eq_abs]
  · refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [normAtPlace_apply_of_isComplex w.2, mult_isComplex, Complex.normSq_eq_norm_sq]

/-- The real norm of an element of `K`, read in the mixed space, is its norm over `ℚ`. -/
theorem abs_algebraNorm_mixedEmbedding (x : K) :
    |Algebra.norm ℝ (mixedEmbedding K x)| = |Algebra.norm ℚ x| := by
  rw [abs_algebraNorm_eq_norm, norm_eq_norm]

open scoped Classical in
/-- A fractional ideal has a `ℤ`-basis in the mixed space indexed by `Fin [K : ℚ]`, with the
volume of its fundamental domain `N 𝔞` times that of `𝓞 K`. -/
theorem exists_idealLatticeBasis (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ (a : Fin (finrank ℚ K) → K) (b : Basis (Fin (finrank ℚ K)) ℝ (mixedSpace K)),
      (∀ k, b k = mixedEmbedding K (a k)) ∧
      (∀ x : K, x ∈ Submodule.span ℤ (Set.range a) ↔ x ∈ (I : FractionalIdeal (𝓞 K)⁰ K)) ∧
      MeasureTheory.volume (ZSpan.fundamentalDomain b) =
        ENNReal.ofReal (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K)) *
          MeasureTheory.volume (ZSpan.fundamentalDomain (latticeBasis K)) := by
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ I) = finrank ℚ K := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, fractionalIdeal_rank, RingOfIntegers.rank]
  set e := Fintype.equivFinOfCardEq hcard
  refine ⟨basisOfFractionalIdeal K I ∘ e.symm, (fractionalIdealLatticeBasis K I).reindex e,
    fun k ↦ ?_, fun x ↦ ?_, ?_⟩
  · simp
  · rw [show Set.range (basisOfFractionalIdeal K I ∘ e.symm)
        = Set.range (basisOfFractionalIdeal K I) by
      rw [Set.range_comp, e.symm.range_eq_univ, Set.image_univ]]
    exact mem_span_basisOfFractionalIdeal K
  · rw [ZSpan.fundamentalDomain_reindex, volume_fundamentalDomain_fractionalIdealLatticeBasis]


open MeasureTheory in
open scoped Classical in
/-- The Borel structure of the space of tuples. -/
instance instBorelSpacePi : @BorelSpace (ι → mixedSpace K)
    (UniformSpace.toTopologicalSpace (self := PseudoMetricSpace.toUniformSpace)) _ := by
  have h : BorelSpace (mixedSpace K) := inferInstance
  exact @Pi.borelSpace ι (fun _ ↦ mixedSpace K) _ _ _ _ (fun _ ↦ h)

open MeasureTheory in
open scoped Classical in
/-- The volume of the space of tuples is a Haar measure. -/
instance instIsAddHaarMeasurePi : (volume : Measure (ι → mixedSpace K)).IsAddHaarMeasure := by
  have h : MeasurableAdd (mixedSpace K) := inferInstance
  exact @Measure.pi.isAddHaarMeasure ι (fun _ ↦ mixedSpace K) _ _ (fun _ ↦ volume) _ _ _ _
    (fun _ ↦ h)

open MeasureTheory in
open scoped Classical in
/-- The fundamental domain of a product basis is the product of the fundamental domains. -/
theorem fundamentalDomain_pi_basis {η : Type*} (b : ι → Basis η ℝ (mixedSpace K)) :
    ZSpan.fundamentalDomain (Pi.basis b) =
      Set.univ.pi fun i ↦ ZSpan.fundamentalDomain (b i) := by
  ext z
  simp only [ZSpan.mem_fundamentalDomain, Pi.basis_repr, Set.mem_pi, Set.mem_univ, true_implies,
    Sigma.forall]

end NumberField.mixedEmbedding

namespace Submodule

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

/-- An `𝓞 K`-submodule of `Kⁱ`, read in `(K ⊗ ℝ)ⁱ` through the mixed embedding. -/
noncomputable def mixedImage (Λ : Submodule (𝓞 K) (ι → K)) : Submodule ℤ (ι → mixedSpace K) :=
  (Λ.restrictScalars ℤ).map ((mixedEmbedding K).compLeft ι).toAddMonoidHom.toIntLinearMap

omit [NumberField K] [Fintype ι] in
/-- Membership in the image, read in `Kⁱ`. -/
theorem mem_mixedImage {Λ : Submodule (𝓞 K) (ι → K)} {z : ι → mixedSpace K} :
    z ∈ Λ.mixedImage ↔ ∃ x ∈ Λ, (fun j ↦ mixedEmbedding K (x j)) = z := by
  simp [mixedImage]
  rfl

/-- **A pseudo-basis with integral coefficient ideals**: a finitely generated `𝓞 K`-module
spanning `Kⁱ` is `⊕ J i • y i` for a `K`-basis `y` and nonzero ideals `J i` of `𝓞 K`. -/
theorem exists_integral_pseudoBasis (Λ : Submodule (𝓞 K) (ι → K)) (hΛ : Λ.FG)
    (hspan : Submodule.span K (Λ : Set (ι → K)) = ⊤) :
    ∃ (y : ι → ι → K) (J : ι → Ideal (𝓞 K)), LinearIndependent K y ∧ (∀ i, J i ≠ ⊥) ∧
      ∀ x, x ∈ Λ ↔ ∃ c : ι → 𝓞 K, (∀ i, c i ∈ J i) ∧ x = ∑ i, (c i : K) • y i := by
  have hk : finrank K (Submodule.span K (Λ : Set (ι → K))) = Fintype.card ι := by
    rw [hspan, finrank_top, Module.finrank_fintype_fun_eq_card]
  obtain ⟨y', 𝔞, hy', h𝔞, hchar⟩ := Submodule.exists_pseudoBasis _ Λ hΛ hk
  set e := Fintype.equivFin ι
  choose a aI ha h𝔞eq using fun i ↦ FractionalIdeal.exists_eq_spanSingleton_mul (𝔞 (e i))
  have haK : ∀ i, (algebraMap (𝓞 K) K (a i)) ≠ 0 := fun i ↦ by
    simpa using ha i
  have hmem : ∀ i (t : K), t ∈ 𝔞 (e i) ↔ ∃ c ∈ aI i, t = (algebraMap (𝓞 K) K (a i))⁻¹ * c := by
    intro i t
    rw [h𝔞eq i, FractionalIdeal.mem_singleton_mul]
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨c, hc, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hu
      exact ⟨c, hc, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨_, (FractionalIdeal.mem_coeIdeal _).2 ⟨c, hc, rfl⟩, rfl⟩
  refine ⟨fun i ↦ (algebraMap (𝓞 K) K (a i))⁻¹ • y' (e i), aI, ?_, fun i ↦ ?_, fun x ↦ ?_⟩
  · have := (hy'.comp e (Equiv.injective e)).units_smul
      (fun i ↦ Units.mk0 ((algebraMap (𝓞 K) K (a i))⁻¹) (inv_ne_zero (haK i)))
    exact this
  · intro hbot
    apply h𝔞 (e i)
    rw [h𝔞eq i, hbot]
    simp
  · rw [hchar]
    constructor
    · rintro ⟨c, hc, rfl⟩
      choose c' hc' hcc' using fun i ↦ (hmem i (c (e i))).1 (hc (e i))
      refine ⟨c', hc', ?_⟩
      rw [← Equiv.sum_comp e (fun k ↦ c k • y' k)]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [hcc' i, smul_smul, mul_comm]
    · rintro ⟨c', hc', rfl⟩
      refine ⟨fun k ↦ (algebraMap (𝓞 K) K (a (e.symm k)))⁻¹ * c' (e.symm k), fun k ↦ ?_, ?_⟩
      · have := (hmem (e.symm k) _).2 ⟨c' (e.symm k), hc' _, rfl⟩
        simpa using this
      · rw [← Equiv.sum_comp e]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simp only [Equiv.symm_apply_apply, smul_smul]
        congr 1
        ring

open MeasureTheory in
open scoped Classical in
/-- **The covolume of a lattice given by an integral pseudo-basis** `Λ = ⊕ J i • y i`: it has a
`ℤ`-basis, and its covolume is `|N (det y)| ∏ N (J i)` times that of `(𝓞 K)ⁱ`. -/
theorem exists_basis_mixedImage_of_pseudoBasis [DecidableEq ι] (Λ : Submodule (𝓞 K) (ι → K))
    (y : ι → ι → K) (J : ι → Ideal (𝓞 K)) (hy : LinearIndependent K y) (hJ : ∀ i, J i ≠ ⊥)
    (hchar : ∀ x, x ∈ Λ ↔ ∃ c : ι → 𝓞 K, (∀ i, c i ∈ J i) ∧ x = ∑ i, (c i : K) • y i) :
    ∃ b : Basis ((_ : ι) × Fin (finrank ℚ K)) ℝ (ι → mixedSpace K),
      Λ.mixedImage = Submodule.span ℤ (Set.range b) ∧
      ZLattice.covolume (Submodule.span ℤ (Set.range b)) =
        |Algebra.norm ℚ (Matrix.of y).det| * (∏ i, (Ideal.absNorm (J i) : ℝ)) *
          ZLattice.covolume (mixedEmbedding.integerLattice K) ^ Fintype.card ι := by
  have hJ0 : ∀ i, (J i : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := fun i ↦ by
    simpa [FractionalIdeal.coeIdeal_ne_zero] using hJ i
  choose a bI hbI hspan_a hvol using fun i ↦
    mixedEmbedding.exists_idealLatticeBasis (Units.mk0 (J i : FractionalIdeal (𝓞 K)⁰ K) (hJ0 i))
  have ha : ∀ i k, ∃ c : 𝓞 K, c ∈ J i ∧ (c : K) = a i k := fun i k ↦ by
    have := (hspan_a i (a i k)).1 (Submodule.subset_span ⟨k, rfl⟩)
    simpa [FractionalIdeal.mem_coeIdeal] using this
  choose ca hcaJ hca using ha
  -- the product basis and the change of variables
  set b' : Basis ((_ : ι) × Fin (finrank ℚ K)) ℝ (ι → mixedSpace K) := Pi.basis bI with hb'
  set A : Matrix ι ι (mixedSpace K) := (Matrix.of y)ᵀ.map (mixedEmbedding K) with hA
  set T : (ι → mixedSpace K) →ₗ[ℝ] (ι → mixedSpace K) :=
    (Matrix.toLin' A).restrictScalars ℝ with hT
  have hdetA : A.det = mixedEmbedding K (Matrix.of y).det := by
    rw [hA, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.transpose_map, Matrix.det_transpose]
  have hdetT : LinearMap.det T = Algebra.norm ℝ (mixedEmbedding K (Matrix.of y).det) := by
    rw [hT, LinearMap.det_restrictScalars, LinearMap.det_toLin', hdetA]
  have hdetY : (Matrix.of y).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1 hy)).ne_zero
  have habs : |LinearMap.det T| = |Algebra.norm ℚ (Matrix.of y).det| := by
    rw [hdetT, mixedEmbedding.abs_algebraNorm_mixedEmbedding]
  have hdet0 : LinearMap.det T ≠ 0 := by
    intro h
    have h' : ((|Algebra.norm ℚ (Matrix.of y).det| : ℚ) : ℝ) = 0 := by
      rw [← habs, h, abs_zero]
    rw [Rat.cast_eq_zero, abs_eq_zero, Algebra.norm_eq_zero_iff] at h'
    exact hdetY h'
  set Te := T.equivOfDetNeZero hdet0 with hTe
  set b := b'.map Te with hb
  have hbq : ∀ i k, b ⟨i, k⟩ = fun j ↦ mixedEmbedding K (a i k * y i j) := by
    intro i k
    funext j
    rw [hb, Basis.map_apply, hb', Pi.basis_apply, hTe]
    change (Matrix.toLin' A) (Pi.single i (bI i k)) j = _
    rw [Matrix.toLin'_apply, Matrix.mulVec_single, hbI, hA]
    simp [mul_comm]
  -- the module is the `ℤ`-span of the products
  have hZ : Λ.restrictScalars ℤ = Submodule.span ℤ
      (Set.range fun q : (_ : ι) × Fin (finrank ℚ K) ↦ a q.1 q.2 • y q.1) := by
    refine le_antisymm (fun x hx ↦ ?_) (Submodule.span_le.2 ?_)
    · obtain ⟨c, hc, rfl⟩ := (hchar x).1 hx
      have hcj : ∀ i, ∃ n : Fin (finrank ℚ K) → ℤ, ∑ k, n k • a i k = (c i : K) := fun i ↦
        (Submodule.mem_span_range_iff_exists_fun ℤ).1 ((hspan_a i (c i)).2
          ((FractionalIdeal.mem_coeIdeal _).2 ⟨c i, hc i, rfl⟩))
      choose n hn using hcj
      refine (Submodule.mem_span_range_iff_exists_fun ℤ).2 ⟨fun q ↦ n q.1 q.2, ?_⟩
      rw [Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← hn i, Finset.sum_smul]
      exact Finset.sum_congr rfl fun k _ ↦ by rw [smul_assoc]
    · rintro _ ⟨q, rfl⟩
      refine (hchar _).2 ⟨Pi.single q.1 (ca q.1 q.2), fun i ↦ ?_, ?_⟩
      · rcases eq_or_ne i q.1 with rfl | hne
        · simpa using hcaJ _ _
        · simp [Pi.single_eq_of_ne hne]
      · rw [Finset.sum_eq_single q.1]
        · simp [hca]
        · intro i _ hne; simp [Pi.single_eq_of_ne hne]
        · simp
  have hL : Λ.mixedImage = Submodule.span ℤ (Set.range b) := by
    rw [mixedImage, hZ, Submodule.map_span, ← Set.range_comp]
    congr 1
    ext z
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨q, by rw [hbq]; rfl⟩
    · rintro ⟨q, rfl⟩
      exact ⟨q, by rw [hbq]; rfl⟩
  refine ⟨b, hL, ?_⟩
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain b volume)]
  have hfd : ZSpan.fundamentalDomain b = T '' ZSpan.fundamentalDomain b' := by
    rw [hb, ← ZSpan.map_fundamentalDomain]
    rfl
  have hO : volume (ZSpan.fundamentalDomain (latticeBasis K))
      = ENNReal.ofReal (ZLattice.covolume (mixedEmbedding.integerLattice K)) := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
      (fundamentalDomain_integerLattice K), measureReal_def, ENNReal.ofReal_toReal]
    exact (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  rw [measureReal_def, hfd, Measure.addHaar_image_linearMap, hb', fundamentalDomain_pi_basis,
    volume_pi_pi]
  simp_rw [hvol, hO]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_prod, habs]
  simp_rw [ENNReal.toReal_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, mul_assoc]
  congr 2
  · refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [Units.val_mk0, FractionalIdeal.coeIdeal_absNorm, ENNReal.toReal_ofReal (by positivity)]
    push_cast
    rfl
  · rw [ENNReal.toReal_ofReal (ZLattice.covolume_pos _ volume).le]

omit [Fintype ι] in
/-- The image of a finitely generated `𝓞 K`-module spanning `Kⁱ` is discrete. -/
theorem discreteTopology_mixedImage [Finite ι] (Λ : Submodule (𝓞 K) (ι → K)) (hΛ : Λ.FG)
    (hspan : Submodule.span K (Λ : Set (ι → K)) = ⊤) : DiscreteTopology Λ.mixedImage := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨y, J, hy, hJ, hchar⟩ := Λ.exists_integral_pseudoBasis hΛ hspan
  obtain ⟨b, hL, -⟩ := Λ.exists_basis_mixedImage_of_pseudoBasis y J hy hJ hchar
  rw [hL]
  infer_instance

open scoped Classical in
/-- The image of a finitely generated `𝓞 K`-module spanning `Kⁱ` is a lattice. -/
theorem isZLattice_mixedImage (Λ : Submodule (𝓞 K) (ι → K)) (hΛ : Λ.FG)
    (hspan : Submodule.span K (Λ : Set (ι → K)) = ⊤) [DiscreteTopology Λ.mixedImage] :
    IsZLattice ℝ Λ.mixedImage := by
  classical
  obtain ⟨y, J, hy, hJ, hchar⟩ := Λ.exists_integral_pseudoBasis hΛ hspan
  obtain ⟨b, hL, -⟩ := Λ.exists_basis_mixedImage_of_pseudoBasis y J hy hJ hchar
  constructor
  rw [hL]
  exact ZSpan.span_top b

/-- The determinant bound, and its attainment, for a lattice with an integral pseudo-basis. -/
private theorem det_le_and_exists [DecidableEq ι] (Λ : Submodule (𝓞 K) (ι → K)) (y : ι → ι → K)
    (J : ι → Ideal (𝓞 K))
    (hchar : ∀ x, x ∈ Λ ↔ ∃ c : ι → 𝓞 K, (∀ i, c i ∈ J i) ∧ x = ∑ i, (c i : K) • y i)
    {m : ι → ℕ} (g : ∀ i, Fin (m i) → 𝓞 K) (hg : ∀ i, Ideal.span (Set.range (g i)) = J i)
    (hgne : ∀ i, Nonempty (Fin (m i))) (v : FinitePlace K) :
    (∀ x : ι → ι → K, (∀ k, x k ∈ Λ) →
      v (Matrix.of x).det ≤ v (Matrix.of y).det * ∏ i, ⨆ k, v (g i k : K)) ∧
    ∃ x : ι → ι → K, (∀ k, x k ∈ Λ) ∧
      v (Matrix.of x).det = v (Matrix.of y).det * ∏ i, ⨆ k, v (g i k : K) := by
  classical
  have hbdd : ∀ i, BddAbove (Set.range fun k ↦ v (g i k : K)) := fun i ↦
    (Set.finite_range _).bddAbove
  have hM0 : ∀ i, 0 ≤ ⨆ k, v (g i k : K) := fun i ↦ Real.iSup_nonneg fun k ↦ apply_nonneg _ _
  refine ⟨fun x hx ↦ ?_, ?_⟩
  · choose c hc hcx using fun k ↦ (hchar (x k)).1 (hx k)
    have hmat : Matrix.of x = Matrix.of (fun k i ↦ (c k i : K)) * Matrix.of y := by
      ext k j
      rw [Matrix.mul_apply, Matrix.of_apply, hcx k, Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.of_apply]
    rw [hmat, Matrix.det_mul, map_mul, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (apply_nonneg _ _)
    rw [Matrix.det_apply]
    refine FinitePlace.apply_sum_le_of_forall_le v (Finset.prod_nonneg fun i _ ↦ hM0 i) fun σ _ ↦ ?_
    rw [Units.smul_def, zsmul_eq_mul, map_mul]
    have hs : v ((σ.sign : ℤ) : K) = 1 := by
      rcases Int.units_eq_one_or σ.sign with h | h <;> simp [h]
    rw [hs, one_mul, map_prod]
    refine Finset.prod_le_prod₀ (fun i _ ↦ apply_nonneg _ _) fun i _ ↦ ?_
    rw [Matrix.of_apply]
    exact FinitePlace.apply_le_iSup_of_mem_span v (g i) (by rw [hg i]; exact hc (σ i) i)
  · have hk : ∀ i, ∃ k, v (g i k : K) = ⨆ k, v (g i k : K) := fun i ↦
      exists_eq_ciSup_of_finite
    choose k hk using hk
    refine ⟨fun i ↦ (g i (k i) : K) • y i, fun i ↦ (hchar _).2 ⟨Pi.single i (g i (k i)),
      fun j ↦ ?_, ?_⟩, ?_⟩
    · rcases eq_or_ne j i with rfl | hne
      · rw [Pi.single_eq_same, ← hg j]
        exact Ideal.subset_span ⟨k j, rfl⟩
      · rw [Pi.single_eq_of_ne hne]
        exact (J j).zero_mem
    · rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hne; simp [Pi.single_eq_of_ne hne]
      · simp
    · have hmat : Matrix.of (fun i ↦ (g i (k i) : K) • y i)
          = Matrix.diagonal (fun i ↦ (g i (k i) : K)) * Matrix.of y := by
        ext i j
        simp only [Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Matrix.diagonal_mul]
      rw [hmat, Matrix.det_mul, Matrix.det_diagonal, map_mul, map_prod, mul_comm]
      congr 1
      exact Finset.prod_congr rfl fun i _ ↦ hk i

open scoped Classical in
/-- **The covolume of an `𝓞 K`-lattice, read at the finite places.** If `B v` is the largest value
of the finite place `v` on the determinants of `ι`-tuples of vectors of `Λ`, then the covolume of
`Λ` is `(∏ᶠ v, B v)⁻¹` times the covolume of `(𝓞 K)ⁱ`. The factor is the generalized index of `Λ`
in `(𝓞 K)ⁱ`, computed place by place. -/
theorem covolume_mixedImage [DecidableEq ι] (Λ : Submodule (𝓞 K) (ι → K)) (hΛ : Λ.FG)
    (hspan : Submodule.span K (Λ : Set (ι → K)) = ⊤) {B : FinitePlace K → ℝ}
    (hle : ∀ (v : FinitePlace K) (x : ι → ι → K), (∀ k, x k ∈ Λ) → v (Matrix.of x).det ≤ B v)
    (hex : ∀ v : FinitePlace K, ∃ x : ι → ι → K, (∀ k, x k ∈ Λ) ∧ v (Matrix.of x).det = B v) :
    ZLattice.covolume Λ.mixedImage =
      (∏ᶠ v, B v)⁻¹ * ZLattice.covolume (mixedEmbedding.integerLattice K) ^ Fintype.card ι := by
  obtain ⟨y, J, hy, hJ, hchar⟩ := Λ.exists_integral_pseudoBasis hΛ hspan
  obtain ⟨b, hL, hcov⟩ := Λ.exists_basis_mixedImage_of_pseudoBasis y J hy hJ hchar
  have hgen : ∀ i, ∃ (m : ℕ) (g : Fin m → 𝓞 K), Ideal.span (Set.range g) = J i := fun i ↦
    Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian (J i))
  choose m g hg using hgen
  have hgne : ∀ i, g i ≠ 0 := by
    intro i h
    apply hJ i
    rw [← hg i, h]
    simp
  have hgne' : ∀ i, Nonempty (Fin (m i)) := fun i ↦ by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hgne i (funext fun k ↦ (IsEmpty.false k).elim)
  have hdetY : (Matrix.of y).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1 hy)).ne_zero
  have hB : ∀ v : FinitePlace K, B v = v (Matrix.of y).det * ∏ i, ⨆ k, v (g i k : K) := by
    intro v
    obtain ⟨hdle, x', hx', hx'v⟩ := det_le_and_exists Λ y J hchar g hg hgne' v
    refine le_antisymm ?_ ?_
    · obtain ⟨x, hx, hxv⟩ := hex v
      rw [← hxv]
      exact hdle x hx
    · rw [← hx'v]
      exact hle v x' hx'
  have hsupp : ∀ i, Function.HasFiniteMulSupport fun v : FinitePlace K ↦ ⨆ k, v (g i k : K) := by
    intro i
    have hne : (fun k ↦ (g i k : K)) ≠ 0 := by
      intro h
      apply hgne i
      funext k
      have := congrFun h k
      simpa using this
    exact FinitePlace.hasFiniteMulSupport_iSup hne
  rw [hL, hcov, finprod_congr hB, finprod_mul_distrib (FinitePlace.hasFiniteMulSupport hdetY)
    (Function.HasFiniteMulSupport.prod hsupp _), FinitePlace.prod_eq_inv_abs_norm hdetY,
    finprod_prod_comm _ _ fun i _ ↦ hsupp i]
  have hN : ∀ i, ∏ᶠ v : FinitePlace K, ⨆ k, v (g i k : K) = ((Ideal.absNorm (J i) : ℝ))⁻¹ := by
    intro i
    have hex' : ∃ k, g i k ≠ 0 := by
      by_contra h
      push Not at h
      exact hgne i (funext h)
    rw [FinitePlace.finprod_iSup_eq_inv_absNorm hex', hg i]
  simp_rw [hN]
  push_cast
  rw [Finset.prod_inv_distrib, ← mul_inv, inv_inv]

end Submodule
