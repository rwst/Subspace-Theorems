/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.ApproximationDomain
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- Used only inside proofs.
import ArithmeticHeights.MixedLattice
import DiophantineApproximation.RationalPlaces
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.NumberTheory.NumberField.Discriminant.Basic

/-!
# The volume of an approximation domain

The body `B` of an approximation domain (`ApproximationDomain.lean`) has volume

```text
vol B = 2 ^ (r₁ #ι) π ^ (r₂ #ι) · ∏_{v | ∞} (v (det L v)⁻¹ ∏ i Q ^ c v i) ^ mult v,
```

the volume of the unit body times the local factors, and together with the covolume of the lattice
`Λ` this gives the comparison with `Q` to the weight that the geometry of numbers of Layer 4.2
consumes:

```text
approxConst · (∏_{v ∈ Sfin} N 𝔭_v ^ #ι)⁻¹ · Q ^ weight
    ≤  vol B / covol Λ  ≤  approxConst · Q ^ weight,
```

with a constant `approxConst` that depends on `K`, `Sfin`, `#ι` and the determinants of the forms
and on nothing else — not on `Q` and not on the exponents.

## Main definitions

* `NumberField.approxConst`: the constant of the comparison, `2 ^ (r₁ #ι) π ^ (r₂ #ι)` divided by
  `covol (𝓞 K) ^ #ι ∏_{v | ∞} v (det L v) ^ mult v ∏_{v ∈ Sfin} v (det L v)`.

## Main results

* `NumberField.volume_approxBody`: the volume displayed above.
* `NumberField.volume_div_covolume_le` and `NumberField.le_volume_div_covolume`: the two-sided
  comparison, **Bombieri–Gubler's Corollary 7.5.8** in the real formulation.
* `NumberField.rpow_approxWeight`: `Q` to the weight is the product of the local bounds.

## Implementation notes

⚠ **The volume is one change of variables, not one per place.** The body is the preimage of a
product of closed balls, one per coordinate and place, under the `mixedSpace K`-linear map whose
matrix has at `w` the coefficients of `L w` embedded by `w`. Its real determinant is the algebra
norm of its determinant, `∏_{v | ∞} v (det L v) ^ mult v`, by `LinearMap.det_restrictScalars`; the
place-by-place coordinate changes of the book's proof of 7.5.7 never appear.

⚠ **Only the finite places make the comparison two-sided.** The infinite places contribute an
exact power of `Q`; the finite ones contribute `∏ a v i`, which lies between `Q` to their part of
the weight and that divided by `∏_{v ∈ Sfin} N 𝔭_v ^ #ι`. The upper bound, the one Layer 4.3
uses to force the last minimum up, carries no loss at all.

⚠ **Two acceptance tests.** Over `ℚ` with no finite place, the coordinate forms and `c = 0`, the
body is the cube `[-1, 1]ⁱ` of volume `2 ^ #ι` and the lattice is `ℤⁱ` of covolume `1`. At the
`2`-adic place of `ℚ`, with `L = id`, `c = 1` and `Q = 3/2`, the largest value of `|·|_2` at most
`3/2` is `1`, and the covolume is `1` where `Q ^ c` would predict `2/3`: the finite-place volume
of Bombieri–Gubler's Lemma 7.5.7(b) is not an equality in `Q ^ c`.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Lemma 7.5.7 and Corollary 7.5.8.

This is Layer 4.1 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Module NumberField NumberField.mixedEmbedding NumberField.InfinitePlace Matrix

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

section Volume

open MeasureTheory

open scoped Classical in
/-- The coordinate of the mixed space at an infinite place, read in `ℂ`. -/
private noncomputable def placeHom (w : InfinitePlace K) : mixedSpace K →+* ℂ :=
  if hw : IsReal w then
    Complex.ofRealHom.comp ((Pi.evalRingHom _ (⟨w, hw⟩ : {w // IsReal w})).comp (RingHom.fst _ _))
  else (Pi.evalRingHom _ (⟨w, not_isReal_iff_isComplex.1 hw⟩ : {w // IsComplex w})).comp
    (RingHom.snd _ _)

omit [NumberField K] [Fintype ι] in
private theorem normAtPlace_eq_norm_placeHom (w : InfinitePlace K) (x : mixedSpace K) :
    normAtPlace w x = ‖placeHom w x‖ := by
  by_cases hw : IsReal w
  · simp [placeHom, hw, normAtPlace_apply_of_isReal hw]
  · simp [placeHom, hw, normAtPlace_apply_of_isComplex (not_isReal_iff_isComplex.1 hw)]

omit [NumberField K] [Fintype ι] in
private theorem placeHom_mixedEmbedding (w : InfinitePlace K) (x : K) :
    placeHom w (mixedEmbedding K x) = w.embedding x := by
  by_cases hw : IsReal w
  · simp [placeHom, hw]
  · simp [placeHom, hw]

/-- The element of the mixed space whose coordinate at `w` is that of `f w`. -/
private noncomputable def assemble (f : InfinitePlace K → K) : mixedSpace K :=
  (fun w ↦ embedding_of_isReal w.2 (f w.1), fun w ↦ w.1.embedding (f w.1))

omit [NumberField K] [Fintype ι] in
private theorem placeHom_assemble (w : InfinitePlace K) (f : InfinitePlace K → K) :
    placeHom w (assemble f) = w.embedding (f w) := by
  by_cases hw : IsReal w
  · simp [placeHom, hw, assemble]
  · simp [placeHom, hw, assemble]

/-- The box of radii `r`: at each infinite place the coordinate has norm at most `r w`. -/
private def mixedBox (r : InfinitePlace K → ℝ) : Set (mixedSpace K) :=
  {x | ∀ w, normAtPlace w x ≤ r w}

omit [NumberField K] [Fintype ι] in
private theorem mixedBox_eq (r : InfinitePlace K → ℝ) :
    mixedBox r = (Set.univ.pi fun w : {w // IsReal w} ↦ Metric.closedBall 0 (r w.1)) ×ˢ
      (Set.univ.pi fun w : {w // IsComplex w} ↦ Metric.closedBall 0 (r w.1)) := by
  ext x
  simp only [mixedBox, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies,
    mem_closedBall_zero_iff]
  refine ⟨fun h ↦ ⟨fun w ↦ ?_, fun w ↦ ?_⟩, fun ⟨h1, h2⟩ w ↦ ?_⟩
  · simpa [normAtPlace_apply_of_isReal w.2] using h w.1
  · simpa [normAtPlace_apply_of_isComplex w.2] using h w.1
  · rcases isReal_or_isComplex w with hw | hw
    · rw [normAtPlace_apply_of_isReal hw]; exact h1 ⟨w, hw⟩
    · rw [normAtPlace_apply_of_isComplex hw]; exact h2 ⟨w, hw⟩

open scoped Classical in
private theorem volume_mixedBox (r : InfinitePlace K → ℝ) (hr : ∀ w, 0 ≤ r w) :
    volume (mixedBox r) = ENNReal.ofReal (2 ^ nrRealPlaces K * Real.pi ^ nrComplexPlaces K *
      ∏ w, r w ^ w.mult) := by
  rw [mixedBox_eq, Measure.volume_eq_prod, Measure.prod_prod, volume_pi, Measure.pi_pi, volume_pi,
    Measure.pi_pi]
  simp_rw [Real.volume_closedBall, Complex.volume_closedBall]
  rw [prod_eq_prod_mul_prod]
  simp_rw [mult_isReal, mult_isComplex, pow_one]
  have hπ : (NNReal.pi : ENNReal) = ENNReal.ofReal Real.pi := by
    rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  simp_rw [hπ, ← ENNReal.ofReal_pow (hr _), ← ENNReal.ofReal_mul (pow_nonneg (hr _) 2)]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun w _ ↦ mul_nonneg zero_le_two (hr _)),
    ← ENNReal.ofReal_prod_of_nonneg (fun w _ ↦ mul_nonneg (pow_nonneg (hr _) 2) Real.pi_pos.le),
    ← ENNReal.ofReal_mul (Finset.prod_nonneg fun w _ ↦ mul_nonneg zero_le_two (hr _))]
  congr 1
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const,
    Finset.card_univ, Finset.card_univ]
  simp only [nrRealPlaces, nrComplexPlaces]
  ring

open scoped Classical in
/-- **The volume of the body of an approximation domain** (Bombieri–Gubler, Lemma 7.5.7(c), (d), in
the real formulation). It is the volume `2 ^ (r₁ #ι) π ^ (r₂ #ι)` of the unit body — the body of
the coordinate forms with `c = 0` — times `∏_{v | ∞} (v (det L v)⁻¹ ∏ i, Q ^ c v i) ^ mult v`. -/
theorem volume_approxBody {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hL : ∀ w : InfinitePlace K, LinearIndependent K (L w.1)) (c : AbsoluteValue K ℝ → ι → ℝ)
    {Q : ℝ} (hQ : 0 < Q) :
    volume (approxBody L c Q) = ENNReal.ofReal (2 ^ (nrRealPlaces K * Fintype.card ι) *
      Real.pi ^ (nrComplexPlaces K * Fintype.card ι) *
      ∏ w : InfinitePlace K,
        ((w (LinearMap.det (LinearMap.pi (L w.1))))⁻¹ * ∏ i, Q ^ c w.1 i) ^ w.mult) := by
  set A : Matrix ι ι (mixedSpace K) :=
    Matrix.of fun i j ↦ assemble fun w ↦ L w.1 i (Pi.basisFun K ι j) with hA
  set T : (ι → mixedSpace K) →ₗ[ℝ] (ι → mixedSpace K) :=
    (Matrix.toLin' A).restrictScalars ℝ with hT
  have hB : approxBody L c Q = T ⁻¹' (Set.univ.pi fun i ↦ mixedBox fun w ↦ Q ^ c w.1 i) := by
    ext z
    have key : ∀ (w : InfinitePlace K) i,
        normAtPlace w (∑ j, mixedEmbedding K (L w.1 i (Pi.basisFun K ι j)) * z j)
          = normAtPlace w (T z i) := by
      intro w i
      rw [normAtPlace_eq_norm_placeHom, normAtPlace_eq_norm_placeHom, hT,
        LinearMap.restrictScalars_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        map_sum, map_sum]
      simp_rw [map_mul, placeHom_mixedEmbedding, hA, Matrix.of_apply, placeHom_assemble]
    simp only [approxBody, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
      true_implies, mixedBox, key]
    exact forall_comm
  set M : InfinitePlace K → Matrix ι ι K :=
    fun w ↦ Matrix.of fun i j ↦ L w.1 i (Pi.basisFun K ι j) with hM
  have hMdet : ∀ w, (M w).det = LinearMap.det (LinearMap.pi (L w.1)) := fun w ↦ by
    rw [← LinearMap.det_toMatrix']
    congr 1
  have hdetA : ∀ w, placeHom w A.det = w.embedding (M w).det := fun w ↦ by
    rw [RingHom.map_det, RingHom.map_det]
    congr 1
    ext i j
    simp [RingHom.mapMatrix_apply, hA, hM, placeHom_assemble]
  have hdetT : LinearMap.det T = Algebra.norm ℝ A.det := by
    rw [hT, LinearMap.det_restrictScalars, LinearMap.det_toLin']
  have habsT : |LinearMap.det T| =
      ∏ w : InfinitePlace K, (w (LinearMap.det (LinearMap.pi (L w.1)))) ^ w.mult := by
    rw [hdetT, mixedEmbedding.abs_algebraNorm_eq_norm, mixedEmbedding.norm_apply]
    refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [normAtPlace_eq_norm_placeHom, hdetA, InfinitePlace.norm_embedding_eq, hMdet]
  have hdet0 : LinearMap.det T ≠ 0 := by
    intro h
    have h0 := habsT
    rw [h, abs_zero, eq_comm, Finset.prod_eq_zero_iff] at h0
    obtain ⟨w, -, hw⟩ := h0
    have hw' := pow_eq_zero_iff (n := w.mult) mult_pos.ne' |>.1 hw
    exact LinearMap.det_pi_ne_zero (hL w) ((w.pos_iff.not_left).1 (by rw [hw']; simp))
  rw [hB, Measure.addHaar_preimage_linearMap _ hdet0, volume_pi_pi]
  simp_rw [volume_mixedBox _ (fun w ↦ (Real.rpow_pos_of_pos hQ _).le)]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ by positivity),
    ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  rw [abs_inv, habsT]
  have h1 : ∏ i : ι, 2 ^ nrRealPlaces K * Real.pi ^ nrComplexPlaces K *
      ∏ w : InfinitePlace K, (Q ^ c w.1 i) ^ w.mult
      = 2 ^ (nrRealPlaces K * Fintype.card ι) * Real.pi ^ (nrComplexPlaces K * Fintype.card ι) *
        ∏ w : InfinitePlace K, (∏ i, Q ^ c w.1 i) ^ w.mult := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const,
      Finset.card_univ, ← pow_mul, ← pow_mul, Finset.prod_comm]
    simp_rw [Finset.prod_pow]
  have h2 : ∏ w : InfinitePlace K,
      ((w (LinearMap.det (LinearMap.pi (L w.1))))⁻¹ * ∏ i, Q ^ c w.1 i) ^ w.mult
      = (∏ w : InfinitePlace K, (w (LinearMap.det (LinearMap.pi (L w.1)))) ^ w.mult)⁻¹ *
        ∏ w : InfinitePlace K, (∏ i, Q ^ c w.1 i) ^ w.mult := by
    simp_rw [mul_pow, Finset.prod_mul_distrib, inv_pow, Finset.prod_inv_distrib]
  rw [h1, h2]
  ring

end Volume

section Ratio

open MeasureTheory


/-- `Q` to the weight is the product of all the local bounds. -/
theorem rpow_approxWeight (Sfin : Finset (FinitePlace K)) (c : AbsoluteValue K ℝ → ι → ℝ)
    {Q : ℝ} (hQ : 0 < Q) :
    Q ^ approxWeight Sfin c = (∏ w : InfinitePlace K, (∏ i, Q ^ c w.1 i) ^ w.mult) *
      ∏ v ∈ Sfin, ∏ i, Q ^ c v.1 i := by
  rw [approxWeight, Real.rpow_add hQ, Real.rpow_sum_of_pos hQ, Real.rpow_sum_of_pos hQ]
  congr 1
  · refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [mul_comm, Real.rpow_mul_natCast hQ.le, Real.rpow_sum_of_pos hQ]
  · exact Finset.prod_congr rfl fun v _ ↦ Real.rpow_sum_of_pos hQ _ _

open scoped Classical in
/-- The constant of the comparison between the volume of the body and the covolume of the
lattice of an approximation domain: it depends on `K`, `Sfin`, `#ι` and the determinants of the
forms, and on nothing else. -/
noncomputable def approxConst (Sfin : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) : ℝ :=
  2 ^ (nrRealPlaces K * Fintype.card ι) * Real.pi ^ (nrComplexPlaces K * Fintype.card ι) /
    (ZLattice.covolume (mixedEmbedding.integerLattice K) ^ Fintype.card ι *
      (∏ w : InfinitePlace K, w (LinearMap.det (LinearMap.pi (L w.1))) ^ w.mult) *
      ∏ v ∈ Sfin, v (LinearMap.det (LinearMap.pi (L v.1))))

open scoped Classical in
/-- The ratio of volume to covolume, exactly. -/
private theorem volume_div_covolume_eq {Sfin : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ}
    (hQ : 0 < Q) :
    (volume (approxBody L c Q)).toReal / ZLattice.covolume (approxLattice Sfin L c Q) =
      approxConst Sfin L * (∏ w : InfinitePlace K, (∏ i, Q ^ c w.1 i) ^ w.mult) *
        ∏ v ∈ Sfin, ∏ i, v.floorValue (Q ^ c v.1 i) := by
  have hdInf : ∀ w : InfinitePlace K, 0 < w (LinearMap.det (LinearMap.pi (L w.1))) := fun w ↦
    w.pos_iff.2 (LinearMap.det_pi_ne_zero (hLInf w))
  have hdFin : ∀ v ∈ Sfin, 0 < v (LinearMap.det (LinearMap.pi (L v.1))) := fun v hv ↦
    FinitePlace.pos_iff.2 (LinearMap.det_pi_ne_zero (hLFin v hv))
  have ha : ∀ (v : FinitePlace K) i, 0 < v.floorValue (Q ^ c v.1 i) := fun v i ↦
    v.floorValue_pos _
  have hO : 0 < ZLattice.covolume (mixedEmbedding.integerLattice K) :=
    ZLattice.covolume_pos _ _
  rw [volume_approxBody hLInf c hQ, ENNReal.toReal_ofReal (by
      refine mul_nonneg (by positivity) (Finset.prod_nonneg fun w _ ↦ pow_nonneg (mul_nonneg
        (inv_nonneg.2 (hdInf w).le) (Finset.prod_nonneg fun i _ ↦
          (Real.rpow_pos_of_pos hQ _).le)) _)),
    covolume_approxLattice hLFin c hQ, approxConst]
  simp_rw [mul_pow, Finset.prod_mul_distrib, inv_pow, Finset.prod_inv_distrib]
  have h1 : ∏ w : InfinitePlace K, w (LinearMap.det (LinearMap.pi (L w.1))) ^ w.mult ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun w _ ↦ (pow_pos (hdInf w) _).ne'
  have h2 : ∏ v ∈ Sfin, v (LinearMap.det (LinearMap.pi (L v.1))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v hv ↦ (hdFin v hv).ne'
  have h3 : ∏ v ∈ Sfin, ∏ i, v.floorValue (Q ^ c v.1 i) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v _ ↦ Finset.prod_ne_zero_iff.2 fun i _ ↦ (ha v i).ne'
  field_simp

open scoped Classical in
/-- The constant of the comparison is positive. -/
theorem approxConst_pos {Sfin : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) : 0 < approxConst Sfin L := by
  have hdInf : ∀ w : InfinitePlace K, 0 < w (LinearMap.det (LinearMap.pi (L w.1))) := fun w ↦
    w.pos_iff.2 (LinearMap.det_pi_ne_zero (hLInf w))
  have hdFin : ∀ v ∈ Sfin, 0 < v (LinearMap.det (LinearMap.pi (L v.1))) := fun v hv ↦
    FinitePlace.pos_iff.2 (LinearMap.det_pi_ne_zero (hLFin v hv))
  have hO : 0 < ZLattice.covolume (mixedEmbedding.integerLattice K) :=
    ZLattice.covolume_pos _ _
  unfold approxConst
  refine div_pos (by positivity) (mul_pos (mul_pos (pow_pos hO _)
    (Finset.prod_pos fun w _ ↦ pow_pos (hdInf w) _)) (Finset.prod_pos hdFin))

open scoped Classical in
/-- **The volume–covolume ratio, upper bound**: at most `approxConst` times `Q` to the weight. -/
theorem volume_div_covolume_le {Sfin : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ}
    (hQ : 0 < Q) :
    (volume (approxBody L c Q)).toReal / ZLattice.covolume (approxLattice Sfin L c Q) ≤
      approxConst Sfin L * Q ^ approxWeight Sfin c := by
  rw [volume_div_covolume_eq hLInf hLFin c hQ, rpow_approxWeight _ _ hQ, ← mul_assoc]
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun v _ ↦ Finset.prod_nonneg fun i _ ↦
    (v.floorValue_pos _).le) fun v _ ↦ Finset.prod_le_prod₀ (fun i _ ↦ (v.floorValue_pos _).le)
      fun i _ ↦ v.floorValue_le (Real.rpow_pos_of_pos hQ _)) ?_
  exact mul_nonneg (approxConst_pos hLInf hLFin).le (Finset.prod_nonneg fun w _ ↦ pow_nonneg
    (Finset.prod_nonneg fun i _ ↦ (Real.rpow_pos_of_pos hQ _).le) _)

open scoped Classical in
/-- **The volume–covolume ratio, lower bound**: at least `approxConst` times `Q` to the weight,
up to the norms of the primes of `Sfin`. -/
theorem le_volume_div_covolume {Sfin : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ}
    (hQ : 0 < Q) :
    approxConst Sfin L *
        (∏ v ∈ Sfin, (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) ^ Fintype.card ι)⁻¹ *
        Q ^ approxWeight Sfin c ≤
      (volume (approxBody L c Q)).toReal / ZLattice.covolume (approxLattice Sfin L c Q) := by
  rw [volume_div_covolume_eq hLInf hLFin c hQ, rpow_approxWeight _ _ hQ]
  have hN : ∀ v : FinitePlace K, 0 < (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) := fun v ↦
    zero_lt_one.trans v.one_lt_absNorm
  have hle : (∏ v ∈ Sfin, (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) ^ Fintype.card ι)⁻¹ *
      ∏ v ∈ Sfin, ∏ i, Q ^ c v.1 i ≤ ∏ v ∈ Sfin, ∏ i, v.floorValue (Q ^ c v.1 i) := by
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun v _ ↦ mul_nonneg (inv_nonneg.2 (pow_pos (hN v) _).le)
      (Finset.prod_nonneg fun i _ ↦ (Real.rpow_pos_of_pos hQ _).le)) fun v _ ↦ ?_
    rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_inv_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun i _ ↦ mul_nonneg (inv_nonneg.2 (hN v).le)
      (Real.rpow_pos_of_pos hQ _).le) fun i _ ↦ ?_
    rw [inv_mul_le_iff₀ (hN v)]
    exact (v.lt_mul_floorValue (Real.rpow_pos_of_pos hQ _)).le
  calc approxConst Sfin L *
        (∏ v ∈ Sfin, (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) ^ Fintype.card ι)⁻¹ *
        ((∏ w : InfinitePlace K, (∏ i, Q ^ c w.1 i) ^ w.mult) * ∏ v ∈ Sfin, ∏ i, Q ^ c v.1 i)
      = approxConst Sfin L * (∏ w : InfinitePlace K, (∏ i, Q ^ c w.1 i) ^ w.mult) *
          ((∏ v ∈ Sfin, (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) ^ Fintype.card ι)⁻¹ *
            ∏ v ∈ Sfin, ∏ i, Q ^ c v.1 i) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hle (mul_nonneg (approxConst_pos hLInf hLFin).le
        (Finset.prod_nonneg fun w _ ↦ pow_nonneg
          (Finset.prod_nonneg fun i _ ↦ (Real.rpow_pos_of_pos hQ _).le) _))

end Ratio

/-! ### Acceptance criteria -/

open MeasureTheory

/-- The coordinate forms have determinant `1`. -/
private theorem det_pi_dualBasis {ι : Type*} [Finite ι] [DecidableEq ι] :
    LinearMap.det (LinearMap.pi ⇑(Pi.basisFun ℚ ι).dualBasis) = 1 := by
  have : LinearMap.pi ⇑(Pi.basisFun ℚ ι).dualBasis = LinearMap.id := by
    ext x i
    simp
  rw [this, LinearMap.det_id]

open scoped Classical in
/-- The ring of integers of `ℚ` has covolume `1`. -/
private theorem covolume_integerLattice_rat :
    ZLattice.covolume (mixedEmbedding.integerLattice ℚ) = 1 := by
  classical
  rw [covolume_integerLattice, nrComplexPlaces_eq_zero_of_finrank_eq_one (Module.finrank_self ℚ),
    Rat.numberField_discr]
  simp

open scoped Classical in
/-- **Conformance: the unit cube.** Over `ℚ`, with no finite place, the coordinate forms and
`c = 0`, the body is the cube `[-1, 1]ⁱ`, of volume `2 ^ #ι`, and the lattice is `ℤⁱ`, of
covolume `1`. -/
example {ι : Type*} [Fintype ι] {Q : ℝ} (hQ : 0 < Q) :
    volume (approxBody (fun _ ↦ ⇑(Pi.basisFun ℚ ι).dualBasis) 0 Q) = 2 ^ Fintype.card ι ∧
      ZLattice.covolume (approxLattice ∅ (fun _ ↦ ⇑(Pi.basisFun ℚ ι).dualBasis) 0 Q) = 1 := by
  refine ⟨?_, ?_⟩
  · have h := volume_approxBody (K := ℚ) (L := fun _ ↦ ⇑(Pi.basisFun ℚ ι).dualBasis)
      (fun _ ↦ (Pi.basisFun ℚ ι).dualBasis.linearIndependent) 0 hQ
    rw [h, nrRealPlaces_eq_one_of_finrank_eq_one (Module.finrank_self ℚ),
      nrComplexPlaces_eq_zero_of_finrank_eq_one (Module.finrank_self ℚ), det_pi_dualBasis]
    simp only [map_one, inv_one, Pi.zero_apply, Real.rpow_zero, Finset.prod_const_one, one_mul,
      one_pow, zero_mul, pow_zero, mul_one]
    rw [ENNReal.ofReal_pow zero_le_two]
    simp
  · rw [covolume_approxLattice (by simp) 0 hQ, covolume_integerLattice_rat]
    simp

open scoped Classical in
/-- **The finite-place covolume is not a power of `Q`.** At the `2`-adic place of `ℚ`, in one
variable, with `L = id`, `c = 1` and `Q = 3/2`, the largest value of `|·|_2` at most `3/2` is `1`,
and the lattice has covolume `1`, where `Q ^ (-c)` would give `2/3`. -/
example : ZLattice.covolume (approxLattice {Rat.finitePlace (⟨2, Nat.prime_two⟩ : Nat.Primes)}
      (fun _ ↦ ⇑(Pi.basisFun ℚ (Fin 1)).dualBasis) 1 (3 / 2)) = 1 ∧
    (3 / 2 : ℝ) ^ (-(1 : ℝ)) ≠ 1 := by
  set v := Rat.finitePlace (⟨2, Nat.prime_two⟩ : Nat.Primes) with hvdef
  have hv : ∀ x : ℚ, v x = ((padicNorm 2 x : ℚ) : ℝ) := fun x ↦ Rat.finitePlace_apply _ x
  have hfv : v.floorValue (3 / 2) = 1 := by
    refine le_antisymm ?_ ?_
    · obtain ⟨x, hx⟩ := v.exists_apply_eq_floorValue (3 / 2)
      have hx0 : x ≠ 0 := by
        rintro rfl
        rw [map_zero] at hx
        exact (v.floorValue_pos (3 / 2)).ne hx
      have hle := v.floorValue_le (r := 3 / 2) (by norm_num)
      rw [← hx] at hle ⊢
      rw [hv, padicNorm.eq_zpow_of_nonzero hx0] at hle ⊢
      push_cast at hle ⊢
      by_contra hcon
      push Not at hcon
      have hk : 0 < -padicValRat 2 x := (one_lt_zpow_iff_right₀ one_lt_two).1 hcon
      have : (2 : ℝ) ^ (1 : ℤ) ≤ 2 ^ (-padicValRat 2 x) :=
        zpow_le_zpow_right₀ one_le_two hk
      rw [zpow_one] at this
      linarith
    · have := v.apply_le_floorValue (r := 3 / 2) (x := 1) (by rw [map_one]; norm_num)
      rwa [map_one] at this
  refine ⟨?_, by norm_num⟩
  have h := covolume_approxLattice (K := ℚ) (Sfin := {v})
    (L := fun _ ↦ ⇑(Pi.basisFun ℚ (Fin 1)).dualBasis)
    (fun _ _ ↦ (Pi.basisFun ℚ (Fin 1)).dualBasis.linearIndependent)
    (1 : AbsoluteValue ℚ ℝ → Fin 1 → ℝ) (Q := 3 / 2) (by norm_num)
  rw [h, covolume_integerLattice_rat, Finset.prod_singleton, det_pi_dualBasis]
  simp [hfv]

end NumberField
