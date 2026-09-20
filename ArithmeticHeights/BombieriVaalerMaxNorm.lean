/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.Duality
public import ArithmeticHeights.Extraction
public import ArithmeticHeights.MinkowskiSecond
public import ArithmeticHeights.MixedCube
public import Mathlib.Algebra.Module.LinearMap.Rat

/-!
# Bombieri–Vaaler over a number field: the max-norm form

**Bombieri–Gubler, Theorem 2.9.4; Bombieri–Vaaler 1983, Theorem 8.** Let `K` be a number field of
degree `d` with `r₁` real and `r₂` complex places and discriminant `D`, and let `V ⊆ Kⁱ` be a
subspace of dimension `k`. Then `V` has a basis `x₁, …, x_k` of vectors with coordinates in `𝓞 K`
and

```text
∏_{l} H(x l)  ≤  (2 / π)^{k r₂ / d} · |D|^{k / (2 d)} · H_Ar(V)^{1/d},
```

`H` the **absolute multiplicative height** — the sup norm at every place — and `H_Ar(V)` the
relative Arakelov height of `V`. That is Bombieri–Vaaler's own constant; since `2 / π < 1` it
implies the inequality applications quote,

```text
∏_{l} H(x l)  ≤  |D|^{k / (2 d)} · H_Ar(V)^{1/d},
```

which is strictly weaker exactly when `K` has a complex place. For `V` the solution space of
`A x = 0` the right-hand side is the height of the **row space** of `A`, by the duality theorem of
Layer 3.5.

## Main results

* `NumberField.exists_basis_ker_prod_absMulHeight_le`: the milestone — a basis of the solution
  space of `A x = 0` with coordinates in `𝓞 K`, bounded by the height of the row space of `A`;
  `NumberField.exists_basis_ker_prod_absMulHeight_le'` is the same at Bombieri–Vaaler's constant.
* `NumberField.exists_basis_prod_absMulHeight_le` and
  `NumberField.exists_basis_prod_absMulHeight_le'`: the subspace forms of the two.
* `NumberField.exists_basis_prod_mulHeight_le`: the relative form, in `Height.mulHeight`, which is
  what the proof produces.
* `NumberField.mixedEmbedding.mulHeight_le_pow_of_mem_smul_mixedCube`: the height of an integral
  tuple lying in `λ · mixedCube` is at most `2^{-r₁} π^{-r₂} · λ ^ d`.
* `NumberField.mixedEmbedding.prod_successiveMinimum_mixedCube_le`: Minkowski's second theorem for
  the sup-norm body, with the covolume of Layer 4.3 and the slice bound of `MixedCube.lean`
  inserted.

## Implementation notes

⚠ **This is where Layer 4.5 is spent, and it is the only place.** Layer 5.3 proves the Hermitian
inequality with no cube slicing at all — the slice of the ℓ² body is computed exactly — and pays
the residue `(2^k/ω_k)^{r₁} (2^k/ω_{2k})^{r₂}`, the ratio of a cube to a ball. Replacing the balls
by cubes and polydiscs removes that residue, and the price is Vaaler's theorem. Vaaler states the
dependency in the same direction: the Hermitian inequality follows from the max-norm theorem,
while the max-norm form "is more difficult because it requires the cube-slicing inequality".

⚠ **The constants: `2^{d k}` from Layer 4.2, `2^{−r₂ k}` from Layer 4.3, and `2^{−r₁ k} π^{−r₂ k}`
from the body, leaving `(2/π)^{k r₂}`.** Since `d = r₁ + 2 r₂` the three powers of two combine to
`2^{k r₂}`, and the only surviving transcendental is `π^{−k r₂}`. Over `ℚ` — `r₂ = 0`, `D = 1` —
the constant is `1`, which is Bombieri–Vaaler's Theorem 2 in height form (Layer 5.2).

⚠ **The anisotropy of the body is paid here, not in the slice bound.** `MixedCube.lean` normalises
every factor of the body to volume one, so the slice bound is `1`; converting a point of `λ · B`
into a height then costs `(λ/2)` at each real place and `(λ/√π)^2` at each complex one, which is
where `2^{−r₁ k} π^{−r₂ k}` enters. The two normalisations cannot be undone by a dilation, because
they differ from place to place.

⚠ **The rank hypothesis of the milestone is unnecessary.** The matrix form is stated for an
arbitrary `A`: Layer 3.5's `Matrix.arakelovMulHeight_ker_mulVecLin` identifies the height of the
solution space with the height of the row space with no hypothesis on `A`, and the geometric half
never looks at `A`. Stating `LinearIndependent K A.row` would only fix `k = N − M`.

⚠ **`k = 0` needs no special case**, and the extraction of Layer 4.4 is applied to `ℚ`-linearity:
both as in Layer 5.3, whose implementation notes spell them out. The two milestones share
everything but the body.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Theorem 2.9.4 and Remark 2.9.5.

E. Bombieri and J. D. Vaaler, *On Siegel's lemma*, Invent. Math. **73** (1983), Theorem 8.

J. D. Vaaler, "The best constant in Siegel's lemma", *Monatshefte für Mathematik* **140** (2003),
71–89, (1.4) and the remark on cube slicing.

D. Roy and J. L. Thunder, "A note on Siegel's lemma over number fields", *Monatshefte für
Mathematik* **120** (1995), 307–318, for the fact that some power of the discriminant must appear.

This is Layer 5.4 of the `ArithmeticHeights` roadmap.
-/

public section

open scoped Real

namespace NumberField.mixedEmbedding

open Module MeasureTheory NumberField NumberField.InfinitePlace
open scoped Pointwise

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

open scoped Classical in
omit [Fintype ι] in
theorem abs_realCoord_mixedPiEmb (w : {w : InfinitePlace K // IsReal w}) (x : ι → K) (j : ι) :
    |realCoord K ι w j (mixedPiEmb K ι x)| = w.1 (x j) := by
  have hs : (toMixedPi K ι).symm (mixedPiEmb K ι x) = fun l ↦ mixedEmbedding K (x l) := by
    rw [mixedPiEmb_apply]
    exact (toMixedPi K ι).symm_apply_apply _
  have hval : realCoord K ι w j (mixedPiEmb K ι x)
      = (((toMixedPi K ι).symm (mixedPiEmb K ι x)) j).1 w := rfl
  have hw : w.1 (x j) = ‖(mixedEmbedding K (x j)).1 w‖ := by
    rw [← normAtPlace_apply_of_isReal w.2, normAtPlace_apply]
  rw [hval, hs, hw, Real.norm_eq_abs]

open scoped Classical in
omit [Fintype ι] in
theorem norm_complexCoord_mixedPiEmb (w : {w : InfinitePlace K // IsComplex w}) (x : ι → K)
    (j : ι) : ‖complexCoord K ι w j (mixedPiEmb K ι x)‖ = w.1 (x j) := by
  have hs : (toMixedPi K ι).symm (mixedPiEmb K ι x) = fun l ↦ mixedEmbedding K (x l) := by
    rw [mixedPiEmb_apply]
    exact (toMixedPi K ι).symm_apply_apply _
  have hval : complexCoord K ι w j (mixedPiEmb K ι x)
      = (((toMixedPi K ι).symm (mixedPiEmb K ι x)) j).2 w := rfl
  have hw : w.1 (x j) = ‖(mixedEmbedding K (x j)).2 w‖ := by
    rw [← normAtPlace_apply_of_isComplex w.2, normAtPlace_apply]
  rw [hval, hs, hw]

open scoped Classical in
omit [Fintype ι] in
theorem iSup_le_of_mem_smul_mixedCube_isReal {r : ℝ} (hr : 0 < r) {x : ι → K}
    (hmem : mixedPiEmb K ι x ∈ r • mixedCube K ι) (w : {w : InfinitePlace K // IsReal w}) :
    (⨆ j, w.1 (x j)) ≤ r * ballRadius 1 := by
  rw [mem_smul_mixedCube hr] at hmem
  refine Real.iSup_le (fun j ↦ ?_) (mul_nonneg hr.le (ballRadius_pos 1).le)
  rw [← abs_realCoord_mixedPiEmb w x j]
  exact hmem.1 w j

open scoped Classical in
omit [Fintype ι] in
theorem iSup_le_of_mem_smul_mixedCube_isComplex {r : ℝ} (hr : 0 < r) {x : ι → K}
    (hmem : mixedPiEmb K ι x ∈ r • mixedCube K ι) (w : {w : InfinitePlace K // IsComplex w}) :
    (⨆ j, w.1 (x j)) ≤ r * ballRadius 2 := by
  rw [mem_smul_mixedCube hr] at hmem
  refine Real.iSup_le (fun j ↦ ?_) (mul_nonneg hr.le (ballRadius_pos 2).le)
  rw [← norm_complexCoord_mixedPiEmb w x j]
  exact hmem.2 w j

omit [Fintype ι] in
open scoped Classical in
/-- **The sup-norm height of an integral tuple in a dilate of the body.** -/
theorem mulHeight_le_of_mem_smul_mixedCube [Finite ι] {r : ℝ} (hr : 0 < r) {x : ι → K}
    (hx : x ≠ 0)
    (hint : ∀ l, ∃ z : 𝓞 K, (z : K) = x l)
    (hmem : mixedPiEmb K ι x ∈ r • mixedCube K ι) :
    Height.mulHeight x ≤ (r * ballRadius 1) ^ nrRealPlaces K
      * ((r * ballRadius 2) ^ 2) ^ nrComplexPlaces K := by
  have hb1 : (0 : ℝ) ≤ r * ballRadius 1 := mul_nonneg hr.le (ballRadius_pos 1).le
  have hb2 : (0 : ℝ) ≤ r * ballRadius 2 := mul_nonneg hr.le (ballRadius_pos 2).le
  have harch : (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult)
      ≤ (r * ballRadius 1) ^ nrRealPlaces K * ((r * ballRadius 2) ^ 2) ^ nrComplexPlaces K := by
    rw [← Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset (InfinitePlace K))
      (fun v ↦ v.IsReal)]
    refine mul_le_mul ?_ ?_
      (Finset.prod_nonneg fun v _ ↦ pow_nonneg (Real.iSup_nonneg fun i ↦ apply_nonneg _ _) _)
      (by positivity)
    · calc ∏ v ∈ Finset.univ.filter (fun v : InfinitePlace K ↦ v.IsReal),
              (⨆ i, v (x i)) ^ v.mult
          ≤ ∏ _v ∈ Finset.univ.filter (fun v : InfinitePlace K ↦ v.IsReal), (r * ballRadius 1) := by
            refine Finset.prod_le_prod₀
              (fun v _ ↦ pow_nonneg (Real.iSup_nonneg fun i ↦ apply_nonneg _ _) _) fun v hv ↦ ?_
            rw [Finset.mem_filter] at hv
            rw [show v.mult = 1 from mult_isReal ⟨v, hv.2⟩, pow_one]
            exact iSup_le_of_mem_smul_mixedCube_isReal hr hmem ⟨v, hv.2⟩
        _ = (r * ballRadius 1) ^ nrRealPlaces K := by
            rw [Finset.prod_const, ← Fintype.card_subtype]
    · calc ∏ v ∈ Finset.univ.filter (fun v : InfinitePlace K ↦ ¬ v.IsReal),
              (⨆ i, v (x i)) ^ v.mult
          ≤ ∏ _v ∈ Finset.univ.filter (fun v : InfinitePlace K ↦ ¬ v.IsReal),
              ((r * ballRadius 2) ^ 2) := by
            refine Finset.prod_le_prod₀
              (fun v _ ↦ pow_nonneg (Real.iSup_nonneg fun i ↦ apply_nonneg _ _) _) fun v hv ↦ ?_
            rw [Finset.mem_filter] at hv
            have hc : v.IsComplex := not_isReal_iff_isComplex.1 hv.2
            rw [show v.mult = 2 from mult_isComplex ⟨v, hc⟩]
            exact pow_le_pow_left₀ (Real.iSup_nonneg fun i ↦ apply_nonneg _ _)
              (iSup_le_of_mem_smul_mixedCube_isComplex hr hmem ⟨v, hc⟩) 2
        _ = ((r * ballRadius 2) ^ 2) ^ nrComplexPlaces K := by
            rw [Finset.prod_const, ← Fintype.card_subtype]
            congr 1
            exact Fintype.card_congr (Equiv.subtypeEquivRight fun _ ↦ not_isReal_iff_isComplex)
  have hfin := finprod_finitePlace_le_one hx hint
  have hfin0 : 0 ≤ ∏ᶠ v : FinitePlace K, ⨆ i, v (x i) :=
    finprod_nonneg fun v ↦ Real.iSup_nonneg fun i ↦ apply_nonneg _ _
  have harch0 : 0 ≤ ∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult :=
    Finset.prod_nonneg fun v _ ↦ pow_nonneg (Real.iSup_nonneg fun i ↦ apply_nonneg _ _) _
  rw [NumberField.mulHeight_eq hx]
  calc (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult) * ∏ᶠ v : FinitePlace K, ⨆ i, v (x i)
      ≤ ((r * ballRadius 1) ^ nrRealPlaces K * ((r * ballRadius 2) ^ 2) ^ nrComplexPlaces K) * 1 :=
        mul_le_mul harch hfin hfin0 (by positivity)
    _ = _ := mul_one _

end NumberField.mixedEmbedding

namespace NumberField.mixedEmbedding

open Module MeasureTheory NumberField NumberField.InfinitePlace
open scoped Pointwise

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

omit [Fintype ι] in
open scoped Classical in
theorem mulHeight_le_pow_of_mem_smul_mixedCube [Finite ι] {r : ℝ} (hr : 0 < r) {x : ι → K}
    (hx : x ≠ 0)
    (hint : ∀ l, ∃ z : 𝓞 K, (z : K) = x l)
    (hmem : mixedPiEmb K ι x ∈ r • mixedCube K ι) :
    Height.mulHeight x ≤ ((2 : ℝ)⁻¹ ^ nrRealPlaces K * (π : ℝ)⁻¹ ^ nrComplexPlaces K)
      * r ^ finrank ℚ K := by
  refine (mulHeight_le_of_mem_smul_mixedCube hr hx hint hmem).trans (le_of_eq ?_)
  have hb2 : (ballRadius 2) ^ 2 = (π : ℝ)⁻¹ := by
    rw [ballRadius_two, div_pow, one_pow, Real.sq_sqrt Real.pi_pos.le, inv_eq_one_div]
  have e1 : (r * ballRadius 1) ^ nrRealPlaces K
      = (2 : ℝ)⁻¹ ^ nrRealPlaces K * r ^ nrRealPlaces K := by
    rw [ballRadius_one, mul_pow, one_div]; ring
  have e2 : ((r * ballRadius 2) ^ 2) ^ nrComplexPlaces K
      = (π : ℝ)⁻¹ ^ nrComplexPlaces K * r ^ (2 * nrComplexPlaces K) := by
    rw [mul_pow, hb2, mul_pow, ← pow_mul]; ring
  rw [e1, e2, ← InfinitePlace.card_add_two_mul_card_eq_rank K, pow_add]
  ring

section Span

variable [LinearOrder ι] (V : Submodule K (ι → K))

omit [Fintype ι] [LinearOrder ι] in
open scoped Classical in
theorem convex_preimage_mixedCube :
    Convex ℝ ((Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedCube K ι) :=
  convex_mixedCube.linear_preimage (V.mixedSpan.subtype)

omit [Fintype ι] [LinearOrder ι] in
open scoped Classical in
theorem neg_mem_preimage_mixedCube {x : ↥V.mixedSpan}
    (hx : x ∈ (Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedCube K ι) :
    -x ∈ (Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedCube K ι := by
  simpa using neg_mem_mixedCube hx

omit [Fintype ι] [LinearOrder ι] in
open scoped Classical in
theorem isClosed_preimage_mixedCube [Finite ι] :
    IsClosed ((Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedCube K ι) :=
  isClosed_mixedCube.preimage continuous_subtype_val

omit [Fintype ι] [LinearOrder ι] in
open scoped Classical in
theorem isBounded_preimage_mixedCube [Finite ι] :
    Bornology.IsBounded ((Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedCube K ι) := by
  let _i : Fintype ι := Fintype.ofFinite ι
  obtain ⟨M, hM⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : mixedPi K ι)).1 (isBounded_mixedCube (K := K))
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨M, fun x hx ↦ ?_⟩
  have h := hM hx
  rw [mem_closedBall_zero_iff] at h ⊢
  exact h

omit [Fintype ι] [LinearOrder ι] in
open scoped Classical in
theorem interior_preimage_mixedCube_nonempty [Finite ι] :
    (interior ((Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedCube K ι)).Nonempty := by
  let _i : Fintype ι := Fintype.ofFinite ι
  refine ⟨0, ?_⟩
  rw [mem_interior_iff_mem_nhds]
  refine continuous_subtype_val.continuousAt.preimage_mem_nhds ?_
  exact convex_mixedCube.mem_nhds_zero_of_symmetric (fun x hx ↦ neg_mem_mixedCube hx)
    interior_mixedCube_nonempty

open scoped Classical in
/-- **Minkowski's second theorem for the sup-norm body over a number field.** -/
theorem prod_successiveMinimum_mixedCube_le :
    (∏ i ∈ Finset.range (finrank ℚ K * finrank K V),
        ZLattice.successiveMinimum V.mixedLattice
          ((Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedCube K ι) i)
      ≤ (2 : ℝ) ^ (finrank ℚ K * finrank K V)
          * (((2 : ℝ)⁻¹ ^ nrComplexPlaces K * Real.sqrt |(NumberField.discr K : ℝ)|)
              ^ finrank K V * V.arakelovMulHeight) := by
  have hmink := ZLattice.prod_successiveMinimum_mul_measure_le V.mixedLattice volume
    (convex_preimage_mixedCube V) (fun x hx ↦ neg_mem_preimage_mixedCube V hx)
    (interior_preimage_mixedCube_nonempty V) (isBounded_preimage_mixedCube V)
  rw [V.finrank_mixedSpan, Submodule.covolume_mixedLattice] at hmink
  have hfinite : volume ((Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedCube K ι) ≠ ⊤ :=
    (isBounded_preimage_mixedCube V).measure_lt_top.ne
  have hvol1 : (1 : ℝ)
      ≤ (volume ((Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedCube K ι)).toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hfinite (one_le_volume_preimage_mixedCube _)
  have hprod0 : 0 ≤ ∏ i ∈ Finset.range (finrank ℚ K * finrank K V),
      ZLattice.successiveMinimum V.mixedLattice
        ((Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedCube K ι) i :=
    Finset.prod_nonneg fun i hi ↦ (ZLattice.successiveMinimum_pos V.mixedLattice
      (convex_preimage_mixedCube V) (fun x hx ↦ neg_mem_preimage_mixedCube V hx)
      (interior_preimage_mixedCube_nonempty V) (isBounded_preimage_mixedCube V)
      (by rw [V.finrank_mixedSpan]; exact Finset.mem_range.1 hi)).le
  refine le_trans ?_ hmink
  nlinarith [hprod0, hvol1]

end Span

end NumberField.mixedEmbedding
namespace NumberField

open Module MeasureTheory NumberField NumberField.InfinitePlace Matrix
open NumberField.mixedEmbedding
open scoped Pointwise

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

section Main

variable [LinearOrder ι] (V : Submodule K (ι → K))

open scoped Classical in
/-- **Layer 5.4, the relative form.** -/
theorem exists_basis_prod_mulHeight_le :
    ∃ x : Fin (finrank K V) → (ι → K), LinearIndependent K x ∧
      (∀ l, x l ∈ V.integerPoints) ∧
      (∏ l, Height.mulHeight (x l))
        ≤ (2 / π) ^ (finrank K V * nrComplexPlaces K)
            * (Real.sqrt |(NumberField.discr K : ℝ)| ^ finrank K V * V.arakelovMulHeight) := by
  set B : Set ↥V.mixedSpan := (Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedCube K ι with hB
  have hconv := convex_preimage_mixedCube V
  have hsymm : ∀ z ∈ B, -z ∈ B := fun z hz ↦ neg_mem_preimage_mixedCube V hz
  have hintn := interior_preimage_mixedCube_nonempty V
  have hbdd := isBounded_preimage_mixedCube V
  have hcl := isClosed_preimage_mixedCube V
  obtain ⟨v, hvL, hvind, hvmem⟩ :=
    ZLattice.exists_linearIndependent_mem_smul_successiveMinimum V.mixedLattice hconv hsymm hintn
      hbdd hcl
  have hfr : finrank ℝ ↥V.mixedSpan = finrank ℚ K * finrank K V := V.finrank_mixedSpan
  set e : Fin (finrank ℚ K * finrank K V) ≃ Fin (finrank ℝ ↥V.mixedSpan) := finCongr hfr.symm
    with he
  have hlift : ∀ j, ∃ z ∈ V.integerPoints, mixedPiEmb K ι z = ((v (e j) : mixedPi K ι)) :=
    fun j ↦ (mem_mixedLattice_iff V).1 (hvL (e j))
  choose x hxmem hxemb using hlift
  set fQ : (ι → K) →ₗ[ℚ] mixedPi K ι := (mixedPiEmb K ι).toAddMonoidHom.toRatLinearMap with hfQ
  have hindR : LinearIndependent ℝ (fQ ∘ x) := by
    have h1 : LinearIndependent ℝ (fun j ↦ v (e j)) := hvind.comp e e.injective
    have h2 : LinearIndependent ℝ (fun j ↦ ((v (e j) : mixedPi K ι))) :=
      h1.map' (V.mixedSpan.subtype) (Submodule.ker_subtype _)
    have hfQapp : ∀ z, fQ z = mixedPiEmb K ι z := fun z ↦ rfl
    simpa only [Function.comp_def, hfQapp, hxemb] using h2
  obtain ⟨s, hsind, hsle⟩ :=
    LinearIndependent.exists_linearIndependent_comp_finrank_mul (F := ℚ) (E := ℝ) fQ hindR
  refine ⟨x ∘ s, hsind, fun l ↦ hxmem _, ?_⟩
  set lam : ℕ → ℝ := ZLattice.successiveMinimum V.mixedLattice B with hlam
  set C : ℝ := (2 : ℝ)⁻¹ ^ nrRealPlaces K * (π : ℝ)⁻¹ ^ nrComplexPlaces K with hC
  have hCpos : 0 < C := by
    have := Real.pi_pos
    positivity
  have hdpos : 0 < finrank ℚ K := Module.finrank_pos
  have hlampos : ∀ i, i < finrank ℚ K * finrank K V → 0 < lam i := fun i hi ↦
    ZLattice.successiveMinimum_pos V.mixedLattice hconv hsymm hintn hbdd (by rw [hfr]; exact hi)
  have hlamnn : ∀ i, 0 ≤ lam i := by
    intro i
    rcases lt_or_ge i (finrank ℚ K * finrank K V) with h | h
    · exact (hlampos i h).le
    · rw [hlam, ZLattice.successiveMinimum_eq_zero_of_le _ _ (by rw [hfr]; exact h)]
  have hlammono : ∀ i j, i ≤ j → j < finrank ℚ K * finrank K V → lam i ≤ lam j :=
    fun i j hij hj ↦
      ZLattice.successiveMinimum_le_of_le hij (by rw [hfr]; exact hj) hconv hsymm hintn
  have hsmulcoe : ∀ (r : ℝ) (z : ↥V.mixedSpan), z ∈ r • B →
      (z : mixedPi K ι) ∈ r • mixedCube K ι := by
    rintro r z ⟨b, hb, rfl⟩
    exact ⟨(b : mixedPi K ι), hb, by simp⟩
  have hheight : ∀ l : Fin (finrank K V),
      Height.mulHeight ((x ∘ s) l) ≤ C * lam (finrank ℚ K * l.val) ^ finrank ℚ K := by
    intro l
    have hsl : (s l).val < finrank ℚ K * finrank K V := (s l).isLt
    have hdl : finrank ℚ K * l.val < finrank ℚ K * finrank K V :=
      (Nat.mul_lt_mul_left hdpos).2 l.isLt
    have hmem : mixedPiEmb K ι (x (s l)) ∈ (lam (s l).val) • mixedCube K ι := by
      have h := hsmulcoe _ _ (hvmem (e (s l)))
      rwa [← hxemb (s l)] at h
    have hintg : ∀ j, ∃ z : 𝓞 K, (z : K) = (x (s l)) j :=
      (Submodule.mem_integerPoints.1 (hxmem (s l))).2
    have h1 : Height.mulHeight (x (s l)) ≤ C * (lam (s l).val) ^ finrank ℚ K :=
      mulHeight_le_pow_of_mem_smul_mixedCube (hlampos _ hsl) (hsind.ne_zero l) hintg hmem
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (hlampos _ hsl).le (hlammono _ _ (hsle l) hdl) _) hCpos.le
  have key : ∀ (t h : ℝ) (a b k : ℕ),
      ((2 : ℝ)⁻¹ ^ a * (π : ℝ)⁻¹ ^ b) ^ k * ((2 : ℝ) ^ ((a + 2 * b) * k)
          * (((2 : ℝ)⁻¹ ^ b * t) ^ k * h))
        = (2 / π : ℝ) ^ (k * b) * (t ^ k * h) := by
    intro t h a b k
    have hπ : π ≠ 0 := Real.pi_ne_zero
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_pow, ← pow_mul, div_pow]
    simp only [inv_pow]
    field_simp
    ring
  calc (∏ l, Height.mulHeight ((x ∘ s) l))
      ≤ ∏ l : Fin (finrank K V), C * lam (finrank ℚ K * l.val) ^ finrank ℚ K :=
        Finset.prod_le_prod₀ (fun l _ ↦ (Height.mulHeight_pos _).le) fun l _ ↦ hheight l
    _ = C ^ finrank K V * ∏ l : Fin (finrank K V), lam (finrank ℚ K * l.val) ^ finrank ℚ K := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ C ^ finrank K V * ∏ j ∈ Finset.range (finrank ℚ K * finrank K V), lam j := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [Fin.prod_univ_eq_prod_range (fun i ↦ lam (finrank ℚ K * i) ^ finrank ℚ K)]
        exact Finset.prod_pow_le_prod_range hlamnn hlammono _ _ le_rfl
    _ ≤ C ^ finrank K V * ((2 : ℝ) ^ (finrank ℚ K * finrank K V)
          * (((2 : ℝ)⁻¹ ^ nrComplexPlaces K * Real.sqrt |(NumberField.discr K : ℝ)|)
              ^ finrank K V * V.arakelovMulHeight)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact prod_successiveMinimum_mixedCube_le V
    _ = (2 / π) ^ (finrank K V * nrComplexPlaces K)
          * (Real.sqrt |(NumberField.discr K : ℝ)| ^ finrank K V * V.arakelovMulHeight) := by
        rw [hC, ← InfinitePlace.card_add_two_mul_card_eq_rank K]
        exact key _ _ _ _ _

open scoped Classical in
/-- **Layer 5.4, the absolute form, at Bombieri–Vaaler's constant.** -/
theorem exists_basis_prod_absMulHeight_le' :
    ∃ x : Fin (finrank K V) → (ι → K), LinearIndependent K x ∧
      (∀ l, x l ∈ V.integerPoints) ∧
      (∏ l, absMulHeight (x l))
        ≤ (2 / π) ^ ((finrank K V * nrComplexPlaces K : ℝ) / finrank ℚ K)
          * |(NumberField.discr K : ℝ)| ^ ((finrank K V : ℝ) / (2 * finrank ℚ K))
          * V.arakelovMulHeight ^ (finrank ℚ K : ℝ)⁻¹ := by
  obtain ⟨x, hind, hmem, hle⟩ := exists_basis_prod_mulHeight_le V
  refine ⟨x, hind, hmem, ?_⟩
  have hdne : ((finrank ℚ K : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 (Module.finrank_pos).ne'
  have hHpos := V.arakelovMulHeight_pos
  have hprod : (∏ l, absMulHeight (x l))
      = (∏ l, Height.mulHeight (x l)) ^ (finrank ℚ K : ℝ)⁻¹ := by
    rw [← Real.finsetProd_rpow _ _ (fun l _ ↦ (Height.mulHeight_pos _).le) _]
    exact Finset.prod_congr rfl fun l _ ↦ absMulHeight_eq _
  rw [hprod]
  have hstep := Real.rpow_le_rpow (Finset.prod_nonneg fun l _ ↦ (Height.mulHeight_pos _).le)
    hle (by positivity : (0 : ℝ) ≤ (finrank ℚ K : ℝ)⁻¹)
  refine hstep.trans (le_of_eq ?_)
  have hD : (Real.sqrt |(NumberField.discr K : ℝ)| ^ finrank K V) ^ ((finrank ℚ K : ℝ))⁻¹
      = |(NumberField.discr K : ℝ)| ^ ((finrank K V : ℝ) / (2 * finrank ℚ K)) := by
    rw [Real.sqrt_eq_rpow,
      ← Real.rpow_natCast (|(NumberField.discr K : ℝ)| ^ (1 / 2 : ℝ)) (finrank K V),
      ← Real.rpow_mul (abs_nonneg _), ← Real.rpow_mul (abs_nonneg _)]
    congr 1
    field_simp
  have hpi : ((2 / π : ℝ) ^ (finrank K V * nrComplexPlaces K)) ^ ((finrank ℚ K : ℝ))⁻¹
      = (2 / π : ℝ) ^ ((finrank K V * nrComplexPlaces K : ℝ) / finrank ℚ K) := by
    have h0 : (0 : ℝ) ≤ 2 / π := by positivity
    rw [← Real.rpow_natCast (2 / π : ℝ) (finrank K V * nrComplexPlaces K), ← Real.rpow_mul h0]
    congr 1
    push_cast
    ring
  rw [Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity), hD, hpi]
  ring

open scoped Classical in
/-- **Layer 5.4, the absolute form** in the shape the literature states it. -/
theorem exists_basis_prod_absMulHeight_le :
    ∃ x : Fin (finrank K V) → (ι → K), LinearIndependent K x ∧
      (∀ l, x l ∈ V.integerPoints) ∧
      (∏ l, absMulHeight (x l))
        ≤ |(NumberField.discr K : ℝ)| ^ ((finrank K V : ℝ) / (2 * finrank ℚ K))
          * V.arakelovMulHeight ^ (finrank ℚ K : ℝ)⁻¹ := by
  obtain ⟨x, hind, hmem, hle⟩ := exists_basis_prod_absMulHeight_le' V
  refine ⟨x, hind, hmem, hle.trans ?_⟩
  have hpi1 : (2 / π : ℝ) ^ ((finrank K V * nrComplexPlaces K : ℝ) / finrank ℚ K) ≤ 1 := by
    refine Real.rpow_le_one (by positivity) ?_ (by positivity)
    rw [div_le_one Real.pi_pos]
    linarith [Real.pi_gt_three]
  have hpos : (0 : ℝ) ≤ |(NumberField.discr K : ℝ)| ^ ((finrank K V : ℝ) / (2 * finrank ℚ K))
      * V.arakelovMulHeight ^ (finrank ℚ K : ℝ)⁻¹ :=
    mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
      (Real.rpow_nonneg V.arakelovMulHeight_pos.le _)
  rw [mul_assoc]
  exact mul_le_of_le_one_left hpos hpi1


end Main

section Kernel

variable [LinearOrder ι] {m : ℕ}

open scoped Classical in
/-- **Layer 5.4 — Bombieri–Vaaler over a number field, max-norm form, at their own constant.** -/
theorem exists_basis_ker_prod_absMulHeight_le' {μ : Type*} (A : Matrix μ ι K) {k : ℕ}
    (hk : finrank K (LinearMap.ker A.mulVecLin) = k) :
    ∃ b : Basis (Fin k) K ↥(LinearMap.ker A.mulVecLin),
      (∀ l j, IsIntegral ℤ ((b l : ι → K) j)) ∧
      (∏ l, absMulHeight (fun j ↦ (b l : ι → K) j)) ≤
        (2 / π) ^ ((k * nrComplexPlaces K : ℝ) / finrank ℚ K)
          * |(NumberField.discr K : ℝ)| ^ ((k : ℝ) / (2 * finrank ℚ K))
          * (Submodule.span K (Set.range A.row)).arakelovMulHeight ^ (finrank ℚ K : ℝ)⁻¹ := by
  subst hk
  obtain ⟨x, hind, hmem, hle⟩ :=
    exists_basis_prod_absMulHeight_le' (LinearMap.ker A.mulVecLin)
  have hxV : ∀ l, x l ∈ LinearMap.ker A.mulVecLin :=
    fun l ↦ (Submodule.mem_integerPoints.1 (hmem l)).1
  have hind' : LinearIndependent K (fun l ↦ (⟨x l, hxV l⟩ : ↥(LinearMap.ker A.mulVecLin))) :=
    LinearIndependent.of_comp (LinearMap.ker A.mulVecLin).subtype hind
  have hsp : Submodule.span K
      (Set.range (fun l ↦ (⟨x l, hxV l⟩ : ↥(LinearMap.ker A.mulVecLin)))) = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [finrank_span_eq_card hind', Fintype.card_fin]
  refine ⟨Basis.mk hind' (le_of_eq hsp.symm), ?_, ?_⟩
  · intro l j
    rw [Basis.coe_mk]
    obtain ⟨z, hz⟩ := (Submodule.mem_integerPoints.1 (hmem l)).2 j
    rw [show ((⟨x l, hxV l⟩ : ↥(LinearMap.ker A.mulVecLin)) : ι → K) j = x l j from rfl, ← hz]
    exact z.2
  · rw [Basis.coe_mk, ← Matrix.arakelovMulHeight_ker_mulVecLin A]
    exact hle

open scoped Classical in
/-- **Layer 5.4 — Bombieri–Vaaler over a number field, max-norm form: the summit.** -/
theorem exists_basis_ker_prod_absMulHeight_le {μ : Type*} (A : Matrix μ ι K) {k : ℕ}
    (hk : finrank K (LinearMap.ker A.mulVecLin) = k) :
    ∃ b : Basis (Fin k) K ↥(LinearMap.ker A.mulVecLin),
      (∀ l j, IsIntegral ℤ ((b l : ι → K) j)) ∧
      (∏ l, absMulHeight (fun j ↦ (b l : ι → K) j)) ≤
        |(NumberField.discr K : ℝ)| ^ ((k : ℝ) / (2 * finrank ℚ K))
          * (Submodule.span K (Set.range A.row)).arakelovMulHeight ^ (finrank ℚ K : ℝ)⁻¹ := by
  obtain ⟨b, hint, hle⟩ := exists_basis_ker_prod_absMulHeight_le' A hk
  refine ⟨b, hint, hle.trans ?_⟩
  have hpi1 : (2 / π : ℝ) ^ ((k * nrComplexPlaces K : ℝ) / finrank ℚ K) ≤ 1 := by
    refine Real.rpow_le_one (by positivity) ?_ (by positivity)
    rw [div_le_one Real.pi_pos]
    linarith [Real.pi_gt_three]
  have hpos : (0 : ℝ) ≤ |(NumberField.discr K : ℝ)| ^ ((k : ℝ) / (2 * finrank ℚ K))
      * (Submodule.span K (Set.range A.row)).arakelovMulHeight ^ (finrank ℚ K : ℝ)⁻¹ :=
    mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
      (Real.rpow_nonneg (Submodule.arakelovMulHeight_pos _).le _)
  rw [mul_assoc]
  exact mul_le_of_le_one_left hpos hpi1

end Kernel


end NumberField
