/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.Duality
public import ArithmeticHeights.Extraction
public import ArithmeticHeights.MinkowskiSecond
public import ArithmeticHeights.MixedBall
public import Mathlib.Algebra.Module.LinearMap.Rat

/-!
# Bombieri–Vaaler over a number field: the Hermitian form

**Bombieri–Vaaler 1983; the inequality Vaaler 2003 quotes as (1.3).** Let `K` be a number field of
degree `d` with `r₁` real and `r₂` complex places and discriminant `D`, and let `V ⊆ Kⁱ` be a
subspace of dimension `k`. Then `V` has a basis `x₁, …, x_k` of vectors with coordinates in
`𝓞 K` and

```text
∏_{l} H_Ar(x l)  ≤  (2^k / ω_k)^{r₁} (2^k / ω_{2k})^{r₂} · |D|^{k/2} · H_Ar(V),
```

relative Arakelov heights on both sides, `ω_n` the volume of the unit ball of `ℝⁿ`; taking `d`-th
roots gives the absolute form the literature states. For `V` the solution space of `A x = 0` the
right-hand side is the Arakelov height of the **row space** of `A`, by the duality theorem of
Layer 3.5.

## Main results

* `NumberField.exists_basis_prod_arakelovMulHeight_le`: the displayed inequality.
* `NumberField.exists_basis_prod_arakelovMulHeight_rpow_le`: its absolute form, all heights raised
  to the power `1/d`.
* `NumberField.exists_basis_ker_prod_arakelovMulHeight_rpow_le`: the matrix form — a basis of the
  solution space of `A x = 0`, bounded by the Arakelov height of the row space of `A`.
* `NumberField.mixedEmbedding.arakelovMulHeight_le_of_mem_smul_mixedBall`: the height of an
  integral tuple lying in `λ · mixedBall` is at most `λ ^ d`.
* `NumberField.mixedEmbedding.prod_successiveMinimum_mixedBall_le`: Minkowski's second theorem for
  the ℓ² body, with the covolume of Layer 4.3 and the slice volume of `MixedBall.lean` inserted.

## Implementation notes

⚠ **The constant is `2^{d k}` from Layer 4.2 against `2^{−r₂ k}` from Layer 4.3, and what survives
is `2^{k(r₁ + r₂)}`.** Over `ℤ` the two powers of two cancelled exactly (Layer 5.2); here they do
not, because the unit balls of the ℓ² norms are not the unit cubes, and the residue
`(2^k/ω_k)^{r₁} (2^k/ω_{2k})^{r₂}` is exactly the ratio between a cube and a ball. Layer 5.4
replaces the balls by cubes and polydiscs, and that is where cube slicing is needed.

⚠ **The rank hypothesis of the milestone is unnecessary.** The matrix form is stated for an
arbitrary `A`: Layer 3.5's `Matrix.arakelovMulHeight_ker_mulVecLin` identifies the height of the
solution space with the height of the row space with no hypothesis on `A`, and the geometric half
never looks at `A` at all. Stating `LinearIndependent K A.row` would only fix `k = N − M`.

⚠ **`k = 0` needs no special case.** The empty product is `1`, and Minkowski's second theorem
applied to the zero-dimensional lattice gives `1 ≤ C · H_Ar(V)` directly; no value of `ω_0` is
ever needed. For the same reason the basis is built with `Basis.mk` and a rank count rather than
with `basisOfLinearIndependentOfCardEqFinrank`, which demands a nonempty index type.

⚠ **The extraction of Layer 4.4 is applied to `ℚ`-linearity, not `ℤ`-linearity.** The mixed
embedding is a `ℤ`-linear map, but the counting argument needs a map of `ℚ`-vector spaces;
`AddMonoidHom.toRatLinearMap` supplies it, since a `ℚ`-linear structure on an additive group is
unique.

## References

E. Bombieri and J. D. Vaaler, *On Siegel's lemma*, Invent. Math. **73** (1983), Theorem 9 and §I.

J. D. Vaaler, "The best constant in Siegel's lemma", *Monatshefte für Mathematik* **140** (2003),
71–89, (1.3).

W. M. Schmidt, "On heights of algebraic subspaces and diophantine approximations", *Annals of
Mathematics* **85** (1967), 430–472, §3, for the covolume identity this consumes.

This is Layer 5.3 of the `ArithmeticHeights` roadmap.
-/

public section

namespace NumberField.mixedEmbedding

open Module MeasureTheory NumberField NumberField.InfinitePlace Matrix
open scoped Pointwise

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

open scoped Classical in
theorem sq_norm_realPart_mixedPiEmb (w : {w : InfinitePlace K // IsReal w}) (x : ι → K) :
    ‖realPart K ι w (mixedPiEmb K ι x)‖ ^ 2 = ∑ j, w.1 (x j) ^ 2 := by
  have hs : (toMixedPi K ι).symm (mixedPiEmb K ι x) = fun l ↦ mixedEmbedding K (x l) := by
    rw [mixedPiEmb_apply]
    exact (toMixedPi K ι).symm_apply_apply _
  rw [realPart_apply, EuclideanSpace.sq_norm_toLp, hs]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hw : w.1 (x j) = ‖(mixedEmbedding K (x j)).1 w‖ := by
    rw [← normAtPlace_apply_of_isReal w.2, normAtPlace_apply]
  rw [hw, Real.norm_eq_abs, sq_abs]

open scoped Classical in
theorem sq_norm_complexPart_mixedPiEmb (w : {w : InfinitePlace K // IsComplex w}) (x : ι → K) :
    ‖complexPart K ι w (mixedPiEmb K ι x)‖ ^ 2 = ∑ j, w.1 (x j) ^ 2 := by
  have hs : (toMixedPi K ι).symm (mixedPiEmb K ι x) = fun l ↦ mixedEmbedding K (x l) := by
    rw [mixedPiEmb_apply]
    exact (toMixedPi K ι).symm_apply_apply _
  rw [complexPart_apply, EuclideanSpace.sq_norm_toLp_complex, hs]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hw : w.1 (x j) = ‖(mixedEmbedding K (x j)).2 w‖ := by
    rw [← normAtPlace_apply_of_isComplex w.2, normAtPlace_apply]
  rw [hw, Complex.sq_norm]

open scoped Classical in
theorem sum_sq_le_of_mem_smul_mixedBall {r : ℝ} (hr : 0 < r) {x : ι → K}
    (hmem : mixedPiEmb K ι x ∈ r • mixedBall K ι) (w : InfinitePlace K) :
    ∑ j, w (x j) ^ 2 ≤ r ^ 2 := by
  rw [mem_smul_mixedBall hr] at hmem
  rcases w.isReal_or_isComplex with h | h
  · have h1 := hmem.1 ⟨w, h⟩
    have h2 := sq_norm_realPart_mixedPiEmb (K := K) ⟨w, h⟩ x
    nlinarith [norm_nonneg (realPart K ι ⟨w, h⟩ (mixedPiEmb K ι x))]
  · have h1 := hmem.2 ⟨w, h⟩
    have h2 := sq_norm_complexPart_mixedPiEmb (K := K) ⟨w, h⟩ x
    nlinarith [norm_nonneg (complexPart K ι ⟨w, h⟩ (mixedPiEmb K ι x))]

omit [Fintype ι] in
open scoped Classical in
theorem finprod_finitePlace_le_one [Finite ι] {x : ι → K} (hx : x ≠ 0)
    (hint : ∀ l, ∃ z : 𝓞 K, (z : K) = x l) :
    (∏ᶠ v : FinitePlace K, ⨆ i, v (x i)) ≤ 1 := by
  choose z hz using hint
  have hzne : ∃ i, z i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (funext fun i ↦ by rw [← hz i, hcon i]; simp)
  have heq : (∏ᶠ v : FinitePlace K, ⨆ i, v (x i))
      = ∏ᶠ v : FinitePlace K, ⨆ i, v ((z i : K)) :=
    finprod_congr fun v ↦ iSup_congr fun i ↦ by rw [hz i]
  rw [heq, NumberField.FinitePlace.finprod_iSup_eq_inv_absNorm hzne]
  have hI : Ideal.span (Set.range z) ≠ (⊥ : Ideal (𝓞 K)) := by
    obtain ⟨i, hi⟩ := hzne
    exact fun h ↦ hi ((Ideal.span_eq_bot.1 h) (z i) ⟨i, rfl⟩)
  have h1 : (1 : ℝ) ≤ (Ideal.absNorm (Ideal.span (Set.range z)) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (fun h ↦ hI (Ideal.absNorm_eq_zero_iff.1 h))
  rw [inv_le_one_iff₀]
  exact Or.inr h1

open scoped Classical in
/-- **The height of an integral tuple in a dilate of the body.** -/
theorem arakelovMulHeight_le_of_mem_smul_mixedBall {r : ℝ} (hr : 0 < r) {x : ι → K}
    (hx : x ≠ 0) (hint : ∀ l, ∃ z : 𝓞 K, (z : K) = x l)
    (hmem : mixedPiEmb K ι x ∈ r • mixedBall K ι) :
    arakelovMulHeight x ≤ r ^ finrank ℚ K := by
  rw [arakelovMulHeight_eq hx]
  have hpow : ∀ n : ℕ, ((r ^ 2 : ℝ)) ^ ((n : ℝ) / 2) = r ^ n := by
    intro n
    rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le, ← Real.rpow_natCast r n]
    congr 1
    push_cast
    ring
  have harch : (∏ w : InfinitePlace K, (∑ i, w (x i) ^ 2) ^ (w.mult / 2 : ℝ))
      ≤ r ^ finrank ℚ K := by
    calc (∏ w : InfinitePlace K, (∑ i, w (x i) ^ 2) ^ (w.mult / 2 : ℝ))
        ≤ ∏ w : InfinitePlace K, r ^ w.mult := by
          refine Finset.prod_le_prod₀ (fun w _ ↦ Real.rpow_nonneg (by positivity) _)
            fun w _ ↦ ?_
          rw [← hpow w.mult]
          exact Real.rpow_le_rpow (by positivity)
            (sum_sq_le_of_mem_smul_mixedBall hr hmem w) (by positivity)
      _ = r ^ (∑ w : InfinitePlace K, w.mult) := by rw [Finset.prod_pow_eq_pow_sum]
      _ = r ^ finrank ℚ K := by rw [InfinitePlace.sum_mult_eq]
  have hfin := finprod_finitePlace_le_one hx hint
  have hfin0 : 0 ≤ ∏ᶠ v : FinitePlace K, ⨆ i, v (x i) :=
    finprod_nonneg fun v ↦ Real.iSup_nonneg fun i ↦ apply_nonneg _ _
  have harch0 : 0 ≤ ∏ w : InfinitePlace K, (∑ i, w (x i) ^ 2) ^ (w.mult / 2 : ℝ) :=
    Finset.prod_nonneg fun w _ ↦ Real.rpow_nonneg (by positivity) _
  calc (∏ w : InfinitePlace K, (∑ i, w (x i) ^ 2) ^ (w.mult / 2 : ℝ))
        * ∏ᶠ v : FinitePlace K, ⨆ i, v (x i)
      ≤ (r ^ finrank ℚ K) * 1 := mul_le_mul harch hfin hfin0 (by positivity)
    _ = r ^ finrank ℚ K := mul_one _

section Span

variable [LinearOrder ι] (V : Submodule K (ι → K))

omit [LinearOrder ι] in
open scoped Classical in
theorem convex_preimage_mixedBall :
    Convex ℝ ((Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedBall K ι) :=
  convex_mixedBall.linear_preimage (V.mixedSpan.subtype)

omit [LinearOrder ι] in
open scoped Classical in
theorem neg_mem_preimage_mixedBall {x : ↥V.mixedSpan}
    (hx : x ∈ (Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedBall K ι) :
    -x ∈ (Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedBall K ι := by
  simpa using neg_mem_mixedBall hx

omit [LinearOrder ι] in
open scoped Classical in
theorem isClosed_preimage_mixedBall :
    IsClosed ((Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedBall K ι) :=
  isClosed_mixedBall.preimage continuous_subtype_val

omit [LinearOrder ι] in
open scoped Classical in
theorem isBounded_preimage_mixedBall :
    Bornology.IsBounded ((Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedBall K ι) := by
  obtain ⟨M, hM⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : mixedPi K ι)).1 (isBounded_mixedBall (K := K))
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨M, fun x hx ↦ ?_⟩
  have h := hM hx
  rw [mem_closedBall_zero_iff] at h ⊢
  exact h

omit [LinearOrder ι] in
open scoped Classical in
theorem interior_preimage_mixedBall_nonempty :
    (interior ((Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedBall K ι)).Nonempty := by
  refine ⟨0, ?_⟩
  rw [mem_interior_iff_mem_nhds]
  refine continuous_subtype_val.continuousAt.preimage_mem_nhds ?_
  exact convex_mixedBall.mem_nhds_zero_of_symmetric (fun x hx ↦ neg_mem_mixedBall hx)
    interior_mixedBall_nonempty

open scoped Classical in
/-- **Minkowski's second theorem for the ℓ² body over a number field.** -/
theorem prod_successiveMinimum_mixedBall_le :
    (∏ i ∈ Finset.range (finrank ℚ K * finrank K V),
        ZLattice.successiveMinimum V.mixedLattice
          ((Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedBall K ι) i)
      ≤ ((2 : ℝ) ^ finrank K V / unitBallVolume (finrank K V)) ^ nrRealPlaces K
          * ((2 : ℝ) ^ finrank K V / unitBallVolume (2 * finrank K V)) ^ nrComplexPlaces K
          * (Real.sqrt |(NumberField.discr K : ℝ)| ^ finrank K V * V.arakelovMulHeight) := by
  have hmink := ZLattice.prod_successiveMinimum_mul_measure_le V.mixedLattice volume
    (convex_preimage_mixedBall V) (fun x hx ↦ neg_mem_preimage_mixedBall V hx)
    (interior_preimage_mixedBall_nonempty V) (isBounded_preimage_mixedBall V)
  rw [V.finrank_mixedSpan] at hmink
  have hvol : (volume ((Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedBall K ι)).toReal
      = unitBallVolume (finrank K V) ^ nrRealPlaces K
        * unitBallVolume (2 * finrank K V) ^ nrComplexPlaces K := by
    rw [volume_preimage_mixedBall_mixedSpan, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal (unitBallVolume_pos _).le,
      ENNReal.toReal_ofReal (unitBallVolume_pos _).le]
  rw [hvol, Submodule.covolume_mixedLattice] at hmink
  have hvolpos : 0 < unitBallVolume (finrank K V) ^ nrRealPlaces K
      * unitBallVolume (2 * finrank K V) ^ nrComplexPlaces K := by
    have h1 := unitBallVolume_pos (finrank K V)
    have h2 := unitBallVolume_pos (2 * finrank K V)
    positivity
  have key : ∀ (s h w1 w2 : ℝ) (a b k : ℕ), w1 ≠ 0 → w2 ≠ 0 →
      (2 : ℝ) ^ ((a + 2 * b) * k) * (((2 : ℝ)⁻¹ ^ b * s) ^ k * h)
        = ((2 : ℝ) ^ k / w1) ^ a * ((2 : ℝ) ^ k / w2) ^ b * (s ^ k * h) * (w1 ^ a * w2 ^ b) := by
    intro s h w1 w2 a b k hw1 hw2
    have e1 : (((2 : ℝ)⁻¹ ^ b) * s) ^ k = ((2 : ℝ) ^ (b * k))⁻¹ * s ^ k := by
      rw [mul_pow, ← pow_mul, inv_pow]
    have e2 : (2 : ℝ) ^ ((a + 2 * b) * k) = 2 ^ (a * k) * (2 ^ (b * k) * 2 ^ (b * k)) := by
      rw [add_mul, pow_add, two_mul, add_mul, pow_add]
    have e3 : ((2 : ℝ) ^ k / w1) ^ a = 2 ^ (a * k) / w1 ^ a := by
      rw [div_pow, ← pow_mul, mul_comm k a]
    have e4 : ((2 : ℝ) ^ k / w2) ^ b = 2 ^ (b * k) / w2 ^ b := by
      rw [div_pow, ← pow_mul, mul_comm k b]
    have hne : ((2 : ℝ) ^ (b * k)) ≠ 0 := by positivity
    rw [e1, e2, e3, e4]
    field_simp
  refine le_of_mul_le_mul_right (hmink.trans (le_of_eq ?_)) hvolpos
  have hd : finrank ℚ K = nrRealPlaces K + 2 * nrComplexPlaces K :=
    (InfinitePlace.card_add_two_mul_card_eq_rank K).symm
  rw [hd]
  exact key _ _ _ _ _ _ _ (unitBallVolume_pos (finrank K V)).ne'
    (unitBallVolume_pos (2 * finrank K V)).ne'

omit [Fintype ι] [LinearOrder ι] in
open scoped Classical in
theorem mem_mixedLattice_iff {y : ↥V.mixedSpan} :
    y ∈ V.mixedLattice ↔ ∃ z ∈ V.integerPoints, mixedPiEmb K ι z = (y : mixedPi K ι) := by
  rw [Submodule.mixedLattice, Submodule.mem_comap, Submodule.mem_map]
  simp

end Span

end NumberField.mixedEmbedding

section Product

open scoped Classical in
private theorem prod_pow_le_prod_range {f : ℕ → ℝ} {N : ℕ} (hf0 : ∀ i, 0 ≤ f i)
    (hmono : ∀ i j, i ≤ j → j < N → f i ≤ f j) (d : ℕ) :
    ∀ k, d * k ≤ N → ∏ j ∈ Finset.range k, f (d * j) ^ d ≤ ∏ i ∈ Finset.range (d * k), f i := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hle
    have hk : d * k ≤ N := le_trans (Nat.mul_le_mul_left d (Nat.le_succ k)) hle
    have hsplit : d * (k + 1) = d * k + d := by ring
    rw [Finset.prod_range_succ, hsplit, Finset.prod_range_add]
    refine mul_le_mul (ih hk) ?_ (pow_nonneg (hf0 _) _)
      (Finset.prod_nonneg fun i _ ↦ hf0 i)
    calc f (d * k) ^ d = ∏ _i ∈ Finset.range d, f (d * k) := by
          rw [Finset.prod_const, Finset.card_range]
      _ ≤ ∏ i ∈ Finset.range d, f (d * k + i) := by
          refine Finset.prod_le_prod₀ (fun i _ ↦ hf0 _) fun i hi ↦ ?_
          rw [Finset.mem_range] at hi
          exact hmono _ _ (Nat.le_add_right _ _) (by omega)

end Product

namespace NumberField

open Module MeasureTheory NumberField NumberField.InfinitePlace Matrix
open NumberField.mixedEmbedding
open scoped Pointwise

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

section Main

variable [LinearOrder ι] (V : Submodule K (ι → K))

open scoped Classical in
/-- **Layer 5.3, the relative form.** -/
theorem exists_basis_prod_arakelovMulHeight_le :
    ∃ x : Fin (finrank K V) → (ι → K), LinearIndependent K x ∧
      (∀ l, x l ∈ V.integerPoints) ∧
      (∏ l, arakelovMulHeight (x l))
        ≤ ((2 : ℝ) ^ finrank K V / unitBallVolume (finrank K V)) ^ nrRealPlaces K
            * ((2 : ℝ) ^ finrank K V / unitBallVolume (2 * finrank K V)) ^ nrComplexPlaces K
            * (Real.sqrt |(NumberField.discr K : ℝ)| ^ finrank K V * V.arakelovMulHeight) := by
  set B : Set ↥V.mixedSpan := (Subtype.val : ↥V.mixedSpan → mixedPi K ι) ⁻¹' mixedBall K ι with hB
  have hconv := convex_preimage_mixedBall V
  have hsymm : ∀ z ∈ B, -z ∈ B := fun z hz ↦ neg_mem_preimage_mixedBall V hz
  have hintn := interior_preimage_mixedBall_nonempty V
  have hbdd := isBounded_preimage_mixedBall V
  have hcl := isClosed_preimage_mixedBall V
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
      (z : mixedPi K ι) ∈ r • mixedBall K ι := by
    rintro r z ⟨b, hb, rfl⟩
    exact ⟨(b : mixedPi K ι), hb, by simp⟩
  have hheight : ∀ l : Fin (finrank K V),
      arakelovMulHeight ((x ∘ s) l) ≤ lam (finrank ℚ K * l.val) ^ finrank ℚ K := by
    intro l
    have hsl : (s l).val < finrank ℚ K * finrank K V := (s l).isLt
    have hdl : finrank ℚ K * l.val < finrank ℚ K * finrank K V :=
      (Nat.mul_lt_mul_left hdpos).2 l.isLt
    have hmem : mixedPiEmb K ι (x (s l)) ∈ (lam (s l).val) • mixedBall K ι := by
      have h := hsmulcoe _ _ (hvmem (e (s l)))
      rwa [← hxemb (s l)] at h
    have hintg : ∀ j, ∃ z : 𝓞 K, (z : K) = (x (s l)) j :=
      (Submodule.mem_integerPoints.1 (hxmem (s l))).2
    have h1 : arakelovMulHeight (x (s l)) ≤ (lam (s l).val) ^ finrank ℚ K :=
      arakelovMulHeight_le_of_mem_smul_mixedBall (hlampos _ hsl) (hsind.ne_zero l) hintg hmem
    exact h1.trans (pow_le_pow_left₀ (hlampos _ hsl).le (hlammono _ _ (hsle l) hdl) _)
  calc (∏ l, arakelovMulHeight ((x ∘ s) l))
      ≤ ∏ l : Fin (finrank K V), lam (finrank ℚ K * l.val) ^ finrank ℚ K :=
        Finset.prod_le_prod₀ (fun l _ ↦ (arakelovMulHeight_pos _).le) fun l _ ↦ hheight l
    _ = ∏ j ∈ Finset.range (finrank K V), lam (finrank ℚ K * j) ^ finrank ℚ K :=
        Fin.prod_univ_eq_prod_range (fun i ↦ lam (finrank ℚ K * i) ^ finrank ℚ K) _
    _ ≤ ∏ i ∈ Finset.range (finrank ℚ K * finrank K V), lam i :=
        prod_pow_le_prod_range hlamnn hlammono _ _ le_rfl
    _ ≤ _ := prod_successiveMinimum_mixedBall_le V

open scoped Classical in
/-- **Layer 5.3, the absolute form.** -/
theorem exists_basis_prod_arakelovMulHeight_rpow_le :
    ∃ x : Fin (finrank K V) → (ι → K), LinearIndependent K x ∧
      (∀ l, x l ∈ V.integerPoints) ∧
      (∏ l, arakelovMulHeight (x l) ^ (finrank ℚ K : ℝ)⁻¹)
        ≤ (((2 : ℝ) ^ finrank K V / unitBallVolume (finrank K V)) ^ nrRealPlaces K
              * ((2 : ℝ) ^ finrank K V / unitBallVolume (2 * finrank K V)) ^ nrComplexPlaces K)
              ^ (finrank ℚ K : ℝ)⁻¹
          * |(NumberField.discr K : ℝ)| ^ ((finrank K V : ℝ) / (2 * finrank ℚ K))
          * V.arakelovMulHeight ^ (finrank ℚ K : ℝ)⁻¹ := by
  obtain ⟨x, hind, hmem, hle⟩ := exists_basis_prod_arakelovMulHeight_le V
  refine ⟨x, hind, hmem, ?_⟩
  have hdne : ((finrank ℚ K : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 (Module.finrank_pos).ne'
  have hw1 := unitBallVolume_pos (finrank K V)
  have hw2 := unitBallVolume_pos (2 * finrank K V)
  have hHpos := V.arakelovMulHeight_pos
  have hprod : (∏ l, arakelovMulHeight (x l) ^ (finrank ℚ K : ℝ)⁻¹)
      = (∏ l, arakelovMulHeight (x l)) ^ (finrank ℚ K : ℝ)⁻¹ :=
    Real.finsetProd_rpow _ _ (fun l _ ↦ (arakelovMulHeight_pos _).le) _
  rw [hprod]
  have hstep := Real.rpow_le_rpow (Finset.prod_nonneg fun l _ ↦ (arakelovMulHeight_pos _).le)
    hle (by positivity : (0 : ℝ) ≤ (finrank ℚ K : ℝ)⁻¹)
  refine hstep.trans (le_of_eq ?_)
  have hD : (Real.sqrt |(NumberField.discr K : ℝ)| ^ finrank K V) ^ ((finrank ℚ K : ℝ))⁻¹
      = |(NumberField.discr K : ℝ)| ^ ((finrank K V : ℝ) / (2 * finrank ℚ K)) := by
    rw [Real.sqrt_eq_rpow,
      ← Real.rpow_natCast (|(NumberField.discr K : ℝ)| ^ (1 / 2 : ℝ)) (finrank K V),
      ← Real.rpow_mul (abs_nonneg _), ← Real.rpow_mul (abs_nonneg _)]
    congr 1
    field_simp
  rw [Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity), hD]
  ring

end Main

section Kernel

variable [LinearOrder ι] {m : ℕ}

open scoped Classical in
/-- **Layer 5.3 — Bombieri–Vaaler over a number field, Hermitian form.** -/
theorem exists_basis_ker_prod_arakelovMulHeight_rpow_le (A : Matrix (Fin m) ι K) {k : ℕ}
    (hk : finrank K (LinearMap.ker A.mulVecLin) = k) :
    ∃ b : Basis (Fin k) K ↥(LinearMap.ker A.mulVecLin),
      (∀ l j, IsIntegral ℤ ((b l : ι → K) j)) ∧
      (∏ l, arakelovMulHeight (fun j ↦ (b l : ι → K) j) ^ (finrank ℚ K : ℝ)⁻¹) ≤
        (((2 : ℝ) ^ k / unitBallVolume k) ^ nrRealPlaces K
            * ((2 : ℝ) ^ k / unitBallVolume (2 * k)) ^ nrComplexPlaces K) ^ (finrank ℚ K : ℝ)⁻¹
          * |(NumberField.discr K : ℝ)| ^ ((k : ℝ) / (2 * finrank ℚ K))
          * (Submodule.span K (Set.range A.row)).arakelovMulHeight ^ (finrank ℚ K : ℝ)⁻¹ := by
  subst hk
  obtain ⟨x, hind, hmem, hle⟩ :=
    exists_basis_prod_arakelovMulHeight_rpow_le (LinearMap.ker A.mulVecLin)
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

end Kernel

end NumberField
