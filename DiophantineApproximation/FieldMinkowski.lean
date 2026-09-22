/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.ApproximationVolume
public import DiophantineApproximation.FieldMinima

-- Used only inside proofs.
import ArithmeticHeights.MinkowskiSecond

/-!
# Minkowski's second theorem over a number field

For a number field `K` of degree `d`, an `𝓞 K`-submodule `Λ` of `Kⁱ` whose mixed embedding is a
lattice, and a symmetric convex body `B` in `(K ⊗ ℝ)ⁱ` balanced over every completion, the
successive minima `μ` over `K` of `FieldMinima.lean` satisfy

```text
2 ^ (d #ι) / (d #ι)! · covol Λ  ≤  c_K ^ (d #ι) · (μ 0 ⋯ μ (#ι - 1)) ^ d · vol B,
(μ 0 ⋯ μ (#ι - 1)) ^ d · vol B  ≤  2 ^ (d #ι) · covol Λ,
```

with `c_K` the largest house of a member of the integral basis. This is the content of the adelic
theorem of Bombieri–Vaaler and McFeat (Bombieri–Gubler, Theorem C.2.11) in the only generality the
Subspace Theorem uses, and it is proved from the real one, `ArithmeticHeights` 4.2, by the
comparisons of `FieldMinima.lean` and the monotonicity of the real minima. For an approximation
domain the ratio `vol B / covol Λ` is `Q` to the weight up to constants (Layer 4.1), and the
product of the minima is `Q` to minus the weight up to constants.

## Main results

* `NumberField.prod_successiveMinimum_pow_mul_measure_le`: the upper bound.
* `NumberField.covolume_le_prod_successiveMinimum_pow_mul_measure`: the lower bound.
* `NumberField.prod_successiveMinimum_approx_le` and `NumberField.le_prod_successiveMinimum_approx`:
  for an approximation domain, `(μ 0 ⋯ μ (#ι - 1)) ^ d` against `Q ^ (-weight)`, on both sides — the
  form Layer 4.3 consumes.

## Implementation notes

⚠ **The two bounds regroup the real minima in opposite directions.** The upper bound needs
`μ i ^ d ≤ λ (d i) ^ d ≤ λ (d i) ⋯ λ (d i + d - 1)`, the regrouping `Finset.prod_pow_le_prod_range`
of `ArithmeticHeights`; the lower bound needs `λ (d i + r) ≤ λ (d (i + 1) - 1) ≤ c_K μ i` for
`r < d`, which is the same regrouping the other way round, `prod_range_mul_le_prod_pow` below.
Both rest on the real minima being monotone below `d #ι`, and only the lower one on the body being
balanced over every completion.

⚠ **The bounds are stated multiplicatively**, as `ArithmeticHeights` states the real theorem, and
for any Haar measure; dividing by `vol B > 0` gives the roadmap's form. For an approximation domain
the measure is `volume`, and the lower bound on the product of the minima uses the comparison of
Layer 4.1 that carries no loss.

⚠ **Three acceptance tests.** Over `ℚ` the minima over the field are the real minima. In one
variable over `ℚ`, where `c_ℚ = 1` because the integral basis is `± 1`, both bounds are equalities,
`μ 0 · vol B = 2 · covol Λ`: the classical `|β| / a` for the interval `[-a, a]` and the lattice
`ℤ β`. And the minima vanish above `#ι`, so they are not monotone on all of `ℕ`, and every
statement is restricted to `i < #ι`.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Theorem C.2.11. J. W. S. Cassels, *An Introduction to the Geometry of Numbers*, Springer (1959),
Chapter VIII, Theorem V.

This is Layer 4.2 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Module NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]
  {B : Set (ι → mixedSpace K)}

section Minkowski

/-- Regrouping a product of `d k` terms into `k` blocks of `d`, each bounded by one term. -/
private theorem prod_range_mul_le_prod_pow {f g : ℕ → ℝ} (hf0 : ∀ i, 0 ≤ f i)
    (hg0 : ∀ j, 0 ≤ g j) (d : ℕ) :
    ∀ k, (∀ j r, j < k → r < d → f (d * j + r) ≤ g j) →
      ∏ i ∈ Finset.range (d * k), f i ≤ ∏ j ∈ Finset.range k, g j ^ d := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro h
    rw [Nat.mul_succ, Finset.prod_range_add, Finset.prod_range_succ]
    refine mul_le_mul (ih fun j r hj hr ↦ h j r (by omega) hr) ?_
      (Finset.prod_nonneg fun i _ ↦ hf0 _) (Finset.prod_nonneg fun j _ ↦ pow_nonneg (hg0 j) d)
    calc ∏ r ∈ Finset.range d, f (d * k + r) ≤ ∏ _r ∈ Finset.range d, g k :=
          Finset.prod_le_prod₀ (fun r _ ↦ hf0 _) fun r hr ↦
            h k r (by omega) (Finset.mem_range.1 hr)
      _ = g k ^ d := by rw [Finset.prod_const, Finset.card_range]

open scoped Classical in
/-- The real minima are nonnegative: positive below the dimension, zero above it. -/
private theorem zlattice_successiveMinimum_nonneg (Λ : Submodule (𝓞 K) (ι → K))
    [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage] (hB₀ : Convex ℝ B)
    (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : (interior B).Nonempty) (hB₃ : Bornology.IsBounded B)
    (i : ℕ) : 0 ≤ ZLattice.successiveMinimum Λ.mixedImage B i := by
  rcases lt_or_ge i (finrank ℝ (ι → mixedSpace K)) with h | h
  · exact (ZLattice.successiveMinimum_pos Λ.mixedImage hB₀ hB₁ hB₂ hB₃ h).le
  · exact (ZLattice.successiveMinimum_eq_zero_of_le Λ.mixedImage B h).ge

open scoped Classical in
/-- **Minkowski's second theorem over `K`, the upper bound**: `(μ 0 ⋯ μ (#ι - 1)) ^ d · vol B` is
at most `2 ^ (d #ι)` times the covolume. From `μ i ≤ λ (d i)`, the regrouping
`λ (d i) ^ d ≤ λ (d i) ⋯ λ (d i + d - 1)` and the real theorem. -/
theorem prod_successiveMinimum_pow_mul_measure_le (Λ : Submodule (𝓞 K) (ι → K))
    [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage]
    (μ : Measure (ι → mixedSpace K)) [μ.IsAddHaarMeasure] (hB₀ : Convex ℝ B)
    (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : (interior B).Nonempty) (hB₃ : Bornology.IsBounded B) :
    (∏ i ∈ Finset.range (Fintype.card ι), successiveMinimum Λ B i) ^ finrank ℚ K *
        (μ B).toReal ≤
      2 ^ (finrank ℚ K * Fintype.card ι) * ZLattice.covolume Λ.mixedImage μ := by
  have hdim : finrank ℝ (ι → mixedSpace K) = finrank ℚ K * Fintype.card ι :=
    mixedEmbedding.finrank_pi
  have hAH := ZLattice.prod_successiveMinimum_mul_measure_le Λ.mixedImage μ hB₀ hB₁ hB₂ hB₃
  rw [hdim] at hAH
  refine le_trans (mul_le_mul_of_nonneg_right ?_ ENNReal.toReal_nonneg) hAH
  rw [← Finset.prod_pow]
  refine le_trans ?_ (Finset.prod_pow_le_prod_range
    (f := ZLattice.successiveMinimum Λ.mixedImage B) (N := finrank ℚ K * Fintype.card ι)
    (zlattice_successiveMinimum_nonneg Λ hB₀ hB₁ hB₂ hB₃)
    (fun i j hij hj ↦ ZLattice.successiveMinimum_le_of_le hij (hdim ▸ hj) hB₀ hB₁ hB₂)
    (finrank ℚ K) (Fintype.card ι) le_rfl)
  exact Finset.prod_le_prod₀ (fun i _ ↦ pow_nonneg (successiveMinimum_nonneg _ _ _) _)
    fun i hi ↦ pow_le_pow_left₀ (successiveMinimum_nonneg _ _ _)
      (successiveMinimum_le_successiveMinimum_mixedImage Λ hB₀ hB₁ hB₂ hB₃
        (Finset.mem_range.1 hi)) _

open scoped Classical in
/-- **Minkowski's second theorem over `K`, the lower bound**: `2 ^ (d #ι) / (d #ι)!` times the
covolume is at most `c_K ^ (d #ι) (μ 0 ⋯ μ (#ι - 1)) ^ d · vol B`. From the real theorem and
`λ (d i + r) ≤ λ (d (i + 1) - 1) ≤ c_K μ i` for `r < d`, which is where the body is balanced over
every completion. -/
theorem covolume_le_prod_successiveMinimum_pow_mul_measure (Λ : Submodule (𝓞 K) (ι → K))
    [DiscreteTopology Λ.mixedImage] [IsZLattice ℝ Λ.mixedImage]
    (μ : Measure (ι → mixedSpace K)) [μ.IsAddHaarMeasure] (hB₀ : Convex ℝ B)
    (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : (interior B).Nonempty) (hB₃ : Bornology.IsBounded B)
    (hBbal : ∀ z ∈ B, ∀ a : mixedSpace K, (∀ w, normAtPlace w a ≤ 1) →
      (fun j ↦ a * z j) ∈ B) :
    2 ^ (finrank ℚ K * Fintype.card ι) / (finrank ℚ K * Fintype.card ι).factorial *
        ZLattice.covolume Λ.mixedImage μ ≤
      integralBasisHouse K ^ (finrank ℚ K * Fintype.card ι) *
        (∏ i ∈ Finset.range (Fintype.card ι), successiveMinimum Λ B i) ^ finrank ℚ K *
          (μ B).toReal := by
  have hdim : finrank ℝ (ι → mixedSpace K) = finrank ℚ K * Fintype.card ι :=
    mixedEmbedding.finrank_pi
  set c := integralBasisHouse K
  have hc0 : 0 ≤ c := zero_le_one.trans (one_le_integralBasisHouse K)
  have hAH := ZLattice.covolume_le_prod_successiveMinimum_mul_measure Λ.mixedImage μ hB₀ hB₁ hB₂
    hB₃
  rw [hdim] at hAH
  refine hAH.trans (mul_le_mul_of_nonneg_right ?_ ENNReal.toReal_nonneg)
  calc ∏ i ∈ Finset.range (finrank ℚ K * Fintype.card ι),
        ZLattice.successiveMinimum Λ.mixedImage B i
      ≤ ∏ j ∈ Finset.range (Fintype.card ι), (c * successiveMinimum Λ B j) ^ finrank ℚ K := by
        refine prod_range_mul_le_prod_pow (zlattice_successiveMinimum_nonneg Λ hB₀ hB₁ hB₂ hB₃)
          (fun j ↦ mul_nonneg hc0 (successiveMinimum_nonneg _ _ _)) _ _ fun j r hj hr ↦ ?_
        refine le_trans ?_ (successiveMinimum_mixedImage_le_mul Λ hB₀ hB₁ hB₂ hB₃ hBbal hj)
        refine ZLattice.successiveMinimum_le_of_le ?_ ?_ hB₀ hB₁ hB₂
        · rw [Nat.mul_succ]; omega
        · rw [hdim]
          exact lt_of_lt_of_le (Nat.sub_lt (Nat.mul_pos Module.finrank_pos j.succ_pos) one_pos)
            (Nat.mul_le_mul_left _ hj)
    _ = c ^ (finrank ℚ K * Fintype.card ι) *
          (∏ i ∈ Finset.range (Fintype.card ι), successiveMinimum Λ B i) ^ finrank ℚ K := by
        rw [Finset.prod_pow, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
          mul_pow, ← pow_mul, mul_comm (Fintype.card ι)]

end Minkowski

section Approximation

open scoped Classical in
/-- **The product of the minima of an approximation domain, upper bound**:
`(μ 0 ⋯ μ (#ι - 1)) ^ d` is at most a constant times `Q ^ (-weight)`, the constant depending on
`K`, `Sfin`, `#ι` and the determinants of the forms only. -/
theorem prod_successiveMinimum_approx_le {Sfin : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ}
    (hQ : 0 < Q) :
    (∏ i ∈ Finset.range (Fintype.card ι),
        successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) i) ^ finrank ℚ K ≤
      2 ^ (finrank ℚ K * Fintype.card ι) *
        (∏ v ∈ Sfin, (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) ^ Fintype.card ι) /
          approxConst Sfin L * Q ^ (-approxWeight Sfin c) := by
  have hD : DiscreteTopology (approxLattice Sfin L c Q) :=
    discreteTopology_approxLattice hLFin c hQ.ne'
  have : DiscreteTopology (approxModule Sfin L c Q).mixedImage := hD
  have hZ : IsZLattice ℝ (approxLattice Sfin L c Q) := isZLattice_approxLattice hLFin c hQ.ne'
  have : IsZLattice ℝ (approxModule Sfin L c Q).mixedImage := hZ
  have hup := prod_successiveMinimum_pow_mul_measure_le (approxModule Sfin L c Q) volume
    (convex_approxBody L c Q) (fun x hx ↦ neg_mem_approxBody hx)
    ⟨0, mem_interior_iff_mem_nhds.2 (approxBody_mem_nhds_zero L c hQ)⟩
    (isBounded_approxBody hLInf c Q)
  have hratio := le_volume_div_covolume hLInf hLFin c hQ
  set V := (volume (approxBody L c Q)).toReal
  set C := ZLattice.covolume (approxLattice Sfin L c Q)
  set P := ∏ v ∈ Sfin, (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) ^ Fintype.card ι
  have hC : 0 < C := ZLattice.covolume_pos _ _
  have hP : 0 < P := Finset.prod_pos fun v _ ↦ pow_pos (zero_lt_one.trans v.one_lt_absNorm) _
  have hA := approxConst_pos hLInf hLFin
  have hQw : 0 < Q ^ approxWeight Sfin c := Real.rpow_pos_of_pos hQ _
  have hV : 0 < V := by
    have : 0 < approxConst Sfin L * P⁻¹ * Q ^ approxWeight Sfin c := by positivity
    exact (div_pos_iff_of_pos_right hC).1 (this.trans_le hratio)
  rw [Real.rpow_neg hQ.le]
  have h1 : (∏ i ∈ Finset.range (Fintype.card ι),
      successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) i) ^ finrank ℚ K ≤
        2 ^ (finrank ℚ K * Fintype.card ι) * C / V := (le_div_iff₀ hV).2 hup
  refine h1.trans ?_
  have h2 : C / V ≤ (approxConst Sfin L * P⁻¹ * Q ^ approxWeight Sfin c)⁻¹ := by
    rw [← inv_div]
    exact inv_anti₀ (by positivity) hratio
  calc 2 ^ (finrank ℚ K * Fintype.card ι) * C / V
      = 2 ^ (finrank ℚ K * Fintype.card ι) * (C / V) := by ring
    _ ≤ 2 ^ (finrank ℚ K * Fintype.card ι) *
        (approxConst Sfin L * P⁻¹ * Q ^ approxWeight Sfin c)⁻¹ :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by field_simp

open scoped Classical in
/-- **The product of the minima of an approximation domain, lower bound**:
`(μ 0 ⋯ μ (#ι - 1)) ^ d` is at least a constant times `Q ^ (-weight)`. This is the form Layer 4.3
consumes: for weight negative it forces the last minimum up. It uses the upper comparison of
Layer 4.1, which carries no loss. -/
theorem le_prod_successiveMinimum_approx {Sfin : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ}
    (hQ : 0 < Q) :
    2 ^ (finrank ℚ K * Fintype.card ι) / ((finrank ℚ K * Fintype.card ι).factorial *
        integralBasisHouse K ^ (finrank ℚ K * Fintype.card ι) * approxConst Sfin L) *
        Q ^ (-approxWeight Sfin c) ≤
      (∏ i ∈ Finset.range (Fintype.card ι),
        successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) i) ^ finrank ℚ K := by
  have hD : DiscreteTopology (approxLattice Sfin L c Q) :=
    discreteTopology_approxLattice hLFin c hQ.ne'
  have : DiscreteTopology (approxModule Sfin L c Q).mixedImage := hD
  have hZ : IsZLattice ℝ (approxLattice Sfin L c Q) := isZLattice_approxLattice hLFin c hQ.ne'
  have : IsZLattice ℝ (approxModule Sfin L c Q).mixedImage := hZ
  have hlow := covolume_le_prod_successiveMinimum_pow_mul_measure (approxModule Sfin L c Q) volume
    (convex_approxBody L c Q) (fun x hx ↦ neg_mem_approxBody hx)
    ⟨0, mem_interior_iff_mem_nhds.2 (approxBody_mem_nhds_zero L c hQ)⟩
    (isBounded_approxBody hLInf c Q) fun z hz a ha ↦ mul_mem_approxBody hz ha
  have hratio := volume_div_covolume_le hLInf hLFin c hQ
  set V := (volume (approxBody L c Q)).toReal
  set C := ZLattice.covolume (approxLattice Sfin L c Q)
  set D := finrank ℚ K * Fintype.card ι
  set h := integralBasisHouse K
  set M := (∏ i ∈ Finset.range (Fintype.card ι),
    successiveMinimum (approxModule Sfin L c Q) (approxBody L c Q) i) ^ finrank ℚ K
  have hC : 0 < C := ZLattice.covolume_pos _ _
  have hA := approxConst_pos hLInf hLFin
  have hQw : 0 < Q ^ approxWeight Sfin c := Real.rpow_pos_of_pos hQ _
  have hh : 0 < h := zero_lt_one.trans_le (one_le_integralBasisHouse K)
  have hDf : (0 : ℝ) < D.factorial := by exact_mod_cast D.factorial_pos
  have hM : 0 ≤ M := pow_nonneg (Finset.prod_nonneg fun i _ ↦ successiveMinimum_nonneg _ _ _) _
  rw [Real.rpow_neg hQ.le]
  have hV' : V ≤ approxConst Sfin L * Q ^ approxWeight Sfin c * C := (div_le_iff₀ hC).1 hratio
  have key : 2 ^ D / D.factorial * C ≤
      h ^ D * M * (approxConst Sfin L * Q ^ approxWeight Sfin c * C) :=
    hlow.trans (mul_le_mul_of_nonneg_left hV' (by positivity))
  rw [div_mul_eq_mul_div, div_le_iff₀ hDf] at key
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have hkey : 2 ^ D * C ≤
      (h ^ D * M * (approxConst Sfin L * Q ^ approxWeight Sfin c) * D.factorial) * C := by
    nlinarith
  have hkey' := le_of_mul_le_mul_right hkey hC
  calc 2 ^ D * (Q ^ approxWeight Sfin c)⁻¹
      ≤ (h ^ D * M * (approxConst Sfin L * Q ^ approxWeight Sfin c) * D.factorial) *
          (Q ^ approxWeight Sfin c)⁻¹ :=
        mul_le_mul_of_nonneg_right hkey' (by positivity)
    _ = M * (D.factorial * h ^ D * approxConst Sfin L) := by field_simp

end Approximation

/-! ### Acceptance criteria -/

section Tests

/-- The integral basis of `ℚ` is `± 1`, so `c_ℚ = 1`. -/
private theorem integralBasisHouse_rat : integralBasisHouse ℚ = 1 := by
  have hcard : Fintype.card (Free.ChooseBasisIndex ℤ (𝓞 ℚ)) = 1 := by
    rw [← finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, Module.finrank_self]
  obtain ⟨r₀, hr₀⟩ := Fintype.card_eq_one_iff.1 hcard
  have key : ∀ r, house (integralBasis ℚ r) = 1 := by
    intro r
    have hsum := (RingOfIntegers.basis ℚ).sum_repr 1
    rw [Fintype.sum_eq_single r fun r' hr' ↦ absurd ((hr₀ r').trans (hr₀ r).symm) hr'] at hsum
    have hunit : IsUnit (Rat.ringOfIntegersEquiv (RingOfIntegers.basis ℚ r)) := by
      refine IsUnit.of_mul_eq_one ((RingOfIntegers.basis ℚ).repr 1 r) ?_
      have := congrArg Rat.ringOfIntegersEquiv hsum
      rwa [zsmul_eq_mul, map_mul, map_intCast, map_one Rat.ringOfIntegersEquiv, Int.cast_id,
        mul_comm] at this
    rw [integralBasis_apply, ← Rat.ringOfIntegersEquiv_apply_coe, house_intCast]
    rcases Int.isUnit_iff.1 hunit with h | h <;> rw [h] <;> simp
  simp only [integralBasisHouse, key, ciSup_const]

open scoped Classical in
/-- **Conformance: over `ℚ` the minima over the field are the real minima**, since `d = 1` makes
`λ i ≤ μ i ≤ λ (d i)` an equality. -/
example {ι : Type*} [Fintype ι] (Λ : Submodule (𝓞 ℚ) (ι → ℚ)) [DiscreteTopology Λ.mixedImage]
    [IsZLattice ℝ Λ.mixedImage] {B : Set (ι → mixedSpace ℚ)} (hB₀ : Convex ℝ B)
    (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : (interior B).Nonempty) (hB₃ : Bornology.IsBounded B) {i : ℕ}
    (hi : i < Fintype.card ι) :
    successiveMinimum Λ B i = ZLattice.successiveMinimum Λ.mixedImage B i := by
  refine le_antisymm ?_ (successiveMinimum_mixedImage_le Λ hB₀ hB₁ hB₂ hB₃ hi)
  simpa [Module.finrank_self] using
    successiveMinimum_le_successiveMinimum_mixedImage Λ hB₀ hB₁ hB₂ hB₃ hi

open scoped Classical in
/-- **Conformance: in one variable over `ℚ` both bounds are sharp**, `μ 0 · vol B = 2 · covol Λ`.
This pins the normalization `2 ^ (d #ι)` of the upper bound and the constant `c_ℚ = 1` of the
lower one. -/
example (Λ : Submodule (𝓞 ℚ) (Fin 1 → ℚ)) [DiscreteTopology Λ.mixedImage]
    [IsZLattice ℝ Λ.mixedImage] (μ : Measure (Fin 1 → mixedSpace ℚ)) [μ.IsAddHaarMeasure]
    {B : Set (Fin 1 → mixedSpace ℚ)} (hB₀ : Convex ℝ B) (hB₁ : ∀ x ∈ B, -x ∈ B)
    (hB₂ : (interior B).Nonempty) (hB₃ : Bornology.IsBounded B)
    (hBbal : ∀ z ∈ B, ∀ a : mixedSpace ℚ, (∀ w, normAtPlace w a ≤ 1) →
      (fun j ↦ a * z j) ∈ B) :
    successiveMinimum Λ B 0 * (μ B).toReal = 2 * ZLattice.covolume Λ.mixedImage μ := by
  have hup := prod_successiveMinimum_pow_mul_measure_le Λ μ hB₀ hB₁ hB₂ hB₃
  have hlow := covolume_le_prod_successiveMinimum_pow_mul_measure Λ μ hB₀ hB₁ hB₂ hB₃ hBbal
  simp only [Module.finrank_self, Fintype.card_fin, Finset.range_one, Finset.prod_singleton,
    pow_one, one_mul, integralBasisHouse_rat, Nat.factorial_one, Nat.cast_one, div_one] at hup hlow
  linarith

open scoped Classical in
/-- **Rejection: the minima are not monotone on all of `ℕ`.** They are positive below `#ι` and
vanish above it, so every statement about them carries `i < #ι`. -/
example [Nonempty ι] (Λ : Submodule (𝓞 K) (ι → K)) [DiscreteTopology Λ.mixedImage]
    [IsZLattice ℝ Λ.mixedImage] (hB₀ : Convex ℝ B) (hB₁ : ∀ x ∈ B, -x ∈ B)
    (hB₂ : (interior B).Nonempty) (hB₃ : Bornology.IsBounded B) :
    ¬ Monotone (successiveMinimum Λ B) := by
  intro hmono
  have h0 := successiveMinimum_pos Λ hB₀ hB₁ hB₂ hB₃ Fintype.card_pos
  have hn := successiveMinimum_eq_zero_of_le Λ B (le_refl (Fintype.card ι))
  have := hmono (Nat.zero_le (Fintype.card ι))
  linarith

end Tests

end NumberField
