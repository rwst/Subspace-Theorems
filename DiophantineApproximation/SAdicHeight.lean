/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.SRegulator
public import DiophantineApproximation.SIntegerLocalization

-- Used only inside proofs.
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.RingTheory.Localization.Integer

/-!
# Where the height of an `S`-integral point lives, and primitive points

Let `K` be a number field and `S` a finite set of finite places, carried as a `Finset` of
height-one primes of `𝓞 K`. For a nonzero tuple `x : ι → K` whose coordinates are `S`-integers,
every local factor of the height away from `S` is at most `1`, so

```text
mulHeight x ≤ (∏_{v | ∞} (⨆ i, v (x i)) ^ mult v) * ∏_{v ∈ S} ⨆ i, |x i|_v,
```

and the two sides are equal exactly when no local factor is lost — which happens as soon as the
coordinates generate the unit ideal of the ring of `S`-integers. Such tuples are called
**`S`-primitive**, and `DiophantineApproximation/SIntegerLocalization.lean` makes them abundant:
once `S` has been enlarged so that `S.integer K` is a principal ideal domain, *every* nonzero
tuple has an `S`-primitive scalar multiple, and the height of an arbitrary point of `Kⁿ⁺¹` is
therefore computed by the places of that enlarged `S` alone.

This is the height bookkeeping Bombieri–Gubler's Theorem 7.2.6 — the affine Subspace Theorem for
`S`-integral points — runs on, and the file closes with the `S`-product formula in multiplicative
form.

## Main definitions

* `Set.IsPrimitive`: a tuple of `S`-integers whose coordinates generate the unit ideal of
  `S.integer K`, stated as `1 ∈ Submodule.span ↥(S.integer K) (Set.range x)`.

## Main results

* `NumberField.mulHeight_le_prod_of_forall_mem_integer`: the display above.
* `NumberField.mulHeight_eq_prod_of_isPrimitive`: it is an equality for an `S`-primitive tuple.
* `NumberField.exists_isPrimitive_mul`: over a principal `S.integer K` every nonzero tuple has an
  `S`-primitive scalar multiple.
* `NumberField.exists_finset_superset_forall_exists_mulHeight_eq`: the two combined — every finite
  `S` is contained in a finite `S'` such that the height of *every* nonzero tuple is, after one
  scaling, the product of the local sup norms over the infinite places and `S'`.
* `NumberField.prod_apply_eq_one_of_mem_unit`: the `S`-product formula for an `S`-unit, in
  multiplicative form.
* `NumberField.FinitePlace.hasFiniteMulSupport_iSup`: the local sup norms of a nonzero tuple are
  `1` at all but finitely many finite places. Mathlib proves this for `AdmissibleAbsValues` but
  keeps it `private`.

## Implementation notes

⚠ **The membership dictionary this layer is stated in is `ArithmeticHeights` 6.4 and is not
restated.** `Set.mem_integer_iff_finitePlace`, `Set.mem_unit_iff_finitePlace` and
`NumberField.FinitePlace.mk_apply_le_one_iff` already say `x ∈ S.integer K ↔ ∀ v ∉ S, |x|_v ≤ 1`
and its `S`-unit counterpart; this file consumes them.

⚠ **Only one direction of "primitive ⇔ full local factors" is proved, and it is the cheap one.**
That an `S`-primitive tuple has `⨆ i, |x i|_v = 1` at every `v ∉ S` is the ultrametric inequality
applied to `1 = ∑ c i x i`: the value of a nonarchimedean absolute value on a sum is at most the
largest value on a summand, and each `|c i|_v ≤ 1`. The converse — full local factors imply
primitivity — is a statement about the maximal ideals of `S.integer K` and needs the localization
of `DiophantineApproximation/SIntegerLocalization.lean` together with the order isomorphism on
primes; it has no consumer here and is not proved.

⚠ **The primitive multiple is produced over a principal `S.integer K` by a one-line module
argument, not by ideal factorization.** Clear denominators so that the coordinates lie in
`R = S.integer K`; the ideal they generate is `R ∙ g` for some `g ≠ 0`; then `g⁻¹ x` has
coordinates in `R` because each `x i` is a multiple of `g`, and its coordinates generate the unit
ideal because `g` is a combination of the `x i`. No finiteness of `S` is used.

⚠ **The finite mulSupport of `v ↦ ⨆ i, v (x i)` has to be reproved.** Mathlib's
`Height.hasFiniteMulSupport_iSup_nonarchAbsVal` is exactly this statement for a field with
`AdmissibleAbsValues`, but it is `private`, and `HasFiniteMulSupport.iSup` needs *every*
coordinate nonzero. The proof here bounds the support by the union over the nonzero coordinates:
if `|x i|_v = 1` for every nonzero coordinate then the supremum is `1`, the zero coordinates
contributing `0`.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
§1.5.10 and Theorem 7.2.6, where the height of an `S`-integral point is expressed through the
places of `S` and the point is normalised to be primitive.

This is Layer 0.3 of the `DiophantineApproximation` roadmap.
-/

public section

open Height IsDedekindDomain
open scoped nonZeroDivisors

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Finite ι]

/-!
### The local sup norms of a nonzero tuple
-/

/-- **The local sup norm of a nonzero tuple is `1` at all but finitely many finite places.**
Mathlib proves the same statement for a field with `AdmissibleAbsValues`, but keeps it `private`,
and its `HasFiniteMulSupport.iSup` asks for every coordinate to be nonzero. -/
theorem FinitePlace.hasFiniteMulSupport_iSup {x : ι → K} (hx : x ≠ 0) :
    Function.HasFiniteMulSupport fun v : FinitePlace K ↦ ⨆ i, v (x i) := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx
  have : Nonempty ι := ⟨i₀⟩
  refine Set.Finite.subset (Set.Finite.biUnion (s := {i | x i ≠ 0}) (Set.toFinite _)
    (fun i hi ↦ FinitePlace.hasFiniteMulSupport (K := K) hi)) ?_
  intro v hv
  by_contra hcon
  simp only [Set.mem_iUnion, Function.mem_mulSupport, not_exists, not_not] at hcon
  refine hv (le_antisymm (Real.iSup_le (fun i ↦ ?_) zero_le_one) ?_)
  · rcases eq_or_ne (x i) 0 with h | h
    · simp [h]
    · exact le_of_eq (hcon i h)
  · exact Finite.le_ciSup_of_le i₀ (le_of_eq (hcon i₀ hi₀).symm)

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

omit [Finite ι] in
/-- The finite part of the height, read on height-one primes rather than on finite places. -/
theorem finprod_iSup_eq {x : ι → K} :
    ∏ᶠ v : FinitePlace K, (⨆ i, v (x i))
      = ∏ᶠ v : HeightOneSpectrum (𝓞 K), ⨆ i, FinitePlace.mk v (x i) := by
  rw [← finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := K)).symm]
  simp only [FinitePlace.equivHeightOneSpectrum_symm_apply, ← FinitePlace.mk_apply]

/-- `NumberField.FinitePlace.hasFiniteMulSupport_iSup` read on height-one primes. -/
theorem hasFiniteMulSupport_iSup_mk {x : ι → K} (hx : x ≠ 0) :
    Function.HasFiniteMulSupport
      fun v : HeightOneSpectrum (𝓞 K) ↦ ⨆ i, FinitePlace.mk v (x i) := by
  have h := FinitePlace.hasFiniteMulSupport_iSup (K := K) hx
  refine Set.Finite.subset (h.preimage
    (FinitePlace.equivHeightOneSpectrum (K := K)).symm.injective.injOn) fun v hv ↦ ?_
  simp only [Set.mem_preimage, Function.mem_mulSupport] at hv ⊢
  simpa only [FinitePlace.equivHeightOneSpectrum_symm_apply, ← FinitePlace.mk_apply] using hv

omit [Finite ι] in
/-- The local sup norm of a tuple of `S`-integers is at most `1` away from `S`. -/
theorem iSup_mk_le_one {x : ι → K} (hxS : ∀ i, x i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) :
    (⨆ i, FinitePlace.mk v (x i)) ≤ 1 :=
  Real.iSup_le (fun i ↦ (FinitePlace.mk_apply_le_one_iff v (x i)).mpr (hxS i v (by simpa using hv)))
    zero_le_one

/-- The finite part of the height of an `S`-integral tuple is at most its part over `S`. -/
theorem finprod_iSup_le_prod {x : ι → K} (hx : x ≠ 0)
    (hxS : ∀ i, x i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) :
    ∏ᶠ v : FinitePlace K, (⨆ i, v (x i)) ≤ ∏ v ∈ S, ⨆ i, FinitePlace.mk v (x i) := by
  classical
  rw [finprod_iSup_eq]
  set F : HeightOneSpectrum (𝓞 K) → ℝ := fun v ↦ ⨆ i, FinitePlace.mk v (x i) with hF
  set G : HeightOneSpectrum (𝓞 K) → ℝ := fun v ↦ if v ∈ S then F v else 1 with hG
  have hF0 : ∀ v, 0 ≤ F v := fun v ↦ Real.iSup_nonneg fun i ↦ AbsoluteValue.nonneg _ _
  have hGv : ∀ v, G v = if v ∈ S then F v else 1 := fun _ ↦ rfl
  have hGsupp : Function.mulSupport G ⊆ (S : Set (HeightOneSpectrum (𝓞 K))) := by
    intro v hv
    by_contra hvS
    have hvS' : v ∉ S := by simpa using hvS
    exact hv (by rw [hGv]; simp [hvS'])
  have hGfin : Function.HasFiniteMulSupport G := (S.finite_toSet).subset hGsupp
  have hFG : F ≤ G := fun v ↦ by
    rw [hGv]
    split_ifs with hv
    · exact le_rfl
    · exact iSup_mk_le_one S hxS hv
  calc ∏ᶠ v, F v ≤ ∏ᶠ v, G v :=
        finprod_le_finprod₀ (hasFiniteMulSupport_iSup_mk hx) hF0 hGfin hFG
    _ = ∏ v ∈ S, G v := finprod_eq_finsetProd_of_mulSupport_subset G (by simpa using hGsupp)
    _ = ∏ v ∈ S, F v := Finset.prod_congr rfl fun v hv ↦ by rw [hGv]; simp [hv]

/-- **The height of an `S`-integral tuple is carried by the infinite places and `S`**, as an
inequality. Bombieri–Gubler, Theorem 7.2.6, first half. -/
theorem mulHeight_le_prod_of_forall_mem_integer {x : ι → K} (hx : x ≠ 0)
    (hxS : ∀ i, x i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) :
    mulHeight x ≤ (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult)
      * ∏ v ∈ S, ⨆ i, FinitePlace.mk v (x i) := by
  rw [NumberField.mulHeight_eq hx]
  refine mul_le_mul_of_nonneg_left (finprod_iSup_le_prod S hx hxS) ?_
  exact Finset.prod_nonneg fun v _ ↦ pow_nonneg (Real.iSup_nonneg fun i ↦ apply_nonneg _ _) _

/-!
### Primitive tuples
-/

omit [Finite ι] in
/-- **An `S`-primitive tuple**: a tuple of `S`-integers whose coordinates generate the unit ideal
of the ring of `S`-integers. Since the coordinates lie in `S.integer K`, the submodule they span
is contained in it, so the condition `1 ∈ span` says exactly that the span is all of
`S.integer K`. -/
def _root_.Set.IsPrimitive (S : Set (HeightOneSpectrum (𝓞 K))) (x : ι → K) : Prop :=
  (∀ i, x i ∈ S.integer K) ∧ (1 : K) ∈ Submodule.span ↥(S.integer K) (Set.range x)

omit [Finite ι] in
/-- `Set.IsPrimitive` written out as a linear combination, which is the form every proof uses. -/
theorem _root_.Set.isPrimitive_iff [Fintype ι] (S : Set (HeightOneSpectrum (𝓞 K))) (x : ι → K) :
    S.IsPrimitive x ↔ (∀ i, x i ∈ S.integer K) ∧
      ∃ c : ι → K, (∀ i, c i ∈ S.integer K) ∧ ∑ i, c i * x i = 1 := by
  refine and_congr_right fun _ ↦ ?_
  rw [Submodule.mem_span_range_iff_exists_fun ↥(S.integer K)]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨fun i ↦ (c i : K), fun i ↦ (c i).2, by simpa [Algebra.smul_def] using hc⟩
  · rintro ⟨c, hcmem, hc⟩
    exact ⟨fun i ↦ ⟨c i, hcmem i⟩, by simpa [Algebra.smul_def] using hc⟩

omit [Finite ι] in
theorem _root_.Set.IsPrimitive.ne_zero {S : Set (HeightOneSpectrum (𝓞 K))} {x : ι → K}
    (h : S.IsPrimitive x) : x ≠ 0 := by
  rintro rfl
  have hle : Submodule.span ↥(S.integer K) (Set.range (0 : ι → K)) ≤ ⊥ :=
    Submodule.span_le.mpr (by rintro y ⟨i, rfl⟩; simp)
  simpa using hle h.2

/-- **An `S`-primitive tuple loses no local factor away from `S`.** The ultrametric inequality
applied to `1 = ∑ c i x i`, the coefficients being `S`-integers. -/
theorem iSup_mk_eq_one_of_isPrimitive {x : ι → K}
    (hprim : (S : Set (HeightOneSpectrum (𝓞 K))).IsPrimitive x)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) :
    (⨆ i, FinitePlace.mk v (x i)) = 1 := by
  let _i : Fintype ι := Fintype.ofFinite ι
  obtain ⟨hxS, c, hcS, hc⟩ := (Set.isPrimitive_iff _ x).mp hprim
  have hι : Nonempty ι := by
    by_contra hι
    rw [not_nonempty_iff] at hι
    simp at hc
  have hne : (Finset.univ : Finset ι).Nonempty := Finset.univ_nonempty
  refine le_antisymm (iSup_mk_le_one S hxS hv) ?_
  have hna : IsNonarchimedean (FinitePlace.mk v : K → ℝ) := map_add_le_max _
  have h1 : (1 : ℝ) = FinitePlace.mk v (∑ i, c i * x i) := by rw [hc, map_one]
  obtain ⟨i, -, hi⟩ := hna.finset_image_add_of_nonempty (g := fun i ↦ c i * x i) hne
  rw [← h1] at hi
  refine hi.trans ?_
  rw [map_mul]
  refine le_trans (mul_le_of_le_one_left (apply_nonneg _ _)
    ((FinitePlace.mk_apply_le_one_iff v (c i)).mpr (hcS i v (by simpa using hv)))) ?_
  exact Finite.le_ciSup_of_le i le_rfl

/-- **The height of an `S`-primitive tuple is the product of the local sup norms over the infinite
places and `S`.** Bombieri–Gubler, Theorem 7.2.6, second half. -/
theorem mulHeight_eq_prod_of_isPrimitive {x : ι → K}
    (hprim : (S : Set (HeightOneSpectrum (𝓞 K))).IsPrimitive x) :
    mulHeight x = (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult)
      * ∏ v ∈ S, ⨆ i, FinitePlace.mk v (x i) := by
  classical
  rw [NumberField.mulHeight_eq hprim.ne_zero, finprod_iSup_eq]
  congr 1
  refine finprod_eq_finsetProd_of_mulSupport_subset _ fun v hv ↦ ?_
  by_contra hvS
  exact hv (iSup_mk_eq_one_of_isPrimitive S hprim (by simpa using hvS))

/-!
### Primitive multiples over a principal ring of `S`-integers
-/

/-- **Over a principal ring of `S`-integers every nonzero tuple has an `S`-primitive scalar
multiple.** Clear denominators, take a generator `g` of the ideal the coordinates generate, and
scale by `g⁻¹`. -/
theorem exists_isPrimitive_mul (S : Set (HeightOneSpectrum (𝓞 K)))
    [IsPrincipalIdealRing ↥(S.integer K)] {x : ι → K} (hx : x ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ S.IsPrimitive fun i ↦ c * x i := by
  classical
  let _i : Fintype ι := Fintype.ofFinite ι
  obtain ⟨i₀, hi₀⟩ : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (𝓞 K)⁰ (Finset.univ : Finset ι) x
  set d : K := algebraMap (𝓞 K) K (b : 𝓞 K) with hd
  have hd0 : d ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).mpr
      (nonZeroDivisors.ne_zero b.2)
  have hy : ∀ i, d * x i ∈ S.integer K := fun i ↦ by
    obtain ⟨a, ha⟩ := hb i (Finset.mem_univ i)
    have hdx : d * x i = algebraMap (𝓞 K) K a := by rw [ha, hd, Algebra.smul_def]
    rw [hdx]
    exact Subalgebra.algebraMap_mem _ a
  set Y : ι → ↥(S.integer K) := fun i ↦ ⟨d * x i, hy i⟩ with hY
  obtain ⟨g, hg⟩ := Submodule.IsPrincipal.principal (Ideal.span (Set.range Y))
  have hY0 : Y i₀ ≠ 0 := fun h ↦
    mul_ne_zero hd0 hi₀ (by simpa [hY] using congrArg (fun t : ↥(S.integer K) ↦ (t : K)) h)
  have hgmem : Y i₀ ∈ Ideal.span (Set.range Y) := Submodule.subset_span ⟨i₀, rfl⟩
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [hg, Submodule.span_singleton_eq_bot.mpr rfl] at hgmem
    exact hY0 hgmem
  have hgK : (g : K) ≠ 0 := fun h ↦ hg0 (Subtype.ext h)
  refine ⟨(g : K)⁻¹ * d, mul_ne_zero (inv_ne_zero hgK) hd0, (Set.isPrimitive_iff _ _).mpr ⟨?_, ?_⟩⟩
  · intro i
    have hmem : Y i ∈ (↥(S.integer K) ∙ g) := by
      rw [← hg]; exact Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    have haK : (g : K) * (a : K) = d * x i := by
      simpa [hY, Algebra.smul_def, mul_comm] using congrArg (fun t : ↥(S.integer K) ↦ (t : K)) ha
    have hval : (g : K)⁻¹ * d * x i = (a : K) := by
      have hassoc : (g : K)⁻¹ * d * x i = (g : K)⁻¹ * (d * x i) := by ring
      rw [hassoc, ← haK, ← mul_assoc, inv_mul_cancel₀ hgK, one_mul]
    rw [hval]
    exact a.2
  · have hgspan : g ∈ Ideal.span (Set.range Y) := by
      rw [hg]; exact Submodule.mem_span_singleton_self g
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ↥(S.integer K)).mp hgspan
    refine ⟨fun i ↦ (c i : K), fun i ↦ (c i).2, ?_⟩
    have hcK : ∑ i, (c i : K) * (d * x i) = (g : K) := by
      have := congrArg (fun t : ↥(S.integer K) ↦ (t : K)) hc
      simpa [hY, Algebra.smul_def] using this
    calc ∑ i, (c i : K) * ((g : K)⁻¹ * d * x i)
        = (g : K)⁻¹ * ∑ i, (c i : K) * (d * x i) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ by ring
      _ = 1 := by rw [hcK, inv_mul_cancel₀ hgK]

/-- **The height of an arbitrary point is computed by finitely many places.** Every finite set of
finite places is contained in a finite set `S'` such that every nonzero tuple has a scalar
multiple whose height is the product of the local sup norms over the infinite places and `S'`.
This is the normalisation Bombieri–Gubler's Theorem 7.2.6 begins with. -/
theorem exists_finset_superset_forall_exists_mulHeight_eq
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ S' : Finset (HeightOneSpectrum (𝓞 K)), S ⊆ S' ∧
      ∀ x : ι → K, x ≠ 0 → ∃ c : K, c ≠ 0 ∧
        mulHeight x = (∏ v : InfinitePlace K, (⨆ i, v (c * x i)) ^ v.mult)
          * ∏ v ∈ S', ⨆ i, FinitePlace.mk v (c * x i) := by
  classical
  obtain ⟨T, hST, hTfin, hTprin⟩ :=
    exists_finite_superset_isPrincipalIdealRing (S : Set (HeightOneSpectrum (𝓞 K)))
      S.finite_toSet
  have hcoe : (hTfin.toFinset : Set (HeightOneSpectrum (𝓞 K))) = T := hTfin.coe_toFinset
  refine ⟨hTfin.toFinset, fun v hv ↦ by simpa [hTfin.mem_toFinset] using hST hv, fun x hx ↦ ?_⟩
  have : IsPrincipalIdealRing ↥(T.integer K) := hTprin
  obtain ⟨c, hc0, hprim⟩ := exists_isPrimitive_mul T hx
  refine ⟨c, hc0, ?_⟩
  have hsmul : mulHeight (fun i ↦ c * x i) = mulHeight x := by
    have h := Height.mulHeight_smul_eq_mulHeight (K := K) x hc0
    have he : (c • x) = fun i ↦ c * x i := by funext i; simp
    rwa [he] at h
  rw [← hsmul]
  exact mulHeight_eq_prod_of_isPrimitive hTfin.toFinset (by rwa [hcoe])

/-!
### The `S`-product formula
-/

/-- **The `S`-product formula**, in multiplicative form: the local factors of an `S`-unit over the
infinite places and `S` have product `1`, every other place contributing `1`. The logarithmic form
is `ArithmeticHeights` 6.5. -/
theorem prod_apply_eq_one_of_mem_unit (S : Finset (HeightOneSpectrum (𝓞 K))) {u : Kˣ}
    (hu : u ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    ((∏ v : InfinitePlace K, v (u : K) ^ v.mult) * ∏ v ∈ S, FinitePlace.mk v (u : K)) = 1 := by
  have h := NumberField.prod_abs_eq_one (K := K) (x := (u : K)) (Units.ne_zero u)
  rwa [NumberField.SUnit.finprod_apply_eq_prod (S := S) ⟨u, hu⟩] at h

/-! ### Acceptance criteria -/

/-- **Conformance: a tuple of `S`-integers with a coordinate `1` is `S`-primitive.** So
`NumberField.mulHeight_eq_prod_of_isPrimitive` is not vacuous, and the affine points of
Bombieri–Gubler's Theorem 7.2.6 — those with a coordinate normalised to `1` — satisfy it. -/
example (S : Set (HeightOneSpectrum (𝓞 K))) {x : ι → K}
    (hx : ∀ i, x i ∈ S.integer K) {i₀ : ι} (h : x i₀ = 1) : S.IsPrimitive x :=
  ⟨hx, h ▸ Submodule.subset_span ⟨i₀, rfl⟩⟩

/-- **Conformance: an `S`-unit is an `S`-primitive `1`-tuple in the `2`-tuple `(1, u)`.** The
`S`-product formula and the height display are then the same statement read twice. -/
example (S : Set (HeightOneSpectrum (𝓞 K))) {u : Kˣ} (hu : u ∈ S.unit K) :
    S.IsPrimitive ![(1 : K), (u : K)] :=
  ⟨fun i ↦ by fin_cases i <;> simp [Set.mem_integer_of_mem_unit hu, one_mem],
    Submodule.subset_span ⟨0, rfl⟩⟩

/-- **Rejection test: `S`-integrality alone does not give the equality of
`NumberField.mulHeight_eq_prod_of_isPrimitive`; primitivity is needed.** The constant tuple
`(2, …, 2)` has algebraic-integer coordinates, so it is `∅`-integral, and its height is `1`
because the height of a tuple is invariant under scaling; but the right-hand side is
`2 ^ [K : ℚ] > 1`, every infinite place reading `2`. The lost factor sits at the finite places
above `2`, which is exactly the `S` this tuple would need. -/
example [Nonempty ι] :
    mulHeight (fun _ : ι ↦ ((2 : ℚ) : K))
      ≠ (∏ v : InfinitePlace K, (⨆ _ : ι, v ((2 : ℚ) : K)) ^ v.mult)
        * ∏ v ∈ (∅ : Finset (HeightOneSpectrum (𝓞 K))),
            ⨆ _ : ι, FinitePlace.mk v ((2 : ℚ) : K) := by
  have hd : 0 < Module.finrank ℚ K := Module.finrank_pos
  have h2 : ((2 : ℚ) : K) ≠ 0 := by simp
  have hlhs : mulHeight (fun _ : ι ↦ ((2 : ℚ) : K)) = 1 := by
    have he : (fun _ : ι ↦ ((2 : ℚ) : K)) = ((2 : ℚ) : K) • (1 : ι → K) := by funext i; simp
    rw [he, Height.mulHeight_smul_eq_mulHeight _ h2, Height.mulHeight_one]
  have htwo : ∀ w : InfinitePlace K, w (((2 : ℚ) : K)) = 2 := fun w ↦ by
    rw [InfinitePlace.map_ratCast, ← Rat.norm_cast_real]
    push_cast
    rw [Real.norm_eq_abs]
    norm_num
  have hrhs : ((∏ v : InfinitePlace K, (⨆ _ : ι, v ((2 : ℚ) : K)) ^ v.mult)
      * ∏ v ∈ (∅ : Finset (HeightOneSpectrum (𝓞 K))), ⨆ _ : ι, FinitePlace.mk v ((2 : ℚ) : K))
      = 2 ^ Module.finrank ℚ K := by
    rw [Finset.prod_empty, mul_one]
    calc (∏ v : InfinitePlace K, (⨆ _ : ι, v ((2 : ℚ) : K)) ^ v.mult)
        = ∏ v : InfinitePlace K, (2 : ℝ) ^ v.mult :=
          Finset.prod_congr rfl fun v _ ↦ by rw [ciSup_const, htwo v]
      _ = 2 ^ ∑ v : InfinitePlace K, v.mult := Finset.prod_pow_eq_pow_sum _ _ _
      _ = 2 ^ Module.finrank ℚ K := by rw [← totalWeight_eq_sum_mult, totalWeight_eq_finrank]
  rw [hlhs, hrhs]
  exact (one_lt_pow₀ (one_lt_two (α := ℝ)) hd.ne').ne

end NumberField
