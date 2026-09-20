/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.UnitHeight
public import Mathlib.RingTheory.DedekindDomain.SInteger

/-!
# `S`-integers, `S`-units, and where their height lives

Let `K` be a number field and `S` a set of finite places, carried as Mathlib carries it, as a set
of height-one primes of `𝓞 K`. Mathlib defines the `S`-integers `S.integer K` and the `S`-units
`S.unit K` by the adic valuations away from `S`, and this file adds nothing to those definitions:
it translates them into the language of `NumberField.FinitePlace` and then reads off where the
height of such an element lives. For `x` an `S`-integer,

```text
mulHeight₁ x = (∏_{w | ∞} max (w x) 1 ^ mult w) * ∏ᶠ v ∈ S, max (|x|_v) 1,
```

so that only the infinite places and the places of `S` contribute — and conversely, an element
whose height is carried by those places alone is an `S`-integer. An `S`-unit is an `S`-integer, so
the display holds for it too; `S = ∅` recovers the ring of integers, its units, and the height of
a unit as a product over the infinite places alone.

## Main results

* `NumberField.FinitePlace.mk_apply_le_one_iff` and
  `NumberField.FinitePlace.mk_apply_eq_one_iff`: the dictionary between the absolute value at a
  finite place and the adic valuation of the corresponding prime — `|x|_v ≤ 1` iff `v x ≤ 1`, and
  `|x|_v = 1` iff `v x = 1`. Everything else in the file is a consequence.
* `Set.mem_integer_iff_finitePlace` and `Set.mem_unit_iff_finitePlace`: membership of the
  `S`-integers and of the `S`-units read at the finite places. The second contains the converse
  the milestone asks for: an element of `Kˣ` whose absolute values at the finite places outside
  `S` are all `1` is an `S`-unit.
* `NumberField.mulHeight₁_eq_of_mem_integer` and `NumberField.logHeight₁_eq_of_mem_integer`: the
  display above and its logarithmic form, with `NumberField.mulHeight₁_eq_of_mem_unit` and
  `NumberField.logHeight₁_eq_of_mem_unit` for `S`-units and
  `NumberField.mulHeight₁_eq_prod_of_mem_integer` for `S` given as a `Finset`.
* `NumberField.mulHeight₁_eq_iff_mem_integer`: the converse, so that the display *characterizes*
  the `S`-integers among the nonzero elements of `K`.
* `Set.mem_integer_empty_iff` and `Set.mem_unit_empty_iff`: the `∅`-integers are the algebraic
  integers and the `∅`-units are the units of `𝓞 K`; with
  `NumberField.Units.valuation_eq_one`, a unit of `𝓞 K` is an `S`-unit for every `S`.
* `NumberField.FinitePlace.finprod_apply_ratCast`: the finite part of the height of a rational,
  `∏ᶠ w, w q = (|q| ^ [K : ℚ])⁻¹`, the acceptance test the roadmap names for this layer.

## Implementation notes

⚠ **The height identity needs only the `S`-integer hypothesis, not the `S`-unit one.** The
milestone states it for `x ∈ S.unit K`, and it is true there, but the proof uses only that the
local factor `max (|x|_v) 1` is trivial away from `S`, and that is `|x|_v ≤ 1`, the defining
condition of an `S`-integer. What the `S`-unit condition buys is that the same holds for `x⁻¹`,
which is what makes the collection a *group* and is what Layer 6.5 needs; it buys nothing here.
The `S`-unit forms are stated as corollaries so that the milestone's statement is present under a
name of its own.

⚠ **The converse holds in the stronger, height-theoretic form.** The milestone asks only for the
converse on membership — all finite absolute values outside `S` equal to `1` implies `S`-unit —
which is the backwards direction of `Set.mem_unit_iff_finitePlace` and costs nothing once the
dictionary is in place. `NumberField.mulHeight₁_eq_iff_mem_integer` says more: for `x ≠ 0` the
height identity *itself* forces `x` to be an `S`-integer, because every local factor is at least
`1`, so a single place outside `S` with `|x|_v > 1` makes the full finite product strictly larger
than the part over `S`. That is the sense in which `S` cannot be shrunk.

⚠ **The dictionary is a statement about `WithZeroMulInt.toNNReal`, and it is an equivalence only
because the norm of a prime exceeds `1`.** `NumberField.HeightOneSpectrum.adicAbv` is the
composite of the valuation with `WithZeroMulInt.toNNReal (absNorm v.asIdeal)`, which is strictly
monotone exactly when that base is `> 1`; Mathlib records the base's size as
`IsDedekindDomain.HeightOneSpectrum.one_lt_absNorm`, and without it the absolute value would
collapse and the dictionary would read only in one direction. Mathlib's own
`NumberField.FinitePlace.norm_eq_one_iff_notMem` is the same statement restricted to algebraic
integers, where the valuation condition becomes membership in the prime.

⚠ **`S = ∅` is a theorem here, not a definitional unfolding.** Mathlib's `integer_empty` says
`(∅ : Set _).integer K = ⊥` as subalgebras, and `Set.unitEquivUnitsInteger` identifies `S`-units
with the units of the `S`-integers, but composing them to reach `(𝓞 K)ˣ` goes through
`Algebra.botEquivOfInjective`. `Set.mem_unit_empty_iff` instead argues directly: `x` and `x⁻¹`
both have all valuations `≤ 1`, so both are algebraic integers by
`IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one`, and they are inverse to
each other there. With it, `NumberField.Units.mulHeight₁_eq_prod_infinitePlace` of Layer 6.1 is
the `S = ∅` case of this layer's display.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
§1.5.10, where the `S`-integers and `S`-units are introduced and the height of an `S`-unit is
described by the places of `S` together with the infinite ones.

The naming of the `S`-adic objects follows mathlib4#40791.

This is Layer 6.4 of the `ArithmeticHeights` roadmap.
-/

public section

open Function Height IsDedekindDomain Module Real

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-!
### The dictionary between finite places and adic valuations
-/

namespace FinitePlace

/-- **An element is `v`-integral iff its absolute value at the corresponding finite place is at
most `1`.** -/
theorem mk_apply_le_one_iff (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    mk v x ≤ 1 ↔ v.valuation K x ≤ 1 := by
  rw [mk_apply, norm_embedding, HeightOneSpectrum.adicAbv_def,
    show (1 : ℝ) = ((1 : NNReal) : ℝ) from rfl, NNReal.coe_le_coe]
  exact WithZeroMulInt.toNNReal_le_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal v)

/-- **An element is a `v`-unit iff its absolute value at the corresponding finite place is `1`.**
This is the dictionary the whole file runs on; Mathlib's
`NumberField.FinitePlace.norm_eq_one_iff_notMem` is its restriction to algebraic integers. -/
theorem mk_apply_eq_one_iff (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    mk v x = 1 ↔ v.valuation K x = 1 := by
  rw [mk_apply, norm_embedding, HeightOneSpectrum.adicAbv_def,
    show (1 : ℝ) = ((1 : NNReal) : ℝ) from rfl, NNReal.coe_inj]
  exact WithZeroMulInt.toNNReal_eq_one_iff _ (HeightOneSpectrum.absNorm_ne_zero v)
    (HeightOneSpectrum.one_lt_absNorm_nnreal v).ne'

/-- `mk_apply_le_one_iff` for a finite place presented as such. -/
theorem apply_le_one_iff (w : FinitePlace K) (x : K) :
    w x ≤ 1 ↔ w.maximalIdeal.valuation K x ≤ 1 := by
  rw [← mk_apply_le_one_iff w.maximalIdeal x, mk_maximalIdeal]

/-- `mk_apply_eq_one_iff` for a finite place presented as such. -/
theorem apply_eq_one_iff (w : FinitePlace K) (x : K) :
    w x = 1 ↔ w.maximalIdeal.valuation K x = 1 := by
  rw [← mk_apply_eq_one_iff w.maximalIdeal x, mk_maximalIdeal]

end FinitePlace

/-!
### Membership in the `S`-integers and the `S`-units
-/

/-- **An `S`-integer is an element whose absolute values at the finite places outside `S` are at
most `1`.** -/
theorem _root_.Set.mem_integer_iff_finitePlace (S : Set (HeightOneSpectrum (𝓞 K))) (x : K) :
    x ∈ S.integer K ↔ ∀ v ∉ S, FinitePlace.mk v x ≤ 1 :=
  forall₂_congr fun v _ ↦ (FinitePlace.mk_apply_le_one_iff v x).symm

/-- **An `S`-unit is an element of `Kˣ` whose absolute values at the finite places outside `S` are
all `1`.** The backwards direction is the converse the milestone asks for. -/
theorem _root_.Set.mem_unit_iff_finitePlace (S : Set (HeightOneSpectrum (𝓞 K))) (x : Kˣ) :
    x ∈ S.unit K ↔ ∀ v ∉ S, FinitePlace.mk v (x : K) = 1 :=
  forall₂_congr fun v _ ↦ (FinitePlace.mk_apply_eq_one_iff v (x : K)).symm

/-- `Set.mem_unit_iff_finitePlace` for a nonzero element of `K` rather than an element of `Kˣ`. -/
theorem _root_.Set.mk0_mem_unit_iff_finitePlace (S : Set (HeightOneSpectrum (𝓞 K))) {x : K}
    (hx : x ≠ 0) :
    Units.mk0 x hx ∈ S.unit K ↔ ∀ v ∉ S, FinitePlace.mk v x = 1 :=
  S.mem_unit_iff_finitePlace (Units.mk0 x hx)

/-- **An `S`-unit is an `S`-integer.** -/
theorem _root_.Set.mem_integer_of_mem_unit {S : Set (HeightOneSpectrum (𝓞 K))} {x : Kˣ}
    (hx : x ∈ S.unit K) : (x : K) ∈ S.integer K :=
  fun v hv ↦ (hx v hv).le

/-!
### The height of an `S`-integer
-/

section Height

variable (S : Set (HeightOneSpectrum (𝓞 K)))

/-- The local factor of an `S`-integer is trivial at every finite place outside `S`. -/
private theorem max_mk_apply_one_eq_one {x : K} (hx : x ∈ S.integer K)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) : max (FinitePlace.mk v x) 1 = 1 :=
  max_eq_right ((FinitePlace.mk_apply_le_one_iff v x).mpr (hx v hv))

/-- **The height of an `S`-integer is carried by the infinite places and the places of `S`.**
The `S`-unit case of this is Bombieri–Gubler 1.5.10; the hypothesis the proof uses is only that
`x` is an `S`-integer. -/
theorem mulHeight₁_eq_of_mem_integer {x : K} (hx : x ∈ S.integer K) :
    mulHeight₁ x
      = (∏ w : InfinitePlace K, max (w x) 1 ^ w.mult)
        * ∏ᶠ v ∈ S, max (FinitePlace.mk v x) 1 := by
  rw [NumberField.mulHeight₁_eq]
  congr 1
  rw [← finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := K)).symm]
  simp only [FinitePlace.equivHeightOneSpectrum_symm_apply, ← FinitePlace.mk_apply]
  rw [← finprod_mem_univ]
  refine finprod_mem_inter_mulSupport_eq' _ Set.univ S fun v hv ↦ ?_
  simp only [Set.mem_univ, true_iff]
  by_contra hvS
  exact hv (max_mk_apply_one_eq_one S hx hvS)

/-- The logarithmic form of `NumberField.mulHeight₁_eq_of_mem_integer`. -/
theorem logHeight₁_eq_of_mem_integer {x : K} (hx : x ∈ S.integer K) :
    logHeight₁ x
      = (∑ w : InfinitePlace K, w.mult * log⁺ (w x))
        + ∑ᶠ v ∈ S, log⁺ (FinitePlace.mk v x) := by
  rw [NumberField.logHeight₁_eq]
  congr 1
  rw [← finsum_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := K)).symm]
  simp only [FinitePlace.equivHeightOneSpectrum_symm_apply, ← FinitePlace.mk_apply]
  rw [← finsum_mem_univ]
  refine finsum_mem_inter_support_eq' _ Set.univ S fun v hv ↦ ?_
  simp only [Set.mem_univ, true_iff]
  by_contra hvS
  refine hv ?_
  change log⁺ (FinitePlace.mk v x) = 0
  rw [posLog_eq_log_max_one (apply_nonneg _ _), max_comm,
    max_mk_apply_one_eq_one S hx hvS, log_one]

/-- **The height of an `S`-unit**, the statement of Bombieri–Gubler 1.5.10. -/
theorem mulHeight₁_eq_of_mem_unit {x : Kˣ} (hx : x ∈ S.unit K) :
    mulHeight₁ (x : K)
      = (∏ w : InfinitePlace K, max (w (x : K)) 1 ^ w.mult)
        * ∏ᶠ v ∈ S, max (FinitePlace.mk v (x : K)) 1 :=
  mulHeight₁_eq_of_mem_integer S (Set.mem_integer_of_mem_unit hx)

/-- The logarithmic form of `NumberField.mulHeight₁_eq_of_mem_unit`. -/
theorem logHeight₁_eq_of_mem_unit {x : Kˣ} (hx : x ∈ S.unit K) :
    logHeight₁ (x : K)
      = (∑ w : InfinitePlace K, w.mult * log⁺ (w (x : K)))
        + ∑ᶠ v ∈ S, log⁺ (FinitePlace.mk v (x : K)) :=
  logHeight₁_eq_of_mem_integer S (Set.mem_integer_of_mem_unit hx)

end Height

/-- `NumberField.mulHeight₁_eq_of_mem_integer` with `S` a `Finset`, so that the finite part is an
ordinary product. This is the form Layer 6.5 consumes, `S` there being finite. -/
theorem mulHeight₁_eq_prod_of_mem_integer (S : Finset (HeightOneSpectrum (𝓞 K))) {x : K}
    (hx : x ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) :
    mulHeight₁ x
      = (∏ w : InfinitePlace K, max (w x) 1 ^ w.mult)
        * ∏ v ∈ S, max (FinitePlace.mk v x) 1 := by
  rw [mulHeight₁_eq_of_mem_integer _ hx, finprod_mem_coe_finset]

/-!
### The identity characterizes the `S`-integers
-/

/-- The finite local factors of a nonzero element have finite multiplicative support, read on
height-one primes rather than on finite places. -/
private theorem hasFiniteMulSupport_max_mk_apply_one {x : K} (hx : x ≠ 0) :
    HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 K) ↦ max (FinitePlace.mk v x) 1 := by
  have h := FinitePlace.hasFiniteMulSupport (K := K) hx
  refine Set.Finite.subset (h.preimage
    (FinitePlace.equivHeightOneSpectrum (K := K)).symm.injective.injOn) fun v hv ↦ ?_
  simp only [Set.mem_preimage, mem_mulSupport] at hv ⊢
  intro hone
  exact hv (by rw [show FinitePlace.mk v x = 1 from hone, max_self])

/-- **The display of `NumberField.mulHeight₁_eq_of_mem_integer` characterizes the `S`-integers.**
Every local factor is at least `1`, so a finite place outside `S` at which `x` has absolute value
greater than `1` makes the full finite product strictly larger than its part over `S`. -/
theorem mulHeight₁_eq_iff_mem_integer (S : Set (HeightOneSpectrum (𝓞 K))) {x : K} (hx : x ≠ 0) :
    mulHeight₁ x
        = (∏ w : InfinitePlace K, max (w x) 1 ^ w.mult)
          * ∏ᶠ v ∈ S, max (FinitePlace.mk v x) 1
      ↔ x ∈ S.integer K := by
  refine ⟨fun h v hv ↦ ?_, mulHeight₁_eq_of_mem_integer S⟩
  rw [← FinitePlace.mk_apply_le_one_iff]
  have hone : ∀ w : HeightOneSpectrum (𝓞 K), (1 : ℝ) ≤ max (FinitePlace.mk w x) 1 :=
    fun w ↦ le_max_right _ _
  have hfin := hasFiniteMulSupport_max_mk_apply_one (K := K) hx
  have harch : (∏ w : InfinitePlace K, max (w x) 1 ^ w.mult) ≠ 0 :=
    (Finset.prod_pos fun w _ ↦ pow_pos (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) _).ne'
  -- the full finite product coincides with its part over `S`
  have hall : ∏ᶠ w : HeightOneSpectrum (𝓞 K), max (FinitePlace.mk w x) 1
      = ∏ᶠ w ∈ S, max (FinitePlace.mk w x) 1 := by
    rw [NumberField.mulHeight₁_eq] at h
    replace h := mul_left_cancel₀ harch h
    rw [← finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := K)).symm] at h
    simpa only [FinitePlace.equivHeightOneSpectrum_symm_apply, ← FinitePlace.mk_apply] using h
  -- so the part outside `S` is trivial
  have hsplit := finprod_mem_inter_mul_sdiff'
    (f := fun w : HeightOneSpectrum (𝓞 K) ↦ max (FinitePlace.mk w x) 1) (s := Set.univ) S
    (by rw [Set.univ_inter]; exact hfin)
  rw [Set.univ_inter, ← Set.compl_eq_univ_sdiff, finprod_mem_univ, hall] at hsplit
  have hSpos : (0 : ℝ) < ∏ᶠ w ∈ S, max (FinitePlace.mk w x) 1 :=
    lt_of_lt_of_le zero_lt_one (one_le_finprod fun w ↦ one_le_finprod fun _ ↦ hone w)
  have hcompl : ∏ᶠ w ∈ Sᶜ, max (FinitePlace.mk w x) 1 = 1 :=
    mul_left_cancel₀ hSpos.ne' (by rw [mul_one]; exact hsplit)
  -- and then so is the single factor at `v`
  have hsing := finprod_mem_inter_mul_sdiff'
    (f := fun w : HeightOneSpectrum (𝓞 K) ↦ max (FinitePlace.mk w x) 1) (s := Sᶜ) {v}
    (hfin.subset Set.inter_subset_right)
  rw [Set.inter_eq_self_of_subset_right (Set.singleton_subset_iff.mpr hv), finprod_mem_singleton,
    hcompl] at hsing
  have hrest : (1 : ℝ) ≤ ∏ᶠ w ∈ (Sᶜ \ {v} : Set (HeightOneSpectrum (𝓞 K))),
      max (FinitePlace.mk w x) 1 :=
    one_le_finprod fun w ↦ one_le_finprod fun _ ↦ hone w
  have key := mul_le_mul_of_nonneg_left hrest (le_trans zero_le_one (hone v))
  rw [mul_one, hsing] at key
  exact le_of_max_le_left key

/-!
### `S = ∅`
-/

namespace Units

/-- **A unit of `𝓞 K` has adic valuation `1` at every prime**, hence is an `S`-unit for every `S`.
This is `NumberField.FinitePlace.apply_units_eq_one` of Layer 6.1 read through the dictionary. -/
theorem valuation_eq_one (v : HeightOneSpectrum (𝓞 K)) (u : (𝓞 K)ˣ) :
    v.valuation K ((u : 𝓞 K) : K) = 1 :=
  (FinitePlace.mk_apply_eq_one_iff v _).mp (FinitePlace.apply_units_eq_one (FinitePlace.mk v) u)

end Units

/-- **The `∅`-integers are the algebraic integers.** This is Mathlib's
`IsDedekindDomain.integer_empty` on elements. -/
theorem _root_.Set.mem_integer_empty_iff {x : K} :
    x ∈ (∅ : Set (HeightOneSpectrum (𝓞 K))).integer K ↔ ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = x :=
  ⟨fun hx ↦ HeightOneSpectrum.mem_integers_of_valuation_le_one K x
      fun v ↦ hx v (Set.notMem_empty v),
    fun ⟨a, ha⟩ v _ ↦ ha ▸ v.valuation_le_one a⟩

/-- **The `∅`-units are the units of `𝓞 K`.** Mathlib reaches this through `integer_empty` and
`Set.unitEquivUnitsInteger`; the argument here is direct, and is the statement rather than the
equivalence. -/
theorem _root_.Set.mem_unit_empty_iff {x : Kˣ} :
    x ∈ (∅ : Set (HeightOneSpectrum (𝓞 K))).unit K ↔ ∃ u : (𝓞 K)ˣ, ((u : 𝓞 K) : K) = (x : K) := by
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K (x : K)
      fun v ↦ (hx v (Set.notMem_empty v)).le
    obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K ((x⁻¹ : Kˣ) : K)
      fun v ↦ ((inv_mem hx) v (Set.notMem_empty v)).le
    have hab : a * b = 1 := by
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      rw [map_mul, ha, hb, map_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha⟩
  · rintro ⟨u, hu⟩ v -
    rw [← hu]
    exact Units.valuation_eq_one v u

/-!
### The finite part of the height of a rational
-/

namespace FinitePlace

/-- **The finite part of the height of a rational number**, `∏ᶠ w, w q = (|q| ^ [K : ℚ])⁻¹`: the
acceptance test the roadmap names for this layer. A rational is an `S`-unit exactly when `S`
contains every prime dividing its numerator or denominator, and then this product is the finite
factor of its height. -/
theorem finprod_apply_ratCast {q : ℚ} (hq : q ≠ 0) :
    ∏ᶠ w : FinitePlace K, w (q : K) = (|(q : ℝ)| ^ finrank ℚ K)⁻¹ := by
  have hK : ((q : ℚ) : K) ≠ 0 := by
    simpa using hq
  rw [prod_eq_inv_abs_norm hK, show ((q : ℚ) : K) = algebraMap ℚ K q from rfl,
    Algebra.norm_algebraMap]
  push_cast [abs_pow]
  ring

end FinitePlace

/-!
### Worked examples
-/

section Examples

variable {K : Type*} [Field K] [NumberField K]

/-- **Conformance with Layer 6.1.** The height of a unit of `𝓞 K` is a product over the infinite
places alone — `NumberField.Units.mulHeight₁_eq_prod_infinitePlace` — and that is the `S = ∅` case
of this layer's display, a unit of `𝓞 K` being an `∅`-integer. -/
example (u : (𝓞 K)ˣ) :
    mulHeight₁ ((u : 𝓞 K) : K)
      = ∏ w : InfinitePlace K, max (w ((u : 𝓞 K) : K)) 1 ^ w.mult := by
  rw [mulHeight₁_eq_of_mem_integer (∅ : Set (HeightOneSpectrum (𝓞 K)))
    fun v _ ↦ (Units.valuation_eq_one v u).le, finprod_mem_empty, mul_one]

/-- **Conformance with Mathlib.** A unit of `𝓞 K` is an `∅`-unit, so
`IsDedekindDomain.integer_empty` and `Set.unitEquivUnitsInteger` are matched by
`Set.mem_unit_empty_iff` on elements. -/
example (u : (𝓞 K)ˣ) (hu : ((u : 𝓞 K) : K) ≠ 0) :
    Units.mk0 _ hu ∈ (∅ : Set (HeightOneSpectrum (𝓞 K))).unit K :=
  Set.mem_unit_empty_iff.mpr ⟨u, rfl⟩

/-- **Acceptance test: the finite part of the height of a rational.** The roadmap names
`∏ᶠ w, w q = (|q| ^ [K : ℚ])⁻¹` as the check for this layer. At `q = 2` it says that the finite
places above `2` carry `2 ^ [K : ℚ]` between them — exactly the factor that
`NumberField.mulHeight₁_eq_of_mem_integer` moves inside `S` once `S` contains those places. -/
example : ∏ᶠ w : FinitePlace K, w ((2 : ℚ) : K) = ((2 : ℝ) ^ finrank ℚ K)⁻¹ := by
  rw [FinitePlace.finprod_apply_ratCast (K := K) (by norm_num : (2 : ℚ) ≠ 0)]
  norm_num

/-- **Rejection test: the `S`-integer hypothesis is load-bearing.** At `S = ∅` and `x = 1/2` the
infinite factor is `1`, every infinite place giving `1/2 < 1`, while the height is `2 ^ [K : ℚ]`;
the whole height of `1/2` sits at the finite places above `2`, which is the `S` this element
needs. By `NumberField.mulHeight₁_eq_iff_mem_integer` the failure is equivalent to `1/2` not
being an algebraic integer. -/
example : mulHeight₁ (((1 : ℚ) / 2 : ℚ) : K)
    ≠ ∏ w : InfinitePlace K, max (w (((1 : ℚ) / 2 : ℚ) : K)) 1 ^ w.mult := by
  have hd : 0 < finrank ℚ K := Module.finrank_pos
  have h2 : ((2 : ℚ) : K) ∈ (∅ : Set (HeightOneSpectrum (𝓞 K))).integer K := by
    have he : ((2 : ℚ) : K) = algebraMap (𝓞 K) K (2 : 𝓞 K) := by rw [map_ofNat]; push_cast; ring
    rw [he]
    exact Subalgebra.algebraMap_mem _ _
  have hhalf : ∀ w : InfinitePlace K, max (w (((1 : ℚ) / 2 : ℚ) : K)) 1 = 1 := fun w ↦ by
    rw [InfinitePlace.map_ratCast, ← Rat.norm_cast_real]
    push_cast
    rw [Real.norm_eq_abs]
    norm_num
  have htwo : ∀ w : InfinitePlace K, max (w (((2 : ℚ) : K))) 1 = 2 := fun w ↦ by
    rw [InfinitePlace.map_ratCast, ← Rat.norm_cast_real]
    push_cast
    rw [Real.norm_eq_abs]
    norm_num
  have hrhs : (∏ w : InfinitePlace K, max (w (((1 : ℚ) / 2 : ℚ) : K)) 1 ^ w.mult) = 1 :=
    Finset.prod_eq_one fun w _ ↦ by rw [hhalf w, one_pow]
  have hlhs : mulHeight₁ (((1 : ℚ) / 2 : ℚ) : K) = 2 ^ finrank ℚ K := by
    rw [show (((1 : ℚ) / 2 : ℚ) : K) = (((2 : ℚ) : K))⁻¹ by push_cast; ring, mulHeight₁_inv,
      mulHeight₁_eq_of_mem_integer _ h2, finprod_mem_empty, mul_one]
    calc (∏ w : InfinitePlace K, max (w (((2 : ℚ) : K))) 1 ^ w.mult)
        = ∏ w : InfinitePlace K, (2 : ℝ) ^ w.mult :=
          Finset.prod_congr rfl fun w _ ↦ by rw [htwo w]
      _ = 2 ^ ∑ w : InfinitePlace K, w.mult := Finset.prod_pow_eq_pow_sum _ _ _
      _ = 2 ^ finrank ℚ K := by rw [← totalWeight_eq_sum_mult, totalWeight_eq_finrank]
  rw [hlhs, hrhs]
  exact (one_lt_pow₀ (one_lt_two (α := ℝ)) hd.ne').ne'

end Examples

end NumberField
