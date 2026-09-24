/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.ApproxProd
public import DiophantineApproximation.SAdicHeight

/-!
# The affine form of the central quantity, and its dictionary with the projective one

**Layer 6.4, first half.** Bombieri–Gubler's Corollary 7.2.5 measures an `S`-integral point `x`
of `Kⁿ⁺¹` by the *undivided* product

```text
affineProd S w L x = (∏_{v | ∞} (∏ᵢ ‖L_{v,i} x‖_v) ^ mult v) * ∏_{v ∈ S} ∏ᵢ ‖L_{v,i} x‖_v,
```

with no denominator `‖x‖_v` — the normalisation that the projective quantity `approxProd` divides
by is carried instead by the hypothesis that the coordinates are `S`-integers, which is what makes
the affine statement the one every application quotes. This file is the dictionary between the
two quantities. Writing

```text
Hs x = (∏_{v | ∞} ‖x‖_v ^ mult v) * ∏_{v ∈ S} ‖x‖_v
```

for the part of the height carried by the infinite places and `S` — at least the height for an
`S`-integral point and exactly the height for an `S`-primitive one, which is Layer 0.3 — the two
quantities differ by that part alone:

```text
affineProd S w L x = approxProd (all v | ∞) S w L x * Hs x ^ (n + 1).
```

So the affine inequality `affineProd ≤ H(x) ^ (-ε)` implies the projective inequality
`approxProd ≤ H(x) ^ (-(n+1) - ε)` for an `S`-integral point, and the two are *equivalent* for an
`S`-primitive one. That is the whole difference between Corollary 7.2.5 and Theorem 7.2.2, and
the exponent `-(n+1) - ε` of the Subspace Theorem is `-ε` plus the `n + 1` copies of the height
that the `n + 1` local denominators contribute.

## Main definitions

* `NumberField.affineProd`: the affine quantity.

## Main results

* `NumberField.affineProd_eq_approxProd_mul`: the factorisation above.
* `NumberField.approxProd_le_of_affineProd_le`: the affine inequality implies the projective one,
  for an `S`-integral point.
* `NumberField.affineProd_le_iff_of_isPrimitive`: for an `S`-primitive point the two inequalities
  are the same statement.
* `NumberField.FinitePlace.mk_injective`: distinct primes give distinct finite places.

## Implementation notes

⚠ **The height enters to the power `#ι`, not `#ι - 1`.** Each local factor of `approxProd`
divides by `‖x‖_v` once for every form, and there are `#ι = n + 1` forms; the exponent of the
Subspace Theorem is therefore `-#ι - ε` against the affine `-ε`, and no dimension count is
involved.

⚠ **`S`-integrality is used only through an inequality.** `mulHeight_le_prod_of_forall_mem_integer`
is all the forward direction needs, and it is one-sided: a tuple of `S`-integers can lose height
at a place of `S` it does not fill. The converse needs `S`-primitivity, where Layer 0.3 turns that
inequality into an equality, and this is the only place where the difference matters.

⚠ **The sets of places are not the same object on the two sides.** The affine statement indexes
its finite places by height-one primes of `𝓞 K`, which is Mathlib's carrier for `S`-integers and
`S`-units; the projective one indexes them by `NumberField.FinitePlace`. The translation is
`FinitePlace.mk`, and it is injective — Mathlib has `FinitePlace.maximalIdeal_injective` for the
other direction of the same equivalence, but not this one.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Corollary 7.2.5 and Theorem 7.2.6.

This is Layer 6.4 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Height IsDedekindDomain Module

namespace NumberField

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
variable {ι : Type*} [Fintype ι]

/-- **The affine central quantity of the Subspace Theorem.** For a finite set `S` of finite
places of `K`, carried as height-one primes of `𝓞 K`, an absolute value `w v` of `F` over each
place of `K`, and linear forms `L v i` over `F`, this is `∏_{v ∈ S∞ ∪ S} ∏ᵢ ‖L_{v,i}(x)‖_v` in
Mathlib's normalisation, for a point `x` of `Kⁿ⁺¹`. Unlike `NumberField.approxProd` it has no
local denominators, so it is not invariant under scaling; the hypothesis that the coordinates are
`S`-integers takes their place. -/
noncomputable def affineProd (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F)) (x : ι → K) : ℝ :=
  (∏ v : InfinitePlace K, (∏ i, w v.1 (L v.1 i fun j ↦ algebraMap K F (x j))) ^ v.mult) *
    ∏ v ∈ S, ∏ i, w (FinitePlace.mk v).1
      (L (FinitePlace.mk v).1 i fun j ↦ algebraMap K F (x j))

omit [NumberField F] in
/-- The affine quantity is a product of nonnegative reals. -/
theorem affineProd_nonneg (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F)) (x : ι → K) :
    0 ≤ affineProd S w L x :=
  mul_nonneg
    (Finset.prod_nonneg fun _ _ ↦ pow_nonneg (Finset.prod_nonneg fun _ _ ↦ apply_nonneg _ _) _)
    (Finset.prod_nonneg fun _ _ ↦ Finset.prod_nonneg fun _ _ ↦ apply_nonneg _ _)

/-- **Distinct primes give distinct finite places.** Mathlib has the injectivity of
`NumberField.FinitePlace.maximalIdeal`, the other direction of the same equivalence. -/
theorem FinitePlace.mk_injective :
    Function.Injective (FinitePlace.mk : HeightOneSpectrum (𝓞 K) → FinitePlace K) :=
  Function.LeftInverse.injective FinitePlace.maximalIdeal_mk

omit [NumberField F] in
open scoped Classical in
/-- **The affine quantity is the projective one times the `S`-part of the height, `#ι` times
over.** The `#ι` local denominators of `approxProd` at a place are the same number `‖x‖_v`, and
their product over the infinite places and `S` is the `S`-part of the height. -/
theorem affineProd_eq_approxProd_mul (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F)) {x : ι → K} (hx : x ≠ 0) :
    affineProd S w L x = approxProd Finset.univ (S.image FinitePlace.mk) w L x *
      ((∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult) *
        ∏ v ∈ S, ⨆ i, FinitePlace.mk v (x i)) ^ Fintype.card ι := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx
  have hpos : ∀ v : AbsoluteValue K ℝ, 0 < ⨆ i, v (x i) := fun v ↦
    lt_of_lt_of_le (v.pos hi₀) (le_ciSup_of_le (Finite.bddAbove_range _) i₀ le_rfl)
  have hloc : ∀ (d : ℝ) (W : AbsoluteValue F ℝ) (M : ι → Dual F (ι → F)),
      (∏ i, W (M i fun j ↦ algebraMap K F (x j)) / d)
        = (∏ i, W (M i fun j ↦ algebraMap K F (x j))) / d ^ Fintype.card ι := fun d W M ↦ by
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
  have himg : ∀ f : FinitePlace K → ℝ,
      ∏ v ∈ S.image FinitePlace.mk, f v = ∏ v ∈ S, f (FinitePlace.mk v) :=
    fun f ↦ Finset.prod_image fun a _ b _ h ↦ FinitePlace.mk_injective h
  have hApos : (0 : ℝ) < ∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult :=
    Finset.prod_pos fun v _ ↦ pow_pos (hpos v.1) _
  have hBpos : (0 : ℝ) < ∏ v ∈ S, ⨆ i, FinitePlace.mk v (x i) :=
    Finset.prod_pos fun v _ ↦ hpos (FinitePlace.mk v).1
  have hinf : (∏ v : InfinitePlace K,
        (∏ i, w v.1 (L v.1 i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)) ^ v.mult)
      = (∏ v : InfinitePlace K, (∏ i, w v.1 (L v.1 i fun j ↦ algebraMap K F (x j))) ^ v.mult)
        / (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult) ^ Fintype.card ι := by
    simp only [hloc, div_pow]
    rw [Finset.prod_div_distrib, ← Finset.prod_pow]
    congr 1
    exact Finset.prod_congr rfl fun v _ ↦ by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have hfin : (∏ v ∈ S, ∏ i, w (FinitePlace.mk v).1
        (L (FinitePlace.mk v).1 i fun j ↦ algebraMap K F (x j)) / ⨆ j, FinitePlace.mk v (x j))
      = (∏ v ∈ S, ∏ i, w (FinitePlace.mk v).1
          (L (FinitePlace.mk v).1 i fun j ↦ algebraMap K F (x j)))
        / (∏ v ∈ S, ⨆ i, FinitePlace.mk v (x i)) ^ Fintype.card ι := by
    simp only [hloc]
    rw [Finset.prod_div_distrib, ← Finset.prod_pow]
  rw [approxProd, himg, hinf, hfin, affineProd, div_mul_div_comm, mul_pow, div_mul_cancel₀]
  exact (mul_pos (pow_pos hApos _) (pow_pos hBpos _)).ne'

omit [NumberField F] in
omit [NumberField F] in
open scoped Classical in
/-- **The affine inequality implies the projective one, at an `S`-integral point.** This is the
forward half of the equivalence between Bombieri–Gubler's Corollary 7.2.5 and their Theorem 7.2.2,
and it uses `S`-integrality only through the inequality `H(x) ≤ Hs x` of Layer 0.3. -/
theorem approxProd_le_of_affineProd_le (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F)) {x : ι → K} (hx : x ≠ 0)
    (hxS : ∀ i, x i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) {ε : ℝ}
    (h : affineProd S w L x ≤ mulHeight x ^ (-ε)) :
    approxProd Finset.univ (S.image FinitePlace.mk) w L x
      ≤ mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) := by
  have hH0 : (0 : ℝ) < mulHeight x := lt_of_lt_of_le zero_lt_one (Height.one_le_mulHeight x)
  have hnn : 0 ≤ approxProd Finset.univ (S.image FinitePlace.mk) w L x :=
    approxProd_nonneg _ _ _ _ _
  have hstep : approxProd Finset.univ (S.image FinitePlace.mk) w L x * mulHeight x ^ Fintype.card ι
      ≤ mulHeight x ^ (-ε) := by
    refine le_trans ?_ (le_trans (le_of_eq (affineProd_eq_approxProd_mul S w L hx).symm) h)
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hH0.le (mulHeight_le_prod_of_forall_mem_integer S hx hxS) _) hnn
  rwa [show -(Fintype.card ι : ℝ) - ε = -ε - (Fintype.card ι : ℝ) by ring, Real.rpow_sub hH0,
    Real.rpow_natCast, le_div_iff₀ (pow_pos hH0 _)]

omit [NumberField F] in
omit [NumberField F] in
open scoped Classical in
/-- **At an `S`-primitive point the affine and the projective inequality are the same statement.**
This is the converse half: Layer 0.3 makes the `S`-part of the height *equal* to the height there,
so nothing is lost in either direction, and Bombieri–Gubler's Corollary 7.2.5 is no weaker than
their Theorem 7.2.2. -/
theorem affineProd_le_iff_of_isPrimitive (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F)) {x : ι → K}
    (hprim : (S : Set (HeightOneSpectrum (𝓞 K))).IsPrimitive x) {ε : ℝ} :
    affineProd S w L x ≤ mulHeight x ^ (-ε) ↔
      approxProd Finset.univ (S.image FinitePlace.mk) w L x
        ≤ mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) := by
  have hH0 : (0 : ℝ) < mulHeight x := lt_of_lt_of_le zero_lt_one (Height.one_le_mulHeight x)
  have heq : affineProd S w L x
      = approxProd Finset.univ (S.image FinitePlace.mk) w L x * mulHeight x ^ Fintype.card ι := by
    rw [affineProd_eq_approxProd_mul S w L hprim.ne_zero,
      ← mulHeight_eq_prod_of_isPrimitive S hprim]
  rw [heq, show -(Fintype.card ι : ℝ) - ε = -ε - (Fintype.card ι : ℝ) by ring, Real.rpow_sub hH0,
    Real.rpow_natCast, le_div_iff₀ (pow_pos hH0 _)]

end NumberField
