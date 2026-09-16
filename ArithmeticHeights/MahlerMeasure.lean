/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.Absolute
public import Mathlib.NumberTheory.MahlerMeasure
public import Mathlib.RingTheory.Polynomial.GaussNorm

import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# The absolute height of an algebraic number and the Mahler measure

For an algebraic number `x` with **primitive integer minimal polynomial** `f` — the primitive
`f ∈ ℤ[X]` that is a nonzero rational multiple of `minpoly ℚ x`, determined up to sign by Gauss's
lemma — the absolute height and the Mahler measure agree after the degree-th power:

`absMulHeight₁ x ^ natDegree f = M(f)`.

This is the identity the rest of the layer runs on: Northcott's theorem with varying degree and
Kronecker's theorem both follow from it together with Mathlib's Northcott and Kronecker theorems
for the Mahler measure of integer polynomials.

## Main results

* `NumberField.absMulHeight₁_pow_natDegree`, the identity above, and
  `NumberField.natDegree_nsmul_absLogHeight₁`, its logarithmic form.
* `NumberField.prod_mulHeight₁_roots_eq_mahlerMeasure_pow`: the number-field statement behind it.
  If a primitive `f ∈ ℤ[X]` splits over a number field `L`, then the product of the *relative*
  heights of its roots in `L` is `M(f) ^ [L : ℚ]`.
* `Polynomial.gaussNorm_map_intCast_eq_one`: a primitive integer polynomial has Gauss norm `1` at
  every nonarchimedean absolute value. With `Polynomial.gaussNorm_mul` — Mathlib's multiplicativity
  of the Gauss norm, which is Gauss's lemma — this is the whole arithmetic input.
* `Polynomial.exists_isPrimitive_map_eq_C_mul` and
  `NumberField.exists_isPrimitive_absMulHeight₁_pow_natDegree`: the existence form. An algebraic
  number *has* a primitive integer minimal polynomial, of degree `[ℚ(x) : ℚ]`; this is what makes
  the identity above usable when no polynomial is given in advance, as in Northcott's theorem.

## Implementation notes

The proof reads the identity **one place at a time**, over a number field `L` in which `f` splits
as `C a * ∏ (X - αᵢ)`. At every place `v` of `L` the local factor of `∏ᵢ mulHeight₁ αᵢ` is a local
Mahler measure of `f`, by the same argument in two guises:

* at a nonarchimedean `v`, `v a * ∏ᵢ max (v αᵢ) 1` is the Gauss norm of `f`, which is `1` because
  `f` is primitive — this is `Polynomial.gaussNorm_mul` and
  `Polynomial.gaussNorm_map_intCast_eq_one`;
* at an archimedean `v`, `v a * ∏ᵢ max (v αᵢ) 1` is `M(f)` itself, by multiplicativity of the
  Mahler measure over the same factorization.

Multiplying over all places and cancelling `a` by the product formula leaves `M(f) ^ [L : ℚ]`.
The roadmap's route through Jensen's formula is therefore not taken: what the archimedean places
need is `Polynomial.mahlerMeasure_mul` and `Polynomial.mahlerMeasure_X_sub_C`, the two facts
Mathlib proves Jensen's formula *from*, and using them directly is what makes the two halves of
the argument the same computation.

Passing to the splitting field is what removes the Galois theory: the roots are not required to be
distinct, no Galois group acts, and the only fact used about them is that each is a root of
`minpoly ℚ x`, hence has the same absolute height as `x` by `NumberField.absMulHeight₁_comp`.

Two deviations from the roadmap's pinned statement, both widenings:

* `x` ranges over an arbitrary field of characteristic zero, not just `ℂ`. Nothing in the proof
  sees the ambient field — the splitting field is built over `ℚ` — and the Mahler measure is over
  `ℂ` on either reading.
* `f ≠ 0` is not a hypothesis: `Polynomial.IsPrimitive.ne_zero` supplies it, which is also why
  the hypotheses force `x` to be algebraic. The scalar `c` is likewise forced, being
  `f.leadingCoeff`.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Proposition 1.6.6, `log M(f) = deg(α) · h(α)`. Their display (1.10) is the nonarchimedean half
above, stated over a Galois closure for a list of conjugates; over a splitting field it is the
Gauss norm of `f`, which is what is used here. Lemma 1.6.7, the comparison with the `ℓ¹` norm of
the coefficient vector, is Mathlib's `Polynomial.mahlerMeasure_le_sum_norm_coeff` and
`Polynomial.norm_coeff_le_choose_mul_mahlerMeasure`.

This is Layer 1.2 of the `ArithmeticHeights` roadmap.
-/

public section

open Function IntermediateField Module Polynomial

/-!
### Two facts about multisets of finitely supported products

Both are the statement that a `Multiset.prod` of functions commutes with a product over the index,
proved by induction; Mathlib has the `Finset` half as `Multiset.prod_map_prod`.
-/

section Support

variable {ι γ M : Type*} [CommMonoid M]

private lemma hasFiniteMulSupport_multiset_prod (m : Multiset ι) {h : ι → γ → M}
    (hfin : ∀ i, HasFiniteMulSupport (h i)) :
    HasFiniteMulSupport fun c ↦ (m.map fun i ↦ h i c).prod := by
  induction m using Multiset.induction with
  | empty => simpa using hasFiniteMulSupport_one
  | cons i m ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (hfin i).mul ih

private lemma multiset_prod_map_finprod (m : Multiset ι) {h : ι → γ → M}
    (hfin : ∀ i, HasFiniteMulSupport (h i)) :
    (m.map fun i ↦ ∏ᶠ c, h i c).prod = ∏ᶠ c, (m.map fun i ↦ h i c).prod := by
  induction m using Multiset.induction with
  | empty => simp
  | cons i m ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, ih]
    exact (finprod_mul_distrib (hfin i) (hasFiniteMulSupport_multiset_prod m hfin)).symm

end Support

namespace Polynomial

/-!
### The Gauss norm of a primitive integer polynomial

Mathlib defines `Polynomial.gaussNorm v c` and proves it multiplicative for a nonarchimedean
absolute value (`Polynomial.gaussNorm_mul`), which is Gauss's lemma. What is missing, and supplied
here, are the two values that lemma is applied to: the Gauss norm of a linear factor and of a
primitive integer polynomial. All of this belongs in
`Mathlib/RingTheory/Polynomial/GaussNorm.lean`.
-/

/-- A bound on every coefficient bounds the Gauss norm. -/
lemma gaussNorm_le {R F : Type*} [Semiring R] [FunLike F R ℝ]
    (v : F) {c B : ℝ} {p : R[X]} (hB : 0 ≤ B) (h : ∀ i, v (p.coeff i) * c ^ i ≤ B) :
    p.gaussNorm v c ≤ B := by
  rw [gaussNorm]
  split
  · exact Finset.sup'_le _ _ fun i _ ↦ h i
  · exact hB

variable {R : Type*} [CommRing R] [IsDomain R] {v : AbsoluteValue R ℝ}

/-- The Gauss norm of a monic linear factor is `max (v α) 1`, the local factor of the height
of `α`. -/
lemma gaussNorm_X_sub_C (hna : IsNonarchimedean v) (α : R) :
    (X - C α).gaussNorm v 1 = max (v α) 1 := by
  refine le_antisymm ?_ (max_le ?_ ?_)
  · rw [sub_eq_add_neg, ← C_neg]
    refine (isNonarchimedean_gaussNorm v hna zero_le_one X (C (-α))).trans (le_of_eq ?_)
    rw [gaussNorm_C, AbsoluteValue.map_neg, ← monomial_one_one_eq_X, gaussNorm_monomial,
      AbsoluteValue.map_one, one_pow, mul_one, max_comm]
  · have h := le_gaussNorm v (X - C α) zero_le_one 0
    rwa [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, AbsoluteValue.map_neg, pow_zero,
      mul_one] at h
  · have h := le_gaussNorm v (X - C α) zero_le_one 1
    rwa [coeff_sub, coeff_X_one, coeff_C_succ, sub_zero, AbsoluteValue.map_one, pow_one,
      mul_one] at h

/-- `Polynomial.gaussNorm_mul` over a multiset of factors. -/
lemma gaussNorm_multiset_prod (hna : IsNonarchimedean v) (m : Multiset R[X]) :
    m.prod.gaussNorm v 1 = (m.map fun p ↦ p.gaussNorm v 1).prod := by
  induction m using Multiset.induction with
  | empty =>
    rw [Multiset.prod_zero, Multiset.map_zero, Multiset.prod_zero, ← C_1, gaussNorm_C,
      AbsoluteValue.map_one]
  | cons p m ih =>
    rw [Multiset.prod_cons, gaussNorm_mul hna one_pos, ih, Multiset.map_cons, Multiset.prod_cons]

/-- **A primitive integer polynomial has Gauss norm one at every nonarchimedean absolute value.**
The bound `≤ 1` is that integers are nonarchimedean integers; the bound `≥ 1` is Bézout applied to
the coefficients, whose gcd is a unit. -/
lemma gaussNorm_map_intCast_eq_one (hna : IsNonarchimedean v) {f : ℤ[X]} (hf : f.IsPrimitive) :
    (f.map (Int.castRingHom R)).gaussNorm v 1 = 1 := by
  have hint : ∀ n : ℤ, v (n : R) ≤ 1 := fun _ ↦
    hna.apply_intCast_le_one (map_zero_le v 1) (map_one v) (map_neg_eq_map v)
  have hcoeff : ∀ i, (f.map (Int.castRingHom R)).coeff i = ((f.coeff i : ℤ) : R) := by
    simp [coeff_map]
  refine le_antisymm (gaussNorm_le v zero_le_one fun i ↦ ?_) ?_
  · rw [hcoeff, one_pow, mul_one]
    exact hint _
  · obtain ⟨g, hg⟩ := Finset.gcd_eq_sum_mul f.support f.coeff
    have h1 : ((1 : R)) = ∑ i ∈ f.support, ((f.coeff i : ℤ) : R) * ((g i : ℤ) : R) := by
      have hc := hf.content_eq_one
      rw [content, hg] at hc
      exact_mod_cast congrArg (Int.cast : ℤ → R) hc.symm
    obtain ⟨b, _, hble⟩ := hna.finset_image_add_of_nonempty (g := fun i ↦
      ((f.coeff i : ℤ) : R) * ((g i : ℤ) : R)) (support_nonempty.mpr hf.ne_zero)
    rw [← h1, AbsoluteValue.map_one, map_mul] at hble
    calc (1 : ℝ) ≤ v ((f.coeff b : ℤ) : R) :=
          hble.trans (mul_le_of_le_one_right (v.nonneg _) (hint _))
      _ = v ((f.map (Int.castRingHom R)).coeff b) * 1 ^ b := by rw [hcoeff, one_pow, mul_one]
      _ ≤ _ := le_gaussNorm v _ zero_le_one b

/-!
### The primitive integer multiple of a rational polynomial

The identity of this layer quantifies over a primitive `f : ℤ[X]` that is a rational multiple of
`minpoly ℚ x`. Nothing upstream says such an `f` exists, and every consumer of the identity needs
it to: `IsLocalization.integerNormalization` clears the denominators and
`Polynomial.primPart` removes the content that clearing them introduced.
-/

/-- **Every nonzero rational polynomial is a rational multiple of a primitive integer
polynomial** — its integer normalization divided by the content. The multiplier `c` is nonzero, so
`f` and `g` have the same degree and the same roots; by Gauss's lemma `f` is determined up to
sign. -/
theorem exists_isPrimitive_map_eq_C_mul {g : ℚ[X]} (hg : g ≠ 0) :
    ∃ (f : ℤ[X]) (c : ℚ), f.IsPrimitive ∧ c ≠ 0 ∧ f.map (Int.castRingHom ℚ) = C c * g := by
  obtain ⟨b, hb, hbq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) g
  set q := IsLocalization.integerNormalization (nonZeroDivisors ℤ) g with hqdef
  have hq0 : q ≠ 0 := fun h ↦ hg (IsFractionRing.integerNormalization_eq_zero_iff.mp h)
  have hb0 : ((b : ℤ) : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hb
  have hc0 : ((q.content : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast Polynomial.content_eq_zero_iff.not.mpr hq0
  have hbq' : q.map (Int.castRingHom ℚ) = C ((b : ℤ) : ℚ) * g := by
    rw [← algebraMap_int_eq, hbq, zsmul_eq_mul]
    norm_cast
  have h1 : C ((q.content : ℤ) : ℚ) * (q.primPart.map (Int.castRingHom ℚ))
      = C ((b : ℤ) : ℚ) * g := by
    rw [← hbq']
    conv_rhs => rw [q.eq_C_content_mul_primPart]
    rw [Polynomial.map_mul, Polynomial.map_C, eq_intCast]
  refine ⟨q.primPart, ((b : ℤ) : ℚ) / ((q.content : ℤ) : ℚ), q.isPrimitive_primPart,
    div_ne_zero hb0 hc0, mul_left_cancel₀ (C_ne_zero.mpr hc0) ?_⟩
  rw [h1, ← mul_assoc, ← C_mul]
  congr 2
  field_simp

end Polynomial

namespace NumberField

/-!
### The identity, one place at a time

`f` is primitive in `ℤ[X]` and splits over `L` as `C a * ∏ (X - α)`. The two lemmas below evaluate
`v a * ∏ max (v α) 1` at a nonarchimedean and at an archimedean absolute value; they are the same
computation performed with `Polynomial.gaussNorm_mul` and with `Polynomial.mahlerMeasure_mul`.
-/

section Local

variable {L : Type*} [Field L]

private lemma gauss_local {v : AbsoluteValue L ℝ} (hna : IsNonarchimedean v) {f : ℤ[X]}
    (hf : f.IsPrimitive) {a : L} {s : Multiset L}
    (hsplit : f.map (Int.castRingHom L) = C a * (s.map fun α ↦ X - C α).prod) :
    v a * (s.map fun α ↦ max (v α) 1).prod = 1 := by
  have hmap : ((s.map fun α ↦ X - C α).map fun p ↦ p.gaussNorm v 1)
      = s.map fun α ↦ max (v α) 1 := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun α _ ↦ gaussNorm_X_sub_C hna α
  have h := gaussNorm_map_intCast_eq_one (R := L) hna hf
  rwa [hsplit, gaussNorm_mul hna one_pos, gaussNorm_C, gaussNorm_multiset_prod hna, hmap] at h

private lemma mahler_local (φ : L →+* ℂ) {f : ℤ[X]} {a : L} {s : Multiset L}
    (hsplit : f.map (Int.castRingHom L) = C a * (s.map fun α ↦ X - C α).prod) :
    ‖φ a‖ * (s.map fun α ↦ max ‖φ α‖ 1).prod = (f.map (Int.castRingHom ℂ)).mahlerMeasure := by
  have hmap : f.map (Int.castRingHom ℂ) = (f.map (Int.castRingHom L)).map φ := by
    rw [Polynomial.map_map]
    congr 1
    exact Subsingleton.elim _ _
  have hmap2 : (((s.map fun α ↦ X - C α).map (Polynomial.mapRingHom φ)).map
      fun p ↦ p.mahlerMeasure) = s.map fun α ↦ max ‖φ α‖ 1 := by
    rw [Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun α _ ↦ ?_
    simp [max_comm]
  rw [hmap, hsplit, Polynomial.map_mul, map_C, mahlerMeasure_mul, mahlerMeasure_const,
    ← Polynomial.coe_mapRingHom, map_multiset_prod, prod_mahlerMeasure_eq_mahlerMeasure_prod,
    hmap2]

end Local

/-!
### The identity over a splitting field
-/

section Core

variable {L : Type*} [Field L] [NumberField L]

private lemma hasFiniteMulSupport_max_one (α : L) :
    HasFiniteMulSupport fun w : FinitePlace L ↦ max (w α) 1 := by
  rcases eq_or_ne α 0 with rfl | h
  · simpa using hasFiniteMulSupport_one
  · exact (FinitePlace.hasFiniteMulSupport h).max hasFiniteMulSupport_one

private lemma prod_mulHeight₁_of_split {f : ℤ[X]} (hf : f.IsPrimitive) {a : L} {s : Multiset L}
    (hsplit : f.map (Int.castRingHom L) = C a * (s.map fun α ↦ X - C α).prod) :
    (s.map Height.mulHeight₁).prod
      = (f.map (Int.castRingHom ℂ)).mahlerMeasure ^ finrank ℚ L := by
  have ha : a ≠ 0 := by
    rintro rfl
    exact hf.ne_zero <|
      (Polynomial.map_eq_zero_iff (Int.castRingHom L).injective_int).mp (by simp [hsplit])
  set M := (f.map (Int.castRingHom ℂ)).mahlerMeasure with hM
  have harch : ∀ v : InfinitePlace L, (s.map fun α ↦ max (v α) 1).prod * (v a) = M := by
    intro v
    have h := mahler_local v.embedding hsplit
    simp only [InfinitePlace.norm_embedding_eq] at h
    rw [mul_comm]
    exact h
  have hfin : ∀ w : FinitePlace L, (s.map fun α ↦ max (w α) 1).prod * (w a) = 1 := by
    intro w
    have h := gauss_local (v := w.val) (fun x y ↦ FinitePlace.add_le w x y) hf hsplit
    rw [mul_comm]
    exact h
  have hdecomp : (s.map Height.mulHeight₁).prod
      = (∏ v : InfinitePlace L, (s.map fun α ↦ max (v α) 1).prod ^ v.mult)
        * ∏ᶠ w : FinitePlace L, (s.map fun α ↦ max (w α) 1).prod := by
    rw [show (Height.mulHeight₁ : L → ℝ)
        = (fun α ↦ (∏ v : InfinitePlace L, max (v α) 1 ^ v.mult)
            * ∏ᶠ w : FinitePlace L, max (w α) 1) from funext mulHeight₁_eq,
      Multiset.prod_map_mul, Multiset.prod_map_prod,
      multiset_prod_map_finprod s hasFiniteMulSupport_max_one]
    congr 1
    exact Finset.prod_congr rfl fun v _ ↦ Multiset.prod_map_pow
  have hA : (∏ v : InfinitePlace L, (v a) ^ v.mult) * ∏ᶠ w : FinitePlace L, w a = 1 :=
    prod_abs_eq_one ha
  have hB : (∏ᶠ w : FinitePlace L, (s.map fun α ↦ max (w α) 1).prod)
      * (∏ᶠ w : FinitePlace L, w a) = 1 := by
    rw [← finprod_mul_distrib (hasFiniteMulSupport_multiset_prod s hasFiniteMulSupport_max_one)
      (FinitePlace.hasFiniteMulSupport ha)]
    exact finprod_eq_one_of_forall_eq_one hfin
  have hC : (∏ v : InfinitePlace L, (s.map fun α ↦ max (v α) 1).prod ^ v.mult)
      * (∏ v : InfinitePlace L, (v a) ^ v.mult) = M ^ finrank ℚ L := by
    rw [← Finset.prod_mul_distrib]
    calc ∏ v : InfinitePlace L, ((s.map fun α ↦ max (v α) 1).prod ^ v.mult * (v a) ^ v.mult)
        = ∏ v : InfinitePlace L, M ^ v.mult :=
          Finset.prod_congr rfl fun v _ ↦ by rw [← mul_pow, harch v]
      _ = M ^ ∑ v : InfinitePlace L, v.mult := Finset.prod_pow_eq_pow_sum _ _ _
      _ = M ^ finrank ℚ L := by rw [← totalWeight_eq_sum_mult, totalWeight_eq_finrank]
  have key := hdecomp ▸ (mul_mul_mul_comm
    (∏ v : InfinitePlace L, (s.map fun α ↦ max (v α) 1).prod ^ v.mult)
    (∏ᶠ w : FinitePlace L, (s.map fun α ↦ max (w α) 1).prod)
    (∏ v : InfinitePlace L, (v a) ^ v.mult) (∏ᶠ w : FinitePlace L, w a))
  rw [hC, hB, mul_one, hA, mul_one] at key
  exact key

/-- **The product of the relative heights of the roots of a primitive integer polynomial over a
number field in which it splits is `M(f) ^ [L : ℚ]`.** This is the identity of this layer before
the normalizations: the roots are counted with multiplicity, the height is Mathlib's relative
height over `L`, and no minimal polynomial is involved. -/
theorem prod_mulHeight₁_roots_eq_mahlerMeasure_pow {f : ℤ[X]} (hf : f.IsPrimitive)
    (hsplits : (f.map (Int.castRingHom L)).Splits) :
    ((f.map (Int.castRingHom L)).roots.map Height.mulHeight₁).prod
      = (f.map (Int.castRingHom ℂ)).mahlerMeasure ^ finrank ℚ L :=
  prod_mulHeight₁_of_split hf hsplits.eq_prod_roots

end Core

/-!
### The absolute height of an algebraic number
-/

section Descent

variable {K : Type*} [Field K] [CharZero K]

/-- **The absolute height of an algebraic number is the `deg`-th root of the Mahler measure of its
primitive integer minimal polynomial** (Bombieri–Gubler, Proposition 1.6.6), stated as an equality
of `deg`-th powers so that no real exponentiation appears.

The polynomial is pinned as a primitive `f ∈ ℤ[X]` that is a nonzero rational multiple of
`minpoly ℚ x`; that determines `f` up to sign, and the Mahler measure ignores the sign. The
hypotheses force `x` algebraic, since `minpoly ℚ x = 0` otherwise while `0` is not primitive.

⚠ `f` is **not** `minpoly ℤ x`, which Mathlib defines to be `0` off the algebraic integers; see
the rejection test at the end of the file. -/
theorem absMulHeight₁_pow_natDegree {x : K} {f : ℤ[X]} (hf : f.IsPrimitive) {c : ℚ} (hc : c ≠ 0)
    (hfx : f.map (Int.castRingHom ℚ) = C c * minpoly ℚ x) :
    absMulHeight₁ x ^ f.natDegree = (f.map (Int.castRingHom ℂ)).mahlerMeasure := by
  have hmp : minpoly ℚ x ≠ 0 := fun h ↦ hf.ne_zero <|
    (Polynomial.map_eq_zero_iff (Int.castRingHom ℚ).injective_int).mp (by rw [hfx, h, mul_zero])
  have hx : IsIntegral ℚ x := minpoly.ne_zero_iff.mp hmp
  set g := minpoly ℚ x with hg
  set L := g.SplittingField with hL
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  have : NumberField L := {}
  have hcomp : (Int.castRingHom L) = (algebraMap ℚ L).comp (Int.castRingHom ℚ) :=
    Subsingleton.elim _ _
  have hfL : f.map (Int.castRingHom L) = C (algebraMap ℚ L c) * g.map (algebraMap ℚ L) := by
    rw [hcomp, ← Polynomial.map_map, hfx, Polynomial.map_mul, map_C]
  have hsplits : (f.map (Int.castRingHom L)).Splits := by
    rw [hfL]
    exact (Polynomial.IsSplittingField.splits (K := ℚ) (L := L) g).C_mul _
  set s := (f.map (Int.castRingHom L)).roots with hs
  have hcard : s.card = f.natDegree := by
    rw [hs, ← hsplits.natDegree_eq_card_roots,
      natDegree_map_eq_of_injective (Int.castRingHom L).injective_int]
  have hconj : ∀ α ∈ s, Height.mulHeight₁ α = absMulHeight₁ x ^ finrank ℚ L := by
    intro α hα
    have hroot : α ∈ g.aroots L := by
      rw [mem_aroots]
      refine ⟨hmp, ?_⟩
      have h0 : (f.map (Int.castRingHom L)).eval α = 0 := by
        rwa [hs, mem_roots
          (Polynomial.map_ne_zero_iff (Int.castRingHom L).injective_int |>.mpr hf.ne_zero),
          IsRoot.def] at hα
      rw [hfL, eval_mul, eval_C, mul_eq_zero] at h0
      rcases h0 with h0 | h0
      · exact absurd h0 (by simpa using hc)
      · rwa [aeval_def, eval₂_eq_eval_map]
    have hσ : ((algHomAdjoinIntegralEquiv (K := L) ℚ hx).symm ⟨α, hroot⟩)
        (AdjoinSimple.gen ℚ x) = α :=
      algHomAdjoinIntegralEquiv_symm_apply_gen ℚ hx ⟨α, hroot⟩
    rw [← absMulHeight₁_pow_finrank, ← hσ, absMulHeight₁_comp]
    congr 1
    exact (absMulHeight₁_comp (IntermediateField.val ℚ⟮x⟯) (AdjoinSimple.gen ℚ x)).symm
  have hlhs : (s.map Height.mulHeight₁).prod
      = (absMulHeight₁ x ^ f.natDegree) ^ finrank ℚ L := by
    rw [Multiset.map_congr rfl hconj, Multiset.map_const', Multiset.prod_replicate, hcard,
      ← pow_mul, ← pow_mul, Nat.mul_comm]
  have hcore := prod_mulHeight₁_roots_eq_mahlerMeasure_pow hf hsplits
  rw [← hs, hlhs] at hcore
  have hN : finrank ℚ L ≠ 0 := (Module.finrank_pos (R := ℚ) (M := L)).ne'
  have hH : 0 < absMulHeight₁ x := absMulHeight_eq_absMulHeight₁ x ▸ absMulHeight_pos _
  exact (pow_left_strictMonoOn₀ hN).injOn (pow_nonneg hH.le _) (mahlerMeasure_nonneg _) hcore

/-- The logarithmic form of `NumberField.absMulHeight₁_pow_natDegree`: `deg(x) · h(x) = log M(f)`,
which is how Bombieri–Gubler state Proposition 1.6.6. -/
theorem natDegree_nsmul_absLogHeight₁ {x : K} {f : ℤ[X]} (hf : f.IsPrimitive) {c : ℚ} (hc : c ≠ 0)
    (hfx : f.map (Int.castRingHom ℚ) = C c * minpoly ℚ x) :
    f.natDegree • absLogHeight₁ x = (f.map (Int.castRingHom ℂ)).logMahlerMeasure := by
  rw [logMahlerMeasure_eq_log_MahlerMeasure, ← absMulHeight₁_pow_natDegree hf hc hfx,
    Real.log_pow, absLogHeight₁, nsmul_eq_mul]

/-- **An algebraic number has a primitive integer minimal polynomial**, and its degree is the
degree of the number. This is `NumberField.absMulHeight₁_pow_natDegree` in the form a consumer
that is handed only `x` can use: the polynomial is produced rather than assumed.

Northcott's theorem is what needs it. The three side conditions are what that proof reads off the
polynomial: its degree bounds the degree of `x`, its Mahler measure is bounded by the height of
`x`, and `x` is one of its finitely many roots. -/
theorem exists_isPrimitive_absMulHeight₁_pow_natDegree {x : K} (hx : IsIntegral ℚ x) :
    ∃ f : ℤ[X], f.IsPrimitive ∧ f.natDegree = finrank ℚ ℚ⟮x⟯ ∧ aeval x f = 0 ∧
      absMulHeight₁ x ^ f.natDegree = (f.map (Int.castRingHom ℂ)).mahlerMeasure := by
  obtain ⟨f, c, hf, hc, hfx⟩ := exists_isPrimitive_map_eq_C_mul (minpoly.ne_zero hx)
  refine ⟨f, hf, ?_, ?_, absMulHeight₁_pow_natDegree hf hc hfx⟩
  · rw [← natDegree_map_eq_of_injective (Int.castRingHom ℚ).injective_int f, hfx,
      natDegree_C_mul hc, IntermediateField.adjoin.finrank hx]
  · have h : aeval x (f.map (Int.castRingHom ℚ)) = 0 := by
      rw [hfx, map_mul, aeval_C, minpoly.aeval, mul_zero]
    rwa [← algebraMap_int_eq, aeval_map_algebraMap] at h

end Descent

/-!
### Worked examples

The smallest case where the two sides can be computed independently, `x = 1/2` and `f = 2X - 1`,
and the rejection test for the ⚠ above.
-/

section Examples

/-- `2X - 1` is primitive: a constant dividing it divides its constant coefficient `-1`. -/
private lemma isPrimitive_two_X_sub_one : (2 * X - 1 : ℤ[X]).IsPrimitive := fun r hr ↦
  isUnit_of_dvd_one (by simpa using (C_dvd_iff_dvd_coeff r _).mp hr 0)

private lemma natDegree_two_X_sub_one : (2 * X - 1 : ℤ[X]).natDegree = 1 := by compute_degree!

/-- `2X - 1` is a primitive integer multiple of `minpoly ℚ (1/2) = X - 1/2`, so it is the
primitive integer minimal polynomial of `1/2`. -/
private lemma map_two_X_sub_one :
    (2 * X - 1 : ℤ[X]).map (Int.castRingHom ℚ) = C 2 * minpoly ℚ (1 / 2 : ℚ) := by
  rw [minpoly.eq_X_sub_C' (1 / 2 : ℚ), mul_sub, ← C_mul]
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat, Polynomial.map_X,
    Polynomial.map_one, map_ofNat]
  norm_num

/-- `M(2X - 1) = 2`, from Mathlib's formula for a linear polynomial. -/
private lemma mahlerMeasure_two_X_sub_one :
    ((2 * X - 1 : ℤ[X]).map (Int.castRingHom ℂ)).mahlerMeasure = 2 := by
  rw [show (2 * X - 1 : ℤ[X]).map (Int.castRingHom ℂ) = C 2 * X + C (-1) by
    simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat, Polynomial.map_X,
      Polynomial.map_one, map_ofNat, C_neg, C_1]
    ring, mahlerMeasure_C_mul_X_add_C two_ne_zero]
  norm_num

/-- `H(1/2) = 2`, from Mathlib's `Rat.mulHeight₁_eq_max`; over `ℚ` the absolute height is the
relative one, the degree being `1`. -/
private lemma absMulHeight₁_one_half : absMulHeight₁ (1 / 2 : ℚ) = 2 := by
  have h := absMulHeight₁_pow_finrank (1 / 2 : ℚ)
  rw [Module.finrank_self, pow_one, Rat.mulHeight₁_eq_max] at h
  rw [h]
  norm_num

/-- **Acceptance test.** Both sides of `absMulHeight₁_pow_natDegree` equal `2` on `x = 1/2`,
`f = 2X - 1`, each computed without the theorem. A version of the identity with `M(f)` divided by
the leading coefficient would give `1` on the right, and one with the `ℓ¹` norm of the coefficient
vector in place of `M(f)` would give `3`. -/
example : absMulHeight₁ (1 / 2 : ℚ) ^ (2 * X - 1 : ℤ[X]).natDegree = 2
    ∧ ((2 * X - 1 : ℤ[X]).map (Int.castRingHom ℂ)).mahlerMeasure = 2 :=
  ⟨by rw [natDegree_two_X_sub_one, pow_one, absMulHeight₁_one_half], mahlerMeasure_two_X_sub_one⟩

/-- The same case as an instance of the theorem, which is what ties the two values together. -/
example : absMulHeight₁ (1 / 2 : ℚ) ^ (2 * X - 1 : ℤ[X]).natDegree
    = ((2 * X - 1 : ℤ[X]).map (Int.castRingHom ℂ)).mahlerMeasure :=
  absMulHeight₁_pow_natDegree isPrimitive_two_X_sub_one two_ne_zero map_two_X_sub_one

private lemma not_isIntegral_one_half : ¬ IsIntegral ℤ (1 / 2 : ℚ) := by
  intro h
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  have h1 : (n : ℚ) = 1 / 2 := by simpa using hn
  have h2 : (2 : ℤ) * n = 1 := by exact_mod_cast (by rw [h1]; norm_num : (2 : ℚ) * n = 1)
  omega

/-- **Rejection test.** The same statement with `minpoly ℤ x` in place of `f` is false. Mathlib
defines `minpoly ℤ x = 0` off the algebraic integers, so at `x = 1/2` the left side is `1` and the
right side is `M(0) = 0`. Adding `IsIntegral ℤ x` to repair it would restrict the identity to
algebraic integers, where it cannot feed Northcott's theorem. -/
example : absMulHeight₁ (1 / 2 : ℚ) ^ (minpoly ℤ (1 / 2 : ℚ)).natDegree
    ≠ ((minpoly ℤ (1 / 2 : ℚ)).map (Int.castRingHom ℂ)).mahlerMeasure := by
  rw [minpoly.eq_zero not_isIntegral_one_half]
  simp

end Examples

end NumberField

end
