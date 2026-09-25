/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.RationalPlaces
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.RingTheory.DedekindDomain.SInteger

-- Used only inside proofs.
import ArithmeticHeights.SUnit
import DiophantineApproximation.LinearFormSubspaces
import DiophantineApproximation.NormForm
import DiophantineApproximation.SAdicHeight
import DiophantineApproximation.SubspaceAffine
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The Corvaja–Zannier gcd bound

**Layer 8.7** (Corvaja–Zannier; Bombieri–Gubler, Theorem 7.4.10). For a finite set `P` of primes
and `ε > 0`, the pairs `(u, v)` of nonzero integers whose prime factors lie in `P` and with
`gcd (u − 1) (v − 1) ≥ (max |u| |v|) ^ ε` are bounded, apart from those on finitely many curves
`u ^ a * v ^ b = 1` with `(a, b) ≠ (0, 0)`.

## Main results

* `Int.exists_forall_of_rpow_le_gcd_sub_one`: the theorem, as a bound `R` and a finite set `E` of
  exponent pairs.
* `Int.finite_setOf_rpow_le_gcd_sub_one`: only finitely many of the pairs are multiplicatively
  independent.
* `Nat.finite_setOf_exp_le_gcd_pow_sub_one`: Bugeaud–Corvaja–Zannier, `gcd (a ^ n − 1) (b ^ n − 1)`
  is at most `exp (ε n)` for all large `n`, for multiplicatively independent `a, b`.
* `Nat.finite_setOf_primeFactors_subset`: Corvaja–Zannier, the greatest prime factor of
  `(a b + 1)(a c + 1)` tends to infinity with `a`, for `a > b > c ≥ 1`.

## Implementation notes

⚠ **One application of 6.4, on a box of monomials, and no filtration.** Write `d` for the gcd and
take the `N² = (m + 2)²` monomials `u ^ (i + 1) * v ^ j` with `i, j < N`. The point is
`z (i, j) = (u ^ (i + 1) * v ^ j − 1) / d`, an integer vector because `u ≡ v ≡ 1` modulo `d`. At
the infinite place the forms are the coordinates, each of size at most `2 |u ^ (i + 1) v ^ j| / d`;
at every prime of `P` they are `z i − z top` and `z top`, where `top` is the monomial of highest
degree in both variables, the `p`-adically *smallest* one. Each is at most the `p`-adic size of its
monomial, and of `1` for the last. By the product formula for the `S`-units `u ^ a * v ^ b`
everything cancels except one monomial and the gcd, and the central quantity is at most
`(2 / d) ^ N² * |u| ^ N * |v| ^ (N − 1)`. Against a height at most `2 H ^ (2 N − 1)` the
`N²` powers of `d ≥ H ^ ε` win as soon as `ε N² > 4 N`, which is why the number of variables grows
like `1 / ε²`, and 6.4 puts `z` in one of finitely many proper subspaces. Every coordinate is a
polynomial vanishing at `(1, 1)` to order one, and that is all the argument needs; the filtrations
by higher order of vanishing that the general forms of the theorem use do not appear.

⚠ **The `p`-part of the gcd costs nothing.** At a prime `p ∈ P` dividing `d` the monomials are
`p`-adic units, so dividing by `d` there is paid for by `d` dividing the numerators; the bound of
each form is `|d|_p` times the size of its monomial in both cases
(`FinitePlace.apply_sub_le_mul`). So the statement holds for the ordinary gcd, not only for its
prime-to-`P` part, the form in which the `S`-unit version is usually stated.

⚠ **The relation is a homogeneous unit equation, and then elementary.** A subspace gives
`∑ c (i, j) (u ^ (i + 1) v ^ j − 1) = 0`, a vanishing sum of `S`-units; the homogeneous
Corollary 7.4.3 of Layer 8.6 makes some ratio `u ^ a v ^ b / u ^ a' v ^ b'` lie in a fixed finite
set. If the ratio is `1` the pair is on a curve `u ^ (a − a') v ^ (b − b') = 1`. Otherwise it is a
fixed `r / s ≠ 1`, and `u ≡ v ≡ 1` modulo `d` forces `d ∣ r − s` (`Int.dvd_num_sub_den`), so `d`,
and with it `H`, is bounded. No translate of a torus needs a separate treatment.

## References

P. Corvaja and U. Zannier, "On the greatest prime factor of `(ab + 1)(ac + 1)`", *Proc. Amer. Math.
Soc.* **131** (2003), 1705–1709; "A lower bound for the height of a rational function at `S`-unit
points", *Monatsh. Math.* **144** (2005), 203–224.

Y. Bugeaud, P. Corvaja and U. Zannier, "An upper bound for the G.C.D. of `a ^ n − 1` and
`b ^ n − 1`", *Math. Z.* **243** (2003), 79–84.

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
§7.4.

This is Layer 8.7 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Finset IsDedekindDomain Module NumberField

/-! ### The primes of `P` as places of `ℚ` -/

namespace Rat

open scoped Classical in
/-- The height-one primes of `𝓞 ℚ` over the primes in a finite set of natural numbers. -/
noncomputable def primesSpectrum (P : Finset ℕ) : Finset (HeightOneSpectrum (𝓞 ℚ)) :=
  (P.subtype Nat.Prime).image fun p ↦ (Rat.finitePlace p).maximalIdeal

theorem finitePlace_maximalIdeal_mem_primesSpectrum {P : Finset ℕ} {p : Nat.Primes}
    (hp : (p : ℕ) ∈ P) : (Rat.finitePlace p).maximalIdeal ∈ primesSpectrum P := by
  classical
  unfold primesSpectrum
  exact Finset.mem_image.mpr ⟨p, Finset.mem_subtype.mpr hp, rfl⟩

/-- **A nonzero integer whose prime factors lie in `P` is a unit at the primes of `P`.** -/
theorem mk0_intCast_mem_unit {P : Finset ℕ} {u : ℤ} (hu : u ≠ 0)
    (hP : u.natAbs.primeFactors ⊆ P) :
    Units.mk0 (u : ℚ) (Int.cast_ne_zero.mpr hu) ∈
      ((primesSpectrum P : Finset (HeightOneSpectrum (𝓞 ℚ))) :
        Set (HeightOneSpectrum (𝓞 ℚ))).unit ℚ := by
  refine (Set.mk0_mem_unit_iff_finitePlace _ _).mpr fun v hv ↦ ?_
  obtain ⟨q, hq, hvq⟩ := Rat.exists_prime_padic_eq (FinitePlace.mk v)
  have hqP : q ∉ P := fun hqP ↦ hv <| by
    have hmem : ∀ q' : Nat.Primes, (q' : ℕ) = q → v = (Rat.finitePlace q').maximalIdeal :=
      fun q' hq' ↦ by
        subst hq'
        rw [← FinitePlace.maximalIdeal_mk v]
        congr 1
        exact Subtype.ext (by rw [hvq, Rat.finitePlace_val])
    rw [hmem ⟨q, hq.out⟩ rfl]
    exact Finset.mem_coe.mpr (finitePlace_maximalIdeal_mem_primesSpectrum hqP)
  have hnorm : padicNorm q (u : ℚ) = 1 := (padicNorm.int_eq_one_iff u).mpr fun hdvd ↦
    hqP (hP (Nat.mem_primeFactors.mpr
      ⟨hq.out, Int.natCast_dvd.mp hdvd, Int.natAbs_ne_zero.mpr hu⟩))
  change (FinitePlace.mk v).1 (u : ℚ) = 1
  rw [hvq]
  change ((padicNorm q (u : ℚ) : ℚ) : ℝ) = 1
  exact_mod_cast hnorm

end Rat

/-! ### Congruences modulo the gcd -/

namespace Int

/-- If `u ≡ v ≡ 1` modulo `d`, so is every monomial `u ^ a * v ^ b`. -/
theorem dvd_pow_mul_pow_sub_one {d u v : ℤ} (hu : d ∣ u - 1) (hv : d ∣ v - 1) (a b : ℕ) :
    d ∣ u ^ a * v ^ b - 1 := by
  have := ((Int.modEq_iff_dvd.mpr hu).pow a).mul ((Int.modEq_iff_dvd.mpr hv).pow b)
  rw [one_pow, one_pow, one_mul] at this
  exact Int.modEq_iff_dvd.mp this

/-- **A rational number that is a quotient of two integers `≡ 1` modulo `d` is `≡ 1` modulo `d`**:
`d` divides its numerator minus its denominator. -/
theorem dvd_num_sub_den {d A B : ℤ} (hA : d ∣ A - 1) (hB : d ∣ B - 1) {φ : ℚ}
    (h : (A : ℚ) = φ * B) : d ∣ φ.num - φ.den := by
  have hden : (φ.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr φ.den_nz
  have hq : A * φ.den = φ.num * B := by
    have : (A : ℚ) * φ.den = φ.num * B := by
      rw [h, mul_right_comm, Rat.mul_den_eq_num]
    exact_mod_cast this
  have h1 : (φ.den : ℤ) ≡ A * φ.den [ZMOD d] := by
    simpa using (Int.modEq_iff_dvd.mpr hA).mul_right (φ.den : ℤ)
  have h2 : φ.num ≡ φ.num * B [ZMOD d] := by
    simpa using (Int.modEq_iff_dvd.mpr hB).mul_left φ.num
  exact Int.modEq_iff_dvd.mp (h1.trans (hq ▸ h2.symm))

end Int

/-! ### The local bounds -/

namespace NumberField.FinitePlace

/-- At a finite place of `ℚ` where `d` is small, `d ∣ u − 1` makes `u` a unit. -/
theorem apply_eq_one_of_lt_one (f : FinitePlace ℚ) {d u : ℤ} (hd : f (d : ℚ) < 1)
    (hu : d ∣ u - 1) : f (u : ℚ) = 1 := by
  obtain ⟨k, hk⟩ := hu
  have h1 : f ((u : ℚ) - 1) < 1 := by
    have : (u : ℚ) - 1 = (d : ℚ) * k := by exact_mod_cast hk
    rw [this, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (apply_nonneg _ _) (f.apply_intCast_le_one k)) hd
  refine le_antisymm (f.apply_intCast_le_one u) (not_lt.mp fun hlt ↦ ?_)
  have := f.add_le (u : ℚ) (-((u : ℚ) - 1))
  rw [map_neg_eq_map, show (u : ℚ) + -((u : ℚ) - 1) = 1 by ring, map_one] at this
  exact absurd this (not_le.mpr (max_lt hlt h1))

/-- **The local bound at a finite place.** If `u ≡ v ≡ 1` modulo `d` and the monomial
`u ^ a' v ^ b'` is at most `u ^ a v ^ b` at a finite place `f`, their difference is at most
`f d` times the larger. Where `f d = 1` this is the ultrametric inequality; where `f d < 1` both
monomials are units and `d` divides the difference. -/
theorem apply_sub_le_mul (f : FinitePlace ℚ) {u v d : ℤ} (hdu : d ∣ u - 1) (hdv : d ∣ v - 1)
    {a b a' b' : ℕ} (hle : f ((u : ℚ) ^ a' * (v : ℚ) ^ b') ≤ f ((u : ℚ) ^ a * (v : ℚ) ^ b)) :
    f ((u : ℚ) ^ a * (v : ℚ) ^ b - (u : ℚ) ^ a' * (v : ℚ) ^ b') ≤
      f (d : ℚ) * f ((u : ℚ) ^ a * (v : ℚ) ^ b) := by
  by_cases hd : f (d : ℚ) < 1
  · rw [map_mul, map_pow, map_pow, f.apply_eq_one_of_lt_one hd hdu,
      f.apply_eq_one_of_lt_one hd hdv, one_pow, one_pow, mul_one, mul_one]
    obtain ⟨k, hk⟩ := (dvd_sub (Int.dvd_pow_mul_pow_sub_one hdu hdv a b)
      (Int.dvd_pow_mul_pow_sub_one hdu hdv a' b'))
    have : (u : ℚ) ^ a * (v : ℚ) ^ b - (u : ℚ) ^ a' * (v : ℚ) ^ b' = (d : ℚ) * k := by
      rw [sub_sub_sub_cancel_right] at hk
      exact_mod_cast hk
    rw [this, map_mul]
    exact mul_le_of_le_one_right (apply_nonneg _ _) (f.apply_intCast_le_one k)
  · rw [le_antisymm (f.apply_intCast_le_one d) (not_lt.mp hd), one_mul, sub_eq_add_neg]
    exact (f.add_le _ _).trans (by rw [map_neg_eq_map, max_eq_left hle])

/-- A finite place of `ℚ` is not the infinite one: it is at most `1` at `2`. -/
theorem val_ne_infinitePlace (f : FinitePlace ℚ) : f.1 ≠ Rat.infinitePlace.1 := by
  intro h
  have h1 : f ((2 : ℤ) : ℚ) ≤ 1 := f.apply_intCast_le_one 2
  rw [FinitePlace.coe_apply, h, ← InfinitePlace.coe_apply, Rat.infinitePlace_apply] at h1
  norm_num at h1

end NumberField.FinitePlace

/-! ### The forms and the central quantity -/

namespace Int

open Height NumberField.FinitePlace

variable {m : ℕ}

/-- The monomial of highest degree in both variables. -/
private def top (m : ℕ) : Fin (m + 2) × Fin (m + 2) := (Fin.last _, Fin.last _)

/-- The coordinate forms. -/
private noncomputable def coordForms (m : ℕ) :
    Fin (m + 2) × Fin (m + 2) → Dual ℚ (Fin (m + 2) × Fin (m + 2) → ℚ) :=
  (Pi.basisFun ℚ _).dualBasis

private theorem coordForms_apply (i : Fin (m + 2) × Fin (m + 2))
    (x : Fin (m + 2) × Fin (m + 2) → ℚ) : coordForms m i x = x i := by
  simp [coordForms]

/-- The forms at the primes: `z i − z top`, and `z top` itself. -/
private noncomputable def triForms (m : ℕ) :
    Fin (m + 2) × Fin (m + 2) → Dual ℚ (Fin (m + 2) × Fin (m + 2) → ℚ) :=
  fun i ↦ coordForms m i - if i = top m then 0 else coordForms m (top m)

private theorem triForms_apply (i : Fin (m + 2) × Fin (m + 2))
    (x : Fin (m + 2) × Fin (m + 2) → ℚ) :
    triForms m i x = x i - if i = top m then 0 else x (top m) := by
  unfold triForms
  split_ifs <;> simp [coordForms_apply]

private theorem linearIndependent_triForms : LinearIndependent ℚ (triForms m) := by
  refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ ?_
  · rw [← (Pi.basisFun ℚ (Fin (m + 2) × Fin (m + 2))).dualBasis.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    by_cases hi : i = top m
    · refine Submodule.subset_span ⟨top m, ?_⟩
      subst hi
      simp [triForms, coordForms]
    · have : (Pi.basisFun ℚ _).dualBasis i = triForms m i + triForms m (top m) := by
        simp [triForms, coordForms, hi]
      rw [this]
      exact add_mem (Submodule.subset_span ⟨i, rfl⟩) (Submodule.subset_span ⟨top m, rfl⟩)
  · rw [Subspace.dual_finrank_eq, Module.finrank_fintype_fun_eq_card]

open scoped Classical in
/-- The forms of the proof: coordinates at the infinite place, `triForms` elsewhere. -/
private noncomputable def gcdForms (m : ℕ) :
    AbsoluteValue ℚ ℝ → Fin (m + 2) × Fin (m + 2) → Dual ℚ (Fin (m + 2) × Fin (m + 2) → ℚ) :=
  fun w ↦ if w = Rat.infinitePlace.1 then coordForms m else triForms m

/-- The monomial `u ^ (i + 1) * v ^ j` at the index `(i, j)`. -/
private def mono (u v : ℤ) (i : Fin (m + 2) × Fin (m + 2)) : ℚ :=
  (u : ℚ) ^ ((i.1 : ℕ) + 1) * (v : ℚ) ^ (i.2 : ℕ)

private theorem prod_infinitePlace_rat (g : InfinitePlace ℚ → ℝ) :
    ∏ v, g v = g Rat.infinitePlace := by
  rw [Fintype.prod_unique]
  exact congrArg g (Subsingleton.elim _ _)

private theorem infinitePlace_apply_rat (v : InfinitePlace ℚ) (x : ℚ) :
    v.1 x = |(x : ℝ)| := by
  rw [← InfinitePlace.coe_apply, Rat.infinitePlace_apply, Rat.cast_abs]

/-- **The `S`-product formula over `ℚ`**: `|x| · ∏_{p ∈ S} |x|_p = 1` for an `S`-unit `x`. -/
private theorem abs_mul_prod_eq_one {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {x : ℚˣ}
    (hx : x ∈ (S : Set (HeightOneSpectrum (𝓞 ℚ))).unit ℚ) :
    |((x : ℚ) : ℝ)| * ∏ p ∈ S, FinitePlace.mk p (x : ℚ) = 1 := by
  have h := prod_apply_eq_one_of_mem_unit S hx
  rwa [prod_infinitePlace_rat, InfinitePlace.IsReal.mult_eq_one Rat.isReal_infinitePlace, pow_one,
    Rat.infinitePlace_apply, Rat.cast_abs] at h

/-- **The central quantity at the point of the proof** is at most
`(2 / d) ^ N² * |u ^ N * v ^ (N − 1)|`. -/
private theorem affineProd_le {P : Finset ℕ} {u v d : ℤ} (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (huP : u.natAbs.primeFactors ⊆ P) (hvP : v.natAbs.primeFactors ⊆ P) (hd : 0 < d)
    (hdu : d ∣ u - 1) (hdv : d ∣ v - 1) :
    affineProd (Rat.primesSpectrum P) (fun w ↦ w) (gcdForms m)
        (fun i ↦ (mono u v i - 1) / d) ≤
      (2 / d) ^ ((m + 2) * (m + 2)) * |((mono u v (top m) : ℚ) : ℝ)| := by
  classical
  set S := Rat.primesSpectrum P
  set x : Fin (m + 2) × Fin (m + 2) → ℚ := fun i ↦ (mono u v i - 1) / d with hx
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hU := Rat.mk0_intCast_mem_unit hu0 huP
  have hV := Rat.mk0_intCast_mem_unit hv0 hvP
  -- the monomials are `S`-units
  have hmono : ∀ a b : ℕ, ∃ y : ℚˣ, y ∈ (S : Set (HeightOneSpectrum (𝓞 ℚ))).unit ℚ ∧
      (y : ℚ) = (u : ℚ) ^ a * (v : ℚ) ^ b := fun a b ↦
    ⟨Units.mk0 (u : ℚ) (Int.cast_ne_zero.mpr hu0) ^ a *
      Units.mk0 (v : ℚ) (Int.cast_ne_zero.mpr hv0) ^ b,
      mul_mem (pow_mem hU a) (pow_mem hV b), by simp⟩
  have halg : ∀ q : ℚ, algebraMap ℚ ℚ q = q := fun q ↦ rfl
  have hone : ∀ a b : ℕ, 1 ≤ |((u : ℚ) : ℝ) ^ a * ((v : ℚ) : ℝ) ^ b| := fun a b ↦ by
    rw [abs_mul, abs_pow, abs_pow]
    have h1 : (1 : ℝ) ≤ |((u : ℚ) : ℝ)| := by
      push_cast; exact_mod_cast Int.one_le_abs hu0
    have h2 : (1 : ℝ) ≤ |((v : ℚ) : ℝ)| := by
      push_cast; exact_mod_cast Int.one_le_abs hv0
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ h1) (one_le_pow₀ h2)
  -- the infinite place
  have hinf : (∏ w : InfinitePlace ℚ,
        (∏ i, w.1 (gcdForms m w.1 i fun j ↦ algebraMap ℚ ℚ (x j))) ^ w.mult) ≤
      ∏ i : Fin (m + 2) × Fin (m + 2), 2 / d * |((mono u v i : ℚ) : ℝ)| := by
    rw [prod_infinitePlace_rat, InfinitePlace.IsReal.mult_eq_one Rat.isReal_infinitePlace,
      pow_one]
    refine Finset.prod_le_prod₀ (fun i _ ↦ apply_nonneg _ _) fun i _ ↦ ?_
    rw [gcdForms, ite_eq_left rfl, coordForms_apply, halg, infinitePlace_apply_rat, hx]
    have h1 := hone ((i.1 : ℕ) + 1) i.2
    simp only [mono] at h1 ⊢
    push_cast at h1 ⊢
    rw [abs_div, abs_of_pos hdR, div_le_iff₀ hdR,
      show ∀ X : ℝ, 2 / (d : ℝ) * X * d = 2 * X from fun X ↦ by field_simp]
    calc |(u : ℝ) ^ ((i.1 : ℕ) + 1) * (v : ℝ) ^ (i.2 : ℕ) - 1|
        ≤ |(u : ℝ) ^ ((i.1 : ℕ) + 1) * (v : ℝ) ^ (i.2 : ℕ)| + |(1 : ℝ)| := abs_sub _ _
      _ ≤ 2 * |(u : ℝ) ^ ((i.1 : ℕ) + 1) * (v : ℝ) ^ (i.2 : ℕ)| := by
        rw [abs_one]; linarith
  -- the finite places
  set m' : Fin (m + 2) × Fin (m + 2) → ℚ := fun i ↦ if i = top m then 1 else mono u v i
    with hm'
  have hfin : ∀ p ∈ S, ∏ i, (FinitePlace.mk p).1
        (gcdForms m (FinitePlace.mk p).1 i fun j ↦ algebraMap ℚ ℚ (x j)) ≤
      ∏ i, FinitePlace.mk p (m' i) := by
    intro p _
    set f := FinitePlace.mk p
    have hfd : 0 < f (d : ℚ) := FinitePlace.pos_iff.mpr (by exact_mod_cast hd.ne')
    refine Finset.prod_le_prod₀ (fun i _ ↦ apply_nonneg _ _) fun i _ ↦ ?_
    rw [gcdForms, ite_eq_right (val_ne_infinitePlace f), triForms_apply]
    simp only [halg, hx]
    change f _ ≤ f _
    have htop : ∀ a b : ℕ, a ≤ m + 2 → b ≤ m + 1 →
        f ((u : ℚ) ^ (m + 2) * (v : ℚ) ^ (m + 1)) ≤ f ((u : ℚ) ^ a * (v : ℚ) ^ b) := by
      intro a b ha hb
      rw [map_mul, map_pow, map_pow, map_mul, map_pow, map_pow]
      exact mul_le_mul (pow_le_pow_of_le_one (apply_nonneg _ _) (f.apply_intCast_le_one u) ha)
        (pow_le_pow_of_le_one (apply_nonneg _ _) (f.apply_intCast_le_one v) hb)
        (pow_nonneg (apply_nonneg _ _) _) (pow_nonneg (apply_nonneg _ _) _)
    have hmtop : mono u v (top m) = (u : ℚ) ^ (m + 2) * (v : ℚ) ^ (m + 1) := by
      simp [mono, top]
    by_cases hi : i = top m
    · subst hi
      have e1 : m' (top m) = 1 := by simp [hm']
      rw [e1, ite_eq_left rfl, sub_zero, hmtop, map_div₀, div_le_iff₀ hfd, map_one, one_mul]
      have h := apply_sub_le_mul f hdu hdv (a := 0) (b := 0)
        (htop 0 0 (Nat.zero_le _) (Nat.zero_le _))
      rw [pow_zero, pow_zero, mul_one, map_one, mul_one] at h
      rw [show (u : ℚ) ^ (m + 2) * (v : ℚ) ^ (m + 1) - 1 =
        -(1 - (u : ℚ) ^ (m + 2) * (v : ℚ) ^ (m + 1)) by ring, map_neg_eq_map]
      exact h
    · have e1 : m' i = mono u v i := by simp [hm', hi]
      rw [e1, ite_eq_right hi, div_sub_div_same, sub_sub_sub_cancel_right, map_div₀,
        div_le_iff₀ hfd, mul_comm, hmtop]
      exact apply_sub_le_mul f hdu hdv (htop _ _ (by omega) (by omega))
  -- the product formula
  have hpf : ∀ i, |((mono u v i : ℚ) : ℝ)| * ∏ p ∈ S, FinitePlace.mk p (m' i) =
      if i = top m then |((mono u v (top m) : ℚ) : ℝ)| else 1 := by
    intro i
    by_cases hi : i = top m
    · simp [hm', hi]
    · obtain ⟨y, hy, hyv⟩ := hmono ((i.1 : ℕ) + 1) i.2
      simp only [hm', ite_eq_right hi]
      have := abs_mul_prod_eq_one hy
      rwa [hyv] at this
  calc affineProd S (fun w ↦ w) (gcdForms m) x
      ≤ (∏ i : Fin (m + 2) × Fin (m + 2), 2 / d * |((mono u v i : ℚ) : ℝ)|) *
          ∏ p ∈ S, ∏ i, FinitePlace.mk p (m' i) :=
        mul_le_mul hinf (Finset.prod_le_prod₀ (fun p _ ↦ Finset.prod_nonneg fun _ _ ↦
          apply_nonneg _ _) hfin)
          (Finset.prod_nonneg fun _ _ ↦ Finset.prod_nonneg fun _ _ ↦ apply_nonneg _ _)
          (Finset.prod_nonneg fun _ _ ↦ by positivity)
    _ = (2 / d) ^ ((m + 2) * (m + 2)) *
          ∏ i : Fin (m + 2) × Fin (m + 2),
            (|((mono u v i : ℚ) : ℝ)| * ∏ p ∈ S, FinitePlace.mk p (m' i)) := by
        rw [Finset.prod_comm (s := S), Finset.prod_mul_distrib, Finset.prod_const,
          Finset.card_univ, Fintype.card_prod, Fintype.card_fin, mul_assoc,
          ← Finset.prod_mul_distrib]
    _ = _ := by
        simp only [hpf]
        rw [Finset.prod_ite_eq' Finset.univ (top m), ite_eq_left (Finset.mem_univ _)]

/-- The monomials are at most `H ^ (2 m + 3)`. -/
private theorem abs_mono_le {u v : ℤ} {H : ℝ} (hH : 1 ≤ H) (hu : |(u : ℝ)| ≤ H)
    (hv : |(v : ℝ)| ≤ H) (i : Fin (m + 2) × Fin (m + 2)) :
    |((mono u v i : ℚ) : ℝ)| ≤ H ^ (2 * m + 3) := by
  have h1 := i.1.isLt
  have h2 := i.2.isLt
  simp only [mono]
  push_cast
  rw [abs_mul, abs_pow, abs_pow]
  calc |(u : ℝ)| ^ ((i.1 : ℕ) + 1) * |(v : ℝ)| ^ (i.2 : ℕ)
      ≤ H ^ ((i.1 : ℕ) + 1) * H ^ (i.2 : ℕ) :=
        mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hu _) (pow_le_pow_left₀ (abs_nonneg _) hv _)
          (by positivity) (by positivity)
    _ = H ^ ((i.1 : ℕ) + 1 + i.2) := by rw [← pow_add]
    _ ≤ H ^ (2 * m + 3) := pow_le_pow_right₀ hH (by omega)

/-- The monomials are at least `1` in absolute value. -/
private theorem one_le_abs_mono {u v : ℤ} (hu : u ≠ 0) (hv : v ≠ 0)
    (i : Fin (m + 2) × Fin (m + 2)) : 1 ≤ |((mono u v i : ℚ) : ℝ)| := by
  simp only [mono]
  push_cast
  rw [abs_mul, abs_pow, abs_pow]
  have h1 : (1 : ℝ) ≤ |(u : ℝ)| := by exact_mod_cast Int.one_le_abs hu
  have h2 : (1 : ℝ) ≤ |(v : ℝ)| := by exact_mod_cast Int.one_le_abs hv
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ h1) (one_le_pow₀ h2)

/-- **The numerical heart**: `N²` powers of `d ≥ H ^ ε` beat `H ^ (4 m + 6)` once
`ε N² ≥ 4 m + 7` and `H ≥ 2 ^ (N² + 1)`. -/
private theorem pow_mul_le_inv {H d ε : ℝ} (hH : 2 ^ ((m + 2) * (m + 2) + 1) ≤ H)
    (hdH : H ^ ε ≤ d) (hεM : ((4 * m + 7 : ℕ) : ℝ) ≤ ε * ((m + 2) * (m + 2) : ℕ)) :
    (2 / d) ^ ((m + 2) * (m + 2)) * H ^ (2 * m + 3) ≤ (2 * H ^ (2 * m + 3))⁻¹ := by
  set M := (m + 2) * (m + 2)
  have hH1 : 1 ≤ H := le_trans (one_le_pow₀ one_le_two) hH
  have hH0 : 0 < H := zero_lt_one.trans_le hH1
  have hd0 : 0 < d := lt_of_lt_of_le (Real.rpow_pos_of_pos hH0 ε) hdH
  have key : 2 ^ (M + 1) * H ^ (4 * m + 6) ≤ d ^ M :=
    calc 2 ^ (M + 1) * H ^ (4 * m + 6) ≤ H * H ^ (4 * m + 6) :=
          mul_le_mul_of_nonneg_right hH (by positivity)
      _ = H ^ (((4 * m + 7 : ℕ)) : ℝ) := by rw [Real.rpow_natCast]; ring
      _ ≤ H ^ (ε * (M : ℕ)) := Real.rpow_le_rpow_of_exponent_le hH1 hεM
      _ = (H ^ ε) ^ M := by rw [Real.rpow_mul hH0.le, Real.rpow_natCast]
      _ ≤ d ^ M := pow_le_pow_left₀ (Real.rpow_nonneg hH0.le _) hdH M
  have hpos : 0 < 2 * H ^ (2 * m + 3) := by positivity
  rw [← one_div, le_div_iff₀ hpos]
  calc (2 / d) ^ M * H ^ (2 * m + 3) * (2 * H ^ (2 * m + 3))
      = 2 ^ (M + 1) * H ^ (4 * m + 6) / d ^ M := by
        rw [div_pow]
        field_simp
        ring
    _ ≤ d ^ M / d ^ M := div_le_div_of_nonneg_right key (by positivity)
    _ = 1 := div_self (by positivity)

/-- The exponents of the monomials of the unit equation: `(0, 0)` for the constant, and
`(i + 1, j)` at the index `(i, j)`. -/
private def ex (m : ℕ) : Option (Fin (m + 2) × Fin (m + 2)) → ℕ × ℕ :=
  fun o ↦ o.elim (0, 0) fun i ↦ ((i.1 : ℕ) + 1, i.2)

private theorem ex_injective : Function.Injective (ex m) := by
  intro o o' h
  cases o with
  | none =>
    cases o' with
    | none => rfl
    | some j => simp only [ex, Option.elim, Prod.mk.injEq] at h; omega
  | some i =>
    cases o' with
    | none => simp only [ex, Option.elim, Prod.mk.injEq] at h; omega
    | some j =>
      simp only [ex, Option.elim, Prod.mk.injEq] at h
      exact congrArg some (Prod.ext (Fin.ext (by omega)) (Fin.ext h.2))

private theorem ex_le (o : Option (Fin (m + 2) × Fin (m + 2))) :
    (ex m o).1 ≤ m + 2 ∧ (ex m o).2 ≤ m + 2 := by
  cases o with
  | none => simp [ex]
  | some i =>
    have := i.1.isLt
    have := i.2.isLt
    simp only [ex, Option.elim]
    omega

/-- **The Corvaja–Zannier gcd bound** (Corvaja–Zannier; Bombieri–Gubler, Theorem 7.4.10), over
`ℤ`. For a finite set `P` of primes and `ε > 0` there are a bound `R` and finitely many nonzero
exponent pairs `E` such that every pair of nonzero integers `u, v` with prime factors in `P` and
`gcd (u − 1) (v − 1) ≥ (max |u| |v|) ^ ε` either has `max |u| |v| ≤ R` or satisfies
`u ^ a * v ^ b = 1` for some `(a, b) ∈ E`. -/
theorem exists_forall_of_rpow_le_gcd_sub_one (P : Finset ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℤ, ∃ E : Finset (ℤ × ℤ), (0, 0) ∉ E ∧ ∀ u v : ℤ, u ≠ 0 → v ≠ 0 →
      u.natAbs.primeFactors ⊆ P → v.natAbs.primeFactors ⊆ P →
      ((max |u| |v| : ℤ) : ℝ) ^ ε ≤ (Int.gcd (u - 1) (v - 1) : ℝ) →
      max |u| |v| ≤ R ∨ ∃ e ∈ E, (u : ℚ) ^ e.1 * (v : ℚ) ^ e.2 = 1 := by
  classical
  set m : ℕ := ⌈4 / ε⌉₊ with hm
  set S := Rat.primesSpectrum P
  set M : ℕ := (m + 2) * (m + 2) with hM
  have hεM : ((4 * m + 7 : ℕ) : ℝ) ≤ ε * ((m + 2) * (m + 2) : ℕ) := by
    have h4 : 4 ≤ ε * m := by
      have := Nat.le_ceil (4 / ε)
      rw [← hm, div_le_iff₀ hε] at this
      linarith
    push_cast
    nlinarith
  -- Layer 6.4
  have hLInf : ∀ w : InfinitePlace ℚ, LinearIndependent ℚ (gcdForms m w.1) := fun w ↦ by
    rw [gcdForms, ite_eq_left (by rw [Subsingleton.elim w Rat.infinitePlace])]
    exact (Pi.basisFun ℚ _).dualBasis.linearIndependent
  have hLFin : ∀ p ∈ S, LinearIndependent ℚ (gcdForms m (FinitePlace.mk p).1) := fun p _ ↦ by
    rw [gcdForms, ite_eq_right (FinitePlace.val_ne_infinitePlace _)]
    exact linearIndependent_triForms
  obtain ⟨T, hT, hcov⟩ := exists_finset_submodule_of_integer_of_affineProd_le (K := ℚ) (F := ℚ)
    (ι := Fin (m + 2) × Fin (m + 2)) S (fun w ↦ w) (fun _ ↦ ⟨AbsoluteValue.ext fun _ ↦ rfl⟩)
    (fun _ _ ↦ ⟨AbsoluteValue.ext fun _ ↦ rfl⟩) (gcdForms m) hLInf hLFin one_pos
  -- a linear relation on each subspace
  have hfun : ∀ W ∈ T, ∃ c : Fin (m + 2) × Fin (m + 2) → ℚ, ∃ i₀, c i₀ ≠ 0 ∧
      ∀ x ∈ W, ∑ i, c i * x i = 0 := by
    intro W hW
    obtain ⟨f, hf0, hWf⟩ := W.exists_le_ker_of_lt_top (hT W hW).lt_top
    set c : Fin (m + 2) × Fin (m + 2) → ℚ := fun i ↦ f fun j ↦ if i = j then 1 else 0 with hc
    have hfc : ∀ y, f y = ∑ i, c i * y i := fun y ↦ by
      rw [LinearMap.pi_apply_eq_sum_univ f y]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [smul_eq_mul, mul_comm]
    obtain ⟨i₀, hi₀⟩ : ∃ i, c i ≠ 0 := by
      by_contra! h
      exact hf0 (LinearMap.ext fun y ↦ by simp [hfc, h])
    exact ⟨c, i₀, hi₀, fun x hx ↦ (hfc x).symm.trans (LinearMap.mem_ker.mp (hWf hx))⟩
  choose! c i₀ hc0 hcW using hfun
  -- the homogeneous unit equation of Layer 8.6
  set a : Submodule ℚ (Fin (m + 2) × Fin (m + 2) → ℚ) → Option (Fin (m + 2) × Fin (m + 2)) → ℚ :=
    fun W o ↦ o.elim (-∑ i, c W i) (c W) with ha
  have hΦ : ∀ W ∈ T, ∃ Φ : Set ℚ, Φ.Finite ∧ ∀ y : Option (Fin (m + 2) × Fin (m + 2)) → ℚˣ,
      (∀ o, y o ∈ (S : Set (HeightOneSpectrum (𝓞 ℚ))).unit ℚ) → ∑ o, a W o * y o = 0 →
      ∃ o ≠ some (i₀ W), a W o ≠ 0 ∧ (y o : ℚ) / y (some (i₀ W)) ∈ Φ := fun W hW ↦
    exists_finite_forall_exists_div_mem S (a W) (i₀ := some (i₀ W)) (hc0 W hW)
  choose! Φ hΦfin hΦ using hΦ
  have hΦall : (⋃ W ∈ T, Φ W).Finite := T.finite_toSet.biUnion fun W hW ↦ hΦfin W hW
  obtain ⟨B, hB⟩ := (hΦall.image fun φ : ℚ ↦ ((|φ.num - φ.den| : ℤ) : ℝ)).bddAbove
  set Rℝ : ℝ := max (2 ^ (M + 1)) (max B 1 ^ ε⁻¹) with hRℝ
  refine ⟨⌈Rℝ⌉, (Finset.Icc (-(m + 2 : ℤ)) (m + 2) ×ˢ Finset.Icc (-(m + 2 : ℤ)) (m + 2)).erase
    (0, 0), Finset.notMem_erase _ _, ?_⟩
  intro u v hu0 hv0 huP hvP hgcd
  set H : ℝ := ((max |u| |v| : ℤ) : ℝ) with hH
  by_cases hu1 : u = 1
  · refine Or.inr ⟨(1, 0), Finset.mem_erase.mpr ⟨by simp, ?_⟩, by simp [hu1]⟩
    simp only [Finset.mem_product, Finset.mem_Icc]
    omega
  by_cases hHR : H ≤ Rℝ
  · exact Or.inl (Int.cast_le.mp (hHR.trans (Int.le_ceil _)))
  refine Or.inr ?_
  push Not at hHR
  have huH : |(u : ℝ)| ≤ H := by rw [hH]; exact_mod_cast le_max_left _ _
  have hvH : |(v : ℝ)| ≤ H := by rw [hH]; exact_mod_cast le_max_right _ _
  have hH1 : 1 ≤ H := le_trans (by exact_mod_cast Int.one_le_abs hu0) huH
  have hH0 : 0 < H := zero_lt_one.trans_le hH1
  -- the gcd and the point
  set d : ℤ := (Int.gcd (u - 1) (v - 1) : ℤ) with hd
  have hdpos : 0 < d := by
    rw [hd]; exact_mod_cast Int.gcd_pos_of_ne_zero_left (v - 1) (sub_ne_zero.mpr hu1)
  have hdu : d ∣ u - 1 := Int.gcd_dvd_left ..
  have hdv : d ∣ v - 1 := Int.gcd_dvd_right ..
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hdpos.ne'
  set Z : Fin (m + 2) × Fin (m + 2) → ℤ :=
    fun i ↦ (u ^ ((i.1 : ℕ) + 1) * v ^ (i.2 : ℕ) - 1) / d with hZdef
  have hZ : ∀ i, (Z i : ℚ) = (mono u v i - 1) / d := fun i ↦ by
    rw [hZdef, Int.cast_div (Int.dvd_pow_mul_pow_sub_one hdu hdv _ _) hdQ]
    simp [mono]
  have hz : (fun i ↦ (Z i : ℚ)) = fun i ↦ (mono u v i - 1) / d := funext hZ
  have hz0 : (fun i ↦ (Z i : ℚ)) ≠ 0 := fun h ↦ by
    have h0 := congrFun h (0, 0)
    rw [hZ] at h0
    simp only [mono, Fin.val_zero, zero_add, pow_one, pow_zero, mul_one, Pi.zero_apply,
      div_eq_zero_iff, hdQ, or_false, sub_eq_zero] at h0
    exact hu1 (by exact_mod_cast h0)
  -- the central quantity against the height
  have hdH : H ^ ε ≤ (d : ℝ) := by rw [hd]; exact_mod_cast hgcd
  have hHM : (2 : ℝ) ^ (M + 1) ≤ H := (le_max_left _ _).trans hHR.le
  have hbound : affineProd S (fun w ↦ w) (gcdForms m) (fun i ↦ (Z i : ℚ)) ≤
      mulHeight (fun i ↦ (Z i : ℚ)) ^ (-(1 : ℝ)) := by
    have hht : mulHeight (fun i ↦ (Z i : ℚ)) ≤ 2 * H ^ (2 * m + 3) := by
      refine (Rat.mulHeight_intCast_le_iSup Rat.infinitePlace hz0).trans (ciSup_le fun i ↦ ?_)
      rw [Rat.infinitePlace_apply, Rat.cast_abs, hZ]
      have h1 := one_le_abs_mono (m := m) hu0 hv0 i
      have h2 := abs_mono_le (m := m) hH1 huH hvH i
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hdpos
      push_cast at h1 h2 ⊢
      rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < d)]
      calc |(mono u v i : ℝ) - 1| / d ≤ |(mono u v i : ℝ) - 1| :=
            div_le_self (abs_nonneg _) hd1
        _ ≤ |(mono u v i : ℝ)| + |(1 : ℝ)| := abs_sub _ _
        _ ≤ 2 * H ^ (2 * m + 3) := by rw [abs_one]; linarith
    have hA := affineProd_le (m := m) hu0 hv0 huP hvP hdpos hdu hdv
    rw [← hz] at hA
    have htop := abs_mono_le (m := m) hH1 huH hvH (top m)
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hdpos
    refine hA.trans ((mul_le_mul_of_nonneg_left htop (by positivity)).trans
      ((pow_mul_le_inv hHM hdH hεM).trans ?_))
    rw [Real.rpow_neg_one]
    exact inv_anti₀ (lt_of_lt_of_le zero_lt_one (one_le_mulHeight _)) hht
  obtain ⟨W, hWT, hzW⟩ := hcov _ hz0 (fun j ↦ intCast_mem _ _) hbound
  have hrel := hcW W hWT _ hzW
  -- the unit equation
  set U : ℚˣ := Units.mk0 (u : ℚ) (Int.cast_ne_zero.mpr hu0)
  set V : ℚˣ := Units.mk0 (v : ℚ) (Int.cast_ne_zero.mpr hv0)
  set y : Option (Fin (m + 2) × Fin (m + 2)) → ℚˣ := fun o ↦ U ^ (ex m o).1 * V ^ (ex m o).2
    with hy
  have hyv : ∀ o, (y o : ℚ) = (u : ℚ) ^ (ex m o).1 * (v : ℚ) ^ (ex m o).2 := fun o ↦ by
    simp [hy, U, V]
  have hyS : ∀ o, y o ∈ (S : Set (HeightOneSpectrum (𝓞 ℚ))).unit ℚ := fun o ↦
    mul_mem (pow_mem (Rat.mk0_intCast_mem_unit hu0 huP) _)
      (pow_mem (Rat.mk0_intCast_mem_unit hv0 hvP) _)
  have hsum : ∑ o, a W o * y o = 0 := by
    have h2 : ∑ i, c W i * (mono u v i - 1) = 0 := by
      simp only [hZ, mul_div_assoc', ← Finset.sum_div, div_eq_zero_iff, hdQ, or_false] at hrel
      exact hrel
    rw [Fintype.sum_option]
    simp only [ha, Option.elim, hyv, ex, pow_zero, mul_one]
    rw [← h2, Finset.sum_congr rfl fun i _ ↦ mul_sub_one (c W i) (mono u v i),
      Finset.sum_sub_distrib]
    simp only [mono]
    ring
  obtain ⟨o, hne, -, hφ⟩ := hΦ W hWT y hyS hsum
  have hee : ex m o ≠ ex m (some (i₀ W)) := fun h ↦ hne (ex_injective h)
  obtain ⟨h1, h2⟩ := ex_le (m := m) o
  obtain ⟨h1', h2'⟩ := ex_le (m := m) (some (i₀ W))
  have hu' : (u : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hu0
  have hv' : (v : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hv0
  by_cases hφ1 : (y o : ℚ) / y (some (i₀ W)) = 1
  · refine ⟨((ex m o).1 - (ex m (some (i₀ W))).1, (ex m o).2 - (ex m (some (i₀ W))).2),
      Finset.mem_erase.mpr ⟨fun h ↦ hee ?_, ?_⟩, ?_⟩
    · simp only [Prod.mk.injEq] at h
      exact Prod.ext (by omega) (by omega)
    · simp only [Finset.mem_product, Finset.mem_Icc]
      omega
    · rw [zpow_sub₀ hu', zpow_sub₀ hv', zpow_natCast, zpow_natCast, zpow_natCast, zpow_natCast,
        div_mul_div_comm, ← hyv, ← hyv]
      exact hφ1
  · exfalso
    set φ : ℚ := (y o : ℚ) / y (some (i₀ W)) with hφdef
    have hA : ((u ^ (ex m o).1 * v ^ (ex m o).2 : ℤ) : ℚ) =
        φ * ((u ^ (ex m (some (i₀ W))).1 * v ^ (ex m (some (i₀ W))).2 : ℤ) : ℚ) := by
      push_cast
      rw [← hyv, ← hyv, hφdef, div_mul_cancel₀ _ (Units.ne_zero _)]
    have hdvd := Int.dvd_num_sub_den (Int.dvd_pow_mul_pow_sub_one hdu hdv _ _)
      (Int.dvd_pow_mul_pow_sub_one hdu hdv _ _) hA
    have hne0 : φ.num - φ.den ≠ 0 := fun h ↦ hφ1 <| by
      rw [← Rat.num_div_den φ, sub_eq_zero.mp h]
      exact div_self (by exact_mod_cast φ.den_nz)
    have hdle : d ≤ |φ.num - φ.den| := Int.le_of_dvd (abs_pos.mpr hne0) ((dvd_abs _ _).mpr hdvd)
    have hBφ : ((|φ.num - φ.den| : ℤ) : ℝ) ≤ B :=
      hB ⟨φ, Set.mem_biUnion hWT hφ, rfl⟩
    have hHε : H ^ ε ≤ max B 1 :=
      hdH.trans ((Int.cast_le.mpr hdle).trans (hBφ.trans (le_max_left _ _)))
    have : H ≤ max B 1 ^ ε⁻¹ := by
      rw [← Real.rpow_rpow_inv hH0.le hε.ne']
      exact Real.rpow_le_rpow (Real.rpow_nonneg hH0.le _) hHε (inv_nonneg.mpr hε.le)
    exact absurd (hHR.trans_le' (le_max_right _ _)) (not_lt.mpr this)

end Int

namespace Int

/-- **Only finitely many of the pairs are multiplicatively independent**: the Corvaja–Zannier
bound read as a finiteness statement. -/
theorem finite_setOf_rpow_le_gcd_sub_one (P : Finset ℕ) {ε : ℝ} (hε : 0 < ε) :
    {p : ℤ × ℤ | p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1.natAbs.primeFactors ⊆ P ∧
      p.2.natAbs.primeFactors ⊆ P ∧
      ((max |p.1| |p.2| : ℤ) : ℝ) ^ ε ≤ (Int.gcd (p.1 - 1) (p.2 - 1) : ℝ) ∧
      ∀ a b : ℤ, (a, b) ≠ (0, 0) → (p.1 : ℚ) ^ a * (p.2 : ℚ) ^ b ≠ 1}.Finite := by
  obtain ⟨R, E, hE0, h⟩ := exists_forall_of_rpow_le_gcd_sub_one P hε
  refine ((Set.finite_Icc (-R) R).prod (Set.finite_Icc (-R) R)).subset ?_
  rintro ⟨u, v⟩ ⟨hu, hv, huP, hvP, hg, hind⟩
  rcases h u v hu hv huP hvP hg with hR | ⟨e, he, heq⟩
  · exact ⟨abs_le.mp ((le_max_left _ _).trans hR), abs_le.mp ((le_max_right _ _).trans hR)⟩
  · exact absurd heq (hind e.1 e.2 fun h0 ↦ hE0 (by rw [← h0]; exact he))

end Int

namespace Nat

/-- **Two multiplicatively dependent integers `≥ 2` have a common power**: if
`x ^ e * y ^ f = 1` with `(e, f) ≠ (0, 0)`, then `x ^ p = y ^ q` with `p, q ≥ 1`. -/
theorem exists_pow_eq_pow_of_zpow_mul_zpow_eq_one {x y : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y)
    {e f : ℤ} (hef : (e, f) ≠ (0, 0)) (h : (x : ℚ) ^ e * (y : ℚ) ^ f = 1) :
    ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ x ^ p = y ^ q := by
  have hx1 : (1 : ℝ) < x := by exact_mod_cast hx
  have hy1 : (1 : ℝ) < y := by exact_mod_cast hy
  have hx0 : (0 : ℝ) < x := zero_lt_one.trans hx1
  have hy0 : (0 : ℝ) < y := zero_lt_one.trans hy1
  have hR : (x : ℝ) ^ e * (y : ℝ) ^ f = 1 := by
    have := congrArg (fun q : ℚ ↦ (q : ℝ)) h
    push_cast at this
    exact this
  have hlx := Real.log_pos hx1
  have hly := Real.log_pos hy1
  have hlog : e * Real.log x + f * Real.log y = 0 := by
    have := congrArg Real.log hR
    rwa [Real.log_mul (zpow_ne_zero _ hx0.ne') (zpow_ne_zero _ hy0.ne'), Real.log_zpow,
      Real.log_zpow, Real.log_one] at this
  have he : e ≠ 0 := by
    rintro rfl
    have hf : f = 0 := by
      have h0 : (f : ℝ) * Real.log y = 0 := by simpa using hlog
      rcases _root_.mul_eq_zero.mp h0 with h | h
      · exact_mod_cast h
      · exact absurd h hly.ne'
    exact hef (by rw [hf])
  have hf : f ≠ 0 := by
    rintro rfl
    have he' : e = 0 := by
      have h0 : (e : ℝ) * Real.log x = 0 := by simpa using hlog
      rcases _root_.mul_eq_zero.mp h0 with h | h
      · exact_mod_cast h
      · exact absurd h hlx.ne'
    exact hef (by rw [he'])
  have key : (e : ℝ) * Real.log x = -((f : ℝ) * Real.log y) := by linarith
  have habs : (e.natAbs : ℝ) * Real.log x = (f.natAbs : ℝ) * Real.log y := by
    rw [Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs]
    calc |(e : ℝ)| * Real.log x = |(e : ℝ) * Real.log x| := by rw [abs_mul, abs_of_pos hlx]
      _ = |(f : ℝ) * Real.log y| := by rw [key, abs_neg]
      _ = |(f : ℝ)| * Real.log y := by rw [abs_mul, abs_of_pos hly]
  refine ⟨e.natAbs, f.natAbs, Int.natAbs_pos.mpr he, Int.natAbs_pos.mpr hf, ?_⟩
  have : ((x ^ e.natAbs : ℕ) : ℝ) = ((y ^ f.natAbs : ℕ) : ℝ) := by
    push_cast
    rw [← Real.exp_log (pow_pos hx0 _), ← Real.exp_log (pow_pos hy0 _), Real.log_pow,
      Real.log_pow, habs]
  exact_mod_cast this

/-- **Bugeaud–Corvaja–Zannier** (*Math. Z.* 2003). For multiplicatively independent integers
`a, b ≥ 2` and `ε > 0`, `gcd (a ^ n − 1) (b ^ n − 1) < exp (ε n)` for all but finitely many `n`.
The case `u = a ^ n`, `v = b ^ n` of the Corvaja–Zannier bound. -/
theorem finite_setOf_exp_le_gcd_pow_sub_one {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hab : ∀ e f : ℤ, (e, f) ≠ (0, 0) → (a : ℚ) ^ e * (b : ℚ) ^ f ≠ 1) {ε : ℝ} (hε : 0 < ε) :
    {n : ℕ | Real.exp (ε * n) ≤ Nat.gcd (a ^ n - 1) (b ^ n - 1)}.Finite := by
  set L := Real.log (max a b : ℕ)
  have hM1 : (1 : ℝ) < (max a b : ℕ) := by
    exact_mod_cast lt_of_lt_of_le one_lt_two (le_max_of_le_left ha)
  have hL : 0 < L := Real.log_pos hM1
  obtain ⟨R, E, hE0, h⟩ :=
    Int.exists_forall_of_rpow_le_gcd_sub_one (a * b).primeFactors (ε := ε / L)
      (_root_.div_pos hε hL)
  refine (Set.finite_Iic R.toNat).subset fun n hn ↦ ?_
  change Real.exp (ε * n) ≤ Nat.gcd (a ^ n - 1) (b ^ n - 1) at hn
  simp only [Set.mem_Iic]
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · exact Nat.zero_le _
  have hab0 : a * b ≠ 0 := by positivity
  have hPa : ((a ^ n : ℕ) : ℤ).natAbs.primeFactors ⊆ (a * b).primeFactors := by
    rw [Int.natAbs_natCast, Nat.primeFactors_pow _ hn0.ne']
    exact Nat.primeFactors_mono (dvd_mul_right a b) hab0
  have hPb : ((b ^ n : ℕ) : ℤ).natAbs.primeFactors ⊆ (a * b).primeFactors := by
    rw [Int.natAbs_natCast, Nat.primeFactors_pow _ hn0.ne']
    exact Nat.primeFactors_mono (dvd_mul_left b a) hab0
  have hmax : max |((a ^ n : ℕ) : ℤ)| |((b ^ n : ℕ) : ℤ)| ≤ ((max a b ^ n : ℕ) : ℤ) := by
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    exact_mod_cast max_le (Nat.pow_le_pow_left (le_max_left a b) n)
      (Nat.pow_le_pow_left (le_max_right a b) n)
  have hgcd : Int.gcd (((a ^ n : ℕ) : ℤ) - 1) (((b ^ n : ℕ) : ℤ) - 1) =
      Nat.gcd (a ^ n - 1) (b ^ n - 1) := by
    rw [← Nat.cast_one, ← Nat.cast_sub (Nat.one_le_pow _ _ (by omega)),
      ← Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Int.gcd_natCast_natCast]
  have hrpow : (((max |((a ^ n : ℕ) : ℤ)| |((b ^ n : ℕ) : ℤ)| : ℤ)) : ℝ) ^ (ε / L) ≤
      Real.exp (ε * n) := by
    have hM0 : (0 : ℝ) < ((max a b ^ n : ℕ) : ℝ) := by positivity
    calc (((max |((a ^ n : ℕ) : ℤ)| |((b ^ n : ℕ) : ℤ)| : ℤ)) : ℝ) ^ (ε / L)
        ≤ ((max a b ^ n : ℕ) : ℝ) ^ (ε / L) :=
          Real.rpow_le_rpow (by positivity) (by exact_mod_cast hmax)
            (_root_.div_pos hε hL).le
      _ = Real.exp (ε * n) := by
          rw [Real.rpow_def_of_pos hM0, Nat.cast_pow, Real.log_pow]
          congr 1
          field_simp
          rfl
  rcases h _ _ (by positivity) (by positivity) hPa hPb (hrpow.trans (by rw [hgcd]; exact hn))
    with hR | ⟨e, he, heq⟩
  · have h1 : ((a ^ n : ℕ) : ℤ) ≤ R := (le_abs_self _).trans ((le_max_left _ _).trans hR)
    have h2 : n < a ^ n := Nat.lt_pow_self (by omega)
    omega
  · exfalso
    refine hab e.1 e.2 (fun h0 ↦ hE0 (by rw [← h0]; exact he)) ?_
    have : ((a : ℚ) ^ e.1 * (b : ℚ) ^ e.2) ^ n = 1 := by
      rw [mul_pow, ← zpow_natCast, ← zpow_natCast (_ ^ e.2), ← zpow_mul, ← zpow_mul, mul_comm e.1,
        mul_comm e.2, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, ← heq]
      push_cast
      rfl
    exact (pow_eq_one_iff_of_nonneg (by positivity) hn0.ne').mp this

/-- **Corvaja–Zannier** (*Proc. Amer. Math. Soc.* 2003): the greatest prime factor of
`(a b + 1)(a c + 1)` tends to infinity with `a`, for `a > b > c ≥ 1`. Stated as: for every finite
set `P`, only finitely many `a` have some such `b, c` with all prime factors of
`(a b + 1)(a c + 1)` in `P`. -/
theorem finite_setOf_primeFactors_subset (P : Finset ℕ) :
    {a : ℕ | ∃ b c : ℕ, 1 ≤ c ∧ c < b ∧ b < a ∧
      ((a * b + 1) * (a * c + 1)).primeFactors ⊆ P}.Finite := by
  obtain ⟨R, E, hE0, h⟩ := Int.exists_forall_of_rpow_le_gcd_sub_one P (ε := 1 / 2) (by norm_num)
  refine (Set.finite_Iic R.toNat).subset ?_
  rintro a ⟨b, c, hc, hcb, hba, hP⟩
  simp only [Set.mem_Iic]
  have hu0 : a * b + 1 ≠ 0 := by omega
  have hv0 : a * c + 1 ≠ 0 := by omega
  rw [Nat.primeFactors_mul hu0 hv0] at hP
  have hcb' : a * c < a * b := Nat.mul_lt_mul_of_pos_left hcb (by omega)
  have hmax : max |((a * b + 1 : ℕ) : ℤ)| |((a * c + 1 : ℕ) : ℤ)| = ((a * b + 1 : ℕ) : ℤ) := by
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    exact max_eq_left (by exact_mod_cast (by omega : a * c + 1 ≤ a * b + 1))
  have hgcd : a ≤ Int.gcd (((a * b + 1 : ℕ) : ℤ) - 1) (((a * c + 1 : ℕ) : ℤ) - 1) := by
    rw [show ((a * b + 1 : ℕ) : ℤ) - 1 = ((a * b : ℕ) : ℤ) by push_cast; ring,
      show ((a * c + 1 : ℕ) : ℤ) - 1 = ((a * c : ℕ) : ℤ) by push_cast; ring,
      Int.gcd_natCast_natCast]
    exact Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (Nat.mul_pos (by omega) (by omega)))
      (Nat.dvd_gcd (dvd_mul_right a b) (dvd_mul_right a c))
  have hsq : (((a * b + 1 : ℕ) : ℤ) : ℝ) ≤ (a : ℝ) ^ 2 := by
    have : a * b + 1 ≤ a ^ 2 := by nlinarith
    exact_mod_cast this
  rcases h (a * b + 1 : ℕ) (a * c + 1 : ℕ) (by exact_mod_cast hu0) (by exact_mod_cast hv0)
      (by rw [Int.natAbs_natCast]; exact Finset.subset_union_left.trans hP)
      (by rw [Int.natAbs_natCast]; exact Finset.subset_union_right.trans hP) (by
        rw [hmax]
        calc (((a * b + 1 : ℕ) : ℤ) : ℝ) ^ (1 / 2 : ℝ) ≤ ((a : ℝ) ^ 2) ^ (1 / 2 : ℝ) :=
              Real.rpow_le_rpow (by positivity) hsq (by norm_num)
          _ = a := by rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
          _ ≤ _ := by exact_mod_cast hgcd) with hR | ⟨e, he, heq⟩
  · rw [hmax] at hR
    push_cast at hR
    have : (a : ℤ) ≤ a * b + 1 := by nlinarith
    omega
  · exfalso
    have he0 : (e.1, e.2) ≠ (0, 0) := fun h0 ↦ hE0 (by rw [← h0]; exact he)
    obtain ⟨p, q, hp, hq, hpq⟩ := exists_pow_eq_pow_of_zpow_mul_zpow_eq_one
      (x := a * b + 1) (y := a * c + 1) (by nlinarith) (by nlinarith) he0 (by simpa using heq)
    obtain ⟨t, htu, htv⟩ := Nat.exists_eq_pow_of_pow_eq_pow (Or.inl hp.ne') hpq
    set g := Nat.gcd p q
    have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ hp
    have hp' : 0 < p / g := Nat.div_pos (Nat.le_of_dvd hp (Nat.gcd_dvd_left p q)) hg0
    have hcop : Nat.gcd (q / g) (p / g) = 1 := (Nat.coprime_div_gcd_div_gcd hg0).symm
    have hac : 1 ≤ a * c := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    have ht : 2 ≤ t := by
      rcases Nat.lt_or_ge t 2 with h | h
      · interval_cases t
        · rw [zero_pow hp'.ne'] at htv; omega
        · rw [one_pow] at htv; omega
      · exact h
    have hlt : p / g < q / g :=
      (pow_lt_pow_iff_right₀ (by omega : 1 < t)).mp
        (show t ^ (p / g) < t ^ (q / g) by rw [← htv, ← htu]; omega)
    have hlt2 : q / g < 2 * (p / g) := by
      refine (pow_lt_pow_iff_right₀ (by omega : 1 < t)).mp ?_
      rw [pow_mul', ← htv, ← htu]
      have h1 : a * b < a * a := Nat.mul_lt_mul_of_pos_left hba (by omega)
      have h2 : a ≤ a * c := Nat.le_mul_of_pos_right _ hc
      nlinarith
    have h1 : a ∣ t ^ (q / g) - 1 := by rw [← htu, Nat.add_sub_cancel]; exact dvd_mul_right a b
    have h2 : a ∣ t ^ (p / g) - 1 := by rw [← htv, Nat.add_sub_cancel]; exact dvd_mul_right a c
    have h3 : a ∣ t - 1 := by
      have := Nat.dvd_gcd h1 h2
      rwa [Nat.pow_sub_one_gcd_pow_sub_one, hcop, pow_one] at this
    have hat : a ≤ t - 1 := Nat.le_of_dvd (by omega) h3
    have hsq' : t ^ 2 ≤ t ^ (p / g) := Nat.pow_le_pow_right (by omega) (by omega)
    have : (a + 1) ^ 2 ≤ t ^ 2 := Nat.pow_le_pow_left (by omega) 2
    nlinarith

end Nat

/-! ### Acceptance criteria -/

section Tests

/-- `2` and `3` are multiplicatively independent: `2 ^ e * 3 ^ f = 1` only for `e = f = 0`. -/
private theorem two_three_independent :
    ∀ e f : ℤ, (e, f) ≠ (0, 0) → (2 : ℚ) ^ e * (3 : ℚ) ^ f ≠ 1 := by
  intro e f hef h
  have h2 := congrArg (padicValRat 2) h
  have h3 := congrArg (padicValRat 3) h
  rw [padicValRat.mul (zpow_ne_zero _ two_ne_zero) (zpow_ne_zero _ three_ne_zero),
    padicValRat.zpow, padicValRat.zpow, padicValRat.one] at h2 h3
  have a22 : padicValRat 2 (2 : ℚ) = 1 := by exact_mod_cast padicValRat.self (p := 2) one_lt_two
  have a33 : padicValRat 3 (3 : ℚ) = 1 := by
    exact_mod_cast padicValRat.self (p := 3) (by norm_num)
  have a23 : padicValRat 2 (3 : ℚ) = 0 := by
    rw [show (3 : ℚ) = ((3 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]
    simp [padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3)]
  have a32 : padicValRat 3 (2 : ℚ) = 0 := by
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]
    simp [padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2)]
  rw [a22, a23] at h2
  rw [a32, a33] at h3
  have he : e = 0 := by linarith
  have hf : f = 0 := by linarith
  exact hef (by rw [he, hf])

/-- Acceptance: `gcd (2 ^ n − 1) (3 ^ n − 1) < exp (n / 100)` for all but finitely many `n`. -/
example : {n : ℕ | Real.exp (1 / 100 * n) ≤ Nat.gcd (2 ^ n - 1) (3 ^ n - 1)}.Finite :=
  Nat.finite_setOf_exp_le_gcd_pow_sub_one le_rfl (by norm_num) two_three_independent
    (by norm_num)

/-- Acceptance: the greatest prime factor of `(a b + 1)(a c + 1)` exceeds `7` for all large `a`. -/
example : {a : ℕ | ∃ b c : ℕ, 1 ≤ c ∧ c < b ∧ b < a ∧
    ((a * b + 1) * (a * c + 1)).primeFactors ⊆ {2, 3, 5, 7}}.Finite :=
  Nat.finite_setOf_primeFactors_subset _

/-- Rejection: the curves are load-bearing. The pairs `(2 ^ k, 2 ^ k)`, on `u * v⁻¹ = 1`, all have
`gcd (u − 1) (v − 1) = 2 ^ k − 1 ≥ (2 ^ k) ^ (1/2)` for `k ≥ 2`, and there are infinitely many. -/
example : {p : ℤ × ℤ | p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1.natAbs.primeFactors ⊆ {2} ∧
    p.2.natAbs.primeFactors ⊆ {2} ∧
    ((max |p.1| |p.2| : ℤ) : ℝ) ^ (1 / 2 : ℝ) ≤ (Int.gcd (p.1 - 1) (p.2 - 1) : ℝ)}.Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ ↦ ((2 : ℤ) ^ (k + 2), (2 : ℤ) ^ (k + 2)))
    (fun k l h ↦ by
      have := congrArg Prod.fst h
      simp only at this
      exact Nat.succ_injective (Nat.succ_injective
        (Nat.pow_right_injective le_rfl (by exact_mod_cast this)))) fun k ↦ ?_
  have hpf : ((2 : ℤ) ^ (k + 2)).natAbs.primeFactors ⊆ {2} := by
    rw [Int.natAbs_pow, show Int.natAbs 2 = 2 from rfl,
      Nat.primeFactors_prime_pow (by omega) Nat.prime_two]
  refine ⟨by positivity, by positivity, hpf, hpf, ?_⟩
  simp only [max_self, Int.gcd_self]
  have hx : (4 : ℝ) ≤ (2 : ℝ) ^ (k + 2) := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 2) := pow_le_pow_right₀ one_le_two (by omega)
  have habs : ((|(2 : ℤ) ^ (k + 2)| : ℤ) : ℝ) = (2 : ℝ) ^ (k + 2) := by
    rw [abs_of_pos (by positivity)]
    push_cast
    rfl
  have hna : (((2 : ℤ) ^ (k + 2) - 1).natAbs : ℝ) = (2 : ℝ) ^ (k + 2) - 1 := by
    rw [Nat.cast_natAbs, abs_of_pos (by
      have : (1 : ℤ) < 2 ^ (k + 2) := one_lt_pow₀ (by norm_num) (by omega)
      omega)]
    push_cast
    rfl
  rw [habs, hna, ← Real.sqrt_eq_rpow, Real.sqrt_le_left (by linarith)]
  nlinarith

/-- Rejection: `c < b` is load-bearing. With `b = c = 1` and `a = 2 ^ (k + 2) − 1`, the product
`(a b + 1)(a c + 1) = 4 ^ (k + 2)` has no prime factor but `2`, for infinitely many `a`. -/
example : {a : ℕ | ∃ b c : ℕ, 1 ≤ c ∧ c ≤ b ∧ b < a ∧
    ((a * b + 1) * (a * c + 1)).primeFactors ⊆ {2}}.Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ ↦ 2 ^ (k + 2) - 1)
    (fun k l h ↦ by
      have h1 : 1 ≤ 2 ^ (k + 2) := Nat.one_le_two_pow
      have h2 : 1 ≤ 2 ^ (l + 2) := Nat.one_le_two_pow
      have : 2 ^ (k + 2) = 2 ^ (l + 2) := by simp only at h; omega
      exact Nat.succ_injective (Nat.succ_injective (Nat.pow_right_injective le_rfl this)))
    fun k ↦ ⟨1, 1, le_rfl, le_rfl, ?_, ?_⟩
  · have : 4 ≤ 2 ^ (k + 2) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · have h1 : 1 ≤ 2 ^ (k + 2) := Nat.one_le_two_pow
    have : (2 ^ (k + 2) - 1) * 1 + 1 = 2 ^ (k + 2) := by omega
    rw [this, ← pow_add, Nat.primeFactors_prime_pow (by omega) Nat.prime_two]

end Tests
