/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic

-- Used only inside proofs.
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# Localizing a unique factorization domain at a prime element

Let `A` be a unique factorization domain and `p ∈ A` a prime element. The localization of `A`
at the prime ideal `(p)` is a discrete valuation ring
(`IsLocalization.AtPrime.isDiscreteValuationRing_of_prime`): every nonzero element is `p ^ n`
times a unit.
-/

@[expose] public section

namespace IsLocalization.AtPrime

variable {A : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
  {P : Ideal A} [P.IsPrime] {p : A} (hp : Prime p) (hP : P = Ideal.span {p})
  (S : Type*) [CommRing S] [IsDomain S] [Algebra A S]
  [IsLocalization.AtPrime S P]

include hP in
omit [IsDomain A] [UniqueFactorizationMonoid A] [IsDomain S] in
theorem maximalIdeal_eq_span [IsLocalRing S] :
    IsLocalRing.maximalIdeal S = Ideal.span {algebraMap A S p} := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P S, hP, Ideal.map_span, Set.image_singleton]

include hp hP in
omit [UniqueFactorizationMonoid A] [IsDomain S] in
/-- `p ^ n ∣ g` can be tested in the localization at `(p)`. -/
theorem algebraMap_mem_span_pow_iff (g : A) (n : ℕ) :
    algebraMap A S g ∈ Ideal.span {algebraMap A S p ^ n} ↔ p ^ n ∣ g := by
  subst hP
  refine ⟨fun h ↦ ?_, fun ⟨c, hc⟩ ↦ Ideal.mem_span_singleton.mpr ⟨algebraMap A S c, by
    rw [hc, map_mul, map_pow]⟩⟩
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp h
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Ideal.span {p}).primeCompl y
  have h' : algebraMap A S (g * s) = algebraMap A S (p ^ n * a) := by
    rw [map_mul, hy, map_mul, map_pow, mul_assoc, IsLocalization.mk'_spec]
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (Ideal.span {p}).primeCompl S).mp h'
  have hcs : ¬p ∣ c * s := by
    have hc' : ¬p ∣ (c : A) := fun h ↦ c.2 (Ideal.mem_span_singleton.mpr h)
    have hs' : ¬p ∣ (s : A) := fun h ↦ s.2 (Ideal.mem_span_singleton.mpr h)
    exact fun h ↦ (hp.dvd_or_dvd h).elim hc' hs'
  refine hp.pow_dvd_of_dvd_mul_left n hcs ⟨c * a, ?_⟩
  linear_combination hc

include hp hP in
/-- **The localization of a unique factorization domain at a prime element is a discrete
valuation ring.** -/
theorem isDiscreteValuationRing_of_prime : IsDiscreteValuationRing S := by
  subst hP
  have := IsLocalization.AtPrime.isLocalRing S (Ideal.span {p})
  have hmax : IsLocalRing.maximalIdeal S = Ideal.span {algebraMap A S p} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {p}) S, Ideal.map_span,
      Set.image_singleton]
  have hp0 : algebraMap A S p ≠ 0 :=
    (IsLocalization.injective S (Ideal.span {p}).primeCompl_le_nonZeroDivisors).ne_iff'
      (map_zero _) |>.mpr hp.ne_zero
  have hprime : Prime (algebraMap A S p) :=
    (Ideal.span_singleton_prime hp0).mp (hmax ▸ (IsLocalRing.maximalIdeal.isMaximal S).isPrime)
  refine .ofHasUnitMulPowIrreducibleFactorization ⟨_, hprime.irreducible, fun {x} hx ↦ ?_⟩
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Ideal.span {p}).primeCompl x
  have ha : a ≠ 0 := by rintro rfl; simp at hx
  obtain ⟨n, c, hc, rfl⟩ := WfDvdMonoid.max_power_factor ha hp.irreducible
  have hcS : IsUnit (algebraMap A S c) := by
    refine (IsLocalization.AtPrime.isUnit_to_map_iff S (Ideal.span {p}) c).mpr ?_
    change c ∉ Ideal.span {p}
    rwa [Ideal.mem_span_singleton]
  refine ⟨n, hcS.unit * (IsLocalization.map_units S s).unit⁻¹, ?_⟩
  symm
  rw [IsLocalization.mk'_eq_iff_eq_mul, Units.val_mul, IsUnit.unit_spec, map_mul, map_pow,
    mul_assoc, mul_assoc, IsUnit.val_inv_mul, mul_one]

end IsLocalization.AtPrime
