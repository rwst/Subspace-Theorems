/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.PlacesOverFinite
public import Mathlib.NumberTheory.Ostrowski
public import Mathlib.NumberTheory.Height.NumberField

/-!
# The places of `ℚ`, named

Layer 3.2 states Roth's theorem for a number field, with the places of `K` carried as
`NumberField.InfinitePlace K` and `NumberField.FinitePlace K`. The classical forms of Layer 3.3
are statements about `|·|` and `padicNorm p` on `ℚ`. This file is the dictionary between the two:
every finite place of `ℚ` **is** a `p`-adic absolute value on the nose, and conversely.

## Main results

* `Rat.exists_prime_padic_eq` and `Rat.exists_finitePlace_val_eq_padic`: the two halves of the
  dictionary.
* `Rat.finitePlace`: the finite place of `ℚ` at a prime, with `Rat.finitePlace_val`,
  `Rat.finitePlace_apply` and `Rat.finitePlace_injective`.
* `Rat.min_one_padicNorm` and `Rat.max_one_padicNorm_inv`: the two local factors of Roth's
  theorem at a finite place of `ℚ`, read off the numerator and the denominator. These are what
  turn the product of Layer 3.2 into Ridout's `∏ |p|_ℓ ∏ |q|_ℓ`.
* `Rat.infinitePlace_val_ne_padic`: the infinite place is not one of them.

## Implementation notes

⚠ **The exponent is the whole difficulty.** Ostrowski's theorem — Mathlib's
`Rat.AbsoluteValue.equiv_padic_of_bounded` — gives only that a finite place is *equivalent* to
some `padic p`, that is, a positive real power of it. A power `≠ 1` would be fatal downstream: a
product `∏ min 1 (v x) ^ t v` is not `∏ min 1 (v x)`, and Ridout's exponent `2 + ε` would become
`(2 + ε) / max t`. The exponent is pinned to `1` here by the height of `p⁻¹`: the multiplicative
height of `p⁻¹` is `p`, its infinite part is `1`, and — by Ostrowski again, applied to *every*
finite place at once — the only finite place contributing to the finite part is the one over `p`.
So that one contributes exactly `p`, and the exponent is `1`.

⚠ **Both halves are needed, and neither implies the other cheaply.** The forward half above says
a finite place is a `padic p`; the converse says every `padic p` is a finite place, and it goes
through Layer 0.1's `AbsoluteValue.exists_heightOneSpectrum_rpow_eq` — Ostrowski for a number
field — followed by the forward half to pin its prime and its exponent.

⚠ **`Fact p.Prime` for `p : Nat.Primes` is an instance here.** `padicNorm` is defined for every
natural number, but every lemma about it needs the `Fact`; indexing the sets of primes of
Ridout's theorem by `Nat.Primes` is what makes `∏ ℓ ∈ S, padicNorm ℓ x` state without a
side-condition on every term.

This is part of Layer 3.3 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open NumberField Height

namespace Rat

/-- Ostrowski at a finite place of `ℚ`. -/
theorem exists_prime_rpow_padic_eq (v : FinitePlace ℚ) :
    ∃ p : ℕ, ∃ _ : Fact p.Prime, ∃ c : ℝ, 0 < c ∧ ∀ x : ℚ, v x ^ c = AbsoluteValue.padic p x := by
  have hbdd : ∀ n : ℕ, v.1 (n : ℚ) ≤ 1 := fun n ↦ by
    rw [← NumberField.FinitePlace.coe_apply]
    simpa using NumberField.FinitePlace.apply_intCast_le_one v (n : ℤ)
  have hnt : v.1.IsNontrivial := by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.maximalIdeal.ne_bot
    refine ⟨((y : 𝓞 ℚ) : ℚ), ?_, ?_⟩
    · exact_mod_cast fun h ↦ hy0 (by exact_mod_cast h)
    · have h1 : NumberField.FinitePlace.mk v.maximalIdeal ((y : 𝓞 ℚ) : ℚ) < 1 :=
        (NumberField.FinitePlace.mk_lt_one_iff_mem v.maximalIdeal y).mpr hy
      rw [NumberField.FinitePlace.mk_maximalIdeal] at h1
      exact ne_of_lt h1
  obtain ⟨p, ⟨hp, heq⟩, -⟩ := AbsoluteValue.equiv_padic_of_bounded hnt hbdd
  obtain ⟨c, hc, hfun⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp heq
  exact ⟨p, hp, c, hc, fun x ↦ congrFun hfun x⟩

/-- Two finite places of a number field that are small on the same elements are equal: a finite
place is determined by the prime it is less than `1` on. -/
theorem _root_.NumberField.FinitePlace.eq_of_lt_one_iff {F : Type*} [Field F] [NumberField F]
    {v w : FinitePlace F} (h : ∀ y : F, v y < 1 ↔ w y < 1) : v = w := by
  refine NumberField.FinitePlace.maximalIdeal_injective ?_
  refine IsDedekindDomain.HeightOneSpectrum.ext (SetLike.ext fun y ↦ ?_)
  rw [← NumberField.FinitePlace.mk_lt_one_iff_mem, ← NumberField.FinitePlace.mk_lt_one_iff_mem,
    NumberField.FinitePlace.mk_maximalIdeal, NumberField.FinitePlace.mk_maximalIdeal]
  exact h _

/-- The prime of Ostrowski's theorem determines the finite place it came from. -/
theorem finitePlace_eq_of_rpow_padic_eq {v w : FinitePlace ℚ} {p : ℕ} [Fact p.Prime] {c c' : ℝ}
    (hc : 0 < c) (hc' : 0 < c') (hv : ∀ x : ℚ, v x ^ c = AbsoluteValue.padic p x)
    (hw : ∀ x : ℚ, w x ^ c' = AbsoluteValue.padic p x) : v = w := by
  refine NumberField.FinitePlace.eq_of_lt_one_iff fun y ↦ ?_
  have h1 : v y < 1 ↔ AbsoluteValue.padic p y < 1 := by
    rw [← hv y]
    exact (Real.rpow_lt_one_iff' (by positivity) hc).symm
  have h2 : w y < 1 ↔ AbsoluteValue.padic p y < 1 := by
    rw [← hw y]
    exact (Real.rpow_lt_one_iff' (by positivity) hc').symm
  rw [h1, h2]

/-- **Every finite place of `ℚ` is a `p`-adic absolute value, on the nose.** Ostrowski's theorem
gives the equivalence; the exponent is pinned to `1` by the height of `p⁻¹`. -/
theorem exists_prime_padic_eq (v : FinitePlace ℚ) :
    ∃ p : ℕ, ∃ _ : Fact p.Prime, v.1 = AbsoluteValue.padic p := by
  obtain ⟨p, hp, c, hc, hv⟩ := exists_prime_rpow_padic_eq v
  refine ⟨p, hp, ?_⟩
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.two_le
  -- the height of `p⁻¹` is `p`, and only `v` contributes to its finite part
  have hother : ∀ w : FinitePlace ℚ, w ≠ v → max (w ((p : ℚ)⁻¹)) 1 = 1 := by
    intro w hwv
    obtain ⟨q, hq, c', hc', hw⟩ := exists_prime_rpow_padic_eq w
    have hqp : q ≠ p := by
      rintro rfl
      exact hwv (finitePlace_eq_of_rpow_padic_eq hc' hc hw hv)
    have hwp : w ((p : ℚ)) = 1 := by
      have h1 : w ((p : ℚ)) ^ c' = 1 := by
        rw [hw]
        have : padicNorm q (p : ℚ) = 1 := by
          rw [show ((p : ℚ)) = ((p : ℕ) : ℚ) by norm_num, padicNorm.nat_eq_one_iff]
          exact fun hdvd ↦ hqp ((Nat.prime_dvd_prime_iff_eq hq.out hp.out).mp hdvd)
        simp [AbsoluteValue.padic_eq_padicNorm, this]
      have h0 : 0 ≤ w ((p : ℚ)) := by positivity
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact absurd h1 (ne_of_lt (Real.rpow_lt_one h0 hlt hc'))
      · exact absurd h1 (ne_of_gt (Real.one_lt_rpow hgt hc'))
    have hinv : w ((p : ℚ)⁻¹) = 1 := by
      rw [NumberField.FinitePlace.coe_apply, map_inv₀, ← NumberField.FinitePlace.coe_apply, hwp,
        inv_one]
    rw [hinv, max_self]
  have hheight : mulHeight₁ ((p : ℚ)⁻¹) = (p : ℝ) := by
    rw [Height.mulHeight₁_inv, show ((p : ℚ)) = ((p : ℕ) : ℚ) by norm_num,
      Rat.mulHeight₁_natCast]
  rw [NumberField.mulHeight₁_eq] at hheight
  have harch : (∏ u : InfinitePlace ℚ, max (u ((p : ℚ)⁻¹)) 1 ^ u.mult) = 1 := by
    refine Finset.prod_eq_one fun u _ ↦ ?_
    have hone : max (u ((p : ℚ)⁻¹)) 1 = 1 := by
      rw [Rat.infinitePlace_apply, max_eq_right]
      have hp1 : (1 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp.out.one_lt.le
      have hq1 : |((p : ℚ))⁻¹| ≤ 1 := by
        rw [abs_of_nonneg (by positivity)]
        rw [inv_le_one₀ (by linarith)]
        exact hp1
      exact_mod_cast hq1
    rw [hone, one_pow]
  rw [harch, one_mul, finprod_eq_single _ v hother] at hheight
  have hvp : v ((p : ℚ)⁻¹) = (p : ℝ) := by
    rcases max_cases (v ((p : ℚ)⁻¹)) 1 with ⟨h, -⟩ | ⟨h, hlt⟩
    · rw [← h]; exact hheight
    · rw [h] at hheight; linarith
  have hvp' : v ((p : ℚ)) = ((p : ℝ))⁻¹ := by
    have h1 : v ((p : ℚ)) * v ((p : ℚ)⁻¹) = 1 := by
      rw [NumberField.FinitePlace.coe_apply, NumberField.FinitePlace.coe_apply, ← map_mul,
        mul_inv_cancel₀ (show ((p : ℚ)) ≠ 0 by exact_mod_cast hp.out.ne_zero), map_one]
    rw [hvp] at h1
    field_simp at h1 ⊢
    linarith
  have hc1 : c = 1 := by
    have h1 : ((p : ℝ))⁻¹ ^ c = ((p : ℝ))⁻¹ := by
      have := hv ((p : ℚ))
      rw [hvp'] at this
      rw [this, AbsoluteValue.padic_eq_padicNorm,
        show ((p : ℚ)) = ((p : ℕ) : ℚ) by norm_num, padicNorm.padicNorm_p_of_prime]
      push_cast
      ring
    have hne : ((p : ℝ))⁻¹ ≠ 1 := by
      intro h
      rw [inv_eq_one] at h
      linarith
    have h2 : ((p : ℝ))⁻¹ ^ c = ((p : ℝ))⁻¹ ^ (1 : ℝ) := by rw [Real.rpow_one]; exact h1
    exact (Real.rpow_right_inj (by positivity) hne).mp h2
  refine AbsoluteValue.ext fun x ↦ ?_
  have := hv x
  rw [hc1, Real.rpow_one] at this
  rw [← this, NumberField.FinitePlace.coe_apply]

/-- **Every `p`-adic absolute value of `ℚ` is a finite place, on the nose.** The converse of
`Rat.exists_prime_padic_eq`. -/
theorem exists_finitePlace_val_eq_padic (p : ℕ) [Fact p.Prime] :
    ∃ v : FinitePlace ℚ, v.1 = AbsoluteValue.padic p := by
  have hp0 : ((p : ℚ)) ≠ 0 := by exact_mod_cast (Fact.out (p := p.Prime)).ne_zero
  have hna : IsNonarchimedean ((AbsoluteValue.padic p : AbsoluteValue ℚ ℝ) : ℚ → ℝ) := by
    intro x y
    simpa [AbsoluteValue.padic_eq_padicNorm] using
      (show ((padicNorm p (x + y) : ℚ) : ℝ) ≤ ((max (padicNorm p x) (padicNorm p y) : ℚ) : ℝ) by
        exact_mod_cast padicNorm.nonarchimedean (p := p))
  have hle : ∀ y : 𝓞 ℚ, AbsoluteValue.padic p ((y : ℚ)) ≤ 1 := fun y ↦ by
    have hy : ((y : ℚ)) = ((Rat.ringOfIntegersEquiv y : ℤ) : ℚ) :=
      (Rat.ringOfIntegersEquiv_apply_coe y).symm
    rw [hy]
    exact AbsoluteValue.padic_le_one p _
  have hnt : ∃ y : 𝓞 ℚ, y ≠ 0 ∧ AbsoluteValue.padic p ((y : ℚ)) < 1 := by
    refine ⟨Rat.ringOfIntegersEquiv.symm (p : ℤ), ?_, ?_⟩
    · simpa using fun h ↦ (Fact.out (p := p.Prime)).ne_zero (by exact_mod_cast h)
    · rw [Rat.ringOfIntegersEquiv_symm_apply_coe]
      simpa [AbsoluteValue.padic_eq_padicNorm] using
        (show ((padicNorm p ((p : ℤ) : ℚ) : ℚ) : ℝ) < 1 by
          rw [show (((p : ℤ) : ℚ)) = ((p : ℕ) : ℚ) by push_cast; ring]
          exact_mod_cast padicNorm.padicNorm_p_lt_one_of_prime (p := p))
  obtain ⟨P, t, ht, hPt⟩ := AbsoluteValue.exists_heightOneSpectrum_rpow_eq hna hle hnt
  obtain ⟨q, hq, hqv⟩ := exists_prime_padic_eq (NumberField.FinitePlace.mk P)
  have hkey : ∀ x : ℚ, AbsoluteValue.padic p x = AbsoluteValue.padic q x ^ t := fun x ↦ by
    rw [hPt x, ← hqv, NumberField.FinitePlace.coe_apply]
  have hqp : q = p := by
    have h1 : AbsoluteValue.padic q ((p : ℚ)) ^ t = ((p : ℝ))⁻¹ := by
      rw [← hkey, AbsoluteValue.padic_eq_padicNorm,
        show ((p : ℚ)) = ((p : ℕ) : ℚ) by norm_num, padicNorm.padicNorm_p_of_prime]
      push_cast
      ring
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Fact.out (p := p.Prime)).two_le
    have hlt : AbsoluteValue.padic q ((p : ℚ)) < 1 := by
      by_contra hcon
      push Not at hcon
      have : (1 : ℝ) ≤ AbsoluteValue.padic q ((p : ℚ)) ^ t := Real.one_le_rpow hcon ht.le
      rw [h1] at this
      rw [le_inv_comm₀ (by norm_num) (by linarith)] at this
      linarith
    rw [AbsoluteValue.padic_eq_padicNorm, show ((p : ℚ)) = ((p : ℕ) : ℚ) by norm_num] at hlt
    have hdvd : q ∣ p := by
      by_contra hcon
      rw [show ((1 : ℝ)) = ((1 : ℚ) : ℝ) by norm_num, Rat.cast_lt] at hlt
      exact absurd ((padicNorm.nat_eq_one_iff (p := q) p).mpr hcon) (ne_of_lt hlt)
    exact (Nat.prime_dvd_prime_iff_eq hq.out (Fact.out (p := p.Prime))).mp hdvd
  subst hqp
  have ht1 : t = 1 := by
    have hp2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Fact.out (p := q.Prime)).two_le
    have h1 : ((q : ℝ))⁻¹ ^ t = ((q : ℝ))⁻¹ ^ (1 : ℝ) := by
      rw [Real.rpow_one]
      have := hkey ((q : ℚ))
      rw [AbsoluteValue.padic_eq_padicNorm, show ((q : ℚ)) = ((q : ℕ) : ℚ) by norm_num,
        padicNorm.padicNorm_p_of_prime] at this
      push_cast at this
      rw [← this]
    have hne : ((q : ℝ))⁻¹ ≠ 1 := by
      intro h
      rw [inv_eq_one] at h
      linarith
    exact (Real.rpow_right_inj (by positivity) hne).mp h1
  subst ht1
  exact ⟨NumberField.FinitePlace.mk P, by simpa using hqv⟩

end Rat

/-- Every prime is prime. -/
instance Nat.Primes.instFactPrime (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

namespace Rat

/-- The finite place of `ℚ` at a prime: the place whose absolute value is `padicNorm p`. -/
noncomputable def finitePlace (p : Nat.Primes) : FinitePlace ℚ :=
  (exists_finitePlace_val_eq_padic (p : ℕ)).choose

@[simp] theorem finitePlace_val (p : Nat.Primes) :
    (finitePlace p).1 = AbsoluteValue.padic (p : ℕ) :=
  (exists_finitePlace_val_eq_padic (p : ℕ)).choose_spec

theorem finitePlace_apply (p : Nat.Primes) (x : ℚ) :
    finitePlace p x = ((padicNorm (p : ℕ) x : ℚ) : ℝ) := by
  rw [NumberField.FinitePlace.coe_apply, finitePlace_val]
  rfl

theorem finitePlace_injective : Function.Injective finitePlace := by
  intro p q hpq
  by_contra hne
  have hpq' : AbsoluteValue.padic (p : ℕ) = AbsoluteValue.padic (q : ℕ) := by
    rw [← finitePlace_val p, ← finitePlace_val q, hpq]
  have h1 : padicNorm (p : ℕ) ((p : ℕ) : ℚ) = padicNorm (q : ℕ) ((p : ℕ) : ℚ) := by
    have h := congrFun (congrArg (fun v : AbsoluteValue ℚ ℝ ↦ (v : ℚ → ℝ)) hpq') ((p : ℕ) : ℚ)
    simp only [AbsoluteValue.padic_eq_padicNorm] at h
    exact_mod_cast h
  rw [padicNorm.padicNorm_p_of_prime,
    (padicNorm.nat_eq_one_iff (p := (q : ℕ)) (p : ℕ)).mpr
      (fun hdvd ↦ hne (Subtype.ext ((Nat.prime_dvd_prime_iff_eq q.2 p.2).mp hdvd).symm))] at h1
  have hp2 : (2 : ℚ) ≤ ((p : ℕ) : ℚ) := by exact_mod_cast p.2.two_le
  rw [inv_eq_one] at h1
  linarith

/-- The infinite place of `ℚ` is not a `p`-adic one: it is `2` at `2`, where every `p`-adic
absolute value is at most `1`. -/
theorem infinitePlace_val_ne_padic (p : Nat.Primes) :
    Rat.infinitePlace.1 ≠ AbsoluteValue.padic (p : ℕ) := by
  intro hcon
  have h1 : Rat.infinitePlace.1 ((p : ℕ) : ℚ) = ((p : ℕ) : ℝ) := by
    rw [← NumberField.InfinitePlace.coe_apply, Rat.infinitePlace_apply,
      abs_of_nonneg (by positivity)]
    push_cast
    ring
  have h2 : AbsoluteValue.padic (p : ℕ) ((p : ℕ) : ℚ) = (((p : ℕ) : ℝ))⁻¹ := by
    rw [AbsoluteValue.padic_eq_padicNorm, padicNorm.padicNorm_p_of_prime]
    push_cast
    ring
  rw [hcon, h2] at h1
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
  have : ((p : ℕ) : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by linarith)]
    linarith
  linarith

/-- The `p`-adic size of a rational number, truncated at `1`, is the `p`-adic size of its
numerator: the numerator and the denominator are coprime, so at most one of them meets `p`. -/
theorem min_one_padicNorm (p : Nat.Primes) (β : ℚ) :
    min 1 (padicNorm (p : ℕ) β) = padicNorm (p : ℕ) β.num := by
  have hden0 : ((β.den : ℚ)) ≠ 0 := by exact_mod_cast β.den_nz
  have hβ : β = ((β.num : ℚ)) / ((β.den : ℚ)) := (Rat.num_div_den β).symm
  by_cases hd : (p : ℕ) ∣ β.den
  · have hnum : ¬ ((p : ℕ) : ℤ) ∣ β.num := by
      intro hcon
      have h1 : (p : ℕ) ∣ β.num.natAbs := Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hcon)
      have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 β.reduced) hd
      exact p.2.ne_one this
    have h1 : padicNorm (p : ℕ) ((β.num : ℚ)) = 1 := (padicNorm.int_eq_one_iff _).mpr hnum
    have h2 : (0 : ℚ) < padicNorm (p : ℕ) ((β.den : ℚ)) :=
      lt_of_le_of_ne (padicNorm.nonneg _) (Ne.symm (padicNorm.nonzero hden0))
    have h3 : padicNorm (p : ℕ) ((β.den : ℚ)) ≤ 1 := padicNorm.of_nat _
    conv_lhs => rw [hβ]
    rw [padicNorm.div, h1]
    refine min_eq_left ?_
    rw [le_div_iff₀ h2]
    linarith
  · have h1 : padicNorm (p : ℕ) ((β.den : ℚ)) = 1 := (padicNorm.nat_eq_one_iff _).mpr hd
    conv_lhs => rw [hβ]
    rw [padicNorm.div, h1, div_one]
    exact min_eq_right (padicNorm.of_int _)

/-- Dually, the truncated inverse is the `p`-adic size of the denominator. -/
theorem max_one_padicNorm_inv (p : Nat.Primes) (β : ℚ) :
    (max 1 (padicNorm (p : ℕ) β))⁻¹ = padicNorm (p : ℕ) β.den := by
  have hden0 : ((β.den : ℚ)) ≠ 0 := by exact_mod_cast β.den_nz
  have hβ : β = ((β.num : ℚ)) / ((β.den : ℚ)) := (Rat.num_div_den β).symm
  by_cases hd : (p : ℕ) ∣ β.den
  · have hnum : ¬ ((p : ℕ) : ℤ) ∣ β.num := by
      intro hcon
      have h1 : (p : ℕ) ∣ β.num.natAbs := Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hcon)
      have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 β.reduced) hd
      exact p.2.ne_one this
    have h1 : padicNorm (p : ℕ) ((β.num : ℚ)) = 1 := (padicNorm.int_eq_one_iff _).mpr hnum
    have h2 : (0 : ℚ) < padicNorm (p : ℕ) ((β.den : ℚ)) :=
      lt_of_le_of_ne (padicNorm.nonneg _) (Ne.symm (padicNorm.nonzero hden0))
    have h3 : padicNorm (p : ℕ) ((β.den : ℚ)) ≤ 1 := padicNorm.of_nat _
    conv_lhs => rw [hβ]
    rw [padicNorm.div, h1]
    rw [max_eq_right (by rw [le_div_iff₀ h2]; linarith), one_div, inv_inv]
  · have h1 : padicNorm (p : ℕ) ((β.den : ℚ)) = 1 := (padicNorm.nat_eq_one_iff _).mpr hd
    conv_lhs => rw [hβ]
    rw [padicNorm.div, h1, div_one, max_eq_left (padicNorm.of_int _), inv_one]

/-- `Rat.min_one_padicNorm`, read in `ℝ`. -/
theorem min_one_padic_apply (p : Nat.Primes) (β : ℚ) :
    min 1 (AbsoluteValue.padic (p : ℕ) β) = ((padicNorm (p : ℕ) β.num : ℚ) : ℝ) := by
  rw [AbsoluteValue.padic_eq_padicNorm, ← min_one_padicNorm p β]
  push_cast
  ring_nf

/-- `Rat.max_one_padicNorm_inv`, read in `ℝ`. -/
theorem max_one_padic_apply_inv (p : Nat.Primes) (β : ℚ) :
    (max 1 (AbsoluteValue.padic (p : ℕ) β))⁻¹ = ((padicNorm (p : ℕ) β.den : ℚ) : ℝ) := by
  rw [AbsoluteValue.padic_eq_padicNorm, ← max_one_padicNorm_inv p β]
  push_cast
  ring_nf

/-! ### Acceptance criteria -/

private theorem padic_two_half : AbsoluteValue.padic 2 (1 / 2 : ℚ) = 2 := by
  rw [AbsoluteValue.padic_eq_padicNorm, padicNorm.div, padicNorm.one,
    show ((2 : ℚ)) = ((2 : ℕ) : ℚ) by norm_num, padicNorm.padicNorm_p_of_prime]
  norm_num

/-- The finite place at `2` is `2` at `1 / 2`: the normalisation is `padicNorm`'s, not its
reciprocal and not a power of it. -/
example (p : Nat.Primes) (hp : (p : ℕ) = 2) : Rat.finitePlace p (1 / 2 : ℚ) = 2 := by
  rw [Rat.finitePlace_apply, hp]
  have h := padic_two_half
  rw [AbsoluteValue.padic_eq_padicNorm] at h
  rw [h]

/-- **The two local factors, at `1 / 2` and the prime `2`.** The truncated size is the
numerator's `padicNorm` and the truncated reciprocal is the denominator's — the identity that
turns the product of Layer 3.2 into Ridout's two products. Neither factor is the whole
`padicNorm`, which is `2`. -/
example : min 1 (AbsoluteValue.padic 2 (1 / 2 : ℚ)) = 1 ∧
    (max 1 (AbsoluteValue.padic 2 (1 / 2 : ℚ)))⁻¹ = 1 / 2 := by
  rw [padic_two_half]
  norm_num

/-- **Rejection test: the infinite place is not a finite one.** Every `p`-adic absolute value is
at most `1` on the integers, and `|2| = 2`. -/
example : ¬ ∃ p : Nat.Primes, Rat.infinitePlace.1 = AbsoluteValue.padic (p : ℕ) := by
  rintro ⟨p, hp⟩
  exact Rat.infinitePlace_val_ne_padic p hp


end Rat

end
