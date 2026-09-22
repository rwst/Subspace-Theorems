/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.IrrationalityExponent
public import DiophantineApproximation.RationalPlaces
public import DiophantineApproximation.RothTheorem

-- Used only inside proofs and in the acceptance criteria.
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber

/-!
# Roth's theorem over `ℚ`, and the irrationality exponent of an algebraic number

**Roth's theorem** (Roth 1955), in the form it is usually quoted: a real algebraic number is
approximable by rationals to order `2` and to no better order. Layer 1.1 defines
`Real.irrationalityExponent` and pins it between `2` — Dirichlet — and the degree of `ξ` —
Liouville; this file closes the gap from above, and the value is `2` whatever the degree.

## Main results

* `Real.finite_setOf_min_one_abs_sub_le`: Roth's theorem over `ℚ` at the real place, with the
  naive height `max |p| q` of `p / q`. This is Layer 3.2 for `K = ℚ`, `F = ℚ⟮ξ⟯` and one place.
* `Real.irrationalityExponent_le_two` and `Real.irrationalityExponent_eq_two`: the exponent.
* `Rat.max_num_den_le_of_div` and `Set.Infinite.of_forall_exists_rat_lt`: the two elementary
  facts the translation needs.

## Implementation notes

⚠ **The naive height, not the denominator, is what Roth's theorem bounds.** Layer 1.1's
`LiouvilleWith` reads the quality of `m / n` against `n`, and Layer 3.2 reads it against
`mulHeight₁`, which over `ℚ` is `max |p| q` on the reduced fraction. The two differ by a bounded
factor once the approximations are good — Layer 1.1's `liouvilleWith_iff_frequently_max` is
exactly that statement — and the bounded factor is absorbed by lowering the exponent, which is
why two exponents `2 < κ' < κ` appear in the proof and not one.

⚠ **Reducing a fraction cannot raise its height**, which is `Rat.max_num_den_le_of_div` and the
step that lets the unreduced `m / n` of `LiouvilleWith` be fed to Roth's theorem.

⚠ **Infinitude is a separating argument, not a counting one.** The approximations produced are
indexed by denominators, and different denominators can name the same rational; that they are
infinitely many follows because they come arbitrarily close to `ξ` and a finite set of rationals
stays a positive distance from an irrational.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Theorem 6.2.3; K. F. Roth, *Rational approximations to algebraic numbers*, Mathematika 2 (1955).

This is part of Layer 3.3 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Height NumberField IntermediateField Filter
open scoped ENNReal NNReal

/-- **Roth's theorem, in the shape it is usually quoted.** For a real algebraic number `ξ` and
`κ > 2` there are only finitely many rationals `β` with `|ξ - β| ≤ H(β) ^ (-κ)`, where
`H(p / q) = max |p| q` is the naive height. -/
theorem Real.finite_setOf_min_one_abs_sub_le {ξ : ℝ} (hξ : IsAlgebraic ℚ ξ) {κ : ℝ} (hκ : 2 < κ) :
    {β : ℚ | min 1 |ξ - (β : ℝ)| ≤ (max β.num.natAbs β.den : ℝ) ^ (-κ)}.Finite := by
  have hint : IsIntegral ℚ ξ := hξ.isIntegral
  have : FiniteDimensional ℚ ℚ⟮ξ⟯ := adjoin.finiteDimensional hint
  have : NumberField ℚ⟮ξ⟯ := {}
  set w : AbsoluteValue ℚ⟮ξ⟯ ℝ := AbsoluteValue.abs.comp (algebraMap ℚ⟮ξ⟯ ℝ).injective with hwdef
  have hwapply : ∀ x : ℚ⟮ξ⟯, w x = |(algebraMap ℚ⟮ξ⟯ ℝ) x| := fun x ↦ rfl
  have hw : w.LiesOver (Rat.infinitePlace.1) := by
    refine ⟨AbsoluteValue.ext fun q ↦ ?_⟩
    rw [AbsoluteValue.under_def]
    simp only [AbsoluteValue.comp_apply]
    rw [hwapply, ← IsScalarTower.algebraMap_apply ℚ ℚ⟮ξ⟯ ℝ,
      ← NumberField.InfinitePlace.coe_apply, Rat.infinitePlace_apply]
    simp
  set a : ℚ⟮ξ⟯ := ⟨ξ, mem_adjoin_simple_self ℚ ξ⟩ with hadef
  have ha : (algebraMap ℚ⟮ξ⟯ ℝ) a = ξ := rfl
  have hroth := finite_setOf_prod_min_one_le (K := ℚ) (F := ℚ⟮ξ⟯) {Rat.infinitePlace} ∅
    (fun _ ↦ w) (fun v hv ↦ by rwa [Finset.mem_singleton.mp hv])
    (fun v hv ↦ absurd hv (Finset.notMem_empty v)) (fun _ ↦ a) hκ
  refine hroth.subset fun β hβ ↦ ?_
  rw [Set.mem_ofPred_eq] at hβ ⊢
  rw [Finset.prod_singleton, Finset.prod_empty, mul_one,
    NumberField.InfinitePlace.IsReal.mult_eq_one Rat.isReal_infinitePlace, pow_one,
    Rat.mulHeight₁_eq_max, Nat.cast_max]
  have hval : w ((algebraMap ℚ ℚ⟮ξ⟯) β - a) = |ξ - (β : ℝ)| := by
    rw [hwapply, map_sub, ha, ← IsScalarTower.algebraMap_apply ℚ ℚ⟮ξ⟯ ℝ, abs_sub_comm]
    simp
  rw [hval]
  exact hβ


/-- Reducing a fraction does not increase its naive height. -/
theorem Rat.max_num_den_le_of_div {m : ℤ} {n : ℕ} (hn : 0 < n) :
    max (((m : ℚ) / (n : ℚ)).num.natAbs) (((m : ℚ) / (n : ℚ)).den) ≤ max m.natAbs n := by
  have hn0 : ((n : ℤ)) ≠ 0 := by exact_mod_cast hn.ne'
  have hdiv : ((m : ℚ) / ((n : ℤ) : ℚ)) = Rat.divInt m (n : ℤ) := (Rat.divInt_eq_div m n).symm
  have hden : (((m : ℚ) / (n : ℚ)).den) ≤ n := by
    have h := Rat.den_dvd m (n : ℤ)
    rw [← hdiv] at h
    push_cast at h ⊢
    have h' : (((m : ℚ) / (n : ℚ)).den) ∣ n := by
      rwa [Int.natCast_dvd_natCast] at h
    exact Nat.le_of_dvd hn h'
  rcases eq_or_ne m 0 with rfl | hm
  · simp only [Int.cast_zero, zero_div, Rat.num_zero, Int.natAbs_zero, Rat.den_zero,
      Int.natAbs_zero]
    exact le_trans (max_le (Nat.zero_le _) hn) (le_max_right _ _)
  · have hnum : (((m : ℚ) / (n : ℚ)).num) ∣ m := by
      have h := Rat.num_dvd m hn0
      rw [← hdiv] at h
      push_cast at h ⊢
      exact h
    have hnum' : (((m : ℚ) / (n : ℚ)).num.natAbs) ≤ m.natAbs :=
      Nat.le_of_dvd (Int.natAbs_pos.mpr hm) (Int.natAbs_dvd_natAbs.mpr hnum)
    exact max_le_max hnum' hden

/-- A set of rationals containing points arbitrarily close to an irrational number is infinite. -/
theorem Set.Infinite.of_forall_exists_rat_lt {ξ : ℝ} (hξ : Irrational ξ) {X : Set ℚ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ β ∈ X, |ξ - (β : ℝ)| < ε) : X.Infinite := by
  intro hfin
  obtain ⟨β₀, hβ₀X, -⟩ := h 1 one_pos
  obtain ⟨b, hbX, hb⟩ := Set.exists_min_image X (fun β ↦ |ξ - (β : ℝ)|) hfin ⟨β₀, hβ₀X⟩
  have hb0 : 0 < |ξ - (b : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr fun hcon ↦ hξ ⟨b, hcon.symm⟩)
  obtain ⟨γ, hγX, hγ⟩ := h _ hb0
  exact absurd (hb γ hγX) (not_le.mpr hγ)

/-- **Roth's theorem: the irrationality exponent of a real algebraic number is at most `2`.** -/
theorem Real.irrationalityExponent_le_two {ξ : ℝ} (halg : IsAlgebraic ℚ ξ) :
    irrationalityExponent ξ ≤ 2 := by
  by_cases hirr : Irrational ξ
  swap
  · rw [irrationalityExponent_eq_one_of_not_irrational hirr]
    norm_num
  rw [irrationalityExponent_le_iff]
  intro pex hpex
  by_contra hcon
  push Not at hcon
  have hp2 : (2 : ℝ) < (pex : ℝ) := by
    have h1 : (2 : ℝ≥0) < pex := by exact_mod_cast hcon
    exact_mod_cast h1
  set κ : ℝ := ((pex : ℝ) + 2) / 2 with hκdef
  set κ' : ℝ := (κ + 2) / 2 with hκ'def
  have hκp : κ < (pex : ℝ) := by rw [hκdef]; linarith
  have hκ2 : 2 < κ := by rw [hκdef]; linarith
  have hκ'2 : 2 < κ' := by rw [hκ'def]; linarith
  have hκ'κ : κ' < κ := by rw [hκ'def]; linarith
  obtain ⟨C, hC⟩ := (liouvilleWith_iff_frequently_max (ξ := ξ) (μ := κ) (by linarith)).1
    (hpex.mono hκp.le)
  set C' : ℝ := max C 1 with hC'def
  have hC'1 : 1 ≤ C' := le_max_right _ _
  have hC'0 : (0 : ℝ) < C' := by linarith
  -- the Roth set is infinite, which contradicts Roth's theorem
  refine absurd (Real.finite_setOf_min_one_abs_sub_le halg hκ'2) ?_
  refine Set.Infinite.of_forall_exists_rat_lt hirr fun ε hε ↦ ?_
  set N₀ : ℝ := max 1 (max (C' ^ (κ - κ')⁻¹) ((C' / ε + 1) ^ κ⁻¹)) with hN₀def
  obtain ⟨n, ⟨hnN, hn1⟩, m, hne, hlt⟩ :=
    (((eventually_ge_atTop ⌈N₀⌉₊).and (eventually_ge_atTop 1)).and_frequently hC).exists
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hnN₀ : N₀ ≤ (n : ℝ) := le_trans (Nat.le_ceil N₀) (by exact_mod_cast hnN)
  set h : ℝ := max |(m : ℝ)| (n : ℝ) with hhdef
  have hhn : (n : ℝ) ≤ h := le_max_right _ _
  have hh0 : (0 : ℝ) < h := lt_of_lt_of_le hn0 hhn
  -- the two size conditions on `n`
  have hstep1 : C' ≤ (n : ℝ) ^ (κ - κ') := by
    calc C' = (C' ^ (κ - κ')⁻¹) ^ (κ - κ') :=
          (Real.rpow_inv_rpow hC'0.le (by linarith)).symm
      _ ≤ (n : ℝ) ^ (κ - κ') := Real.rpow_le_rpow (by positivity)
          (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hnN₀) (by linarith)
  have hstep2 : C' / ε + 1 ≤ (n : ℝ) ^ κ := by
    calc C' / ε + 1 = ((C' / ε + 1) ^ κ⁻¹) ^ κ :=
          (Real.rpow_inv_rpow (by positivity) (by linarith)).symm
      _ ≤ (n : ℝ) ^ κ := Real.rpow_le_rpow (by positivity)
          (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hnN₀) (by linarith)
  -- the rational `β`
  have hhκ : (0 : ℝ) < h ^ κ := Real.rpow_pos_of_pos hh0 κ
  have hcast : ((m : ℝ)) / ((n : ℝ)) = (((m : ℚ) / (n : ℚ) : ℚ) : ℝ) := by push_cast; ring
  have hsmall : |ξ - (((m : ℚ) / (n : ℚ) : ℚ) : ℝ)| < C' / h ^ κ := by
    rw [← hcast]
    refine lt_of_lt_of_le hlt ?_
    have h3 : (0 : ℝ) ≤ (C' - C) / h ^ κ := div_nonneg (by simp [hC'def]) hhκ.le
    have h2 : C' / h ^ κ - C / h ^ κ = (C' - C) / h ^ κ := by ring
    linarith
  refine ⟨(m : ℚ) / (n : ℚ), ?_, ?_⟩
  · rw [Set.mem_ofPred_eq, ← Nat.cast_max]
    set H : ℝ := ((max (((m : ℚ) / (n : ℚ)).num.natAbs) (((m : ℚ) / (n : ℚ)).den) : ℕ) : ℝ)
      with hHdef
    have hHle : H ≤ h := by
      have hnat := Rat.max_num_den_le_of_div (m := m) (n := n) hn1
      have hmax : ((max m.natAbs n : ℕ) : ℝ) ≤ h := by
        rw [hhdef, Nat.cast_max]
        refine max_le_max ?_ le_rfl
        rw [Nat.cast_natAbs]
        simp
      refine le_trans ?_ hmax
      rw [hHdef]
      exact Nat.cast_le.mpr hnat
    have hH0 : (0 : ℝ) < H := by
      have hpos : 0 < max (((m : ℚ) / (n : ℚ)).num.natAbs) (((m : ℚ) / (n : ℚ)).den) :=
        lt_of_lt_of_le ((m : ℚ) / (n : ℚ)).pos (le_max_right _ _)
      rw [hHdef]
      exact_mod_cast hpos
    -- from `C' / h ^ κ` down to `H ^ (-κ')`
    have hstep3 : C' / h ^ κ ≤ h ^ (-κ') := by
      have h1 : C' ≤ h ^ (κ - κ') :=
        le_trans hstep1 (Real.rpow_le_rpow hn0.le hhn (by linarith))
      have h2 : h ^ (κ - κ') / h ^ κ - C' / h ^ κ = (h ^ (κ - κ') - C') / h ^ κ := by ring
      have h3 : (0 : ℝ) ≤ (h ^ (κ - κ') - C') / h ^ κ :=
        div_nonneg (by linarith) hhκ.le
      have h4 : h ^ (κ - κ') / h ^ κ = h ^ (-κ') := by
        rw [← Real.rpow_sub hh0]
        ring_nf
      linarith
    have hstep4 : h ^ (-κ') ≤ H ^ (-κ') := by
      have hHκ : (0 : ℝ) < H ^ κ' := Real.rpow_pos_of_pos hH0 κ'
      have hhκ' : (0 : ℝ) < h ^ κ' := Real.rpow_pos_of_pos hh0 κ'
      have hle : H ^ κ' ≤ h ^ κ' := Real.rpow_le_rpow hH0.le hHle (by linarith)
      rw [Real.rpow_neg hh0.le, Real.rpow_neg hH0.le]
      have heq : (H ^ κ')⁻¹ - (h ^ κ')⁻¹ = (h ^ κ' - H ^ κ') / (H ^ κ' * h ^ κ') := by
        field_simp
      have : (0 : ℝ) ≤ (h ^ κ' - H ^ κ') / (H ^ κ' * h ^ κ') :=
        div_nonneg (by linarith) (mul_nonneg hHκ.le hhκ'.le)
      linarith
    calc min 1 |ξ - (((m : ℚ) / (n : ℚ) : ℚ) : ℝ)|
        ≤ |ξ - (((m : ℚ) / (n : ℚ) : ℚ) : ℝ)| := min_le_right _ _
      _ ≤ C' / h ^ κ := hsmall.le
      _ ≤ h ^ (-κ') := hstep3
      _ ≤ H ^ (-κ') := hstep4
  · refine lt_of_lt_of_le hsmall ?_
    have hnκ : (0 : ℝ) < (n : ℝ) ^ κ := Real.rpow_pos_of_pos hn0 κ
    have hle : (n : ℝ) ^ κ ≤ h ^ κ := Real.rpow_le_rpow hn0.le hhn (by linarith)
    have h1 : C' / h ^ κ ≤ C' / (n : ℝ) ^ κ := by
      have heq : C' / (n : ℝ) ^ κ - C' / h ^ κ = C' * (h ^ κ - (n : ℝ) ^ κ)
          / ((n : ℝ) ^ κ * h ^ κ) := by field_simp
      have : (0 : ℝ) ≤ C' * (h ^ κ - (n : ℝ) ^ κ) / ((n : ℝ) ^ κ * h ^ κ) :=
        div_nonneg (mul_nonneg hC'0.le (by linarith)) (mul_nonneg hnκ.le hhκ.le)
      linarith
    refine le_trans h1 ?_
    rw [div_le_iff₀ hnκ]
    have : C' / ε * ε = C' := by field_simp
    nlinarith [hstep2]


/-- **Roth's theorem** (Roth 1955). The irrationality exponent of a real algebraic irrational
number is exactly `2`: it is approximable to order `2` and to no better order, whatever its
degree. This is the value Layer 1.1 leaves open between `2` and `deg ξ`. -/
theorem Real.irrationalityExponent_eq_two {ξ : ℝ} (hirr : Irrational ξ)
    (halg : IsAlgebraic ℚ ξ) : irrationalityExponent ξ = 2 :=
  le_antisymm (irrationalityExponent_le_two halg) (two_le_irrationalityExponent hirr)

/-! ### Acceptance criteria -/

/-- **The test Layer 1.1 could not do.** Layer 1 pins `irrationalityExponent (2 ^ (1/3))` only
between `2` and the degree `3`; Roth's theorem gives the value. -/
example : Real.irrationalityExponent (2 ^ ((1 : ℝ) / 3)) = 2 := by
  have hb : (1 : ℝ) < 2 := by norm_num
  have hx3 : (2 ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = ((2 : ℤ) : ℝ) := by
    rw [← Real.rpow_natCast (2 ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul (by norm_num)]
    norm_num
  have h1 : (1 : ℝ) < 2 ^ ((1 : ℝ) / 3) := by
    have h := Real.rpow_lt_rpow_of_exponent_lt hb (y := 0) (z := 1 / 3) (by norm_num)
    rwa [Real.rpow_zero] at h
  have h2 : (2 ^ ((1 : ℝ) / 3) : ℝ) < 2 := by
    have h := Real.rpow_lt_rpow_of_exponent_lt hb (y := 1 / 3) (z := 1) (by norm_num)
    rwa [Real.rpow_one] at h
  have hirr : Irrational (2 ^ ((1 : ℝ) / 3)) := by
    refine irrational_nrt_of_notint_nrt 3 2 hx3 ?_ (by norm_num)
    rintro ⟨y, hy⟩
    rw [hy] at h1 h2
    have hy1 : (1 : ℤ) < y := by exact_mod_cast h1
    have hy2 : y < 2 := by exact_mod_cast h2
    omega
  have halg : IsAlgebraic ℚ ((2 : ℝ) ^ ((1 : ℝ) / 3)) := by
    refine ⟨(Polynomial.X ^ 3 - Polynomial.C 2 : Polynomial ℚ), ?_, ?_⟩
    · intro hcon
      have h := congrArg (fun q : Polynomial ℚ ↦ q.coeff 3) hcon
      simp at h
    · simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
      have hx3' : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = (2 : ℝ) := by rw [hx3]; norm_num
      rw [hx3']
      simp
  exact Real.irrationalityExponent_eq_two hirr halg

/-- **Rejection test: algebraicity is what Roth's theorem is about.** Liouville's constant is
irrational and its exponent is `⊤`, so the conclusion is false for irrationals in general. -/
example : ¬ ∀ ξ : ℝ, Irrational ξ → Real.irrationalityExponent ξ = 2 := by
  intro h
  have htop : Real.irrationalityExponent (liouvilleNumber 2) = ⊤ :=
    Real.irrationalityExponent_eq_top_iff.2 (liouville_liouvilleNumber le_rfl)
  have h1 := h (liouvilleNumber 2) (liouville_liouvilleNumber le_rfl).irrational
  rw [htop] at h1
  exact absurd h1 (by simp)


/-- **Sharpness: Roth's theorem is false at `κ = 2`.** This is the test Layer 3.2 deferred, and
it is Dirichlet's theorem: for `ξ = √2 - 1`, which lies in `(1/4, 3/4)`, every rational `q` with
`|ξ - q| < 1 / q.den ^ 2` has naive height exactly `q.den`, so Mathlib's infinite Dirichlet set
sits inside the set the theorem would have to bound. The hypothesis `2 < κ` is therefore not an
artefact of the proof: the exponent `2` is attained. -/
example : ¬ {β : ℚ |
    min 1 |(√2 - 1) - (β : ℝ)| ≤ (max β.num.natAbs β.den : ℝ) ^ (-(2 : ℝ))}.Finite := by
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2nn : (0 : ℝ) ≤ √2 := Real.sqrt_nonneg 2
  have hlow : (1 : ℝ) / 4 < √2 - 1 := by nlinarith
  have hhigh : √2 - 1 < (3 : ℝ) / 4 := by nlinarith
  have hirr : Irrational (√2 - 1) := by
    simpa using irrational_sqrt_two.sub_intCast 1
  refine Set.Infinite.mono ?_
    (Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hirr)
  intro q hq
  rw [Set.mem_ofPred_eq] at hq ⊢
  have hd0 : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.pos
  have hcast : ((q.num : ℝ)) = (q : ℝ) * (q.den : ℝ) := by
    rw [Rat.cast_def]
    field_simp
  -- the naive height of `q` is its denominator
  have hnum : q.num.natAbs ≤ q.den := by
    have habs : |(q : ℝ)| ≤ 1 := by
      by_cases hd : q.den = 1
      · have hq1 : (q : ℝ) = (q.num : ℝ) := by rw [hcast, hd]; norm_num
        have hbnd : |(√2 - 1) - (q : ℝ)| < 1 := by
          refine lt_of_lt_of_le hq ?_
          rw [hd]
          norm_num
        rw [hq1] at hbnd ⊢
        have hab := abs_lt.mp hbnd
        have hl : (-1 : ℤ) < q.num := by
          have : (-1 : ℝ) < (q.num : ℝ) := by
            have := hab.2
            linarith
          exact_mod_cast this
        have hr : q.num < 2 := by
          have : (q.num : ℝ) < 2 := by
            have := hab.1
            linarith
          exact_mod_cast this
        have : q.num = 0 ∨ q.num = 1 := by omega
        rcases this with h | h <;> rw [h] <;> norm_num
      · have hd2 : (2 : ℝ) ≤ (q.den : ℝ) := by
          have hden2 : 2 ≤ q.den := by
            have := q.pos
            omega
          exact_mod_cast hden2
        have hsmall : |(√2 - 1) - (q : ℝ)| < 1 / 4 := by
          refine lt_of_lt_of_le hq ?_
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
        have hab := abs_lt.mp hsmall
        rw [abs_le]
        constructor <;> linarith
    have hnatabs : ((q.num.natAbs : ℕ) : ℝ) = |(q.num : ℝ)| := by
      rw [Nat.cast_natAbs]
      push_cast
      ring
    have hle : ((q.num.natAbs : ℕ) : ℝ) ≤ ((q.den : ℕ) : ℝ) := by
      rw [hnatabs, hcast, abs_mul, abs_of_pos hd0]
      calc |(q : ℝ)| * (q.den : ℝ) ≤ 1 * (q.den : ℝ) :=
            mul_le_mul_of_nonneg_right habs hd0.le
        _ = (q.den : ℝ) := one_mul _
    exact_mod_cast hle
  rw [← Nat.cast_max, max_eq_right hnum]
  have hpow : ((q.den : ℝ)) ^ (-(2 : ℝ)) = 1 / (q.den : ℝ) ^ 2 := by
    rw [Real.rpow_neg hd0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  rw [hpow]
  exact le_trans (min_le_right _ _) hq.le

end
