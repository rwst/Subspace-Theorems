/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.RationalPlaces
public import QuantitativeSubspace.ResultantHeights
public import QuantitativeSubspace.SubspaceCountTwo
public import STForMathlib.Analysis.SpecialFunctions.Log.SeriesBounds

/-!
# Numerical evaluation of the counts in two variables

The counts of `QuantitativeSubspace/SubspaceCountTwo.lean` are closed forms in `δ`, the number of
forms and the threshold `X₀`, but they contain logarithms, a ceiling and Evertse's factor
`max (1, 2 (m + 1) / η) ^ (m + 1)`. A caller that wants a decimal number (a count of lines below
`4·10⁹`, say) has to bound each of them by rationals. This file does the part of that work that
does not depend on the caller's system, so that what is left is `norm_num` at given `δ`.

* **Places of `ℚ`.** Every height-one prime of `𝓞 ℚ` is the prime of `Rat.finitePlace p` and has
  absolute norm `p`; the places of `ℚ` over `S` are `S` itself; Minkowski's constant over `ℚ` is
  `2 ∏ p`.
* **The parameters.** In two variables over a field of degree `e`, `η = e δ / (64 (6 e + 1))`
  (`δ/448` over `ℚ`), and the chain length `m` is at most any `M ≥ (2/3) Λ / η²` with
  `Λ ≥ log (4 s)`.
* **The counts.** `systemLargeCountTwo ≤ 2 + M (1 + Λ / L)` and the same for
  `systemGapCountTwo`, from rational bounds `m ≤ M`, `log (16 (M + 1) / η) ≤ Λ` and
  `L ≤ log (1 + δ / 4)` (or `L ≤ log ρ`). Lower bounds `L` come from the series of
  `STForMathlib/Analysis/SpecialFunctions/Log/SeriesBounds.lean`.
* **The threshold over `ℚ`.** For a system over `ℚ` in two variables with `t` primes, Evertse's
  Roth lemma and `b ≤ β`, `systemThresholdTwo` is at most `ratThresholdCoeffTwo t β δ m` times
  `4 (1 + t) log H + ∑ log p + 1`, or one of the two terms that come from the system. The
  coefficient is a polynomial in `t`, `m` and `δ⁻¹` times Evertse's factor; only the factor
  matters for the logarithm, which is what the middle term of the count needs.

The evaluations at the frame of Problem 10.13 of Bugeaud's book (`δ = 13/50`, `S = {2, 3}`),
where they give `3.87·10⁹` lines, are the first consumer.

## Main definitions

* `NumberField.ratThresholdCoeffTwo`: the coefficient of the threshold over `ℚ`.
* `NumberField.ratThresholdCoeffTwoAt`: the same at a given margin, `η` and chain length;
  `NumberField.ratThresholdCoeffTwoExplicit` also at Siegel's exponent `q`.

## Main results

* `Rat.absNorm_maximalIdeal_finitePlace`, `Rat.prime_absNorm`: the absolute norm of a prime of
  `𝓞 ℚ` is the rational prime under it.
* `NumberField.systemPlacesOver_rat`, `NumberField.card_systemPlacesOver_rat`,
  `NumberField.scalarConst_rat`: the places and Minkowski's constant over `ℚ`.
* `NumberField.subspaceEta_systemTwo`, `NumberField.subspaceChainLength_one_le`: `η` and `m`.
* `NumberField.systemLargeCountTwo_evertse_le_of_le`,
  `NumberField.systemGapCountTwo_evertse_le_of_le`: the counts from rational bounds.
* `NumberField.systemMiddleRatio_le`: the ratio of the middle interval is at most
  `max (1, δ X / (2 n log n))`.
* `NumberField.systemThresholdTwo_rat_le`: the threshold over `ℚ` in closed form.
* `NumberField.penultimateCoeff_evertse_rat_le_at`, `NumberField.systemThresholdTwoAt_rat_le`:
  the same at the caller's parameters (`NumberField.systemThresholdTwoAt`).
* `NumberField.penultimateCoeffAt_evertse_rat_le`, `NumberField.systemThresholdTwoExplicit_rat_le`:
  the same at an explicit chain length `m`, `η` and Siegel exponent `q`, with Evertse's Roth
  lemma at them (`NumberField.systemThresholdTwoExplicit`).
* `MvPolynomial.resultantHeight_botBound_one_le`: `h(ℙ¹) ≤ 6` for Rémond's heights, the `β` of
  Evertse's Roth lemma at them.

## References

* [Ste26] R. Stephan, *Line counts and a census for the exceptions to `‖(3/2)^n‖ ≥ (3/4)^n`,
  with an application to Waring's problem*, preprint (2026), doi:10.13140/RG.2.2.15019.20008,
  §7.3, (13)–(14), and §13 (the evaluation at `δ = 13/50`, at the generic parameters and at
  those of Theorem 7.2).
-/

@[expose] public section

open Finset Module IsDedekindDomain

universe u

namespace Rat

open NumberField

/-- **Every prime of `𝓞 ℚ` is the prime of a `p`-adic place.** -/
theorem exists_maximalIdeal_finitePlace_eq (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ p : Nat.Primes, (finitePlace p).maximalIdeal = v := by
  obtain ⟨p, hp, hv⟩ := exists_prime_padic_eq (FinitePlace.mk v)
  refine ⟨⟨p, hp.out⟩, ?_⟩
  have : finitePlace ⟨p, hp.out⟩ = FinitePlace.mk v :=
    Subtype.ext ((finitePlace_val _).trans hv.symm)
  rw [this, FinitePlace.maximalIdeal_mk]

/-- **The prime of `𝓞 ℚ` over `p` has absolute norm `p`.** -/
theorem absNorm_maximalIdeal_finitePlace (p : Nat.Primes) :
    Ideal.absNorm (finitePlace p).maximalIdeal.asIdeal = p := by
  have hp : (p : ℕ).Prime := p.2
  have hx : ((p : ℕ) : 𝓞 ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h := FinitePlace.apply_mul_absNorm_pow_eq_one (finitePlace p) hx
  have hv : finitePlace p (((p : ℕ) : 𝓞 ℚ) : ℚ) = ((p : ℕ) : ℝ)⁻¹ := by
    rw [finitePlace_apply]
    simp
  rw [hv] at h
  set N := Ideal.absNorm (finitePlace p).maximalIdeal.asIdeal
  set k := multiplicity (finitePlace p).maximalIdeal.asIdeal (Ideal.span {((p : ℕ) : 𝓞 ℚ)})
  have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast hp.pos
  have hNk : (N : ℝ) ^ k = (p : ℕ) := by
    field_simp at h
    linarith
  have hNk' : N ^ k = (p : ℕ) := by exact_mod_cast hNk
  exact ((Nat.Prime.pow_eq_iff hp).1 hNk').1

/-- **The absolute norm of a prime of `𝓞 ℚ` is a prime number.** -/
theorem prime_absNorm (v : HeightOneSpectrum (𝓞 ℚ)) : (Ideal.absNorm v.asIdeal).Prime := by
  obtain ⟨p, rfl⟩ := exists_maximalIdeal_finitePlace_eq v
  rw [absNorm_maximalIdeal_finitePlace]
  exact p.2

end Rat

namespace MvPolynomial

open Height

variable {σ ι K : Type} [Fintype σ] [Fintype ι] [DecidableEq ι] [Field K]
  [AdmissibleAbsValues K] {b : σ → ι}

/-- **`h(ℙ¹) ≤ 6` for Rémond's heights**: `2 (log 4 / 2 + 2) = log 4 + 4`. With
`NumberField.SubspaceRoth.evertse` at these heights, `b ≤ 6` in
`NumberField.systemThresholdTwo_rat_le`. -/
theorem resultantHeight_botBound_one_le (hK : ArchEmbedded K) (hb : Function.Surjective b) :
    (resultantHeight hK hb).botBound 1 ≤ 6 := by
  refine (resultantHeight_botBound_le hK hb 1).trans ?_
  have h4 : Real.log (2 * ((1 + 1 : ℕ) : ℝ)) = 2 * Real.log 2 := by
    rw [show (2 : ℝ) * ((1 + 1 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [h4]
  have := Real.log_two_lt_d9
  norm_num
  linarith

end MvPolynomial

namespace NumberField

/-! ### Places of `ℚ` -/

open scoped Classical in
/-- **The places of `ℚ` over `S` are the places of `S`.** -/
theorem systemPlacesOver_rat (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    systemPlacesOver ℚ S = S.image FinitePlace.mk := by
  ext V
  rw [mem_systemPlacesOver, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, hV⟩
    have h1 : V.maximalIdeal.asIdeal = p.asIdeal := by
      have hV' := hV.over
      rw [FinitePlace.maximalIdeal_mk] at hV'
      rw [hV', Ideal.under]
      ext x
      simp only [Ideal.mem_comap]
      exact Iff.rfl
    refine ⟨p, hp, ?_⟩
    rw [← FinitePlace.mk_maximalIdeal V, HeightOneSpectrum.asIdeal_injective h1]
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, ⟨by rw [Ideal.under]; ext x; simp only [Ideal.mem_comap]; exact Iff.rfl⟩⟩

theorem finitePlace_mk_injective_rat :
    Function.Injective (FinitePlace.mk : HeightOneSpectrum (𝓞 ℚ) → FinitePlace ℚ) :=
  fun p q h ↦ by rw [← FinitePlace.maximalIdeal_mk p, h, FinitePlace.maximalIdeal_mk]

open scoped Classical in
theorem card_systemPlacesOver_rat (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    #(systemPlacesOver ℚ S) = #S := by
  rw [systemPlacesOver_rat, Finset.card_image_of_injective _ finitePlace_mk_injective_rat]

open scoped Classical in
theorem sum_log_absNorm_systemPlacesOver_rat (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    ∑ V ∈ systemPlacesOver ℚ S, Real.log (Ideal.absNorm V.maximalIdeal.asIdeal : ℝ) =
      ∑ q ∈ S, Real.log (Ideal.absNorm q.asIdeal : ℝ) := by
  rw [systemPlacesOver_rat, Finset.sum_image fun p _ q _ h ↦ finitePlace_mk_injective_rat h]
  simp only [FinitePlace.maximalIdeal_mk]

/-- **Minkowski's constant over `ℚ`** is `2 ∏_{p ∈ S} p`. -/
theorem scalarConst_rat (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    scalarConst ℚ S = 2 * ∏ q ∈ S, (Ideal.absNorm q.asIdeal : ℝ) := by
  rw [scalarConst, Rat.numberField_discr]
  simp

/-! ### The parameters in two variables -/

/-- **`η` in two variables**: `e δ / (64 (6 e + 1))` over a field of degree `e`, for `δ ≤ 1`. Over
`ℚ` it is `δ / 448`. -/
theorem subspaceEta_systemTwo (e : ℕ) {δ : ℝ} (hδ1 : δ ≤ 1) :
    subspaceEta 1 (2 * systemEps e δ) (systemAbsBound e 2) = e * δ / (64 * (6 * e + 1)) := by
  have he : (0 : ℝ) ≤ e := Nat.cast_nonneg e
  have hval : 2 * systemEps e δ / (8 * (((1 : ℕ) : ℝ) + 1) ^ 2 * (systemAbsBound e 2 + 1)) =
      e * δ / (64 * (6 * e + 1)) := by
    rw [systemEps, systemAbsBound]
    push_cast
    field_simp
    ring
  rw [subspaceEta, hval, min_eq_right]
  rw [div_le_one (by positivity)]
  nlinarith

/-- **The chain length in two variables** is at most any `M ≥ (2/3) Λ / η²` with
`Λ ≥ log (4 s)`. -/
theorem subspaceChainLength_one_le {s : ℕ} {ε A Λ : ℝ} {M : ℕ}
    (hΛ : Real.log (4 * s) ≤ Λ) (hM : 2 / 3 * Λ / subspaceEta 1 ε A ^ 2 ≤ M) :
    subspaceChainLength 1 s ε A ≤ M := by
  rw [subspaceChainLength, Nat.ceil_le]
  refine le_trans ?_ hM
  have h4 : (2 * (((1 : ℕ) : ℝ) + 1) * s) = 4 * s := by push_cast; ring
  rw [h4]
  have : 4 * Real.log (4 * s) / ((((1 : ℕ) : ℝ) + 1) * (((1 : ℕ) : ℝ) + 2) *
      subspaceEta 1 ε A ^ 2) = 2 / 3 * Real.log (4 * s) / subspaceEta 1 ε A ^ 2 := by
    push_cast
    ring
  rw [this]
  gcongr

/-! ### The counts from rational bounds -/

/-- **The large count in two variables from rational bounds**: if `m ≤ M`,
`log (16 (M + 1) / η) ≤ Λ` and `0 < L ≤ log (1 + δ / 4)`, then
`systemLargeCountTwo ≤ 2 + M (1 + Λ / L)`. -/
theorem systemLargeCountTwo_evertse_le_of_le (b : ℕ → ℝ) {e s : ℕ} (he : 1 ≤ e) {δ : ℝ}
    (hδ : 0 < δ) {M : ℕ} {Λ L : ℝ}
    (hm : subspaceChainLength 1 s (2 * systemEps e δ) (systemAbsBound e 2) ≤ M)
    (hΛ : Real.log (16 * ((M : ℝ) + 1) /
      subspaceEta 1 (2 * systemEps e δ) (systemAbsBound e 2)) ≤ Λ)
    (hL : 0 < L) (hLδ : L ≤ Real.log (1 + δ / 4)) :
    systemLargeCountTwo (RothParams.evertse b) e s δ ≤ 2 + M * (1 + Λ / L) := by
  set ε := 2 * systemEps e δ with hε
  set A := systemAbsBound e 2 with hA
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hε0 : 0 < ε := by rw [hε, systemEps]; positivity
  have hA0 : 0 ≤ A := by rw [hA, systemAbsBound]; positivity
  have hη : 0 < subspaceEta 1 ε A := subspaceEta_pos hε0 hA0
  have hmR : (subspaceChainLength 1 s ε A : ℝ) ≤ M := by exact_mod_cast hm
  have hσ0 : 0 < evertseRatio 1 s ε A := (RothParams.evertse b).ratio_pos hε0 hA0
  have hσ1 : evertseRatio 1 s ε A ≤ 1 := (RothParams.evertse b).ratio_le_one hε0 hA0
  have hρ1 : 1 ≤ 4 * (evertseRatio 1 s ε A)⁻¹ := by
    have : 1 ≤ (evertseRatio 1 s ε A)⁻¹ := (one_le_inv₀ hσ0).2 hσ1
    linarith
  have hlog0 : 0 ≤ Real.log (4 * (evertseRatio 1 s ε A)⁻¹) := Real.log_nonneg hρ1
  have hlog : Real.log (4 * (evertseRatio 1 s ε A)⁻¹) ≤ Λ := by
    refine le_trans (Real.log_le_log (by linarith) ?_) hΛ
    rw [four_mul_inv_evertseRatio]
    gcongr
  have hq : Real.log (4 * (evertseRatio 1 s ε A)⁻¹) / Real.log (1 + δ / (2 * 2)) ≤ Λ / L := by
    rw [show (2 : ℝ) * 2 = 4 by norm_num]
    exact div_le_div₀ (hlog0.trans hlog) hlog hL hLδ
  have hq0 : 0 ≤ Real.log (4 * (evertseRatio 1 s ε A)⁻¹) / Real.log (1 + δ / (2 * 2)) :=
    div_nonneg hlog0 (Real.log_nonneg (by linarith [div_pos hδ (by norm_num : (0 : ℝ) < 2 * 2)]))
  rw [systemLargeCountTwo]
  change 2 + _ * (1 + Real.log (4 * (evertseRatio 1 s ε A)⁻¹) / _) ≤ _
  have := mul_le_mul hmR (add_le_add_left hq 1) (by linarith) (Nat.cast_nonneg M)
  linarith

/-- **The count with the caller's gap principle from rational bounds**: as
`NumberField.systemLargeCountTwo_evertse_le_of_le` with `0 < L ≤ log ρ`, and
`log (X₀ / Y) ≤ Λ'` for the range below the threshold. -/
theorem systemGapCountTwo_evertse_le_of_le (b : ℕ → ℝ) {e s : ℕ} (he : 1 ≤ e) {δ ρ X₀ Y : ℝ}
    (hδ : 0 < δ) (hY : 0 < Y) (hYX : Y ≤ X₀) {M : ℕ} {Λ Λ' L : ℝ}
    (hm : subspaceChainLength 1 s (2 * systemEps e δ) (systemAbsBound e 2) ≤ M)
    (hΛ : Real.log (16 * ((M : ℝ) + 1) /
      subspaceEta 1 (2 * systemEps e δ) (systemAbsBound e 2)) ≤ Λ)
    (hΛ' : Real.log (X₀ / Y) ≤ Λ') (hL : 0 < L) (hLρ : L ≤ Real.log ρ) :
    systemGapCountTwo (RothParams.evertse b) e s δ ρ X₀ Y ≤ 3 + M * (1 + Λ / L) + Λ' / L := by
  set ε := 2 * systemEps e δ with hε
  set A := systemAbsBound e 2 with hA
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hε0 : 0 < ε := by rw [hε, systemEps]; positivity
  have hA0 : 0 ≤ A := by rw [hA, systemAbsBound]; positivity
  have hη : 0 < subspaceEta 1 ε A := subspaceEta_pos hε0 hA0
  have hmR : (subspaceChainLength 1 s ε A : ℝ) ≤ M := by exact_mod_cast hm
  have hσ0 : 0 < evertseRatio 1 s ε A := (RothParams.evertse b).ratio_pos hε0 hA0
  have hσ1 : evertseRatio 1 s ε A ≤ 1 := (RothParams.evertse b).ratio_le_one hε0 hA0
  have hρ1 : 1 ≤ 4 * (evertseRatio 1 s ε A)⁻¹ := by
    have : 1 ≤ (evertseRatio 1 s ε A)⁻¹ := (one_le_inv₀ hσ0).2 hσ1
    linarith
  have hlog0 : 0 ≤ Real.log (4 * (evertseRatio 1 s ε A)⁻¹) := Real.log_nonneg hρ1
  have hlog : Real.log (4 * (evertseRatio 1 s ε A)⁻¹) ≤ Λ := by
    refine le_trans (Real.log_le_log (by linarith) ?_) hΛ
    rw [four_mul_inv_evertseRatio]
    gcongr
  have hq : Real.log (4 * (evertseRatio 1 s ε A)⁻¹) / Real.log ρ ≤ Λ / L :=
    div_le_div₀ (hlog0.trans hlog) hlog hL hLρ
  have hq0 : 0 ≤ Real.log (4 * (evertseRatio 1 s ε A)⁻¹) / Real.log ρ :=
    div_nonneg hlog0 (hL.le.trans hLρ)
  have hXY0 : 0 ≤ Real.log (X₀ / Y) := Real.log_nonneg (by rw [le_div_iff₀ hY]; linarith)
  have hq' : Real.log (X₀ / Y) / Real.log ρ ≤ Λ' / L :=
    div_le_div₀ (hXY0.trans hΛ') hΛ' hL hLρ
  rw [systemGapCountTwo]
  change 2 + _ * (1 + Real.log (4 * (evertseRatio 1 s ε A)⁻¹) / _) + _ ≤ _
  have := mul_le_mul hmR (add_le_add_left hq 1) (by linarith) (Nat.cast_nonneg M)
  linarith

/-- **The ratio of the middle interval** is at most `max (1, δ X / (2 n log n))`: the large
solutions have height at least `n ^ (2 n / δ)`. -/
theorem systemMiddleRatio_le {d n : ℕ} (hd : 1 ≤ d) (hn : 2 ≤ n) {H δ X : ℝ} (hδ : 0 < δ)
    (hX : 0 ≤ X) :
    systemMiddleRatio d n H δ X ≤ max 1 (δ * X / (2 * n * Real.log n)) := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hlogn : 0 < Real.log n := Real.log_pos hn1
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ (2 * n / δ : ℝ) :=
    Real.one_le_rpow hn1.le (by positivity)
  have hmax : (n : ℝ) ^ (2 * n / δ : ℝ) ≤ max (2 * H) ((n : ℝ) ^ (2 * n / δ : ℝ)) :=
    le_max_right _ _
  have hlog : 2 * n / δ * Real.log n ≤ Real.log (max (2 * H) ((n : ℝ) ^ (2 * n / δ : ℝ))) := by
    rw [← Real.log_rpow (by linarith)]
    exact Real.log_le_log (by linarith) hmax
  have hpos : 0 < 2 * n / δ * Real.log n := by positivity
  have hden : 2 * n / δ * Real.log n ≤
      d * Real.log (max (2 * H) ((n : ℝ) ^ (2 * n / δ : ℝ))) := by
    nlinarith
  rw [systemMiddleRatio]
  refine max_le_max le_rfl ?_
  calc X / (d * Real.log (max (2 * H) ((n : ℝ) ^ (2 * n / δ : ℝ))))
      ≤ X / (2 * n / δ * Real.log n) := div_le_div_of_nonneg_left hX hpos hden
    _ = δ * X / (2 * n * Real.log n) := by field_simp

/-! ### The threshold over `ℚ` -/

/-- **The coefficient of the threshold over `ℚ` in two variables**, with `t` primes, `b ≤ β` in
Evertse's Roth lemma, the chain length `m` and `η = δ / 448`:
`(16 (1 + t) F (m + 1)² (m + β⁺ + 40 (1 + t) + 5) + 5100 (1 + t)³ + 192 (896 / δ + 2)²) / δ`,
`F = max (1, 896 (m + 1) / δ) ^ (m + 1)` Evertse's factor. -/
noncomputable def ratThresholdCoeffTwo (t : ℕ) (β δ : ℝ) (m : ℕ) : ℝ :=
  (16 * (1 + t) * max 1 (896 * ((m : ℝ) + 1) / δ) ^ (m + 1) * ((m : ℝ) + 1) ^ 2 *
      (m + max β 0 + 40 * (1 + t) + 5) + 5100 * (1 + (t : ℝ)) ^ 3 + 192 * (896 / δ + 2) ^ 2) / δ

/-- `η` over `ℚ` in two variables is `δ / 448`. -/
theorem subspaceEta_rat {δ : ℝ} (hδ1 : δ ≤ 1) : subspaceEta 1 (δ / 2) 6 = δ / 448 := by
  have h := subspaceEta_systemTwo 1 hδ1
  rw [show 2 * systemEps 1 δ = δ / 2 by rw [systemEps]; ring,
    show systemAbsBound 1 2 = 6 by rw [systemAbsBound]; norm_num] at h
  rw [h]
  norm_num

theorem detCoeff_one_one : detCoeff 1 1 = 1 := by simp [detCoeff]

theorem detCoeff_one_two_le : detCoeff 1 2 ≤ 5 := by
  have := Real.log_two_lt_d9
  simp only [detCoeff, Nat.factorial]
  norm_num
  linarith

theorem auxCoeff_one_two_le (t : ℕ) : auxCoeff 1 2 1 t ≤ 3 + 40 * (1 + t) := by
  have := Real.log_two_lt_d9
  have := detCoeff_one_two_le
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  simp only [auxCoeff]
  push_cast
  nlinarith

theorem refCoeff_one_two_le (t B : ℕ) : refCoeff 1 2 1 t B ≤ 40 * (1 + t) + 3 * (B : ℝ) ^ 2 := by
  have := detCoeff_one_two_le
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hlog : (2 * (B : ℝ) + 1) * Real.log B ≤ 3 * (B : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos B with rfl | hB
    · simp
    have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
    have hl : Real.log B ≤ B := Real.log_le_self (Nat.cast_nonneg B)
    have hl0 : 0 ≤ Real.log B := Real.log_natCast_nonneg B
    nlinarith
  simp only [refCoeff]
  push_cast
  nlinarith

theorem kappaCoeff_one_two_le (T : ℕ) : kappaCoeff 1 (Nat.choose 2 1) 1 T ≤ 8 * (T : ℝ) ^ 2 := by
  have := Real.log_two_lt_d9
  have hT : (0 : ℝ) ≤ (T : ℝ) ^ 2 := by positivity
  simp only [kappaCoeff, detCoeff_one_one]
  norm_num
  nlinarith

theorem patternConstCoeff_one_two_le (t : ℕ) : patternConstCoeff 1 2 1 t ≤ 18 + (1 + t) := by
  have := detCoeff_one_two_le
  have h3 := Real.log_le_sub_one_of_pos (x := 3) (by norm_num)
  have h5 := Real.log_le_sub_one_of_pos (x := 5) (by norm_num)
  have ht := Real.log_le_sub_one_of_pos (x := (1 : ℝ) + t + 1) (by positivity)
  simp only [patternConstCoeff, invCoeff]
  push_cast
  norm_num at h3 h5 ⊢
  linarith

theorem patternHeightCoeff_one_two_le (t : ℕ) :
    patternHeightCoeff 1 2 1 t ≤ 3 + 82 * (1 + t) := by
  have := detCoeff_one_two_le
  have := Real.log_two_lt_d9
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  simp only [patternHeightCoeff]
  push_cast
  norm_num
  nlinarith

theorem rankCoeff_one_two_le (t : ℕ) {η : ℝ} (hη : 0 < η) :
    rankCoeff 1 2 t η ≤ 1 + (22 + 5 * (1 + t)) / η := by
  have := detCoeff_one_two_le
  have := Real.log_two_lt_d9
  have h3 := Real.log_le_sub_one_of_pos (x := 3) (by norm_num)
  have hpi := Real.log_le_sub_one_of_pos (x := 2 * Real.pi) (by positivity)
  have hpi4 := Real.pi_lt_four
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hnum : rankNumCoeff 1 2 t ≤ 22 + 5 * (1 + t) := by
    simp only [rankNumCoeff, basisCoeff, Nat.factorial]
    push_cast
    norm_num at h3 ⊢
    nlinarith
  simp only [rankCoeff]
  rw [inv_mul_eq_div]
  have := div_le_div_of_nonneg_right hnum hη.le
  linarith

/-- **The penultimate coefficient over `ℚ` in two variables**, with `t` places, `ε = δ / 2` and
Evertse's Roth lemma with `b ≤ β`: at most `1` plus
`(186 + 4640 T + 8 T² + 128 T³ + 192 B² + 16 T F (m + 1)² (m + β⁺ + 40 T + 5)) / δ`,
`T = 1 + t`, `B = 896 / δ + 2`, `F` Evertse's factor. -/
theorem penultimateCoeff_evertse_rat_le (b : ℕ → ℝ) {β : ℝ} (hb : ∀ k, b k ≤ β) (t s : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    penultimateCoeff (RothParams.evertse b) 1 2 1 t s 1 (δ / 2) 6 ≤
      1 + (186 + 4640 * (1 + t) + 8 * (1 + (t : ℝ)) ^ 2 + 128 * (1 + (t : ℝ)) ^ 3 +
        192 * (896 / δ + 2) ^ 2 + 16 * (1 + t) * max 1 (896 * ((subspaceChainLength 1 s (δ / 2) 6
          : ℝ) + 1) / δ) ^ (subspaceChainLength 1 s (δ / 2) 6 + 1) *
          ((subspaceChainLength 1 s (δ / 2) 6 : ℝ) + 1) ^ 2 *
          (subspaceChainLength 1 s (δ / 2) 6 + max β 0 + 40 * (1 + t) + 5)) / δ := by
  have hη := subspaceEta_rat hδ1
  have hF : 2 * ((subspaceChainLength 1 s (δ / 2) 6 : ℝ) + 1) / subspaceEta 1 (δ / 2) 6 =
      896 * ((subspaceChainLength 1 s (δ / 2) 6 : ℝ) + 1) / δ := by
    rw [hη]; field_simp; ring
  have hshift : (RothParams.evertse b).shift 1 s (δ / 2) 6 ≤
      max β 0 + subspaceChainLength 1 s (δ / 2) 6 + 2 := by
    change max (b _) 0 + _ + 2 ≤ _
    gcongr
    exact hb _
  have hfac : (RothParams.evertse b).factor 1 s (δ / 2) 6 =
      max 1 (896 * ((subspaceChainLength 1 s (δ / 2) 6 : ℝ) + 1) / δ)
        ^ (subspaceChainLength 1 s (δ / 2) 6 + 1) *
        ((subspaceChainLength 1 s (δ / 2) 6 : ℝ) + 1) := by
    change ((1 : ℕ) : ℝ) * max 1 (2 * ((subspaceChainLength 1 s (δ / 2) 6 : ℝ) + 1) /
      subspaceEta 1 (δ / 2) 6) ^ (subspaceChainLength 1 s (δ / 2) 6 + 1) *
      ((subspaceChainLength 1 s (δ / 2) 6 : ℝ) + 1) = _
    rw [hF]
    push_cast
    ring
  -- the ceiling of the reference index
  have hB : (⌈2 * ((1 : ℕ) : ℝ) / subspaceEta 1 (δ / 2) 6 + 1⌉₊ : ℝ) ≤ 896 / δ + 2 := by
    rw [hη]
    have h0 : 0 ≤ 2 * ((1 : ℕ) : ℝ) / (δ / 448) + 1 := by positivity
    have := Nat.ceil_lt_add_one h0
    have he : 2 * ((1 : ℕ) : ℝ) / (δ / 448) = 896 / δ := by field_simp; norm_num
    rw [he] at this
    linarith
  have hB2 : (⌈2 * ((1 : ℕ) : ℝ) / subspaceEta 1 (δ / 2) 6 + 1⌉₊ : ℝ) ^ 2 ≤ (896 / δ + 2) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hB 2
  have hlog4 : ((1 : ℕ) : ℝ) * Real.log (2 * (((1 : ℕ) : ℝ) + 1) * (1 : ℕ)) =
      2 * Real.log 2 := by
    rw [show (2 : ℝ) * (((1 : ℕ) : ℝ) + 1) * (1 : ℕ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hl2 := Real.log_two_lt_d9
  have haux := auxCoeff_one_two_le t
  have href := refCoeff_one_two_le t ⌈2 * ((1 : ℕ) : ℝ) / subspaceEta 1 (δ / 2) 6 + 1⌉₊
  rw [penultimateCoeff]
  set B := ⌈2 * ((1 : ℕ) : ℝ) / subspaceEta 1 (δ / 2) 6 + 1⌉₊ with hBdef
  have hkap := kappaCoeff_one_two_le (1 + t)
  have hpc := patternConstCoeff_one_two_le t
  have hph := patternHeightCoeff_one_two_le t
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  set m := subspaceChainLength 1 s (δ / 2) 6 with hm
  set F := max 1 (896 * ((m : ℝ) + 1) / δ) ^ (m + 1) with hFdef
  have hF1 : 1 ≤ F := one_le_pow₀ (le_max_left _ _)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hshift0 : 0 ≤ (RothParams.evertse b).shift 1 s (δ / 2) 6 :=
    (RothParams.evertse b).shift_nonneg (by positivity) (by norm_num)
  have hβ : 0 ≤ max β 0 := le_max_right _ _
  -- the three terms, each against its share of the bound
  have hδ2 : ∀ X Y : ℝ, 2 * X ≤ Y → X / (δ / 2) ≤ Y / δ := fun X Y h ↦ by
    rw [div_div_eq_mul_div]
    exact div_le_div_of_nonneg_right (by linarith) hδ.le
  have hA : 8 * (((1 : ℕ) : ℝ) + 1) * ((1 : ℕ) * Real.log (2 * (((1 : ℕ) : ℝ) + 1) * (1 : ℕ)) +
      auxCoeff 1 2 1 t + 2 * refCoeff 1 2 1 t B) / (δ / 2) ≤
      (160 + 3840 * (1 + t) + 192 * (896 / δ + 2) ^ 2) / δ := by
    refine hδ2 _ _ ?_
    rw [hlog4]
    linarith
  have hBterm : 8 * (((1 + t : ℕ) : ℝ)) * ((RothParams.evertse b).factor 1 s (δ / 2) 6 *
      ((m : ℝ) + 1) * (auxCoeff 1 2 1 t + (RothParams.evertse b).shift 1 s (δ / 2) 6 * (1 : ℕ))
      + kappaCoeff 1 (Nat.choose 2 1) 1 (1 + t)) / (δ / 2) ≤
      (128 * (1 + (t : ℝ)) ^ 3 + 16 * (1 + t) * F * ((m : ℝ) + 1) ^ 2 *
        (m + max β 0 + 40 * (1 + t) + 5)) / δ := by
    refine hδ2 _ _ ?_
    rw [hfac]
    push_cast at hkap ⊢
    have hsum : auxCoeff 1 2 1 t + (RothParams.evertse b).shift 1 s (δ / 2) 6 * 1 ≤
        m + max β 0 + 40 * (1 + t) + 5 := by linarith
    have hprod : F * ((m : ℝ) + 1) * ((m : ℝ) + 1) *
        (auxCoeff 1 2 1 t + (RothParams.evertse b).shift 1 s (δ / 2) 6 * 1) ≤
        F * ((m : ℝ) + 1) ^ 2 * (m + max β 0 + 40 * (1 + t) + 5) := by
      rw [sq, ← mul_assoc]
      gcongr
    nlinarith
  have hC : (4 * ((((1 : ℕ) : ℝ) + t) * patternConstCoeff 1 2 1 t + patternHeightCoeff 1 2 1 t)
      + 1) / (δ / 2) ≤ (26 + 800 * (1 + t) + 8 * (1 + (t : ℝ)) ^ 2) / δ := by
    refine hδ2 _ _ ?_
    push_cast
    have hpc0 := patternConstCoeff_nonneg 1 2 1 t
    nlinarith
  have hsplit : (186 + 4640 * (1 + t) + 8 * (1 + (t : ℝ)) ^ 2 + 128 * (1 + (t : ℝ)) ^ 3 +
      192 * (896 / δ + 2) ^ 2 + 16 * (1 + t) * F * ((m : ℝ) + 1) ^ 2 *
        (m + max β 0 + 40 * (1 + t) + 5)) / δ =
      (160 + 3840 * (1 + t) + 192 * (896 / δ + 2) ^ 2) / δ +
      (128 * (1 + (t : ℝ)) ^ 3 + 16 * (1 + t) * F * ((m : ℝ) + 1) ^ 2 *
        (m + max β 0 + 40 * (1 + t) + 5)) / δ +
      (26 + 800 * (1 + t) + 8 * (1 + (t : ℝ)) ^ 2) / δ := by ring
  rw [hsplit]
  push_cast at hA hBterm hC ⊢
  linarith

open scoped Classical in
/-- **The threshold over `ℚ` in two variables, in closed form.** For a normalized system over `ℚ`
in two variables with `t = #S` primes, `δ ≤ 1` and Evertse's Roth lemma with `b ≤ β`,
`systemThresholdTwo` is at most the largest of `ratThresholdCoeffTwo t β δ m` times
`4 (1 + t) log H + ∑_{p ∈ S} log p + 1`, of `(4 / δ) log 2`, and of the part
`systemHeightThreshold` that comes from the system; `m` is the chain length at `s = R` forms. -/
theorem systemThresholdTwo_rat_le {ι : Type u} [Fintype ι] (b : ℕ → ℝ) {β : ℝ}
    (hb : ∀ k, b k ≤ β) (hcard : Fintype.card ι = 2) {S : Finset (HeightOneSpectrum (𝓞 ℚ))}
    {w : AbsoluteValue ℚ ℝ → AbsoluteValue ℚ ℝ}
    (hwInf : ∀ v : InfinitePlace ℚ, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue ℚ ℝ → ι → Dual ℚ (ι → ℚ)} {C : InfinitePlace ℚ ⊕ S → ℝ}
    {c : InfinitePlace ℚ ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) (hδ1 : δ ≤ 1) :
    systemThresholdTwo ℚ S w L (RothParams.evertse b) R H δ ≤
      max (ratThresholdCoeffTwo #S β δ (subspaceChainLength 1 R (δ / 2) 6) *
          (4 * (1 + #S) * Real.log H + ∑ q ∈ S, Real.log (Ideal.absNorm q.asIdeal : ℝ) + 1))
        (max (4 / δ * Real.log 2)
          (systemHeightThreshold 2 1 (1 + #S) δ H
            (Real.log (2 * ∏ q ∈ S, (Ideal.absNorm q.asIdeal : ℝ))))) := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hδ := hN.delta_pos
  have hH := hN.one_le_height
  have hT := systemThresholdTwo_le (RothParams.evertse b) hcard hwInf hwFin hN
  have he : finrank ℚ ℚ = 1 := finrank_self ℚ
  have hr : Fintype.card (InfinitePlace ℚ) = 1 := Fintype.card_unique
  have hε : systemEps 1 δ = δ / 4 := by rw [systemEps]; push_cast; ring
  have hε2 : 2 * (δ / 4) = δ / 2 := by ring
  have hA : systemAbsBound 1 2 = 6 := by rw [systemAbsBound]; norm_num
  rw [he, hr, card_systemPlacesOver_rat, sum_log_absNorm_systemPlacesOver_rat, hcard,
    Rat.numberField_discr, hε, hε2, hA, mul_one, scalarConst_rat] at hT
  refine hT.trans (max_le_max ?_ (max_le_max (le_of_eq ?_) le_rfl))
  · -- the coefficient
    set t := #S with ht
    have htR : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    have hrank := rankCoeff_one_two_le t (η := δ / 4) (by positivity)
    have hpen := penultimateCoeff_evertse_rat_le b hb t R hδ hδ1
    set m := subspaceChainLength 1 R (δ / 2) 6 with hm
    set F := max 1 (896 * ((m : ℝ) + 1) / δ) ^ (m + 1) with hF
    have hF1 : 1 ≤ F := one_le_pow₀ (le_max_left _ _)
    have hcoef : 1 + rankCoeff 1 2 t (δ / 4) +
        penultimateCoeff (RothParams.evertse b) 1 2 1 t R 1 (δ / 2) 6 ≤
        ratThresholdCoeffTwo t β δ m := by
      rw [ratThresholdCoeffTwo]
      have h3 : (3 : ℝ) ≤ 3 / δ := by rw [le_div_iff₀ hδ]; linarith
      have hr4 : (22 + 5 * (1 + (t : ℝ))) / (δ / 4) = 4 * (22 + 5 * (1 + (t : ℝ))) / δ := by
        field_simp
      rw [hr4] at hrank
      have hT1 : (1 : ℝ) ≤ 1 + t := by linarith
      have hsum : 3 / δ + 4 * (22 + 5 * (1 + (t : ℝ))) / δ +
          (186 + 4640 * (1 + t) + 8 * (1 + (t : ℝ)) ^ 2 + 128 * (1 + (t : ℝ)) ^ 3 +
            192 * (896 / δ + 2) ^ 2 + 16 * (1 + t) * F * ((m : ℝ) + 1) ^ 2 *
            (m + max β 0 + 40 * (1 + t) + 5)) / δ ≤
          (16 * (1 + t) * F * ((m : ℝ) + 1) ^ 2 * (m + max β 0 + 40 * (1 + t) + 5) +
            5100 * (1 + (t : ℝ)) ^ 3 + 192 * (896 / δ + 2) ^ 2) / δ := by
        rw [← add_div, ← add_div]
        refine div_le_div_of_nonneg_right ?_ hδ.le
        have h2 : (1 + (t : ℝ)) ≤ (1 + (t : ℝ)) ^ 3 := by
          nlinarith [pow_le_pow_right₀ hT1 (by norm_num : 1 ≤ 3)]
        have h22 : (1 + (t : ℝ)) ^ 2 ≤ (1 + (t : ℝ)) ^ 3 :=
          pow_le_pow_right₀ hT1 (by norm_num)
        have h1 : (1 : ℝ) ≤ (1 + (t : ℝ)) ^ 3 := one_le_pow₀ hT1
        nlinarith
      linarith
    have hP0 : 0 ≤ ratThresholdCoeffTwo t β δ m := by
      have := rankCoeff_nonneg 1 2 t (η := δ / 4) (by positivity)
      have := penultimateCoeff_nonneg (RothParams.evertse b) 1 2 1 t R 1
        (by positivity : 0 < δ / 2) (by norm_num : (0 : ℝ) ≤ 6)
      linarith
    have hlogH := Real.log_nonneg hH
    have hsum : 0 ≤ ∑ q ∈ S, Real.log (Ideal.absNorm q.asIdeal : ℝ) :=
      sum_nonneg fun q _ ↦ Real.log_natCast_nonneg _
    refine mul_le_mul hcoef (le_of_eq ?_) ?_ hP0
    · simp only [Nat.cast_one, Nat.cast_ofNat, Int.cast_one, abs_one, Real.log_one, add_zero,
        one_mul]
      ring
    · simp only [Nat.cast_one, Nat.cast_ofNat, Int.cast_one, abs_one, Real.log_one, add_zero,
        one_mul]
      positivity
  · push_cast
    ring

/-! ### The threshold over `ℚ` at given parameters -/

/-- **The penultimate coefficient over `ℚ` in two variables, at explicit parameters**: with `t`
places, margin `ε`, the chain length `m`, `η`, Siegel's exponent `q ≥ 1` and Evertse's height cost
at them, with `b₁ ≤ β` the bound on `h(ℙ¹)`: at most `1` plus
`(93 + 2320 T + 4 T² + 64 T³ + 96 B² + 16 (q - 1)(3 + 40 T)
  + 8 T F (m + 1)² (m + β⁺ + q (40 T + 3) + 2)) / ε`,
`T = 1 + t`, `B = 2 / η + 2`, `F = max (1, 2 (m + 1) / η) ^ (m + 1)` Evertse's factor. -/
theorem penultimateCoeffAt_evertse_rat_le {β b₁ : ℝ} (hb : b₁ ≤ β) (t m : ℕ) {η q ε : ℝ}
    (hq : 1 ≤ q) (hε : 0 < ε) (hη : 0 < η) :
    penultimateCoeffAt 1 2 1 t 1 m η q ε
        (((1 : ℕ) : ℝ) * max 1 (2 * ((m : ℝ) + 1) / η) ^ (m + 1) * ((m : ℝ) + 1))
        (max b₁ 0 + (m : ℝ) + 2) ≤
      1 + (93 + 2320 * (1 + t) + 4 * (1 + (t : ℝ)) ^ 2 + 64 * (1 + (t : ℝ)) ^ 3 +
        96 * (2 / η + 2) ^ 2 + 16 * (q - 1) * (3 + 40 * (1 + t)) +
        8 * (1 + t) * max 1 (2 * ((m : ℝ) + 1) / η) ^ (m + 1) *
          ((m : ℝ) + 1) ^ 2 * (m + max β 0 + q * (40 * (1 + t) + 3) + 2)) / ε := by
  set Fr : ℝ := ((1 : ℕ) : ℝ) * max 1 (2 * ((m : ℝ) + 1) / η) ^ (m + 1) * ((m : ℝ) + 1) with hFr
  set gr : ℝ := max b₁ 0 + (m : ℝ) + 2 with hgr
  have hshift : gr ≤ max β 0 + m + 2 := by
    rw [hgr]
    gcongr
  have hfac : Fr = max 1 (2 * ((m : ℝ) + 1) / η) ^ (m + 1) * ((m : ℝ) + 1) := by
    rw [hFr]
    push_cast
    ring
  -- the ceiling of the reference index
  have hB : (⌈2 * ((1 : ℕ) : ℝ) / η + 1⌉₊ : ℝ) ≤ 2 / η + 2 := by
    have h0 : 0 ≤ 2 * ((1 : ℕ) : ℝ) / η + 1 := by positivity
    have := Nat.ceil_lt_add_one h0
    push_cast at this
    linarith
  have hB2 : (⌈2 * ((1 : ℕ) : ℝ) / η + 1⌉₊ : ℝ) ^ 2 ≤
      (2 / η + 2) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hB 2
  have hlog4 : ((1 : ℕ) : ℝ) * Real.log (2 * (((1 : ℕ) : ℝ) + 1) * (1 : ℕ)) =
      2 * Real.log 2 := by
    rw [show (2 : ℝ) * (((1 : ℕ) : ℝ) + 1) * (1 : ℕ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hl2 := Real.log_two_lt_d9
  have haux₁ := auxCoeff_one_two_le t
  have haux : q * auxCoeff 1 2 1 t ≤ q * (3 + 40 * (1 + t)) :=
    mul_le_mul_of_nonneg_left haux₁ (by linarith)
  have href := refCoeff_one_two_le t ⌈2 * ((1 : ℕ) : ℝ) / η + 1⌉₊
  rw [penultimateCoeffAt]
  set B := ⌈2 * ((1 : ℕ) : ℝ) / η + 1⌉₊ with hBdef
  have hkap := kappaCoeff_one_two_le (1 + t)
  have hpc := patternConstCoeff_one_two_le t
  have hph := patternHeightCoeff_one_two_le t
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  set F := max 1 (2 * ((m : ℝ) + 1) / η) ^ (m + 1) with hFdef
  have hF1 : 1 ≤ F := one_le_pow₀ (le_max_left _ _)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hshift0 : 0 ≤ gr := by positivity
  have hβ : 0 ≤ max β 0 := le_max_right _ _
  -- the three terms, each against its share of the bound
  have hε1 : ∀ X Y : ℝ, X ≤ Y → X / ε ≤ Y / ε := fun X Y h ↦
    div_le_div_of_nonneg_right h hε.le
  have hAt : 8 * (((1 : ℕ) : ℝ) + 1) * ((1 : ℕ) * Real.log (2 * (((1 : ℕ) : ℝ) + 1) * (1 : ℕ)) +
      q * auxCoeff 1 2 1 t + 2 * refCoeff 1 2 1 t B) / ε ≤
      (80 + 1920 * (1 + t) + 96 * (2 / η + 2) ^ 2 + 16 * (q - 1) * (3 + 40 * (1 + t))) / ε := by
    refine hε1 _ _ ?_
    rw [hlog4]
    linarith
  have hBterm : 8 * (((1 + t : ℕ) : ℝ)) * (Fr *
      ((m : ℝ) + 1) * (q * auxCoeff 1 2 1 t + gr * (1 : ℕ))
      + kappaCoeff 1 (Nat.choose 2 1) 1 (1 + t)) / ε ≤
      (64 * (1 + (t : ℝ)) ^ 3 + 8 * (1 + t) * F * ((m : ℝ) + 1) ^ 2 *
        (m + max β 0 + q * (40 * (1 + t) + 3) + 2)) / ε := by
    refine hε1 _ _ ?_
    rw [hfac]
    push_cast at hkap ⊢
    have hsum : q * auxCoeff 1 2 1 t + gr * 1 ≤
        m + max β 0 + q * (40 * (1 + t) + 3) + 2 := by linarith
    have hprod : F * ((m : ℝ) + 1) * ((m : ℝ) + 1) *
        (q * auxCoeff 1 2 1 t + gr * 1) ≤
        F * ((m : ℝ) + 1) ^ 2 * (m + max β 0 + q * (40 * (1 + t) + 3) + 2) := by
      rw [sq, ← mul_assoc]
      gcongr
    nlinarith
  have hC : (4 * ((((1 : ℕ) : ℝ) + t) * patternConstCoeff 1 2 1 t + patternHeightCoeff 1 2 1 t)
      + 1) / ε ≤ (13 + 400 * (1 + t) + 4 * (1 + (t : ℝ)) ^ 2) / ε := by
    refine hε1 _ _ ?_
    push_cast
    have hpc0 := patternConstCoeff_nonneg 1 2 1 t
    nlinarith
  have hsplit : (93 + 2320 * (1 + t) + 4 * (1 + (t : ℝ)) ^ 2 + 64 * (1 + (t : ℝ)) ^ 3 +
      96 * (2 / η + 2) ^ 2 + 16 * (q - 1) * (3 + 40 * (1 + t)) +
      8 * (1 + t) * F * ((m : ℝ) + 1) ^ 2 *
        (m + max β 0 + q * (40 * (1 + t) + 3) + 2)) / ε =
      (80 + 1920 * (1 + t) + 96 * (2 / η + 2) ^ 2 + 16 * (q - 1) * (3 + 40 * (1 + t))) / ε +
      (64 * (1 + (t : ℝ)) ^ 3 + 8 * (1 + t) * F * ((m : ℝ) + 1) ^ 2 *
        (m + max β 0 + q * (40 * (1 + t) + 3) + 2)) / ε +
      (13 + 400 * (1 + t) + 4 * (1 + (t : ℝ)) ^ 2) / ε := by ring
  rw [hsplit]
  push_cast at hAt hBterm hC ⊢
  linarith

/-- **The penultimate coefficient over `ℚ` in two variables, at any margin and parameter**: with
`t` places, margin `ε`, parameter `A`, `η = subspaceEta 1 ε A`, `m = subspaceChainLength 1 s ε A`
and Evertse's Roth lemma with `b ≤ β`: at most `1` plus
`(93 + 2320 T + 4 T² + 64 T³ + 96 B² + 8 T F (m + 1)² (m + β⁺ + 40 T + 5)) / ε`,
`T = 1 + t`, `B = 2 / η + 2`, `F = max (1, 2 (m + 1) / η) ^ (m + 1)` Evertse's factor. -/
theorem penultimateCoeff_evertse_rat_le_at (b : ℕ → ℝ) {β : ℝ} (hb : ∀ k, b k ≤ β) (t s : ℕ)
    {ε A : ℝ} (hε : 0 < ε) (hA : 0 ≤ A) :
    penultimateCoeff (RothParams.evertse b) 1 2 1 t s 1 ε A ≤
      1 + (93 + 2320 * (1 + t) + 4 * (1 + (t : ℝ)) ^ 2 + 64 * (1 + (t : ℝ)) ^ 3 +
        96 * (2 / subspaceEta 1 ε A + 2) ^ 2 + 8 * (1 + t) *
          max 1 (2 * ((subspaceChainLength 1 s ε A : ℝ) + 1) / subspaceEta 1 ε A)
            ^ (subspaceChainLength 1 s ε A + 1) *
          ((subspaceChainLength 1 s ε A : ℝ) + 1) ^ 2 *
          (subspaceChainLength 1 s ε A + max β 0 + 40 * (1 + t) + 5)) / ε := by
  rw [penultimateCoeff_eq_at]
  refine (penultimateCoeffAt_evertse_rat_le (hb _) t _ le_rfl hε (subspaceEta_pos hε hA)).trans
    (le_of_eq ?_)
  ring

/-- **The coefficient of the threshold over `ℚ` in two variables at given parameters**, with `t`
primes, `b ≤ β`, the margin `ε`, `η` and the chain length `m` of the interval result:
`(8 (1 + t) F (m + 1)² (m + β⁺ + 40 (1 + t) + 5) + 2600 (1 + t)³ + 96 (2 / η + 2)²) / (2 ε)`,
`F = max (1, 2 (m + 1) / η) ^ (m + 1)` Evertse's factor. At `ε = δ / 4`, `η = δ / 448` it is
`ratThresholdCoeffTwo`, up to the constant `2600` for `2550`. -/
noncomputable def ratThresholdCoeffTwoAt (t : ℕ) (β ε η : ℝ) (m : ℕ) : ℝ :=
  (8 * (1 + t) * max 1 (2 * ((m : ℝ) + 1) / η) ^ (m + 1) * ((m : ℝ) + 1) ^ 2 *
      (m + max β 0 + 40 * (1 + t) + 5) + 2600 * (1 + (t : ℝ)) ^ 3 + 96 * (2 / η + 2) ^ 2) /
    (2 * ε)

/-- **The coefficient of the threshold over `ℚ` in two variables at explicit parameters**:
`ratThresholdCoeffTwoAt` with Siegel's exponent `q`,
`(8 (1 + t) F (m + 1)² (m + β⁺ + q (40 (1 + t) + 3) + 2) + 2600 (1 + t)³
  + 16 (q - 1)(3 + 40 (1 + t)) + 96 (2 / η + 2)²) / (2 ε)`; at `q = 1` it is
`ratThresholdCoeffTwoAt` (`ratThresholdCoeffTwoExplicit_one`). -/
noncomputable def ratThresholdCoeffTwoExplicit (t : ℕ) (β ε η q : ℝ) (m : ℕ) : ℝ :=
  (8 * (1 + t) * max 1 (2 * ((m : ℝ) + 1) / η) ^ (m + 1) * ((m : ℝ) + 1) ^ 2 *
      (m + max β 0 + q * (40 * (1 + t) + 3) + 2) + 2600 * (1 + (t : ℝ)) ^ 3
      + 16 * (q - 1) * (3 + 40 * (1 + t)) + 96 * (2 / η + 2) ^ 2) / (2 * ε)

theorem ratThresholdCoeffTwoExplicit_one (t : ℕ) (β ε η : ℝ) (m : ℕ) :
    ratThresholdCoeffTwoExplicit t β ε η 1 m = ratThresholdCoeffTwoAt t β ε η m := by
  rw [ratThresholdCoeffTwoExplicit, ratThresholdCoeffTwoAt]
  ring

open scoped Classical in
/-- **The threshold over `ℚ` in two variables at explicit parameters, in closed form**: as
`NumberField.systemThresholdTwoAt_rat_le`, for `systemThresholdTwoExplicit` at the chain length
`m`, `0 < η`, Siegel's exponent `q ≥ 1`, the margin `0 < ε ≤ 1/2`, the fraction `τ` and Evertse's
height cost at `m` and `η` (`NumberField.rothLemmaAt_evertse`); for the frame of [Ste26] this
gives (13) there. -/
theorem systemThresholdTwoExplicit_rat_le {ι : Type u} [Fintype ι] (b : ℕ → ℝ) {β : ℝ}
    (hb : ∀ k, b k ≤ β) (hcard : Fintype.card ι = 2) {S : Finset (HeightOneSpectrum (𝓞 ℚ))}
    {w : AbsoluteValue ℚ ℝ → AbsoluteValue ℚ ℝ}
    (hwInf : ∀ v : InfinitePlace ℚ, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue ℚ ℝ → ι → Dual ℚ (ι → ℚ)} {C : InfinitePlace ℚ ⊕ S → ℝ}
    {c : InfinitePlace ℚ ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) (m : ℕ) (τ : ℝ) {η q ε : ℝ} (hη : 0 < η)
    (hq : 1 ≤ q) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    systemThresholdTwoExplicit ℚ S w L m H δ τ η q ε
        (((1 : ℕ) : ℝ) * max 1 (2 * ((m : ℝ) + 1) / η) ^ (m + 1) * ((m : ℝ) + 1))
        (max (b (m + 1)) 0 + (m : ℝ) + 2) ≤
      max (ratThresholdCoeffTwoExplicit #S β ε η q m *
          (4 * (1 + #S) * Real.log H + ∑ q ∈ S, Real.log (Ideal.absNorm q.asIdeal : ℝ) + 1))
        (max (4 / δ * Real.log 2)
          (systemHeightThreshold 2 1 (1 + #S) δ H
            (Real.log (2 * ∏ q ∈ S, (Ideal.absNorm q.asIdeal : ℝ))) / (2 * τ))) := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hδ := hN.delta_pos
  have hH := hN.one_le_height
  have hT := systemThresholdTwoExplicit_le hcard hwInf hwFin hN m τ (η := η) (q := q)
    (by linarith) hε
    (F := ((1 : ℕ) : ℝ) * max 1 (2 * ((m : ℝ) + 1) / η) ^ (m + 1) * ((m : ℝ) + 1))
    (g := max (b (m + 1)) 0 + (m : ℝ) + 2) (by positivity) (by positivity)
  have he : finrank ℚ ℚ = 1 := finrank_self ℚ
  have hr : Fintype.card (InfinitePlace ℚ) = 1 := Fintype.card_unique
  rw [he, hr, card_systemPlacesOver_rat, sum_log_absNorm_systemPlacesOver_rat, hcard,
    Rat.numberField_discr, scalarConst_rat] at hT
  refine hT.trans (max_le_max ?_ (max_le_max (le_of_eq ?_) le_rfl))
  · -- the coefficient
    set t := #S with ht
    have htR : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    have hrank := rankCoeff_one_two_le t hε
    have hpen := penultimateCoeffAt_evertse_rat_le (hb (m + 1)) t m hq
      (by positivity : 0 < 2 * ε) hη
    set F := max 1 (2 * ((m : ℝ) + 1) / η) ^ (m + 1) with hF
    have hF1 : 1 ≤ F := one_le_pow₀ (le_max_left _ _)
    have hcoef : 1 + rankCoeff 1 2 t ε +
        penultimateCoeffAt 1 2 1 t 1 m η q (2 * ε)
          (((1 : ℕ) : ℝ) * max 1 (2 * ((m : ℝ) + 1) / η) ^ (m + 1) * ((m : ℝ) + 1))
          (max (b (m + 1)) 0 + (m : ℝ) + 2) ≤
        ratThresholdCoeffTwoExplicit t β ε η q m := by
      rw [ratThresholdCoeffTwoExplicit]
      have h3 : (3 : ℝ) ≤ 3 / (2 * ε) := by rw [le_div_iff₀ (by positivity)]; linarith
      have hr2 : (22 + 5 * (1 + (t : ℝ))) / ε = 2 * (22 + 5 * (1 + (t : ℝ))) / (2 * ε) := by
        field_simp
      rw [hr2] at hrank
      have hT1 : (1 : ℝ) ≤ 1 + t := by linarith
      have hsum : 3 / (2 * ε) + 2 * (22 + 5 * (1 + (t : ℝ))) / (2 * ε) +
          (93 + 2320 * (1 + t) + 4 * (1 + (t : ℝ)) ^ 2 + 64 * (1 + (t : ℝ)) ^ 3 +
            96 * (2 / η + 2) ^ 2 + 16 * (q - 1) * (3 + 40 * (1 + t)) +
            8 * (1 + t) * F * ((m : ℝ) + 1) ^ 2 *
            (m + max β 0 + q * (40 * (1 + t) + 3) + 2)) / (2 * ε) ≤
          (8 * (1 + t) * F * ((m : ℝ) + 1) ^ 2 * (m + max β 0 + q * (40 * (1 + t) + 3) + 2) +
            2600 * (1 + (t : ℝ)) ^ 3 + 16 * (q - 1) * (3 + 40 * (1 + t))
            + 96 * (2 / η + 2) ^ 2) / (2 * ε) := by
        rw [← add_div, ← add_div]
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        have h2 : (1 + (t : ℝ)) ≤ (1 + (t : ℝ)) ^ 3 := by
          nlinarith [pow_le_pow_right₀ hT1 (by norm_num : 1 ≤ 3)]
        have h22 : (1 + (t : ℝ)) ^ 2 ≤ (1 + (t : ℝ)) ^ 3 :=
          pow_le_pow_right₀ hT1 (by norm_num)
        have h1 : (1 : ℝ) ≤ (1 + (t : ℝ)) ^ 3 := one_le_pow₀ hT1
        nlinarith
      linarith
    have hP0 : 0 ≤ ratThresholdCoeffTwoExplicit t β ε η q m := by
      have := rankCoeff_nonneg 1 2 t hε.le
      have := penultimateCoeffAt_nonneg 1 2 1 t 1 m (η := η) (by linarith : 0 ≤ q)
        (by positivity : 0 < 2 * ε)
        (by positivity : (0 : ℝ) ≤ ((1 : ℕ) : ℝ) * max 1 (2 * ((m : ℝ) + 1) / η) ^ (m + 1)
          * ((m : ℝ) + 1)) (by positivity : (0 : ℝ) ≤ max (b (m + 1)) 0 + (m : ℝ) + 2)
      linarith
    have hlogH := Real.log_nonneg hH
    have hsum : 0 ≤ ∑ q ∈ S, Real.log (Ideal.absNorm q.asIdeal : ℝ) :=
      sum_nonneg fun q _ ↦ Real.log_natCast_nonneg _
    refine mul_le_mul hcoef (le_of_eq ?_) ?_ hP0
    · simp only [Nat.cast_one, Nat.cast_ofNat, Int.cast_one, abs_one, Real.log_one, add_zero,
        one_mul]
      ring
    · simp only [Nat.cast_one, Nat.cast_ofNat, Int.cast_one, abs_one, Real.log_one, add_zero,
        one_mul]
      positivity
  · push_cast
    ring

open scoped Classical in
/-- **The threshold over `ℚ` in two variables at given parameters, in closed form**: as
`NumberField.systemThresholdTwo_rat_le`, for `systemThresholdTwoAt` at the margin `0 < ε ≤ 1/2`,
the parameter `A ≥ 0`, the form count `s` and the fraction `τ`, with
`η = subspaceEta 1 (2 ε) A` and `m = subspaceChainLength 1 s (2 ε) A`. -/
theorem systemThresholdTwoAt_rat_le {ι : Type u} [Fintype ι] (b : ℕ → ℝ) {β : ℝ}
    (hb : ∀ k, b k ≤ β) (hcard : Fintype.card ι = 2) {S : Finset (HeightOneSpectrum (𝓞 ℚ))}
    {w : AbsoluteValue ℚ ℝ → AbsoluteValue ℚ ℝ}
    (hwInf : ∀ v : InfinitePlace ℚ, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue ℚ ℝ → ι → Dual ℚ (ι → ℚ)} {C : InfinitePlace ℚ ⊕ S → ℝ}
    {c : InfinitePlace ℚ ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) (s : ℕ) (τ : ℝ) {ε A : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 2) (hA : 0 ≤ A) :
    systemThresholdTwoAt ℚ S w L (RothParams.evertse b) s H δ τ ε A ≤
      max (ratThresholdCoeffTwoAt #S β ε (subspaceEta 1 (2 * ε) A)
          (subspaceChainLength 1 s (2 * ε) A) *
          (4 * (1 + #S) * Real.log H + ∑ q ∈ S, Real.log (Ideal.absNorm q.asIdeal : ℝ) + 1))
        (max (4 / δ * Real.log 2)
          (systemHeightThreshold 2 1 (1 + #S) δ H
            (Real.log (2 * ∏ q ∈ S, (Ideal.absNorm q.asIdeal : ℝ))) / (2 * τ))) := by
  rw [systemThresholdTwoAt_eq_explicit, ← ratThresholdCoeffTwoExplicit_one]
  exact systemThresholdTwoExplicit_rat_le b hb hcard hwInf hwFin hN _ τ
    (subspaceEta_pos (by positivity) hA) le_rfl hε hε1

end NumberField
