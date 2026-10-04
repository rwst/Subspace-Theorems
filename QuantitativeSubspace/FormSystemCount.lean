/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.FormDomainSystem
public import QuantitativeSubspace.FormIntervalCount
public import DiophantineApproximation.SystemSubspaceCount

/-!
# The count of the large solutions at Evertse–Ferretti strength

J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative Subspace Theorem*,
Ann. of Math. **177** (2013), 513–590, Theorem 3.1 with §5 and §21; J.-H. Evertse,
*On the Quantitative Subspace Theorem*, Zap. Nauchn. Sem. POMI **377** (2010), Theorem 2.1.

For a system under Evertse's normalization (2.4) (`NumberField.IsNormalizedSystem`), with `n`
forms over a Galois extension `E / K`, `R` distinct forms and coefficients of absolute height at
most `H`, the solutions `x` with `log H(x) ≥ X₀ = efSystemThreshold` lie in at most

```text
efLargeCount n [E : K] R δ = 1 + intervalCount n R' δ' · (1 + log ω₀ / log (1 + δ / 2n))
```

proper subspaces of `Kⁿ`, with `R' = R [E : K] + n`, `δ' = δ / (4 (n + δ))` and
`ω₀ = cutRatio R' δ' = δ'⁻¹ log 3R'`. It is Q0.3's assembly
(`NumberField.exists_finset_submodule_of_forall_interval`) fed with Q4.2's interval result for
approximation domains (`NumberField.exists_forall_mem_interval_approxDomain_ef`) in place of
Layer 6.1's. With the closed form of `intervalCount` (Q4.2d) and `log (1 + x) ≥ x / 2`:

```text
efLargeCount ≤ 1 + 60 n (n + 3) mb (1 + 4 n δ⁻¹ log ω₀)
             ≤ 3 · 10⁹ · 4ⁿ n¹³ δ⁻³ · log(64 n R' / δ') · log ω₀
             ≤ 2 · 10¹³ · 4ⁿ n¹⁴ δ⁻³ · log(3RD / δ) · log(δ⁻¹ log 3RD),
```

`mb = 64000 n⁸ 4ⁿ δ'⁻² log(64 n R' / δ') + 2`, `D = [E : K]`. The last line is EF13 Theorem 3.1
(Evertse 2010, Theorem 2.1), `10⁹ 2^{2n} n^{14} δ⁻³ log(3δ⁻¹RD) log(δ⁻¹ log 3RD)`, with a larger
constant; the middle one has EF13's `n¹³` before their `log n`s are absorbed. The count does not
depend on `[E : ℚ]`, on the number of places or on `H`.

The threshold `X₀` is linear in `log H` (`NumberField.efSystemThreshold_le`), and all solutions
lie in that many subspaces plus Layer 9.3's count plus one interval of Layer 9.4
(`NumberField.exists_finset_submodule_of_isNormalizedSystem_ef`).

## Main definitions

* `NumberField.efEps`, `NumberField.efSpread`: `ε = [E : K] δ / 2` and half the spread
  `A = [E : K] (1 + δ / n) / 2` of the exponents over `E`.
* `NumberField.efSystemDelta`: `δ' = δ / (4 (n + δ))`, the `δ` of Theorem 2.3.
* `NumberField.efSystemThreshold`: the threshold `X₀`.
* `NumberField.efLargeCount`: the number of subspaces of the large solutions.

## Main results

* `NumberField.exists_finset_submodule_of_efSystemThreshold_le`: the large solutions.
* `NumberField.exists_finset_submodule_of_isNormalizedSystem_ef`: all solutions.
* `NumberField.efLargeCount_le`, `NumberField.efLargeCount_le_shape`,
  `NumberField.efLargeCount_le_ef`: the closed forms.
* `NumberField.efSystemThreshold_le`: `X₀` is linear in `log H`.

## Implementation notes

⚠ **The fields are in `Type`**, as Theorem 2.3 needs (its exceptional subspace lives over
`AlgebraicClosure E`).

⚠ **The spread, not the absolute weight.** The twist `κ` of EF13 (5.2) must be at least the
spread `Σ_v max_i (c_iv - mean_v)` (EF13 (5.5)). For the raised exponents of a normalized system
(`max_i c_pi ≤ s(p)`, `Σ_p s(p) = 1`, weight exactly `-δ`) the spread over `E` is at most
`[E : K] (1 + δ / n)`, as in EF13 (where it is `1 + ε / n`), while the absolute weight is
`[E : K] (2 n + 2)`. Twisting by the latter cost a factor `n` in `δ'` and `n²` in the count.

This is milestone Q4.3 of `QuantitativeSubspace/README.md`.
-/

@[expose] public section

open Finset Module NumberField IsDedekindDomain Height

namespace NumberField

/-! ### The parameters -/

/-- **The weight margin over `E`**, `ε = [E : K] δ / 2`: the raised exponents have weight `-δ`,
and the shift that absorbs the constants adds `δ / 2`. -/
noncomputable def efEps (e : ℕ) (δ : ℝ) : ℝ := e * δ / 2

/-- **Half the spread over `E`**, `A = [E : K] (1 + δ / n) / 2`: the largest exponents at the places
of a normalized system sum to `1`, plus `δ / 2n` from the shift, and minus the weight over `n`
adds `δ / 2n` (EF13 (5.5), where the spread is `1 + ε / n`). -/
noncomputable def efSpread (e n : ℕ) (δ : ℝ) : ℝ := e * (1 + δ / n) / 2

/-- **The `δ` of Theorem 2.3 for a system**, `δ' = δ / (4 (n + δ))`: Q4.2's `ε / (4 n A)` at
`ε = efEps [E : K] δ` and `A = efSpread [E : K] n δ`, where `[E : K]` cancels
(`NumberField.domainDelta_efEps`). EF13 (5.4) has `δ = ε / (n + ε)`; the factor `4` is Q4.2's. -/
noncomputable def efSystemDelta (n : ℕ) (δ : ℝ) : ℝ := δ / (4 * (n + δ))

theorem domainDelta_efEps {n e : ℕ} (hn : 0 < n) (he : 0 < e) {δ : ℝ} (hδ : 0 < δ) :
    domainDelta n (efEps e δ) (efSpread e n δ) = efSystemDelta n δ := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have he0 : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  have hnδ : (n : ℝ) + δ ≠ 0 := by positivity
  rw [domainDelta, efEps, efSpread, efSystemDelta]
  field_simp

theorem efSystemDelta_pos {n : ℕ} {δ : ℝ} (hδ : 0 < δ) : 0 < efSystemDelta n δ := by
  rw [efSystemDelta]
  positivity

theorem efSystemDelta_le_one (n : ℕ) {δ : ℝ} (hδ : 0 < δ) : efSystemDelta n δ ≤ 1 := by
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  rw [efSystemDelta, div_le_one (by positivity)]
  linarith

/-- `δ'⁻¹ = 4 (n + δ) / δ ≤ 6 n / δ` for `n ≥ 2`. -/
theorem inv_efSystemDelta_le {n : ℕ} (hn : 2 ≤ n) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (efSystemDelta n δ)⁻¹ ≤ 6 * n / δ := by
  have hN : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rw [efSystemDelta, inv_div, div_le_div_iff_of_pos_right hδ]
  linarith

/-- **The number of subspaces of the large solutions**: the exceptional subspace of Theorem 2.3
and, for each of its `intervalCount n R' δ'` intervals of ratio `ω₀ = cutRatio R' δ'`, the windows
of the gap principle, with `R' = r e + n` (`r e` conjugated forms over `E`, `e = [E : K]`, and the
`n` coordinates). -/
noncomputable def efLargeCount (n e r : ℕ) (δ : ℝ) : ℝ :=
  1 + FormSystem.intervalCount n (r * e + n) (efSystemDelta n δ) *
    (1 + Real.log (FormSystem.cutRatio (r * e + n) (efSystemDelta n δ)) /
      Real.log (1 + δ / (2 * n)))

variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
variable {ι : Type*} [Fintype ι]

variable (E) in
open scoped Classical in
/-- **The threshold of the large solutions** on the scale of `log H(x)`: the largest of Q4.2's
threshold for the conjugated forms over `E` (`domainThreshold`, linear in their height), of
`[K : ℚ] (2 n / δ) log n` and of `systemHeightThreshold`. -/
noncomputable def efSystemThreshold (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue E ℝ) (L : AbsoluteValue K ℝ → ι → Dual E (ι → E))
    (r : ℕ) (H δ : ℝ) : ℝ :=
  max (domainThreshold (Fintype.card ι) (finrank ℚ E) (r * finrank K E)
      (efEps (finrank K E) δ) (efSpread (finrank K E) (Fintype.card ι) δ)
      (formLogHeight (systemPlacesOver E S) (conjSystem univ (S.image FinitePlace.mk) w L)))
    (max (finrank ℚ K * (2 * Fintype.card ι / δ) * Real.log (Fintype.card ι))
      (systemHeightThreshold (Fintype.card ι) (finrank ℚ E) (Fintype.card (InfinitePlace K) + #S)
        δ H (Real.log (scalarConst K S))))

/-! ### The large solutions -/

open scoped Classical in
/-- **The quantitative Subspace Theorem for the large solutions of a system, at Evertse–Ferretti
strength** (Q4.3). Under the normalization (2.4), with forms over a Galois extension `E / K`, the
solutions `x` with `log H(x) ≥ efSystemThreshold` lie in at most `efLargeCount n [E : K] R δ`
proper subspaces of `Kⁿ`, a number that depends on `n`, `δ`, `[E : K]` and the number `R` of
distinct forms only. It is `NumberField.exists_finset_submodule_of_forall_interval` with Q4.2's
interval result (EF13 Theorem 3.3), taken at `R [E : K]` forms over `E`. -/
theorem exists_finset_submodule_of_efSystemThreshold_le [IsGalois K E]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (w : AbsoluteValue K ℝ → AbsoluteValue E ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) :
    ∃ T : Finset (Submodule K (ι → K)),
      (#T : ℝ) ≤ efLargeCount (Fintype.card ι) (finrank K E) R δ ∧
      (∀ U ∈ T, U ≠ ⊤) ∧
      ∀ x ∈ systemSet S w L C c,
        efSystemThreshold E S w L R H δ ≤ Real.log (mulHeightAff x) → ∃ U ∈ T, x ∈ U := by
  set n := Fintype.card ι with hn
  have hn2 : 2 ≤ n := hN.two_le_card
  have : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  have hδ := hN.delta_pos
  have hδ1 := hN.delta_le_one
  set e := finrank K E with he
  have he0 : 0 < e := finrank_pos
  set Sfin' := systemPlacesOver E S with hSfin'
  set L' := conjSystem univ (S.image FinitePlace.mk) w L with hL'
  set ε := efEps e δ with hε
  set A := efSpread e n δ with hA
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have he0' : (0 : ℝ) < e := by exact_mod_cast he0
  have hε0 : 0 < ε := by rw [hε, efEps]; positivity
  have hεA : ε ≤ 4 * n * A := by
    rw [hε, hA, efEps, efSpread]
    have : (n : ℝ) * (1 + δ / n) = n + δ := by field_simp
    nlinarith
  have hsE : formCount Sfin' L' ≤ R * e := formCount_conjSystem_le hwInf hwFin hN.ncard_le
  have hLI : ∀ v : InfinitePlace K, LinearIndependent E (L v.1) := fun v ↦
    hN.linearIndependent (.inl v)
  have hLF : ∀ p ∈ S, LinearIndependent E (L (FinitePlace.mk p).1) := fun p hp ↦
    hN.linearIndependent (.inr ⟨p, hp⟩)
  set X₀ := efSystemThreshold E S w L R H δ with hX₀
  have hδ' : domainDelta n ε A = efSystemDelta n δ := domainDelta_efEps (by omega) he0 hδ
  obtain ⟨T, hTcard, hTtop, hT⟩ := exists_finset_submodule_of_forall_interval S w hwInf hwFin hN
    (X₀ := X₀) (ρ := FormSystem.cutRatio (R * e + n) (efSystemDelta n δ)) (NS := 1)
    (NI := FormSystem.intervalCount n (R * e + n) (efSystemDelta n δ))
    ((le_max_right _ _).trans (le_max_right _ _)) ((le_max_left _ _).trans (le_max_right _ _))
    (FormSystem.one_lt_cutRatio (by omega) (efSystemDelta_pos hδ)
      (efSystemDelta_le_one n hδ)).le fun c' _ _ hwe hsup ↦ by
      have hc : approxWeight Sfin' c' ≤ -ε := by rw [hwe, hε, efEps]
      have hspread : approxSupWeight Sfin' c' - approxWeight Sfin' c' / n ≤ 2 * A := by
        rw [hwe, hA, efSpread]
        have : (e : ℝ) * (1 + δ / (2 * n)) - -(e * δ / 2) / n = e * (1 + δ / n) := by
          field_simp
          ring
        linarith
      have h := exists_forall_mem_interval_approxDomain_ef (K := E) (Sfin := Sfin') (L := L')
        (linearIndependent_conjSystem_infinitePlace hwInf hLI)
        (fun V hV ↦ linearIndependent_conjSystem_systemPlacesOver hwFin hLF hV) hε0 hc hεA
        hspread hsE (X₀ := X₀) (le_max_left _ _)
      rwa [hδ'] at h
  exact ⟨T, hTcard.trans_eq (by rw [efLargeCount, Nat.cast_one]), hTtop, hT⟩

/-! ### All solutions -/

open scoped Classical in
/-- **The quantitative Subspace Theorem for a system, at Evertse–Ferretti strength** (Q4.3).
Under the normalization (2.4), with forms over a Galois extension `E / K`, all solutions lie in at
most

`δ⁻¹ ((10³ n) ^ (n [K : ℚ]) + 4 n log log (4 H)) + 1 + log ω / log (1 + δ / (2 n))`
`+ efLargeCount n [E : K] R δ`

proper subspaces of `Kⁿ`: the solutions that are not large by Layer 9.3, the large ones below
`X₀ = efSystemThreshold` by one interval of Layer 9.4 with ratio `ω = systemMiddleRatio`, and the
rest by `NumberField.exists_finset_submodule_of_efSystemThreshold_le`. -/
theorem exists_finset_submodule_of_isNormalizedSystem_ef [IsGalois K E]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (w : AbsoluteValue K ℝ → AbsoluteValue E ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) :
    ∃ T : Finset (Submodule K (ι → K)),
      (#T : ℝ) ≤ δ⁻¹ * ((10 ^ 3 * Fintype.card ι) ^ (Fintype.card ι * finrank ℚ K) +
          4 * Fintype.card ι * Real.log (Real.log (4 * H))) +
        (1 + Real.log (systemMiddleRatio (finrank ℚ K) (Fintype.card ι) H δ
            (efSystemThreshold E S w L R H δ)) /
              Real.log (1 + δ / (2 * Fintype.card ι))) +
        efLargeCount (Fintype.card ι) (finrank K E) R δ ∧
      (∀ U ∈ T, U ≠ ⊤) ∧ ∀ x ∈ systemSet S w L C c, ∃ U ∈ T, x ∈ U :=
  exists_finset_submodule_of_isNormalizedSystem_of_large S w hwInf hwFin hN
    (exists_finset_submodule_of_efSystemThreshold_le S w hwInf hwFin hN)

/-! ### The threshold in terms of heights -/

/-- `domainThreshold` is monotone in the height of the forms. -/
theorem domainThreshold_mono {n d s : ℕ} {ε A F F' : ℝ} (hn : 0 < n) (hd : 0 < d) (hε : 0 < ε)
    (hA : 0 < A) (hF : F ≤ F') : domainThreshold n d s ε A F ≤ domainThreshold n d s ε A F' := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hδ' : 0 < domainDelta n ε A := by rw [domainDelta]; positivity
  rw [domainThreshold, domainThreshold]
  gcongr

open scoped Classical in
/-- **The threshold is linear in the height of the coefficients**: `efSystemThreshold` is at most
the largest of `domainThreshold` at `F = (r_E + s_E) n² [E : ℚ] log H`, the sum over the infinite
places of `E` and the places `V` of `E` above `S`, of `[K : ℚ] (2 n / δ) log n` and of
`systemHeightThreshold`. With `domainThreshold`'s formula, the first is
`[E : ℚ] / 2A · (ℓ + log n / δ' + C(R' , n) ℓ / (n δ'))`, `ℓ = log n! + n F / [E : ℚ]`. -/
theorem efSystemThreshold_le [IsGalois K E] {S : Finset (HeightOneSpectrum (𝓞 K))}
    {w : AbsoluteValue K ℝ → AbsoluteValue E ℝ}
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) :
    efSystemThreshold E S w L R H δ ≤
      max (domainThreshold (Fintype.card ι) (finrank ℚ E) (R * finrank K E)
          (efEps (finrank K E) δ) (efSpread (finrank K E) (Fintype.card ι) δ)
          ((Fintype.card (InfinitePlace E) + #(systemPlacesOver E S)) * Fintype.card ι ^ 2 *
            (finrank ℚ E * Real.log H)))
        (max (finrank ℚ K * (2 * Fintype.card ι / δ) * Real.log (Fintype.card ι))
          (systemHeightThreshold (Fintype.card ι) (finrank ℚ E)
            (Fintype.card (InfinitePlace K) + #S) δ H (Real.log (scalarConst K S)))) := by
  have hn2 := hN.two_le_card
  have hδ := hN.delta_pos
  have he0 : (0 : ℝ) < finrank K E := by exact_mod_cast (finrank_pos : 0 < finrank K E)
  have hn0 : (0 : ℝ) < Fintype.card ι := by exact_mod_cast (by omega : 0 < Fintype.card ι)
  refine max_le_max (domainThreshold_mono (by omega) finrank_pos (by rw [efEps]; positivity)
    (by rw [efSpread]; positivity) (hN.formLogHeight_conjSystem_le hwInf hwFin)) le_rfl

/-! ### The closed form -/

/-- `log (1 + δ / 2n) ≥ δ / 4n` for `0 < δ ≤ 1`. -/
theorem div_le_log_one_add {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    δ / (4 * n) ≤ Real.log (1 + δ / (2 * n)) := by
  have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set x := δ / (2 * n) with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 := by rw [hx, div_le_one (by positivity)]; linarith
  have hlog := Real.one_sub_inv_le_log_of_pos (by linarith : 0 < 1 + x)
  have h4 : δ / (4 * n) = x / 2 := by rw [hx]; field_simp; ring
  have : (1 + x)⁻¹ ≤ 1 - x / 2 := by
    rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
    nlinarith
  linarith

/-- **The closed form of the count of the large solutions**:
`efLargeCount n e r δ ≤ 1 + 60 n (n + 3) mb (1 + 4 n δ⁻¹ log ω₀)` with `R' = r e + n`,
`δ' = δ / (4 (n + δ))`, `mb = chainBound n R' δ'` and `ω₀ = δ'⁻¹ log 3R'`. -/
theorem efLargeCount_le {n : ℕ} (e r : ℕ) (hn : 2 ≤ n) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    efLargeCount n e r δ ≤ 1 + 60 * n * (n + 3) *
      FormSystem.chainBound n (r * e + n) (efSystemDelta n δ) *
      (1 + 4 * n / δ * Real.log (FormSystem.cutRatio (r * e + n) (efSystemDelta n δ))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hδ'0 := efSystemDelta_pos (n := n) hδ
  have hδ'1 := efSystemDelta_le_one n hδ
  have hR : 2 ≤ r * e + n := by omega
  have hω := FormSystem.one_lt_cutRatio hR hδ'0 hδ'1
  have hlω : 0 ≤ Real.log (FormSystem.cutRatio (r * e + n) (efSystemDelta n δ)) :=
    Real.log_nonneg hω.le
  have hcount := FormSystem.intervalCount_le hn hR hδ'0 hδ'1
  have hlog := div_le_log_one_add (by omega : 0 < n) hδ hδ1
  have hfac : Real.log (FormSystem.cutRatio (r * e + n) (efSystemDelta n δ)) /
      Real.log (1 + δ / (2 * n)) ≤
      4 * n / δ * Real.log (FormSystem.cutRatio (r * e + n) (efSystemDelta n δ)) := by
    calc _ ≤ Real.log (FormSystem.cutRatio (r * e + n) (efSystemDelta n δ)) / (δ / (4 * n)) :=
          div_le_div_of_nonneg_left hlω (by positivity) hlog
      _ = _ := by field_simp
  rw [efLargeCount, add_le_add_iff_left]
  have hl0 : 0 < Real.log (1 + δ / (2 * n)) := (by positivity : 0 < δ / (4 * n)).trans_le hlog
  exact mul_le_mul hcount (by linarith) (add_nonneg zero_le_one (div_nonneg hlω hl0.le))
    ((Nat.cast_nonneg _).trans hcount)

/-- The arithmetic of `efLargeCount_le_shape`, over abstract reals: `a = n`, `F = 4ⁿ`,
`d = δ`, `D = δ'⁻¹ ≤ 6 n / δ`, `L₁ = log(64 n R' / δ') ≥ 1`, `L₂ = log ω₀ ≥ 1/2`. -/
private theorem shape_aux {a F d D L₁ L₂ : ℝ} (ha : 2 ≤ a) (hF : 1 ≤ F) (hd : 0 < d)
    (hd1 : d ≤ 1) (hD0 : 0 ≤ D) (hD : D ≤ 6 * a / d) (hL₁ : 1 ≤ L₁) (hL₂ : 1 / 2 ≤ L₂) :
    1 + 60 * a * (a + 3) * (64000 * a ^ 8 * F * D ^ 2 * L₁ + 2) * (1 + 4 * a / d * L₂) ≤
      3 * 10 ^ 9 * F * a ^ 13 / d ^ 3 * L₁ * L₂ := by
  set u := 1 / d with hu
  have hu1 : 1 ≤ u := by rw [hu, le_div_iff₀ hd]; linarith
  have hDu : D ≤ 6 * a * u := by
    rw [hu]; linarith [hD.trans_eq (by ring : 6 * a / d = 6 * a * (1 / d))]
  have hD2 : D ^ 2 ≤ 36 * a ^ 2 * u ^ 2 := by
    calc D ^ 2 ≤ (6 * a * u) ^ 2 := pow_le_pow_left₀ hD0 hDu 2
      _ = 36 * a ^ 2 * u ^ 2 := by ring
  have ha1 : 1 ≤ a := by linarith
  have ha10 : 1 ≤ a ^ 10 := one_le_pow₀ ha1
  have hu2 : 1 ≤ u ^ 2 := one_le_pow₀ hu1
  have hX : 1 ≤ a ^ 10 * F * u ^ 2 * L₁ :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le ha10 hF) hu2) hL₁
  -- the number of blocks
  have hM : 64000 * a ^ 8 * F * D ^ 2 * L₁ + 2 ≤ 2368000 * (a ^ 10 * F * u ^ 2 * L₁) := by
    have : 64000 * a ^ 8 * F * D ^ 2 * L₁ ≤ 64000 * a ^ 8 * F * (36 * a ^ 2 * u ^ 2) * L₁ := by
      gcongr
    nlinarith
  -- the gap factor
  have hG : 1 + 4 * a / d * L₂ ≤ 6 * a * u * L₂ := by
    have e : 4 * a / d * L₂ = 4 * a * u * L₂ := by rw [hu]; ring
    have : 1 ≤ 2 * a * u * L₂ := by
      have h1 : 1 ≤ a * u := one_le_mul_of_one_le_of_one_le ha1 hu1
      nlinarith
    linarith
  have ha3 : a + 3 ≤ 5 / 2 * a := by linarith
  have hY0 : 0 ≤ a ^ 10 * F * u ^ 2 * L₁ := by linarith
  have hP : 60 * a * (a + 3) * (64000 * a ^ 8 * F * D ^ 2 * L₁ + 2) ≤
      60 * a * (5 / 2 * a) * (2368000 * (a ^ 10 * F * u ^ 2 * L₁)) := by
    have h0 : 0 ≤ 60 * a := by linarith
    have h1 : 0 ≤ 64000 * a ^ 8 * F * D ^ 2 * L₁ + 2 := by positivity
    calc 60 * a * (a + 3) * (64000 * a ^ 8 * F * D ^ 2 * L₁ + 2)
        ≤ 60 * a * (5 / 2 * a) * (64000 * a ^ 8 * F * D ^ 2 * L₁ + 2) := by gcongr
      _ ≤ _ := by gcongr
  have hG0 : 0 ≤ 1 + 4 * a / d * L₂ := by positivity
  have hprod := mul_le_mul hP hG hG0 (by positivity)
  have e : 60 * a * (5 / 2 * a) * (2368000 * (a ^ 10 * F * u ^ 2 * L₁)) * (6 * a * u * L₂) =
      2131200000 * (F * a ^ 13 * u ^ 3 * L₁ * L₂) := by ring
  have e2 : 3 * 10 ^ 9 * F * a ^ 13 / d ^ 3 * L₁ * L₂ =
      3 * 10 ^ 9 * (F * a ^ 13 * u ^ 3 * L₁ * L₂) := by
    rw [hu]; field_simp
  have hZ : 1 / 2 ≤ F * a ^ 13 * u ^ 3 * L₁ * L₂ := by
    have : 1 ≤ F * a ^ 13 * u ^ 3 * L₁ :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le hF (one_le_pow₀ ha1)) (one_le_pow₀ hu1)) hL₁
    nlinarith
  rw [e2]
  nlinarith

/-- **The count of the large solutions in EF13's shape**:
`efLargeCount n e r δ ≤ 3 · 10⁹ · 4ⁿ n¹³ δ⁻³ · log(64 n R' / δ') · log ω₀` with `R' = r e + n`,
`δ' = δ / (4 (n + δ))` and `ω₀ = δ'⁻¹ log 3R'`. EF13 Theorem 3.1 (Evertse 2010, Theorem 2.1):
`10⁹ · 4ⁿ n¹⁴ δ⁻³ · log(3δ⁻¹RD) · log(δ⁻¹ log 3RD)`. Since `δ'⁻¹ ≤ 6 n / δ` and
`R' ≤ (n + 1) r e`, both logarithms differ from EF13's by `O(log n)`. -/
theorem efLargeCount_le_shape {n : ℕ} (e r : ℕ) (hn : 2 ≤ n) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) :
    efLargeCount n e r δ ≤ 3 * 10 ^ 9 * 4 ^ n * n ^ 13 / δ ^ 3 *
      Real.log (64 * n * (r * e + n : ℕ) / efSystemDelta n δ) *
      Real.log (FormSystem.cutRatio (r * e + n) (efSystemDelta n δ)) := by
  have hδ'0 := efSystemDelta_pos (n := n) hδ
  have hδ'1 := efSystemDelta_le_one n hδ
  have hR : 2 ≤ r * e + n := by omega
  have hN : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hL₁ := FormSystem.one_le_log_heightBase hn (by omega : 1 ≤ r * e + n) hδ'0 hδ'1
  have hL₂ := FormSystem.half_le_log_cutRatio hR hδ'0 hδ'1
  have hD := inv_efSystemDelta_le hn hδ hδ1
  have h := shape_aux (F := (4 : ℝ) ^ n) hN (one_le_pow₀ (by norm_num)) hδ hδ1
    (inv_nonneg.2 hδ'0.le) hD hL₁ hL₂
  have e1 : FormSystem.chainBound n (r * e + n) (efSystemDelta n δ) =
      64000 * n ^ 8 * 4 ^ n * (efSystemDelta n δ)⁻¹ ^ 2 *
        Real.log (64 * n * (r * e + n : ℕ) / efSystemDelta n δ) + 2 := by
    rw [FormSystem.chainBound, inv_pow, div_eq_mul_inv]
  refine (efLargeCount_le e r hn hδ hδ1).trans ?_
  rw [e1]
  convert h using 1

/-! ### EF13's variables -/

/-- `21 / 20 ≤ log 3`: `e^{1/20} ≤ 20/19` and `e · 20/19 < 3`. -/
theorem le_log_three : (21 : ℝ) / 20 ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h1 : Real.exp (1 / 20) ≤ 20 / 19 := by
    have h := Real.add_one_le_exp (-(1 / 20))
    have hpos := Real.exp_pos (1 / 20)
    have : Real.exp (-(1 / 20)) * Real.exp (1 / 20) = 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith
  have e : Real.exp (21 / 20) = Real.exp 1 * Real.exp (1 / 20) := by
    rw [← Real.exp_add]; norm_num
  rw [e]
  have := Real.exp_one_lt_d9
  nlinarith [Real.exp_pos 1, Real.exp_pos (1 / 20)]

/-- `(log x)² ≤ 4 x` for `x ≥ 1`. -/
theorem sq_log_le {x : ℝ} (hx : 1 ≤ x) : Real.log x ^ 2 ≤ 4 * x := by
  have hs : 0 < √x := Real.sqrt_pos.2 (by linarith)
  have hl : Real.log x = 2 * Real.log √x := by
    rw [Real.log_sqrt (by linarith)]; ring
  have h1 := Real.log_le_sub_one_of_pos hs
  have h0 : 0 ≤ Real.log √x := Real.log_nonneg (Real.one_le_sqrt.2 hx)
  have hsq : √x ^ 2 = x := Real.sq_sqrt (by linarith)
  rw [hl]
  nlinarith

/-- **The logarithms of the count, in EF13's variables**, over abstract reals: with `a = n ≥ 2`,
`M = r e ≥ 1`, `R' ≤ (a + 1) M`, `δ'⁻¹ ≤ 6 a / δ`, the product
`log(64 a R' / δ') · log(δ'⁻¹ log 3R')` is at most `4473 a` times
`log(3M / δ) · log(δ⁻¹ log 3M)`. -/
private theorem logs_aux {a M R' D d : ℝ} (ha : 2 ≤ a) (hM : 1 ≤ M) (hR'1 : 1 ≤ R')
    (hR' : R' ≤ (a + 1) * M) (hd : 0 < d) (hd1 : d ≤ 1) (hD1 : 1 ≤ D) (hD : D ≤ 6 * a / d)
    (hL₂0 : 0 ≤ Real.log (Real.log (3 * R') * D)) :
    Real.log (64 * a * R' * D) * Real.log (Real.log (3 * R') * D) ≤
      4473 * a * (Real.log (3 * M / d) * Real.log (Real.log (3 * M) / d)) := by
  have hl2 := Real.log_two_lt_d9
  have hl3 := le_log_three
  have hD0 : 0 < D := by linarith
  have ha0 : 0 < a := by linarith
  have hla : 0 ≤ Real.log a := Real.log_nonneg (by linarith)
  -- `X = log(3M/δ) ≥ 1`
  have hX : 1 ≤ Real.log (3 * M / d) := by
    have : (3 : ℝ) ≤ 3 * M / d := by rw [le_div_iff₀ hd]; nlinarith
    have := Real.log_le_log (by norm_num) this
    linarith
  -- `log 3M ≥ 21/20`, `Z = log 3M / δ ≥ 21/20`, `Y = log Z ≥ 1/25`
  have hl3M : 21 / 20 ≤ Real.log (3 * M) :=
    hl3.trans (Real.log_le_log (by norm_num) (by linarith))
  have hZ : 21 / 20 ≤ Real.log (3 * M) / d := by
    rw [le_div_iff₀ hd]; nlinarith
  have hY : 1 / 25 ≤ Real.log (Real.log (3 * M) / d) := by
    have h := Real.one_sub_inv_le_log_of_pos (by linarith : 0 < Real.log (3 * M) / d)
    have : (Real.log (3 * M) / d)⁻¹ ≤ 20 / 21 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    linarith
  -- `L₁ ≤ (7 + 3 log a) X`
  have hL₁ : Real.log (64 * a * R' * D) ≤ (7 + 3 * Real.log a) * Real.log (3 * M / d) := by
    have hb : 64 * a * R' * D ≤ 256 * a ^ 3 * (3 * M / d) := by
      have h1 : 64 * a * R' * D ≤ 64 * a * ((a + 1) * M) * (6 * a / d) := by gcongr
      have h2 : 64 * a * ((a + 1) * M) * (6 * a / d) = 128 * a ^ 2 * (a + 1) * (3 * M / d) := by
        field_simp
        ring
      have h3 : 128 * a ^ 2 * (a + 1) ≤ 256 * a ^ 3 := by nlinarith
      have h4 : 0 ≤ 3 * M / d := by positivity
      nlinarith
    have hlog : Real.log (256 * a ^ 3 * (3 * M / d)) =
        8 * Real.log 2 + 3 * Real.log a + Real.log (3 * M / d) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
        (by positivity), Real.log_pow, show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
      push_cast
      ring
    have := Real.log_le_log (by positivity) hb
    rw [hlog] at this
    nlinarith
  -- `L₂ ≤ 71 (1 + log a) Y`
  have hL₂ : Real.log (Real.log (3 * R') * D) ≤
      71 * (1 + Real.log a) * Real.log (Real.log (3 * M) / d) := by
    have hl3R : Real.log (3 * R') ≤ (1 + Real.log (a + 1)) * Real.log (3 * M) := by
      have h1 : Real.log (3 * R') ≤ Real.log ((a + 1) * (3 * M)) :=
        Real.log_le_log (by positivity) (by nlinarith)
      rw [Real.log_mul (x := a + 1) (y := 3 * M) (by positivity) (by positivity)] at h1
      have : 0 ≤ Real.log (a + 1) := Real.log_nonneg (by linarith)
      nlinarith
    have hla1 : Real.log (a + 1) ≤ a := by
      have := Real.log_le_sub_one_of_pos (by linarith : 0 < a + 1); linarith
    have hb : Real.log (3 * R') * D ≤ 16 * a ^ 2 * (Real.log (3 * M) / d) := by
      have hpos : 0 ≤ Real.log (3 * R') := Real.log_nonneg (by linarith)
      have h1 : Real.log (3 * R') * D ≤ ((1 + a) * Real.log (3 * M)) * (6 * a / d) := by
        have : Real.log (3 * R') ≤ (1 + a) * Real.log (3 * M) :=
          hl3R.trans (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
        exact mul_le_mul this hD hD0.le (by nlinarith)
      have h2 : ((1 + a) * Real.log (3 * M)) * (6 * a / d) =
          6 * a * (1 + a) * (Real.log (3 * M) / d) := by ring
      have h3 : 6 * a * (1 + a) ≤ 16 * a ^ 2 := by nlinarith
      have h4 : 0 ≤ Real.log (3 * M) / d := by positivity
      nlinarith
    have hpos : 0 < Real.log (3 * R') * D :=
      mul_pos (Real.log_pos (by linarith)) hD0
    have h1 := Real.log_le_log hpos hb
    have hlog : Real.log (16 * a ^ 2 * (Real.log (3 * M) / d)) =
        4 * Real.log 2 + 2 * Real.log a + Real.log (Real.log (3 * M) / d) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
        (by positivity), Real.log_pow, show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      push_cast
      ring
    rw [hlog] at h1
    have hY0 : 0 ≤ Real.log (Real.log (3 * M) / d) := by linarith
    have h2 : 4 * Real.log 2 + 2 * Real.log a ≤
        25 * (4 * Real.log 2 + 2 * Real.log a) * Real.log (Real.log (3 * M) / d) := by
      have : 0 ≤ 4 * Real.log 2 + 2 * Real.log a := by
        have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2); linarith
      nlinarith
    nlinarith
  -- the product
  have hsq := sq_log_le (by linarith : (1 : ℝ) ≤ a)
  have hL₁0 : 0 ≤ Real.log (64 * a * R' * D) := by
    refine Real.log_nonneg ?_
    have : 1 ≤ a * R' := one_le_mul_of_one_le_of_one_le (by linarith) hR'1
    have : 1 ≤ a * R' * D := one_le_mul_of_one_le_of_one_le this hD1
    linarith
  calc Real.log (64 * a * R' * D) * Real.log (Real.log (3 * R') * D)
      ≤ ((7 + 3 * Real.log a) * Real.log (3 * M / d)) *
          (71 * (1 + Real.log a) * Real.log (Real.log (3 * M) / d)) :=
        mul_le_mul hL₁ hL₂ hL₂0 (by nlinarith)
    _ = (7 + 3 * Real.log a) * (71 * (1 + Real.log a)) *
          (Real.log (3 * M / d) * Real.log (Real.log (3 * M) / d)) := by ring
    _ ≤ 4473 * a * (Real.log (3 * M / d) * Real.log (Real.log (3 * M) / d)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by nlinarith)
        nlinarith

/-- **The count of the large solutions in EF13's variables** (EF13 Theorem 3.1, Evertse 2010
Theorem 2.1): with `M = r e` the number of conjugated forms (EF13's `RD`),
`efLargeCount n e r δ ≤ 2 · 10¹³ · 4ⁿ n¹⁴ δ⁻³ · log(3M / δ) · log(δ⁻¹ log 3M)`, against EF13's
`10⁹ · 2^{2n} n^{14} δ⁻³ · log(3δ⁻¹RD) · log(δ⁻¹ log 3RD)`: the same shape, with a larger
constant. Before the logarithms are compared (`efLargeCount_le_shape`) it is `n¹³`, as in EF13's
proof (whose `n^{14}` absorbs their `log n`s). -/
theorem efLargeCount_le_ef {n e r : ℕ} (hn : 2 ≤ n) (he : 1 ≤ e) (hr : 1 ≤ r) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    efLargeCount n e r δ ≤ 2 * 10 ^ 13 * 4 ^ n * n ^ 14 / δ ^ 3 *
      Real.log (3 * (r * e : ℕ) / δ) * Real.log (Real.log (3 * (r * e : ℕ)) / δ) := by
  have hδ'0 := efSystemDelta_pos (n := n) hδ
  have hδ'1 := efSystemDelta_le_one n hδ
  have hR : 2 ≤ r * e + n := by omega
  have hN : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hM : (1 : ℝ) ≤ (r * e : ℕ) := Nat.one_le_cast.2 (Nat.mul_pos (by omega) (by omega))
  have hR'1 : (1 : ℝ) ≤ (r * e + n : ℕ) := by exact_mod_cast (by omega : 1 ≤ r * e + n)
  have hR' : ((r * e + n : ℕ) : ℝ) ≤ (n + 1) * (r * e : ℕ) := by
    push_cast
    push_cast at hM
    nlinarith
  have hD1 : 1 ≤ (efSystemDelta n δ)⁻¹ := (one_le_inv₀ hδ'0).2 hδ'1
  have hD := inv_efSystemDelta_le hn hδ hδ1
  have hL₂ := FormSystem.half_le_log_cutRatio hR hδ'0 hδ'1
  have hL₁ := FormSystem.one_le_log_heightBase hn (by omega : 1 ≤ r * e + n) hδ'0 hδ'1
  have hlogs := logs_aux hN hM hR'1 hR' hδ hδ1 hD1 hD (by
    rw [← div_eq_mul_inv]; exact (by linarith : (0 : ℝ) ≤ 1 / 2).trans hL₂)
  have hshape := efLargeCount_le_shape e r hn hδ hδ1
  rw [FormSystem.cutRatio] at hshape hL₂
  rw [div_eq_mul_inv, div_eq_mul_inv (Real.log _)] at hshape
  rw [div_eq_mul_inv (Real.log _)] at hL₂
  rw [div_eq_mul_inv] at hL₁
  push_cast at hshape hlogs hL₁ hL₂ ⊢
  have hX0 : 0 ≤ Real.log (3 * (r * e : ℝ) / δ) * Real.log (Real.log (3 * (r * e : ℝ)) / δ) := by
    have := hlogs.trans' (mul_nonneg (by linarith) (by linarith))
    nlinarith
  have hc : (0 : ℝ) ≤ 3 * 10 ^ 9 * 4 ^ n * n ^ 13 / δ ^ 3 := by positivity
  calc _ ≤ _ := hshape
    _ = 3 * 10 ^ 9 * 4 ^ n * n ^ 13 / δ ^ 3 *
          (Real.log (64 * n * (r * e + n) * (efSystemDelta n δ)⁻¹) *
            Real.log (Real.log (3 * (r * e + n)) * (efSystemDelta n δ)⁻¹)) := by
        simp only [div_eq_mul_inv]; ring
    _ ≤ 3 * 10 ^ 9 * 4 ^ n * n ^ 13 / δ ^ 3 * (4473 * n *
          (Real.log (3 * (r * e) / δ) * Real.log (Real.log (3 * (r * e)) / δ))) :=
        mul_le_mul_of_nonneg_left hlogs hc
    _ ≤ _ := by
        have e1 : 3 * 10 ^ 9 * 4 ^ n * n ^ 13 / δ ^ 3 * (4473 * n *
            (Real.log (3 * (r * e) / δ) * Real.log (Real.log (3 * (r * e)) / δ))) =
            13419000000000 * 4 ^ n * n ^ 14 / δ ^ 3 *
              (Real.log (3 * (r * e) / δ) * Real.log (Real.log (3 * (r * e)) / δ)) := by ring
        rw [e1, mul_assoc (2 * 10 ^ 13 * 4 ^ n * n ^ 14 / δ ^ 3)]
        refine mul_le_mul_of_nonneg_right ?_ hX0
        have : (0 : ℝ) ≤ 4 ^ n * n ^ 14 / δ ^ 3 := by positivity
        have h1 : 13419000000000 * 4 ^ n * (n : ℝ) ^ 14 / δ ^ 3 =
            13419000000000 * (4 ^ n * n ^ 14 / δ ^ 3) := by ring
        have h2 : 2 * 10 ^ 13 * 4 ^ n * (n : ℝ) ^ 14 / δ ^ 3 =
            2 * 10 ^ 13 * (4 ^ n * n ^ 14 / δ ^ 3) := by ring
        rw [h1, h2]
        nlinarith

end NumberField
