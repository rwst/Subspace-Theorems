/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.SubspaceCount

/-!
# The quantitative Subspace Theorem in two variables

Y. Bugeaud and J.-H. Evertse, *On two notions of complexity of algebraic numbers*, Acta Arith.
**133** (2008), 221–250, Appendix (Proposition A.1): for `n = 2` the parametric Subspace Theorem
holds with `225 δ⁻³ log (2 r) log (δ⁻¹ log (2 r))` subspaces, `r` the number of distinct forms,
which is the best count known in two variables. Their proof is Evertse 1996 specialized to
`n = 2`: a chain of `m ≍ δ⁻² log (2 r)` levels (A.26) whose logarithms grow at the rate
`162 m² / δ` (A.30), Roth's lemma (A.7) in the form of Evertse 1995, and the gap principle
(A.3, A.4) inside each of the `m - 1` intervals that the chain leaves.

The same shape comes out of Layer Q0 when `#ι = 2`. Then the domains at large levels have rank
`0` or `1 = #ι - 1` (Layer 4.3), so Layer 5.6 applies to them directly and Layer 6.1, with its
wedges and its grids of exponents, is not needed. The interval result has `m` intervals of ratio
`4 σ⁻¹`, and Q0.3's assembly (`NumberField.exists_finset_submodule_of_forall_interval`) turns
each into `1 + log (4 σ⁻¹) / log (1 + δ / 4)` windows of the gap principle. With Evertse's Roth
lemma (Q1.5) `4 σ⁻¹ = 16 (m + 1) / η` is polynomial, so the count is
`m (1 + O(δ⁻¹ log (m / η)))` with `m = O(η⁻² log s)`: Bugeaud–Evertse's
`δ⁻³ log · log (δ⁻¹ log)` (`NumberField.systemLargeCountTwo_evertse_le`).

## Main definitions

* `NumberField.twoThreshold`: the threshold of the interval result in two variables, the larger
  of Layer 4.3's rank threshold and Layer 5.6's `penultimateThreshold`.
* `NumberField.systemThresholdTwo`, `NumberField.systemLargeCountTwo`: Q0.3's threshold and count
  of the large solutions for `n = 2`, with Layer 5.6 in place of 6.1.

## Main results

* `NumberField.exists_forall_mem_interval_approxDomain_two`: **the parametric Subspace Theorem in
  two variables as an interval result**, with at most two subspaces (`⊥` and Layer 5.4's
  exceptional one) and `m = subspaceChainLength 1 s (2 ε) A` intervals of ratio `4 σ⁻¹`. No grids.
* `NumberField.twoThreshold_le`, `NumberField.systemThresholdTwo_le`: the thresholds, linear in
  the heights.
* `NumberField.exists_finset_submodule_of_systemThresholdTwo_le`,
  `NumberField.exists_finset_submodule_of_isNormalizedSystem_two`: Q0.3 for `n = 2`, any Roth
  lemma.
* `NumberField.exists_finset_submodule_of_isNormalizedSystem_two_evertse`: the same with
  Evertse's.
* `NumberField.systemLargeCountTwo_evertse_le`: **the count in closed form**. With `s = R e`
  distinct forms over `E` and `Y = 449 / δ`,

  `systemLargeCountTwo ≤ 2 + 2 ℓ Y² (1 + 5 log (32 ℓ Y³) / δ)`, `ℓ = 1 + log (4 s)`.

## Comparison with Bugeaud–Evertse

The main term `10 (1 + log (4 s)) Y² log (32 (1 + log (4 s)) Y³) / δ` is
`O(δ⁻³ log s · log (δ⁻¹ log s))`, Bugeaud–Evertse's `δ⁻³ log (2 r) log (δ⁻¹ log (2 r))` with
`s = R [E : K]` forms, the conjugates over `E` of the system's `R` (Q1.8b: Layer 5.2 imposes its
conditions per form). It depends neither on `|S|` nor on the number `t` of places of the
system: Q0.3's raised exponents have absolute weight at most `[E : K] (2 n + 2)`, as
Bugeaud–Evertse's are normalized by (A.7), `∑ max c ≤ 1`, and one scalar absorbs the constants
(Q1.8a).

## References

Y. Bugeaud and J.-H. Evertse, *On two notions of complexity of algebraic numbers*, Acta Arith.
**133** (2008), 221–250 (arXiv:0709.1560), Appendix.

This is Layer Q1.6 of the `QuantitativeSubspace` roadmap.
-/

@[expose] public section

open Finset Module MvPolynomial Height IsDedekindDomain

universe u

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type u} [Fintype ι]

/-! ### The parametric theorem in two variables -/

variable (Sfin : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) in
open scoped Classical in
/-- **The threshold of the interval result in two variables**, on the scale of `log Q`: the
largest of `1`, the logarithm of Layer 4.3's rank threshold at weight `-ε`, and Layer 5.6's
`penultimateThreshold` in dimension `1` at margin `2 ε`. An order on `ι` is chosen by transport
from `Fin #ι`, as for `parametricThreshold`. -/
noncomputable def twoThreshold (R : RothParams) (s : ℕ) (ε A : ℝ) : ℝ :=
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Equiv.injective _)
  max 1 (max (Real.log (rankThreshold Sfin L ε)) (penultimateThreshold Sfin L R 1 s (2 * ε) A))

open scoped Classical in
/-- **The parametric Subspace Theorem in two variables, as an interval result** (Bugeaud–Evertse
2008, Proposition A.1, in the form of Layer 6.1's interval result). For `#ι = 2`, forms linearly
independent at every place of `S`, at most `2 s` distinct forms, and exponents with
`approxWeight ≤ -ε < 0` and `approxAbsWeight ≤ A`, there is a set `T` of at most two proper
subspaces such that
for every `Q₀' ≥ twoThreshold` the levels `Q` with `log Q ≥ Q₀'` at which the domain lies in no
member of `T` have `log Q` in at most `m = subspaceChainLength 1 s (2 ε) A` intervals
`[t, 4 σ⁻¹ t)` with `t ≥ Q₀'`, where `σ` is the ratio of the Roth lemma `R`.

Above the rank threshold the domain has rank `0` or `1` (Layer 4.3), and rank `1 = #ι - 1` is
Layer 5.6's case, so 5.6 applies to the domain itself: no wedges and no grids. -/
theorem exists_forall_mem_interval_approxDomain_two (R : SubspaceRoth.{u} K)
    (hcard : Fintype.card ι = 2) {Sfin : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) {c : AbsoluteValue K ℝ → ι → ℝ}
    {ε : ℝ} (hε : 0 < ε) (hc : approxWeight Sfin c ≤ -ε) {A : ℝ}
    (hA : approxAbsWeight Sfin c ≤ A) {s : ℕ} (hs : formCount Sfin L ≤ 2 * s) :
    ∃ T : Finset (Submodule K (ι → K)),
      #T ≤ 2 ∧ (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ Q₀' : ℝ, twoThreshold Sfin L R.toRothParams s ε A ≤ Q₀' →
      ∃ 𝒯 : Finset ℝ,
        #𝒯 ≤ subspaceChainLength 1 s (2 * ε) A ∧
        (∀ t ∈ 𝒯, Q₀' ≤ t) ∧ ∀ Q : ℝ, 1 < Q → Q₀' ≤ Real.log Q →
          (∃ W ∈ T, approxDomain Sfin L c Q ⊆ W) ∨
            ∃ t ∈ 𝒯, t ≤ Real.log Q ∧ Real.log Q < 4 * (R.ratio 1 s (2 * ε) A)⁻¹ * t := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  let _ : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Equiv.injective _)
  have hε2 : 0 < 2 * ε := by positivity
  obtain ⟨𝒲, Q₀, h𝒲fin, h𝒲card, -, hQ₀eq, hint⟩ := exists_forall_mem_interval_approxSpan R
    (n := 1) le_rfl hcard hLInf hLFin hε2 (by linarith) hA (s := s) (by omega)
  set T : Finset (Submodule K (ι → K)) := insert ⊥ (h𝒲fin.toFinset.filter (· ≠ ⊤)) with hT
  refine ⟨T, ?_, ?_, fun Q₀' hQ₀' ↦ ?_⟩
  · refine (Finset.card_insert_le _ _).trans (Nat.add_le_add_right ?_ 1)
    refine (Finset.card_filter_le _ _).trans ?_
    rw [← Set.ncard_eq_toFinset_card 𝒲 h𝒲fin]
    exact h𝒲card
  · intro W hW
    rcases Finset.mem_insert.1 hW with rfl | hW
    · exact bot_ne_top
    · exact (Finset.mem_filter.1 hW).2
  have hQ₀ : Q₀ ≤ Q₀' := by
    rw [hQ₀eq]
    exact ((le_max_right _ _).trans (le_max_right _ _)).trans hQ₀'
  obtain ⟨k, hk, t, ht, hint⟩ := hint Q₀' hQ₀
  refine ⟨Finset.univ.image t, Finset.card_image_le.trans (by simpa using hk), fun u hu ↦ ?_,
    fun Q hQ1 hQ ↦ ?_⟩
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hu
    exact ht i
  have hQ0 : (0 : ℝ) < Q := lt_trans one_pos hQ1
  have ha0 : 0 < rankThreshold Sfin L ε := by
    rw [rankThreshold]
    positivity
  have hrank := finrank_approxSpan_lt_of_rankThreshold_le hLInf hLFin hε hc
    ((Real.log_le_log_iff ha0 hQ0).1
      ((((le_max_left _ _).trans (le_max_right _ _)).trans hQ₀').trans hQ))
  rw [hcard] at hrank
  rcases Nat.lt_or_ge (finrank K (approxSpan Sfin L c Q)) 1 with hR0 | hR1
  · refine Or.inl ⟨⊥, Finset.mem_insert_self _ _, fun z hz ↦ ?_⟩
    have hmem : z ∈ approxSpan Sfin L c Q := Submodule.subset_span hz
    have h0 : finrank K (approxSpan Sfin L c Q) = 0 := by omega
    rwa [Submodule.finrank_eq_zero.1 h0] at hmem
  have hR : finrank K (approxSpan Sfin L c Q) = 1 := by omega
  by_cases hW : approxSpan Sfin L c Q ∈ 𝒲
  · have htop : approxSpan Sfin L c Q ≠ ⊤ := fun h ↦ by
      rw [h, finrank_top, Module.finrank_fintype_fun_eq_card, hcard] at hR
      omega
    exact Or.inl ⟨_, Finset.mem_insert_of_mem (Finset.mem_filter.2
      ⟨h𝒲fin.mem_toFinset.2 hW, htop⟩), Submodule.subset_span⟩
  · obtain ⟨i, h1, h2⟩ := hint Q hQ1 hQ hR hW
    exact Or.inr ⟨t i, Finset.mem_image_of_mem t (Finset.mem_univ i), h1, h2⟩

open scoped Classical in
/-- **The threshold in two variables is linear in the heights**: `twoThreshold ≤ a Λ` with
`a = 1 + rankCoeff + penultimateCoeff` and `Λ = thresholdScale`. -/
theorem twoThreshold_le (R : RothParams) {Sfin : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ w : InfinitePlace K, LinearIndependent K (L w.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) (hcard : Fintype.card ι = 2) (s : ℕ)
    {ε : ℝ} (hε : 0 < ε) {A : ℝ} (hA : 0 ≤ A) :
    twoThreshold Sfin L R s ε A ≤ (1 + rankCoeff (finrank ℚ K) 2 #Sfin ε
      + penultimateCoeff R (finrank ℚ K) 2 (Fintype.card (InfinitePlace K)) #Sfin s 1 (2 * ε) A)
        * thresholdScale Sfin L := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  let o : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Equiv.injective _)
  have hsc := thresholdScale_congr (Sfin := Sfin) (L := L)
    (fun a b ↦ @LinearOrder.toDecidableEq ι o a b) (fun a b ↦ Classical.propDecidable (a = b))
  have hΛ : 1 ≤ thresholdScale Sfin L := one_le_thresholdScale Sfin L
  have hrank := log_rankThreshold_le hLInf hLFin hε (Sfin := Sfin) (L := L)
  have hpen := penultimateThreshold_le R hLInf hLFin (n := 1) (by omega) s (ε := 2 * ε)
    (by positivity) hA (Sfin := Sfin) (L := L)
  rw [hcard, hsc] at hrank hpen
  have h1 := rankCoeff_nonneg (finrank ℚ K) 2 #Sfin hε.le
  have h2 := penultimateCoeff_nonneg R (finrank ℚ K) 2 (Fintype.card (InfinitePlace K)) #Sfin s 1
    (by positivity : 0 < 2 * ε) hA
  have e1 := mul_nonneg h1 (by linarith : 0 ≤ thresholdScale Sfin L)
  have e2 := mul_nonneg h2 (by linarith : 0 ≤ thresholdScale Sfin L)
  rw [twoThreshold]
  refine max_le (by nlinarith) (max_le ?_ ?_) <;> nlinarith

/-! ### Systems in two variables -/

section System

variable {E : Type*} [Field E] [NumberField E] [Algebra K E]

variable (E) in
open scoped Classical in
/-- **The threshold of the quantitative Subspace Theorem for a system in two variables**, on the
scale of `log H(x)`: `systemThreshold` with `twoThreshold` in place of Layer 6.1's
`parametricThreshold`. -/
noncomputable def systemThresholdTwo (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue E ℝ) (L : AbsoluteValue K ℝ → ι → Dual E (ι → E))
    (R : RothParams) (r : ℕ) (H δ : ℝ) : ℝ :=
  max (twoThreshold (systemPlacesOver E S) (conjSystem univ (S.image FinitePlace.mk) w L) R
      (r * finrank K E) (systemEps (finrank K E) δ)
      (systemAbsBound (finrank K E) (Fintype.card ι)))
    (max (finrank ℚ K * (2 * Fintype.card ι / δ) * Real.log (Fintype.card ι))
      (systemHeightThreshold (Fintype.card ι) (finrank ℚ E) (Fintype.card (InfinitePlace K) + #S)
        δ H (Real.log (scalarConst K S))))

/-- **The number of subspaces of the large solutions in two variables**: `⊥`, Layer 5.6's
exceptional subspace and, for each of its `m` intervals of ratio `4 σ⁻¹`, the windows of the gap
principle. The parameters are `e = [E : K]` and a bound `s` on the number of distinct forms over
`E`; for a system with `R` distinct forms `s = R e` (`NumberField.formCount_conjSystem_le`). -/
noncomputable def systemLargeCountTwo (R : RothParams) (e s : ℕ) (δ : ℝ) : ℝ :=
  2 + (subspaceChainLength 1 s (2 * systemEps e δ) (systemAbsBound e 2) : ℝ) *
    (1 + Real.log (4 * (R.ratio 1 s (2 * systemEps e δ) (systemAbsBound e 2))⁻¹) /
      Real.log (1 + δ / (2 * 2)))

variable [IsGalois K E]

open scoped Classical in
/-- **The quantitative Subspace Theorem for the large solutions of a system in two variables**:
Q0.3's assembly (`NumberField.exists_finset_submodule_of_forall_interval`) fed with the interval
result in two variables (`NumberField.exists_forall_mem_interval_approxDomain_two`) in place of
Layer 6.1's. -/
theorem exists_finset_submodule_of_systemThresholdTwo_le (RL : SubspaceRoth.{u} E)
    (hcard : Fintype.card ι = 2)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (w : AbsoluteValue K ℝ → AbsoluteValue E ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) :
    ∃ T : Finset (Submodule K (ι → K)),
      (#T : ℝ) ≤ systemLargeCountTwo RL.toRothParams (finrank K E) (R * finrank K E) δ ∧
      (∀ U ∈ T, U ≠ ⊤) ∧
      ∀ x ∈ systemSet S w L C c,
        systemThresholdTwo E S w L RL.toRothParams R H δ ≤ Real.log (mulHeightAff x) →
        ∃ U ∈ T, x ∈ U := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hδ := hN.delta_pos
  set e := finrank K E with he
  set dE := finrank ℚ E with hdE
  have he0 : (0 : ℝ) < e := by exact_mod_cast (finrank_pos : 0 < finrank K E)
  set Sfin' := systemPlacesOver E S with hSfin'
  set L' := conjSystem univ (S.image FinitePlace.mk) w L with hL'
  set ε := systemEps e δ with hε
  set A := systemAbsBound e (Fintype.card ι) with hA
  have hε0 : 0 < ε := by rw [hε, systemEps]; positivity
  have hε2 : 0 < 2 * ε := by positivity
  have hA0 : 0 ≤ A := by rw [hA, systemAbsBound]; positivity
  set s := R * e with hs
  have hsE : formCount Sfin' L' ≤ 2 * s :=
    (formCount_conjSystem_le hwInf hwFin hN.ncard_le).trans (Nat.le_mul_of_pos_left _ two_pos)
  have hLI : ∀ v : InfinitePlace K, LinearIndependent E (L v.1) := fun v ↦
    hN.linearIndependent (.inl v)
  have hLF : ∀ p ∈ S, LinearIndependent E (L (FinitePlace.mk p).1) := fun p hp ↦
    hN.linearIndependent (.inr ⟨p, hp⟩)
  set X₀ := systemThresholdTwo E S w L RL.toRothParams R H δ with hX₀
  have hX₀P : twoThreshold Sfin' L' RL.toRothParams s ε A ≤ X₀ := le_max_left _ _
  set σ := RL.ratio 1 s (2 * ε) A with hσ
  have hσ0 : 0 < σ := RL.ratio_pos hε2 hA0
  have hσ1 : σ ≤ 1 := RL.ratio_le_one hε2 hA0
  have hρ1 : 1 ≤ 4 * σ⁻¹ := by
    have : 1 ≤ σ⁻¹ := (one_le_inv₀ hσ0).2 hσ1
    linarith
  obtain ⟨T, hTcard, hTtop, hT⟩ := exists_finset_submodule_of_forall_interval S w hwInf hwFin hN
    (X₀ := X₀) (ρ := 4 * σ⁻¹) (NS := 2)
    (NI := subspaceChainLength 1 s (2 * ε) A)
    ((le_max_right _ _).trans (le_max_right _ _)) ((le_max_left _ _).trans (le_max_right _ _))
    hρ1 fun c' hcw hcA _ _ ↦ by
      obtain ⟨T, hTcard, hTtop, hint⟩ :=
        exists_forall_mem_interval_approxDomain_two (K := E) (Sfin := Sfin') (L := L') RL hcard
          (linearIndependent_conjSystem_infinitePlace hwInf hLI)
          (fun V hV ↦ linearIndependent_conjSystem_systemPlacesOver hwFin hLF hV) hε0 hcw hcA hsE
      obtain ⟨𝒯, h𝒯card, h𝒯ge, hQint⟩ := hint X₀ hX₀P
      exact ⟨T, hTcard, hTtop, 𝒯, h𝒯card, h𝒯ge, hQint⟩
  refine ⟨T, hTcard.trans_eq ?_, hTtop, hT⟩
  simp only [systemLargeCountTwo, hσ, hA, hε, hs, hcard]
  push_cast
  ring

open scoped Classical in
/-- **The quantitative Subspace Theorem for a system in two variables**: all solutions lie in at
most Layer 9.3's count, plus one interval of Layer 9.4 below `X₀ = systemThresholdTwo`, plus
`systemLargeCountTwo` proper subspaces. -/
theorem exists_finset_submodule_of_isNormalizedSystem_two (RL : SubspaceRoth.{u} E)
    (hcard : Fintype.card ι = 2)
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
            (systemThresholdTwo E S w L RL.toRothParams R H δ)) /
              Real.log (1 + δ / (2 * Fintype.card ι))) +
        systemLargeCountTwo RL.toRothParams (finrank K E) (R * finrank K E) δ ∧
      (∀ U ∈ T, U ≠ ⊤) ∧ ∀ x ∈ systemSet S w L C c, ∃ U ∈ T, x ∈ U :=
  exists_finset_submodule_of_isNormalizedSystem_of_large S w hwInf hwFin hN
    (exists_finset_submodule_of_systemThresholdTwo_le RL hcard S w hwInf hwFin hN)

open scoped Classical in
/-- **The threshold in two variables is linear in the height of the coefficients**: as
`NumberField.systemThreshold_le`, with the coefficient of `twoThreshold_le` in place of
`parametricCoeff`. -/
theorem systemThresholdTwo_le (RL : RothParams) (hcard : Fintype.card ι = 2)
    {S : Finset (HeightOneSpectrum (𝓞 K))} {w : AbsoluteValue K ℝ → AbsoluteValue E ℝ}
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) :
    systemThresholdTwo E S w L RL R H δ ≤
      max ((1 + rankCoeff (finrank ℚ E) 2 #(systemPlacesOver E S) (systemEps (finrank K E) δ)
          + penultimateCoeff RL (finrank ℚ E) 2 (Fintype.card (InfinitePlace E))
            #(systemPlacesOver E S) (R * finrank K E) 1 (2 * systemEps (finrank K E) δ)
            (systemAbsBound (finrank K E) (Fintype.card ι)))
          * ((Fintype.card (InfinitePlace E) + #(systemPlacesOver E S)) * Fintype.card ι ^ 2 *
              (finrank ℚ E * Real.log H) + Real.log |(discr E : ℝ)| +
            ∑ V ∈ systemPlacesOver E S, Real.log (Ideal.absNorm V.maximalIdeal.asIdeal : ℝ) + 1))
        (max (finrank ℚ K * (2 * Fintype.card ι / δ) * Real.log (Fintype.card ι))
          (systemHeightThreshold (Fintype.card ι) (finrank ℚ E)
            (Fintype.card (InfinitePlace K) + #S) δ H (Real.log (scalarConst K S)))) := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hδ := hN.delta_pos
  have he0 : (0 : ℝ) < finrank K E := by exact_mod_cast (finrank_pos : 0 < finrank K E)
  have hε : 0 < systemEps (finrank K E) δ := by rw [systemEps]; positivity
  have hA : 0 ≤ systemAbsBound (finrank K E) (Fintype.card ι) := by
    rw [systemAbsBound]; positivity
  refine max_le_max ?_ le_rfl
  refine (twoThreshold_le RL (linearIndependent_conjSystem_infinitePlace hwInf
    fun v ↦ hN.linearIndependent (.inl v))
    (fun V hV ↦ linearIndependent_conjSystem_systemPlacesOver hwFin
      (fun p hp ↦ hN.linearIndependent (.inr ⟨p, hp⟩)) hV) hcard (R * finrank K E) hε hA).trans ?_
  have h1 := rankCoeff_nonneg (finrank ℚ E) 2 #(systemPlacesOver E S) hε.le
  have h2 := penultimateCoeff_nonneg RL (finrank ℚ E) 2 (Fintype.card (InfinitePlace E))
    #(systemPlacesOver E S) (R * finrank K E) 1
    (by positivity : 0 < 2 * systemEps (finrank K E) δ) hA
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [thresholdScale]
  gcongr
  exact hN.formLogHeight_conjSystem_le hwInf hwFin

omit [IsGalois K E] in
/-- **The count in two variables with Evertse's Roth lemma, in closed form.** With at most `s`
distinct forms over `E` (`s = R e` for `R` forms of the system), `ℓ = 1 + log (4 s)` and
`Y = 449 / δ`,

`systemLargeCountTwo ≤ 2 + 2 ℓ Y² (1 + 5 log (32 ℓ Y³) / δ)`.

The intervals number at most `T ≤ 2 ℓ Y²`, their ratio is at most `16 T X ≤ 32 ℓ Y³`
(`four_mul_inv_evertseRatio_le`), and `log (1 + δ / 4) ≥ δ / 5`. The main term is
`O(δ⁻³ log s · log (δ⁻¹ log s))`: Bugeaud–Evertse's shape. -/
theorem systemLargeCountTwo_evertse_le (b : ℕ → ℝ) {e s : ℕ} (he : 1 ≤ e)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    systemLargeCountTwo (RothParams.evertse b) e s δ ≤
      2 + 2 * (1 + Real.log (4 * (s : ℝ))) * (449 / δ) ^ 2 *
        (1 + 5 * Real.log (32 * (1 + Real.log (4 * (s : ℝ))) * (449 / δ) ^ 3) / δ) := by
  set ε := 2 * systemEps e δ with hε
  set A := systemAbsBound e 2 with hA
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hε0 : 0 < ε := by rw [hε, systemEps]; positivity
  have hA0 : 0 ≤ A := by rw [hA, systemAbsBound]; positivity
  set X := evertseEtaInvBound 1 ε A with hX
  set T := evertseChainBound 1 s ε A with hT
  set Y : ℝ := 449 / δ with hY
  set ℓ : ℝ := 1 + Real.log (4 * (s : ℝ)) with hℓ
  have hℓ0 : 0 ≤ Real.log (4 * (s : ℝ)) := by
    have : (4 * (s : ℝ)) = ((4 * s : ℕ) : ℝ) := by push_cast; ring
    rw [this]; exact Real.log_natCast_nonneg _
  have hX1 : 1 ≤ X := one_le_evertseEtaInvBound 1 hε0 hA0
  -- `X ≤ Y`
  have hXY : X ≤ Y := by
    have hAe : A + 1 ≤ 7 * e := by
      rw [hA, systemAbsBound]
      push_cast
      linarith
    have h1 : 8 * ((1 : ℕ) + 1 : ℝ) ^ 2 * (A + 1) / ε ≤ 448 / δ := by
      rw [div_le_div_iff₀ hε0 hδ, hε, systemEps]
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hAe (by positivity : (0 : ℝ) ≤ δ)]
    have h2 : 1 ≤ 1 / δ := by
      rw [le_div_iff₀ hδ]; linarith
    rw [hX, evertseEtaInvBound, hY]
    have : (449 : ℝ) / δ = 448 / δ + 1 / δ := by ring
    rw [this]
    linarith
  have hY0 : 0 ≤ Y := by positivity
  -- `T ≤ 2 ℓ Y²`
  have hTY : T ≤ 2 * ℓ * Y ^ 2 := by
    rw [hT, evertseChainBound, hℓ]
    have : (2 * (((1 : ℕ) : ℝ) + 1) * (s : ℝ)) = 4 * s := by push_cast; ring
    rw [this]
    gcongr
  have hm : (subspaceChainLength 1 s ε A : ℝ) ≤ 2 * ℓ * Y ^ 2 := by
    have := subspaceChainLength_add_one_le 1 s hε0 hA0
    linarith
  -- the ratio
  have hσ0 : 0 < evertseRatio 1 s ε A := (RothParams.evertse b).ratio_pos hε0 hA0
  have hσ1 : evertseRatio 1 s ε A ≤ 1 := (RothParams.evertse b).ratio_le_one hε0 hA0
  have hρ1 : 1 ≤ 4 * (evertseRatio 1 s ε A)⁻¹ := by
    have : 1 ≤ (evertseRatio 1 s ε A)⁻¹ := (one_le_inv₀ hσ0).2 hσ1
    linarith
  have hρY : 4 * (evertseRatio 1 s ε A)⁻¹ ≤ 32 * ℓ * Y ^ 3 := by
    refine (four_mul_inv_evertseRatio_le 1 s hε0 hA0).trans ?_
    rw [← hT, ← hX]
    have hT0 : 0 ≤ T := (two_le_evertseChainBound 1 s hε0 hA0).trans' zero_le_two
    calc 16 * T * X ≤ 16 * (2 * ℓ * Y ^ 2) * Y := by gcongr
      _ = 32 * ℓ * Y ^ 3 := by ring
  have hlogρ : Real.log (4 * (evertseRatio 1 s ε A)⁻¹) ≤ Real.log (32 * ℓ * Y ^ 3) :=
    Real.log_le_log (by linarith) hρY
  have hlogρ0 : 0 ≤ Real.log (4 * (evertseRatio 1 s ε A)⁻¹) := Real.log_nonneg hρ1
  -- `log (1 + δ / 4) ≥ δ / 5`
  have hL : δ / 5 ≤ Real.log (1 + δ / (2 * 2)) := by
    refine le_trans ?_ (Real.one_sub_inv_le_log_of_pos (by positivity))
    rw [show (1 : ℝ) - (1 + δ / (2 * 2))⁻¹ = δ / (4 + δ) by field_simp; ring]
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    nlinarith
  have hW : 1 + Real.log (4 * (evertseRatio 1 s ε A)⁻¹) / Real.log (1 + δ / (2 * 2))
      ≤ 1 + 5 * Real.log (32 * ℓ * Y ^ 3) / δ := by
    have hδ5 : 0 < δ / 5 := by positivity
    have := div_le_div₀ (hlogρ0.trans hlogρ) hlogρ hδ5 hL
    rw [show Real.log (32 * ℓ * Y ^ 3) / (δ / 5) = 5 * Real.log (32 * ℓ * Y ^ 3) / δ by
      field_simp] at this
    linarith
  have hW0 : 0 ≤ 1 + Real.log (4 * (evertseRatio 1 s ε A)⁻¹) / Real.log (1 + δ / (2 * 2)) :=
    add_nonneg zero_le_one (div_nonneg hlogρ0 ((by positivity : (0 : ℝ) ≤ δ / 5).trans hL))
  rw [systemLargeCountTwo]
  change _ + _ * (1 + Real.log (4 * (evertseRatio 1 s ε A)⁻¹) / _) ≤ _
  refine add_le_add le_rfl ?_
  calc (subspaceChainLength 1 s ε A : ℝ) *
        (1 + Real.log (4 * (evertseRatio 1 s ε A)⁻¹) / Real.log (1 + δ / (2 * 2)))
      ≤ 2 * ℓ * Y ^ 2 * (1 + 5 * Real.log (32 * ℓ * Y ^ 3) / δ) :=
        mul_le_mul hm hW hW0 (by positivity)
    _ = _ := by rw [hℓ, hY]

/-- **The quantitative Subspace Theorem for a system in two variables, with Evertse's Roth
lemma** (Q1.6, Bugeaud–Evertse's case):
`NumberField.exists_finset_submodule_of_isNormalizedSystem_two` run with
`NumberField.SubspaceRoth.evertse`. Its large count is bounded in closed form by
`NumberField.systemLargeCountTwo_evertse_le`. -/
theorem exists_finset_submodule_of_isNormalizedSystem_two_evertse
    (Hm : ∀ m : ℕ, MultiprojectiveHeight (K := E) (Prod.fst : Fin m × Fin 2 → Fin m))
    (hcard : Fintype.card ι = 2)
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
            (systemThresholdTwo E S w L (RothParams.evertse fun m ↦ (Hm m).botBound 1) R H δ)) /
              Real.log (1 + δ / (2 * Fintype.card ι))) +
        systemLargeCountTwo (RothParams.evertse fun m ↦ (Hm m).botBound 1) (finrank K E)
          (R * finrank K E) δ ∧
      (∀ U ∈ T, U ≠ ⊤) ∧ ∀ x ∈ systemSet S w L C c, ∃ U ∈ T, x ∈ U :=
  exists_finset_submodule_of_isNormalizedSystem_two (SubspaceRoth.evertse.{u} Hm) hcard S w
    hwInf hwFin hN

end System

end NumberField
