/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.SystemSubspaceCount

/-!
# The quantitative Subspace Theorem for sets of systems with the same forms

`NumberField.exists_forall_mem_interval_systemSet` for a set `𝒩` of exponents of normalized
systems with common forms, constants and normalization. Each system has its own raised exponents
and its own scalar (`NumberField.exists_domain_of_shift`); one interval result for the set of all
their exponents over `E` then puts the large solutions of every system of `𝒩` into the same
`NS` proper subspaces of `Kⁿ` or the same `NI` height intervals. EF13's Theorem 2.3 for a set of
exponents (`NumberField.FormSystem.exists_intervals_cover_family`) supplies such an interval
result with counts independent of `𝒩`.

## Main results

* `NumberField.exists_forall_mem_interval_systemSet_family`: the large solutions of all systems of
  `𝒩` lie in `NS` subspaces or in `NI` height intervals.

## References

J.-H. Evertse, *On the Quantitative Subspace Theorem*, Zap. Nauchn. Sem. POMI **377** (2010),
217–240 (arXiv:1008.2268), proof of Theorem 2.1. J.-H. Evertse and R. G. Ferretti, *A further
improvement of the Quantitative Subspace Theorem*, Ann. of Math. **177** (2013), 513–590.
-/

@[expose] public section

open Finset Module NumberField IsDedekindDomain Height

universe u

namespace NumberField

variable {K E : Type*} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
variable {ι : Type u} [Fintype ι]

open scoped Classical in
/-- **The large solutions of a set of systems with the same forms lie in `NS` subspaces or in `NI`
height intervals**: `NumberField.exists_forall_mem_interval_systemSet` for a set `𝒩` of exponents
`c` of normalized systems with common forms, constants and normalization, from one interval result
for the whole set of exponents over `E` that the systems give. The subspaces and the intervals are
the same for all `c ∈ 𝒩`. -/
theorem exists_forall_mem_interval_systemSet_family [IsGalois K E]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (w : AbsoluteValue K ℝ → AbsoluteValue E ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)} {C : InfinitePlace K ⊕ S → ℝ} {H : ℝ}
    {D R : ℕ} {δ : ℝ} (𝒩 : Set (InfinitePlace K ⊕ S → ι → ℝ))
    (hN : ∀ c ∈ 𝒩, IsNormalizedSystem S w L C c H D R δ) {X₀ ρ : ℝ} {NS NI : ℕ}
    (hX₀H : systemHeightThreshold (Fintype.card ι) (finrank ℚ E)
      (Fintype.card (InfinitePlace K) + #S) δ H (Real.log (scalarConst K S)) ≤ X₀)
    (hX₀n : finrank ℚ K * (2 * Fintype.card ι / δ) * Real.log (Fintype.card ι) ≤ X₀)
    (hint : ∀ 𝒞' : Set (AbsoluteValue E ℝ → ι → ℝ),
      (∀ c' ∈ 𝒞', approxWeight (systemPlacesOver E S) c' ≤ -systemEps (finrank K E) δ) →
      (∀ c' ∈ 𝒞', approxAbsWeight (systemPlacesOver E S) c' ≤
        systemAbsBound (finrank K E) (Fintype.card ι)) →
      (∀ c' ∈ 𝒞', approxWeight (systemPlacesOver E S) c' = -(finrank K E * δ / 2)) →
      (∀ c' ∈ 𝒞', approxSupWeight (systemPlacesOver E S) c' ≤
        finrank K E * (1 + δ / (2 * Fintype.card ι))) →
      ∃ T : Finset (Submodule E (ι → E)), #T ≤ NS ∧ (∀ W ∈ T, W ≠ ⊤) ∧
        ∃ 𝒯 : Finset ℝ, #𝒯 ≤ NI ∧ (∀ s ∈ 𝒯, X₀ ≤ s) ∧
          ∀ c' ∈ 𝒞', ∀ Q : ℝ, 1 < Q → X₀ ≤ Real.log Q →
            (∃ W ∈ T, approxDomain (systemPlacesOver E S)
              (conjSystem univ (S.image FinitePlace.mk) w L) c' Q ⊆ W) ∨
              ∃ s ∈ 𝒯, s ≤ Real.log Q ∧ Real.log Q < ρ * s) :
    ∃ T : Finset (Submodule K (ι → K)), #T ≤ NS ∧ (∀ U ∈ T, U ≠ ⊤) ∧
      ∃ 𝒯 : Finset ℝ, #𝒯 ≤ NI ∧ (∀ s ∈ 𝒯, X₀ ≤ s) ∧
        ∀ c ∈ 𝒩, ∀ x ∈ systemSet S w L C c, X₀ ≤ Real.log (mulHeightAff x) →
          (∃ U ∈ T, x ∈ U) ∨
            ∃ s ∈ 𝒯, s ≤ Real.log (mulHeightAff x) ∧ Real.log (mulHeightAff x) < ρ * s := by
  have key : ∀ c ∈ 𝒩, ∃ (e' : InfinitePlace K ⊕ S → ι → ℝ) (β : K), β ≠ 0 ∧
      approxWeight (systemPlacesOver E S) (conjExponent S e') ≤ -systemEps (finrank K E) δ ∧
      approxAbsWeight (systemPlacesOver E S) (conjExponent S e') ≤
        systemAbsBound (finrank K E) (Fintype.card ι) ∧
      approxWeight (systemPlacesOver E S) (conjExponent S e') = -(finrank K E * δ / 2) ∧
      approxSupWeight (systemPlacesOver E S) (conjExponent S e') ≤
        finrank K E * (1 + δ / (2 * Fintype.card ι)) ∧
      ∀ x ∈ systemSet S w L C c, X₀ ≤ Real.log (mulHeightAff x) →
        (fun j ↦ algebraMap K E (β * x j)) ∈ approxDomain (systemPlacesOver E S)
          (conjSystem univ (S.image FinitePlace.mk) w L) (conjExponent S e') (mulHeightAff x) := by
    intro c hc
    have hNc := hN c hc
    have hδ := hNc.delta_pos
    have hδ1 := hNc.delta_le_one
    have he0 : (0 : ℝ) < finrank K E := by exact_mod_cast (finrank_pos : 0 < finrank K E)
    have hn0 : (0 : ℝ) < Fintype.card ι := by exact_mod_cast (by have := hNc.two_le_card; omega)
    have hP := hNc.systemPosWeight_le
    obtain ⟨e', β, hβ0, hw, hA, hsup, -, hdom⟩ :=
      exists_domain_of_shift S w hwInf hwFin hNc (τ := 1 / 2) (by norm_num) (by linarith) hX₀n
    refine ⟨e', β, hβ0, ?_, ?_, ?_, ?_, hdom⟩
    · rw [hw, systemEps]; nlinarith
    · refine hA.trans ?_
      rw [systemAbsBound]
      exact mul_le_mul_of_nonneg_left (by nlinarith) he0.le
    · rw [hw]; ring
    · refine hsup.trans_eq ?_
      congr 1
      field_simp
  choose! e' β hβ0 hw1 hw2 hw3 hw4 hdom using key
  obtain ⟨T, hTcard, hTtop, 𝒯, h𝒯card, h𝒯ge, hQint⟩ :=
    hint ((fun c ↦ conjExponent S (e' c)) '' 𝒩) (by rintro _ ⟨c, hc, rfl⟩; exact hw1 c hc)
      (by rintro _ ⟨c, hc, rfl⟩; exact hw2 c hc) (by rintro _ ⟨c, hc, rfl⟩; exact hw3 c hc)
      (by rintro _ ⟨c, hc, rfl⟩; exact hw4 c hc)
  refine ⟨T.image fun W ↦ (W.restrictScalars K).comap (algebraMapPi K E ι),
    Finset.card_image_le.trans hTcard, fun U hU ↦ ?_, 𝒯, h𝒯card, h𝒯ge, fun c hc x hx hlogH ↦ ?_⟩
  · obtain ⟨W, hW, rfl⟩ := Finset.mem_image.1 hU
    exact comap_algebraMapPi_ne_top (hTtop W hW)
  have hn2 : 2 ≤ Fintype.card ι := (hN c hc).two_le_card
  have hn0 : (0 : ℝ) < Fintype.card ι := by exact_mod_cast (by omega : 0 < Fintype.card ι)
  have hδ := (hN c hc).delta_pos
  have hX₀pos : 0 < X₀ := by
    have hl : 0 < Real.log (Fintype.card ι) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < Fintype.card ι))
    have hK : (0 : ℝ) < finrank ℚ K := by exact_mod_cast finrank_pos
    exact (by positivity : (0 : ℝ) < finrank ℚ K * (2 * Fintype.card ι / δ) *
      Real.log (Fintype.card ι)).trans_le hX₀n
  have hH1 : 1 < mulHeightAff x := by
    rw [← Real.log_pos_iff (mulHeightAff_pos x).le]
    linarith
  rcases hQint _ ⟨c, hc, rfl⟩ (mulHeightAff x) hH1 hlogH with ⟨W, hW, hsub⟩ | hs
  · exact Or.inl ⟨_, Finset.mem_image_of_mem _ hW,
      mem_comap_algebraMapPi_of_mul (hβ0 c hc) (hsub (hdom c hc x hx hlogH))⟩
  · exact Or.inr hs

end NumberField
