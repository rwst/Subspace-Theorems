/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.NumberTheory.Height.ResultantHeight
public import ForMathlib.RingTheory.MvPolynomial.ResultantLinear
public import ForMathlib.RingTheory.MvPolynomial.ResultantReindex

/-!
# Heights of resultant forms: reindexing and components

* `MvPolynomial.gaussHeight_resForm_comp`: the height of `α res_d(I)` does not depend on the
  numbering of the generic forms.
* `MvPolynomial.gaussHeight_resForm_linIndex_congr`: for generic linear forms, it only depends on
  the number of forms in each block.
* `MvPolynomial.exists_gaussHeight_resForm_eq_sum`: **Rémond's Thm 3.3 for heights**,
  `h(α res_d(I)) = ∑_𝔭 ℓ_𝔭(I) h(α res_d(𝔭))` over the components of `I` of dimension `r - 1`.
-/

@[expose] public section

open Finset Height

namespace MvPolynomial

universe u

variable {σ ι : Type u} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι}
  {K : Type u} [Field K] [AdmissibleAbsValues K] {κ κ' : Type u} [Fintype κ] [Fintype κ']

/-- Heights of resultant forms do not depend on the numbering of the generic forms. -/
theorem gaussHeight_resForm_comp (hK : ArchEmbedded K) (f : κ' ≃ κ) (d : κ → ι → ℕ)
    (hb : Function.Surjective b) {I : Ideal (MvPolynomial σ K)}
    (hI : I.IsWeightedHomogeneous (multiWeight b))
    (hdim : (hilbertPoly b I).totalDegree + 1 ≤ Nat.card κ) :
    gaussHeight remodelWeight (resForm b K (d ∘ f) I) =
      gaussHeight remodelWeight (resForm b K d I) := by
  rw [← gaussHeight_of_associated hK remodelWeight_ne_zero
    (associated_reindexEquiv_resForm f d hb hI hdim)]
  have h : reindexEquiv b K f d (resForm b K (d ∘ f) I) =
      rename (Equiv.sigmaCongrLeft f (β := fun l ↦ blockMonomials b (d l)))
        (resForm b K (d ∘ f) I) := rfl
  have hw : ∀ v : GenericVar b (d ∘ f), remodelWeight (b := b) (d := d)
      (Equiv.sigmaCongrLeft f (β := fun l ↦ blockMonomials b (d l)) v) = remodelWeight v := by
    intro v
    unfold remodelWeight
    rfl
  rw [h]
  exact (gaussHeight_rename _ hw _).symm

/-- For generic linear forms, heights of resultant forms only depend on the number of forms in
each block. -/
theorem gaussHeight_resForm_linIndex_congr (hK : ArchEmbedded K) {τ : κ → ι} {τ' : κ' → ι}
    (h : formCount τ univ = formCount τ' univ) (hb : Function.Surjective b)
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsWeightedHomogeneous (multiWeight b))
    (hdim : (hilbertPoly b I).totalDegree + 1 ≤ Fintype.card κ) :
    gaussHeight remodelWeight (resForm b K (linIndex τ') I) =
      gaussHeight remodelWeight (resForm b K (linIndex τ) I) := by
  classical
  have hfib : ∀ i, {l' // τ' l' = i} ≃ {l // τ l = i} := fun i ↦ Fintype.equivOfCardEq (by
    rw [Fintype.card_subtype, Fintype.card_subtype, ← formCount_apply, ← formCount_apply, h])
  have hf : linIndex τ ∘ Equiv.ofFiberEquiv hfib = linIndex τ' := funext fun l' ↦ by
    simp only [Function.comp_apply, linIndex, Equiv.ofFiberEquiv_map]
  rw [← hf]
  exact gaussHeight_resForm_comp hK _ _ hb hI (by rwa [Nat.card_eq_fintype_card])

/-- **Rémond's Thm 3.3 for heights**: `h(α res_d(I)) = ∑_𝔭 ℓ_𝔭(I) h(α res_d(𝔭))`, over the
relevant multihomogeneous primes `𝔭 ⊇ I` with `deg H_𝔭 = r - 1`. -/
theorem exists_gaussHeight_resForm_eq_sum (hK : ArchEmbedded K) (d : κ → ι → ℕ)
    (hb : Function.Surjective b) {I : Ideal (MvPolynomial σ K)}
    (hI : I.IsWeightedHomogeneous (multiWeight b))
    (hdim : (hilbertPoly b I).totalDegree + 1 ≤ Nat.card κ) :
    ∃ (S : Finset (Ideal (MvPolynomial σ K))) (ℓ : Ideal (MvPolynomial σ K) → ℕ),
      (∀ 𝔭, 𝔭 ∈ S ↔ 𝔭.IsPrime ∧ 𝔭.IsWeightedHomogeneous (multiWeight b) ∧ I ≤ 𝔭 ∧
        ¬irrelevantIdeal K b ≤ 𝔭 ∧ (hilbertPoly b 𝔭).totalDegree + 1 = Nat.card κ) ∧
      (∀ 𝔭 ∈ S, ∀ [𝔭.IsPrime], Ideal.localLength 𝔭 I = ℓ 𝔭) ∧
      gaussHeight remodelWeight (resForm b K d I) =
        ∑ 𝔭 ∈ S, (ℓ 𝔭 : ℝ) * gaussHeight remodelWeight (resForm b K d 𝔭) := by
  obtain ⟨-, S, ℓ, hS, hℓ, hassoc⟩ := associated_resForm_prod (d := d) hb hI hdim
  have hne : ∀ 𝔭 ∈ S, resForm b K d 𝔭 ≠ 0 := fun 𝔭 h𝔭 ↦ by
    obtain ⟨_, h𝔭h, -, -, h𝔭d⟩ := (hS 𝔭).mp h𝔭
    exact resForm_ne_zero hb h𝔭h h𝔭d.le
  refine ⟨S, ℓ, hS, hℓ, ?_⟩
  rw [gaussHeight_of_associated hK remodelWeight_ne_zero hassoc,
    gaussHeight_prod hK remodelWeight_ne_zero _ fun 𝔭 h𝔭 ↦ pow_ne_zero _ (hne 𝔭 h𝔭)]
  exact sum_congr rfl fun 𝔭 h𝔭 ↦ gaussHeight_pow hK remodelWeight_ne_zero (hne 𝔭 h𝔭) _

end MvPolynomial
