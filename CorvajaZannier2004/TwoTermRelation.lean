/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.SInteger

-- Used only inside proofs.
import DiophantineApproximation.NormForm

/-!
# Lemma 2 of Corvaja–Zannier: a vanishing sum of conjugates degenerates to two terms

**Lemma 2** (Corvaja–Zannier 2004, p. 4). Let `σ₁, …, σₙ` be automorphisms of a number field `K`
and `a₁, …, aₙ` nonzero elements of `K`. If infinitely many `S`-units `u` satisfy
`a₁ σ₁(u) + ⋯ + aₙ σₙ(u) = 0`, then there are indices `i ≠ j` and nonzero `a, b ∈ K` such that
`a σᵢ(u) + b σⱼ(u) = 0` for infinitely many of them.

The paper cites Schmidt's book for it; here it is the homogeneous unit equation of Layer 8.6
(`NumberField.exists_finite_forall_exists_div_mem`, Bombieri–Gubler Corollary 7.4.3) and a
pigeonhole over the finitely many pairs `(i, c)` of an index and a ratio.

## Main results

* `NumberField.exists_ne_infinite_setOf_add_eq_zero`: Lemma 2, for any family `y` of `S`-unit
  valued functions in place of the conjugates `u ↦ σᵢ(u)`.
* `NumberField.exists_ne_infinite_setOf_algEquiv_add_eq_zero`: Lemma 2 as stated, with
  automorphisms.

## Implementation notes

⚠ **The automorphisms play no role.** The proof sees only that the `n` quantities `σᵢ(u)` are
`S`-units, so the general form is stated for arbitrary `S`-unit valued `y i u`, and the paper's
form is its instance. Distinctness of the `σᵢ` is not needed either.

⚠ **`n ≥ 1` is needed** (`[Nonempty ι]`): for `n = 0` the equation holds for every `u` and there
are no two indices.
-/

@[expose] public section

open IsDedekindDomain

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [Nonempty ι]

/-- **Lemma 2 of Corvaja–Zannier, for any `S`-unit valued family.** If infinitely many `u ∈ Ξ`
satisfy `∑ i, a i * y i u = 0` with all `a i ≠ 0` and all `y i u` `S`-units, then two distinct
indices carry a two-term relation `a' * y i u + b' * y j u = 0`, with `a', b' ≠ 0`, for
infinitely many `u ∈ Ξ`. -/
theorem exists_ne_infinite_setOf_add_eq_zero {α : Type*} (S : Finset (HeightOneSpectrum (𝓞 K)))
    (y : ι → α → Kˣ) (a : ι → K) (ha : ∀ i, a i ≠ 0) {Ξ : Set α} (hΞ : Ξ.Infinite)
    (hS : ∀ u ∈ Ξ, ∀ i, y i u ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K)
    (hsum : ∀ u ∈ Ξ, ∑ i, a i * y i u = 0) :
    ∃ i j, i ≠ j ∧ ∃ a' b' : K, a' ≠ 0 ∧ b' ≠ 0 ∧
      {u ∈ Ξ | a' * y i u + b' * y j u = 0}.Infinite := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨Φ, hΦ, hmem⟩ := exists_finite_forall_exists_div_mem S a (ha i₀)
  -- every solution has some ratio `y i u / y i₀ u` in `Φ`
  have hcover : Ξ ⊆ ⋃ p ∈ (Set.univ : Set ι) ×ˢ Φ,
      {u ∈ Ξ | ((y p.1 u : Kˣ) : K) / y i₀ u = p.2 ∧ p.1 ≠ i₀} := by
    intro u hu
    obtain ⟨i, hi, -, hc⟩ := hmem (fun i ↦ y i u) (hS u hu) (hsum u hu)
    exact Set.mem_biUnion (x := (i, _)) ⟨trivial, hc⟩ ⟨hu, rfl, hi⟩
  -- so one of the finitely many fibres is infinite
  obtain ⟨⟨i, c⟩, -, hinf⟩ : ∃ p ∈ (Set.univ : Set ι) ×ˢ Φ,
      {u ∈ Ξ | ((y p.1 u : Kˣ) : K) / y i₀ u = p.2 ∧ p.1 ≠ i₀}.Infinite := by
    by_contra h
    push Not at h
    exact hΞ (((Set.finite_univ.prod hΦ).biUnion fun p hp ↦ h p hp).subset hcover)
  obtain ⟨u₀, ⟨-, hu₀, hi⟩⟩ := hinf.nonempty
  dsimp only at hu₀ hi hinf
  have hc0 : c ≠ 0 := by rw [← hu₀]; exact div_ne_zero (Units.ne_zero _) (Units.ne_zero _)
  refine ⟨i, i₀, hi, 1, -c, one_ne_zero, neg_ne_zero.mpr hc0, hinf.mono fun u hu ↦ ⟨hu.1, ?_⟩⟩
  have h := hu.2.1
  rw [div_eq_iff (Units.ne_zero _)] at h
  rw [h]
  ring

/-- **Lemma 2 of Corvaja–Zannier** (p. 4). Let `σ : ι → Gal(K/ℚ)` and `a i ≠ 0`. If infinitely
many `u ∈ Ξ`, all of whose conjugates `σ i u` are `S`-units, satisfy
`∑ i, a i * σ i u = 0`, then there are `i ≠ j` and nonzero `a', b'` with
`a' * σ i u + b' * σ j u = 0` for infinitely many `u ∈ Ξ`. -/
theorem exists_ne_infinite_setOf_algEquiv_add_eq_zero (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : ι → K ≃ₐ[ℚ] K) (a : ι → K) (ha : ∀ i, a i ≠ 0) {Ξ : Set Kˣ} (hΞ : Ξ.Infinite)
    (hS : ∀ u ∈ Ξ, ∀ i, Units.map (σ i : K →* K) u ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K)
    (hsum : ∀ u ∈ Ξ, ∑ i, a i * σ i (u : K) = 0) :
    ∃ i j, i ≠ j ∧ ∃ a' b' : K, a' ≠ 0 ∧ b' ≠ 0 ∧
      {u ∈ Ξ | a' * σ i (u : K) + b' * σ j (u : K) = 0}.Infinite :=
  exists_ne_infinite_setOf_add_eq_zero S (fun i u ↦ Units.map (σ i : K →* K) u) a ha hΞ hS hsum

end NumberField
