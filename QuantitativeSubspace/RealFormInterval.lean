/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.RealFormCount

/-!
# The quantitative Subspace Theorem for real forms, in interval form

For the systems of `QuantitativeSubspace/RealFormCount.lean` (forms in `1, α, α²` at `∞`, the
coordinates at the primes of a finite set `S`, integer points), the count of Evertse–Ferretti
before the gap principle: the solutions above the threshold lie in **one** proper subspace `U`,
or `log |x|` lies in one of at most `K δ⁻² (1 + log δ⁻¹)` intervals `[s, K δ⁻¹ s)`
(`Real.SubspaceIntervalWith α S n K`). This is EF13's Theorem 3.3 for the system: the exceptional
subspace of the parametric theorem and its `m₀ ≍ δ⁻² log δ⁻¹` intervals of ratio
`ω₀ ≍ δ⁻¹ log δ⁻¹` (`NumberField.exists_forall_mem_interval_of_efSystemThreshold_le`).

`Real.SubspaceBoundWith α S 3 n K` counts each interval with the gap principle, which costs
`log ω₀ / log (1 + δ / 2n) ≍ δ⁻¹ log δ⁻¹` subspaces per interval. Solutions whose logarithmic
heights grow geometrically, `log |x_{m+1}| ≥ λ log |x_m|` with `λ > 1`, put only
`log ω₀ / log λ + 1` points into an interval (`Real.card_le_of_forall_mem_window`). For them the
interval form saves a whole power of `δ⁻¹`: outside `U` there are `O(δ⁻² (1 + log δ⁻¹)²)` of
them. The applications of Bugeaud–Evertse type (integer bases, continued fractions, the steering
word of `(3/2)^n`) use doubling sequences of this kind.

## Main definitions

* `Real.SubspaceIntervalWith α S n K`, `Real.SubspaceIntervalAt α S`: the interval form.
* `Real.efIntervalConst n M`, `Real.efRatioConst n M`: EF13's constants for the number of
  intervals and for their ratio, at `M` forms and coordinates; `Real.efIntervalConstAt n M a`
  the first at `δ' ≥ δ / a`.
* `Real.intervalConst n d s h μ`: the constant of the interval form, in the variables of
  `Real.subspaceConst`.

## Main results

* `Real.intervalCount_le_of_inv_le`: the closed form
  `intervalCount n M δ' ≤ efIntervalConstAt n M a δ⁻² (1 + log δ⁻¹)` whenever `δ'⁻¹ ≤ a δ⁻¹`.
* `Real.intervalCount_half_le`, `Real.cutRatio_half_le`: the closed forms
  `intervalCount ≤ efIntervalConst n M δ⁻² (1 + log δ⁻¹)` and `ω₀ ≤ efRatioConst n M δ⁻¹`.
* `Real.subspaceIntervalWith_of_mem`: **the interval form of Evertse–Ferretti 2013, with an
  explicit constant**, for `2 ≤ n ≤ 4` and every Galois field `E ⊆ ℂ` containing `α`.
* `Real.subspaceIntervalAt_of_isAlgebraic`: the interval form for every real algebraic `α`.
* `Real.subspaceIntervalWith_ratCast`, `Real.subspaceIntervalWith_zero`: the case `α ∈ ℚ`.

## References

J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative Subspace Theorem*,
Ann. of Math. **177** (2013), 513–590, Theorem 3.3 and §21.
-/

@[expose] public section

open Module Finset Height NumberField IsDedekindDomain

namespace Real

/-- **The interval form of `Real.SubspaceBoundWith`**: for the same data, there are one proper
subspace `U` of `ℚⁿ` and at most `K δ⁻² (1 + log δ⁻¹)` reals `s` such that every solution `x`
above the threshold `K δ⁻¹ (1 + log B + log C + log γ⁻¹)` lies in `U` or has
`s ≤ log |x| < K δ⁻¹ s` for one of them. Solutions whose logarithmic heights grow geometrically
put `O(log (K δ⁻¹))` points into each interval (`Real.card_le_of_forall_mem_window`), so they lie
in `U` up to `O(δ⁻² (1 + log δ⁻¹)²)` points: one power of `δ⁻¹` less than
`Real.SubspaceBoundWith α S 3 n K` gives for the number of subspaces. -/
def SubspaceIntervalWith (α : ℝ) (S : Finset Nat.Primes) (n : ℕ) (K : ℝ) : Prop :=
  ∀ (P : Fin n → Fin n → Fin 3 → ℤ) (B : ℝ), 1 ≤ B → (∀ i k m, |(P i k m : ℝ)| ≤ B) →
    ∀ γ : ℝ, 0 < γ → γ ≤ 1 → γ ≤ |(Matrix.of fun i k ↦ quadVal α (P i k)).det| →
    ∀ C : ℝ, 1 ≤ C → ∀ (e : Fin n → ℝ) (f : Nat.Primes → Fin n → ℝ) (δ : ℝ), 0 < δ → δ ≤ 1 →
      (∀ i, e i ≤ 1) → (∃ i, e i = 1) → (∃ i, e i ≤ 1 - δ / (2 * n)) →
      (∀ l ∈ S, ∀ i, f l i ≤ 0) → (∀ l ∈ S, ∃ i, f l i = 0) →
      ∑ i, e i + ∑ l ∈ S, ∑ i, f l i ≤ -δ →
    ∃ U : Submodule ℚ (Fin n → ℚ), U ≠ ⊤ ∧
      ∃ 𝒯 : Finset ℝ, (#𝒯 : ℝ) ≤ K * δ⁻¹ ^ 2 * (1 + log δ⁻¹) ∧
      ∀ x : Fin n → ℤ, x ≠ 0 →
        (∀ i, |∑ k, quadVal α (P i k) * x k| ≤ C * (⨆ k, |(x k : ℝ)|) ^ e i) →
        (∀ l ∈ S, ∀ i, ((padicNorm (l : ℕ) (x i : ℚ) : ℚ) : ℝ) ≤ (⨆ k, |(x k : ℝ)|) ^ f l i) →
        K * δ⁻¹ * (1 + log B + log C + log γ⁻¹) ≤ log (⨆ k, |(x k : ℝ)|) →
        (fun k ↦ (x k : ℚ)) ∈ U ∨
          ∃ s ∈ 𝒯, s ≤ log (⨆ k, |(x k : ℝ)|) ∧ log (⨆ k, |(x k : ℝ)|) < K * δ⁻¹ * s

/-- **The interval form for forms in `1, α, α²` at `∞` and the primes of `S`**:
`Real.SubspaceIntervalWith α S n K` for `2 ≤ n ≤ 4` and some `K ≥ 1`, which depends on `α`, `S`
and `n` only. -/
def SubspaceIntervalAt (α : ℝ) (S : Finset Nat.Primes) : Prop :=
  ∀ n : ℕ, 2 ≤ n → n ≤ 4 → ∃ K : ℝ, 1 ≤ K ∧ SubspaceIntervalWith α S n K

/-- A larger constant is a weaker statement. -/
theorem SubspaceIntervalWith.mono_const {α K K' : ℝ} {S : Finset Nat.Primes} {n : ℕ}
    (h : SubspaceIntervalWith α S n K) (hK : 0 ≤ K) (hKK : K ≤ K') :
    SubspaceIntervalWith α S n K' := by
  intro P B hB hP γ hγ hγ1 hdet C hC e f δ hδ hδ1 he1 he he0 hf hf0 hsum
  obtain ⟨U, hU, 𝒯, hcard, hmem⟩ :=
    h P B hB hP γ hγ hγ1 hdet C hC e f δ hδ hδ1 he1 he he0 hf hf0 hsum
  have hδi : 0 < δ⁻¹ := inv_pos.2 hδ
  have hl : 0 ≤ log δ⁻¹ := Real.log_nonneg ((one_le_inv₀ hδ).2 hδ1)
  refine ⟨U, hU, 𝒯, hcard.trans (by gcongr), fun x hx hsol hfin hlarge ↦ ?_⟩
  have hΞ : 0 ≤ δ⁻¹ * (1 + log B + log C + log γ⁻¹) := by
    have := Real.log_nonneg hB
    have := Real.log_nonneg hC
    have := Real.log_nonneg ((one_le_inv₀ hγ).2 hγ1)
    positivity
  have hlarge' : K * δ⁻¹ * (1 + log B + log C + log γ⁻¹) ≤ log (⨆ k, |(x k : ℝ)|) := by
    refine le_trans ?_ hlarge
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right hKK hΞ
  rcases hmem x hx hsol hfin hlarge' with hU | ⟨s, hs, h1, h2⟩
  · exact .inl hU
  refine .inr ⟨s, hs, h1, h2.trans_le ?_⟩
  have hX : 0 ≤ log (⨆ k, |(x k : ℝ)|) := by
    refine Real.log_nonneg ?_
    rw [← Height.mulHeightAff_intCast hx]
    exact one_le_mulHeightAff _
  have hs0 : 0 ≤ s := by
    by_contra hs0
    push Not at hs0
    nlinarith [mul_nonneg hK hδi.le]
  have : 0 ≤ δ⁻¹ * s := by positivity
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_right hKK this


/-- **The constant of EF13's number of intervals**, for `n` variables and `R' = M` forms and
coordinates: `60 n (n + 3) (9216000 n¹⁰ 4ⁿ (log (768 n² M) + 1) + 2)`. -/
noncomputable def efIntervalConst (n M : ℕ) : ℝ :=
  60 * n * (n + 3) * (9216000 * n ^ 10 * 4 ^ n * (Real.log (768 * n ^ 2 * M) + 1) + 2)

/-- **The constant of EF13's number of intervals at `δ' ≥ δ / a`**, for `n` variables and `M`
forms and coordinates: `60 n (n + 3) (64000 n⁸ 4ⁿ a² (log (64 n M a) + 1) + 2)`. -/
noncomputable def efIntervalConstAt (n M : ℕ) (a : ℝ) : ℝ :=
  60 * n * (n + 3) * (64000 * n ^ 8 * 4 ^ n * a ^ 2 * (Real.log (64 * n * M * a) + 1) + 2)

/-- **EF13's number of intervals in closed form**: if `δ'⁻¹ ≤ a δ⁻¹`, `a ≥ 1`, then
`intervalCount n M δ' ≤ efIntervalConstAt n M a δ⁻² (1 + log δ⁻¹)`. -/
theorem intervalCount_le_of_inv_le {n M : ℕ} (hn : 2 ≤ n) (hM : 2 ≤ M) {δ δ' a : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδ'0 : 0 < δ') (hδ'1 : δ' ≤ 1) (ha : 1 ≤ a)
    (hinv : δ'⁻¹ ≤ a * δ⁻¹) :
    (FormSystem.intervalCount n M δ' : ℝ) ≤ efIntervalConstAt n M a * δ⁻¹ ^ 2 * (1 + log δ⁻¹) := by
  have hN : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hM1 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hδi : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).2 hδ1
  have hl : 0 ≤ log δ⁻¹ := Real.log_nonneg hδi
  have hinv0 : 0 < δ'⁻¹ := inv_pos.2 hδ'0
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  set L := Real.log (64 * n * M * a) with hL
  have h64 : (1 : ℝ) ≤ 64 * n * M := by nlinarith
  have hL0 : 0 ≤ L := Real.log_nonneg (one_le_mul_of_one_le_of_one_le h64 ha)
  -- the logarithm
  have hlog : Real.log (64 * n * M / δ') ≤ (L + 1) * (1 + log δ⁻¹) := by
    have e : 64 * (n : ℝ) * M / δ' = 64 * n * M * δ'⁻¹ := div_eq_mul_inv _ _
    have h1 : Real.log (64 * n * M * δ'⁻¹) ≤ Real.log (64 * n * M * (a * δ⁻¹)) :=
      Real.log_le_log (by positivity) (by gcongr)
    have e2 : 64 * (n : ℝ) * M * (a * δ⁻¹) = 64 * n * M * a * δ⁻¹ := by ring
    rw [e2, Real.log_mul (x := 64 * (n : ℝ) * M * a) (by positivity) (by positivity), ← hL]
      at h1
    rw [e]
    nlinarith [mul_nonneg hL0 hl]
  -- the number of blocks
  have hsq : (1 : ℝ) / δ' ^ 2 ≤ a ^ 2 * δ⁻¹ ^ 2 := by
    rw [one_div, ← inv_pow]
    calc δ'⁻¹ ^ 2 ≤ (a * δ⁻¹) ^ 2 := pow_le_pow_left₀ hinv0.le hinv 2
      _ = a ^ 2 * δ⁻¹ ^ 2 := by ring
  have hX1 : 1 ≤ δ⁻¹ ^ 2 * (1 + log δ⁻¹) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hδi) (by linarith)
  have hchain : FormSystem.chainBound n M δ' ≤
      (64000 * n ^ 8 * 4 ^ n * a ^ 2 * (L + 1) + 2) * (δ⁻¹ ^ 2 * (1 + log δ⁻¹)) := by
    rw [FormSystem.chainBound]
    have hlog0 : 0 ≤ Real.log (64 * n * M / δ') :=
      Real.log_nonneg ((one_le_div hδ'0).2 (by nlinarith))
    have : 64000 * (n : ℝ) ^ 8 * 4 ^ n / δ' ^ 2 * Real.log (64 * n * M / δ') ≤
        64000 * n ^ 8 * 4 ^ n * (a ^ 2 * δ⁻¹ ^ 2) * ((L + 1) * (1 + log δ⁻¹)) := by
      rw [div_eq_mul_one_div (64000 * (n : ℝ) ^ 8 * 4 ^ n)]
      gcongr
    have e : 64000 * (n : ℝ) ^ 8 * 4 ^ n * (a ^ 2 * δ⁻¹ ^ 2) * ((L + 1) * (1 + log δ⁻¹)) =
        64000 * n ^ 8 * 4 ^ n * a ^ 2 * (L + 1) * (δ⁻¹ ^ 2 * (1 + log δ⁻¹)) := by ring
    nlinarith
  calc (FormSystem.intervalCount n M δ' : ℝ) ≤ 60 * n * (n + 3) * FormSystem.chainBound n M δ' :=
        FormSystem.intervalCount_le hn hM hδ'0 hδ'1
    _ ≤ 60 * n * (n + 3) *
        ((64000 * n ^ 8 * 4 ^ n * a ^ 2 * (L + 1) + 2) * (δ⁻¹ ^ 2 * (1 + log δ⁻¹))) := by gcongr
    _ = efIntervalConstAt n M a * δ⁻¹ ^ 2 * (1 + log δ⁻¹) := by rw [efIntervalConstAt, ← hL]; ring

/-- **EF13's number of intervals in closed form**, at `δ / 2`:
`intervalCount n M δ' ≤ efIntervalConst n M δ⁻² (1 + log δ⁻¹)`, `δ' = efSystemDelta n (δ / 2)`. -/
theorem intervalCount_half_le {n M : ℕ} (hn : 2 ≤ n) (hM : 2 ≤ M) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) :
    (FormSystem.intervalCount n M (efSystemDelta n (δ / 2)) : ℝ) ≤
      efIntervalConst n M * δ⁻¹ ^ 2 * (1 + log δ⁻¹) := by
  have hδ2 : 0 < δ / 2 := by positivity
  have hN : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hinv : (efSystemDelta n (δ / 2))⁻¹ ≤ 12 * n * δ⁻¹ := by
    refine (inv_efSystemDelta_le hn hδ2 (by linarith)).trans_eq ?_
    field_simp
    ring
  refine (intervalCount_le_of_inv_le hn hM hδ hδ1 (efSystemDelta_pos hδ2)
    (efSystemDelta_le_one n hδ2) (by linarith) hinv).trans_eq ?_
  have e : 64 * (n : ℝ) * M * (12 * n) = 768 * n ^ 2 * M := by ring
  rw [efIntervalConstAt, efIntervalConst, e]
  ring

/-- **The constant of EF13's interval ratio**: `12 n log 3M`. -/
noncomputable def efRatioConst (n M : ℕ) : ℝ := 12 * n * Real.log (3 * M)

/-- **EF13's interval ratio in closed form**, at `δ / 2`:
`ω₀ = cutRatio M δ' ≤ efRatioConst n M δ⁻¹`, `δ' = efSystemDelta n (δ / 2)`. -/
theorem cutRatio_half_le {n M : ℕ} (hn : 2 ≤ n) (hM : 1 ≤ M) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) :
    FormSystem.cutRatio M (efSystemDelta n (δ / 2)) ≤ efRatioConst n M * δ⁻¹ := by
  have hδ2 : 0 < δ / 2 := by positivity
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hinv : (efSystemDelta n (δ / 2))⁻¹ ≤ 12 * n * δ⁻¹ := by
    refine (inv_efSystemDelta_le hn hδ2 (by linarith)).trans_eq ?_
    field_simp
    ring
  have hl : 0 ≤ Real.log (3 * M) := Real.log_nonneg (by linarith)
  rw [FormSystem.cutRatio, div_eq_mul_inv, efRatioConst]
  calc Real.log (3 * M) * (efSystemDelta n (δ / 2))⁻¹ ≤ Real.log (3 * M) * (12 * n * δ⁻¹) := by
        gcongr
    _ = 12 * n * Real.log (3 * M) * δ⁻¹ := by ring


/-- **The constant of `Real.subspaceIntervalWith_of_mem`**, in the variables of
`Real.subspaceConst`: the larger of EF13's constants for the number of intervals and for their
ratio at `R' = 2 n d + n` forms and coordinates, and of `Real.subspaceConst` (for the threshold). -/
noncomputable def intervalConst (n d s : ℕ) (h μ : ℝ) : ℝ :=
  max (max (efIntervalConst n (2 * n * d + n)) (efRatioConst n (2 * n * d + n)))
    (subspaceConst n d s h μ)

theorem one_le_intervalConst (n d s : ℕ) (h μ : ℝ) : 1 ≤ intervalConst n d s h μ :=
  (one_le_subspaceConst ..).trans (le_max_right _ _)

theorem efIntervalConst_le_intervalConst (n d s : ℕ) (h μ : ℝ) :
    efIntervalConst n (2 * n * d + n) ≤ intervalConst n d s h μ :=
  (le_max_left _ _).trans (le_max_left _ _)

theorem efRatioConst_le_intervalConst (n d s : ℕ) (h μ : ℝ) :
    efRatioConst n (2 * n * d + n) ≤ intervalConst n d s h μ :=
  (le_max_right _ _).trans (le_max_left _ _)

theorem thrConst_le_intervalConst (n d s : ℕ) (h μ : ℝ) :
    thrConst n d s μ * (1 + 17 * d + 3 * h) + 2 * n ^ 2 ≤ intervalConst n d s h μ :=
  (thrConst_le_subspaceConst ..).trans (le_max_right _ _)


/-- **The interval form at `∞` and finitely many finite places of `ℚ`**, with an explicit constant
(`Real.intervalConst`): the form `Real.subspaceIntervalWith_of_mem` is assembled from. The forms
are taken over a Galois field `E ⊆ ℂ` containing `α` (`Real.exists_normalized_places_of_mem`)
and counted by `NumberField.exists_forall_mem_interval_of_efSystemThreshold_le`. -/
theorem subspaceInterval_places_of_mem {α : ℝ} (E : IntermediateField ℚ ℂ) [IsGalois ℚ E]
    [NumberField E] (hαE : (α : ℂ) ∈ E) {n : ℕ} (hn : 2 ≤ n) (hn4 : n ≤ 4)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    let K := intervalConst n (finrank ℚ E) #S (log (mulHeight₁ (⟨α, hαE⟩ : E)))
        (log (scalarConst ℚ S))
    ∀ (P : Fin n → Fin n → Fin 3 → ℤ) (B : ℝ), 1 ≤ B → (∀ i k m, |(P i k m : ℝ)| ≤ B) →
      ∀ γ : ℝ, 0 < γ → γ ≤ 1 → γ ≤ |(Matrix.of fun i k ↦ quadVal α (P i k)).det| →
      ∀ C : ℝ, 1 ≤ C → ∀ (e : Fin n → ℝ) (f : HeightOneSpectrum (𝓞 ℚ) → Fin n → ℝ) (δ : ℝ),
        0 < δ → δ ≤ 1 → (∀ i, e i ≤ 1) → (∃ i, e i = 1) → (∃ i, e i ≤ 1 - δ / (2 * n)) →
        (∀ v ∈ S, ∀ i, f v i ≤ 0) → (∀ v ∈ S, ∃ i, f v i = 0) →
        ∑ i, e i + ∑ v ∈ S, ∑ i, f v i ≤ -δ →
      ∃ U : Submodule ℚ (Fin n → ℚ), U ≠ ⊤ ∧
        ∃ 𝒯 : Finset ℝ, (#𝒯 : ℝ) ≤ K * δ⁻¹ ^ 2 * (1 + log δ⁻¹) ∧
        ∀ x : Fin n → ℤ, x ≠ 0 →
          (∀ i, |∑ k, quadVal α (P i k) * x k| ≤ C * (⨆ k, |(x k : ℝ)|) ^ e i) →
          (∀ v ∈ S, ∀ i, FinitePlace.mk v (x i : ℚ) ≤ (⨆ k, |(x k : ℝ)|) ^ f v i) →
          K * δ⁻¹ * (1 + log B + log C + log γ⁻¹) ≤ log (⨆ k, |(x k : ℝ)|) →
          (fun k ↦ (x k : ℚ)) ∈ U ∨
            ∃ s ∈ 𝒯, s ≤ log (⨆ k, |(x k : ℝ)|) ∧ log (⨆ k, |(x k : ℝ)|) < K * δ⁻¹ * s := by
  intro K P B hB hP γ hγ hγ1 hdet C hC e f δ hδ hδ1 he1 he he0 hf hf0 hsum
  have hwInf := placeAbs_liesOver_infinitePlace E.val.toRingHom
  have hwFin : ∀ v ∈ S, (placeAbs E.val.toRingHom (FinitePlace.mk v).1).LiesOver
      (FinitePlace.mk v).1 := fun v _ ↦ placeAbs_liesOver_finitePlace _ (FinitePlace.mk v)
  obtain ⟨L, Cs, c, H, hN, hmem⟩ := exists_normalized_places_of_mem E hαE hn hn4 S P hB hP hγ
    hγ1 hdet hC e f hδ hδ1 he1 he he0 hf hf0 hsum
  obtain ⟨T, hT1, htop, 𝒯, h𝒯, h𝒯ge, hTmem⟩ :=
    exists_forall_mem_interval_of_efSystemThreshold_le S _ hwInf hwFin hN
  rw [Fintype.card_fin] at h𝒯 hTmem
  set M := 2 * n * finrank ℚ E + n with hMdef
  have hM : 2 ≤ M := by omega
  have hδi : 0 < δ⁻¹ := inv_pos.2 hδ
  have hl : 0 ≤ log δ⁻¹ := Real.log_nonneg ((one_le_inv₀ hδ).2 hδ1)
  -- the subspace: the one of `T`, or `0` if there is none
  obtain ⟨U, hU, hTU⟩ : ∃ U : Submodule ℚ (Fin n → ℚ), U ≠ ⊤ ∧ ∀ W ∈ T, W = U := by
    rcases T.eq_empty_or_nonempty with rfl | ⟨W, hW⟩
    · refine ⟨⊥, fun h ↦ ?_, by simp⟩
      have := congrArg (fun U : Submodule ℚ (Fin n → ℚ) ↦ finrank ℚ U) h
      simp only [finrank_bot, finrank_top, finrank_fin_fun] at this
      omega
    · exact ⟨W, htop W hW, fun W' hW' ↦ Finset.card_le_one.1 hT1 W' hW' W hW⟩
  refine ⟨U, hU, 𝒯, ?_, fun x hx hsol hfin hlarge ↦ ?_⟩
  · refine (Nat.cast_le.2 h𝒯).trans ((intervalCount_half_le hn hM hδ hδ1).trans ?_)
    have : efIntervalConst n M ≤ K := efIntervalConst_le_intervalConst ..
    gcongr
  have hΞ : 0 ≤ δ⁻¹ * (1 + log B + log C + log γ⁻¹) := by
    have := Real.log_nonneg hB
    have := Real.log_nonneg hC
    have := Real.log_nonneg ((one_le_inv₀ hγ).2 hγ1)
    positivity
  obtain ⟨h1, h2⟩ := hmem x hx hsol hfin <| le_trans (by
    rw [mul_assoc, mul_assoc K]
    exact mul_le_mul_of_nonneg_right (thrConst_le_intervalConst ..) hΞ) hlarge
  rcases hTmem _ h1 h2 with ⟨W, hW, hxW⟩ | ⟨s, hs, hs1, hs2⟩
  · exact .inl (hTU W hW ▸ hxW)
  refine .inr ⟨s, hs, ?_, ?_⟩ <;> rw [Height.mulHeightAff_intCast hx] at hs1 hs2
  · exact hs1
  · have hX : 0 ≤ log (⨆ k, |(x k : ℝ)|) := by
      refine Real.log_nonneg ?_
      rw [← Height.mulHeightAff_intCast hx]
      exact one_le_mulHeightAff _
    have hs0 : 0 ≤ s := by
      by_contra hs0
      push Not at hs0
      have := FormSystem.one_lt_cutRatio hM (efSystemDelta_pos (n := n) (by positivity : 0 < δ / 2))
        (efSystemDelta_le_one n (by positivity : 0 < δ / 2))
      nlinarith
    refine hs2.trans_le ?_
    have hr := cutRatio_half_le (n := n) hn (by omega : 1 ≤ M) hδ hδ1
    have : efRatioConst n M ≤ K := efRatioConst_le_intervalConst ..
    calc FormSystem.cutRatio M (efSystemDelta n (δ / 2)) * s ≤ efRatioConst n M * δ⁻¹ * s := by
          gcongr
      _ ≤ K * δ⁻¹ * s := by gcongr


/-- **The interval form of Evertse–Ferretti 2013 for forms in `1, α, α²` at `∞` and the primes of
`S`, with an explicit constant**: one proper subspace and `K δ⁻² (1 + log δ⁻¹)` intervals
`[s, K δ⁻¹ s)` of `log |x|`, with the constant `Real.intervalConst` of `n`, the degree `d` of a
Galois field `E ⊆ ℂ` containing `α`, the height `log H(α)` of `α` in `E`, `#S` and
`log 2 + ∑_{l ∈ S} log l`. The count of `Real.subspaceBoundWith_three_of_mem` before the gap
principle (`NumberField.exists_forall_mem_interval_of_efSystemThreshold_le`). -/
theorem subspaceIntervalWith_of_mem {α : ℝ} (E : IntermediateField ℚ ℂ) [IsGalois ℚ E]
    [NumberField E] (hαE : (α : ℂ) ∈ E) (S : Finset Nat.Primes) {n : ℕ} (hn : 2 ≤ n)
    (hn4 : n ≤ 4) :
    SubspaceIntervalWith α S n (intervalConst n (finrank ℚ E) #S
      (log (mulHeight₁ (⟨α, hαE⟩ : E))) (log 2 + ∑ l ∈ S, log (l : ℕ))) := by
  classical
  have hT := subspaceInterval_places_of_mem E hαE hn hn4 (S.image primeIdeal)
  rw [card_image_primeIdeal, log_scalarConst_image_primeIdeal] at hT
  intro P B hB hP γ hγ hγ1 hdet C hC e f δ hδ hδ1 he1 he he0 hf hf0 hsum
  set f' : HeightOneSpectrum (𝓞 ℚ) → Fin n → ℝ := fun v ↦ f (Function.invFun primeIdeal v)
  have hf' (l : Nat.Primes) : f' (primeIdeal l) = f l := by
    simp only [f', Function.leftInverse_invFun primeIdeal_injective l]
  have hsum' : ∑ v ∈ S.image primeIdeal, ∑ i, f' v i = ∑ l ∈ S, ∑ i, f l i := by
    rw [Finset.sum_image fun l _ l' _ h ↦ primeIdeal_injective h]
    simp only [hf']
  obtain ⟨U, hU, 𝒯, hcard, hmem⟩ := hT P B hB hP γ hγ hγ1 hdet C hC e f' δ hδ hδ1 he1 he he0
    (fun v hv ↦ by
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hv
      rw [hf']; exact hf l hl)
    (fun v hv ↦ by
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hv
      rw [hf']; exact hf0 l hl)
    (by rwa [hsum'])
  refine ⟨U, hU, 𝒯, hcard, fun x hx hsol hfin hlarge ↦ hmem x hx hsol (fun v hv i ↦ ?_) hlarge⟩
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hv
  rw [hf', finitePlace_mk_primeIdeal]
  exact hfin l hl i

/-- **The interval form of Evertse–Ferretti 2013 for forms in `1, α, α²` at `∞` and the primes
of `S`**, for every real algebraic `α`. The forms are taken over the Galois closure of `α` in `ℂ`
(`Real.subspaceIntervalWith_of_mem`). -/
theorem subspaceIntervalAt_of_isAlgebraic {α : ℝ} (hα : IsAlgebraic ℚ α) (S : Finset Nat.Primes) :
    SubspaceIntervalAt α S := by
  intro n hn hn4
  obtain ⟨E, hgal, hfd, hmem⟩ := exists_isGalois_mem hα
  have : NumberField E := { }
  exact ⟨_, one_le_intervalConst .., subspaceIntervalWith_of_mem E hmem S hn hn4⟩

/-- **The rational case of `Real.subspaceIntervalWith_of_mem`**: for `α = q ∈ ℚ` the forms are
over `ℚ`, `d = 1`, and the height is `log max (|num q|, den q)`. -/
theorem subspaceIntervalWith_ratCast (q : ℚ) (S : Finset Nat.Primes) {n : ℕ} (hn : 2 ≤ n)
    (hn4 : n ≤ 4) :
    SubspaceIntervalWith (q : ℝ) S n
      (intervalConst n 1 #S (log (mulHeight₁ q)) (log 2 + ∑ l ∈ S, log (l : ℕ))) := by
  have : NumberField (⊥ : IntermediateField ℚ ℂ) := { }
  have hq : (((q : ℝ) : ℂ)) ∈ (⊥ : IntermediateField ℚ ℂ) :=
    IntermediateField.mem_bot.2 ⟨q, by simp⟩
  have h := subspaceIntervalWith_of_mem ⊥ hq S hn hn4
  have hβ : (⟨((q : ℝ) : ℂ), hq⟩ : (⊥ : IntermediateField ℚ ℂ)) =
      algebraMap ℚ (⊥ : IntermediateField ℚ ℂ) q := Subtype.ext (by simp)
  rwa [IntermediateField.finrank_bot, hβ, ← NumberField.mulHeight₁_pow_finrank,
    IntermediateField.finrank_bot, pow_one] at h

/-- **The case `α = 0`** of the interval form: forms with integer coefficients. -/
theorem subspaceIntervalWith_zero (S : Finset Nat.Primes) {n : ℕ} (hn : 2 ≤ n) (hn4 : n ≤ 4) :
    SubspaceIntervalWith 0 S n (intervalConst n 1 #S 0 (log 2 + ∑ l ∈ S, log (l : ℕ))) := by
  have h := subspaceIntervalWith_ratCast 0 S hn hn4
  rwa [Rat.cast_zero, mulHeight₁_zero, Real.log_one] at h

end Real
