/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.SubspaceGap

/-!
# From intervals to subspaces

**Layer 9.4.** Evertse, "On the Quantitative Subspace Theorem", proof of Theorem 2.1: under the
normalization (2.4) of a system (`NumberField.IsNormalizedSystem`), if the solutions outside a
subspace `U₀` have absolute affine height in `⋃_{i < m} [Q i, Q i ^ ω)` with every
`Q i ≥ n ^ (2 n / δ)` and `ω ≥ 1`, then they lie in at most
`m (1 + log ω / log (1 + δ / (2 n)))` proper subspaces
(`NumberField.exists_finset_submodule_of_forall_mem_interval`). Each interval `[Q, Q ^ ω)` is
covered by the windows `[Q ^ ((1 + e) ^ h), Q ^ ((1 + e) ^ (h + 1)))`, `e = δ / (2 n)`, of which
`⌈log ω / log (1 + e)⌉` suffice, and each window lies in one proper subspace by the gap principle
(Layer 9.2).

This is the step that turns an *interval result* — the form in which quantitative Roth and
Subspace theorems are proved — into a count, and it takes the intervals as its hypothesis, so
that any interval result can be fed to it.

## Main results

* `NumberField.exists_finset_submodule_of_forall_mem_interval_of_mem`: **from intervals to
  subspaces**, for the solutions in any set `X`.
* `NumberField.exists_finset_submodule_of_forall_mem_interval`: the same outside a subspace `U₀`,
  as the source states it.

## Implementation notes

⚠ **The intervals are a hypothesis, not Evertse's Theorem 3.1.** The source feeds this step its
interval result, Theorem 3.1, whose proof is the bulk of the paper and is not part of this
roadmap. The count is the source's, `m (1 + log ω / log (1 + δ / (2 n)))`, from the ceiling of
the number of windows per interval; the solutions in `U₀` are not counted, as in the source.

⚠ **`ω ≥ 1` is a hypothesis**: for `ω < 1` the intervals are empty, but the bound
`1 + log ω / log (1 + e)` can be negative. An empty index type `ι` needs no case of its own in
the statement: then every point is `0 ∈ U₀`.

## References

J.-H. Evertse, *On the Quantitative Subspace Theorem*, Zap. Nauchn. Sem. POMI **377** (2010),
217–240; J. Math. Sci. **171** (2010), 824–837 (arXiv:1008.2268), proof of Theorem 2.1.

This is Layer 9.4 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Height IsDedekindDomain Module

namespace NumberField

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
variable {ι : Type*} [Fintype ι]

/-- **From intervals to subspaces, for any set of solutions** (Evertse, proof of Theorem 2.1).
Under the normalization (2.4), if every solution in a set `X` has absolute affine height in
`[Q i, Q i ^ ω)` for some `i < m`, where every `Q i ≥ n ^ (2 n / δ)` and `ω ≥ 1`, then the
solutions in `X` lie in at most `m (1 + log ω / log (1 + δ / (2 n)))` proper subspaces of `Kⁿ`. -/
theorem exists_finset_submodule_of_forall_mem_interval_of_mem [Nonempty ι]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual F (ι → F)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) (X : Set (ι → K)) {m : ℕ}
    (Q : Fin m → ℝ) (hQ : ∀ i, (Fintype.card ι : ℝ) ^ (2 * Fintype.card ι / δ) ≤ Q i) {ω : ℝ}
    (hω : 1 ≤ ω)
    (hint : ∀ x ∈ systemSet S w L C c, x ∈ X → ∃ i, Q i ≤ mulHeightAff x ^ ((finrank ℚ K : ℝ)⁻¹) ∧
      mulHeightAff x ^ ((finrank ℚ K : ℝ)⁻¹) < Q i ^ ω) :
    ∃ T : Finset (Submodule K (ι → K)),
      (T.card : ℝ) ≤ m * (1 + Real.log ω / Real.log (1 + δ / (2 * Fintype.card ι))) ∧
      (∀ U ∈ T, U ≠ ⊤) ∧ ∀ x ∈ systemSet S w L C c, x ∈ X → ∃ U ∈ T, x ∈ U := by
  classical
  set n := Fintype.card ι with hn
  set e := δ / (2 * n) with he
  have hδ := hN.delta_pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Fintype.card_pos
  have he0 : 0 < e := by positivity
  have hl : 0 < Real.log (1 + e) := Real.log_pos (by linarith)
  have hQ1 : ∀ i, 1 ≤ Q i := fun i ↦
    (Real.one_le_rpow (by exact_mod_cast Fintype.card_pos) (by positivity)).trans (hQ i)
  -- The windows of the `i`-th interval, and the subspace of each.
  set a : Fin m → ℕ → ℝ := fun i h ↦ Q i ^ ((1 + e) ^ h) with hadef
  have ha : ∀ i h, a i (h + 1) = a i h ^ (1 + δ / (2 * Fintype.card ι)) := fun i h ↦ by
    change Q i ^ ((1 + e) ^ (h + 1)) = (Q i ^ ((1 + e) ^ h)) ^ (1 + δ / (2 * Fintype.card ι))
    rw [← Real.rpow_mul (by linarith [hQ1 i] : (0 : ℝ) ≤ Q i), pow_succ]
  have haQ : ∀ i h, (n : ℝ) ^ (2 * n / δ) ≤ a i h := fun i h ↦ by
    refine (hQ i).trans ?_
    conv_lhs => rw [← Real.rpow_one (Q i)]
    exact Real.rpow_le_rpow_of_exponent_le (hQ1 i) (one_le_pow₀ (by linarith))
  have hU := fun i h ↦ exists_submodule_ne_top_of_window S w hwInf hwFin hN (haQ i h)
  choose U hUtop hU using hU
  -- `⌈log ω / log (1 + e)⌉` windows cover an interval.
  set A := ⌈Real.log ω / Real.log (1 + e)⌉₊ with hA
  have hωA : ω ≤ (1 + e) ^ A := by
    rw [← Real.log_le_log_iff (by linarith) (by positivity), Real.log_pow]
    calc Real.log ω = Real.log ω / Real.log (1 + e) * Real.log (1 + e) := by field_simp
      _ ≤ A * Real.log (1 + e) := mul_le_mul_of_nonneg_right (Nat.le_ceil _) hl.le
  have hT := fun i ↦ exists_finset_submodule_of_chain
    (P := fun x ↦ x ∈ systemSet S w L C c ∧ x ∈ X)
    (ht := fun x ↦ mulHeightAff x ^ ((finrank ℚ K : ℝ)⁻¹)) (a i) (fun h ↦ {U i h})
    (fun h V hV ↦ (Finset.mem_singleton.1 hV) ▸ hUtop i h)
    (fun h x hx h1 h2 ↦ ⟨U i h, Finset.mem_singleton_self _,
      hU i h x hx.1 h1 (by rw [← ha]; exact h2)⟩) A
  choose T hTcard hTtop hT using hT
  refine ⟨Finset.univ.biUnion T, ?_, fun V hV ↦ ?_, fun x hx hxX ↦ ?_⟩
  · have hTA : ∀ i, ((T i).card : ℝ) ≤ A := fun i ↦ by
      have : (T i).card ≤ A := by simpa using hTcard i
      exact_mod_cast this
    have hA1 : (A : ℝ) ≤ 1 + Real.log ω / Real.log (1 + e) := by
      have := Nat.ceil_lt_add_one (div_nonneg (Real.log_nonneg hω) hl.le)
      rw [← hA] at this
      linarith
    calc ((Finset.univ.biUnion T).card : ℝ) ≤ ∑ i, ((T i).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin m, (1 + Real.log ω / Real.log (1 + e)) :=
          Finset.sum_le_sum fun i _ ↦ (hTA i).trans hA1
      _ = m * (1 + Real.log ω / Real.log (1 + δ / (2 * Fintype.card ι))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  · obtain ⟨i, -, hV⟩ := Finset.mem_biUnion.1 hV
    exact hTtop i V hV
  · obtain ⟨i, hlo, hhi⟩ := hint x hx hxX
    have hup : Q i ^ ω ≤ a i A :=
      Real.rpow_le_rpow_of_exponent_le (hQ1 i) hωA
    obtain ⟨V, hV, hxV⟩ := hT i x ⟨hx, hxX⟩ (by simpa [hadef] using hlo) (hhi.trans_le hup)
    exact ⟨V, Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hV⟩, hxV⟩


/-- **From intervals to subspaces** (Evertse, proof of Theorem 2.1). Under the normalization
(2.4), if every solution outside a subspace `U₀` has absolute affine height in
`[Q i, Q i ^ ω)` for some `i < m`, where every `Q i ≥ n ^ (2 n / δ)` and `ω ≥ 1`, then those
solutions lie in at most `m (1 + log ω / log (1 + δ / (2 n)))` proper subspaces of `Kⁿ`. -/
theorem exists_finset_submodule_of_forall_mem_interval (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual F (ι → F)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) (U₀ : Submodule K (ι → K)) {m : ℕ}
    (Q : Fin m → ℝ) (hQ : ∀ i, (Fintype.card ι : ℝ) ^ (2 * Fintype.card ι / δ) ≤ Q i) {ω : ℝ}
    (hω : 1 ≤ ω)
    (hint : ∀ x ∈ systemSet S w L C c, x ∉ U₀ → ∃ i, Q i ≤ mulHeightAff x ^ ((finrank ℚ K : ℝ)⁻¹) ∧
      mulHeightAff x ^ ((finrank ℚ K : ℝ)⁻¹) < Q i ^ ω) :
    ∃ T : Finset (Submodule K (ι → K)),
      (T.card : ℝ) ≤ m * (1 + Real.log ω / Real.log (1 + δ / (2 * Fintype.card ι))) ∧
      (∀ U ∈ T, U ≠ ⊤) ∧ ∀ x ∈ systemSet S w L C c, x ∉ U₀ → ∃ U ∈ T, x ∈ U := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨∅, by
      simp only [Finset.card_empty, Nat.cast_zero]
      refine mul_nonneg (Nat.cast_nonneg _) (add_nonneg zero_le_one (div_nonneg
        (Real.log_nonneg hω) (Real.log_nonneg ?_)))
      simp [Fintype.card_eq_zero],
      by simp, fun x _ hx ↦ absurd (Subsingleton.elim x 0 ▸ U₀.zero_mem) hx⟩
  exact exists_finset_submodule_of_forall_mem_interval_of_mem S w hwInf hwFin hN
    {x | x ∉ U₀} Q hQ hω hint

end NumberField
