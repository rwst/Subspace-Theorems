/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Bugeaud2013.additions.Hyperplanes

/-!
# The points in a proper subspace of `ℚ⁴`

A proper subspace `S` of `ℚ⁴` holds `O(log ε⁻¹)` of the points outside `T₀ = {X₁ = X₂}`
(`Real.card_mem_le_of_ne_top`). Let `a < b < c` be the first such points with `v_a`, `v_b`, `v_c`
independent; if there are none, all the points lie in a plane. The earlier points lie in the plane
of `v_a, v_b`. The cross product `z` of `v_c, v_a, v_b` is orthogonal to `S`, of size
`Z = 6 H_c³`, and `Λ(z) ≠ 0` since `v_a ∉ T₀`. The later points are either early,
`log H < K (1 + log Z) ≤ 9 K log H_c`, which the doubling bounds by `O(1)`, or lie in one of the
`NT` planes of `Real.exists_planes_of_lamCoef_ne_zero`.
-/

@[expose] public section

open Finset Module

namespace Real

variable {α A ε c : ℝ} {D : ℕ}

/-- **The cover of `Real.exists_planes_of_lamCoef_ne_zero`**: for every `z` with `Λ(z) ≠ 0`, the
points `v ⊥ z` with `log H ≥ K (1 + log Z)` lie in at most `NT` planes. -/
def PlaneCover (α A K NT : ℝ) : Prop :=
  ∀ (z : Fin 4 → ℤ) (Z : ℝ), 1 ≤ Z → (∀ i, |(z i : ℝ)| ≤ Z) → quadVal α (lamCoef z) ≠ 0 →
    ∃ T : Finset (Submodule ℚ (Fin 4 → ℚ)), (#T : ℝ) ≤ NT ∧ (∀ U ∈ T, finrank ℚ U ≤ 2) ∧
      ∀ (ε : ℝ) (v : Fin 4 → ℤ) (H Q : ℝ), 0 ≤ ε → CFPoint α A ε v H Q →
        ∑ i, z i * v i = 0 → K * (1 + log Z) ≤ log H → ∃ U ∈ T, ptQ v ∈ U

theorem exists_planeCover {a : ℝ} (hSB : SubspaceBound α a) (hA : 1 ≤ A) (hc : 0 < c)
    (hL : LiouvilleQuad α c D) : ∃ K NT : ℝ, 0 ≤ NT ∧ PlaneCover α A K NT :=
  exists_planes_of_lamCoef_ne_zero hSB hA hc hL

/-- `Λ(z) ≠ 0` when `z ≠ 0` is orthogonal to a point with `v₁ ≠ v₂`. -/
theorem lamCoef_ne_zero {z v : Fin 4 → ℤ} (hz : z ≠ 0) (hzv : ∑ i, z i * v i = 0)
    (hv : v 1 ≠ v 2) : lamCoef z ≠ 0 := by
  intro h
  have h0 : z 0 = 0 := by simpa [lamCoef] using congrFun h 0
  have h12 : z 1 + z 2 = 0 := by simpa [lamCoef] using congrFun h 1
  have h3 : z 3 = 0 := by simpa [lamCoef] using congrFun h 2
  rw [Fin.sum_univ_four, h0, h3, show z 2 = -z 1 by linarith] at hzv
  have : z 1 * (v 1 - v 2) = 0 := by linarith
  rcases mul_eq_zero.1 this with h1 | h1
  · refine hz (funext fun i ↦ ?_)
    fin_cases i
    · exact h0
    · exact h1
    · simp only [Fin.reduceFinMk, Pi.zero_apply]; linarith
    · exact h3
  · exact hv (by linarith)

theorem quadVal_ne_zero_of_liouvilleQuad (hc : 0 < c) (hL : LiouvilleQuad α c D)
    {b : Fin 3 → ℤ} (hb : b ≠ 0) : quadVal α b ≠ 0 := by
  intro h
  have := hL b ((⨆ i, |(b i : ℝ)|)) hb (abs_le_iSup_abs b)
  rw [h, abs_zero, zero_mul] at this
  linarith

/-- An integer point of a span of integer points orthogonal to `z` is orthogonal to `z`. -/
theorem sum_mul_eq_zero_of_mem {z v : Fin 4 → ℤ} {S : Submodule ℚ (Fin 4 → ℚ)}
    (hS : S ≤ perpZ z) (hv : ptQ v ∈ S) : ∑ i, z i * v i = 0 := by
  have := mem_perpZ.1 (hS hv)
  simp only [ptQ] at this
  exact_mod_cast this

variable {Hs Qs : ℕ → ℝ} {vs : ℕ → Fin 4 → ℤ}

open scoped Classical in
/-- **A proper subspace holds `O(log ε⁻¹)` points outside `T₀`.** -/
theorem card_mem_le_of_ne_top (hc : 0 < c) (hL : LiouvilleQuad α c D) (hα : |α| ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hdbl : Doubling Hs) (I : Finset ℕ)
    (hpt : ∀ k ∈ I, CFPoint α A ε (vs k) (Hs k) (Qs k)) {K NT : ℝ} (hNT : 0 ≤ NT)
    (hcov : PlaneCover α A K NT) (S : Submodule ℚ (Fin 4 → ℚ)) (hS : S ≠ ⊤) :
    (#{k ∈ I | ptQ (vs k) ∈ S ∧ vs k 1 ≠ vs k 2} : ℝ) ≤
      (NT + 1) * planeBound c D ε + logb 2 (max 1 (9 * K)) + 1 := by
  set B := planeBound c D ε
  have hB := planeBound_nonneg hc D hε hε1
  set ME := max 1 (9 * K)
  have hME : 1 ≤ ME := le_max_left _ _
  have hlME : 0 ≤ logb 2 ME := Real.logb_nonneg (by norm_num) hME
  have hRHS : B ≤ (NT + 1) * B + logb 2 ME + 1 := by nlinarith
  set K0 := ({k ∈ I | ptQ (vs k) ∈ S ∧ vs k 1 ≠ vs k 2} : Finset ℕ)
  have hK0 {k : ℕ} (hk : k ∈ K0) : k ∈ I ∧ ptQ (vs k) ∈ S ∧ vs k 1 ≠ vs k 2 := by
    simpa [K0] using hk
  have hHmono {i k : ℕ} (hi : i ∈ I) (hk : k ∈ I) (hik : i ≤ k) : Hs i ≤ Hs k :=
    (Real.log_le_log_iff (hpt i hi).H_pos (hpt k hk).H_pos).1 (hdbl.log_mono hik)
  -- all points in one plane
  have hplane (P : Submodule ℚ (Fin 4 → ℚ)) (hP : finrank ℚ P ≤ 2)
      (hsub : ∀ k ∈ K0, ptQ (vs k) ∈ P) : (#K0 : ℝ) ≤ (NT + 1) * B + logb 2 ME + 1 := by
    have : K0 ⊆ {k ∈ I | ptQ (vs k) ∈ P} := fun k hk ↦
      Finset.mem_filter.2 ⟨(hK0 hk).1, hsub k hk⟩
    exact ((Nat.cast_le.2 (card_le_card this)).trans
      (card_mem_le_of_finrank_le_two hc hL hα hε hε1 hdbl I hpt P hP)).trans hRHS
  rcases K0.eq_empty_or_nonempty with h0 | hne
  · rw [h0, card_empty, Nat.cast_zero]; linarith
  set a := K0.min' hne
  obtain ⟨haI, haS, ha12⟩ := hK0 (K0.min'_mem hne)
  have hpa := hpt a haI
  have hva : ptQ (vs a) ≠ 0 := fun h ↦ hpa.v0_ne_zero (by simpa [ptQ] using congrFun h 0)
  -- the line through `v_a`
  by_cases hb : ∀ k ∈ K0, ptQ (vs k) ∈ ℚ ∙ ptQ (vs a)
  · exact hplane _ (by rw [finrank_span_singleton hva]; norm_num) hb
  push Not at hb
  set K1 := K0.filter fun k ↦ ptQ (vs k) ∉ ℚ ∙ ptQ (vs a)
  have hne1 : K1.Nonempty := by
    obtain ⟨k, hk, hk'⟩ := hb
    exact ⟨k, Finset.mem_filter.2 ⟨hk, hk'⟩⟩
  set b := K1.min' hne1
  have hb1 := K1.min'_mem hne1
  obtain ⟨hbK0, hbL⟩ := Finset.mem_filter.1 hb1
  obtain ⟨hbI, hbS, -⟩ := hK0 hbK0
  have hab : a ≤ b := K0.min'_le b hbK0
  have hli2 : LinearIndependent ℚ ![ptQ (vs a), ptQ (vs b)] := by
    rw [LinearIndependent.pair_iff' hva]
    intro r hr
    exact hbL (Submodule.mem_span_singleton.2 ⟨r, hr⟩)
  set P2 := Submodule.span ℚ (Set.range ![ptQ (vs a), ptQ (vs b)])
  have hP2 : finrank ℚ P2 = 2 := by rw [finrank_span_eq_card hli2, Fintype.card_fin]
  -- the plane of `v_a, v_b`
  by_cases hcc : ∀ k ∈ K0, ptQ (vs k) ∈ P2
  · exact hplane P2 hP2.le hcc
  push Not at hcc
  set K2 := K0.filter fun k ↦ ptQ (vs k) ∉ P2
  have hne2 : K2.Nonempty := by
    obtain ⟨k, hk, hk'⟩ := hcc
    exact ⟨k, Finset.mem_filter.2 ⟨hk, hk'⟩⟩
  set cc := K2.min' hne2
  have hc2 := K2.min'_mem hne2
  obtain ⟨hcK0, hcP2⟩ := Finset.mem_filter.1 hc2
  obtain ⟨hcI, hcS, -⟩ := hK0 hcK0
  have hpc := hpt cc hcI
  have hacc : a ≤ cc := K0.min'_le cc hcK0
  have hline : ℚ ∙ ptQ (vs a) ≤ P2 := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.subset_span ⟨0, rfl⟩
  have hbcc : b ≤ cc := K1.min'_le cc (Finset.mem_filter.2 ⟨hcK0, fun h ↦ hcP2 (hline h)⟩)
  -- the three points span `S`
  have hli3 : LinearIndependent ℚ ![ptQ (vs cc), ptQ (vs a), ptQ (vs b)] :=
    linearIndependent_finCons.2 ⟨hli2, hcP2⟩
  set S3 := Submodule.span ℚ (Set.range ![ptQ (vs cc), ptQ (vs a), ptQ (vs b)])
  have hS3 : S3 = S := by
    refine Submodule.eq_of_le_of_finrank_le ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact hcS
      · exact haS
      · exact hbS
    · have h1 := Submodule.finrank_lt hS
      rw [Module.finrank_fin_fun] at h1
      rw [finrank_span_eq_card hli3, Fintype.card_fin]
      omega
  -- the cross product
  set z := crossZ (vs cc) (vs a) (vs b)
  have hz0 : z ≠ 0 := crossZ_ne_zero hli3
  have hSz : S ≤ perpZ z := by
    rw [← hS3, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ptQ_mem_perpZ (sum_crossZ_mul_left _ _ _)
    · exact ptQ_mem_perpZ (sum_crossZ_mul_mid _ _ _)
    · exact ptQ_mem_perpZ (sum_crossZ_mul_right _ _ _)
  have hperp {k : ℕ} (hk : k ∈ K0) : ∑ i, z i * vs k i = 0 :=
    sum_mul_eq_zero_of_mem hSz (hK0 hk).2.1
  have hΛ : quadVal α (lamCoef z) ≠ 0 :=
    quadVal_ne_zero_of_liouvilleQuad hc hL (lamCoef_ne_zero hz0 (hperp (K0.min'_mem hne)) ha12)
  -- its size
  have hHc1 := hpc.one_le_H
  set Z := 6 * Hs cc ^ 3
  have hZ1 : 1 ≤ Z := by
    have : 1 ≤ Hs cc ^ 3 := one_le_pow₀ hHc1
    simp only [Z]; linarith
  have hzZ : ∀ i, |(z i : ℝ)| ≤ Z :=
    abs_crossZ_le (hpc.abs_le) (fun i ↦ (hpa.abs_le i).trans (hHmono haI hcI hacc))
      (fun i ↦ ((hpt b hbI).abs_le i).trans (hHmono hbI hcI hbcc))
  obtain ⟨T, hT, hTr, hTmem⟩ := hcov z Z hZ1 hzZ hΛ
  -- early points
  have hlogc := hdbl.one_le_log cc
  have hearly : K * (1 + log Z) ≤ ME * log (Hs cc) := by
    have hlZ : log Z = log 6 + 3 * log (Hs cc) := by
      simp only [Z]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
    have hl6 : log 6 ≤ 5 := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 6 by norm_num)]
    have hl60 : 0 ≤ log 6 := Real.log_nonneg (by norm_num)
    have h1 : 1 + log Z ≤ 9 * log (Hs cc) := by rw [hlZ]; linarith
    rcases le_total K 0 with hK | hK
    · have : K * (1 + log Z) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hK (by
        rw [hlZ]; linarith)
      nlinarith
    · calc K * (1 + log Z) ≤ K * (9 * log (Hs cc)) := mul_le_mul_of_nonneg_left h1 hK
        _ = 9 * K * log (Hs cc) := by ring
        _ ≤ ME * log (Hs cc) := mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
  -- the decomposition
  have hsplit : K0 ⊆ ({k ∈ I | ptQ (vs k) ∈ P2} ∪
      {k ∈ I | cc ≤ k ∧ log (Hs k) ≤ ME * log (Hs cc)}) ∪
      T.biUnion fun U ↦ {k ∈ I | ptQ (vs k) ∈ U} := by
    intro k hk
    obtain ⟨hkI, hkS, -⟩ := hK0 hk
    rcases lt_or_ge k cc with hlt | hge
    · refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hkI, ?_⟩))
      by_contra hkP
      exact absurd (K2.min'_le k (Finset.mem_filter.2 ⟨hk, hkP⟩)) (not_le.2 hlt)
    · by_cases hlate : K * (1 + log Z) ≤ log (Hs k)
      · obtain ⟨U, hU, hkU⟩ := hTmem ε (vs k) (Hs k) (Qs k) hε.le (hpt k hkI) (hperp hk) hlate
        exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨U, hU, Finset.mem_filter.2
          ⟨hkI, hkU⟩⟩)
      · push Not at hlate
        exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.2
          ⟨hkI, hge, (hlate.trans_le hearly).le⟩))
  have h1 : (#{k ∈ I | ptQ (vs k) ∈ P2} : ℝ) ≤ B :=
    card_mem_le_of_finrank_le_two hc hL hα hε hε1 hdbl I hpt P2 hP2.le
  have h2 : (#{k ∈ I | cc ≤ k ∧ log (Hs k) ≤ ME * log (Hs cc)} : ℝ) ≤ logb 2 ME + 1 :=
    hdbl.card_le I cc hME
  have h3 : (#(T.biUnion fun U ↦ {k ∈ I | ptQ (vs k) ∈ U}) : ℝ) ≤ NT * B := by
    refine (Nat.cast_le.2 Finset.card_biUnion_le).trans ?_
    push_cast
    calc ∑ U ∈ T, (#{k ∈ I | ptQ (vs k) ∈ U} : ℝ) ≤ ∑ _U ∈ T, B :=
          Finset.sum_le_sum fun U hU ↦
            card_mem_le_of_finrank_le_two hc hL hα hε hε1 hdbl I hpt U (hTr U hU)
      _ = #T * B := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ NT * B := mul_le_mul_of_nonneg_right hT hB
  calc (#K0 : ℝ) ≤ #(({k ∈ I | ptQ (vs k) ∈ P2} ∪
        {k ∈ I | cc ≤ k ∧ log (Hs k) ≤ ME * log (Hs cc)}) ∪
        T.biUnion fun U ↦ {k ∈ I | ptQ (vs k) ∈ U}) := Nat.cast_le.2 (card_le_card hsplit)
    _ ≤ #{k ∈ I | ptQ (vs k) ∈ P2} + #{k ∈ I | cc ≤ k ∧ log (Hs k) ≤ ME * log (Hs cc)} +
        #(T.biUnion fun U ↦ {k ∈ I | ptQ (vs k) ∈ U}) := by
        have := (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le
          ({k ∈ I | ptQ (vs k) ∈ P2} : Finset ℕ)
          ({k ∈ I | cc ≤ k ∧ log (Hs k) ≤ ME * log (Hs cc)} : Finset ℕ))
          (#(T.biUnion fun U ↦ {k ∈ I | ptQ (vs k) ∈ U})))
        exact_mod_cast this
    _ ≤ B + (logb 2 ME + 1) + NT * B := by linarith
    _ = (NT + 1) * B + logb 2 ME + 1 := by ring

end Real
