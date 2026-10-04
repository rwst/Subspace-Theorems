/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.FormInfimaLimit
public import QuantitativeSubspace.FormWedgeHeight

/-!
# A height bound for the filtration subspaces

J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative Subspace Theorem*,
Ann. of Math. **177** (2013), 513–590, Lemmas 17.2, 17.3 and Proposition 17.5.

Let `0 = T_0 < ⋯ < T_r = Ωⁿ` be the filtration of `(L, c)` and `H₂` the largest Arakelov height of
a form of `L`. Prop. 17.5: `H₂(T_l) ≤ H₂^{4ⁿ}` for `0 < l < r`. EF13's proof, followed here: with
`k = dim T_l` and `p = n - k`, Theorem 16.1 gives `T_k(Q) = T_l` and `λ_k(Q)/λ_{k+1}(Q) ≤ Q^{-θ}`
for large `Q`. Take independent `g_1, …, g_n` with `H(g_j) ≤ 2λ_j`. By Lemma 17.1 the `N - 1`
wedges `ĝ_I`, `I ≠ {k+1, …, n}`, have height at most `C ν_top Q^{-θ}` for the exterior power
`(L̂, ĉ)`, `ν_top = λ_{k+1} ⋯ λ_n`, while `λ̂_N ≥ c ν_top` by Prop. 9.2 for `L` and `L̂` (the
products of Lemma 17.2). So the `N - 1`-st infimum of `L̂` is separated from the `N`-th, and
`T̂_{N-1}(Q)` is the span `T̂` of the wedges. Theorem 16.1 for `(L̂, ĉ)` makes `T̂` the member of
dimension `N - 1` of the filtration of `(L̂, ĉ)`, i.e. its destabilizing subspace, and Lemma 17.4
bounds its height by `(H₂^p)^{(N-1)²}`. Lemma 6.1 gives `H₂(T̂) = H₂(T_l)`.

Like Theorem 16.1, the result is conditional on `NumberField.SemistableGap K Ω`, the qualitative
EF13 Theorem 8.1. Heights are relative to `K` (`Submodule.arakelovMulHeight` of the subspace of
`Kⁿ` underlying `T_l`, and `FormSystem.arakelovFormHeight`); the inequality is the same as EF13's
absolute one raised to `[K:ℚ]`.

## Main results

* `NumberField.FormSystem.qHeight_compound_le`: Lemma 17.1 for the reindexed exterior power.
* `NumberField.FormSystem.eventually_isDestabilizing`: a subspace of dimension `N - 1` cut out
  by a gap at the last successive infimum is the destabilizing subspace.
* `NumberField.FormSystem.arakelovMulHeight_le_of_isWeightFiltration`: EF13 Prop. 17.5.

This is milestone Q3.6 of `QuantitativeSubspace/README.md`.
-/

@[expose] public section

open Module Finset Matrix Filter Submodule
open exteriorPower (plucker)

namespace NumberField.FormSystem

variable {K : Type*} [Field K] [NumberField K] {Ω : Type*} [Field Ω] [Algebra K Ω]
  [Algebra.IsAlgebraic K Ω]

/-- **EF13 Lemma 17.1 for the wedges of the rows of `G`**, read in the exterior power moved to
`Ω^N`: `Ĥ(ĝ_s) ≤ p! ∏_{i ∈ s} H(g_i)`. -/
theorem qHeight_compound_le {n N p : ℕ} (L : FormSystem K (Fin n)) (c : FormExponent K (Fin n))
    (e : Set.powersetCard (Fin n) p ≃ Fin N) {Q : ℝ} (hQ : 1 ≤ Q)
    {G : Matrix (Fin n) (Fin n) Ω} (hG : G.det ≠ 0) (s : Set.powersetCard (Fin n) p) :
    ((L.exteriorPower p).reindex e).qHeight ((c.exteriorPower p).reindex e) Q
        (G.compound p s ∘ e.symm) ≤ p.factorial * ∏ i ∈ s.val, L.qHeight c Q (G i) := by
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  rw [qHeight_of_one_le _ _ hQ, qHeight_of_one_le _ _ hQ, FormExponent.weight_reindex,
    absMulHeight_reindex, Function.comp_assoc, e.symm_comp_self, Function.comp_id,
    FormExponent.weight_exteriorPower, compound_row]
  have hrows : LinearIndependent Ω G.row :=
    linearIndependent_rows_iff_isUnit.2 ((isUnit_iff_isUnit_det _).2 hG.isUnit)
  have hx : LinearIndependent Ω fun r ↦ G (Set.powersetCard.ofFinEmbEquiv.symm s r) :=
    hrows.comp _ (Set.powersetCard.ofFinEmbEquiv.symm s).injective
  refine (L.absMulHeight_exteriorPower_plucker_le _ hx).trans (le_of_eq ?_)
  rw [Set.powersetCard.prod_ofFinEmbEquiv_symm s (fun i ↦ L.absMulHeight (c.weight hQ0) (G i))]

/-- `C(n, p) ≥ 2` for `0 < p < n`. -/
theorem _root_.Nat.two_le_choose {n p : ℕ} (hp : 0 < p) (hpn : p < n) : 2 ≤ n.choose p := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [Nat.choose_succ_succ']
  have h1 := Nat.choose_pos (n := m) (k := q) (by omega)
  have h2 := Nat.choose_pos (n := m) (k := q + 1) (by omega)
  omega

/-- The member of a filtration of `Ω^N` containing the index `N`: `d_l < N ≤ d_{l+1}`. -/
theorem _root_.Submodule.IsWeightFiltration.exists_finrank_lt_le {N : ℕ}
    {w : Submodule Ω (Fin N → Ω) → ℝ} {r : ℕ} {T : ℕ → Submodule Ω (Fin N → Ω)}
    (hT : IsWeightFiltration w ⊤ r T) (hN : 0 < N) :
    ∃ l < r, finrank Ω (T l) < N ∧ N ≤ finrank Ω (T (l + 1)) := by
  classical
  have hex : ∃ l, N ≤ finrank Ω (T l) :=
    ⟨r, by rw [hT.top, finrank_top, Module.finrank_fin_fun]⟩
  have h0 : Nat.find hex ≠ 0 := fun h ↦ by
    have := Nat.find_spec hex
    rw [h, hT.zero, finrank_bot] at this
    omega
  obtain ⟨l, hl⟩ : ∃ l, Nat.find hex = l + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hlr : l + 1 ≤ r := hl ▸ Nat.find_min' hex (by rw [hT.top, finrank_top,
    Module.finrank_fin_fun])
  refine ⟨l, by omega, not_le.1 (Nat.find_min hex (by omega)), hl ▸ Nat.find_spec hex⟩

variable [IsAlgClosed Ω]

/-- **The destabilizing subspace from a gap in the last infimum** (the end of EF13's proof of
Prop. 17.5): for all large `Q`, a subspace `S ⊆ Ω^N` of dimension `N - 1` spanned by points of
height `≤ β` with `β Q^ε ≤ λ_N(Q)` is the destabilizing subspace of `(L, c)`. Indeed
`T_{N-1}(Q) = S`, and Theorem 16.1 puts `λ_{N-1}` and `λ_N` in different blocks, so `S` is the
member of dimension `N - 1` of the filtration. -/
theorem eventually_isDestabilizing (hgap : SemistableGap K Ω) {N : ℕ} (hN : 2 ≤ N)
    (L : FormSystem K (Fin N)) (c : FormExponent K (Fin N)) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q₀, ∀ Q, 1 ≤ Q → Q₀ ≤ Q → ∀ S : Submodule Ω (Fin N → Ω), finrank Ω S + 1 = N →
      ∀ β, 0 < β → S ≤ heightSpace Ω (L.qHeight c Q) β →
        β * Q ^ ε ≤ heightInf Ω (L.qHeight c Q) N →
        IsDestabilizing (L.subspaceWeight (Ω := Ω) c) ⊤ S := by
  classical
  obtain ⟨r, T, hT, -⟩ := L.exists_isWeightFiltration_top (Ω := Ω) c
  obtain ⟨Q₁, hQ₁⟩ := L.eventually_successiveInf c hgap hT (δ := ε / 4) (by positivity)
  obtain ⟨Q₂, hQ₂⟩ := eventually_atTop.1 ((tendsto_rpow_atTop hε).eventually_gt_atTop 2)
  refine ⟨max Q₁ (max Q₂ 2), fun Q hQ1 hQQ S hS β hβ hSβ hβN ↦ ?_⟩
  have hQQ₁ : Q₁ ≤ Q := le_of_max_le_left hQQ
  have hQ2 : 2 < Q ^ ε := hQ₂ Q ((le_max_left _ _).trans ((le_max_right _ _).trans hQQ))
  have hQgt : 1 < Q := by linarith [(le_max_right Q₂ 2).trans ((le_max_right _ _).trans hQQ)]
  have hQ0 : 0 < Q := by linarith
  set h := L.qHeight (Ω := Ω) c Q
  have hh : h = L.absMulHeight (c.weight hQ0) := qHeight_of_one_le L c hQ1
  have hlamN1 : heightInf Ω h (N - 1) ≤ β :=
    heightInf_le hβ.le ((show N - 1 = finrank Ω S by omega) ▸ Submodule.finrank_mono hSβ)
  have h2β : 2 * β < heightInf Ω h N :=
    lt_of_lt_of_le (by rw [mul_comm]; exact mul_lt_mul_of_pos_left hQ2 hβ) hβN
  have hlt : N - 1 < Fintype.card (Fin N) := by rw [Fintype.card_fin]; omega
  have hN1 : N - 1 + 1 = N := by omega
  have h₁ : heightInf Ω h (N - 1) < 2 * β := by linarith
  have h₂ : 2 * β < heightInf Ω h (N - 1 + 1) := by rwa [hN1]
  have hflag : heightFlag Ω h (N - 1) = S := by
    rw [← heightSpace_eq_heightFlag hlt h₁ h₂]
    refine (eq_of_le_of_finrank_eq (hSβ.trans (heightSpace_mono (by linarith))) ?_).symm
    rw [finrank_heightSpace_of_lt hlt h₁ h₂]
    omega
  obtain ⟨l, hlr, hllt, hlle⟩ := hT.exists_finrank_lt_le (by omega)
  have hTn : ∀ j, finrank Ω (T j) ≤ N := fun j ↦ by
    simpa using Submodule.finrank_le (T j)
  have hdim : finrank Ω (T l) = N - 1 := by
    by_contra hne
    have hlt' : finrank Ω (T l) < N - 1 := by omega
    obtain ⟨hb, -⟩ := hQ₁ Q hQ1 hQQ₁ l hlr
    simp only [successiveInf, ← hh] at hb
    set μ := weightSlope (L.subspaceWeight (Ω := Ω) c) (T l) (T (l + 1))
    have hA := (hb (N - 1) hlt' (by omega)).1
    have hB := (hb N (by omega) hlle).2
    have hQe : Q ^ (-μ + ε / 4) = Q ^ (-μ - ε / 4) * Q ^ (ε / 2) := by
      rw [← Real.rpow_add hQ0]
      ring_nf
    have h1 : β * Q ^ ε ≤ β * Q ^ (ε / 2) := by
      calc β * Q ^ ε ≤ heightInf Ω h N := hβN
        _ ≤ Q ^ (-μ - ε / 4) * Q ^ (ε / 2) := hQe ▸ hB
        _ ≤ β * Q ^ (ε / 2) := by gcongr; exact hA.trans hlamN1
    have h2 : Q ^ (ε / 2) < Q ^ ε := Real.rpow_lt_rpow_of_exponent_lt hQgt (by linarith)
    exact (not_le.2 h2) (le_of_mul_le_mul_left h1 hβ)
  have hl0 : l ≠ 0 := fun h0 ↦ by
    rw [h0, hT.zero, finrank_bot] at hdim
    omega
  have hltop : l + 1 = r := by
    by_contra hne
    have hlt := hT.lt (l + 1) (by omega)
    have heq : T (l + 1) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (le_antisymm (by simpa using hTn _) (by simpa using hlle))
    exact (hlt.trans_le (hT.le_top (by omega))).ne (by rw [heq])
  obtain ⟨j, rfl⟩ : ∃ j, l = j + 1 := ⟨l - 1, by omega⟩
  obtain ⟨-, hflag₁⟩ := hQ₁ Q hQ1 hQQ₁ j (by omega)
  simp only [infFlag, ← hh] at hflag₁
  rw [hdim, hflag] at hflag₁
  subst hltop
  rw [hflag₁]
  exact hT.isDestabilizing (L.isSupermodularWeight_subspaceWeight c)

/-- **EF13 Proposition 17.5.** Let `0 = T_0 < ⋯ < T_r = Ωⁿ` be the filtration of `(L, c)` and
`0 < l < r`. If `T_l = V ⊗ Ω` with `V ⊆ Kⁿ`, then `H₂(V) ≤ H₂^{4ⁿ}`, `H₂` the largest Arakelov
height of a form of `L` (both relative to `K`). The hypothesis `SemistableGap K Ω` is the
qualitative EF13 Theorem 8.1. -/
theorem arakelovMulHeight_le_of_isWeightFiltration (hgap : SemistableGap K Ω) {n : ℕ}
    (L : FormSystem K (Fin n)) (c : FormExponent K (Fin n)) {r : ℕ}
    {T : ℕ → Submodule Ω (Fin n → Ω)} (hT : IsWeightFiltration (L.subspaceWeight c) ⊤ r T)
    {l : ℕ} (hl0 : 0 < l) (hlr : l < r) {V : Submodule K (Fin n → K)}
    (hV : V.extendPi Ω = T l) : V.arakelovMulHeight ≤ L.arakelovFormHeight ^ (4 ^ n) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  -- dimensions
  set k := finrank Ω (T (m + 1)) with hk_def
  have hTn : ∀ j ≤ r, finrank Ω (T j) ≤ n := fun j _ ↦ by
    have := Submodule.finrank_le (T j)
    rwa [Module.finrank_fin_fun] at this
  have hprev : finrank Ω (T m) < k := Submodule.finrank_lt_finrank_of_lt (hT.lt m (by omega))
  have hnext : k < finrank Ω (T (m + 2)) :=
    Submodule.finrank_lt_finrank_of_lt (hT.lt (m + 1) hlr)
  have hkn : k < n := hnext.trans_le (hTn _ (by omega))
  have hk0 : 0 < k := (Nat.zero_le _).trans_lt hprev
  have hk1 : k + 1 ≤ finrank Ω (T (m + 2)) := hnext
  set kF : Fin n := ⟨k, hkn⟩
  set p := n - k with hp_def
  have hp1 : 1 ≤ p := by omega
  set N := Fintype.card (Set.powersetCard (Fin n) p) with hN_def
  set e : Set.powersetCard (Fin n) p ≃ Fin N := Fintype.equivFin _
  have hNchoose : N = n.choose p := by
    rw [hN_def, ← Nat.card_eq_fintype_card, Set.powersetCard.card, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hN2 : 2 ≤ N := hNchoose ▸ Nat.two_le_choose (by omega) (by omega)
  -- the exterior power, moved to `Ω^N`
  set L' := (L.exteriorPower p).reindex e
  set c' := (c.exteriorPower p).reindex e
  set N' := (n - 1).choose (p - 1)
  have hsum' : c'.sum = N' * c.sum := by
    rw [FormExponent.sum_reindex, FormExponent.sum_exteriorPower c hp1, Fintype.card_fin]
  -- the slopes of `L` around `T_l`
  set w := L.subspaceWeight (Ω := Ω) c
  set μ₁ := weightSlope w (T m) (T (m + 1))
  set μ₂ := weightSlope w (T (m + 1)) (T (m + 2))
  have hμ : μ₂ < μ₁ := hT.slope_lt m (by omega)
  set g := μ₁ - μ₂
  have hg : 0 < g := by simp only [g]; linarith
  -- Theorem 16.1 for `L` and for `L'`
  obtain ⟨Q₀, hQ₀⟩ := L.eventually_successiveInf c hgap hT (δ := g / 4) (by positivity)
  obtain ⟨B, hB, hBQ⟩ := L'.exists_le_prod_heightInf (Ω := Ω) c'
  obtain ⟨Q₁, hQ₁⟩ := L'.eventually_isDestabilizing hgap hN2 c' (ε := g / 4) (by positivity)
  set C₀ := √2 ^ (n * (n - 1)) * L.absDet
  have hC₀ : 0 < C₀ := mul_pos (pow_pos (by positivity) _) L.absDet_pos
  set C₁ : ℝ := p.factorial * 2 ^ p
  have hC₁ : 0 < C₁ := by positivity
  set c₂ := B / (C₁ ^ (N - 1) * C₀ ^ N')
  have hc₂ : 0 < c₂ := by positivity
  obtain ⟨Q, hQ1, hQQ₀, hQQ₁, hQa, hQc⟩ : ∃ Q : ℝ, 1 ≤ Q ∧ Q₀ ≤ Q ∧ Q₁ ≤ Q ∧
      2 < Q ^ (g / 2) ∧ C₁ / c₂ < Q ^ (g / 4) := by
    have h2 := (tendsto_rpow_atTop (by positivity : 0 < g / 2)).eventually_gt_atTop
    have h4 := (tendsto_rpow_atTop (by positivity : 0 < g / 4)).eventually_gt_atTop
    exact ((eventually_ge_atTop 1).and ((eventually_ge_atTop Q₀).and
      ((eventually_ge_atTop Q₁).and ((h2 2).and (h4 (C₁ / c₂)))))).exists
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ1
  set h := L.qHeight (Ω := Ω) c Q
  set h' := L'.qHeight (Ω := Ω) c' Q
  have hh : h = L.absMulHeight (c.weight hQ0) := qHeight_of_one_le L c hQ1
  have hh' : h' = L'.absMulHeight (c'.weight hQ0) := qHeight_of_one_le L' c' hQ1
  -- the bounds of Theorem 16.1 for `L` at `Q`
  obtain ⟨hb₁, hflag⟩ := hQ₀ Q hQ1 hQQ₀ m (by omega)
  obtain ⟨hb₂, -⟩ := hQ₀ Q hQ1 hQQ₀ (m + 1) hlr
  simp only [successiveInf, infFlag, ← hh] at hb₁ hb₂ hflag
  have hlamk : heightInf Ω h k ≤ Q ^ (-μ₁ + g / 4) := (hb₁ k hprev le_rfl).2
  have hlamk1 : Q ^ (-μ₂ - g / 4) ≤ heightInf Ω h (k + 1) := (hb₂ (k + 1) (by omega) hk1).1
  have hexp : Q ^ (-μ₂ - g / 4) = Q ^ (-μ₁ + g / 4) * Q ^ (g / 2) := by
    rw [← Real.rpow_add hQ0]
    congr 1
    simp only [g]
    ring
  set lam : Fin n → ℝ := fun i ↦ heightInf Ω h (i + 1)
  have hpos : ∀ i, 0 < lam i := fun i ↦ by
    have := L.successiveInf_pos (Ω := Ω) (c.weight hQ0) i
    simpa [lam, hh] using this
  have hmono : Monotone lam := fun i j hij ↦
    heightInf_mono (by simpa using hij) (by simp)
  have hlamk0 : 0 < heightInf Ω h k := by
    have := hpos ⟨k - 1, by omega⟩
    simpa [lam, Nat.sub_add_cancel hk0] using this
  have hgapL : 2 * heightInf Ω h k < heightInf Ω h (k + 1) := by
    calc 2 * heightInf Ω h k ≤ 2 * Q ^ (-μ₁ + g / 4) := by gcongr
      _ < Q ^ (g / 2) * Q ^ (-μ₁ + g / 4) :=
          mul_lt_mul_of_pos_right hQa (Real.rpow_pos_of_pos hQ0 _)
      _ = Q ^ (-μ₂ - g / 4) := by rw [hexp, mul_comm]
      _ ≤ heightInf Ω h (k + 1) := hlamk1
  have hratio : lam ⟨k - 1, by omega⟩ / lam kF ≤ Q ^ (-(g / 2)) := by
    have h1 : lam ⟨k - 1, by omega⟩ = heightInf Ω h k := by
      simp [lam, Nat.sub_add_cancel hk0]
    have h2 : lam kF = heightInf Ω h (k + 1) := rfl
    rw [h1, h2, div_le_iff₀ ((hpos kF).trans_eq h2), Real.rpow_neg hQ0.le]
    calc heightInf Ω h k ≤ Q ^ (-μ₁ + g / 4) := hlamk
      _ = (Q ^ (g / 2))⁻¹ * Q ^ (-μ₂ - g / 4) := by
          have := (Real.rpow_pos_of_pos hQ0 (g / 2)).ne'
          rw [hexp]
          field_simp
      _ ≤ (Q ^ (g / 2))⁻¹ * heightInf Ω h (k + 1) := by gcongr
  -- points `g_j` with `H(g_j) ≤ 2 λ_j`
  obtain ⟨g₀, hg₀, hgb₀⟩ := exists_linearIndependent_le_mul Ω h one_lt_two
    (fun i ↦ by simpa [lam] using hpos (Fin.cast (Fintype.card_fin n) i))
  set G : Matrix (Fin n) (Fin n) Ω := Matrix.of fun i ↦ g₀ (Fin.cast (Fintype.card_fin n).symm i)
  have hGli : LinearIndependent Ω G.row := hg₀.comp _ (Fin.cast_injective _)
  have hGdet : G.det ≠ 0 :=
    ((isUnit_iff_isUnit_det G).1 (linearIndependent_rows_iff_isUnit.1 hGli)).ne_zero
  have hGb : ∀ i, h (G i) ≤ 2 * lam i := fun i ↦ by
    change h (g₀ (Fin.cast (Fintype.card_fin n).symm i)) ≤ _
    simpa [lam] using hgb₀ (Fin.cast (Fintype.card_fin n).symm i)
  have hGh0 : ∀ i, 0 ≤ h (G i) := fun i ↦ by
    rw [hh]
    exact L.absMulHeight_nonneg _ _
  -- `g_1, …, g_k` lie in `T_l`
  have hspaceT : heightSpace Ω h (2 * heightInf Ω h k) = T (m + 1) := by
    rw [heightSpace_eq_heightFlag (by simpa using hkn) (by linarith) hgapL]
    exact hflag
  have hGV : ∀ i : Fin n, (i : ℕ) < k → G i ∈ V.extendPi Ω := fun i hi ↦ by
    rw [hV, ← hspaceT]
    refine mem_heightSpace ((hGb i).trans ?_)
    have : lam i ≤ heightInf Ω h k :=
      heightInf_mono (by omega) (by simpa using hkn.le)
    linarith
  have hVk : finrank K V = k := by rw [← finrank_extendPi (Ω := Ω), hV]
  -- Lemma 6.1
  obtain ⟨W, hWspan, hWdim, hWH⟩ := exists_extendPi_span_compound_eq G hGdet kF e hVk hGV
  -- the wedges
  set f : Set.powersetCard (Fin n) p → Fin N → Ω := fun s ↦ G.compound p s ∘ e.symm
  have hf : LinearIndependent Ω f := linearIndependent_compound_comp hGdet e
  set ν : Set.powersetCard (Fin n) p → ℝ := fun s ↦ ∏ i ∈ s.val, lam i
  have hνpos : ∀ s, 0 < ν s := fun s ↦ prod_pos fun i _ ↦ hpos i
  have hwedge : ∀ s, h' (f s) ≤ C₁ * ν s := fun s ↦ by
    refine (qHeight_compound_le L c e hQ1 hGdet s).trans ?_
    calc (p.factorial : ℝ) * ∏ i ∈ s.val, h (G i) ≤ p.factorial * ∏ i ∈ s.val, (2 * lam i) :=
          mul_le_mul_of_nonneg_left (prod_le_prod₀ (fun i _ ↦ hGh0 i) fun i _ ↦ hGb i)
            (Nat.cast_nonneg _)
      _ = C₁ * ν s := by
          rw [prod_mul_distrib, prod_const, Set.powersetCard.card_eq s]
          simp only [C₁, ν]
          ring
  have hh'0 : ∀ y, 0 ≤ h' y := fun y ↦ by
    rw [hh']
    exact L'.absMulHeight_nonneg _ _
  set top := topSet kF
  set β := C₁ * ν top * Q ^ (-(g / 2))
  have hβ : 0 < β := mul_pos (mul_pos hC₁ (hνpos top)) (Real.rpow_pos_of_pos hQ0 _)
  have hwedge' : ∀ s ≠ top, h' (f s) ≤ β := fun s hs ↦ by
    refine (hwedge s).trans ?_
    have h1 := prod_le_prod_topSet_mul (k := kF) hk0 hpos hmono hs
    calc C₁ * ν s ≤ C₁ * (ν top * (lam ⟨k - 1, by omega⟩ / lam kF)) :=
          mul_le_mul_of_nonneg_left h1 hC₁.le
      _ ≤ C₁ * (ν top * Q ^ (-(g / 2))) := by gcongr; exact (hνpos top).le
      _ = β := by simp only [β]; ring
  -- `λ̂_N ≥ c₂ ν_top`, from Prop. 9.2 for `L` and `L'` (the products of Lemma 17.2)
  set S' := univ.filter fun s : Set.powersetCard (Fin n) p ↦ s ≠ top
  have hS'e : S' = univ.erase top := filter_ne' univ top
  have hS' : #S' = N - 1 := by
    rw [hS'e, card_erase_of_mem (mem_univ _), card_univ]
  have hprod_ν : (∏ s ∈ S', ν s) * ν top = (∏ i, lam i) ^ N' := by
    rw [hS'e, prod_erase_mul _ _ (mem_univ _),
      Set.powersetCard.prod_eq_prod_powersetCard (f := fun t ↦ ∏ i ∈ t, lam i),
      Finset.prod_powersetCard_prod hp1, Fintype.card_fin, prod_pow]
  have hsplit : ∀ j : ℕ, 1 ≤ j → ∀ F : ℕ → ℝ,
      ∏ i ∈ range j, F i = (∏ i ∈ range (j - 1), F i) * F (j - 1) := by
    intro j hj F
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    simp [prod_range_succ]
  have hPiL : ∏ i, lam i ≤ C₀ * Q ^ (-c.sum) := by
    have h1 := prod_heightInf_le' (Ω := Ω) (by omega : n = n - 1 + 1) L c hQ1
    have h2 : ∏ i, lam i = (∏ i ∈ range (n - 1), heightInf Ω h (i + 1)) * heightInf Ω h n := by
      rw [Fin.prod_univ_eq_prod_range (fun i ↦ heightInf Ω h (i + 1)) n,
        hsplit n (by omega), Nat.sub_add_cancel (by omega : 1 ≤ n)]
    rw [h2]
    simpa [C₀, mul_assoc] using h1
  have hsort := prod_heightInf_le_prod Ω h' f (fun s ↦ hh'0 _) S'
    (hf.linearIndepOn (s := (S' : Set _)))
  rw [hS'] at hsort
  have hB' := hBQ Q hQ1
  have hNsplit : ∏ j ∈ range N, heightInf Ω h' (j + 1) =
      (∏ j ∈ range (N - 1), heightInf Ω h' (j + 1)) * heightInf Ω h' N := by
    rw [hsplit N (by omega), Nat.sub_add_cancel (by omega : 1 ≤ N)]
  have hlamN : c₂ * ν top ≤ heightInf Ω h' N := by
    have hS'b : ∏ s ∈ S', h' (f s) ≤ C₁ ^ (N - 1) * ∏ s ∈ S', ν s := by
      rw [← hS', ← prod_const, ← prod_mul_distrib]
      exact prod_le_prod₀ (fun s _ ↦ hh'0 _) fun s _ ↦ hwedge s
    have hQpow : Q ^ (-c'.sum) = (Q ^ (-c.sum)) ^ N' := by
      rw [hsum', ← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]
      ring_nf
    have hlamN0 : 0 ≤ heightInf Ω h' N := heightInf_nonneg _
    have hlow : B * Q ^ (-c'.sum) * ν top ≤
        C₁ ^ (N - 1) * (C₀ * Q ^ (-c.sum)) ^ N' * heightInf Ω h' N := by
      calc B * Q ^ (-c'.sum) * ν top
          ≤ (∏ j ∈ range (N - 1), heightInf Ω h' (j + 1)) * heightInf Ω h' N * ν top := by
            rw [← hNsplit]
            exact mul_le_mul_of_nonneg_right hB' (hνpos top).le
        _ ≤ (C₁ ^ (N - 1) * ∏ s ∈ S', ν s) * heightInf Ω h' N * ν top := by
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hsort.trans hS'b)
              (heightInf_nonneg _)) (hνpos top).le
        _ = C₁ ^ (N - 1) * (∏ i, lam i) ^ N' * heightInf Ω h' N := by
            rw [← hprod_ν]
            ring
        _ ≤ C₁ ^ (N - 1) * (C₀ * Q ^ (-c.sum)) ^ N' * heightInf Ω h' N := by
            gcongr
            exact prod_nonneg fun i _ ↦ (hpos i).le
    rw [hQpow, mul_pow] at hlow
    have hq : 0 < (Q ^ (-c.sum)) ^ N' := pow_pos (Real.rpow_pos_of_pos hQ0 _) _
    have hden : 0 < C₁ ^ (N - 1) * C₀ ^ N' := by positivity
    rw [show c₂ * ν top = B * ν top / (C₁ ^ (N - 1) * C₀ ^ N') by simp only [c₂]; ring,
      div_le_iff₀ hden]
    refine le_of_mul_le_mul_right ?_ hq
    calc B * ν top * (Q ^ (-c.sum)) ^ N' = B * (Q ^ (-c.sum)) ^ N' * ν top := by ring
      _ ≤ _ := hlow
      _ = _ := by ring
  -- Theorem 16.1 for `L'`: the span of the wedges is the destabilizing subspace of `(L', c')`
  have hTw_le : W.extendPi Ω ≤ heightSpace Ω h' β := by
    rw [hWspan]
    refine span_le.2 ?_
    rintro _ ⟨s, hs, rfl⟩
    exact mem_heightSpace (hwedge' s hs)
  have hβN : β * Q ^ (g / 4) ≤ heightInf Ω h' N := by
    refine le_trans ?_ hlamN
    have hQg : Q ^ (-(g / 2)) * Q ^ (g / 4) = (Q ^ (g / 4))⁻¹ := by
      rw [← Real.rpow_add hQ0, ← Real.rpow_neg hQ0.le]
      ring_nf
    have hQ4 : 0 < Q ^ (g / 4) := Real.rpow_pos_of_pos hQ0 _
    have hC : C₁ * (Q ^ (g / 4))⁻¹ ≤ c₂ := by
      rw [← div_eq_mul_inv, div_le_iff₀ hQ4]
      rw [div_lt_iff₀ hc₂] at hQc
      linarith
    calc β * Q ^ (g / 4) = C₁ * (Q ^ (g / 4))⁻¹ * ν top := by
          simp only [β]
          rw [mul_assoc, hQg]
          ring
      _ ≤ c₂ * ν top := mul_le_mul_of_nonneg_right hC (hνpos top).le
  have hdimW : finrank Ω (W.extendPi Ω) + 1 = N := by rw [finrank_extendPi]; omega
  have hdest := hQ₁ Q hQ1 hQQ₁ (W.extendPi Ω) hdimW β hβ hTw_le hβN
  have h174 := L'.arakelovMulHeight_le_of_isDestabilizing c' hdest hdimW rfl
  -- the constants
  have hHL : 1 ≤ L.arakelovFormHeight := by
    have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    exact L.one_le_arakelovFormHeight
  have hH' : L'.arakelovFormHeight ≤ L.arakelovFormHeight ^ p :=
    (L.exteriorPower p).arakelovFormHeight_reindex_le e |>.trans
      (L.arakelovFormHeight_exteriorPower_le p)
  have hH'0 : 0 ≤ L'.arakelovFormHeight :=
    Real.iSup_nonneg fun _ ↦ (NumberField.arakelovMulHeight_pos _).le
  have hexp4 : p * ((N - 1) * (N - 1)) ≤ 4 ^ n := by
    have h1 := Nat.mul_choose_sq_le (n := n) (p := p) (by omega)
    rw [← hNchoose] at h1
    calc p * ((N - 1) * (N - 1)) ≤ p * N ^ 2 := by
          rw [sq]
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _))
      _ ≤ 4 ^ n := h1
  rw [← hWH]
  calc W.arakelovMulHeight ≤ L'.arakelovFormHeight ^ ((N - 1) * (N - 1)) := h174
    _ ≤ (L.arakelovFormHeight ^ p) ^ ((N - 1) * (N - 1)) := pow_le_pow_left₀ hH'0 hH' _
    _ = L.arakelovFormHeight ^ (p * ((N - 1) * (N - 1))) := by rw [← pow_mul]
    _ ≤ L.arakelovFormHeight ^ (4 ^ n) := pow_le_pow_right₀ hHL hexp4

end NumberField.FormSystem
