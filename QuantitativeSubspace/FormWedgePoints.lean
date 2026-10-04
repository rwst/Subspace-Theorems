/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.FormInfimaGap

-- Used only inside proofs.
import ArithmeticHeights.CauchyBinet

/-!
# The points `ĥ_j(Q)` and the exponents `ĉ_{i,v₀}(Q)`

J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative Subspace Theorem*,
Ann. of Math. **177** (2013), 513–590, (11.8)–(11.17), Lemma 11.4 (11.21), (11.22) and
Lemma 11.6.

Let `(L, c)` satisfy (8.3), (8.4), (8.8), (8.9) and let `Q` satisfy (9.3), (9.4). Lemma 9.4 gives
`0 < k < n` with `λ_k ≤ Q^{-δ/(n-1)} λ_{k+1}`. Davenport's lemma (EF13 Lemma 11.3) gives a basis
`h_1, …, h_n` of `Ωⁿ` with local bounds `Q^{c_iw}` off `v₀` and `3^{n²} min(λ_i, λ_j)` above
`v₀`, with `h_1, …, h_k` spanning `T_k(Q)`. In the exterior power `Λ^{n-k}`, the wedges
`ĥ_J = h_{j_1} ∧ ⋯ ∧ h_{j_{n-k}}`, `J ≠ I_N = {k+1, …, n}`, span a hyperplane `T̂` with
`H₂(T̂) = H₂(T_k(Q)) ≥ Q^{δ/3Rⁿ}` (Lemmas 6.1, 10.3, i.e. Lemma 11.6), and they satisfy the bounds
(11.17): the local factors of `(L̂, ĉ)` are at most `1` off `v₀`, and above `v₀` the Plücker
coordinate at `I` is at most `Q^{ĉ_{I,v₀}(Q)}`, where `Q^{ĉ_{I,v₀}(Q)} = 3^{n³} topBound λ π I`
(11.15). Lemma 11.4: `Σ_I ĉ_{I,v₀}(Q) ≤ -δ/n` and `|ĉ_{I,v₀}(Q)| ≤ n`, the hypotheses of
Prop. 13.6.

The subsets are indexed by `Set.powersetCard (Fin n) (n - k)` with `k : Fin n` 0-based, as in
`FormExteriorPower.lean`: `topSet k = {k, …, n-1}` is EF13's `I_N`.

## Main results

* `NumberField.topBound_eq_prod`: `topBound` is a product of `n - k` distinct infima.
* `NumberField.FormSystem.abs_logb_topBound_le`: EF13 (11.22).
* `NumberField.FormSystem.sum_logb_topBound_le`: EF13 (11.21).
* `NumberField.FormSystem.exists_wedgePoints`: the points `ĥ_J` and exponents `ĉ_{I,v₀}(Q)` with
  (11.17), (11.21), (11.22) and Lemma 11.6.

This is milestone Q4.1b of `QuantitativeSubspace/README.md`.
-/

@[expose] public section

open Module Finset Matrix Submodule Filter Topology
open exteriorPower (plucker)

namespace NumberField

/-- `n 2^{n²} < 3^{n²}` for `n ≥ 1`, the room in Davenport's constant `3^{n²}`. -/
theorem mul_two_pow_sq_lt_three_pow_sq {n : ℕ} (hn : 1 ≤ n) : n * 2 ^ (n ^ 2) < 3 ^ (n ^ 2) := by
  have h4 : ∀ m : ℕ, 1 ≤ m → 2 * 2 ^ (2 * m + 1) ≤ 3 ^ (2 * m + 1) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ m _ ih =>
      have e1 : 2 * 2 ^ (2 * (m + 1) + 1) = 4 * (2 * 2 ^ (2 * m + 1)) := by ring
      have e2 : 3 ^ (2 * (m + 1) + 1) = 9 * 3 ^ (2 * m + 1) := by ring
      omega
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have e1 : 2 ^ ((m + 1) ^ 2) = 2 ^ (m ^ 2) * 2 ^ (2 * m + 1) := by rw [← pow_add]; ring_nf
    have e2 : 3 ^ ((m + 1) ^ 2) = 3 ^ (m ^ 2) * 3 ^ (2 * m + 1) := by rw [← pow_add]; ring_nf
    rw [e1, e2]
    have := h4 m hm
    have hp : 0 < 2 ^ (2 * m + 1) := by positivity
    calc (m + 1) * (2 ^ (m ^ 2) * 2 ^ (2 * m + 1))
        ≤ 2 * m * (2 ^ (m ^ 2) * 2 ^ (2 * m + 1)) := Nat.mul_le_mul_right _ (by omega)
      _ = (m * 2 ^ (m ^ 2)) * (2 * 2 ^ (2 * m + 1)) := by ring
      _ < 3 ^ (m ^ 2) * (2 * 2 ^ (2 * m + 1)) := Nat.mul_lt_mul_of_pos_right ih (by positivity)
      _ ≤ 3 ^ (m ^ 2) * 3 ^ (2 * m + 1) := Nat.mul_le_mul_left _ this

/-! ### `topBound` as a product of `n - k` infima -/

section TopBound

variable {n : ℕ} {k : Fin n} {lam : Fin n → ℝ} {π : Equiv.Perm (Fin n)}

/-- **`topBound λ π I` is a product of `n - k` distinct `λ_i`** (EF13, proof of (11.22)): `ν_J`
for `J = π⁻¹(I)`, or `λ_{k-1} ∏_{i > k} λ_i` for `J = I_N`. -/
theorem topBound_eq_prod (hk : 0 < (k : ℕ)) (hpos : ∀ i, 0 < lam i)
    (I : Set.powersetCard (Fin n) (n - k)) :
    ∃ s : Finset (Fin n), #s = n - k ∧ topBound lam π I = ∏ i ∈ s, lam i := by
  classical
  unfold topBound
  split_ifs with h
  · set k' : Fin n := ⟨k - 1, by omega⟩
    have hkT : k ∈ (topSet k).val := (mem_topSet k).2 le_rfl
    have hk'T : k' ∉ (topSet k).val := fun h ↦ by
      have := (mem_topSet k).1 h
      simp only [k'] at this
      omega
    have hk'e : k' ∉ (topSet k).val.erase k := fun h ↦ hk'T (mem_of_mem_erase h)
    refine ⟨insert k' ((topSet k).val.erase k), ?_, ?_⟩
    · rw [card_insert_of_notMem hk'e, card_erase_of_mem hkT, (topSet k).prop]
      omega
    · have hI := (forall_le_symm_iff I).1 h
      have hprod : ∏ i ∈ I.val, lam (π.symm i) = ∏ i ∈ (topSet k).val, lam i := by
        rw [hI]
        simp [prod_map]
      rw [hprod, prod_insert hk'e, ← mul_prod_erase _ _ hkT]
      field_simp [(hpos k).ne']
  · refine ⟨I.val.map π.symm.toEmbedding, ?_, ?_⟩
    · rw [card_map, I.prop]
    · rw [prod_map]
      rfl

end TopBound

namespace FormSystem

variable {K : Type*} [Field K] [NumberField K] {n : ℕ} {Ω : Type*} [Field Ω] [Algebra K Ω]
  [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω] (L : FormSystem K (Fin n)) (c : FormExponent K (Fin n))

/-! ### EF13 Lemma 11.4, (11.21) and (11.22) -/

/-- **EF13 (11.22)**: `|ĉ_{I,v₀}(Q)| ≤ n` for `Q^{ĉ_{I,v₀}(Q)} = 3^{n³} topBound λ π I`, from
Lemma 9.3 and `3^{n³} ≤ Q^{1/2}`. -/
theorem abs_logb_topBound_le (hn : 0 < n) (hc₀ : c.sum = 0)
    (hc : (∑ v, ⨆ i, c.arch v i) + ∑ᶠ v, ⨆ i, c.fin v i ≤ 1) {Q : ℝ} (hQ : 1 < Q)
    (hQ₁ : n * L.absFormHeight ^ ((L.forms.card.choose n : ℕ) : ℝ) ≤ Q ^ (1 / (3 * n) : ℝ))
    (hQ₂ : √2 ^ (n * (n - 1)) * L.absDet ≤ Q ^ (1 / 6 : ℝ))
    (hQ₃ : (3 : ℝ) ^ (n ^ 3) ≤ Q ^ (1 / 2 : ℝ)) {k : Fin n} (hk : 0 < (k : ℕ))
    (π : Equiv.Perm (Fin n)) (I : Set.powersetCard (Fin n) (n - k)) :
    |Real.logb Q (3 ^ (n ^ 3) * topBound
      (fun i : Fin n ↦ L.successiveInf (c.weight (zero_lt_one.trans hQ)) Ω (i + 1)) π I)| ≤ n := by
  have hQ0 : 0 < Q := zero_lt_one.trans hQ
  set lam : Fin n → ℝ := fun i ↦ L.successiveInf (c.weight hQ0) Ω (i + 1)
  have hpos : ∀ i, 0 < lam i := L.successiveInf_pos _
  obtain ⟨s, hs, hst⟩ := topBound_eq_prod (π := π) hk hpos I
  have hlow := L.rpow_le_prod_successiveInf c hn hc hQ.le hQ₁ s (Ω := Ω)
  have hup := L.prod_successiveInf_le_rpow c hn hc₀ hc hQ.le hQ₁ hQ₂ s (Ω := Ω)
  have hP : 0 < topBound lam π I := topBound_pos hpos I
  have hD : (1 : ℝ) ≤ 3 ^ (n ^ 3) := one_le_pow₀ (by norm_num)
  have hsn : (#s : ℝ) = n - k := by rw [hs, Nat.cast_sub (by omega)]
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkn : (k : ℝ) ≤ n - 1 := by
    have : (k : ℕ) + 1 ≤ n := k.2
    have h' : ((k : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast this
    linarith
  rw [abs_le]
  constructor
  · -- `Q^{-n} ≤ 3^{n³} topBound`
    rw [Real.le_logb_iff_rpow_le hQ (by positivity)]
    calc Q ^ (-(n : ℝ)) ≤ Q ^ (-(#s + 1 / 2) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hQ.le (by rw [hsn]; linarith)
      _ ≤ topBound lam π I := by rw [hst]; exact hlow
      _ ≤ 3 ^ (n ^ 3) * topBound lam π I := le_mul_of_one_le_left hP.le hD
  · -- `3^{n³} topBound ≤ Q^n`
    rw [Real.logb_le_iff_le_rpow hQ (by positivity)]
    calc 3 ^ (n ^ 3) * topBound lam π I ≤ Q ^ (1 / 2 : ℝ) * Q ^ ((n - #s + 1 / 2) : ℝ) := by
          rw [hst]
          exact mul_le_mul hQ₃ hup (prod_nonneg fun i _ ↦ (hpos i).le)
            (Real.rpow_nonneg hQ0.le _)
      _ = Q ^ ((n - #s + 1) : ℝ) := by rw [← Real.rpow_add hQ0]; ring_nf
      _ ≤ Q ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le hQ.le (by rw [hsn]; linarith)

/-- **EF13 (11.21)**: `Σ_I ĉ_{I,v₀}(Q) ≤ -δ/n`, from (9.2), the gap `λ_k ≤ Q^{-δ/(n-1)} λ_{k+1}`
and `(3^{n³} 2^{n(n-1)/2} H_L)^{2ⁿ} ≤ Q^{δ/n(n-1)}`. -/
theorem sum_logb_topBound_le (hn : 2 ≤ n) (hc₀ : c.sum = 0) {Q δ : ℝ}
    (hQ : 1 < Q)
    (hQ₄ : (3 ^ (n ^ 3) * (√2 ^ (n * (n - 1)) * L.absFormHeight)) ^ (2 ^ n) ≤
      Q ^ (δ / (n * (n - 1))))
    {k : Fin n} (hk : 0 < (k : ℕ))
    (hgap : L.successiveInf (c.weight (zero_lt_one.trans hQ)) Ω k ≤
      Q ^ (-(δ / (n - 1))) * L.successiveInf (c.weight (zero_lt_one.trans hQ)) Ω (k + 1))
    (π : Equiv.Perm (Fin n)) :
    ∑ I : Set.powersetCard (Fin n) (n - k), Real.logb Q (3 ^ (n ^ 3) * topBound
      (fun i : Fin n ↦ L.successiveInf (c.weight (zero_lt_one.trans hQ)) Ω (i + 1)) π I) ≤
        -δ / n := by
  have hQ0 : 0 < Q := zero_lt_one.trans hQ
  set lam : Fin n → ℝ := fun i ↦ L.successiveInf (c.weight hQ0) Ω (i + 1)
  have hpos : ∀ i, 0 < lam i := L.successiveInf_pos _
  rw [sum_logb_topBound hk hpos (by positivity) Q]
  set D : ℝ := 3 ^ (n ^ 3)
  set C : ℝ := √2 ^ (n * (n - 1)) * L.absFormHeight
  set N := n.choose (n - k)
  set N' := (n - 1).choose (n - k - 1)
  have hD : 1 ≤ D := one_le_pow₀ (by norm_num)
  have hH1 : 1 ≤ L.absFormHeight := Real.one_le_rpow L.one_le_mulFormHeight (by positivity)
  have hC : 1 ≤ C :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (Real.one_le_sqrt.2 one_le_two)) hH1
  have hup := L.prod_successiveInf_weight_le (Ω := Ω) (by omega) c hQ0
  rw [hc₀, neg_zero, Real.rpow_zero, mul_one] at hup
  have hprodC : ∏ i, lam i ≤ C := hup.trans (mul_le_mul_of_nonneg_left L.absDet_le_absFormHeight
    (by positivity))
  have hratio : lam ⟨k - 1, by omega⟩ / lam k ≤ Q ^ (-(δ / (n - 1))) := by
    rw [div_le_iff₀ (hpos k)]
    have e1 : lam ⟨k - 1, by omega⟩ = L.successiveInf (c.weight hQ0) Ω k := by
      simp only [lam]
      congr 1
      omega
    have e2 : lam k = L.successiveInf (c.weight hQ0) Ω (k + 1) := rfl
    rw [e1, e2]
    exact hgap
  have hN : N ≤ 2 ^ n := Nat.choose_le_two_pow n _
  have hN' : N' ≤ 2 ^ n := (Nat.choose_le_two_pow _ _).trans
    (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le n 1))
  have hn1 : (0 : ℝ) < n - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hprod0 : 0 ≤ ∏ i, lam i := prod_nonneg fun i _ ↦ (hpos i).le
  have hbound : D ^ N * ((∏ i, lam i) ^ N' * (lam ⟨k - 1, by omega⟩ / lam k)) ≤
      Q ^ (-δ / n) := by
    calc D ^ N * ((∏ i, lam i) ^ N' * (lam ⟨k - 1, by omega⟩ / lam k))
        ≤ D ^ (2 ^ n) * (C ^ (2 ^ n) * Q ^ (-(δ / (n - 1)))) :=
          mul_le_mul (pow_le_pow_right₀ hD hN)
            (mul_le_mul ((pow_le_pow_left₀ hprod0 hprodC _).trans (pow_le_pow_right₀ hC hN'))
              hratio (div_nonneg (hpos _).le (hpos _).le) (pow_nonneg (zero_le_one.trans hC) _))
            (mul_nonneg (pow_nonneg hprod0 _) (div_nonneg (hpos _).le (hpos _).le))
            (pow_nonneg (zero_le_one.trans hD) _)
      _ = (D * C) ^ (2 ^ n) * Q ^ (-(δ / (n - 1))) := by ring
      _ ≤ Q ^ (δ / (n * (n - 1))) * Q ^ (-(δ / (n - 1))) := by gcongr
      _ = Q ^ (-δ / n) := by
          rw [← Real.rpow_add hQ0]
          congr 1
          have hn0 : (n : ℝ) ≠ 0 := by positivity
          field_simp
          ring
  have hpos' : 0 < D ^ N * ((∏ i, lam i) ^ N' * (lam ⟨k - 1, by omega⟩ / lam k)) :=
    mul_pos (pow_pos (zero_lt_one.trans_le hD) _) (mul_pos (pow_pos (prod_pos fun i _ ↦ hpos i) _)
      (div_pos (hpos _) (hpos _)))
  rw [Real.logb_le_iff_le_rpow hQ hpos']
  exact hbound

/-! ### Davenport's points and their wedges -/

omit [IsAlgClosed Ω] in
/-- **EF13 (11.1)**: an `ε > 0` with `(1+ε)² λ_i < λ_{i+1}` at every jump and
`(1+ε)^{n+1} n 2^{n²} ≤ 3^{n²}`. -/
theorem exists_eps_davenport (hn : 0 < n) (a : FormWeight K (Fin n)) :
    ∃ ε > 0, (∀ i : ℕ, i + 1 < n → L.successiveInf a Ω (i + 1) < L.successiveInf a Ω (i + 2) →
      (1 + ε) ^ 2 * L.successiveInf a Ω (i + 1) < L.successiveInf a Ω (i + 2)) ∧
      (1 + ε) ^ (n + 1) * n * 2 ^ (n ^ 2) ≤ 3 ^ (n ^ 2) := by
  set lam := fun i ↦ L.successiveInf a Ω i
  have h1 : ∀ i : Fin n, ∀ᶠ ε in 𝓝 (0 : ℝ), (i : ℕ) + 1 < n → lam (i + 1) < lam (i + 2) →
      (1 + ε) ^ 2 * lam (i + 1) < lam (i + 2) := by
    intro i
    by_cases h : (i : ℕ) + 1 < n ∧ lam (i + 1) < lam (i + 2)
    · have ht : Tendsto (fun ε : ℝ ↦ (1 + ε) ^ 2 * lam (i + 1)) (𝓝 0)
          (𝓝 ((1 + 0) ^ 2 * lam (i + 1))) :=
        ((continuous_const.add continuous_id).pow 2 |>.mul continuous_const).tendsto 0
      rw [add_zero, one_pow, one_mul] at ht
      exact (ht.eventually (gt_mem_nhds h.2)).mono fun ε hε _ _ ↦ hε
    · exact Eventually.of_forall fun ε h1 h2 ↦ absurd ⟨h1, h2⟩ h
  have h2 : ∀ᶠ ε in 𝓝 (0 : ℝ), (1 + ε) ^ (n + 1) * n * 2 ^ (n ^ 2) ≤ (3 : ℝ) ^ (n ^ 2) := by
    have ht : Tendsto (fun ε : ℝ ↦ (1 + ε) ^ (n + 1) * n * 2 ^ (n ^ 2)) (𝓝 0)
        (𝓝 ((1 + 0) ^ (n + 1) * n * 2 ^ (n ^ 2))) :=
      ((((continuous_const.add continuous_id).pow (n + 1)).mul continuous_const).mul
        continuous_const).tendsto 0
    rw [add_zero, one_pow, one_mul] at ht
    have hlt : (n : ℝ) * 2 ^ (n ^ 2) < 3 ^ (n ^ 2) := by
      exact_mod_cast mul_two_pow_sq_lt_three_pow_sq hn
    exact (ht.eventually (gt_mem_nhds hlt)).mono fun ε hε ↦ hε.le
  have h3 := ((eventually_all.2 h1).and h2).filter_mono (nhdsWithin_le_nhds (s := Set.Ioi 0))
  obtain ⟨ε, ⟨hε1, hε2⟩, hε⟩ := (h3.and (self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)))).exists
  exact ⟨ε, hε, fun i hi ↦ hε1 ⟨i, by omega⟩ hi, hε2⟩

/-- **The points `ĥ_J(Q)` and the exponents `ĉ_{I,v₀}(Q)`** (EF13 (11.8)–(11.17), Lemma 11.4
(11.21), (11.22), Lemma 11.6). Let `(L, c)` satisfy (8.3), (8.4), (8.8) at `v₀`, (8.9), with
`r ≤ R` forms and `n ≤ R`, and let `Q > 1` satisfy the size conditions of Lemmas 9.3, 10.3,
(11.21), (11.22), with Lemma 9.4's gap `λ_k ≤ Q^{-δ/(n-1)} λ_{k+1}` at `0 < k < n` (as
`k : Fin n`). Then there are a number field `E ⊆ Ω`, exponents `e = ĉ_{·,v₀}(Q)` and points
`x_J ∈ E^{C(n,n-k)}` such that:
* `|e_I| ≤ n` and `Σ_I e_I ≤ -δ/n`;
* for `J ≠ I_N`, the local factors of `x_J` for `(L̂, ĉ)` are at most `1` at the infinite places
  and at the finite places off `v₀`, and `‖x_J(I)‖_w ≤ Q^{e_I}` above `v₀`, in the relative
  normalization;
* the `x_J`, `J ≠ I_N`, are linearly independent and span the extension of a subspace `W` of
  `K^N`, `N = C(n, n-k)`, of dimension `N - 1` with `H₂(W)^{1/[K:ℚ]} ≥ Q^{δ/3Rⁿ}`. -/
theorem exists_wedgePoints (hLs : L.IsNormalSemistable c Ω) {v₀ : FinitePlace K}
    (hL₀ : L.fin v₀ = 1) (hc₀ : c.fin v₀ = 0) (hn : 2 ≤ n) {R : ℕ} (hR : #L.forms ≤ R)
    (hnR : n ≤ R) {Q δ : ℝ} (hQ : 1 < Q) (hδ : 0 < δ) (k : Fin n) (hk : 0 < (k : ℕ))
    (hgap' : L.successiveInf (c.weight (zero_lt_one.trans hQ)) Ω k ≤
      Q ^ (-(δ / (n - 1))) * L.successiveInf (c.weight (zero_lt_one.trans hQ)) Ω (k + 1))
    (hQ₁ : n * L.absFormHeight ^ ((L.forms.card.choose n : ℕ) : ℝ) ≤ Q ^ (1 / (3 * n) : ℝ))
    (hQ₂ : √2 ^ (n * (n - 1)) * L.absDet ≤ Q ^ (1 / 6 : ℝ))
    (hQ₃ : (3 : ℝ) ^ (n ^ 3) ≤ Q ^ (1 / 2 : ℝ))
    (hQ₄ : (3 ^ (n ^ 3) * (√2 ^ (n * (n - 1)) * L.absFormHeight)) ^ (2 ^ n) ≤
      Q ^ (δ / (n * (n - 1))))
    (hbig : (2 ^ (3 * n ^ 2) * L.absFormHeight) ^ (3 * n * R ^ n) ≤ Q ^ δ) :
    ∃ (E : IntermediateField K Ω) (_ : NumberField E) (e : Set.powersetCard (Fin n) (n - k) → ℝ)
      (x : Set.powersetCard (Fin n) (n - k) → Set.powersetCard (Fin n) (n - k) → E),
      (∀ I, |e I| ≤ n) ∧ ∑ I, e I ≤ -δ / n ∧
      (∀ J ≠ topSet k, ∀ w : InfinitePlace E, (L.exteriorPower (n - k)).archFactor
        ((c.weight (zero_lt_one.trans hQ)).exteriorPower (n - k)) w (x J) ≤ 1) ∧
      (∀ J ≠ topSet k, ∀ w : FinitePlace E, w.under K ≠ v₀ → (L.exteriorPower (n - k)).finFactor
        ((c.weight (zero_lt_one.trans hQ)).exteriorPower (n - k)) w (x J) ≤ 1) ∧
      (∀ J ≠ topSet k, ∀ I, ∀ w : FinitePlace E, w.under K = v₀ →
        w (x J I) ≤ ((Q ^ e I) ^ finrank ℚ K) ^ w.localDegree K) ∧
      LinearIndepOn Ω (fun J I ↦ (x J I : Ω)) {J | J ≠ topSet k} ∧
      ∃ W : Submodule K (Fin (Fintype.card (Set.powersetCard (Fin n) (n - k))) → K),
        W.extendPi Ω = span Ω ((fun J ↦ (fun I ↦ (x J I : Ω)) ∘
          (Fintype.equivFin (Set.powersetCard (Fin n) (n - k))).symm) '' {J | J ≠ topSet k}) ∧
        finrank K W + 1 = Fintype.card (Set.powersetCard (Fin n) (n - k)) ∧
        Q ^ (δ / (3 * R ^ n)) ≤ W.arakelovMulHeight ^ ((finrank ℚ K : ℝ)⁻¹) := by
  classical
  have hQ0 : 0 < Q := zero_lt_one.trans hQ
  have hn0 : 0 < n := by omega
  set a := c.weight hQ0
  set lam : Fin n → ℝ := fun i ↦ L.successiveInf a Ω (i + 1) with hlam
  have hpos : ∀ i, 0 < lam i := L.successiveInf_pos a
  have hmono : Monotone lam := fun i j hij ↦
    heightInf_mono (by simpa using hij) (by simp [Nat.succ_le_of_lt j.2])
  -- Lemma 9.4's gap
  obtain ⟨k₀, hkn⟩ := k
  have hk0 : 0 < k₀ := hk
  have hgap : L.successiveInf a Ω k₀ ≤ Q ^ (-(δ / (n - 1))) * L.successiveInf a Ω (k₀ + 1) :=
    hgap'
  set k : Fin n := ⟨k₀, hkn⟩
  have hposk1 : 0 < L.successiveInf a Ω (k₀ + 1) := by simpa using hpos k
  have hlt := L.successiveInf_lt_of_le hk0 hkn hQ hδ hposk1 hgap
  -- Davenport's lemma
  obtain ⟨ε, hε, hεgap, hε3⟩ := L.exists_eps_davenport (Ω := Ω) hn0 a
  have hC : 1 < 1 + ε / 2 := by linarith
  obtain ⟨g₀, hg₀li, hg₀⟩ := exists_linearIndependent_le_mul Ω (L.absMulHeight a) hC
    (fun i ↦ by simpa using hpos ⟨i, by simpa using i.2⟩)
  set g : Fin n → Fin n → Ω := g₀ ∘ Fin.cast (Fintype.card_fin n).symm
  have hgli : LinearIndependent Ω g := hg₀li.comp _ (Fin.cast_injective _)
  have hg : ∀ j : Fin n, L.absMulHeight a (g j) ≤ (1 + ε / 2) * L.successiveInf a Ω (j + 1) :=
    fun j ↦ hg₀ _
  have ha : a.fin v₀ = 1 := by
    funext i
    simp [a, FormExponent.weight, hc₀]
  obtain ⟨E, hE, π, h, hspan, harch, hfin, hv0⟩ :=
    L.exists_davenport a hL₀ ha hn0 hε hεgap hε3 hgli hg
  set D : ℝ := 3 ^ (n ^ 3)
  set e : Set.powersetCard (Fin n) (n - (k : ℕ)) → ℝ :=
    fun I ↦ Real.logb Q (D * topBound (k := k) lam π I)
  set x : Set.powersetCard (Fin n) (n - (k : ℕ)) → Set.powersetCard (Fin n) (n - (k : ℕ)) → E :=
    fun J ↦ plucker (n - (k : ℕ)) fun r ↦ h (Set.powersetCard.ofFinEmbEquiv.symm J r)
  -- the matrix of the `h_j`
  set G : Matrix (Fin n) (Fin n) Ω := Matrix.of fun j i ↦ (h j i : Ω)
  have hGtop : ⊤ ≤ span Ω (Set.range G) := by
    have h1 := hspan n le_rfl
    have hu : {j : Fin n | (j : ℕ) < n} = Set.univ := Set.eq_univ_of_forall fun j ↦ j.2
    rw [hu, Set.image_univ, Set.image_univ] at h1
    rw [show Set.range G = Set.range fun j i ↦ (h j i : Ω) from rfl, h1,
      hgli.span_eq_top_of_card_eq_finrank' (by simp)]
  have hGli : LinearIndependent Ω G.row :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hGtop (by simp)
  have hGdet : G.det ≠ 0 :=
    ((Matrix.linearIndependent_rows_iff_isUnit.1 hGli).map Matrix.detMonoidHom).ne_zero
  have hxG : ∀ J, (fun I ↦ (x J I : Ω)) = G.compound (n - (k : ℕ)) J := fun J ↦ by
    funext I
    rw [compound_row]
    exact (_root_.exteriorPower.plucker_map (algebraMap E Ω) (n - (k : ℕ)) _ I).symm
  refine ⟨E, hE, e, x, fun I ↦ ?_, ?_, fun J _ w ↦ ?_, fun J _ w hw ↦ ?_,
    fun J hJ I w hw ↦ ?_, ?_, ?_⟩
  · exact L.abs_logb_topBound_le c hn0 hLs.sum_eq_zero hLs.sum_iSup_le hQ hQ₁ hQ₂ hQ₃ hk π I
  · exact L.sum_logb_topBound_le c hn hLs.sum_eq_zero hQ hQ₄ hk hgap π
  · refine L.archFactor_exteriorPower_plucker_le a (by simp) w fun r ↦ ?_
    simpa using harch _ w
  · exact L.finFactor_exteriorPower_plucker_le a w fun r ↦ hfin _ w hw
  · -- above `v₀`
    set m := finrank ℚ K * w.localDegree K
    have hb : ∀ i j, w (h j (π i)) ≤ (3 ^ (n ^ 2) * min (lam i) (lam j)) ^ m := fun i j ↦ by
      rw [pow_mul]
      exact hv0 i j w hw
    have h2 := FinitePlace.apply_plucker_le_topBound w hk hpos hmono (by positivity) m hb hJ I
    have hP := topBound_pos (π := π) hpos I
    have hpow : ((3 : ℝ) ^ (n ^ 2)) ^ (n - (k : ℕ)) ≤ D := by
      rw [← pow_mul]
      exact pow_le_pow_right₀ (by norm_num) (by
        have : n - (k : ℕ) ≤ n := Nat.sub_le _ _
        calc n ^ 2 * (n - (k : ℕ)) ≤ n ^ 2 * n := Nat.mul_le_mul_left _ this
          _ = n ^ 3 := by ring)
    have hQe : Q ^ e I = D * topBound (k := k) lam π I :=
      Real.rpow_logb hQ0 hQ.ne' (mul_pos (by positivity) hP)
    rw [hQe, ← pow_mul]
    exact h2.trans (pow_le_pow_left₀ (mul_nonneg (by positivity) hP.le)
      (mul_le_mul_of_nonneg_right hpow hP.le) _)
  · -- linear independence
    have hrows : LinearIndependent Ω (G.compound (n - (k : ℕ))).row :=
      linearIndependent_rows_iff_isUnit.2 ((isUnit_iff_isUnit_det _).2
        (det_compound_ne_zero (n - (k : ℕ)) hGdet).isUnit)
    have : (fun J I ↦ (x J I : Ω)) = (G.compound (n - (k : ℕ))).row := funext hxG
    rw [this]
    exact hrows.linearIndepOn _
  · -- Lemma 11.6
    set T := L.infFlag a Ω k₀
    obtain ⟨V, hV⟩ := Submodule.exists_extendPi_eq (L.infFlag_isDefinedOver a k₀ (Ω := Ω))
    have hTk : finrank Ω T = k₀ := finrank_heightFlag (by simpa using hkn) hlt
    have hVk : finrank K V = k := by
      rw [← Submodule.finrank_extendPi (Ω := Ω), hV, hTk]
    have hH := L.rpow_le_arakelovMulHeight_infFlag c hLs hR hnR hk0 hkn hQ hδ hgap hbig hV
    -- `h_1, …, h_k` lie in `T_k(Q)`
    have hεk : (1 + ε / 2) * L.successiveInf a Ω k₀ < L.successiveInf a Ω (k₀ + 1) := by
      have hj := hεgap (k₀ - 1) (by omega) (by
        rw [show k₀ - 1 + 1 = k₀ by omega, show k₀ - 1 + 2 = k₀ + 1 by omega]
        exact hlt)
      rw [show k₀ - 1 + 1 = k₀ by omega, show k₀ - 1 + 2 = k₀ + 1 by omega] at hj
      have hk0' : 0 ≤ L.successiveInf a Ω k₀ := heightInf_nonneg _
      have : (1 + ε / 2) ≤ (1 + ε) ^ 2 := by nlinarith
      exact (mul_le_mul_of_nonneg_right this hk0').trans_lt hj
    have hgT : ∀ j : Fin n, (j : ℕ) < k₀ → g j ∈ T := fun j hj ↦ by
      by_contra hjT
      have h1 := le_of_notMem_heightFlag hkn hlt hjT
      have h2 : L.absMulHeight a (g j) ≤ (1 + ε / 2) * L.successiveInf a Ω k₀ :=
        (hg j).trans (mul_le_mul_of_nonneg_left (heightInf_mono (by omega) (by simp; omega))
          (by linarith))
      linarith
    have hGV : ∀ i : Fin n, (i : ℕ) < k → G i ∈ V.extendPi Ω := fun i hi ↦ by
      rw [hV]
      have hmem : G i ∈ span Ω ((fun j i ↦ (h j i : Ω)) '' {j | (j : ℕ) < k₀}) :=
        subset_span ⟨i, hi, rfl⟩
      rw [hspan k₀ hkn.le] at hmem
      exact span_le.2 (by rintro _ ⟨j, hj, rfl⟩; exact hgT j hj) hmem
    obtain ⟨W, hWspan, hWdim, hWH⟩ :=
      exists_extendPi_span_compound_eq G hGdet k (Fintype.equivFin _) hVk hGV
    refine ⟨W, ?_, hWdim, ?_⟩
    · rw [hWspan]
      congr 1
      refine Set.image_congr fun J _ ↦ ?_
      simp only [Function.comp_def]
      rw [← hxG J]
    · rw [hWH]
      exact hH

end FormSystem

end NumberField
