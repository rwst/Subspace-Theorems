/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.RingTheory.MvPolynomial.PointIdeal
public import QuantitativeSubspace.ZerosOfIndexHeight

-- Used only inside proofs.
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Evertse's Roth lemma (Evertse 1995, Thm. 3 and §5)

J.-H. Evertse, *An explicit version of Faltings' Product theorem and an improvement of Roth's
lemma*, Acta Arith. **73** (1995), Thm. 3: on `(ℙ¹)^m`, if `δ_i / δ_{i+1}` is large compared with
`1/ε` (not with `(1/ε)^m`, as in the product theorem), a polynomial of multidegree `δ` cannot
vanish to index `ε` at a point `P` all of whose coordinates `P_k` have large height.

* `MvPolynomial.exists_eRk_lt_and_mul_height_le`: the sharper product theorem behind it, for any
  blocks. Under the hypotheses of Rémond's product theorem (`MvPolynomial.productTheorem_height`)
  with `t ≥ 1`, but the ratio condition `δ_i / δ_{i+1} > m / ε` in place of `(m / ε)^t`, some
  projection `Z_k` of `V(𝔭)` to `ℙ^{n_k}` is not onto, and the height bound holds in the type `β`
  of a transcendence basis adapted to the first blocks.
  `MvPolynomial.exists_eRk_lt_and_mul_height_le_indexIdeal` is the same for the zeros of index
  `a`, with Rémond's error term.
* `MvPolynomial.exists_mul_logHeight_le`: Evertse's Roth lemma. If `δ_i / δ_{i+1} > m² / ε` and
  `F` vanishes to index `ε` at `P` (`MvPolynomial.indexIdeal_le_pointIdeal_iff`), some `k` has
  `δ_k h(P_k) ≤ max(1, m²/ε)^m ([K : ℚ] h(ℙ¹) |δ| + m (h(F) + [K : ℚ] (|δ| log 2 +
  m log |δ| + m)))`. Evertse's condition is `δ_i / δ_{i+1} ≥ 2m³/ε`, and his bound is
  `δ_k h(P_k) ≤ (3m³/ε)^m (|δ| + h(F))` in absolute heights.

The proof of the sharper product theorem compares two transcendence bases of `K[X]/𝔭` made of
variables, `T` adapted to the last blocks (which carries the multiplicity estimate) and `T'`
adapted to the first blocks (whose type `β` has `d_β(𝔭) ≥ 1`), as in
`MvPolynomial.productTheorem_of_basis`. With the cut excesses
`G_k = r(P_k) + r(σ \ P_k) - r(σ) ≥ 0`, `P_k = {s | b s < k}`, Abel summation gives
`∑_i (c_i - c'_i) log δ_i = ∑_k G_{k+1} log (δ_k / δ_{k+1})`, `c_i` and `c'_i` the numbers of
variables of block `i` outside `T` and `T'`. Rémond uses only that one `G_k` is positive when
`V(𝔭)` is not a product. Evertse's Lemma 11 is, in the algebraic matroid of the variables, the
bound `∑_k G_k ≥ ∑_i r(B_i) - r(σ)` (`MvPolynomial.exists_cutExcess`), by submodularity of the
rank: when every projection is onto, `∑_k G_k ≥ codim V(𝔭) = t`, and then
`δ_i / δ_{i+1} > m / ε` already contradicts `ε^t ∏ δ_i^{c_i} ≤ m^t ∏ δ_i^{c'_i}`. Evertse proves
Lemma 11 for `(ℙ¹)^m` with tangent spaces at smooth points.

The Roth lemma then follows Evertse's §5. Descend along `Z_0 ⊇ Z_{ε/m} ⊇ ⋯ ⊇ Z_ε` to a component
`V(𝔭) ∋ P` of two consecutive ones (`MvPolynomial.exists_minimalPrimes_indexIdeal_le` below the
point ideal `MvPolynomial.pointIdeal b P`). A projection of `V(𝔭)` to a factor `ℙ¹` is a point,
hence `P_k` (`MvPolynomial.sub_mem_of_eRk_le_one`), and the point bound (L) of the height theory
(`MvPolynomial.MultiprojectiveHeight.logHeight_mul_le_cycleHeight`) gives
`h(P_k) ≤ d_β(𝔭) h(P_k) ≤ h_{β + ε_k}(𝔭)`.

This is Layer Q1.4 of the `QuantitativeSubspace` roadmap.
-/

@[expose] public section

open Finset

namespace MvPolynomial

section Abel

/-- **Summation by parts** with `G 0 = 0`. -/
theorem sum_range_sub_mul_eq (G L : ℕ → ℝ) (hG : G 0 = 0) (n : ℕ) :
    ∑ i ∈ range n, (G (i + 1) - G i) * L i =
      G n * L n + ∑ i ∈ range n, G (i + 1) * (L i - L (i + 1)) := by
  induction n with
  | zero => simp [hG]
  | succ n ih =>
    rw [sum_range_succ, ih, sum_range_succ]
    ring

/-- If nonnegative weights `G_i` sum to at least `t ≥ 1`, and `g_i ≥ 0` exceeds `C` wherever
`G_i ≠ 0`, then `t C < ∑_i G_i g_i`. -/
theorem mul_lt_sum_mul {n t : ℕ} {G g : ℕ → ℝ} {C : ℝ} (hG : ∀ i ∈ range n, 0 ≤ G i)
    (hg : ∀ i ∈ range n, G i ≠ 0 → C < g i) (hg0 : ∀ i ∈ range n, 0 ≤ g i) (ht : 1 ≤ t)
    (hsum : (t : ℝ) ≤ ∑ i ∈ range n, G i) : t * C < ∑ i ∈ range n, G i * g i := by
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  rcases lt_or_ge C 0 with hC | hC
  · calc (t : ℝ) * C < 0 := mul_neg_of_pos_of_neg (by linarith) hC
      _ ≤ _ := sum_nonneg fun i hi ↦ mul_nonneg (hG i hi) (hg0 i hi)
  obtain ⟨i, hi, hGi⟩ : ∃ i ∈ range n, G i ≠ 0 := by
    by_contra h
    push Not at h
    rw [sum_eq_zero h] at hsum
    linarith
  calc (t : ℝ) * C ≤ (∑ i ∈ range n, G i) * C := mul_le_mul_of_nonneg_right hsum hC
    _ = ∑ i ∈ range n, G i * C := sum_mul _ _ _
    _ < ∑ i ∈ range n, G i * g i := by
      refine sum_lt_sum (fun j hj ↦ ?_) ⟨i, hi, ?_⟩
      · by_cases h0 : G j = 0
        · simp [h0]
        exact mul_le_mul_of_nonneg_left (hg j hj h0).le (hG j hj)
      · exact mul_lt_mul_of_pos_left (hg i hi hGi) (lt_of_le_of_ne (hG i hi) (Ne.symm hGi))

end Abel

section Cut

variable {σ K : Type*} [Field K] [Fintype σ] {𝔭 : Ideal (MvPolynomial σ K)} [𝔭.IsPrime]
  {m : ℕ} {b : σ → Fin m}

omit [Fintype σ] in
theorem card_filter_lt_add_one (S : Finset σ) (i : Fin m) :
    #(S.filter fun s ↦ (b s : ℕ) < i + 1) =
      #(S.filter fun s ↦ (b s : ℕ) < i) + #(S.filter (b · = i)) := by
  classical
  rw [← card_union_of_disjoint]
  · congr 1
    ext s
    simp only [mem_filter, mem_union, ← and_or_left, Fin.ext_iff, Nat.lt_add_one_iff_lt_or_eq]
  · rw [disjoint_filter]
    intro s _ h1 h2
    rw [Fin.ext_iff] at h2
    omega

/-- **The cut excesses** (Evertse 1995, Lemma 11). Let `T` be a transcendence basis of `K[X]/𝔭`
made of variables, adapted to the last blocks, meeting every block, with `t + |T| = |σ|`. There is
such a basis `T'` adapted to the first blocks and a function `G ≥ 0` with `G 0 = G m = 0` such
that `c_i - c'_i = G (i + 1) - G i`, `c_i`, `c'_i` the numbers of variables of block `i` outside
`T`, `T'`; and if every projection of `V(𝔭)` is onto, i.e. every block has full rank, then
`t ≤ ∑_{i < m} G (i + 1)`. -/
theorem exists_cutExcess [Finite σ] (hb : Function.Surjective b)
    (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b)) (hne : hilbertPoly b 𝔭 ≠ 0) {T : Finset σ}
    (hB : IsTranscendenceBasis K (fun t : (T : Set σ) ↦ Ideal.Quotient.mk 𝔭 (X (t : σ))))
    (hadapt : ∀ s ∉ T, IsAlgebraic (Algebra.adjoin K
      ((fun t ↦ Ideal.Quotient.mk 𝔭 (X t)) '' {t | t ∈ T ∧ b s ≤ b t}))
        (Ideal.Quotient.mk 𝔭 (X s))) {t : ℕ} (hcard : t + #T = Nat.card σ) :
    ∃ T' : Finset σ,
      IsTranscendenceBasis K (fun t : (T' : Set σ) ↦ Ideal.Quotient.mk 𝔭 (X (t : σ))) ∧
      (∀ i, ∃ s ∈ T', b s = i) ∧ t + #T' = Nat.card σ ∧
      ∃ G : ℕ → ℝ, G 0 = 0 ∧ G m = 0 ∧ (∀ k, 0 ≤ G k) ∧
        (∀ i : Fin m, ({s | s ∉ T ∧ b s = i}.ncard : ℝ) - {s | s ∉ T' ∧ b s = i}.ncard =
          G (i + 1) - G i) ∧
        ((∀ i, (#(univ.filter (b · = i)) : ℕ∞) ≤ (varMatroid 𝔭).eRk {s | b s = i}) →
          (t : ℝ) ≤ ∑ i ∈ range m, G (i + 1)) := by
  classical
  obtain ⟨T', hB', hTb', hTT', hrT, hP, hQ⟩ := exists_isTranscendenceBasis_cuts hb h𝔭 hne hB hadapt
  set N := varMatroid 𝔭
  set p' : ℕ → ℕ := fun k ↦ #(T'.filter fun s ↦ (b s : ℕ) < k)
  set p : ℕ → ℕ := fun k ↦ #(T.filter fun s ↦ (b s : ℕ) < k)
  have hsplit : ∀ (S : Finset σ) (k : ℕ),
      #(S.filter fun s ↦ k ≤ (b s : ℕ)) + #(S.filter fun s ↦ (b s : ℕ) < k) = #S := by
    intro S k
    rw [add_comm]
    have := Finset.card_filter_add_card_filter_not (s := S) (fun s ↦ (b s : ℕ) < k)
    simpa only [not_lt] using this
  have hall : ∀ (S : Finset σ), S.filter (fun s ↦ (b s : ℕ) < m) = S := fun S ↦
    Finset.filter_true_of_mem fun s _ ↦ (b s).2
  have hnone : ∀ (S : Finset σ), S.filter (fun s ↦ (b s : ℕ) < 0) = ∅ := fun S ↦
    Finset.filter_false_of_mem fun s _ ↦ Nat.not_lt_zero _
  -- `p k ≤ p' k`: the cut ranks are subadditive.
  have hsub : ∀ k : ℕ, p k ≤ p' k := by
    intro k
    have h := N.eRk_union_le_eRk_add_eRk {s | (b s : ℕ) < k} {s | k ≤ (b s : ℕ)}
    have hU' : {s | (b s : ℕ) < k} ∪ {s | k ≤ (b s : ℕ)} = Set.univ := by
      ext s
      simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      omega
    rw [hU', hrT, hP, hQ] at h
    have h' : #T ≤ p' k + #(T.filter fun s ↦ k ≤ (b s : ℕ)) := by exact_mod_cast h
    have := hsplit T k
    simp only [p, p'] at h' ⊢
    omega
  set G : ℕ → ℝ := fun k ↦ (p' k : ℝ) - p k
  have hcount : ∀ (S : Finset σ) (i : Fin m),
      ({s | s ∉ S ∧ b s = i}.ncard : ℝ) = #(univ.filter (b · = i)) -
        ((#(S.filter fun s ↦ (b s : ℕ) < i + 1) : ℝ) - #(S.filter fun s ↦ (b s : ℕ) < i)) := by
    intro S i
    have h1 := ncard_notMem_add_card_filter b S i
    have h2 := card_filter_lt_add_one (b := b) S i
    rw [h2, Nat.cast_add, ← h1, Nat.cast_add]
    ring
  refine ⟨T', hB', hTb', by rw [hTT']; exact hcard, G, ?_, ?_, fun k ↦ ?_, fun i ↦ ?_,
    fun hfull ↦ ?_⟩
  · simp [G, p, p']
  · simp only [G, p, p', hall, hTT', sub_self]
  · simp only [G, sub_nonneg, Nat.cast_le]
    exact hsub k
  · rw [hcount T i, hcount T' i]
    simp only [G, p, p']
    ring
  -- Every block has full rank: `|B_i| + p i ≤ p' (i + 1)` by submodularity.
  have hblock : ∀ i : Fin m, #(univ.filter (b · = i)) + p i ≤ p' (i + 1) := by
    intro i
    have h := N.eRk_inter_add_eRk_union_le {s | (b s : ℕ) < i + 1} {s | (i : ℕ) ≤ b s}
    have hI : {s | (b s : ℕ) < i + 1} ∩ {s | (i : ℕ) ≤ b s} = {s | b s = i} := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Fin.ext_iff]
      omega
    have hU' : {s | (b s : ℕ) < i + 1} ∪ {s | (i : ℕ) ≤ b s} = Set.univ := by
      ext s
      simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      omega
    rw [hI, hU', hrT, hP, hQ] at h
    have h' : #(univ.filter (b · = i)) + #T ≤
        p' (i + 1) + #(T.filter fun s ↦ (i : ℕ) ≤ (b s : ℕ)) := by
      have := (add_le_add (hfull i) le_rfl).trans h
      exact_mod_cast this
    have := hsplit T i
    simp only [p, p'] at h' ⊢
    omega
  have hsum : (Fintype.card σ : ℝ) + ∑ i ∈ range m, (p i : ℝ) ≤
      ∑ i ∈ range m, (p' (i + 1) : ℝ) := by
    have hfib : ∑ i : Fin m, #(univ.filter (b · = i)) = Fintype.card σ :=
      (Finset.card_eq_sum_card_fiberwise fun s _ ↦ mem_univ (b s)).symm
    rw [← Fin.sum_univ_eq_sum_range (fun i ↦ (p i : ℝ)),
      ← Fin.sum_univ_eq_sum_range (fun i ↦ (p' (i + 1) : ℝ)), ← hfib, Nat.cast_sum,
      ← sum_add_distrib]
    exact sum_le_sum fun i _ ↦ by exact_mod_cast hblock i
  have htel : ∑ i ∈ range m, ((p (i + 1) : ℝ) - p i) = #T := by
    rw [sum_range_sub (fun i ↦ (p i : ℝ))]
    simp [p]
  have hcardR : (t : ℝ) + #T = Fintype.card σ := by
    rw [← Nat.card_eq_fintype_card]
    exact_mod_cast hcard
  have : ∑ i ∈ range m, G (i + 1) = ∑ i ∈ range m, (p' (i + 1) : ℝ) -
      ∑ i ∈ range m, (p i : ℝ) - ∑ i ∈ range m, ((p (i + 1) : ℝ) - p i) := by
    simp only [G, sum_sub_distrib]
    ring
  rw [this, htel]
  linarith

/-- **Evertse's sharper product theorem** (Evertse 1995, §5, Lemma 11 and p. 246, for any
blocks). Under the hypotheses of `MvPolynomial.productTheorem_height`, with `t ≥ 1` and the ratio
condition `δ_i / δ_{i+1} > m / ε` in place of `(m / ε)^t`: for the type `β` of a transcendence
basis adapted to the first blocks, `d_β(𝔭) ≥ 1` and `β_i + 1 ≤ r(B_i)` (`β_i ≤ dim Z_i`); some
block `k` has `r(B_k) < n_k + 1`, i.e. the projection `Z_k` of `V(𝔭)` to `ℙ^{n_k}` is not onto;
and for every `k`,
`ε^t δ_k h_{β + ε_k}(𝔭) ≤ ∑_l h(ℙ^{n_l}) δ_l #F_l + (∑_{j < t} max(B(|δ|^j), 0)) #G_k`
with `F_l`, `G_k` as in `MvPolynomial.productTheorem_height`. -/
theorem exists_eRk_lt_and_mul_height_le [CharZero K] [Height.AdmissibleAbsValues K]
    (hb : Function.Surjective b) (H : MultiprojectiveHeight b)
    {δ : Fin m → ℕ}
    {R : Finset (MvPolynomial σ K)} (hR : ∀ r ∈ R, IsWeightedHomogeneous (multiWeight b) r δ)
    (h𝔭R : 𝔭 ∈ (Ideal.span (R : Set (MvPolynomial σ K))).minimalPrimes)
    (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b)) (hne : hilbertPoly b 𝔭 ≠ 0) {t : ℕ}
    (ht : 𝔭.height = t) (ht1 : 1 ≤ t) (hδ : ∀ i, 0 < δ i) {ε : ℝ} (hε : 0 < ε)
    {R' : Set (MvPolynomial σ K)} (hRR' : Ideal.span (R : Set (MvPolynomial σ K)) ≤ Ideal.span R')
    (hI : ∀ P ∈ R', ∀ κ : σ →₀ ℕ, Finsupp.weight (fun s ↦ ((δ (b s) : ℝ))⁻¹) κ ≤ ε →
      hasseDeriv κ P ∈ 𝔭)
    (hanti : Antitone δ) (hratio : ∀ i j : Fin m, (i : ℕ) + 1 = j → (m : ℝ) < ε * (δ i / δ j))
    {B : ℕ → ℝ} (hBmono : Monotone B)
    (hRB : ∀ a : MvPolynomial σ K → ℕ, ∑ r ∈ R, a r • r ≠ 0 →
      bombieriLogHeight b (∑ r ∈ R, a r • r) ≤ B (∑ r ∈ R, a r)) :
    ∃ β : Fin m →₀ ℕ, (hilbertPoly b 𝔭).totalDegree = β.degree ∧ 1 ≤ multidegree b 𝔭 β ∧
      (∀ i, (β i : ℕ∞) + 1 ≤ (varMatroid 𝔭).eRk {s | b s = i}) ∧
      (∃ k, (varMatroid 𝔭).eRk {s | b s = k} < #(univ.filter (b · = k))) ∧
      ∀ k, ε ^ t * δ k * H.height 𝔭 (β + Finsupp.single k 1) ≤
        ∑ l, Height.totalWeight K * H.botBound (bottomType b l) * δ l *
            #(univ.filter fun f : Fin t → Fin m ↦ β + Finsupp.single k 1 +
              ∑ j, Finsupp.single (f j) 1 = bottomType b + Finsupp.single l 1) +
          (∑ j ∈ range t, max (B ((∑ i, δ i) ^ j)) 0) *
            #(univ.filter fun g : Fin (t - 1) → Fin m ↦ β + Finsupp.single k 1 +
              ∑ j, Finsupp.single (g j) 1 = bottomType b) := by
  classical
  obtain ⟨T, hB, hadapt, hTb, hcard, hineq, P, hPa, hh⟩ :=
    prod_pow_mul_pow_mul_height_le hb H hR h𝔭R h𝔭 hne ht hδ hε hRR' hI
  obtain ⟨T', hB', hTb', hcard', G, hG0, hGm, hGnn, hcc, hfull⟩ :=
    exists_cutExcess hb h𝔭 hne hB hadapt hcard
  set β := coneType b T'
  obtain ⟨hdeg, hpos⟩ := totalDegree_hilbertPoly_eq_and_one_le_multidegree hb h𝔭 hB' hTb'
  have hβdeg : β.degree = _ := (degree_coneType_eq_sub hb hTb' hcard').1
  have hδR : ∀ i, (0 : ℝ) < δ i := fun i ↦ Nat.cast_pos.mpr (hδ i)
  have hPpos : ∀ c : Fin m → ℕ, 0 < ∏ i, (δ i : ℝ) ^ c i :=
    fun c ↦ Finset.prod_pos fun i _ ↦ pow_pos (hδR i) _
  have hlogP : ∀ c : Fin m → ℕ,
      Real.log (∏ i, (δ i : ℝ) ^ c i) = ∑ i, (c i : ℝ) * Real.log (δ i) := by
    intro c
    rw [Real.log_prod fun i _ ↦ (pow_pos (hδR i) _).ne']
    simp only [Real.log_pow]
  set Pc := ∏ i, (δ i : ℝ) ^ {s | s ∉ T ∧ b s = i}.ncard
  set Pc' := ∏ i, (δ i : ℝ) ^ {s | s ∉ T' ∧ b s = i}.ncard
  -- Abel summation: `∑_i (c_i - c'_i) log δ_i = ∑_{i < m} G (i + 1) (L i - L (i + 1))`.
  set L : ℕ → ℝ := fun j ↦ if h : j < m then Real.log (δ ⟨j, h⟩) else 0
  have habel : Real.log Pc - Real.log Pc' = ∑ i ∈ range m, G (i + 1) * (L i - L (i + 1)) := by
    have h := sum_range_sub_mul_eq G L hG0 m
    rw [hGm, zero_mul, zero_add] at h
    rw [hlogP, hlogP, ← sum_sub_distrib, ← h,
      ← Fin.sum_univ_eq_sum_range (fun i ↦ (G (i + 1) - G i) * L i)]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [← sub_mul, hcc i]
    simp [L, i.2]
  have hgap0 : ∀ i ∈ range m, 0 ≤ L i - L (i + 1) := by
    intro i hi
    rw [mem_range] at hi
    by_cases hi' : i + 1 < m
    · simp only [L, hi, hi', ↓reduceDIte, sub_nonneg]
      exact Real.log_le_log (hδR _) (by exact_mod_cast hanti (Fin.mk_le_mk.mpr (Nat.le_succ i)))
    · simp only [L, hi, hi', ↓reduceDIte, sub_zero]
      exact Real.log_natCast_nonneg _
  have hPcPc' : Pc' ≤ Pc := by
    rw [← Real.log_le_log_iff (hPpos _) (hPpos _), ← sub_nonneg, habel]
    exact sum_nonneg fun i hi ↦ mul_nonneg (hGnn _) (hgap0 i hi)
  refine ⟨β, hdeg, hpos, fun i ↦ ?_, ?_, fun k ↦ ?_⟩
  · -- `β_i + 1 = |T' ∩ B_i| ≤ r(B_i)`.
    have hind : (varMatroid 𝔭).Indep (T'.filter (b · = i) : Set σ) :=
      varMatroid_indep_iff.mpr (AlgebraicIndepOn.mono hB'.1 fun s hs ↦ (mem_filter.mp hs).1)
    have hle := hind.encard_le_eRk_of_subset (X := {s | b s = i})
      fun s hs ↦ (mem_filter.mp hs).2
    rw [Set.encard_coe_eq_coe_finsetCard] at hle
    obtain ⟨s, hs, hsi⟩ := hTb' i
    have hc : 0 < #(T'.filter (b · = i)) := card_pos.mpr ⟨s, mem_filter.mpr ⟨hs, hsi⟩⟩
    have hβi' : β i = #(T'.filter (b · = i)) - 1 := by simp [β, coneType]
    have hβi : β i + 1 = #(T'.filter (b · = i)) := by omega
    rw [← Nat.cast_one, ← Nat.cast_add, hβi]
    exact hle
  · -- Some projection is not onto.
    by_contra hcon
    push Not at hcon
    have htG := hfull hcon
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp only [range_zero, sum_empty] at htG
      have : (1 : ℝ) ≤ t := by exact_mod_cast ht1
      linarith
    have h' := hineq β hβdeg.ge
    rw [sum_prod_eq_card_mul_prod_pow b hTb' δ] at h'
    have hF : (#(univ.filter fun f : Fin t → Fin m ↦
        β + ∑ j, Finsupp.single (f j) 1 = bottomType b) : ℝ) ≤ (m : ℝ) ^ t := by
      have : #(univ.filter fun f : Fin t → Fin m ↦
          β + ∑ j, Finsupp.single (f j) 1 = bottomType b) ≤ m ^ t :=
        (Finset.card_filter_le _ _).trans (by simp)
      exact_mod_cast this
    have hd : (1 : ℝ) ≤ multidegree b 𝔭 β := by exact_mod_cast hpos
    have h2 : Pc * ε ^ t ≤ (m : ℝ) ^ t * Pc' :=
      calc Pc * ε ^ t ≤ Pc * ε ^ t * multidegree b 𝔭 β :=
            le_mul_of_one_le_right (mul_pos (hPpos _) (pow_pos hε t)).le hd
        _ ≤ _ := h'
        _ ≤ _ := mul_le_mul_of_nonneg_right hF (hPpos _).le
    have hlog := Real.log_le_log (mul_pos (hPpos _) (pow_pos hε t)) h2
    rw [Real.log_mul (hPpos _).ne' (pow_pos hε t).ne',
      Real.log_mul (pow_pos (Nat.cast_pos.mpr hm) t).ne' (hPpos _).ne', Real.log_pow,
      Real.log_pow] at hlog
    have hlt := mul_lt_sum_mul (n := m) (G := fun i ↦ G (i + 1)) (g := fun i ↦ L i - L (i + 1))
      (C := Real.log m - Real.log ε) (fun i _ ↦ hGnn _) (fun i hi hGi ↦ ?_) hgap0 ht1 htG
    · have := habel
      linarith
    rw [mem_range] at hi
    have hi' : i + 1 < m := by
      by_contra h
      exact hGi (by rw [show i + 1 = m by omega, hGm])
    have hr := hratio ⟨i, hi⟩ ⟨i + 1, hi'⟩ rfl
    simp only [L, hi, hi', ↓reduceDIte]
    rw [← Real.log_div (hδR _).ne' (hδR _).ne', ← Real.log_div (Nat.cast_pos.mpr hm).ne' hε.ne']
    refine Real.log_lt_log (div_pos (Nat.cast_pos.mpr hm) hε) ?_
    rwa [div_lt_iff₀ hε, mul_comm]
  · -- The height bound in the type `β + ε_k`.
    have hS : ∑ j, max (bombieriLogHeight b (P j)) 0 ≤
        ∑ j ∈ range t, max (B ((∑ i, δ i) ^ j)) 0 := by
      rw [← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_le_sum fun j _ ↦ ?_
      obtain ⟨a, ha, hPj⟩ := hPa j
      rw [hPj]
      by_cases h0 : ∑ r ∈ R, a r • r = 0
      · rw [h0, bombieriLogHeight_zero, max_self]
        exact le_max_right _ _
      exact max_le_max ((hRB a h0).trans (hBmono ha)) le_rfl
    have hmain := hh (β + Finsupp.single k 1) (by
      simp only [map_add, Finsupp.degree_single, hβdeg])
    have hmul := (mul_le_mul_of_nonneg_left hmain (Nat.cast_nonneg (δ k))).trans
      (mul_bezoutSum_add_le hb H hδ hTb' hcard' k _)
    have hh0 : 0 ≤ H.height 𝔭 (β + Finsupp.single k 1) :=
      H.height_nonneg 𝔭 inferInstance h𝔭 hne _
    set X := ∑ l, Height.totalWeight K * H.botBound (bottomType b l) * δ l *
      #(univ.filter fun f : Fin t → Fin m ↦ β + Finsupp.single k 1 +
        ∑ j, Finsupp.single (f j) 1 = bottomType b + Finsupp.single l 1)
    set Gk := (#(univ.filter fun g : Fin (t - 1) → Fin m ↦ β + Finsupp.single k 1 +
      ∑ j, Finsupp.single (g j) 1 = bottomType b) : ℝ)
    have hY : X + (∑ j, max (bombieriLogHeight b (P j)) 0) * Gk ≤
        X + (∑ j ∈ range t, max (B ((∑ i, δ i) ^ j)) 0) * Gk :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hS (Nat.cast_nonneg _))
    have hlhs : 0 ≤ (δ k : ℝ) * (Pc * ε ^ t * H.height 𝔭 (β + Finsupp.single k 1)) := by
      have := hPpos (fun i ↦ {s | s ∉ T ∧ b s = i}.ncard)
      positivity
    have hYnn : 0 ≤ X + (∑ j ∈ range t, max (B ((∑ i, δ i) ^ j)) 0) * Gk := by
      have h1 := hlhs.trans hmul
      have h2 := nonneg_of_mul_nonneg_right h1 (hPpos _)
      exact h2.trans hY
    refine le_of_mul_le_mul_left ?_ (hPpos (fun i ↦ {s | s ∉ T ∧ b s = i}.ncard))
    calc Pc * (ε ^ t * δ k * H.height 𝔭 (β + Finsupp.single k 1))
        = δ k * (Pc * ε ^ t * H.height 𝔭 (β + Finsupp.single k 1)) := by ring
      _ ≤ Pc' * (X + (∑ j, max (bombieriLogHeight b (P j)) 0) * Gk) := hmul
      _ ≤ Pc' * (X + (∑ j ∈ range t, max (B ((∑ i, δ i) ^ j)) 0) * Gk) :=
        mul_le_mul_of_nonneg_left hY (hPpos _).le
      _ ≤ Pc * (X + (∑ j ∈ range t, max (B ((∑ i, δ i) ^ j)) 0) * Gk) :=
        mul_le_mul_of_nonneg_right hPcPc' hYnn

end Cut

section Index

variable {σ K : Type*} [Field K] [Fintype σ] {m : ℕ} {b : σ → Fin m}

/-- **Evertse's sharper product theorem for the zeros of index `a`** (Evertse 1995, §5). Let `𝔭`,
of height `t ≥ 1`, be a component of both `Z_a(F)` and `Z_{a+ε}(F)`, `F` of multidegree `δ`, `δ`
decreasing with `δ_i / δ_{i+1} > m / ε`. Then for the type `β` of a transcendence basis adapted
to the first blocks, `d_β(𝔭) ≥ 1`, some projection `Z_k` of `V(𝔭)` is not onto, and for every `k`
`ε^t δ_k h_{β + ε_k}(𝔭) ≤ ∑_l h(ℙ^{n_l}) δ_l #F_l + S · #G_k` with Rémond's
`S = ∑_{j < t} max(h(F) + [K : ℚ] (|δ| log 2 + j log |δ| + |√n|), 0)`, as in
`MvPolynomial.productTheorem_indexIdeal_height`. -/
theorem exists_eRk_lt_and_mul_height_le_indexIdeal [CharZero K] [Height.AdmissibleAbsValues K]
    (hb : Function.Surjective b) (H : MultiprojectiveHeight b) {δ : Fin m → ℕ} (hδ : ∀ i, 0 < δ i)
    {F : MvPolynomial σ K} (hF : IsWeightedHomogeneous (multiWeight b) F δ) {a ε : ℝ}
    (hε : 0 < ε) {𝔭 : Ideal (MvPolynomial σ K)} [𝔭.IsPrime]
    (h𝔭a : 𝔭 ∈ (indexIdeal b δ F a).minimalPrimes) (h𝔭ε : indexIdeal b δ F (a + ε) ≤ 𝔭)
    (hne : hilbertPoly b 𝔭 ≠ 0) {t : ℕ} (ht : 𝔭.height = t) (ht1 : 1 ≤ t) (hanti : Antitone δ)
    (hratio : ∀ i j : Fin m, (i : ℕ) + 1 = j → (m : ℝ) < ε * (δ i / δ j)) :
    ∃ β : Fin m →₀ ℕ, (hilbertPoly b 𝔭).totalDegree = β.degree ∧ 1 ≤ multidegree b 𝔭 β ∧
      (∀ i, (β i : ℕ∞) + 1 ≤ (varMatroid 𝔭).eRk {s | b s = i}) ∧
      (∃ k, (varMatroid 𝔭).eRk {s | b s = k} < #(univ.filter (b · = k))) ∧
      ∀ k, ε ^ t * δ k * H.height 𝔭 (β + Finsupp.single k 1) ≤
        ∑ l, Height.totalWeight K * H.botBound (bottomType b l) * δ l *
            #(univ.filter fun f : Fin t → Fin m ↦ β + Finsupp.single k 1 +
              ∑ j, Finsupp.single (f j) 1 = bottomType b + Finsupp.single l 1) +
          (∑ j ∈ range t, max (Height.logHeight (fun ν : F.support ↦ F.coeff ν) +
            Height.totalWeight K * ((∑ i, δ i : ℕ) * Real.log 2 +
              j * Real.log (∑ i, δ i : ℕ) +
              ∑ i, √((#({s | b s = i} : Finset σ) : ℝ) - 1))) 0) *
            #(univ.filter fun g : Fin (t - 1) → Fin m ↦ β + Finsupp.single k 1 +
              ∑ j, Finsupp.single (g j) 1 = bottomType b) := by
  classical
  obtain ⟨R, R', hR, h𝔭R, hRR', hI, hM, hh⟩ := exists_finset_indexIdeal hb hF h𝔭a h𝔭ε hne
  have h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b) :=
    (isWeightedHomogeneous_indexIdeal hF a).of_mem_minimalPrimes h𝔭a
  have hmono : Monotone fun n : ℕ ↦ Height.logHeight (coeffTuple R (blockMonomials b δ)) +
      Height.totalWeight K * (Real.log n +
        Real.log √(∑ μ ∈ blockMonomials b δ, 1 / (blockMultinomial b μ : ℝ))) := by
    intro n n' hn
    have hlog : Real.log n ≤ Real.log n' := by
      rcases n.eq_zero_or_pos with rfl | hn0
      · simpa using Real.log_natCast_nonneg n'
      · exact Real.log_le_log (Nat.cast_pos.mpr hn0) (Nat.cast_le.mpr hn)
    dsimp only
    gcongr
  obtain ⟨β, hdeg, hpos, hrk, hk, hheight⟩ := exists_eRk_lt_and_mul_height_le hb H hR h𝔭R h𝔭
    hne ht ht1 hδ hε hRR' hI hanti hratio hmono fun a ha ↦ by
      rw [Nat.cast_sum]
      exact bombieriLogHeight_sum_nsmul_le b hM a ha
  refine ⟨β, hdeg, hpos, hrk, hk, fun k ↦ (hheight k).trans ?_⟩
  -- Rémond's Lemma 5.2: `log c(δ)^{1/2} ≤ |√n|`.
  have h52 := mul_le_mul_of_nonneg_left (log_sqrt_sum_inv_blockMultinomial_le b δ)
    (Nat.cast_nonneg (Height.totalWeight K))
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_right
    (sum_le_sum fun j _ ↦ max_le_max ?_ le_rfl) (Nat.cast_nonneg _))
  rw [Nat.cast_pow, Real.log_pow]
  linear_combination hh + h52


omit [Fintype σ] in
/-- **The index at a point.** `F` vanishes to index `a` at `P`, i.e. `P ∈ Z_a(F)`, iff every Hasse
derivative `∂_κ F` with `∑_s κ_s / δ_{b s} ≤ a` vanishes at `P`. -/
theorem indexIdeal_le_pointIdeal_iff [Finite σ] {δ : Fin m → ℕ} {F : MvPolynomial σ K}
    (hF : IsWeightedHomogeneous (multiWeight b) F δ) {a : ℝ} {P : σ → K} :
    indexIdeal b δ F a ≤ pointIdeal b P ↔
      ∀ κ : σ →₀ ℕ, Finsupp.weight (fun s ↦ ((δ (b s) : ℝ))⁻¹) κ ≤ a →
        eval P (hasseDeriv κ F) = 0 := by
  classical
  have hhom : ∀ κ : σ →₀ ℕ, IsWeightedHomogeneous (multiWeight b) (hasseDeriv κ F)
      ⇑(Finsupp.equivFunOnFinite.symm (δ - Finsupp.weight (multiWeight b) κ)) := fun κ ↦ by
    rw [Finsupp.coe_equivFunOnFinite_symm]
    exact isWeightedHomogeneous_hasseDeriv hF κ
  constructor
  · intro h κ hκ
    exact (mem_pointIdeal_iff (hhom κ)).mp (h (hasseDeriv_mem_indexIdeal hκ))
  · intro h
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨κ, hκ, rfl⟩
    exact (mem_pointIdeal_iff (hhom κ)).mpr (h κ hκ)

/-- **Evertse's Roth lemma** (Evertse 1995, Thm. 3, with Rémond's heights and a better ratio
condition). Let the `2m` variables be in `m` blocks of two, i.e. work on `(ℙ¹)^m`, let `F ≠ 0` be
multihomogeneous of multidegree `δ`, `δ` decreasing with `δ_i / δ_{i+1} > m² / ε`, and let `P` be
a point of `(ℙ¹(K))^m` at which `F` vanishes to index `ε`: every `∂_κ F` with
`∑_s κ_s / δ_{b s} ≤ ε` vanishes at `P`. Then for some `k`,
`δ_k h(P_k) ≤ max(1, m²/ε)^m ([K : ℚ] max(h(ℙ¹), 0) |δ| + m (h(F) + [K : ℚ] (|δ| log 2 +
m log |δ| + m)))`,
where `h(P_k)` is the height of the `k`-th coordinate of `P`, `h(F)` that of the coefficients of
`F`, and `h(ℙ¹)` is `H.botBound 1`, all relative to `K`. Evertse's condition is
`δ_i / δ_{i+1} ≥ 2m³/ε`.

The proof is Evertse's §5: descend along `Z_0 ⊇ Z_{ε/m} ⊇ ⋯ ⊇ Z_ε` to a component `V(𝔭) ∋ P` of
`Z_{jε/m}` and `Z_{(j+1)ε/m}`; by `MvPolynomial.exists_eRk_lt_and_mul_height_le_indexIdeal` its
projection to some factor `ℙ¹` is a point, which is `P_k`
(`MvPolynomial.sub_mem_of_eRk_le_one`); and the point bound (L) of the height theory gives
`h(P_k) ≤ d_β(𝔭) h(P_k) ≤ h_{β + ε_k}(𝔭)`. -/
theorem exists_mul_logHeight_le [CharZero K] [Height.AdmissibleAbsValues K]
    (hb : Function.Surjective b) (H : MultiprojectiveHeight (K := K) b)
    (h2 : ∀ i, #(univ.filter (b · = i)) = 2) {δ : Fin m → ℕ} (hδ : ∀ i, 0 < δ i)
    (hanti : Antitone δ) {F : MvPolynomial σ K} (hF : IsWeightedHomogeneous (multiWeight b) F δ)
    (hF0 : F ≠ 0) {ε : ℝ} (hε : 0 < ε)
    (hratio : ∀ i j : Fin m, (i : ℕ) + 1 = j → (m : ℝ) ^ 2 < ε * (δ i / δ j))
    {P : σ → K} (hP : ∀ i, ∃ s, b s = i ∧ P s ≠ 0) (hFP : indexIdeal b δ F ε ≤ pointIdeal b P) :
    ∃ k, (δ k : ℝ) * Height.logHeight (fun s : {s // b s = k} ↦ P s) ≤
      max 1 ((m : ℝ) ^ 2 / ε) ^ m * (Height.totalWeight K * max (H.botBound 1) 0 *
        (∑ i, δ i : ℕ) + m * (Height.logHeight (fun ν : F.support ↦ F.coeff ν) +
          Height.totalWeight K * ((∑ i, δ i : ℕ) * Real.log 2 +
            m * Real.log (∑ i, δ i : ℕ) + m))) := by
  classical
  have hσ : Nat.card σ = 2 * m := by
    rw [Nat.card_eq_fintype_card, ← card_univ,
      card_eq_sum_card_fiberwise (f := b) (t := univ) fun _ _ ↦ mem_univ _]
    simp [h2, mul_comm]
  have h𝔮 := isWeightedHomogeneous_pointIdeal (b := b) (P := P)
  have hne𝔮 := hilbertPoly_pointIdeal_ne_zero hb hP
  obtain ⟨t𝔮, ht𝔮, ht𝔮m⟩ := exists_height_eq_add_le hb (pointIdeal b P) h𝔮 hne𝔮
  have hF𝔮 : F ∈ pointIdeal b P := hFP (mem_indexIdeal hε.le)
  have hm : 0 < m := by
    have h1 := one_le_height_of_mem hF0 hF𝔮
    rw [ht𝔮] at h1
    have : 1 ≤ t𝔮 := by exact_mod_cast h1
    omega
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  -- The descent along `Z_0 ⊇ Z_{ε'} ⊇ ⋯ ⊇ Z_{m ε'} = Z_ε`.
  set ε' := ε / m with hε'def
  have hε' : 0 < ε' := div_pos hε hmR
  have hmε : (m : ℝ) * ε' = ε := by rw [hε'def]; field_simp
  obtain ⟨𝔭, h𝔭p, h𝔭𝔮, hne𝔭, j, h𝔭min, h𝔭next⟩ :=
    exists_minimalPrimes_indexIdeal_le hb hF hF0 hε'.le m (pointIdeal b P) h𝔮 hne𝔮
      (by rw [hmε]; exact hFP) (by rw [ht𝔮]; exact_mod_cast (by omega : t𝔮 ≤ m))
  have h𝔭h := (isWeightedHomogeneous_indexIdeal hF _).of_mem_minimalPrimes h𝔭min
  obtain ⟨t, ht, htm⟩ := exists_height_eq_add_le hb 𝔭 h𝔭h hne𝔭
  have ht1 : 1 ≤ t := by
    have h1 := one_le_height_of_mem hF0 (h𝔭min.1.2 (mem_indexIdeal (by positivity)))
    rw [ht] at h1
    exact_mod_cast h1
  have htm' : t ≤ m := by omega
  have hratio' : ∀ i j : Fin m, (i : ℕ) + 1 = j → (m : ℝ) < ε' * (δ i / δ j) := by
    intro i j hij
    have h := hratio i j hij
    rw [hε'def, div_mul_eq_mul_div, lt_div_iff₀ hmR]
    nlinarith
  obtain ⟨β, hdeg, hpos, -, ⟨k, hk⟩, hheight⟩ := exists_eRk_lt_and_mul_height_le_indexIdeal hb H
    hδ hF hε' h𝔭min h𝔭next hne𝔭 ht ht1 hanti hratio'
  refine ⟨k, ?_⟩
  -- The projection to the factor `k` is the point `P_k`.
  have hrk : (varMatroid 𝔭).eRk {s | b s = k} ≤ 1 := by
    rw [h2 k] at hk
    by_contra hcon
    exact absurd (Order.add_one_le_of_lt (not_le.mp hcon)) (not_le.mpr hk)
  obtain ⟨s₀, hs₀, hP₀⟩ := hP k
  have hL := H.logHeight_mul_le_cycleHeight 𝔭 k P s₀ h𝔭h hs₀ hP₀
    (fun s t hs ht ↦ sub_mem_of_eRk_le_one h𝔭𝔮 hs₀ hP₀ hrk hs ht) β hdeg.le
  rw [cycleHeight_eq_of_forall_le H.height le_rfl (fun q _ h ↦ h) hne𝔭
    (by rw [hdeg, map_add, Finsupp.degree_single]), primeMult_eq, Ideal.localLength_self] at hL
  simp only [ENat.toNat_one, Nat.cast_one, one_mul] at hL
  have hlogH : Height.logHeight (fun s : {s // b s = k} ↦ P s) ≤
      H.height 𝔭 (β + Finsupp.single k 1) := by
    refine le_trans ?_ hL
    exact le_mul_of_one_le_left (Height.logHeight_nonneg _) (by exact_mod_cast hpos)
  have hmain := (mul_le_mul_of_nonneg_left hlogH (by positivity : (0 : ℝ) ≤ ε' ^ t * δ k)).trans
    (hheight k)
  -- Estimating the right-hand side.
  set W : ℝ := (Height.totalWeight K : ℝ)
  set D : ℝ := ((∑ i, δ i : ℕ) : ℝ)
  set hFh := Height.logHeight (fun ν : F.support ↦ F.coeff ν)
  have hW : 0 ≤ W := Nat.cast_nonneg _
  have hLD : 0 ≤ Real.log D := Real.log_natCast_nonneg _
  have hhF : 0 ≤ hFh := Height.logHeight_nonneg _
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  have hmt : (1 : ℝ) ≤ (m : ℝ) ^ t := one_le_pow₀ (by exact_mod_cast hm)
  have hbot : ∀ l, bottomType b l = 1 := by
    intro l
    rw [bottomType_eq_coneType]
    simp [coneType, h2]
  have hsqrt : ∑ i, √((#({s | b s = i} : Finset σ) : ℝ) - 1) = m := by
    simp [h2]
    norm_num
  have hcardF : ∀ {u : ℕ} (p : (Fin u → Fin m) → Prop) [DecidablePred p],
      (#(univ.filter p) : ℝ) ≤ (m : ℝ) ^ u := by
    intro u p _
    exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
  set B₁ := max (H.botBound 1) 0
  have hX : ∑ l, W * H.botBound (bottomType b l) * δ l *
      #(univ.filter fun f : Fin t → Fin m ↦ β + Finsupp.single k 1 +
        ∑ j, Finsupp.single (f j) 1 = bottomType b + Finsupp.single l 1) ≤
      (m : ℝ) ^ t * (W * B₁ * D) := by
    rw [show D = ∑ l, (δ l : ℝ) by simp [D], Finset.mul_sum, Finset.mul_sum]
    refine sum_le_sum fun l _ ↦ ?_
    rw [hbot l]
    calc W * H.botBound 1 * δ l * #(univ.filter fun f : Fin t → Fin m ↦ β + Finsupp.single k 1 +
          ∑ j, Finsupp.single (f j) 1 = bottomType b + Finsupp.single l 1)
        ≤ W * B₁ * δ l * #(univ.filter fun f : Fin t → Fin m ↦ β + Finsupp.single k 1 +
          ∑ j, Finsupp.single (f j) 1 = bottomType b + Finsupp.single l 1) := by
          gcongr
          exact le_max_left _ _
      _ ≤ W * B₁ * δ l * (m : ℝ) ^ t := by
          gcongr
          exact hcardF _
      _ = _ := by ring
  set Z : ℝ := hFh + W * (D * Real.log 2 + t * Real.log D + m)
  have hZ : 0 ≤ Z := by positivity
  have hS : ∑ j ∈ range t, max (hFh + W * (D * Real.log 2 + j * Real.log D +
      ∑ i, √((#({s | b s = i} : Finset σ) : ℝ) - 1))) 0 ≤ t * Z := by
    rw [hsqrt]
    have := Finset.sum_le_card_nsmul (range t) (fun j ↦ max (hFh + W * (D * Real.log 2 +
      j * Real.log D + m)) 0) Z fun j hj ↦ by
        rw [mem_range] at hj
        refine max_le ?_ hZ
        have : (j : ℝ) ≤ t := by exact_mod_cast hj.le
        simp only [Z]
        gcongr
    simpa using this
  have hS0 : 0 ≤ ∑ j ∈ range t, max (hFh + W * (D * Real.log 2 + j * Real.log D +
      ∑ i, √((#({s | b s = i} : Finset σ) : ℝ) - 1))) 0 :=
    sum_nonneg fun _ _ ↦ le_max_right _ _
  have hG : (#(univ.filter fun g : Fin (t - 1) → Fin m ↦ β + Finsupp.single k 1 +
      ∑ j, Finsupp.single (g j) 1 = bottomType b) : ℝ) ≤ (m : ℝ) ^ t :=
    (hcardF _).trans (pow_le_pow_right₀ (by exact_mod_cast hm) (Nat.sub_le t 1))
  have hRHS := hmain.trans (add_le_add hX (mul_le_mul hS hG (Nat.cast_nonneg _)
    (by positivity)))
  -- `t Z_t ≤ m Z_m`.
  set Q : ℝ := W * B₁ * D + m * (hFh + W * (D * Real.log 2 + m * Real.log D + m))
  have hQ : (m : ℝ) ^ t * (W * B₁ * D) + t * Z * (m : ℝ) ^ t ≤ (m : ℝ) ^ t * Q := by
    have htmR : (t : ℝ) ≤ m := by exact_mod_cast htm'
    have hZm : Z ≤ hFh + W * (D * Real.log 2 + m * Real.log D + m) := by
      simp only [Z]
      gcongr
    have : (t : ℝ) * Z ≤ m * (hFh + W * (D * Real.log 2 + m * Real.log D + m)) :=
      mul_le_mul htmR hZm hZ (Nat.cast_nonneg _)
    have hB₁ : 0 ≤ B₁ := le_max_right _ _
    simp only [Q]
    nlinarith
  have hfinal := hRHS.trans hQ
  -- Divide by `ε'^t` and compare `(m / ε')^t = (m²/ε)^t ≤ max(1, m²/ε)^m`.
  have hQ0 : 0 ≤ Q := by
    have : 0 ≤ B₁ := le_max_right _ _
    positivity
  have hε't : 0 < ε' ^ t := pow_pos hε' t
  have h1 : (δ k : ℝ) * Height.logHeight (fun s : {s // b s = k} ↦ P s) ≤
      ((m : ℝ) ^ 2 / ε) ^ t * Q := by
    have hmε' : (m : ℝ) ^ 2 / ε = m / ε' := by
      rw [hε'def]
      field_simp
    rw [hmε', div_pow, div_mul_eq_mul_div, le_div_iff₀ hε't]
    linarith
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ hQ0)
  calc ((m : ℝ) ^ 2 / ε) ^ t ≤ max 1 ((m : ℝ) ^ 2 / ε) ^ t :=
        pow_le_pow_left₀ (by positivity) (le_max_right _ _) t
    _ ≤ max 1 ((m : ℝ) ^ 2 / ε) ^ m := pow_le_pow_right₀ (le_max_left _ _) htm'

end Index

end MvPolynomial
