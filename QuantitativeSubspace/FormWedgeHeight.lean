/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.FormExteriorPower
public import QuantitativeSubspace.FormHyperplaneHeight

-- Used only inside proofs.
import ArithmeticHeights.CauchyBinet
import ArithmeticHeights.Duality
import ArithmeticHeights.RowEntryHeight
import Mathlib.Data.Nat.Choose.Central

/-!
# Exterior powers of a twisted height

J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative Subspace Theorem*,
Ann. of Math. **177** (2013), 513–590, Lemmas 6.1, 17.1 and the estimates behind Lemmas 17.2,
17.3 and (17.10).

The proof of Prop. 17.5 runs Theorem 16.1 on the `p`-th exterior power `(L̂, ĉ)` of `(L, c)`.
Theorem 16.1 is stated on `Ω^N` with `N` a natural number, while `L̂` (`FormSystem.exteriorPower`)
is indexed by the `p`-element subsets; `FormSystem.reindex` moves a system along an equivalence of
index types, carrying heights, forms and exponent sums along.

* Lemma 17.1: `H_{L̂,ĉ,Q}(x_1 ∧ ⋯ ∧ x_p) ≤ p! ∏_r H_{L,c,Q}(x_r)` (EF13 have `p^{p/2}` from
  Hadamard's inequality; the factor plays no role).
* (17.10): the forms of `L̂` have Arakelov height at most `H₂^p`.
* Lemma 6.1: for `g_1, …, g_n` independent with `g_1, …, g_k` spanning `T = V ⊗ Ω`, the span `T̂`
  of the wedges `ĝ_I`, `I ≠ {k+1, …, n}`, is the extension of a subspace of `K^N` of the same
  height as `V`: `T̂` is cut out by `φ_1 ∧ ⋯ ∧ φ_p` for a basis `φ` of `V^⊥` (Cauchy–Binet), and
  duality does the rest.
* The successive infima: `λ_1 ⋯ λ_m ≤ ∏ h(x_b)` for `m` independent points (the products of
  Lemma 17.2), and points `g_j` with `h(g_j) ≤ C λ_j`.
* `Nat.mul_choose_sq_le`: `p C(n, p)² ≤ 4ⁿ`, EF13's last step in the proof of Prop. 17.5.

## Main definitions

* `NumberField.FormSystem.reindex`, `NumberField.FormWeight.reindex`,
  `NumberField.FormExponent.reindex`: systems moved along `ι ≃ κ`.

## Main results

* `NumberField.FormSystem.absMulHeight_exteriorPower_plucker_le`: EF13 Lemma 17.1.
* `NumberField.FormSystem.arakelovFormHeight_exteriorPower_le`: EF13 (17.10).
* `NumberField.exists_extendPi_span_compound_eq`: EF13 Lemma 6.1.
* `NumberField.prod_heightInf_le_prod`, `NumberField.exists_linearIndependent_le_mul`.
* `NumberField.FormExponent.sum_exteriorPower`: `α̂ = C(n-1, p-1) α`.

This is part of milestone Q3.6 of `QuantitativeSubspace/README.md`.
-/

@[expose] public section

open Module Finset Matrix Submodule
open exteriorPower (plucker plucker_apply)

namespace Nat

/-- `C(2m, m)² (3m + 1) ≤ 16^m`: the central binomial coefficient is at most `4^m / √(3m+1)`. -/
theorem centralBinom_sq_mul_le (m : ℕ) : m.centralBinom ^ 2 * (3 * m + 1) ≤ 16 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := succ_mul_centralBinom_succ m
    have key : (2 * m + 1) ^ 2 * (3 * m + 4) + m = 4 * (m + 1) ^ 2 * (3 * m + 1) := by ring
    refine Nat.le_of_mul_le_mul_left (c := (m + 1) ^ 2) ?_ (by positivity)
    calc (m + 1) ^ 2 * ((m + 1).centralBinom ^ 2 * (3 * (m + 1) + 1))
        = ((m + 1) * (m + 1).centralBinom) ^ 2 * (3 * m + 4) := by ring
      _ = 4 * m.centralBinom ^ 2 * ((2 * m + 1) ^ 2 * (3 * m + 4)) := by rw [h]; ring
      _ ≤ 4 * m.centralBinom ^ 2 * (4 * (m + 1) ^ 2 * (3 * m + 1)) :=
          Nat.mul_le_mul_left _ (key ▸ Nat.le_add_right _ _)
      _ = 16 * (m + 1) ^ 2 * (m.centralBinom ^ 2 * (3 * m + 1)) := by ring
      _ ≤ 16 * (m + 1) ^ 2 * 16 ^ m := Nat.mul_le_mul_left _ ih
      _ = (m + 1) ^ 2 * 16 ^ (m + 1) := by ring

/-- **`p C(n, p)² ≤ 4ⁿ`** (EF13, end of the proof of Prop. 17.5). -/
theorem mul_choose_sq_le {n p : ℕ} (hp : p ≤ n) : p * n.choose p ^ 2 ≤ 4 ^ n := by
  induction n using Nat.strong_induction_on generalizing p with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · simp
  by_cases hpn : p = n
  · subst hpn
    rw [choose_self, one_pow, mul_one]
    exact (Nat.lt_pow_self (by norm_num)).le
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  by_cases h2 : 2 * p ≤ m + 1
  · have ih' := ih m (by omega) (p := p) (by omega)
    have hid := choose_mul_succ_eq m p
    refine Nat.le_of_mul_le_mul_right (c := (m + 1) ^ 2) ?_ (by positivity)
    calc p * (m + 1).choose p ^ 2 * (m + 1) ^ 2
        ≤ p * (m + 1).choose p ^ 2 * (2 * (m + 1 - p)) ^ 2 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
      _ = 4 * (p * ((m + 1).choose p * (m + 1 - p)) ^ 2) := by ring
      _ = 4 * (m + 1) ^ 2 * (p * m.choose p ^ 2) := by rw [← hid]; ring
      _ ≤ 4 * (m + 1) ^ 2 * 4 ^ m := Nat.mul_le_mul_left _ ih'
      _ = 4 ^ (m + 1) * (m + 1) ^ 2 := by ring
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hid := add_one_mul_choose_eq m q
  by_cases h3 : m + 1 ≤ 2 * q
  · have ih' := ih m (by omega) (p := q) (by omega)
    have hsq : (m + 1) ^ 2 ≤ 4 * q * (q + 1) := by
      calc (m + 1) ^ 2 ≤ (2 * q) ^ 2 := Nat.pow_le_pow_left h3 2
        _ ≤ 4 * q * (q + 1) := by ring_nf; omega
    refine Nat.le_of_mul_le_mul_right (c := (m + 1) ^ 2) ?_ (by positivity)
    calc (q + 1) * (m + 1).choose (q + 1) ^ 2 * (m + 1) ^ 2
        ≤ (q + 1) * (m + 1).choose (q + 1) ^ 2 * (4 * q * (q + 1)) := Nat.mul_le_mul_left _ hsq
      _ = 4 * q * ((m + 1).choose (q + 1) * (q + 1)) ^ 2 := by ring
      _ = 4 * (m + 1) ^ 2 * (q * m.choose q ^ 2) := by rw [← hid]; ring
      _ ≤ 4 * (m + 1) ^ 2 * 4 ^ m := Nat.mul_le_mul_left _ ih'
      _ = 4 ^ (m + 1) * (m + 1) ^ 2 := by ring
  · have hm : m = 2 * q := by omega
    subst hm
    have hc : (q + 1).centralBinom = 2 * (2 * q + 1).choose (q + 1) := by
      rw [centralBinom_eq_two_mul_choose, show 2 * (q + 1) = 2 * q + 1 + 1 by ring,
        choose_succ_succ, ← choose_symm_half]
      ring
    have hcb := centralBinom_sq_mul_le (q + 1)
    refine Nat.le_of_mul_le_mul_left (c := 4) ?_ (by norm_num)
    calc 4 * ((q + 1) * (2 * q + 1).choose (q + 1) ^ 2)
        = (q + 1).centralBinom ^ 2 * (q + 1) := by rw [hc]; ring
      _ ≤ (q + 1).centralBinom ^ 2 * (3 * (q + 1) + 1) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ 16 ^ (q + 1) := hcb
      _ = 4 * 4 ^ (2 * q + 1) := by rw [show (16 : ℕ) = 4 ^ 2 by norm_num, ← pow_mul]; ring

end Nat

namespace NumberField

/-! ### Successive infima of a height function -/

section Generic

variable {ι : Type*} (Ω : Type*) [Field Ω] (h : (ι → Ω) → ℝ)

/-- **The product of the first `m` successive infima is at most the product of the heights of
`m` independent points.** -/
theorem prod_heightInf_le_prod [Finite ι] {β : Type*} (x : β → ι → Ω)
    (hh : ∀ b, 0 ≤ h (x b)) (s : Finset β) (hs : LinearIndepOn Ω x (s : Set β)) :
    ∏ j ∈ range #s, heightInf Ω h (j + 1) ≤ ∏ b ∈ s, h (x b) := by
  classical
  revert hs
  refine Finset.induction_on_max_value (fun b ↦ h (x b))
    (motive := fun s ↦ LinearIndepOn Ω x (s : Set β) →
      ∏ j ∈ range #s, heightInf Ω h (j + 1) ≤ ∏ b ∈ s, h (x b)) s (fun _ ↦ by simp) ?_
  intro a s ha hmax ih hs
  have hs' : LinearIndepOn Ω x (s : Set β) := hs.mono (by simp)
  rw [card_insert_of_notMem ha, prod_range_succ, prod_insert ha, mul_comm (h (x a))]
  refine mul_le_mul (ih hs') ?_ (heightInf_nonneg _) (prod_nonneg fun b _ ↦ hh b)
  set t := insert a s
  have h1 : LinearIndependent Ω (fun b : t ↦ x b) := hs
  have hli : LinearIndependent Ω (fun j : Fin #t ↦ x (t.equivFin.symm j)) :=
    h1.comp _ t.equivFin.symm.injective
  have hle := heightInf_le_of_linearIndependent (h := h) hli (hh a) fun j ↦ by
    rcases mem_insert.1 (t.equivFin.symm j).2 with hb | hb
    · rw [hb]
    · exact hmax _ hb
  rwa [card_insert_of_notMem ha] at hle

/-- **Points close to the successive infima**: for `C > 1` there are independent `g_1, …, g_n`
with `h(g_j) ≤ C λ_j`, if the `λ_j` are positive. -/
theorem exists_linearIndependent_le_mul [Fintype ι] {C : ℝ} (hC : 1 < C)
    (hpos : ∀ i : Fin (Fintype.card ι), 0 < heightInf Ω h (i + 1)) :
    ∃ g : Fin (Fintype.card ι) → ι → Ω, LinearIndependent Ω g ∧
      ∀ j, h (g j) ≤ C * heightInf Ω h (j + 1) := by
  suffices H : ∀ m ≤ Fintype.card ι, ∃ g : Fin m → ι → Ω, LinearIndependent Ω g ∧
      ∀ j : Fin m, h (g j) ≤ C * heightInf Ω h (j + 1) from H _ le_rfl
  intro m hm
  induction m with
  | zero => exact ⟨Fin.elim0, linearIndependent_empty_type, fun j ↦ j.elim0⟩
  | succ m ih =>
    obtain ⟨g, hg, hgb⟩ := ih (by omega)
    have hlam := hpos ⟨m, by omega⟩
    have hlt : heightInf Ω h (m + 1) < C * heightInf Ω h (m + 1) := by
      simp only at hlam
      nlinarith
    obtain ⟨x, hx, hxg⟩ : ∃ x, h x ≤ C * heightInf Ω h (m + 1) ∧
        x ∉ span Ω (Set.range g) := by
      by_contra hcon
      push Not at hcon
      have hle : heightSpace Ω h (C * heightInf Ω h (m + 1)) ≤ span Ω (Set.range g) :=
        span_le.2 fun x hx ↦ hcon x hx
      have h1 := le_finrank_heightSpace (h := h) hm hlt
      have h2 := Submodule.finrank_mono hle
      rw [finrank_span_eq_card hg, Fintype.card_fin] at h2
      omega
    refine ⟨Fin.snoc g x, linearIndependent_finSnoc.2 ⟨hg, hxg⟩, Fin.lastCases ?_ fun j ↦ ?_⟩
    · simpa using hx
    · simpa using hgb j

end Generic

/-! ### Reindexing a system -/

section Reindex

variable {K : Type*} [Field K] [NumberField K] {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

namespace FormSystem

/-- The system `L` with forms and coordinates moved along `e : ι ≃ κ`. -/
noncomputable def reindex (L : FormSystem K ι) (e : ι ≃ κ) : FormSystem K κ where
  arch v := (L.arch v).reindex e e
  arch_det_ne_zero v := by rw [det_reindex_self]; exact L.arch_det_ne_zero v
  fin v := (L.fin v).reindex e e
  fin_det_ne_zero v := by rw [det_reindex_self]; exact L.fin_det_ne_zero v
  finite_range_fin := (L.finite_range_fin.image fun M ↦ M.reindex e e).subset <| by
    rintro _ ⟨v, rfl⟩
    exact ⟨L.fin v, ⟨v, rfl⟩, rfl⟩

end FormSystem

namespace FormWeight

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- Weights moved along `e : ι ≃ κ`. -/
noncomputable def reindex (a : FormWeight K ι) (e : ι ≃ κ) : FormWeight K κ where
  arch v k := a.arch v (e.symm k)
  arch_pos v _ := a.arch_pos v _
  fin v k := a.fin v (e.symm k)
  fin_pos v _ := a.fin_pos v _
  finite_setOf_fin_ne_one := a.finite_setOf_fin_ne_one.subset fun v hv h ↦ hv <| by
    funext k
    simp [h]

end FormWeight

namespace FormExponent

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- Exponents moved along `e : ι ≃ κ`. -/
noncomputable def reindex (c : FormExponent K ι) (e : ι ≃ κ) : FormExponent K κ where
  arch v k := c.arch v (e.symm k)
  fin v k := c.fin v (e.symm k)
  finite_setOf_fin_ne_zero := c.finite_setOf_fin_ne_zero.subset fun v hv h ↦ hv <| by
    funext k
    simp [h]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem weight_reindex (c : FormExponent K ι) (e : ι ≃ κ) {Q : ℝ} (hQ : 0 < Q) :
    (c.reindex e).weight hQ = (c.weight hQ).reindex e :=
  rfl

omit [DecidableEq ι] [DecidableEq κ] in
theorem sum_reindex (c : FormExponent K ι) (e : ι ≃ κ) : (c.reindex e).sum = c.sum := by
  simp only [sum, reindex]
  congr 1
  · exact sum_congr rfl fun v _ ↦ e.symm.sum_comp (c.arch v)
  · exact finsum_congr fun v ↦ e.symm.sum_comp (c.fin v)

end FormExponent

namespace FormSystem

variable (L : FormSystem K ι) (a : FormWeight K ι) (e : ι ≃ κ)

omit [DecidableEq ι] [DecidableEq κ] in
theorem _root_.Matrix.reindex_mulVec_apply {R : Type*} [CommSemiring R] (M : Matrix ι ι R)
    (x : κ → R) (k : κ) : (M.reindex e e *ᵥ x) k = (M *ᵥ (x ∘ e)) (e.symm k) := by
  simp only [mulVec, dotProduct, reindex_apply, submatrix_apply, Function.comp_apply]
  rw [← e.sum_comp]
  simp

variable {E : Type*} [Field E] [NumberField E] [Algebra K E]

omit [NumberField E] in
theorem archFactor_reindex (w : InfinitePlace E) (x : κ → E) :
    (L.reindex e).archFactor (a.reindex e) w x = L.archFactor a w (x ∘ e) := by
  simp only [archFactor]
  have hmap : ((L.reindex e).arch (w.comap (algebraMap K E))).map (algebraMap K E) =
      ((L.arch (w.comap (algebraMap K E))).map (algebraMap K E)).reindex e e := rfl
  simp_rw [hmap, reindex_mulVec_apply]
  exact e.symm.iSup_comp (g := fun i ↦ w ((((L.arch (w.comap (algebraMap K E))).map
    (algebraMap K E)) *ᵥ (x ∘ e)) i) / a.arch (w.comap (algebraMap K E)) i)

theorem finFactor_reindex (w : FinitePlace E) (x : κ → E) :
    (L.reindex e).finFactor (a.reindex e) w x = L.finFactor a w (x ∘ e) := by
  simp only [finFactor]
  have hmap : ((L.reindex e).fin (w.under K)).map (algebraMap K E) =
      ((L.fin (w.under K)).map (algebraMap K E)).reindex e e := rfl
  simp_rw [hmap, reindex_mulVec_apply]
  exact e.symm.iSup_comp (g := fun i ↦ w ((((L.fin (w.under K)).map (algebraMap K E)) *ᵥ
    (x ∘ e)) i) / a.fin (w.under K) i ^ w.localDegree K)

theorem mulHeight_reindex (x : κ → E) :
    (L.reindex e).mulHeight (a.reindex e) x = L.mulHeight a (x ∘ e) := by
  simp only [mulHeight, archFactor_reindex, finFactor_reindex]

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]

/-- **Reindexing preserves heights**: `H_{L ∘ e}(x) = H_L(x ∘ e)`. -/
theorem absMulHeight_reindex (x : κ → Ω) :
    (L.reindex e).absMulHeight (a.reindex e) x = L.absMulHeight a (x ∘ e) := by
  have := Twist.numberField_adjoin_range (K := K) x
  have hx : ∀ k, x k ∈ IntermediateField.adjoin K (Set.range x) :=
    fun k ↦ IntermediateField.subset_adjoin K _ ⟨k, rfl⟩
  rw [absMulHeight_eq_of_mem _ _ hx, absMulHeight_eq_of_mem (x := x ∘ e) _ _ (fun i ↦ hx (e i)),
    mulHeight_reindex]
  rfl

/-- The forms of the reindexed system are those of `L`, reindexed. -/
theorem arakelovFormHeight_reindex_le : (L.reindex e).arakelovFormHeight ≤ L.arakelovFormHeight :=
  by
  have h0 : 0 ≤ L.arakelovFormHeight :=
    Real.iSup_nonneg fun _ ↦ (NumberField.arakelovMulHeight_pos _).le
  refine Real.iSup_le (fun f ↦ ?_) h0
  obtain ⟨f, hf⟩ := f
  simp only [forms, Set.Finite.mem_toFinset, formSet, Set.mem_union, Set.mem_ofPred_eq] at hf
  rcases hf with ⟨v, k, rfl⟩ | ⟨v, k, rfl⟩
  · change NumberField.arakelovMulHeight ((L.reindex e).arch v k) ≤ _
    have hrow : (L.reindex e).arch v k = L.arch v (e.symm k) ∘ e.symm := rfl
    rw [hrow, NumberField.arakelovMulHeight_comp_equiv]
    exact L.arakelovMulHeight_le_arakelovFormHeight (L.arch_mem_forms v _)
  · change NumberField.arakelovMulHeight ((L.reindex e).fin v k) ≤ _
    have hrow : (L.reindex e).fin v k = L.fin v (e.symm k) ∘ e.symm := rfl
    rw [hrow, NumberField.arakelovMulHeight_comp_equiv]
    exact L.arakelovMulHeight_le_arakelovFormHeight (L.fin_mem_forms v _)

end FormSystem

end Reindex

/-! ### EF13 Lemma 17.1 -/

section Lemma171

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [LinearOrder ι]

theorem _root_.Matrix.abv_det_le_of_le_mul {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    [IsDomain R] (f : AbsoluteValue R ℝ) (M : Matrix n n R) {α β : n → ℝ}
    (h : ∀ i j, f (M i j) ≤ α i * β j) :
    f M.det ≤ (Fintype.card n).factorial * ((∏ i, α i) * ∏ j, β j) := by
  refine (abv_det_le_sum f M).trans ?_
  calc ∑ σ : Equiv.Perm n, ∏ i, f (M (σ i) i) ≤ ∑ σ : Equiv.Perm n, ∏ i, α (σ i) * β i :=
        sum_le_sum fun σ _ ↦ prod_le_prod₀ (fun i _ ↦ apply_nonneg _ _) fun i _ ↦ h _ _
    _ = ∑ _σ : Equiv.Perm n, (∏ i, α i) * ∏ j, β j :=
        sum_congr rfl fun σ _ ↦ by rw [prod_mul_distrib, Equiv.prod_comp σ α]
    _ = _ := by rw [sum_const, card_univ, Fintype.card_perm, nsmul_eq_mul]

theorem FinitePlace.apply_det_le_of_le_mul {E : Type*} [Field E] [NumberField E] {n : Type*}
    [Fintype n] [DecidableEq n] (w : FinitePlace E) (M : Matrix n n E) {α β : n → ℝ}
    (hα : ∀ i, 0 ≤ α i) (hβ : ∀ j, 0 ≤ β j) (h : ∀ i j, w (M i j) ≤ α i * β j) :
    w M.det ≤ (∏ i, α i) * ∏ j, β j :=
  FinitePlace.apply_det_le w M (mul_nonneg (prod_nonneg fun i _ ↦ hα i)
    (prod_nonneg fun j _ ↦ hβ j)) fun σ ↦ by
    calc ∏ i, w (M (σ i) i) ≤ ∏ i, α (σ i) * β i :=
          prod_le_prod₀ (fun _ _ ↦ apply_nonneg _ _) fun i _ ↦ h _ _
      _ = (∏ i, α i) * ∏ j, β j := by rw [prod_mul_distrib, Equiv.prod_comp σ α]

theorem _root_.Matrix.compound_row {ι' R : Type*} [Fintype ι'] [LinearOrder ι'] [CommRing R]
    (M : Matrix ι' ι' R) (p : ℕ) (s : Set.powersetCard ι' p) :
    M.compound p s = plucker p fun r ↦ M (Set.powersetCard.ofFinEmbEquiv.symm s r) := by
  funext t
  rw [compound_apply, plucker_apply, plucker_apply, ← det_transpose]
  rfl

namespace FormSystem

variable (L : FormSystem K ι) (a : FormWeight K ι)
variable {E : Type*} [Field E] [NumberField E] [Algebra K E]

omit [NumberField E] in
/-- **EF13 Lemma 17.1, infinite places**: the local factor of `x_1 ∧ ⋯ ∧ x_p` for `L̂` is at most
`p!` times the product of the local factors of the `x_r`. -/
theorem archFactor_exteriorPower_plucker_le_prod {p : ℕ} (w : InfinitePlace E)
    (x : Fin p → ι → E) :
    (L.exteriorPower p).archFactor (a.exteriorPower p) w (plucker p x) ≤
      p.factorial * ∏ r, L.archFactor a w (x r) := by
  set v := w.comap (algebraMap K E)
  have hy (r : Fin p) (i : ι) : w (((L.arch v).map (algebraMap K E) *ᵥ x r) i) ≤
      L.archFactor a w (x r) * a.arch v i := by
    have h1 : w (((L.arch v).map (algebraMap K E) *ᵥ x r) i) / a.arch v i ≤
        L.archFactor a w (x r) :=
      le_ciSup (f := fun i ↦ w (((L.arch v).map (algebraMap K E) *ᵥ x r) i) / a.arch v i)
        (Finite.bddAbove_range _) i
    rwa [div_le_iff₀ (a.arch_pos v i)] at h1
  refine Real.iSup_le (fun s ↦ ?_) (mul_nonneg (Nat.cast_nonneg _)
    (prod_nonneg fun r _ ↦ L.archFactor_nonneg a w _))
  have hpos : 0 < ∏ i ∈ s.val, a.arch v i := prod_pos fun i _ ↦ a.arch_pos v i
  change w ((((L.arch v).compound p).map (algebraMap K E) *ᵥ plucker p x) s) /
    ∏ i ∈ s.val, a.arch v i ≤ _
  rw [compound_map_mulVec_plucker, plucker_apply, div_le_iff₀ hpos]
  calc w (Matrix.of fun r q ↦ ((L.arch v).map (algebraMap K E) *ᵥ x r)
        (Set.powersetCard.ofFinEmbEquiv.symm s q)).det
      ≤ (Fintype.card (Fin p)).factorial * ((∏ r, L.archFactor a w (x r)) *
          ∏ q, a.arch v (Set.powersetCard.ofFinEmbEquiv.symm s q)) :=
        abv_det_le_of_le_mul w.1 _ fun r q ↦ hy r _
    _ = _ := by rw [Fintype.card_fin, Set.powersetCard.prod_ofFinEmbEquiv_symm]; ring

/-- **EF13 Lemma 17.1, finite places**. -/
theorem finFactor_exteriorPower_plucker_le_prod {p : ℕ} (w : FinitePlace E) (x : Fin p → ι → E) :
    (L.exteriorPower p).finFactor (a.exteriorPower p) w (plucker p x) ≤
      ∏ r, L.finFactor a w (x r) := by
  set v := w.under K
  set e := w.localDegree K
  have hy (r : Fin p) (i : ι) : w (((L.fin v).map (algebraMap K E) *ᵥ x r) i) ≤
      L.finFactor a w (x r) * a.fin v i ^ e := by
    have h1 : w (((L.fin v).map (algebraMap K E) *ᵥ x r) i) / a.fin v i ^ e ≤
        L.finFactor a w (x r) :=
      le_ciSup (f := fun i ↦ w (((L.fin v).map (algebraMap K E) *ᵥ x r) i) / a.fin v i ^ e)
        (Finite.bddAbove_range _) i
    rwa [div_le_iff₀ (pow_pos (a.fin_pos v i) _)] at h1
  refine Real.iSup_le (fun s ↦ ?_) (prod_nonneg fun r _ ↦ L.finFactor_nonneg a w _)
  have hpos : 0 < (∏ i ∈ s.val, a.fin v i) ^ e := pow_pos (prod_pos fun i _ ↦ a.fin_pos v i) _
  change w ((((L.fin v).compound p).map (algebraMap K E) *ᵥ plucker p x) s) /
    (∏ i ∈ s.val, a.fin v i) ^ e ≤ _
  rw [compound_map_mulVec_plucker, plucker_apply, div_le_iff₀ hpos, ← prod_pow,
    ← Set.powersetCard.prod_ofFinEmbEquiv_symm]
  exact FinitePlace.apply_det_le_of_le_mul w _ (fun r ↦ L.finFactor_nonneg a w _)
    (fun q ↦ pow_nonneg (a.fin_pos v _).le _) fun r q ↦ hy r _

/-- **EF13 Lemma 17.1, relative form**: `H(x_1 ∧ ⋯ ∧ x_p) ≤ p!^{[E:ℚ]} ∏_r H(x_r)`. -/
theorem mulHeight_exteriorPower_plucker_le {p : ℕ} {x : Fin p → ι → E}
    (hx : LinearIndependent E x) :
    (L.exteriorPower p).mulHeight (a.exteriorPower p) (plucker p x) ≤
      (p.factorial : ℝ) ^ finrank ℚ E * ∏ r, L.mulHeight a (x r) := by
  have hx0 : ∀ r, x r ≠ 0 := hx.ne_zero
  have hpx : plucker p x ≠ 0 := exteriorPower.plucker_ne_zero hx
  have harch : ∏ w : InfinitePlace E,
      (L.exteriorPower p).archFactor (a.exteriorPower p) w (plucker p x) ^ w.mult ≤
        (p.factorial : ℝ) ^ finrank ℚ E * ∏ r, ∏ w : InfinitePlace E,
          L.archFactor a w (x r) ^ w.mult := by
    calc _ ≤ ∏ w : InfinitePlace E, ((p.factorial : ℝ) * ∏ r, L.archFactor a w (x r)) ^ w.mult :=
          prod_le_prod₀ (fun w _ ↦ pow_nonneg ((L.exteriorPower p).archFactor_nonneg _ w _) _)
            fun w _ ↦ pow_le_pow_left₀ ((L.exteriorPower p).archFactor_nonneg _ w _)
              (L.archFactor_exteriorPower_plucker_le_prod a w x) _
      _ = _ := by
          simp_rw [mul_pow, prod_mul_distrib, prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq,
            ← prod_pow]
          rw [prod_comm]
  have hfin : ∏ᶠ w : FinitePlace E,
      (L.exteriorPower p).finFactor (a.exteriorPower p) w (plucker p x) ≤
        ∏ r, ∏ᶠ w : FinitePlace E, L.finFactor a w (x r) := by
    rw [← finprod_prod_comm univ (fun w r ↦ L.finFactor a w (x r))
      (fun r _ ↦ L.hasFiniteMulSupport_finFactor a (hx0 r))]
    exact finprod_le_finprod₀ ((L.exteriorPower p).hasFiniteMulSupport_finFactor _ hpx)
      (fun w ↦ (L.exteriorPower p).finFactor_nonneg _ w _)
      (Function.hasFiniteMulSupport_prod _ _ fun r _ ↦ L.hasFiniteMulSupport_finFactor a (hx0 r))
      fun w ↦ L.finFactor_exteriorPower_plucker_le_prod a w x
  calc (L.exteriorPower p).mulHeight (a.exteriorPower p) (plucker p x)
      ≤ ((p.factorial : ℝ) ^ finrank ℚ E * ∏ r, ∏ w : InfinitePlace E,
          L.archFactor a w (x r) ^ w.mult) * ∏ r, ∏ᶠ w : FinitePlace E, L.finFactor a w (x r) :=
        mul_le_mul harch hfin (finprod_nonneg fun w ↦ (L.exteriorPower p).finFactor_nonneg _ w _)
          (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (prod_nonneg fun r _ ↦
            prod_nonneg fun w _ ↦ pow_nonneg (L.archFactor_nonneg a w _) _))
    _ = _ := by simp only [mulHeight, prod_mul_distrib]; ring

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]

/-- **EF13 Lemma 17.1**: `H_{L̂,â}(x_1 ∧ ⋯ ∧ x_p) ≤ p! ∏_r H_{L,a}(x_r)` for independent
`x_1, …, x_p ∈ Ωⁿ`. -/
theorem absMulHeight_exteriorPower_plucker_le {p : ℕ} {x : Fin p → ι → Ω}
    (hx : LinearIndependent Ω x) :
    (L.exteriorPower p).absMulHeight (a.exteriorPower p) (plucker p x) ≤
      p.factorial * ∏ r, L.absMulHeight a (x r) := by
  set z : Fin p × ι → Ω := fun q ↦ x q.1 q.2
  set F := IntermediateField.adjoin K (Set.range z)
  have := Twist.numberField_adjoin_range (K := K) z
  have hmem : ∀ r i, x r i ∈ F := fun r i ↦ IntermediateField.subset_adjoin K _ ⟨(r, i), rfl⟩
  set y : Fin p → ι → F := fun r i ↦ ⟨x r i, hmem r i⟩
  have hxy : (fun r ↦ algebraMap F Ω ∘ y r) = x := rfl
  have hy : LinearIndependent F y := by
    have h1 : LinearIndependent F x := hx.restrict_scalars' F
    exact LinearIndependent.of_comp ((Algebra.linearMap F Ω).compLeft ι) h1
  have hpl : ∀ s, plucker p x s = algebraMap F Ω (plucker p y s) := fun s ↦ by
    rw [← hxy, exteriorPower.plucker_map]
  have hplm : ∀ s, plucker p x s ∈ F := fun s ↦ by rw [hpl s]; exact (plucker p y s).2
  have hd : finrank ℚ F ≠ 0 := finrank_pos.ne'
  rw [absMulHeight_eq_of_mem _ _ hplm]
  simp_rw [fun r ↦ absMulHeight_eq_of_mem (x := x r) L a (hmem r)]
  have hvec : (fun s ↦ (⟨plucker p x s, hplm s⟩ : F)) = plucker p y :=
    funext fun s ↦ Subtype.ext (hpl s)
  have hvec' : ∀ r, (fun i ↦ (⟨x r i, hmem r i⟩ : F)) = y r := fun r ↦ rfl
  rw [hvec]
  simp_rw [hvec']
  have h0 : ∀ r, 0 ≤ L.mulHeight a (y r) := fun r ↦ L.mulHeight_nonneg a _
  calc (L.exteriorPower p).mulHeight (a.exteriorPower p) (plucker p y) ^ ((finrank ℚ F : ℝ))⁻¹
      ≤ ((p.factorial : ℝ) ^ finrank ℚ F * ∏ r, L.mulHeight a (y r)) ^ ((finrank ℚ F : ℝ))⁻¹ :=
        Real.rpow_le_rpow ((L.exteriorPower p).mulHeight_nonneg _ _)
          (L.mulHeight_exteriorPower_plucker_le a hy) (by positivity)
    _ = p.factorial * ∏ r, L.mulHeight a (y r) ^ ((finrank ℚ F : ℝ))⁻¹ := by
        rw [Real.mul_rpow (by positivity) (prod_nonneg fun r _ ↦ h0 r),
          Real.pow_rpow_inv_natCast (Nat.cast_nonneg _) hd,
          Real.finsetProd_rpow _ _ fun r _ ↦ h0 r]

/-- **EF13 (17.10)**: the forms of `L̂` have Arakelov height at most `H₂^p`. -/
theorem arakelovFormHeight_exteriorPower_le (p : ℕ) :
    (L.exteriorPower p).arakelovFormHeight ≤ L.arakelovFormHeight ^ p := by
  have h0 : 0 ≤ L.arakelovFormHeight :=
    Real.iSup_nonneg fun _ ↦ (NumberField.arakelovMulHeight_pos _).le
  have key : ∀ (M : Matrix ι ι K), (∀ i, M i ∈ L.forms) → ∀ s,
      NumberField.arakelovMulHeight ((M.compound p) s) ≤ L.arakelovFormHeight ^ p := by
    intro M hM s
    set A : Matrix (Fin p) ι K := Matrix.of fun r ↦ M (Set.powersetCard.ofFinEmbEquiv.symm s r)
    rw [compound_row]
    calc NumberField.arakelovMulHeight (plucker p A.row)
        ≤ ∏ r, NumberField.arakelovMulHeight (A r) :=
          Matrix.arakelovMulHeight_plucker_row_le_prod A
      _ ≤ ∏ _r : Fin p, L.arakelovFormHeight :=
          prod_le_prod₀ (fun r _ ↦ (NumberField.arakelovMulHeight_pos _).le) fun r _ ↦
            L.arakelovMulHeight_le_arakelovFormHeight (hM _)
      _ = L.arakelovFormHeight ^ p := by rw [prod_const, card_univ, Fintype.card_fin]
  refine Real.iSup_le (fun f ↦ ?_) (pow_nonneg h0 p)
  obtain ⟨f, hf⟩ := f
  simp only [forms, Set.Finite.mem_toFinset, formSet, Set.mem_union, Set.mem_ofPred_eq] at hf
  rcases hf with ⟨v, s, rfl⟩ | ⟨v, s, rfl⟩
  · exact key (L.arch v) (L.arch_mem_forms v) s
  · exact key (L.fin v) (L.fin_mem_forms v) s

end FormSystem

end Lemma171

/-! ### The exponent sum of the exterior power -/

section ExponentSum

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

/-- **`α̂ = C(n-1, p-1) α`** (EF13, proof of Lemma 17.2). -/
theorem FormExponent.sum_exteriorPower (c : FormExponent K ι) {p : ℕ} (hp : 1 ≤ p) :
    (c.exteriorPower p).sum = (Fintype.card ι - 1).choose (p - 1) * c.sum := by
  classical
  simp only [FormExponent.sum, c.sum_exteriorPower_arch hp, c.sum_exteriorPower_fin hp, mul_add]
  rw [mul_sum, mul_finsum]

end ExponentSum

/-! ### EF13 Lemma 6.1 -/

section Lemma61

variable {K : Type*} [Field K] [NumberField K]

theorem _root_.Set.powersetCard.exists_ofFinEmbEquiv_symm_eq {α : Type*} [LinearOrder α] {p : ℕ}
    (s : Set.powersetCard α p) {i : α} (hi : i ∈ s.val) :
    ∃ b, Set.powersetCard.ofFinEmbEquiv.symm s b = i :=
  (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s i).2 hi

/-- The wedges `ĝ_I` of independent `g_1, …, g_n`, moved to `Ω^N` along `e`, are independent. -/
theorem linearIndependent_compound_comp {n N p : ℕ} {Ω : Type*} [Field Ω]
    {G : Matrix (Fin n) (Fin n) Ω} (hG : G.det ≠ 0) (e : Set.powersetCard (Fin n) p ≃ Fin N) :
    LinearIndependent Ω fun s ↦ G.compound p s ∘ e.symm := by
  have hrows : LinearIndependent Ω (G.compound p).row :=
    linearIndependent_rows_iff_isUnit.2 ((isUnit_iff_isUnit_det _).2
      (det_compound_ne_zero p hG).isUnit)
  exact hrows.map' (LinearMap.funLeft Ω Ω e.symm)
    (LinearMap.ker_eq_bot.2 (LinearMap.funLeft_injective_of_surjective _ _ _ e.symm.surjective))

/-- **EF13 Lemma 6.1.** Let `G` have independent rows `g_0, …, g_{n-1}` with `g_i ∈ V ⊗ Ω` for
`i < k = dim V`, and `p = n - k`. The span of the wedges `ĝ_I`, `I ≠ {k, …, n-1}`, moved to `Ω^N`
along `e`, is the extension of a subspace of `K^N` with the Arakelov height of `V`. -/
theorem exists_extendPi_span_compound_eq {n N : ℕ} {Ω : Type*} [Field Ω] [Algebra K Ω]
    (G : Matrix (Fin n) (Fin n) Ω) (hG : G.det ≠ 0) (k : Fin n)
    (e : Set.powersetCard (Fin n) (n - k) ≃ Fin N) {V : Submodule K (Fin n → K)}
    (hVk : finrank K V = k) (hGV : ∀ i : Fin n, (i : ℕ) < k → G i ∈ V.extendPi Ω) :
    ∃ W : Submodule K (Fin N → K),
      W.extendPi Ω = span Ω ((fun s ↦ G.compound (n - k) s ∘ e.symm) '' {s | s ≠ topSet k}) ∧
      finrank K W + 1 = N ∧ W.arakelovMulHeight = V.arakelovMulHeight := by
  classical
  set Vp := V.dualAnnihilator.comap (Module.piEquiv (Fin n) K K).toLinearMap
  have hVp : finrank K Vp = (n - k) := by
    have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq V
    have h2 : finrank K Vp = finrank K V.dualAnnihilator := by
      have : Vp = V.dualAnnihilator.map (Module.piEquiv (Fin n) K K).symm.toLinearMap :=
        Submodule.comap_piEquiv_dualAnnihilator_eq_map V
      rw [this]
      exact LinearEquiv.finrank_map_eq _ _
    rw [Module.finrank_fin_fun] at h1
    omega
  set bφ := Module.finBasisOfFinrankEq K Vp hVp
  set φ : Fin (n - k) → Fin n → K := fun a ↦ bφ a
  have hφ : LinearIndependent K φ := bφ.linearIndependent.map' Vp.subtype Vp.ker_subtype
  have hspanφ : span K (Set.range φ) = Vp := by
    rw [show Set.range φ = Vp.subtype '' Set.range bφ from Set.range_comp _ _, ← map_span,
      bφ.span_eq, map_subtype_top]
  have hφV : ∀ a, ∀ y ∈ V, y ⬝ᵥ φ a = 0 := fun a ↦
    Submodule.mem_comap_piEquiv_dualAnnihilator.1 (bφ a).2
  set Φ := plucker (n - k) φ
  have hΦ : Φ ≠ 0 := exteriorPower.plucker_ne_zero hφ
  -- the hyperplane `W = Φ̂^⊥` of `K^N`
  set ψ : Module.Dual K (Fin N → K) := ∑ m, Φ (e.symm m) • LinearMap.proj m
  have hψapp : ∀ x : Fin N → K, ψ x = ∑ m, Φ (e.symm m) * x m := fun x ↦ by
    simp [ψ, LinearMap.sum_apply]
  have hψsingle : ∀ m, ψ (Pi.single m 1) = Φ (e.symm m) := fun m ↦ by
    rw [hψapp]
    simp [Pi.single_apply]
  obtain ⟨s₀, hs₀⟩ : ∃ s₀, Φ s₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hΦ (funext h)
  have hψ0 : ψ ≠ 0 := fun h ↦ hs₀ (by
    have := hψsingle (e s₀)
    rw [h, LinearMap.zero_apply, e.symm_apply_apply] at this
    exact this.symm)
  set W := LinearMap.ker ψ
  have hW := Module.Dual.finrank_ker_add_one_of_ne_zero hψ0
  rw [Module.finrank_fin_fun] at hW
  refine ⟨W, ?_, hW, ?_⟩
  · set ψΩ := FormSystem.dualExtend (Ω := Ω) ψ
    have hψΩ0 : ψΩ ≠ 0 := fun h ↦ hs₀ (by
      have h2 : ψΩ (extendLin Ω (Pi.single (e s₀) 1 : Fin N → K)) =
          algebraMap K Ω (ψ (Pi.single (e s₀) 1)) :=
        FormSystem.dualExtend_extendLin (Ω := Ω) ψ _
      rw [h, LinearMap.zero_apply, hψsingle, e.symm_apply_apply] at h2
      exact (map_eq_zero_iff _ (algebraMap K Ω).injective).1 h2.symm)
    have hZ := Module.Dual.finrank_ker_add_one_of_ne_zero hψΩ0
    rw [Module.finrank_fin_fun] at hZ
    -- `W ⊗ Ω = ker ψ̂`
    have hWZ : W.extendPi Ω = LinearMap.ker ψΩ := by
      refine eq_of_le_of_finrank_eq (span_le.2 ?_) ?_
      · rintro _ ⟨y, hy, rfl⟩
        change ψΩ (extendLin Ω y) = 0
        rw [FormSystem.dualExtend_extendLin, LinearMap.mem_ker.1 hy, map_zero]
      · rw [finrank_extendPi]
        change finrank K (LinearMap.ker ψ) = _
        omega
    -- the wedges lie in `ker ψ̂`
    have hcol : ∀ a, ∀ i : Fin n, (i : ℕ) < k → (algebraMap K Ω ∘ φ a) ⬝ᵥ G i = 0 := by
      intro a i hi
      have hmem := hGV i hi
      refine Submodule.span_induction (p := fun z _ ↦ (algebraMap K Ω ∘ φ a) ⬝ᵥ z = 0)
        ?_ (by simp) (fun x y _ _ hx hy ↦ by rw [dotProduct_add, hx, hy, add_zero])
        (fun t x _ hx ↦ by rw [dotProduct_smul, hx, smul_zero]) hmem
      rintro _ ⟨y, hy, rfl⟩
      rw [extendLin_apply, ← RingHom.map_dotProduct, dotProduct_comm, hφV a y hy, map_zero]
    have hwedge : ∀ s ≠ topSet k, ψΩ (G.compound (n - k) s ∘ e.symm) = 0 := by
      intro s hs
      obtain ⟨i, his, hik⟩ : ∃ i ∈ s.val, (i : ℕ) < k := by
        by_contra h
        push Not at h
        exact hs ((Set.powersetCard.eq_iff_subset).2 fun i hi ↦ (mem_topSet k).2 (h i hi))
      obtain ⟨b₀, hb₀⟩ := Set.powersetCard.exists_ofFinEmbEquiv_symm_eq s his
      rw [FormSystem.dualExtend_apply]
      simp_rw [hψsingle]
      have hsum : ∑ m, algebraMap K Ω (Φ (e.symm m)) * (G.compound (n - k) s ∘ e.symm) m =
          ∑ t, plucker (n - k) (fun a ↦ algebraMap K Ω ∘ φ a) t *
            plucker (n - k) (fun r ↦ G (Set.powersetCard.ofFinEmbEquiv.symm s r)) t := by
        rw [← e.symm.sum_comp]
        refine sum_congr rfl fun t _ ↦ ?_
        rw [Function.comp_apply, compound_row, exteriorPower.plucker_map]
      rw [hsum, exteriorPower.sum_plucker_mul_plucker]
      exact det_eq_zero_of_column_eq_zero b₀ fun a ↦ by
        simp only [of_apply, hb₀]
        exact hcol a i hik
    -- the wedges span a space of dimension `N - 1`
    set T := {s : Set.powersetCard (Fin n) (n - k) | s ≠ topSet k}
    set f : Set.powersetCard (Fin n) (n - k) → Fin N → Ω := fun s ↦ G.compound (n - k) s ∘ e.symm
    have hf : LinearIndependent Ω f := linearIndependent_compound_comp hG e
    have hfT : LinearIndependent Ω (fun s : T ↦ f s) := hf.comp _ Subtype.val_injective
    have hcardT : Fintype.card T = N - 1 := by
      have h1 := Fintype.card_subtype_compl
        (fun s : Set.powersetCard (Fin n) (n - k) ↦ s = topSet k)
      rw [Fintype.card_subtype_eq, Fintype.card_congr e, Fintype.card_fin] at h1
      exact h1
    have hspan : span Ω (f '' T) = LinearMap.ker ψΩ := by
      refine eq_of_le_of_finrank_eq (span_le.2 ?_) ?_
      · rintro _ ⟨s, hs, rfl⟩
        exact hwedge s hs
      · rw [Set.image_eq_range, finrank_span_eq_card hfT, hcardT]
        omega
    rw [hWZ, ← hspan]
  · -- `H(W) = H(span Φ̂) = H(Φ) = H(span φ) = H(V^⊥) = H(V)`
    set B : Matrix (Fin 1) (Fin N) K := Matrix.of fun _ ↦ Φ ∘ e.symm
    have hker : W = LinearMap.ker B.mulVecLin := by
      ext x
      simp only [W, LinearMap.mem_ker, hψapp, Matrix.mulVecLin_apply, funext_iff,
        Fin.forall_fin_one, Matrix.mulVec, dotProduct, B, of_apply, Function.comp_apply,
        Pi.zero_apply]
    have hΦe : Φ ∘ e.symm ≠ 0 := fun h ↦ hs₀ (by simpa using congrFun h (e s₀))
    rw [hker, Matrix.arakelovMulHeight_ker_mulVecLin,
      show Set.range B.row = {Φ ∘ e.symm} from Set.range_const,
      arakelovMulHeight_span_singleton hΦe, NumberField.arakelovMulHeight_comp_equiv,
      ← arakelovMulHeight_span_range hφ, hspanφ,
      Submodule.arakelovMulHeight_comap_piEquiv_dualAnnihilator]

end Lemma61

end NumberField
