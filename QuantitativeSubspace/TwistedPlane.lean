/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.TwistedMinkowski
public import QuantitativeSubspace.TwistedSymmetric
public import Mathlib.FieldTheory.IsAlgClosed.Basic

-- Used only inside proofs.
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

/-!
# The absolute Minkowski theorem in the plane

D. Roy and J. L. Thunder, *An absolute Siegel's lemma*, J. reine angew. Math. **476** (1996),
1–26, Prop. 5.3: for a twist `A` of the plane over a number field `K`,

```text
μ₁(A) μ₂(A) ≤ 2 |det A|_𝔸,
```

the absolute minima taken over an algebraically closed field. The constant does not depend on `K`.
The proof, for each `r ≥ 1`:

1. Minkowski over `K` (Lemma 5.2, `TwistedMinkowski.lean`) applied to `S^r A` gives a basis
   `α₁, …, α_{r+1}` of the binary forms of degree `r` over `K` with
   `∏ H_{S^r A}(α_i) ≤ (|D_K|^{1/(2d)} √(r+1))^{r+1} |det A|_𝔸^{r(r+1)/2}`.
2. Over `Ω` each `α_i` splits into `r` linear forms `x_{i1}, …, x_{ir}`
   (`exists_eq_C_mul_prod_binLinear`, a factor `(1, 0)` for each root at infinity), and Lemma 4.8
   (`TwistedSymmetric.lean`) bounds `∏_j H_A(x_{ij}) ≤ √2^r H_{S^r A}(α_i)`.
3. **The counting argument** (`exists_linearIndependent_pair`): with `y₁` the `x_{ij}` of least
   height, `y₁` is proportional to at most `r(r+1)/2` of them, because independent forms divisible
   by `ℓ_{y₁}^s` number at most `r + 1 - s` (`card_filter_lt_card_le`); with `y₂` the least among
   the others, `(H(y₁) H(y₂))^{r(r+1)/2} ≤ ∏ H(x_{ij})`.

Taking the `r(r+1)/2`-th root gives `μ₁ μ₂ ≤ c_r |det A|_𝔸` with
`c_r = 2 (|D_K|^{1/d} (r+1))^{1/r}` (`planeConst`, `absMinimum_one_mul_absMinimum_two_le`), and
`c_r → 2` (`tendsto_planeConst`). RT also bound the degrees of `y₁, y₂` by `r`; the absolute minima
do not need it.

## Main definitions

* `NumberField.Twist.planeConst r`: the constant for a given `r` (over the implicit `K`).

## Main results

* `Polynomial.exists_eq_C_mul_prod_binLinear`: binary forms split over an algebraically closed
  field.
* `Polynomial.exists_linearIndependent_pair`: the counting argument.
* `NumberField.Twist.absMinimum_one_mul_absMinimum_two_le`: RT96 Prop. 5.3 for a given `r`.
* `NumberField.Twist.absMinimum_one_mul_absMinimum_two_le_two_mul`: RT96 Prop. 5.3,
  `μ₁ μ₂ ≤ 2 |det A|_𝔸`.

This is milestone Q2.2c of `QuantitativeSubspace/README.md` (its second part).
-/

@[expose] public section

open Finset Polynomial

namespace Polynomial

variable {Ω : Type*} [Field Ω]

theorem coeffVec_C_mul (r : ℕ) (c : Ω) (p : Polynomial Ω) :
    coeffVec r (C c * p) = c • coeffVec r p := by
  ext k
  simp [coeffVec, coeff_C_mul]

theorem binLinear_smul (a : Ω) (y : Fin 2 → Ω) : binLinear (a • y) = C a * binLinear y := by
  simp only [binLinear, Pi.smul_apply, smul_eq_mul, C_mul]
  ring

/-- **A binary form of degree `r` splits into `r` linear forms** over an algebraically closed
field: a nonzero polynomial of degree at most `r` is `c ∏_{j < r} (x_{j0} + x_{j1} T)` with every
`x_j ≠ 0` (a factor `x_j = (1, 0)` for each missing degree, the root at infinity). -/
theorem exists_eq_C_mul_prod_binLinear [IsAlgClosed Ω] {r : ℕ} {p : Polynomial Ω} (hp0 : p ≠ 0)
    (hp : p.natDegree ≤ r) :
    ∃ c ≠ 0, ∃ x : Fin r → Fin 2 → Ω, (∀ j, x j ≠ 0) ∧ p = C c * ∏ j, binLinear (x j) := by
  induction r generalizing p with
  | zero =>
    refine ⟨p.coeff 0, fun h ↦ hp0 ?_, finZeroElim, finZeroElim, ?_⟩
    · rw [eq_C_of_natDegree_le_zero hp, h, C_0]
    · rw [Fin.prod_univ_zero, mul_one]
      exact eq_C_of_natDegree_le_zero hp
  | succ r ih =>
    by_cases hd : p.natDegree = 0
    · refine ⟨p.coeff 0, fun h ↦ hp0 ?_, fun _ ↦ ![1, 0], fun _ h ↦ ?_, ?_⟩
      · rw [eq_C_of_natDegree_eq_zero hd, h, C_0]
      · simpa using congrFun h 0
      · simp only [binLinear, Matrix.cons_val_zero, Matrix.cons_val_one, C_1, C_0, zero_mul,
          add_zero, prod_const_one, mul_one]
        exact eq_C_of_natDegree_eq_zero hd
    obtain ⟨ρ, hρ⟩ := IsAlgClosed.exists_root p fun h ↦ hd (natDegree_eq_of_degree_eq_some h)
    have hq := mul_divByMonic_eq_iff_isRoot.mpr hρ
    set q := p /ₘ (X - C ρ)
    have hq0 : q ≠ 0 := fun h ↦ hp0 (by rw [← hq, h, mul_zero])
    have hqd : q.natDegree ≤ r := by
      have := congrArg natDegree hq
      rw [natDegree_mul (X_sub_C_ne_zero ρ) hq0, natDegree_X_sub_C] at this
      omega
    obtain ⟨c, hc, x, hx, hqx⟩ := ih hq0 hqd
    refine ⟨c, hc, Fin.cons ![-ρ, 1] x, fun j ↦ ?_, ?_⟩
    · refine Fin.cases (fun h ↦ ?_) (fun j ↦ ?_) j
      · simpa using congrFun h 1
      · simpa using hx j
    · rw [Fin.prod_univ_succ, Fin.cons_zero]
      simp only [Fin.cons_succ]
      rw [← hq, hqx]
      simp only [binLinear, Matrix.cons_val_zero, Matrix.cons_val_one, C_neg, C_1]
      ring

open scoped Classical in
/-- Splitting off the factors proportional to `y`: `∏ ℓ_{x_j} = b ℓ_y^m ∏_{j ∉ J} ℓ_{x_j}`, where
`J` is the set of `j` with `x_j ∈ Ω y` and `m = #J`. -/
theorem exists_prod_binLinear_eq {r : ℕ} (x : Fin r → Fin 2 → Ω) (y : Fin 2 → Ω) :
    ∃ b : Ω, ∏ j, binLinear (x j) = C b * binLinear y ^ #{j | ∃ a : Ω, x j = a • y} *
      ∏ j ∈ {j | ¬ ∃ a : Ω, x j = a • y}, binLinear (x j) := by
  let a : Fin r → Ω := fun j ↦ if h : ∃ a : Ω, x j = a • y then h.choose else 0
  have ha : ∀ j ∈ ({j | ∃ a : Ω, x j = a • y} : Finset (Fin r)),
      binLinear (x j) = C (a j) * binLinear y := fun j hj ↦ by
    have h : ∃ a : Ω, x j = a • y := (mem_filter.mp hj).2
    simp only [a, dite_eq_left h]
    rw [← binLinear_smul, ← h.choose_spec]
  refine ⟨∏ j ∈ {j | ∃ a : Ω, x j = a • y}, a j, ?_⟩
  rw [← prod_filter_mul_prod_filter_not univ (fun j ↦ ∃ a : Ω, x j = a • y),
    prod_congr rfl ha, prod_mul_distrib, prod_const, map_prod]

open Module in
open scoped Classical in
/-- **The forms divisible by `ℓ^{t+1}`.** Independent binary forms of degree `r`, each divisible
by `ℓ_y^{t+1}` in the homogeneous sense, number at most `r - t`: the forms `ℓ_y^{t+1} Q` with `Q`
of degree `r - t - 1` make up a space of dimension `r - t`. -/
theorem card_filter_lt_card_le {κ : Type*} [Fintype κ] {r : ℕ} {P : κ → Polynomial Ω}
    (hP : LinearIndependent Ω fun i ↦ coeffVec r (P i)) (c : κ → Ω) (x : κ → Fin r → Fin 2 → Ω)
    (hPx : ∀ i, P i = C (c i) * ∏ j, binLinear (x i j)) (y : Fin 2 → Ω) {t : ℕ} (ht : t < r) :
    #{i | t < #{j | ∃ a : Ω, x i j = a • y}} ≤ r - t := by
  set ℓ := binLinear y
  let Φ : (Fin (r - t) → Ω) →ₗ[Ω] (Fin (r + 1) → Ω) :=
    (LinearMap.pi fun k : Fin (r + 1) ↦ lcoeff Ω (k : ℕ)) ∘ₗ LinearMap.mulLeft Ω (ℓ ^ (t + 1)) ∘ₗ
      (degreeLT Ω (r - t)).subtype ∘ₗ (degreeLTEquiv Ω (r - t)).symm.toLinearMap
  set I : Finset κ := {i | t < #{j | ∃ a : Ω, x i j = a • y}}
  have hmem : ∀ i ∈ I, coeffVec r (P i) ∈ LinearMap.range Φ := by
    intro i hi
    have hm : t < #{j | ∃ a : Ω, x i j = a • y} := (mem_filter.mp hi).2
    obtain ⟨b, hb⟩ := exists_prod_binLinear_eq (x i) y
    set m := #{j | ∃ a : Ω, x i j = a • y}
    set R := ∏ j ∈ {j | ¬ ∃ a : Ω, x i j = a • y}, binLinear (x i j)
    set Q := C (c i * b) * ℓ ^ (m - (t + 1)) * R
    have hpow : ℓ ^ m = ℓ ^ (t + 1) * ℓ ^ (m - (t + 1)) := by
      rw [← pow_add, Nat.add_sub_cancel' hm]
    have hPQ : P i = ℓ ^ (t + 1) * Q := by
      rw [hPx, hb, hpow]
      simp only [Q, C_mul]
      ring
    have hcard : m + #{j | ¬ ∃ a : Ω, x i j = a • y} = r := by
      rw [card_filter_add_card_filter_not, card_univ, Fintype.card_fin]
    have hR : R.natDegree ≤ #{j | ¬ ∃ a : Ω, x i j = a • y} :=
      (natDegree_prod_le _ _).trans ((sum_le_sum fun j _ ↦ natDegree_binLinear_le _).trans
        (by simp))
    have hQ : Q.natDegree < r - t := by
      have h1 := natDegree_mul_le (p := C (c i * b) * ℓ ^ (m - (t + 1))) (q := R)
      have h2 := natDegree_C_mul_le (c i * b) (ℓ ^ (m - (t + 1)))
      have h3 : (ℓ ^ (m - (t + 1))).natDegree ≤ m - (t + 1) := by
        simpa using natDegree_pow_le_of_le (m - (t + 1)) (natDegree_binLinear_le y)
      change (C (c i * b) * ℓ ^ (m - (t + 1)) * R).natDegree < r - t
      omega
    refine ⟨degreeLTEquiv Ω (r - t) ⟨Q, mem_degreeLT.mpr
      (degree_le_natDegree.trans_lt (by exact_mod_cast hQ))⟩, ?_⟩
    ext k
    simp [Φ, coeffVec, hPQ]
  have hli : LinearIndependent Ω fun i : I ↦
      (⟨coeffVec r (P i), hmem i i.2⟩ : LinearMap.range Φ) :=
    LinearIndependent.of_comp (LinearMap.range Φ).subtype (hP.comp _ Subtype.val_injective)
  calc #I = Fintype.card I := (Fintype.card_coe I).symm
    _ ≤ finrank Ω (LinearMap.range Φ) := hli.fintype_card_le_finrank
    _ ≤ finrank Ω (Fin (r - t) → Ω) := LinearMap.finrank_range_le Φ
    _ = r - t := Module.finrank_fin_fun Ω

/-- `2 ∑_{t < r} (r - t) = r (r + 1)`. -/
private theorem two_mul_sum_range_sub (r : ℕ) : 2 * ∑ t ∈ range r, (r - t) = r * (r + 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h : ∑ t ∈ range r, (r + 1 - t) = ∑ t ∈ range r, (r - t) + r := by
      calc ∑ t ∈ range r, (r + 1 - t) = ∑ t ∈ range r, ((r - t) + 1) :=
            sum_congr rfl fun t ht ↦ by have := mem_range.mp ht; omega
        _ = _ := by rw [sum_add_distrib, sum_const, card_range, smul_eq_mul, mul_one]
    rw [sum_range_succ, h, Nat.add_sub_cancel_left]
    nlinarith [ih]

/-- `(ab)^s ≤ a^k b^l` for `0 ≤ a ≤ b`, `k ≤ s` and `k + l = 2s`. -/
private theorem mul_pow_le_pow_mul_pow {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {s k l : ℕ}
    (hk : k ≤ s) (hkl : k + l = 2 * s) : (a * b) ^ s ≤ a ^ k * b ^ l := by
  obtain ⟨d, rfl⟩ : ∃ d, s = k + d := ⟨s - k, by omega⟩
  have hb : 0 ≤ b := ha.trans hab
  calc (a * b) ^ (k + d) = a ^ k * (a ^ d * b ^ (k + d)) := by ring
    _ ≤ a ^ k * (b ^ d * b ^ (k + d)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ ha hab d) (pow_nonneg hb _)) (pow_nonneg ha _)
    _ = a ^ k * b ^ l := by rw [show l = d + (k + d) by omega]; ring

open scoped Classical in
/-- **The counting argument of RT96 Prop. 5.3.** Let `P₁, …, P_{r+1}` be independent binary forms
of degree `r`, each a product of `r` linear forms `ℓ_{x_{ij}}`, and let `h ≥ 0` be any function
on points. Then there are two independent points `y₁, y₂` among the `x_{ij}` with
`h(y₁) ≤ h(y₂)` and `(h(y₁) h(y₂))^{r(r+1)/2} ≤ ∏ h(x_{ij})`: `y₁` of least `h`, which divides at
most `r(r+1)/2` of the factors, and `y₂` of least `h` among the factors not proportional to it. -/
theorem exists_linearIndependent_pair {κ : Type*} [Fintype κ] {r : ℕ} (hr : 0 < r)
    (hκ : Fintype.card κ = r + 1) {P : κ → Polynomial Ω}
    (hP : LinearIndependent Ω fun i ↦ coeffVec r (P i)) (c : κ → Ω) (x : κ → Fin r → Fin 2 → Ω)
    (hx : ∀ i j, x i j ≠ 0) (hPx : ∀ i, P i = C (c i) * ∏ j, binLinear (x i j))
    (h : (Fin 2 → Ω) → ℝ) (h0 : ∀ y, 0 ≤ h y) :
    ∃ y₁ y₂ : Fin 2 → Ω, LinearIndependent Ω ![y₁, y₂] ∧ h y₁ ≤ h y₂ ∧
      (h y₁ * h y₂) ^ (r * (r + 1) / 2) ≤ ∏ i, ∏ j, h (x i j) := by
  have : Nonempty κ := Fintype.card_pos_iff.mp (by omega)
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨p₁, -, hp₁⟩ := exists_min_image univ (fun p : κ × Fin r ↦ h (x p.1 p.2)) univ_nonempty
  set y₁ := x p₁.1 p₁.2
  set S : Finset (κ × Fin r) := {p | ∃ a : Ω, x p.1 p.2 = a • y₁}
  set m : κ → ℕ := fun i ↦ #{j | ∃ a : Ω, x i j = a • y₁}
  have hm : ∀ i, m i ≤ r := fun i ↦ (card_le_univ _).trans (by simp)
  have hS : #S = ∑ i, m i := by
    simp only [S, m, card_filter, Fintype.sum_prod_type]
  have hmt : ∀ i, m i = ∑ t ∈ range r, if t < m i then 1 else 0 := fun i ↦ by
    rw [sum_boole, Nat.cast_id]
    have : (range r).filter (· < m i) = range (m i) := by
      ext t
      simp only [mem_filter, mem_range]
      have := hm i
      omega
    rw [this, card_range]
  have h2S : 2 * #S ≤ r * (r + 1) := by
    rw [← two_mul_sum_range_sub r, hS]
    refine Nat.mul_le_mul_left 2 ?_
    calc ∑ i, m i = ∑ i, ∑ t ∈ range r, if t < m i then 1 else 0 := sum_congr rfl fun i _ ↦ hmt i
      _ = ∑ t ∈ range r, #{i | t < m i} := by
        rw [sum_comm]
        exact sum_congr rfl fun t _ ↦ by rw [card_filter]
      _ ≤ _ := sum_le_sum fun t ht ↦
        card_filter_lt_card_le hP c x hPx y₁ (mem_range.mp ht)
  have hcardS : #S + #Sᶜ = (r + 1) * r := by
    rw [card_add_card_compl, Fintype.card_prod, hκ, Fintype.card_fin]
  have hSc : Sᶜ.Nonempty := by
    rw [← card_pos]
    nlinarith
  obtain ⟨p₂, hp₂S, hp₂⟩ := exists_min_image _ (fun p : κ × Fin r ↦ h (x p.1 p.2)) hSc
  set y₂ := x p₂.1 p₂.2
  have hp₂S' : ¬ ∃ a : Ω, y₂ = a • y₁ := by
    have := mem_compl.mp hp₂S
    simpa [S] using this
  refine ⟨y₁, y₂, LinearIndependent.pair_iff.mpr fun s t hst ↦ ?_, hp₁ p₂ (mem_univ _), ?_⟩
  · by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero, smul_eq_zero] at hst
      exact ⟨hst.resolve_right (hx _ _), rfl⟩
    · refine absurd ⟨-(t⁻¹ * s), ?_⟩ hp₂S'
      have h' : t • y₂ = -(s • y₁) := eq_neg_of_add_eq_zero_right hst
      calc y₂ = t⁻¹ • (t • y₂) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        _ = -(t⁻¹ * s) • y₁ := by rw [h', smul_neg, smul_smul, neg_smul]
  · have hle : ∀ p : κ × Fin r, (if p ∈ S then h y₁ else h y₂) ≤ h (x p.1 p.2) := fun p ↦ by
      split_ifs with hp
      · exact hp₁ p (mem_univ _)
      · exact hp₂ p (mem_compl.mpr hp)
    have hs2 : 2 * (r * (r + 1) / 2) = r * (r + 1) :=
      Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self r)
    calc (h y₁ * h y₂) ^ (r * (r + 1) / 2)
        ≤ h y₁ ^ #S * h y₂ ^ #Sᶜ :=
          mul_pow_le_pow_mul_pow (h0 _) (hp₁ p₂ (mem_univ _)) (by omega)
            (by rw [hcardS, hs2, Nat.mul_comm])
      _ = ∏ p : κ × Fin r, if p ∈ S then h y₁ else h y₂ := by
          rw [prod_ite, prod_const, prod_const]
          congr 3 <;> ext p <;> simp
      _ ≤ ∏ p : κ × Fin r, h (x p.1 p.2) :=
          prod_le_prod₀ (fun p _ ↦ by split_ifs <;> exact h0 _) fun p _ ↦ hle p
      _ = ∏ i, ∏ j, h (x i j) := Fintype.prod_prod_type _

end Polynomial

namespace NumberField.Twist

open Module

variable {K : Type*} [Field K] [NumberField K] (A : Twist K (Fin 2))
  (Ω : Type*) [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω]

/-- The constant of RT96 Prop. 5.3 for a given `r`:
`((√2^r · |D_K|^{1/(2d)} · √(r+1))^{r+1})^{2/(r(r+1))}`, which tends to `2` as `r → ∞`. -/
noncomputable def planeConst (r : ℕ) : ℝ :=
  ((√2 ^ r * (√|(discr K : ℝ)| ^ ((finrank ℚ K : ℝ))⁻¹ * √((r : ℝ) + 1))) ^ (r + 1)) ^
    (((r * (r + 1) / 2 : ℕ) : ℝ))⁻¹

/-- **RT96 Prop. 5.3 for a given `r`**: `μ₁(A) μ₂(A) ≤ c_r · |det A|_𝔸` with
`c_r = planeConst K r`. -/
theorem absMinimum_one_mul_absMinimum_two_le {r : ℕ} (hr : 0 < r) :
    A.absMinimum Ω 1 * A.absMinimum Ω 2 ≤ planeConst (K := K) r * A.absDet := by
  set s := r * (r + 1) / 2 with hs_def
  have hs : 0 < s := Nat.div_pos (by nlinarith) two_pos
  obtain ⟨α, hα, hαH⟩ := (A.symPow r).exists_linearIndependent_prod_absMulHeight_le Ω
  simp only [Fintype.card_fin, absDet_symPow] at hαH
  set P : Fin (Fintype.card (Fin (r + 1))) → Polynomial Ω :=
    fun i ↦ ∑ k : Fin (r + 1), C (algebraMap K Ω (α i k)) * X ^ (k : ℕ)
  have hcoeff : ∀ i, coeffVec r (P i) = algebraMap K Ω ∘ α i := fun i ↦ by
    ext k
    simp only [P, coeffVec, finsetSum_coeff, coeff_C_mul_X_pow, Function.comp_apply,
      Fin.val_inj]
    rw [sum_ite_eq]
    simp
  have hP : LinearIndependent Ω fun i ↦ coeffVec r (P i) := by
    simp_rw [hcoeff]
    exact linearIndependent_algebraMap_comp_iff.mpr hα
  have hP0 : ∀ i, P i ≠ 0 := fun i h ↦ hP.ne_zero i (by
    rw [h]
    rfl)
  have hPd : ∀ i, (P i).natDegree ≤ r := fun i ↦
    natDegree_sum_le_of_forall_le _ _ fun k _ ↦ (natDegree_C_mul_X_pow_le _ _).trans
      (Nat.lt_succ_iff.mp k.2)
  choose c hc x hx hPx using fun i ↦ exists_eq_C_mul_prod_binLinear (hP0 i) (hPd i)
  have hH : ∀ i, (A.symPow r).absMulHeight (algebraMap K Ω ∘ α i) =
      (A.symPow r).absMulHeight (coeffVec r (∏ j, binLinear (x i j))) := fun i ↦ by
    rw [← hcoeff, hPx, coeffVec_C_mul, absMulHeight_smul _ _ (hc i)]
  obtain ⟨y₁, y₂, hy, h12, hprod⟩ := exists_linearIndependent_pair hr (by simp) hP c x hx hPx
    A.absMulHeight A.absMulHeight_nonneg
  set B := √2 ^ r * (√|(discr K : ℝ)| ^ ((finrank ℚ K : ℝ))⁻¹ * √((r : ℝ) + 1))
  have hB : 0 ≤ B := by positivity
  -- the product of all the heights
  have hall : (A.absMulHeight y₁ * A.absMulHeight y₂) ^ s ≤ B ^ (r + 1) * A.absDet ^ s := by
    refine hprod.trans ?_
    calc ∏ i, ∏ j, A.absMulHeight (x i j)
        ≤ ∏ i, (√2 ^ r * (A.symPow r).absMulHeight (algebraMap K Ω ∘ α i)) :=
          prod_le_prod₀ (fun i _ ↦ prod_nonneg fun j _ ↦ A.absMulHeight_nonneg _)
            fun i _ ↦ (hH i).symm ▸ A.prod_absMulHeight_le (hx i)
      _ = (√2 ^ r) ^ (r + 1) * ∏ i, (A.symPow r).absMulHeight (algebraMap K Ω ∘ α i) := by
          rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
          congr 2
          exact Fintype.card_fin _
      _ ≤ (√2 ^ r) ^ (r + 1) * ((√|(discr K : ℝ)| ^ ((finrank ℚ K : ℝ))⁻¹ *
            √((r + 1 : ℕ) : ℝ)) ^ (r + 1) * A.absDet ^ s) :=
          mul_le_mul_of_nonneg_left hαH (by positivity)
      _ = B ^ (r + 1) * A.absDet ^ s := by
          simp only [B, mul_pow, Nat.cast_add, Nat.cast_one]
          ring
  -- the two minima
  have hy₁ : y₁ ≠ 0 := by simpa using hy.ne_zero 0
  have hμ₁ : A.absMinimum Ω 1 ≤ A.absMulHeight y₁ := A.absMinimum_one_le hy₁
  have hμ₂ : A.absMinimum Ω 2 ≤ A.absMulHeight y₂ := A.absMinimum_le two_pos hy fun j ↦ by
    fin_cases j
    · exact h12
    · exact le_rfl
  have hμ₁0 : 0 ≤ A.absMinimum Ω 1 := (A.absMinimum_pos one_pos (by simp)).le
  have hH0 : 0 ≤ A.absMulHeight y₁ * A.absMulHeight y₂ :=
    mul_nonneg (A.absMulHeight_nonneg _) (A.absMulHeight_nonneg _)
  have hs' : s ≠ 0 := hs.ne'
  calc A.absMinimum Ω 1 * A.absMinimum Ω 2 ≤ A.absMulHeight y₁ * A.absMulHeight y₂ :=
        mul_le_mul hμ₁ hμ₂ (A.absMinimum_pos two_pos (by simp)).le (A.absMulHeight_nonneg _)
    _ = ((A.absMulHeight y₁ * A.absMulHeight y₂) ^ s) ^ ((s : ℝ))⁻¹ :=
        (Real.pow_rpow_inv_natCast hH0 hs').symm
    _ ≤ (B ^ (r + 1) * A.absDet ^ s) ^ ((s : ℝ))⁻¹ :=
        Real.rpow_le_rpow (pow_nonneg hH0 _) hall (by positivity)
    _ = planeConst (K := K) r * A.absDet := by
        rw [Real.mul_rpow (by positivity) (pow_nonneg A.absDet_pos.le _),
          Real.pow_rpow_inv_natCast A.absDet_pos.le hs']
        rfl

private theorem log_planeConst {r : ℕ} (hr : 0 < r) :
    planeConst (K := K) r = Real.exp (Real.log 2 +
      (2 * Real.log (√|(discr K : ℝ)| ^ ((finrank ℚ K : ℝ))⁻¹) + Real.log ((r : ℝ) + 1)) / r) := by
  set a := √|(discr K : ℝ)| ^ ((finrank ℚ K : ℝ))⁻¹
  have ha : 0 < a := Real.rpow_pos_of_pos (Real.sqrt_pos.mpr (abs_pos.mpr (by
    exact_mod_cast discr_ne_zero K))) _
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hB : 0 < √2 ^ r * (a * √((r : ℝ) + 1)) := by positivity
  have hs : (((r * (r + 1) / 2 : ℕ) : ℝ)) = r * (r + 1) / 2 := by
    rw [Nat.cast_div (Nat.even_mul_succ_self r).two_dvd two_ne_zero]
    push_cast
    ring
  rw [planeConst, ← Real.exp_log (Real.rpow_pos_of_pos (pow_pos hB _) _), Real.log_rpow
    (pow_pos hB _), Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_mul ha.ne' (by positivity), Real.log_sqrt zero_le_two,
    Real.log_sqrt (by positivity), hs]
  congr 1
  field_simp
  push_cast
  ring

/-- **The constant of RT96 Prop. 5.3 tends to `2`.** -/
theorem tendsto_planeConst : Filter.Tendsto (planeConst (K := K)) Filter.atTop (nhds 2) := by
  set a := √|(discr K : ℝ)| ^ ((finrank ℚ K : ℝ))⁻¹
  have hinv : Filter.Tendsto (fun r : ℕ ↦ ((r : ℝ))⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlog : Filter.Tendsto (fun r : ℕ ↦ Real.log ((r : ℝ) + 1) / r) Filter.atTop (nhds 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
      (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    refine this.congr fun r ↦ ?_
    simp
  have hlim : Filter.Tendsto (fun r : ℕ ↦ Real.exp (Real.log 2 +
      (2 * Real.log a + Real.log ((r : ℝ) + 1)) / r)) Filter.atTop (nhds 2) := by
    have h := (Real.continuous_exp.tendsto _).comp ((tendsto_const_nhds (x := Real.log 2)).add
      ((hinv.const_mul (2 * Real.log a)).add hlog))
    rw [mul_zero, add_zero, add_zero, Real.exp_log two_pos] at h
    refine h.congr fun r ↦ ?_
    simp only [Function.comp_apply, div_eq_mul_inv]
    ring_nf
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with r hr
  exact (log_planeConst hr).symm

/-- **The absolute Minkowski theorem in the plane** (RT96 Prop. 5.3, with RT's constant):
`μ₁(A) μ₂(A) ≤ 2 |det A|_𝔸` for every twist `A` of the plane over a number field `K`, the
absolute minima taken over an algebraically closed `Ω`. The constant is absolute: the
discriminant of `K`, which enters each `planeConst K r`, disappears as `r → ∞`. -/
theorem absMinimum_one_mul_absMinimum_two_le_two_mul :
    A.absMinimum Ω 1 * A.absMinimum Ω 2 ≤ 2 * A.absDet := by
  refine ge_of_tendsto ((tendsto_planeConst (K := K)).mul_const A.absDet) ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with r hr
  exact A.absMinimum_one_mul_absMinimum_two_le Ω hr

end NumberField.Twist
