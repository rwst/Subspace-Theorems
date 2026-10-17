/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Group.Embedding
public import Mathlib.Data.Fintype.BigOperators

-- Used only inside proofs.
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Lattice points in a simplex

The points `e : Fin t → ℕ` with `∑ e ≤ M` (`Finset.simplexPoints t M`) number `C(M + t, t)`
(`Finset.card_simplexPoints`), and each coordinate sums over them to `C(M + t, t + 1)`
(`Finset.sum_simplexPoints_apply`). Both by the bijection `e ↦ e + e_j` from the points of
`∑ e ≤ M` onto those of `∑ e ≤ M + 1` with `e_j ≠ 0`.

The application is the count of Corvaja–Zannier, *On a general Thue's equation*, Amer. J. Math.
126 (2004), §3. A family labelled by exponents `ℓ x : Fin t → ℕ` with `δ σ(ℓ x) ≤ N`, at most `D`
members of each label and exactly `D` of each label `i` with `δ σ(i) + N₀ ≤ N`, has
`d ≤ D C(⌊N/δ⌋ + t, t)` members (`Finset.card_le_mul_choose`) and label sums
`A_j = ∑_x ℓ x j ≥ D C(⌊(N - N₀)/δ⌋ + t, t + 1)` (`Finset.mul_choose_le_sum_apply`). For
`θ < -δ (t + 1)` and every large `N` this gives `d N + θ A_j < 0`
(`Finset.exists_forall_card_mul_add_mul_sum_lt_zero`), with an explicit threshold: the ratio
`C(M + t, t) / C(M' + t, t)` is at most `((M + 1)/(M' + 1))^t`, and Bernoulli's inequality does
the rest.
-/

@[expose] public section

open Finset

namespace Finset

/-- The lattice points `e : Fin t → ℕ` with `∑ e ≤ M`. -/
def simplexPoints (t M : ℕ) : Finset (Fin t → ℕ) :=
  (Fintype.piFinset fun _ : Fin t ↦ range (M + 1)).filter fun e ↦ ∑ j, e j ≤ M

variable {t M : ℕ}

@[simp]
theorem mem_simplexPoints {e : Fin t → ℕ} : e ∈ simplexPoints t M ↔ ∑ j, e j ≤ M := by
  simp only [simplexPoints, mem_filter, Fintype.mem_piFinset, mem_range, and_iff_right_iff_imp]
  intro h j
  have := single_le_sum (f := e) (fun _ _ ↦ Nat.zero_le _) (mem_univ j)
  omega

theorem apply_le_of_mem_simplexPoints {e : Fin t → ℕ} (he : e ∈ simplexPoints t M) (j : Fin t) :
    e j ≤ M :=
  (single_le_sum (f := e) (fun _ _ ↦ Nat.zero_le _) (mem_univ j)).trans (mem_simplexPoints.mp he)

theorem simplexPoints_zero_eq : simplexPoints t 0 = {0} := by
  ext e
  simp only [mem_simplexPoints, Nat.le_zero, sum_eq_zero_iff, mem_univ, true_implies,
    mem_singleton]
  exact ⟨fun h ↦ funext h, fun h j ↦ by simp [h]⟩

/-- The shift `e ↦ e + e_j` maps the points of `∑ e ≤ M` onto those of `∑ e ≤ M + 1` with
`e j ≠ 0`. -/
theorem filter_simplexPoints_succ (j : Fin t) :
    (simplexPoints t (M + 1)).filter (· j ≠ 0) =
      (simplexPoints t M).map (addLeftEmbedding (Pi.single j 1)) := by
  classical
  have hsum : ∀ e : Fin t → ℕ, ∑ k, ((Pi.single j 1 : Fin t → ℕ) + e) k = 1 + ∑ k, e k :=
    fun e ↦ by simp [sum_add_distrib]
  ext e
  simp only [mem_filter, mem_simplexPoints, mem_map, addLeftEmbedding_apply]
  constructor
  · rintro ⟨he, hj⟩
    have hdec : Pi.single j 1 + (e - Pi.single j 1) = e := by
      funext k
      by_cases hk : k = j
      · subst hk; simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same]; omega
      · simp [hk]
    refine ⟨e - Pi.single j 1, ?_, hdec⟩
    have := hsum (e - Pi.single j 1)
    rw [hdec] at this
    omega
  · rintro ⟨a, ha, rfl⟩
    refine ⟨by rw [hsum]; omega, by simp⟩

theorem card_simplexPoints (t M : ℕ) : #(simplexPoints t M) = (M + t).choose t := by
  classical
  induction t generalizing M with
  | zero => simp [simplexPoints]
  | succ t iht =>
  induction M with
  | zero => simp [simplexPoints_zero_eq]
  | succ M ihM =>
  rw [← card_filter_add_card_filter_not (fun e : Fin (t + 1) → ℕ ↦ e 0 ≠ 0),
    filter_simplexPoints_succ, card_map, ihM]
  have h0 : #((simplexPoints (t + 1) (M + 1)).filter fun e ↦ ¬ e 0 ≠ 0) =
      #(simplexPoints t (M + 1)) := by
    refine card_nbij' Fin.tail (fun e ↦ Fin.cons (0 : ℕ) e) ?_ ?_ ?_ ?_
    · intro e he
      simp only [mem_coe, mem_filter, mem_simplexPoints, not_not] at he ⊢
      rw [Fin.sum_univ_succ, he.2, zero_add] at he
      exact he.1
    · intro e he
      simp only [mem_coe, mem_filter, mem_simplexPoints, not_not] at he ⊢
      simpa [Fin.sum_cons] using he
    · intro e he
      simp only [mem_coe, mem_filter, mem_simplexPoints, not_not] at he
      rw [← he.2]
      exact Fin.cons_self_tail e
    · intro e _
      exact Fin.tail_cons _ _
  rw [h0, iht, show M + 1 + (t + 1) = (M + (t + 1)) + 1 by omega, Nat.choose_succ_succ',
    show M + (t + 1) = M + 1 + t by omega, add_comm]

/-- Each coordinate sums over the points of `∑ e ≤ M` to `C(M + t, t + 1)`. -/
theorem sum_simplexPoints_apply (j : Fin t) :
    ∑ e ∈ simplexPoints t M, e j = (M + t).choose (t + 1) := by
  classical
  induction M with
  | zero => simp [simplexPoints_zero_eq]
  | succ M ih =>
  rw [← sum_filter_ne_zero, filter_simplexPoints_succ j, sum_map]
  simp only [addLeftEmbedding_apply, Pi.add_apply, Pi.single_eq_same]
  rw [sum_add_distrib, ih, sum_const, card_simplexPoints, smul_eq_mul, mul_one,
    show M + 1 + t = (M + t) + 1 by omega, Nat.choose_succ_succ']

/-- The ratio of two simplex counts: `C(M + t, t) (M' + 1)^t ≤ C(M' + t, t) (M + 1)^t` for
`M' ≤ M`. -/
theorem choose_mul_pow_le {M M' : ℕ} (h : M' ≤ M) (t : ℕ) :
    (M + t).choose t * (M' + 1) ^ t ≤ (M' + t).choose t * (M + 1) ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.succ_pos t)
  have e1 := Nat.add_one_mul_choose_eq (M + t) t
  have e2 := Nat.add_one_mul_choose_eq (M' + t) t
  rw [show M + (t + 1) = M + t + 1 by omega, show M' + (t + 1) = M' + t + 1 by omega]
  have key : (M + t + 1) * (M' + 1) ≤ (M' + t + 1) * (M + 1) := by nlinarith
  calc (M + t + 1).choose (t + 1) * (M' + 1) ^ (t + 1) * (t + 1)
      = (M + t + 1) * (M' + 1) * ((M + t).choose t * (M' + 1) ^ t) := by
        rw [show (M + t + 1) * (M' + 1) * ((M + t).choose t * (M' + 1) ^ t) =
          (M' + 1) ^ t * (M' + 1) * ((M + t + 1) * (M + t).choose t) by ring, e1, pow_succ]
        ring
    _ ≤ (M' + t + 1) * (M + 1) * ((M' + t).choose t * (M + 1) ^ t) :=
        Nat.mul_le_mul key ih
    _ = (M' + t + 1).choose (t + 1) * (M + 1) ^ (t + 1) * (t + 1) := by
        rw [show (M' + t + 1) * (M + 1) * ((M' + t).choose t * (M + 1) ^ t) =
          (M + 1) ^ t * (M + 1) * ((M' + t + 1) * (M' + t).choose t) by ring, e2, pow_succ]
        ring

section Count

variable {ι : Type*} [Fintype ι] [DecidableEq (Fin t → ℕ)] {ℓ : ι → Fin t → ℕ} {δ N D N₀ : ℕ}

/-- At most `D` members of each label `i` with `δ σ(i) ≤ N`: at most `D C(⌊N/δ⌋ + t, t)`
members. -/
theorem card_le_mul_choose (hδ : 0 < δ) (hℓ : ∀ x, δ * ∑ j, ℓ x j ≤ N)
    (hD : ∀ i, #(univ.filter (ℓ · = i)) ≤ D) :
    Fintype.card ι ≤ D * (N / δ + t).choose t := by
  have hmaps : ∀ x ∈ (univ : Finset ι), ℓ x ∈ simplexPoints t (N / δ) := fun x _ ↦
    mem_simplexPoints.mpr ((Nat.le_div_iff_mul_le hδ).mpr (by rw [mul_comm]; exact hℓ x))
  rw [← card_univ, card_eq_sum_card_fiberwise hmaps, ← card_simplexPoints, mul_comm]
  exact sum_le_card_nsmul _ _ _ fun i _ ↦ hD i

/-- Exactly `D` members of each label `i` with `δ σ(i) + N₀ ≤ N`: the label sums are at least
`D C(⌊(N - N₀)/δ⌋ + t, t + 1)`. -/
theorem mul_choose_le_sum_apply (hδ : 0 < δ) (hℓ : ∀ x, δ * ∑ j, ℓ x j ≤ N)
    (hD : ∀ i, δ * ∑ j, i j + N₀ ≤ N → #(univ.filter (ℓ · = i)) = D) (j : Fin t) :
    D * ((N - N₀) / δ + t).choose (t + 1) ≤ ∑ x, ℓ x j := by
  have hmaps : ∀ x ∈ (univ : Finset ι), ℓ x ∈ simplexPoints t (N / δ) := fun x _ ↦
    mem_simplexPoints.mpr ((Nat.le_div_iff_mul_le hδ).mpr (by rw [mul_comm]; exact hℓ x))
  rw [← sum_fiberwise_of_maps_to hmaps]
  have hsub : simplexPoints t ((N - N₀) / δ) ⊆ simplexPoints t (N / δ) := fun e he ↦
    mem_simplexPoints.mpr ((mem_simplexPoints.mp he).trans
      (Nat.div_le_div_right (Nat.sub_le N N₀)))
  rcases le_or_gt N₀ N with hN | hN
  · rw [← sum_simplexPoints_apply (M := (N - N₀) / δ) j, mul_sum]
    refine (sum_le_sum fun i hi ↦ ?_).trans (sum_le_sum_of_subset hsub)
    have hi' : δ * ∑ j, i j + N₀ ≤ N := by
      have := (Nat.le_div_iff_mul_le hδ).mp (mem_simplexPoints.mp hi)
      rw [mul_comm] at this
      omega
    rw [sum_congr rfl fun x hx ↦ by rw [(mem_filter.mp hx).2], sum_const, smul_eq_mul,
      hD i hi']
  · rw [Nat.sub_eq_zero_of_le hN.le, Nat.zero_div, zero_add,
      Nat.choose_eq_zero_of_lt (Nat.lt_succ_self t), mul_zero]
    exact Nat.zero_le _

/-- Exactly `D` members of each label `i` with `δ σ(i) + N₀ ≤ N`: at least
`D C(⌊(N - N₀)/δ⌋ + t, t)` members. -/
theorem mul_choose_le_card (hδ : 0 < δ) (hN : N₀ ≤ N) (hℓ : ∀ x, δ * ∑ j, ℓ x j ≤ N)
    (hD : ∀ i, δ * ∑ j, i j + N₀ ≤ N → #(univ.filter (ℓ · = i)) = D) :
    D * ((N - N₀) / δ + t).choose t ≤ Fintype.card ι := by
  have hmaps : ∀ x ∈ (univ : Finset ι), ℓ x ∈ simplexPoints t (N / δ) := fun x _ ↦
    mem_simplexPoints.mpr ((Nat.le_div_iff_mul_le hδ).mpr (by rw [mul_comm]; exact hℓ x))
  have hsub : simplexPoints t ((N - N₀) / δ) ⊆ simplexPoints t (N / δ) := fun e he ↦
    mem_simplexPoints.mpr ((mem_simplexPoints.mp he).trans
      (Nat.div_le_div_right (Nat.sub_le N N₀)))
  rw [← card_univ, card_eq_sum_card_fiberwise hmaps, ← card_simplexPoints, mul_comm,
    ← smul_eq_mul, ← sum_const]
  refine (sum_le_sum fun i hi ↦ ?_).trans (sum_le_sum_of_subset hsub)
  have := (Nat.le_div_iff_mul_le hδ).mp (mem_simplexPoints.mp hi)
  rw [mul_comm] at this
  exact (hD i (by omega)).ge

end Count

/-- Bernoulli's inequality in the form used for the choice of `N`: `u^n ≤ a (u - c)^n` once
`a n c ≤ (a - 1) u`. -/
theorem _root_.Real.pow_le_mul_sub_pow {a u c : ℝ} (n : ℕ) (ha : 1 < a) (hc : 0 ≤ c)
    (hcu : c ≤ u) (hu : a * n * c ≤ (a - 1) * u) : u ^ n ≤ a * (u - c) ^ n := by
  rcases hcu.lt_or_eq with hlt | rfl
  · have hu0 : 0 < u := hc.trans_lt hlt
    have hb := one_add_mul_le_pow (a := -(c / u)) (by
      have : c / u ≤ 1 := (div_le_one hu0).mpr hlt.le
      linarith) n
    have hfac : (u - c) ^ n = u ^ n * (1 + -(c / u)) ^ n := by
      rw [← mul_pow]; congr 1; field_simp; ring
    have hkey : a * u ^ n * (1 + n * -(c / u)) - u ^ n = u ^ n / u * ((a - 1) * u - a * n * c) := by
      field_simp; ring
    have hnn : 0 ≤ u ^ n / u * ((a - 1) * u - a * n * c) :=
      mul_nonneg (div_nonneg (pow_nonneg hu0.le n) hu0.le) (by linarith)
    rw [hfac]
    nlinarith [mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ a * u ^ n)]
  · rw [sub_self]
    rcases n with _ | n
    · simp only [pow_zero, mul_one]; exact ha.le
    · have hc0 : c = 0 := by
        push_cast at hu
        nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ a) (Nat.cast_nonneg n)) hc]
      subst hc0; simp

/-- **The choice of `N`, numerically** (Corvaja–Zannier 2004, §3). For `θ < -δ (t + 1)` there is
`N₁` with `C(⌊N/δ⌋ + t, t) N + θ C(⌊(N - N₀)/δ⌋ + t, t + 1) < 0` for every `N ≥ N₁`; explicitly
`N₁ = δ ⌈a (t + 1)(N₀ + 1)/(a - 1)⌉` with `-θ = a δ (t + 1)`. -/
theorem exists_forall_choose_mul_add_mul_choose_lt_zero {t δ N₀ : ℕ} (hδ : 0 < δ) {θ : ℝ}
    (hθ : θ < -(δ * (t + 1) : ℝ)) :
    ∃ N₁ : ℕ, ∀ N ≥ N₁, ((N / δ + t).choose t : ℝ) * N +
      θ * ((N - N₀) / δ + t).choose (t + 1) < 0 := by
  have hδt : (0 : ℝ) < δ * (t + 1) := by positivity
  set a : ℝ := -θ / (δ * (t + 1)) with ha_def
  have ha : 1 < a := (one_lt_div hδt).mpr (by linarith)
  have hθa : θ = -(a * δ * (t + 1)) := by rw [ha_def]; field_simp
  set K : ℕ := ⌈a * (t + 1) * (N₀ + 1) / (a - 1)⌉₊
  have hK : a * (t + 1) * (N₀ + 1) / (a - 1) ≤ K := Nat.le_ceil _
  have hK1 : ((N₀ + 1 : ℕ) : ℝ) ≤ K := by
    refine le_trans ?_ hK
    rw [le_div_iff₀ (by linarith)]
    push_cast
    have : (0 : ℝ) ≤ a * t * (N₀ + 1) := by positivity
    nlinarith
  have hK1' : N₀ + 1 ≤ K := by exact_mod_cast hK1
  refine ⟨δ * K, fun N hN ↦ ?_⟩
  set M := N / δ
  set M' := (N - N₀) / δ
  have hMK : K ≤ M := (Nat.le_div_iff_mul_le hδ).mpr (by rw [mul_comm]; exact hN)
  have hMM' : M - N₀ ≤ M' := by
    refine (Nat.le_div_iff_mul_le hδ).mpr ?_
    have h1 : M * δ ≤ N := Nat.div_mul_le_self N δ
    have h2 : N₀ ≤ N₀ * δ := Nat.le_mul_of_pos_right N₀ hδ
    rw [Nat.sub_mul]
    omega
  have hM'M : M' ≤ M := Nat.div_le_div_right (Nat.sub_le N N₀)
  have hNlt : (N : ℝ) < δ * (M + 1) := by
    have h : N < M * δ + δ := Nat.lt_div_mul_add hδ
    have : N < δ * (M + 1) := by rw [mul_add, mul_one, mul_comm]; exact h
    exact_mod_cast this
  set P := (M + t).choose t
  set P' := (M' + t).choose t
  set Q' := (M' + t).choose (t + 1)
  have hQ' : (Q' : ℝ) * (t + 1) = P' * M' := by
    have := Nat.choose_succ_right_eq (M' + t) t
    rw [Nat.add_sub_cancel] at this
    exact_mod_cast this
  have hP : (0 : ℝ) < P := by exact_mod_cast Nat.choose_pos (Nat.le_add_left t M)
  have hratio : (P : ℝ) * (M' + 1) ^ t ≤ P' * (M + 1) ^ t := by
    exact_mod_cast choose_mul_pow_le hM'M t
  -- Bernoulli: `(M + 1)^(t + 1) ≤ a M'^(t + 1)`.
  have hbern : ((M : ℝ) + 1) ^ (t + 1) ≤ a * M' ^ (t + 1) := by
    have hN₀M : N₀ ≤ M := by omega
    have hcast : ((M : ℝ) + 1) - (N₀ + 1) ≤ M' := by
      have : ((M - N₀ : ℕ) : ℝ) ≤ M' := by exact_mod_cast hMM'
      rw [Nat.cast_sub hN₀M] at this
      linarith
    refine (Real.pow_le_mul_sub_pow (u := (M : ℝ) + 1) (c := (N₀ : ℝ) + 1) (t + 1) ha
      (by positivity) ?_ ?_).trans ?_
    · have : (N₀ : ℝ) ≤ M := by exact_mod_cast hN₀M
      linarith
    · have hKM : (K : ℝ) ≤ M := by exact_mod_cast hMK
      have := (div_le_iff₀ (by linarith : (0 : ℝ) < a - 1)).mp (hK.trans hKM)
      push_cast
      nlinarith
    · refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ hcast _) (by linarith)
      have : (N₀ : ℝ) ≤ M := by exact_mod_cast hN₀M
      linarith
  have hM'0 : (0 : ℝ) ≤ M' := Nat.cast_nonneg _
  have hpow : (0 : ℝ) < ((M' : ℝ) + 1) ^ t := by positivity
  -- `P N < a δ M' P'`.
  have hmain : (P : ℝ) * N < a * δ * M' * P' := by
    have h1 : (P : ℝ) * N * (M' + 1) ^ t < δ * P' * (M + 1) ^ (t + 1) := by
      calc (P : ℝ) * N * (M' + 1) ^ t < P * (δ * (M + 1)) * (M' + 1) ^ t := by gcongr
        _ = δ * (M + 1) * (P * (M' + 1) ^ t) := by ring
        _ ≤ δ * (M + 1) * (P' * (M + 1) ^ t) := by gcongr
        _ = δ * P' * (M + 1) ^ (t + 1) := by ring
    have h2 : (δ : ℝ) * P' * (M + 1) ^ (t + 1) ≤ a * δ * M' * P' * (M' + 1) ^ t := by
      have hM'pow : (M' : ℝ) ^ (t + 1) ≤ M' * (M' + 1) ^ t := by
        rw [pow_succ']
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hM'0 (by linarith) t) hM'0
      have : (δ : ℝ) * P' * (M + 1) ^ (t + 1) ≤ δ * P' * (a * (M' * (M' + 1) ^ t)) := by
        gcongr
        exact hbern.trans (mul_le_mul_of_nonneg_left hM'pow (by linarith))
      linarith
    exact lt_of_mul_lt_mul_right (h1.trans_le h2) hpow.le
  calc (P : ℝ) * N + θ * Q' = P * N - a * δ * (Q' * (t + 1)) := by rw [hθa]; ring
    _ = P * N - a * δ * M' * P' := by rw [hQ']; ring
    _ < 0 := by linarith

/-- **The choice of `N`** (Corvaja–Zannier 2004, §3, with Finding 4 of the paper's README). For
`θ < -δ (t + 1)` there is `N₁` such that for every `N ≥ N₁` and every family labelled by
exponents `ℓ x` with `δ σ(ℓ x) ≤ N`, at most `D > 0` members of each label and exactly `D` of each
label `i` with `δ σ(i) + N₀ ≤ N`: `d N + θ A_j < 0` for `d` the number of members and
`A_j = ∑_x ℓ x j`. -/
theorem exists_forall_card_mul_add_mul_sum_lt_zero {t δ D N₀ : ℕ} [DecidableEq (Fin t → ℕ)]
    (hδ : 0 < δ) (hD : 0 < D) {θ : ℝ} (hθ : θ < -(δ * (t + 1) : ℝ)) :
    ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ (ι : Type) [Fintype ι] (ℓ : ι → Fin t → ℕ),
      (∀ x, δ * ∑ j, ℓ x j ≤ N) → (∀ i, #(univ.filter (ℓ · = i)) ≤ D) →
      (∀ i, δ * ∑ j, i j + N₀ ≤ N → #(univ.filter (ℓ · = i)) = D) →
      ∀ j, (Fintype.card ι : ℝ) * N + θ * ∑ x, (ℓ x j : ℝ) < 0 := by
  obtain ⟨N₁, hN₁⟩ := exists_forall_choose_mul_add_mul_choose_lt_zero (N₀ := N₀) hδ hθ
  refine ⟨N₁, fun N hN ι _ ℓ hℓ hcnt heq j ↦ ?_⟩
  have hd' : (Fintype.card ι : ℝ) ≤ D * (N / δ + t).choose t := by
    exact_mod_cast card_le_mul_choose hδ hℓ hcnt
  have hA' : (D : ℝ) * ((N - N₀) / δ + t).choose (t + 1) ≤ ∑ x, (ℓ x j : ℝ) := by
    exact_mod_cast mul_choose_le_sum_apply hδ hℓ heq j
  have hθ0 : θ ≤ 0 := by linarith [(by positivity : (0 : ℝ) ≤ δ * (t + 1))]
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  calc (Fintype.card ι : ℝ) * N + θ * ∑ x, (ℓ x j : ℝ)
      ≤ D * (N / δ + t).choose t * N + θ * (D * ((N - N₀) / δ + t).choose (t + 1)) := by
        gcongr ?_ + ?_
        · exact mul_le_mul_of_nonneg_right hd' (Nat.cast_nonneg _)
        · exact mul_le_mul_of_nonpos_left hA' hθ0
    _ = D * (((N / δ + t).choose t : ℝ) * N + θ * ((N - N₀) / δ + t).choose (t + 1)) := by ring
    _ < 0 := mul_neg_of_pos_of_neg hD' (hN₁ N hN)

end Finset
