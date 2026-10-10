/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Bugeaud2013.Estimates

-- Used only inside proofs.
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Lagrange's theorem for `[0; a₁, a₂, …]`

A continued fraction `α = [0; a₁, a₂, …]` that is a root of a non-zero rational polynomial of
degree at most `2` has an eventually periodic sequence of partial quotients (Lagrange). With
Euler's converse (`Nat.exists_quadratic_of_isEventuallyPeriodic`) this is the classical
characterization; Bugeaud's Theorem 3.1 needs this direction, since its proof only shows that `α`
is transcendental *or quadratic*.

The proof is the classical one. The tail `α_k = [0; a_{k+1}, a_{k+2}, …]` satisfies
`α = (p_k + p_{k-1} α_k) / (q_k + q_{k-1} α_k)` (`Nat.contFrac_eq_of_tail`), so if `f(α) = 0` for
`f = A X² + B X + C` over `ℤ`, then `α_k` is a root of `F_k = A_k X² + B_k X + C_k` with
`A_k = q_{k-1}² f(p_{k-1} / q_{k-1}) ≠ 0` and, by (2.2), `|A_k|, |B_k|, |C_k| ≤ 2 (3 |A| + |B|)`.
So the tails take finitely many values, two of them coincide, and since `α` determines its partial
quotients (`Nat.contFrac_injective`), the sequence is periodic from there on.

## Main results

* `Nat.contFrac_injective`: `[0; a₁, a₂, …] = [0; b₁, b₂, …]` implies `a_i = b_i` for `i ≥ 1`.
* `Nat.isEventuallyPeriodic_of_quadratic`: **Lagrange's theorem**.
-/

@[expose] public section

open Filter

namespace Nat

variable {a b : ℕ → ℕ}

section Positive

variable (ha : ∀ n, 1 ≤ a (n + 1))
include ha

/-- `α = 1 / (a₁ + α₁)` with `α₁ = [0; a₂, a₃, …]`. -/
theorem contFrac_eq_inv_add :
    contFrac a = ((a 1 : ℝ) + contFrac (fun i ↦ a (i + 1)))⁻¹ := by
  have h := contFrac_eq_of_tail ha 0
  simp only [zero_add, contNum_one, contNum_zero, contDen_one, contDen_zero, Nat.cast_one,
    Nat.cast_zero, zero_mul, add_zero, one_mul] at h
  rw [h, one_div]

/-- `a₁ = ⌊1 / α⌋`. -/
theorem floor_inv_contFrac : ⌊(contFrac a)⁻¹⌋₊ = a 1 := by
  have hs : ∀ n, 1 ≤ (fun i ↦ a (i + 1)) (n + 1) := fun n ↦ ha (n + 1)
  have h0 := contFrac_pos (a := fun i ↦ a (i + 1)) hs
  have h1 := contFrac_lt_one (a := fun i ↦ a (i + 1)) hs
  rw [contFrac_eq_inv_add ha, inv_inv, Nat.floor_eq_iff (by positivity)]
  constructor <;> linarith

/-- **`α` determines its partial quotients.** -/
theorem contFrac_injective (hb : ∀ n, 1 ≤ b (n + 1)) (h : contFrac a = contFrac b) (i : ℕ) :
    a (i + 1) = b (i + 1) := by
  induction i generalizing a b with
  | zero => rw [← floor_inv_contFrac ha, ← floor_inv_contFrac hb, h]
  | succ i ih =>
    have h1 : a 1 = b 1 := by rw [← floor_inv_contFrac ha, ← floor_inv_contFrac hb, h]
    have htail : contFrac (fun k ↦ a (k + 1)) = contFrac (fun k ↦ b (k + 1)) := by
      have ea := contFrac_eq_inv_add ha
      have eb := contFrac_eq_inv_add hb
      rw [h, eb, h1] at ea
      have := inv_injective ea
      linarith
    exact ih (fun n ↦ ha (n + 1)) (fun n ↦ hb (n + 1)) htail

end Positive

/-- A rational number is not a root of an integer quadratic `A X² + B X + C` with `A ≠ 0` that
also has an irrational real root. -/
theorem quadratic_ne_zero_of_irrational {A B C : ℤ} (hA : A ≠ 0) {α : ℝ} (hα : Irrational α)
    (hf : (A : ℝ) * α ^ 2 + B * α + C = 0) (r : ℚ) :
    (A : ℝ) * (r : ℝ) ^ 2 + B * r + C ≠ 0 := by
  intro hr
  have hne : α - r ≠ 0 := sub_ne_zero.mpr (hα.ne_rat r)
  have h : (A : ℝ) * (α + r) + B = 0 := by
    have : (α - r) * ((A : ℝ) * (α + r) + B) = 0 := by linear_combination hf - hr
    exact (_root_.mul_eq_zero.mp this).resolve_left hne
  have hA' : (A : ℝ) ≠ 0 := by exact_mod_cast hA
  refine hα ⟨-B / A - r, ?_⟩
  push_cast
  field_simp
  linarith

section Positive

variable (ha : ∀ n, 1 ≤ a (n + 1))
include ha

/-- The integer polynomial `l X² + m X + n`. -/
noncomputable def quadPoly (t : ℤ × ℤ × ℤ) : Polynomial ℤ :=
  Polynomial.C t.1 * Polynomial.X ^ 2 + Polynomial.C t.2.1 * Polynomial.X + Polynomial.C t.2.2

omit ha in
theorem aeval_quadPoly (t : ℤ × ℤ × ℤ) (y : ℝ) :
    Polynomial.aeval y (quadPoly t) = (t.1 : ℝ) * y ^ 2 + t.2.1 * y + t.2.2 := by
  simp [quadPoly]

omit ha in
theorem quadPoly_ne_zero {t : ℤ × ℤ × ℤ} (ht : t.1 ≠ 0) : quadPoly t ≠ 0 := by
  intro h
  have h2 : (quadPoly t).coeff 2 = t.1 := by
    rw [quadPoly, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
  rw [h, Polynomial.coeff_zero] at h2
  exact ht h2.symm

/-- **Lagrange's theorem**, integer form: if `[0; a₁, a₂, …]` is a root of `A X² + B X + C` with
`A ≠ 0` over `ℤ`, then `(a_{k+1})_k` is eventually periodic. -/
theorem isEventuallyPeriodic_of_quadratic_int {A B C : ℤ} (hA : A ≠ 0)
    (hf : (A : ℝ) * contFrac a ^ 2 + B * contFrac a + C = 0) :
    Function.IsEventuallyPeriodic fun k ↦ a (k + 1) := by
  set α := contFrac a
  have hirr : Irrational α := irrational_contFrac ha
  have hα0 : 0 < α := contFrac_pos ha
  have hα1 : α < 1 := contFrac_lt_one ha
  -- the tails and their quadratics
  set t : ℕ → ℝ := fun j ↦ contFrac (fun i ↦ a (i + (j + 1)))
  set e : ℕ → ℝ := fun ℓ ↦ (contDen a ℓ : ℝ) * α - contNum a ℓ with he
  have he1 (ℓ : ℕ) : |e ℓ| ≤ 1 := by
    refine (abs_contDen_mul_contFrac_sub_le ha ℓ).trans ?_
    rw [div_le_one (contDen_pos_real ha _)]
    exact_mod_cast one_le_contDen ha (ℓ + 1)
  have hqe (m ℓ : ℕ) (h : m ≤ ℓ + 1) : |(contDen a m : ℝ) * e ℓ| ≤ 1 := by
    rw [abs_mul, Nat.abs_cast]
    calc (contDen a m : ℝ) * |e ℓ| ≤ contDen a m * (1 / contDen a (ℓ + 1)) :=
          mul_le_mul_of_nonneg_left (abs_contDen_mul_contFrac_sub_le ha ℓ) (Nat.cast_nonneg _)
      _ ≤ 1 := by
          rw [mul_one_div, div_le_one (contDen_pos_real ha _)]
          exact contDen_mono_real ha h
  set L : ℕ → ℤ := fun j ↦ A * contNum a j ^ 2 + B * contNum a j * contDen a j +
    C * contDen a j ^ 2
  set Mc : ℕ → ℤ := fun j ↦ 2 * A * contNum a (j + 1) * contNum a j +
    B * (contNum a (j + 1) * contDen a j + contNum a j * contDen a (j + 1)) +
    2 * C * contDen a (j + 1) * contDen a j
  set Bd : ℤ := 2 * (3 * |A| + |B|)
  have hAα : |2 * (A : ℝ) * α + B| ≤ 2 * |(A : ℝ)| + |(B : ℝ)| := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos hα0, abs_two]
    nlinarith [abs_nonneg (A : ℝ)]
  have hL (j : ℕ) : |(L j : ℝ)| ≤ 3 * |(A : ℝ)| + |(B : ℝ)| := by
    have hid : (L j : ℝ) = -((contDen a j : ℝ) * e j) * (2 * A * α + B) + A * e j ^ 2 := by
      simp only [L, he]; push_cast; linear_combination (contDen a j : ℝ) ^ 2 * hf
    rw [hid]
    refine (abs_add_le _ _).trans ?_
    have h1 := hqe j j (by omega)
    have h2 : |e j| ^ 2 ≤ 1 := by nlinarith [he1 j, abs_nonneg (e j)]
    have t1 : |-((contDen a j : ℝ) * e j) * (2 * A * α + B)| ≤ 2 * |(A : ℝ)| + |(B : ℝ)| := by
      rw [abs_mul, abs_neg]
      exact (mul_le_mul h1 hAα (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    have t2 : |(A : ℝ) * e j ^ 2| ≤ |(A : ℝ)| := by
      rw [abs_mul, abs_pow]; exact mul_le_of_le_one_right (abs_nonneg _) h2
    linarith
  have hM (j : ℕ) : |(Mc j : ℝ)| ≤ 2 * (3 * |(A : ℝ)| + |(B : ℝ)|) := by
    have hid : (Mc j : ℝ) = -((contDen a (j + 1) : ℝ) * e j + (contDen a j : ℝ) * e (j + 1)) *
        (2 * A * α + B) + 2 * A * e (j + 1) * e j := by
      simp only [Mc, he]; push_cast
      linear_combination 2 * (contDen a (j + 1) : ℝ) * contDen a j * hf
    rw [hid]
    refine (abs_add_le _ _).trans ?_
    have h1 : |(contDen a (j + 1) : ℝ) * e j + (contDen a j : ℝ) * e (j + 1)| ≤ 2 :=
      (abs_add_le _ _).trans (by linarith [hqe (j + 1) j le_rfl, hqe j (j + 1) (by omega)])
    have h2 : |e (j + 1)| * |e j| ≤ 1 := by
      nlinarith [he1 j, he1 (j + 1), abs_nonneg (e j), abs_nonneg (e (j + 1))]
    have t1 : |-((contDen a (j + 1) : ℝ) * e j + (contDen a j : ℝ) * e (j + 1)) *
        (2 * A * α + B)| ≤ 2 * (2 * |(A : ℝ)| + |(B : ℝ)|) := by
      rw [abs_mul, abs_neg]
      exact mul_le_mul h1 hAα (abs_nonneg _) zero_le_two
    have t2 : |2 * (A : ℝ) * e (j + 1) * e j| ≤ 2 * |(A : ℝ)| := by
      rw [abs_mul, abs_mul, abs_mul, abs_two, mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (abs_nonneg _)
        (by rw [← abs_mul, abs_mul]; exact h2)) zero_le_two
    linarith
  have hLne (j : ℕ) : L j ≠ 0 := by
    intro h0
    have hq := contDen_pos_real ha j
    refine quadratic_ne_zero_of_irrational hA hirr hf
      ((contNum a j : ℚ) / contDen a j) ?_
    have : (L j : ℝ) = 0 := by exact_mod_cast h0
    simp only [L] at this
    push_cast at this ⊢
    field_simp
    linear_combination this
  -- `t j` is a root of `L j X² + M j X + L (j + 1)`
  have hroot (j : ℕ) : (L j : ℝ) * t j ^ 2 + Mc j * t j + L (j + 1) = 0 := by
    have ht := contFrac_eq_of_tail ha j
    have hs : ∀ n, 1 ≤ (fun i ↦ a (i + (j + 1))) (n + 1) := fun n ↦ ha (n + 1 + j)
    have hpos : (0 : ℝ) < contDen a (j + 1) + contDen a j * t j := by
      have := contDen_pos_real ha (j + 1)
      have := contFrac_pos (a := fun i ↦ a (i + (j + 1))) hs
      positivity
    have ht' : α = ((contNum a (j + 1) : ℝ) + contNum a j * t j) /
        ((contDen a (j + 1) : ℝ) + contDen a j * t j) := ht
    have key : (L j : ℝ) * t j ^ 2 + Mc j * t j + L (j + 1) =
        ((contDen a (j + 1) : ℝ) + contDen a j * t j) ^ 2 * ((A : ℝ) * α ^ 2 + B * α + C) := by
      rw [ht']
      simp only [L, Mc]
      push_cast
      field_simp
      ring
    rw [key, hf, mul_zero]
  -- the tails take finitely many values
  set box : Finset (ℤ × ℤ × ℤ) := Finset.Icc (-Bd) Bd ×ˢ Finset.Icc (-Bd) Bd ×ˢ Finset.Icc (-Bd) Bd
  have hfin : (⋃ τ ∈ box, (quadPoly τ).rootSet ℝ).Finite :=
    (box.finite_toSet).biUnion fun τ _ ↦ Polynomial.rootSet_finite _ _
  have hBd (x : ℤ) (h : |(x : ℝ)| ≤ 2 * (3 * |(A : ℝ)| + |(B : ℝ)|)) : x ∈ Finset.Icc (-Bd) Bd := by
    have : |x| ≤ Bd := by simp only [Bd]; exact_mod_cast h
    rw [Finset.mem_Icc]; exact abs_le.mp this
  have hmem (j : ℕ) : t j ∈ ⋃ τ ∈ box, (quadPoly τ).rootSet ℝ := by
    refine Set.mem_biUnion (x := (L j, Mc j, L (j + 1))) ?_ ?_
    · simp only [box, Finset.coe_product, Set.mem_prod, Finset.mem_coe]
      exact ⟨hBd _ (by linarith [hL j, abs_nonneg (A : ℝ), abs_nonneg (B : ℝ)]), hBd _ (hM j),
        hBd _ (by linarith [hL (j + 1), abs_nonneg (A : ℝ), abs_nonneg (B : ℝ)])⟩
    · rw [Polynomial.mem_rootSet]
      exact ⟨quadPoly_ne_zero (hLne j), by rw [aeval_quadPoly]; exact hroot j⟩
  obtain ⟨j1, j2, hlt, heq⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem hmem hfin
  -- equal tails have equal partial quotients
  have hq := contFrac_injective (a := fun i ↦ a (i + (j1 + 1))) (b := fun i ↦ a (i + (j2 + 1)))
    (fun n ↦ ha (n + 1 + j1)) (fun n ↦ ha (n + 1 + j2)) heq
  refine ⟨j1 + 1, j2 - j1, by omega, fun n hn ↦ ?_⟩
  have := hq (n - (j1 + 1))
  simp only at this ⊢
  rw [show n - (j1 + 1) + 1 + (j1 + 1) = n + 1 by omega,
    show n - (j1 + 1) + 1 + (j2 + 1) = n + (j2 - j1) + 1 by omega] at this
  exact this.symm

/-- **Lagrange's theorem.** If `[0; a₁, a₂, …]` is a root of a non-zero rational polynomial of
degree at most `2`, then `(a_{k+1})_k` is eventually periodic. -/
theorem isEventuallyPeriodic_of_quadratic {A B C : ℚ} (hne : ¬ (A = 0 ∧ B = 0 ∧ C = 0))
    (hf : (A : ℝ) * contFrac a ^ 2 + B * contFrac a + C = 0) :
    Function.IsEventuallyPeriodic fun k ↦ a (k + 1) := by
  have hirr := irrational_contFrac ha
  by_cases hA : A = 0
  · exfalso
    rw [hA] at hf
    push_cast at hf
    by_cases hB : B = 0
    · rw [hB] at hf; push_cast at hf
      exact hne ⟨hA, hB, by exact_mod_cast (by linarith : (C : ℝ) = 0)⟩
    · have hB' : (B : ℝ) ≠ 0 := by exact_mod_cast hB
      exact hirr ⟨-C / B, by push_cast; field_simp; linarith⟩
  -- clear denominators
  set D : ℕ := A.den * B.den * C.den
  have hD : (D : ℝ) ≠ 0 := by positivity
  refine isEventuallyPeriodic_of_quadratic_int ha (A := A.num * B.den * C.den)
    (B := B.num * A.den * C.den) (C := C.num * A.den * B.den) ?_ ?_
  · have := Rat.num_ne_zero.mpr hA
    positivity
  · have hA' : (A : ℝ) = A.num / A.den := Rat.cast_def A
    have hB' : (B : ℝ) = B.num / B.den := Rat.cast_def B
    have hC' : (C : ℝ) = C.num / C.den := Rat.cast_def C
    rw [hA', hB', hC'] at hf
    have hAd : (A.den : ℝ) ≠ 0 := by positivity
    have hBd : (B.den : ℝ) ≠ 0 := by positivity
    have hCd : (C.den : ℝ) ≠ 0 := by positivity
    field_simp at hf
    push_cast
    linear_combination hf

end Positive

end Nat
