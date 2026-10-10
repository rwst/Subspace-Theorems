/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Bugeaud2013.Value

-- Used only inside proofs.
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# The estimates (3.1)–(3.4) of Bugeaud 2013

Fix `w ≥ 1`, a period `r ≥ 1` and a length `u ≤ r` such that `a_m = a_{m+r}` for
`w < m ≤ w + u`. The paper's `P_n` is the polynomial `A X² - (B₂ + B₃) X + C` with

```text
A  = q_{w-1} q_{w+r} - q_w q_{w+r-1},   B₂ = q_{w-1} p_{w+r} - q_w p_{w+r-1},
B₃ = p_{w-1} q_{w+r} - p_w q_{w+r-1},   C  = p_{w-1} p_{w+r} - p_w p_{w+r-1},
```

the integer point `v_n = (A, B₂, B₃, C)`; everything is stated at `w = j + 1`. This file proves
the bounds on the linear forms of §3 at `v_n`:

* `|α A - B₂| ≤ 2 q_w / q_{w+r}` and `|α A - B₃| ≤ 2 q_{w+r} / q_w` ((3.2), (3.3));
* `|A|, |B₂|, |B₃|, |C| ≤ q_w q_{w+r}`;
* **(3.4)** `|P_n(α)| ≤ 12 (q_{w+r} / q_w) q_N⁻²`, `N = w + r + u`, from (3.1) and the root
  `α_n` of `P_n` (the continued fraction completed by periodicity);
* the products of the forms of the two Subspace applications are at most
  `48 q_{w+r}² / q_N² ≤ 96 · 2^{-u}`.

## Main definitions

* `Nat.spadeVec a j r`: the point `v_n = (A, B₂, B₃, C)` for `w = j + 1`.
* `Nat.spadeExt a j r`: the continued fraction completed by periodicity (the paper's `b^{(n)}`).

## References

Y. Bugeaud, *Automatic continued fractions are transcendental or quadratic*, Ann. Sci. Éc. Norm.
Supér. (4) **46** (2013), 1005–1022, §3.
-/

@[expose] public section

namespace Nat

/-- **The point `v_n = (A, B₂, B₃, C)`** of §3, the coefficients of `P_n`, for the preperiod
`w = j + 1` and the period `r`. -/
def spadeVec (a : ℕ → ℕ) (j r : ℕ) : Fin 4 → ℤ :=
  ![contDen a j * contDen a (j + 1 + r) - contDen a (j + 1) * contDen a (j + r),
    contDen a j * contNum a (j + 1 + r) - contDen a (j + 1) * contNum a (j + r),
    contNum a j * contDen a (j + 1 + r) - contNum a (j + 1) * contDen a (j + r),
    contNum a j * contNum a (j + 1 + r) - contNum a (j + 1) * contNum a (j + r)]

/-- **The continued fraction completed by periodicity** (the paper's `b^{(n)}`): `a_i` for
`i ≤ w = j + 1`, then periodic with period `r`. -/
def spadeExt (a : ℕ → ℕ) (j r : ℕ) (i : ℕ) : ℕ :=
  if i < j + 2 then a i else a (j + 2 + (i - (j + 2)) % r)

variable {a : ℕ → ℕ}

theorem spadeVec_zero (a : ℕ → ℕ) (j r : ℕ) : spadeVec a j r 0 =
    contDen a j * contDen a (j + 1 + r) - contDen a (j + 1) * contDen a (j + r) := rfl

theorem spadeVec_one (a : ℕ → ℕ) (j r : ℕ) : spadeVec a j r 1 =
    contDen a j * contNum a (j + 1 + r) - contDen a (j + 1) * contNum a (j + r) := rfl

theorem spadeVec_two (a : ℕ → ℕ) (j r : ℕ) : spadeVec a j r 2 =
    contNum a j * contDen a (j + 1 + r) - contNum a (j + 1) * contDen a (j + r) := rfl

theorem spadeVec_three (a : ℕ → ℕ) (j r : ℕ) : spadeVec a j r 3 =
    contNum a j * contNum a (j + 1 + r) - contNum a (j + 1) * contNum a (j + r) := rfl

theorem spadeExt_add (a : ℕ → ℕ) (j r : ℕ) {m : ℕ} (hm : j + 2 ≤ m) :
    spadeExt a j r (m + r) = spadeExt a j r m := by
  simp only [spadeExt, show ¬ m + r < j + 2 by omega, show ¬ m < j + 2 by omega, ↓reduceIte]
  rw [show m + r - (j + 2) = m - (j + 2) + r by omega, Nat.add_mod_right]

/-- The completed sequence agrees with `a` on `a₁, …, a_{w+r+u}`. -/
theorem spadeExt_eq {j r u : ℕ} (hur : u ≤ r)
    (hrep : ∀ m, j + 1 < m → m ≤ j + 1 + u → a (m + r) = a m) {i : ℕ}
    (hi : i ≤ j + 1 + r + u) : a i = spadeExt a j r i := by
  unfold spadeExt
  split_ifs with h
  · rfl
  · rcases (show i ≤ j + 1 + r ∨ j + 1 + r < i by omega) with h1 | h1
    · rw [Nat.mod_eq_of_lt (by omega), show j + 2 + (i - (j + 2)) = i by omega]
    · have := hrep (i - r) (by omega) (by omega)
      rw [show i - r + r = i by omega] at this
      rw [this, show i - (j + 2) = i - r - (j + 2) + r by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (show i - r - (j + 2) < r by omega),
        show j + 2 + (i - r - (j + 2)) = i - r by omega]

/-- `X |E| ≤ P / Q` from `X ≤ P`, `|E| ≤ 1 / Q'` and `Q ≤ Q'`. -/
private theorem mul_abs_le_div {X P Q Q' E : ℝ} (hX : 0 ≤ X) (hXP : X ≤ P) (hQ : 0 < Q)
    (hQQ : Q ≤ Q') (hE : |E| ≤ 1 / Q') : X * |E| ≤ P / Q := by
  have hP : 0 ≤ P := hX.trans hXP
  calc X * |E| ≤ P * (1 / Q') := mul_le_mul hXP hE (abs_nonneg _) hP
    _ ≤ P * (1 / Q) := by gcongr
    _ = P / Q := by ring

/-- `|x y - x' y'| ≤ X Y` when both products lie in `[0, X Y]`. -/
private theorem abs_mul_sub_mul_le {x y x' y' X Y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hx' : 0 ≤ x')
    (hy' : 0 ≤ y') (h1 : x ≤ X) (h2 : y ≤ Y) (h3 : x' ≤ X) (h4 : y' ≤ Y) :
    |x * y - x' * y'| ≤ X * Y :=
  abs_sub_le_of_nonneg_of_le (mul_nonneg hx hy)
    (mul_le_mul h1 h2 hy (hx.trans h1)) (mul_nonneg hx' hy') (mul_le_mul h3 h4 hy' (hx.trans h1))

section Positive

variable (ha : ∀ n, 1 ≤ a (n + 1))
include ha

/-- `|q_ℓ α - p_ℓ| ≤ 1 / q_{ℓ+1}`, the non-strict form of (2.2). -/
theorem abs_contDen_mul_contFrac_sub_le (n : ℕ) :
    |(contDen a n : ℝ) * contFrac a - contNum a n| ≤ 1 / contDen a (n + 1) := by
  rw [one_div]; exact (abs_contDen_mul_contFrac_sub_lt ha n).le

theorem contDen_mono_real {m n : ℕ} (h : m ≤ n) : (contDen a m : ℝ) ≤ contDen a n := by
  have : Monotone (contDen a) := monotone_nat_of_le_succ (contDen_le_contDen_succ ha)
  exact_mod_cast this h

theorem contNum_le_contDen_real (n : ℕ) : (contNum a n : ℝ) ≤ contDen a n := by
  exact_mod_cast contNum_le_contDen ha n

/-- **(3.2)** `|α A - B₂| ≤ 2 q_w / q_{w+r}`. -/
theorem abs_spadeL2_le (j r : ℕ) :
    |contFrac a * ((contDen a j * contDen a (j + 1 + r) - contDen a (j + 1) * contDen a (j + r)
        : ℤ) : ℝ) -
      ((contDen a j * contNum a (j + 1 + r) - contDen a (j + 1) * contNum a (j + r) : ℤ) : ℝ)|
      ≤ 2 * contDen a (j + 1) / contDen a (j + 1 + r) := by
  have e1 := abs_contDen_mul_contFrac_sub_le ha (j + 1 + r)
  have e2 := abs_contDen_mul_contFrac_sub_le ha (j + r)
  rw [show j + r + 1 = j + 1 + r by ring] at e2
  have hq := contDen_pos_real ha (j + 1 + r)
  have key : contFrac a *
      ((contDen a j * contDen a (j + 1 + r) - contDen a (j + 1) * contDen a (j + r)
      : ℤ) : ℝ) -
      ((contDen a j * contNum a (j + 1 + r) - contDen a (j + 1) * contNum a (j + r) : ℤ) : ℝ) =
      contDen a j * (contDen a (j + 1 + r) * contFrac a - contNum a (j + 1 + r)) -
        contDen a (j + 1) * (contDen a (j + r) * contFrac a - contNum a (j + r)) := by
    push_cast; ring
  rw [key]
  refine (abs_sub _ _).trans ?_
  simp only [abs_mul, Nat.abs_cast]
  have h1 := mul_abs_le_div (Nat.cast_nonneg _) (contDen_mono_real ha (show j ≤ j + 1 by omega)) hq
    (contDen_mono_real ha (show j + 1 + r ≤ j + 1 + r + 1 by omega)) e1
  have h2 := mul_abs_le_div (X := (contDen a (j + 1) : ℝ)) (Nat.cast_nonneg _) le_rfl hq le_rfl e2
  calc _ ≤ (contDen a (j + 1) : ℝ) / contDen a (j + 1 + r) +
        (contDen a (j + 1) : ℝ) / contDen a (j + 1 + r) := by linarith
    _ = _ := by ring

/-- **(3.3)** `|α A - B₃| ≤ 2 q_{w+r} / q_w`. -/
theorem abs_spadeL3_le (j r : ℕ) :
    |contFrac a * ((contDen a j * contDen a (j + 1 + r) - contDen a (j + 1) * contDen a (j + r)
        : ℤ) : ℝ) -
      ((contNum a j * contDen a (j + 1 + r) - contNum a (j + 1) * contDen a (j + r) : ℤ) : ℝ)|
      ≤ 2 * contDen a (j + 1 + r) / contDen a (j + 1) := by
  have e1 := abs_contDen_mul_contFrac_sub_le ha j
  have e2 := abs_contDen_mul_contFrac_sub_le ha (j + 1)
  have hq := contDen_pos_real ha (j + 1)
  have key : contFrac a *
      ((contDen a j * contDen a (j + 1 + r) - contDen a (j + 1) * contDen a (j + r)
      : ℤ) : ℝ) -
      ((contNum a j * contDen a (j + 1 + r) - contNum a (j + 1) * contDen a (j + r) : ℤ) : ℝ) =
      contDen a (j + 1 + r) * (contDen a j * contFrac a - contNum a j) -
        contDen a (j + r) * (contDen a (j + 1) * contFrac a - contNum a (j + 1)) := by
    push_cast; ring
  rw [key]
  refine (abs_sub _ _).trans ?_
  simp only [abs_mul, Nat.abs_cast]
  have h1 := mul_abs_le_div (X := (contDen a (j + 1 + r) : ℝ)) (Nat.cast_nonneg _) le_rfl hq
    le_rfl e1
  have h2 := mul_abs_le_div (Nat.cast_nonneg _) (contDen_mono_real ha (show j + r ≤ j + 1 + r by
    omega)) hq (contDen_mono_real ha (show j + 1 ≤ j + 1 + 1 by omega)) e2
  calc _ ≤ (contDen a (j + 1 + r) : ℝ) / contDen a (j + 1) +
        (contDen a (j + 1 + r) : ℝ) / contDen a (j + 1) := by linarith
    _ = _ := by ring

/-- The coordinates of `v_n` are at most `q_w q_{w+r}` in absolute value. -/
theorem abs_spadeVec_le (j r : ℕ) (i : Fin 4) :
    |(spadeVec a j r i : ℝ)| ≤ contDen a (j + 1) * contDen a (j + 1 + r) := by
  have hj := contDen_mono_real ha (Nat.le_succ j)
  have hr := contDen_mono_real ha (show j + r ≤ j + 1 + r by omega)
  have n0 := contNum_le_contDen_real ha j
  have n1 := contNum_le_contDen_real ha (j + 1)
  have n2 := contNum_le_contDen_real ha (j + r)
  have n3 := contNum_le_contDen_real ha (j + 1 + r)
  have c (n : ℕ) : (0 : ℝ) ≤ contDen a n := Nat.cast_nonneg _
  have d (n : ℕ) : (0 : ℝ) ≤ contNum a n := Nat.cast_nonneg _
  fin_cases i
  · change |((spadeVec a j r 0 : ℤ) : ℝ)| ≤ _
    rw [spadeVec_zero]; push_cast
    exact abs_mul_sub_mul_le (c _) (c _) (c _) (c _) hj le_rfl le_rfl hr
  · change |((spadeVec a j r 1 : ℤ) : ℝ)| ≤ _
    rw [spadeVec_one]; push_cast
    exact abs_mul_sub_mul_le (c _) (d _) (c _) (d _) hj n3 le_rfl (n2.trans hr)
  · change |((spadeVec a j r 2 : ℤ) : ℝ)| ≤ _
    rw [spadeVec_two]; push_cast
    exact abs_mul_sub_mul_le (d _) (c _) (d _) (c _) (n0.trans hj) le_rfl n1 hr
  · change |((spadeVec a j r 3 : ℤ) : ℝ)| ≤ _
    rw [spadeVec_three]; push_cast
    exact abs_mul_sub_mul_le (d _) (d _) (d _) (d _) (n0.trans hj) n3 n1 (n2.trans hr)

/-- `|v_n|_∞ ≤ q_w q_{w+r}`. -/
theorem iSup_abs_spadeVec_le (j r : ℕ) :
    (⨆ i, |(spadeVec a j r i : ℝ)|) ≤ contDen a (j + 1) * contDen a (j + 1 + r) :=
  ciSup_le (abs_spadeVec_le ha j r)

/-- The leading coefficient `A` of `P_n` is non-zero. -/
theorem spadeVec_zero_ne (j : ℕ) {r : ℕ} (hr : 1 ≤ r) : spadeVec a j r 0 ≠ 0 := by
  have := contDen_mul_contDen_ne ha j hr
  simp only [spadeVec, Matrix.cons_val_zero]
  zify at this
  exact sub_ne_zero.mpr this

/-- **(3.4)**: `|P_n(α)| ≤ 12 (q_{w+r} / q_w) / q_N²` with `N = w + r + u`, where `P_n` vanishes at
the continued fraction `α_n` completed by periodicity and `|α - α_n| < 2 / q_N²` by (3.1). -/
theorem abs_spadeL1_le {j r u : ℕ} (hu : 1 ≤ u) (hur : u ≤ r)
    (hrep : ∀ m, j + 1 < m → m ≤ j + 1 + u → a (m + r) = a m) :
    |contFrac a ^ 2 * (spadeVec a j r 0 : ℝ) -
        contFrac a * ((spadeVec a j r 1 : ℝ) + spadeVec a j r 2) + spadeVec a j r 3|
      ≤ 12 * (contDen a (j + 1 + r) / contDen a (j + 1)) / (contDen a (j + 1 + r + u) : ℝ) ^ 2 := by
  set α := contFrac a
  set b := spadeExt a j r
  have hb : ∀ n, 1 ≤ b (n + 1) := fun n ↦ by
    simp only [b, spadeExt]; split_ifs
    · exact ha n
    · have := ha (j + 1 + (n + 1 - (j + 2)) % r)
      rwa [show j + 1 + (n + 1 - (j + 2)) % r + 1 = j + 2 + (n + 1 - (j + 2)) % r by ring] at this
  have hagree : ∀ i, 1 ≤ i → i ≤ j + 1 + r + u → a i = b i := fun i _ hi ↦
    spadeExt_eq hur hrep hi
  set N := j + 1 + r + u
  -- the convergents of `a` and `b` agree up to index `w + r`
  have hN (i : ℕ) (hi : i ≤ j + 1 + r) : contNum b i = contNum a i ∧ contDen b i = contDen a i :=
    ⟨(contNum_eq_of_eqOn (m := N) hagree (by omega)).symm,
      (contDen_eq_of_eqOn (m := N) hagree (by omega)).symm⟩
  -- the root `α_n = [0; b₁, b₂, …]` of `P_n`
  have hroot := contFrac_isRoot hb j r fun m hm ↦ spadeExt_add a j r hm
  rw [(hN j (by omega)).1, (hN j (by omega)).2, (hN (j + 1) (by omega)).1,
    (hN (j + 1) (by omega)).2, (hN (j + r) (by omega)).1, (hN (j + r) (by omega)).2,
    (hN (j + 1 + r) le_rfl).1, (hN (j + 1 + r) le_rfl).2] at hroot
  set γ := contFrac b
  -- (3.1)
  have h31 : |α - γ| < 2 / (contDen a N : ℝ) ^ 2 := abs_contFrac_sub_contFrac_lt ha hb hagree
  have hL2 := abs_spadeL2_le ha j r
  have hL3 := abs_spadeL3_le ha j r
  have hA := abs_spadeVec_le ha j r 0
  set A : ℝ := (spadeVec a j r 0 : ℝ)
  set B2 : ℝ := (spadeVec a j r 1 : ℝ)
  set B3 : ℝ := (spadeVec a j r 2 : ℝ)
  set C : ℝ := (spadeVec a j r 3 : ℝ)
  have eA : A = ((contDen a j * contDen a (j + 1 + r) - contDen a (j + 1) * contDen a (j + r)
      : ℤ) : ℝ) := rfl
  have eB2 : B2 = ((contDen a j * contNum a (j + 1 + r) - contDen a (j + 1) * contNum a (j + r)
      : ℤ) : ℝ) := rfl
  have eB3 : B3 = ((contNum a j * contDen a (j + 1 + r) - contNum a (j + 1) * contDen a (j + r)
      : ℤ) : ℝ) := rfl
  have eC : C = ((contNum a j * contNum a (j + 1 + r) - contNum a (j + 1) * contNum a (j + r)
      : ℤ) : ℝ) := rfl
  rw [← eA, ← eB2] at hL2
  rw [← eA, ← eB3] at hL3
  have hroot' : A * γ ^ 2 - (B2 + B3) * γ + C = 0 := by
    rw [eA, eB2, eB3, eC]; push_cast at hroot ⊢; linear_combination hroot
  -- `P_n(α) = (α - α_n) ((α A - B₂) + (α A - B₃) + A (α_n - α))`
  have key : α ^ 2 * A - α * (B2 + B3) + C =
      (α - γ) * ((α * A - B2) + (α * A - B3) + A * (γ - α)) := by
    linear_combination hroot'
  rw [key, abs_mul]
  -- sizes
  have q1 := contDen_pos_real ha (j + 1)
  have qr := contDen_pos_real ha (j + 1 + r)
  have qN := contDen_pos_real ha N
  have h1r : (contDen a (j + 1) : ℝ) ≤ contDen a (j + 1 + r) := contDen_mono_real ha (by omega)
  have hrN : (contDen a (j + 1 + r) : ℝ) ≤ contDen a N := contDen_mono_real ha (by omega)
  set ρ : ℝ := contDen a (j + 1 + r) / contDen a (j + 1)
  have hρ : 1 ≤ ρ := (one_le_div q1).2 h1r
  have hL2' : |α * A - B2| ≤ 2 * ρ := by
    refine hL2.trans ?_
    have : (contDen a (j + 1) : ℝ) / contDen a (j + 1 + r) ≤ 1 := (div_le_one qr).2 h1r
    calc 2 * (contDen a (j + 1) : ℝ) / contDen a (j + 1 + r)
        = 2 * ((contDen a (j + 1) : ℝ) / contDen a (j + 1 + r)) := by ring
      _ ≤ 2 * ρ := by linarith
  have hL3' : |α * A - B3| ≤ 2 * ρ := by
    refine hL3.trans (le_of_eq ?_); simp only [ρ]; ring
  have hAγ : |A * (γ - α)| ≤ 2 * ρ := by
    rw [abs_mul, abs_sub_comm]
    have hprod : (contDen a (j + 1) : ℝ) * contDen a (j + 1 + r) ≤ (contDen a N : ℝ) ^ 2 := by
      rw [sq]; exact mul_le_mul (h1r.trans hrN) hrN qr.le qN.le
    calc |A| * |α - γ| ≤ (contDen a (j + 1) * contDen a (j + 1 + r)) * (2 / (contDen a N) ^ 2) :=
          mul_le_mul hA h31.le (abs_nonneg _) (by positivity)
      _ ≤ (contDen a N : ℝ) ^ 2 * (2 / (contDen a N) ^ 2) := by gcongr
      _ = 2 := by field_simp
      _ ≤ 2 * ρ := by linarith
  have hsum : |(α * A - B2) + (α * A - B3) + A * (γ - α)| ≤ 6 * ρ :=
    (abs_add_le _ _).trans (by linarith [abs_add_le (α * A - B2) (α * A - B3)])
  calc |α - γ| * |(α * A - B2) + (α * A - B3) + A * (γ - α)|
      ≤ (2 / (contDen a N : ℝ) ^ 2) * (6 * ρ) :=
        mul_le_mul h31.le hsum (abs_nonneg _) (by positivity)
    _ = 12 * ρ / (contDen a N : ℝ) ^ 2 := by ring

/-- `q_{w+r}² / q_N² ≤ 2 / 2^u` for `N = w + r + u`, by (2.3). -/
theorem contDen_sq_div_le (l : ℕ) {u : ℕ} (hu : 1 ≤ u) :
    (contDen a l : ℝ) ^ 2 / (contDen a (l + u) : ℝ) ^ 2 ≤ 2 / 2 ^ u := by
  obtain ⟨t, rfl⟩ : ∃ t, u = t + 1 := ⟨u - 1, by omega⟩
  have h := contDen_sq_mul_two_pow_le ha l t
  rw [show l + t + 1 = l + (t + 1) by omega] at h
  have h' : (contDen a l : ℝ) ^ 2 * 2 ^ t ≤ (contDen a (l + (t + 1)) : ℝ) ^ 2 := by
    exact_mod_cast h
  have hq := contDen_pos_real ha (l + (t + 1))
  rw [div_le_div_iff₀ (by positivity) (by positivity), show (2 : ℝ) ^ (t + 1) = 2 ^ t * 2 from
    pow_succ 2 t]
  nlinarith [h']

/-- **The product of the four forms of §3 at `v_n`**:
`|P_n(α)| |α A - B₂| |α A - B₃| |A| ≤ 96 · 2^{-u}`. -/
theorem spade_prod_four_le {j r u : ℕ} (hu : 1 ≤ u) (hur : u ≤ r)
    (hrep : ∀ m, j + 1 < m → m ≤ j + 1 + u → a (m + r) = a m) :
    |contFrac a ^ 2 * (spadeVec a j r 0 : ℝ) -
        contFrac a * ((spadeVec a j r 1 : ℝ) + spadeVec a j r 2) + spadeVec a j r 3| *
      |contFrac a * (spadeVec a j r 0 : ℝ) - spadeVec a j r 1| *
      |contFrac a * (spadeVec a j r 0 : ℝ) - spadeVec a j r 2| * |(spadeVec a j r 0 : ℝ)|
      ≤ 96 / 2 ^ u := by
  have h1 := abs_spadeL1_le ha hu hur hrep
  have h2 := abs_spadeL2_le ha j r
  have h3 := abs_spadeL3_le ha j r
  have h4 := abs_spadeVec_le ha j r 0
  have hsq := contDen_sq_div_le ha (j + 1 + r) hu
  have q1 := contDen_pos_real ha (j + 1)
  have qr := contDen_pos_real ha (j + 1 + r)
  have qN := contDen_pos_real ha (j + 1 + r + u)
  set Q1 : ℝ := (contDen a (j + 1) : ℝ)
  set Qr : ℝ := (contDen a (j + 1 + r) : ℝ)
  set QN : ℝ := (contDen a (j + 1 + r + u) : ℝ)
  calc _ ≤ (12 * (Qr / Q1) / QN ^ 2) * (2 * Q1 / Qr) * (2 * Qr / Q1) * (Q1 * Qr) := by
        gcongr
        · exact h2
        · exact h3
    _ = 48 * (Qr ^ 2 / QN ^ 2) := by field_simp; ring
    _ ≤ 48 * (2 / 2 ^ u) := by gcongr
    _ = 96 / 2 ^ u := by ring

/-- **The product of the three forms of the last Subspace application** (second case, when
`B₂ = B₃`): `|P_n(α)| |α A - B₂| |A| ≤ 96 · 2^{-u}`. -/
theorem spade_prod_three_le {j r u : ℕ} (hu : 1 ≤ u) (hur : u ≤ r)
    (hrep : ∀ m, j + 1 < m → m ≤ j + 1 + u → a (m + r) = a m) :
    |contFrac a ^ 2 * (spadeVec a j r 0 : ℝ) -
        contFrac a * ((spadeVec a j r 1 : ℝ) + spadeVec a j r 2) + spadeVec a j r 3| *
      |contFrac a * (spadeVec a j r 0 : ℝ) - spadeVec a j r 1| * |(spadeVec a j r 0 : ℝ)|
      ≤ 96 / 2 ^ u := by
  have h1 := abs_spadeL1_le ha hu hur hrep
  have h2 := abs_spadeL2_le ha j r
  have h4 := abs_spadeVec_le ha j r 0
  have hsq := contDen_sq_div_le ha (j + 1 + r) hu
  have q1 := contDen_pos_real ha (j + 1)
  have qr := contDen_pos_real ha (j + 1 + r)
  have qN := contDen_pos_real ha (j + 1 + r + u)
  have h1r : (contDen a (j + 1) : ℝ) ≤ contDen a (j + 1 + r) := contDen_mono_real ha (by omega)
  set Q1 : ℝ := (contDen a (j + 1) : ℝ)
  set Qr : ℝ := (contDen a (j + 1 + r) : ℝ)
  set QN : ℝ := (contDen a (j + 1 + r + u) : ℝ)
  calc _ ≤ (12 * (Qr / Q1) / QN ^ 2) * (2 * Q1 / Qr) * (Q1 * Qr) := by
        gcongr
        exact h2
    _ = 24 * (Q1 * Qr / QN ^ 2) := by field_simp; ring
    _ ≤ 24 * (2 * (Qr ^ 2 / QN ^ 2)) := by
        gcongr
        have hle : Q1 * Qr ≤ Qr ^ 2 := by rw [sq]; exact mul_le_mul_of_nonneg_right h1r qr.le
        have : 0 ≤ Qr ^ 2 / QN ^ 2 := by positivity
        calc Q1 * Qr / QN ^ 2 ≤ Qr ^ 2 / QN ^ 2 := by gcongr
          _ ≤ 2 * (Qr ^ 2 / QN ^ 2) := by linarith
    _ ≤ 24 * (2 * (2 / 2 ^ u)) := by gcongr
    _ = 96 / 2 ^ u := by ring

end Positive

end Nat
