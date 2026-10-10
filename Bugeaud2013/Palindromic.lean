/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Bugeaud2013.Claim
public import Bugeaud2013.ClubEstimates
public import Bugeaud2013.Theorem31

-- Used only inside proofs.
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.LinearCombination

/-!
# Theorem 5.1 (Bugeaud 2013, §5): quasi-palindromic continued fractions

**Theorem 5.1**: if `(q_ℓ^{1/ℓ})` is bounded and `a₁ a₂ …` satisfies Condition `(♣)`, then
`α = [0; a₁, a₂, …]` is transcendental.

The paper only indicates the changes to the proof of Theorem 2.4 (= Theorem 3 of the arXiv
version) of Adamczewski–Bugeaud, *Palindromic continued fractions* (2007), and omits the end.
The full argument, at the point `(Q, Q', P, P')` of `ClubEstimates.lean`:

1. the four forms `αX₂ - X₄`, `αX₁ - X₂`, `X₂` and Bugeaud's `L₅ = α²X₁ - αX₂ - αX₃ + X₄` have
   product `≤ 1332 (q_r/q_s)² ≤ H^{-ε}`; the Subspace Theorem gives a non-zero rational relation
   `y₁ Q + y₂ Q' + y₃ P + y₄ P' = 0` for infinitely many `n`;
2. dividing by `Q` and letting `n → ∞` (`Q'/Q, P/Q → α`, `P'/Q → α²`) gives
   `y₁ + (y₂ + y₃) α + y₄ α² = 0`, so `y₁ = y₄ = 0`, `y₃ = -y₂ ≠ 0`, and `Q' = P` infinitely
   often;
3. along those `n`, the three forms `α²X₁ - 2αX₂ + X₃`, `αX₂ - X₃`, `X₁` at `(Q, Q', P')` have
   product `≤ 222 q_r/q_s ≤ H^{-ε}`; the Subspace Theorem gives `z₁ Q + z₂ Q' + z₃ P' = 0`
   infinitely often, and the limit `z₁ + z₂ α + z₃ α² = 0` contradicts `deg α ≥ 3`.

## Main results

* `Nat.exists_club_relation`, `Nat.exists_club_relation_three`: the two Subspace applications.
* `Nat.club_limit`: the limit of a relation at the points `(Q, Q', P, P')`.
* `Nat.transcendental_contFrac_of_isClub`: **Theorem 5.1**.

## Implementation notes

⚠ **Step 3 is where the paper says "we omit the details".** It is the end of the proof of
Theorem 2 of Adamczewski–Bugeaud, which works verbatim: no third application is needed, as the
limit of the relation is already a quadratic equation for `α`.

⚠ **Bugeaud's `L₅` replaces Adamczewski–Bugeaud's `L₁ = αX₁ - X₃`.** With `L₁` the product is
`≪ q_r⁴ q_s⁻²`, which needs `q_s ≥ q_r^{2+η}` (their condition (2.1)); with `L₅` it is
`≪ q_r² q_s⁻²`, and `q_s² / q_r² ≥ 2^{u-1}` holds for every `w`. This is the improvement of
Theorem 5.1 over [5, Theorem 2.4].
-/

@[expose] public section

open Filter

namespace Nat

variable {a : ℕ → ℕ}

/-! ### The forms -/

/-- The coefficients of the four forms of the first application are algebraic. -/
theorem isAlgebraic_formsClubFour {α : ℝ} (halg : IsAlgebraic ℚ α) :
    ∀ i k, IsAlgebraic ℚ ((![![α ^ 2, -α, -α, 1], ![0, α, 0, -1], ![α, -1, 0, 0],
      ![0, 1, 0, 0]] : Fin 4 → Fin 4 → ℝ) i k) := by
  intro i k
  fin_cases i <;> fin_cases k <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons] <;>
    first
    | exact halg
    | exact halg.neg
    | exact halg.pow 2
    | exact isAlgebraic_zero
    | exact isAlgebraic_one
    | exact isAlgebraic_one.neg

/-- The four forms of the first application are linearly independent. -/
theorem linearIndependent_formsClubFour {α : ℝ} (hα : α ≠ 0) :
    LinearIndependent ℝ (![![α ^ 2, -α, -α, 1], ![0, α, 0, -1], ![α, -1, 0, 0],
      ![0, 1, 0, 0]] : Fin 4 → Fin 4 → ℝ) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h (k : Fin 4) := congrFun hg k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply] at h
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2 h3
  have e0 : g 0 = 0 := by
    have : g 0 * α = 0 := by linear_combination -h2
    exact (_root_.mul_eq_zero.mp this).resolve_right hα
  have e1 : g 1 = 0 := by linear_combination e0 - h3
  have e2 : g 2 = 0 := by
    have : g 2 * α = 0 := by linear_combination h0 - α ^ 2 * e0
    exact (_root_.mul_eq_zero.mp this).resolve_right hα
  have e3 : g 3 = 0 := by linear_combination h1 + α * e0 - α * e1 + e2
  intro i
  fin_cases i
  exacts [e0, e1, e2, e3]

theorem prod_formsClubFour (α : ℝ) (x : Fin 4 → ℝ) :
    (∏ i, |∑ k, (![![α ^ 2, -α, -α, 1], ![0, α, 0, -1], ![α, -1, 0, 0], ![0, 1, 0, 0]] :
      Fin 4 → Fin 4 → ℝ) i k * x k|) =
      |α ^ 2 * x 0 - α * (x 1 + x 2) + x 3| * |α * x 1 - x 3| * |α * x 0 - x 1| * |x 1| := by
  simp only [Fin.prod_univ_four, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring_nf

/-- The coefficients of the three forms of the second application are algebraic. -/
theorem isAlgebraic_formsClubThree {α : ℝ} (halg : IsAlgebraic ℚ α) :
    ∀ i k, IsAlgebraic ℚ ((![![α ^ 2, -(2 * α), 1], ![0, α, -1], ![1, 0, 0]] :
      Fin 3 → Fin 3 → ℝ) i k) := by
  have h2 : IsAlgebraic ℚ (2 * α) := by
    simpa using (isAlgebraic_ratCast 2).mul halg
  intro i k
  fin_cases i <;> fin_cases k <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
    first
    | exact halg
    | exact h2.neg
    | exact halg.pow 2
    | exact isAlgebraic_zero
    | exact isAlgebraic_one
    | exact isAlgebraic_one.neg

/-- The three forms of the second application are linearly independent. -/
theorem linearIndependent_formsClubThree {α : ℝ} (hα : α ≠ 0) :
    LinearIndependent ℝ (![![α ^ 2, -(2 * α), 1], ![0, α, -1], ![1, 0, 0]] :
      Fin 3 → Fin 3 → ℝ) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h (k : Fin 3) := congrFun hg k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply] at h
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  have e0 : g 0 = 0 := by
    have : g 0 * α = 0 := by linear_combination -h1 - α * h2
    exact (_root_.mul_eq_zero.mp this).resolve_right hα
  have e1 : g 1 = 0 := by linear_combination -h2 + e0
  have e2 : g 2 = 0 := by linear_combination h0 - α ^ 2 * e0
  intro i
  fin_cases i
  exacts [e0, e1, e2]

theorem prod_formsClubThree (α : ℝ) (x : Fin 3 → ℝ) :
    (∏ i, |∑ k, (![![α ^ 2, -(2 * α), 1], ![0, α, -1], ![1, 0, 0]] :
      Fin 3 → Fin 3 → ℝ) i k * x k|) =
      |α ^ 2 * x 0 - 2 * α * x 1 + x 2| * |α * x 1 - x 2| * |x 0| := by
  simp only [Fin.prod_univ_three, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring_nf

section Positive

variable (ha : ∀ n, 1 ≤ a (n + 1))
include ha

/-! ### The bound `H^{-ε}` -/

/-- **The bound feeding the Subspace Theorem.** If `X ≤ 1332 q_w / q_{w+u}`, `u` is large,
`w + v ≤ C u` and `0 < H ≤ Q`, then `X ≤ H^{-ε}` with `ε = 1 / (16 (M + 1))`,
`M = 2 K (C + 1) + 1`, where `q_ℓ ≤ 2^{K ℓ}`. -/
theorem le_rpow_club {K C : ℕ} (hK : ∀ ℓ, (contDen a ℓ : ℝ) ≤ 2 ^ (K * ℓ)) {w u v : ℕ}
    (hw : 1 ≤ w) (hu : 2 * 3548448 + 14 ≤ u) (hC : w + v ≤ C * u) {X H : ℝ} (hX0 : 0 ≤ X)
    (hX : X ≤ 1332 * (contDen a w / contDen a (w + u))) (hH : 0 < H)
    (hHQ : H ≤ clubVec a w u v 0) :
    X ≤ H ^ (-(1 / (16 * (((2 * K * (C + 1) + 1 : ℕ) : ℝ) + 1)))) := by
  have hqw : (0 : ℝ) < contDen a w := contDen_pos_real ha w
  have hqs : (0 : ℝ) < contDen a (w + u) := contDen_pos_real ha (w + u)
  set ρ := (contDen a w : ℝ) / contDen a (w + u) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  -- `ρ² ≤ 2 / 2^u`, by (2.3)
  have hρ2 : ρ ^ 2 ≤ 2 / 2 ^ u := by
    have h := contDen_sq_mul_two_pow_le ha w (u - 1)
    rw [show w + (u - 1) + 1 = w + u by omega] at h
    have h' : (contDen a w : ℝ) ^ 2 * 2 ^ (u - 1) ≤ (contDen a (w + u) : ℝ) ^ 2 := by
      exact_mod_cast h
    rw [hρ, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    calc (contDen a w : ℝ) ^ 2 * 2 ^ u = 2 * ((contDen a w : ℝ) ^ 2 * 2 ^ (u - 1)) := by
          rw [show u = u - 1 + 1 by omega, pow_succ]; simp only [Nat.add_sub_cancel]; ring
      _ ≤ 2 * (contDen a (w + u) : ℝ) ^ 2 := by gcongr
  have hX2 : X ^ 2 ≤ ((3548448 : ℕ) : ℝ) / 2 ^ u := by
    calc X ^ 2 ≤ (1332 * ρ) ^ 2 := pow_le_pow_left₀ hX0 hX 2
      _ = 1332 ^ 2 * ρ ^ 2 := by ring
      _ ≤ 1332 ^ 2 * (2 / 2 ^ u) := by gcongr
      _ = ((3548448 : ℕ) : ℝ) / 2 ^ u := by push_cast; ring
  -- the height: `Q ≤ 2 q_w q_t ≤ 2^{1 + K (w + t)}`
  set t := w + 2 * u + v
  have hHm : H ≤ 2 ^ (1 + K * w + K * t) := by
    calc H ≤ clubVec a w u v 0 := hHQ
      _ ≤ 2 * contDen a w * contDen a t := clubVec_zero_le ha hw
      _ ≤ 2 * 2 ^ (K * w) * 2 ^ (K * t) := by
          gcongr
          · exact hK w
          · exact hK t
      _ = 2 ^ (1 + K * w + K * t) := by rw [pow_add, pow_add, pow_one]
  have hm : 1 + K * w + K * t ≤ (2 * K * (C + 1) + 1) * u := by
    have h1 : w + t ≤ 2 * (C + 1) * u := by
      have : 2 * (C + 1) * u = 2 * (C * u) + 2 * u := by ring
      omega
    have h2 : K * (w + t) ≤ K * (2 * (C + 1) * u) := Nat.mul_le_mul_left K h1
    have h3 : (2 * K * (C + 1) + 1) * u = K * (2 * (C + 1) * u) + u := by ring
    have h4 : K * (w + t) = K * w + K * t := by ring
    omega
  exact le_rpow_of_sq_le hX0 hX2 (by omega) hH hHm hm

/-- The product of the four forms at `(Q, Q', P, P')` is at most `1332 q_w / q_{w+u}`. -/
theorem prod_formsClubFour_clubVec_le {w u v : ℕ} (hw : 1 ≤ w)
    (hrep : ∀ j, j < u → a (w + u + v + 1 + j) = a (w + u - j)) :
    (∏ i, |∑ k, (![![contFrac a ^ 2, -contFrac a, -contFrac a, 1], ![0, contFrac a, 0, -1],
      ![contFrac a, -1, 0, 0], ![0, 1, 0, 0]] : Fin 4 → Fin 4 → ℝ) i k *
        (clubVec a w u v k : ℝ)|) ≤ 1332 * (contDen a w / contDen a (w + u)) := by
  obtain ⟨hQ'1, hQ'Q, -, -, -, -⟩ := clubVec_bounds ha hw (u := u) (v := v)
  have hqw : (0 : ℝ) < contDen a w := contDen_pos_real ha w
  have hrs : (contDen a w : ℝ) ≤ contDen a (w + u) := contDen_mono_real ha (by omega)
  have hρ1 : (contDen a w : ℝ) / contDen a (w + u) ≤ 1 :=
    (div_le_one (contDen_pos_real ha _)).mpr hrs
  rw [prod_formsClubFour]
  refine (club_prod_four_le (by linarith) hQ'Q hqw hrs (contDen_mono_real ha (by omega))
    (abs_contFrac_sub_clubVec_two_div ha hw).le (abs_contFrac_sub_clubVec_three_div ha hw).le
    (abs_contFrac_sub_clubVec_one_div ha hw hrep).le (abs_clubVec_det ha hw)
    (clubVec_zero_le ha hw)).trans ?_
  have h0 : 0 ≤ (contDen a w : ℝ) / contDen a (w + u) := by positivity
  nlinarith

/-- The product of the three forms at `(Q, Q', P')`, when `Q' = P`, is at most
`1332 q_w / q_{w+u}`. -/
theorem prod_formsClubThree_clubVec_le {w u v : ℕ} (hw : 1 ≤ w)
    (hP : clubVec a w u v 1 = clubVec a w u v 2) :
    (∏ i, |∑ k, (![![contFrac a ^ 2, -(2 * contFrac a), 1], ![0, contFrac a, -1], ![1, 0, 0]] :
      Fin 3 → Fin 3 → ℝ) i k *
        (![clubVec a w u v 0, clubVec a w u v 1, clubVec a w u v 3] k : ℝ)|) ≤
      1332 * (contDen a w / contDen a (w + u)) := by
  obtain ⟨hQ'1, hQ'Q, -, -, -, -⟩ := clubVec_bounds ha hw (u := u) (v := v)
  have hqw : (0 : ℝ) < contDen a w := contDen_pos_real ha w
  have hrs : (contDen a w : ℝ) ≤ contDen a (w + u) := contDen_mono_real ha (by omega)
  rw [prod_formsClubThree]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  refine (club_prod_three_le (by linarith) hQ'Q hqw hrs (contDen_mono_real ha (by omega))
    (abs_contFrac_sub_clubVec_two_div ha hw).le (abs_contFrac_sub_clubVec_three_div ha hw).le
    (abs_clubVec_det ha hw) (clubVec_zero_le ha hw) (by exact_mod_cast hP)).trans ?_
  have h0 : 0 ≤ (contDen a w : ℝ) / contDen a (w + u) := by positivity
  nlinarith

/-! ### The Subspace applications and the limit -/

variable {w u v : ℕ → ℕ} {C : ℕ}

/-- **The first Subspace application** (§5): a non-zero rational relation
`y · (Q, Q', P, P') = 0` holds for infinitely many `n`. -/
theorem exists_club_relation (halg : IsAlgebraic ℚ (contFrac a)) {K : ℕ}
    (hK : ∀ ℓ, (contDen a ℓ : ℝ) ≤ 2 ^ (K * ℓ)) (hd : ClubData a w u v C) :
    ∃ y : Fin 4 → ℚ, y ≠ 0 ∧ ∃ᶠ n in atTop,
      ∑ i, (y i : ℝ) * (clubVec a (w n) (u n) (v n) i : ℝ) = 0 := by
  refine Real.exists_ne_zero_frequently_sum_eq_zero (isAlgebraic_formsClubFour halg)
    (linearIndependent_formsClubFour (contFrac_pos ha).ne')
    (ε := 1 / (16 * (((2 * K * (C + 1) + 1 : ℕ) : ℝ) + 1))) (by positivity) _ ?_
  filter_upwards [hd.tendsto.eventually_ge_atTop (2 * 3548448 + 14)] with n hn
  have hw := hd.one_le n
  obtain ⟨hQ'1, hQ'Q, hP0, hPQ, hP'0, hP'Q'⟩ := clubVec_bounds ha hw (u := u n) (v := v n)
  have hle : ∀ i, |(clubVec a (w n) (u n) (v n) i : ℝ)| ≤ clubVec a (w n) (u n) (v n) 0 := by
    intro i
    fin_cases i
    · change |(clubVec a (w n) (u n) (v n) 0 : ℝ)| ≤ _
      exact (abs_of_nonneg (by linarith)).le
    · change |(clubVec a (w n) (u n) (v n) 1 : ℝ)| ≤ _
      rw [abs_of_nonneg (by linarith)]; exact hQ'Q
    · change |(clubVec a (w n) (u n) (v n) 2 : ℝ)| ≤ _
      rw [abs_of_nonneg hP0]; exact hPQ
    · change |(clubVec a (w n) (u n) (v n) 3 : ℝ)| ≤ _
      rw [abs_of_nonneg hP'0]; linarith
  have hH1 : (1 : ℝ) ≤ ⨆ i, |(clubVec a (w n) (u n) (v n) i : ℝ)| :=
    le_trans (by rw [abs_of_nonneg (by linarith)]; exact hQ'1)
      (le_ciSup (f := fun i ↦ |(clubVec a (w n) (u n) (v n) i : ℝ)|)
        (Set.finite_range _).bddAbove 1)
  refine ⟨fun h ↦ ?_, ?_⟩
  · have : (clubVec a (w n) (u n) (v n) 1 : ℝ) = 0 := by rw [h]; simp
    linarith
  · refine le_rpow_club ha hK hw hn (hd.le n) (by positivity)
      (prod_formsClubFour_clubVec_le ha hw (hd.rep n)) (by linarith) (ciSup_le hle)

/-- **The second Subspace application** (§5): if `Q' = P` at every point, a non-zero rational
relation `z · (Q, Q', P') = 0` holds for infinitely many `n`. -/
theorem exists_club_relation_three (halg : IsAlgebraic ℚ (contFrac a)) {K : ℕ}
    (hK : ∀ ℓ, (contDen a ℓ : ℝ) ≤ 2 ^ (K * ℓ)) (hd : ClubData a w u v C)
    (hP : ∀ n, clubVec a (w n) (u n) (v n) 1 = clubVec a (w n) (u n) (v n) 2) :
    ∃ z : Fin 3 → ℚ, z ≠ 0 ∧ ∃ᶠ n in atTop,
      (z 0 : ℝ) * (clubVec a (w n) (u n) (v n) 0 : ℝ) +
        z 1 * (clubVec a (w n) (u n) (v n) 1 : ℝ) +
        z 2 * (clubVec a (w n) (u n) (v n) 3 : ℝ) = 0 := by
  set X : ℕ → Fin 3 → ℤ := fun n ↦ ![clubVec a (w n) (u n) (v n) 0,
    clubVec a (w n) (u n) (v n) 1, clubVec a (w n) (u n) (v n) 3]
  suffices h : ∃ z : Fin 3 → ℚ, z ≠ 0 ∧ ∃ᶠ n in atTop, ∑ i, (z i : ℝ) * (X n i : ℝ) = 0 by
    obtain ⟨z, hz, hrel⟩ := h
    refine ⟨z, hz, hrel.mono fun n hn ↦ ?_⟩
    simp only [Fin.sum_univ_three, X, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hn
    exact hn
  refine Real.exists_ne_zero_frequently_sum_eq_zero
    (isAlgebraic_formsClubThree halg) (linearIndependent_formsClubThree (contFrac_pos ha).ne')
    (ε := 1 / (16 * (((2 * K * (C + 1) + 1 : ℕ) : ℝ) + 1))) (by positivity) X ?_
  filter_upwards [hd.tendsto.eventually_ge_atTop (2 * 3548448 + 14)] with n hn
  have hw := hd.one_le n
  obtain ⟨hQ'1, hQ'Q, -, -, hP'0, hP'Q'⟩ := clubVec_bounds ha hw (u := u n) (v := v n)
  have hle : ∀ i, |(X n i : ℝ)| ≤ clubVec a (w n) (u n) (v n) 0 := by
    intro i
    fin_cases i
    · exact (abs_of_nonneg (by simp only [X]; push_cast; linarith)).le
    · simp only [X]; rw [abs_of_nonneg (by push_cast; linarith)]; exact_mod_cast hQ'Q
    · simp only [X]; rw [abs_of_nonneg (by push_cast; linarith)]; push_cast; linarith
  have hX1 : (X n 1 : ℝ) = clubVec a (w n) (u n) (v n) 1 := rfl
  have hH1 : (1 : ℝ) ≤ ⨆ i, |(X n i : ℝ)| :=
    le_trans (by rw [hX1, abs_of_nonneg (by linarith)]; exact hQ'1)
      (le_ciSup (f := fun i ↦ |(X n i : ℝ)|) (Set.finite_range _).bddAbove 1)
  refine ⟨fun h ↦ ?_, ?_⟩
  · have : (X n 1 : ℝ) = 0 := by rw [h]; simp
    linarith
  · exact le_rpow_club ha hK hw hn (hd.le n) (by positivity)
      (prod_formsClubThree_clubVec_le ha hw (hP n)) (by linarith) (ciSup_le hle)

/-- **The limit of a relation** (§5): if `y₁ Q + y₂ Q' + y₃ P + y₄ P' = 0` for infinitely many
`n`, then `y₁ + (y₂ + y₃) α + y₄ α² = 0`, as `Q'/Q, P/Q → α` and `P'/Q → α²`. -/
theorem club_limit (hd : ClubData a w u v C) {y0 y1 y2 y3 : ℝ}
    (h : ∃ᶠ n in atTop, y0 * (clubVec a (w n) (u n) (v n) 0 : ℝ) +
      y1 * (clubVec a (w n) (u n) (v n) 1 : ℝ) + y2 * (clubVec a (w n) (u n) (v n) 2 : ℝ) +
      y3 * (clubVec a (w n) (u n) (v n) 3 : ℝ) = 0) :
    y0 + (y1 + y2) * contFrac a + y3 * contFrac a ^ 2 = 0 := by
  set α := contFrac a
  have hα0 := contFrac_pos ha
  have hα1 := contFrac_lt_one ha
  have hs : Tendsto (fun n ↦ w n + u n) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ Nat.le_add_left _ _) hd.tendsto
  refine eq_zero_of_frequently_abs_le_div (tendsto_contDen_comp ha hs)
    (L := 3 * |y1| + 3 * |y2| + 6 * |y3|) (h.mono fun n hn ↦ ?_)
  have hw := hd.one_le n
  obtain ⟨hQ'1, hQ'Q, -, -, -, -⟩ := clubVec_bounds ha hw (u := u n) (v := v n)
  set Q := (clubVec a (w n) (u n) (v n) 0 : ℝ)
  set Q' := (clubVec a (w n) (u n) (v n) 1 : ℝ)
  set P := (clubVec a (w n) (u n) (v n) 2 : ℝ)
  set P' := (clubVec a (w n) (u n) (v n) 3 : ℝ)
  have hQ : 0 < Q := by linarith
  have hQ' : 0 < Q' := by linarith
  have hqs : (1 : ℝ) ≤ contDen a (w n + u n) := by exact_mod_cast one_le_contDen ha _
  set qs := (contDen a (w n + u n) : ℝ)
  have hst : qs ≤ contDen a (w n + 2 * u n + v n) := contDen_mono_real ha (by omega)
  have h1 := (abs_contFrac_sub_clubVec_two_div ha hw (u := u n) (v := v n)).le
  have h2 := (abs_contFrac_sub_clubVec_three_div ha hw (u := u n) (v := v n)).le
  have h3 := (abs_contFrac_sub_clubVec_one_div ha hw (hd.rep n)).le
  have hqt2 : 3 / (contDen a (w n + 2 * u n + v n) : ℝ) ^ 2 ≤ 3 / qs ^ 2 := by gcongr
  -- the three errors, multiplied by `Q`
  have e1 : |α * Q - Q'| ≤ 3 * Q / qs ^ 2 := by
    rw [show α * Q - Q' = Q * (α - Q' / Q) by field_simp, abs_mul, abs_of_pos hQ]
    calc Q * |α - Q' / Q| ≤ Q * (3 / qs ^ 2) := by gcongr
      _ = 3 * Q / qs ^ 2 := by ring
  have e2 : |α * Q - P| ≤ 3 * Q / qs ^ 2 := by
    rw [show α * Q - P = Q * (α - P / Q) by field_simp, abs_mul, abs_of_pos hQ]
    calc Q * |α - P / Q| ≤ Q * (3 / qs ^ 2) := by gcongr; exact h1.trans hqt2
      _ = 3 * Q / qs ^ 2 := by ring
  have e3 : |α ^ 2 * Q - P'| ≤ 6 * Q / qs ^ 2 := by
    rw [show α ^ 2 * Q - P' = α * (α * Q - Q') + Q' * (α - P' / Q') by field_simp; ring]
    calc |α * (α * Q - Q') + Q' * (α - P' / Q')|
        ≤ |α * (α * Q - Q')| + |Q' * (α - P' / Q')| := abs_add_le _ _
      _ = α * |α * Q - Q'| + Q' * |α - P' / Q'| := by
          rw [abs_mul, abs_mul, abs_of_pos hα0, abs_of_pos hQ']
      _ ≤ 1 * (3 * Q / qs ^ 2) + Q * (3 / qs ^ 2) := by
          gcongr
          · exact h2.trans hqt2
      _ = 6 * Q / qs ^ 2 := by ring
  -- `c Q` is a combination of the errors
  have hc : (y0 + (y1 + y2) * α + y3 * α ^ 2) * Q =
      y1 * (α * Q - Q') + y2 * (α * Q - P) + y3 * (α ^ 2 * Q - P') := by
    linear_combination hn
  have hcQ : |y0 + (y1 + y2) * α + y3 * α ^ 2| * Q ≤
      (3 * |y1| + 3 * |y2| + 6 * |y3|) * Q / qs ^ 2 := by
    rw [← abs_of_pos hQ, ← abs_mul, hc, abs_of_pos hQ]
    calc |y1 * (α * Q - Q') + y2 * (α * Q - P) + y3 * (α ^ 2 * Q - P')|
        ≤ |y1| * |α * Q - Q'| + |y2| * |α * Q - P| + |y3| * |α ^ 2 * Q - P'| := by
          rw [← abs_mul, ← abs_mul, ← abs_mul]
          exact (abs_add_le _ _).trans (_root_.add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ |y1| * (3 * Q / qs ^ 2) + |y2| * (3 * Q / qs ^ 2) + |y3| * (6 * Q / qs ^ 2) := by
          gcongr
      _ = (3 * |y1| + 3 * |y2| + 6 * |y3|) * Q / qs ^ 2 := by ring
  have hL : 0 ≤ 3 * |y1| + 3 * |y2| + 6 * |y3| := by positivity
  rw [mul_div_right_comm] at hcQ
  have hc' := le_of_mul_le_mul_right hcQ hQ
  calc |y0 + (y1 + y2) * α + y3 * α ^ 2| ≤ (3 * |y1| + 3 * |y2| + 6 * |y3|) / qs ^ 2 := hc'
    _ ≤ (3 * |y1| + 3 * |y2| + 6 * |y3|) / qs := by
        gcongr
        nlinarith

/-! ### Theorem 5.1 -/

/-- **The core of the proof of Theorem 5.1.** If `α = [0; a₁, a₂, …]` is algebraic, satisfies
no non-trivial rational equation of degree at most `2`, and `q_ℓ ≤ 2^{K ℓ}`, then the
normalized lengths of Condition `(♣)` cannot exist. -/
theorem false_of_clubData (halg : IsAlgebraic ℚ (contFrac a))
    (hq : ∀ A B C : ℚ, (A : ℝ) * contFrac a ^ 2 + B * contFrac a + C = 0 →
      A = 0 ∧ B = 0 ∧ C = 0)
    {K : ℕ} (hK : ∀ ℓ, (contDen a ℓ : ℝ) ≤ 2 ^ (K * ℓ)) (hd : ClubData a w u v C) : False := by
  obtain ⟨y, hy0, hrel⟩ := exists_club_relation ha halg hK hd
  -- the limit: `y₀ + (y₁ + y₂) α + y₃ α² = 0`, so `y₀ = y₃ = 0` and `y₂ = -y₁`
  have hS := club_limit ha hd (y0 := y 0) (y1 := y 1) (y2 := y 2) (y3 := y 3)
    (hrel.mono fun n hn ↦ by rw [Fin.sum_univ_four] at hn; exact hn)
  obtain ⟨h3, h12, h0⟩ := hq (y 3) (y 1 + y 2) (y 0) (by push_cast; linear_combination hS)
  have hy1 : y 1 ≠ 0 := by
    intro h1
    have h2 : y 2 = 0 := by rw [h1, zero_add] at h12; exact h12
    exact hy0 (funext fun i ↦ by fin_cases i <;> assumption)
  -- hence `Q' = P` along the relation
  have hP : ∀ n, ∑ i, (y i : ℝ) * (clubVec a (w n) (u n) (v n) i : ℝ) = 0 →
      clubVec a (w n) (u n) (v n) 1 = clubVec a (w n) (u n) (v n) 2 := by
    intro n h
    rw [Fin.sum_univ_four, h0, h3, show y 2 = -y 1 by linarith [h12]] at h
    push_cast at h
    have hy1' : (y 1 : ℝ) ≠ 0 := by exact_mod_cast hy1
    have : (y 1 : ℝ) * ((clubVec a (w n) (u n) (v n) 1 : ℝ) -
        clubVec a (w n) (u n) (v n) 2) = 0 := by linear_combination h
    have := (_root_.mul_eq_zero.mp this).resolve_left hy1'
    exact_mod_cast sub_eq_zero.mp this
  obtain ⟨g, hg, hgP⟩ := extraction_of_frequently_atTop hrel
  have hd' := hd.comp hg
  -- the second application and the limit again
  obtain ⟨z, hz0, hzrel⟩ := exists_club_relation_three ha halg hK hd' fun n ↦ hP (g n) (hgP n)
  have hT := club_limit ha hd' (y0 := z 0) (y1 := z 1) (y2 := 0) (y3 := z 2)
    (hzrel.mono fun n hn ↦ by linear_combination hn)
  obtain ⟨g2, g1, g0⟩ := hq (z 2) (z 1) (z 0) (by linear_combination hT)
  exact hz0 (funext fun i ↦ by fin_cases i <;> assumption)

/-- **Bugeaud 2013, Theorem 5.1.** Let `a₁, a₂, …` be positive integers with `(q_ℓ^{1/ℓ})`
bounded. If `(a_ℓ)_{ℓ ≥ 1}` satisfies Condition `(♣)`, then `[0; a₁, a₂, …]` is transcendental. -/
theorem transcendental_contFrac_of_isClub
    (hq : BddAbove (Set.range fun ℓ : ℕ ↦ (contDen a ℓ : ℝ) ^ (1 / (ℓ : ℝ))))
    (hs : Function.IsClub fun k ↦ a (k + 1)) : Transcendental ℚ (contFrac a) := by
  intro halg
  obtain ⟨hnp, hrep⟩ := hs
  obtain ⟨w, u, v, C, hd⟩ := exists_clubData hrep
  obtain ⟨K, hK⟩ := exists_contDen_le_two_pow hq
  refine false_of_clubData ha halg (fun A B C h ↦ ?_) hK hd
  by_contra hne
  exact hnp (isEventuallyPeriodic_of_quadratic ha hne h)

end Positive

end Nat
