/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Bugeaud2013.Club
public import Bugeaud2013.Mirror
public import Bugeaud2013.Stammering

-- Used only inside proofs.
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# The estimates of §5 (Bugeaud 2013; Adamczewski–Bugeaud 2007, §7)

For lengths `w ≥ 1`, `u`, `v` with `a_{w+u+v+1+j} = a_{w+u-j}` (`j < u`), put `r = w`,
`s = w + u`, `t = w + 2u + v`, so that `a₁ … a_t = W U V Ū`, and let

`P / Q = [0; W U V Ū rev(W)]`,  `P' / Q'` the convergent before it.

The word `W U V Ū rev(W)` has the mirror image `W U rev(V) Ū rev(W)`, which begins with
`W U = a₁ … a_s`; by the mirror formula `Q' / Q` is its value. This file proves

* (5.1) `|α - P/Q| < 3 q_t⁻²`, `|α - P'/Q'| < 3 q_t⁻²` (the prefix `a₁ … a_t`);
* (5.2) `|α - Q'/Q| < 3 q_s⁻²` (the mirror image);
* (5.3) `Q ≤ 2 q_r q_t`;

and then bounds the products of the forms of the two Subspace applications by `1332 (q_r/q_s)²`
and `222 q_r / q_s`, and those by `H^{-ε}`.

## Main definitions

* `Nat.clubSeq a r t`: the word `a₁ … a_t a_r … a₁`, continued by `1`s.
* `Nat.clubVec a w u v`: the point `(Q, Q', P, P')`.

## Implementation notes

⚠ **Constants are not optimized.** The paper writes `≪`; here `3` replaces the `1` of
Adamczewski–Bugeaud's Lemma 2 (the prefix estimate is proved via an infinite completion, which
costs `2 + 1`), and the products are bounded by `1332 (q_r/q_s)²` and `222 q_r/q_s`.

⚠ **(5.3) uses the mirror symmetry of continuants.** By the tail formula,
`Q ≤ 2 q_t K(a_r, …, a₁)`, and `K(a_r, …, a₁) = q_r` (`Nat.contDen_rev`). A cruder bound such as
`K(a_r, …, a₁) ≤ 2^r q_r` would not do: the factor `4^r` can outweigh `q_s² / q_r² ≥ 2^{u-1}`.
-/

@[expose] public section

namespace Nat

variable {a : ℕ → ℕ}

/-- **The word `W U V Ū rev(W)`**: `a₁ … a_t` followed by `a_r … a₁`, then `1`s (`t = |W U V Ū|`,
`r = |W|`). -/
def clubSeq (a : ℕ → ℕ) (r t : ℕ) (i : ℕ) : ℕ :=
  if i ≤ t then a i else if i ≤ t + r then a (t + r + 1 - i) else 1

/-- **The point** `(Q, Q', P, P')` of §5, for `Q = q_N`, `P = p_N`, `Q' = q_{N-1}`,
`P' = p_{N-1}` of `W U V Ū rev(W)`, `N = 2w + 2u + v`. -/
def clubVec (a : ℕ → ℕ) (w u v : ℕ) : Fin 4 → ℤ :=
  ![contDen (clubSeq a w (w + 2 * u + v)) (2 * w + 2 * u + v),
    contDen (clubSeq a w (w + 2 * u + v)) (2 * w + 2 * u + v - 1),
    contNum (clubSeq a w (w + 2 * u + v)) (2 * w + 2 * u + v),
    contNum (clubSeq a w (w + 2 * u + v)) (2 * w + 2 * u + v - 1)]

theorem clubSeq_of_le {r t i : ℕ} (hi : i ≤ t) : clubSeq a r t i = a i := by
  simp only [clubSeq, hi, ↓reduceIte]

theorem clubSeq_of_lt {r t i : ℕ} (h1 : t < i) (h2 : i ≤ t + r) :
    clubSeq a r t i = a (t + r + 1 - i) := by
  simp only [clubSeq, show ¬ i ≤ t by omega, h2, ↓reduceIte]

/-! ### Pure inequalities -/

/-- **The product of the four forms of the first Subspace application** (§5): from (5.1)–(5.3)
and `|P'/Q' - P/Q| = 1 / (Q Q')`, the product is at most `1332 (q_r / q_s)²`. -/
theorem club_prod_four_le {α Q Q' P P' qr qs qt : ℝ} (hQ' : 0 < Q') (hQ'Q : Q' ≤ Q)
    (hqr : 0 < qr) (hrs : qr ≤ qs) (hst : qs ≤ qt)
    (h1 : |α - P / Q| ≤ 3 / qt ^ 2) (h2 : |α - P' / Q'| ≤ 3 / qt ^ 2)
    (h3 : |α - Q' / Q| ≤ 3 / qs ^ 2) (hdet : |P' / Q' - P / Q| = 1 / (Q * Q'))
    (hQle : Q ≤ 2 * qr * qt) :
    |α ^ 2 * Q - α * (Q' + P) + P'| * |α * Q' - P'| * |α * Q - Q'| * |Q'| ≤
      1332 * (qr / qs) ^ 2 := by
  have hQ : 0 < Q := lt_of_lt_of_le hQ' hQ'Q
  have hqs : 0 < qs := lt_of_lt_of_le hqr hrs
  have hqt : 0 < qt := lt_of_lt_of_le hqs hst
  have e2 : |α * Q' - P'| = Q' * |α - P' / Q'| := by
    rw [← abs_of_pos hQ', ← abs_mul, abs_of_pos hQ']; congr 1; field_simp
  have e3 : |α * Q - Q'| = Q * |α - Q' / Q| := by
    rw [← abs_of_pos hQ, ← abs_mul, abs_of_pos hQ]; congr 1; field_simp
  have e5 : α ^ 2 * Q - α * (Q' + P) + P' =
      (α * Q - Q') * (α - P / Q) + Q' * (P' / Q' - P / Q) := by
    field_simp; ring
  have b2 : |α * Q' - P'| ≤ 3 * Q / qt ^ 2 := by
    rw [e2]
    calc Q' * |α - P' / Q'| ≤ Q * (3 / qt ^ 2) :=
          mul_le_mul hQ'Q h2 (abs_nonneg _) hQ.le
      _ = 3 * Q / qt ^ 2 := by ring
  have b3 : |α * Q - Q'| ≤ 3 * Q / qs ^ 2 := by
    rw [e3]
    calc Q * |α - Q' / Q| ≤ Q * (3 / qs ^ 2) := mul_le_mul_of_nonneg_left h3 hQ.le
      _ = 3 * Q / qs ^ 2 := by ring
  have b5 : |α ^ 2 * Q - α * (Q' + P) + P'| ≤ 3 * Q / qs ^ 2 * (3 / qt ^ 2) + 1 / Q := by
    rw [e5]
    calc |(α * Q - Q') * (α - P / Q) + Q' * (P' / Q' - P / Q)|
        ≤ |(α * Q - Q') * (α - P / Q)| + |Q' * (P' / Q' - P / Q)| := abs_add_le _ _
      _ = |α * Q - Q'| * |α - P / Q| + 1 / Q := by
          rw [abs_mul, abs_mul, hdet, abs_of_pos hQ']; field_simp
      _ ≤ 3 * Q / qs ^ 2 * (3 / qt ^ 2) + 1 / Q := by gcongr
  have b4 : |Q'| ≤ Q := by rw [abs_of_pos hQ']; exact hQ'Q
  set ρ := qr / qs with hρ
  set y := Q / (qs * qt) with hy
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ ≤ 1 := by rw [hρ, div_le_one hqs]; exact hrs
  have hy0 : 0 ≤ y := by positivity
  have hyρ : y ≤ 2 * ρ := by
    rw [hy, hρ, div_le_iff₀ (by positivity)]
    calc Q ≤ 2 * qr * qt := hQle
      _ = 2 * (qr / qs) * (qs * qt) := by field_simp
  have hprod : 3 * Q / qs ^ 2 * (3 / qt ^ 2) + 1 / Q = (9 * y ^ 2 + 1) / Q := by
    rw [hy]; field_simp; ring
  calc |α ^ 2 * Q - α * (Q' + P) + P'| * |α * Q' - P'| * |α * Q - Q'| * |Q'|
      ≤ (3 * Q / qs ^ 2 * (3 / qt ^ 2) + 1 / Q) * (3 * Q / qt ^ 2) * (3 * Q / qs ^ 2) * Q := by
        gcongr
    _ = 9 * y ^ 2 * (9 * y ^ 2 + 1) := by rw [hprod, hy]; field_simp; ring
    _ ≤ 9 * (2 * ρ) ^ 2 * (9 * (2 * ρ) ^ 2 + 1) := by gcongr
    _ ≤ 1332 * ρ ^ 2 := by nlinarith [sq_nonneg ρ, mul_le_mul hρ1 hρ1 hρ0 zero_le_one]

/-- **The product of the three forms of the second Subspace application** (§5): if moreover
`Q' = P`, the product is at most `222 q_r / q_s`. -/
theorem club_prod_three_le {α Q Q' P P' qr qs qt : ℝ} (hQ' : 0 < Q') (hQ'Q : Q' ≤ Q)
    (hqr : 0 < qr) (hrs : qr ≤ qs) (hst : qs ≤ qt)
    (h1 : |α - P / Q| ≤ 3 / qt ^ 2) (h2 : |α - P' / Q'| ≤ 3 / qt ^ 2)
    (hdet : |P' / Q' - P / Q| = 1 / (Q * Q')) (hQle : Q ≤ 2 * qr * qt) (hPQ : Q' = P) :
    |α ^ 2 * Q - 2 * α * Q' + P'| * |α * Q' - P'| * |Q| ≤ 222 * (qr / qs) := by
  have hQ : 0 < Q := lt_of_lt_of_le hQ' hQ'Q
  have hqs : 0 < qs := lt_of_lt_of_le hqr hrs
  have hqt : 0 < qt := lt_of_lt_of_le hqs hst
  have e2 : |α * Q' - P'| = Q' * |α - P' / Q'| := by
    rw [← abs_of_pos hQ', ← abs_mul, abs_of_pos hQ']; congr 1; field_simp
  have e5 : α ^ 2 * Q - 2 * α * Q' + P' = Q * (α - P / Q) ^ 2 + Q' * (P' / Q' - P / Q) := by
    rw [← hPQ]; field_simp; ring
  have b2 : |α * Q' - P'| ≤ 3 * Q / qt ^ 2 := by
    rw [e2]
    calc Q' * |α - P' / Q'| ≤ Q * (3 / qt ^ 2) :=
          mul_le_mul hQ'Q h2 (abs_nonneg _) hQ.le
      _ = 3 * Q / qt ^ 2 := by ring
  have b5 : |α ^ 2 * Q - 2 * α * Q' + P'| ≤ Q * (3 / qt ^ 2) ^ 2 + 1 / Q := by
    rw [e5]
    calc |Q * (α - P / Q) ^ 2 + Q' * (P' / Q' - P / Q)|
        ≤ |Q * (α - P / Q) ^ 2| + |Q' * (P' / Q' - P / Q)| := abs_add_le _ _
      _ = Q * |α - P / Q| ^ 2 + 1 / Q := by
          rw [abs_mul, abs_mul, hdet, abs_of_pos hQ', abs_of_pos hQ, abs_pow]; field_simp
      _ ≤ Q * (3 / qt ^ 2) ^ 2 + 1 / Q := by gcongr
  set ρ := qr / qs with hρ
  set z := Q / qt ^ 2 with hz
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ ≤ 1 := by rw [hρ, div_le_one hqs]; exact hrs
  have hz0 : 0 ≤ z := by positivity
  have hzρ : z ≤ 2 * ρ := by
    rw [hz, hρ, div_le_iff₀ (by positivity)]
    have : qr * qt ≤ qr / qs * qt ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hqs]; nlinarith
    nlinarith
  calc |α ^ 2 * Q - 2 * α * Q' + P'| * |α * Q' - P'| * |Q|
      ≤ (Q * (3 / qt ^ 2) ^ 2 + 1 / Q) * (3 * Q / qt ^ 2) * Q := by
        rw [abs_of_pos hQ]; gcongr
    _ = 27 * z ^ 3 + 3 * z := by rw [hz]; field_simp; ring
    _ ≤ 27 * (2 * ρ) ^ 3 + 3 * (2 * ρ) := by gcongr
    _ ≤ 222 * ρ := by nlinarith [mul_le_mul hρ1 hρ1 hρ0 zero_le_one, mul_nonneg hρ0 hρ0]

/-- **From `X² ≤ E / 2^u` to `X ≤ H^{-ε}`**, for `H ≤ 2^m`, `m ≤ M u`, `u ≥ 2E + 14`, with
`ε = 1 / (16 (M + 1))`. -/
theorem le_rpow_of_sq_le {X H : ℝ} {E u m M : ℕ} (hX0 : 0 ≤ X) (hX : X ^ 2 ≤ E / 2 ^ u)
    (hu : 2 * E + 14 ≤ u) (hH : 0 < H) (hHm : H ≤ 2 ^ m) (hm : m ≤ M * u) :
    X ≤ H ^ (-(1 / (16 * ((M : ℝ) + 1)))) := by
  set k := u / 8 with hk
  have hk8 : 8 * k ≤ u := by omega
  have hk8' : u < 8 * k + 8 := by omega
  -- `E 4^k ≤ 2^u`
  have hE : E * 4 ^ k ≤ 2 ^ u := by
    have h1 : E ≤ 2 ^ (u - 2 * k) := (Nat.lt_two_pow_self).le.trans
      (Nat.pow_le_pow_right (by norm_num) (by omega))
    calc E * 4 ^ k = E * 2 ^ (2 * k) := by rw [pow_mul]; norm_num
      _ ≤ 2 ^ (u - 2 * k) * 2 ^ (2 * k) := Nat.mul_le_mul_right _ h1
      _ = 2 ^ u := by rw [← pow_add]; congr 1; omega
  have hX' : X ≤ (1 / 2 : ℝ) ^ k := by
    have h2 : X ^ 2 ≤ ((1 / 2 : ℝ) ^ k) ^ 2 := by
      refine hX.trans ?_
      rw [← pow_mul, div_le_iff₀ (by positivity)]
      have : ((E * 4 ^ k : ℕ) : ℝ) ≤ ((2 ^ u : ℕ) : ℝ) := by exact_mod_cast hE
      push_cast at this
      calc (E : ℝ) = E * 4 ^ k * ((1 / 2) ^ (k * 2)) := by
            rw [show k * 2 = 2 * k by ring, pow_mul, mul_assoc, ← mul_pow]; norm_num
        _ ≤ 2 ^ u * ((1 / 2) ^ (k * 2)) := by gcongr
        _ = (1 / 2) ^ (k * 2) * 2 ^ u := by ring
    exact (pow_le_pow_iff_left₀ hX0 (by positivity) two_ne_zero).mp h2
  have hε : (0 : ℝ) ≤ 1 / (16 * ((M : ℝ) + 1)) := by positivity
  have hmε : (m : ℝ) * (1 / (16 * ((M : ℝ) + 1))) ≤ k := by
    have hm' : (m : ℝ) ≤ M * u := by exact_mod_cast hm
    have hu' : (14 : ℝ) ≤ u := by exact_mod_cast (show 14 ≤ u by omega)
    have hk' : (u : ℝ) ≤ 8 * k + 7 := by exact_mod_cast (show u ≤ 8 * k + 7 by omega)
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    nlinarith
  calc X ≤ (1 / 2 : ℝ) ^ k := hX'
    _ = (2 : ℝ) ^ (-(k : ℝ)) := by
        rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow]
    _ ≤ (2 : ℝ) ^ (-((m : ℝ) * (1 / (16 * ((M : ℝ) + 1))))) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_neg hmε)
    _ ≤ H ^ (-(1 / (16 * ((M : ℝ) + 1)))) := two_rpow_neg_le hH hHm hε

/-! ### The estimates at one triple `(w, u, v)` -/

section Positive

variable (ha : ∀ n, 1 ≤ a (n + 1))
include ha

theorem clubSeq_pos (r t : ℕ) (n : ℕ) : 1 ≤ clubSeq a r t (n + 1) := by
  by_cases h1 : n + 1 ≤ t
  · rw [clubSeq_of_le h1]; exact ha n
  · by_cases h2 : n + 1 ≤ t + r
    · rw [clubSeq_of_lt (by omega) h2, show t + r + 1 - (n + 1) = (t + r - n - 1) + 1 by omega]
      exact ha _
    · simp only [clubSeq, h1, h2, ↓reduceIte, le_refl]

variable {w u v : ℕ} (hw : 1 ≤ w) (hrep : ∀ j, j < u → a (w + u + v + 1 + j) = a (w + u - j))

omit ha in
include hrep in
/-- **The mirror image of `W U V Ū rev(W)` begins with `W U`**: its letters `a_{N+1-i}`,
`N = t + r`, are `a_i` for `i ≤ s = w + u`. -/
theorem clubSeq_mirror_eq {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ w + u) :
    a i = clubSeq a w (w + 2 * u + v) (2 * w + 2 * u + v + 1 - i) := by
  by_cases hi : i ≤ w
  · rw [clubSeq_of_lt (by omega) (by omega)]
    congr 1; omega
  · rw [clubSeq_of_le (by omega)]
    have := hrep (w + u - i) (by omega)
    rw [show w + u + v + 1 + (w + u - i) = 2 * w + 2 * u + v + 1 - i by omega,
      show w + u - (w + u - i) = i by omega] at this
    exact this.symm

include hw

/-- **(5.1)**, first half: `|α - P/Q| < 3 / q_t²`. -/
theorem abs_contFrac_sub_clubVec_two_div :
    |contFrac a - (clubVec a w u v 2 : ℝ) / (clubVec a w u v 0 : ℝ)| <
      3 / (contDen a (w + 2 * u + v) : ℝ) ^ 2 := by
  have := abs_contFrac_sub_contConv_lt_three ha (c := clubSeq a w (w + 2 * u + v))
    (m := w + 2 * u + v) (N := 2 * w + 2 * u + v)
    (fun i hi _ ↦ by obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
                     exact clubSeq_pos ha _ _ n)
    (by omega) (fun i _ hi ↦ (clubSeq_of_le hi).symm)
  simpa [clubVec, contConv] using this

/-- **(5.1)**, second half: `|α - P'/Q'| < 3 / q_t²` (here `w ≥ 1` is used). -/
theorem abs_contFrac_sub_clubVec_three_div :
    |contFrac a - (clubVec a w u v 3 : ℝ) / (clubVec a w u v 1 : ℝ)| <
      3 / (contDen a (w + 2 * u + v) : ℝ) ^ 2 := by
  have := abs_contFrac_sub_contConv_lt_three ha (c := clubSeq a w (w + 2 * u + v))
    (m := w + 2 * u + v) (N := 2 * w + 2 * u + v - 1)
    (fun i hi _ ↦ by obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
                     exact clubSeq_pos ha _ _ n)
    (by omega) (fun i _ hi ↦ (clubSeq_of_le hi).symm)
  simpa [clubVec, contConv] using this

include hrep in
/-- **(5.2)** `|α - Q'/Q| < 3 / q_s²`, by the mirror formula. -/
theorem abs_contFrac_sub_clubVec_one_div :
    |contFrac a - (clubVec a w u v 1 : ℝ) / (clubVec a w u v 0 : ℝ)| <
      3 / (contDen a (w + u) : ℝ) ^ 2 := by
  obtain ⟨M, hM⟩ : ∃ M, 2 * w + 2 * u + v = M + 1 := ⟨2 * w + 2 * u + v - 1, by omega⟩
  set b := clubSeq a w (w + 2 * u + v)
  have hmir := contDen_rev_and_contNum_rev b M
  have := abs_contFrac_sub_contConv_lt_three ha (c := fun i ↦ b (M + 2 - i))
    (m := w + u) (N := M + 1)
    (fun i hi hiN ↦ by
      obtain ⟨n, hn⟩ : ∃ n, M + 2 - i = n + 1 := ⟨M + 1 - i, by omega⟩
      simp only [hn]; exact clubSeq_pos ha _ _ n)
    (by omega) (fun i h1 h2 ↦ by
      rw [show M + 2 - i = 2 * w + 2 * u + v + 1 - i by omega]
      exact clubSeq_mirror_eq hrep h1 h2)
  rw [contConv, hmir.1, hmir.2] at this
  simpa [clubVec, hM] using this

/-- **(5.3)** `Q ≤ 2 q_r q_t`. -/
theorem clubVec_zero_le :
    (clubVec a w u v 0 : ℝ) ≤ 2 * contDen a w * contDen a (w + 2 * u + v) := by
  set t := w + 2 * u + v
  set b := clubSeq a w t
  have hb : ∀ n, 1 ≤ b (n + 1) := clubSeq_pos ha w t
  obtain ⟨t', ht'⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  have hadd := contDen_add b t' w
  set tail : ℕ → ℕ := fun i ↦ b (i + (t' + 1))
  have htail : ∀ n, 1 ≤ tail (n + 1) := fun n ↦ by
    simp only [tail, show n + 1 + (t' + 1) = (n + t' + 1) + 1 by omega]; exact hb _
  have hrev : contDen tail w = contDen a w := by
    rw [← contDen_rev a w]
    refine contDen_eq_of_eqOn (m := w) (fun i h1 h2 ↦ ?_) le_rfl
    simp only [tail, b]
    rw [clubSeq_of_lt (by omega) (by omega)]
    congr 1; omega
  have hbt : contDen b (t' + 1) = contDen a t := by
    rw [← ht']; exact (contDen_eq_of_eqOn (fun i _ hi ↦ clubSeq_of_le hi) le_rfl)
  have h1 : contNum tail w ≤ contDen tail w := contNum_le_contDen htail w
  have h2 : contDen b t' ≤ contDen b (t' + 1) := contDen_le_contDen_succ hb t'
  have hN : 2 * w + 2 * u + v = t' + 1 + w := by omega
  have key : contDen b (2 * w + 2 * u + v) ≤ 2 * contDen a w * contDen a t := by
    rw [hN, hadd, hrev, hbt]
    rw [hrev] at h1
    rw [hbt] at h2
    nlinarith
  simp only [clubVec, Matrix.cons_val_zero, Int.cast_natCast]
  exact_mod_cast key

/-- The coordinates: `1 ≤ Q' ≤ Q`, `P ≤ Q`, `P' ≤ Q'`. -/
theorem clubVec_bounds :
    (1 : ℝ) ≤ clubVec a w u v 1 ∧ (clubVec a w u v 1 : ℝ) ≤ clubVec a w u v 0 ∧
      (0 : ℝ) ≤ clubVec a w u v 2 ∧ (clubVec a w u v 2 : ℝ) ≤ clubVec a w u v 0 ∧
      (0 : ℝ) ≤ clubVec a w u v 3 ∧ (clubVec a w u v 3 : ℝ) ≤ clubVec a w u v 1 := by
  set b := clubSeq a w (w + 2 * u + v)
  have hb : ∀ n, 1 ≤ b (n + 1) := clubSeq_pos ha _ _
  obtain ⟨M, hM⟩ : ∃ M, 2 * w + 2 * u + v = M + 1 := ⟨2 * w + 2 * u + v - 1, by omega⟩
  simp only [clubVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Int.cast_natCast, hM,
    Nat.add_sub_cancel]
  refine ⟨by exact_mod_cast one_le_contDen hb M, by exact_mod_cast contDen_le_contDen_succ hb M,
    by positivity, by exact_mod_cast contNum_le_contDen hb (M + 1), by positivity,
    by exact_mod_cast contNum_le_contDen hb M⟩

/-- `|P'/Q' - P/Q| = 1 / (Q Q')`. -/
theorem abs_clubVec_det :
    |(clubVec a w u v 3 : ℝ) / clubVec a w u v 1 - (clubVec a w u v 2 : ℝ) / clubVec a w u v 0| =
      1 / ((clubVec a w u v 0 : ℝ) * clubVec a w u v 1) := by
  set b := clubSeq a w (w + 2 * u + v)
  have hb : ∀ n, 1 ≤ b (n + 1) := clubSeq_pos ha _ _
  obtain ⟨M, hM⟩ : ∃ M, 2 * w + 2 * u + v = M + 1 := ⟨2 * w + 2 * u + v - 1, by omega⟩
  have hdet := contNum_mul_contDen_sub b M
  have hq0 : (0 : ℝ) < contDen b M := contDen_pos_real hb M
  have hq1 : (0 : ℝ) < contDen b (M + 1) := contDen_pos_real hb (M + 1)
  simp only [clubVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Int.cast_natCast, hM,
    Nat.add_sub_cancel]
  have hdet' : ((contNum b (M + 1) : ℝ) * contDen b M - contNum b M * contDen b (M + 1)) =
      (-1) ^ M := by exact_mod_cast hdet
  rw [div_sub_div _ _ hq0.ne' hq1.ne', abs_div, abs_of_pos (mul_pos hq0 hq1),
    show (contNum b M : ℝ) * contDen b (M + 1) - contDen b M * contNum b (M + 1) = -(-1) ^ M by
      linear_combination -hdet']
  rw [abs_neg, abs_pow, abs_neg, abs_one, one_pow, mul_comm]

end Positive

end Nat
