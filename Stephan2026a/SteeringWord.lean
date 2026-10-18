/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Stephan2026a.NearestInt
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

-- Used only inside proofs.
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# The steering word of `(3/2)^n`

Write `(3/2)^n = mₙ + εₙ` with `mₙ = round ((3/2)^n)` and `εₙ ∈ [-1/2, 1/2)` (Definition 1.4 of
the paper). The **steering letter** is

```text
tₙ = 2 mₙ₊₁ - 3 mₙ = 3 εₙ - 2 εₙ₊₁ ∈ {-2, …, 2},        tₙ ≡ mₙ (mod 2),
```

the integer translate the map `x ↦ 3x/2` selects at step `n`, and `T = (tₙ)` is the **steering
word**. The **circuit sum** `W(a, k) = ∑_{i<k} 3^(k-1-i) 2^i t_{a+i}` (Definition 1.5) has the
exact closed form `W(a, k) = 3^k ε_a - 2^k ε_{a+k}` (Lemma 2.1): the main terms of the orbit
cancel, and every repetition statement of the paper flows from this. Everything here is
arithmetic in `ℤ` and `ℚ`.

## Main definitions

* `SteeringWord.m`, `SteeringWord.eps`: the nearest integer and the centred fractional part of
  `(3/2)^n`.
* `SteeringWord.t`: the steering letter; `SteeringWord.b`: the parity letter.
* `SteeringWord.W`: the circuit sum.

## Main results

* `SteeringWord.W_closed`, `SteeringWord.circuit_sum`: **Lemma 2.1**, in its fractional and its
  integer form.
* `SteeringWord.t_abs_le`: the alphabet has five letters.
* `SteeringWord.m_strictMono`: `m` is strictly increasing from index `2` on.
* `SteeringWord.distToNearestInt_orbit_le`: `‖(3/2)^c - (3/2)^a‖ ≤ |ε_c - ε_a|`, the bridge from
  the orbit to the kernel (K).
* `SteeringWord.one_le_two_pow_mul_distToNearestInt_orbit`: **Lemma 2.8**, the trivial repulsion
  floor `2^c ‖(3/2)^c - (3/2)^a‖ ≥ 1` for `1 ≤ a < c`.

## References

R. Stephan, *Superlinear complexity of the `(3/2)^n` steering word*, arXiv:2607.11648, §§1–2.
-/

@[expose] public section

namespace SteeringWord

/-- `m n` is the nearest integer to `(3/2)^n`; ties round up, so `eps n ∈ [-1/2, 1/2)`. -/
def m (n : ℕ) : ℤ := round ((3 / 2 : ℚ) ^ n)

/-- `eps n = (3/2)^n - m n ∈ [-1/2, 1/2)`, the centred fractional part of the orbit point. -/
def eps (n : ℕ) : ℚ := (3 / 2 : ℚ) ^ n - m n

/-- The **steering letter** `t n = 2 m (n + 1) - 3 m n`. -/
def t (n : ℕ) : ℤ := 2 * m (n + 1) - 3 * m n

/-- The **parity letter** `b n = m n % 2`; the parity word is the reduction of the steering word
modulo `2` (`SteeringWord.t_emod_two`). -/
def b (n : ℕ) : ℤ := m n % 2

/-- The **circuit sum** `W a k = ∑_{i<k} 3^(k-1-i) 2^i t (a + i)`. -/
def W (a k : ℕ) : ℤ := ∑ i ∈ Finset.range k, 3 ^ (k - 1 - i) * 2 ^ i * t (a + i)

/-! ### The centred fractional part -/

theorem neg_half_le_eps (n : ℕ) : -(1 / 2 : ℚ) ≤ eps n := by
  have h := Int.floor_le ((3 / 2 : ℚ) ^ n + 1 / 2)
  unfold eps m
  rw [round_eq]
  linarith

theorem eps_lt_half (n : ℕ) : eps n < 1 / 2 := by
  have h := Int.lt_floor_add_one ((3 / 2 : ℚ) ^ n + 1 / 2)
  unfold eps m
  rw [round_eq]
  linarith

/-- The difference of two centred fractional parts has modulus `< 1`. -/
theorem abs_eps_sub_lt_one (x y : ℕ) : |eps x - eps y| < 1 := by
  have h1 := neg_half_le_eps x
  have h2 := eps_lt_half x
  have h3 := neg_half_le_eps y
  have h4 := eps_lt_half y
  rw [abs_lt]
  constructor <;> linarith

/-! ### The steering letter -/

/-- The step recurrence `2 m (n + 1) = 3 m n + t n`. -/
theorem two_mul_m_succ (n : ℕ) : 2 * m (n + 1) = 3 * m n + t n := by
  unfold t
  ring

/-- `t n = 3 eps n - 2 eps (n + 1)`. -/
theorem t_eq_eps (n : ℕ) : (t n : ℚ) = 3 * eps n - 2 * eps (n + 1) := by
  unfold t eps
  push_cast
  rw [pow_succ]
  ring

/-- **The alphabet has five letters**: `|t n| ≤ 2`. -/
theorem t_abs_le (n : ℕ) : |t n| ≤ 2 := by
  have h1 := neg_half_le_eps n
  have h2 := eps_lt_half n
  have h3 := neg_half_le_eps (n + 1)
  have h4 := eps_lt_half (n + 1)
  have habs : |(t n : ℚ)| < 3 := by
    rw [t_eq_eps n, abs_lt]
    constructor <;> linarith
  have hz : |t n| < 3 := by exact_mod_cast habs
  omega

/-- `t n ≡ m n (mod 2)`. -/
theorem t_emod_two (n : ℕ) : t n % 2 = m n % 2 := by
  unfold t
  omega

/-! ### The circuit sum -/

theorem W_zero (a : ℕ) : W a 0 = 0 := by
  simp [W]

theorem W_succ (a k : ℕ) : W a (k + 1) = 3 * W a k + 2 ^ k * t (a + k) := by
  unfold W
  rw [Finset.sum_range_succ, show k + 1 - 1 - k = 0 by omega, pow_zero, one_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hik : i < k := Finset.mem_range.mp hi
  rw [show k + 1 - 1 - i = (k - 1 - i) + 1 by omega, pow_succ]
  ring

/-- **Lemma 2.1, fractional form**: `W a k = 3^k eps a - 2^k eps (a + k)`. -/
theorem W_closed (a k : ℕ) : (W a k : ℚ) = 3 ^ k * eps a - 2 ^ k * eps (a + k) := by
  induction k with
  | zero => simp [W_zero]
  | succ k ih =>
    rw [W_succ]
    push_cast
    rw [ih, t_eq_eps (a + k), show a + (k + 1) = (a + k) + 1 from rfl]
    ring

/-- **Lemma 2.1, integer form**: `2^k m (a + k) = 3^k m a + W a k`. -/
theorem circuit_sum (a k : ℕ) : 2 ^ k * m (a + k) = 3 ^ k * m a + W a k := by
  induction k with
  | zero => simp [W_zero]
  | succ k ih =>
    rw [show a + (k + 1) = (a + k) + 1 from rfl, W_succ]
    calc (2 : ℤ) ^ (k + 1) * m ((a + k) + 1)
        = 2 ^ k * (2 * m ((a + k) + 1)) := by ring
      _ = 2 ^ k * (3 * m (a + k) + t (a + k)) := by rw [two_mul_m_succ]
      _ = 3 * (2 ^ k * m (a + k)) + 2 ^ k * t (a + k) := by ring
      _ = 3 ^ (k + 1) * m a + (3 * W a k + 2 ^ k * t (a + k)) := by rw [ih]; ring

/-! ### Growth of `m` -/

theorem m_pos (n : ℕ) : 0 < m n := by
  have h1 : (1 : ℚ) ≤ (3 / 2 : ℚ) ^ n := one_le_pow₀ (by norm_num)
  have h2 := eps_lt_half n
  have h3 : (0 : ℚ) < m n := by
    unfold eps at h2
    linarith
  exact_mod_cast h3

/-- `2 (2^n m n) ≤ 2 · 3^n + 2^n`, a restatement of `eps n ≥ -1/2`. -/
theorem two_pow_mul_m_le (n : ℕ) : 2 * ((2 : ℤ) ^ n * m n) ≤ 2 * 3 ^ n + 2 ^ n := by
  have h := neg_half_le_eps n
  have heq : (2 : ℚ) ^ n * eps n = 3 ^ n - 2 ^ n * m n := by
    unfold eps
    rw [div_pow, mul_sub, mul_div_cancel₀ _ (by positivity)]
  have hq : 2 * ((2 : ℚ) ^ n * m n) ≤ 2 * 3 ^ n + 2 ^ n := by
    nlinarith [mul_le_mul_of_nonneg_left h (by positivity : (0 : ℚ) ≤ 2 ^ n)]
  exact_mod_cast hq

private theorem round_helper {x : ℚ} {z : ℤ} (h1 : (z : ℚ) ≤ x + 1 / 2)
    (h2 : x + 1 / 2 < z + 1) : round x = z := by
  rw [round_eq]
  exact Int.floor_eq_iff.mpr ⟨h1, by exact_mod_cast h2⟩

theorem m_zero : m 0 = 1 := round_helper (by norm_num) (by norm_num)

theorem m_one : m 1 = 2 := round_helper (by norm_num) (by norm_num)

theorem m_two : m 2 = 2 := round_helper (by norm_num) (by norm_num)

theorem m_three : m 3 = 3 := round_helper (by norm_num) (by norm_num)

theorem three_le_m {n : ℕ} (hn : 3 ≤ n) : 3 ≤ m n := by
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 3 with hk | hk
    · rw [show k = 2 by omega, m_three]
    · have h1 := ih hk
      have h2 := two_mul_m_succ k
      have ht := abs_le.mp (t_abs_le k)
      omega

theorem m_lt_m_succ {n : ℕ} (hn : 2 ≤ n) : m n < m (n + 1) := by
  rcases eq_or_lt_of_le hn with h | h
  · rw [← h, m_two, m_three]
    norm_num
  · have h1 := three_le_m h
    have h2 := two_mul_m_succ n
    have ht := abs_le.mp (t_abs_le n)
    omega

/-- `m` is strictly increasing from index `2` on. -/
theorem m_strictMono {a c : ℕ} (ha : 2 ≤ a) (hac : a < c) : m a < m c := by
  induction c with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge a k with h | h
    · exact lt_trans (ih h) (m_lt_m_succ (by omega))
    · obtain rfl : a = k := by omega
      exact m_lt_m_succ ha

/-! ### The distance to the nearest integer

The kernel (K) speaks about `‖(3/2)^c - (3/2)^a‖`. The orbit difference is `ε_c - ε_a` away from
the integer `m_c - m_a`, so `‖·‖ ≤ |ε_c - ε_a|`; and the orbit difference
`3^a (3^(c-a) - 2^(c-a)) / 2^c` has odd numerator, so `‖·‖ ≥ 2^(-c)`. -/

/-- `‖(3/2)^c - (3/2)^a‖ ≤ |eps c - eps a|`. -/
theorem distToNearestInt_orbit_le (a c : ℕ) :
    ((3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a).distToNearestInt ≤ |eps c - eps a| := by
  have h : (3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a = (eps c - eps a) + ((m c - m a : ℤ) : ℚ) := by
    unfold eps
    push_cast
    ring
  rw [h, Rat.distToNearestInt_add_intCast]
  exact Rat.distToNearestInt_le_abs _

/-- **Lemma 2.8, the trivial repulsion floor**: for `1 ≤ a < c`,
`1 ≤ 2^c ‖(3/2)^c - (3/2)^a‖`. The kernel (K) improves `2^(-c)` to `θ^c` for every `θ < 1`. -/
theorem one_le_two_pow_mul_distToNearestInt_orbit {a c : ℕ} (ha : 1 ≤ a) (hac : a < c) :
    1 ≤ 2 ^ c * ((3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a).distToNearestInt := by
  obtain ⟨s, rfl⟩ : ∃ s, c = a + s := ⟨c - a, by omega⟩
  have h3a : (3 : ℤ) ^ a % 2 = 1 := Int.odd_iff.mp (Odd.pow (by decide))
  have h3s : (3 : ℤ) ^ s % 2 = 1 := Int.odd_iff.mp (Odd.pow (by decide))
  have h2s : (2 : ℤ) ^ s % 2 = 0 := by
    obtain ⟨j, rfl⟩ : ∃ j, s = j + 1 := ⟨s - 1, by omega⟩
    rw [show (2 : ℤ) ^ (j + 1) = 2 * 2 ^ j by ring]
    exact Int.mul_emod_right 2 _
  have hOodd : ((3 : ℤ) ^ a * (3 ^ s - 2 ^ s)) % 2 = 1 := by
    have hsub : ((3 : ℤ) ^ s - 2 ^ s) % 2 = 1 := by omega
    rw [Int.mul_emod, h3a, hsub]
    norm_num
  refine Rat.one_le_two_pow_mul_distToNearestInt (by omega) hOodd ?_
  have h2 : ((2 : ℚ)) ^ (a + s) ≠ 0 := by positivity
  push_cast
  rw [div_pow, div_pow]
  field_simp
  ring

/-- The kernel quantity never vanishes. -/
theorem distToNearestInt_orbit_pos {a c : ℕ} (ha : 1 ≤ a) (hac : a < c) :
    0 < ((3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a).distToNearestInt := by
  have h := one_le_two_pow_mul_distToNearestInt_orbit ha hac
  rcases (Rat.distToNearestInt_nonneg _).lt_or_eq with h0 | h0
  · exact h0
  · rw [← h0, mul_zero] at h
    norm_num at h

end SteeringWord

/-! ### Acceptance criteria -/

/-- The sequences begin `m = 1, 2, 2, 3, …` and `t = 1, -2, 0, …`, as the paper says. -/
example : SteeringWord.t 0 = 1 ∧ SteeringWord.t 1 = -2 ∧ SteeringWord.t 2 = 0 := by
  simp [SteeringWord.t, SteeringWord.m_zero, SteeringWord.m_one, SteeringWord.m_two,
    SteeringWord.m_three]
