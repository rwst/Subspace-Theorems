/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Stephan2026a.SteeringWord
public import DiophantineApproximation.StammeringWords

-- Used only inside proofs.
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination

/-!
# The repetition identity

A **repetition** of length `k` at positions `a < c` is an equality of factors of the steering
word, `t (a + i) = t (c + i)` for `i < k` (Definition 2.2). Occurrences may overlap, and nothing
anchors them to a prefix: the dynamics is autonomous. Equal factors accumulate equal circuit
sums, so the closed form of Lemma 2.1 turns every repetition into **the repetition identity**
(Theorem 2.3)

```text
3^k (ε_c - ε_a) = 2^k (ε_{c+k} - ε_{a+k}),        3^k (m_c - m_a) = 2^k (m_{c+k} - m_{a+k}),
```

whose shadows drive the whole paper: the divisibility `2^k ∣ m_c - m_a` (Corollary 2.4), the
growth ceiling `2^(k+c+1) ≤ 3^(c+1)` once `m` is increasing (Proposition 2.5), and the
contraction `|ε_c - ε_a| ≤ (2/3)^k` (Lemma 2.7), the interface to the kernel (K).

## Main definitions

* `SteeringWord.IsRepetition a c k`: a factor of length `k` occurs at `a` and at `c`.

## Main results

* `SteeringWord.lemmaR_int`, `SteeringWord.lemmaR_eps`: **Theorem 2.3**.
* `SteeringWord.two_pow_dvd_of_repetition`, `SteeringWord.three_pow_dvd_of_repetition`:
  **Corollary 2.4**.
* `SteeringWord.repetition_pow_le`: **Proposition 2.5**, the growth ceiling.
* `SteeringWord.abs_eps_sub_le_of_repetition`: **Lemma 2.7**, the contraction.
* `SteeringWord.not_isEventuallyPeriodic`: **Theorem 2.9**, `T` is not eventually periodic.

## References

R. Stephan, *Superlinear complexity of the `(3/2)^n` steering word*, arXiv:2607.11648, §2.
-/

@[expose] public section

namespace SteeringWord

/-- A factor of length `k` of the steering word occurs at positions `a` and `c`. -/
def IsRepetition (a c k : ℕ) : Prop := ∀ i < k, t (a + i) = t (c + i)

/-- Equal factors accumulate equal circuit sums. -/
theorem W_eq_of_repetition {a c k : ℕ} (h : IsRepetition a c k) : W a k = W c k :=
  Finset.sum_congr rfl fun i hi ↦ by rw [h i (Finset.mem_range.mp hi)]

/-- **Theorem 2.3, integer form**: `3^k (m c - m a) = 2^k (m (c + k) - m (a + k))`. -/
theorem lemmaR_int {a c k : ℕ} (h : IsRepetition a c k) :
    3 ^ k * (m c - m a) = 2 ^ k * (m (c + k) - m (a + k)) := by
  linear_combination circuit_sum a k - circuit_sum c k + W_eq_of_repetition h

/-- **Theorem 2.3, fractional form**: `3^k (eps c - eps a) = 2^k (eps (c + k) - eps (a + k))`. -/
theorem lemmaR_eps {a c k : ℕ} (h : IsRepetition a c k) :
    (3 : ℚ) ^ k * (eps c - eps a) = 2 ^ k * (eps (c + k) - eps (a + k)) := by
  have hw : (W a k : ℚ) = W c k := by exact_mod_cast W_eq_of_repetition h
  linear_combination W_closed a k - W_closed c k - hw

private theorem isCoprime_two_pow_three_pow (k : ℕ) : IsCoprime ((2 : ℤ) ^ k) ((3 : ℤ) ^ k) :=
  IsCoprime.pow (Int.isCoprime_iff_gcd_eq_one.mpr (by decide))

/-- **Corollary 2.4**: `2^k ∣ m c - m a`. -/
theorem two_pow_dvd_of_repetition {a c k : ℕ} (h : IsRepetition a c k) :
    (2 : ℤ) ^ k ∣ m c - m a := by
  have hdvd : (2 : ℤ) ^ k ∣ 3 ^ k * (m c - m a) := by
    rw [lemmaR_int h]
    exact Dvd.intro _ rfl
  exact (isCoprime_two_pow_three_pow k).dvd_of_dvd_mul_left hdvd

/-- **Corollary 2.4**: `3^k ∣ m (c + k) - m (a + k)`. -/
theorem three_pow_dvd_of_repetition {a c k : ℕ} (h : IsRepetition a c k) :
    (3 : ℤ) ^ k ∣ m (c + k) - m (a + k) := by
  have hdvd : (3 : ℤ) ^ k ∣ 2 ^ k * (m (c + k) - m (a + k)) := by
    rw [← lemmaR_int h]
    exact Dvd.intro _ rfl
  exact (isCoprime_two_pow_three_pow k).symm.dvd_of_dvd_mul_left hdvd

/-- **Proposition 2.5, the growth ceiling**: a repetition of length `k` at `2 ≤ a < c` forces
`2^(k+c+1) ≤ 3^(c+1)`, that is `k ≤ (c + 1) log₂ (3/2)`. -/
theorem repetition_pow_le {a c k : ℕ} (ha : 2 ≤ a) (hac : a < c) (h : IsRepetition a c k) :
    2 ^ (k + c + 1) ≤ 3 ^ (c + 1) := by
  have h1 : (2 : ℤ) ^ k ≤ m c - m a :=
    Int.le_of_dvd (sub_pos.mpr (m_strictMono ha hac)) (two_pow_dvd_of_repetition h)
  have h4 : (2 : ℤ) ^ k ≤ m c := by linarith [m_pos a]
  have h2 := two_pow_mul_m_le c
  have hz : (2 : ℤ) ^ (k + c + 1) ≤ 3 ^ (c + 1) :=
    calc (2 : ℤ) ^ (k + c + 1) = 2 ^ k * (2 * 2 ^ c) := by rw [pow_add, pow_succ]; ring
      _ ≤ m c * (2 * 2 ^ c) := mul_le_mul_of_nonneg_right h4 (by positivity)
      _ = 2 * (2 ^ c * m c) := by ring
      _ ≤ 2 * 3 ^ c + 2 ^ c := h2
      _ ≤ 3 ^ (c + 1) := by
          rw [pow_succ]
          linarith [pow_le_pow_left₀ (by norm_num : (0 : ℤ) ≤ 2) (by norm_num : (2 : ℤ) ≤ 3) c]
  exact_mod_cast hz

/-- **Lemma 2.7, the contraction**: a repetition of length `k` forces
`|eps c - eps a| ≤ (2/3)^k`. -/
theorem abs_eps_sub_le_of_repetition {a c k : ℕ} (h : IsRepetition a c k) :
    |eps c - eps a| ≤ (2 / 3 : ℚ) ^ k := by
  have heq : eps c - eps a = (2 / 3 : ℚ) ^ k * (eps (c + k) - eps (a + k)) := by
    have h3 : (0 : ℚ) < 3 ^ k := by positivity
    rw [div_pow]
    field_simp
    linarith [lemmaR_eps h]
  have hpos : (0 : ℚ) ≤ (2 / 3 : ℚ) ^ k := by positivity
  rw [heq, abs_mul, abs_of_nonneg hpos]
  calc (2 / 3 : ℚ) ^ k * |eps (c + k) - eps (a + k)| ≤ (2 / 3 : ℚ) ^ k * 1 :=
        mul_le_mul_of_nonneg_left (abs_eps_sub_lt_one _ _).le hpos
    _ = (2 / 3 : ℚ) ^ k := mul_one _

/-- **Theorem 2.9, aperiodicity**: the steering word is not eventually periodic. A period `p`
from `N` on gives repetitions of every length at `a = max N 2` and `c = a + p`, and the length
`3^(c+1)` breaks the growth ceiling. -/
theorem not_isEventuallyPeriodic : ¬ Function.IsEventuallyPeriodic t := by
  rintro ⟨N, p, hp, hper⟩
  set a := max N 2 with ha
  set c := a + p with hc
  have hrep : ∀ k, IsRepetition a c k := fun k i _ ↦ by
    rw [show c + i = (a + i) + p by omega, hper (a + i) (by have := le_max_left N 2; omega)]
  have hbound := repetition_pow_le (le_max_right N 2) (by omega) (hrep (3 ^ (c + 1)))
  have hlt : (3 : ℕ) ^ (c + 1) < 2 ^ (3 ^ (c + 1)) := Nat.lt_two_pow_self
  have hmono : (2 : ℕ) ^ (3 ^ (c + 1)) ≤ 2 ^ (3 ^ (c + 1) + c + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end SteeringWord
