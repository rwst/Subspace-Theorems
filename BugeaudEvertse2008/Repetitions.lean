/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.ComplexityRepetitions
public import DiophantineApproximation.DigitExpansions

/-!
# Repetitions from a complexity bound `p n ≤ c n (log n)^u` (Bugeaud–Evertse 2008, Lemma 6.1)

If the factor complexity of a sequence over a finite alphabet is at most `c n (log n)^u`, then
for every `v > u` there are positions `r_n < t_n`, growing at least geometrically
(`2 t_n < t_{n+1}`) and at most like `(2n + 2)^{C (n + 1)}`, such that the `t_n (log t_n)^{-v}`
letters after position `t_n` repeat those after position `r_n`, and the repetition cannot be
slid to the left (`a (r_n - 1) ≠ a (t_n - 1)` when `r_n ≥ 1`). For the base-`b` digits of `ξ` this
is the approximation `|b^{t_n} ξ - b^{r_n} ξ - p_n| ≤ (b^{t_n})^{-(log t_n)^{-v}}` with `b ∤ p_n`
when `r_n ≥ 1` (`Real.exists_approx_of_complexity_le`).

**The paper states the lemma for `v < u`; it holds for `v > u`.** The pigeonhole (two equal
factors of length `m` among the first `p m + 1` positions) gives a repetition of length about
`ℓ (log ℓ)^{-u}` after a position `t ≤ ℓ`, i.e. the exponent `c₃ (log t)^{-u}`, which is at least
`(log t)^{-v}` for large `t` only when `v > u` (the paper's choice of `ℓ₁`,
"`c₃ (log t_ℓ)^u ≥ (log t_ℓ)^v`", is the reciprocal of what is needed). §7 is unaffected: it
needs the exponent `ε = (log t_N)^{-v}` with `ε⁻¹ ≤ N^{v + η}`, and for `η < 1/11` (or the
exponent proved here) one picks `u < v` in between.

The combinatorial form, which says nothing about numbers, is
`Function.exists_repetitions_of_complexity_le` in
`DiophantineApproximation/ComplexityRepetitions.lean`, shared with `Stephan2026a/`; it was proved
here first.

## Main results

* `Real.not_dvd_digitsPrefix_sub`: the integer `p_n` is prime to `b` in the sense `b ∤ p_n`.
* `Real.exists_approx_of_complexity_le`: **Lemma 6.1** for the digits of `ξ`.

## References

Y. Bugeaud, J.-H. Evertse, *On two notions of complexity of algebraic numbers*, Acta Arith.
**133** (2008), 221–250, §6.
-/

@[expose] public section

open Filter Topology

namespace Real

variable {b : ℕ}

/-- **`b ∤ p_n`**: if the digits before positions `r ≥ 1` and `t ≥ 1` differ, the integer
`digitsPrefix a t - digitsPrefix a r` is not divisible by `b`. -/
theorem not_dvd_digitsPrefix_sub {a : ℕ → Fin b} {r t : ℕ} (hr : 1 ≤ r) (ht : 1 ≤ t)
    (hne : a (r - 1) ≠ a (t - 1)) :
    ¬ (b : ℤ) ∣ (digitsPrefix a t : ℤ) - digitsPrefix a r := by
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hne
  intro h
  rw [digitsPrefix_succ, digitsPrefix_succ] at h
  push_cast at h
  have h2 : (b : ℤ) ∣ ((a t : ℕ) : ℤ) - ((a r : ℕ) : ℤ) := by
    have : ((a t : ℕ) : ℤ) - ((a r : ℕ) : ℤ) =
        ((b : ℤ) * digitsPrefix a t + (a t : ℕ) - ((b : ℤ) * digitsPrefix a r + (a r : ℕ))) -
          (b : ℤ) * ((digitsPrefix a t : ℤ) - digitsPrefix a r) := by ring
    rw [this]
    exact dvd_sub h (dvd_mul_right _ _)
  have hat := (a t).isLt
  have har := (a r).isLt
  have h3 := Int.eq_zero_of_abs_lt_dvd h2 (by rw [abs_lt]; constructor <;> omega)
  exact hne (Fin.ext (by omega))

/-- **Bugeaud–Evertse 2008, Lemma 6.1** (with `v > u`; see the module docstring). If the base-`b`
digits of `ξ = ofDigits a` have complexity `p n ≤ c n (log n)^u` for `n ≥ n₀`, `0 ≤ u < v`,
there are `r n < t n` with `2 t n < t (n + 1)`, `t n ≤ (2 n + 2)^{C (n + 1)}`, and integers `p n`
with `|p n| ≤ b^{t n}`, `|b^{t n} ξ - b^{r n} ξ - p n| ≤ (b^{t n})^{-(log t n)^{-v}}` and
`b ∤ p n` when `r n ≥ 1`. -/
theorem exists_approx_of_complexity_le {a : ℕ → Fin b} {c u v : ℝ} (hb : 2 ≤ b) (hu : 0 ≤ u)
    (huv : u < v) (n₀ : ℕ)
    (hp : ∀ n ≥ n₀, (Function.complexity a n : ℝ) ≤ c * n * Real.log n ^ u) :
    ∃ (C : ℕ) (r t : ℕ → ℕ) (p : ℕ → ℤ), (∀ n, r n < t n) ∧ (∀ n, 2 * t n < t (n + 1)) ∧
      (∀ n, t n ≤ (2 * n + 2) ^ (C * (n + 1))) ∧ (∀ n, 1 ≤ r n → ¬ (b : ℤ) ∣ p n) ∧
      (∀ n, |(p n : ℝ)| ≤ (b : ℝ) ^ t n) ∧
      ∀ n, |(b : ℝ) ^ t n * ofDigits a - b ^ r n * ofDigits a - p n| ≤
        ((b : ℝ) ^ t n) ^ (-Real.log (t n) ^ (-v)) := by
  obtain ⟨C, r, t, hrt, hgap, hbd, hmin, hrep⟩ :=
    Function.exists_repetitions_of_complexity_le (Function.finite_factors a) hu huv n₀ hp
  refine ⟨C, r, t, fun n ↦ (digitsPrefix a (t n) : ℤ) - digitsPrefix a (r n), hrt, hgap, hbd,
    fun n hr ↦ not_dvd_digitsPrefix_sub hr (by have := hrt n; omega)
      ((hmin n).resolve_left (by omega)), fun n ↦ ?_, fun n ↦ ?_⟩
  · -- `0 ≤ p n ≤ b^{r n} (b^{t n - r n} - 1) ≤ b^{t n}`
    have hrs : r n + (t n - r n) = t n := by have := hrt n; omega
    obtain ⟨h0, h1⟩ := digitsPrefix_sub_mem a (r n) (t n - r n)
    have h2 : (b : ℤ) ^ r n * ((b : ℤ) ^ (t n - r n) - 1) ≤ (b : ℤ) ^ (r n + (t n - r n)) := by
      rw [pow_add]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    rw [hrs] at h0 h1 h2
    rw [← Int.cast_abs, abs_of_nonneg h0]
    exact_mod_cast h1.trans h2
  have hB : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  have hrs : r n + (t n - r n) = t n := by have := hrt n; omega
  have h := abs_mul_ofDigits_sub_le a (r := r n) (s := t n - r n)
    (t := ⌈t n * Real.log (t n) ^ (-v)⌉₊) (fun i hi ↦ by rw [hrs]; exact hrep n i hi)
  rw [hrs] at h
  push_cast at h ⊢
  refine (le_of_eq (by ring_nf)).trans (h.trans ?_)
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_neg (by positivity),
    ← Real.rpow_mul (by positivity)]
  refine Real.rpow_le_rpow_of_exponent_le hB ?_
  have := Nat.le_ceil ((t n : ℝ) * Real.log (t n) ^ (-v))
  linarith

end Real
