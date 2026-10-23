/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- Used only inside proofs.
import DiophantineApproximation.DoublingSequences

/-!
# The thresholds (Bugeaud–Evertse 2008, §7)

The proof of Theorem 2.1 works with the points `x_n`, `N ≤ n ≤ 2N`, of Lemma 6.1 and with
`ε = (log t_{2N})^{-v}`. Lemma 6.1 (`Function.exists_repetitions_of_complexity_le`) gives
`2 t_n < t_{n+1}` and `t_n ≤ (2n + 2)^{C(n+1)}`, so `log t_{2N}` lies between `(2N - 1) log 2` and
`C (2N + 1) log (4N + 2)`. For `N` large this gives everything the counting needs
(`Real.eventually_thresholds`):

* `0 < ε ≤ 1`;
* `ε ≤ (log t_n)^{-v}` for `N ≤ n ≤ 2N`, so the approximations of Lemma 6.1 hold with exponent `ε`;
* `K ε⁻¹ ≤ t_n log b` for `n ≥ N`: the threshold of the three-variable step
  (`Real.exists_planes_of_approx`), since `ε⁻¹ = O(N²)` and `t_n ≥ 2^{n-1}`;
* `K ε⁻⁷ (1 + log ε⁻¹)⁴ < N` when `7v < 1`: the count of the planes times the count per plane
  (`Real.card_mem_plane_le`) is smaller than the number of points.

The plane step needs no threshold from here; it handles its own (`Real.card_mem_plane_le`).

## Main results

* `Real.eventually_thresholds`: the inequalities above, for all large `N`; the case
  `(p, q) = (7, 4)` of `Real.eventually_doubling_thresholds`
  (`DiophantineApproximation/DoublingSequences.lean`, where the proof, first written here, now
  lives).

## References

Y. Bugeaud, J.-H. Evertse, *On two notions of complexity of algebraic numbers*, Acta Arith.
**133** (2008), 221–250, §7.
-/

@[expose] public section

open Filter

namespace Real

/-- **The thresholds of §7.** Let `0 < v`, `7 v < 1`, `K, L > 0`. For all large `N` and every
`t` with `2 t_n < t_{n+1}` and `t_n ≤ (2n + 2)^{C(n+1)}`, the number `ε = (log t_{2N})^{-v}`
satisfies `0 < ε ≤ 1`, `ε ≤ (log t_n)^{-v}` for `N ≤ n ≤ 2N`, `K ε⁻¹ ≤ t_n L` for `n ≥ N`, and
`K ε⁻⁷ (1 + log ε⁻¹)⁴ < N`. -/
theorem eventually_thresholds {C : ℕ} {v : ℝ} (hv : 0 < v) (hv7 : 7 * v < 1) {K L : ℝ}
    (hK : 0 < K) (hL : 0 < L) :
    ∀ᶠ N : ℕ in atTop, ∀ t : ℕ → ℕ, (∀ n, 2 * t n < t (n + 1)) →
      (∀ n, t n ≤ (2 * n + 2) ^ (C * (n + 1))) →
      0 < log (t (2 * N)) ^ (-v) ∧ log (t (2 * N)) ^ (-v) ≤ 1 ∧
      (∀ n, N ≤ n → n ≤ 2 * N → log (t (2 * N)) ^ (-v) ≤ log (t n) ^ (-v)) ∧
      (∀ n, N ≤ n → K * (log (t (2 * N)) ^ (-v))⁻¹ ≤ t n * L) ∧
      K * ((log (t (2 * N)) ^ (-v))⁻¹) ^ 7 * (1 + log (log (t (2 * N)) ^ (-v))⁻¹) ^ 4 < N :=
  eventually_doubling_thresholds 7 4 (by norm_num) (by norm_num) hv (by exact_mod_cast hv7) hK hL

end Real
