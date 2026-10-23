# Stephan 2026: superlinear complexity of the `(3/2)^n` steering word

R. Stephan, *Superlinear complexity of the `(3/2)^n` steering word*, arXiv:2607.11648 (2026).
Its Section 4 proves the kernel (K) by a two-variable (Ridout-type) and a three-variable
application of the Subspace Theorem.

**Status (2026-10-18): Theorem 1.1 is proved, within Lean's three standard axioms**
(`SteeringWord.tendsto_complexity_div`, `SteeringWord.exists_forall_lt_complexity`).
**(2026-10-21): Problem 5.2 is solved**: `p_T(k) > C k (log k)^η` for infinitely many `k`, for
every `η < 1/4` and every `C` (`SteeringWord.frequently_lt_complexity`,
`SteeringWord.quantitativeSuperlinear`), within the same three axioms; published as Theorem 1.3
of R. Stephan, *The exponent `1/4` in three complexity bounds: integer bases, continued fractions,
and the `(3/2)^n` steering word*, arXiv:2610.30937 (2026), §5. The
directory is its own `lean_lib` (`Stephan2026a`), held to the same rules as the other paper
directories (no `sorry`, no `set_option`, std3 axioms, fine-grained imports, module system,
Mathlib-style namespaces), and is in the gates' library lists. Its comparator lane certifies
Theorem 1.1 and Problem 5.2: `comparator/stephan-2026a.txt`, `ChallengeStephan2026a.lean`,
`SolutionStephan2026a.lean`, `comparator/stephan-2026a.json`, and `formalization.yaml` here.

This is the **minimal** formalization: the main theorem and the numbered results on its proof
path, nothing else, plus the solution of Problem 5.2 (below). The Subspace Theorem, Ridout's
theorem and Evertse–Ferretti's quantitative Subspace Theorem are theorems of
`DiophantineApproximation` and `QuantitativeSubspace`, so nothing is assumed.

## The results of the paper, and where they are

| Paper | Statement | Lean |
|---|---|---|
| Def. 1.4 | `mₙ = round ((3/2)^n)`, `εₙ`, `tₙ = 2 mₙ₊₁ - 3 mₙ` | `SteeringWord.m`, `eps`, `t` (`SteeringWord.lean`) |
| Def. 1.5 | the circuit sum `W(a, k)` | `SteeringWord.W` |
| **Thm 1.1 = Thm 4.7** | `p_T(k) / k → ∞` | `SteeringWord.tendsto_complexity_div`, `exists_forall_lt_complexity` (`Kernel.lean`) |
| Lemma 2.1 | `W(a, k) = 3^k ε_a - 2^k ε_{a+k}` | `SteeringWord.W_closed`, `circuit_sum` |
| Def. 2.2 | repetition | `SteeringWord.IsRepetition` (`RepetitionIdentity.lean`) |
| Thm 2.3 | the repetition identity | `SteeringWord.lemmaR_eps`, `lemmaR_int` |
| Cor. 2.4 | `2^k ∣ m_c - m_a`, `3^k ∣ m_{c+k} - m_{a+k}` | `two_pow_dvd_of_repetition`, `three_pow_dvd_of_repetition` |
| Prop. 2.5 | growth ceiling `2^(k+c+1) ≤ 3^(c+1)` | `SteeringWord.repetition_pow_le` |
| Lemma 2.7 | contraction `|ε_c - ε_a| ≤ (2/3)^k` | `SteeringWord.abs_eps_sub_le_of_repetition` |
| Lemma 2.8 | trivial floor `2^c ‖(3/2)^c - (3/2)^a‖ ≥ 1` | `one_le_two_pow_mul_distToNearestInt_orbit` |
| Thm 2.9 | `T` is not eventually periodic | `SteeringWord.not_isEventuallyPeriodic` |
| Thm 2.10 | `41 k ≤ 24 p_T(k) + 72` | `SteeringWord.complexity_lower` (`ComplexityFloor.lean`) |
| Prop. 2.12 | parity dichotomy | `SteeringWord.parity_dichotomy` |
| Def. 3.1 | `V(θ)`, the kernel (K) | `SteeringWord.kernelViolators` (`Reduction.lean`) |
| Thm 3.2 | (K) implies superlinearity | `forall_lt_complexity_of_kernel`, `tendsto_complexity_div_of_kernel`; the exchange rate `lt_complexity_of_forall_le` |
| Thm 4.1 | the `p`-adic Subspace Theorem, `S = {2, 3}` | `SteeringWord.exists_finset_submodule_of_prod_le` (`SubspaceStep.lean`), from DA `Rat.exists_finset_submodule_of_prod_mul_prod_padicNorm_le` |
| Lemma 4.2 | `0 < ‖ξ (3/2)^a‖ ≤ θ^a` finitely often | `SteeringWord.finite_setOf_distToNearestInt_mul_le` (`ConstantGap.lean`) |
| Cor. 4.3 | the gap-bounded slice | `SteeringWord.finite_kernelViolators_gap_le` |
| **Thm 4.5** | (K) holds | `SteeringWord.finite_kernelViolators` (`Kernel.lean`) |
| **Problem 5.2** | `p_T(k) ≥ k (log k)^δ` infinitely often | **solved**, every `η < 1/4`: `SteeringWord.frequently_lt_complexity`, `quantitativeSuperlinear` (`QuantitativeTheorem.lean`) |
| Problems 5.1, 5.3, 5.4, Conj. A.2 | open | stated in `Problems.lean` |

`Function.complexity` (DA Layer 7.5, `FactorComplexity.lean`) is the subword complexity; the
steering word has finitely many factors of each length (`SteeringWord.finite_factors`), so its
`Set.ncard` counts honestly.

**Not formalized**, as not on the proof path of Theorem 1.1: Proposition 1.2 (packing bound),
Corollary 1.3 (density forces exponential complexity), the remarks (power repetitions after
Prop. 2.5, the desynchronization bound after Prop. 2.12, short fixed-gap repetitions after
Cor. 4.3), Proposition A.1 and the numerics of Appendix A.

## How the proof uses `DiophantineApproximation`

- **Theorem 4.1** is the specialization to the field `ℚ`, with `W = |·|` at `∞`, of DA Layer
  7.4's `Rat.exists_finset_submodule_of_prod_mul_prod_padicNorm_le`, itself DA 6.3 (the Subspace
  Theorem with algebraic coefficients and finite places). The forms at `∞` are
  `Module.Dual.sumForm` of rational coefficient vectors.
- **Lemma 4.2** follows the paper's proof: Theorem 4.1 with `n = 2` at the point
  `(u 3^a, v M 2^a)`. DA has Ridout's theorem itself (`Rat.finite_setOf_ridout`, Layer 3.3) and
  Mahler's theorem (`Nat.finite_setOf_exists_int_abs_sub_ratPow_le`, the case `ξ = 1`), but the
  paper's two-variable argument is shorter than the reduction to either.
- **Theorem 4.5** applies Theorem 4.1 with `n = 3` at `(2^c M, 3^c, 2^s 3^a)`. The case analysis
  of the exceptional planes is elementary, plus Corollary 4.3 on planes of constant gap.
- `SteeringWord.exists_forall_mul_pow_le_rpow_neg` is the one choice of `ε` both applications
  share: `ε = log (1/θ) / (2 log 3)`, so that `3^(-ε) = θ^(1/2) > θ`.

## Files

| File | Contents |
|---|---|
| `NearestInt.lean` | `Rat.distToNearestInt`, the dyadic floor |
| `SteeringWord.lean` | Defs. 1.4–1.5, Lemma 2.1, Lemma 2.8, monotonicity of `m` |
| `RepetitionIdentity.lean` | Def. 2.2, Thm 2.3, Cor. 2.4, Prop. 2.5, Lemma 2.7, Thm 2.9 |
| `ComplexityFloor.lean` | Thm 2.10, Prop. 2.12 |
| `Reduction.lean` | Def. 3.1, Thm 3.2 |
| `SubspaceStep.lean` | Thm 4.1 at `{∞, 2, 3}`, the choice of `ε`, hyperplanes |
| `ConstantGap.lean` | Lemma 4.2, Cor. 4.3 |
| `Kernel.lean` | Thm 4.5, Thm 1.1 |
| `Problems.lean` | Problems 5.1–5.4, Conjecture A.2 |
| `QuantitativeViolators.lean` | Problem 5.2, step 1: a doubling sequence of repetitions from `p_T(k) ≤ c k (log k)^u` |
| `QuantitativePlanes.lean` | step 2: the kernel point, `N = 2^c (ε_c - ε_a)`; the three-variable Evertse–Ferretti count |
| `QuantitativePlaneStep.lean` | step 3: the same-gap and distinct-gap principles; `12 (1 + log ε⁻¹)` points per plane |
| `QuantitativeLines.lean` | step 4: small gaps, two variables; three points per line |
| `QuantitativeTheorem.lean` | step 5: Problem 5.2 for every `η < 1/4` |

## Problem 5.2

`SteeringWord.frequently_lt_complexity`: for every `η < 1/4` and every `C`,
`p_T(k) > C k (log k)^η` for infinitely many `k`. The route is Bugeaud–Evertse 2008, Theorem 2.1
(`BugeaudEvertse2008/`), with the kernel points of §4 in place of their approximations. It is
§5 of arXiv:2610.30937: step 1 is its Lemma 5.1, step 2 Proposition 5.2, step 3 Lemmas 5.3–5.6,
step 4 Lemma 5.7, step 5 the proof of Theorem 1.3.

1. A bound `p_T(k) ≤ c k (log k)^u`, `u < v`, gives repetitions of length `τ_n (log τ_n)^{-v}` at
   pairs `(r_n + 2, τ_n + 2)` with `2 τ_n < τ_{n+1}` (DA's
   `Function.exists_repetitions_of_complexity_le`, the combinatorial half of Bugeaud–Evertse's
   Lemma 6.1, moved to `DiophantineApproximation/ComplexityRepetitions.lean` so that both papers
   share it), and Lemma 2.7 turns each into `|ε_c - ε_a| ≤ (3^c)^{-ε}`.
2. Pairs with a large gap `s > ε c / 4`: the kernel point `(3^c, 2^s 3^a, 2^c M)` solves a
   three-variable system at `∞`, `2`, `3` in the class `⌊k s / c⌋` of its gap; Evertse–Ferretti
   (`Real.subspaceBoundAt_three`) gives `K ε⁻⁴ (1 + log ε⁻¹)²` planes. One exponent at `∞` is
   `λ - ε` with `λ = log 2 / log 3 ≈ 0.63`, not `≤ 0`; the hypothesis of `Real.SubspaceBoundAt` was
   weakened to "one exponent `≤ 1 - δ / 2n`", which is all its proof uses.
3. On one plane the points are few by integer identities alone: the same gap gives `7 c₂ < 19 c₁`
   (`2^19 < 3^12`), two different gaps bound every further point by `c < 18 (c₁ + c₂) + 18`; a
   doubling sequence then has `O(1 + log ε⁻¹)` points on a plane.
4. Pairs with a small gap: the point `(3^c - 2^s 3^a, 2^c M)` solves a two-variable system;
   `K ε⁻³ (1 + log ε⁻¹)²` lines, at most three points on each (`3^5 < 2^8`).
5. With `ε ≈ (log τ_{2N})^{-v}` the `N` points `N ≤ n < 2N` number at most
   `K ε⁻⁴ (1 + log ε⁻¹)³ = o(N)` when `4 v < 1` (DA's `Real.eventually_doubling_thresholds`).

The exponent `1/4` is the count `ε⁻⁴` of planes; Bugeaud–Evertse's per-plane step costs
`ε⁻³` more for algebraic numbers (their `1/7` here, `1/11` in the paper). The same split of the
gap, with Liouville's inequality on the planes, brings algebraic numbers to `1/4` too
(`BugeaudEvertse2008/Additions/`, 2026-10-21).
