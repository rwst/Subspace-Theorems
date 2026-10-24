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
and the `(3/2)^n` steering word*, arXiv:2610.30937 (2026), §5. **(2026-10-24): every
`η < 1/3`** (`SteeringWord.frequently_lt_complexity_third`, `QuantitativeThird.lean`), with the
interval form of Evertse–Ferretti's count (`Real.SubspaceIntervalWith`); **every `η < 1/2`**
(`SteeringWord.frequently_lt_complexity_half`, `QuantitativeHalf.lean`), with the interval form
for a set of exponents (`Real.SubspaceIntervalFamilyWith`). The `1/3` and the `1/2` are Remark 8.1
and Theorem C of R. Stephan, *The Evertse–Ferretti interval result for a set of weights, and the
exponent `1/2` in three complexity bounds* (2026). The
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
| **Problem 5.2** | `p_T(k) ≥ k (log k)^δ` infinitely often | **solved**, every `η < 1/4`: `SteeringWord.frequently_lt_complexity`, `quantitativeSuperlinear` (`QuantitativeTheorem.lean`); every `η < 1/3`: `SteeringWord.frequently_lt_complexity_third` (`QuantitativeThird.lean`); every `η < 1/2`: `SteeringWord.frequently_lt_complexity_half` (`QuantitativeHalf.lean`) |
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
| `QuantitativeThird.lean` | steps 2, 4 and 5 with the interval form: Problem 5.2 for every `η < 1/3` |
| `QuantitativeHalf.lean` | step 2 with one interval result for all classes: Problem 5.2 for every `η < 1/2` |

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
   (`Real.subspaceBoundAt_three`) gives `K ε⁻⁴ (1 + log ε⁻¹)²` planes, with `K = 96 · 10²⁴`
   (`SteeringWord.exists_planes_of_violators_explicit`: the forms have integer coefficients, so
   Evertse–Ferretti's constant is explicit, `≤ 10²⁴`). One exponent at `∞` is
   `λ - ε` with `λ = log 2 / log 3 ≈ 0.63`, not `≤ 0`; the hypothesis of `Real.SubspaceBoundAt` was
   weakened to "one exponent `≤ 1 - δ / 2n`", which is all its proof uses.
3. On one plane the points are few by integer identities alone: the same gap gives `7 c₂ < 19 c₁`
   (`2^19 < 3^12`), two different gaps bound every further point by `c < 18 (c₁ + c₂) + 18`; a
   doubling sequence then has `O(1 + log ε⁻¹)` points on a plane.
4. Pairs with a small gap: the point `(3^c - 2^s 3^a, 2^c M)` solves a two-variable system;
   `K ε⁻³ (1 + log ε⁻¹)²` lines with `K = 32 · 10²¹`
   (`SteeringWord.exists_lines_of_violators_explicit`), at most three points on each
   (`3^5 < 2^8`).
5. With `ε ≈ (log τ_{2N})^{-v}` the `N` points `N ≤ n < 2N` number at most
   `K ε⁻⁴ (1 + log ε⁻¹)³ = o(N)` when `4 v < 1` (DA's `Real.eventually_doubling_thresholds`).

The exponent `1/4` is the count `ε⁻⁴` of planes; Bugeaud–Evertse's per-plane step costs
`ε⁻³` more for algebraic numbers (their `1/7` here, `1/11` in the paper). The same split of the
gap, with Liouville's inequality on the planes, brings algebraic numbers to `1/4` too
(`BugeaudEvertse2008/Additions/`, 2026-10-21).

**Every `η < 1/3`** (`QuantitativeThird.lean`, 2026-10-24). Evertse–Ferretti's `δ⁻³` is the
product of `δ⁻² log δ⁻¹` intervals `[s, ω₀ s)` of `log |x|` outside one exceptional subspace (the
parametric theorem, EF13 Thm 3.3) and `δ⁻¹ log δ⁻¹` windows of the gap principle in each. The
points here have doubling positions `c = τ_n + 2`, so an interval of ratio `ω₀ ≍ δ⁻¹` holds
`O(log δ⁻¹)` of them and the gap principle is not needed. The interval form
(`Real.SubspaceIntervalWith`, `QuantitativeSubspace/RealFormInterval.lean`) gives, per class of
the gap, one plane with `O(log ε⁻¹)` points and `O(ε⁻² log² ε⁻¹)` further points
(`SteeringWord.exists_plane_intervals_of_violators`), and for the small gaps one line and
`O(ε⁻² log² ε⁻¹)` points (`SteeringWord.exists_line_intervals_of_violators`). So
`N = O(ε⁻³ log² ε⁻¹)` (`SteeringWord.card_le_of_violators_third`), which is `o(N)` when
`3 v < 1`. The step-2 and step-4 systems are shared with the count form
(`SteeringWord.kernel_class_hyps`, `SteeringWord.kernel_class_mem`, `SteeringWord.line_hyps`,
`SteeringWord.line_mem`). The same change brings integer bases and continued fractions to `1/3`
(`BugeaudEvertse2008/Additions/Theorem21Third.lean`, `Bugeaud2013/Additions/CountThird.lean`).

**Every `η < 1/2`** (`QuantitativeHalf.lean`, 2026-10-24). The `≈ 2/ε` classes of the gap cost
the remaining factor `ε⁻¹`: one interval result per class. The classes have the same forms and
differ only in their exponents, and Evertse–Ferretti's Theorem 2.3 holds for a whole set of
exponents with counts that do not depend on the set (`NumberField.FormSystem.exists_intervals_cover_family`,
`QuantitativeSubspace/FormIntervalFamily.lean`): the destabilizing subspaces `T(L, c)` are
determined by a finite weight type, and the reduction to the quotient depends on `c` only through
finitely many row selections. Its interval form for real forms
(`Real.SubspaceIntervalFamilyWith`, `QuantitativeSubspace/RealFormFamily.lean`) puts the kernel
points of all classes into `K` planes, `K` independent of `ε`, and `O(ε⁻² log ε⁻¹)` intervals
(`SteeringWord.exists_plane_intervals_family_of_violators`). So
`N = O(ε⁻² log² ε⁻¹)` (`SteeringWord.card_le_of_violators_half`), which is `o(N)` when `2 v < 1`.
The `δ⁻²` left is the number of intervals of Theorem 2.3, the number `m ≍ δ⁻²` of blocks of
the auxiliary polynomial (Hoeffding). The same change brings integer bases and continued
fractions to `1/2` (`BugeaudEvertse2008/Additions/Theorem21Half.lean`,
`Bugeaud2013/Additions/CountHalf.lean`). All three, and the theorem for a set of exponents, are in
R. Stephan, *The Evertse–Ferretti interval result for a set of weights, and the exponent `1/2` in
three complexity bounds* (2026): its Theorem 2.1 is
`NumberField.FormSystem.exists_intervals_cover_family`, and its §7 is this step.
