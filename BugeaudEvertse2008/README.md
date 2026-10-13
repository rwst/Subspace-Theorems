# Bugeaud–Evertse 2008: two notions of complexity of algebraic numbers

Y. Bugeaud and J.-H. Evertse, *On two notions of complexity of algebraic numbers*, Acta Arith.
**133** (2008), 221–250; arXiv `0709.1560` (the copy read: `~/math/lean-code/papers/BugeaudEvertse2008.pdf`,
the arXiv v1, 30 pages).

**Status: Theorem 2.1 PROVED with `η < 1/7` (paper: `1/11`), std3, 2026-10-13
(`Real.frequently_lt_complexity`, `Theorem21.lean`). BE.0–BE.5 done.** Optional later work:
Thm 3.1, Cor. 3.2, Thm 9.1, 9.2. The directory is its own `lean_lib`
(`BugeaudEvertse2008`), held to the same rules as the other paper directories (no `sorry`, no
`set_option`, std3 axioms, fine-grained imports, module system, Mathlib root namespaces). Read
§§5–7 of the paper and this file's *Settled checks* before continuing.

## Why this paper

`~/math/lean-code` records the paper's main result as a **cited axiom**,
`BugeaudEvertse.exists_pComplexity_gt` in `CITED/BugeaudEvertseComplexity.lean` (Ralf Stephan with
Claude Code, CC0). Its consumer is the corpus root `BB47/` (`BB47/Cited.lean`,
`BB47/TheoremA.lean`). **Once Theorem 2.1 below is proved here, that axiom can be discharged** the
way the corpus already discharged the Corvaja–Zannier, Adamczewski–Bugeaud and Evertse 1984 axioms:
derive the corpus statement from this library's theorem and delete the `axiom`. The corpus also
keeps Corollary 5.2 as the axiom `BugeaudEvertse.ridout_line_cover`
(`CITED/BugeaudEvertseRidout.lean`). That one needs the small threshold and is **not** in scope
here; see `QuantitativeSubspace/README.md`, Q4.4 and Q4.5.

## The results of the paper

`p(n, ξ, b)` is the number of distinct blocks of length `n` in the `b`-ary expansion of `ξ`
(`Function.complexity` of the digit sequence, `DiophantineApproximation/FactorComplexity.lean`).
`nbdc(n, ξ, b)` is the number of `k ≤ n` with `a_k ≠ a_{k+1}`.

| Result | Statement | Proof uses |
|---|---|---|
| **Thm 2.1** | `ξ` algebraic irrational, `0 < ξ < 1`, `η < 1/11`: `limsup p(n, ξ, b) / (n (log n)^η) = +∞` | Lemma 6.1, Thm 5.1 at `n = 3`, Cor. 5.2 |
| (2.4) | a `(log log n)^δ` refinement of Thm 2.1, stated without proof | not a target |
| **Thm 3.1** | `nbdc(n, ξ, b) ≥ c₁ (log n)^{3/2} / ((log log n)^{1/2} (log 6d)^{1/2})` for `n ≥ c₂(ξ, b)`, `c₁` absolute and effective | Cor. 5.2, Lemma 8.1 |
| Cor. 3.2 | `∑_j b^{-2^{[j^η]}}` is transcendental for `η > 2/3` | Thm 3.1 |
| Prop. 4.1 | ES02's quantitative parametric Subspace Theorem; for `n = 2` the sharper count `225 δ⁻³ log 2r log(δ⁻¹ log 2r)` (Appendix, Prop. A.1) | ES02 |
| **Thm 5.1** | systems `|L_{ip}(x)|_p ≤ Ψ(x)^{e_{ip}}` over `S = {∞, p₁, …, p_t}`, weight `-ε`: the solutions with `Ψ(x) > max(2H, n^{2n/ε})` lie in `8^{(n+9)²} (1 + ε⁻¹)^{n+4} log 2RD log log 2RD` proper subspaces (`n ≥ 3`), or `2³² (1 + ε⁻¹)³ log 2RD log((1 + ε⁻¹) log 2RD)` (`n = 2`). **The count does not depend on `|S|`.** | Prop. 4.1 |
| Cor. 5.2 | quantitative Ridout: lines through the solutions with `y > max(2H(ξ), 2^{4/ε})` | Thm 5.1, `n = 2` |
| Thm 9.1, 9.2 | an improvement of Mahler's extension of Ridout; a digit-change bound for `θ`-gap series | Cor. 5.2 |

## The proof of Theorem 2.1 (§§6–7), and what ST already has for it

1. **Lemma 6.1 (combinatorial).** If `p(n, ξ, b) ≤ c n (log n)^u` for all `n`, then for every
   `v > u` (**the paper prints `v < u`, which its proof does not give**; see BE.1) there are `0 ≤ r_n < t_n` and `p_n` with `|b^{t_n} ξ − b^{r_n} ξ − p_n| ≤ (b^{t_n})^{−(log t_n)^{−v}}`,
   `2 t_n < t_{n+1}`, `t_n ≤ (2n)^{Cn}`, and `b ∤ p_n` when `r_n ≥ 1`. Pigeonhole on the prefix
   `A(ℓ) = U V W V X` with `|V| ≥ c ℓ (log ℓ)^{−u}`, then the rational number `U (V W)^∞`.
   **ST has the ingredients**: `Function.exists_rep_of_lt` / `exists_rep_min` /
   `exists_rep_of_encard_le` (`Bugeaud2013/Additions/Complexity.lean`) are the same pigeonhole for
   continued fractions; `DiophantineApproximation/FactorComplexity.lean` has the qualitative
   version for any alphabet (`exists_periodic_of_frequently_complexity_le`), and
   `DiophantineApproximation/StammeringWords.lean` the periodic blocks
   (`IsStammeringWith.exists_periodic`). Lemma 6.1 is their quantitative form, with
   `|V| ≥ c ℓ (log ℓ)^{−u}` in place of `|V| ≥ c ℓ`. The approximation itself is
   `Real.abs_mul_ofDigits_sub_le_rpow` (`DiophantineApproximation/TranscendenceCriterion.lean`):
   a period `s` on `[r, r + ⌈w s⌉)` puts `(b^{r+s} − b^r) ξ` within `b^{−(w−1)s}` of the integer
   `digitsPrefix a (r+s) − digitsPrefix a r`. So `t_n = r + s`, `p_n` is that integer, and
   `w − 1 = (log t_n)^{−v}` up to the constant.
2. **The 3-variable step (§7, (7.3)–(7.11)).** With `ε = (log t_N)^{−v}`, the vectors
   `x_n = (b^{t_n}, b^{r_n}, p_n)`, `N/2 ≤ n ≤ N`, split into `k = [2/ε] + 1` classes by `r_n/t_n`.
   Each class solves a system of Thm 5.1 with `n = 3`, `R = 4`, `D = d`, `H = H(ξ)` and
   `S = {∞} ∪ {p | b}`: forms `X₁, X₂, −ξX₁ + ξX₂ + X₃` at `∞`, coordinates at `p | b`. So all
   `x_n` lie in `k · A₁ ≤ (ε⁻¹)^{8+η}` planes (`A₁ ≍ (ε − 1/k)^{−7}`, ES02's `δ^{−n−4}` at `n = 3`).
   **ST has**: EF13's count for systems with finite places, `efLargeCount_le_ef`
   (`QuantitativeSubspace/FormSystemCount.lean`, Q4.3): `δ⁻³`, independent of the places, of
   `[E : ℚ]` and of `H`, which is exactly the property BE08 single out as the key point.
   **The qualitative skeleton of this step is already in ST**:
   `Real.transcendental_ofDigits_of_forall_periodic` (`TranscendenceCriterion.lean`) builds the
   same points `![b^{r+s}, b^r, p]` and feeds them to `exists_finset_submodule_of_repetition`
   (`DiophantineApproximation/RepetitionSubspaces.lean`), which is the qualitative Subspace
   Theorem for exactly this product inequality, `ξX₁ − ξX₂ − X₃` at `∞` and the coordinates at
   `S = b.primesOf`. BE.2 is its quantitative version (via BE.0).
3. **The 2-variable step ((7.12)–(7.19)).** On a plane `z₁X₁ + z₂X₂ + z₃X₃ = 0` the points give
   approximations to `ξ' = ξ(z₁ + z₂)/(ξz₃ − z₂)` with `H(ξ') ≤ b^{3 t_{i₂}}`. After dropping the
   first `k₀ ≤ 4 + log(4/ε)/log 2` of them ((7.14), (7.15)), Cor. 5.2 with `S₂ = {p | b}` bounds
   the rest by `2 B(d, ε)`, `B ≍ ε^{−3}`. So each plane holds `≤ (ε⁻¹)^{3+η}` points.
   **ST has**: EF13's count holds for every `n ≥ 2`, so BE.0 (Q4.6) at `n = 2` gives `δ⁻³`
   lines per plane, the same exponent as BE08's Appendix count. The two-variable count Q1.6
   (`systemLargeCountTwo_evertse_le`) is not needed; its threshold is `exp(O(δ⁻² log δ⁻¹))`,
   which would also have sufficed, but EF13's is linear in `δ⁻¹`.
4. **Conclusion.** `N/2 ≤ (ε⁻¹)^{8+η} (ε⁻¹)^{3+η} ≤ N^{(11+2η)(v+η)} = N^{1−η}`: contradiction.
   The `11` of `1/11` is `1` (the classes) `+ 7` (ES02 at `n = 3`) `+ 3` (Cor. 5.2).

### Why the threshold is not an obstacle here (unlike for Cor. 5.2 itself)

ST's counts hold above its own thresholds, not above Evertse's `max(2H, n^{2n/δ})`. BE.0
(`Real.SubspaceBoundAt`, Q4.6) has the threshold `log |x| ≥ K δ⁻¹ (1 + log B + log C + log γ⁻¹)`
with `K = K(ξ, S, n)`: linear in `δ⁻¹` and in the logarithms of the coefficient bound `B`, the
constant `C` and the determinant bound `γ`. Theorem 2.1 has room at both steps:

* **step 2** (`n = 3`): `B`, `C`, `γ` depend on `ξ` and `b` only, and
  `log |x_n| = t_n log b ≥ 2^{N/2 − 1} log 2` is doubly exponential in `N`, while
  `ε⁻¹ ≤ (C N log 2N)^{v+η}`.
* **step 3** (`n = 2`): `log B ≤ 2 t_{i₂} log b + O(1)` and, by Liouville,
  `log γ⁻¹ ≤ (d − 1) log B + O_ξ(1)`, so the threshold is `O(ε⁻¹ t_{i₂})`. (7.14) already demands
  `log y ≥ (3 d t_{i₂})^{2/ε} log b`, which is far larger for `N` large.

So BE.4 is elementary real analysis. (Before BE.0 was proved this section planned step 3 with
Q1.6, whose threshold `exp(O(δ⁻² log δ⁻¹))` would also have worked, since `v + η < 1`.)

### Outcome: a better exponent (confirmed, BE.5)

With EF13 in step 2 the count per class is `δ⁻³` up to logarithms instead of `δ^{−7}`, so the
exponent becomes `1 + 3 + 3 = 7`: **`η < 1/7` is what BE.5 proves** (by the same mechanism by
which `Bugeaud2013/Additions` gets `δ < 1/4` from EF13 against `δ < 1/9` from ES02's shape).
Since `1/7 > 1/11`, the corpus axiom (`η < 1/11`) follows at once.

## Settled checks (2026-10-13, against ST's definitions)

- **One field for all planes.** `ξ' = ξ(z₁ + z₂)/(ξz₃ − z₂)` lies in `ℚ(ξ)`, so the Galois field
  `E ⊇ ℚ(ξ)` of `Real.exists_isGalois_mem` (`Bugeaud2013/Additions/SubspaceCount.lean`, the
  splitting field inside `ℂ`) serves every plane. `[E : ℚ]`, `|D_E|` and `scalarConst ℚ S` are
  fixed; only `formLogHeight` varies with the plane, linearly in `log max |zᵢ|`. Better still,
  step 3 needs no `ξ'` at all in Lean: the form `(ξz₃ − z₂)X − ξ(z₁ + z₂)Y` is linear in `ξ` with
  integer coefficients, the same shape as step 2's forms. Its coefficient bound is
  `B ≤ 2 max |zᵢ| ≤ 4 b^{2 t_{i₂}}` (`z` is the cross product of two points on the plane).
- **`δ` is BE08's `ε`.** In `IsNormalizedSystem` (`DiophantineApproximation/SubspaceSystem.lean`)
  `δ` is the weight bound (`weight_le : systemWeight c ≤ -δ`), with exponents in the affine height,
  which for integer points is `max |xᵢ|` = BE08's `Ψ`. So ST's `δ` is the `ε` of BE08 Thm 5.1
  directly. The passage `δ = ε/(n + ε)`, `r = n + DR`, `Q = Ψ^{1+ε/n}` ((5.19)–(5.20), Lemma 5.3)
  happens inside ST (`efSystemDelta n δ = δ/(4(n + δ))`). What the caller does have to supply is
  `const_le : systemConst C ≤ systemDet ^ (1/n)`, i.e. the constants (7.8) must be absorbed. The
  recipe is Additions' (`normLam`, `normExp`, `isNormalizedSystem_qForms`): raise the exponents
  that are not maximal by `τ = δ/2n` and scale the forms by powers of `2`, at the cost of half of
  `δ` and a threshold term linear in `log C` and `log γ⁻¹`.
- **The determinant in step 3** is `ξz₃ − z₂ ≠ 0` (irrationality of `ξ`). Its lower bound `γ` comes
  from Liouville: `|ξz₃ − z₂| ≥ c(ξ) max|zᵢ|^{−(d−1)}`, so `log γ⁻¹ ≤ (d − 1) log B + O_ξ(1)`,
  linear in `t_{i₂}`, like `log B`.
- **`S₂`-type exponents fit.** At a finite place `systemExponent` is `0`, and `exists_exponent_eq`
  wants one exponent equal to it. For `|y|_p ≤ y^{−f_p}` take exponent `−f_p` on `Y` and `0` on `X`
  (`|x|_p ≤ 1` holds for integers). Same at `n = 3` with the coordinates `X₁, X₂` (`b^{t}, b^{r}`)
  and `0` on `X₃`. This is BE.0's hypothesis `∀ l ∈ S, ∃ i, f l i = 0`.
- **The thresholds**: see *Why the threshold is not an obstacle* above; BE.0's is linear in
  `δ⁻¹`.

## Lean targets

The statement of record, in this repository's vocabulary (`Real.ofDigits`, `Function.complexity`),
**proved** in `Theorem21.lean` (std3):

```lean
theorem Real.frequently_lt_complexity (hb : 2 ≤ b) {a : ℕ → Fin b}
    (hirr : Irrational (Real.ofDigits a)) (halg : IsAlgebraic ℚ (Real.ofDigits a))
    {η : ℝ} (hη : η < 1 / 7) (C : ℝ) :
    ∃ᶠ n : ℕ in atTop, C * n * Real.log n ^ η < Function.complexity a n
```

The paper has `1 / 11`. For `η < 1/11` apply the theorem directly, since `1/11 < 1/7`.
The corpus axiom has the same shape with `∀ N, ∃ n ≥ N` and the corpus `pComplexity`; the bridge
`pComplexity = complexity` is `BB47.pComplexity_eq_complexity` (`BB47/Cited.lean`, via `List.ofFn`) and has to move into
`CITED/` when the axiom is discharged.

### Files

| file | milestone | content |
| --- | --- | --- |
| `QuantitativeSubspace/RealFormCount.lean` | BE.0 ✅ | EF13 for forms in `1, ξ, ξ²` at `∞` and the coordinates at the primes of `S`, integer points (Q4.6) |
| `Repetitions.lean` | BE.1 ✅ | Lemma 6.1 (with `v > u`), combinatorial and for the digits |
| `ThreeVariable.lean` | BE.2 ✅ | §7 (7.3)–(7.11): the classes, the system, the planes |
| `PlaneStep.lean` | BE.3 ✅ | §7 (7.12)–(7.19): the points on one plane |
| `Thresholds.lean` | BE.4 ✅ | the thresholds and the final count, for `N ≥ N₀` |
| `Theorem21.lean` | BE.5 ✅ | the counting contradiction; **Thm 2.1** with `1/7` |

### Milestones

BE.0–BE.5 are done (2026-10-13).

- **BE.0 ✅ (2026-10-13) — the quantitative Subspace Theorem for these forms, with finite
  places.** `Real.subspaceBoundAt_three (hα : IsAlgebraic ℚ α) (S : Finset Nat.Primes) :
  Real.SubspaceBoundAt α S 3` in `QuantitativeSubspace/RealFormCount.lean` (Q4.6; std3). For
  `2 ≤ n ≤ 4`, `∃ K > 0` such that for

  * forms `∑ₖ quadVal α (P i k) Xₖ` at `∞`, `quadVal α b = b₀ + b₁ α + b₂ α²`, with
    `|P i k m| ≤ B`, `γ ≤ |det|` (`0 < γ ≤ 1`), a constant `C ≥ 1`;
  * exponents `e i ≤ 1` at `∞`, one `= 1` and one `≤ 0`;
  * exponents `f l i ≤ 0` at `l ∈ S` (`f : Nat.Primes → Fin n → ℝ`), one `= 0` at each `l`;
  * `∑ e + ∑_{l ∈ S} ∑ f ≤ −δ`, `0 < δ ≤ 1`,

  the nonzero `x : Fin n → ℤ` with `|Lᵢ x| ≤ C ‖x‖^{e i}`, `padicNorm l (x i) ≤ ‖x‖^{f l i}` and
  `K δ⁻¹ (1 + log B + log C + log γ⁻¹) ≤ log ‖x‖` lie in `≤ K δ⁻³ (1 + log δ⁻¹)²` proper
  subspaces of `ℚⁿ`. BE08's forms are linear in `ξ` (`P i k 2 = 0`). Placed in
  `QuantitativeSubspace/` so that no paper library imports another; `Bugeaud2013/Additions`'
  `Real.subspaceBound_three` is now its case `S = ∅`.
- **BE.1 ✅ (2026-10-13) — Lemma 6.1.** `BugeaudEvertse2008/Repetitions.lean` (std3), positions
  `0`-based as in DA:

  ```lean
  theorem Function.exists_repetitions_of_complexity_le [Finite α] {a : ℕ → α} {c u v : ℝ}
      (hu : 0 ≤ u) (huv : u < v) (n₀ : ℕ)
      (hp : ∀ n ≥ n₀, (complexity a n : ℝ) ≤ c * n * Real.log n ^ u) :
      ∃ (C : ℕ) (r t : ℕ → ℕ), (∀ n, r n < t n) ∧ (∀ n, 2 * t n < t (n + 1)) ∧
        (∀ n, t n ≤ (2 * n + 2) ^ (C * (n + 1))) ∧
        (∀ n, r n = 0 ∨ a (r n - 1) ≠ a (t n - 1)) ∧
        ∀ n, ∀ i < ⌈t n * Real.log (t n) ^ (-v)⌉₊, a (i + t n) = a (i + r n)

  theorem Real.exists_approx_of_complexity_le {a : ℕ → Fin b} {c u v : ℝ} (hb : 2 ≤ b)
      (hu : 0 ≤ u) (huv : u < v) (n₀ : ℕ)
      (hp : ∀ n ≥ n₀, (Function.complexity a n : ℝ) ≤ c * n * Real.log n ^ u) :
      ∃ (C : ℕ) (r t : ℕ → ℕ) (p : ℕ → ℤ), (∀ n, r n < t n) ∧ (∀ n, 2 * t n < t (n + 1)) ∧
        (∀ n, t n ≤ (2 * n + 2) ^ (C * (n + 1))) ∧ (∀ n, 1 ≤ r n → ¬ (b : ℤ) ∣ p n) ∧
        ∀ n, |(b : ℝ) ^ t n * ofDigits a - b ^ r n * ofDigits a - p n| ≤
          ((b : ℝ) ^ t n) ^ (-Real.log (t n) ^ (-v))
  ```

  No irrationality or non-periodicity hypothesis is needed; `p n` is
  `digitsPrefix a (t n) − digitsPrefix a (r n)`.

  **Correction to the paper: `v > u`, not `v < u`.** The pigeonhole gives a repetition of length
  `≍ ℓ (log ℓ)^{−u}` after a position `t ≤ ℓ`, i.e. the exponent `c₃ (log t)^{−u}`, which beats
  `(log t)^{−v}` for large `t` only when `v > u`. (The paper's choice of `ℓ₁`,
  "`c₃ (log t_ℓ)^u ≥ (log t_ℓ)^v`", is the reciprocal of the needed inequality.) §7 is
  unaffected: it needs `ε = (log t_N)^{−v}` with `ε⁻¹ ≤ N^{v+η}`, which follows from
  `t_N ≤ (2N + 2)^{C(N+1)}` for any `v`. So BE.5 assumes `p ≤ c n (log n)^u` and applies
  BE.1 with some `v` between `u` and the target exponent, where §7 applies it with `u := v + η`.

  The proof does not follow §6's recursive `ℓ_{k+1}`. It applies the pigeonhole at the explicit
  factor lengths `m_k = (2k + 2)^{D(k+1)}`, with `D = 2⌈u⌉ + E`. Then
  `12 c m_k (log m_k)^u ≤ m_{k+1}` gives the spacing, and `t_k ≤ m_{k+1}` gives the growth bound.
  The pigeonhole lemma (`exists_rep_of_complexity_le_nat`) is written fresh for this library,
  not imported from `Bugeaud2013/Additions`, because paper libraries do not import each other.
- **BE.2 ✅ (2026-10-13) — the 3-variable step.** `BugeaudEvertse2008/ThreeVariable.lean`
  (std3):

  ```lean
  theorem Real.exists_planes_of_approx (hb : 2 ≤ b) {ξ : ℝ} (hξ : IsAlgebraic ℚ ξ) :
      ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ T : Finset (Submodule ℚ (Fin 3 → ℚ)),
        (#T : ℝ) ≤ K * ε⁻¹ ^ 4 * (1 + log ε⁻¹) ^ 2 ∧ (∀ U ∈ T, U ≠ ⊤) ∧
        ∀ (r t : ℕ) (p : ℤ), r < t → |(p : ℝ)| ≤ (b : ℝ) ^ t →
          |(b : ℝ) ^ t * ξ - b ^ r * ξ - p| ≤ ((b : ℝ) ^ t) ^ (-ε) → K * ε⁻¹ ≤ t * log b →
          ∃ U ∈ T, ![(b : ℚ) ^ t, (b : ℚ) ^ r, (p : ℚ)] ∈ U
  ```

  This is stated for all triples at once, not for a sequence; BE.5 feeds it the `x_n`. With
  `k = ⌊2/ε⌋ + 1`, the class `ℓ = ⌊k r/t⌋` is one application of BE.0 at `n = 3`:
  * `S` is the primes dividing `b` (`b.primeFactors.subtype Nat.Prime`);
  * the forms are `X₁, X₂, ξX₁ − ξX₂ − X₃` (`B = C = γ = 1`);
  * the exponents are `1, (ℓ+1)/k, −ε` at `∞`, and `g_l, g_l ℓ/k, 0` at each `l`, with
    `g_l = −v_l(b) log l / log b` (`Real.padicNorm_pow_eq_rpow`, `Real.sum_factorization_log_div`);
  * the weight is `δ = ε − 1/k ≥ ε/2`.

  There are `k ≤ 3/ε` classes, each giving `≤ K₀ δ⁻³ (1 + log δ⁻¹)²` planes above the threshold
  `K₀ δ⁻¹ ≤ 2 K₀ ε⁻¹`. The hypothesis `|p| ≤ b^t` makes `max |xᵢ| = b^t`; for the digit
  approximations it is `Real.digitsPrefix_sub_mem`. `ε ≤ 1` keeps `δ ≤ 1`.
  The paper's `(ε⁻¹)^{8+η}` becomes `ε⁻⁴ (1 + log ε⁻¹)²`.
- **BE.3 ✅ (2026-10-13) — the plane step.** `BugeaudEvertse2008/PlaneStep.lean` (std3):

  ```lean
  theorem Real.card_mem_plane_le (hb : 2 ≤ b) {ξ : ℝ} (hξ : IsAlgebraic ℚ ξ)
      (hirr : Irrational ξ) :
      ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (r t : ℕ → ℕ) (p : ℕ → ℤ),
        (∀ n, 2 * t n < t (n + 1)) → ∀ U : Submodule ℚ (Fin 3 → ℚ), U ≠ ⊤ → ∀ I : Finset ℕ,
        (∀ n ∈ I, r n < t n) → (∀ n ∈ I, 1 ≤ r n → ¬ (b : ℤ) ∣ p n) →
        (∀ n ∈ I, |(p n : ℝ)| ≤ (b : ℝ) ^ t n) →
        (∀ n ∈ I, |(b : ℝ) ^ t n * ξ - b ^ r n * ξ - p n| ≤ ((b : ℝ) ^ t n) ^ (-ε)) →
        (∀ n ∈ I, ![(b : ℚ) ^ t n, (b : ℚ) ^ r n, (p n : ℚ)] ∈ U) →
        (#I : ℝ) ≤ K * ε⁻¹ ^ 3 * (1 + log ε⁻¹) ^ 2
  ```

  **There is no threshold hypothesis**: the plane step disposes of its own threshold. The proof:
  * `z = x_{i₁} × x_{i₂}` for the two smallest `i₁ < i₂` in `I`. Every `x_n ∈ U` satisfies
    `z · x_n = 0` (`Submodule.det_eq_zero_of_forall_mem`), and `|zᵢ| ≤ 2 b^{2 t_{i₂}}`.
    `(z₂, z₃) ≠ 0`, because `x_{i₁}` and `x_{i₂}` are not proportional.
  * Two eliminations, each one BE.0 at `n = 2` (`Real.exists_lines_of_approx`), with
    `B = C = 2 max |zᵢ|`, exponents `1, −ε` at `∞` and `g_l, 0` at `l ∣ b`, `δ = ε`:
    * Eliminating `b^r` gives `|ξ(z₁+z₂) b^t + (ξz₃ − z₂) p| ≤ |z₂| (b^t)^{−ε}` ((7.13)), so
      the pairs `(b^t, p)` with `r ≥ 1` lie on `≤ K ε⁻³ (1 + log ε⁻¹)²` lines. Each line holds
      at most one of them, because `b ∤ p`.
    * Eliminating `p` gives `|(ξz₃ + z₁) b^t + (z₂ − ξz₃) b^r| ≤ |z₃| (b^t)^{−ε}`. This handles
      the pairs `(b^t, 1)` with `r = 0`, which are distinct since `t` is injective.
  * The determinant `±(ξz₃ − z₂)` is bounded below by Liouville,
    `|c₀ + c₁ ξ| ≥ (A Z^d)⁻¹` (`Real.exists_inv_le_abs_add_mul`, from DA's
    `Real.exists_pos_one_le_pow_natDegree_mul_abs_sub_div`). So the threshold is
    `K ε⁻¹ (1 + log max |zᵢ|) ≤ K' ε⁻¹ t_{i₂}`, and `Real.card_le_of_plane` counts the points
    above it.
  * The points below it are `i₁` and the `n` with `i₂ ≤ n ≤ i₂ + m`, where
    `2^m ≥ K' ε⁻¹`: by doubling, `t_n ≥ 2^{n−i₂} t_{i₂}`
    (`Nat.two_pow_mul_le_of_doubling`, in `Repetitions.lean`). There are `O(1 + log ε⁻¹)` of them.

  This is the paper's `k₀ + 2B(d, ε)` with `B ≍ ε⁻³`. The paper's threshold `(3 d t_{i₂})^{2/ε}`
  for Cor. 5.2 gives `k₀ ≍ log ε⁻¹` too.
- **BE.4 ✅ (2026-10-13) — the thresholds.** `BugeaudEvertse2008/Thresholds.lean` (std3):

  ```lean
  theorem Real.eventually_thresholds {C : ℕ} {v : ℝ} (hv : 0 < v) (hv7 : 7 * v < 1) {K L : ℝ}
      (hK : 0 < K) (hL : 0 < L) :
      ∀ᶠ N : ℕ in atTop, ∀ t : ℕ → ℕ, (∀ n, 2 * t n < t (n + 1)) →
        (∀ n, t n ≤ (2 * n + 2) ^ (C * (n + 1))) →
        0 < log (t (2 * N)) ^ (-v) ∧ log (t (2 * N)) ^ (-v) ≤ 1 ∧
        (∀ n, N ≤ n → n ≤ 2 * N → log (t (2 * N)) ^ (-v) ≤ log (t n) ^ (-v)) ∧
        (∀ n, N ≤ n → K * (log (t (2 * N)) ^ (-v))⁻¹ ≤ t n * L) ∧
        K * ((log (t (2 * N)) ^ (-v))⁻¹) ^ 7 * (1 + log (log (t (2 * N)) ^ (-v))⁻¹) ^ 4 < N
  ```

  The points are `x_n` for `N ≤ n < 2N`, which is `N` of them; the paper uses `N/2 ≤ n ≤ N`.
  With `ε = (log t_{2N})^{−v}`, the conjuncts are, in order:
  1. and 2. `0 < ε ≤ 1`.
  3. Lemma 6.1's exponents `(log t_n)^{−v}` are `≥ ε`.
  4. BE.2's threshold, with `L = log b`: `ε⁻¹ ≤ log t_{2N} = O(N²)` and `t_n ≥ 2^{n−1}`.
  5. The final count. With `X = log t_{2N} ≤ C (2N+1) log(4N+2)` and `δ = (1 − 7v)/10`:
     `log y ≤ y^δ/δ` gives `X ≤ A N^{1+δ}` and `1 + v log X ≤ (1 + v/δ) X^δ`. So the left side is
     `≤ K' N^{(1+δ)(7v+4δ)}`, and that exponent is `< 1`.
- **BE.5 ✅ (2026-10-13) — assembly.** `BugeaudEvertse2008/Theorem21.lean` (std3):
  `Real.frequently_lt_complexity` as in *Lean targets*, with `1/7`. Suppose not. Then
  `p(n) ≤ c n (log n)^u` for large `n`, with `c = max C 1` and `u = max η 0 < 1/7`. Take
  `v = (u + 1/7)/2`.
  * BE.1 (`Real.exists_approx_of_complexity_le`) gives `r, t, p`. It now also states
    `|p_n| ≤ b^{t_n}`, from `Real.digitsPrefix_sub_mem`.
  * BE.4 with `K = K₂ + K₂K₃` and `L = log b` gives one `N`.
  * BE.2 gives the planes `T` for `ε = (log t_{2N})^{−v}`.
  * The points `n ∈ Ico N (2N)` are split by plane (`card_eq_sum_card_fiberwise`), and BE.3
    bounds each fiber.
  * So `N ≤ K₂K₃ ε⁻⁷ (1 + log ε⁻¹)⁴ < N`.

  `#lint` on the five library files is clean.

  **Next, outside this repository:** the lean-code axiom `BugeaudEvertse.exists_pComplexity_gt`
  (`CITED/BugeaudEvertseComplexity.lean`, `η < 1/11`) can now be discharged, using the
  `pComplexity = complexity` bridge (see *Lean targets*).
- Optional, later: **Thm 3.1** and Cor. 3.2 (Cor. 5.2 enters through Lemma 8.1; check whether that
  use survives ST's threshold before planning it), Thm 9.1, 9.2.

## References

* [BE08] Y. Bugeaud, J.-H. Evertse, *On two notions of complexity of algebraic numbers*, Acta Arith.
  **133** (2008), 221–250; arXiv:0709.1560.
* [ES02] J.-H. Evertse, H. P. Schlickewei, *A quantitative version of the Absolute Subspace
  Theorem*, J. reine angew. Math. **548** (2002), 21–127.
* [EF13] J.-H. Evertse, R. G. Ferretti, *A further improvement of the Quantitative Subspace
  Theorem*, Ann. of Math. **177** (2013), 513–590.
* [AB07] B. Adamczewski, Y. Bugeaud, *On the complexity of algebraic numbers I*, Ann. of Math.
  **165** (2007), 547–565 (`AdamczewskiBugeaud2007/`).
