# Outgoing: the exponent `δ` in (6.1), continued-fraction version

Status: **paper-level derivation, not yet checked independently.** Kept here for later, to be
turned into a Lean milestone once the paper itself (Thm 3.1 in particular) is formalized.

## Origin

Mail exchange with Y. Bugeaud (2026-10). I wrote to him about his remark in the 2015 survey
(`Expansions of algebraic numbers`, *Four Faces of Number Theory*, EMS 2015, after Thm 12.2):
"Using the recent results of [EF13] allows us to show that Theorem 12.2 holds for η in a
slightly larger interval than [0, 1/11)", and that Evertse–Ferretti 2013 actually gives `1/7`.
He replied: "I can believe this, yes. I announced somewhere (at the end of Bugeaud 2013) an
analogous result for continued fraction expansions. I never wrote the details. Perhaps you may
find a suitable value for delta."

What he means is **(6.1) in §6 of this paper**: if `a ∈ ℤ_{≥1}^ℕ` and `[0; a₁, a₂, …]` is
algebraic of degree `≥ 3`, there is `δ > 0` with

```text
limsup_{n→∞} p(n, a) / (n (log n)^δ) = +∞,
```

"proceeding as in [15] and [18]" (Bugeaud 2008 Lincei; Bugeaud–Evertse 2008 Acta Arith.,
= BE08). The 2015 survey confirms (after its Thm 12.4): "The analogues of Theorems 12.2 and 12.3
[for continued fractions] have not been written yet".

## Where `1/11` and `1/7` come from (BE08 §7)

`δ < 1/(A + B)`. `A` = exponent of `ε⁻¹` in the 3-dimensional subspace count, plus 1 for the
`k = ⌊2/ε⌋ + 1` exponent grid (7.6). `B = 3` from the quantitative Ridout count (7.19) on each
plane. ES02: `A = 7 + 1`, so `1/11`. EF13 (`δ⁻³`): `A = 3 + 1`, so `1/7`.

## The continued-fraction version: any `δ < 1/4` (EF13), `δ < 1/9` (ES02)

Assume `p(n, a) ≤ c n (log n)^{v+η}`. The alphabet is then finite (`p(1) < ∞`), so
`q_ℓ^{1/ℓ}` is bounded. Notation of the proof of Thm 3.1: prefixes `W_n U_n V_n U_n`,
`w = |W|, u = |U|, v = |V|`, `m = w + u + v`, points `v_n ∈ ℤ⁴`, forms `L₁, …, L₄`.

0. **Points.** As in BE08 Lemma 6.1: `|U| ≥ c ℓ (log ℓ)^{-u}`, `|W|` minimal so that
   `a_w ≠ a_m` (or `W` empty), and a subsequence with `t_{n+1} > 2 t_n` (`t = |WUV|`), hence
   `log H(v_n)` at least doubles up to a constant factor. Then, with `H = q_w q_m ≍ H(v_n)`
   (the lower bound uses `a_w ≠ a_m`, bounded partial quotients and the mirror formula) and
   `ρ = log q_w / log H ∈ [0, 1/2]`:
   `|L₁| ≤ H^{-1-ε}` ((3.4), since `q_{w+2u+v} ≥ q_m 2^{(u-1)/2}`), `|L₂| ≤ H^{2ρ-1}` (3.2),
   `|L₃| ≤ H^{1-2ρ}` (3.3), `|L₄| ≤ H`, with `ε = (log t_N)^{-v}`, `ε⁻¹ ≤ N^{v+η}`.
   Non-collinearity: `v_n ∥ v_{n'}` forces `α_{n'}` to be a root of `P_n`; Liouville
   (`|α - β| ≫ H(β)^{-d}`, `β` quadratic) bounds `log H(v_{n'}) ≪ log H(v_n)`, so each
   proportionality class has `O(1)` members.
1. **First application (`n = 4`).** Grid of `⌈8/ε⌉ + 1` cells in `ρ`; exponents
   `(-1-ε, 2ρ⁺-1, 1-2ρ⁻, 1)`, max `1`, sum `≤ -ε/2`. EF13 (Evertse 2010 Thm 2.1): the `v_n`,
   `N/2 ≤ n ≤ N`, lie in `≤ cells · C ε⁻³ log²(1/ε) ≈ ε⁻⁴` proper subspaces. All points are
   large (`log H(v_n) ≫ 2^{N/2}`), so no small solutions.
2. **A hyperplane `T = x^⊥ ≠ T₀ := {X₂ = X₃}` holds `O(1)` points.** Late points
   (`log H(v_n) ≥ C log H(x)`; only `O(1)` points are early, by the doubling):
   - `ρ ≥ 1/4` (long `W`, `q_w ≥ H(x)^{C₁}`): Bugeaud's Claim. (3.14) gives
     `|Q_n - 1| · |Λ| ≪ |x| q_w^{-2}`, `Λ = x₁ + (x₂+x₃)α + x₄α²`. If `Λ ≠ 0`, Liouville gives
     `|Λ| ≫ H(x)^{-(d-1)}`, and `|Q_n - 1| ≥ (A+1)^{-3}` because `a_w ≠ a_m` (mirror formula,
     bounded alphabet; Lean: `head_gap`). Contradiction. If `Λ = 0`, then `x ∝ (0, 1, -1, 0)`,
     i.e. `T = T₀`.
   - `ρ ≤ 1/4` (short `W`): on `T`, `L₁|_T, L₂|_T` are independent (else `α` rational), and one
     of `L₃|_T, L₄|_T` completes them; the exponents `(-1-ε, 2ρ-1, 1)` sum to `≤ -1/2`, so EF13
     with `δ = 1/2` (count `O_d(1)`, threshold `≲ log H(x)`) puts these points in `O(1)` planes.
     In a plane `P`: if `L₁|_P, L₂|_P` are independent, `|v| ≲ H(P)^C (H^{-1-ε} + H^{-1/2}) < 1`.
     If they are dependent, then `|L₂(v)| ≍ |L₁(v)| ≤ H^{-1-ε}`, against
     `|L₂(v_n)| ≥ q_w |q_{m-1}α - p_{m-1}| ≥ q_w / 2q_m ≥ H^{-1}/2`. (The two terms of (3.2)
     have the same sign.)
3. **`T₀`.** Bugeaud's 3-form system `L'''` (after the Claim) with the same grid:
   `≈ ε⁻⁴` planes, each with `O(1)` late points: long `W` by the same Claim argument for
   `t₁ + t₂α + t₃α²` ((3.17)–(3.18)), short `W` by the plane argument of step 2.

Total: `N/2 ≤ ε^{-4-o(1)} ≤ N^{4(v+η)+o(1)}`, a contradiction once `4v < 1`.

**Why this beats `1/7`.** In base `b` every plane needs a Ridout count (`B = 3`). For continued
fractions the plane step is elementary (the rigidity `|Q_n - 1| ≫ 1` from the mirror formula),
and only the one exceptional subspace `T₀` needs a second subspace count. That count is
`≈ ε⁻⁴`, which adds to the first rather than multiplying it.

**To check by hand:** step 2 in full (short-`W` case, the degenerate planes) and step 3. If they
hold, the answer to Bugeaud's question is `δ = 1/4⁻`.

## Lean

`../tmp/BugeaudCF.lean` (a temp file, compiled with `lake env lean`, no `sorry`; `#print axioms`
not yet run) proves the quantitative core:

- `exists_cell`: the `ρ`-grid, `⌈8/ε⌉ + 1` cells, max `1`, sum `≤ -ε/2`.
- `head_gap`: `[0; a, …]` and `[0; a', …]` with `a < a' ≤ A` differ by `≥ (A+1)⁻³`.
- `efLargeCount_le_log`: `QuantitativeSubspace`'s `NumberField.efLargeCount_le_ef` (EF13) at
  `n = 3, 4`, `δ = ε/2`.
- `cfBudget_le`: budget `≤ budgetConst · ε⁻⁴ · log(24e/ε)²`.
- `budget_lt_half`: `ε⁻¹ ≤ N^w`, `w < 1/4` ⇒ budget `< N/2` for large `N`.
- `false_of_reduction`: (6.1) for any `δ < 1/4`, **given** the reduction (steps 0–3) as
  hypothesis `hred`.

Formalizing steps 0–3 needs the paper's Thm 3.1 machinery (this directory) plus the
quantitative counts on subspaces, so it comes after the paper.
