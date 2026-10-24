# `BugeaudEvertse2008/Additions/`: Theorem 2.1 with `η < 1/2`

Bugeaud–Evertse's Theorem 2.1 with a better exponent, machine-checked with the standard axioms
only. Let `ξ = ofDigits a` be real algebraic irrational, with base-`b` digits `a`. Then for every
`C` the complexity of `a` exceeds `C n (log n)^η` for infinitely many `n`:

| statement | `η` | file |
|---|---|---|
| `Real.frequently_lt_complexity_of_lt_half` | `η < 1/2` | `Additions/Theorem21Half.lean` |
| `Real.frequently_lt_complexity_of_lt_third` | `η < 1/3` | `Additions/Theorem21Third.lean` |
| `Real.frequently_lt_complexity_of_lt_quarter` | `η < 1/4` | `Additions/Theorem21Quarter.lean` |
| `Real.frequently_lt_complexity` | `η < 1/7` | `Theorem21.lean` (BE08's route with EF13) |
| BE08, Theorem 2.1 | `η < 1/11` | the paper (ES02's count) |

The exponent `4 = 1 + 3` matches the `δ < 1/4` of `Bugeaud2013/Additions` (continued fractions)
and the `η < 1/4` of the `(3/2)^n` steering word (`Stephan2026a/QuantitativeTheorem.lean`). BE08's
`7 = 1 + 3 + 3` and `11 = 1 + 7 + 3` have an extra `ε⁻³` for the points on one plane.

## Files, in import order

| file | content |
|---|---|
| `PlaneLiouville.lean` | Liouville bound on a plane with `z₃ ≠ 0` (`Real.exists_mul_log_le_of_plane`); the plane step for large gaps, `K (1 + log ε⁻¹)` points (`Real.card_mem_plane_le_log`) |
| `SmallGap.lean` | one point per line (`Int.dvd_of_pow_sub_pow_mul_eq`); the two-variable step for small gaps, `K ε⁻³ (1 + log ε⁻¹)²` lines (`Real.exists_lines_of_small_gap`) |
| `Theorem21Quarter.lean` | the counting contradiction; **Thm 2.1 with `1/4`** |
| `Theorem21Third.lean` | the interval forms of the three- and two-variable steps; the count `A ε⁻³ (1 + log ε⁻¹)²` (`Real.card_le_of_approx_third`); **Thm 2.1 with `1/3`** |
| `Theorem21Half.lean` | the three-variable step with one interval result for all classes; the count `A ε⁻² (1 + log ε⁻¹)²` (`Real.card_le_of_approx_half`); **Thm 2.1 with `1/2`** |

The library files used: `Repetitions.lean` (Lemma 6.1), `ThreeVariable.lean` (the planes),
`PlaneStep.lean` (`Real.exists_plane_eq`, Liouville `Real.exists_inv_le_abs_add_mul`), and DA's
`Real.eventually_doubling_thresholds` at `(p, q) = (4, 3)`.

## The proof

Lemma 6.1 gives the points `x_n = (b^{t_n}, b^{r_n}, p_n)` with `2 t_n < t_{n+1}`,
`|b^{t_n} ξ − b^{r_n} ξ − p_n| ≤ (b^{t_n})^{−ε}` and `b ∤ p_n` when `r_n ≥ 1`. The `N` points
`N ≤ n < 2N` are split by their gap `s_n = t_n − r_n`.

1. **Large gap, `ε t < 4 s`.** BE08's three-variable step puts them into `K ε⁻⁴ (1 + log ε⁻¹)²`
   planes. On a plane `z₁ X₁ + z₂ X₂ + z₃ X₃ = 0`, with `|zᵢ| ≤ Z = 2 b^{2 t_{i₂}}` the cross
   product of its first two points, there are two cases.
   * **`z₃ ≠ 0`.** Eliminating `p` gives `b^r Γ = z₃ (b^t ξ − b^r ξ − p)` with
     `Γ = (z₃ ξ + z₁) b^s + (z₂ − z₃ ξ)`, so `|Γ| ≤ Z`. Liouville at `z₁ + z₃ ξ` gives
     `b^s ≤ Z^{O(d)}`. Liouville at `Γ = z₃ (b^s − 1) ξ + (z₁ b^s + z₂) ≠ 0` then gives
     `b^r ≤ Z^{O(d²)}`. So `t ≤ C_ξ t_{i₂}`: a window of the doubling sequence, `O(1)` points. No
     Subspace Theorem and no `ε` are involved. BE08 spend a two-variable Subspace count here.
   * **`z₃ = 0`.** Then `z₁ b^t = −z₂ b^r`, so the gap `s₀` is the same at every point of the
     plane. These planes are Ridout problems. A large gap gives `t < 4 s₀ / ε ≤ 4 t_{i₁} / ε`: a
     window of ratio `4/ε`, `O(log ε⁻¹)` points.
2. **Small gap, `4 s ≤ ε t`.** One more application of EF13 for all of them, in two variables:
   `y = (b^t − b^r, p)`, with the forms `ξ X₀ − X₁` and `X₀` at `∞` and the coordinates at
   `l ∣ b`. Since `|y₀|_l = |b^r|_l` and `r ≥ (1 − ε/4) t`, the exponents sum to `−3ε/4`. That
   gives `K ε⁻³ (1 + log ε⁻¹)²` lines. Two points on a line have
   `(b^{t₁} − b^{r₁}) p₂ = (b^{t₂} − b^{r₂}) p₁` with `r₁ < r₂`, hence `b ∣ p₂`, because
   `b^{s₁} − 1` is prime to `b`. So each line holds at most one point.

Total: `N ≤ K' ε⁻⁴ (1 + log ε⁻¹)³`, with `ε⁻¹ = (log t_{2N})^v = N^{v + o(1)}`, so `4v < 1` is a
contradiction. The split by the size of the gap is the one of the steering word's proof.

## `1/3`: the interval form

EF13's `δ⁻³` subspaces are one exceptional subspace, `δ⁻² log δ⁻¹` intervals `[s, ω₀ s)` of
`log |x|` (`ω₀ ≍ δ⁻¹ log`), and `δ⁻¹ log δ⁻¹` windows of the gap principle in each interval. The
points `x_n` have `log |x_n| = t_n log b` with `2 t_n < t_{n+1}`, so an interval holds
`O(log ε⁻¹)` of them and the gap principle is not needed (`Real.SubspaceIntervalWith`,
`QuantitativeSubspace/RealFormInterval.lean`; `Real.card_le_of_forall_mem_window`).

1. **Large gap.** In each of the `k ≤ 3/ε` classes: one plane, holding `O(1 + log ε⁻¹)` points
   (`Real.card_mem_plane_le_log`), and `O(ε⁻² log ε⁻¹)` intervals
   (`Real.exists_plane_intervals_of_approx`).
2. **Small gap.** One line, holding at most one point, and `O(ε⁻² log ε⁻¹)` intervals
   (`Real.exists_line_intervals_of_small_gap`).

Total `N ≤ A ε⁻³ (1 + log ε⁻¹)²` (`Real.card_le_of_approx_third`), a contradiction for `3v < 1`.
The systems of the classes are shared with the count form (`Real.approx_class_hyps`,
`Real.approx_class_mem`, `Real.gap_hyps`, `Real.gap_mem`).

## `1/2`: one interval result for all classes

The `k ≤ 3/ε` classes of `r/t` have the same forms `approxForms` and differ only in their
exponents. The interval form for a set of exponents (`Real.SubspaceIntervalFamilyWith`,
`QuantitativeSubspace/RealFormFamily.lean`, from EF13's Theorem 2.3 for a set of exponents) puts
the points of all classes into `K` planes, `K` independent of `ε`, or into `O(ε⁻² log ε⁻¹)`
intervals (`Real.exists_plane_intervals_family_of_approx`). Each plane holds `O(1 + log ε⁻¹)`
points as before, the small gaps are as before, and `N ≤ A ε⁻² (1 + log ε⁻¹)²`
(`Real.card_le_of_approx_half`), a contradiction for `2v < 1`.

## Literature

The results of this directory first appear in R. Stephan, *The exponent `1/4` in three complexity
bounds: integer bases, continued fractions, and the `(3/2)^n` steering word*, arXiv:2610.30937
(2026), §3: Theorem 1.1 is `Real.frequently_lt_complexity_of_lt_quarter`, Lemmas 3.4–3.7 are the
lemmas of `PlaneLiouville.lean` and `SmallGap.lean`, and Remark 6.1 is the `1/7` of
`Theorem21.lean`. Its Appendix A maps every numbered statement to its Lean declaration.

The `1/2` of `Theorem21Half.lean` is Theorem A of R. Stephan, *The Evertse–Ferretti interval
result for a set of weights, and the exponent `1/2` in three complexity bounds* (2026), §5:
Propositions 5.1–5.2 are `Real.exists_plane_intervals_family_of_approx` and
`Real.card_le_of_approx_half`. Its Remark 8.1 is the `1/3` of `Theorem21Third.lean`, and its
Appendix A maps every numbered statement to its Lean declaration.

## Checks (2026-10-21)

* `lake build BugeaudEvertse2008`: no errors, no warnings, no `set_option`.
* `#print axioms Real.frequently_lt_complexity_of_lt_quarter`: `propext, Classical.choice,
  Quot.sound`. The same for `Real.frequently_lt_complexity_of_lt_third` and
  `Real.frequently_lt_complexity_of_lt_half` (2026-10-24).
* `scripts/check.sh`: see the BE08 README.
