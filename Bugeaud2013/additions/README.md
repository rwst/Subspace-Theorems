# `Bugeaud2013/additions/`: the exponent `δ` in (6.1)

The theorem (6.1) of `outgoing.md`, machine-checked with the standard axioms only. Let
`α = [0; a₁, a₂, …]` with `aₙ ≥ 1` be algebraic of degree at least 3. Then for every `C`, the
number of factors of length `n` of `a₁ a₂ …` exceeds `C n (log n)^δ` for infinitely many `n`:

| statement | `δ` | Subspace count used |
|---|---|---|
| `Nat.frequently_lt_encard_factors_of_lt_quarter` | `0 ≤ δ < 1/4` | Evertse–Ferretti 2013 (`Real.subspaceBound_three`, proved) |
| `Nat.frequently_lt_encard_factors_of_lt_ninth` | `0 ≤ δ < 1/9` | the shape of Evertse–Schlickewei 2002, `δ^{-(n+4)}` at `n = 4` (`SubspaceBound.mono`) |
| `Nat.frequently_lt_encard_factors` | `(b+1) δ < 1` | any `Real.SubspaceBound α b` |

ES02 itself is not formalized. Its exponent 8 is weaker than EF13's 3, so the `1/9` statement
follows from the proved EF13 count.

## Files, in import order

| file | content |
|---|---|
| `SubspaceCount.lean` | `Real.SubspaceBound`; EF13 for forms in `1, α, α²` ⇒ `subspaceBound_three` |
| `Liouville2.lean` | `b₀ + b₁α + b₂α² ≠ 0` and the quadratic Liouville bound (degree ≥ 3) |
| `Points.lean` | the abstract point inequalities `CFPoint`, `Doubling` heights, lines and planes |
| `Forms.lean` | the forms of the subspace applications; `det = ±z_j² Λ`; cross product |
| `Hyperplanes.lean` | the 3-variable applications on `z^⊥` and on `T₀ = {X₂ = X₃}` |
| `Subspaces.lean` | a proper subspace holds `O(log 1/ε)` points off `T₀` |
| `Count.lean` | `card_le_of_cfPoints`: `#points ≤ K ε^{-(b+1)} (1 + log ε⁻¹)³` |
| `CFPoints.lean` | the continued-fraction points `spadeVec` are `CFPoint`s |
| `Complexity.lean` | `exists_config`: from `p(ℓ) ≤ p`, a repetition that cannot slide left |
| `Asymptotics.lean` | the lengths `ℓ_k = E^{k+1}(k+1)^{2(k+1)}` and the final growth estimates |
| `Delta.lean` | the contradiction; the 1/4 and 1/9 instances |

## The proof

Suppose `p(ℓ) ≤ C ℓ (log ℓ)^δ` for all large `ℓ`. Then the alphabet is finite (`aₙ ≤ A`). At each
length `ℓ_k`, pigeonhole gives a repetition (`exists_config`). Its point `v_k` has height
`H_k = q_w q_{w+r}`, and the heights double. All the points satisfy the inequalities of
`CFPoint` with one exponent `ε`, where `ε⁻¹ ≍ (log ℓ_{2N})^δ ≍ (N log N)^δ`.

The count `card_le_of_cfPoints` covers the `N` points with `N ≤ k < 2N` in three steps:

1. One application of the 4-variable Subspace Theorem per cell of a `ρ`-grid.
2. On each proper subspace, the 3-variable application on `z^⊥` or on `T₀`.
3. Lines and planes hold `O(log 1/ε)` points (quadratic Liouville).

This bounds the `N` points by `O(N^{(b+1)δ(1+η)+3η})`. That is `o(N)` when `(b + 1)δ < 1`, a
contradiction.

## Checks (2026-10-10)

* Each module builds without errors or warnings, and no `set_option` is used.
* `#print axioms` gives `propext, Classical.choice, Quot.sound` for all three theorems.
* `#lint in Bugeaud2013.additions` is clean.
* `scripts/guards.sh` passes.
* `scripts/lint-style.sh`: headers conform. Its only complaint is the module name: lowercase
  `additions` is not UpperCamelCase. Renaming the directory to `Additions/` fixes it.
