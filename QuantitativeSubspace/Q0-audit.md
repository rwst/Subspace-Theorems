# Q0 audit: how explicit is the landed proof?

A read-only audit of `DiophantineApproximation` Layers 2–6, plus the Layer 9 interface, done on
2026-09-30. It asks one question: can the landed qualitative proof be turned into an explicit
count of subspaces (Schmidt 1989, Schlickewei 1992) by bookkeeping alone? Paths are relative to
`DiophantineApproximation/`, and line numbers are as of that date.

Every main statement falls into one of three classes:

- **E**: the constant is written out explicitly in the statement.
- **X**: the statement says `∃ C` or `∀ᶠ … atTop`, but the proof builds a concrete value.
- **N**: genuinely non-explicit. The proof uses compactness, a limit, a Northcott selection, an
  infinite sequence, or a `choose` whose value feeds a count or a threshold.

## Verdict

**The analytic core is already quantitative.** Two things carry the proof, and both are
explicit:

- **Roth's lemma**: `RothLemma.lean:462` and `GeneralizedRothLemma.lean:189`.
- **The contradiction.** In both Roth and Subspace, it rules out a *finite* chain of `m + 1`
  levels with explicit `m`, explicit growth `ω`, and an explicit lower threshold. For Roth this
  is `roth_no_chain`, `RothTheorem.lean:663`. For Subspace it is `exists_forall_not_chain`,
  `PenultimateMinimum.lean:378`.

The number of approximation classes and the number of exceptional subspaces are explicit too.
Nothing in Layers 2–6 uses compactness.

What is not explicit falls into three groups. Each can be removed without new mathematics, but
the third is real work.

1. **Two ways a finite chain is turned into "finitely many".** Both throw the count away:
   - `exists_forall_approxSpan_mem`, `PenultimateMinimum.lean:684`, builds an unbounded chain
     with `choose` and derives a contradiction. `finite_setOf_approxSpan` (:748) and
     `SubspaceTheorem.lean:131` then apply Northcott to the low levels.
   - On the Roth side, the counting lemmas call qualitative Roth only to know that a set is
     finite (`CountingApproximations.lean:354`, `RothIntervals.lean:163`).

   **The fix:** cover the levels greedily by intervals, using the chain lemma that is already
   there.
2. **The enlargement from `S` to `S′` in 5.1** (`UnitNormalization.lean:278`). It picks an
   arbitrary element of each class and adds the primes dividing it, so `|S′|` has no bound. It
   also brings in the radius `R` of an arbitrary basis of the S-unit lattice (:112). `|S′|`
   feeds `m`, the number of classes and the number of exceptional subspaces.

   **The fix:** do not go through 5.1 and 6.2. Start from the systems of 9.1 (`systemSet`),
   whose points are already `S`-integral. Base-change to the Galois closure with 6.3's
   `conjSystem`, and absorb the constants of the system into the level.
3. **Thresholds built from arbitrary choices or from local data with no bound in terms of
   heights.** These affect thresholds, not counts. But DA 9.4 turns the band between Evertse's
   large-solution level `max (2H, N^{2N/δ})` and the proof's threshold `Q*` into extra intervals.
   The count sees `log (log Q* / log Q_E)`, so `Q*` must be bounded in terms of heights.

   | Constant | Where | Problem |
   |---|---|---|
   | `c_K = integralBasisHouse K` | `FieldMinima.lean:174` | Built from Mathlib's `Free.chooseBasis`; no bound in `\|D_K\|`. |
   | `A_K`, and through it Evertse's `C_E` | `SIntegerApproximation.lean:163`, `EvertseLemma.lean:357` | Same chosen basis. The recursion in `(A, n)` is explicit. |
   | `ζ_p`, and through it `C₄` | `ExceptionalSubspace.lean:393–395` | An arbitrary nonzero vector of the pattern space. |
   | `A`, `A₀`, `A₁`, `A₂`, `κ`, `C₅`, `C₆` | `SubspaceHeightBounds.lean:106, 395`; `MinimaBounds.lean:78` | Finite maxima and minima of local sizes of inverse matrices, not bounded by `H(L)`. |
   | The Möbius base point `c` | `RothIntervals.lean:271`, `RothInfinity.lean:282` | Taken from `infinite_compl.nonempty`. The `mobiusConst` bound goes through `\|α − c\|`. |
   | `covol(𝓞_K)` | `ApproximationVolume.lean:257` | Never rewritten as `2^{−r₂} √\|D_K\|`. |

   **The fix:** choose each of these by Cramer's rule, Siegel's lemma, or a reduced integral
   basis. For the Möbius point, take `c ∈ {0, …, s}` and bound `|α − c|` by Liouville's
   inequality.

## By layer

| Layer | State | Largest item |
|---|---|---|
| 2 (Roth machinery) | E everywhere except the `∃ D₀` of the index theorem, which is X with a closed-form witness (`AuxiliaryPolynomial.lean:708`) | Expose `D₀`. The multihomogeneous tail at `CountingVolume.lean:794` is a density bound, not a lattice count. Check how Layer 5 turns it into a count. |
| 3 (Roth) | The count is E: `rothLargeCount`, `CountingApproximations.lean:294`. The threshold `L` is X with an explicit witness (`RothTheorem.lean:677`). N only in the Möbius base point. | **Q0.1 is about 3–5 days of bookkeeping.** |
| 4 (parallelepipeds) | X throughout; N only in `finite_image_approxSpan` (`ApproximationRank.lean:394`), which the quantitative path can avoid | `c_K` and `A_K` come from a chosen basis. |
| 5 (Subspace machinery) | Chernoff, Siegel, the generalized Roth lemma and the key inequality are E. `exists_forall_not_chain` is X. | The `S′` enlargement is N. The 5.6 contradiction and Northcott step is N. `C₄` is N. |
| 6 (summit) | The grid, wedges and recovery are E or X. The base change does not multiply the count (`\|T_K\| ≤ \|T_E\|`). | The set `T` of 6.1 inherits 5.6's N. The small lines in 6.2 come from Northcott. |

The shape of the resulting count: the chain lives in dimension `M = C(N, p)`, and
`ω = 2(4/η)^{2^m}`. DA 9.4 takes only `log ω`. So the count comes out of the same shape as
Schmidt's and Schlickewei's, doubly exponential in `N`. That is what Q0 promises.

`m` grows like `(d + |S|)² / ε²` (through `AW`, `PenultimateMinimum.lean:402`), not like
`log |S| / ε²`.

## Prose that contradicts the code

- DA README 3.7-restated and 9.4 (around line 4358) call the Roth threshold *ineffective*. So
  do `RothSubspaceCount.lean:61` and the first draft of Q0.1. The docstrings of
  `CountingApproximations.lean` say "`L` is explicit", and they are right. The threshold is
  explicit apart from the Möbius base point, and only the OnePoint variant, which
  `RothSubspaceCount` consumes, has that point.
- DA README 9.4 says "nothing here produces" the interval result. The contrapositive of it
  exists already, as `exists_forall_not_chain`.
