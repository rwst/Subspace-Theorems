# Roadmap: the quantitative Subspace Theorem

The qualitative Subspace Theorem says that the solutions of a Diophantine inequality lie in a
finite union of proper subspaces. The **quantitative** Subspace Theorem gives an explicit upper
bound for the number of those subspaces. The bound depends only on the dimension `n`, the
exponent `δ`, the number of places and the degrees of the coefficients. It does not depend on the
heights of the forms. That uniformity is what the counting applications use: the uniform bounds
for unit equations, the counts for norm-form equations, and the complexity and transcendence
measures of Bugeaud–Evertse and Adamczewski–Bugeaud.

This roadmap is **paper-level**. It names the papers, says what each one contributes and consumes,
and orders them into layers that end at the best bounds known. It has no milestones stated to Lean
precision yet and no Lean files. It stands on the
[`DiophantineApproximation`](../DiophantineApproximation/README.md) roadmap, which lists this
theory under *Long horizon*, and on [`ArithmeticHeights`](../ArithmeticHeights/README.md). It
rebuilds nothing from either.

*Compiled on 2026-09-30. Bibliographic data were checked against the authors' publication lists
and arXiv where marked ✓. Entries marked (?) still need checking against the paper.*

## ⚠ The roadmap is preliminary

The layer boundaries below come from reading abstracts, surveys and the introductions of the
papers, not from their proofs. Q0 and Q1 have since been checked against the proofs. The two
dependencies this section used to flag as unverified are settled (2026-09-30):

- **EF13 still uses Ev95.** EF13 Prop. 12.1 is Ev96 Lemma 26, a Roth lemma at grid points of
  hyperplanes `T_h ⊂ ℚ̄^N` with `r_h / r_{h+1} ≥ 2m² / ε`. EF13 says it "was deduced from a sharp
  version of Roth's Lemma, and ultimately goes back to Faltings' Product Theorem". The
  Faltings–Wüstholz ideas EF13 imports replace Schmidt's auxiliary polynomial, not Roth's lemma.
- **Ev95 needs the multiprojective case in full, plus Arakelov heights.** It proves the product
  theorem only for `ℙ^{n₁} × ⋯ × ℙ^{n_m}`, but for arbitrary subvarieties of that space. Its
  Roth lemma (Thm 3), although about `(ℙ¹)^m`, runs through the general intersection theory of
  §2 and the Faltings height of subvarieties of §3. See Layer Q1.

Read the relevant sections of the papers before turning a layer into Lean milestones.

## The target: what "best" means

There is no single "best quantitative Subspace Theorem". There are five independent axes, each
with its own record holder. The summit of this roadmap is the conjunction of the five.

| Axis | Best known | Status in this repo |
|---|---|---|
| Number of subspaces containing the **large** solutions, linear forms, number field `K` | Evertse–Ferretti 2013: `10^9 · 2^{2n} · n^{14} · δ^{-3} · log(3δ^{-1}RD) · log(δ^{-1} log 3RD)` (as stated in Evertse 2010, Thm 2.1) | Q0 landed at Schmidt's parameters (Q0.3). Q1 started: the multigraded Hilbert polynomial and its degrees (Q1.1a–d, the excess Bézout inequality modulo Cohen–Macaulay) and the multiplicity estimate against degree (Q1.1e, with the transversal equations and the positivity of the degree in characteristic `0`, i.e. Rémond 2001 Prop. 2.1 modulo unmixedness) are in `ForMathlib`. Q1.2, the geometric product theorem with its degree bound and corollary (Rémond 2001 Thm 1.1 and Cor. 1.1, i.e. Ev95 Thm 1 and Corollary with better constants), is in `QuantitativeSubspace/`, modulo the same unmixedness. DA 9.4 turns any *interval result* into this kind of count. DA 6.1 now has one with explicit counts and ratio (Q0.2d), and its threshold `Q₀` is at most `a · (formLogHeight + log |D_K| + ∑ log N(v) + 1)` with `a` explicit in `N`, `d`, `|S|`, `ε` and `A` (Q0.2e, `parametricThreshold_le`). Q0.3 feeds it to 9.4: the solutions of a normalized system above `X₀`, linear in `log H`, lie in a number of subspaces depending on `n`, `δ`, the degrees, the number of places and `|S|` alone; all solutions in that plus `O(log X₀)` plus 9.3's count (`exists_finset_submodule_of_isNormalizedSystem`). |
| Number of subspaces containing the **small** solutions | Evertse 2010, Thm 2.2: `δ^{-1}((10^3 n)^{nd} + 4n log log 4H)`; over `ℚ`, `δ^{-1}(10^{3n} + 4n log log 4H)` | **Landed**, DA 9.3. |
| **Absolute** form: points in `ℚ̄ⁿ`, count independent of the field | Evertse–Schlickewei 2002 (parametric, twisted heights), sharpened by Evertse–Ferretti 2013 | Not started. |
| `n = 2`: **quantitative Roth / Ridout** | Bugeaud–Evertse 2008, Appendix (improving Davenport–Roth 1955, Bombieri–van der Poorten 1988, Evertse 1996/97) | Davenport–Roth-strength count landed, DA 3.7. |
| **Higher degree**: hypersurfaces and projective varieties | Evertse–Ferretti 2008 (general position); Quang 2022 (subgeneral position, better Chow-weight bound) | Not started. |

**No improvement of the Evertse–Ferretti 2013 count for linear forms was found in the literature
up to 2026-09.** Searches of arXiv and of Evertse's publication list turned up extensions in other
directions (higher degree, subgeneral position, big linear systems) but nothing that lowers the
`2^{2n} δ^{-3}` shape. Treat EF13 as the summit for linear forms and recheck this claim before the
last layer starts.

## The line of papers

In chronological order. "Consumes" names the earlier results each paper actually uses.

### The linear case

| Ref | Paper | Contributes | Consumes |
|---|---|---|---|
| DR55 | H. Davenport, K. F. Roth, *Rational approximations to algebraic numbers*, Mathematika **2** (1955), 160–167. | First count for Roth's theorem. | Roth 1955. |
| BvdP88 | E. Bombieri, A. J. van der Poorten, *Some quantitative results related to Roth's Theorem*, J. Austral. Math. Soc. **45** (1988), 233–248. ✓ | Much better quantitative Roth. | Roth's method, explicit. |
| Sch89 | W. M. Schmidt, *The Subspace Theorem in diophantine approximations*, Compositio Math. **69** (1989), 121–173. ✓ | **The first quantitative Subspace Theorem.** Rational points, algebraic coefficients, archimedean place only. Count `(2d)^{2^{26n} δ^{-2}}` (as quoted by Bugeaud 2011), doubly exponential in `n`. Introduces the split into large and small solutions. | Schmidt 1972 with every constant tracked. The classical Roth lemma is enough. |
| Sch92 | H. P. Schlickewei, *The quantitative Subspace Theorem for number fields*, Compositio Math. **82** (1992), 245–273. ✓ | Sch89 over a number field with finitely many places, archimedean and non-archimedean. The form every application quotes. | Sch89, Schlickewei 1977. |
| Fa91 | G. Faltings, *Diophantine approximation on abelian varieties*, Ann. of Math. **133** (1991), 549–576. | **The product theorem**, a replacement for Roth's lemma that is much stronger in the number of variables. | Intersection theory on products of projective spaces. |
| Ev95 | J.-H. Evertse, *An explicit version of Faltings' Product theorem and an improvement of Roth's lemma*, Acta Arith. **73** (1995), 215–248. ✓ | Fa91 with explicit constants, specialized to products of projective spaces, and the resulting **improved Roth lemma**. This is the input that makes the dependence on `δ⁻¹` polynomial. Free at `matwbn.icm.edu.pl/ksiazki/aa/aa73/aa7332.pdf`. | Fa91; Fulton's intersection theory on `ℙ^{n₁} × ⋯ × ℙ^{n_m}` (cycles, rational equivalence, lengths, Cohen–Macaulay multiplicities); the Faltings height of subvarieties (Gillet–Soulé, in Gubler's 1994 form), with Chern forms and Wirtinger's theorem. |
| Ré01 | G. Rémond, *Sur le théorème du produit*, J. Théor. Nombres Bordeaux **13** (2001), 287–302. ✓ | The product theorem with sharper constants (`δ_i/δ_{i+1} ≥ (m/ε)^{codim Z}`), over a number field, **without Arakelov theory**: Samuel multiplicity and Kähler differentials. The planned Q1 source. | Ev95, Ferretti 1996, Philippon's zero estimates; Rémond's multiprojective elimination (LNM 1752, Chs. 5 and 7). |
| Ev96 | J.-H. Evertse, *An improvement of the quantitative Subspace theorem*, Compositio Math. **101** (1996), 225–311. ✓ | Replaces Sch92's doubly exponential count by a singly exponential one (?) (copy the exact bound from the paper). Also contains the lemma that DA 4.4 builds. | Sch92, Ev95. |
| RT96 | D. Roy, J. L. Thunder, *An absolute Siegel's lemma*, J. reine angew. Math. **476** (1996), 1–26. ✓ | Siegel's lemma over `ℚ̄` with constants independent of the field. | Geometry of numbers over number fields. |
| Zh95 | S. Zhang, *Positive line bundles on arithmetic varieties*, J. Amer. Math. Soc. **8** (1995), 187–221. (?) | The theorem on successive minima that yields an **absolute Minkowski theorem**. | Arakelov theory. ⚠ This is a heavy dependency. Check whether RT96, or the adelic form of Minkowski's second theorem, is enough for ES02. |
| ES99 | J.-H. Evertse, H. P. Schlickewei, *The Absolute Subspace Theorem and linear equations with unknowns from a multiplicative group*, in *Number Theory in Progress* (Zakopane 1997), de Gruyter 1999, 121–142. ✓ | States the **absolute** Subspace Theorem, with points in `ℚ̄ⁿ`, and shows what it is for. | Sch72 and Sch77. |
| ES02 | J.-H. Evertse, H. P. Schlickewei, *A quantitative version of the Absolute Subspace Theorem*, J. reine angew. Math. **548** (2002), 21–127. ✓ | **The quantitative absolute parametric Subspace Theorem**: twisted heights `H_{Q,L,c}`, an interval result, and the count `4^{(n+9)^2} δ^{-n-4} log(2RD) log log(2RD)` for the large solutions (Evertse 2010, Thm B). The source of every uniform count in ESS02 and BE08. | Ev95, Ev96, RT96, and an absolute Minkowski theorem. |
| Ev10 | J.-H. Evertse, *On the Quantitative Subspace Theorem*, Zap. Nauchn. Sem. POMI **377** (2010), 217–240; J. Math. Sci. **171** (2010), 824–837; arXiv:1008.2268. ✓ | Survey of ES02 → EF13. Also proves the new gap principle and the **small-solutions bound**, which is the current record on that axis. | ES02, EF13 (announced). **The source of DA Layer 9.** |
| EF13 | J.-H. Evertse, R. G. Ferretti, *A further improvement of the Quantitative Subspace Theorem*, Ann. of Math. **177** (2013), 513–590; arXiv:1008.2340. ✓ | **The current best count.** It lowers the dependence on `n` from `4^{n²}` to `2^{2n}` and the dependence on `δ` from `δ^{-n-4}` to `δ^{-3}`. It also gives a sharper interval result (Evertse 2010, Thm 3.1). | ES02, the Faltings–Wüstholz method (FW94), and the Chow-weight estimates of Ferretti and EF02. Ev95, through Ev96 Lemma 26 (EF13 Prop. 12.1). |

### The geometric route (Faltings–Wüstholz, Chow weights)

EF13 is a hybrid. It takes Schmidt's 1972 proof, as refined in ES02, and combines it with ideas
from the Faltings–Wüstholz proof. The papers below are where those ideas and the needed estimates
are developed.

| Ref | Paper | Contributes | Consumes |
|---|---|---|---|
| FW94 | G. Faltings, G. Wüstholz, *Diophantine approximations on projective spaces*, Invent. Math. **116** (1994), 109–138. | A second proof of the Subspace Theorem, with filtrations and a stability argument. It also covers polynomials of higher degree. Taken alone, its explicit count is far worse than ES02's. | Fa91. |
| Fe00 | R. G. Ferretti, *Mumford's degree of contact and Diophantine approximations*, Compositio Math. **121** (2000), 247–262. ✓ | Recasts the FW94 framework through **Chow weights** (Mumford's degree of contact). | FW94, Chow forms. |
| EF02 | J.-H. Evertse, R. G. Ferretti, *Diophantine inequalities on projective varieties*, IMRN 2002, no. 25, 1295–1330. | The Subspace Theorem on a projective variety, and the **lower bound for Chow weights** that the later quantitative work uses. | Fe00, ES02. |
| Fe03 | R. G. Ferretti, *Diophantine approximations and toric deformations*, Duke Math. J. **118** (2003), 493–522. ✓ | Toric deformations and Chow polytopes. Bézout's theorem for the degree of contact, via arithmetic Bézout. | Fe00, Arakelov intersection theory. |

### Beyond linear forms (the newest work)

| Ref | Paper | Contributes |
|---|---|---|
| EF08 | J.-H. Evertse, R. G. Ferretti, *A generalization of the Subspace Theorem with polynomials of higher degree*, in *Diophantine Approximation, Festschrift for Wolfgang Schmidt*, Dev. Math. **16**, Springer 2008, 175–198; arXiv:math/0408381. ✓ | Generalizes the Corvaja–Zannier extension of the Subspace Theorem: polynomials of any degree, points on a projective variety. Gives **explicit bounds for the number and degrees** of the exceptional subvarieties. It works by reduction to ES02. |
| Qu22 | Si Duc Quang, *Quantitative subspace theorem and general form of second main theorem for higher degree polynomials*, Manuscripta Math. **169** (2022), 519–547; arXiv:1808.10286. ✓ | A new lower bound for Chow weights, giving a quantitative Subspace Theorem for hypersurfaces in **subgeneral position** on a variety. It improves on EF08 in that setting. |
| Qu22b | Si Duc Quang, *Some generalizations of Schmidt's subspace theorem*, arXiv:2212.02471. (?) venue | A quantitative version for arbitrary families of higher-degree polynomials, and a qualitative version for families of closed subschemes. |
| Gr23 | N. Grieve, *On qualitative aspects of the quantitative subspace theorem*, arXiv:2306.16583, accepted in Rocky Mountain J. Math. (?) year | Starts from the parametric theorem of EF13. Gives Diophantine inequalities for **big linear systems** and a partition ("linear scattering") of the exceptional set, with an application to the Ru–Vojta inequalities. |

Excluded on purpose:

- **Vojta's refinement** (Vojta 1989; Schmidt, *Vojta's refinement of the Subspace Theorem*, Trans.
  AMS **340** (1993) (?)). It is about the shape of the exceptional set, not about how many
  subspaces there are.
- **Moving targets** (Ru–Vojta 1997).
- **Uniform unit-equation bounds** (ESS02; Amoroso–Viada 2009). Amoroso–Viada's better bound does
  not come from the Subspace Theorem at all.

Each of these is a consumer or a sibling of this roadmap, not a step on the way to the best count.

## The build, in layers

Each layer names its papers and the gap in Mathlib and in this repository that it has to fill.
"DA n.m" is a milestone of the `DiophantineApproximation` roadmap.

### Layer Q0: the explicit machinery (Schmidt 1989, Schlickewei 1992)

Run the landed proof of DA Layers 2–6 again with every constant made explicit. The output is an
**interval result**: all large solutions have heights in at most `m` intervals `[Qᵢ, Qᵢ^ω)`, with
`m` and `ω` explicit. Feed it to DA 9.4. That gives Sch92's count, doubly exponential in `n`, for
the forms and places DA 6.4 already handles.

This is the first genuinely quantitative Subspace Theorem that can land here. It needs **no new
mathematics**, only bookkeeping, and the DA long-horizon section notes that the Roth lemma of DA
2.7 is enough for it.

The landed proof was audited for this layer; see [`Q0-audit.md`](Q0-audit.md). Its analytic core
is already quantitative. The contradiction rules out a finite chain of explicit length and
growth, both for Roth (`roth_no_chain`) and for Subspace (`exists_forall_not_chain`). The work
is to stop throwing that away, and to make the thresholds explicit. The milestones below
replace the earlier sketch.

- **Q0.1 Quantitative Roth** (3–5 days, bookkeeping). All steps are **landed**:
  - **Landed:** `δ` and `L` are definitions. `NumberField.rothDelta` and
    `NumberField.rothThreshold` are closed forms, and `roth_no_moving_chain` and
    `roth_no_chain` are stated with them.
  - **Landed:** 6.5.7 is stated for finite sets. `NumberField.card_le_rothLargeCount` says every
    finite set of solutions above `rothLargeThreshold` has at most `rothLargeCount` elements.
    `NumberField.ncard_setOf_lt_absLogHeight₁_le` derives finiteness from that bound, not from
    Roth's theorem. That threshold is linear in the heights of the targets.
  - **Landed:** the interval result `exists_forall_mem_interval_of_prod_min_one_le` holds above
    `rothLargeThreshold`, and its finiteness also comes from the count.
  - **Landed:** the Möbius base point. It is a natural number `j ≤ s` missing from the targets
    (pigeonhole), so the height shift is `mobiusShift s = log (2 (s + 1))`. Liouville's inequality
    at one place (`inv_mulHeight₁_le_min_one_of_infinitePlace`/`…_of_finitePlace`) bounds
    `mobiusConst` by `2 H(a − j) ^ 2` (`AbsoluteValue.mobiusConst_coe_le`,
    `NumberField.mobiusConst_le_exp`). `exists_forall_mem_interval_of_prod_onePointApprox_le`
    now holds above `NumberField.rothOnePointThreshold`, a closed form in the heights of the
    targets, `C`, `κ`, `s` and the degrees.
  - **Landed:** the system constants. `exists_finset_submodule_of_card_eq_two` now holds above
    `NumberField.systemRothThreshold s r [F : ℚ] [K : ℚ] δ H`, a formula in the coefficient
    height bound `H` of `IsNormalizedSystem`. The threshold of the interval result was refactored
    into the scalar, monotone `NumberField.rothOnePointBound`. The statement of record in
    `Challenge/` and `ChallengeFlat.lean` was regenerated.
  - **Landed:** the Davenport–Roth total count. `NumberField.card_le_rothTotalCount` and
    `NumberField.ncard_setOf_rothGapHeight_lt_absLogHeight₁_le` bound every solution above
    `rothGapHeight κ s = log 16 / (c − 1)` by `rothTotalCount κ s r [F : ℚ] Ht`: the window
    lemma on `(log 16 / (c − 1), rothLargeThreshold]` plus `rothLargeCount`. It is
    `A(κ, s, r) + B(κ, s) · ⌈log (max ((1 + Ht) / δ) X₀ / X₀) / log q⌉`, so `O(log (1 + Ht))` in
    the sum `Ht` of the target heights. Finiteness comes from the count, not from Northcott.
    Q0.1 is complete, apart from the solutions below `log 16 / (c − 1)`, which the book also
    leaves to Northcott.
- **Q0.2a An interval version of 5.6.** **Landed.** `NumberField.exists_forall_mem_interval_approxSpan`
  gives a finite `𝒲`, `m`, `σ > 0` and `Q₀` such that, above any `Q₀' ≥ Q₀`, the levels at which
  `V(Q)` has rank `n` and is not in `𝒲` have `log Q` in at most `m` intervals `[t, 4 σ⁻¹ t)` with
  `t ≥ Q₀'`. It combines `exists_forall_not_chain`, 5.4's dichotomy and the greedy covering
  `Set.exists_forall_mem_Ico_of_not_exists_chain`. The levels form a continuum, so a window
  starts at an infimum and costs a factor `2` in the ratio. `exists_forall_approxSpan_mem` is
  now read off the intervals, without the `choose`-built sequence. No Northcott. `𝒲`, `m` and
  `σ` are still existentials; bounding them is Q0.2b.
- **Q0.2b Uniform parameters.** **Landed.** `η`, `m` and `σ` are the definitions
  `NumberField.subspaceEta`, `subspaceChainLength` and `subspaceRatio`, functions of `n`, `|S|`,
  `ε` and a bound `A ≥ approxAbsWeight`. `exists_forall_not_chain` and
  `exists_forall_mem_interval_approxSpan` are stated with them, so only `Qlow` and `Q₀` still
  depend on the forms and the exponents. `|𝒲| ≤ 2 ^ (#ι |S|)`, one subspace per pattern
  (`exists_finite_forall_logHeight_approxSpan`). The classes of 6.1 are the grids `g` with
  `|g| ≤ m'`; there are at most `(2 m' + 1) ^ (#∞ · #ρ)` of them (`ncard_setOf_abs_le_le`), and
  they share the bound `A = AW(cT) + γ m' #ρ [K : ℚ]`
  (`approxAbsWeight_gridExponent_le`), hence one `m` and one `σ`.
- **Q0.2c A bridge from systems to the parametric theorem.** **Landed**, in
  `DiophantineApproximation/SystemDomain.lean`. For `E / K` Galois,
  `NumberField.mem_approxDomain_conjSystem_of_mem_systemSet` puts a solution `x` of a system of
  9.1 into an approximation domain over `E` at level `H(x)`:
  - the forms are 6.3's `conjSystem`;
  - the finite places are those above `S` (`systemPlacesOver`);
  - the exponents are `conjExponent S (c + γ)`: `c/mult v` above an infinite place and
    `e f · c` above a prime of `S`;
  - the constants are absorbed as `C p ≤ H(x) ^ (γ p)`.

  Both weights over `E` are `[E : K]` times the system's (`approxWeight_conjExponent`,
  `approxAbsWeight_conjExponent`, `approxWeight_conjExponent_add`), and the forms are independent
  at every place the domain reads. `systemSet_compRingHom` moves a system over an intermediate
  field `F` to `E` unchanged. No `S`-unit normalization, no `S′` and no Northcott: the points are
  already `S`-integral, and above a finite place outside `S` integrality comes from
  `SIntegerExtension.lean`.
- **Q0.2d 6.1 as an interval result.** **Landed.**
  `NumberField.exists_forall_mem_interval_approxDomain`: for `approxWeight ≤ −ε` and
  `approxAbsWeight ≤ A` there are at most `parametricSubspaceCount` proper subspaces `T` and a
  level `Q₀ > 0` such that, above any `Q₀' ≥ Q₀`, the levels whose domain lies in no member of `T`
  have `log Q` in at most `parametricIntervalCount` intervals `[t, ρ t)` with `t ≥ Q₀'`,
  `ρ = parametricRatio`.
  - The grid and wedge argument is unchanged. For each `k`
    (`exists_forall_mem_interval_approxSpan_le`), each grid `g` gets Q0.2a in `⋀^p`, and its
    exceptional subspaces are pulled back through `recoverSpan`. The counts are summed over `(k, g)`, and the ratio is the sum over `p` of the
    per-`p` ratios.
  - The counts and `ρ` are closed forms in `#ι`, `[K : ℚ]`, `#∞`, `|S|`, `ε` and `A`. This needed
    the minima exponent explicit: `exists_pos_forall_rpow_le_successiveMinimum_le` now also gives
    `B ≤ #ι (AW + 1) / [K : ℚ]`, so `B = parametricMinimaExp`, and the mesh `γ`, box `m'` and the
    grid systems' weight bound `binom(N, p) A + γ m' binom(N, p) [K : ℚ]`
    (`approxAbsWeight_sum_le`) follow.
  - The milestone `exists_finset_submodule_forall_approxDomain_subset` is now read off the
    interval result, with its statement unchanged. The old per-`k` finiteness lemma is gone.
  - Only `Q₀` still depends on the forms: the Plücker constant `C`, `Q₁`, `Q₂`, the rank threshold
    of 4.3 and 5.6's `Q₀` per grid. Bounding those is Q0.2e.
- **Q0.2e Thresholds bounded in terms of heights.** Bound each of these by Cramer's rule,
  Siegel's lemma or a reduced integral basis: `c_K`, `A_K`/`C_E`, `ζ_p`/`C₄`, `A`, `A₀`, `κ`,
  `C₅`, `C₆`, `Q₁`, `Q₂`. **This is the bulk of Q0 (L to XL).** If only
  `log Q* ≤ a + b log(H · |D_K|)` is reached, the count gains a `log log` term, as 9.3 already
  has.
  - **Landed: the threshold is a formula in the forms, with no arbitrary choice left.**
    `exists_forall_mem_interval_approxDomain` now gives `Q₀ = parametricThreshold Sfin L ε A`,
    and 6.1's milestone is read off it with its statement unchanged. The threshold is compared
    with `log Q` throughout. Before, `Q₁`, `Q₂`, `C` and the rank threshold were thresholds on `Q`
    put against `log Q`, which cost an exponential. Its ingredients:
    - `c_K ≤ d · 2 ^ d · √|D_K|`. `integralBasisHouse` now reads a reduced integral basis
      (`reducedIntegralBasis`, `exists_basis_house_le` in the new `ReducedIntegralBasis.lean`):
      Cassels' basis from the successive minima of `𝓞 K`, bounded by Minkowski's second theorem.
    - The radius of `S`-integral approximation is `d · reducedBasisBound K`. Evertse's constant is
      the recursion `evertseConst`, and the Plücker constant is `pluckerConst K N`. All three are
      closed forms in `d`, `|D_K|` and `N`.
    - 4.3's level is `rankThreshold`. The level of the minima bounds is `minimaThreshold` via
      `pointHeightConst`, with exponent `B ≤ N (A + 1) / d` (Q0.2d). The wedge weight gives
      `wedgeWeightConst`. They are formulas in `c_K`, `approxConst` and
      `invFormBound v (L v) = N (1 + ∑ |M_v⁻¹|_v)`.
    - 5.6's threshold is `penultimateThreshold`. It is built from `chainThreshold` (`Qlow`, with the
      auxiliary polynomial's `auxHeightConst` and the heights of `refFamily`), `normalKappa` (`C₅`,
      from the maximal minors) and
      `C₄ = 4 ((d + |Sfin|) log patternConst + log (2 patternHeightBound)) + 1`. It does not depend
      on the exponents, so all grid systems share it.
    - **`ζ_p` is no longer chosen.** Any nonzero vector of the pattern space works: its local
      sizes are absorbed into its height by the product formula
      (`one_le_mul_mulHeight_rpow_weightAt`), and the combination bound
      (`apply_dotProduct_le_of_mem_span_vec`) only needs `M_v⁻¹`. So `C₄` sees `patternHeight`,
      the least height of a nonzero pattern vector, and no denominator.
  - **Local bounds: `ThresholdHeights.lean`.** Generic tools: the height of a determinant
    (`logHeight₁_det_le`), Cramer's rule in heights (`logHeight₁_inv_apply_le`), and the value at
    one place between `H(x)⁻¹` and `H(x)` (`apply_le_exp_logHeight₁`,
    `exp_neg_logHeight₁_le_apply`, infinite and finite). Measured by `formLogHeight` (the sum of
    the entry heights of the form matrices at the places of `S`), with `detLogBound` and
    `invSizeBound`: `approxConst` from both sides, `invFormBound`, `pointHeightConst`,
    `minimaThreshold`, `rankThreshold` and `wedgeWeightConst` are bounded. So are
    `auxHeightConst` and the `refFamily` heights, the height of the wedge forms
    (`formLogHeight_wedgeForms_le`: their entries are minors), `normalKappa` from below
    (`kappaFactor_pow_le_normalKappa`), `patternConst`, and `patternHeightBound`: a pattern space
    is the kernel of `patternMatrix` (columns of the `M_v⁻¹`), and Siegel's lemma over `K`
    bounds its least height by `exp patternLogBound`. **Every local invariant is now bounded.**
  - **Done: the assembly, `ThresholdBound.lean`.** `parametricThreshold_le`:
    `parametricThreshold Sfin L ε A ≤ parametricCoeff d N r t ε A · Λ`, with
    `Λ = thresholdScale = formLogHeight + log |D_K| + ∑_{v ∈ Sfin} log N(v) + 1` and
    `parametricCoeff` an explicit formula in `N = #ι`, `d = [K : ℚ]`, `r` infinite places,
    `t = #Sfin`, `ε` and `A`. Every local bound is put in the form `X ≤ exp (c Λ)`, and the
    coefficients add under products and multiply under powers. Along the way:
    `evertseConst_le` (`≤ (4 m² max A 1) ^ m`), `penultimateThreshold_le` for any forms (with
    `C₅` from `normalKappa ≤ 1` and `kappaFactor`), and `thresholdScale_wedgeForms_le`, which
    bounds the scale of the wedge forms by `wedgeScaleCoeff` times that of the forms. The wedge
    instances (`LinearOrder.lift'` on `powersetCard`, any `DecidableEq`) are matched by stating
    every lemma for arbitrary instances.
- **Q0.3 Assembly.** **Landed**, in `DiophantineApproximation/SystemSubspaceCount.lean`. For a
  normalized system (2.4) with `n` forms over a Galois `E / K`, `t` places and coefficients of
  absolute height at most `H`:
  - the solutions with `log H(x) ≥ X₀ = systemThreshold` lie in at most `systemLargeCount`
    proper subspaces, which depends on `n`, `δ`, `[E : ℚ]`, `[E : K]`, `t` and `|S|` alone
    (`exists_finset_submodule_of_systemThreshold_le`);
  - all solutions lie in at most 9.3's count, plus `1 + log ω / log (1 + δ / (2 n))` with
    `ω = max (1, X₀ / ([K : ℚ] log Q))` for the large ones below `X₀`, plus `systemLargeCount`
    (`exists_finset_submodule_of_isNormalizedSystem`);
  - `X₀` is linear in `log H`: at most the largest of
    `parametricCoeff · ((r_E + s_E) n² [E : ℚ] log H + log |D_E| + ∑_{V | S} log N(V) + 1)`,
    `[K : ℚ] (2 n / δ) log n` and `systemHeightThreshold` (`systemThreshold_le`). It does not
    see the constants `C p`.

  The route:
  - **Exponents.** Each solution gets its own exponents `log |L p i x|_p / log H(x)`
    (`IsNormalizedSystem.exists_gridExponent`). They are at most `2` by the trivial bound
    `|L p i x|_p ≤ (n H^{[E:ℚ]})² H(x)`. Clamped at `-2 n t`, their weight is at most `-δ / 2`,
    either because one of them is clamped or by `∏ |L p i x|_p ≤ systemDet · H(x)^{-δ}` from
    (2.4) with `systemDet ≤ (n! H^{n [E:ℚ]})^{2 t}`.
  - **Grid.** The exponents are rounded up to `ℤ / ⌈4 n t / δ⌉`, which leaves weight
    `≤ -δ / 4`. So only the product of the constants is used, as in Evertse.
  - **Layer 6.1.** Bridge each grid system to a domain over `E` (Q0.2c) and run 6.1's interval
    result there (Q0.2d); its threshold is shared by all grid systems. Pull the exceptional
    subspaces back to `Kⁿ`, and hand the union of the intervals to 9.4 in its `_of_mem` form.
  - **The heights of the conjugated forms** are those of the coefficients (`logHeight₁_algEquiv`,
    `IsNormalizedSystem.formLogHeight_conjSystem_le`).
  - **The counts over `E`** are bounded by monotonicity at `[E : ℚ]` infinite places and
    `[E : ℚ] + [E : K] |S|` places (`parametricSubspaceCount_mono`, `parametricRatio_mono`,
    `card_systemPlacesOver_le`).

  No kernels need a separate case, since a vanishing form is a clamped exponent. The forms'
  independence comes from the normalization (`IsNormalizedSystem.linearIndependent`).
The original sketch is kept below for reference.

- **Q0.1 (original)** Quantitative Roth, `n = 2`, at the strength the classical Roth lemma (DA 2.7) gives,
  as in Davenport–Roth and Schmidt 1989. This is DA 3.7 with explicit constants in place of the
  ineffective threshold. ⚠ **Bombieri–van der Poorten strength is not bookkeeping.** BvdP88
  replaces Roth's lemma by the Esnault–Viehweg form of **Dyson's lemma** (algebraic geometry of
  the same weight as Q1). BvdP88 is an optional side branch, not part of Q0. Its corrigenda are
  in J. Austral. Math. Soc. Ser. A **48** (1990), 154–155.
- **Q0.2** The explicit interval result for general `n` (Sch89 §§ on the "large solutions",
  Sch92 over `K`).
- **Q0.3** Sch92's count, from Q0.2 and DA 9.4.

⚠ **The landed proof is not Schmidt's.** Sch89 (§§6–7, 11–13) works with Mahler's compound and
pseudocompound bodies. DA follows Bombieri–Gubler and replaces those with Evertse's lemma (DA 4.4).
So Q0 has to redo Sch89's constants along the DA route, not transcribe them. Ev96 is the paper
that already runs the quantitative argument along the Evertse-lemma route, and it is the better
guide for constants here, even though Q0 does not need its improved Roth lemma.

⚠ DA 5.1 moves points by `S`-units and DA 6.1 counts the members of a finite set `T`. Check which
steps of the landed proof hide a non-explicit choice, such as a compactness or pigeonhole
argument with an unbounded range, before assuming the whole thing is only bookkeeping.

### Layer Q1: Faltings's product theorem, explicit (Faltings 1991, Evertse 1995)

This is the heavy algebraic-geometry input. The plan below comes from reading Ev95 in full
(2026-09-30). Throughout, `k` is algebraically closed of characteristic 0,
`ℙⁿ = ℙ^{n₁} × ⋯ × ℙ^{n_m}`, `M = n₁ + ⋯ + n_m`, `L_h = O(e_h)` and `L = d₁L₁ + ⋯ + d_mL_m`.

**What Ev95 contains, section by section.**

| § | Content | Foundations it uses |
|---|---|---|
| 1 | Statements. Thm 1 (geometric product theorem, `d_h/d_{h+1} ≥ (mM/ε)^M`), Thm 2 (heights of the factors), Corollary (components of `Z_ε`), Thm 3 (Roth's lemma on `(ℙ¹)^m`, `d_h/d_{h+1} ≥ 2m³/ε`). The index `i_d(F, P)`. | Multihomogeneous ideals; the ideal–variety correspondence on `ℙⁿ`; products of varieties are varieties. |
| 2 | Intersection theory. Lemma 1: intersection numbers `(Z·M₁⋯M_t)` on cycles, characterized by `(Z·M₁⋯M_t) = (div(f\|Z)·M₂⋯M_t)` and `deg` on 0-cycles. Lemma 2: products, `(Z·L^δ) = (δ!/∏δ_h!) ∏ d_h^{δ_h} ∏ deg Z_h`. Lemma 3: a non-product has two tuples `e` with `(Z·L^e) > 0`. Lemma 4 (Bézout with multiplicities): `∑ m_{Z_i}(Z_i·L^e) ≤ (L^e·L^t)` for the codimension-`t` components of `{A = 0}`, `A ⊂ Γ(d)`. Lemma 5: the cutting polynomials are integer combinations of `A` with coefficients `≤ C = (M!/∏n_h!) ∏ d_h^{n_h}`. | Fulton Ch. 1–2 (cycles, `ord_W` as a length, rational equivalence, independence of degree on 0-cycles), Fulton Ex. 7.1.10 (multiplicity = length on the Cohen–Macaulay `ℙⁿ`), dimension theory of varieties, images of projections are closed. |
| 3 | The Faltings height `h(Z, M₀, …, M_t)` of cycles over `ℚ̄`. Lemma 6: recursion `h(Z,M₀,…) = h(div(f\|Z), M₁,…) + ∑_σ κ_σ + ∑_℘ κ_℘`, with `κ_σ` an integral of `log ‖f‖` against Chern forms. Lemma 7: `h(P) = log H(P)`, `h(ℙⁿ) = ½∑∑1/l`, positivity, and the arithmetic Bézout step. Lemma 8: heights of products. Lemma 9: the arithmetic analogue of Lemma 4. | **Arakelov theory**: Gillet–Soulé, Gubler's *Höhentheorie*, the Fubini–Study form, integration of forms over complex subvarieties, Wirtinger's theorem, the reduction of `Z` mod `℘`. Existence and uniqueness (Lemma 6) are cited, not proved. |
| 4 | Proof of Thms 1, 2. Lemma 10: the multiplicity lower bound `m_Z ≥ (ε/s)^s ∏ d_h^{n_h − δ_h}`, by differential operators in local parameters at a smooth point (van der Put, Wüstholz). | Smooth points are dense; generic smoothness of projections; tangent spaces; the local ring `O_Z` and its length. |
| 5 | Proof of Thm 3. Lemma 11: a sharper Lemma 3 on `(ℙ¹)^m`. Then Lemmas 9 and 7 bound `log H(P_h)`. | §§2–4, restricted to `(ℙ¹)^m` but with arbitrary subvarieties `Z`. |

Two consequences for the plan:

- The README's old Q1 omitted **§3**. It is a second foundational layer, and at least as heavy as
  §2: it needs complex integration on singular subvarieties, or else Gubler's adelic reworking.
  The purely geometric Thm 1 needs only §§2 and 4.
- **What the later papers consume is not Thm 3 itself** but Ev96 Lemma 26 (= EF13 Prop. 12.1): a
  non-vanishing statement at grid points of hyperplanes `T_h ⊂ ℚ̄^N`, with `r_h/r_{h+1} ≥ 2m²/ε`
  and `H₂(T_h)^{r_h} ≥ (e^{r₁+⋯+r_m} H₂(P))^{(N−1)(3m²/ε)^m}`. It is the analogue of DA 5.3.
  (?) How Ev96 derives it from Ev95 (Thm 3 or the Corollary) is still to be read.

**Milestones.**

- **Q1.1** Multiprojective intersection theory: Ev95 §2 and the geometric input of §4.
  Proposed route: replace Fulton's cycles and rational equivalence by **multigraded Hilbert
  functions** `h_I(d) = dim_k (k[X]/I)_d` (van der Waerden 1929). The intersection numbers
  `(Z·L^e)` are then the top coefficients of the Hilbert polynomial. Lemma 1(iv) follows from the
  exact sequence `0 → (k[X]/𝔭)(−d) →·f k[X]/𝔭 → k[X]/(𝔭 + (f)) → 0`, and Lemma 4 from the
  associativity formula over the minimal primes. Everything is finite-dimensional linear algebra
  over `k`, which suits Mathlib; the multigrading already exists
  (`MvPolynomial.weightedHomogeneousSubmodule`, `weightedGradedAlgebra`). Sub-milestones:
  - **Q1.1a** ✅ Setup (2026-09-30, `ForMathlib/RingTheory/MvPolynomial/Multigraded.lean`): the
    blocks `b : σ → ι` and the grading `multiWeight b`; `Γ(d)`; the count
    `#(blockMonomials b d) = ∏ i, C(N_i + d i - 1, d i)` (`card_blockMonomials`) and
    `dim Γ(d)` equal to it (`finrank_multiWeight`); multihomogeneous ideals
    (`Ideal.IsWeightedHomogeneous`, closed under `⊔`, colon and span of homogeneous elements);
    the Hilbert function `hilbertFunction b I d`.
  - **Q1.1b** ✅ Exact-sequence calculus: `dim (J + (g))_{d+e} + dim (J : g)_d = dim J_{d+e} +
    dim Γ(d)` (`finrank_sup_span_singleton_add_finrank_colon`), and at the level of Hilbert
    polynomials `H_{J+(g)}(T) = H_J(T) − H_{(J:g)}(T − e)` (`hilbertPoly_sup_span_singleton`),
    with the prime case `H_{𝔭+(g)}(T) = H_𝔭(T) − H_𝔭(T − e)` for `g ∉ 𝔭`. Additivity along prime
    filtrations moves to Q1.1d, where it is needed.
  - **Q1.1c** ✅ Polynomiality (`ForMathlib/RingTheory/MvPolynomial/HilbertPolynomial.lean`,
    `exists_hilbertPolynomial`; the polynomial `hilbertPoly`, unique by
    `hilbertPoly_eq_of_forall_le`; for the whole space `hilbertPoly_bot = ∏ i, C(T_i + n_i, n_i)`).
    **The proof is not Rémond's.** It goes through leading monomials
    (`ForMathlib/RingTheory/MvPolynomial/StandardMonomials.lean`). For any monomial order,
    `dim I_d` is the number of leading monomials of `I` of multidegree `d`, with no Gröbner basis
    needed. So `h_I(d)` counts the monomials outside an upper set, which Dickson's lemma generates
    by finitely many monomials `G`. Removing one generator `g` changes the count by the count for
    `G − g` in multidegree `d − deg g`, and induction on `#G` gives a polynomial. There are no
    prime filtrations and no Krull dimension. What this route does *not* yet give is Rémond's
    Thm 2.10 (1)–(3): total degree equal to `dim V(I)`, positive leading coefficients, and the
    partial degrees. These move to Q1.1d.
  - **Q1.1d** Degrees. Pieces, in order:
    - (i) ✅ **Positivity** (2026-09-30,
      `ForMathlib/RingTheory/MvPolynomial/MultiprojectiveDegree.lean`, with the top-form calculus
      `MvPolynomial.AgreeAbove` in `.../AgreeAbove.lean`). If every generator of the leading-monomial upper set has coordinates `≤ k`, being standard depends only
      on the truncation `min(c, k)`, so the standard monomials are a disjoint union of cones
      `a + ℕ^V` (a Stanley decomposition with no induction). Each cone contributes a product of
      binomials whose top form is the positive monomial `∏ T_i^{N_i - 1}/(N_i - 1)!`, and positive
      top forms cannot cancel. So `α! · [T^α] H_I` is the number of cones of type `α` for
      `|α| ≥ deg H_I` (`coeff_hilbertPoly_mul_factorial`), a natural number
      (`exists_multidegree_eq_natCast`), and nonnegative (`coeff_hilbertPoly_nonneg`).
      **Dimension is taken to be `deg H_I`** throughout. Its identification with the Krull
      dimension of `V(I)` (Rémond Thm 2.10(1)) and the partial degrees (Thm 2.10(2)) are not
      formalized; nothing downstream needs them so far, as long as Q1.1d–Q1.2 use `deg H_I`
      consistently.
    - (ii) ✅ **Degrees and Ev95 Lemma 1(iv)** (same file). `multidegree b I α = α! · [T^α] H_I`.
      First-order Taylor formula: the top part of `P(T) − P(T − e)` is `∑ e_i ∂_i P`
      (`agreeAbove_sub_shiftPoly`). Hence for a prime `𝔭` and `g ∉ 𝔭` of multidegree `e`,
      `d_β(𝔭 + (g)) = ∑_i e_i · d_{β+ε_i}(𝔭)` for `|β| ≥ dim 𝔭 − 1`
      (`multidegree_sup_span_singleton_of_isPrime`), and the dimension drops by exactly one when
      every `e_i > 0` and `dim 𝔭 ≥ 1` (`totalDegree_hilbertPoly_sup_span_singleton`).
    - (iii) ✅ **The associativity formula** (2026-09-30,
      `ForMathlib/RingTheory/MvPolynomial/Associativity.lean`, with localized lengths in
      `ForMathlib/RingTheory/Ideal/LocalLength.lean`). `d_α(I) = ∑_𝔭 ℓ(B_𝔭/I_𝔭) d_α(𝔭)` for
      `|α| ≥ dim I`, over the finite set of multihomogeneous primes `𝔭 ⊇ I` with `H_𝔭 ≠ 0` and
      `dim 𝔭 = dim I`, all of whose lengths are finite (`multidegree_eq_sum_localLength`,
      `coeff_hilbertPoly_eq_sum_localLength`). The proof builds a prime filtration by colon ideals,
      `J_k = J_{k-1} + (f_k)` with `(J_{k-1} : f_k) = 𝔮_k` prime (`exists_primeFiltration`). A
      maximal colon ideal is prime by Mathlib's graded criterion, transported to `Lex (ι → ℕ)`
      (`Ideal.IsWeightedHomogeneous.isPrime_of_mem_or_mem`). Each step gives
      `H_{J_{k-1}} = H_{J_k} + H_{𝔮_k}(T − a_k)` and the exact sequence
      `0 → B/(J : f) → B/J → B/(J + (f)) → 0` for lengths. The shifted summands have nonnegative
      top forms, which cannot cancel (`totalDegree_le_totalDegree_sum`). This also gives dimension
      monotone in the ideal (`totalDegree_hilbertPoly_le_of_le`) and strictly decreasing along
      primes (`totalDegree_hilbertPoly_lt_of_lt`), so a prime of maximal dimension meets the
      filtration only in the factors `𝔮_k = 𝔭`, and the length at `𝔭` counts them. The sum is over
      primes of maximal *dimension* (`deg H`); since the Krull dimension is not formalized, their
      minimality over `I` is not stated.
    - (iv) Bézout and products. ✅ (2026-09-30), the excess form modulo unmixedness of `B_𝔭`.
      - ✅ **Sections by nonzerodivisors** (`MultiprojectiveDegree.lean`): Lemma 1(iv) holds for
        any multihomogeneous `J` and `g` with `(J : g) = J`
        (`multidegree_sup_span_singleton_of_colon_eq`, with the exact dimension drop); the prime
        case is a corollary.
      - ✅ **Bézout with multiplicities for complete intersections**
        (`ForMathlib/RingTheory/MvPolynomial/Bezout.lean`). Along a regular sequence
        (`IsRegularSeq`) of multidegrees `e_j`,
        `d_β(J + (g_1, …, g_t)) = ∑_{f : Fin t → ι} ∏_j e_j(f j) · d_{β + ∑ ε_{f j}}(J)`
        (`multidegree_sup_span_range_of_isRegularSeq`), and the dimension drops by exactly `t` when
        all degrees are positive. The whole space has `d_α = [α = n]` (`multidegree_bot`). With
        the associativity formula: `∑_𝔭 ℓ(B_𝔭/I_𝔭) d_β(𝔭)` over the primes of maximal dimension
        of `I = (g_1, …, g_t)` equals the weighted number of `f` with `β + ∑ ε_{f j} = n`
        (`sum_localLength_mul_multidegree_eq_bezout`).
      - ✅ **Products, Ev95 Lemma 2** (`ForMathlib/RingTheory/MvPolynomial/Product.lean`). For
        `I₁ ⊆ K[X]`, `I₂ ⊆ K[Y]`: `h_{I₁ × I₂}(d₁, d₂) = h₁(d₁) h₂(d₂)`
        (`hilbertFunction_prodIdeal`), by linear algebra in each degree: complements of `(I_i)_{d_i}`
        for `≤`, and the map `K[X, Y] → K[X]/I₁ ⊗ K[Y]/I₂` for `≥`. Hence `H = H₁ H₂`,
        dimensions add, and `d_{(α₁, α₂)} = d_{α₁}(I₁) d_{α₂}(I₂)` (`multidegree_prodIdeal`).
      - ✅ **The excess form, Ev95 Lemma 4 / Rémond 2001 Prop. 3.2 (degree part), modulo
        unmixedness** (`ForMathlib/RingTheory/MvPolynomial/ExcessBezout.lean`). For `I` generated
        by a set `R` of multihomogeneous polynomials of multidegree `e`, and a multihomogeneous
        prime `𝔭` minimal over `I` with `H_𝔭 ≠ 0` and `ht 𝔭 = t`:
        `ℓ(B_𝔭/I_𝔭) · d_β(𝔭) ≤ ∑_{f : β + ∑ ε_{f j} = n} ∏ j, e (f j)` for `|β| ≥ |n| - t`, and
        `dim 𝔭 ≤ |n| - t` (`exists_localLength_span_mul_multidegree_le`). The version with
        `P_1, …, P_t` in the `K`-span of `R` in place of `I` is
        `exists_localLength_mul_multidegree_le`, which is Rémond's statement. The proof is Ev95
        Lemma 5 / Philippon's scheme, with contractions of `(P_1, …, P_k) B_𝔭` in place of cycles:
        they are multihomogeneous because associated primes of multigraded quotients are
        (`isWeightedHomogeneous_of_mem_associatedPrimes`), and degrees are monotone in the ideal
        (`multidegree_le_of_le` in `Associativity.lean`). `K` must be infinite, for prime
        avoidance in a vector space.
        - ⚠ **Hypothesis: `IsUnmixedRing (Localization.AtPrime 𝔭)`**, Macaulay's unmixedness
          (an ideal of height `k` generated by `k` elements has only associated primes of height
          `k`). It holds because `B_𝔭` is regular, hence Cohen–Macaulay (Matsumura Thm. 17.6),
          and it cannot be dropped: `J = (x², xy)`, `g = y` gives `ℓ = 2 > 1`. Mathlib has
          regular local rings, `MvPolynomial` over a field as a regular ring, and Rees's theorem on
          depth, but not "regular ⇒ Cohen–Macaulay ⇒ unmixed". That is formalized in N. Guan et
          al., *Formalization of Auslander–Buchsbaum–Serre criterion in Lean4* (arXiv:2510.24818),
          and is being upstreamed; the hypothesis is to be discharged from there. Proving it here
          would need regular ⇒ domain, a regular sequence of length `dim`, and depth of a quotient
          by a nonzerodivisor (via Rees).
        - No dimension–height link is needed: dimension stays `deg H`, and height enters only
          through `B_𝔭`.
  - **Q1.1e** Multiplicities, projections and Ev95 Lemma 3 (Rémond LNM Ch. 5 Thm 2.10(3)). The
    multiplicity side follows Rémond 2001 rather than Ev95 Lemma 10.
    - ✅ **The multiplicity estimate, Rémond 2001 Prop. 3.1 with Lemma 3.1, without Samuel
      multiplicities** (2026-09-30, `ForMathlib/RingTheory/MvPolynomial/Multiplicity.lean`, with
      `ForMathlib/RingTheory/Ideal/LengthPow.lean`). Let `Q_1, …, Q_d ∈ 𝔭` and directions
      `v_1, …, v_d` satisfy `∂Q_β/∂X_{v_α} ∈ 𝔭` exactly when `α ≠ β`, and give `v_α` the weight
      `1/δ_α`, `δ_α ∈ ℕ_{>0}`. If every `P ∈ I` vanishes at the generic point of `𝔭` to weighted
      order `> ε` along the `v_α`, then `ε^d ∏ δ_α ≤ ℓ(B_𝔭/(x_1, …, x_d)B_𝔭)` for any `x_α ∈ I`
      (`prod_mul_pow_le_localLength`). Rémond's two statements are only ever used together, and
      together they need no Samuel multiplicity:
      - upper bound `ℓ(A/J^n) ≤ C(n - 1 + d, d) ℓ(A/J)` for `J = (x_1, …, x_d)`, since
        `J^k/J^{k+1}` is a quotient of `(A/J)^{#monomials}` (`length_quotient_span_range_pow_le`);
      - lower bound `ℓ(B_𝔭/I^n B_𝔭) ≥ #{γ : ∑ γ_α/δ_α ≤ nε} ≥ C(⌊nε⌋, d) ∏ δ_α`, by a chain of
        the `Q^γ` in order of decreasing degree whose colon ideals lie in `𝔭`
        (`card_le_localLength_comap_weightIdeal`). Vanishing is expressed by the **Taylor map**
        `taylorAtPrime 𝔭 v : B → (B/𝔭)[Z_1, …, Z_d]`, `X_s ↦ (X_s mod 𝔭) + ∑_{v_α = s} Z_α`, a ring
        homomorphism, so Leibniz rules and `I^n ↦` weight `> nε` are free. Its degree-`≤ 1`
        coefficients are `P mod 𝔭` and the gradient mod `𝔭`; the coefficient of `Z^γ` in
        `taylorAtPrime (y Q^γ)` is `ȳ ∏ ∂_αQ_α^{γ_α} ≠ 0`, and it vanishes on the earlier links;
      - `n → ∞`. Nothing uses the characteristic.
    - ✅ **Multiplicity against degree** (`.../MultiplicityBezout.lean`,
      `prod_mul_pow_mul_multidegree_le`): with Q1.1d(iv),
      `ε^t (∏ δ_α) d_β(𝔭) ≤ ∑_{f : β + ∑ ε_{f j} = n} ∏ e(f j)` for a multihomogeneous minimal
      prime `𝔭` of height `t`, `|β| ≥ |n| - t`. This is the inequality Rémond's Prop. 2.1 (degree
      part) is derived from.
    - ✅ **The Hasse-derivative bridge** (`DiophantineApproximation/TaylorAtPrimeHasse.lean`,
      which imports both the Hasse calculus and `ForMathlib`). For injective `v`, the coefficient
      of `Z^γ` in `taylorAtPrime 𝔭 v P` is `∂_{v_* γ} P mod 𝔭` (`coeff_taylorAtPrime`, from
      `coeff_taylor` of `MvHasseDerivTaylor.lean` and Mathlib's `killCompl`); so vanishing to
      weighted order `> a` means `∂_{v_* γ} P ∈ 𝔭` for every `γ` of weight `≤ a`
      (`taylorAtPrime_mem_weightIdeal_iff`). A transversal family forces `v` injective
      (`injective_of_pderiv_mem`). `prod_mul_pow_mul_multidegree_le_of_hasseDeriv` is the degree
      inequality with Rémond's hypothesis on Hasse derivatives, asked of the generators of `I`
      only. Q1.2 should define Rémond's `Z_σ(P)` by Hasse derivatives (equivalent to his `∂^κ` in
      characteristic 0), as the index in `PolynomialIndex.lean` already is.
    - ✅ **The transversal `Q_α`, in characteristic `0`, without Kähler differentials**
      (`ForMathlib/RingTheory/MvPolynomial/Transversal.lean`, `.../TransversalHeight.lean`).
      Rémond gets them from exact sequences of differentials (§4); here they come from
      separability. A transcendence basis `(x_t)_{t ∈ T}` of `B/𝔭` is chosen greedily in order of
      decreasing factor, so each `x_s`, `s ∉ T`, is algebraic over the `x_t` of factor `≥ b s`; a
      relation `f(x_s) = 0` of least degree has `f'(x_s) ≠ 0`, and lifting it gives `Q_s ∈ 𝔭` in
      `X_s` and those `X_t` only, so `∂Q_s/∂X_{s'} = 0` for `s' ∉ T`, `s' ≠ s`, and
      `∂Q_s/∂X_s ∉ 𝔭` (`exists_isTranscendenceBasis_transversal`). Their number is `ht 𝔭`: `𝔭` is
      minimal over the `Q_s` (a smaller prime would force a nonzero polynomial in the `X_t` into
      `𝔭`), so Krull's height theorem gives `≤`; and `le_of_localLength_eq` (in `Multiplicity.lean`:
      `d` transversal equations and `ℓ(B_𝔭/(x_1, …, x_e)) < ∞` force `d ≤ e`, comparing growth
      `n^d` against `n^e`), applied to a system of parameters, gives `≥`
      (`exists_isTranscendenceBasis_transversal_height`). By-product: the dimension formula
      `ht 𝔭 + trdeg_K (B/𝔭) = |σ|` (`height_add_trdeg`). With this,
      `prod_pow_mul_pow_mul_multidegree_le` (in `TaylorAtPrimeHasse.lean`) is the degree inequality
      with Rémond's hypothesis: if every generator has `∂_κ P ∈ 𝔭` for all `κ` with
      `∑_s κ_s/δ_{b s} ≤ ε`, then `ε^t (∏_i δ_i^{c_i}) d_β(𝔭) ≤` the Bézout number, `c_i` the number
      of variables of factor `i` outside the adapted transcendence basis.
    - ✅ **Projections: the degree in the type of the basis is positive** (2026-10-01,
      `ForMathlib/RingTheory/MvPolynomial/Projection.lean`; Rémond LNM Ch. 5 Thm 2.10(3)). For a
      transcendence basis `(x_t)_{t ∈ T}` of `B/𝔭` made of variables and meeting every block,
      `deg H_𝔭 = |T| - |ι|` and `d_β(𝔭) ≥ 1` for `β_i = |T ∩ block i| - 1`
      (`totalDegree_hilbertPoly_eq_and_one_le_multidegree`). No projections are formed and no
      Krull dimension enters: in the cone decomposition of the standard monomials (now for any
      lexicographic order, `exists_hilbertPoly_eq_sum_conePoly_lex`), the free variables `V` of a
      cone are algebraically independent modulo `𝔭` (`X^a f`, `f ∈ 𝔭 ∩ K[X_V]`, would have a
      standard leading monomial), so `|V| ≤ |T|`; and for the lexicographic order with the
      variables outside `T` first, the monomials in `X_T` are standard, so `T` is itself the set
      of free variables of a cone. `d_β(𝔭)` counts the cones of type `β`
      (`totalDegree_eq_sup_of_eq_sum_conePoly`). The adapted basis of the transversal equations
      meets every block when `H_𝔭 ≠ 0`, because `X_s ∉ 𝔭` is transcendental over the variables
      of the other blocks by homogeneity in the block of `s` alone
      (`not_isAlgebraic_of_isWeightedHomogeneous`,
      `exists_transversal_fin_of_hilbertPoly_ne_zero`). Together:
      **`prod_pow_mul_pow_le`** (in `TaylorAtPrimeHasse.lean`), Rémond 2001 Prop. 2.1 (degree
      part) in characteristic `0`, modulo the unmixedness of `B_𝔭`: under Rémond's
      Hasse-derivative hypothesis, `ε^t ∏_i δ_i^{c_i} ≤ ∑_{f : β + ∑ ε_{f j} = n} ∏ e(f j)` with
      `β` the type of `T` and `c_i = |block i \ T|`. Rémond writes the exponent as
      `ht 𝔭_i - ht 𝔭_{i+1}` (traces on the last factors); `c_i` is that number by adaptedness
      and `height_add_trdeg` on each `B_i`, which nothing downstream needs as long as the
      exponents are kept in the form `c_i`.
    - Open: only the unmixedness hypothesis (Q1.1d(iv)).
- **Q1.2** Ev95 Thm 1 and its Corollary, the geometric product theorem with explicit constants.
  - ✅ **Done, modulo the unmixedness of `B_𝔭`** (Q1.1d(iv)). This is the geometric part of
    Rémond 2001 Thm 1.1 and Cor. 1.1, which is Ev95 Thm 1 and its Corollary with better constants.
    Everything is in `QuantitativeSubspace/`, the first files of this library.
    - `productTheorem` (`ProductTheorem.lean`). Let `𝔭` be minimal over generators of
      multidegree `δ`, and let some generating set `R'` of a larger ideal have `∂_κ P ∈ 𝔭` for
      every `P ∈ R'` and every `κ` of weight `≤ ε`. Suppose `δ` decreases with
      `δ_i / δ_{i+1} > (m/ε)^t`, where `t = ht 𝔭`. Then two things hold. First, `𝔭` is minimal over
      the ideal generated by its traces on the blocks, so `V(𝔭)` is a component of
      `Z_1 × ⋯ × Z_m`. Second, `ε^t d_β(𝔭) ≤ #{f : β + ∑ ε_{f j} = n} ≤ m^t` with `β_i = dim Z_i`;
      the count is the multinomial coefficient `t!/∏ (codim Z_i)!`, which is Rémond's
      `d(Z) ≤ ρ(ε, Z)`. The proof uses ranks in the algebraic matroid of the variables
      (`ForMathlib/RingTheory/MvPolynomial/ProductStructure.lean`) in place of heights of primes.
      It compares two transcendence bases, one adapted to the last blocks and one to the first,
      by Abel summation over the cuts.
    - `productTheorem_indexIdeal` (`ZerosOfIndex.lean`) is Thm 1.1 as Rémond states it, for
      `indexIdeal b δ P σ`, the ideal of the zeros `Z_σ(P)` of index `σ`. It applies to a
      component of both `Z_σ(P)` and `Z_{σ+ε}(P)`. The reduction pads `∂_κ P` to multidegree `δ`
      with a monomial in variables outside `𝔭`, so it needs no Leibniz rule.
    - `exists_productTheorem_indexIdeal` is Cor. 1.1. Let `N = |σ| - m` and suppose
      `δ_i / δ_{i+1} > max(1, (mN/ε)^N)`. Then every irreducible subvariety of `Z_ε(P)` lies in a
      product `Z ≠ ℙ`, with the degree bound at `ε/N`. The proof descends along
      `Z_0 ⊇ Z_{ε/N} ⊇ ⋯ ⊇ Z_ε`. A minimal prime of a multihomogeneous ideal is multihomogeneous
      (`Ideal.IsWeightedHomogeneous.of_mem_minimalPrimes`).
    - Not formalized, and not needed downstream so far:
      - Rémond's `N^{-1} d(Z_1)⋯d(Z_m)`, where `N` is the number of components of the product.
        His identification of it with `d(Z)` assumes that the components of `Z_1 × ⋯ × Z_m` all
        have the same degree. This fails in general (Galois orbits on pairs of geometric
        components can have different sizes). Over an algebraically closed field the product of
        primes is prime, so `d(Z) = ∏ d(Z_i)`; that would need the `m`-fold version of
        `Product.lean`.
      - Rémond's Cor. 1.2 (a weaker ratio condition, by a different proof).
      - The height bounds of Thm 1.1 and Cor. 1.1, which belong to Q1.3.
- **Q1.3** Heights of subvarieties: Ev95 §3, Lemmas 6–9, or their analogue in Rémond's setting.
  Use elimination-theoretic heights (Philippon, Rémond), not Arakelov theory; Ev95 (1.6) cites
  Philippon and Soulé for the comparison between the two.
  - ✅ **Interface route, chosen 2026-10-01.** The height bounds use only the interface
    `MultiprojectiveHeight b`; a variant of Rémond's heights `h_β(V)` (LNM 1752 Ch. 7)
    instantiates it (below). `MultiprojectiveHeight b` (`MultiprojectiveHeight.lean`) is a structure
    whose fields are the properties §5 of Rémond 2001 uses, like the unmixedness hypothesis of
    Q1.1–Q1.2:
    - `height_nonneg` (Ch. 7 Prop. 2.5 with Bost–Gillet–Soulé Prop. 3.2.4). (?) Check this
      citation.
    - `height_bot_single_le`, `height_bot_of_ne`: the heights of `ℙ` are at most
      `[K : ℚ] botBound(n_l)` in the indices `n + ε_l`, and `0` otherwise. For Rémond's heights
      `botBound` is the Stoll number (Ch. 7 Cor. 2.4). Weakened from equality on 2026-10-01.
    - `cycleHeight_sup_le`: the arithmetic intersection inequality
      `h_β(V · div p) ≤ ∑_i δ_i h_{β+ε_i}(V) + d_β(V) h_m(p)` for cycles (Ch. 7 Thm 3.4 with
      Cor. 3.6). For non-prime `J` this needs the length formula
      `ℓ_𝔯(J + (p)) = ∑_𝔮 ℓ_𝔮(J) ℓ_𝔯(𝔮 + (p))`, which is not proved.

    The polynomial height `h_m` (`bombieriLogHeight`, the weighted `ℓ²` norm at the infinite
    places) and the heights of cycles (`cycleHeight`, summed over components with their
    lengths) are concrete. All heights are relative to `K`, in Mathlib's
    `Height.AdmissibleAbsValues` normalization, so `[K : ℚ]` times Rémond's.
  - ✅ For every such structure:
    - Rémond's Lemma 5.1, natural combinations avoiding finitely many subspaces
      (`ForMathlib/LinearAlgebra/SmallCombination.lean`).
    - Prop. 3.2, height part (`exists_localLength_mul_height_le`, `ArithmeticBezout.lean`):
      Rémond's chain `J_{k+1} = (J_k + (P_{k+1}))B_𝔭 ∩ B` with `P_{k+1}` a combination of the
      generators with coefficients `≤ |δ|^k`, and
      `ℓ_𝔭 h_β(𝔭) ≤ ∑ δ^f h(ℙ) + (∑_j max(h_m(P_j), 0)) · ∑ δ^g d(ℙ)`.
    - Thm 1.1, height part (`productTheorem_height`, `ProductTheoremHeight.lean`), for a
      monotone bound `B` on `h_m` of the nonzero natural combinations of the generators, and
      `productTheorem_height_coeff` with
      `B(s) = h(R) + [K : ℚ](log s + log (∑_{μ ∈ M} 1/C(δ, μ))^{1/2})`
      (`bombieriLogHeight_sum_nsmul_le`, `PolynomialHeight.lean`), `h(R)` the height of the
      tuple of coefficients. This is `h(𝔭)` in place of Rémond's `N⁻¹ ∏_{j ≠ k} d(Z_j) h(Z_k)`.
    - Thm 1.1 and Cor. 1.1 for the zeros of index `σ`, with heights
      (`productTheorem_indexIdeal_height`, `exists_productTheorem_indexIdeal_height`,
      `ZerosOfIndexHeight.lean`). The padded derivatives `∂_κ P · X^{κ'}` have coefficients
      `c P_ν` with `c ≤ 2^{|δ|}`, so their height is at most `h(P) + [K : ℚ] |δ| log 2`
      (`logHeight_le_of_forall_eq_natCast_mul`), and the error term is
      `∑_{j < t} max(h(P) + [K : ℚ](|δ| log 2 + j log |δ| + |√n|), 0)`, Rémond's, with
      `|√n| = ∑_i √n_i`.
    - Rémond's Lemma 5.2, `∑_{|a| = d} a₀! ⋯ aₙ!/d! ≤ e^{2√n}`
      (`Finset.sum_inv_multinomial_le`, `ForMathlib/Data/Nat/Choose/MultinomialSum.lean`), so
      `log (∑_{μ ∈ M_δ} 1/C(δ, μ))^{1/2} ≤ |√n|` (`log_sqrt_sum_inv_blockMultinomial_le`,
      `PolynomialHeight.lean`). The combinatorial half is Rémond's recurrence for the sums over
      compositions with positive parts, an identity of natural numbers proved by the bijection
      `m ↦ m - e_t`. The analytic half replaces his Stirling estimate and numerical checks by a
      termwise comparison with the series of `e^{2√n}`, using `C(2j + 1, j) ≤ 4^j`.
  - ✅ **Actual heights satisfy the interface** (`resultantHeight`, `ResultantHeights.lean`,
    2026-10-01), over every field whose archimedean absolute values come from complex
    embeddings, e.g. number fields. `h_β(𝔮)` is the height of Rémond's remodeled resultant form
    in `|β|` generic linear forms, with a Gaussian Mahler measure in place of the sphere measure
    at the archimedean places. `botBound n = log M(det_{n+1})`, the Gaussian Mahler measure of
    the generic determinant. H1–H2 follow route (ii), H3–H6 route (i); see the milestones below.
  - Open: an explicit numerical bound for `log M(det_{n+1})` (Hadamard or second moments), and
    the point bound (L) of Ev95 §5, which Q1.4 needs.
- **Q1.4** Ev95 Thm 2 and Thm 3, the improved Roth lemma on `(ℙ¹)^m`.
- **Q1.5** Ev96 Lemma 26, the grid form that replaces DA 5.3 in the Subspace proofs.
- **Q1.6** Re-run Q0 with Q1.5. That gives Ev96's singly exponential count, and on the way the
  quantitative Roth theorem of Bugeaud–Evertse 2008 (Appendix), the best known for `n = 2`.

**Is there a more elementary route to Ev95's Thm 3 strength?** (searched 2026-09-30)

- **No route avoids the product theorem.** Every Roth lemma of this strength found (Evertse 1995,
  Ferretti 1996, Nakamaye 1995, Philippon, Rémond 2001) goes through a product theorem, and so
  through multiprojective degrees and multiplicity estimates. Maculan's GIT proof of Roth
  (arXiv:1305.0926) uses Arakelov geometry and GIT, which is heavier. Ferretti's arXiv:math/9708214
  only applies the lemma.
- **But Arakelov theory can be avoided.** G. Rémond, *Sur le théorème du produit*, JTNB **13**
  (2001), 287–302 ✓ (read in full), proves the product theorem with commutative algebra alone. It
  works over a number field `K`, which need not be algebraically closed. Its ingredients:
  - Prop. 3.1, the multiplicity lower bound `e_{I B_𝔭}(B_𝔭) ≥ ε^{ht 𝔭} ∏ δ_i^{ht 𝔭_i − ht 𝔭_{i+1}}`.
    It uses **Samuel multiplicity** (Bourbaki AC VIII §7) in place of Ev95's length, and exact
    sequences of Kähler differentials in place of smooth points and tangent spaces.
  - Lemma 3.1: Samuel multiplicity `≤` length, for a system of parameters.
  - Prop. 3.2, a multiprojective Bézout inequality for degrees and heights. It is taken from
    Rémond's *Élimination multihomogène* and *Géométrie diophantienne multiprojective*, Chapters 5
    and 7 of Nesterenko–Philippon (eds.), *Introduction to algebraic independence theory*, LNM
    **1752** (2001). There the degrees come from the multigraded Hilbert–Samuel polynomial and
    the heights from eliminant forms (see below: they do need an integral at the infinite places).
  - Better constants: `δ_i/δ_{i+1} ≥ max(1, (m/ε)^{codim Z})` in place of `(mM/ε)^M`, with a
    factor `(codim Z)!` saved in the degree and height bounds (Thm 1.1, Cor. 1.1, 1.2).
- A modern systematic reference for heights on multiprojective space via Chow forms, including
  an arithmetic Bézout theorem: D'Andrea–Krick–Sombra, *Heights of varieties in multiprojective
  spaces and arithmetic Nullstellensätze*, Ann. Sci. ÉNS **46** (2013), 549–627 (open access on
  numdam).
- **Nakamaye 1995** (Bull. SMF **123**, 155–188; read 2026-09-30). Not useful for Q1. It is
  purely geometric, over `ℂ`, with no heights and no Roth lemma. Its product theorem (Thm 5.2)
  has constants that are not made explicit ("no effort has been made to estimate the constants").
  It rests on Fulton–Lazarsfeld refined Bézout (Thm 1.1, via Fulton Ex. 12.3.7), which is heavier
  than what Ev95 uses. One reusable piece: Thm 2.9, length `≥ δ + 1` when `δ` transversal
  differential operators send the ideal into the prime. It is a short power-series argument, and
  on `(ℙ¹)^m` the operators are ordinary partial derivatives.
- **Ferretti 1996** (Forum Math. **8**, 401–427; read 2026-09-30). Two halves:
  - The geometric half (§§1–5) is commutative algebra only, with no cycles and no rational
    equivalence. It uses multihomogeneous Hilbert polynomials (§1, cited from Masser–Wüstholz
    without proof), Bézout via contracted ideals (Thm 2.3), Wüstholz's length estimate (Prop. 3.2,
    Lemma 3.3: length `≥ σ^k d^ω / k!`), and the product criterion (Lemma 5.1, which needs `k`
    algebraically closed). Thm 5.3: `d_i/d_{i+1} ≥ k!(m/ε)^k` with `k = codim Z`, which is
    Rémond's condition with an extra `k!`.
  - The arithmetic half (§§6–7, Thm 7.2) is full Bost–Gillet–Soulé Arakelov theory.
  - There is no Roth-lemma corollary. The geometric half is a good second blueprint for Q1.1–Q1.2.
- **LNM 1752, Ch. 5, *Élimination multihomogène*** (Rémond; read 2026-09-30).
  - **Thm 2.10 is the multigraded Hilbert–Samuel theorem (Q1.1c).** For a finitely generated
    multigraded `M` over a Noetherian multigraded `B`, `dim M_d` agrees with a polynomial `H_M`
    for `d ≥ b`. Its total degree and its partial degrees in every subset of the factors are
    given, and its leading coefficients are positive. The proof is two pages: associated primes
    are multihomogeneous (Lemma 2.5), there is a prime filtration with shifts (Lemma 2.6), and
    induction on the dimension via `0 → B/𝔭(−ε_J) → B/𝔭 → B/(𝔭, X_J) → 0` with a monomial
    `X_J ∉ 𝔭`. Only basic commutative algebra is used, following van der Waerden 1928.
  - Degrees: `deg(I)_α` are the leading coefficients (times `α!`), with the decomposition
    formula `deg I = ∑_{𝔭 ⊇ I, ht 𝔭 = ht I} ℓ(B_𝔭/I_𝔭) deg 𝔭`.
  - The rest of the chapter is eliminant ideals (Thm 2.2), eliminant forms (principality, Thm 2.13),
    and resultant (Chow) forms (Thm 3.3), with their degrees `deg(I)·d₂⋯d_r` (Prop. 3.4),
    specialization (Props. 2.16, 3.6) and separation of variables (Prop. 3.5).
- **LNM 1752, Ch. 7, *Géométrie diophantienne multiprojective*** (Rémond; read 2026-09-30).
  - The height `h_α(V)` (`|α| = dim V + 1`) is the height of a resultant form of `V`, with
    `h(F) = ∑_v [K_v:ℚ_v]/[K:ℚ] log M_v(F)`.
  - At finite places `M_v` is the Gauss norm, the max of the coefficients.
  - **At infinite places `M_v` is Philippon's sphere Mahler measure:**
    `log M(F) = ∫_{S^{2l₁+1} × ⋯} log |F| dσ + ∑_i deg_{z⁽ⁱ⁾}F · ∑_{j ≤ l_i} 1/(2j)`. It is
    multiplicative and invariant under dummy variables.
  - The arithmetic Bézout formula (Thm 3.4) is exact, and its upper bounds (Cor. 3.6) run through
    a Wirtinger-type identity `∫_{σ_v(V)} Ω₁^{α₁} ∧ ⋯ ∧ Ω_q^{α_q} = d_α(V)` (Lemma 3.1) over the
    complex points of `V`, with Fubini–Study forms. So the infinite places still need integration
    on complex varieties. They do not need Green currents or arithmetic Chow groups.
  - Prop. 2.5 compares these heights with the BGS/Arakelov ones.

**Consequence for the plan.** Follow **Rémond 2001 rather than Ev95** as the Q1 source, with LNM
1752 Chs. 5 and 7 as its foundations and Ferretti §§1–5 as a second blueprint for the geometry:

- **Q1.1 keeps the multigraded Hilbert-function route**, now with a written proof to follow: Ch. 5
  §2.2 for Q1.1b–c. Rémond's degrees are the Hilbert–Samuel coefficients, and Samuel multiplicity
  replaces Ev95's lengths and Fulton's Ex. 7.1.10.
- **Q1.2 needs no heights.** Rémond 2001 Thm 1.1 (degree part) needs Q1.1, Samuel multiplicity,
  and the Kähler-differential argument of its §4.
- **Q1.3 is the real open problem.** Rémond's heights avoid Arakelov intersection theory but not
  analysis: they use the sphere Mahler measure, and the Wirtinger identity on `σ_v(V)`. There are
  two ways forward:
  - (i) Formalize them as they stand: resultant forms, then integrals over spheres, then
    Wirtinger for multiprojective varieties.
  - (ii) Only *upper* bounds for heights enter the product theorem and Roth's lemma (Rémond's
    Prop. 3.2, Ev95 Lemma 9). An inequality-only theory with the Gauss norm or `ℓ¹` norm at
    every place might therefore suffice, paying combinatorial factors like the `|δ| log 2` that
    already appear in `h₀`. Cor. 3.6 proves its finite-place bound purely algebraically, and the
    same argument works for any norm. (?) What is missing is a replacement for the exact
    change-of-index formula (Ch. 7 Thm 2.2) and for the lower bound `h(Z) ≥ log H(P)` used at
    the end of Ev95 §5. Both would presumably become Gelfond-type inequalities.
  - Mathlib has the one-variable Mahler measure (`Analysis/Polynomial/MahlerMeasure`), Jensen's
    formula, circle averages and `Module.length`. It has no sphere Mahler measure, no Samuel
    multiplicity and no multigraded Hilbert polynomial.
- **Q1.4–Q1.5.** Thm 3 on `(ℙ¹)^m` and Ev96 Lemma 26 have to be re-derived from Rémond's Thm 1.1.
  That is bookkeeping of the kind Ev95 §5 does. (?) It remains to check that the constants still
  give Ev96's shape.

**Q1.3, route (ii): plan (2026-10-01).**

*What the proofs use.*
- The height parts of Thm 1.1 and Cor. 1.1 use only upper bounds: for `h(ℙ)`, and for the
  intersection inequality. Additive errors of size `c(n) |δ| d_β(V)` per cut are harmless.
- Ev95 §5 (Roth's lemma, Q1.4) also uses two lower bounds:
  - All mixed heights are nonnegative (Lemma 7(iii)), so the expansion of `h(Z, L^{m-s+1})`
    can drop terms.
  - The point bound (L): if the `h`-th projection of `Z` is a point `P_h`, then
    `h(Z, L^e L_h) ≥ log H(P_h) (Z · L^e)` (p. 247). In Rémond's terms the resultant form
    of `Z` of index `(ε_h, rest)` is `λ (u · P_h)^{d_e(Z)}`.
- (?) The errors should go into the `d_1 + ⋯ + d_m` term of Thm 3, at the price of a worse
  constant. Confirm this in the Q1.4 bookkeeping.

*Definition (LNM 1752 Ch. 7 §2.3).*
- `h_a(V)` is the height of `α_d f`, where `f` is a resultant (Chow) form of `V` of index
  `(ε_1^{a_1}, …, ε_q^{a_q})`, i.e. in generic linear forms.
- The height of a form is `∑_v [K_v : ℚ_v]/[K : ℚ] log M_v`. At a finite place `M_v` is the
  maximum of the coefficients; at an infinite place it is the sphere Mahler measure.
- Route (ii) keeps the eliminants and the finite places. At the infinite places it replaces
  the Mahler measure by a coefficient norm: the Bombieri `ℓ²` norm (`bombieriNorm`, which is
  what `α_d` encodes) or the `ℓ¹` norm.
- With a coefficient norm, nonnegativity is the product formula (Mathlib's
  `Height.logHeight` is `≥ 0`). The bound (L) uses `[L^D] = [L]^D` for linear `L` in the
  Bombieri norm.

*Milestones.* H1 and H2 are pure algebra and are needed by both routes.
- **H1. Elimination (Ch. 5 §2).**
  - ✅ §2.1 (`ForMathlib/RingTheory/MvPolynomial/Elimination.lean`):
    - The characteristic and eliminant ideals `𝔈_d(I) = 𝔄_d(I) ∩ A[d]` (Def. 2.1).
    - The elimination theorem (Thm 2.2) over an algebraically closed field: the
      Nullstellensatz, then the determinant trick in one multidegree.
    - Rémond's substitution `δ` and Lemma 2.3, by inverting `∏_i X_{t_i}`.
    - Lemma 2.4: for primes, `𝔄_d(𝔭)` and `𝔈_d(𝔭)` are prime and `𝔄_d(𝔭) ∩ K[X] = 𝔭`; both
      ideals commute with intersections.
  - ✅ Partial degrees for primes (Thm 2.10(1), (3), Lemma 2.7;
    `ForMathlib/RingTheory/MvPolynomial/PartialDegree.lean`): `e_J = r_J - |J|` with `r_J` a
    rank in the algebraic matroid of the variables, via the cone decomposition and nested bases.
  - ✅ Lemma 2.12 (passage to `L = Frac(K[u^{(1)}])`): `𝔮 = 𝔄_{(d_1)}(𝔭) L[X]` is prime,
    `H_𝔮 = Δ_{d_1} H_𝔭`, `deg 𝔮 = deg 𝔭 * d_1` (`GenericSection.lean`, with `BaseChange.lean` for
    the Hilbert function under field extension and `Saturation.lean` for `H_{J : 𝔪^∞} = H_J`).
    ✅ The splitting `𝔄_{d'}(𝔮) = 𝔄_d(𝔭) L[d'][X]`, `𝔈_{d'}(𝔮) = 𝔈_d(𝔭) L[d']`, via
    `K[d] ≅ K[u^{(1)}][d']` (`Splitting.lean`); the assertion on `e_J` as a transfer of ranks
    (`blockRank_add_blockRank_le`).
  - ✅ Thm 2.13 (1) over any field (`EliminantCriterion.lean`): `𝔈_d(𝔭) = 0 ⟺ 𝔪 ⊄ 𝔭` and
    `e_J(𝔭) ≥ r_J(d)` for all `J`. Rémond's specializations and Lemma 2.8 are replaced by partial
    degrees of `Δ_{d_0} H_𝔭` and positivity of its top coefficients.
  - ✅ Thm 2.13 (2) (`Principality.lean`): if `e_J(𝔭) ≥ r_J(d) - 1` for all `J`, then
    `𝔈_d(𝔭)` is principal. The tight sets `J` are stable under `∩`; a form supported in the
    smallest one is dropped, `𝔈_d(𝔭) ∩ K[d ∖ Z] = 0` for `Z = u^{(0)}_{m_0}` by Rémond's
    specialization, and Gauss's lemma in `K[d ∖ Z][Z]` (`Polynomial/PrimeOverZero.lean`).
  - ✅ Cor. 2.15 (`EliminantForm.lean`): the eliminant forms `elim_d(𝔭)`, up to a constant
    (a generator of `𝔈_d(𝔭)` if principal and proper, else `1`). In case (3), `𝔈_d(𝔭)` is
    not principal when `𝔪 ⊄ 𝔭`.
  - ✅ Prop. 2.16 (`Specialization.lean`): the specializations of `elim_d(𝔭)` in all forms
    but the first are `c ∏ U(z_i)`. The zero sets are compared via the elimination theorem
    and the Nullstellensatz; each factor comes from a minimal prime `q` of the specialized
    ideal whose eliminant ideal is nonzero, so the relevant blocks have rank one modulo `q`
    (Thm 2.13 (1)) and the projection is a point.
- **H2. Resultant forms (Ch. 5 §3).**
  - ✅ The characteristic form `χ(M) = ∏_π π^{ℓ(M_π)}` of a torsion `K[d]`-module, as the gcd
    of the maximal minors of a presentation (Lemma 3.1; `CharForm.lean`, `DetIdeal.lean`).
  - ✅ `res_d(I)`, the eventual value of `χ((B[d]/I[d])_k)` (Lemma 3.2), and
    `res_d(I) = ∏_𝔭 res_d(𝔭)^{ℓ(B_𝔭/I_𝔭)}` over the top-dimensional components (Thm 3.3;
    `ResultantForm.lean`). Rémond's flatness argument is replaced by `𝔄(J) : f = 𝔄(J : f)`
    (Lemma 2.3).
  - ✅ Degree in `u^{(l₀)}` = `(∏_{l ≠ l₀} Δ_{d_l}) H_I`, i.e. `deg(I) * d_2 * ⋯ * d_r`
    (Prop. 3.4; `ResultantDegree.lean`). For one form `χ` is the determinant of the
    multiplication by `U`; the induction passes to `L = Frac(K[u^{(l)}])` by Lemma 2.12, and
    homogeneity of `χ` descends from the localization `K[d] → L[d']`. No algebraic closure.
  - ✅ Separation of variables (Prop. 3.5, two factors; `ResultantProduct.lean`): specializing
    `U_1` of multidegree `e + e'` to a product `V W` of generic forms gives
    `res_{(e, …)}(I) · res_{(e', …)}(I)` up to a constant. Rémond's zero-set comparison over an
    algebraic closure is replaced by divisibility (the exact sequence of multiplication by `V`,
    and `χ` unchanged by dummy variables) plus equal degrees (Prop. 3.4). Iterating and
    identifying variables gives Rémond's product of linear forms.
  - ✅ Hypersurface section (Prop. 3.6; `ResultantSection.lean`): specializing `u^{(1)}` to
    the coefficients of a non-zero-divisor `P` gives `res_{d'}(I + (P))` up to a constant.
    Graded pieces commute with the specialization (`GradedPieceBaseChange.lean`), so
    `ρ(res_d(I)) ∣ res_{d'}(I + (P))`, and both have the same degrees by Prop. 3.4.
  - ✅ Lemma 3.7 for linear forms (`ResultantSpace.lean`): with `n_i` generic linear forms in
    the block `i ≠ j` and `n_j + 1` in the block `j`, the resultant form of `ℙ` is the
    determinant of the coefficients of the block `j`, and it is a unit for every other
    distribution of the forms. The determinant lies in the eliminant ideal (Cramer), is prime
    (`IrreducibleDet.lean`), and Prop. 3.4 gives degree `1`. Rémond's general `U_{n+1}(Δ)`
    is not needed for `h(ℙ)`.
- **H3–H5 switched to route (i) (2026-10-01).** With a coefficient norm, Thm 2.2 needs a lower
  bound on `‖ω(f)‖`. The torus-Mahler Gelfond bound loses the sum of the partial degrees over
  all `u^{(1)}` variables, which is exponential in `δ`. The Bombieri inequality loses about
  `t |δ| log t`. Only the sphere Mahler measure gives Rémond's exact equality.
- **H3. Mahler measures at the infinite places.** Rémond's sphere measure is replaced by a
  **Gaussian** one: `log M(F) = ∫ log |F| dγ - c · deg F`, with `γ` the product of standard
  complex Gaussians and `c = ∫ log |w| dγ₁(w)`. For multihomogeneous `F` this is Rémond's
  `M(F)`, by the polar decomposition, but that is never needed. The Gaussian makes his
  properties easy:
  - Fubini, and invariance under dummy variables: `γ` is a product measure.
  - `M(∑ a_s z_s) = ‖a‖₂`: the law of `∑ a_s z_s` is that of `‖a‖₂ w` (characteristic
    functions, Mathlib `stdGaussian`, `charFun`).
  - Multiplicativity: `log |F|` is integrable for `F ≠ 0`. The proof is Tonelli, induction
    on the variables, the roots of a polynomial in one variable, and Landau's
    `∏ max(1, |r|) ≤ ‖p‖₁ / |lead p|`.
  - Lemma 2.1: (1) averaging over specializations is Fubini; (2) is Cauchy–Schwarz.
  Finite places: the maximum of the coefficients, with Gauss's lemma. Lemma 2.1 (1) there
  needs specializations whose reduction avoids a hypersurface (an infinite residue field).
- ✅ **H3** (`ForMathlib/Probability/ComplexGaussian.lean`,
  `ForMathlib/Analysis/Polynomial/GaussianMahler*.lean`, `ResultantMahler.lean`,
  `ForMathlib/RingTheory/MvPolynomial/GaussNorm.lean`, `ResultantGauss.lean`). Thm 2.2 holds at
  every place, and as `h(α res_{(δ, d')}) = ∑_i δ_i h(α res_{(ε_i, d')})`
  (`ForMathlib/NumberTheory/Height/ResultantHeight.lean`). The finite places use a valuation
  ring of an algebraic closure of `K(u)` instead of Rémond's specializations avoiding a
  hypersurface.
- **H4. The heights `h_a(V)` and their easy properties.**
  - ✅ Nonnegativity: `|f_m| ≤ M(f)` for a monomial `m` depending only on the support (Jensen and
    rotation invariance), then the product formula (`gaussHeight_nonneg`). Rémond's Arakelov
    argument is not needed.
  - ✅ `h(ℙ) ≤ [K : ℚ] log M(det_{n_j+1})` (`ForMathlib/NumberTheory/Height/SpaceHeight.lean`).
  - Open: the point bound (L).
- ✅ **H5. The intersection inequality** (`ForMathlib/NumberTheory/Height/SectionHeight.lean`;
  for cycles via Thm 3.3 for heights, `LinearHeight.lean`, and the degree in the first form,
  `ResultantLinear.lean`). The error is exactly Rémond's `d_β(V) h_m(P)`.
  `h_a(V · div P) ≤ ∑_i δ_i h_{a+ε_i}(V) + d_a(V) (h_2(P) + c(n) |δ|)`.
  - `h_a(V · div P) = h(ρ(f))` (Prop. 3.6) and `M(ρ(f)) ≤ M(α_d f) ‖P‖₂^{d_a}` (Lemma 2.1 (2)
    with Prop. 2.16). Rémond's exact formula (Lemma 3.5, integrals over `V`) is not needed.
  - `h(α_d f) = ∑_i δ_i h(f_{(ε_i, …)})` (Thm 2.2), via Prop. 3.5, Lemma 2.1 (1) and
    Prop. 2.16.
- ✅ **H6. Interface.** Only `height_bot_*` had to be weakened (to `height_bot_single_le` with a
  field `botBound`); `cycleHeight_sup_le` holds as stated. The height theorems of Q1.1–Q1.2 were
  re-run, and `resultantHeight` instantiates the interface. (L) is still to be added.

Q1.1 does not depend on the Q1.3 decision. Q1.1a–d have landed, the excess Bézout inequality of
Q1.1d(iv) modulo the unmixedness of `B_𝔭` (Cohen–Macaulay, expected from Mathlib). Q1.1e has the
multiplicity estimate, its combination with Bézout, the Hasse-derivative form of its
hypothesis and, in characteristic `0`, the transversal `Q_α` with the dimension formula
`ht 𝔭 + trdeg = |σ|` and the positivity of the degree in the type of the adapted basis
(`prod_pow_mul_pow_le`, Rémond 2001 Prop. 2.1 modulo unmixedness). Q1.2 is done modulo
unmixedness: Rémond's Thm 1.1 and Cor. 1.1, geometric parts (`productTheorem_indexIdeal`,
`exists_productTheorem_indexIdeal`). Q1.3 (heights): the height parts of Thm 1.1 and Cor. 1.1
hold for every `MultiprojectiveHeight` (`productTheorem_indexIdeal_height`,
`exists_productTheorem_indexIdeal_height`), with Rémond's error term via his Lemma 5.2, and
actual heights of resultant forms satisfy the interface (`resultantHeight`). Left for Q1.4: the
point bound (L) and a numerical bound for `log M(det_{n+1})`.

### Layer Q2: the absolute theory (Roy–Thunder 1996, Evertse–Schlickewei 1999/2002)

Move from points in `Kⁿ` to points in `ℚ̄ⁿ`, with counts independent of `K`.

- **Q2.1** Twisted heights `H_{Q,L,c}` on `ℚ̄ⁿ` and their basic calculus (ES02 §§1–3). Here
  `ArithmeticHeights`' absolute heights are consumed.
- **Q2.2** Absolute Siegel's lemma (RT96), and an absolute Minkowski theorem for twisted heights.
  ⚠ Settle how much of Zhang 1995 this needs before starting. If ES02 needs the full arithmetic
  successive-minima theorem, the layer grows into Arakelov theory and should be split off.
- **Q2.3** The absolute Subspace Theorem, qualitative (ES99).
- **Q2.4** **ES02's quantitative absolute parametric Subspace Theorem**: the interval result and
  the count `4^{(n+9)^2} δ^{-n-4} …`. This theorem is the input to the Bugeaud–Evertse 2008
  complexity bound, whose statement is in `rwst/lean-code`
  (`CITED/BugeaudEvertseComplexity.lean`).

### Layer Q3: Chow forms and Chow weights (Faltings–Wüstholz 1994, Ferretti 2000/2003, Evertse–Ferretti 2002)

This layer can proceed in parallel with Q1 and Q2. It is pure algebraic geometry until its last
milestone.

- **Q3.1** Chow forms of projective varieties over `K`, and their heights.
- **Q3.2** Chow weights (Mumford's degree of contact) with respect to a weight vector.
- **Q3.3** The EF02 lower bound for Chow weights, and its improvement by Quang 2022 if that is
  needed for Q5.
- **Q3.4** The Faltings–Wüstholz filtration argument, as far as EF13 uses it. ⚠ Determine that
  extent from EF13's §§ on the "interval result" before writing milestones.

### Layer Q4: the summit (Evertse–Ferretti 2013)

- **Q4.1** EF13's parametric theorem, which combines Q2.4's framework with Q3's Chow-weight
  estimates.
- **Q4.2** EF13's interval result (Evertse 2010, Thm 3.1): `m = ⌊10^8 · 2^{2n} · n^{14} · δ^{-2} ·
  log(3δ^{-1}RD)⌋` intervals with `ω = 3nδ^{-1} log 3RD`.
- **Q4.3** **The count of the large solutions**, `10^9 · 2^{2n} · n^{14} · δ^{-3} · log(3δ^{-1}RD)
  · log(δ^{-1} log 3RD)`, from Q4.2 and DA 9.4. Together with DA 9.3 this is the full
  quantitative Subspace Theorem at the best known strength.

### Layer Q5 (branch): higher degree (Evertse–Ferretti 2008, Quang 2022)

- **Q5.1** EF08: the number and degrees of the exceptional subvarieties for polynomials of higher
  degree in general position on a variety. It is reduced to Q2.4 or Q4.3 by a Veronese
  embedding and Q3.
- **Q5.2** Quang 2022: subgeneral position, via the sharper Chow-weight bound of Q3.3.
- **Q5.3** (optional) Grieve 2023: big linear systems and the structure of the exceptional set.

## Ordering

```
DA 2–6, 9 (landed) ──► Q0 ──► Q1 ──► Q2 ──► Q4 ──► Q5
                                        ▲
                         Q3 ────────────┘ (Q3 also feeds Q5)
```

**Recommended first formalization target: Q0.** It is the only layer that yields a quantitative
Subspace Theorem without new foundations, and it will show whether the landed proof really is
explicit. The first *paper* worth formalizing in the style of the other paper directories of
this repository (a `Challenge*.lean` statement and a `Solution*.lean` proof) is **Ev95**. It is
34 pages long, and every later record depends on it, EF13 included (through Ev96 Lemma 26). It is
self-contained only as a paper: it cites Fulton for its intersection theory and Gubler for its
heights, and both are foundations Mathlib lacks (Layer Q1).

## Consumers (why the best versions matter)

These use the counts above and are recorded in [`papers.md`](../papers.md):

- **BE08**, Bugeaud–Evertse 2008, Thm 2.1: `p(n) > n (log n)^η` infinitely often for the digits of
  an algebraic irrational, for every `η < 1/11`. It uses ES02. (?) Nobody has yet checked whether
  EF13 improves `η`.
- **ESS02**: the uniform bound for unit equations in a multiplicative group of finite rank.
- **Sch90**: bounds for S-unit equations over number fields.
- **AB10, AB11**: transcendence and irrationality measures from repetitive patterns.
- Schmidt's uniform counts for norm-form equations (Trans. AMS **317** (1990), 197–227 (?)) and
  their extension to decomposable forms by Evertse and Győry.

## References

The main references are **EF13**, **ES02** and **Ev10**, the last of which is also the best
single entry point. For a survey with applications in view, see Y. Bugeaud, *Quantitative
versions of the Subspace Theorem and applications*, J. Théor. Nombres Bordeaux **23** (2011),
35–57 ✓. Full data for every paper are in the tables above.
