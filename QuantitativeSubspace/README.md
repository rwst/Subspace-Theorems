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
| Number of subspaces containing the **large** solutions, linear forms, number field `K` | Evertse–Ferretti 2013: `10^9 · 2^{2n} · n^{14} · δ^{-3} · log(3δ^{-1}RD) · log(δ^{-1} log 3RD)` (as stated in Evertse 2010, Thm 2.1) | Q0 landed at Schmidt's parameters (Q0.3). DA 9.4 turns any *interval result* into this kind of count. DA 6.1 now has one with explicit counts and ratio (Q0.2d), and its threshold `Q₀` is at most `a · (formLogHeight + log |D_K| + ∑ log N(v) + 1)` with `a` explicit in `N`, `d`, `|S|`, `ε` and `A` (Q0.2e, `parametricThreshold_le`). Q0.3 feeds it to 9.4: the solutions of a normalized system above `X₀`, linear in `log H`, lie in a number of subspaces depending on `n`, `δ`, the degrees, the number of places and `|S|` alone; all solutions in that plus `O(log X₀)` plus 9.3's count (`exists_finset_submodule_of_isNormalizedSystem`). |
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
  - **Q1.1a** Setup: the blocks of variables, `Γ(d)`, `dim Γ(d) = ∏ C(d_h + n_h, n_h)`,
    multihomogeneous ideals and their Hilbert functions.
  - **Q1.1b** Exact-sequence calculus: `h_{𝔭+(f)}(d) = h_𝔭(d) − h_𝔭(d − e)` for `f ∈ Γ(e) ∖ 𝔭`;
    additivity along filtrations with prime quotients.
  - **Q1.1c** Polynomiality, a multigraded Hilbert–Serre theorem: `h_I` agrees with a polynomial of
    total degree `dim V(I)` for `d ≫ 0`. **The hard core of the layer.** Follow LNM 1752
    Ch. 5, Lemmas 2.5–2.9 and Thm 2.10.
  - **Q1.1d** Intersection numbers as top coefficients; Ev95 Lemmas 1, 2, 4 and 5.
  - **Q1.1e** Projections and Ev95 Lemma 3; smooth points and the length bound of Lemma 10.
- **Q1.2** Ev95 Thm 1 and its Corollary, the geometric product theorem with explicit constants.
- **Q1.3** Heights of subvarieties: Ev95 §3, Lemmas 6–9, or their analogue in Rémond's setting.
  Use elimination-theoretic heights (Philippon, Rémond), not Arakelov theory; Ev95 (1.6) cites
  Philippon and Soulé for the comparison between the two. ⚠ Choose between (i) and (ii) below
  before writing milestones.
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

Q1.1 does not depend on the Q1.3 decision and can start now, from Ch. 5 §2.

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
