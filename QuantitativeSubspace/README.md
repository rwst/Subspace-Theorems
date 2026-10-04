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
| Number of subspaces containing the **large** solutions, linear forms, number field `K` | Evertse–Ferretti 2013: `10^9 · 2^{2n} · n^{14} · δ^{-3} · log(3δ^{-1}RD) · log(δ^{-1} log 3RD)` (as stated in Evertse 2010, Thm 2.1) | Q0 landed at Schmidt's parameters (Q0.3). Q1 started: the multigraded Hilbert polynomial and its degrees (Q1.1a–d, the excess Bézout inequality modulo Cohen–Macaulay) and the multiplicity estimate against degree (Q1.1e, with the transversal equations and the positivity of the degree in characteristic `0`, i.e. Rémond 2001 Prop. 2.1) are in `ForMathlib`. Q1.2, the geometric product theorem with its degree bound and corollary (Rémond 2001 Thm 1.1 and Cor. 1.1, i.e. Ev95 Thm 1 and Corollary with better constants), is in `QuantitativeSubspace/`, unconditionally since the Cohen–Macaulay property of `K[X]_𝔭` was proved (2026-10-02). DA 9.4 turns any *interval result* into this kind of count. DA 6.1 now has one with explicit counts and ratio (Q0.2d), and its threshold `Q₀` is at most `a · (formLogHeight + log |D_K| + ∑ log N(v) + 1)` with `a` explicit in `N`, `d`, `|S|`, `ε` and `A` (Q0.2e, `parametricThreshold_le`). Q0.3 feeds it to 9.4: the solutions of a normalized system above `X₀`, linear in `log H`, lie in a number of subspaces depending on `n`, `δ`, the degrees, the number of places and `|S|` alone; all solutions in that plus `O(log X₀)` plus 9.3's count (`exists_finset_submodule_of_isNormalizedSystem`). With Evertse's Roth lemma (Q1.6), Ev96's grids and exceptional subspaces (Q1.7), one scalar for the constants (Q1.8a) the auxiliary polynomial built from the distinct forms (Q1.8b) and the minima at one place (Q1.8c) that count is `c ^ (n + 7) Z ^ (n + 3) ℓ (1 + log (ℓ Z))`, `c = 2 ^ (n + 11) n ^ 6`, `Z = c / δ` (free of the degree since Q1.9a), `ℓ = 1 + log (2 ^ (n + 1) s ^ n)` with `s = R [E : K]` for `R` distinct forms: polynomial in `δ⁻¹`, singly exponential in `n`, independent of the degrees, of the number of places of the system and of `|S|`. ES02's shape: `δ ^ (-n - 3) log δ⁻¹` against ES02's `δ ^ (-n - 4)` (Q1.9b), and `c ^ (2 n + 10)` against `4 ^ ((n + 8)²)`. |
| Number of subspaces containing the **small** solutions | Evertse 2010, Thm 2.2: `δ^{-1}((10^3 n)^{nd} + 4n log log 4H)`; over `ℚ`, `δ^{-1}(10^{3n} + 4n log log 4H)` | **Landed**, DA 9.3. |
| **Absolute** form: points in `ℚ̄ⁿ`, count independent of the field | Evertse–Schlickewei 2002 (parametric, twisted heights), sharpened by Evertse–Ferretti 2013 | Absolute geometry of numbers landed: RT96 Thm 6.3 for twisted heights on `Ωⁿ`, `\|det A\| ≤ μ₁⋯μₙ ≤ 2^{n(n-1)/2}\|det A\|` (Q2.2). EF13's set-up and its ES02 inputs are Q2.4; ES02's own count is skipped in favour of EF13's. |
| `n = 2`: **quantitative Roth / Ridout** | Bugeaud–Evertse 2008, Appendix (improving Davenport–Roth 1955, Bombieri–van der Poorten 1988, Evertse 1996/97) | Davenport–Roth-strength count landed, DA 3.7. Bugeaud–Evertse's `δ⁻³ log · log` shape landed for systems in two variables (Q1.6, `systemLargeCountTwo_evertse_le`), with extra factors `t⁴` and the grid count. |
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
| Zh95 | S. Zhang, *Positive line bundles on arithmetic varieties*, J. Amer. Math. Soc. **8** (1995), 187–221. (?) | The theorem on successive minima that yields an **absolute Minkowski theorem**. | Arakelov theory. Not needed: ES02 uses Roy–Thunder's version (RT96 Thm 6.3, its Cor. 7.2), and over a fixed `K` our Minkowski's second theorem (`FieldMinkowski.lean`) does, with `\|D_K\|` in the thresholds (Q1.8). |
| ES99 | J.-H. Evertse, H. P. Schlickewei, *The Absolute Subspace Theorem and linear equations with unknowns from a multiplicative group*, in *Number Theory in Progress* (Zakopane 1997), de Gruyter 1999, 121–142. ✓ | States the **absolute** Subspace Theorem, with points in `ℚ̄ⁿ`, and shows what it is for. | Sch72 and Sch77. |
| ES02 | J.-H. Evertse, H. P. Schlickewei, *A quantitative version of the Absolute Subspace Theorem*, J. reine angew. Math. **548** (2002), 21–127. ✓ | **The quantitative absolute parametric Subspace Theorem**: twisted heights `H_{Q,L,c}`, an interval result, and the count `4^{(n+9)^2} δ^{-n-4} log(2RD) log log(2RD)` for the large solutions (Evertse 2010, Thm B). The source of every uniform count in ESS02 and BE08. | Ev95, Ev96, RT96, and an absolute Minkowski theorem. |
| Ev10 | J.-H. Evertse, *On the Quantitative Subspace Theorem*, Zap. Nauchn. Sem. POMI **377** (2010), 217–240; J. Math. Sci. **171** (2010), 824–837; arXiv:1008.2268. ✓ | Survey of ES02 → EF13. Also proves the new gap principle and the **small-solutions bound**, which is the current record on that axis. | ES02, EF13 (announced). **The source of DA Layer 9.** |
| EF13 | J.-H. Evertse, R. G. Ferretti, *A further improvement of the Quantitative Subspace Theorem*, Ann. of Math. **177** (2013), 513–590; arXiv:1008.2340. ✓ | **The current best count.** It lowers the dependence on `n` from `4^{n²}` to `2^{2n}` and the dependence on `δ` from `δ^{-n-4}` to `δ^{-3}`. It also gives a sharper interval result (Evertse 2010, Thm 3.1). | ES02 (twisted heights, Cor. 7.2 = RT96 Thm 6.3), two ideas of FW94 (their auxiliary polynomial and their filtration, both redone in EF13 §§13, 15), Bombieri–Vaaler's Siegel lemma, Hoeffding's inequality. Ev95, through Ev96 Lemma 26 (EF13 Prop. 12.1). **No Chow forms or Chow weights** (Q3.0). |

### The geometric route (Faltings–Wüstholz, Chow weights)

EF13 is a hybrid. It takes Schmidt's 1972 proof, as refined in ES02, and combines it with ideas
from the Faltings–Wüstholz proof. EF13 redoes those ideas itself (Q3.0); the Chow-weight papers
below are needed only for higher degree (Layer Q5).

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
    proper subspaces, which depends on `n`, `δ`, `[E : ℚ]`, `[E : K]` and the number `R` of
    distinct forms alone (`exists_finset_submodule_of_systemThreshold_le`);
  - all solutions lie in at most 9.3's count, plus `1 + log ω / log (1 + δ / (2 n))` with
    `ω = max (1, X₀ / ([K : ℚ] log Q))` for the large ones below `X₀`, plus `systemLargeCount`
    (`exists_finset_submodule_of_isNormalizedSystem`);
  - `X₀` is linear in `log H`: at most the largest of
    `parametricCoeff · ((r_E + s_E) n² [E : ℚ] log H + log |D_E| + ∑_{V | S} log N(V) + 1)`,
    `[K : ℚ] (2 n / δ) log n` and `systemHeightThreshold` (`systemThreshold_le`). It does not
    see the constants `C p`.

  The route (since Q1.8a; Q0.3 first took each solution's own exponents, clamped at `-2 n t`
  and rounded to `ℤ / ⌈4 n t / δ⌉`, at the price of `(…) ^ (t n)` grid systems):
  - **Raised exponents** (`IsNormalizedSystem.exists_raise`). The positive exponents sum to at
    most `n`; scaling the negative ones down leaves weight `-δ` and `∑ |c| ≤ 2 n + δ`.
  - **One scalar for the constants** (`exists_ne_zero_systemAbs_le`, Minkowski's first theorem
    on `K¹` via Layer 4.1's minima): a nonzero `S`-integer `β` with `|β|_p ^ mult p ≤ κ / C p`,
    `κ ^ t = scalarConst K S · (n! H^{n [E:ℚ]}) ^ (2 t / n)`, which (2.4) with
    `systemDet ≤ (n! H^{n [E:ℚ]})^{2 t}` makes possible. So only the product of the constants
    is used, as in Evertse.
  - **Layer 6.1, once.** Above the threshold `κ ≤ H(x) ^ (δ / (2 n t))`, so `β x` lies in the
    domain over `E` (Q0.2c) of the raised exponents shifted by `δ / (2 n t)`, of weight `-δ / 2`
    and absolute weight at most `2 n + 2`. Run 6.1's interval result there (Q0.2d), pull the
    exceptional subspaces back to `Kⁿ` (they contain `x` with `β x`), and hand the intervals
    to 9.4 in its `_of_mem` form.
  - **The heights of the conjugated forms** are those of the coefficients (`logHeight₁_algEquiv`,
    `IsNormalizedSystem.formLogHeight_conjSystem_le`).
  - **The counts over `E`** do not depend on the infinite places of `E` (since Q1.8c; before, by
    monotonicity at `[E : ℚ]` of them) and are taken at `R [E : K]` distinct forms: the conjugated forms over `E` are the `Gal(E / K)`-conjugates of the system's
    (`formCount_conjSystem_le`, since Q1.8b; before, `[E : ℚ] + [E : K] |S|` places).

  The forms' independence comes from the normalization (`IsNormalizedSystem.linearIndependent`).
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
  ✅ Read (2026-10-02): from Thm 3 alone. Ev96 Lemma 24 reduces hyperplanes to points of `ℙ¹`
  by Schmidt's elimination (Bombieri–Gubler 7.5.19's reduction), and Lemma 26 adds a grid
  argument (Lemma 25, Schmidt's Lemma 8A), which is DA Layers 5.5–5.6.

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
    - (iv) Bézout and products. ✅ (2026-09-30; the excess form unconditional since 2026-10-02).
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
      - ✅ **The excess form, Ev95 Lemma 4 / Rémond 2001 Prop. 3.2 (degree part)**
        (`ForMathlib/RingTheory/MvPolynomial/ExcessBezout.lean`). For `I` generated
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
        - ✅ **The Cohen–Macaulay input, proved** (2026-10-02,
          `ForMathlib/RingTheory/RegularLocalRing/RegularSequence.lean`). Until then the excess
          form and everything after it assumed Macaulay's unmixedness of `B_𝔭`
          (`IsUnmixedRing`, now deleted); it cannot be dropped for arbitrary rings:
          `J = (x², xy)`, `g = y` gives `ℓ = 2 > 1`. Mathlib has `B_𝔭` regular local and the Rees
          theorem; added: regular local rings are domains and a regular system of parameters is a
          regular sequence (Matsumura 14.3), the depth of `M / x M` is one less
          (`exists_isRegular_quotSMulTop`, from Rees), `dim R/Q ≥ depth M` for `Q ∈ Ass M`
          (Matsumura 17.2) and `ht Q + dim R/Q ≤ dim R`. The chain `P_1, …, P_t` now carries a
          regular sequence of length `t - k` on `B_𝔭/(P_1, …, P_k)`: so the maximal ideal is not
          associated for `k < t` (all `ExcessBezout.lean` needs), and every associated prime has
          height `k` (`height_eq_of_mem_associatedPrimes`, which Rémond's count of the associated
          primes in `ArithmeticBezout.lean` needs). Full unmixedness, for every ideal of height `k`
          generated by `k` elements, is not needed and not proved.
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
      part) in characteristic `0`: under Rémond's
      Hasse-derivative hypothesis, `ε^t ∏_i δ_i^{c_i} ≤ ∑_{f : β + ∑ ε_{f j} = n} ∏ e(f j)` with
      `β` the type of `T` and `c_i = |block i \ T|`. Rémond writes the exponent as
      `ht 𝔭_i - ht 𝔭_{i+1}` (traces on the last factors); `c_i` is that number by adaptedness
      and `height_add_trdeg` on each `B_i`, which nothing downstream needs as long as the
      exponents are kept in the form `c_i`.
    - Open: nothing (the unmixedness hypothesis of Q1.1d(iv) was discharged 2026-10-02).
- **Q1.2** Ev95 Thm 1 and its Corollary, the geometric product theorem with explicit constants.
  - ✅ **Done** (unconditional since 2026-10-02, Q1.1d(iv)). This is the geometric part of
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
    whose fields are the properties §5 of Rémond 2001 uses:
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
    the generic determinant, and `log M(det_N) ≤ N (log (2N) / 2 + 2)`
    (`resultantHeight_botBound_le`, by Hadamard's inequality and Jensen;
    `ForMathlib/Analysis/Polynomial/GaussianMahlerDet.lean`). H1–H2 follow route (ii), H3–H6
    route (i); see the milestones below.
  - ✅ The point bound (L) of Ev95 §5 (p. 247), as the interface field
    `logHeight_mul_le_cycleHeight`: if `J ∋ P_s X_t - P_t X_s` (`b s = b t = h`), then
    `h_{β + ε_h}(V(J)) ≥ d_β(V(J)) log H(P)` (2026-10-01). Specializing the other forms into an
    algebraic closure, the resultant form becomes `c (u · P)^D`: its zeros come from zeros of `J`
    (`exists_zero_of_eval_specEval_resForm`), which are proportional to `P` in the block `h`.
    Lifting back gives `P_{s₀}^D res = (u · P)^D g` (`C_mul_resForm_eq`,
    `ForMathlib/RingTheory/MvPolynomial/ResultantPoint.lean`), and Gauss additivity with
    nonnegativity gives the bound (`ForMathlib/NumberTheory/Height/PointHeight.lean`).
- **Q1.4** Ev95 Thm 2 and Thm 3, the improved Roth lemma on `(ℙ¹)^m`.
  - ✅ Thm 3, Roth's lemma (`exists_mul_logHeight_le`, `RothLemma.lean`, 2026-10-01), for every
    `MultiprojectiveHeight`. If `δ_i / δ_{i+1} > m²/ε` and `F`
    vanishes to index `ε` at `P ∈ (ℙ¹(K))^m`, then some `k` has
    `δ_k h(P_k) ≤ max(1, m²/ε)^m ([K : ℚ] h(ℙ¹) |δ| + m (h(F) + [K : ℚ] (|δ| log 2 +
    m log |δ| + m)))`.
    Evertse's condition is `δ_i / δ_{i+1} ≥ 2m³/ε`.
  - The geometric heart is a sharper product theorem for any blocks
    (`exists_eRk_lt_and_mul_height_le`): with `δ_i / δ_{i+1} > m/ε` in place of Rémond's
    `(m/ε)^t`, some projection of `V(𝔭)` is not onto. Ev95's Lemma 11 (tangent spaces at smooth
    points) becomes the bound `∑_k G_k ≥ ∑_i r(B_i) - r(σ)` on the cut excesses
    `G_k = r(P_k) + r(σ \ P_k) - r(σ)` of the algebraic matroid of the variables, by
    submodularity (`exists_cutExcess`). The descent runs below the point ideal of `P`
    (`ForMathlib/RingTheory/MvPolynomial/PointIdeal.lean`), and the point bound (L) closes it.
  - Not done: Thm 2 (the height bound for the factors of a product). Q1.5 did not need it.
- **Q1.5** Ev96 Lemma 26, the grid form that replaces DA 5.3 in the Subspace proofs.
  - ✅ Ev96 Lemma 24 (`formIndex_le_of_sq_lt_ratio`, `GeneralizedRothLemma.lean`, 2026-10-02),
    stated like DA 5.3 (`formIndex_le_of_degree_ratio`) so that it can replace it: if
    `d_h / d_{h+1} > m²/θ`, `P ≠ 0` has multidegree at most `d` in blocks of `n + 1` variables,
    and every form has `d_h h(M_h) > n B` with `B` the bound of Q1.4 at `h(P)`, then the index
    of `P` along the forms is at most `θ`. With Evertse's `Θ = θ/m` the ratio condition is
    `m/Θ` against his `2m²/Θ`. The proof is DA 5.3's elimination to two coordinates per block,
    then the bridge `formIndex_le_index` (index along forms ≤ index at their common zero), a
    renaming to `(ℙ¹)^m`, padding the multidegree to `d`, and Q1.4.
  - The grid half of Lemma 26 is DA 5.5–5.6 unchanged
    (`exists_linSubst_hasseDeriv_ne_zero_of_formIndex_le`, `exists_eval_hasseDeriv_ne_zero`):
    they take the index along the forms as input, so Q1.6 only swaps the 5.3 call.
- **Q1.6** Re-run Q0 with Q1.5, and the quantitative Roth theorem of Bugeaud–Evertse 2008
  (Appendix), the best known for `n = 2`. **Done** (2026-10-02). Ev96's singly exponential count
  for general `n` turned out to need more than the Roth lemma; it is Q1.7, which also revised the
  counts quoted below.
  - ✅ The Q0 chain takes the Roth lemma as a parameter (2026-10-02). Steps IV and VI use DA 5.3
    once, and everything after sees it only through the ratio `σ` and the height cost
    `F (h(P) + g (m + 1) d₀ [K : ℚ])`. `NumberField.RothParams` (`σ`, `F`, `g`) and
    `NumberField.SubspaceRoth` (those plus the index bound) in `PenultimateMinimum.lean` are
    threaded through 5.6, 6.1 (`ParametricSubspace.lean`), the thresholds (`ThresholdBound.lean`)
    and Q0.3 (`SystemSubspaceCount.lean`). Bombieri–Gubler's is `SubspaceRoth.bombieriGubler`; the
    qualitative milestones use it and keep their statements.
  - ✅ Evertse's (`SubspaceRoth.evertse`, `QuantitativeSubspace/SubspaceCount.lean`), from Q1.5
    with `θ = (m + 1) η / 2`: `σ = η / (4 (m + 1))` in place of `(η / 4) ^ (2 ^ m)`, so the
    intervals have ratio `16 (m + 1) / η` (`four_mul_inv_evertseRatio`) and the `log ρ` in the
    counts drops from `2 ^ m log (4 / η)` to `log (16 (m + 1) / η)`. The height cost is
    `F = n max(1, 2 (m + 1) / η) ^ (m + 1) (m + 1)`, `g = max(h(ℙ¹), 0) + m + 2`. Corollaries:
    5.6 as an interval result (`exists_forall_mem_interval_approxSpan_evertse`) and Q0.3's count
    (`exists_finset_submodule_of_isNormalizedSystem_evertse`). They take a `MultiprojectiveHeight`
    on `(ℙ¹)^m` for every `m`, as Q1.4 does for one (until 2026-10-02 also a Cohen–Macaulay
    hypothesis for every `m`).
  - ✅ Closed forms (2026-10-02). With `X = 1 + 8 (n + 1) ^ 2 (A + 1) / ε ≥ η⁻¹` and
    `T = 2 (1 + log (2 (n + 1) s)) X ^ 2 ≥ m + 1` (`inv_subspaceEta_le`,
    `subspaceChainLength_add_one_le`):
    - the ratio: `4 σ⁻¹ ≤ 16 T X` (`four_mul_inv_evertseRatio_le`), so
      `log ρ = O(log (n s (A + 1) / ε))`; summed over the steps of 6.1:
      `parametricRatio_evertse_le`;
    - the thresholds: the coefficients of DA are monotone in the height cost
      (`penultimateCoeff_mono`, `parametricCoeff_mono`, `ThresholdBound.lean`), and Evertse's cost
      is at most `F ≤ n T exp (T log (2 T X))`, `g ≤ max(β, 0) + T + 1` for `β ≥ h(ℙ¹)`
      (`evertse_factor_le`, `evertse_shift_le`). These are the parameters
      `RothParams.evertseBound`, and `penultimateThreshold_evertse_le`,
      `parametricThreshold_evertse_le` bound the thresholds of 5.6 and 6.1 by their coefficients
      times `Λ`. The logarithm of the coefficient is now `O(T log (T X))`, polynomial in
      `(A + 1) / ε`, against `2 ^ m log (4 / η)` for Bombieri–Gubler.
  - ✅ The count in closed form against Ev96 (`SubspaceCountBound.lean`, 2026-10-02). As of Q1.6
    (superseded by Q1.7, which removed the `2 ^ n`):
    `systemLargeCount_evertse_le` gave `Z ^ (t n + 2 ^ n (2 d + e u) + 13)` with
    `Z = 2 ^ (n + 12) n ^ 6 t ^ 2 d ^ 2 / δ`, `d = [E : ℚ]`, `e = [E : K]`, `t = |S|`, `u = |S_fin|`;
    Q0.3 with it: `exists_finset_submodule_of_isNormalizedSystem_evertse_le`. Ev96 Thm (i):
    `(2 ^ (60 n ^ 2) δ ^ (-7 n)) ^ s log 4D log log 4D`. So:
    - `δ`: polynomial in `δ⁻¹` like Ev96 (with Bombieri–Gubler's lemma it is exponential in a
      power of `δ⁻¹`), exponent `t n + 2 ^ n (2 d + e u)` against `7 n s`;
    - `n`: doubly exponential (`2 ^ n` in the exponent) against Ev96's `2 ^ (60 n ^ 2 s)`;
    - degree: `[E : ℚ]` in the exponent against Ev96's `log 4D log log 4D`.
    The last two gaps are Layer 6.1's grid covering (`(2 m + 1) ^ ([E : ℚ] binom(n, p))` grids),
    not the Roth lemma. Reaching Ev96's shape means replacing that covering.
  - ✅ Two variables, Bugeaud–Evertse's case (`SubspaceCountTwo.lean`, 2026-10-02). For `#ι = 2`
    the domains at large levels have rank `0` or `1 = #ι - 1`, so Layer 5.6 applies to them
    directly and 6.1's wedges and grids are not needed:
    - `exists_forall_mem_interval_approxDomain_two`: the parametric theorem as an interval
      result, `2` subspaces (`2 ^ (2 s) + 1` before Q1.7) and `m` intervals of ratio
      `4 σ⁻¹`, any Roth lemma; its
      threshold `twoThreshold` is linear in the heights (`twoThreshold_le`);
    - Q0.3's assembly now takes any interval result
      (`exists_finset_submodule_of_forall_interval`,
      `exists_finset_submodule_of_isNormalizedSystem_of_large` in `SystemSubspaceCount.lean`;
      the 6.1 theorems are instances), so the system theorem for `n = 2` is
      `exists_finset_submodule_of_isNormalizedSystem_two` (`_evertse` with Evertse's lemma),
      threshold `systemThresholdTwo_le`;
    - closed form `systemLargeCountTwo_evertse_le`:
      `G (2 + 2 ℓ Y² (1 + 5 log (32 ℓ Y³) / δ))`, `ℓ = 1 + log (4 s)`, `Y = 833 t² / δ`,
      `s = d + e u`. The main term was `O(t⁴ δ⁻³ log s · log (t δ⁻¹ log s))`, Bugeaud–Evertse's
      `225 δ⁻³ log (2 r) log (δ⁻¹ log (2 r))` with places `s` for forms `r`, with two extras: `t⁴`
      from the absolute weight of Q0.3's clamped exponents and the grid factor `G`. Q1.8a removed
      both: now `2 + 2 ℓ Y² (1 + 5 log (32 ℓ Y³) / δ)` with `Y = 449 / δ`, i.e.
      `O(δ⁻³ log s · log (δ⁻¹ log s))`, Bugeaud–Evertse's shape with `s` for `r`.
  - The chain length needs no change. Ours is `⌈4 log (2 (n + 1) s) / ((n + 1) (n + 2) η²)⌉`
    with `η ≍ ε / ((n + 1)² (A + 1))` (5.2's Siegel lemma), BE's (A.26) is
    `1 + ⌊25600 δ⁻² log (2 r)⌋`: the same `δ⁻² log` shape, up to `s` for `r` and the factor `A`.
- **Q1.7** Ev96's singly exponential count for general `n`. **Done** (2026-10-02), read from
  Ev96 §§ 4–6 and 9 (Theorems A–C, Lemmas 18, 27) and ES02 § 12 (Lemmas 12.1–12.4). The `2 ^ n`
  in the exponent of Q1.6's count had two sources, each removed by a short argument; neither
  needed the Roth lemma or a new route through `⋀^{n - 1}`. (The sketch that stood here, with its
  worry that the compound domain need not have rank `M - 1`, was wrong: Ev96's Theorem B produces
  `dim V = N - 1` exactly, as our 6.1 does, and his Theorem C is our 5.6. Its "Ev96 §§ 12–17" was
  ES02, which BE's Lemma A.5 cites.)
  - ✅ **The grids of 6.1** (`DiophantineApproximation/MinimaGrid.lean`; Ev96 Lemma 18, (6.53)).
    The wedge exponent at an infinite place and a `p`-subset is the sum of the original exponents
    plus `logb Q` of a constant, of `p` minima read through the bijection of Evertse's lemma, and
    of the jump. 6.1 rounded each of the `r binom(n, p)` entries separately:
    `(2 m + 1) ^ (r binom(n, p))` grids. It now rounds the `n` minima, the constant and the jump,
    with one bijection per infinite place: `n! ^ r (2 m + 1) ^ (n + 2)` grids
    (`minimaGrid`, `ncard_minimaGridSet_le`). An entry collects up to `p + 2` roundings, so the
    mesh is `n + 2` times finer (`parametricMesh`); the pool keeps the grids with entries at most
    `m + n + 2`, which the rounded grid satisfies, so the absolute-weight bound
    (`parametricWedgeAbsWeight_le`) is unchanged.
  - ✅ **One exceptional subspace in 5.4** (`ExceptionalSubspace.lean`; ES02 Lemmas 12.3–12.4,
    with the threshold patterns of Ev96 Lemma 27). The exceptional vector was chosen per pattern,
    `2 ^ (#ι s)` of them, `2 ^ (binom(n, p) s)` in `⋀^p`. The proof only uses that the pattern
    carries the normal vector and that its indices have exponent at most `c v (k v)`; the
    threshold set `{i | c v i ≤ c v (k v)}` has both properties and depends on `k v` alone. Call
    `k` bad if `weightAt c k < -ε/4` and its threshold pattern carries a nonzero vector, a
    condition independent of `Q`. If some `k` is bad, one fixed vector of one fixed bad `k₀`
    kills the domain at every large level, so every exceptional `V(Q)` is its kernel. So at most
    one exceptional subspace: in 5.6, per grid in 6.1 (`parametricSubspaceCount` no longer
    depends on `s`), and `2` subspaces (with `⊥`) in the two-variable count. Bombieri–Gubler's
    "a linear space `W`" is thus true, though their proof does not give it.
  - ✅ **The closed form** (`SubspaceCountBound.lean`; superseded by Q1.8a):
    `systemLargeCount_evertse_le` became `Z ^ ((t + 1) n + n d + 15)` with `Z = 2 ^ (n + 12) n ^ 7 t ^ 2 d ^ 2 / δ` (`n ^ 7` for the
    finer mesh), against `Z ^ (t n + 2 ^ n (2 d + e u) + 13)` before. As `Z` carries `2 ^ n`,
    the count is `2 ^ O(n ^ 2 (t + d)) δ ^ (-O(n (t + d)))`, Ev96's
    `(2 ^ (60 n ^ 2) δ ^ (-7 n)) ^ s` shape in `n` and `δ`. The finite places of `E` no longer
    appear.
- ✅ **Q1.8** The places and the degree. **Done** (Q1.8a–c, 2026-10-02). ES02 read in full (2026-10-02), with Ev10 § 6. The count
  `Z ^ ((t + 1) n + n d + 15)`, `Z = 2 ^ (n + 12) n ^ 7 t ^ 2 d ^ 2 / δ`, `d = [E : ℚ]`, has four
  sources of `t` and `d`; ES02's parametric count `4 ^ ((n + 8) ^ 2) δ ^ (-n - 4) log 2r
  log log 2r` (Prop. 6.1) has none. **What ES02 does that we do not**:
  - **Only `∑_v max_i c_{iv} ≤ 1` is used**, never `∑ |c|`. In the index estimate (Lemma 15.1)
    the exponents are shifted to `b_{iv} = c_{iv} - max_i c_{iv} ≤ 0`, with the total
    `∑_v max_i c_{iv}` put at one place `v₀` (15.9); then `∑ |b| ≤ 2 n`. The minima are bounded
    by `Q ^ (-1 - η) < λ₁`, `λ_n < Q ^ (n - 1 + η)` from the product formula alone (Lemma 17.1).
  - **All the minima sit at one non-archimedean place `v₀`** (`λ ∗ Π`, (6.13)–(6.14)), outside
    `S`, where the forms are the coordinates. Davenport's lemma (§ 9, Lemma 9.2) then gives *one*
    permutation, and needs `v₀` finite ((9.31)). The compound domain keeps the exact `c_τ` at every
    other place and rounds only the `n` minima exponents at `v₀` (Lemmas 17.2, 18.1):
    `G ≤ (2 n B) ^ n` classes, `B = ⌊3 n² 2 ^ n / δ⌋`, permutations included. The dilation of the
    compound domain moves to a second such place `v₁` (Lemma 18.2).
  - **Forms from one family `{L_1, …, L_r}`.** The auxiliary polynomial is built from the `r`
    forms (Index Theorem with `s = r`), so the chain length is `1600 n⁴ δ⁻² log 2r` (16.2), and
    the height bound of the penultimate subspace has exponent `R n - 1`, `R ≤ binom(r, n)` the
    number of distinct systems, not `s n` (Lemma 12.1). In `⋀^k`: `r ↦ binom(r, k)`, and
    `log 2 binom(r, k) ≤ k log 2r` (18.40).
  - **Moving mass between places** (Lemma 6.3): for `∏_w A_w > 1` there is `β ∈ ℚ̄` with
    `|β|_w ≤ A_w`. ES02 needs `ℚ̄` (a `k`-th root of an `S`-unit) only to make the error
    `(1 + ϑ)`; over `K`, Minkowski's first theorem gives `β ∈ K` with a constant `c_K` that
    depends on `|D_K|` and the norms of the places involved, which only enters thresholds.
  - Not needed by us: the absolute Minkowski theorem of Roy–Thunder (Cor. 7.6, used to avoid
    `|D_K|` in the *threshold*; our thresholds may carry `log |D_K|`), and ES02's own reduction
    of the product inequality (§ 21), which pays `(4 n² e / δ) ^ {n s}` classes, as our Q0.3 does.
    Ev10 Thm B counts the solutions of one *system* (2.3), which is our setting.

  Ev10 § 6 explains the remaining gap to EF13: every class subdivision (ours and ES02's) comes from
  Schmidt's polynomial, which needs the solutions of a chain to share their exponents; the
  Faltings–Wüstholz polynomial does not, and removes the `4 ^ (n²) δ ^ (-n)` (Q2, not Q1.8).

  **The plan**, cheapest first:
  - ✅ **Q1.8a The system's own exponents.** **Done** (2026-10-02). Raised exponents
    (`IsNormalizedSystem.exists_raise`, `c⁺ - λ c⁻` with `λ = (P + δ) / N`, so no shift is
    needed for (i)); one scalar from Minkowski's first theorem on `K¹`
    (`exists_ne_zero_systemAbs_le`: Layer 4.1's minima bound for the coordinate form, with
    `scalarConst K S = 2 ^ [K : ℚ] ∏_{q ∈ S} N(q) √|D_K|`); 6.1 runs once with
    `A = [E : K] (2 n + 2)` (`systemAbsBound`). `systemGridCount`, `systemClamp`,
    `systemGridDen` and `exists_gridExponent` are gone; `systemLargeCount` no longer takes `t`;
    `systemHeightThreshold` is `(2 n log scalarConst + 4 t log (n! H ^ (n d))) / δ`. The closed
    form (`systemLargeCount_evertse_le`) is now `Z ^ (n d + n + 14) ℓ (1 + log ℓ)` with
    `Z = 2 ^ (n + 11) n ^ 6 d / δ` and `ℓ = 1 + log (2 ^ (n + 1) (d + e u))`, against
    `Z ^ ((t + 1) n + n d + 15)` with `Z = 2 ^ (n + 12) n ^ 7 t ^ 2 d ^ 2 / δ` before: `t` is
    gone, and the places enter as `log s log log s`, ES02's `log 2r log log 2r` with `s` for `r`.
    The plan as written: Q0.3 gives each solution its own exponents, clamped at
    `-2 n t` and rounded: `(M m + 2 m + 1) ^ (t n)` grid systems, and absolute weight
    `A = [E : K] t n (2 n t + 2)`, whose square sits in `η` and so in `Z` (`t ^ 2`). This is
    only to absorb the constants `C p`, of which only the product is controlled. Instead:
    (i) raise the exponents to weight exactly `-δ` (Ev10's `max_i c_{pi} = s(p)` is kept), so
    `∑ |c| ≤ 2 n + δ` independently of `t`; (ii) absorb the constants by one fixed `β ∈ K`
    with `|β|_p ≤ |det L_p|_p ^ (1 / n) / C_p` on the places of the system and `|β| ≤ 1`
    elsewhere (Minkowski's first theorem over `K`, `FieldMinkowski.lean`, the slack `c_K` at
    one place); `βx` lies in the domain of the given exponents at level `H(x)`, up to constants
    bounded by `H` and `|D_K|`, which a shift of `δ / (2 n t)` per place and a larger threshold
    absorb; (iii) run 6.1 once, with `A ≤ 2 n + 2`. Removes the factor `t n` from the exponent
    and `t ^ 2` from `Z`. Touches only Q0.3 (`SystemSubspaceCount.lean`) and the closed form.
  - ✅ **Q1.8b Distinct forms.** **Done** (2026-10-02). The vanishing conditions of Layer 5.2
    are imposed per distinct form, not per place and coordinate: whether all monomials of `P`
    read in the coordinates `A v` have large exponent along row `i` depends only on that row,
    since two systems sharing a form differ by a substitution whose row is a unit vector
    (`MvPolynomial.blockSubst_coeff_mem_of_row`, `MultiHomogeneous.lean`). So 5.2 takes the
    forms `F` with a representative row each and needs `4 log (2 #F) < (n + 1)(n + 2) η² m`
    (`SubspaceAuxiliary.lean`). Then:
    - **5.6** (`PenultimateMinimum.lean`) takes a form count `s` with
      `formCount Sfin L ≤ (n + 1) s` (`s = |S|` always works, `formCount_le`); chain length,
      ratio and the height cost of the Roth lemma are taken at `s`, so `chainThreshold`,
      `penultimateThreshold` and `penultimateCoeff` gained the argument. 5.4's
      `ε log Q / (4 |S|)` stays with the places, since it only enters the threshold.
    - **6.1** (`ParametricSubspace.lean`) takes `formCount Sfin L ≤ s`; the wedge forms in
      `⋀^p` are wedges of `p`-tuples of forms, at most `s ^ p` of them
      (`formCount_wedgeForms_le`), so `parametricChainLength N d s p` is 5.6's chain length at
      `s ^ p` (ES02 (18.40): `log 2 binom(r, k) ≤ k log 2r`). The thresholds
      (`parametricStepThreshold`, `parametricThreshold`, their coefficients) take `s`.
    - **Q0.3** (`SystemSubspaceCount.lean`) runs 6.1 over `E` at `s = R [E : K]`: the forms at a
      place of `E` are `Gal(E / K)`-conjugates of the forms at the place below
      (`formCount_conjSystem_le`). `systemLargeCount R n d e r δ` and `systemThreshold` take the
      number `r` of forms in place of `|S|`; `IsNormalizedSystem.one_le_formBound` gives
      `1 ≤ R`.
    - **Closed form** (`SubspaceCountBound.lean`): `Z ^ (n d + n + 14) ℓ (1 + log ℓ)` with
      `ℓ = 1 + log (2 ^ (n + 1) s ^ n)`, `s = R e`, in place of `ℓ = 1 + log (2 ^ (n + 1)
      (d + e u))`. `|S|` no longer appears anywhere in the count. The price is the factor `n` in
      `ℓ ≤ (n + 1) log (2 s) + 1`, which ES02 pays too (`k log 2r` in `⋀^k`); if `R e` is much
      smaller than the number of places of `E`, this is a gain, otherwise a factor `n` in `ℓ`
      only.
    - **Two variables** (`SubspaceCountTwo.lean`): `systemLargeCountTwo R e s δ` with
      `s = R [E : K]`, so `2 + 2 ℓ Y² (1 + 5 log (32 ℓ Y³) / δ)` with `ℓ = 1 + log (4 R e)`:
      Bugeaud–Evertse's `δ⁻³ log 2r log (δ⁻¹ log 2r)` with `r = R [E : K]` forms (the
      conjugates over `E`), now with forms in place of places.
  - ✅ **Q1.8c The minima at one place.** **Done** (2026-10-02), at an **infinite** place `w₀`
    rather than ES02's finite `v₀`. The plan above (a prime `p₀ ∉ S`, scaling by powers of `p₀`)
    does not work as written: the places of `E` above `p₀` are several, and Davenport's pivot
    (ES02 (9.24)–(9.33)) is chosen at one place, so each would need its own permutation; ES02
    avoid this because their relations have coefficients in `K` and `v₀ ∈ M(K)`, over `ℚ̄`.
    A single place of `E` with balanced scaling elements would need `S`-units with a controlled
    regulator. Instead (`WedgeDomainAt.lean`):
    - `w₀` is an infinite place with `mult w₀ ∣ [K : ℚ]` (a real one if any;
      `exists_mult_dvd_finrank`), `a = [K : ℚ] / mult w₀`.
    - Each vector `x j` realizing the `j`-th minimum `μ j` (at all infinite places) is scaled by a
      nonzero integer `β j` with `|β j|_w μ j ≤ 1` at `w ≠ w₀` and
      `|β j|_{w₀} ≤ c μ j ^ (a - 1)` (`exists_balance`, from Minkowski's first theorem for one
      scalar, `exists_ne_zero_le_of_unitConst_le`, `c = unitConst K = 2 ^ [K : ℚ] √|D_K|`): the
      product formula balances since the other places carry `(a - 1) mult w₀`. The scaled
      vectors meet the domain's bounds at every place but `w₀`, and `c μ j ^ a` times them there.
    - Evertse's lemma (Layer 4.4, already per place) with minima at `w₀` alone: the bijections at
      the other places pair equal bounds and drop out, **one** bijection remains. An archimedean
      `w₀` costs only Evertse's constant, which is there anyway; ES02 need `v₀` finite for their
      absolute constants only.
    - The wedge domain `wedgeExponentAt` has `logb Q C` at every infinite place and `a` times the
      minima correction at `w₀`; its weight is that of Layer 4.5 exactly
      (`rpow_approxWeight_wedgeExponentAt`), so 7.5.31 and the negative weight apply unchanged
      (`rpow_approxWeight_le_of_eq`, `exists_forall_approxWeight_wedgeExponent_le` now take any
      exponents with that weight). The per-place wedge estimate is factored out of Layer 4.5
      (`apply_wedgeForms_plucker_le`).
    - The grid (`MinimaGrid.lean`, rewritten) rounds the constant, the jump and the `N` minima at
      the same mesh, with the minima part multiplied by `a` at `w₀`; since `w₀` weighs
      `mult w₀ = [K : ℚ] / a`, the cost in the weight is `[K : ℚ] binom(N, p) (p + 2)` meshes as
      before (`approxWeight_gridExponent_minimaGrid_le`), and the box and absolute weight are
      unchanged (`abs_ceil_add_abs_sum_ceil_le`, `sum_mult_abs_minimaGrid_le`).
      `N! (2 m + 1) ^ (N + 2)` grids: `parametricGridCount N d p`, and the counts of 6.1 no
      longer take the number of infinite places.
    - Thresholds: the constant is `pluckerConstAt K N = pluckerConst K N · unitConst K ^ N`
      (`pluckerAtCoeff = pluckerCoeff + N (d + 1)` in `ThresholdBound.lean`).
    - **Closed form**: `Z ^ (2 n + 14) ℓ (1 + log ℓ)` (grids `n! Z ^ (n + 2) ≤ Z ^ (2 n + 2)`),
      against `Z ^ (n d + n + 14) ℓ (1 + log ℓ)`. `d` stays in `Z`, linearly (the mesh `γ ∝ 1 / d`
      and `A = [E : K] (2 n + 2)`); removing it is not part of Q1.8.

  End state of Q1.8: `Z ^ (2 n + 14) log s log log s`-shaped, `Z = 2 ^ (n + 11) n ^ 6 d / δ`,
  against ES02's `4 ^ ((n + 8) ^ 2) δ ^ (-n - 4) log 2r log log 2r`: the same shape in `n`
  (`Z ^ (2 n)` carries `2 ^ (2 n²)`) and `log s`, with `δ ^ (-2 n - 14)` against `δ ^ (-n - 4)`
  and an extra `d ^ (2 n + 14)`. Thresholds gain `N log unitConst` and stay linear in `log H`.
- ✅ **Q1.9** The degree and `δ` (planned 2026-10-02, done 2026-10-03). Two gaps to ES02's parametric count that are
  bookkeeping in the present framework (Schmidt's polynomial, Evertse's Roth lemma), of the kind
  of Q1.7–Q1.8. The gap `Z ^ (2 n) ↔ 4 ^ (n²)` is not one of them: it is Ev10 § 6's, and Q2–Q4's.
  - ✅ **Q1.9a `d` out of `Z`.** **Done** (2026-10-03): `Z = 2 ^ (n + 11) n ^ 6 / δ`, no degree.
    Listing each `d` back to its lemma: every one sat in `(d + N (N + 2) (A + 1)) / ε` (the box
    `parametricBox_arg_eq`, the absolute weight `parametricWedgeAbsWeight_le`, and through it
    `η⁻¹`, the chain and the ratio), with `ε = systemEps e δ = [E : K] δ / 4` and
    `A = systemAbsBound e n = [E : K] (2 n + 2)`. Two parts:
    - `N (N + 2) (A + 1) / ε`: the minima, `B = N (A + 1) / d` rounded at the mesh `γ ∝ ε / d`, so
      `d` cancels, and `A ∝ [E : K]` cancels against `ε` (`systemCoeff_div_le`).
    - `d / ε`: the `1` in the box `(1 + B N + 2 B) / γ`, i.e. the range `|log_Q C| ≤ 1` of the
      constant at each infinite place, rounded at the per-place mesh `γ ∝ ε / d`. A coarser mesh
      for the constant does not help: its cost in the weight is per place either way. Instead
      Layer 6.1's threshold keeps `|log_Q C| ≤ B` like the minima: `parametricStepThreshold` takes
      `log C / B` in place of `log C` (`hQC : C ≤ Q ^ B` in
      `exists_forall_mem_interval_approxSpan_le`), the box is
      `⌈(B + B N + 2 B) / γ⌉ = ⌈4 N ^ 3 binom(N, p) (N + 2) (N + 3) (A + 1) / ε⌉`, and
      `A_p ≤ binom(N, p) (A + N (N + 3) (A + 1)) + ε` (`abs_ceil_add_abs_sum_ceil_le` takes any
      range `X` for the constant). The price is in the threshold: `parametricStepCoeff` has
      `pluckerAtCoeff d N / B` for `pluckerAtCoeff d N`; for a system
      `1 / B = [E : ℚ] / (n (A + 1)) ≤ [K : ℚ] / (2 n²)`, so the Plücker term of the threshold is
      multiplied by at most `[K : ℚ]`. ES02 (Lemma 15.1) normalize the absolute values, so their
      constants carry the `1 / [E : ℚ]` that this threshold supplies.
    The count lemmas of `SubspaceCountBound.lean` take `1 ≤ d` in place of `e ≤ d`;
    `evertseCountBase n δ` lost its degree argument. `[E : K]` is left only in `ℓ`, through
    `s = R [E : K]`, as ES02's `r`.
  - ✅ **Q1.9b `δ ^ (-2 n - 14)` toward `δ ^ (-n - 4)`.** **Done** (2026-10-03):
    `systemLargeCount ≤ c ^ (n + 7) Z ^ (n + 3) ℓ (1 + log (ℓ Z))` with
    `c = evertseCountConst n = 2 ^ (n + 11) n ^ 6` and `Z = c / δ`, i.e.
    `2 ^ (O(n²)) δ ^ (-n - 3) ℓ log (ℓ / δ)`. Two steps:
    - (i) Bookkeeping. Most of `2 n + 14` came from bounding factors free of `δ` by powers of
      `Z` (`n! ≤ Z ^ n`, `binom(n, p) ^ 3 ≤ Z ^ 3` in `η⁻¹`, `log ρ ≤ 14 Z`). Bounding them by
      `c` instead: `η⁻¹ ≤ c ^ 3 Z`, chain lengths `2 ℓ c ^ 6 Z ^ 2` (`δ ^ (-2)`, ES02's (16.2)),
      ratio `ρ ≤ 32 ℓ c ^ 10 Z ^ 3`, so `1 + log ρ / log (1 + δ / (2 n)) ≤ Z (1 + log (ℓ Z))`
      (`δ⁻¹ log δ⁻¹`).
    - (ii) The grids. They rounded `N + 2` numbers, the `N` minima, the constant `log_Q C` and
      the jump `log_Q (μ (k - 1) / μ k)`, each in the box: `N! (2 m + 1) ^ (N + 2)`, so
      `δ ^ (-n - 2)`. Now neither of the last two takes an integer (`MinimaGrid.lean`):
      `parametricStepThreshold` has `log C / γ` (was `log C / B`), so `0 ≤ log_Q C ≤ γ` and the
      constant rounds to `1`; and the top block, the only `p`-subset with all `π⁻¹ t ≥ k`, has
      exactly `p = N - k` indices, so it contains `k` (`mem_of_forall_le`) and its sum plus the
      jump is the sum with `k - 1` in place of `k`, rounded by `minimaJump k b = b (k - 1) - b k`
      (`sum_add_minimaJump_eq`). The grid count is `N! (2 m + 1) ^ N`, `m = ⌈B / γ⌉`
      (`parametricBox`, `= 4 N³ binom(N, p) (N + 2) (A + 1) / ε` up to rounding), so `c ^ n Z ^ n`,
      `δ ^ (-n)` like ES02's `(2 n B) ^ n` classes (Lemmas 17.2, 18.1); the entries are at most
      `1 + N m` (`abs_sum_add_minimaJump_le`), so `A_p ≤ binom(N, p) (A + N² (A + 1)) + ε`, and the
      rounding costs `p + 1` meshes per subset instead of `p + 2`. The price is in the threshold:
      `parametricStepCoeff` has `pluckerAtCoeff d N / γ`, with
      `1 / γ = 4 N² d binom(N, p) (N + 2) / ε`, which enters the count only through the
      logarithm of the middle ratio (Layer 9.4).

    So the large solutions cost `δ ^ (-n - 3) log δ⁻¹`, within ES02's `δ ^ (-n - 4)`; the two
    `δ` need not be the same normalization (Q0.3's `δ` is the weight of a normalized system).
  - End state aimed at: `C(n) δ ^ (-n - O(1)) ℓ log ℓ`, `C(n) = 2 ^ (O(n²))`, no `d`. **Reached**
    (after Q1.9b): `c ^ (n + 7) Z ^ (n + 3) ℓ (1 + log (ℓ Z))`, i.e.
    `2 ^ (O(n²)) δ ^ (-n - 3) ℓ log (ℓ / δ)`. What is left against ES02 is `n`: `c ^ (2 n + 10)`
    against `4 ^ ((n + 8)²)` are both `2 ^ (O(n²))`; EF13's `2 ^ (2 n)` is Q2's.

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
  That is bookkeeping of the kind Ev95 §5 does. Thm 3 is done (Q1.4), with a better ratio
  condition than Ev95's. (?) It remains to check that the constants still give Ev96's shape.

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
- ✅ The errors go into the `d_1 + ⋯ + d_m` term of Thm 3, at the price of a worse constant
  (confirmed by `exists_mul_logHeight_le`, Q1.4).

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
  - ✅ `h(ℙ) ≤ [K : ℚ] log M(det_{n_j+1})` (`ForMathlib/NumberTheory/Height/SpaceHeight.lean`),
    with `log M(det_N) ≤ N (log (2N) / 2 + 2)` (`detLogMahler_le`).
  - ✅ The point bound (L) (`logHeight_mul_le_gaussHeight_resForm`,
    `ForMathlib/NumberTheory/Height/PointHeight.lean`).
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
  re-run, and `resultantHeight` instantiates the interface. (L) was added as the field
  `logHeight_mul_le_cycleHeight`.

Q1.1 does not depend on the Q1.3 decision. Q1.1a–d have landed, the excess Bézout inequality of
Q1.1d(iv) (with the Cohen–Macaulay property of `B_𝔭`, proved 2026-10-02). Q1.1e has the
multiplicity estimate, its combination with Bézout, the Hasse-derivative form of its
hypothesis and, in characteristic `0`, the transversal `Q_α` with the dimension formula
`ht 𝔭 + trdeg = |σ|` and the positivity of the degree in the type of the adapted basis
(`prod_pow_mul_pow_le`, Rémond 2001 Prop. 2.1). Q1.2 is done: Rémond's Thm 1.1 and Cor. 1.1, geometric parts (`productTheorem_indexIdeal`,
`exists_productTheorem_indexIdeal`). Q1.3 (heights): the height parts of Thm 1.1 and Cor. 1.1
hold for every `MultiprojectiveHeight` (`productTheorem_indexIdeal_height`,
`exists_productTheorem_indexIdeal_height`), with Rémond's error term via his Lemma 5.2, and
actual heights of resultant forms satisfy the interface (`resultantHeight`), with
`h(ℙ^n) ≤ [K : ℚ](n + 1)(log (2(n + 1)) / 2 + 2)`, and the point bound (L) of Ev95 §5 holds.

### Layer Q2: the absolute theory (Roy–Thunder 1996, Evertse–Schlickewei 1999/2002)

Move from points in `Kⁿ` to points in `ℚ̄ⁿ`, with counts independent of `K`.

- **Q2.0** ✅ **Literature gate — decided: Q2 stays elementary.** The absolute geometry of numbers
  is RT96 Theorem 6.3, proved from `FieldMinkowski.lean` by Roy–Thunder's own argument; no Zhang,
  no Arakelov layer, no addendum.
  - **What ES02 uses.** Exactly one external result, ES02 Prop. 7.1 = RT96 Thm 6.3 (ES02 §7,
    `../lean-code/papers/EvertseSchlickewei2002.pdf`): for twisted heights
    `H_A(x) = ∏_w max_i ‖L_i^{(w)}(x)‖_w / A_{iw}` on `ℚ̄ⁿ`, with place-dependent forms and
    weights, the minima `λ_i = inf{λ : dim span{x ∈ ℚ̄ⁿ : H_A(x) ≤ λ} ≥ i}` satisfy
    `n^{-n/2} ∏_v Δ_v/A_v ≤ λ₁⋯λₙ ≤ 2^{n(n-1)/2} ∏_v Δ_v/A_v`, under ES02's hypothesis (7.4)
    that every `A_{iv}` is a value `‖α_{iv}‖_v`. The upper bound is the hard half; it is where
    Schlickewei's `D_K^{n/2d}` came from (ES02 §1). ES02 removes (7.4) themselves (Cor. 7.2, an
    elementary `N`-th-root approximation), and pass from RT's ℓ² norm at infinity to the max norm
    with the factor `n^{1/2}` of (7.8). No absolute Siegel lemma in product form is used.
  - **The proof of RT96 Thm 6.3** (`../lean-code/papers/RoyThunder1996.pdf`, §§1–6) is
    elementary. Dependency chain: Thm 6.3 ← Lemma 3.3 (a local map adapted to a flag), Lemma 4.7
    (the lower bound: Hadamard for wedges), Prop. 6.2 (`μ₁ ≤ 2^{(n-1)/2} |det A|^{1/n}`, induction
    on `n`) ← twisted duality Thm 1.1 (quoted from Thunder 1993), Prop. 4.2 and Cor. 4.3 (pulling a
    twisted height back along an injective map; exterior-power and determinant parts only), and the
    base case `n = 2`, Prop. 5.3 ← Lemma 5.2 (Bombieri–Vaaler's adelic Minkowski theorem **with**
    its field constant `C(K)`), Lemma 4.8 (heights of products in `S^r`, from Lemma 3.4(ii) and the
    algebra identity `S^rA(x₁⋯x_r) = (Ax₁)⋯(Ax_r)`), Lemma 4.5 (`det S^rA = (det A)^{r(r+1)/2}`
    for `n = 2`). The field constant disappears in Prop. 5.3: Lemma 5.2 on `S^r(K²)`, of
    dimension `r + 1`, costs `C(K)^{O(r)}`, a nonzero binary form of degree `r` splits into `r`
    linear forms over an extension of degree `≤ r`, and the counting argument takes an
    `r(r+1)/2`-th root, leaving `C(K)^{2/r} → 1` as `r → ∞`. The absolute statement is a limit
    of number-field statements, not Arakelov theory.
  - **The addendum is not needed.** RT's *Addendum and erratum* (J. reine angew. Math. **508**
    (1999) 47–51, paywalled, front page seen) refines the constant of RT96's Siegel lemma (Thm
    2.2, not used by ES02) and "corrects a mistake that invalidates parts of some auxiliary
    results in §§3–4", concerning the norms on symmetric powers. The mistake as we read it: §1
    gives `S^r(Lⁿ)` the ℓ² norm in the monomial basis, and the proof of Lemma 3.2(ii) identifies
    that inner product with `perm(⟨x_i, y_j⟩)`, which gives `⟨e₁², e₁²⟩ = 2`, not `1`; so `S^rφ`
    need not preserve norms, and Lemma 3.2(ii) for `S^r`, Cor. 4.3(ii), Cor. 4.4(ii) and Prop. 4.6
    fall. None of these is on the chain above: Prop. 4.6 is used only in the Remark after Thm 5.1,
    and Lemma 4.8 uses the algebra identity, not norm preservation. ES02 cite RT96 alone. This
    reading is ours, not the addendum's text; Q2.2c re-proves every step it uses, so nothing rests
    on it.
  - **Rejected alternatives.** *Zhang 1995* (`../lean-code/papers/Zhang1995.pdf`; ES02's
    "Theorem 5.8" is Theorem 5.2 in the JAMS numbering, (5.8) there is a remark) implies the upper
    bound: on `ℙ^{n-1}` with the twisted metric, `e_{n-k+1} ≥ log λ_k` is elementary and
    `Σ e_i ≤ ĥ(ℙ(M), Ō(1))` is Thm 5.2. But Thm 5.2 rests on arithmetic Hilbert–Samuel
    (Gillet–Soulé, Hironaka), arithmetic ampleness (Hörmander L² estimates) and an induction
    through arbitrary arithmetic hypersurfaces — out of reach. *Forst–Fukshansky 2024*
    (`ForstFukshansky.pdf`, an absolute Siegel lemma by linear algebra alone) bounds
    `max H(ω_i) ≤ H(Z)`, not the product; it is for coordinate heights, which place-dependent
    twists `L^{(v)}` are not, and over a fixed `k`, not `ℚ̄`; it does not give Thm 6.3. *Keeping
    `|D_K|`* in the thresholds (as Q1.8 does) stays available as the unconditional fallback, but
    is no longer the plan.
  - **What `ArithmeticHeights` and DA already supply.** The general `NumberField.
    prod_successiveMinimum_pow_mul_measure_le` (`DA/FieldMinkowski.lean`: any symmetric convex
    body, any `𝓞 K`-lattice in `Kⁿ`, constant `2^{dn}`), with `DA/ModuleCovolume.lean` for the
    covolume of a twisted lattice place by place and `DA/FieldMinima.lean` for minima over `K`,
    is Lemma 5.2 up to computing a volume. `ArithmeticHeights/Hadamard.lean`, `CauchyBinet.lean`,
    `Plucker.lean`, `Subspace.lean` and `Arakelov.lean` give Hadamard for wedges and ℓ² Plücker
    heights; `Duality.lean` gives untwisted duality; `GaussLemma.lean`, `Gelfond.lean` and
    Mathlib's `Polynomial.mahlerMeasure_mul` give heights of products; `Absolute.lean`,
    `Extension.lean`, `DA/PlacesOver*.lean` and `DA/LocalExtension.lean` give independence of the
    field and the places above a place.
  - **The carrier of a twist — the one design decision.** RT's twists are adelic,
    `A ∈ GLₙ(K_𝔸)`, and their constructions produce local matrices that are not `K`-rational
    (Gram–Schmidt in Lemma 3.2(i)). Avoid completions as follows. At a **finite** place a twist
    only matters through the `𝒪_v`-lattice it defines, and every lattice of `K_vⁿ` has a basis in
    `Kⁿ` (density), so finite twists are `K`-rational: a matrix in `GLₙ(K)` per finite place, the
    identity outside a finite set, and `‖A_v x‖_w` is read with the absolute value `w` of the
    extension directly. At an **infinite** place a twist is a complex matrix `A_v` (real for a
    real place) acting through the embedding of `v`, conjugated for a place `w` whose embedding
    restricts to the conjugate — `‖conj(A) conj(y)‖ = ‖A y‖`. RT's Thm 6.3 needs one auxiliary
    place `u₀` with `|b|_{u₀} > 1`; Q2.0 took it **finite** (`u₀ = p`, `b = 1/p`), so Lemma 3.3 is
    needed at a finite place only and is `K`-rational too. Revised at Q2.2a: Q2.2e does both a
    complex and a finite `u₀` (see there). ES02's twisted heights (7.3) are the special
    case `A_v = diag(A_{iv}⁻¹) ∘ (L_i^{(v)})`.
  - **Constants.** RT's `2^{n(n-1)/2}` comes from `2^{(n-1)/2}` in Prop. 6.2(ii), which in turn
    comes from the base case `n = 2`; whatever constant Q2.2c delivers at `n = 2` propagates.
    ES02's count only needs `c(n) ≤ 2^{O(n²)}`, so a weaker base constant is acceptable if exact
    `√2` costs effort; record which one landed.
- **Q2.1** Twisted heights on `ℚ̄ⁿ` and their basic calculus (RT96 §1, §4 Props. 4.1–4.2; ES02
  (7.3)). The carrier of Q2.0: archimedean complex matrices, finite `K`-rational matrices, the
  identity at almost all places; the ℓ² norm at infinity (RT's) with ES02's max-norm comparison
  (7.8) beside it. The height `H_A` on `Eⁿ` for every finite extension `E ⊇ K`, independent of
  `E` (on `Absolute.lean`'s pattern), so that it is a height on `ℚ̄ⁿ`; `|det A|_𝔸`; the height
  of a subspace through `⋀^m A` and Plücker coordinates (Lemma 3.2(ii) for exterior powers:
  unitary and `GLₙ(𝒪_v)` invariance of `⋀`); comparison with the untwisted height, two-sided with
  constants depending on `A` (Prop. 4.1), so that Northcott makes the minima attained and positive;
  the absolute minima `μ_i(A)` of RT Def. 6.1.
  - **Q2.1a** ✅ **The height of a point** — landed, in `QuantitativeSubspace/TwistedHeight.lean`.
    `NumberField.Twist K ι` is the carrier (`arch` per complex embedding with `arch_conjugate`,
    `fin` per finite place, `K`-rational, `1` off a finite set, all invertible);
    `Twist.mulHeight` is RT's `H_A` relative to a number field `E ⊇ K`, the archimedean product
    taken over the complex embeddings of `E` (each complex place twice, which is its `n_w = 2`).
    Proved: `mulHeight_algebraMap` (over `F ⊇ E` it is raised to `[F : E]`), `mulHeight_smul`
    (product formula), `mulHeight_pos`; and `Twist.absMulHeight` on any `Ω` algebraic over `K`,
    computed over `K(x₀, x₁, …)` and normalized by its degree, with `absMulHeight_eq_of_mem` (any
    finite extension inside `Ω` containing the coordinates gives the same value),
    `absMulHeight_smul` and `absMulHeight_pos`. The finite half of the extension formula is the
    reusable `FinitePlace.finprod_under_pow_localDegree`, on a new `FinitePlace.under` (the place
    below, from Mathlib's `HeightOneSpectrum.under`); its archimedean half is
    `NumberField.prod_comp_eq_prod_pow`, made public in `ArithmeticHeights/Extension.lean` together
    with `prod_embeddings_eq`. ⚠ The height of `0` is `0`, not Mathlib's junk `1`.
  - **Q2.1b** ✅ **The comparison with the untwisted height** (RT Prop. 4.1) — landed, in the
    same file, for any two twists at once: `compConst A B` is the product over `K` of the ℓ²
    operator norms of `A_φ B_φ⁻¹` and the largest entries of `A_v B_v⁻¹`, and
    `mulHeight_le_compConst_pow_mul` gives `H_A ≤ c ^ [E : K] · H_B` over every `E`, absolutely
    `absMulHeight_le_compConst_rpow_mul` (`c ^ {1/[K:ℚ]}`). `B = 1` is RT's `H_A ≤ c_A H_1`,
    `A = 1` is `H_1 ≤ c_{A⁻¹} H_A` (no inverse twist needed). `mulHeight_one_eq`: `H_1` is
    `arakelovMulHeight`; hence `compConst_rpow_neg_le_absMulHeight`, a positive lower bound on
    nonzero points (what makes `μ₁ > 0` in Q2.1c), and `finite_setOf_mulHeight_rep_le`,
    Northcott over a fixed `E` (from `ArithmeticHeights/Northcott.lean`). `compConst_pos` needs
    `ι` nonempty. ⚠ Over `ℚ̄` the minima of RT Def. 6.1 are infima — Northcott needs a degree
    bound, so attainment is only over a fixed field.
  - **Q2.1c** ✅ **The absolute minima** (RT Def. 6.1) — landed, in the same file:
    `absMinimum A Ω i = sInf (absMinimumSet A Ω i)`, over any `Ω` algebraic over `K` (RT's
    `μ_i(A)` at `Ω = AlgebraicClosure K`), meaningful for `1 ≤ i ≤ n` (junk `0` otherwise).
    Proved: `absMinimumSet_nonempty` (standard basis), `absMinimum_le` (independent points bound
    it), `absMinimum_one_le`, `absMinimum_le_absMinimum` (monotone), the uniform lower bound
    `compConst_rpow_neg_le_absMinimum` and `absMinimum_pos`, and in place of attainment
    `exists_linearIndependent_absMulHeight_lt` (independent points of height `< μ` above `μ_i`),
    which is what RT's proof of Thm 6.3 takes (its `μ_i(A) + ε`).
  - **Q2.1d** ✅ **`⋀^m A` and `|det A|_𝔸`** — landed, in
    `QuantitativeSubspace/TwistedSubspaceHeight.lean`. `Matrix.compound k M` is *defined* as the
    matrix of `exteriorPower.map k` in the induced basis, so `compound_mul`/`compound_one` are
    functoriality (no Cauchy–Binet); `compound_mulVec_plucker` (`⋀^k M` on Plücker coordinates),
    `compound_apply` (minors), `compound_map` (ring homs, for `arch_conjugate`),
    `compound_card_apply` (top degree = `det`), `det_compound_ne_zero`.
    `Twist.exteriorPower A k`, `Twist.absDet A` (`|det A|_𝔸`, absolute) with `absDet_pos`;
    `Twist.absSubspaceHeight A V` for `V : Submodule Ω (ι → Ω)` (read off the Plücker point),
    `absSubspaceHeight_eq` (any basis), `absSubspaceHeight_span_range`, `absSubspaceHeight_pos`,
    and `absSubspaceHeight_top : H_A(Ωⁿ) = |det A|_𝔸`. Helpers in `TwistedHeight.lean`:
    `FinitePlace.under_self`, `Twist.absMulHeight_algebraMap` (a point of `Kⁿ`: `H_{A,K}^{1/[K:ℚ]}`).
    Deferred to Q2.2a, where it is used: a line's height is its point's (`⋀¹ A ≅ A` needs a
    reindexing lemma for twists).
- **Q2.2** **The absolute Minkowski theorem** (RT96 Thm 6.3; ES02 Prop. 7.1 and Cor. 7.2), in five
  parts.
  - **Q2.2a** ✅ **Local and global calculus** — landed, in three files. Lemma 3.3 moved to
    Q2.2e, the only place it is used (see there).
    - `QuantitativeSubspace/TwistedCalculus.lean`: **base change**
      (`Twist.baseChange A E`, a twist over any finite extension `E`, with
      `absMulHeight_baseChange`, `absSubspaceHeight_baseChange`, `absDet_baseChange`: no
      absolute quantity changes; RT96 §6 needs it whenever `φ` or `B` lives over a larger
      field), `absMulHeight_algHom` (the absolute height in any field of definition, through any
      `K`-embedding), **lines** (`absSubspaceHeight_span_singleton : H_A(Ω x) = H_A(x)`, read
      through `Set.powersetCard.ofSingleton` — no reindexed twist needed), and **Lemma 4.7**
      (`absSubspaceHeight_span_range_le_prod : H_A(V) ≤ ∏ H_A(x_i)`, from
      `sum_sq_norm_plucker_row_le_prod` and `iSup_plucker_le_prod` place by place).
    - `QuantitativeSubspace/TwistedDuality.lean`: **twisted duality** (RT96 Thm 1.1).
      `Twist.dual A` (`(A_v⁻¹)ᵀ`), `dual_dual`, `dual_baseChange`, `absDet_dual`;
      `absSubspaceHeight_eq_absDet_mul : H_A(V) = |det A|_𝔸 · H_{A*}(V^⊥)` and
      `absSubspaceHeight_dual`, `V^⊥` the transported annihilator of `Duality.lean`. Proof as
      in `Duality.lean`: dual matrices `C Dᵀ = 1`; the rows of `C Mᵀ` and `D M⁻¹` are again dual
      (`Matrix.plucker_mulVec_inl_eq_or_eq_neg`), so the twisted Plücker norms differ by
      `|det C|·|det M|` at every place, and the product formula removes `det C`.
      `ArithmeticHeights/Duality.lean` gained the public `Matrix.plucker_inl_eq_or_eq_neg`, and
      five of its helpers (`exists_dual_matrices`, `span_range_inr_row_eq`,
      `linearIndependent_row_of_mul_transpose_eq_one`,
      `isUnit_det_submatrix_of_mul_transpose_eq_one`, `det_submatrix_equiv_eq_or_eq_neg`) are
      no longer private.
    - `QuantitativeSubspace/TwistedPullback.lean`: **Prop. 4.2 and the determinant identity**.
      For `P : Matrix ι (Fin m) K` with independent columns, `Twist.pullback A P hP` with
      `absMulHeight_pullback : H_B(x) = H_A(P x)` and
      `absDet_pullback : |det B|_𝔸 = H_A(P Ωᵐ)`. Not RT's Lemma 3.2(i): at a finite place
      `B_v` is a **maximal minor** of `A_v P` (`Matrix.iSup_mulVec_eq_of_isMaxMinor`: by Cramer
      each row of `M` is a combination of the rows of a maximal minor with coefficients of
      absolute value `≤ 1`, so the max norms agree over every extension), `1` off the finite set
      `badPlaces` (there `iSup_mulVec_eq_of_det`, an integral matrix with unit determinant is an
      isometry) — so no completions, DVRs or Iwasawa decomposition. At a complex embedding
      `B_φ = gramSqrt (A_φ P)`, the CFC square root of the Gram matrix, and `gramSqrt_map_conj`
      (uniqueness of the positive square root) gives `arch_conjugate`. The determinant identity
      is Cauchy–Binet at infinity and `iSup_plucker_col_eq` (the largest Plücker coordinate is
      the maximal minor) at the finite places. RT's Cor. 4.3(i) for general subspaces `W` is not
      proved: Prop. 6.2 uses only the point and top-degree statements.
  - **Q2.2b** ✅ **Lemma 5.2 over `K`** — landed, in `QuantitativeSubspace/TwistedMinkowski.lean`.
    `exists_linearIndependent_prod_mulHeight_le`: `n` vectors of `Kⁿ`, independent over `K`, with
    `∏ H_A(x_i) ≤ (√|D_K| · √n^d)ⁿ · |det A|_K` (relative heights; the exact constant of the proof
    is `((2/π)^{r₂} √|D_K| √n^d)ⁿ`), and the absolute form
    `exists_linearIndependent_prod_absMulHeight_le`, `(|D_K|^{1/2d} √n)ⁿ · |det A|_𝔸`. Proof:
    `FieldMinkowski`'s upper bound and `FieldMinima`'s attained minima for
    - the **lattice** `Twist.lattice` (`A_v x` integral at every finite `v`), which is the
      approximation module of `DA/ApproximationDomain.lean` for the rows of the finite components
      at level `1`, exponents `0` — so FG, discreteness, the lattice property and the covolume
      `∏_v |det A_v|_v · covol(𝒪_K)ⁿ` are `covolume_approxLattice`, with no new finite-place work;
    - the **body** `Twist.body`, the preimage of the sup-norm unit ball under the
      `mixedSpace K`-linear map of `Twist.mixedMatrix` (real parts at real places, where
      `arch_conjugate` makes the components real; `w.embedding` at complex places), of volume
      `(2^{r₁}π^{r₂})ⁿ / ∏_φ |det A_φ|` (`volume_body`, via `volume_mixedBox` and
      `abs_algebraNorm_eq_norm`).
    A lattice point in `μ` times the body has `H_A ≤ (√n μ)^d` (`mulHeight_le_of_mem_lattice`).
    ⚠ The constant is `c(K)ⁿ · n^{dn/2}`, not `c(K)ⁿ`: the box inside the ℓ² ball, as in RT's own
    volume estimate (`(r + 1)^{d/r}` in their Thm 5.1). Prop. 5.3 takes the `r(r+1)/2`-th root
    with `n = r + 1`, so the extra factor tends to `1`. No basis reduction is needed (Prop. 5.3
    uses only independence). `DA/ApproximationVolume.lean`'s `placeHom`,
    `normAtPlace_eq_norm_placeHom`, `placeHom_mixedEmbedding`, `mixedBox`, `mixedBox_eq` and
    `volume_mixedBox` are no longer private.
  - **Q2.2c** ✅ **The case `n = 2`** (RT Prop. 5.3) — landed, with RT's constant `c₂ = 2`:
    `absMinimum_one_mul_absMinimum_two_le_two_mul : μ₁(A) μ₂(A) ≤ 2 |det A|_𝔸` for every twist of
    the plane, minima over an algebraically closed `Ω`. Two files.
    - `QuantitativeSubspace/TwistedSymmetric.lean`: binary forms dehomogenized (`binLinear x =
      x₀ + x₁ T`, `coeffVec r` the first `r + 1` coefficients), `Matrix.symPow r M` (column `l` =
      coefficients of `(M e₀)^{r-l} (M e₁)^l`), its action on products of linear forms
      (`symPow_mulVec_coeffVec_prod`, from the homogenization identity `homEval_prod_binLinear`),
      `symPow_mul`, `symPow_one`, `symPow_map`; **Lemma 4.5** `det_symPow : det S^r M =
      (det M)^{r(r+1)/2}` by `diagonal_transvection_induction` (triangular/diagonal cases);
      `Twist.symPow A r`, `absDet_symPow`; **Lemma 4.8** (lower half) `prod_absMulHeight_le :
      ∏ H_A(x_j) ≤ √2^r H_{S^r A}(x₁ ⋯ x_r)`: Gauss's lemma at finite places (equality), and at
      complex places `‖z‖ ≤ √2 M(ℓ_z)`, multiplicativity of the Mahler measure and Landau's
      `M(p) ≤ ‖p‖₂` (Mathlib). The archimedean components of `S^r A` are just `S^r A_φ`; no
      claim about `S^r` preserving norms is used, so the addendum's correction is irrelevant.
    - `QuantitativeSubspace/TwistedPlane.lean`: splitting a binary form over `Ω`
      (`exists_eq_C_mul_prod_binLinear`, a factor `(1, 0)` per root at infinity), the dimension
      bound `card_filter_lt_card_le` (independent forms divisible by `ℓ^{t+1}` number `≤ r - t`,
      divisibility read homogeneously through the factorization, so the point at infinity needs no
      special case), the counting argument `exists_linearIndependent_pair` (any height `h ≥ 0`),
      Prop. 5.3 for a given `r` with `planeConst r = 2 (|D_K|^{1/d} (r+1))^{1/r}`
      (`absMinimum_one_mul_absMinimum_two_le`), and `tendsto_planeConst` (→ 2). RT's degree bound
      `[K(y_i) : K] ≤ r` is not kept: the absolute minima do not need it.
  - **Q2.2d** ✅ **The first minimum** (RT Prop. 6.2) — landed, with RT's constants, in
    `QuantitativeSubspace/TwistedFirstMinimum.lean`, for twists of `Kⁿ` indexed by `Fin n`:
    (ii) `absMinimum_one_pow_le : μ₁(A)^n ≤ √2^{n(n-1)} |det A|_𝔸` for every `n ≥ 1` (RT's form
    `μ₁(A) ≤ √2^{n-1} |det A|_𝔸^{1/n}` is `absMinimum_one_le_rpow`), and (i)
    `absDet_mul_dual_absMinimum_one_pow_le : |det A|_𝔸 μ₁(A*)^{n-1} ≤ √2^{(n-1)(n-2)} μ₁(A)`.
    For (i), every nonzero `x` (not one of height near `μ₁(A)`, so no `ε`): over `F = K(x)`
    `exists_col_span_eq_dual` gives `P` with independent columns spanning `(Ω x)^⊥` (a basis of
    the kernel of `z ↦ Σ x_i z_i`, equality by dimension), the pullback `B` of `A*_F` along `P`
    has `μ₁(A*) ≤ μ₁(B)` (`absMulHeight_pullback`) and `|det B|_𝔸 = |det A|_𝔸⁻¹ H_A(x)`
    (`absDet_pullback`, `absSubspaceHeight_dual`, lines), and (ii) in dimension `n - 1` applies
    to `B`. (ii) in dimension `n ≥ 3` is (i) for `A` and `A*` (private `pow_le_of_dual`);
    `n = 2` is Q2.2c, `n = 1` is `absMinimum_one_le_absDet`. The field changes from `K` to `F`,
    in the universe of `Ω`, so the induction (`absMinimum_one_pow_le_aux`) runs over number fields
    in that universe, and the statements for arbitrary `K` call it in dimension `n - 1`.
  - **Q2.2e** ✅ **The theorem** (RT Thm 6.3) — landed, with RT's constant, through **both**
    auxiliary places: `|det A|_𝔸 ≤ μ₁(A) ⋯ μₙ(A) ≤ √2^{n(n-1)} |det A|_𝔸 = 2^{n(n-1)/2} |det A|_𝔸`
    for twists of `Kⁿ` on `Fin n`, minima over an algebraically closed `Ω`. ES02 Prop. 7.1 and
    Cor. 7.2 are not done here; they moved to Q2.2f (see there).
    - `QuantitativeSubspace/TwistedSuccessiveMinima.lean`, **complex `u₀`** and the shared parts.
      The **lower bound** `absDet_le_prod_absMinimum` (any `ι`, `Fintype.card ι = n`): Lemma 4.7
      for bases of almost minimal height, then `ε → 0`. The **flag** (shared):
      `exists_absMinimum_gap` (an `ε` below every jump of the minima),
      `exists_linearIndependent_absMulHeight_lt_absMinimum_add` (a greedy basis with
      `H_A(x_k) < μ_{k+1} + ε`), `absMinimum_le_absMulHeight_of_notMem_span` (outside
      `span(x_k : k < i)` the height is `≥ μ_{i+1}`, RT's argument with the gap), plus
      `absMinimum_zero`/`_nonneg`/`_mono`. The **upper bound** `prod_absMinimum_le`: `E` generated
      by the basis and `√-1`, so a complex embedding `φ₀` of `E` is never real; Lemma 3.3 is
      replaced by `Matrix.exists_isUpperTriangular_gram_eq` (an upper triangular `R` with
      `Rᴴ R = Gᴴ G`, `G = A_{φ₀} φ₀(X)`, from Mathlib's `gramSchmidtOrthonormalBasis` and
      `gramSchmidtOrthonormalBasis_inv_triangular`; the isometry is `norm_toLp_mulVec_eq_of_gram`
      of Q2.2a, so no unitary matrix is built); `Twist.modify` (components `M`, `conj M` at
      `φ₀`, `conj φ₀`) with `le_absMulHeight_modify` (`H_B ≥ c^{2/[E:ℚ]} H_A` from a bound at
      every embedding `ψ : Ω → ℂ` above `φ₀`, extended by `RingHom.exists_comp_algebraMap_eq`) and
      `absDet_modify`; `M = diag(a) R φ₀(X)⁻¹`, `a_i = μ_i^{-[E:ℚ]/2}` exactly. No `ε` in the
      bound, no `N`-th roots.
    - `QuantitativeSubspace/TwistedSuccessiveMinimaFinite.lean`, **finite `u₀`** (RT's route).
      `Matrix.exists_integral_mul_isUpperTriangular` (Iwasawa at a nonarchimedean absolute value:
      mutually inverse integral `V`, `W` with `V G` upper triangular, by Gaussian elimination with
      the largest pivot, column by column on full-size matrices, so no block matrices),
      `Matrix.iSup_mulVec_eq_of_mul_eq_one` (such `V` are max-norm isometries over every
      extension), `Twist.modifyFin` with `mulHeight_modifyFin_ge`, `le_absMulHeight_modifyFin`,
      `absDet_modifyFin`; `FinitePlace.exists_one_lt` (`u₀`, `b₀ ∈ K` with `|b₀|_{u₀} > 1`, from
      the product formula at `2`). An `N`-th root `b` of `b₀` and any place `w'` above `u₀` give
      `β = |b|_{w'}^{1/[E:ℚ]} ∈ (1, 1 + ε]` because the local degree is `≤ [E:K]`: no ramification
      theory, unlike RT's "we may assume `1 < |a|_{v₀} < 1 + ε`". Weights `a_i = b^{m_i}`,
      `m_i = ⌈-log μ_i / log β⌉`; `prod_absMinimum_le_one_add_pow_mul` (bound with `(1 + ε)ⁿ`) and
      `prod_absMinimum_le_of_finitePlace` (`ε → 0`).
  - **Q2.2f** Merged into **Q2.4c** (ES02 Prop. 7.1 and Cor. 7.2 = EF13 Prop. 9.2): they are
    about ES02's height (7.3), whose forms and real weights Q2.4a introduces.
  - Not part of Q2.2: RT96 Thm 2.2 (the absolute Siegel lemma in product form), §7 (duality of
    all minima) and §8; ES02 does not use them.
- **Q2.3** The absolute Subspace Theorem, qualitative (ES99). ES99 is not local; the qualitative
  statement is a corollary of Q4 (formerly of ES02), so this milestone is optional and may be
  dropped.
- **Q2.4** **EF13's set-up, and what EF13 takes from ES02.** Scope decided 2026-10-03: EF13
  (`../lean-code/papers/EvertseFerretti.pdf`) cites ES02 (`EvertseSchlickewei2002.pdf`) for
  exactly Cor. 7.2 (EF13 Prop. 9.2), Lemma 6.3 (EF13 Lemma 11.1) and Davenport's Lemma 9.2 (EF13
  Lemma 11.3, "the same proof, with small modifications"); Thm 20.1 only to compare bounds, and
  §21 only for EF13 Cor. 3.2, stated without proof. EF13 restates ES02's set-up itself (§§2, 6,
  7), and its Roth machinery (§§12–14) and reduction (§§15–18) replace ES02's (§§12–19). So
  **ES02's own theorems (2.1, 3.1, 20.1) and their count `4^{(n+9)²} δ^{-n-4}` are not
  formalized**: Q4 gives the better count, and consumers (BE08 and the rest) are to use EF13's
  Thm 3.1. The work over `ℚ̄` that ES02 §1 warns about is the part of EF13 §§8–14 that Q4 does.
  Notation as in EF13: `L = (L_i^{(v)})`, `c = (c_iv)` over all places `v ∈ M_K`, normalized
  `‖·‖_v`, max norm at every place (RT96's ℓ² norm only in Q2.4c's proof).
  - **Q2.4a** ✅ **The twisted height `H_{L,c,Q}`** (EF13 §2.2, §7):
    `QuantitativeSubspace/FormHeight.lean`. Places are indexed as in EF13 (`InfinitePlace K`,
    `FinitePlace K`), not by embeddings. `NumberField.FormSystem K ι` (an invertible `K`-matrix
    of forms per place, finitely many distinct at the finite places) and
    `NumberField.FormWeight K ι` (positive weights, `1` almost everywhere), in Mathlib's relative
    normalization: ES02's `A_iv = ‖α_iv‖_v` is `a_iv = v α_iv`. `mulHeight` (relative,
    `mulHeight_algebraMap` via the new `FinitePlace.localDegree_tower`), `absMulHeight` (through
    `adjoin K (range x)`), `absMulHeight_smul`, `absMulHeight_algHom`, `absMulHeight_algEquiv`
    (Galois invariance, EF13/ES02 Lemma 4.1). `FormExponent` and `FormExponent.weight`
    (`Q ^ {c_iv [K:ℚ] / mult v}` at an infinite `v`, `Q ^ {c_iv [K:ℚ]}` at a finite one) make
    `absMulHeight L (c.weight hQ)` EF13's `H_{L,c,Q}`. Lemma 7.2 (i):
    `absMulHeight_of_scale`, `absMulHeight_weight_of_sub`. Lemma 7.3 (i), (iv): `comp`,
    `absMulHeight_comp`, `absDet_comp`. `absDet` (`Δ_L`), `forms`, `detSet`, `absFormHeight`
    (`H_L`); (7.4) `absDet_le_absFormHeight` and `absFormHeight_rpow_le_absDet`
    (`H_L ^ {1 - C(r,n)} ≤ Δ_L`, the count from squared determinants, which depend only on the
    set of rows: `det_sq_eq_of_image_eq`, `card_detSq_le`). Lemma 7.1: `one_le_absMulHeight`
    (any weights, `1 ≤ n ((H_L/Δ_L) A) ^ {1/[K:ℚ]} H(x)`) via Cramer in row form
    (`mul_adjugate_apply_eq_det_updateRow`), and `le_absMulHeight_weight`
    (`H_{L,c,Q}(x) ≥ n⁻¹ H_L ^ {-C(r,n)} Q ^ {-θ}`, `θ = Σ_v max_i c_iv`, `Q ≥ 1`). Lemma 7.3
    (ii), (iii) are about the weight `w(U)` of a subspace and go with Q3.
  - **Q2.4b** ✅ **Successive infima** (EF13 §9 start, ES02 Lemma 4.2 and Cor. 7.5):
    `QuantitativeSubspace/FormSuccessiveInfima.lean`. `Submodule.IsDefinedOver K T` (spanned by
    points of `Kⁿ`); ES02 Lemma 4.2 as `Submodule.mem_span_algebraMap_of_forall_algHom` /
    `isDefinedOver_of_forall_algHom` for `Ω` algebraically closed and algebraic over `K` (any
    subspace stable under `Ω →ₐ[K] Ω`), proved with the trace dual basis of `K(x)` and
    `AlgHom.liftNormal` instead of inverting `(σ_i(ω_j))`. `FormSystem.infSpace` (`T(λ)`),
    `successiveInf` (`λ_i`, junk `0` for `i > n`), `infFlag` (`T_i`); `successiveInf_le`,
    `le_finrank_infSpace`, `successiveInf_mono`, `exists_infSpace_eq_top`. EF13 Lemma 9.1:
    (i) `infSpace_isDefinedOver`, `infFlag_isDefinedOver` (via the new
    `absMulHeight_comp_algHom` in `FormHeight.lean`); (ii) `finrank_infSpace_of_lt`,
    `infSpace_eq_infFlag`, `finrank_infFlag`. Stated for any weights `a`, so also for
    `c.weight hQ`.
  - **Q2.4c** ✅ **Absolute Minkowski for `H_{L,c,Q}`** (EF13 Prop. 9.2 = ES02 Prop. 7.1 +
    Cor. 7.2, formerly Q2.2f): `QuantitativeSubspace/FormMinkowski.lean`.
    `FormSystem.prod_successiveInf_weight_le` / `le_prod_successiveInf_weight`
    (`n^{-n/2} Δ_L Q^{-α} ≤ λ₁(Q) ⋯ λₙ(Q) ≤ √2^{n(n-1)} Δ_L Q^{-α}`, any `Q > 0`, systems on
    `Fin n`), from the general-weight `prod_successiveInf_le` / `le_prod_successiveInf` with
    `FormWeight.absProd` (`∏_v ∏_i A_iv`, `FormExponent.absProd_weight` = `Q ^ c.sum`). ES02
    Prop. 7.1 (`*_of_eq_apply`, weights `a_iv = v(α_iv)`) via `FormSystem.toTwist` into Q2.2e's
    complex-route theorems: `absMulHeight_le_toTwist`, `toTwist_absMulHeight_le` (ES02 (7.8),
    `√n`), `absDet_toTwist` (`Δ_L / A`); off `badPlaces` (weights `1`, forms and inverses
    integral) the twist is the identity. Cor. 7.2 by `exists_eq_apply_weight`: `β_v` with
    `|β_v|_v = N(𝔭_v) > 1`, `k_iv = round(N log A_iv / log|β_v|_v)`, `E = K(β_v^{1/N})`; weights
    compared through `FormSystem.baseChange` / `FormWeight.baseChange` (height and `Δ_L`
    unchanged), `absMulHeight_le_of_le` (monotone), `FormWeight.scale` + Lemma 7.2; factor
    `(1+ε)^{s/[K:ℚ]}`, then `ε → 0`. Q2.4b's infima were made generic (`heightSpace`,
    `heightInf`, `heightFlag` for any height function; `heightInf_le_mul`) to compare `L` over
    `K`, over `E` and the twist.
  - **Q2.4d** ✅ **Lemma 6.3 and scaling into local bounds** (EF13 Lemmas 11.1, 11.2 = ES02
    Lemmas 6.3, 6.2 / 7.3, and Cor. 7.4): `QuantitativeSubspace/FormParallelepiped.lean`.
    `exists_ne_zero_le_of_mul_le`: Minkowski for one scalar with finite places (Layer 4.1's
    approximation domain for the coordinate form on `K¹`), constant
    `unitConst K · ∏_{v ∈ Sfin} N(𝔭_v)`. ES02 Lemma 6.3 without `S`-units:
    `exists_pow_le_of_one_lt` (`g ∈ K`, `|g|_u ≤ A_u ^ k` once `(∏ A_u)^k` beats the constant),
    `le_of_pow_eq_algebraMap` (the `k`-th root, `|γ|_q ≤ C_u ^ {e f}`), `exists_le_of_one_lt`
    (EF13 Lemma 11.1, `E = K(g^{1/k}) ⊆ Ω`). `FormSystem.LocallyLe` (local factors of `y ∈ Eⁿ`
    below budgets `ρa_v`, `ρf_v ^ {e f}`), `mulHeight_le_of_locallyLe`,
    `absMulHeight_le_of_locallyLe`. `exists_locallyLe_smul` (ES02 Lemma 6.2 / 7.3, general
    budgets, finitely many points in one `E`): Lemma 6.3 over `F = K(x)` for the budgets divided
    by the local factors, the root in `E = K(x, γ)` with the tower `F → E` built by hand.
    `exists_smul_le_of_lt`: EF13 Lemma 11.2 ((11.3) `≤ 1/n` at the infinite places, `≤ 1` at the
    finite ones off `v₀`; (11.4) `((n μ_j)^{[K:ℚ]})^{e f}` above `v₀`, any `μ_j > H(g_j)`).
    `paraSet` (`μ ∗ Π(A)`, scaled at a finite `v₀` as in ES02 (6.13), (6.14)), `paraSpace`
    (`U_A(μ)`), `paraInf`; `exists_smul_mem_paraSet` (ES02 Lemma 7.3, `H(x) < μ`),
    `paraSpace_le_infSpace`, `infSpace_le_paraSpace`, `paraInf_eq_successiveInf` (Cor. 7.4).
  - **Q2.4e** ✅ **Davenport's lemma** (EF13 Lemma 11.3 = ES02 Lemmas 9.1, 9.2 with EF13's
    modifications): `QuantitativeSubspace/FormDavenport.lean`. ES02 Lemma 9.1 `exists_approx`
    (`|γ_j + ϑ_j γ₀|_w ≤ 1`, `|γ₀|_w ≤ D` above `v₀`, `γ₀ ≠ 0` by the product formula): Q2.4c's
    `prod_successiveInf_le` over `F = K(ϑ)` for the forms `X_j + ϑ_j X₀`, `X₀` (`approxMatrix`)
    gives `λ₁ < 1`, Q2.4d's `exists_locallyLe_smul` the point; the field over `F` is read over `K`
    by `restrictScalars` (definitionally the same places). The permutation of ES02 (9.24)–(9.33):
    `HasIntegralEchelon` (reduced echelon basis in `Kⁿ`, pivots `π 0, …, π (r-1)`, `v₀`-integral),
    built from the bottom by row reduction with the largest pivot (`exists_sup`, `exists_of_le`,
    `exists_perm_hasIntegralEchelon`) instead of ES02's relations from the top; `apply_eq` is the
    graph relation (9.32). Blocks (9.14): `blockStart`. The construction: `DavenportLe` (bounds
    (11.6), (11.7) over a field `E ⊆ Ω`, `mono`), `exists_davenport_step`
    (`h_q = γ₀ (g_q - z) + Σ_j (γ_j + θ_j γ₀) h_j` gives (9.47) and (9.48) together),
    `exists_davenport_of_graph` (ES02 Lemma 9.2 given the pivots, any forms, weights and
    nondecreasing `λ`), `exists_davenport` (EF13's statement under (8.7), (8.8) at `v₀` and
    (11.1) with `≤`; constants `B = n(1+ε)`, `D = (1+ε) n^n 2^{n(n-1)/2}`,
    `pow_mul_sqrt_two_pow_le`). Helpers: `archFactor_sum_smul_le`, `finFactor_sum_smul_le`,
    `FinitePlace.apply_sum_le`, `FinitePlace.apply_inclusion_le`, `successiveInf_pos`.
    `AbsoluteValue.exists_evertse_of_approx` is not reused: Evertse's lemma adds `R`-combinations
    over one fixed field with per-place permutations, Davenport's rescales `g_q` over growing
    extensions with one permutation at `v₀`.
  - Not in Q2.4: ES02 §§5, 8, 10–21 (reductions, gap principle, Schmidt's auxiliary polynomial,
    Index and Polynomial Theorems, counting), and Thms 2.1, 3.1, 20.1.

### Layer Q3: EF13's Faltings–Wüstholz ingredients

- **Q3.0** ✅ **Literature gate — decided (2026-10-03): EF13 uses no Chow theory.** Read against
  `../lean-code/papers/EvertseFerretti.pdf` (arXiv:1008.2340v1, 93 pp.). The words "Chow",
  "degree of contact" and "Mumford" do not occur, and the bibliography has neither Fe00, EF02 nor
  Fe03. What EF13 takes from FW94 it reproves in a few pages:
  - **The auxiliary polynomial** (§13) replaces Schmidt's. Its tools are Bombieri–Vaaler's Siegel
    lemma with `C_K = |D_K|^{1/2[K:ℚ]}` (Lemma 13.1; landed as
    `ArithmeticHeights/BombieriVaalerRelative.lean`) and Hoeffding's inequality (Lemma 13.2;
    Mathlib's `ProbabilityTheory.measure_sum_ge_le_of_iIndepFun`), combined in the monomial count
    Lemma 13.3 (`#{j ∈ U(r) : Σ_h r_h⁻¹ Σ_l j_hl ĉ_hl ≥ …} ≤ e^{-mε²/2} V`). Lemmas 13.4, 13.5 and
    Prop. 13.6 work in the set-up of §11 (exterior powers, the `Q_h`, `ĉ`), i.e. Q2.4's.
  - **The filtration** (§15) is linear algebra: the weight `w(U) = Σ_v Σ_{i ∈ I_v(U)} c_iv` is
    supermodular (Lemma 15.1), so there is a unique destabilizing subspace of minimal dimension,
    defined over `K` by Galois invariance (Lemma 15.2), and a unique filtration whose points
    `(dim T_i, w(T_i))` are the vertices of the upper convex hull (Lemma 15.4, an adaptation of
    FW94's Harder–Narasimhan filtration). Lemma 15.3 is the special case of the forms
    `X_1, …, X_n, X_1 + ⋯ + X_n`.
  - **The successive infima as `Q → ∞`** (§§16–17, Thm 16.1, Prop. 17.5) and the reduction of
    the general case to the semistable one (§18). These need twisted heights `H_{L,c,Q}`.
  - Other inputs: Ev96 Lemma 26 (Prop. 12.1, Q1) and ES02 Cor. 7.2 (Prop. 9.2, Q2.2e/f).

  So Q3 as first planned (Chow forms, Chow weights, the EF02 bound) is not on the way to Q4. It
  moves to Q5, the only layer that needs it. What remains of Q3 is EF13's own FW material, and
  almost all of it needs ES02's set-up: **Q3 follows Q2.4.** Its milestones (written
  2026-10-03, after Q2.4) follow EF13 §§13, 15–18. Sections 8, 10, 12, 14, the end of §11
  and Prop. 18.5 (which uses Thm 8.1) are Q4.1.
- **Q3.1** ✅ **The abstract filtration** (EF13 Lemmas 15.2 and 15.4, for any supermodular weight
  with finitely many values): `ForMathlib/LinearAlgebra/WeightFiltration.lean`.
  `Submodule.IsSupermodularWeight`, `weightSlope` (`μ(V, U)` of (15.6)).
  - `IsDestabilizing w V T`: the least proper subspace of `V` minimizing `μ(V, ·)`. EF13 takes a
    minimizer of minimal dimension; by (ii) it lies in every minimizer.
  - `exists_isDestabilizing` and `IsDestabilizing.unique` are Lemma 15.2 (i);
    `weightSlope_inf_le` is (ii).
  - `IsWeightFiltration w V r T`: the chain `⊥ = T 0 < ⋯ < T r = V` with strictly decreasing
    slopes, every `P(U)` on or below each line through consecutive `P(T_l)`. Stated this way, the
    `P(T_l)` are the vertices of the upper convex hull without forming it.
  - `exists_isWeightFiltration` and `IsWeightFiltration.unique` are Lemma 15.4.
  - `restrict` drops the top step, and `isDestabilizing` shows that `T (r-1)` is the
    destabilizing subspace of `V`.
  - `IsDestabilizing.map_eq` and `IsWeightFiltration.map_eq`: a lattice automorphism of the
    subspaces that preserves dimension and `w` and fixes `V` fixes `T` and the filtration. This
    is "defined over `K`" once applied to Galois conjugation (Q3.2).
- **Q3.2** ✅ **The weight `w_{L,c}`** (EF13 (2.19)–(2.21), (15.3), (15.4), Lemmas 15.1, 7.3 (ii),
  (iii)): `QuantitativeSubspace/FormSubspaceWeight.lean`.
  - `Submodule.formWeight ℓ c U`: EF13's minimum (2.19) of `Σ_{i ∈ I} c_i` over the `I`
    (`IsFormBasis`) with `(ℓ_i|_U)_{i ∈ I}` a basis of the dual of `U`.
  - `isLeast_formWeight`, `formWeight_eq_sum`, `formWeight_eq_sum_range`: for any ordering `e`
    making `c` increase (`exists_monotone_equiv`, by `Tuple.sort`), the greedy basis
    (`greedy`, `card_greedy`, `linearIndepOn_greedy`) attains the minimum, which is
    (15.4) in both forms (chain `formChain`). Optimality comes from summation by parts
    (`sum_le_sum_of_card_filter_le`).
  - `isSupermodularWeight_formWeight` (Lemma 15.1, local), `finite_range_formWeight`, and
    `formWeight_orderIso` (transport along a lattice isomorphism preserving dimensions and the
    kernels).
  - `NumberField.galoisIso σ` (Galois conjugation of subspaces, `finrank_galoisIso`),
    `FormSystem.matrixForms`, `FormSystem.subspaceWeight L c` (2.20; the finite places with
    `c_v = 0` contribute `0`, `subspaceWeight_eq_sum`).
  - Global results: `isSupermodularWeight_subspaceWeight` (Lemma 15.1),
    `finite_range_subspaceWeight`, `subspaceWeight_galoisIso`.
  - Defined over `K`: `isDefinedOver_of_isDestabilizing` and
    `isDefinedOver_of_isWeightFiltration` (Lemmas 15.2 (i), 15.4, through
    `isDefinedOver_of_forall_algHom`). `exists_isDestabilizing_top` gives `T(L, c)` of (2.21),
    `exists_isWeightFiltration_top` the filtration of `Ωⁿ`.
  - Lemma 7.3 (ii), (iii): `subspaceWeight_comp`, `isDestabilizing_comap_comp` (`compEquiv`).
  - `Submodule.IsDefinedOver.comp_mem`, `Submodule.isDefinedOver_top`. The filtration file
    gained `IsSupermodularWeight.add`, `.sum` and `IsDestabilizing.orderIso`.
- **Q3.2b** ✅ **EF13 Lemma 15.3** (forms among `X_1, …, X_n, X_1 + ⋯ + X_n`: `T` is cut out by
  sums over disjoint blocks), `QuantitativeSubspace/FormBlockSubspace.lean`. Split off from Q3.2:
  it is used only for EF13's remark after (2.21) and §3's applications, not on the way to
  Thm 2.3.
  - `FormSystem.HasCoordSumForms` is (15.7); `exists_blockSums_of_isDestabilizing` is the lemma:
    a finset `𝓘` of nonempty pairwise disjoint blocks with `x ∈ T ↔ ∀ I ∈ 𝓘, Σ_{j ∈ I} x_j = 0`.
    It holds for any destabilizing subspace of `Ωⁿ`, so for `T(L, c)` and every `c`.
  - The proof is EF13's. `sumSpace T` is the space `H` (with `u_0` the coordinate `none` of
    `Option ι → Ω`). For `b ∈ H` with no zero coordinate, `diagEquiv` is `x ↦ (b_j x_j)`; on `T`
    it multiplies each form by a nonzero constant, so `Submodule.formWeight_eq_of_linearEquiv`
    gives the same weight, and the leastness in `IsDestabilizing` gives `φ(T) = T`.
    `mul_mem_sumSpace` follows.
  - EF13 then asserts that `H`, a unital subalgebra of `Ω^{n+1}`, is the set of vectors constant
    on the blocks of a partition. Only one half of this is needed:
    `Subalgebra.exists_indicator_mem` puts the indicator of each class of coordinates into `H`,
    via products of the separating elements `(a - a_j)/(a_i - a_j)`. The converse inclusion
    `T ⊇ {block sums vanish}` comes from a dual form separating `x ∉ T`, regrouped over the
    classes.
  - EF13's count `p = n - dim T` of the blocks is not formalized.
- **Q3.3** ✅ **The monomial count** (EF13 (13.4), (13.5), Lemma 13.3),
  `QuantitativeSubspace/FormMonomialCount.lean`.
  - `Finset.blockCompositions r` is `U(r)`; `card_blockCompositions` is (13.4) (as a product of
    `multichoose`); `card_blockCompositions_le` gives `#U(r) ≤ N^{Σ r_h}` and
    `card_blockCompositions_le_exp` (13.5).
  - `card_filter_blockCompositions_le` is Lemma 13.3. Instead of Hoeffding's inequality for
    independent variables (Lemma 13.2), the Chernoff argument runs on the finite sums: the sum
    over `U(r)` of `exp (t Σ_h Y_h)` factors over the blocks (`Finset.prod_univ_sum`), and each
    factor is bounded by Hoeffding's lemma, restated for finite averages as
    `Finset.sum_exp_mul_le_of_sum_eq_zero` (from Mathlib's
    `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` on the uniform measure). The mean-zero
    property comes from the symmetry of `U(r)` under permutations of the coordinates in a block.
  - Lemma 13.3 holds for `0 ≤ ε`; EF13's `ε ≤ 1` is not needed.
- **Q3.4** ✅ **The auxiliary polynomial** (EF13 Lemmas 13.1, 13.4, 13.5, Prop. 13.6).
  - Lemma 13.1 is `ArithmeticHeights/BombieriVaalerRelative.lean`.
  - Lemmas 13.5 and 13.6 need the exterior-power set-up of §11 (Q3.4a); 13.4–13.6 themselves
    are Q3.4b.
- **Q3.4a** ✅ **The exterior-power set-up** (EF13 §11, (6.10), (11.10)–(11.21), Lemmas 11.4,
  11.5): `QuantitativeSubspace/FormExteriorPower.lean`.
  - `FormSystem.exteriorPower L p` (`L̂`, the rows of `Matrix.compound`),
    `FormWeight.exteriorPower` (`â_I = ∏_{i ∈ I} a_i`), `FormExponent.exteriorPower`
    (`ĉ_I = Σ_{i ∈ I} c_i`) and `weight_exteriorPower`. The points `ĥ_J` are `plucker`.
  - Off `v₀`: `archFactor_exteriorPower_plucker_le` and `finFactor_exteriorPower_plucker_le`
    turn Davenport's (11.6) into (11.14), (11.17). This uses Hadamard (`Matrix.abv_det_le_of_col`)
    and the ultrametric bound (`FinitePlace.apply_det_le_of_col`).
  - Above `v₀`: `FinitePlace.apply_plucker_le_topBound` turns (11.7) into (11.17).
    - `topSet k` is `I_N = {k, …, n-1}` (0-based `k`). `topBound λ π I` is EF13's
      `Q^{ĉ_{I,v₀}} / 3^{n³}` of (11.15): `ν_{π̂⁻¹(I)}`, with `ν_{I_N}` replaced by
      `ν_{I_N} λ_{k-1}/λ_k`.
    - It rests on `prod_le_prod_topSet_mul` (`ν_J ≤ ν_{I_N} λ_{k-1}/λ_k` for `J ≠ I_N`) and
      `min_le_topBound`.
  - (11.21): `prod_topBound` and `sum_logb_topBound` give the identity
    `∏_I topBound = (λ_0 ⋯ λ_{n-1})^{C(n-1, n-k-1)} λ_{k-1}/λ_k`.
  - Lemma 11.4 (11.18)–(11.20): `sum_exteriorPower_arch/_fin` (via
    `Finset.sum_powersetCard_sum`), `abs_exteriorPower_arch_le/_fin_le`,
    `sum_iSup_abs_exteriorPower_le`.
  - Lemma 11.5:
    - Local bounds: `apply_inv_exteriorPower_arch_le` / `_fin_le`, using
      `(M^{∧p})⁻¹ = (M⁻¹)^{∧p}` (`Matrix.inv_compound`) and `apply_inv_le`. The latter needs the
      coordinate forms in the system (`one_mem_forms`, from (8.8)).
    - Product: `prod_invBound` gives `p!^{[K:ℚ]} (H_L/Δ_L)^p`, and `prod_invBound_rpow_le` gives
      `p! H_L^{p C(r, n)}` absolutely, through (7.4).
    - This is a different constant from EF13's `H_L^{R^n}`, which comes from Jacobi's identity.
      It is also not what §13 uses: Q3.4b proves EF13's joint form separately.
  - Moved to Q4.1:
    - the inequalities (11.21) `Σ ĉ_{i,v₀} ≤ -δ/n` and (11.22) `|ĉ_{i,v₀}| ≤ n`, which need
      Lemmas 9.3 and 9.4 and `C_2` of (8.10);
    - Lemma 11.6 (`H_2(T̂) ≥ Q^{δ/3R^n}`), which needs Lemma 10.3 and Lemma 6.1.
- **Q3.4b** ✅ **Lemmas 13.4, 13.5, Prop. 13.6** (the auxiliary polynomial itself):
  `QuantitativeSubspace/FormInverseHeight.lean`,
  `QuantitativeSubspace/FormAuxiliaryPolynomial.lean`.
  The polynomial machinery is DA's (Layer 5.2): `MvPolynomial.blockSubst`, `multiMons`, the chain
  rule `coeff_blockSubst_hasseDeriv_eq_zero` and the multihomogeneous Siegel lemma.
  - **Joint Lemma 11.5** (`FormInverseHeight`). EF13's Lemma 11.5 is a bound on the *joint*
    height of all the `(L̂^{(v)})⁻¹`, which Q3.4a's per-place `prod_invBound` is not. It is
    `FormSystem.invTuple` (`1` and the entries of all `((L^{(v)})^{∧p})⁻¹`, over
    `matSet`, the distinct `L^{(v)}`), with `le_iSup_invTuple` (it dominates every inverse at every
    absolute value) and `mulHeight_invTuple_le`: `H(invTuple) ≤ p!^{[K:ℚ]} H_L^{2ps}`,
    `s = #matSet`.
    The inverse determinants are cleared with `δ = ∏_{B ∈ matSet} det B`, and the computation is
    DA's `Height.mulHeight_le_pow_mul_mul_pow`. The local bounds hold at any absolute value
    (`apply_inv_compound_le`, and `_of_isNonarchimedean` with the new ultrametric Hadamard bound
    `Matrix.abv_det_le_of_col_of_isNonarchimedean`).
  - **Lemma 13.4.** `d^{(v)}_{I,J}(a_P)` is `(blockSubst (L̂^{(v)})⁻¹ (∂_I P)).coeff J`; (13.10) is
    `blockSubst_blockSubst`. The bounds (13.11) are `iSup_coeff_blockSubst_hasseDeriv_le` and
    `_of_isNonarchimedean`, against `invTuple`.
  - **Lemma 13.3 on `multiMons`**: `MvPolynomial.blockAvg` (EF13's `Σ_h r_h⁻¹ Σ_l ν_{hl} f_{hl}`),
    `multiMons_eq_map`, `card_filter_multiMons_le`.
  - **Lemma 13.5**: `FormSystem.exists_auxiliaryPolynomial`, through
    `MvPolynomial.exists_ne_zero_coeff_blockSubst_eq_zero_of_card` (Siegel for families of
    conditions). Places are `InfinitePlace K ⊕ FinitePlace K` (`FormSystem.mat`,
    `FormExponent.vec`).
  - **Prop. 13.6**:
    - `exists_representatives` (the `S₀` of (13.30)–(13.32));
    - `exists_auxiliaryPolynomial_hasseDeriv` ((i)–(iii); (i) at every place);
    - `prod_iSup_coeff_blockSubst_hasseDeriv_le` ((iv), (13.29)).
  - Differences from EF13:
    - Heights are relative to `K` with sup norms (`Height.mulHeight`), not absolute `H₂`.
      (13.18) reads `h(P) ≤ ½ log |D_K| + ([K:ℚ](N/2 + log N + log p!) + 2ps log H_L) Σ r`.
    - (13.22) is replaced by `2 (#matSet (n/ε + 2)^n + 1) ≤ e^{mε²/2}`. EF13's derivation of
      (13.13) from (13.22) slips twice: `c_{iv}/γ_v ∈ [-(n-1), 1]`, not `[-1, 1]`; and
      `2((3R/ε)^n + 1) ≤ (4R/ε)^n` fails at `n = 2`.
    - The `v₀`-exponents `ĉ_{s,v₀}(Q_h)` are an input `e` with (11.21), (11.22) as hypotheses,
      since these need Q4.1.
- **Q3.5** ✅ **The successive infima as `Q → ∞`** (EF13 §16, Thm 16.1), conditional on the
  qualitative EF13 Thm 8.1 (`NumberField.SemistableGap K Ω`, to be discharged by Q4.1). Four files:
  - `QuantitativeSubspace/FormWeightExchange.lean`: matroid facts about the local weight
    `Submodule.formWeight`. They are `formWeight_comp_embedding` (an exchange argument: only forms
    `ℓ_{g j}` matter when every `ℓ_i` is a combination of them with `c_{g j} ≤ c_i`),
    `formWeight_eq_of_mem_span` (triangular changes of the forms), `formWeight_map`,
    `formWeight_comap` (`w(π⁻¹ U) = Σ_{i ∈ I} c_i + w_h(U)`, i.e. Lemma 16.2 (ii) locally),
    `formWeight_bot/top`, and `formWeight_sub_const` and `formWeight_div_const` (Lemma 7.2 (ii)).
  - `QuantitativeSubspace/FormInducedSystem.lean`: the systems `(L', c')`, `(L'', c'')` of
    (16.4)–(16.6) and Lemmas 16.2, 16.3.
    - A `NumberField.Splitting K n k m` is an invertible `n × (k + m)` matrix over `K`, giving
      `φ'` (`inclLin`) and `φ''` (`projLin`). `Splitting.exists_range_inclLin` gives one with
      `φ'(Ω^k) = T` for any `T` defined over `K`.
    - `I_v(T)` is `Matrix.selectRows`: `k` rows of `L^{(v)} φ'` forming an invertible matrix with
      the least `Σ c`. Its exchange property `Matrix.le_of_mul_inv_ne_zero` (by Cramer's rule,
      `det_updateRow_sum`) replaces EF13's increasing order (15.1): `α_is ≠ 0 → c_{σ s} ≤ c_i`.
    - `L''` is the Schur complement (`Splitting.quotMat`); its determinant is nonzero by
      `det_fromBlocks₁₁`.
    - `restrictSystem`/`restrictExp` and `quotSystem`/`quotExp` are the systems; their finite
      ranges come from `finite_range_fin_exp` (the pairs `(L^{(v)}, c_v)` are finitely many).
    - Lemma 16.2: `subspaceWeight_restrictSystem` and `subspaceWeight_quotSystem`.
    - Lemma 16.3 comes from one comparison for systems with `L₂^{(v)} Φ₂ = M_v L₁^{(v)} Φ₁`
      (`absMulHeight_le_of_mul_eq`, `exists_absMulHeight_weight_le`). The instances are
      `exists_absMulHeight_restrictSystem_le`, `exists_absMulHeight_le_restrictSystem` and
      `exists_absMulHeight_quotSystem_le`.
  - `QuantitativeSubspace/FormSemistable.lean`: Lemma 16.4 and the reductions it uses.
    - `FinitePlace.infinite` (a number field has infinitely many finite places), proved from the
      product formula and Bézout. It is needed for the `v₀` of (8.8).
    - `FormExponent.center` (8.3) and `FormExponent.divConst` (8.4), with
      `subspaceWeight_top/center/divConst` and `absMulHeight_center` (Lemma 7.2).
    - `SemistableGap K Ω`: Thm 8.1's conclusion under (8.3), (8.4), (8.8), (8.9): eventually
      `H_{L,c,Q}(x) > Q^{-δ}` for all `x ≠ 0` and `0 < δ ≤ 1`. The interval structure of (8.11)
      is not needed here.
    - `exists_lt_absMulHeight_of_semistable`: Lemma 16.4, the lower bound. For `n = 1` it comes
      from Lemma 7.1 directly. Otherwise it normalizes (8.3), (8.4) and (8.8) through
      `L ∘ (L^{(v₀)})⁻¹` and applies the hypothesis.
  - `QuantitativeSubspace/FormInfimaLimit.lean`: Thm 16.1.
    - `IsWeightFiltration.comap_of_injective` carries the filtration of `T_{r-1}` to `Ω^k`.
    - Generic comparisons of successive infima and of `T(λ)` through `φ'`:
      `heightInf_le_mul_of_comp`, `heightInf_le_mul_of_lt`, `heightSpace_le_map`,
      `map_heightSpace_le`, and `le_heightInf_of_forall_notMem` (16.14).
    - `qHeight` is `H_{L,c,max(Q,1)}`. `prod_heightInf_le` and `exists_le_prod_heightInf` are
      Prop. 9.2 for it.
    - `InfimaBounds` and `eventually_infimaBounds`: the induction, on `n`. It bundles the upper
      bounds, the lower bounds and the stability `T(λ) = T_{l+1}` for
      `Q^{-μ_l+δ} ≤ λ ≤ Q^{-μ_{l+1}-δ}`, which replaces (16.16).
    - `eventually_successiveInf`: (16.2) and (16.3) for `successiveInf` and `infFlag`.
  - Differences from EF13:
    - `I_v(T)` is a least-weight basis, not the greedy one after reordering (15.1); see above.
    - The induction runs on `n`, not `r`. The base case `r = 1` is the case `T_{r-1} = 0` of the
      step (`k = 0`, so `L''` is `L` reindexed), with no separate appeal to Lemma 16.4.
    - The last infimum is bounded through Prop. 9.2's lower bound for `L'` on the first `d_{r-1}`
      infima, instead of the bounds (16.17) for each of them.
- **Q3.6** ✅ **A height bound for the filtration** (EF13 §17, Lemmas 17.1–17.4, Prop. 17.5):
  `H₂(T_l) ≤ H₂^{4ⁿ}` for `0 < l < r`, `H₂` the largest height of a form of `L`, through Thm 16.1
  applied to the exterior powers. Conditional on `SemistableGap K Ω`, like Q3.5. Three files:
  - `QuantitativeSubspace/FormHyperplaneHeight.lean`: Lemma 17.4 and its algebra.
    - `Submodule.extendPi`: the span `V ⊗ Ω ⊆ Ωⁿ` of `V ⊆ Kⁿ`; it is injective, monotone,
      preserves `finrank`, `⊔` and `⊥`, and every subspace defined over `K` is one
      (`exists_extendPi_eq`).
    - The weight of a hyperplane `ker φ` is read from the coordinates of `φ` in the basis of
      forms (`formWeight_ker_le`, `le_formWeight_ker`).
    - `arakelovFormHeight` (`H₂`), `kerForms` (common kernels of forms, height `≤ H₂^{N-1}`) and
      `arakelovMulHeight_finset_sup_le` (Struppeck–Vaaler for a finite join).
    - `arakelovMulHeight_le_of_isDestabilizing`: Lemma 17.4, `H₂(T) ≤ H₂^{(N-1)²}` for a
      destabilizing hyperplane `T`. `T` is the sum of the common kernels `U_v` of the forms with
      `c_i ≤ max{c_j : φ_j ≠ 0}`; a functional vanishing on that sum but not on `T` would give a
      hyperplane of larger weight (`dualExtend`).
  - `QuantitativeSubspace/FormWedgeHeight.lean`: Lemmas 17.1 and 6.1 and (17.10).
    - `FormSystem.reindex` and `FormExponent.reindex` move the exterior power, indexed by
      `Set.powersetCard (Fin n) p`, to `Fin N`; heights and weights are unchanged.
    - `absMulHeight_exteriorPower_plucker_le`: Lemma 17.1 with `p!` for EF13's `p^{p/2}`
      (Leibniz instead of Hadamard at the infinite places).
    - `arakelovFormHeight_exteriorPower_le`: (17.10), `H₂(L̂) ≤ H₂^p`.
    - `FormExponent.sum_exteriorPower`: `Σĉ = C(n-1, p-1) Σc`.
    - `exists_extendPi_span_compound_eq`: Lemma 6.1 for the wedges, `H₂(T̂) = H₂(T_l)`.
    - `prod_heightInf_le_prod` (the first `#s` infima are at most the heights of any `#s`
      independent points), `exists_linearIndependent_le_mul` (points with `H(g_j) ≤ C λ_j`) and
      `Nat.mul_choose_sq_le` (`p C(n,p)² ≤ 4ⁿ`).
  - `QuantitativeSubspace/FormFiltrationHeight.lean`: Prop. 17.5.
    - `qHeight_compound_le`: Lemma 17.1 for the reindexed exterior power.
    - `eventually_isDestabilizing`: for large `Q`, a subspace of dimension `N - 1` spanned by
      points of height `≤ β` with `β Q^ε ≤ λ_N(Q)` is the destabilizing subspace (Thm 16.1).
    - `arakelovMulHeight_le_of_isWeightFiltration`: Prop. 17.5.
  - Differences from EF13:
    - Heights are relative to `K` (EF13's absolute bound raised to `[K:ℚ]`).
    - The weight of a hyperplane comes from dual coordinates, not from ordering the forms.
    - `λ̂_N ≥ c ν_top` comes from Prop. 9.2 for `L` and `L̂` and the sorting bound
      `prod_heightInf_le_prod`, not from Lemmas 17.2 and 17.3 as stated.
    - The exponent `4ⁿ` (EF13 Prop. 17.5) uses `p (N-1)² ≤ p C(n,p)² ≤ 4ⁿ`; the earlier plan's
      `4n` was a typo.
- **Q3.7** ✅ **The height estimates of §18** (EF13 Lemmas 18.1–18.4) for the reduction to the
  semistable case. Prop. 18.5 and the proof of Thm 2.3 are Q4.1. Conditional on
  `SemistableGap K Ω` through Prop. 17.5, like Q3.5 and Q3.6. `R` is the number of forms of `L`.
  Two files:
  - `QuantitativeSubspace/FormMinorRatio.lean`: Lemmas 10.1, 10.2 and 18.1.
    - `localRatio`, `mulSupProd`, `mulRatioProd` (`max/min` of a finite set of numbers, and
      `∏_v M_v`, `∏_v M_v / m_v`); `mulRatioProd_le`: `∏_v M_v / m_v ≤ (∏_v M_v)^{#θ}` by the
      product formula (the idea of (10.2)).
    - `HasUnitForms` (`L` contains `X_1, …, X_n`), `minorSet` (the nonzero `θ` of (18.1) for the
      columns of `G`), `plucker_mem_detSet` and `apply_mem_detSet` (Lemma 10.1, by a block
      determinant), `mulSupProd_minorSet_le` (Lemma 10.2, (10.1), by Cauchy–Binet),
      `arakelovFormHeight_le` (`H₂(L_i) ≤ √n H_L`).
    - Change of coordinates: `exists_of_mem_forms_comp`, `mulFormHeight_comp_le`,
      `minorSet_comp` (the `θ` are unchanged), `isWeightFiltration_comp` (via the new
      `Submodule.IsWeightFiltration.orderIso` in `ForMathlib/LinearAlgebra/WeightFiltration.lean`),
      `extendPi_span_col_inv_mul`.
    - `mulRatioProd_minorSet_le` / `mulRatioProd_minorSet_rpow_le`: Lemma 18.1,
      `∏_v M_v / m_v ≤ (2 H_L)^{(4R)ⁿ}`; the exponent count is `minorRatio_pow_le`.
  - `QuantitativeSubspace/FormQuotientHeight.lean`: Lemmas 18.2–18.4 for Q3.5's
    `quotSystem`/`quotExp`.
    - `cramerCoeff`, `det_update_eq` (Cramer's rule) and `apply_cramerCoeff_le`;
      `apply_quotCoeff_le` is (18.7), `‖α_ijv‖_v ≤ M_v / m_v`.
    - `absMulHeight_quotSystem_le` and `absMulHeight_quotSystem_le_of_isWeightFiltration`: (18.5)
      with the explicit constant of Lemma 16.3 (ii), `n (2 H_L)^{(4R)ⁿ}`.
    - `quotRow`, `card_forms_quotSystem_le`: (18.15), at most `R^{k+1}` forms.
    - `quotNormExp` (the `d` of (18.12)), `sum_iSup_quotNormExp_le` ((18.14):
      `Σ_v max_i d_iv ≤ Σ_v max_i c_iv - Σ_v Σ_i c_iv / n`) and
      `subspaceWeight_quotNormExp_nonpos` ((18.16) for proper `U`, when `ker φ''` is the
      destabilizing subspace).
    - `det_mul_det_eq` (a block determinant), `det_sum_smul` (multilinear expansion),
      `exists_detSet_quotSystem`, `mulFormHeight_quotSystem_le` and `absFormHeight_quotSystem_le`:
      Lemma 18.4, `H_{L''} ≤ (2 H_L)^{(8R)ⁿ}`.
  - Differences from EF13:
    - Lemmas 18.1 and 18.4 hold for any member `T_l`, `0 < l < r`, of the filtration, not only
      for `T(L, c) = T_{r-1}`.
    - No normalization (18.8), (18.9) and no full system `L̃`: the splitting of Q3.5 is arbitrary.
      Lemma 18.4 comes from the block determinant identity and the product formula for
      `det P' / det(B₀ φ')`, and (18.5) directly from the comparison of Q3.5. (18.6) is not
      needed.
    - (18.15) gives `R^{k+1} ≤ Rⁿ` forms (EF13 `n Rⁿ`): a form of `L''` is fixed by one form of
      `L` and a `k`-tuple of forms of `L`. EF13 count through the ordered `n`-tuples of forms,
      which does not carry over to the least-weight `I_v(T)` of Q3.5 (it depends on the values
      of `c_v`, not only on their order).
    - (18.14) is stated with `- α / n`, `α = Σ_v Σ_i c_iv`, so it gives `≤ 1` under (2.8) and
      (2.9). (8.8) for `(L'', d)` is left to Q4.1.

### Layer Q4: the summit (Evertse–Ferretti 2013)

- **Q4.1** ✅ EF13's parametric theorem, which combines Q2.4's framework with Q3's auxiliary
  polynomial and filtration. Its Thm 8.1 must discharge `NumberField.SemistableGap K Ω`, the
  hypothesis of Q3.5's Thm 16.1 (so EF13 §§16–18 stay free of circularity: §14 does not use §16).
  Milestones (written 2026-10-04) follow EF13 §§9–12, 14, 18. Throughout, `Q` satisfies (9.3),
  (9.4) (`Q ≥ C₂`, `λ₁(Q) ≤ Q^{-δ}`) and `(L, c)` satisfies (8.1)–(8.9).
  - **Q4.1a** ✅ **The gap and the height of `T_k(Q)`** (EF13 Lemmas 9.3, 9.4, 10.3):
    `QuantitativeSubspace/FormInfimaGap.lean`.
    - `FormSystem.IsNormalSemistable L c Ω` bundles (8.3), (8.4), (8.8), (8.9); `sum_eq_zero`,
      `hasUnitForms` (from `v₀`).
    - `rpow_le_successiveInf_one` (`λ_1 ≥ n⁻¹ H_L^{-C(r,n)} Q^{-1}`, Lemma 7.1) and Lemma 9.3
      (`rpow_le_prod_successiveInf`, `prod_successiveInf_le_rpow`) under the explicit size
      conditions `n H_L^{C(r,n)} ≤ Q^{1/3n}` and `2^{n(n-1)/2} Δ_L ≤ Q^{1/6}`.
    - Lemma 9.4: `exists_successiveInf_le`, from `λ_1 ≤ Q^{-δ}` and `n^{n/2} ≤ Δ_L Q^δ`.
    - Lemma 10.3 by a route that stays over `K`. `T = T_k(Q)` is defined over `K` (Lemma 9.1);
      Q3.5's splitting with `φ'(Ω^k) = T` gives the induced system `(L', c')` with
      `H_{L',c',Q}(y) ≤ n H_{L,c,Q}(φ' y)` (`absMulHeight_restrictSystem_le`), so its infima are at
      most `n λ_1, …, n λ_k` (points off `T` have height `≥ λ_{k+1}`), and `Σ c' = w(T) ≤ 0`
      (`sum_restrictExp`). Prop. 9.2 for `L'` bounds `Δ_{L'} ≤ k^{k/2} nᵏ λ_1 ⋯ λ_k`, and
      `prod_range_pow_le` gives `(λ_1 ⋯ λ_k)ⁿ ≤ Q^{-δ} (2^{n(n-1)/2} H_L)ⁿ` from the gap. The
      determinants of `L'` are minors `θ` of Q3.7 (`det_restrictMat_mem_minorSet`), so EF13 (10.2)
      (`mulSupProd_div_mulRatioProd_le`, `one_le_mulDet_restrictSystem_mul`) and Lemma 10.2 bound
      `Δ_{L'}` below. EF13's determinants `θ_w` over a field containing near-minimal points are not
      needed.
    - `rpow_le_mul_arakelovMulHeight` is the resulting inequality,
      `Q^δ ≤ (k^{k/2} nᵏ 2^{n(n-1)/2} H_L)ⁿ (C(n,k) H_L H₂(V)^{1/[K:ℚ]})^{n Rᵏ}`, and
      `rpow_le_arakelovMulHeight_infFlag` is Lemma 10.3, `H₂(V)^{1/[K:ℚ]} ≥ Q^{δ/3Rⁿ}` for
      `V ⊗ Ω = T_k(Q)`, once `(2^{3n²} H_L)^{3nRⁿ} ≤ Q^δ`. The size conditions on `Q` are
      explicit hypotheses; Q4.1d derives them from `Q ≥ C₂`.
    - The exponent of `H₂(V)` uses `#θ ≤ Rᵏ` (`card_minorSet_le`), not EF13's `C(R, k)`.
    - Lemma 11.6 (Lemma 6.1 applied to `T_k(Q)`) moved to Q4.1b, where the wedges are built.
  - **Q4.1b** ✅ **The points `ĥ_j(Q)` and the exponents `ĉ_{i,v₀}(Q)`** (EF13 (11.8)–(11.17),
    Lemma 11.4 (11.21), (11.22), Lemma 11.6): `QuantitativeSubspace/FormWedgePoints.lean`.
    - `exists_wedgePoints`: from Lemma 9.4's gap at `0 < k < n` (`k : Fin n`, 0-based as in
      Q3.4a), Davenport's lemma (Q2.4e) with an `ε` from `exists_eps_davenport` (EF13 (11.1), by
      continuity; `mul_two_pow_sq_lt_three_pow_sq` gives the room `n 2^{n²} < 3^{n²}`), the
      wedges `x_J = ĥ_J` over the field `E` of the `h_j`, and the exponents
      `e_I = log_Q(3^{n³} topBound λ π I)` (11.15). Its conclusions: `|e_I| ≤ n`,
      `Σ_I e_I ≤ -δ/n`, local factors of `x_J` (`J ≠ I_N`) at most `1` for `(L̂, ĉ)` off `v₀`,
      `‖x_J(I)‖_w ≤ Q^{e_I}` above `v₀` (11.17), the `x_J` independent, and their span the
      extension of `W ⊆ K^N` of dimension `N - 1` with `H₂(W)^{1/[K:ℚ]} ≥ Q^{δ/3Rⁿ}`
      (Lemma 11.6 = Lemma 6.1 + Lemma 10.3).
    - (11.22): `abs_logb_topBound_le`, via `topBound_eq_prod` (`topBound` is a product of `n - k`
      distinct infima) and Lemma 9.3, with `3^{n³} ≤ Q^{1/2}`. (11.21): `sum_logb_topBound_le`,
      from Q3.4a's `sum_logb_topBound`, (9.2) and the gap, with
      `(3^{n³} 2^{n(n-1)/2} H_L)^{2ⁿ} ≤ Q^{δ/n(n-1)}`. EF13's proof of (11.21) drops the factor
      `Δ_L^{N'}` of (9.2); here it is kept, bounded by `H_L`.
    - The size conditions on `Q` are hypotheses, as in Q4.1a.
  - **Q4.1c** ✅ **The non-vanishing result** (EF13 Prop. 12.1 = Ev96 Lemma 26):
    `QuantitativeSubspace/FormNonVanishing.lean`.
    - `MvPolynomial.exists_eval_hasseDeriv_ne_zero_of_logHeight`: `P ≠ 0` over a number field `K`,
      multihomogeneous of degree `r` in `m` blocks of `n + 1` variables, `r_h/r_{h+1} > m/ε`,
      forms `M_h` over `K` with `n max(1, m/ε)^m (10 m² [K:ℚ] Σr + m h(P)) < r_h h(M_h)`, and `y_h`
      spanning `M_h = 0` over any field `E ⊇ K` of characteristic zero. Conclusion: integers
      `|z_{hl}| ≤ n/ε + 1` and `I` with `Σ_h |I_h|/r_h ≤ 2mε` and
      `P_I((Σ_l z_{hl} y_{hl})_h) ≠ 0`. The ratio condition `m/ε` is weaker than EF13's `2m²/ε`.
    - Proof: Evertse's Lemma 24 (Q1.5) over `K`, with Rémond's heights `resultantHeight`
      (`botBound 1 ≤ 7`) and `θ = mε`; `formIndex_map` (via `substFormInv_map`) moves the index
      along the forms to `E`; then DA 5.5–5.6 with `η = 2ε`.
    - `Submodule.exists_normal_logHeight_le`: a hyperplane `W ⊆ Kⁿ` is `M ⬝ x = 0` with
      `h₂(W) ≤ [K:ℚ]/2 log n + h(M)` (duality theorem, `arakelovLogHeight_le_logHeight`).
    - `K : Type` (universe `0`): Rémond's heights are built for fields in `Type`.
  - **Q4.1d** ✅ **Theorem 8.1** (EF13 §14): `QuantitativeSubspace/FormEvalBound.lean`,
    `FormIntervalTheorem.lean`, `FormSemistableGap.lean`.
    - `FormSystem.one_le_evalBound` (FormEvalBound): (14.10)–(14.17) and the product formula over
      a number field `F` holding the points. Per place, `P_I(x)` is read in the coordinates
      `L̂^{(v)}` (`eval_eq_eval_blockSubst`, `map_blockSubst`), and only the monomials allowed by
      Prop. 13.6 (i), (ii) count (`prod_apply_pow_le`, exponent count `sum_log_mul_le`). The output
      is `1 ≤ (∏_v A_v)(2^{NΣr} G^{Σr})^{[K:ℚ]} e^{[K:ℚ]Λm(10nε - δ/nN)}`.
    - `FormSystem.false_of_chain` (FormIntervalTheorem): `m` values `Q_h` with the same gap
      index `k`, `log Q_{h+1} ≥ (4m/ε) log Q_h`, and two numerical thresholds `hΘ₁` (Prop. 12.1's
      height condition) and `hΘ₂` (the product formula) give a contradiction.
      - The wedge points of the `Q_h` (`exists_wedgePoints`, which now takes `k` and its gap as
        input) live in fields `E_h`, which are moved into the compositum
        `F = ⨆ E_h` (`apply_mulVec_le_arch_of_le`, `apply_mulVec_le_fin_of_le`).
      - The degrees `r_h = ⌈Λ/log Q_h⌉` are (14.8) (`exists_blockDegrees`). Prop. 12.1 is applied
        over `Ω` with the normal vectors of the `W_h` (`mem_extendPi_of_sum_eq_zero`).
      - (14.9) is replaced by `Λ ≥ log|D_K| log Q_0`, which absorbs `log|D_K|` of Prop. 13.6 (iii).
    - `FormSystem.exists_intervals` (FormSemistableGap) is **Theorem 8.1**. The `Q ≥ C₂` with
      `λ_1(Q) ≤ Q^{-δ}` lie in `(n - 1)(m - 1)` intervals `[a, a^{2ω}]`.
      - The parameters are `ε = δ/(40n²2ⁿ)`, `m` from Prop. 13.6's count, `ω = 4m/ε`, and
        `log C₂ = gapThreshold n R δ (log H_L)`, which is linear in `log H_L`.
      - The proof covers the exceptional set greedily (`Real.exists_cover_of_not_chain`), and finds
        a monochromatic sub-chain for the colouring by Lemma 9.4's `k` (`Real.exists_subchain`).
      - The size conditions of §§9–13 follow from `log Q ≥ log C₂` term by term.
    - `NumberField.semistableGap : SemistableGap K Ω` for `K : Type` and `Ω` algebraically closed.
      Thm 16.1 (Q3.5), Prop. 17.5 (Q3.6) and Lemmas 18.1–18.4 (Q3.7) all assume `IsAlgClosed Ω`,
      so passing `semistableGap K Ω` makes them unconditional for `K : Type`.
    - The constants are not EF13's: EF13 have `ε = δ/(11n²2^{n-1})`, `m₂` intervals
      `[Q_h, Q_h^{ω₂})` with `ω₂ = m₂^{5/2}`, and `C₂ = (2H_L)^{m₂^{2m₂}}`. The exponent `2ω` comes
      from the covering, since the infimum of the exceptional set need not be exceptional.
  - **Q4.1e** ✅ **Theorem 2.3** (EF13 §18 end): `QuantitativeSubspace/FormIntervalResult.lean`.
    - Lemmas 18.1 and 18.4 for the destabilizing subspace `T = T(L, c)`, including `T = 0`
      (`mulRatioProd_minorSet_rpow_le_of_isDestabilizing`: the filtration member `T_{r-1}` is `T`
      by uniqueness, and for `k = 0` the only minor is `1`).
    - **Prop. 18.5** (`absMulHeight_quotNormExp_le_rpow`): `H_{L'',d,Q'}(φ'' x) ≤ Q'^{-δ/2n}`,
      `Q' = Q^{n/(n-k)}`, from `H_{L'',d,Q'} = Q^{μ(T)} H_{L'',c'',Q}` (`weight_divConst`,
      `absMulHeight_center`), `μ(T) ≤ μ(0) = 0` and (18.5).
    - (8.8) for `(L'', d)` by a change of coordinates (`isNormalSemistable_comp`, EF13 Lemma 7.3):
      composing with `(L''^{(v₀)})⁻¹` at a finite place with `c_{v₀} = 0`. So Theorem 8.1 holds
      without (8.8) (`exists_intervals_of_fin_eq_zero`).
    - `n - k = 1` (`false_of_card_eq_one`): `d = 0`, and Lemma 7.1 (`le_absMulHeight_weight`)
      bounds the heights below by `H_{L''}^{-R^n}`.
    - EF13 (18.23) is `exists_intervals_of_isDestabilizing`, with Theorem 8.1 for `n - k`
      variables, `Rⁿ` forms and `δ / 2n`, above `log C = quotThreshold n R δ (log H_L)`.
    - **Theorem 2.3** is `exists_intervals_cover`. At most `intervalCount n R δ` reals
      `b ≥ C₀ = max(H_L^{1/R}, n^{1/δ})` such that every `Q ≥ C₀` with (2.24) lies in some
      `[b, b^{ω₀})`, `ω₀ = δ⁻¹ log 3R`. `Real.exists_cut` cuts `[a, a^θ]` into
      `⌊log θ / log ω₀⌋ + 1` pieces. `[C₀, C)` is cut with `log C / log C₀ ≤ intervalBound n R δ`,
      from `log C₀ ≥ log 2 / δ`, `log C₀ ≥ log H_L / R` and `log C` affine in `log H_L`.
    - Differences from EF13:
      - The hypothesis is `Σ_v Σ_i c_iv = 0`, weaker than (2.8) at every place.
      - Prop. 18.5 loses `δ/2n` (EF13: `99δ/100n`).
      - The count is explicit but is not EF13's `m₀ = ⌊10⁵ 2^{2n} n^{10} δ^{-2} log(3δ⁻¹R)⌋`;
        it takes the largest over the possible `n - k` of the cut counts (a sum until
        2026-10-04). A closed-form bound is Q4.2d.
- **Q4.2** ✅ EF13's interval result for approximation domains (EF13 §5: Lemma 5.1 and Thm 3.3;
  Evertse 2010, Thm 3.1: `m = ⌊10^8 · 2^{2n} · n^{14} · δ^{-2} · log(3δ^{-1}RD)⌋` intervals with
  `ω = 3nδ^{-1} log 3RD`). Theorem 2.3 in the shape that Q0.3's assembly
  (`exists_finset_submodule_of_forall_interval`) takes, i.e. a twin of Layer 6.1's
  `exists_forall_mem_interval_approxDomain`: forms `L` on `Kⁱ` independent at the infinite places
  and at `Sfin`, exponents of weight `≤ -ε` and spread `≤ 2A` (absolute weight `≤ A` until
  2026-10-04), at most `s` distinct forms.
  Milestones (written 2026-10-04):
  - **Q4.2a** ✅ **The system of an approximation domain** (EF13 (5.1)–(5.5), Lemma 5.1):
    `QuantitativeSubspace/FormDomainSystem.lean`.
    - `domainSystem`: a `FormSystem K (Fin n)` through `ι ≃ Fin n` (`domainMatrix`), the forms of
      `L` at the infinite places and at `Sfin`, the coordinates elsewhere.
    - `domainExponent`: `(c_iv - (1/n) Σ_j c_jv) mult v / κ` at `S`, `0` elsewhere; (2.8) in sum
      (`domainExponent_sum`) and EF13 (5.5): `Σ_v max_i ≤ M/κ` with the spread
      `M = approxSupWeight - approxWeight / n = Σ_v mult v · max_i (c_iv - (1/n) Σ_j c_jv)`
      (`domainExponent_sup_le_spread`; `approxSupWeight` in DA's `SystemDomain.lean`), and the
      cruder `≤ 2A/κ`, `A` the absolute weight (`domainExponent_sup_le`).
    - Lemma 5.1 (`absMulHeight_domainSystem_le`): a nonzero point of the domain at level `Q` has
      `H_{L,c',Q'}(x) ≤ Q^{W / (n [K : ℚ])}`, `Q' = Q^{κ / [K : ℚ]}`, `W` the weight. EF13 take
      `Q = H(x)^{1 + ε/n}` for their system (3.7); the domain has no `‖x‖_v`, and integrality off
      `S` bounds the coordinates there, so this holds at every level.
    - `FinitePlace.localDegree_self`: local degree `1` over the own field.
  - **Q4.2b** ✅ **Heights** (EF13 (5.6), (5.10), (7.4)): at most `s + n` distinct forms
    (`card_forms_domainSystem_le`); `log H_L ≤ log n! + n · formLogHeight / [K : ℚ]`
    (`log_absFormHeight_domainSystem_le`, Hadamard and the ultrametric Leibniz bound through
    `Height.mulHeight_le_pow_mul_pow`; EF13 have `H*(L_1) ⋯ H*(L_r)`, we have the `n`-th power of
    the height of all entries). `Δ_L ≥ H_L^{1 - C(r, n)}` is `absFormHeight_rpow_le_absDet`.
  - **Q4.2c** ✅ **The interval result** (EF13 Thm 3.3 with Lemma 5.2):
    `exists_forall_mem_interval_approxDomain_ef`. One proper subspace (`domainComap` of
    `T(L', c')` over `AlgebraicClosure K`, `domainComap_ne_top`), at most
    `intervalCount n (s + n) δ'` reals `t ≥ X₀` with `δ' = ε / 4nA` (`domainDelta`; hypotheses
    spread `≤ 2A` and `ε ≤ 4nA`), such that the
    domain at every level `log Q ≥ X₀` lies in the subspace or `log Q ∈ [t, ω₀ t)`,
    `ω₀ = cutRatio (s + n) δ'`. With `κ = 2A`: `H ≤ Q'^{-2δ'}`, and `Q'^{-δ'} ≤ Δ_L^{1/n}` and
    `Q' ≥ C₀` above `X₀ ≥ domainThreshold n [K : ℚ] s ε A (formLogHeight)`, linear in the
    height of the forms; an interval `[b, b^{ω₀})` of `Q'` is `[log b / M, ω₀ log b / M)` of
    `log Q`, `M = 2A / [K : ℚ]`, moved up to `X₀` if below (Lemma 5.2).
  - **Q4.2d** ✅ **A closed form for `intervalCount`**: `QuantitativeSubspace/FormIntervalCount.lean`,
    `intervalCount_le`: `intervalCount n R δ ≤ 60 n (n + 3) m̄` with
    `m̄ = 64000 n⁸ 4ⁿ δ⁻² log(64 n R / δ) + 2` (`chainBound`, a bound for the number of blocks of
    Theorem 8.1 for every quotient, `gapBlocks_le_chainBound`). So `O(n¹⁰ 4ⁿ δ⁻² log(nR/δ))`:
    EF13's `m₀ = 10⁵ 2^{2n} n^{10} δ⁻² log(3δ⁻¹R)` up to the constant.
    - `Real.cutCount_le_div`: `cutCount θ ω₀ ≤ log θ / log ω₀ + 1`; `log ω₀ ≥ 1/2`
      (`half_le_log_cutRatio`: `ω₀ ≥ log 6 > 5/3 > √e`).
    - The intervals of Theorem 8.1 (ratio `2ω = 8m/ε ≤ Y`, `two_gapRatio_le`) give
      `n m̄ (μ / log ω₀ + 1)` for the one quotient that occurs; the cut of `[C₀, C)` gives
      `log intervalBound / log ω₀ + 1 ≤ 3 m̄ μ / log ω₀ + 1` (`log_intervalBound_le`), from
      `gapThreshold_le` (Theorem 8.1's threshold is at most
      `200 n⁷ 8ⁿ R^{2n} m³ (m/ε)^m / (εδ) · (1 + ℓ)`) and `intervalBound ≤ (R + 2) qT(1)`. Together
      `intervalCount_le_div`: `≤ (n + 3) m̄ (μ / log ω₀ + 1)`, `μ = log(640 n³ 2ⁿ m̄ / δ)`
      (`countLog`).
    - EF13 §18's last step: `Y ≤ c ω₀⁴`, `c = 2744320000 n¹² 8ⁿ` (`countBase_le`), so
      `μ / log ω₀ + 1 ≤ 2 log c + 5 ≤ 60 n` (`countLog_div_add_one_le`,
      `two_log_countConst_add_five_le`).
    - Until 2026-10-04 the cut counts were bounded by `2 log θ + 1`, dropping `log ω₀`, and summed
      over all quotients: `(n² + 3) m̄ (2μ + 1)`, a factor `n μ` above EF13.
- **Q4.3** ✅ **The count of the large solutions** (EF13 Thm 3.1 / Evertse 2010 Thm 2.1:
  `10^9 · 2^{2n} · n^{14} · δ^{-3} · log(3δ^{-1}RD) · log(δ^{-1} log 3RD)`), from Q4.2 and DA 9.4:
  `QuantitativeSubspace/FormSystemCount.lean`. Q0.3's assembly
  (`exists_finset_submodule_of_forall_interval`) with Q4.2c's interval result in place of 6.1's.
  - `exists_finset_submodule_of_efSystemThreshold_le`: for a normalized system (2.4) with forms
    over a Galois `E / K` (fields in `Type`), the solutions with `log H(x) ≥ efSystemThreshold`
    lie in at most `efLargeCount n [E : K] R δ = 1 + intervalCount n R' δ' (1 + log ω₀ /
    log (1 + δ / 2n))` proper subspaces, `R' = R [E : K] + n`, `δ' = δ / (4 (n + δ))`
    (`efSystemDelta`; Q4.2's `ε / 4nA` at `ε = [E:K] δ / 2` (`efEps`) and half the spread
    `A = [E:K] (1 + δ/n) / 2` (`efSpread`), where `[E : K]` cancels, `domainDelta_efEps`; EF13
    (5.4): `δ = ε / (n + ε)`), `ω₀ = cutRatio R' δ' = δ'⁻¹ log 3R'`.
  - The spread: Q0.3's raised exponents (`IsNormalizedSystem.exists_raise`, now with weight
    exactly `-δ` and `c' ≤ s(p)`) shifted by `δ / 2nt` have weight `-[E:K] δ/2` over `E` and
    largest exponents of weight `approxSupWeight ≤ [E:K] (1 + δ/2n)`
    (`approxSupWeight_conjExponent`); the assembly's interval hypothesis receives both.
  - `exists_finset_submodule_of_isNormalizedSystem_ef`: all solutions, with DA 9.3 and one
    interval of DA 9.4 (`exists_finset_submodule_of_isNormalizedSystem_of_large`).
  - `efSystemThreshold_le`: the threshold is linear in `log H` (Q4.2's `domainThreshold`,
    monotone in the height of the forms, at Q0.3's bound for the conjugated forms).
  - Closed forms: `efLargeCount_le`: `≤ 1 + 60 n (n + 3) m̄ (1 + 4n δ⁻¹ log ω₀)` (Q4.2d and
    `log (1 + x) ≥ x / 2`); `efLargeCount_le_shape`:
    `≤ 3 · 10⁹ · 4ⁿ n¹³ δ⁻³ · log(64 n R' / δ') · log ω₀`; `efLargeCount_le_ef`, in EF13's
    variables with `RD = R [E : K]`:
    `≤ 2 · 10¹³ · 4ⁿ n¹⁴ δ⁻³ · log(3RD / δ) · log(δ⁻¹ log 3RD)`. EF13's shape; the constant is
    larger (EF13: `10⁹`). Independent of `[E : ℚ]`, the places and `H`.
  - The gap closed on 2026-10-04 (it was a factor `n μ`, `μ = O(n + log δ⁻¹ + log log RD)`):
    - `n`: Q4.2 twisted by `κ = 2A` with `A` the absolute weight, `≍ n [E : K]` for the raised
      exponents; EF13 twist by the spread, `≍ [E : K]` (`δ'` was `δ / (32 n (n + 1))`).
    - `μ`: Q4.2d dropped `log ω₀` from the cut counts and summed over the quotients.
  Together with DA 9.3 this is the full quantitative Subspace Theorem at EF13's strength.

### Layer Q5 (branch): higher degree (Evertse–Ferretti 2008, Quang 2022)

- **Q5.0** Chow forms and Chow weights (moved here from Q3 by Q3.0; FW94, Fe00, Fe03, EF02).
  Chow forms of projective varieties over `K` and their heights; Chow weights (Mumford's degree
  of contact) with respect to a weight vector; the EF02 lower bound for Chow weights, and Quang's
  2022 improvement for Q5.2. Fe00, EF02 and FW94 are not in the local paper folders.

- **Q5.1** EF08: the number and degrees of the exceptional subvarieties for polynomials of higher
  degree in general position on a variety. It is reduced to Q2.4 or Q4.3 by a Veronese
  embedding and Q5.0.
- **Q5.2** Quang 2022: subgeneral position, via the sharper Chow-weight bound of Q5.0.
- **Q5.3** (optional) Grieve 2023: big linear systems and the structure of the exceptional set.

## Ordering

```
DA 2–6, 9 (landed) ──► Q0 ──► Q1 ──► Q2 ──► Q3 ──► Q4 ──► Q5
                                                           ▲
                                     Chow theory (Q5.0) ───┘
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
