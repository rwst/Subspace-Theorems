# Corvaja–Zannier 2004: on a general Thue's equation

P. Corvaja and U. Zannier, *On a general Thue's equation*, Amer. J. Math. **126** (2004),
1033–1055 (the copy read: `~/math/lean-code/papers/CorvajaZannier2004-Thue.pdf`, 23 pages). Ref
`CZ04a` in `../papers.md`. Not to be confused with `../CorvajaZannier2004/` (CZ04b, Acta Math.,
powers of an algebraic number).

**Status: CZ.7 done (2026-10-16), all of the paper's results in scope: Lemmas 2.1–2.4, 3.1,
3.2, homogenization, the adapted basis, the counts and the generic linear forms in
`STForMathlib`; the engine in `Engine.lean`; the local Nullstellensatz inequality in
`DiophantineApproximation/`; Lemma 3.3 and Prop. 3.1 in `EqualDegrees.lean`; Theorems 2 and 1,
and Theorem 1 for `n = 2` as a finiteness statement, in `Theorems.lean`; Theorem 3 and
Corollary 2 in `PolynomialSubspace.lean`.** The directory is its own
`lean_lib` (`CorvajaZannier2004Thue`), held to the same rules as the other paper directories (no
`sorry`, no `set_option`, std3 axioms, fine-grained imports, module system, Mathlib root
namespaces), and in the gates' library lists since its first file (CZ.4). Its comparator lane and
`formalization.yaml` come later. The directory name has no hyphen because a Lean module name
cannot contain one.

**House rule: no paper library imports another.** The commutative algebra of §2 goes to
`STForMathlib/`, general Diophantine pieces (the local Nullstellensatz inequality, the affine
Northcott count) to `DiophantineApproximation/` or `ArithmeticHeights/`. Only what is specific to
the equation `f₁ ⋯ f_r = g` stays here.

## Why this paper

DA 8.7 (`GcdBound.lean`) records under ⚠ that it was done with "order of vanishing one, and one
application … there is no filtration by higher order of vanishing". CZ04a §3 is that filtration,
in its first general form, in the language of DA 6.4: polynomials, `S`-integers, one
application of the affine Subspace Theorem per class of points. Levin 2009, Autissier 2011 and
Ru–Vojta 2020 carry the same construction on arbitrary varieties through divisors and Nevanlinna
constants, which neither roadmap owns. See `../formalize.md`, A2.

## The results of the paper

`k` a number field, `S ⊇ M_∞(k)` finite, `|·|_v` normalized by `[k_v : ℚ_p] / [k : ℚ]`,
`‖P‖_v = max (1, |p₁|_v, …, |pₙ|_v)`, `h(P) = ∑_v log ‖P‖_v` (the affine height), `f̄` the
homogenization of `f` in `k[X₀, …, Xₙ]`, `n ≥ 2`. `Z ⊂ ℙⁿ` an irreducible ideal-theoretic complete
intersection `Ḡ₁ = ⋯ = Ḡ_b = 0` of dimension `n − b`, with `Z ∩ {X₀ = 0}` of dimension `n − b − 1`;
`Z = Z̄ ∩ 𝔸ⁿ`, `E = E₁ ⋯ E_b` with `E_i = deg G_i`. `e = deg g`.

| Result | Statement | Proof uses |
|---|---|---|
| **Thm 1** | if `X₀ ḡ` and any `n − 1` of the `f̄ᵢ` have finitely many common zeros, no `n` of the `f̄ᵢ` have a common zero at infinity, and `∑ deg fᵢ > n max deg fᵢ + e`, then the `S`-integral points of `f₁ ⋯ f_r = g` are not Zariski-dense | Thm 2 with `b = 1`, `s = n − 1`, `Z` an irreducible component |
| Cor. 1 | `n = 3`, the same hypotheses with `∑ deg fᵢ > 4 max deg fᵢ + e`: finitely many solutions with `g(x) ≠ 0` | Thm 1, **Siegel's theorem**, a valuation argument on curves |
| **Thm 2** | `Z ⊂ X`; any `n − b` of the `fᵢ` cut `Z` in finitely many points; no `s + 1` of the `f̄ᵢ` have a common zero on `Z̄ ∖ Z`; `∑ deg fᵢ > s (n−b+1)/(n−b) · max deg fᵢ + e`. Then `Z(O_S)` is not Zariski-dense in `Z` | Prop. 3.1 after padding to equal degrees by generic linear forms `ρᵢ` |
| Thm 2′ | the same with "`n − c` of the `fᵢ` cut `Z` in dimension `≤ c − b`" and `n − c` in the denominator | stated without proof |
| **Prop. 3.1** | Thm 2 when `deg fᵢ = δ` for all `i`: `r > s (n−b+1)/(n−b) + e/δ` | Lemmas 3.1–3.3, the Subspace Theorem |
| Lemma 2.1 | `m` forms cutting `ℙⁿ` in dimension `n − m` form a regular sequence | Cohen–Macaulay (cited) |
| Lemma 2.2 | `φ^i q = ∑_r φ^{j(r)} q_r` with all `j(r) >_lex i`, `φ` regular: `q ∈ (φ)` | induction on `m` |
| Lemma 2.3 | `n` forms cutting `ℙⁿ` in dimension `0`: `dim (V̄_N / (φ) ∩ V̄_N) = ∏ deg φᵢ` for large `N` | Hilbert polynomial, Bézout (cited) |
| Lemma 2.4 | `V̄_N / (Ḡ) ∩ V̄_N ≅ V_N^*` by `X₀ = 1`; `(G) ∩ V_N = {∑ Aᵢ Gᵢ : deg Aᵢ ≤ N − Eᵢ}` | `X₀` regular modulo `(Ḡ)` (Lemma 2.1) |
| Lemma 3.1 | `W_(i) / W_(i′) ≅ V̄_{N−δσ(i)} / (γ̄, Ḡ) ∩ V̄_{N−δσ(i)}` for consecutive `(i) <_lex (i′)` | 2.1, 2.2, 2.4 |
| Lemma 3.2 | `Δ(i) = dim W_(i)/W_(i′) = E δ^{n−b}` when `δσ(i) < N − N₀`, bounded otherwise | 3.1 + 2.3 |
| (3.2) | `log ∏_t |ψ_t(P)|_v ≤ ∑_j log |γ_j(P)|_v · E N^{n−b+1}/(δ(n−b+1)!) + log ‖P‖_v · E N^{n−b+1}/(n−b+1)! (1 + O(1/N)) + c₁` | the adapted basis, lattice-point counts |
| Lemma 3.3 | `∑_{j ≤ s} log |f_{l_v(j)}(P)|_v ≤ (e − δ(r − s)) log ‖P‖_v + O(1)` along a sequence converging `v`-adically | the equation, no `s + 1` common zeros at infinity |
| **Thm 3** | Subspace Theorem for polynomials: `n − 1` polynomials `f_{iv}` per `v ∈ S` with `X₀, f̄_{iv}` of dimension `0`; the solutions of `∏_v ∏_i |f_{iv}(x)|_v^{1/δ_v} ≤ H(x)^{µ−n−ε}` lie in a hypersurface `H`, and on each component of `H` of dimension `n − 1` the `f_{iv}` of some `v` cut a curve | sketched: a two-level filtration on `ℙⁿ`; Prop. 3.1 with `Z = H`, `b = 1` |
| Cor. 2 | `f ∈ ℚ̄[X]` of degree `δ`: the `x ∈ ℤⁿ` with `0 < |f(x)| < H(x)^{−δ(n−1)−ε}` lie in one variety of dimension `≤ n − 2` | Thm 3 with Galois-conjugate places |

## Findings from reading the plan against the repository

1. **Corollary 1 is not reachable.** Its proof is Theorem 1 *and Siegel's theorem* (a curve with
   infinitely many `S`-integral points has at most two points at infinity), followed by a
   valuation argument on a nonsingular model of the curve. Siegel's theorem and curves are
   *Not owned here* in the DA README (Riemann–Roch belongs to `AlgebraicCurves`). This corrects
   `formalize.md` A2, which named Corollary 1 a first target.
2. **Zariski density needs no topology.** Prop. 3.1's proof ends with one polynomial
   `q ∉ (G₁, …, G_b)` vanishing on infinitely many points; the passage to "not dense" enumerates
   the proper closed subsets. Run backwards with primality of `(G)`, it says: **there is one
   `q ∉ (G)` vanishing on all of `Z(O_S)`**. That is the theorem of record's form, with
   `MvPolynomial` only: a product of polynomials outside a prime ideal stays outside it, and
   finitely many exceptional points are absorbed by one linear factor each.
3. **No limits, no compactness of `Z(k_v)`.** The sequence `P_i → P_v` is used only in
   Lemma 3.3, to get `|f(P)|_v ≫ ‖P‖_v^δ` for the `f` not vanishing at the limit point at
   infinity. The same follows uniformly from the hypothesis in ideal form: if `X₀` and
   `f̄_{j₀}, …, f̄_{j_s}` have no common zero in `ℙⁿ(k̄)`, then `Xᵢ^M ∈ (X₀, f̄_{j₀}, …, f̄_{j_s})`
   for some `M` (Nullstellensatz), and evaluating that identity gives
   `max_{j ∈ J} |f_j(P)|_v ≥ c ‖P‖_v^δ` once `‖P‖_v ≥ R` (a **local Nullstellensatz
   inequality**, for archimedean and ultrametric `v`). The points then fall into finitely many
   classes — the ordering `l_v` of (3.1) and "bounded or not" at each `v ∈ S` — and 6.4 is
   applied once per class. Points of bounded height are finite (Northcott,
   `ArithmeticHeights/Northcott.lean`).
4. **The `(1 + O(1/N))` of (3.2) multiplies terms of either sign.** `log |γ_j(P)|_v` can be
   positive. The fix: write `c_j = log |γ_j(P)|_v − δ log ‖P‖_v`, which is `≤ C₀`. Then
   `log ∏_t |ψ_t(P)|_v ≤ d N log ‖P‖_v + ∑_j A_j c_j + c₁` exactly, with `d = ∑ Δ(i)` and
   `A_j = ∑ i_j Δ(i)`, and only **an upper bound for `d` and a lower bound for each `A_j`** are
   needed, both from Lemma 3.2 by counting lattice points in the simplex `σ(i) ≤ N/δ`. Negativity
   of `d N + A (n−b)(e − δr)/s` is the inequality on `r`.
5. **Lemma 2.3 is explicit and elementary.** For a regular sequence of forms of degrees `dᵢ` in
   `n + 1` variables, the Hilbert series is `∏ (1 − t^{dᵢ}) / (1 − t)^{n+1}` (each `φᵢ` cuts
   `dim A_m − dim A_{m−dᵢ}`; `STForMathlib/RingTheory/MvPolynomial/GradedPiece.lean` has the
   exact sequence). So `Δ(i) ≤ E δ^{n−b}` always, with equality as soon as
   `N − δσ(i) ≥ N₀ = (n−b)(δ − 1) + ∑ (Eᵢ − 1)`. No Hilbert polynomial and no Bézout theorem are
   needed, although `STForMathlib`'s `Bezout.lean` (one block) gives the same.
6. **Lemma 2.1 is the one real piece of commutative algebra.** Mathlib has regular sequences and
   their permutation in local rings (`IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal`),
   Krull's height theorem and regular local rings; `STForMathlib` has regular systems of
   parameters (`RegularLocalRing/RegularSequence.lean`). Missing: graded unmixedness, "`m` forms
   generating an ideal of height `m` are a regular sequence", via `k[X]` localized at the
   irrelevant ideal. The hypotheses "define a variety of codimension `m`" are stated as
   `(Ideal.span (Set.range φ)).height = m`, which does not see `k̄`. Only the height of the
   whole sequence is needed, not of its initial segments (see CZ.1).
7. **Homogenization of `MvPolynomial` is missing.** Mathlib has `Polynomial.homogenize` only.
   `MvPolynomial.homogenize` (degree-`N` version, `X₀` the new variable, `Option σ` indexing) goes
   to `STForMathlib` with dehomogenization `X₀ = 1` and Lemma 2.4.
8. **The Subspace Theorem is DA 6.4 over `k` itself.** The forms `ψ_{tv}` are elements of
   `V_N^*` with coefficients in `k` (the `γ_j` are among the `fᵢ`), so
   `NumberField.exists_finset_submodule_of_integer_of_affineProd_le` applies with `F = K`, the
   point `Q = (φ₁(P), …, φ_d(P))` for a basis `φ` with `S`-integral coefficients and `φ₁ = 1`, and
   `h(Q) ≤ N h(P) + c₄`. For Corollary 2 DA's pinned convention (points in `K = ℚ`, forms over an
   extension `F`) removes the paper's Galois-conjugate places, as for Sch90's `d!`.
9. **An engine theorem for both Thm 2 and Thm 3's second part.** Prop. 3.1 uses (1.1) only
   through Lemma 3.3, and Thm 3's second conclusion is Prop. 3.1 with `Z = H`, `b = 1` and (1.4)
   in place of Lemma 3.3. So the core is stated with the inequality as a hypothesis (CZ.4).
10. **Theorem 3's first part is sketched only.** It needs a two-level filtration on `ℙⁿ` with
    `n − 1` polynomials (dimension `1`, so `Δ(i)` grows linearly) and the degree count
    `∑ deg q ∼ δ^{n−1} (N − δσ(i))² / 2`. Last, and only after CZ.6. *Corrected in CZ.7*: the
    two-level filtration is the engine's filtration for the `n` polynomials
    `γ₁, …, γ_{n−1}, 1`, since `1^h = X₀^δ`, with the second level in steps of `δ`; no new
    filtration or count is needed.

## Milestones

- **CZ.1 — commutative algebra (`STForMathlib`).** Regular sequences are `Bezout.lean`'s
  `MvPolynomial.IsRegularSeq t J g` (each `g j` nonzero, `colon = J` modulo the earlier ones).
  - ✅ Lemma 2.2, `MvPolynomial.mem_sup_span_range_of_prod_pow_mul_sub_sum_mem`
    (`LexCancellation.lean`), with `Pi.Lex` on `Fin m → ℕ`; induction on `m` as in the paper.
  - ✅ Lemma 2.3, `MvPolynomial.hilbertFunction_span_range_le` and
    `MvPolynomial.hilbertFunction_span_range_eq` (`CompleteIntersection.lean`), in the form of
    Finding 5: through `hilbertSeries_sup_span_range`, `HS · (1 − X) = ∏ (1 + ⋯ + X^{e_j − 1})`
    (`boxPoly`), and partial sums of its coefficients. The grading is the one-block multigrading
    `oneBlock σ`, so `hilbertFunction` and the exact-sequence identity of `Multigraded.lean`
    apply unchanged.
  - ✅ Homogenization (Finding 7), `Homogenize.lean`: `homogenize N` (a linear map, by
    monomials `d ↦ d.optionElim (N − deg d)`), `dehomogenize = aeval (Option.elim 1 X)`,
    `homogenize_dehomogenize` for forms, `homogenize_mul`, `homogenize_add_eq_X_pow_mul`.
  - ✅ Lemma 2.4, `DehomogenizeIdeal.lean`: `mem_span_homogenization_of_dehomogenize_mem` (the
    kernel) and `exists_sum_mul_eq_of_mem_span` (the degrees fit), under the hypothesis
    `(Ḡ).colon {X none} = (Ḡ)`; `homogenization p = homogenize (deg p) p`.
  - ✅ Lemma 2.1, `HomogeneousRegular.lean`: `MvPolynomial.colon_eq_of_height_eq` (each `φ j`
    a nonzerodivisor modulo `(φ i | i < j)`), `MvPolynomial.isRegularSeq_of_height_eq`
    (`IsRegularSeq m ⊥ φ`) and `MvPolynomial.colon_eq_of_height_insert_eq` (`(g, p)` of height
    `t + 1` makes `p` regular modulo `(g)`; with `p = X none`, `g = G^h` this is the hypothesis of
    Lemma 2.4). Hypothesis: homogeneous `φ` with `ht (φ) = m`. Proof in `A = K[X]_𝔪`, `𝔪` the
    irrelevant ideal, regular local by Mathlib: `IsLocalRing.isSMulRegular_of_le_height`
    (`RegularLocalRing/HeightRegular.lean`), then descent to `K[X]` because homogeneous ideals
    are saturated with respect to polynomials with nonzero constant term (their associated primes
    are homogeneous, `ExcessBezout.lean`). The local step needs no catenarity, so the heights of
    the initial segments need not be assumed: if `x_{j+1}` lay in an associated prime `Q` of
    `A/(x_{≤j})`, then `dim A/Q ≥ d − j` by depth, while Krull's height theorem cuts `A/Q` by the
    remaining `m − j − 1` elements to a quotient of dimension `≤ d − m`.
- **CZ.2 — the filtration and the adapted basis (Lemmas 3.1, 3.2).** ✅ In `STForMathlib`, since
  nothing here is specific to the equation. `γ₁, …, γ_t` of degree `≤ δ`, `δ > 0`,
  `γ̄ = homogenize δ γ`, `I = (G)`.
  - The filtration (`RingTheory/MvPolynomial/PowerFiltration.lean`): `V_N^*` is
    `MvPolynomial.quotDegLE I N ⊆ k[X]/I`, the pieces `S_e = γ^e V^*_{N−δσ(e)}` are
    `MvPolynomial.powPiece`, the exponents with `δσ(e) ≤ N` in `Lex (Fin t → ℕ)` are
    `MvPolynomial.powIndex`, and `W_{> i} = ∑_{e >_lex i} S_e` is `MvPolynomial.powFiltrationGT`.
    The paper's `W_(i)` is `S_i + W_{> i}` and its successor `W_(i′)` is `W_{> i}`, so no
    successor in the lexicographic order is needed.
  - ✅ Lemma 3.1, in dimensions: `MvPolynomial.finrank_powPiece_sup_eq`,
    `dim (S_i + W_{> i}) = dim W_{> i} + HF_{(Ḡ, γ̄)}(N − δσ(i))`, under `X₀` regular modulo `(Ḡ)`
    and `γ̄` regular modulo `(Ḡ)`. The map `q ↦ γ^i q(1, X)` sends the forms of degree
    `N − δσ(i)` onto `S_i`, and `S_i ∩ W_{> i}` pulls back to `(Ḡ, γ̄)`: Lemma 2.4, homogenization
    (`homogenize_prod_pow`) and Lemma 2.2 one way, homogeneous components of `q ∈ (Ḡ, γ̄)` the
    other. The dimension count is `Submodule.finrank_map_sup_add_finrank_inf_comap`
    (`LinearAlgebra/AdaptedBasis.lean`).
  - ✅ Lemma 3.2: `MvPolynomial.finrank_powPiece_sup_le_and`. If `|σ| = b + t`, `(Ḡ, γ̄)` has
    height `b + t` and `(Ḡ, X₀)` height `b + 1`, then `Δ(i) ≤ E δ^t` for every `i`, with equality
    when `δσ(i) + N₀ ≤ N`, `N₀ = t(δ − 1) + ∑(E_l − 1)`. The bound for every `i` is stronger than
    the paper's "bounded by `dim V̄_{N₀}`". The regularity hypotheses of Lemma 3.1 come from
    Lemma 2.1 (`colon_eq_of_height_insert_eq`, `isRegularSeq_append_of_height_eq`).
  - ✅ The adapted basis: `MvPolynomial.exists_adapted_basis`. Classes of `γ^{ℓ(x)} q_x` with
    `δσ(ℓ(x)) ≤ N` and `deg q_x ≤ N − δσ(ℓ(x))`, linearly independent and spanning
    `quotDegLE I N`, at most `E δ^t` of each exponent and exactly `E δ^t` when
    `δσ(i) + N₀ ≤ N`. It comes from `Submodule.exists_adapted_family`, a basis adapted to any
    finite filtration by finite-dimensional pieces, by induction from the last piece back.
- **CZ.3 — the counts.** ✅ In `STForMathlib/Data/Nat/Choose/SimplexCount.lean`, for any family
  labelled by exponents `ℓ x` with `δσ(ℓ x) ≤ N`, at most `D` of each label and exactly `D` of
  each label `i` with `δσ(i) + N₀ ≤ N`: the output of `exists_adapted_basis` with `D = E δ^t`.
  - Lattice points: `Finset.simplexPoints t M` (the `e : Fin t → ℕ` with `∑ e ≤ M`) has
    `C(M + t, t)` elements (`Finset.card_simplexPoints`), and each coordinate sums over it to
    `C(M + t, t + 1)` (`Finset.sum_simplexPoints_apply`), both by the shift `e ↦ e + e_j`.
  - `d ≤ D C(⌊N/δ⌋ + t, t)` (`Finset.card_le_mul_choose`) and
    `A_j ≥ D C(⌊(N − N₀)/δ⌋ + t, t + 1)` (`Finset.mul_choose_le_sum_apply`). Exact, no `O`.
  - `d ≥ D C(⌊(N − N₀)/δ⌋ + t, t)` for `N ≥ N₀` (`Finset.mul_choose_le_card`), used in CZ.4
    for `d ≥ 2`.
  - The choice of `N`: `Finset.exists_forall_card_mul_add_mul_sum_lt_zero`, from the purely
    numerical `Finset.exists_forall_choose_mul_add_mul_choose_lt_zero`
    (`C(⌊N/δ⌋ + t, t) N + θ C(⌊(N − N₀)/δ⌋ + t, t + 1) < 0`), which is the form CZ.4 uses. For
    `θ < −δ(t + 1)` there is `N₁` with `d N + θ A_j < 0` for every `N ≥ N₁` and every `j`. Write
    `−θ = a δ (t + 1)`, `a > 1`; then `N₁ = δ ⌈a (t + 1)(N₀ + 1)/(a − 1)⌉` works, by
    `C(M + t, t)(M' + 1)^t ≤ C(M' + t, t)(M + 1)^t` (`Finset.choose_mul_pow_le`) and Bernoulli
    (`Real.pow_le_mul_sub_pow`). A strict inequality is all CZ.4 needs: with
    `h(Q) ≤ N h(P) + c₄`, any `ε < −(d N + θ A)/N` serves in DA 6.4.
- **CZ.4 — the engine.** ✅ `Engine.lean`: `NumberField.exists_finset_eval_eq_zero_of_prod_le`
  (finitely many `q ∉ (G)`) and `NumberField.exists_eval_eq_zero_of_prod_le` (one `q`, for `(G)`
  prime, Finding 2). Places are DA's `InfinitePlace K ⊕ S` (`systemPlace`, `systemMult`), `γ` is a
  function of the absolute value, and the hypotheses on `γ_v` (degree `≤ δ`, `(G^h, γ_v^h)` of
  height `b + t`) are asked only at the places of the system. The inequality is stated without
  denominators, `∏_v ∏_j |γ_{jv}(P)|_v ≤ H(P)^{−(1+η)δ}` with `H = mulHeightAff`; for an
  `S`-integral `P` it is the paper's `∑_v ∑_j log (|γ_{jv}(P)|_v / ‖P‖_v^δ) ≤ −(t + 1 + η) δ h(P)`.
  - DA 6.4 is applied once, over `F = K`, to `Q(P) = (P^{m_i})_i` for a monomial basis of
    `V_N^*` containing `1` (`MvPolynomial.exists_monomial_basis`): `Q(P)` is `S`-primitive and
    `H(Q(P)) ≤ H(P)^N` exactly (`MvPolynomial.abv_eval_monomial_le`, `EvalBound.lean`). The forms
    at `v` are the coordinates of the basis adapted to `γ_v`, reindexed by `Fin (dim V_N^*)`
    (`MvPolynomial.exists_adapted_basis_fin`).
  - The local estimate (3.2) is `Finset.prod_mul_pow_le_of_le`, with
    `|q(P)|_v ≤ (∑ |c_m|_v) ‖P‖_v^{deg q}` (`MvPolynomial.abv_eval_le`) and the common lower bound
    `A = D C(M' + t, t + 1)` of the `A_j` (Finding 4). It gives
    `affineProd ≤ C · H(P)^{d N − (t + 1 + η) δ A}`, a negative power by CZ.3.
  - `N` is also taken with `⌊(N − N₀)/δ⌋ ≥ 1`, so `d ≥ 2` (`t ≥ 1`); the points of height `≤ B`
    are finite (Northcott) and each lies on a proper line, as in DA 9.1's Theorem A. A proper
    subspace gives a functional `λ ≠ 0` and `q = ∑ λ_i X^{m_i} ∉ (G)`.
  - `D > 0` is derived, not assumed: `(G) = (1)` has no points, otherwise `1 ≤ d ≤ D C(·)`.
- **CZ.5 — Lemma 3.3 and Prop. 3.1.** ✅ Prop. 3.1 is
  `NumberField.exists_eval_eq_zero_of_prod_sub_mem` (`EqualDegrees.lean`):
  `∃ q ∉ Ideal.span (range G), ∀ P ∈ Z(O_S), eval P q = 0`.
  - The local Nullstellensatz inequality (Finding 3) is DA 8.9,
    `MvPolynomial.exists_le_abv_eval_of_pow_mem` (`DiophantineApproximation/LocalNullstellensatz.lean`).
    Its degree bookkeeping is the graded form of ideal membership,
    `MvPolynomial.exists_sum_mul_eq_of_isHomogeneous` (`STForMathlib`, `DehomogenizeIdeal.lean`).
  - Lemma 3.3 is `MvPolynomial.exists_prod_mul_pow_le_of_monotone`. It holds at one absolute
    value, uniformly in `P` and in the ordering `τ`:
    `|f_{τ 0}(P) ⋯ f_{τ (s−1)}(P)|_v ‖P‖_v^{δ(r−s)} ≤ C ‖P‖_v^e`. The constants of the inequality
    are made uniform over the finitely many `(s + 1)`-sets, and `‖P‖_v < R` is the bounded case.
    (3.3) is `Finset.prod_range_pow_le_prod_range_pow`, raised to the power `s` so that no root
    is taken before the end.
  - A class is one `Tuple.sort` permutation per place of `InfinitePlace K ⊕ S`. The engine (prime
    version) is applied once per class, with `γ_v` the first `t` `f` in that order. The product of
    the `q`s stays outside `(G)` because `(G)` is prime. The points with `g(P) = 0` need no
    separate treatment, since then some `fᵢ(P) = 0` and the product in the engine is `0`.
  - The engine now takes a constant: `∏_v ∏_j |γ_{jv}(P)|_v ≤ C₀ H(P)^{−(1+η)δ}`. Lemma 3.3 gives
    the inequality only up to a constant, and in the engine it only multiplies the constant of
    (3.2). With `η = (t r δ − s (t + 1) δ − t e)/(s δ)`, the exponent `t (e − δ (r − s))/s` is
    exactly `−(1 + η) δ`. The `S`-integral height `H(P) = ∏_v ‖P‖_v` is
    `NumberField.mulHeightAff_eq_prod_systemPlace` (`Engine.lean`).
  - **Hypotheses as stated.**
    - Any `t` of the `fᵢ` cutting `Z` finitely is taken projectively, as Lemma 3.2 uses it:
      `(G^h, f^h_j)` has height `b + t` for every embedding `j : Fin t ↪ Fin r`.
    - No `s + 1` of the `f̄ᵢ` vanishing together on `Z̄ ∖ Z` is taken in ideal form: each `X_x`
      has a power in `(X₀, G^h, f^h_J)`, `#J = s + 1`.
    - `deg fᵢ ≤ δ` with `f^h = homogenize δ fᵢ`, rather than `deg fᵢ = δ`.
    - `t ≤ s` is assumed, because the paper's derivation is geometric (dimension of `Z̄ ∖ Z`).
      `s < r` follows from `s (t + 1) δ + t e < t r δ`, the inequality on `r`.
- **CZ.6 — Theorems 2 and 1.** ✅ `Theorems.lean`.
  - **Theorem 2** is `NumberField.exists_eval_eq_zero_of_prod_sub_mem_of_totalDegree_le`:
    `deg fᵢ ≤ δᵢ`, `fᵢ^h = homogenize δᵢ fᵢ`, the inequality `t ∑ δᵢ > s (t + 1) max δᵢ + t e`, the
    other hypotheses as in Prop. 3.1 with `t`-sets and `(s + 1)`-sets as `Finset`s.
  - **The padding.** `fᵢ ρᵢ^(δ − δᵢ)` and `g ∏ ρᵢ^(δ − δᵢ)`, with `ρᵢ` linear forms in
    `X₁, …, Xₙ`. The `ρᵢ` are chosen one at a time by `MvPolynomial.exists_mem_span_forall`
    (`STForMathlib`, `GenericLinear.lean`): over an infinite field one linear form avoids the
    finitely many primes that matter, by prime avoidance in a vector space. Kept along the way:
    `ht (G^h, f^h_F, ρ_H) ≥ b + |F| + |H|` for `|F| + |H| ≤ t`, and the dimension at the origin
    of `(X₀, G^h, f^h_F, ρ_H)`, `MvPolynomial.originDim` (Krull dimension of `K[X]_𝔪/J`),
    `≤ s + 1 − |F| − |H|`. A prime containing the padded forms contains `fᵢ^h` or `ρᵢ` for each
    `i`, which gives Prop. 3.1's two hypotheses.
  - **No dimension theory beyond Krull's height theorem.** The paper's preliminaries ("`V(j₁, …,
    j_h)` has dimension `n − b − h`", "`s ≥ n − b − 1`") are replaced: the heights of subfamilies
    come from Lemma 2.1 (a regular sequence generates an ideal of height `≥` its length,
    `Ideal.natCast_le_height_span_range_of_colon_eq`), and the dimension at the origin starts from
    Krull's bound (`MvPolynomial.originDim_le_card`). Every step that lowers a dimension is "a
    minimal prime is avoided" (Mathlib's
    `Module.supportDim_quotSMulTop_succ_le_of_notMem_minimalPrimes`), so no catenarity is used.
  - **Theorem 1** is `NumberField.exists_eval_eq_zero_of_dvd_prod_sub`: for every irreducible
    `G ∣ f₁ ⋯ f_r − g`, one `q ∉ (G)` vanishes at the `S`-integral zeros of `G`. That is stronger
    than "not dense in `X`" and is what the paper's proof gives. Hypotheses:
    `ht (X₀ g^h, f^h_T) = n` for `|T| = n − 1`, a power of each `X_x` in `(X₀, f^h_J)` for
    `|J| = n`, and `n max deg fᵢ + deg g < ∑ deg fᵢ`. The paper's "immediate to verify" is
    `X₀^(Δ − e) g^h = ∏ fᵢ^h − (∏ fᵢ − g)^h` with `G^h ∣ (∏ fᵢ − g)^h`, and `(G^h, X₀)` has height
    `2` because `X₀ ∤ G^h` (`MvPolynomial.height_span_X_none_homogenization`).
  - **Theorem 1 for `n = 2`** is `NumberField.finite_setOf_eval_prod_sub_eq_zero`: the
    `S`-integral solutions of `f₁ ⋯ f_r = g` are finite. For each irreducible factor `G` and its
    `q`, `(G, q)` has height `2` (`MvPolynomial.two_le_height_span_pair`), and an ideal of height
    `≥ |σ|` has finitely many zeros in `K^σ` (`MvPolynomial.finite_setOf_forall_eval_eq_zero`,
    `FiniteZeros.lean`). It contains Thue's theorem and its extension to `deg g < r − 2`
    (DA 8.4 is the linear, constant-`g` case). `f₁ ⋯ f_r − g ≠ 0` follows from the hypotheses (no
    `fᵢ` is `0`, then degrees).
- **CZ.7 — Theorem 3 and Corollary 2.** ✅ `PolynomialSubspace.lean`.
  - **Theorem 3, equal degrees.** The second part is the engine with `b = 1`
    (`NumberField.exists_eval_eq_zero_of_prod_le_of_irreducible`, Finding 9). The first part is
    the engine with `b = 0` and the `n` polynomials `γ₁, …, γ_{n−1}, 1`
    (`NumberField.exists_ne_zero_eval_eq_zero_of_prod_le`): `1^h = X₀^δ`, `(X₀^δ, γ^h)` has the
    height of `(X₀, γ^h)` (`Ideal.height_span_insert_pow`), and `|1|_v = 1`. So the paper's
    two-level filtration is the engine's, in steps of `δ` (Finding 10, corrected).
  - **Unequal degrees** (`NumberField.exists_prod_le_of_prod_rpow_le`). `f_{jv}` is padded to
    `f_{jv} ρ_{jv}^{δ_v − δ_{jv}}` by generic linear forms
    (`MvPolynomial.exists_le_height_span_mul_pow`, `STForMathlib`: heights only, all `t` forms at
    once) and raised to the power `D/δ_v`, `D = ∏_v δ_v`. The padding costs
    `‖x‖_v^{n − 1 − ∑_j δ_{jv}/δ_v} ≤ ‖x‖_v^{n − 1 − μ}`.
  - **Theorem 3** is `NumberField.exists_ne_zero_eval_eq_zero_of_prod_rpow_le` (one `q ≠ 0` at
    all `S`-integral solutions of (1.4)) and
    `NumberField.exists_eval_eq_zero_of_prod_rpow_le_of_irreducible` (the second part as its
    contrapositive: on an irreducible `G = 0` cut finitely by the `f_v` at every `v`, one
    `q ∉ (G)`). (1.4) is `∏_v (∏_j |f_{jv}(x)|_v)^{m_v/δ_v} ≤ H(x)^{μ − n − ε}`, Mathlib's
    normalization and the relative height, `μ` any lower bound of the `∑_j δ_{jv}/δ_v`. "`x₀` and
    the `f̄_{iv}` define a variety of dimension `0`" is `ht (X₀, f_v^h) = n`.
  - **Corollary 2** is `NumberField.exists_finset_eval_eq_zero_of_abv_lt`, over `K` Galois over
    `ℚ`, `x ∈ ℤⁿ`, `H(x) = max (1, |x_s|)`: finitely many `(G, q)`, `G` irreducible, `q ∉ (G)`,
    every solution of `0 < |f(x)|_ν < H(x)^{−δ(n−1)−ε}` a common zero of one pair. Theorem 3
    over `K` with `S = ∅`. At the place `w = τ_w • ν` the polynomials are `τ_w(f)` and `ρ^δ`,
    `ρ` generic linear forms chosen place by place
    (`MvPolynomial.exists_le_height_sup_span_range`). Finding 8's route through DA's
    "points over `ℚ`, forms over `F`" is not needed. Then the first part gives `q₀ ≠ 0`, and the
    second part is applied at each irreducible factor `G` of `q₀`:
    - a `G` dividing a conjugate of `f` carries no solution, since `f(x) ≠ 0`;
    - for the others, `(G^h, τ_w(f)^h)` has height `2` because `G^h` is prime
      (`MvPolynomial.prime_homogenization`).
- **Out of scope:** Corollary 1 (Finding 1); Theorem 2′ (no proof in the paper).

## Reads

CZ04a §§2–3 (read in full, 2026-10-16); Corvaja–Zannier 2018, Ch. 3 (not local) for the same
filtration explained; Autissier 2011 §2 for the general form; DA README, 6.4 and 8.7.
