# Faltings–Wüstholz 1994: Diophantine approximations on projective spaces

G. Faltings and G. Wüstholz, *Diophantine approximations on projective spaces*, Invent. Math.
**116** (1994), 109–138 (the copy read: `~/math/lean-code/papers/FaltingsWustholz1994.pdf`, 30
pages). Ref `FW94` in `../papers.md`. The directory name has no umlaut.

**Status: FW.1–FW.4 done (2026-10-17).**
- FW.1, the Subspace Theorem on a subspace, is DA 6.7.
- The weights are in `Weight.lean`, the see-saw and semistability in `Semistability.lean`.
- Theorem 8.1 is in `LinearForms.lean` and `Semistability.lean`, Roth's theorem from it in
  `Roth.lean`.
- Theorem 9.3 for one `t` is in `HigherDegree.lean`.
- Open: FW.5 (§3), which waits for Q5.

The directory is its own `lean_lib` (`FaltingsWustholz1994`), held to the same rules as the
other paper directories:
- no `sorry`, no `set_option`, std3 axioms;
- fine-grained imports, module system, Mathlib root namespaces.

It is in the gates' library lists. Its comparator lane and `formalization.yaml` come later.

**House rule: no paper library imports another.** General Diophantine pieces go to
`DiophantineApproximation/`, linear and commutative algebra to `STForMathlib/`. Importing the
roadmap libraries (`DiophantineApproximation`, `QuantitativeSubspace`) is allowed.

## Why this paper

`../formalize.md`, A3, ranks FW94 "for Q5.0 only": its §3 (the limit measure of a filtered graded
algebra and its expectation) is the definition that Ferretti 2000 and EF02 recast as Chow weights.
The DA README lists FW94's higher-degree theorem (Theorem 9.3) under *Long horizon*, "and the
Evertse–Ferretti deduction of it from the Subspace Theorem". Finding 1 below makes Theorem 9.3,
in a form that needs no §3, a consequence of DA 6.3. That changes A3's verdict "formalize nothing
from it before Q5 starts".

## The results of the paper

`K ⊆ L` number fields, `𝒮` a finite set of places of `L`. Places `w` are counted with
multiplicity `n_w = [L_w : ℚ_p]`. `‖·‖_w` extends the standard `p`-adic or real norm and is
extended to `𝒪(1)`, so `‖f(x)‖_w = |f(x)|_w / ‖x‖_w^{deg f}`. `H` is the absolute height. For
`w ∈ 𝒮`, finitely many forms `f_{w,α}` over `L` and reals `c_{w,α} > 0` are given. The system is

```text
(1)   ‖f_{w,α}(x)‖_w < H(x)^{−c_{w,α}}      (w ∈ 𝒮, α ∈ I_w),   x ∈ ℙⁿ(K).
```

For linear forms, `F^p V_L` is the span of the `f_{w,α}` with `c_{w,α} ≥ p` (and `F^0 = V_L`).
Then `μ_w(V) = ∑_j p_j dim gr^{p_j} / dim V`. A subspace carries the induced filtration, and
`V` is *jointly semistable* if `∑_w μ_w(W) ≤ ∑_w μ_w(V)` for all `0 ≠ W ⊊ V` over `K`.

| Result | Statement | Proof in the paper |
|---|---|---|
| §2 | review of Faltings 1991: the product theorem on `ℙ^{n₁} × ⋯ × ℙ^{n_m}`, its arithmetic form, good projections | cited |
| Lemmas 3.1–3.3 | for a filtration `F^j` of a graded algebra `R` with `gr_F R` finitely generated, the bigraded Hilbert series is a sum of `P_i/Q_i` with `Q_i` products of `1 − X^a Y^b`. The measures `p_n = ∑_j dim gr^j R_n / dim R_n · δ_{j/n}` converge to a limit `p_∞` | Hilbert–Serre, induction on dimension; sketched |
| Ex. 1, 2 | one form of degree `r` on `X` of dimension `d`: `p_∞[x, 1/r] = (1 − r x)^d` and `E(p_∞) = 1/(r(d+1))` | computation |
| §4 | the see-saw `dim V · μ(V) = dim V' μ(V') + dim V'' μ(V'')`; filtered morphisms between semistable spaces; the Harder–Narasimhan filtration; several filtrations; Galois descent; perturbing the `p_j` | linear algebra |
| **Thm 4.1** | `V₁ ⊗ V₂` is semistable if `V₁`, `V₂` are; hence `E(p_∞) ≥ μ(V)` on `Sym V / I` | Narasimhan–Seshadri on a cyclic cover of `ℙ¹` |
| Prop. 5.1 | the law of large numbers for the product filtration on `X₁ × ⋯ × X_m` | Chebyshev |
| Prop. 6.1 | Siegel's lemma for several subspaces | Bombieri–Vaaler |
| Lemmas 7.1, 7.2 | integrality and local bounds of differential operators on good projections | Faltings 1991 |
| **Thm 8.1** | linear `f_{w,α}`, jointly semistable, `∑_w μ_w(V) > [L : ℚ]`: (1) has finitely many solutions, also on any subscheme `X ⊆ ℙⁿ` | Prop. 8.2 by induction: auxiliary section, index, product theorem |
| Thm 9.1 | linear, `W` the first Harder–Narasimhan step, `∑_w μ_w(W) > [L : ℚ]`: finitely many solutions outside `ℙ(V/W)` | projection to `ℙ(W)`, sketched |
| Cor. 9.2 | the Subspace Theorem with finite places | Thm 9.1 |
| Roth | `f = T₀ − α T₁` with its conjugates | Thm 8.1 |
| **Thm 9.3** | forms of any degrees, `∑_w E(p_w) > [L : ℚ]`: the solutions of (1) are not Zariski-dense in `ℙⁿ`, or in a closed subscheme with its coordinate ring | Veronese embedding, Thm 9.1 |
| Thm 10 | the unit equation through the isotypic decomposition | Thm 8.1 |
| Thm 11.1 | `∏ f_j(x) = c` on `X`, `D > (l − 1) d`: the `𝒪`-integral solutions lie in finitely many hypersurfaces | Thm 9.3 and Noether normalization |
| Thm 12.1 | gap principle: the solutions with `R < H(x) < R^{1+ρ}` lie in `≤ N` hyperplanes | determinant |

## Findings from reading the plan against the repository

1. **Theorems 8.1 and 9.3 follow from DA 6.3; FW's own proof is not needed for them.** FW's
   proof of 8.1 needs the arithmetic product theorem on products of subvarieties (§§2, 7),
   Theorem 4.1 (Narasimhan–Seshadri) and §§5–6. None of that is in the repository or planned.
   The statements, however, are consequences of the Subspace Theorem:
   - **Thm 8.1** by induction on a subspace `U` containing solutions. At each place pick a basis
     of `U^*` among the restricted forms with the largest sum of exponents. That sum is
     `dim U · μ_v(U)` for the quotient filtration (greedy choice). The product of these forms is
     `≤ H(x)^{−dim U · ∑ μ_v(U)}`, so if the exponent exceeds `dim U`, the Subspace Theorem
     *on `U`* puts the solutions into finitely many proper subspaces of `U`. A line holds one
     point.
   - **Thm 9.3** by the `t`-th Veronese map `x ↦ x^{(t)}`, `‖x^{(t)}‖_v = ‖x‖_v^t` exactly. The
     products `m ∏ f_{v,α}^{j_α}` of degree `t` (monomials `m` of weight `0`) are linear forms
     in `x^{(t)}` with exponent `(∑ j_α c_α)/t`. A best basis of `R_t` (or of `(R/I)_t`) among
     them has exponent sum `W_v(R_t)/t`, and 6.3 on `K^{R_t}` (or on `I_t^⊥`) gives finitely
     many hyperplanes, i.e. finitely many forms `q` of degree `t`, `q ∉ I`.

   This is the Evertse–Ferretti route the DA README names, and it is the theorem as later
   literature uses it.
2. **Theorem 9.3 has a form without §3.** FW's hypothesis is `∑ E(p_w) > [L : ℚ]`, where
   `E(p_w) = lim_t W_w(R_t)/(t · dim R_t)` needs Lemmas 3.1–3.3. The proof only uses one `t`
   with `∑_v W_v(R_t) > t · dim R_t` (normalized as in Finding 5). Stated with "for some `t`", the
   theorem is stronger, needs no measures, and FW's version is the special case once the limit
   exists. So §3 splits off as its own milestone, FW.5, which is the Q5.0 piece.
3. **Joint semistability is stronger than what is used.** The induction of Finding 1 needs only
   `∑_v μ_v(U) > 1` for every nonzero `K`-subspace `U` of points, with the *quotient* filtration
   on `U^* = V/U^⊥`. FW's hypothesis implies it, through the see-saw and `μ(U) ≥ μ(V)`. The
   theorem of record takes the weaker hypothesis. FW's own definition, by subspaces of forms with
   the induced filtration, is connected by the see-saw (FW.2).
4. **The weight is EF13's, with the sign flipped.** The best basis of `U^*` among the restricted
   forms is `Submodule.formWeight` of `QuantitativeSubspace/FormSubspaceWeight.lean` (Q3.2) for the
   exponents `−c`. EF13 takes the least sum because its exponents are signed the other way.
   Supermodularity (Lemma 15.1), the destabilizing subspace and the filtration (Q3.1) are
   therefore FW's Harder–Narasimhan filtration in point language. The first HN step `W` of forms
   is `T^⊥` for EF13's `T`, and maximal rank of `W` is minimal dimension of `T`. §4 minus
   Theorem 4.1 is already in the repository, up to this dictionary.
5. **Normalizations.** DA's `approxProd` uses `InfinitePlace` absolute values with `mult` and
   `FinitePlace`s (already raised to `n_w`), and `mulHeight` is relative to `K`. FW's
   `‖·‖_w ≤ H^{−c}` at a place of `K` becomes:
   - `w v (f x) / ‖x‖_v ≤ mulHeight x ^ (−c')` with `c' = c/[K : ℚ]` at an infinite place;
   - the same with `c' = c n_v/[K : ℚ]` at a finite place.

   FW's `∑_w n_w μ_w > [K : ℚ]` becomes `∑_{v ∈ S∞} mult v · μ_v(c') + ∑_{v ∈ S₀} μ_v(c') > 1`,
   i.e. `∑ … W_v(U) > dim U`.
6. **FW's places of `L` reduce to DA's places of `K`.** FW allow different forms at the places
   `w ∣ v` of `L`. For `x ∈ Kⁿ⁺¹`, `‖f(x)‖_w = |σ_w f (x)|_{w₀}` for one `w₀ ∣ v` and embeddings
   `σ_w`, so all of them become one family over the Galois closure at `w₀`, with the same
   exponents. The merged family's best basis at `v` is at least the best of each `w`, hence at
   least the `n_w`-weighted mean. So the statement with one finite family per place of `K` (any
   number of forms, as in DA 6.5) implies FW's. The theorem of record uses DA's convention: forms
   over a finite extension `F`, measured by `w v`.
7. **The Subspace Theorem on a subspace is missing.** DA 6.3 is for points of `Kⁿ⁺¹` and
   `n + 1` forms on it. The induction needs it for points of a subspace `U` and `dim U` forms
   independent on `U_F`. Coordinates `φ : K^d ≅ U` change the local factors `‖x‖_v` (at
   `v ∈ S`) and the height by bounded factors only. That is a constant in front of
   `H^{−d−ε}`, removed by halving `ε` and Northcott, as in DA 6.5. General, so it goes to DA
   (FW.1).
8. **Theorem 9.1: the paper does not justify its key step; out of scope.** The projection
   `π : x ↦ (f(x))_{f ∈ W}` does not carry (1) to `ℙ(W)`: `‖f(x)‖_w/‖π x‖_w` is
   `‖f(x)‖_w/‖x‖_w` times `‖x‖_w/‖π x‖_w`, which is unbounded on a fibre. So finiteness of the
   `π(x)` does not follow from Theorem 8.1 on `W` as claimed. 9.1 is Vojta's refinement, recorded
   in DA as "can be deduced from 6.4 but not in a few lines" (*Long horizon*). Corollary 9.2 is
   DA 6.3 itself.
9. **The rest is in the repository or out of reach.**
   - §10 (unit equation) is DA 8.2, §11's Theorem 11.1 is CZ04a Theorem 1 with constant `g`
     (`../CorvajaZannier2004Thue/`) and DA 8.6, and §12 is DA 9.2.
   - §2's product theorem is Q1.2 only for products of projective spaces; the arithmetic form
     needs Q1.3.
   - Theorem 4.1 needs Narasimhan–Seshadri, or Totaro's GIT proof, and nothing else here needs
     it.

10. **Theorem 9.3 is false for a zero-dimensional `X`; FW.4 assumes `dim (R/I)_t ≥ 2`.** Take
    `K = L = ℚ`, `X = V(2T₀ − T₁) = {(1:2)}` and the one form `f = T₀ + βT₁`, with
    `β = −1/2 + 10⁻⁹` and `c = 3`.
    - The point solves FW's system, even with the strict `<`: `‖f(x)‖ = 10⁻⁹ < 2⁻³ = H(x)^{−c}`.
    - FW's hypothesis holds: `(R/I)_t` is spanned by the class of `f^t`, so `E = c = 3 > 1`.
    - The conclusion fails: the solutions are all of `X`, hence Zariski-dense in it.

    In the terms of FW.4 this is `dim (R/I)_t = 1`. There `U = I_t^⊥` is a line, which has no
    proper subspaces but `0`, and FW.1 (DA 6.7) needs `dim U ≥ 2`. The hypothesis
    `2 ≤ dim (R/I)_t` holds whenever `dim X ≥ 1`, so nothing of FW's intended use is lost. FW's
    proof through Theorem 9.1 on the Veronese image has the same gap.

## Milestones

- ✅ **FW.1 — the Subspace Theorem on a subspace (`DiophantineApproximation/`)**, landed as DA
  6.7, `NumberField.exists_finset_submodule_lt_of_generalProd_le`
  (`SubspaceSubmodule.lean`), as planned. For a
  `K`-subspace `U ⊆ Kⁿ⁺¹` of dimension `d ≥ 2` and, at each `v ∈ S∞ ∪ S₀`, forms
  `ℓ v : κ → Dual F (ι → F)`, `#κ = d`, linearly independent on `U_F = span_F U`: the
  `x ∈ U ∖ 0` with
  `∏_{S∞} (∏_k w v (ℓ v k x)/‖x‖_v)^{mult v} ∏_{S₀} ∏_k … ≤ mulHeight x ^ (−d − ε)` lie in
  finitely many proper subspaces of `U` (Finding 7). The proof goes through a basis of `U`,
  `Matrix.mulHeight_mulVec_le` both ways (with a left inverse), local comparisons at the finitely
  many places of `S`, 6.3 at `ε/2`, Northcott for the small heights, and the image of the
  subspaces. DA 6.3 is the case `U = ⊤`.
- ✅ **FW.2 — the weight of a subspace (`Weight.lean`, `Semistability.lean`).**
  - The local weight `W_v(U)`: the largest `∑_{i ∈ I} c_i` over the bases `I` of `U_F^*` among
    the restrictions of `ℓ v` and the coordinate forms, the latter with exponent `0` (FW's
    `p₀ = 0`): `NumberField.IsWeightBasis`, `localMaxWeight`, attained
    (`localMaxWeight_mem`). A basis exists through
    `Module.Dual.linearIndependent_algebraMap_comp`
    (`STForMathlib/LinearAlgebra/DualScalarExtension.lean`).
  - The global `W(U) = ∑_{S∞} mult v · W_v(U) + ∑_{S₀} W_v(U)`, `maxWeight` (Finding 5).
  - FW's filtration `F^p V` (`filtration`, `= ⊤` for `p ≤ 0`), the degree
    `dim X · μ(X) = ∑_p p · dim gr^p X` of the induced filtration (`degree`), `slope`,
    `U^⊥` (`vanishingForms`, the kernel of `restrictForms`).
  - **The greedy identification** `localMaxWeight_eq_sum`: `W_v(U)` is the degree of `U^*` for
    the quotient filtration. The general step is `STForMathlib/LinearAlgebra/GreedyBasis.lean`
    (an exchange argument: a best basis meets every `F^p` in its rank). It needs
    `finrank_span_restrictForms`: the restricted forms span a space of dimension `dim U`.
  - **The see-saw** `degree_top_eq_degree_add_localMaxWeight`: `deg V = deg U^⊥ + W_v(U)`.
  - **FW's joint semistability** `IsJointlySemistable` (over the `U^⊥`, `0 ≠ U ⊊ K^ι`, which
    are the `K`-rational `0 ≠ W ⊊ V`) with `1 < totalSlope ⊤` gives `W(U) > dim U` for all
    `U ≠ 0`: `lt_maxWeight_of_isJointlySemistable` (Finding 3).

  The identification with `formWeight (−c)` (Finding 4) is used only for the existence of a
  basis; the Harder–Narasimhan dictionary is not formalized, as nothing here uses it.
- ✅ **FW.3 — Theorem 8.1 (`LinearForms.lean`, `Semistability.lean`, `Roth.lean`).**
  - The theorem: `NumberField.exists_finset_line_of_lt_maxWeight` (finitely many lines) and
    `finite_setOf_isSystemSolution` (finitely many projective points), with FW's system (1) as
    `IsSystemSolution` (inequalities `≤`, any real exponents). The hypothesis is
    `dim U < W(U)` for every nonzero `K`-subspace `U`. The proof is strong induction on `dim U`
    with FW.1 (Finding 1), through the product bound `generalProd_le_of_isSystemSolution`.
  - FW's form, with joint semistability:
    `finite_setOf_isSystemSolution_of_isJointlySemistable` (`Semistability.lean`, through FW.2).
  - Roth's theorem as the paper's test:
    `NumberField.finite_setOf_min_one_abs_sub_le_of_irrational` (`Roth.lean`). It is DA 3.3's
    `Real.finite_setOf_min_one_abs_sub_le` for irrational `ξ`, here from Theorem 8.1 with the
    one form `T₀ − ξ T₁` over `ℚ⟮ξ⟯` and an exponent `c ∈ (2, κ)`. The weight is `c` on every
    `U ≠ 0`: a line because `ξ` is irrational, the plane through the basis `T₀ − ξ T₁`, `T₁`.
    FW need conjugate forms at the other infinite places of `L`; over `K = ℚ` there are none.
  - FW's remark "the same on any subscheme `X ⊆ ℙⁿ`" is not a separate theorem: the hypothesis
    is on `V`, not on `X`, so the solutions in `X(K)` are a subset of the finite set. The
    content FW have in mind, a hypothesis on `X` through its coordinate ring, is FW.4's.

- ✅ **FW.4 — Theorem 9.3 for one `t` (`HigherDegree.lean`).** For forms `f v k` over `F` of
  degrees `d v k`, finitely many per place, and an ideal `I` of `K[X]`:
  - `NumberField.exists_finset_isHomogeneous_notMem`: if for some `t ≥ 1`,
    `2 ≤ dim U_t(I) < W(U_t(I))` (Finding 10), finitely many forms `q` of degree `t`, none in
    `I`, cover the nonzero solutions in `V(I)(K)` of the system `IsFormSystemSolution`.
  - `NumberField.exists_notMem_of_isPrime`: for a prime `I`, one form not in `I` vanishes at all
    of them, so they are not Zariski-dense in `V(I)` (Findings 1, 2).
  - `U_t(I) = I_t^⊥` is `formAnnihilator`, the weight is `veroneseWeight`: FW.2's `maxWeight` for
    the products `X^μ ∏ f_k^{j_k}` of degree `t` (`productPoly`, `productIndex`), with exponents
    `(∑ j_k c_k)/t` (`productExp`). So `dim U < W(U)` is FW's
    `∑_v W_v((R/I)_t) > t · dim (R/I)_t`. FW's Theorem 9.3 for `ℙⁿ` is `I = 0`.

  The proof:
  - (a) ✅ One step of FW.3, `exists_finset_submodule_lt_of_lt_maxWeight` (`LinearForms.lean`),
    now also used by FW.3's induction.
  - (b) ✅ The Veronese map and its height, in `STForMathlib/`:
    `MvPolynomial.degreeMonomials`, `MvPolynomial.veronese`
    (`RingTheory/MvPolynomial/Veronese.lean`), `AbsoluteValue.iSup_veronese` (the local identity
    `⨆_μ v(x^μ) = (⨆_j v(x_j))^t`) and `Height.mulHeight_veronese` (`H(x^{(t)}) = H(x)^t`,
    through Mathlib's `Height.mulHeight_pow`; `NumberTheory/Height/Veronese.lean`).
  - (c) ✅ The dictionary between forms of degree `t` and linear forms on `F^{R_t}`, in the same
    STForMathlib file: `MvPolynomial.coeffForm` with `coeffForm_veronese`
    (`λ_p(x^{(t)}) = p(x)`), `MvPolynomial.ofDual` with `coeffForm_ofDual` and `eval_ofDual`,
    `veronese_comp`.
  - (d) ✅ `HigherDegree.lean`: the local bound `div_iSup_veronese_le`, the Veronese transfer
    `isSystemSolution_veronese`, the theorem and the prime corollary.
  - (e) ✅ `dim U_t(I) = dim (R/I)_t` (`finrank_formAnnihilator`, with `(R/I)_t` the forms of
    degree `t` modulo those in `I`): `U_t(I)` is the coannihilator of `I_t` under the linear
    equivalence `MvPolynomial.homogeneousEquivDual` of the forms of degree `t` with the dual of
    the Veronese space (`formAnnihilator_eq_dualCoannihilator`).

  Two simplifications against the plan: the forms need no degree `≥ 1` (the exponents `j_k`
  range over `0, …, t`, which bounds the family), and `I` need not be homogeneous (only its forms
  of degree `t` enter).
- **FW.5 — the limit measure (§3), the Q5.0 piece.**
  - The expectation `E_v = lim_t W_v((R/I)_t)/(t · dim (R/I)_t)` exists, i.e. Lemma 3.3 in
    expectation form.
  - FW's Theorem 9.3 with `∑ E > 1` follows from FW.4.
  - Example 1 (`E = 1/(r(d+1))` for one form of degree `r`) as the acceptance test.
  - For linear forms `E_v(ℙⁿ) = μ_v(V)` exactly at every `t`: an adapted basis chosen among the
    `f`'s makes the filtration on `R_t` monomial.

  The route is open. FW's Lemma 3.1 needs `gr_F R` finitely generated, hence rational
  exponents, and a bigraded Hilbert–Serre theorem with generators of arbitrary bidegree, which
  Q1.1's multigraded Hilbert polynomial does not cover. The alternatives are Mumford's
  polynomiality of the weight, or Okounkov bodies (Boucksom–Chen). Read EF02 (local) and
  Ferretti 2000 before writing it. This milestone waits until Q5.0 is opened, as A3 says.
- **Out of scope:**
  - FW's proof of 8.1: §2's product theorem on products of subvarieties, Theorem 4.1, §§5–7
    (Finding 1);
  - Theorem 9.1 (Finding 8);
  - §§10–12, which are already in the repository (Finding 9).

## Reads

FW94 read in full (2026-10-17). Before FW.5: EF02 (`EvertseFerretti2002.pdf`) and Ferretti 2000
(not local). Background: DA README 6.3, 6.5 and *Long horizon*; QS README Q3.0–Q3.2 and Q5.0.
