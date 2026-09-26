# Corvaja–Zannier 2004: the rational approximations to the powers of an algebraic number

P. Corvaja and U. Zannier, *On the rational approximations to the powers of an algebraic number:
solution of two problems of Mahler and Mendès France*, Acta Math. **193** (2004), 175–191;
arXiv `math/0403522` (the copy read: `../CorvajaZannier2004.pdf`, 12 pages).

This directory formalizes the whole paper on top of the two libraries of this repository. It is
its own `lean_lib` (`CorvajaZannier2004`), held to the same rules (no `sorry`, no `set_option`,
std3 axioms, fine-grained imports, module system, Mathlib root namespaces), and it will carry its
own Palomar submission: its own flat Challenge, comparator config and `formalization.yaml`.
The directory name has no hyphen or dash because a Lean module name cannot contain one.

Material taken from `~/math/lean-code/CITED/CorvajaZannier*.lean` (Ralf Stephan with Claude Code,
CC0): the pseudo-Pisot predicate and its conjugate computations. The rest of those files is the
`Γ = ⟨2, 3⟩ ≤ ℚˣ` specialization of the Main Theorem derived from a *cited* Subspace axiom; here
the Subspace Theorem is a theorem (Layers 6.2/6.3), so the Main Theorem is proved in full
generality instead and the specialization is not ported.

## The results of the paper, as Lean targets

`‖x‖` (distance to the nearest integer) is written `|x - round x|`. Heights are Mathlib's
`NumberField.absMulHeight₁`, which is the paper's `H` (absolute, `max (1, ·)` at every place).

**Definition (pseudo-Pisot, p. 2).** `|α| > 1`, every conjugate other than `α` has modulus `< 1`,
and `Tr_{ℚ(α)/ℚ} α ∈ ℤ`; conjugates are the complex roots of `minpoly ℚ α`.

```lean
def IsPseudoPisot (α : ℝ) : Prop :=
  1 < |α| ∧ IsAlgebraic ℚ α ∧ (∀ z ∈ (minpoly ℚ α).aroots ℂ, z ≠ α → ‖z‖ < 1) ∧
    ∃ n : ℤ, ((minpoly ℚ α).aroots ℂ).sum = n

/-- A Pisot number: a real algebraic integer `> 1` whose other conjugates lie in the open unit
disc (p. 1; rational integers `> 1` included). -/
def IsPisot (α : ℝ) : Prop :=
  1 < α ∧ IsIntegral ℤ α ∧ ∀ z ∈ (minpoly ℚ α).aroots ℂ, z ≠ α → ‖z‖ < 1
```

**Main Theorem (p. 2).**

```lean
theorem finite_setOf_not_isPseudoPisot {Γ : Subgroup ℝˣ} (hΓ : Γ.FG)
    (hΓalg : ∀ u ∈ Γ, IsAlgebraic ℚ (u : ℝ)) {δ : ℝ} (hδ : IsAlgebraic ℚ δ) (hδ0 : δ ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    {p : ℤ × Γ | 1 < |δ * p.1 * ((p.2 : ℝˣ) : ℝ)| ∧
      ¬ IsPseudoPisot (δ * p.1 * ((p.2 : ℝˣ) : ℝ)) ∧
      0 < |δ * p.1 * ((p.2 : ℝˣ) : ℝ) - round (δ * p.1 * ((p.2 : ℝˣ) : ℝ))| ∧
      |δ * p.1 * ((p.2 : ℝˣ) : ℝ) - round (δ * p.1 * ((p.2 : ℝˣ) : ℝ))| <
        absMulHeight₁ ((p.2 : ℝˣ) : ℝ) ^ (-ε) *
          |(p.1 : ℝ)| ^ (-(finrank ℚ ℚ⟮((p.2 : ℝˣ) : ℝ)⟯ : ℝ) - ε)}.Finite
```

**Theorem 1 (p. 1).**

```lean
theorem exists_isPisot_pow_of_frequently {α l : ℝ} (hα : 1 < α) (halg : IsAlgebraic ℚ α)
    (hl0 : 0 < l) (hl1 : l < 1) (h : ∃ᶠ n : ℕ in atTop, |α ^ n - round (α ^ n)| < l ^ n) :
    (∃ n, 0 < n ∧ IsPisot (α ^ n)) ∧ IsIntegral ℤ α
```

**Lemma 4 (p. 7).** As printed, and in the stronger form the proof gives (see the fidelity notes):

```lean
theorem isIntegral_or_exists_pow_eq_ratCast {α : ℂ} (hα : IsAlgebraic ℚ α) {Ξ : Set ℕ}
    (hΞ : Ξ.Infinite) {q : ℕ → ℕ} (hq : ∀ n ∈ Ξ, 0 < q n)
    (hlog : Tendsto (fun n : ℕ ↦ Real.log (q n) / n) (atTop ⊓ 𝓟 Ξ) (𝓝 0))
    (htr : ∀ n ∈ Ξ, ∃ t : ℤ, t ≠ 0 ∧
      Algebra.trace ℚ ℚ⟮α⟯ (q n * AdjoinSimple.gen ℚ α ^ n) = t) :
    (∃ h : ℕ, 0 < h ∧ ∃ r : ℚ, α ^ h = r) ∨ IsIntegral ℤ α
theorem isIntegral_of_trace_mul_pow … : IsIntegral ℤ α
```

**Theorem 2 (p. 1).** `α > 0` a real quadratic irrational; `Real.cfPeriod x` is the length of
the (eventual) period of the continued fraction of `x` (a definition of this directory: the least
`r > 0` with `a (i + r) = a i` for all large `i`, `a` the partial quotients).

```lean
-- (a) neither a square root of a rational nor a unit: the period tends to infinity
-- (`α > 0` is not needed here)
theorem tendsto_cfPeriod_pow (hα : IsQuadraticIrrational α)
    (hsq : ∀ r : ℚ, α ^ 2 ≠ r) (hunit : ¬ (IsIntegral ℤ α ∧ IsIntegral ℤ α⁻¹)) :
    Tendsto (fun n ↦ cfPeriod (α ^ n)) atTop atTop
-- (b) a square root of a rational: along the odd powers
theorem tendsto_cfPeriod_pow_odd (hα : IsQuadraticIrrational α) (h0 : 0 < α)
    (hsq : ∃ r : ℚ, α ^ 2 = r) :
    Tendsto (fun n ↦ cfPeriod (α ^ (2 * n + 1))) atTop atTop
-- (c) a unit: the period is bounded
theorem bddAbove_cfPeriod_pow (hα : IsQuadraticIrrational α) (h0 : 0 < α)
    (hunit : IsIntegral ℤ α ∧ IsIntegral ℤ α⁻¹) :
    BddAbove (Set.range fun n ↦ cfPeriod (α ^ n))
```

**Appendix.** "Algebraic" cannot be dropped from Theorem 1:

```lean
theorem exists_frequently_not_isPisot :
    ∃ α : ℝ, 1 < α ∧ (∃ᶠ n : ℕ in atTop, |α ^ n - round (α ^ n)| ≤ 1 / 2 ^ n) ∧
      ∀ d, 0 < d → ¬ IsPisot (α ^ d)
-- with the closing remark: every such `α` is transcendental (from Theorem 1)
theorem exists_transcendental_frequently_not_isPisot :
    ∃ α : ℝ, 1 < α ∧ (∃ᶠ n : ℕ in atTop, |α ^ n - round (α ^ n)| ≤ 1 / 2 ^ n) ∧
      (∀ d, 0 < d → ¬ IsPisot (α ^ d)) ∧ Transcendental ℚ α
```

### Fidelity decisions, recorded before they are made twice

- **`Γ ≤ ℝˣ`, `δ ∈ ℝ`.** The paper takes `Γ ≤ Q̄ˣ`, `δ ∈ Q̄ˣ`, but `‖·‖` is defined only for
  reals and the proof (Lemma 3, `k ⊂ K ∩ ℝ`; the Main Theorem, `k₀ = K ∩ ℝ`) treats only real
  `u`. Every application in the paper has `u = αⁿ` real and `δ = 1`. Extending to complex `δ`
  (with `‖z‖ = min_n |z − n|`) looks routine and can be added later; complex `u` is not covered by
  the paper's proof.
- **`|q|` for `q`.** The paper writes `q^{-d-ε}` with `q ∈ ℤ`; `‖−x‖ = ‖x‖`, so `|q|` is the
  faithful reading, and `q = 0` is excluded by `|δqu| > 1`.
- **`d = [ℚ(u):ℚ]`.** The proof's inequality (2.1) carries `d = [k:ℚ]` for the field `k` the
  induction is at; the Main Theorem follows after passing to infinitely many `u` with the same
  `ℚ(u)` (finitely many subfields of `K`), which the paper leaves implicit.
- **Skolem–Mahler–Lech is not needed.** Lemma 4 applies it to `∑ aᵢ σᵢ(αʰ)ᵐ = 0` for infinitely
  many `m`. Lemma 2 (the unit equation) already gives `a σᵢ(αʰ)ᵐ + b σⱼ(αʰ)ᵐ = 0` for two
  distinct `m`, hence `σᵢ(αʰ)/σⱼ(αʰ)` is a root of unity, which is all the proof uses.
- **Lemma 4 is stronger than printed.** Its first alternative (`α ^ h ∈ ℚ`) comes from the case
  `d = 1`, where the paper's Lemma 1 has one term. The hypothesis of Lemma 1 then bounds the height,
  which `log qₙ = o(n)` contradicts just as well, so `α` is always an algebraic integer. Lemma 1 is
  needed at a *finite* place here (`LinearRelationFinite.lean`).
- **Continued fractions.** Mathlib has no periodicity theory. Theorem 2 needs Lagrange's theorem
  (quadratic irrationals are eventually periodic), purely periodic reduced numbers (Galois), the
  fixed-point quadratic of a purely periodic expansion, and the "Facts" of p. 9 (the periods of
  `|α|, |α'|, 1/|α|, 1/|α'|` agree). How much of Serret's theorem the Facts really need is to be
  settled at T2.1 below; the unit case (c) needs none of it, only the explicit expansions of p. 9.

## Plan

Layers bottom-up; each milestone a file (or two), each with its acceptance criterion.

**P. Vocabulary.**
- P.1 `PseudoPisot.lean`: `IsPseudoPisot`, `IsPisot`, the conjugate computations ported from
  `CITED/CorvajaZannierAlgebraic.lean` (`aroots_minpoly_ratCast_mul`, `exists_conjugate_ne`,
  `not_isPseudoPisot_mul_ratCast`, `isPseudoPisot_ratCast_iff`), `IsPisot → IsPseudoPisot`.
- P.2 Pisot powers are near integers: `IsPisot β → |βᵐ − round βᵐ| → 0`
  (trace of `βᵐ` is the power sum of the conjugates, an integer). Used by the Appendix and by the
  converse remark after Theorem 1.

**G. The Galois setting (§2, p. 2–3).**
- G.1 Given `Γ`, `δ`: a number field `K`, Galois over `ℚ`, with an embedding `K → ℂ`, containing
  `δ` and `Γ`, and a finite `Galois-stable` `S` with `Γ ⊆ O_S^×` (`exists_finset_le_unit`).
- G.2 Archimedean places as automorphisms, `|x|_ρ = |ρ⁻¹ x|^{d(ρ)/[K:ℚ]}`, and
  `∑_{v ∈ M_∞} d(ρ_v) = [K:ℚ]`, in Mathlib's normalization (`InfinitePlace.mult`); the product
  formula for `S`-units.
- G.3 Heights: `H(σ₁u, …, σ_d u) ≤ H(u)^{[K:ℚ]}`; `H(δ v) ≥ H(δ)⁻¹ H(v)`; `H(αⁿ) = H(α)ⁿ`.

**L. The lemmas of §2.**
- L.1 Lemma 1 (Evertse), from 6.2 `exists_finset_submodule_of_approxProd_le`.
- L.2 Lemma 2, from Corollary 7.4.3 (`NumberField.exists_finite_forall_exists_div_mem`) and
  pigeonhole.
- L.3 Lemma 3, the heart: the forms `x₀ − ρ_v(δ) xᵢ`, the product (2.4)–(2.6), 6.2 once, the
  Claim (Galois elimination of `p`), the two cases through Lemma 1, then Lemma 2 to land `u/δ'`
  in a proper subfield.
- L.4 Main Theorem: the descending chain of subfields, starting from the field `ℚ(u)` shared by
  infinitely many solutions.

**T1. Theorem 1.**
- T1.1 Lemma 4 (via Lemma 1 and Lemma 2, no Skolem–Mahler–Lech).
- T1.2 Theorem 1 from the Main Theorem (`q = 1`, `u = αⁿ`, `δ = 1`) and Lemma 4.

**T2. Theorem 2.**
- T2.0 Continued fractions of reals: partial quotients by `Int.fract` iteration, agreement with
  Mathlib's `GenContFract.of`, convergents, (4.1) and (4.2), `cfPeriod`.
- T2.1 Quadratic irrationals: Lagrange (eventual periodicity), reduced ⇒ purely periodic, the
  fixed-point quadratic, the Facts of p. 9 (or a route around them).
- T2.2 The unit case (c): the explicit expansions `[tₙ]` and `[tₙ − 1; 1, tₙ − 2]`.
- T2.3 Lemma 5, from the Main Theorem and Lemma 4.
- T2.4 Theorem 2 (a), (b).

**A. The Appendix.** Nested intervals `I_{n+1} ⊆ I_n^{b_{n+1}}`, `α ∈ ⋂ J_n`, and P.2 for the
non-Pisot conclusion; transcendence from Theorem 1.

**C. Certification.** A flat Challenge for this directory's theorems, a comparator config, and
`formalization.yaml`, as for the repository's own submission (`../COMPARATOR.md`).

## Status

| milestone | file | status |
| --- | --- | --- |
| P.1 | `PseudoPisot.lean` | done |
| G.1, G.2 | `GaloisSetting.lean` | done |
| L.1 Lemma 1 | `LinearRelation.lean` | done (general form and paper form) |
| L.2 Lemma 2 | `TwoTermRelation.lean` | done |
| L.3 Roth for a fixed `u` | `RothMultiples.lean` | done |
| L.3 conjugates, the first-case claim | `Conjugates.lean` | done |
| L.3 the Subspace step (2.5)–(2.7) | `SubspaceStep.lean` | done |
| L.3 Lemma 3 | `SubfieldDescent.lean` | done: `exists_lt_exists_mem_infinite_setOf_div_mem` (δ' = a member u₀), paper form `exists_lt_infinite_setOf_div_mem` |
| L.4 Main Theorem | `MainTheorem.lean` | **done**: `finite_setOf_not_isPseudoPisot` (std3 axioms only); number-field form `NumberField.finite_setOf_not_isPseudoPisot`, descent `NumberField.finite_of_finrank_le` |
| T1.1 Lemma 1 at a finite place | `LinearRelationFinite.lean` | done |
| T1.1 Lemma 4 | `IntegralPowerSums.lean` | done: number-field form `NumberField.isIntegral_of_mul_sum_pow_eq_intCast`, paper form `isIntegral_of_trace_mul_pow` / `isIntegral_or_exists_pow_eq_ratCast` |
| T1.2 Theorem 1 | `PisotPowers.lean` | done: `exists_isPisot_pow_of_frequently` (std3 axioms only) |
| T2.0 CF basics, convergents, (4.1), (4.2), Serret | `ContinuedFraction.lean` | done: `Real.cfTail`/`cfQuot`/`cfPeriod` (via Mathlib `GenContFract.of`), `tailEquiv_mob`, `abs_sub_cfNum_div_cfDen_le` |
| T2.1 Facts: Lagrange, Galois, conjugate period | `QuadraticIrrational.lean` | done: `IsQuadraticIrrational`, `quadConj`, `exists_isCFPeriod`, `IsReduced.cfTail_eq_self`, `cfPeriod_quadConj`, minpoly/aroots lemmas |
| T2.2 Theorem 2 (c) | `UnitPowers.lean` | done: `Real.bddAbove_cfPeriod_pow` |
| T2.3 Lemma 5 | `PartialQuotients.lean` | done: core `isPisot_of_exp_le_cfQuot`, `isPisot_or_tendsto_log_cfQuot(_odd/_of_mem)` |
| T2.4 Theorem 2 (a)(b) | `PeriodLength.lean` | done (std3): `Real.tendsto_cfPeriod_pow`, `Real.tendsto_cfPeriod_pow_odd`; the Proposition `isPisot_of_cfPeriod_le`, `abs_sub_quadConj_le` |
| P.2 | `PisotNearInteger.lean` | done (std3): `IsPisot.tendsto_abs_sub_round`, via `sum_aroots_pow_eq_trace` (power sums of conjugates are traces) |
| A Appendix | `Appendix.lean` | done (std3): `Real.exists_frequently_not_isPisot`, `Real.exists_transcendental_frequently_not_isPisot` (`I₀ = [2, 5/2]`; `Jₙ` as a preimage, no roots) |
| C Certification | `comparator/corvaja-zannier-2004.{txt,json}`, `ChallengeCorvajaZannier2004.lean`, `SolutionCorvajaZannier2004.lean`, `formalization.yaml` | done: 11 theorems, comparator passes (`lake test -- comparator/corvaja-zannier-2004.json`); flat Challenge 229 lines, 11 KB, generated by `scripts/make-challenge.py --paper CorvajaZannier2004`; negative control rejected |

All done files are sorry-free and pass `lake build` with the linters.

### How T2.4 was proved

- **The Proposition** (`isPisot_of_cfPeriod_le`): the paper's reduction (4.6) is replaced by
  `z = βⁿ − (⌊β'ⁿ⌋ + 1)`, reduced once `βⁿ − β'ⁿ > 2`, hence purely periodic with period `r`
  and partial quotients among `a₁(βⁿ), …, a_r(βⁿ)`. `|z − z'| ≤ 4 ∏ (aᵢ + 1) = e^{o(n)}` (Lemma 5)
  contradicts the gap `c βⁿ`.
- **(b)**: `β' = −β`, so for odd `n` the gap is `2βⁿ` (`c = 1`); Pisot contradicts `|β'| = β > 1`.
  `α < 1` is reduced to `1/α`.
- **(a)**: `γ₁` is whichever of `α, α'` has the larger absolute value (`|α| ≠ |α'|` since `α²`
  is irrational). The Proposition, applied to `|γ₁|` (if `> 1`) and then to `|1/γ₁'|`, gives `γ₁`
  and `1/γ₁'` integral; the conjugate of an integral quadratic irrational is integral, so `α` is a
  unit. Signs are handled by `tailEquiv_neg`, periods of conjugates by `cfPeriod_quadConj`.

### How L.4 was proved

1. **Descent** (`NumberField.finite_of_finrank_le`): strong induction on `[k:ℚ]` with the exponent
   `d ≥ [k:ℚ]` fixed. Step: Lemma 3 gives `k' < k` and a member `u₀`; the family `(q, u/u₀)` with
   `δ u₀` and `C H(u₀)^ε` is infinite at `k'`, since `H(u/u₀) ≤ H(u) H(u₀)`.
2. **Number field** (`NumberField.finite_setOf_not_isPseudoPisot`): pigeonhole on `ℚ⟮u⟯` over the
   finitely many intermediate fields; `ℚ⟮u⟯` is real because `NumberField.realField φ` is an
   intermediate field.
3. **Transfer to ℝ**: a Galois `K ⊆ ℂ` containing `δ` and the generators of `Γ`; `S` from the
   conjugates of the generators (`exists_finset_le_unit`); each `u ∈ Γ` lifts to `w ∈ K` all of
   whose conjugates are `S`-units (closure induction); heights by `NumberField.absMulHeight₁_map`,
   degrees by `minpoly.algHom_eq`.
