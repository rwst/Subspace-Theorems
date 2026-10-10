# Bugeaud 2013: automatic continued fractions are transcendental or quadratic

Y. Bugeaud, *Automatic continued fractions are transcendental or quadratic*, Ann. Sci. Éc. Norm.
Supér. (4) **46** (2013), 1005–1022. (Local copy: `~/math/lean-code/Bugeaud2013.pdf`.)

This directory is for formalizing the whole paper on top of the libraries of this repository.
It is its own `lean_lib` (`Bugeaud2013`), held to the same rules (no `sorry`, no `set_option`,
std3 axioms, fine-grained imports, module system, Mathlib root namespaces).

`outgoing.md` records a follow-up that goes beyond the paper: the value of `δ` in (6.1), which
Bugeaud announced but never wrote out.

## The library

| file | content |
| --- | --- |
| `Convergents.lean` | §2: the convergents `p_ℓ / q_ℓ` of a sequence of positive integers, (2.1), the determinant, `p_ℓ ≤ q_ℓ`, monotonicity, (2.3), the mirror formula (2.4) |
| `Subspace.lean` | Theorem 2.1 for real algebraic forms; the step "small products ⇒ a non-zero rational relation infinitely often" |
| `Spade.lean` | Condition `(♠)` (`Function.IsSpade`); its lengths, normalized: `w ≥ 1`, `a_w ≠ a_{w+u+v}` for `w ≥ 2` (`Nat.SpadeData`) |
| `Estimates.lean` | §3: the point `v_n` (`Nat.spadeVec`), the completed sequence `b^{(n)}`, (3.1)–(3.4), the products `≤ 96 · 2^{-u}` |
| `Claim.lean` | rigidity `|A| ≥ q_{w+r-1}` from `a_w ≠ a_{w+r}`; **the Claim** of the second case |
| `Stammering.lean` | the two Subspace applications at `v_n` ((3.5), (3.17)) |
| `FirstCase.lean` | the first case: `β`, its irrationality, (3.9)–(3.12), the quadratic equation |
| `Lagrange.lean` | `α` determines `a`; **Lagrange**: quadratic ⇒ eventually periodic |
| `Theorem31.lean` | the case split; **Theorem 3.1** (`Nat.transcendental_contFrac_of_isSpade`) |
| `Theorem11.lean` | §4: `(♠)` from periodic segments, bounded `a_ℓ` ⇒ `q_ℓ^{1/ℓ}` bounded; **Thm 1.1** (`Nat.eventually_lt_encard_factors`, `Nat.tendsto_complexity_div_atTop`) |
| `Theorem12.lean` | algebraic + automatic ⇒ eventually periodic; **Thm 1.2** (`Nat.not_isAutomatic_of_three_le_natDegree`) |
| `Theorem14.lean` | quasi-periodic sequences (`Nat.IsQuasiPeriodic`), their `(♠)` repetitions; **Thm 1.4** (`Nat.transcendental_contFrac_of_isQuasiPeriodic`) |
| `Mirror.lean` | mirror images of continuants: `q_N(c_N … c_1) = q_N`, `p_N(c_N … c_1) = q_{N-1}`; a finite continued fraction with the prefix of `α` is within `3 q_m⁻²` |
| `Club.lean` | Condition `(♣)` (`Function.IsClub`); its lengths, normalized: `w ≥ 1` (`Nat.ClubData`) |
| `ClubEstimates.lean` | §5: `P/Q = [0; W U V Ū rev(W)]`, the point `(Q, Q', P, P')`, (5.1)–(5.3), the products `≤ 1332 (q_r/q_s)²`, `≤ 222 q_r/q_s`, and `≤ H^{-ε}` |
| `Palindromic.lean` | the two Subspace applications of §5, the limit argument; **Thm 5.1** (`Nat.transcendental_contFrac_of_isClub`) |
| `Theorem13.lean` | Condition `(∗)` (`Function.IsStar`); **Thm 1.3** (`Nat.transcendental_contFrac_of_isStar`) |
| `SevenThirds.lean` | §6: `7/3`-powers and overlaps; Thue–Morse desubstitution of `7/3`-power-free binary words; **the `U^{7/3}` remark** (`Nat.frequently_hasSevenThirdsPowerAt`, `Nat.frequently_hasOverlapAt`) |
| `Value.lean` | §§2–3: `α = [0; a₁, a₂, …]` (`Nat.contFrac`), `p_ℓ/q_ℓ → α`, `α` strictly between consecutive convergents, (2.2), `α ∈ (0, 1)` irrational, the common-prefix estimate behind (3.1), the tail formula, the polynomial `P_n` of §3 with non-zero leading coefficient, Euler (eventually periodic ⇒ quadratic) |

## The paper

| § | result | content |
| --- | --- | --- |
| 1 | **Thm 1.1** | `[0; a₁, a₂, …]` algebraic, `a` not eventually periodic ⇒ `p(n, a)/n → ∞` |
| 1 | **Thm 1.2** | the continued fraction of an algebraic number of degree `≥ 3` is not automatic |
| 1 | **Thm 1.3** | `(q_ℓ^{1/ℓ})` bounded and Condition `(∗)` ⇒ transcendental (= Thm 3.1 ∪ Thm 5.1) |
| 1 | **Thm 1.4** | quasi-periodic continued fractions with `liminf λ_{k+1}/λ_k > 1` |
| 2 | (2.1)–(2.4), Thm 2.1 | convergents, `|q_ℓ α - p_ℓ| < q_{ℓ+1}⁻¹`, `q_{ℓ+h} ≥ q_ℓ √2^{h-1}`, the mirror formula; Schmidt's Subspace Theorem |
| 3 | **Thm 3.1** | Condition `(♠)` (stammering, `W U V U`) ⇒ transcendental |
| 4 | proofs of Thms 1.1, 1.4 | Schubfachprinzip on the prefix of length `(C+1)n` |
| 5 | **Thm 5.1** | Condition `(♣)` (quasi-palindromic, `W U V Ū`) ⇒ transcendental |
| 6 | remarks | `U^{7/3}` in binary algebraic continued fractions; (6.1), see `outgoing.md` |

## Plan

### What the repository already has

- **Theorem 2.1** (Schmidt): `DiophantineApproximation/SubspaceAlgebraic.lean` (DA 6.3) and
  `SubspaceTheorem.lean`.
- **Complexity**: `DiophantineApproximation/FactorComplexity.lean` (`complexity`, `factors`,
  Morse–Hedlund `lt_complexity`, `exists_periodic_of_frequently_complexity_le`), and
  `StammeringWords.lean` (`IsEventuallyPeriodic`, `IsStammeringWith`). Words there are indexed
  from `0`; the paper's `a₁ a₂ …` is `fun k ↦ a (k + 1)`.
- **Cobham's bound** `p(n) = O(n)` for automatic sequences and `Function.IsAutomatic`:
  `AdamczewskiBugeaud2007/AutomaticComplexity.lean`. Thm 1.2 needs it; either import that
  library or move the two files to `ForMathlib` first (preferred).
- **Continued fractions of a real number** (`Real.cfTail`, `Real.cfQuot`, `Real.cfNum`,
  `Real.cfDen`, `IsQuadraticIrrational`): `CorvajaZannier2004/ContinuedFraction.lean`,
  `QuadraticIrrational.lean`. Those start from `x`, the paper starts from the sequence `a`. Here
  the convergents are defined from `a` (`Nat.contNum a`, `Nat.contDen a`). The paper never goes
  from a real number to its partial quotients, so no bridge to `Real.cfQuot` is needed; it would
  also make this library import another paper library.

### Work packages

- **WP1, §2 convergents** (`Convergents.lean`). **Done.**
- **WP2, the value** (`Value.lean`). **Done.** `Nat.contFrac a = lim p_ℓ/q_ℓ`; (2.2); `α ∈ (0, 1)`
  irrational; common prefix `a₁ … a_ℓ` ⇒ `|α - α'| < 2 q_ℓ⁻²` (`abs_contFrac_sub_contFrac_lt`, for
  (3.1)); `contFrac_isRoot` = `P_n(α_n) = 0` for a sequence periodic from index `w + 1` (`w ≥ 1`;
  the case `w = 0` needs `p_{-1}, q_{-1}` and is left to WP3), `contDen_mul_contDen_ne` = its
  leading coefficient is non-zero; `exists_quadratic_of_isEventuallyPeriodic` (Euler). Proved from
  scratch: lean-code's `Lagrange.lean` works with Mathlib's `GenContFract` and was not needed.
- **WP3, Thm 3.1**. **Done.** Deviations from the paper, all in the direction of more detail:
  - the repetitions are normalized once, before the Subspace Theorem (`Spade.lean`): sliding
    `W U V U` left until `a_w ≠ a_{w+u+v}` serves the second case, and the trick
    `U V U = U₁ · U' · (V U₁) · U'` removes `w = 0`, where (3.5) would need `p_{-1}, q_{-1}`;
  - in the first case the paper shifts `α` to make `w_n = 0`; here the shift is a change of
    coefficients `x ↦ Y` (invertible since `p_j q_{j+1} - p_{j+1} q_j = ±1`), for every `ℓ ≥ 1`;
  - (3.8) is proved without limits: `D (q_M - β q_{M+1}) = Y₃ e_{M+1} + Y₄ e_M` with
    `e_ℓ = q_ℓ α - p_ℓ`, so `|β q_{M+1} - q_M| ≤ K / q_{M+1}`;
  - the Claim works with the integer `A = q_w q_{w+r-1} (Q_n - 1)`: rigidity `|A| ≥ q_{w+r-1}`
    (for `w ≥ 3`) and the case `Q_n ≥ 2` give `q_{w-1} q_{w+r} ≤ 2 q_w |A|`, hence
    `|x₁ + (x₂+x₃) α + x₄ α²| ≤ 12 (|x₂| + |x₃| + |x₄|) / q_{w-1}`;
  - the explicit `ε = 1 / (4 (K + 1) (C + 1))` for `q_ℓ ≤ 2^{K ℓ}`, `w + v ≤ C u`;
  - "transcendental" needs Lagrange's theorem (quadratic ⇒ eventually periodic), which the paper
    takes as known; it is proved in `Lagrange.lean`.
- **WP4, §4, Thms 1.1, 1.2**. **Done.** Deviations from the paper:
  - the Schubfachprinzip is not redone: `Function.exists_periodic_of_frequently_complexity_le`
    (AB07 §4, `DiophantineApproximation/FactorComplexity.lean`) gives periodic segments with a
    re-cut period, and `Function.hasSpadeRepetitions_of_periodic` reads `W U V U` off them; the
    paper's case split `|W_n X_n| ≤ |W'_n|` is not needed;
  - `Function.complexity` is `Set.ncard`, which is `0` for an unbounded sequence, so Thm 1.1 is
    stated twice: with `Set.encard` and no finiteness (`p(n, a) > C n` eventually, every `C`), and
    as `p(n, a) / n → ∞` for a sequence with finitely many values;
  - Thm 1.2 takes "degree at least three" as `3 ≤ (minpoly ℚ α).natDegree` and goes through
    `Nat.isEventuallyPeriodic_of_isAutomatic` (algebraic + automatic ⇒ eventually periodic) and
    Euler; Cobham's bound is imported from `AdamczewskiBugeaud2007/AutomaticComplexity.lean`
    (only `Theorem12.lean` imports another paper library; automaticity = finite `k`-kernel).
- **WP5, Thm 1.4** (quasi-periodic). **Done.** Deviations from the paper:
  - bounded `(r_k)` is not delegated to Corollary 3.3 of [4]: the §4 argument only needs
    `r_h ≤ R r_k` for all `h < k`, for infinitely many `k` (records when `(r_k)` is unbounded,
    every `k` when it is bounded), so Theorem 3.1 covers both cases;
  - `liminf λ_{k+1}/λ_k > 1` is stated as `∃ ε > 0, ∀ᶠ k, (1 + ε) λ_k < λ_{k+1}` (`Filter.liminf`
    on `ℝ` has a junk value when the ratios tend to `∞`); `|W_k| ≤ n_{k₀} + R r_k λ_k / ε` is an
    induction on `k`, not a geometric sum;
  - `U_k` (period `⌊λ_k/2⌋ r_k`) is fed to `Function.hasSpadeRepetitions_of_periodic` with `w = 2`.
- **WP6, §5, Thm 5.1, Thm 1.3**. **Done.** The paper only lists the changes to the proof of
  Theorem 2.4 of [5] (Adamczewski–Bugeaud, *Palindromic continued fractions*, Ann. Inst. Fourier
  2007; Theorem 3 of arXiv:math/0512014) and omits the end. Reconstruction:
  - `w = 0` is removed as for `(♠)`: the first letter of `U` moves into `W`
    (`W U V Ū = (W x) U' V Ū' x`), so [5]'s separate Theorem 2 is not needed;
  - (5.1)–(5.3) are proved with explicit constants (`3` for `≪`); (5.2) needs the mirror formula
    in integers and (5.3) the mirror symmetry of continuants (`Mirror.lean`), proved from the tail
    formula without matrices;
  - first application: forms `L₂, L₃, L₄, L₅` at `(Q, Q', P, P')`, product
    `≤ 1332 (q_r/q_s)²`; the limit (`Q'/Q, P/Q → α`, `P'/Q → α²`) gives `Q' = P` infinitely often;
  - second application ("we omit the details"): forms `α²X₁ - 2αX₂ + X₃, αX₂ - X₃, X₁` at
    `(Q, Q', P')`, product `≤ 222 q_r/q_s`; the limit of the relation is a quadratic equation for
    `α`, which ends the proof (as at the end of [5, Theorem 2]);
  - the explicit `ε = 1 / (16 (M + 1))`, `M = 2K(C + 1) + 1`, for `q_ℓ ≤ 2^{K ℓ}`, `w + v ≤ C u`;
  - Thm 1.3: infinitely many `n` of one of the two kinds, then a subsequence.
- **WP7, §6**. **Done** (the `U^{7/3}` remark). [11] (Adamczewski–Rampersad, Proc. AMS 136
  (2008)) was not at hand; its argument is reconstructed. Deviations from the paper:
  - "arbitrarily large blocks `U` such that `U^{7/3}` occurs" is proved in the form of [11]:
    `7/3`-powers occur at infinitely many positions. The argument only excludes a suffix with no
    `7/3`-power at all (it uses the short powers `xxx`, `ababa`, `baabaab`), so it does not bound
    the periods from below;
  - Restivo–Salemi / Karhumäki–Shallit are not cited: the desubstitution `s = u μ(y)` is proved
    directly, with `|u| ≤ 5` instead of `≤ 2` (the squares `s_i = s_{i+1}`, `i ≥ 1`, all have the
    same parity); iterating gives squares of period `P ≥ 2^k` at positions `≤ 9 P`, so Theorem 3.1
    (with `V` empty) suffices and Theorem 5.1 is not needed; `m < M` is not needed;
  - corollary: infinitely many overlaps;
  - not formalized: the transcendence measures of [17] (only cited) and (6.1) with the bound
    `p(n, a) ≥ (1 + 1/M) n`, announced without proof (`outgoing.md` has a sketch for (6.1)).

## Status

WP1–WP7 done (std3; `#lint` clean). Theorem 3.1 is `Nat.transcendental_contFrac_of_isSpade`,
Theorem 1.1 is `Nat.eventually_lt_encard_factors` / `Nat.tendsto_complexity_div_atTop`, Theorem 1.2
is `Nat.not_isAutomatic_of_three_le_natDegree`, Theorem 1.4 is
`Nat.transcendental_contFrac_of_isQuasiPeriodic`, Theorem 5.1 is
`Nat.transcendental_contFrac_of_isClub`, Theorem 1.3 is `Nat.transcendental_contFrac_of_isStar`.
The §6 `U^{7/3}` remark is `Nat.frequently_hasSevenThirdsPowerAt` (with the deviation above);
(6.1) is not formalized (announced without proof in the paper).
