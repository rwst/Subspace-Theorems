# Schlickewei 1990: `S`-unit equations over number fields

H. P. Schlickewei, *`S`-unit equations over number fields*, Invent. Math. **102** (1990), 95–107
(the copy read: `~/math/lean-code/papers/Schlickewei1990.pdf`, 13 pages).

**Status: S90.0–S90.6 done (2026-10-16): S90-A, Theorem 1.1 with a `log log` term, is proved
(`NumberField.ncard_unitSolutions_le`); S90-B waits for QS Q4.4.** The directory is its own
`lean_lib` (`Schlickewei1990`), held to the same rules as the other paper directories (no
`sorry`, no `set_option`, std3 axioms, fine-grained imports, module system, Mathlib root
namespaces), and is in the gates' library lists. Its comparator lane
(`comparator/schlickewei-1990.txt`, `ChallengeSchlickewei1990.lean`,
`SolutionSchlickewei1990.lean`, `formalization.yaml` here) comes later;
see `COMPARATOR.md`, *Formalized papers*.

**House rule for this paper: no paper library imports another.** Anything taken from another
paper directory (here `Evertse1984/`) is moved into `DiophantineApproximation/` or
`QuantitativeSubspace/` first, and that paper's files import it from there (milestone S90.0).
General lemmas this paper needs that are not specific to the unit equation go to DA or QS too,
not here.

## Why this paper

It is the first **count** of the solutions of a Diophantine equation, and it turns two landed
pieces into one: DA 8.2 (`UnitEquationSeveral.lean`, finiteness of the unit equation) and the
quantitative Subspace Theorem of QS (Q0.3, Q4.3). Nothing in the repository counts unit-equation
solutions. `QuantitativeSubspace/README.md` lists it under *Consumers*. See `../formalize.md`, A1.

## The results of the paper

`M(K)` the places of `K`, `‖·‖_v = |·|_v ^ (d_v / d)` (the product-formula normalization), `S ⊇
M_∞(K)` finite with `s` elements, `d = [K : ℚ]`.

| Result | Statement | Proof uses |
|---|---|---|
| **Thm 1.1** | `a₁ x₁ + ⋯ + aₙ xₙ = 1` has at most `(4 s d!) ^ (2 ^ (36 n) · s⁶)` solutions in `S`-units with no vanishing proper subsum | Lemma 6.1, induction on `n` (§7) |
| (1.6) | the same count for projective solutions of `α₁ x₁ + ⋯ + α_{n+1} x_{n+1} = 0` | equivalent to Thm 1.1 |
| Thm 2.1, Cor. 2.2 | Sch92's quantitative Subspace Theorem, product form; count `(4 s d!) ^ (2 ^ (36 n d!) s⁶)`, threshold `max ((n!)^8, H(L)^{…})` | cited |
| Lemma 3.1 | outside `t₃ = (n+1)^s (4sd!)^{…}` proper subspaces of `U = {y₁ + ⋯ + y_{n+1} = 0}`, `H(y') ≤ max ((n!)^18, n^{9ns(d!)²}, A² n^{3n+2})` | Cor. 2.2 with `δ = 1/2`, per class |
| (3.6) | `A = ∏_{v∈S} ‖α₁‖_v ⋯ ‖α_{n+1}‖_v · ∏_{v∉S} (max_i ‖α_i‖_v)^{n+1}`, `A ≥ 1` by the product formula | — |
| (3.20) | in the class of `(i(v))_{v∈S}`: `∏_{v∈S} ∏_{i ≠ i(v)} ‖L_i(y')‖_v / (‖L_i‖_v ‖y'‖_v) ≤ A n^{3n+1} H(y')^{-n-1}` | (3.11) product formula, (3.18)–(3.19) |
| Lemma 4.1 | the simplex net: `≤ 2 ^ (q / (1 − γ))` points `Γ` of `{∑ Γ_i = γ, Γ_i ≥ 0}` such that every `x ∈ ℝ^q_{≥0}` has `x_i ≥ Γ_i ∑ x` | Sch92 Lemma 5.1 (Mahler) |
| Lemma 4.2 | **gap principle**: for `B ≥ n^{9n}`, `C = A ^ (1 / (2(n² − 1)))`, the solutions with `B ≤ H(y') ≤ B C` lie in `≤ (n+1)^{2s} 2^{2n² s}` proper subspaces of `U` | (4.6) `D_j = D₁`, (4.7), subclasses by `k(v)` and `Γ`, the determinant of `n` solutions |
| Lemma 5.1 | the number of points of `ℙ^{n−1}(K)` of height `< D` is `≤ n · 36^{n−1} 2^{2d(n−1)} D^{2d(n−1)}` | Schmidt's lecture notes, Lemma 8B |
| Lemma 5.2 | the solutions with `H(y') < n^{9ns(d!)²}` lie in `t₅` proper subspaces | Lemma 5.1 |
| Lemma 5.3 | the solutions with `n^{9n} ≤ H(y') < A² n^{3n+2}` lie in `4(n² − 1) (n+1)^{2s} 2^{2n² s}` proper subspaces | Lemma 4.2 on `4(n² − 1)` windows |
| Lemma 6.1 | all solutions lie in `2 (n+1)^s (4sd!)^{…}` proper subspaces of `U` | 3.1 + 5.2 + 5.3 |
| §7 | a solution in a proper subspace `V ⊂ U` satisfies a shorter relation `∑_{i∈J} β_i x_i = 0` with no vanishing subsum; `≤ 2ⁿ Z(n−1)²` projective solutions per `V` | induction hypothesis twice |

## The obstacle: the threshold, not the count

Sch90's count depends on `n`, `d`, `s` only. That uniformity comes from Cor. 2.2: Sch92's
**threshold** is free of the field. The repository's counts above the threshold
(`exists_finset_submodule_of_efSystemThreshold_le`, Q4.3, and Q0.3's) are free of the field too
(`efLargeCount` sees `n`, `[E : K]`, `R`, `δ` only). But their threshold `efSystemThreshold` is
linear in `log |D_K|` and `∑_{p∈S} log N(p)` (`scalarConst`, Minkowski over `K`;
`efSystemThreshold_le`). The large solutions below it cost one interval of DA 9.4, i.e.
`O((n / δ) log X₀)` subspaces (`systemMiddleRatio` in
`exists_finset_submodule_of_isNormalizedSystem_ef`).

So, with what is landed, Lemma 6.1's count comes out as

`Z(n, s) + c(n) · log (log |D_K| + ∑_{p∈S} log N(p) + 2)`,

and Theorem 1.1's as a power of it, `C(n, s) (1 + log M) ^ (2 ^ (n + 1) − 1)` with
`M = log |D_K| + ∑_{p∈S} log N(p) + 2`, because §7 squares the count at every step (S90.6). Both
are independent of the coefficients `a` (Evertse–Győry's uniformity, now explicit), but not
of `K` and `S` beyond `d`, `s`. Removing the `log log` term is exactly **QS Q4.4** (EF13's count
above `max (2H, n^{2n/δ})`), which is open. Sch90 is its second consumer after BE08 Cor. 5.2.
Lemma 4.2 cannot bridge the gap: its windows have ratio `A^{1/(2(n²−1))}`, so it covers only up
to `A² n^{3n+2}`, which is where Sch90 needs it.

**Decision: two theorems of record.**

- **S90-A ✅ (2026-10-16).** The count above, with the `log log` term. Every step uses only
  landed DA/QS results.
- **S90-B (Sch90 as printed, after Q4.4).** The count depends on `n`, `d`, `s` only. Once Q4.4
  lands, S90-A's proof gives it without changes except for the threshold call.

The `d!` disappears in both. The forms (3.7) have rational coefficients, so the Galois extension
`E / K` that Q0.3 and Q4.3 require can be `K` itself (`IsGalois K K`), and Sch90's detour through
the normal closure (Cor. 2.2) is not needed.

## Milestones

- **S90.0 ✅ (2026-10-16) — moves into DA** (per the house rule), recorded as DA 8.8:
  - `Evertse1984/PlaceProd.lean` → `DiophantineApproximation/PlaceProd.lean`, whole
    (`placeProd`, `relevantPlaces` and their API, `one_le_placeProd_univ`,
    `mulHeight_le_iSup_house_pow`, `exists_pos_forall_le_of_finite`);
  - `Evertse1984/SumForms.lean` split: `sumForms`, `linearIndependent_sumForms`,
    `prod_sumForms_mul`, `affineProd_sumForms_mul` → `DiophantineApproximation/SumForms.lean`.
    Evertse's Subspace step (`exists_finset_submodule_of_prod_placeProd_le`) stays in
    `Evertse1984/SumForms.lean`;
  - Evertse's minimal subsum `exists_subset_sum_eq_forall_ne_zero` → DA 8.2's
    `UnitEquationSeveral.lean`, where `exists_subset_sum_eq_one_forall_ne_zero` is now its
    two-line special case. (`PlaceProd.lean` cannot host it: it imports 8.6, which imports 8.2.)

  Declaration names are unchanged, so only imports moved. `lake build` is clean, all std3
  (`#print axioms`). `ChallengeEvertse1984.lean` was regenerated (only `placeProd`'s owning
  module changed; 317 lines), and `lake test -- comparator/evertse-1984.json` passes. The
  class decomposition (3.12) is Evertse's `r : AbsoluteValue K ℝ → Option ι`; Sch90's forms
  (3.7) at `v` are `sumForms r v`, with `r v = some (i(v))`, or `none` when `i(v) = n + 1`.
- **S90.1 ✅ (2026-10-16) — the statement and the projective dictionary.**
  `Schlickewei1990/ProjectiveSolutions.lean` (std3):

  ```lean
  def NumberField.projUnitSolutions [Nonempty ι] (S : Finset (HeightOneSpectrum (𝓞 K)))
      (α : ι → K) : Set (Projectivization K (ι → K))

  theorem NumberField.projUnitSolutions_eq_image (S) (h0 : α none ≠ 0) :
      projUnitSolutions S α =
        homogenizeMk '' unitSolutions S (fun i ↦ -α (some i) / α none)

  theorem NumberField.ncard_projUnitSolutions (S) (h0 : α none ≠ 0) :
      (projUnitSolutions S α).ncard = (unitSolutions S (fun i ↦ -α (some i) / α none)).ncard

  theorem NumberField.finite_projUnitSolutions (S) (hα : ∀ o, α o ≠ 0) :
      (projUnitSolutions S α).Finite
  ```

  `α : Option ι → K`, with `none` the coordinate `x_{n+1}`. A projective solution has
  `x_{n+1} ≠ 0`, an `S`-unit, so it has the representative `(x₁ / x_{n+1} : ⋯ : 1)`.
  `homogenizeMk x = (x₁ : ⋯ : xₙ : 1)` is injective. A proper subsum of (1.6) containing
  `x_{n+1}` vanishes iff its complement does, and the complement is a subsum of (1.4). Only
  `α_{n+1} ≠ 0` is needed for the dictionary. Finiteness needs all `αᵢ ≠ 0` (DA 8.2's
  `finite_unitSolutions`). The theorems of record are stated with `projUnitSolutions`, so that
  the induction of §7, which shortens (1.6) to relations `∑_{i∈J} βᵢ xᵢ = 0`, stays in one
  shape.

  The change of variables (3.1)–(3.3) needs no lemma of its own: `∏_{v∈S} ‖αᵢ xᵢ‖_v =
  ∏_{v∈S} ‖αᵢ‖_v` is `placeProd_univ_mul_unit`. That lemma and the `S`-product formula
  `placeProd_univ_eq_one_of_mem_unit` (with `mulHeight_le_placeProd_univ`) moved from
  `Evertse1984/Normalization.lean` to `DiophantineApproximation/PlaceProd.lean` under the house
  rule.
- **S90.2 ✅ (2026-10-16) — the product inequality per class (3.11)–(3.20).**
  `Schlickewei1990/ProductInequality.lean` (std3):

  ```lean
  theorem NumberField.exists_unitClass [Finite ι] (S) (y : Option ι → K) :
      ∃ r : AbsoluteValue K ℝ → Option ι,
        (∀ v ∈ relevantPlaces S, v (y (r v)) = ⨆ o, v (y o)) ∧
          ∀ v ∉ relevantPlaces S, r v = none

  theorem NumberField.affineProd_sumForms_mul_mulHeight_some_le (S) (r)
      (hα : ∀ o, α o ∈ S.integer K) (hα0 : ∀ o, α o ≠ 0) (hx : ∀ o, x o ∈ S.unit K)
      (hsum : ∑ o, α o * x o = 0)
      (hr : ∀ v ∈ relevantPlaces S, v (α (r v) * x (r v)) = ⨆ o, v (α o * x o)) :
      affineProd S (fun v ↦ v) (sumForms r) (fun i ↦ α (some i) * x (some i)) *
          mulHeight (fun i ↦ α (some i) * x (some i)) ≤
        ∏ o, placeProd S Set.univ (fun v ↦ v (α o))
  ```

  (and `affineProd_sumForms_mul_mulHeight_le`, the same with the height of `y = α x`).
  Three departures from the paper, all simplifications:
  - **Unnormalized.** The statement is in the `affineProd` form that Layer 6.4 and Q4.3 take:
    the forms are not divided by `‖L‖_v ‖y'‖_v`, so the exponent is `−1` and not `−n − 1`, and
    (3.18)–(3.19) with their `n^{3n+1}` are not needed. Only `H(y') ≤ H(y)` is used
    (`Height.mulHeight_comp_le`).
  - **`S`-integral coefficients.** Then `y = α x` is `S`-integral, `H(y)` is at most its
    `S`-product (`mulHeight_le_placeProd_univ`), and the constant is
    `A' = ∏ᵢ ∏_{v∈S∞∪S} ‖αᵢ‖_v`. (3.6)'s factor `∏_{v∉S} max ‖αᵢ‖_v` is `≤ 1` and is dropped.
    Clearing denominators does not change `projUnitSolutions`; S90.3 does that reduction.
  - **The identity needs no class.** On the hyperplane, the product of the sum forms times
    `∏ ‖y_{r v}‖_v` is the product of all the coordinates for *every* `r`
    (`affineProd_sumForms_mul_eq_prod_option`, DA 8.8, (3.11)/(3.14)); the class (3.12) is only
    used to identify `∏ ‖y_{r v}‖_v` with the `S`-product of the sup norms (3.15). The classes are
    `r` with `r v = none` off `S∞ ∪ S` (`exists_unitClass`), `(n+1)^s` of them (3.13).

  **Checked (2026-10-16): affine against projective height, and what it costs.** Q4.3's
  `systemSet` takes `S`-integral points, measures them by `mulHeightAff`, and its normalization
  `IsNormalizedSystem` asks `max_i c p i = s(p)` with `∏ C p ≤ |det|^{1/n}`. That is a condition
  on the **representative** of the projective point (DA `SubspaceSystem.lean`, implementation
  notes), so each solution has to be moved first, and every constant the move costs ends up in
  the threshold of the Subspace step. Findings:

  1. **Moving by an `S`-unit is ruled out** (Lemma 7.5.4,
     `exists_forall_logHeightAff_smul_le`). Its constant `C₀ = (M + 1) ∑ ‖Bᵢ‖`, for *some* basis
     of the `S`-unit lattice, is only known to exist and is of the size of the `S`-regulator. In
     the count it would cost `log C₀ ≈ ½ log |D_K|`, not `log log`, and it is not explicit. It
     also meets the normalization only up to a constant.
  2. **Moving by one Minkowski scalar works** (`exists_ne_zero_systemAbs_le`, the same tool
     Q4.3's large step uses). The scalar `β` is balanced up to
     `κ = scalarConst K S = 2^d ∏_{q∈S} N(q) √|D_K|`. Pushing the excess `κ` to one finite place
     `P₀ ∈ S` (where `β y'` is made `< 1/κ`, free in `H_aff`) gives constants `κ^{s(w)}`, `κ⁻¹`,
     `1` of **product exactly `1`**. So every solution satisfies the normalization with the
     *same* constants, and (3.20) holds against `H_aff` at the cost `κ^{n+2}`. A set `S` without
     a finite place gets one prime first (`s → s + 1`).
  3. **The coefficients must be normalized too.** The representative is `S`-integral, so it
     sees the common ideal `𝔞` of `α` outside `S`. Our constant `A' = ∏ᵢ ∏_{S∞∪S} ‖αᵢ‖` is
     Sch90's (3.6) `A` times `N(𝔞)^{n+1}`, which is unbounded in `α`. Minkowski's bound on ideal
     classes fixes it: one multiplier `c` makes `c α` integral with ideal of norm
     `≤ 2^d √|D_K|`. Then `∏_{S∞∪S} max ‖yᵢ‖ ≤ 2^d √|D_K| · H(y)` for every solution `y`
     (`placeProd_iSup_le_mul_mulHeight`). With it, `A' ≤ (2^d √|D_K|)^{n+1} A`.
  4. **What remains: the range between the two thresholds, for S90.4.** The Subspace step now
     starts at `H(y') ≈ (Λ A)^{O(1)}` with `Λ = κ^{O(n)}`, explicit in `d`, `|D_K|` and `N(q)`.
     Sch90's starts at `A² n^{3n+2}`. Lemma 4.2's windows `[B, B A^{1/(2(n²−1))}]` cover up to
     `A² n^{3n+2}` in `4(n² − 1)` windows, but **not** the range `[A², (Λ A)^{O(1)}]` when `A` is
     close to `1` (`A = 1` for `S`-unit coefficients). The same determinant argument
     (4.14)–(4.19) with `γ = 1 − 1/(4(n+1))` and windows `[B, B^{1+1/(4n)}]` gives
     `∏_v ‖D₁‖_v ≤ n! n^{n+2} A^{−(1−γ)} H(y'₁)^{−1/2} < 1` for `B ≥ (n! n^{n+2})²`, uniformly
     in `A`, with `(n+1)^s n^s 2^{4(n+1)(n−1)s}` subclasses (Lemma 4.1 at that `γ`). It covers
     `[max(A², B₀), (Λ A)^{O(1)}]` in `O(n log(2 + n log Λ))` windows. That is `log log` in
     `|D_K|` and `∏ N(q)`, uniform in `α`. **So S90-A stands as stated.** These windows are
     not in the paper. They start at `(n!)^{2d}` for every `A`, so S90.4 needs only them, not
     Lemma 4.2's.

  The Lean for 2 and 3 (all std3):
  - DA 8.8, `DiophantineApproximation/BalancedPoint.lean`: `one_le_scalarConst`,
    `prod_iSup_pow_le_mulHeightAff`, `affineProd_smul`, `balancedConst` with
    `systemConst_balancedConst` (`= 1`), **`exists_smul_balanced`** (the representative: `∏‖β‖ ≤ κ`,
    `≤ κ⁻¹` at `P₀`, `≤ 1` on `S`, `≤ (κ H_aff)^{s(w)}` at infinity,
    `κ ∏‖x‖ ≤ H_aff(βx) ≤ κ² ∏‖x‖`), **`exists_smul_systemValue_le`** (for forms bounded by
    the sup norm: every form `≤ balancedConst p · H_aff^{s(p)}`, and
    `affineProd(βx) H_aff(βx) ≤ κ^{n+2} affineProd(x) ∏‖x‖`), `exists_mul_isIntegral`,
    **`exists_mul_isIntegral_inv_le_finprod_iSup`** (Minkowski's class bound, via
    `ArithmeticHeights`' `finprod_iSup_eq_inv_absNorm`) and **`placeProd_iSup_le_mul_mulHeight`**.
    In `PlaceProd.lean`, `one_le_placeProd_univ_of_mem_integer` and `placeProd_univ_iSup_mul`.
  - DA 8.8, `SumForms.lean`: `apply_sumForms_le_iSup` (on the hyperplane, in the class, every
    form is at most the sup norm of `y'`: the sum form is `−y_{n+1}`) and `det_pi_sumForms`
    (determinant `1`, so `systemDet = 1` and `∏ C ≤ |det|^{1/n}` reads `∏ C ≤ 1`).
  - Here, `ProductInequality.lean`: `affineProd_sumForms_mul_placeProd_iSup_eq` (the exact
    identity (3.14)–(3.15)) and **`exists_smul_balanced_unitClass`**: the representative
    `z = β y'` of a solution in the class `r`, `S`-integral, each form
    `≤ balancedConst p · H_aff(z)^{s(p)}`, and
    `affineProd(z) H_aff(z) ≤ κ^{n+2} ∏ᵢ ∏_{S∞∪S} ‖αᵢ‖`.
  - Here, `ProjectiveSolutions.lean`, the reductions: `projUnitSolutions_mono` (enlarging `S`)
    and `projUnitSolutions_mul` (scaling `α`).

- **S90.3 ✅ (2026-10-16) — the Subspace step (Lemma 3.1).** `SubspaceStep.lean`:

  ```lean
  theorem NumberField.exists_finset_submodule_of_stepThreshold_lt [Nonempty ι] (S)
      (hP₀ : P₀ ∈ S) (hα : ∀ o, α o ∈ S.integer K) (hα0 : ∀ o, α o ≠ 0) :
      ∃ T : Finset (Submodule K (ι → K)),
        (#T : ℝ) ≤ ((n + 1) ^ t * ((n + 1) N + 1) ^ (n t) : ℕ) * stepCount K S n ∧
        (∀ U ∈ T, U ≠ ⊤) ∧
        ∀ x, (∀ o, x o ∈ S.unit K) → ∑ o, α o * x o = 0 →
          stepThreshold K S α < mulHeight (fun i ↦ α (some i) * x (some i)) →
          ∃ U ∈ T, (fun i ↦ α (some i) * x (some i)) ∈ U
  ```

  with `t = #(InfinitePlace K ⊕ S)`, `N = stepGrid = 4 t n`, `stepCount` Q4.3's count for one
  system (with `E = K`, coefficient height `1`, degree `1`, `R = n + 1`, `δ = 1/4`), and
  `θ = stepThreshold = (κ^{n+2} A' (κ² n^{d+#S})^n)²`. The proof:
  - **Classes** are `ρ : InfinitePlace K ⊕ S → Option ι` (`classChoice`, `exists_classChoice`),
    `(n + 1)^t` of them, so that they form a `Fintype`.
  - **The representative** is S90.2's `exists_smul_balanced_unitClass`, now also giving
    `H_aff(z) ≤ κ² ∏_{S∞∪S} ‖z‖_v`.
  - **The largest form** at each place is at least `1/n` of the sup norm
    (`iSup_le_card_mul_iSup_sumForms`, DA `SumForms.lean`), so the product of the largest forms
    is at least `H_aff(z) / (κ² n^{d+#S})` (`placeProd_iSup_le_mul_prod_iSup_systemValue`, DA
    `SystemGrid.lean`). Together with (3.20) and `H_aff(z) ≥ H(y') > θ` this is the hypothesis
    of the grid lemma with `δ = 1/4`.
  - **Product to system** (no existing lemma fitted: DA 9.1's
    `exists_finset_forall_exists_mem_systemSet` gives systems that are not normalized, with an
    existential level and no count; `cellIndex` and Layer 6.1's `gridExponent` are for
    approximation domains): `exists_mem_systemSet_systemGridExponent`, new in DA
    `SystemGrid.lean`. The exponent of a form relative to the **largest** form at its place,
    rounded down on a grid of mesh `1/N` and capped at `n + 1`, so `max_i c p i = s(p)` holds
    and the systems number `((n + 1) N + 1)^{n t}`. It replaces Lemma 4.1's simplex net.
  - **Each system** is normalized (`isNormalizedSystem_sumForms`: coefficients `0, 1`
    (`sumForms_basisFun`), at most `n + 1` forms (`sumForms_mem_range`), `det = 1`, constants of
    product `1`) and counted by Q4.3 (`exists_finset_submodule_sumForms`). The count is uniform
    in the class, because `efSystemThreshold_le` at `H = 1` does not see the forms (`stepX`);
    `stepCount_nonneg` uses the new `one_le_efLargeCount` (QS `FormSystemCount.lean`).
  - For `n = 1` no grid point qualifies (the weight is `1 − 0`), so there are no large solutions,
    as there should not be.

  What S90.4 must now cover is `H(y') ≤ θ`, i.e. up to
  `(κ^{n+2} A' (κ² n^{d+#S})^n)²`, with `A' ≤ (2^d √|D_K|)^{n+1} A` after the coefficient
  normalization of the check (item 3). `log θ = O(n² (log κ + (d + s) log n) + n log A)`.
- **S90.4 ✅ (2026-10-16) — the gap principle (Lemmas 4.2 and 5.3), with exponential
  windows.** `GapPrinciple.lean`:

  ```lean
  theorem NumberField.exists_finset_submodule_of_le_mulHeight_le [Nonempty ι] (S)
      (hα0 : ∀ o, α o ≠ 0) (hB : ((n ! : ℝ) ^ finrank ℚ K) ^ 2 < B) :
      ∃ T : Finset (Submodule K (ι → K)),
        #T ≤ (n + 1) ^ t * (gapGrid S n + 1) ^ (n * t) * gapWindows n B Θ ∧
        (∀ U ∈ T, U ≠ ⊤) ∧
        ∀ x, (∀ o, x o ∈ S.unit K) → ∑ o, α o * x o = 0 →
          B ≤ mulHeight (α x) → mulHeight (α x) ≤ Θ → ∃ U ∈ T, y' ∈ U
  ```

  with `N = gapGrid = 4 (n + 1) t n` and
  `gapWindows n B Θ = ⌊log (log Θ / log B) / log (1 + 1/(4n))⌋ + 1`. **No hypothesis on `α` but
  `αᵢ ≠ 0`, none on `S`, and the count does not see `α`.** The proof is §4 of the paper with three
  changes (module docstring):
  - **Windows `[B, B ^ (1 + 1/(4n)))`**, for every `B > (n!)^{2d}`, rather than
    `[B, B A^{1/(2(n²−1))}]`. These are the windows of the S90.3 check (item 4). Any `n` solutions
    in a window and a subclass have determinant `0` (`det_eq_zero_of_gapWindow`), because
    `A ≤ (n!)^d B^{n + 1/4} min(1, A / B^{n+1})^γ < A` with `γ = 1 − 1/(4(n+1))`, uniformly in
    `A ≥ 1`. That inequality is (4.20), as `gapConst_le`.
  - **(4.9) is an identity**: the relative sizes `gapRatio` (`≤ 1` in the class) multiply to
    `A / H(y)^{n+1}` (`prod_gapRatio`). `A = gapConst` is Schlickewei's (3.6), written as
    `∏ᵢ ∏_{S∞∪S} ‖αᵢ‖ · (H(α) / ∏_{S∞∪S} max ‖α‖)^{n+1}`, and is `≥ 1` (`one_le_gapConst`). The
    subclasses round the exponents `log u / log (A / H^{n+1})` down on a grid of mesh `1/N`
    (`exists_le_rpow_prod_grid`, DA) instead of Lemma 4.1's simplex net and the column `k(v)`.
  - **Off `S`** ((4.17)–(4.19)): `ζ α_k`, `ζ = Δ / ∏ α`, is an `S`-integer for every `k` (at
    `v ∉ S` the forms `y_o`, `o ≠ k`, have determinant `Δ` and sizes `‖α_o‖_v`), and
    `H(ζ α) = H(α)` is at most its product over `S∞ ∪ S`. So
    `∏ᵢ ∏_{S∞∪S} ‖αᵢ‖ · H(α) ≤ ∏_{S∞∪S} ‖Δ‖ · ∏_{S∞∪S} max ‖α‖`
    (`prod_placeProd_mul_mulHeight_le`). At the places of `S∞ ∪ S` each column is divided by its
    largest coordinate before Leibniz (`placeProd_det_le`, (4.14)–(4.15)).

  The heights are those of `y = α x` and not of `y'` (`H(y') ≤ H(y)`), since `H(y)` is what the
  relative sizes see (`mulHeight_mul_unit_mul_placeProd`, DA). S90.3 covers `H(y') > θ`; the
  rest, `B ≤ H(y)` and `H(y') ≤ θ`, is `exists_finset_submodule_of_mulHeight_some_le`, the
  theorem at `Θ = n^d θ`, since `H(y) ≤ n^d H(y')` (DA `mulHeight_elim_neg_sum_le`: at the
  infinite places `|y_{n+1}| ≤ n max |yᵢ|`, at the finite ones `≤ max |yᵢ|`). So S90.6 takes
  `θ = stepThreshold` there. `log Θ = O(n² (log κ + (d + s) log n) + n log A')`, so the count is
  `(n+1)^t (4(n+1)tn + 1)^{nt} · O(n log (log Θ / log B))`, which is `log log` in `|D_K|` and
  `∏ N(q)`. Below `B = (n!)^{2d} + 1` the solutions are S90.5's
  (`exists_finset_submodule_of_mulHeight_lt`).
- **S90.5 ✅ (2026-10-16) — the small solutions (Lemmas 5.1 and 5.2).** `SmallSolutions.lean`:

  ```lean
  theorem NumberField.exists_finset_submodule_of_mulHeight_lt (hι : 2 ≤ Fintype.card ι) (S)
      (hα0 : ∀ o, α o ≠ 0) (B : ℝ) :
      ∃ T : Finset (Submodule K (ι → K)),
        #T ≤ northcottCount (finrank ℚ K) (max B 1).toNNReal ^ n ∧ (∀ U ∈ T, U ≠ ⊤) ∧
        ∀ x, (∀ o, x o ∈ S.unit K) → mulHeight (α x) < B → ∃ U ∈ T, y' ∈ U
  ```

  The check came out against DA 9.3: `exists_finset_submodule_of_not_isLargeSolution` is a gap
  principle for a normalized system (Proposition 4.2 sorts the points by the forms at each
  place), not a statement about heights alone, so it does not apply below the Subspace step.
  The uniform Northcott count went to ArithmeticHeights instead (Layer 1.3, *Added with Sch90's
  S90.5*), and it is cheap: Mathlib's `Polynomial.card_mahlerMeasure_le_prod` already counts the
  integer polynomials of bounded degree and Mahler measure, and 1.2's
  `exists_isPrimitive_absMulHeight₁_pow_natDegree` attaches one to each algebraic number. So
  `Projectivization.ncard_setOfPred_mulHeight_le` bounds the points of `ℙ^{n−1}(K)` of relative
  height `≤ X` by `northcottCount d (max X 1) ^ n`, with
  `northcottCount d M = d ∏_{i ≤ d} (2 ⌊binom d i · M⌋ + 1)`, which sees `K` only through `d`.
  Each `y'` lies on the line `K y'`, proper when `n ≥ 2`. Lemma 5.2's range `n^{9ns(d!)²}` is not
  needed, because S90.4's windows start at `(n!)^{2d}` for every `α`. S90.6 takes
  `B = (n!)^{2d} + 1` (or anything above `(n!)^{2d}`), so the count is
  `northcottCount d ((n!)^{2d} + 1) ^ n`, depending on `n` and `d` only. Neither the equation nor
  `S` is used beyond `y' ≠ 0`. For `n = 1` the lines are not proper; §7 handles that case
  separately (there is one projective solution).
- **S90.6 ✅ (2026-10-16) — Lemma 6.1, the induction (§7), the theorems of record.** Three files.

  **`AllSolutions.lean`, Lemma 6.1.**

  ```lean
  theorem NumberField.exists_finset_submodule_of_sum_eq_zero (hι : 2 ≤ Fintype.card ι) (S)
      (hP₀ : P₀ ∈ S) (hα0 : ∀ o, α o ≠ 0) :
      ∃ T : Finset (Submodule K (ι → K)), (#T : ℝ) ≤ lemmaCount K S n ∧ (∀ U ∈ T, U ≠ ⊤) ∧
        ∀ x, (∀ o, x o ∈ S.unit K) → ∑ o, α o * x o = 0 → ∃ U ∈ T, y' ∈ U
  ```

  The count `lemmaCount` does **not** see `α`, which the plan above took for granted and which
  S90.4 alone does not give. Its windows run from a fixed `B` to `n^d θ`, and `θ` grows with
  `A' = ∏ᵢ ∏_{S∞∪S} ‖αᵢ‖`. The repair, not in the paper:
  - **every solution has `A ≤ H(y) ^ (n + 1)`** (`gapConst_le_mulHeight_pow`, from
    `prod_gapRatio` and `gapRatio_le_one`), so the windows start at
    `B = max (B₀, A ^ (1 / (n + 1)))`, `B₀ = (n!)^{2d} + 1`;
  - **for normalized coefficients, `A' ≤ A (2^d √|D_K|) ^ (n + 1)`**
    (`prod_placeProd_le_gapConst_mul`, the S90.3 check's item 3).

  Then `n^d θ ≤ windowConst · B ^ (2 (n + 1))` (`mul_stepThreshold_le`), and the number of
  windows is at most `⌊log windowRatio / log (1 + 1/(4n))⌋ + 1` (`gapWindows_le`), with
  `windowRatio = 2 (n + 1) + log windowConst / log B₀`. The solutions with `B₀ ≤ H(y) < B` do not
  exist. The coefficients are normalized first by `exists_mul_isIntegral_inv_le_finprod_iSup`,
  which leaves the solutions alone and the points up to a scalar.

  **`Induction.lean`, §7.** The solutions are counted by their normalized representatives
  (`normUnitSolutions S α k₀`, `x k₀ = 1`), so the induction takes no quotients. One step
  (`ncard_normUnitSolutions_option_le`): each `U ∈ T` lies in a hyperplane `∑ βᵢ yᵢ = 0`
  (`exists_ne_zero_forall_sum_mul_eq_zero_of_ne_top`, new in DA 8.2), and a solution in `U` has a
  minimal nonempty vanishing subsum `J` of it (`exists_subset_nonempty_sum_eq_zero_forall_ne_zero`,
  new in DA 8.2; DA's `exists_subset_sum_eq_forall_ne_zero` returns `∅` for a vanishing sum).
  Each `(U, J)` costs at most `Z²` (`ncard_setOf_minimal_le`): the solution is determined by
  `(xᵢ / x_{j₀})_{i ∈ J}`, a solution of the shorter equation, and by `(x_{j₀}, (x_o)_{o ∉ J})`, a
  solution of the equation with the block `J` merged into one term `γ z`. The second has no
  vanishing proper subsum either, which needs `J ≠ univ` and `none ∉ J`. Both have at most `n`
  terms, as `#J ≥ 2`. So `#T · 2ⁿ · Z²` for `n + 1` terms, Schlickewei's `2ⁿ Z(n−1)²` per
  subspace. `ncard_normUnitSolutions_le_unitCount` runs the recursion
  `Z(m + 1) = Z(m) + L(m) 2^m Z(m)²` for any bound `L` of Lemma 6.1, over all index types. Zero
  coefficients are not a hypothesis anywhere: they make a singleton vanishing subsum.

  **`UnitCount.lean`, the theorems of record.** A prime `P₀` above `2` is added to `S` first
  (`exists_absNorm_le_two_pow`, new in DA `BalancedPoint.lean`: `N(P₀) ≤ 2^d`), so that S90.3 has
  a finite place.
  - `ncard_unitSolutions_le_unitCount`: Theorem 1.1 for one field, through (1.6) with
    `α_{n+1} = -1`, as `unitCount L (n + 1)` with `L m = ⌈lemmaCount K (S ∪ {P₀}) m⌉`.
  - `lemmaCount_le`: `lemmaCount K S n ≤ lemmaConst n d t₁ #S · (1 + log M)`, with `t₁` the
    number of infinite places. It holds because `log κ ≤ d + M`,
    `windowRatio ≤ windowRatioConst · M` and Q4.3's `stepX ≤ stepXConst · M`.
  - `unitCount_le`: the recursion squares, `unitCount L N ≤ recursionConst c N · X ^ (2^N − 1)`.
  - `exists_ncard_unitSolutions_le`: Theorem 1.1 with explicit invariants. `M` of `S ∪ {P₀}` is
    at most `(1 + d) M`.
  - **The theorem of record**, with constants summed over the finitely many `(d, t₁, #S)`,
    `d ≤ 2 t₁`:

  ```lean
  theorem NumberField.ncard_unitSolutions_le (n s : ℕ) :
      ∃ C : ℝ, ∀ (K : Type) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K)))
        (a : Fin n → K), Fintype.card (InfinitePlace K) + #S ≤ s →
        ((unitSolutions S a).ncard : ℝ) ≤
          C * (1 + Real.log (Real.log |(discr K : ℝ)| +
            ∑ p ∈ S, Real.log (Ideal.absNorm p.asIdeal) + 2)) ^ (2 ^ (n + 1) - 1)
  ```

  It differs from the sketch this README had before:
  - the `log log` term carries the power `2 ^ (n + 1) − 1` that §7's squares produce;
  - the coefficients are any `a : Fin n → K`, not units, since zero coefficients give no
    solutions;
  - `C` is existential, and is explicit in `exists_ncard_unitSolutions_le`.

  S90-B, after Q4.4, removes `log M` from `lemmaCount` and with it the power.

## Reads before S90.3

- Sch90 §§3–5 against the scans: `pdftotext` garbles the exponents; (3.6), (3.20), (4.2), (4.9)
  were checked against pages 99–102.
- Evertse–Győry, *Unit Equations in Diophantine Number Theory* (2015), Ch. 6. It has the modern
  version of this argument with ES02's count. Not in the local folder.
- `QuantitativeSubspace/README.md` Q4.4, to see whether S90-B can wait for it or whether a
  threshold free of `|D_K|` for **these** forms (rational coefficients, `H(L) ≤ √n`) is cheaper.

## References

* [Sch90] H. P. Schlickewei, *`S`-unit equations over number fields*, Invent. Math. **102**
  (1990), 95–107.
* [Sch92] H. P. Schlickewei, *The quantitative Subspace Theorem for number fields*, Compositio
  Math. **82** (1992), 245–273.
* [Ev84] J.-H. Evertse, *On sums of `S`-units and linear recurrences*, Compositio Math. **53**
  (1984), 225–244 (`Evertse1984/`).
* [EF13] J.-H. Evertse, R. G. Ferretti, *A further improvement of the Quantitative Subspace
  Theorem*, Ann. of Math. **177** (2013), 513–590 (`QuantitativeSubspace/`).
