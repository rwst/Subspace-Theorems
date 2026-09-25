# Certifying the headline theorems with `leanprover/comparator`

`lake test` runs [`leanprover/comparator`](https://github.com/leanprover/comparator) over
`comparator/*.json`. For every theorem a config names it checks three things:

1. the statement in `Solution` is **the same statement** as in the challenge — compared constant
   by constant over the whole definitional closure, definitions by value, not just by name;
2. the `Solution` proof uses **no axiom** outside the config's `permitted_axioms` — here only
   `propext`, `Quot.sound` and `Classical.choice`;
3. the resulting environment is **re-accepted by the Lean kernel**.

The trusted statement of record comes in **two shapes stating the same theorems**, both generated
by `scripts/make-challenge.py` and neither edited by hand:

- `Challenge.lean` and `Challenge/` — one module per module of the development that owns a
  compared declaration, each under that module's own imports in that module's order;
- `ChallengeFlat.lean` — **one module importing only Mathlib**, the shape the
  [Palomar registry](https://palomar-registry.org/statement) requires of a Challenge.

Every certified theorem in either is `sorry`-proved. `Solution.lean` re-exports the modules of the
two libraries that own the certified statements. None of the three is a default target, and
`scripts/guards.sh` rejects any library file importing one of them, so `lake build` and every gate
in `scripts/` are unaffected.

## Running it

```sh
lake build comparator lean4export   # once
lake build Solution                 # so that comparator's sandboxed build has nothing to do
lake test                           # both configs
lake test -- comparator/std3-flat.json
```

`landrun` must be on `PATH` (Linux/Landlock only; it sandboxes the builds):

```sh
git clone https://github.com/Zouuup/landrun && cd landrun
go build -o ~/.local/bin/landrun cmd/landrun/main.go
```

Each binary is overridable via `COMPARATOR_BIN`, `COMPARATOR_LEAN4EXPORT`, `COMPARATOR_LANDRUN`.
Comparator is pinned to the tag of the toolchain (`v4.35.0-rc3`); a toolchain bump moves the tag.

## What is certified

The 26 theorems of `comparator/theorems.txt`, both configs, all within the three standard axioms:

| milestone | Lean identifier |
| --- | --- |
| **Siegel's lemma and Bombieri–Vaaler** (`ArithmeticHeights`, Layer 5) | |
| 5.1 Siegel over `ℤ` | `Int.Matrix.exists_ne_zero_mulVec_eq_zero_iSup_abs_le` |
| 5.1 Siegel over a number field | `NumberField.exists_forall_exists_ne_zero_mulVec_eq_zero_absMulHeight_le` |
| 5.2 Bombieri–Vaaler, Theorem 2 | `Int.Matrix.exists_linearIndependent_mulVec_eq_zero_prod_iSup_abs_le` |
| 5.2 Bombieri–Vaaler, Theorem 1 | `Int.Matrix.exists_ne_zero_mulVec_eq_zero_iSup_abs_le_det_rpow` |
| 5.5 one small solution over a number field | `NumberField.exists_ne_zero_mem_ker_absMulHeight_le` |
| 5.6 the relative form | `NumberField.exists_linearIndependent_mem_ker_prod_absMulHeight_le` |
| 5.7 the auxiliary polynomial | `MvPolynomial.exists_ne_zero_mem_ker_mulHeight_rpow_le` |
| **Roth's theorem** (`DiophantineApproximation`, Layer 3) | |
| 3.2 over a number field, several places | `NumberField.finite_setOf_prod_min_one_le` |
| 3.3 over `ℚ`: the exponent is `2` | `Real.irrationalityExponent_eq_two` |
| 3.3 Ridout | `Rat.finite_setOf_ridout` |
| 3.3 the `p`-adic form | `Rat.finite_setOf_apply_intCast_sub_le` |
| 3.3 targets at infinity | `NumberField.finite_setOf_prod_onePointApprox_le` |
| 3.4 on the projective line | `NumberField.finite_setOf_prod_min_one_le_card_two` |
| 3.8 moving targets | `NumberField.finite_setOf_prod_min_one_le_of_isLittleO` |
| **The Subspace Theorem** (Layers 3.4 and 6) | |
| 3.4 in two variables | `NumberField.exists_finset_submodule_of_approxProd_le_card_two` |
| 6.1 the parametric form | `NumberField.exists_finset_submodule_forall_approxDomain_subset` |
| 6.2 coefficients in `K` | `NumberField.exists_finset_submodule_of_approxProd_le` |
| 6.3 algebraic coefficients | `NumberField.exists_finset_submodule_of_approxProd_le_extension` |
| 6.4 the affine form, `S`-integral points | `NumberField.exists_finset_submodule_of_integer_of_affineProd_le` |
| 6.5 Vojta's general-position form | `NumberField.exists_finset_submodule_of_generalProd_le` |
| 6.6 `n = 1`, algebraic coefficients | `NumberField.exists_finset_submodule_of_approxProd_le_card_two_of_extension` |
| **Counting the subspaces** (Layer 9, Evertse) | |
| 9.1 Theorem A | `NumberField.exists_finset_submodule_of_systemWeight_neg` |
| 9.3 the small solutions | `NumberField.exists_finset_submodule_of_not_isLargeSolution` |
| 9.3 the small solutions over `ℚ` | `Rat.exists_finset_submodule_of_not_isLargeSolution` |
| 9.4 intervals to subspaces | `NumberField.exists_finset_submodule_of_forall_mem_interval` |
| 3.7 into 9.4 for `N = 2` | `NumberField.exists_finset_submodule_of_card_eq_two` |

The compared closure of these statements holds 38 definitions of the two libraries — the
heights (`absMulHeight`, `arakelovMulHeight`, `Matrix.mulHeight`, `MvPolynomial.mulHeight`,
`mulHeightAff`), the approximation products (`approxProd`, `affineProd`, `generalProd`), the
approximation domains, Roth's parameters, the systems of Layer 9 — each repeated verbatim in the
challenge and compared by value.

### Not certified, and why

- **Layers 5.3 and 5.4**, the "basis of the kernel" forms of Bombieri–Vaaler over a number field
  (`NumberField.exists_basis_ker_prod_arakelovMulHeight_rpow_le`,
  `NumberField.exists_basis_ker_prod_absMulHeight_le`). Their statements mention the height of a
  subspace, whose definition reaches four `private` lemmas of `ArithmeticHeights/Arakelov.lean`, a
  `private` lemma of `ArithmeticHeights/Plucker.lean`, and the auxiliary proofs of
  `Submodule.mulHeight`, which are private because that definition is not `@[expose]`d. A private
  name embeds its module's name (`_private.ArithmeticHeights.Arakelov.0.…`), so no challenge
  module can reproduce it, and comparator compares such constants by name. Certifying them means
  making those six constants public in the development first. The same holds for anything else
  stated with `Submodule.mulHeight` (Northcott for subspaces, the duality theorem).
- The **applications** (Layers 7 and 8: Schmidt's simultaneous approximation, the transcendence
  criterion, unit equations, Thue–Mahler, norm forms, …) and the rest of `ArithmeticHeights`
  (Northcott, Kronecker, Minkowski's second theorem, …) are left out for size: Palomar caps a
  Challenge at 1000 lines and 100 KiB. Adding one is a line in `comparator/theorems.txt`; the
  generator reports the flat file's size.

## Regenerating

```sh
lake build
python3 scripts/make-challenge.py      # under the usual thread and memory caps
lake build Challenge ChallengeFlat
lake test
```

The generator runs a metaprogram over both libraries, which writes the compared closure (every
declaration reached from a certified theorem's *type*, following definitions' values and
theorems' proofs, exactly as comparator walks it), every declaration's line range, and the import
graph. It then copies each needed declaration from its source file — docstrings and comment lines
dropped, certified theorems cut at their `:=` — together with the source's `namespace`, `section`,
`open` and `variable` commands that some copied declaration follows. It refuses a theorem whose
closure reaches a `private` constant, and it names any `Challenge/` file it no longer writes, for
deletion by hand.

## Why the flat challenge looks the way it does

Comparator compares **definitions by value** and does not quotient by proof irrelevance. A
challenge that merely *means* the same is rejected. Flattening 34 modules into one broke three
things. The per-module tree needs none of the three cures, and it passes too, which shows the
cures are not changing what is stated.

1. **Load order decides ties between instances.** Lean tries instances of equal priority
   latest-loaded first, and loading is a depth-first walk of the import list. The flat file
   therefore imports its Mathlib modules in the order the development loads them (starting from
   `Solution.lean`'s imports), not alphabetically, and drops an import only when an earlier one
   already loads it and makes it visible. It also keeps each import private unless some module
   imports it publicly along a path of public imports, because under the module system a
   private import is invisible to public statements.
2. **The development itself does not load Mathlib in one order.** Most modules try
   `Module.Free.instFaithfulSMulOfNontrivial` before `instFaithfulSMul_1` (from
   `Mathlib.Algebra.Algebra.IsSimpleRing`), and `IsLocalRing.toNontrivial` before
   `EuclideanDomain.toNontrivial`. The modules that descend from
   `DiophantineApproximation/ApproxProd.lean` (and `ArithmeticHeights/BombieriVaaler.lean`, for the
   first pair) try them the other way round. So the same goal `FaithfulSMul K F` or
   `Nontrivial F` elaborates to different terms in different files. One file has one load order.
   So in the part of `ChallengeFlat.lean` copied from such a module, `attribute [local instance
   999] …` lowers the candidates that module does not try first, restoring its ranking, and nothing
   else. Lowering rather than raising matters: a more specific instance such as `Rat.nontrivial`
   is tried before all of them, and raising `EuclideanDomain.toNontrivial` overrules it. The
   candidate groups are the `TIES` table of the generator, and the generator computes which module
   needs which ranking from the import graph. Only a group that comparator has rejected belongs
   there, listing every candidate that has been seen chosen. The instances are all propositions,
   so the pins change which proof of a `Prop` the statement carries, never what it says.
   Patching the development instead was tried and does not converge: 68 of its 184 modules
   disagree with the rest on the first pair, from over a dozen origins, and moving one pair moves
   another.
3. **The auxiliary-proof cache is module-local.** A numeral `≥ 2` in a definition's body carries a
   `Nat.AtLeastTwo` proof, which Lean lifts out as `<owner>._proof_<n>` and caches by type for the
   rest of the *module*. The development's modules each mint their own, so
   `NumberField.rothEps._proof_1` and `NumberField.IsLargeSolution._proof_1` exist beside
   `NumberField.arakelovMulHeight._proof_1`. In one file all three would be the last. Each part of
   `ChallengeFlat.lean` therefore opens with
   `run_cmd Lean.modifyEnv (Lean.Meta.auxLemmasExt.setState · {})`, which clears that cache —
   Lean's own comment calls it "a mere cache, keep local" — exactly as a module boundary does.

Everything else about the flat file is size. Docstrings and comments are gone, and so are the
context commands no copied declaration follows. At 823 lines and 41 KiB it clears Palomar's hard
limits (1000 lines, 100 KiB) and trips both of its warnings (300 lines, 32 KiB).

## Palomar

Only `comparator/std3-flat.json` is a submission candidate: one configuration is one registry
entry, and its Challenge must import only Lean core and Mathlib. `permitted_axioms` is the
standard three, as Palomar requires. `formalization.yaml` (schema v0.4) names the same 26
declarations as `comparator/theorems.txt` under `status.main_results` and `alignment`; a change
to the certified list must be made in both. The lakefile already complies: a committed `lake-manifest.json`,
every dependency a public `https://github.com/…` repository pinned to a full commit.

## Negative controls

All three bite on `comparator/std3-flat.json`, and should be re-run after any change here:

- weakening `hB : 1 ≤ B` to `0 ≤ B` in Siegel's lemma over `ℤ` is rejected with
  `Challenge and solution theorem statement do not match:
  'Int.Matrix.exists_ne_zero_mulVec_eq_zero_iSup_abs_le'`;
- deleting the `run_cmd` cache resets is rejected with
  `Const does not match between challenge and target 'NumberField.rothRatio'`;
- deleting the `attribute [local instance …]` pins is rejected with
  `Challenge and solution theorem statement do not match: 'Rat.finite_setOf_apply_intCast_sub_le'`.
