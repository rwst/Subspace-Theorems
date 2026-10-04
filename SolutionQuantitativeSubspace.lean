/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import QuantitativeSubspace.FormSemistableGap
public import QuantitativeSubspace.FormIntervalResult
public import QuantitativeSubspace.FormIntervalCount
public import QuantitativeSubspace.FormDomainSystem
public import QuantitativeSubspace.FormSystemCount

/-!
# Evertse–Ferretti 2013, re-exported for `comparator`

`comparator` compares the theorems named in `comparator/quantitative-subspace.json` between this
module's environment and `ChallengeQuantitativeSubspace.lean`'s, constant by constant over the
definitional closure of each statement. These imports are the modules of `QuantitativeSubspace`
that own the certified statements; nothing is proved here, and no library imports this module. See
`COMPARATOR.md`.
-/
