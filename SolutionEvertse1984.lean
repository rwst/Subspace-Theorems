/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.SubspaceAffine
public import Evertse1984.SUnitSums
public import Evertse1984.AdmissiblePoints
public import Evertse1984.Corollaries
public import Evertse1984.PolynomialValues
public import Evertse1984.GeneralRoots

/-!
# Evertse 1984, re-exported for `comparator`

`comparator` compares the theorems named in `comparator/evertse-1984.json` between this module's
environment and `ChallengeEvertse1984.lean`'s, constant by constant over the definitional closure
of each statement. These imports are the modules that own the certified statements: those of
`Evertse1984`, and `DiophantineApproximation.SubspaceAffine` for the Subspace Theorem the paper
cites as Theorem 4; nothing is proved here, and no library imports this module. See
`COMPARATOR.md`.
-/
