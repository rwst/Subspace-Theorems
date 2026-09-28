/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.AuxiliaryPolynomial
public import ArithmeticHeights.BombieriVaaler
public import ArithmeticHeights.BombieriVaalerEntries
public import ArithmeticHeights.BombieriVaalerRelative
public import ArithmeticHeights.Siegel
public import DiophantineApproximation.MovingTargets
public import DiophantineApproximation.ParametricSubspace
public import DiophantineApproximation.Ridout
public import DiophantineApproximation.RothInfinity
public import DiophantineApproximation.RothProjective
public import DiophantineApproximation.RothRational
public import DiophantineApproximation.RothSubspaceCount
public import DiophantineApproximation.RothTheorem
public import DiophantineApproximation.SubspaceAffine
public import DiophantineApproximation.SubspaceAlgebraic
public import DiophantineApproximation.SubspaceConsistency
public import DiophantineApproximation.SubspaceGeneralPosition
public import DiophantineApproximation.SubspaceIntervals
public import DiophantineApproximation.SubspaceSmall
public import DiophantineApproximation.SubspaceSystem
public import DiophantineApproximation.SubspaceTheorem

/-!
# The development, re-exported for `comparator`

`comparator` compares the theorems named in `comparator/*.json` between this module's environment
and the challenge's (`Challenge.lean` or `ChallengeFlat.lean`), constant by constant over the
definitional closure of each statement. These imports are the modules of the two libraries that
own the certified statements; nothing is proved here, and neither library imports this module.
See `COMPARATOR.md`.
-/
