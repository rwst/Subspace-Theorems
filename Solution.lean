/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
import ArithmeticHeights.AuxiliaryPolynomial
import ArithmeticHeights.BombieriVaaler
import ArithmeticHeights.BombieriVaalerEntries
import ArithmeticHeights.BombieriVaalerRelative
import ArithmeticHeights.Siegel
import DiophantineApproximation.MovingTargets
import DiophantineApproximation.ParametricSubspace
import DiophantineApproximation.Ridout
import DiophantineApproximation.RothInfinity
import DiophantineApproximation.RothProjective
import DiophantineApproximation.RothRational
import DiophantineApproximation.RothSubspaceCount
import DiophantineApproximation.RothTheorem
import DiophantineApproximation.SubspaceAffine
import DiophantineApproximation.SubspaceAlgebraic
import DiophantineApproximation.SubspaceConsistency
import DiophantineApproximation.SubspaceGeneralPosition
import DiophantineApproximation.SubspaceIntervals
import DiophantineApproximation.SubspaceSmall
import DiophantineApproximation.SubspaceSystem
import DiophantineApproximation.SubspaceTheorem

/-!
# The development, re-exported for `comparator`

`comparator` compares the theorems named in `comparator/*.json` between this module's environment
and the challenge's (`Challenge.lean` or `ChallengeFlat.lean`), constant by constant over the
definitional closure of each statement. These imports are the modules of the two libraries that
own the certified statements; nothing is proved here, and neither library imports this module.
See `COMPARATOR.md`.
-/
