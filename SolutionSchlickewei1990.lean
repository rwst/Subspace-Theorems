/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.NorthcottTheorem
public import Schlickewei1990.ProjectiveSolutions
public import Schlickewei1990.UnitCount

/-!
# Schlickewei 1990, re-exported for `comparator`

`comparator` compares the theorems named in `comparator/schlickewei-1990.json` between this
module's environment and `ChallengeSchlickewei1990.lean`'s, constant by constant over the
definitional closure of each statement. These imports are the modules that own the certified
statements: those of `Schlickewei1990`, and `ArithmeticHeights.NorthcottTheorem` for the uniform
count of points of bounded height (Lemma 5.1); nothing is proved here, and no library imports this
module. See `COMPARATOR.md`.
-/
