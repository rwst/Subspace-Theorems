/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Stephan2026a.Kernel

/-!
# Stephan 2026, re-exported for `comparator`

`comparator` compares the theorems named in `comparator/stephan-2026a.json` between this module's
environment and `ChallengeStephan2026a.lean`'s, constant by constant over the definitional closure
of each statement. The import is the module that owns the certified statements, the two forms of
Theorem 1.1; nothing is proved here, and no library imports this module. See `COMPARATOR.md`.
-/
