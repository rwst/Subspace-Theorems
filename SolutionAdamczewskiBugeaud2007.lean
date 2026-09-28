/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
import DiophantineApproximation.ComplexityTranscendence
import AdamczewskiBugeaud2007.AutomaticComplexity
import AdamczewskiBugeaud2007.Automaton
import AdamczewskiBugeaud2007.MorphicTranscendence
import AdamczewskiBugeaud2007.BetaApproximation
import AdamczewskiBugeaud2007.PisotTranscendence
import AdamczewskiBugeaud2007.SchmidtPeriodicity
import AdamczewskiBugeaud2007.BetaDigitsTranscendence
import AdamczewskiBugeaud2007.PadicTranscendence
import AdamczewskiBugeaud2007.HenselDigits
import AdamczewskiBugeaud2007.Christol
import AdamczewskiBugeaud2007.ChristolTranscendence

/-!
# Adamczewski–Bugeaud 2007, re-exported for `comparator`

`comparator` compares the theorems named in `comparator/adamczewski-bugeaud-2007.json` between
this module's environment and `ChallengeAdamczewskiBugeaud2007.lean`'s, constant by constant over
the definitional closure of each statement. These imports are the modules that own the certified
statements (Theorem 1 is `DiophantineApproximation`'s); nothing is proved here, and no library
imports this module. See `COMPARATOR.md`.
-/
