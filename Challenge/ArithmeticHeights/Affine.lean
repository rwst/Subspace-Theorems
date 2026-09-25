/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.NumberTheory.Height.NumberField

public section
open Function Real
namespace Height
variable {K : Type*} [Field K] [AdmissibleAbsValues K] {ι ι' : Type*}
@[expose] noncomputable def mulHeightAff (x : ι → K) : ℝ := mulHeight fun o : Option ι ↦ o.elim 1 x
end Height
end
