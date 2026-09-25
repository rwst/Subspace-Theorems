/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber

public section
open Filter
open scoped ENNReal NNReal
namespace Real
@[expose] noncomputable def irrationalityExponent (ξ : ℝ) : ℝ≥0∞ :=
  ⨆ (p : ℝ≥0) (_ : LiouvilleWith p ξ), (p : ℝ≥0∞)
end Real
