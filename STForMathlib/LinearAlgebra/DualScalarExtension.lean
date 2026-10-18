/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Pi

-- Used only inside proofs.
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.StdBasis

/-!
# Independent linear forms stay independent after extending the scalars of their values

For a field extension `F/K` and `K`-linearly independent linear forms `f_j : V → K`, finitely
many, the functions `x ↦ f_j(x)` with values in `F` are `F`-linearly independent in `V → F`. The
map `x ↦ (f_j(x))_j` is onto `Kᴶ`: a functional on `Kᴶ` vanishing on its range is a relation
between the `f_j`. So there are points `u_i` with `f_j(u_i) = δ_{ij}`, and evaluating an
`F`-relation at them kills each coefficient.

## Main results

* `Module.Dual.surjective_pi_of_linearIndependent`: the evaluation map is onto.
* `Module.Dual.linearIndependent_algebraMap_comp`: **the transfer**.
-/

@[expose] public section

open Module

namespace Module.Dual

variable {K V J : Type*} [Field K] [AddCommGroup V] [Module K V] [Finite J]

/-- **Independent forms have a surjective evaluation map** `x ↦ (f_j x)_j`. -/
theorem surjective_pi_of_linearIndependent {f : J → Dual K V} (hf : LinearIndependent K f) :
    Function.Surjective (LinearMap.pi f) := by
  have := Fintype.ofFinite J
  classical
  rw [← LinearMap.range_eq_top]
  by_contra h
  obtain ⟨g, hg0, hg⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 h) inferInstance
  have hrel : ∑ j, g (Pi.single j 1) • f j = 0 := by
    ext x
    have hx : g (LinearMap.pi f x) = 0 := by
      have : g (LinearMap.pi f x) ∈ (LinearMap.range (LinearMap.pi f)).map g :=
        ⟨_, ⟨x, rfl⟩, rfl⟩
      rw [hg] at this
      exact (Submodule.mem_bot K).1 this
    have hsum : LinearMap.pi f x = ∑ j, f j x • (Pi.single j 1 : J → K) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hsum, map_sum] at hx
    simpa [mul_comm] using hx
  have hcoef := Fintype.linearIndependent_iff.1 hf _ hrel
  apply hg0
  refine LinearMap.pi_ext' fun j ↦ ?_
  ext
  simpa using hcoef j

variable (F : Type*) [Field F] [Algebra K F]

/-- **Independent `K`-valued forms are `F`-independent as `F`-valued functions.** -/
theorem linearIndependent_algebraMap_comp {f : J → Dual K V} (hf : LinearIndependent K f) :
    LinearIndependent F fun j (x : V) ↦ algebraMap K F (f j x) := by
  have := Fintype.ofFinite J
  classical
  choose u hu using surjective_pi_of_linearIndependent hf
  have hfu : ∀ i j, f j (u (Pi.single i 1)) = if i = j then 1 else 0 := by
    intro i j
    have := congrFun (hu (Pi.single i 1)) j
    simp only [LinearMap.pi_apply] at this
    rw [this, Pi.single_apply]
    exact if_congr eq_comm rfl rfl
  refine Fintype.linearIndependent_iff.2 fun a ha i ↦ ?_
  have h := congrFun ha (u (Pi.single i 1))
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hfu] at h
  simpa using h

end Module.Dual
