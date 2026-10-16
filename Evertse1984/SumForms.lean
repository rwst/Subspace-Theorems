/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.SumForms
-- Used only inside proofs.
import DiophantineApproximation.NormForm
import DiophantineApproximation.SubspaceAffine

/-!
# The Subspace step of Evertse's proof

In the proof of Theorem 2 (§2, p. 232) Evertse applies Schlickewei's `p`-adic Subspace Theorem
(his Theorem 4) to the sum forms (`NumberField.sumForms`, `DiophantineApproximation/SumForms.lean`):
at a place `v` of `T` the coordinates, except that the largest one at `v` is replaced by the sum
`x₀ + ⋯ + xₘ`; at a place of `S` outside `T`, the coordinates. Theorem 4 is the affine Subspace
Theorem of Layer 6.4, and Evertse's size `‖x‖ ^ (-ε)` is traded for the height
`H(x) ^ (-ε / [K : ℚ])`.

## Main results

* `NumberField.exists_finset_submodule_of_prod_placeProd_le`: **the Subspace step**, the points
  with small product lie in finitely many proper subspaces.

## References

J.-H. Evertse, *On sums of `S`-units and linear recurrences*, Compositio Math. **53** (1984),
225–244, §2.
-/

@[expose] public section

open IsDedekindDomain Height Module

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **The Subspace step of Evertse's proof.** For a choice `r` of largest coordinates at the
places `T = {v | r v ≠ none}` and `ε > 0`, the points of `𝓞_Kⁿ⁺¹` with nonzero coordinates, the
largest coordinate at each `v ∈ T` the one `r` names, and

```text
(∏_{k} ∏_{v ∈ S} ‖x_k‖_v) · ∏_{v ∈ T} ‖x₀ + ⋯ + xₘ‖_v ≤ (∏_{v ∈ T} max_k ‖x_k‖_v) · ‖x‖ ^ (-ε)
```

(Evertse's (20)) lie in finitely many proper subspaces. -/
theorem exists_finset_submodule_of_prod_placeProd_le [Nontrivial ι]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (r : AbsoluteValue K ℝ → Option ι) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ Ws : Finset (Submodule K (ι → K)), (∀ W ∈ Ws, W ≠ ⊤) ∧
      ∀ x : ι → K, (∀ i, IsIntegral ℤ (x i)) → (∀ i, x i ≠ 0) →
        (∀ v i, r v = some i → v (x i) = ⨆ j, v (x j)) →
        (∏ i, placeProd S Set.univ (fun w ↦ w (x i))) *
            placeProd S {w | (r w).isSome} (fun w ↦ w (∑ j, x j)) ≤
          placeProd S {w | (r w).isSome} (fun w ↦ ⨆ j, w (x j)) * (⨆ i, house (x i)) ^ (-ε) →
        ∃ W ∈ Ws, x ∈ W := by
  classical
  set D : ℕ := finrank ℚ K with hD
  have hDpos : (0 : ℝ) < D := by exact_mod_cast Module.finrank_pos
  obtain ⟨Ws, hWs, hcov⟩ := exists_finset_submodule_of_integer_of_affineProd_le (F := K) S
    (fun v ↦ v) (fun _ ↦ ⟨AbsoluteValue.ext fun _ ↦ rfl⟩)
    (fun _ _ ↦ ⟨AbsoluteValue.ext fun _ ↦ rfl⟩) (sumForms r)
    (fun v ↦ linearIndependent_sumForms r v.1) (fun _ _ ↦ linearIndependent_sumForms r _)
    (ε := ε / D) (by positivity)
  refine ⟨Ws, hWs, fun x hint hx0 hr hle ↦ ?_⟩
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  have hx : x ≠ 0 := fun h ↦ hx0 i₀ (congrFun h i₀)
  refine hcov x hx (fun i ↦ mem_integer_of_isIntegral (hint i)) ?_
  have hM : 0 < placeProd S {w | (r w).isSome} (fun w ↦ ⨆ j, w (x j)) :=
    placeProd_pos S _ fun w _ ↦ (AbsoluteValue.pos w (hx0 i₀)).trans_le
      (le_ciSup (f := fun j ↦ w (x j)) (Finite.bddAbove_range _) i₀)
  have hh : 0 < ⨆ i, house (x i) := zero_lt_one.trans_le (one_le_iSup_house (hint i₀) (hx0 i₀))
  have h1 : affineProd S (fun v ↦ v) (sumForms r) x ≤ (⨆ i, house (x i)) ^ (-ε) := by
    refine le_of_mul_le_mul_right ?_ hM
    rw [affineProd_sumForms_mul S r x hr, mul_comm ((⨆ i, house (x i)) ^ (-ε))]
    exact hle
  refine h1.trans ?_
  calc (⨆ i, house (x i)) ^ (-ε) = ((⨆ i, house (x i)) ^ D) ^ (-(ε / D)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le]
        congr 1
        field_simp
    _ ≤ mulHeight x ^ (-(ε / D)) :=
        Real.rpow_le_rpow_of_nonpos (mulHeight_pos x) (mulHeight_le_iSup_house_pow hx hint)
          (neg_nonpos.mpr (by positivity))

end NumberField
