/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import CorvajaZannier2004.PseudoPisot
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Algebra.Order.Round
public import Mathlib.RingTheory.Trace.Basic

-- Used only inside proofs.
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.Monoid

/-!
# The powers of a Pisot number are near integers

The "well-known argument" of Corvaja–Zannier (Appendix, p. 11): if `β` is a Pisot number, then
`‖βᵐ‖ → 0`, because `βᵐ` plus the `m`-th powers of the other conjugates is a rational integer.

## Main results

* `sum_aroots_pow_eq_trace`: the `m`-th power sum of the conjugates of `x` is
  `Tr_{ℚ(x)/ℚ}(xᵐ)`.
* `exists_intCast_eq_sum_aroots_pow`: for an algebraic integer, it is a rational integer.
* `IsPisot.tendsto_abs_sub_round`: `|βᵐ - round βᵐ| → 0` for a Pisot number `β`.

## References

P. Corvaja and U. Zannier, Acta Math. **193** (2004), 175–191, Appendix.
-/

@[expose] public section

open Filter Topology IntermediateField Polynomial

/-- **The power sums of the conjugates are traces**: `∑ zᵐ` over the complex conjugates `z` of
`x` is `Tr_{ℚ(x)/ℚ}(xᵐ)`, the embeddings of `ℚ(x)` into `ℂ` being given by the conjugates. -/
theorem sum_aroots_pow_eq_trace {x : ℝ} (hx : IsIntegral ℚ x) (m : ℕ) :
    (((minpoly ℚ x).aroots ℂ).map (· ^ m)).sum =
      algebraMap ℚ ℂ (Algebra.trace ℚ ℚ⟮x⟯ (AdjoinSimple.gen ℚ x ^ m)) := by
  classical
  have := adjoin.finiteDimensional hx
  set pb := adjoin.powerBasis hx with hpb
  have hgen : pb.gen = AdjoinSimple.gen ℚ x := adjoin.powerBasis_gen hx
  have hmin : minpoly ℚ pb.gen = minpoly ℚ x := by rw [hgen, minpoly_gen]
  have hnodup : ((minpoly ℚ x).aroots ℂ).Nodup :=
    nodup_roots ((separable_map _).mpr (minpoly.irreducible hx).separable)
  rw [trace_eq_sum_embeddings (E := ℂ),
    Fintype.sum_equiv pb.liftEquiv' _ (fun y ↦ (y : ℂ) ^ m) (fun σ ↦ by
      rw [PowerBasis.liftEquiv'_apply_coe, ← hgen, map_pow]),
    Finset.sum_mem_multiset _ _ (fun y ↦ y ^ m) (fun _ ↦ rfl), Finset.sum_eq_multiset_sum,
    Multiset.toFinset_val, Multiset.dedup_eq_self.mpr (hmin ▸ hnodup), hmin]

/-- **The power sums of the conjugates of an algebraic integer are rational integers.** -/
theorem exists_intCast_eq_sum_aroots_pow {x : ℝ} (hx : IsIntegral ℤ x) (m : ℕ) :
    ∃ t : ℤ, (((minpoly ℚ x).aroots ℂ).map (· ^ m)).sum = t := by
  have hxQ : IsIntegral ℚ x := hx.tower_top
  have := adjoin.finiteDimensional hxQ
  have hgen : IsIntegral ℤ (AdjoinSimple.gen ℚ x) := by
    have hinj : Function.Injective ((ℚ⟮x⟯.val : ℚ⟮x⟯ →ₐ[ℚ] ℝ).restrictScalars ℤ) :=
      Subtype.val_injective
    exact (isIntegral_algHom_iff _ hinj).mp (by simpa using hx)
  obtain ⟨t, ht⟩ :=
    IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_trace (L := ℚ) (hgen.pow m))
  refine ⟨t, ?_⟩
  rw [sum_aroots_pow_eq_trace hxQ, ← ht]
  simp

/-- **P.2: the powers of a Pisot number are near integers**: `|βᵐ - round βᵐ| → 0`. -/
theorem IsPisot.tendsto_abs_sub_round {β : ℝ} (h : IsPisot β) :
    Tendsto (fun m : ℕ ↦ |β ^ m - round (β ^ m)|) atTop (𝓝 0) := by
  obtain ⟨-, hint, hconj⟩ := h
  have hxQ : IsIntegral ℚ β := hint.tower_top
  set s := (minpoly ℚ β).aroots ℂ with hs
  have hmem : (β : ℂ) ∈ s := mem_aroots_minpoly hxQ.isAlgebraic
  have hnodup : s.Nodup :=
    nodup_roots ((separable_map _).mpr (minpoly.irreducible hxQ).separable)
  set s' := s.erase (β : ℂ) with hs'def
  have hs' : ∀ z ∈ s', ‖z‖ < 1 := fun z hz ↦
    hconj z (Multiset.mem_of_mem_erase hz) ((hnodup.mem_erase_iff).mp hz).1
  -- the other conjugates contribute `o(1)`
  have hlim : Tendsto (fun m : ℕ ↦ (s'.map fun z ↦ z ^ m).sum) atTop (𝓝 0) := by
    have := tendsto_multiset_sum (f := fun z (m : ℕ) ↦ z ^ m) (a := fun _ ↦ (0 : ℂ)) s'
      fun z hz ↦ tendsto_pow_atTop_nhds_zero_of_norm_lt_one (hs' z hz)
    simpa using this
  have hbound : ∀ m : ℕ, |β ^ m - round (β ^ m)| ≤ ‖(s'.map fun z ↦ z ^ m).sum‖ := fun m ↦ by
    obtain ⟨t, ht⟩ := exists_intCast_eq_sum_aroots_pow hint m
    rw [← hs, ← Multiset.cons_erase hmem, Multiset.map_cons, Multiset.sum_cons] at ht
    have : (s'.map fun z ↦ z ^ m).sum = ((t - β ^ m : ℝ) : ℂ) := by
      push_cast
      linear_combination ht
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm (t : ℝ)]
    exact round_le (β ^ m) t
  exact squeeze_zero (fun _ ↦ abs_nonneg _) hbound (by simpa using hlim.norm)
