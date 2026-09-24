/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.ApproxProd
public import DiophantineApproximation.ApproximationDomain

-- Used only inside proofs.
import DiophantineApproximation.UnitNormalization

/-!
# The reduction of the Subspace Theorem to approximation domains

For a number field `K`, finite sets `Sinf` of infinite and `Sfin` of finite places, forms
`L v i` on `Kⁱ` with coefficients in `K` and `ε > 0`, every point `x ≠ 0` with

```text
approxProd Sinf Sfin L x ≤ H(x) ^ (-#ι - ε)
```

and large height either lies on the kernel of one of the forms or has a scalar multiple in
`approxDomain Sfin' L' c (H(x))` for one of **finitely many** exponent systems `c`, each of weight
at most `-ε/2` — Bombieri–Gubler's 7.5.6. Here `Sfin' ⊇ Sfin` is the enlargement of Theorem 7.2.6
(`UnitNormalization.lean`) and `L'` agrees with `L` on `Sinf` and `Sfin` and is the coordinate
forms at the added places, infinite and finite, whose local factor is at most `1`, so the
inequality survives. This is Layer 5.1 read as a whole: Layer 6.2 is Layer 6.1 applied to each of
the finitely many `c`, plus the kernels, plus Northcott for the small heights.

The exponents are read off the point: `c v i` is `log v (L v i y) / log H(x)` rounded up to the
grid `ℤ / N`, `y` the normalized multiple of Lemma 7.5.4; by Corollary 7.5.5 they lie in
`[-2, 2]` once `log H(x)` exceeds the constant, so they lie in a finite set, and the weight is at
most `log (approxProd y · H(x) ^ #ι) / log H(x) + #ι D / N ≤ -ε + ε / 2`, with `D` the number of
places counted with multiplicity.

## Main results

* `NumberField.approxProd_le_approxProd_of_subset`: enlarging the places, with forms whose local
  factor is at most `1` at the new ones, can only decrease the central quantity;
  `NumberField.prod_proj_div_iSup_le_one`: the coordinate forms are such forms.
* `NumberField.exists_finset_superset_forall_approxProd_le`: the prologue of the proof — every
  infinite place and enough finite places for primitive multiples, with the coordinate forms.
* `NumberField.log_approxProd_eq`: the central quantity at a primitive point.
* `NumberField.exists_finset_forall_exists_smul_mem_approxDomain`: Bombieri–Gubler 7.5.6.
* `NumberField.exists_forall_approxProd_le_imp`: the three together.

## Implementation notes

⚠ **The classes are cells of a cube, not of the simplex, and Layer 3.1 is not reused.** Roth's
approximation classes (Layer 3.1) index the points of the unit simplex, because in Roth's theorem
every local factor is at most `1`. Here the exponents `log v (L v i y) / log H(x)` have both
signs, and all that bounds them is Corollary 7.5.5; the classes are the cells of edge `1/N` of
the cube `[-2, 2]`, as in the book, and the count is the finiteness of a set of functions with
finite support and values in a finite grid. Nor is the book's pigeonhole needed: the statement is
parametric in `x`, not along an infinite sequence of solutions.

⚠ **The exponents live on `AbsoluteValue K ℝ`, so finitely many of them must vanish off the
places.** An exponent system is a function of an absolute value, and those of the classes are `0`
away from the infinite places and `Sfin`; that is what makes the set of them finite.

⚠ **A level `Q₀` is part of the statement.** The weight bound is `-ε + log C / log Q + #ι D / N`
and the exponents lie in `[-2, 2]` only for `log Q ≥ C`, so small heights are excluded; Layer 6.2
disposes of them by Northcott.

⚠ **The kernels are not avoided.** A point on the kernel of `L' v i` meets that condition of a
domain at every exponent, and could be given a very negative one, but no bound on the remaining
exponents follows from `approxProd = 0`; the book removes those points, and so does this statement.

⚠ **`approxProd` is taken with `F = K` and `w = id`**, and the prologue needs
`AbsoluteValue.liesOver_self`, which Mathlib does not state.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Theorem 7.2.6 and 7.5.6.

This is Layer 5.1 (second half) of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Height Module

namespace AbsoluteValue

variable {K : Type*} [Field K]

/-- Every absolute value lies over itself, along the identity of `K`. -/
theorem liesOver_self (v : AbsoluteValue K ℝ) : v.LiesOver v :=
  ⟨AbsoluteValue.ext fun _ ↦ rfl⟩

end AbsoluteValue

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*}

/-!
### Enlarging the places
-/

/-- An infinite place and a finite place are different absolute values: `|2| = 2` at the first
and `|2| ≤ 1` at the second. -/
private theorem InfinitePlace.coe_ne_coe (w : InfinitePlace K) (v : FinitePlace K) :
    w.1 ≠ v.1 := by
  intro h
  have h2 := FinitePlace.add_le v 1 1
  change v.1 (1 + 1) ≤ max (v.1 1) (v.1 1) at h2
  have h3 : w.1 (1 + 1) = 2 := by
    have := w.map_natCast 2
    rw [Nat.cast_ofNat, Nat.cast_ofNat] at this
    rw [one_add_one_eq_two]
    exact this
  rw [← h, h3, map_one, max_self] at h2
  norm_num at h2

omit [NumberField K] in
/-- The coordinate forms are linearly independent. -/
theorem linearIndependent_proj [Finite ι] :
    LinearIndependent K fun i : ι ↦ (LinearMap.proj i : Dual K (ι → K)) := by
  let _i : Fintype ι := Fintype.ofFinite ι
  classical
  refine linearIndependent_iff'.2 fun s g hg i hi ↦ ?_
  have := congrArg (fun f : Dual K (ι → K) ↦ f (Pi.single i 1)) hg
  simpa [Finset.sum_apply, Pi.single_apply, hi] using this

variable {F : Type*} [Field F] [Algebra K F]

omit [NumberField K] in
/-- **The local factor of the coordinate forms is at most `1`.** -/
theorem prod_proj_div_iSup_le_one [Fintype ι] (W : AbsoluteValue F ℝ)
    (v : AbsoluteValue K ℝ) [W.LiesOver v] (x : ι → K) :
    ∏ i, W ((LinearMap.proj i : Dual F (ι → F)) fun j ↦ algebraMap K F (x j)) /
      ⨆ j, v (x j) ≤ 1 := by
  refine Finset.prod_le_one₀ (fun i _ ↦ div_nonneg (W.nonneg _)
    (Real.iSup_nonneg fun j ↦ v.nonneg _)) fun i _ ↦ ?_
  rw [LinearMap.proj_apply, AbsoluteValue.apply_algebraMap_of_liesOver (v := v) W]
  exact div_le_one_of_le₀ (le_ciSup_of_le (Finite.bddAbove_range _) i le_rfl)
    (Real.iSup_nonneg fun j ↦ v.nonneg _)

/-- **Enlarging the places can only decrease the central quantity**, if the forms at the new
places have local factor at most `1` and those at the old places are unchanged. -/
theorem approxProd_le_approxProd_of_subset [Fintype ι] {Sinf Sinf' : Finset (InfinitePlace K)}
    {Sfin Sfin' : Finset (FinitePlace K)} (hinf : Sinf ⊆ Sinf') (hfin : Sfin ⊆ Sfin')
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) {L L' : AbsoluteValue K ℝ → ι → Dual F (ι → F)}
    (hLinf : ∀ v ∈ Sinf, L' v.1 = L v.1) (hLfin : ∀ v ∈ Sfin, L' v.1 = L v.1) (x : ι → K)
    (hnewInf : ∀ v ∈ Sinf', v ∉ Sinf →
      ∏ i, w v.1 (L' v.1 i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) ≤ 1)
    (hnewFin : ∀ v ∈ Sfin', v ∉ Sfin →
      ∏ i, w v.1 (L' v.1 i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) ≤ 1) :
    approxProd Sinf' Sfin' w L' x ≤ approxProd Sinf Sfin w L x := by
  classical
  have hfac : ∀ (v : AbsoluteValue K ℝ) (M : ι → Dual F (ι → F)),
      (0 : ℝ) ≤ ∏ i, w v (M i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) := fun v M ↦
    Finset.prod_nonneg fun i _ ↦ div_nonneg (AbsoluteValue.nonneg _ _)
      (Real.iSup_nonneg fun j ↦ v.nonneg _)
  have e1 : ∏ v ∈ Sinf, (∏ i, w v.1 (L' v.1 i fun j ↦ algebraMap K F (x j)) /
      ⨆ j, v (x j)) ^ v.mult = ∏ v ∈ Sinf, (∏ i, w v.1 (L v.1 i fun j ↦ algebraMap K F (x j)) /
      ⨆ j, v (x j)) ^ v.mult := Finset.prod_congr rfl fun v hv ↦ by rw [hLinf v hv]
  have e2 : ∏ v ∈ Sfin, ∏ i, w v.1 (L' v.1 i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) =
      ∏ v ∈ Sfin, ∏ i, w v.1 (L v.1 i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) :=
    Finset.prod_congr rfl fun v hv ↦ by rw [hLfin v hv]
  unfold approxProd
  rw [← Finset.prod_sdiff hinf, ← Finset.prod_sdiff hfin, e1, e2]
  have h1 : ∏ v ∈ Sinf' \ Sinf,
      (∏ i, w v.1 (L' v.1 i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)) ^ v.mult ≤ 1 :=
    Finset.prod_le_one₀ (fun v _ ↦ pow_nonneg (hfac _ _) _) fun v hv ↦
      pow_le_one₀ (hfac _ _) (hnewInf v (Finset.mem_sdiff.1 hv).1 (Finset.mem_sdiff.1 hv).2)
  have h2 : ∏ v ∈ Sfin' \ Sfin,
      ∏ i, w v.1 (L' v.1 i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) ≤ 1 :=
    Finset.prod_le_one₀ (fun v _ ↦ hfac _ _) fun v hv ↦
      hnewFin v (Finset.mem_sdiff.1 hv).1 (Finset.mem_sdiff.1 hv).2
  have h3 : 0 ≤ ∏ v ∈ Sinf, (∏ i, w v.1 (L v.1 i fun j ↦ algebraMap K F (x j)) /
      ⨆ j, v (x j)) ^ v.mult := Finset.prod_nonneg fun v _ ↦ pow_nonneg (hfac _ _) _
  have h4 : 0 ≤ ∏ v ∈ Sfin, ∏ i, w v.1 (L v.1 i fun j ↦ algebraMap K F (x j)) /
      ⨆ j, v (x j) := Finset.prod_nonneg fun v _ ↦ hfac _ _
  calc _ ≤ (1 * ∏ v ∈ Sinf, (∏ i, w v.1 (L v.1 i fun j ↦ algebraMap K F (x j)) /
        ⨆ j, v (x j)) ^ v.mult) * (1 * ∏ v ∈ Sfin, ∏ i, w v.1 (L v.1 i fun j ↦
          algebraMap K F (x j)) / ⨆ j, v (x j)) := by
        gcongr
        · exact mul_nonneg (Finset.prod_nonneg fun v _ ↦ hfac _ _) h4
    _ = _ := by rw [one_mul, one_mul]

/-- **The prologue of the Subspace Theorem** (Bombieri–Gubler, Theorem 7.2.6 and the opening of
7.5.3): every infinite place and enough finite places that every point has a primitive
multiple, with the coordinate forms at the added places. The forms are independent at every
place of the enlarged sets, agree with the given ones at the given places, and the central
quantity can only decrease. -/
theorem exists_finset_superset_forall_approxProd_le [Fintype ι]
    (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K))
    (hLInf : ∀ v ∈ Sinf, LinearIndependent K (L v.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) :
    ∃ Sfin' : Finset (FinitePlace K), Sfin ⊆ Sfin' ∧
      (∀ x : ι → K, x ≠ 0 → ∃ t : K, t ≠ 0 ∧
        ∀ v : FinitePlace K, v ∉ Sfin' → ⨆ i, v ((t • x) i) = 1) ∧
      ∃ L' : AbsoluteValue K ℝ → ι → Dual K (ι → K),
        (∀ v ∈ Sinf, L' v.1 = L v.1) ∧ (∀ v ∈ Sfin, L' v.1 = L v.1) ∧
        (∀ w : InfinitePlace K, LinearIndependent K (L' w.1)) ∧
        (∀ v ∈ Sfin', LinearIndependent K (L' v.1)) ∧
        ∀ x : ι → K,
          approxProd Finset.univ Sfin' (fun v ↦ v) L' x ≤ approxProd Sinf Sfin (fun v ↦ v) L x := by
  classical
  obtain ⟨Sfin', hsub, hprim⟩ := exists_finset_superset_forall_exists_iSup_eq_one Sfin
  set P : Set (AbsoluteValue K ℝ) := (fun w : InfinitePlace K ↦ w.1) '' (Sinf : Set _) ∪
    (fun v : FinitePlace K ↦ v.1) '' (Sfin : Set _) with hP
  set L' : AbsoluteValue K ℝ → ι → Dual K (ι → K) := fun v ↦
    if v ∈ P then L v else fun i ↦ LinearMap.proj i with hL'
  have hPI : ∀ w : InfinitePlace K, w.1 ∈ P ↔ w ∈ Sinf := by
    intro w
    refine ⟨fun h ↦ ?_, fun h ↦ Or.inl ⟨w, h, rfl⟩⟩
    rcases h with ⟨w', hw', h⟩ | ⟨v, -, h⟩
    · rwa [← Subtype.ext h]
    · exact absurd h.symm (InfinitePlace.coe_ne_coe w v)
  have hPF : ∀ v : FinitePlace K, v.1 ∈ P ↔ v ∈ Sfin := by
    intro v
    refine ⟨fun h ↦ ?_, fun h ↦ Or.inr ⟨v, h, rfl⟩⟩
    rcases h with ⟨w, -, h⟩ | ⟨v', hv', h⟩
    · exact absurd h (InfinitePlace.coe_ne_coe w v)
    · rwa [← Subtype.ext h]
  have hL'I : ∀ w : InfinitePlace K, L' w.1 = if w ∈ Sinf then L w.1 else
      fun i ↦ LinearMap.proj i := fun w ↦ by simp only [hL', hPI]
  have hL'F : ∀ v : FinitePlace K, L' v.1 = if v ∈ Sfin then L v.1 else
      fun i ↦ LinearMap.proj i := fun v ↦ by simp only [hL', hPF]
  refine ⟨Sfin', hsub, fun x hx ↦ hprim x hx, L', fun v hv ↦ by simp [hL'I, hv],
    fun v hv ↦ by simp [hL'F, hv], fun w ↦ ?_, fun v _ ↦ ?_, fun x ↦ ?_⟩
  · rw [hL'I]
    split_ifs with hw
    · exact hLInf w hw
    · exact linearIndependent_proj
  · rw [hL'F]
    split_ifs with hv
    · exact hLFin v hv
    · exact linearIndependent_proj
  · refine approxProd_le_approxProd_of_subset (Finset.subset_univ _) hsub _
      (fun v hv ↦ by simp [hL'I, hv]) (fun v hv ↦ by simp [hL'F, hv]) x
      (fun v _ hv ↦ ?_) (fun v _ hv ↦ ?_)
    · have := AbsoluteValue.liesOver_self v.1
      simp only [hL'I, hv, ↓reduceIte]
      exact prod_proj_div_iSup_le_one (F := K) _ v.1 x
    · have := AbsoluteValue.liesOver_self v.1
      simp only [hL'F, hv, ↓reduceIte]
      exact prod_proj_div_iSup_le_one (F := K) _ v.1 x

/-!
### The central quantity at a primitive point
-/

omit [NumberField K] in
private theorem log_prod_div_eq {W V κ : Type*} [Fintype W] [Fintype κ] (S : Finset V)
    (m : W → ℕ) (a : W → κ → ℝ) (s : W → ℝ) (b : V → κ → ℝ) (t : V → ℝ)
    (ha : ∀ w i, 0 < a w i) (hs : ∀ w, 0 < s w) (hb : ∀ v ∈ S, ∀ i, 0 < b v i)
    (ht : ∀ v ∈ S, 0 < t v) :
    Real.log ((∏ w, (∏ i, a w i / s w) ^ m w) * ∏ v ∈ S, ∏ i, b v i / t v) =
      (∑ w, (m w : ℝ) * ∑ i, Real.log (a w i) + ∑ v ∈ S, ∑ i, Real.log (b v i)) -
        Fintype.card κ * (∑ w, (m w : ℝ) * Real.log (s w) + ∑ v ∈ S, Real.log (t v)) := by
  have hfa : ∀ w, 0 < ∏ i, a w i / s w := fun w ↦
    Finset.prod_pos fun i _ ↦ div_pos (ha w i) (hs w)
  have hfb : ∀ v ∈ S, 0 < ∏ i, b v i / t v := fun v hv ↦
    Finset.prod_pos fun i _ ↦ div_pos (hb v hv i) (ht v hv)
  rw [Real.log_mul (Finset.prod_ne_zero_iff.2 fun w _ ↦ pow_ne_zero _ (hfa w).ne')
      (Finset.prod_ne_zero_iff.2 fun v hv ↦ (hfb v hv).ne'),
    Real.log_prod (fun w _ ↦ pow_ne_zero _ (hfa w).ne'),
    Real.log_prod (fun v hv ↦ (hfb v hv).ne')]
  have e1 : ∀ w, Real.log ((∏ i, a w i / s w) ^ m w) =
      m w * ∑ i, Real.log (a w i) - Fintype.card κ * (m w * Real.log (s w)) := by
    intro w
    rw [Real.log_pow, Real.log_prod fun i _ ↦ (div_pos (ha w i) (hs w)).ne']
    simp only [Real.log_div (ha w _).ne' (hs w).ne', Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    ring
  have e2 : ∀ v ∈ S, Real.log (∏ i, b v i / t v) =
      ∑ i, Real.log (b v i) - Fintype.card κ * Real.log (t v) := by
    intro v hv
    rw [Real.log_prod fun i _ ↦ (div_pos (hb v hv i) (ht v hv)).ne']
    simp only [Real.log_div (hb v hv _).ne' (ht v hv).ne', Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.sum_congr rfl fun w _ ↦ e1 w, Finset.sum_congr rfl e2, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- The central quantity with coefficients in `K`, written out. -/
theorem approxProd_univ_self_eq [Fintype ι] (Sfin : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) (y : ι → K) :
    approxProd Finset.univ Sfin (fun v ↦ v) L y =
      (∏ w : InfinitePlace K, (∏ i, w (L w.1 i y) / ⨆ j, w (y j)) ^ w.mult) *
        ∏ v ∈ Sfin, ∏ i, v (L v.1 i y) / ⨆ j, v (y j) := by
  simp only [approxProd, Algebra.algebraMap_self, RingHom.id_apply]
  rfl

/-- The central quantity is positive at a nonzero point where no form vanishes. -/
theorem approxProd_univ_self_pos [Fintype ι] {Sfin : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} {y : ι → K} (hy : y ≠ 0)
    (hLI : ∀ (w : InfinitePlace K) i, L w.1 i y ≠ 0) (hLF : ∀ v ∈ Sfin, ∀ i, L v.1 i y ≠ 0) :
    0 < approxProd Finset.univ Sfin (fun v ↦ v) L y := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, y i ≠ 0 := Function.ne_iff.mp hy
  have hpos : ∀ v : AbsoluteValue K ℝ, 0 < ⨆ i, v (y i) := fun v ↦
    lt_of_lt_of_le (v.pos hi₀) (le_ciSup_of_le (Finite.bddAbove_range _) i₀ le_rfl)
  rw [approxProd_univ_self_eq]
  refine mul_pos (Finset.prod_pos fun w _ ↦ pow_pos (Finset.prod_pos fun i _ ↦
    div_pos (w.pos_iff.2 (hLI w i)) (hpos w.1)) _) (Finset.prod_pos fun v hv ↦
    Finset.prod_pos fun i _ ↦ div_pos (FinitePlace.pos_iff.2 (hLF v hv i)) (hpos v.1))

/-- **The central quantity at a primitive point**: its logarithm is the weighted sum of the
logarithms of the form values, minus `#ι` times the height, the height being the product of the
local sup norms over the places (`NumberField.mulHeight_eq_prod_of_forall_iSup_eq_one`). -/
theorem log_approxProd_eq [Fintype ι] {Sfin : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)} {y : ι → K} (hy : y ≠ 0)
    (hprim : ∀ v : FinitePlace K, v ∉ Sfin → ⨆ i, v (y i) = 1)
    (hLI : ∀ (w : InfinitePlace K) i, L w.1 i y ≠ 0) (hLF : ∀ v ∈ Sfin, ∀ i, L v.1 i y ≠ 0) :
    Real.log (approxProd Finset.univ Sfin (fun v ↦ v) L y) =
      (∑ w : InfinitePlace K, (w.mult : ℝ) * ∑ i, Real.log (w (L w.1 i y)) +
        ∑ v ∈ Sfin, ∑ i, Real.log (v (L v.1 i y))) - Fintype.card ι * logHeight y := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, y i ≠ 0 := Function.ne_iff.mp hy
  have hpos : ∀ v : AbsoluteValue K ℝ, 0 < ⨆ i, v (y i) := fun v ↦
    lt_of_lt_of_le (v.pos hi₀) (le_ciSup_of_le (Finite.bddAbove_range _) i₀ le_rfl)
  have hposI : ∀ w : InfinitePlace K, 0 < ⨆ i, w (y i) := fun w ↦ hpos w.1
  have hposF : ∀ v : FinitePlace K, 0 < ⨆ i, v (y i) := fun v ↦ hpos v.1
  have hH : logHeight y = ∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (⨆ i, w (y i)) +
      ∑ v ∈ Sfin, Real.log (⨆ i, v (y i)) := by
    rw [logHeight_eq_log_mulHeight, mulHeight_eq_prod_of_forall_iSup_eq_one hy hprim,
      Real.log_mul (Finset.prod_ne_zero_iff.2 fun w _ ↦ pow_ne_zero _ (hposI w).ne')
        (Finset.prod_ne_zero_iff.2 fun v _ ↦ (hposF v).ne'),
      Real.log_prod (fun w _ ↦ pow_ne_zero _ (hposI w).ne'),
      Real.log_prod (fun v _ ↦ (hposF v).ne')]
    simp only [Real.log_pow]
  rw [approxProd_univ_self_eq, hH]
  exact log_prod_div_eq (W := InfinitePlace K) (V := FinitePlace K) (κ := ι) Sfin
    (fun w : InfinitePlace K ↦ w.mult) (fun (w : InfinitePlace K) (i : ι) ↦ w (L w.1 i y))
    (fun w : InfinitePlace K ↦ ⨆ j, w (y j)) (fun (v : FinitePlace K) (i : ι) ↦ v (L v.1 i y))
    (fun v : FinitePlace K ↦ ⨆ j, v (y j)) (fun w i ↦ w.pos_iff.2 (hLI w i)) hposI
    (fun v hv i ↦ FinitePlace.pos_iff.2 (hLF v hv i)) (fun v _ ↦ hposF v)

/-!
### The approximation classes
-/

omit [NumberField K] in
private theorem finite_setOf_forall_notMem_eq_zero {α κ : Type*} [Finite κ] {P : Set α}
    (hP : P.Finite) (G : Finset ℝ) :
    {c : α → κ → ℝ | (∀ v ∉ P, ∀ i, c v i = 0) ∧ ∀ v ∈ P, ∀ i, c v i ∈ G}.Finite := by
  have : Finite P := hP.to_subtype
  refine Set.Finite.of_finite_image (f := fun c (v : P) (i : κ) ↦ c v i) ?_ ?_
  · refine (Set.Finite.pi (t := fun _ : P ↦ Set.univ.pi fun _ : κ ↦ (G : Set ℝ))
      fun v ↦ Set.Finite.pi fun i ↦ G.finite_toSet).subset ?_
    rintro _ ⟨c, ⟨-, hc⟩, rfl⟩
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Finset.mem_coe]
    exact fun v i ↦ hc v v.2 i
  · intro c hc c' hc' h
    funext v i
    by_cases hv : v ∈ P
    · exact congrFun (congrFun h ⟨v, hv⟩) i
    · rw [hc.1 v hv i, hc'.1 v hv i]

omit [NumberField K] in
private theorem rpow_div_log_eq {Q a : ℝ} (hQ : 1 < Q) (ha : 0 < a) :
    Q ^ (Real.log a / Real.log Q) = a := by
  rw [Real.rpow_def_of_pos (by linarith), mul_div_cancel₀ _ (Real.log_pos hQ).ne',
    Real.exp_log ha]

/-- **Bombieri–Gubler, 7.5.6: the approximation classes.** If every point has a primitive
multiple for `Sfin`, then for `ε > 0` there are finitely many exponent systems `c`, each of weight
at most `-ε / 2`, and a level `Q₀`, such that every `x ≠ 0` of height at least `Q₀` with no
vanishing form and `approxProd ≤ H(x) ^ (-#ι - ε)` has a scalar multiple in the approximation
domain `approxDomain Sfin L c (H(x))` of one of them. No independence of the forms is used. -/
theorem exists_finset_forall_exists_smul_mem_approxDomain [Fintype ι]
    (Sfin : Finset (FinitePlace K))
    (hS : ∀ x : ι → K, x ≠ 0 → ∃ t : K, t ≠ 0 ∧
      ∀ v : FinitePlace K, v ∉ Sfin → ⨆ i, v ((t • x) i) = 1)
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) {ε : ℝ} (hε : 0 < ε) :
    ∃ 𝒞 : Finset (AbsoluteValue K ℝ → ι → ℝ), (∀ c ∈ 𝒞, approxWeight Sfin c ≤ -ε / 2) ∧
      ∃ Q₀ : ℝ, ∀ x : ι → K, x ≠ 0 →
        (∀ (w : InfinitePlace K) (i : ι), L w.1 i x ≠ 0) → (∀ v ∈ Sfin, ∀ i, L v.1 i x ≠ 0) →
        approxProd Finset.univ Sfin (fun v ↦ v) L x ≤
          mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) →
        Q₀ ≤ mulHeight x →
        ∃ c ∈ 𝒞, ∃ t : K, t ≠ 0 ∧ t • x ∈ approxDomain Sfin L c (mulHeight x) := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_forall_logHeight₁_apply_smul_le Sfin L
  set n : ℕ := Fintype.card ι with hn
  set D : ℝ := ∑ w : InfinitePlace K, (w.mult : ℝ) + Sfin.card with hD
  have hD0 : 0 ≤ D := by positivity
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 2 * n * D / ε < N := exists_nat_gt _
  have hN0 : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
  have hnD : n * D / N ≤ ε / 2 := by
    rw [div_le_iff₀ hN0]
    rw [div_lt_iff₀ hε] at hN
    nlinarith
  set G : Finset ℝ := (Finset.Icc (-(2 * N : ℤ)) (2 * N)).image fun k : ℤ ↦ (k : ℝ) / N with hG
  set P : Set (AbsoluteValue K ℝ) := Set.range (fun w : InfinitePlace K ↦ w.1) ∪
    (fun v : FinitePlace K ↦ v.1) '' (Sfin : Set (FinitePlace K)) with hP
  have hPfin : P.Finite := (Set.finite_range _).union (Sfin.finite_toSet.image _)
  set 𝒞' : Set (AbsoluteValue K ℝ → ι → ℝ) := {c | ((∀ v ∉ P, ∀ i, c v i = 0) ∧
    ∀ v ∈ P, ∀ i, c v i ∈ G) ∧ approxWeight Sfin c ≤ -ε / 2} with h𝒞'
  have h𝒞 : 𝒞'.Finite := (finite_setOf_forall_notMem_eq_zero hPfin G).subset fun c hc ↦ hc.1
  refine ⟨h𝒞.toFinset, fun c hc ↦ (h𝒞.mem_toFinset.1 hc).2, max 2 (Real.exp C), ?_⟩
  intro x hx hLI hLF happ hQ
  set Q : ℝ := mulHeight x with hQdef
  have hQ1 : 1 < Q := by linarith [le_trans (le_max_left _ _) hQ]
  have hlogQ : C ≤ Real.log Q := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact le_trans (le_max_right _ _) hQ
  have hlogQpos : 0 < Real.log Q := Real.log_pos hQ1
  obtain ⟨t₁, ht₁, hprim₁⟩ := hS x hx
  have hx' : t₁ • x ≠ 0 := smul_ne_zero ht₁ hx
  obtain ⟨u, hu0, huS, hHI, hHF⟩ := hC (t₁ • x) hx' hprim₁
  set s : K := u * t₁ with hsdef
  have hs : s ≠ 0 := mul_ne_zero hu0 ht₁
  have hyx : u • t₁ • x = s • x := smul_smul u t₁ x
  rw [hyx] at hHI hHF
  have hlogx' : logHeight (t₁ • x) = Real.log Q := by
    rw [logHeight_smul_eq_logHeight x ht₁, logHeight_eq_log_mulHeight]
  rw [hlogx'] at hHI hHF
  have hprim : ∀ v : FinitePlace K, v ∉ Sfin → ⨆ i, v ((s • x) i) = 1 := by
    intro v hv
    have : ∀ i, v ((s • x) i) = v ((t₁ • x) i) := fun i ↦ by
      simp only [Pi.smul_apply, smul_eq_mul, hsdef, mul_assoc, map_mul, huS v hv, one_mul]
    simp only [this]
    exact hprim₁ v hv
  have hsx : s • x ≠ 0 := smul_ne_zero hs hx
  have hLIy : ∀ (w : InfinitePlace K) i, L w.1 i (s • x) ≠ 0 := fun w i ↦ by
    rw [map_smul, smul_eq_mul]; exact mul_ne_zero hs (hLI w i)
  have hLFy : ∀ v ∈ Sfin, ∀ i, L v.1 i (s • x) ≠ 0 := fun v hv i ↦ by
    rw [map_smul, smul_eq_mul]; exact mul_ne_zero hs (hLF v hv i)
  have hbI : ∀ (w : InfinitePlace K) i, |Real.log (w (L w.1 i (s • x)))| ≤ Real.log Q + C := by
    intro w i
    refine le_trans ?_ ((w.abs_mult_mul_log_le_logHeight₁ (hLIy w i)).trans (hHI w i))
    rw [abs_mul, Nat.abs_cast]
    exact le_mul_of_one_le_left (abs_nonneg _) (by exact_mod_cast w.mult_pos)
  have hbF : ∀ v ∈ Sfin, ∀ i, |Real.log (v (L v.1 i (s • x)))| ≤ Real.log Q + C := fun v hv i ↦
    (v.abs_log_le_logHeight₁ (hLFy v hv i)).trans (hHF v hv i)
  have hratio : ∀ a : ℝ, |Real.log a| ≤ Real.log Q + C → |Real.log a / Real.log Q| ≤ 2 := by
    intro a ha
    rw [abs_div, abs_of_pos hlogQpos, div_le_iff₀ hlogQpos]
    linarith
  have hround : ∀ r : ℝ, r ≤ (⌈N * r⌉ : ℝ) / N ∧ (⌈N * r⌉ : ℝ) / N ≤ r + 1 / N := by
    intro r
    constructor
    · rw [le_div_iff₀ hN0, mul_comm]; exact Int.le_ceil _
    · rw [div_le_iff₀ hN0, add_mul, one_div, inv_mul_cancel₀ hN0.ne', mul_comm]
      exact (Int.ceil_lt_add_one _).le
  have hgrid : ∀ r : ℝ, |r| ≤ 2 → (⌈N * r⌉ : ℝ) / N ∈ G := by
    intro r hr
    rw [abs_le] at hr
    refine Finset.mem_image.2 ⟨⌈N * r⌉, Finset.mem_Icc.2 ⟨?_, ?_⟩, rfl⟩
    · rw [Int.le_ceil_iff]
      push_cast; nlinarith
    · refine Int.ceil_le.2 ?_
      push_cast; nlinarith
  set g : AbsoluteValue K ℝ → ι → ℝ := fun v i ↦
    (⌈N * (Real.log (v (L v i (s • x))) / Real.log Q)⌉ : ℝ) / N with hg
  set c : AbsoluteValue K ℝ → ι → ℝ := fun v i ↦ if v ∈ P then g v i else 0 with hc
  have hcI : ∀ (w : InfinitePlace K) i, c w.1 i = g w.1 i := fun w i ↦
    ite_eq_left_iff.2 fun h ↦ absurd (Or.inl ⟨w, rfl⟩) h
  have hcF : ∀ v ∈ Sfin, ∀ i, c v.1 i = g v.1 i := fun v hv i ↦
    ite_eq_left_iff.2 fun h ↦ absurd (Or.inr ⟨v, hv, rfl⟩) h
  -- the weight
  have hsum : ∑ w : InfinitePlace K, (w.mult : ℝ) * ∑ i, Real.log (w (L w.1 i (s • x))) +
      ∑ v ∈ Sfin, ∑ i, Real.log (v (L v.1 i (s • x))) ≤ -ε * Real.log Q := by
    have h1 := log_approxProd_eq hsx hprim hLIy hLFy
    have h2 : approxProd Finset.univ Sfin (fun v ↦ v) L (s • x) =
        approxProd Finset.univ Sfin (fun v ↦ v) L x :=
      approxProd_smul Finset.univ Sfin (fun v ↦ v) (fun v _ ↦ AbsoluteValue.liesOver_self v.1)
        (fun v _ ↦ AbsoluteValue.liesOver_self v.1) L x hs
    have h3 : Real.log (approxProd Finset.univ Sfin (fun v ↦ v) L (s • x)) ≤
        (-(n : ℝ) - ε) * Real.log Q := by
      rw [← Real.log_rpow (by linarith)]
      exact Real.log_le_log (approxProd_univ_self_pos hsx hLIy hLFy) (h2 ▸ happ)
    rw [h1, logHeight_smul_eq_logHeight x hs, logHeight_eq_log_mulHeight] at h3
    linarith
  have hwt : approxWeight Sfin c ≤ -ε / 2 := by
    have hle : approxWeight Sfin c ≤
        ∑ w : InfinitePlace K, (w.mult : ℝ) *
          ∑ i, (Real.log (w (L w.1 i (s • x))) / Real.log Q + 1 / N) +
        ∑ v ∈ Sfin, ∑ i, (Real.log (v (L v.1 i (s • x))) / Real.log Q + 1 / N) := by
      unfold approxWeight
      simp only [hcI]
      rw [Finset.sum_congr rfl fun v hv ↦ Finset.sum_congr rfl fun i _ ↦ hcF v hv i]
      gcongr with w _ i _ v _ i _
      · exact (hround _).2
      · exact (hround _).2
    have heq : ∑ w : InfinitePlace K, (w.mult : ℝ) *
          ∑ i, (Real.log (w (L w.1 i (s • x))) / Real.log Q + 1 / N) +
        ∑ v ∈ Sfin, ∑ i, (Real.log (v (L v.1 i (s • x))) / Real.log Q + 1 / N) =
        (∑ w : InfinitePlace K, (w.mult : ℝ) * ∑ i, Real.log (w (L w.1 i (s • x))) +
          ∑ v ∈ Sfin, ∑ i, Real.log (v (L v.1 i (s • x)))) / Real.log Q + n * D / N := by
      have e1 : ∀ w : InfinitePlace K, (w.mult : ℝ) *
          ∑ i, (Real.log (w (L w.1 i (s • x))) / Real.log Q + 1 / N) =
          (w.mult * ∑ i, Real.log (w (L w.1 i (s • x)))) / Real.log Q + n / N * w.mult := by
        intro w
        rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, ← hn]
        ring
      have e2 : ∀ v : FinitePlace K,
          ∑ i, (Real.log (v (L v.1 i (s • x))) / Real.log Q + 1 / N) =
          (∑ i, Real.log (v (L v.1 i (s • x)))) / Real.log Q + n / N := by
        intro v
        rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, ← hn]
        ring
      rw [Finset.sum_congr rfl fun w _ ↦ e1 w, Finset.sum_congr rfl fun v _ ↦ e2 v,
        Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div,
        ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hD]
      ring
    have hdiv : (∑ w : InfinitePlace K, (w.mult : ℝ) * ∑ i, Real.log (w (L w.1 i (s • x))) +
          ∑ v ∈ Sfin, ∑ i, Real.log (v (L v.1 i (s • x)))) / Real.log Q ≤ -ε := by
      rw [div_le_iff₀ hlogQpos]; linarith
    linarith
  refine ⟨c, h𝒞.mem_toFinset.2 ⟨⟨fun v hv i ↦ ite_eq_right_iff.2 fun h ↦ absurd h hv,
    fun v hv i ↦ ?_⟩, hwt⟩, s, hs,
    fun w i ↦ ?_, fun v hv i ↦ ?_, fun v hv j ↦ ?_⟩
  · simp only [hc, hv, ↓reduceIte]
    rcases hv with ⟨w, rfl⟩ | ⟨v, hv, rfl⟩
    · exact hgrid _ (hratio _ (hbI w i))
    · exact hgrid _ (hratio _ (hbF v hv i))
  · rw [hcI]
    calc w (L w.1 i (s • x)) = Q ^ (Real.log (w (L w.1 i (s • x))) / Real.log Q) :=
          (rpow_div_log_eq hQ1 (w.pos_iff.2 (hLIy w i))).symm
      _ ≤ Q ^ g w.1 i := Real.rpow_le_rpow_of_exponent_le hQ1.le (hround _).1
  · rw [hcF v hv]
    calc v (L v.1 i (s • x)) = Q ^ (Real.log (v (L v.1 i (s • x))) / Real.log Q) :=
          (rpow_div_log_eq hQ1 (FinitePlace.pos_iff.2 (hLFy v hv i))).symm
      _ ≤ Q ^ g v.1 i := Real.rpow_le_rpow_of_exponent_le hQ1.le (hround _).1
  · rw [← hprim v hv]
    exact le_ciSup_of_le (Finite.bddAbove_range _) j le_rfl

/-- **Layer 5.1: the reduction of the Subspace Theorem to approximation domains.** For forms
independent at the places of `Sinf` and `Sfin` and `ε > 0` there are an enlargement `Sfin'` of
`Sfin`, forms `L'` independent at every infinite place and every place of `Sfin'` and agreeing
with `L` at the given places, finitely many exponent systems of weight at most `-ε / 2` and a level
`Q₀` such that every solution `x ≠ 0` of height at least `Q₀` lies on the kernel of one of the
forms `L'` or has a scalar multiple in the approximation domain, at its own height, of one of the
exponent systems. -/
theorem exists_forall_approxProd_le_imp [Fintype ι]
    (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K))
    (hLInf : ∀ v ∈ Sinf, LinearIndependent K (L v.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ Sfin' : Finset (FinitePlace K), Sfin ⊆ Sfin' ∧
      ∃ L' : AbsoluteValue K ℝ → ι → Dual K (ι → K),
        (∀ v ∈ Sinf, L' v.1 = L v.1) ∧ (∀ v ∈ Sfin, L' v.1 = L v.1) ∧
        (∀ w : InfinitePlace K, LinearIndependent K (L' w.1)) ∧
        (∀ v ∈ Sfin', LinearIndependent K (L' v.1)) ∧
        ∃ 𝒞 : Finset (AbsoluteValue K ℝ → ι → ℝ), (∀ c ∈ 𝒞, approxWeight Sfin' c ≤ -ε / 2) ∧
          ∃ Q₀ : ℝ, ∀ x : ι → K, x ≠ 0 →
            approxProd Sinf Sfin (fun v ↦ v) L x ≤ mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) →
            Q₀ ≤ mulHeight x →
            (∃ (w : InfinitePlace K) (i : ι), L' w.1 i x = 0) ∨
              (∃ v ∈ Sfin', ∃ i, L' v.1 i x = 0) ∨
              ∃ c ∈ 𝒞, ∃ t : K, t ≠ 0 ∧ t • x ∈ approxDomain Sfin' L' c (mulHeight x) := by
  obtain ⟨Sfin', hsub, hprim, L', hLI, hLF, hIndI, hIndF, hle⟩ :=
    exists_finset_superset_forall_approxProd_le Sinf Sfin L hLInf hLFin
  obtain ⟨𝒞, h𝒞, Q₀, hQ₀⟩ := exists_finset_forall_exists_smul_mem_approxDomain Sfin' hprim L' hε
  refine ⟨Sfin', hsub, L', hLI, hLF, hIndI, hIndF, 𝒞, h𝒞, Q₀, fun x hx happ hQ ↦ ?_⟩
  by_cases hI : ∃ (w : InfinitePlace K) (i : ι), L' w.1 i x = 0
  · exact Or.inl hI
  by_cases hF : ∃ v ∈ Sfin', ∃ i, L' v.1 i x = 0
  · exact Or.inr (Or.inl hF)
  push Not at hI hF
  exact Or.inr (Or.inr (hQ₀ x hx hI hF ((hle x).trans happ) hQ))

end NumberField
