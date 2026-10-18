/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import FaltingsWustholz1994.Weight
public import DiophantineApproximation.SubspaceSubmodule

/-!
# Theorem 8.1 of Faltings–Wüstholz

G. Faltings and G. Wüstholz, *Diophantine approximations on projective spaces*, Invent. Math.
**116** (1994), Theorem 8.1.

At every place `v` of `S = S∞ ∪ S₀` of a number field `K`, finitely many linear forms `ℓ_{v,k}`
over a finite extension `F` (`k ∈ B v`) carry exponents `c_{v,k}`. FW's system (1) is

```text
‖ℓ_{v,k}(x)‖_v / ‖x‖_v ≤ H(x) ^ (-c_{v,k})      (v ∈ S, k ∈ B v),   x ∈ Kⁿ⁺¹ ∖ 0,
```

with `‖·‖_v` measured by `w v` over `v` and `H` the height relative to `K`. If every nonzero
subspace `U` of `Kⁿ⁺¹` has weight `W(U) > dim U` (`FaltingsWustholz1994/Weight.lean`), the
solutions lie on finitely many lines: there are finitely many projective solutions.

The proof is not FW's, which needs the product theorem on products of subvarieties and the
semistability of tensor products. It is the Subspace Theorem on a subspace
(`DiophantineApproximation/SubspaceSubmodule.lean`) and strong induction on `dim U`. In a
subspace `U` of dimension `n ≥ 2`, pick at each place a basis of `U^*` among the restricted
forms attaining `W_v(U)`. Each of its forms satisfies its inequality (the coordinate forms
trivially, with exponent `0`), so their product is at most `H(x)^{-W(U)}`, and `W(U) > n` is the
hypothesis of the Subspace Theorem on `U` with `ε = W(U) - n`. The solutions in `U` lie in
finitely many proper subspaces of `U`, and the induction finishes in each.

## Main definitions

* `NumberField.IsSystemSolution`: FW's system (1).

## Main results

* `NumberField.generalProd_le_of_isSystemSolution`: the chosen bases give `H(x)^{-W(U)}`.
* `NumberField.exists_finset_submodule_lt_of_lt_maxWeight`: one step of the induction.
* `NumberField.exists_finset_line_of_lt_maxWeight`: **FW Theorem 8.1**, as finitely many lines.
* `NumberField.finite_setOf_isSystemSolution`: the same as finitely many projective points.

## Implementation notes

⚠ **The hypothesis is weaker than FW's.** FW assume the filtrations jointly semistable and
`∑_w μ_w(V) > [L : ℚ]`. Through the see-saw this gives `μ(U) ≥ μ(V) > 1` for the quotient
filtration on every `U^*`, which is `W(U) > dim U` here. Only that is used, so it is the
hypothesis.

⚠ **The inequalities are `≤`, FW's are `<`.** That is a weaker hypothesis on the points, so the
theorem is stronger. Exponents may be any reals.

This is milestone FW.3 of `FaltingsWustholz1994/README.md`.
-/

@[expose] public section

open Finset Height Module Module.Dual

namespace NumberField

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
  {ι κ : Type*} [Fintype ι]

/-- **FW's system (1)**: at every place of `S` and for every form `ℓ_{v,k}`, `k ∈ B v`, the local
factor is at most `H(x) ^ (-c_{v,k})`. -/
def IsSystemSolution (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (B : AbsoluteValue K ℝ → Finset κ)
    (ℓ : AbsoluteValue K ℝ → κ → Dual F (ι → F)) (c : AbsoluteValue K ℝ → κ → ℝ)
    (x : ι → K) : Prop :=
  (∀ v ∈ Sinf, ∀ k ∈ B v.1,
    w v.1 (ℓ v.1 k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) ≤ mulHeight x ^ (-c v.1 k)) ∧
  (∀ v ∈ Sfin, ∀ k ∈ B v.1,
    w v.1 (ℓ v.1 k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) ≤ mulHeight x ^ (-c v.1 k))

/-- At one place, the forms of a basis `I` give `∏_{i ∈ I} ‖ℓ_i(x)‖_v / ‖x‖_v ≤ H(x)^{-∑ c_i}`
for a point satisfying the inequalities of the forms in `B`. -/
theorem prod_le_rpow_of_forall_le {u : AbsoluteValue K ℝ} {W : AbsoluteValue F ℝ}
    (hW : W.LiesOver u) {B : Finset κ} {ℓ : κ → Dual F (ι → F)} {c : κ → ℝ} {x : ι → K}
    {H : ℝ} (hH : 1 ≤ H)
    (hx : ∀ k ∈ B, W (ℓ k fun j ↦ algebraMap K F (x j)) / ⨆ j, u (x j) ≤ H ^ (-c k))
    {I : Finset (κ ⊕ ι)} (hI : I ⊆ B.disjSum univ) :
    ∏ i ∈ I, W (extendProj ℓ i fun j ↦ algebraMap K F (x j)) / ⨆ j, u (x j)
      ≤ H ^ (-∑ i ∈ I, extendExp c i) := by
  have hH0 : 0 < H := lt_of_lt_of_le zero_lt_one hH
  rw [← Finset.sum_neg_distrib, Real.rpow_sum_of_pos hH0]
  refine Finset.prod_le_prod₀ (fun i _ ↦ div_nonneg (W.nonneg _)
    (Real.iSup_nonneg fun j ↦ u.nonneg _)) fun i hi ↦ ?_
  have hi' := hI hi
  rcases i with k | j
  · rw [Finset.inl_mem_disjSum] at hi'
    exact hx k hi'
  · simp only [extendProj_inr, LinearMap.proj_apply, extendExp_inr, neg_zero, Real.rpow_zero]
    rw [AbsoluteValue.apply_algebraMap_of_liesOver (v := u) W (x j)]
    by_cases h0 : (⨆ j, u (x j)) = 0
    · rw [h0, div_zero]
      exact zero_le_one
    · exact (div_le_one (lt_of_le_of_ne (Real.iSup_nonneg fun j ↦ u.nonneg _) (Ne.symm h0))).2
        (le_ciSup (f := fun j ↦ u (x j)) (Finite.bddAbove_range _) j)

/-- **The chosen bases give `H(x)^{-W(U)}`**: for bases `I u` attaining the local weights,
indexed by `Fin n` through `e u`, the central quantity of the Subspace Theorem at a solution is
at most `H(x) ^ (-W(U))`. -/
theorem generalProd_le_of_isSystemSolution (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwI : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwF : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (B : AbsoluteValue K ℝ → Finset κ) (ℓ : AbsoluteValue K ℝ → κ → Dual F (ι → F))
    (c : AbsoluteValue K ℝ → κ → ℝ) (U : Submodule K (ι → K)) {n : ℕ}
    (I : AbsoluteValue K ℝ → Finset (κ ⊕ ι)) (hI : ∀ u, IsWeightBasis (B u) (ℓ u) U (I u))
    (hIw : ∀ u, ∑ i ∈ I u, extendExp (c u) i = localMaxWeight (B u) (ℓ u) (c u) U)
    (e : ∀ u, Fin n ≃ I u) {x : ι → K} (hx : IsSystemSolution Sinf Sfin w B ℓ c x) :
    generalProd Sinf Sfin w (fun _ ↦ univ)
        (fun u m ↦ extendProj (ℓ u) (e u m)) x
      ≤ mulHeight x ^ (-maxWeight Sinf Sfin B ℓ c U) := by
  have hH := one_le_mulHeight x
  have hH0 : 0 < mulHeight x := lt_of_lt_of_le zero_lt_one hH
  have hprod : ∀ u : AbsoluteValue K ℝ,
      (∏ m ∈ (univ : Finset (Fin n)),
          w u (extendProj (ℓ u) (e u m) fun j ↦ algebraMap K F (x j)) / ⨆ j, u (x j))
        = ∏ i ∈ I u, w u (extendProj (ℓ u) i fun j ↦ algebraMap K F (x j)) / ⨆ j, u (x j) := by
    intro u
    rw [← Finset.prod_coe_sort (I u)]
    exact Fintype.prod_equiv (e u) _ _ fun m ↦ rfl
  have hloc : ∀ u : AbsoluteValue K ℝ, (w u).LiesOver u →
      (∀ k ∈ B u, w u (ℓ u k fun j ↦ algebraMap K F (x j)) / ⨆ j, u (x j)
        ≤ mulHeight x ^ (-c u k)) →
      (∏ m ∈ (univ : Finset (Fin n)),
          w u (extendProj (ℓ u) (e u m) fun j ↦ algebraMap K F (x j)) / ⨆ j, u (x j))
        ≤ mulHeight x ^ (-localMaxWeight (B u) (ℓ u) (c u) U) := by
    intro u hu hxu
    rw [hprod u, ← hIw u]
    exact prod_le_rpow_of_forall_le hu hH hxu (hI u).1
  have hnn : ∀ u : AbsoluteValue K ℝ, (0 : ℝ) ≤ ∏ m ∈ (univ : Finset (Fin n)),
      w u (extendProj (ℓ u) (e u m) fun j ↦ algebraMap K F (x j)) / ⨆ j, u (x j) := fun u ↦
    Finset.prod_nonneg fun m _ ↦ div_nonneg (AbsoluteValue.nonneg _ _)
      (Real.iSup_nonneg fun j ↦ u.nonneg _)
  rw [generalProd, maxWeight, neg_add, Real.rpow_add hH0, ← Finset.sum_neg_distrib,
    ← Finset.sum_neg_distrib, Real.rpow_sum_of_pos hH0, Real.rpow_sum_of_pos hH0]
  refine mul_le_mul ?_ ?_ (Finset.prod_nonneg fun v _ ↦ hnn v.1)
    (Finset.prod_nonneg fun v _ ↦ (Real.rpow_pos_of_pos hH0 _).le)
  · refine Finset.prod_le_prod₀ (fun v _ ↦ pow_nonneg (hnn v.1) _) fun v hv ↦ ?_
    rw [show -((v.mult : ℝ) * localMaxWeight (B v.1) (ℓ v.1) (c v.1) U)
      = -localMaxWeight (B v.1) (ℓ v.1) (c v.1) U * ((v.mult : ℕ) : ℝ) by ring,
      Real.rpow_mul_natCast hH0.le]
    exact pow_le_pow_left₀ (hnn v.1) (hloc v.1 (hwI v hv) (hx.1 v hv)) _
  · exact Finset.prod_le_prod₀ (fun v _ ↦ hnn v.1) fun v hv ↦ hloc v.1 (hwF v hv) (hx.2 v hv)

/-- **One step of the induction**: in a subspace `U` of dimension `n ≥ 2` with `W(U) > n`, the
solutions lie in finitely many proper subspaces of `U`. It is FW.1 with the bases attaining the
local weights and `ε = W(U) - n`. -/
theorem exists_finset_submodule_lt_of_lt_maxWeight (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwI : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwF : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (B : AbsoluteValue K ℝ → Finset κ) (ℓ : AbsoluteValue K ℝ → κ → Dual F (ι → F))
    (c : AbsoluteValue K ℝ → κ → ℝ) (U : Submodule K (ι → K)) (hn : 2 ≤ finrank K U)
    (hW : (finrank K U : ℝ) < maxWeight Sinf Sfin B ℓ c U) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, W < U) ∧
      ∀ x ∈ U, x ≠ 0 → IsSystemSolution Sinf Sfin w B ℓ c x → ∃ W ∈ T, x ∈ W := by
  set n := finrank K U with hUn
  -- the bases attaining the local weights
  have hbest : ∀ u : AbsoluteValue K ℝ, ∃ I : Finset (κ ⊕ ι),
      IsWeightBasis (B u) (ℓ u) U I ∧
        ∑ i ∈ I, extendExp (c u) i = localMaxWeight (B u) (ℓ u) (c u) U := fun u ↦ by
    obtain ⟨I, hI, hIw⟩ := localMaxWeight_mem (B u) (ℓ u) (c u) U
    exact ⟨I, hI, hIw⟩
  choose I hI hIw using hbest
  have hcard : ∀ u, #(I u) = n := fun u ↦ (hI u).2.1
  let e : ∀ u, Fin n ≃ I u := fun u ↦ ((I u).equivFinOfCardEq (hcard u)).symm
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  have hind : ∀ u : AbsoluteValue K ℝ, LinearIndependent F
      fun m (x : U) ↦ extendProj (ℓ u) (e u m) fun j ↦ algebraMap K F ((x : ι → K) j) :=
    fun u ↦ ((hI u).2.2).comp (e u) (e u).injective
  set ε : ℝ := maxWeight Sinf Sfin B ℓ c U - n with hεdef
  have hε : 0 < ε := by linarith
  obtain ⟨TU, hTU1, hTU2⟩ := exists_finset_submodule_lt_of_generalProd_le U
    (by rw [Fintype.card_fin]) Sinf Sfin w hwI hwF
    (fun u m ↦ extendProj (ℓ u) (e u m)) (fun v _ ↦ hind v.1) (fun v _ ↦ hind v.1) hε
  refine ⟨TU, hTU1, fun x hxU hx hsol ↦ hTU2 x hxU hx ?_⟩
  have hbound := generalProd_le_of_isSystemSolution Sinf Sfin w hwI hwF B ℓ c U I hI hIw e hsol
  have hexp : -maxWeight Sinf Sfin B ℓ c U = -((Fintype.card (Fin n) : ℕ) : ℝ) - ε := by
    rw [Fintype.card_fin, hεdef]
    ring
  rwa [hexp] at hbound

open scoped Classical in
/-- **FW Theorem 8.1**, as finitely many lines: if every nonzero subspace `U` has weight
`W(U) > dim U`, the solutions of FW's system (1) lie on finitely many lines. -/
theorem exists_finset_line_of_lt_maxWeight (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwI : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwF : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (B : AbsoluteValue K ℝ → Finset κ) (ℓ : AbsoluteValue K ℝ → κ → Dual F (ι → F))
    (c : AbsoluteValue K ℝ → κ → ℝ)
    (hW : ∀ U : Submodule K (ι → K), U ≠ ⊥ →
      (finrank K U : ℝ) < maxWeight Sinf Sfin B ℓ c U) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, finrank K W = 1) ∧
      ∀ x : ι → K, x ≠ 0 → IsSystemSolution Sinf Sfin w B ℓ c x → ∃ W ∈ T, x ∈ W := by
  suffices key : ∀ n, ∀ U : Submodule K (ι → K), finrank K U = n →
      ∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, finrank K W = 1) ∧
        ∀ x ∈ U, x ≠ 0 → IsSystemSolution Sinf Sfin w B ℓ c x → ∃ W ∈ T, x ∈ W by
    obtain ⟨T, hT1, hT2⟩ := key _ ⊤ rfl
    exact ⟨T, hT1, fun x hx hsol ↦ hT2 x Submodule.mem_top hx hsol⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro U hUn
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · refine ⟨∅, by simp, fun x hxU hx _ ↦ absurd ?_ hx⟩
      rw [Submodule.finrank_eq_zero] at hUn
      rw [hUn] at hxU
      exact (Submodule.mem_bot K).1 hxU
    · exact ⟨{U}, by simpa using hUn, fun x hxU _ _ ↦ ⟨U, Finset.mem_singleton_self U, hxU⟩⟩
  have hU0 : U ≠ ⊥ := by
    rintro rfl
    simp at hUn
    omega
  obtain ⟨TU, hTU1, hTU2⟩ := exists_finset_submodule_lt_of_lt_maxWeight Sinf Sfin w hwI hwF
    B ℓ c U (hUn ▸ hn) (hW U hU0)
  -- the induction in each proper subspace
  have hsub : ∀ W' : Submodule K (ι → K), ∃ T : Finset (Submodule K (ι → K)), W' < U →
      (∀ W ∈ T, finrank K W = 1) ∧
        ∀ x ∈ W', x ≠ 0 → IsSystemSolution Sinf Sfin w B ℓ c x → ∃ W ∈ T, x ∈ W := by
    intro W'
    by_cases h : W' < U
    · obtain ⟨T, hT⟩ := ih (finrank K W') (hUn ▸ Submodule.finrank_lt_finrank_of_lt h) W' rfl
      exact ⟨T, fun _ ↦ hT⟩
    · exact ⟨∅, fun h' ↦ absurd h' h⟩
  choose TW hTW using hsub
  refine ⟨TU.biUnion TW, ?_, ?_⟩
  · intro W hW
    obtain ⟨W', hW', hW⟩ := Finset.mem_biUnion.1 hW
    exact (hTW W' (hTU1 W' hW')).1 W hW
  · intro x hxU hx hsol
    obtain ⟨W', hW'T, hxW'⟩ := hTU2 x hxU hx hsol
    obtain ⟨W, hWT, hxW⟩ := (hTW W' (hTU1 W' hW'T)).2 x hxW' hx hsol
    exact ⟨W, Finset.mem_biUnion.2 ⟨W', hW'T, hWT⟩, hxW⟩

/-- **FW Theorem 8.1**, as finitely many projective points. -/
theorem finite_setOf_isSystemSolution (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwI : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwF : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (B : AbsoluteValue K ℝ → Finset κ) (ℓ : AbsoluteValue K ℝ → κ → Dual F (ι → F))
    (c : AbsoluteValue K ℝ → κ → ℝ)
    (hW : ∀ U : Submodule K (ι → K), U ≠ ⊥ →
      (finrank K U : ℝ) < maxWeight Sinf Sfin B ℓ c U) :
    {Q : Projectivization K (ι → K) |
      ∃ (x : ι → K) (hx : x ≠ 0), Projectivization.mk K x hx = Q ∧
        IsSystemSolution Sinf Sfin w B ℓ c x}.Finite := by
  classical
  obtain ⟨T, hT1, hT2⟩ := exists_finset_line_of_lt_maxWeight Sinf Sfin w hwI hwF B ℓ c hW
  refine ((T.attach.image fun W ↦ Projectivization.mk'' W.1 (hT1 W.1 W.2)).finite_toSet).subset ?_
  rintro Q ⟨x, hx, rfl, hsol⟩
  obtain ⟨W, hWT, hxW⟩ := hT2 x hx hsol
  refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨⟨W, hWT⟩, Finset.mem_attach _ _, ?_⟩)
  apply Projectivization.submodule_injective
  rw [Projectivization.submodule_mk'', Projectivization.submodule_mk]
  exact eq_span_singleton_of_mem_of_finrank_eq_one (hT1 W hWT) hxW hx

end NumberField
