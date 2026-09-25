/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.RothProjective
public import DiophantineApproximation.SubspaceGeneralPosition
public import Mathlib.NumberTheory.Height.Projectivization

/-!
# Consistency with Layer 3: on the projective line the Subspace Theorem is Roth's theorem

**Layer 6.6.** Layer 3.4 proves the Subspace Theorem for `Fintype.card ι = 2` from Roth's
theorem of Layer 3.3, and Layer 6.3 proves it for every index type from Layers 4 to 6. This file
shows that the two are one theorem and not two: the statement of Layer 3.4 is the statement of
Layer 6.3 at a two-element index type, *hypothesis for hypothesis*, so each layer discharges the
other, and Roth's theorem of Layer 3.2 comes back out of Layer 6.3 alone.

What makes the agreement an equation rather than a translation is that Layer 3.4 was stated for
an arbitrary index type with `Fintype.card ι = 2` and with `approxProd`, the very quantity Layer
6.3 uses. The only difference between the two statements is that Layer 6.3 asks for
`[Nontrivial ι]` where Layer 3.4 asks for `Fintype.card ι = 2`, and the second implies the first.

Two things are proved beyond the agreement. Vojta's refinement of Layer 6.5 also specializes to
Layer 3.4, since general position for two forms in two variables is linear independence. And on
a two-element index type the conclusion "the solutions lie in finitely many proper subspaces" is
a genuine finiteness statement: a proper subspace of a plane holds at most one point of the
projective line, so the solutions are **finitely many points of `ℙ¹(K)`**.

## Main results

* `Projectivization.subsingleton_setOf_rep_mem`: a proper subspace of a plane holds at most one
  point of the projective line.
* `NumberField.exists_finset_submodule_of_approxProd_le_card_two_of_extension`: **Layer 3.4 from
  Layer 6.3**, which is the milestone.
* `NumberField.exists_finset_submodule_of_approxProd_le_card_two_of_generalPosition`: the same
  from Layer 6.5.
* `NumberField.finite_setOf_approxProd_le_card_two`: the projective reading — finitely many
  points of `ℙ¹(K)`.
* `NumberField.finite_setOf_prod_min_one_le_of_extension`: **Roth's theorem of Layer 3.2 from
  Layer 6.3**, without Layer 3.3.

## Implementation notes

⚠ **The converse needs nothing, because the two statements are the same proposition.** "Layer
6.3 at `card ι = 2` is no stronger than Layer 3.4" is not an implication to be proved: once
`Fintype.card ι = 2` supplies `[Nontrivial ι]`, the two conclusions are syntactically equal, and
the acceptance criteria below record that by giving one statement two proofs — one through Roth's
theorem and one through the parametric Subspace Theorem — and by checking that the two theorems
have the same type. That is the precise sense in which the library carries one theorem on the
projective line.

⚠ **The agreement is checked by `rfl`, and that is not a coincidence.** Proof irrelevance is
definitional in Lean, so two proofs of one proposition are one term; the equality of two theorems
is therefore the equality of their *statements*, and `rfl` between two theorem constants is
exactly the assertion that they prove the same thing. The acceptance criteria use it four times.

⚠ **"Without Layer 3.3" is a claim about the proofs and not about the imports.**
`NumberField.finite_setOf_prod_min_one_le_of_extension` is assembled from Layer 6.3 and from
Layer 3.4's converse implication, whose proof takes the Subspace Theorem as a hypothesis and uses
nothing of Layer 3 besides Northcott's theorem; it is therefore a second proof of Roth's theorem
over a number field and not a restatement of the first. The module graph does not record that
independence — `SubspaceAlgebraic.lean` reaches `RothTheorem.lean` through `ApproxProd.lean`,
where the central quantity is defined — and Lean does not hand out the bodies of imported
theorems, so the claim is read off the two proofs rather than checked mechanically.

⚠ **The exceptional subspaces of `ℙ¹` are its points, and the finiteness is a count of points and
not of subspaces.** The finite set of subspaces Layer 6.3 returns may be larger than the
solution set — it is allowed to contain lines meeting no solution, and it contains the line at
infinity for the coordinate forms — so the projective statement is proved by *discarding* the
subspaces: a solution is pinned by the one that holds it, and a proper subspace of `K²` holds at
most one point. Going the other way, from finitely many points to finitely many subspaces, is
`Layer 3.4`'s own construction and is not repeated here.

⚠ **Vojta's refinement specializes with no work at all.** `Module.Dual.IsGeneralPosition` for two
forms in two variables is linear independence, and `NumberField.generalProd` over
`Finset.univ` is `NumberField.approxProd` by `rfl`, so Layer 6.5 gives Layer 3.4 through the same
one equation. Both of Layer 6's Subspace Theorems therefore contain Roth's theorem on the
projective line.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Theorem 7.2.2 for `n = 1` and Example 7.2.7.

This is Layer 6.6 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Height Module AbsoluteValue

namespace Projectivization

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]

/-- **A proper subspace of a plane holds at most one point of the projective line.** Two points
whose representatives lie in `V` are either proportional, and then equal as points, or
independent, and then they span the plane and `V` is everything. This is the linear algebra
behind the reading of Layer 3.4 as a finiteness statement. -/
theorem subsingleton_setOf_rep_mem (hcard : Fintype.card ι = 2)
    {V : Submodule K (ι → K)} (hV : V ≠ ⊤) :
    {P : Projectivization K (ι → K) | P.rep ∈ V}.Subsingleton := by
  intro P hP Q hQ
  by_contra hne
  refine hV ?_
  have hli : LinearIndependent K ![P.rep, Q.rep] := by
    rw [linearIndependent_fin2]
    refine ⟨by simpa using Q.rep_nonzero, fun a ha ↦ hne ?_⟩
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at ha
    have hmk : Projectivization.mk K P.rep P.rep_nonzero
        = Projectivization.mk K Q.rep Q.rep_nonzero :=
      (mk_eq_mk_iff' K _ _ P.rep_nonzero Q.rep_nonzero).mpr ⟨a, ha⟩
    rwa [P.mk_rep, Q.mk_rep] at hmk
  have hle : Submodule.span K (Set.range ![P.rep, Q.rep]) ≤ V := by
    refine Submodule.span_le.mpr (Set.range_subset_iff.mpr fun i ↦ ?_)
    fin_cases i
    · exact hP
    · exact hQ
  have hspan : finrank K (Submodule.span K (Set.range ![P.rep, Q.rep])) = 2 := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have htop : finrank K (ι → K) = 2 := by
    rw [Module.finrank_fintype_fun_eq_card, hcard]
  refine Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le V) ?_)
  rw [htop, ← hspan]
  exact Submodule.finrank_mono hle

/-- **Finitely many proper subspaces of a plane hold finitely many points of the projective
line.** This is what turns the conclusion of the Subspace Theorem at `Fintype.card ι = 2` into a
count of solutions. -/
theorem finite_setOf_exists_rep_mem (hcard : Fintype.card ι = 2)
    (T : Finset (Submodule K (ι → K))) (hT : ∀ V ∈ T, V ≠ ⊤) :
    {P : Projectivization K (ι → K) | ∃ V ∈ T, P.rep ∈ V}.Finite := by
  have heq : {P : Projectivization K (ι → K) | ∃ V ∈ T, P.rep ∈ V}
      = ⋃ V ∈ (T : Set (Submodule K (ι → K))), {P : Projectivization K (ι → K) | P.rep ∈ V} := by
    ext P
    simp
  rw [heq]
  exact Set.Finite.biUnion T.finite_toSet fun V hV ↦
    (subsingleton_setOf_rep_mem hcard (hT V hV)).finite

end Projectivization

namespace Module.Dual

variable {F : Type*} [Field F]

/-- **The two forms of Bombieri–Gubler's Example 7.2.7 are linearly independent**, whatever the
target `α`: `X₀` and `X₁ - α X₀` have determinant `1`. Stated through the values of the forms, so
that it applies to any family that takes those values. -/
theorem linearIndependent_proj_sub_smul {α : F} {M : Fin 2 → Dual F (Fin 2 → F)}
    (h0 : ∀ y : Fin 2 → F, M 0 y = y 0) (h1 : ∀ y : Fin 2 → F, M 1 y = y 1 - α * y 0) :
    LinearIndependent F M := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have happ : ∀ y : Fin 2 → F, g 0 * M 0 y + g 1 * M 1 y = 0 := by
    intro y
    have h : (∑ i, g i • M i) y = (0 : Dual F (Fin 2 → F)) y := by rw [hg]
    rw [LinearMap.sum_apply, Fin.sum_univ_two, LinearMap.smul_apply, LinearMap.smul_apply,
      LinearMap.zero_apply, smul_eq_mul, smul_eq_mul] at h
    exact h
  have hg1 : g 1 = 0 := by
    have hy := happ ![0, 1]
    rw [h0, h1] at hy
    simpa using hy
  have hg0 : g 0 = 0 := by
    have hy := happ ![1, 0]
    rw [h0, h1, hg1] at hy
    simpa using hy
  intro i
  fin_cases i
  · exact hg0
  · exact hg1

end Module.Dual

namespace NumberField

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
variable {ι : Type*} [Fintype ι]

/-- **Layer 6.6: Layer 3.4 is Layer 6.3 at a two-element index type.** The Subspace Theorem with
algebraic coefficients, specialized to `Fintype.card ι = 2`, is Roth's theorem on the projective
line — the statement of `NumberField.exists_finset_submodule_of_approxProd_le_card_two`,
hypothesis for hypothesis. The whole of the specialization is that `Fintype.card ι = 2` supplies
the `[Nontrivial ι]` that Layer 6.3 asks for. -/
theorem exists_finset_submodule_of_approxProd_le_card_two_of_extension
    (hcard : Fintype.card ι = 2)
    (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    (hLInf : ∀ v ∈ Sinf, LinearIndependent F (L v.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent F (L v.1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ V ∈ T, V ≠ ⊤) ∧
      ∀ x : ι → K, x ≠ 0 →
        approxProd Sinf Sfin w L x ≤ mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) →
        ∃ V ∈ T, x ∈ V :=
  have : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  exists_finset_submodule_of_approxProd_le_extension Sinf Sfin w hwInf hwFin L hLInf hLFin hε

/-- **Layer 6.5 also contains Layer 3.4.** Vojta's refinement asks for the forms at a place to be
in general position and allows any finite number of them; for two forms in two variables general
position *is* linear independence, and the quantity it bounds is `approxProd` on the nose. So the
same one equation specializes Layer 6.5 to Roth's theorem on the projective line. -/
theorem exists_finset_submodule_of_approxProd_le_card_two_of_generalPosition
    (hcard : Fintype.card ι = 2)
    (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    (hLInf : ∀ v ∈ Sinf, LinearIndependent F (L v.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent F (L v.1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ V ∈ T, V ≠ ⊤) ∧
      ∀ x : ι → K, x ≠ 0 →
        approxProd Sinf Sfin w L x ≤ mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) →
        ∃ V ∈ T, x ∈ V :=
  have : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  exists_finset_submodule_of_generalProd_le Sinf Sfin w hwInf hwFin (fun _ ↦ Finset.univ) L
    (fun v hv ↦ Module.Dual.IsGeneralPosition.of_linearIndependent _ (hLInf v hv))
    (fun v hv ↦ Module.Dual.IsGeneralPosition.of_linearIndependent _ (hLFin v hv)) hε

/-- **The Subspace Theorem on the projective line is a finiteness statement.** For
`Fintype.card ι = 2` the exceptional subspaces are points, so the conclusion of Layer 3.4 and of
Layer 6.3 is that **finitely many points of `ℙ¹(K)`** satisfy the approximation inequality. This
is the form in which the theorem is visibly Roth's. -/
theorem finite_setOf_approxProd_le_card_two (hcard : Fintype.card ι = 2)
    (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    (hLInf : ∀ v ∈ Sinf, LinearIndependent F (L v.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent F (L v.1))
    {ε : ℝ} (hε : 0 < ε) :
    {P : Projectivization K (ι → K) | approxProd Sinf Sfin w L P.rep
      ≤ Projectivization.mulHeight P ^ (-(Fintype.card ι : ℝ) - ε)}.Finite := by
  obtain ⟨T, hTproper, hTmem⟩ := exists_finset_submodule_of_approxProd_le_card_two_of_extension
    hcard Sinf Sfin w hwInf hwFin L hLInf hLFin hε
  refine (Projectivization.finite_setOf_exists_rep_mem hcard T hTproper).subset fun P hP ↦ ?_
  refine hTmem P.rep P.rep_nonzero ?_
  rwa [← Projectivization.mulHeight_mk P.rep_nonzero, P.mk_rep]

/-- **Roth's theorem from the Subspace Theorem of Layer 6.** Layer 3.4 proved the converse
implication `NumberField.finite_setOf_prod_min_one_le_of_subspace` — that Roth's theorem of Layer
3.2 is the two-variable Subspace Theorem for the forms `X₀` and `X₁ - α v X₀` — and discharged
its hypothesis from Layer 3.3. Discharging it from Layer 6.3 instead gives a second proof of
Roth's theorem over a number field, one that uses no theorem of Layer 3. -/
theorem finite_setOf_prod_min_one_le_of_extension (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (α : AbsoluteValue K ℝ → F) {κ : ℝ} (hκ : 2 < κ) :
    {β : K | (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) ≤ mulHeight₁ β ^ (-κ)}.Finite := by
  classical
  set L : AbsoluteValue K ℝ → Fin 2 → Dual F (Fin 2 → F) := fun u i ↦
    if i = 0 then LinearMap.proj 0 else LinearMap.proj 1 - α u • LinearMap.proj 0 with hLdef
  have hL0 : ∀ (u : AbsoluteValue K ℝ) (y : Fin 2 → F), L u 0 y = y 0 := by
    intro u y
    simp only [hLdef, ite_eq_left rfl]
    rfl
  have hL1 : ∀ (u : AbsoluteValue K ℝ) (y : Fin 2 → F), L u 1 y = y 1 - α u * y 0 := by
    intro u y
    simp only [hLdef, ite_eq_right (by decide : ¬((1 : Fin 2) = 0))]
    simp
  have hLi : ∀ u : AbsoluteValue K ℝ, LinearIndependent F (L u) := fun u ↦
    Module.Dual.linearIndependent_proj_sub_smul (hL0 u) (hL1 u)
  refine finite_setOf_prod_min_one_le_of_subspace Sinf Sfin w hwInf hwFin α hκ L hL0 hL1 ?_
  intro ε hε
  exact exists_finset_submodule_of_approxProd_le_extension Sinf Sfin w hwInf hwFin L
    (fun v _ ↦ hLi v.1) (fun v _ ↦ hLi v.1) hε

end NumberField

/-! ### Acceptance criteria -/

/-- **The milestone, checked as an equation between theorems.** Layer 3.4's Subspace Theorem in
two variables and the specialization of Layer 6.3 to `Fintype.card ι = 2` are not two theorems
with the same content: they are one theorem, and `rfl` says so. The two proofs — one through
Roth's theorem of Layer 3.3, one through Layers 4 to 6 — are proofs of the same proposition. -/
example : @NumberField.exists_finset_submodule_of_approxProd_le_card_two
    = @NumberField.exists_finset_submodule_of_approxProd_le_card_two_of_extension := rfl

/-- **Vojta's refinement is the same theorem again.** Layer 6.5 specializes to Layer 3.4 through
the same equation, so the projective line sees no difference between the Subspace Theorem with
`n + 1` independent forms and the Subspace Theorem with any number of forms in general
position. -/
example : @NumberField.exists_finset_submodule_of_approxProd_le_card_two_of_generalPosition
    = @NumberField.exists_finset_submodule_of_approxProd_le_card_two_of_extension := rfl

/-- **Roth's theorem: three proofs, one statement.** Layer 3.2 proves it directly, Layer 3.4
recovers it from the two-variable Subspace Theorem, and Layer 6.6 recovers it from the Subspace
Theorem with algebraic coefficients. All three are the same theorem. -/
example : @NumberField.finite_setOf_prod_min_one_le
    = @NumberField.finite_setOf_prod_min_one_le_of_extension := rfl

example : @NumberField.finite_setOf_prod_min_one_le_card_two
    = @NumberField.finite_setOf_prod_min_one_le_of_extension := rfl

/-- **Conformance with Layer 3.2.** The route through Layer 6.3 lands on Roth's theorem over a
number field as Layer 3.2 states it, hypothesis for hypothesis. -/
example {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
    (Sinf : Finset (NumberField.InfinitePlace K))
    (Sfin : Finset (NumberField.FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (α : AbsoluteValue K ℝ → F) {κ : ℝ} (hκ : 2 < κ) :
    {β : K | (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) ≤ mulHeight₁ β ^ (-κ)}.Finite :=
  NumberField.finite_setOf_prod_min_one_le_of_extension Sinf Sfin w hwInf hwFin α hκ

/-- **The Subspace Theorem on `ℙ¹` counts points.** At `ι = Fin 2` the conclusion is that finitely
many points of the projective line satisfy the inequality — no subspace appears in the
statement. -/
example {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
    (Sinf : Finset (NumberField.InfinitePlace K))
    (Sfin : Finset (NumberField.FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (L : AbsoluteValue K ℝ → Fin 2 → Dual F (Fin 2 → F))
    (hLInf : ∀ v ∈ Sinf, LinearIndependent F (L v.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent F (L v.1))
    {ε : ℝ} (hε : 0 < ε) :
    {P : Projectivization K (Fin 2 → K) | NumberField.approxProd Sinf Sfin w L P.rep
      ≤ Projectivization.mulHeight P ^ (-(2 : ℝ) - ε)}.Finite :=
  NumberField.finite_setOf_approxProd_le_card_two (Fintype.card_fin 2) Sinf Sfin w hwInf hwFin L
    hLInf hLFin hε

/-- ⚠ **Rejection test: the count has to be on the projective line.** If one nonzero tuple
satisfies the inequality then so does every nonzero multiple of it, since both sides are
invariant under scaling. The set of *tuples* is therefore infinite as soon as it is nonempty, and
`NumberField.finite_setOf_approxProd_le_card_two` cannot be improved to a statement about
tuples. This holds at every index type, not only at a two-element one. -/
example {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
    {ι : Type*} [Fintype ι]
    (Sinf : Finset (NumberField.InfinitePlace K))
    (Sfin : Finset (NumberField.FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    {ε : ℝ} (x : ι → K) (hx : x ≠ 0)
    (hsol : NumberField.approxProd Sinf Sfin w L x
      ≤ mulHeight x ^ (-(Fintype.card ι : ℝ) - ε)) :
    {y : ι → K | y ≠ 0 ∧ NumberField.approxProd Sinf Sfin w L y
      ≤ mulHeight y ^ (-(Fintype.card ι : ℝ) - ε)}.Infinite := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ ↦ ((n + 1 : ℕ) : K) • x) (fun m n hmn ↦ ?_) fun n ↦ ?_
  · have h := congrFun hmn i₀
    simp only [Pi.smul_apply, smul_eq_mul] at h
    exact Nat.succ_injective (Nat.cast_injective (mul_right_cancel₀ hi₀ h))
  · have hc : (((n + 1 : ℕ) : K)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    refine ⟨smul_ne_zero hc hx, ?_⟩
    rw [NumberField.approxProd_smul Sinf Sfin w hwInf hwFin L x hc,
      Height.mulHeight_smul_eq_mulHeight x hc]
    exact hsol
