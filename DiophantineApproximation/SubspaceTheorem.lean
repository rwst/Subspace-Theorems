/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.SubspaceReduction
public import DiophantineApproximation.ParametricSubspace

-- Used only inside proofs.
import ArithmeticHeights.Northcott

/-!
# The Subspace Theorem, with coefficients in the field

For a number field `K`, finite sets `Sinf` of infinite and `Sfin` of finite places, forms
`L v i : Module.Dual K (Kⁱ)` with coefficients in `K` and linearly independent at every place of
`Sinf` and of `Sfin`, and `ε > 0`, the points `x ≠ 0` of `Kⁱ` with

```text
approxProd Sinf Sfin L x ≤ H(x) ^ (-#ι - ε)
```

lie in **finitely many proper linear subspaces** of `Kⁱ`. This is Schmidt's Subspace Theorem in
the `S`-adic form of Schlickewei, and it is Bombieri–Gubler's Theorem 7.2.2 with `F = K`.

It is Layer 6.1 and Layer 5.1 put together, and nothing else. Layer 5.1 replaces the inequality,
for every solution of large height, by membership in one of finitely many approximation domains
of negative weight — after an enlargement of `Sfin` and an extension of the forms by the
coordinate forms, which is harmless because their local factor is at most `1`. Layer 6.1 covers
each of those domains, at every large level, by one of finitely many proper subspaces. What is
left over is bounded: the solutions on the kernel of one of the forms, and the solutions of small
height.

## Main results

* `NumberField.exists_finset_submodule_of_approxProd_le`: **the milestone**, the Subspace Theorem
  with coefficients in `K`.
* `NumberField.exists_finset_submodule_setOf_approxProd_le_subset`: the same read as an inclusion
  of the solution set in a finite union of proper subspaces, the shape the literature states.

## Implementation notes

⚠ **Northcott is applied on projective space, and the small-height solutions contribute lines.**
There is no Northcott property for `Height.mulHeight` on tuples —
`Height.mulHeight_smul_eq_mulHeight` puts a whole line at one height — so the solutions of height
below the threshold are not finite in number and cannot be collected as points. They are collected
as the lines `K ∙ x` they span, which are finite in number by
`Projectivization.finite_setOfPred_mulHeight_le` (`ArithmeticHeights` 1.1). This is the one place
where `[Nontrivial ι]` is used for more than bookkeeping: a line is a proper subspace only when
`2 ≤ #ι`, and indeed for `#ι = 1` the theorem is false — the solutions are then the roots of
unity, finite in number but spanning `⊤`.

⚠ **The kernels are proper because the forms are nonzero, not because they are few.** A form of a
linearly independent family is nonzero (`LinearIndependent.ne_zero`), and the kernel of a nonzero
functional is a proper subspace. No count of the forms enters.

⚠ **The two thresholds are combined by one `max`, and no uniformity is needed.** Layer 5.1
produces a level `Q₀` above which every solution is classified, and Layer 6.1 produces, for each
of the finitely many exponent systems `c`, a level above which its domains are covered. Those
levels are not uniform in `c` and need not be: `Finset.exists_le` bounds finitely many reals.

⚠ **The normalizing scalar never has to be undone.** Layer 5.1 puts a multiple `t • x` in the
domain, not `x` itself, and Layer 6.1 puts `t • x` in a subspace; a subspace is closed under
`t⁻¹ • ‑`, so `x` lies in the same subspace. This is why the conclusion can be about `x` although
every intermediate statement is about a multiple of it.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Theorem 7.2.2 with `F = K`.

W. M. Schmidt, "Norm form equations", *Annals of Mathematics* **96** (1972), 526–551, for
`K = ℚ` and `S = {∞}`.

H. P. Schlickewei, "The `𝔭`-adic Thue–Siegel–Roth–Schmidt theorem", *Archiv der Mathematik* **29**
(1977), 267–270, for the finite places.

This is Layer 6.2 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Finset Height Module

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

open scoped Classical in
/-- **The Subspace Theorem, with coefficients in `K`** (Schmidt 1972 for `K = ℚ` and `S = {∞}`;
Schlickewei 1977 with finite places; Bombieri–Gubler, Theorem 7.2.2 with `F = K`). For forms
linearly independent at every place of `Sinf` and of `Sfin` and `ε > 0`, finitely many proper
subspaces of `Kⁱ` contain every `x ≠ 0` with `approxProd Sinf Sfin L x ≤ H(x) ^ (-#ι - ε)`.

`[Nontrivial ι]` is `n ≥ 1`, without which the statement is false: for `#ι = 1` the solutions are
the roots of unity of `K`, finite in number but spanning the whole line. -/
theorem exists_finset_submodule_of_approxProd_le [Nontrivial ι]
    (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K))
    (hLInf : ∀ v ∈ Sinf, LinearIndependent K (L v.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x : ι → K, x ≠ 0 →
        approxProd Sinf Sfin (fun v ↦ v) L x ≤ mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) →
        ∃ W ∈ T, x ∈ W := by
  -- Layer 5.1: the enlargement, the forms `L'`, the exponent systems `𝒞` and the level `Qstart`
  obtain ⟨Sfin', hsub, L', hLI, hLF, hIndI, hIndF, 𝒞, h𝒞, Qstart, hQstart⟩ :=
    exists_forall_approxProd_le_imp Sinf Sfin L hLInf hLFin hε
  -- Layer 6.1, applied to each of the finitely many exponent systems
  have hfam : ∀ c : AbsoluteValue K ℝ → ι → ℝ, ∃ (T : Finset (Submodule K (ι → K))) (Q : ℝ),
      c ∈ 𝒞 → ((∀ W ∈ T, W ≠ ⊤) ∧ ∀ Q' ≥ Q, ∃ W ∈ T, approxDomain Sfin' L' c Q' ⊆ W) := by
    intro c
    by_cases hc : c ∈ 𝒞
    · obtain ⟨T, hT, Q, hQ⟩ := exists_finset_submodule_forall_approxDomain_subset hIndI hIndF
        (lt_of_le_of_lt (h𝒞 c hc) (by linarith))
      exact ⟨T, Q, fun _ ↦ ⟨hT, hQ⟩⟩
    · exact ⟨∅, 0, fun h ↦ absurd h hc⟩
  choose Tc Qc hTc using hfam
  obtain ⟨Qmax, hQmax⟩ := (𝒞.image Qc).exists_le
  set Q₀ : ℝ := max Qstart Qmax with hQ₀
  -- the kernels of the forms, at the infinite places and at the places of the enlargement
  set Kinf : Finset (Submodule K (ι → K)) :=
    (Finset.univ : Finset (InfinitePlace K × ι)).image
      fun p ↦ LinearMap.ker (L' p.1.1 p.2) with hKinf
  set Kfin : Finset (Submodule K (ι → K)) :=
    (Sfin' ×ˢ (Finset.univ : Finset ι)).image fun p ↦ LinearMap.ker (L' p.1.1 p.2) with hKfin
  -- the lines spanned by the solutions of height below the threshold, finite by Northcott
  have hNor : {P : Projectivization K (ι → K) | Projectivization.mulHeight P ≤ Q₀}.Finite :=
    Projectivization.finite_setOfPred_mulHeight_le Q₀
  set Tsmall : Finset (Submodule K (ι → K)) :=
    (hNor.image Projectivization.submodule).toFinset with hTsmall
  refine ⟨Kinf ∪ Kfin ∪ Tsmall ∪ 𝒞.biUnion Tc, ?_, ?_⟩
  · intro W hW
    simp only [Finset.mem_union, Finset.mem_biUnion] at hW
    rcases hW with ((hW | hW) | hW) | ⟨c, hc, hW⟩
    · obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hW
      exact fun h ↦ (hIndI p.1).ne_zero p.2 (LinearMap.ker_eq_top.1 h)
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hW
      exact fun h ↦ (hIndF p.1 (Finset.mem_product.1 hp).1).ne_zero p.2 (LinearMap.ker_eq_top.1 h)
    · rw [hTsmall, Set.Finite.mem_toFinset] at hW
      obtain ⟨P, -, rfl⟩ := hW
      intro h
      have h1 : finrank K (P.submodule) = 1 := by
        rw [Projectivization.submodule_eq]
        exact finrank_span_singleton P.rep_nonzero
      rw [h] at h1
      have htop : finrank K (⊤ : Submodule K (ι → K)) = Fintype.card ι := by
        simp [finrank_top]
      have h2 : 2 ≤ Fintype.card ι := Fintype.one_lt_card
      omega
    · exact (hTc c hc).1 W hW
  · intro x hx happ
    rcases le_or_gt (mulHeight x) Q₀ with hsmall | hlarge
    -- small height: the line `K ∙ x`
    · refine ⟨(Projectivization.mk K x hx).submodule, ?_, ?_⟩
      · simp only [Finset.mem_union]
        refine Or.inl (Or.inr ?_)
        rw [hTsmall, Set.Finite.mem_toFinset]
        exact ⟨Projectivization.mk K x hx, by
          simpa [Projectivization.mulHeight_mk] using hsmall, rfl⟩
      · rw [Projectivization.submodule_mk]
        exact Submodule.mem_span_singleton_self x
    -- large height: Layer 5.1 classifies, Layer 6.1 covers
    · have hQs : Qstart ≤ mulHeight x := le_trans (le_max_left _ _) hlarge.le
      rcases hQstart x hx happ hQs with ⟨w, i, h⟩ | ⟨v, hv, i, h⟩ | ⟨c, hc, t, ht, hmem⟩
      · exact ⟨LinearMap.ker (L' w.1 i), by
          simp only [Finset.mem_union]
          exact Or.inl (Or.inl (Or.inl (Finset.mem_image.2 ⟨(w, i), Finset.mem_univ _, rfl⟩))), h⟩
      · exact ⟨LinearMap.ker (L' v.1 i), by
          simp only [Finset.mem_union]
          exact Or.inl (Or.inl (Or.inr (Finset.mem_image.2
            ⟨(v, i), Finset.mem_product.2 ⟨hv, Finset.mem_univ _⟩, rfl⟩))), h⟩
      · have hQc : Qc c ≤ mulHeight x :=
          le_trans (le_trans (hQmax _ (Finset.mem_image.2 ⟨c, hc, rfl⟩)) (le_max_right _ _))
            hlarge.le
        obtain ⟨W, hWT, hWsub⟩ := (hTc c hc).2 (mulHeight x) hQc
        refine ⟨W, by
          simp only [Finset.mem_union, Finset.mem_biUnion]
          exact Or.inr ⟨c, hc, hWT⟩, ?_⟩
        have hxt : t • x ∈ W := hWsub hmem
        have := W.smul_mem t⁻¹ hxt
        rwa [smul_smul, inv_mul_cancel₀ ht, one_smul] at this

/-- **The Subspace Theorem read as an inclusion**: the solution set is contained in a finite union
of proper subspaces. This is the shape the literature states — "the solutions lie in finitely many
proper subspaces" — and it is `exists_finset_submodule_of_approxProd_le` rearranged. -/
theorem exists_finset_submodule_setOf_approxProd_le_subset [Nontrivial ι]
    (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K))
    (hLInf : ∀ v ∈ Sinf, LinearIndependent K (L v.1))
    (hLFin : ∀ v ∈ Sfin, LinearIndependent K (L v.1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, W ≠ ⊤) ∧
      {x : ι → K | x ≠ 0 ∧ approxProd Sinf Sfin (fun v ↦ v) L x ≤
          mulHeight x ^ (-(Fintype.card ι : ℝ) - ε)} ⊆ ⋃ W ∈ T, (W : Set (ι → K)) := by
  obtain ⟨T, hT, hx⟩ := exists_finset_submodule_of_approxProd_le Sinf Sfin L hLInf hLFin hε
  refine ⟨T, hT, fun x hxmem ↦ ?_⟩
  obtain ⟨W, hWT, hxW⟩ := hx x hxmem.1 hxmem.2
  exact Set.mem_biUnion hWT hxW

end NumberField
