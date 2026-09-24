/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.SubspaceAlgebraic
public import DiophantineApproximation.GeneralPosition

-- Used only inside proofs.
import ArithmeticHeights.Northcott
import DiophantineApproximation.SubspaceReduction

/-!
# The Subspace Theorem for forms in general position

**Layer 6.5.** For a number field `K`, finite sets `Sinf` of infinite and `Sfin` of finite places,
an absolute value `w v` of a finite extension `F` over each of them, and at every one of them a
family of linear forms `L v k : Module.Dual F (Fⁱ)`, `k ∈ B v`, **in general position** — every
`#ι` of them linearly independent — the points `x ≠ 0` of `Kⁱ` with

```text
∏_{v ∈ S} (∏_{k ∈ B v} ‖L_{v,k} x‖_v / ‖x‖_v) ^ mult v ≤ H(x) ^ (-#ι - ε)
```

lie in finitely many proper subspaces of `Kⁱ`. The families may have **any** finite sizes, and
that is the whole of the refinement: Layer 6.3 is the case where every family has exactly `#ι`
members, where general position is linear independence and the two products are the same one.

This is Vojta's strengthening, Bombieri–Gubler's Theorem 7.2.9, and it is Layer 6.3 plus one
local observation and one partition. The observation is `GeneralPosition.lean`: at every point,
some `#ι` of the forms at `v` are independent and their local factor is at most a constant times
the local factor of the whole family. The partition is here: the chosen system at `v` is an index
map `ι → κ ⊕ ι`, of which there are finitely many, so finitely many systems of `#ι` independent
forms cover every solution, 6.3 applies to each, and the constant is absorbed by halving `ε` —
at the cost of the solutions of bounded height, which Northcott collects as finitely many lines.

## Main definitions

* `NumberField.generalProd`: the central quantity, over families of any size.

## Main results

* `NumberField.approxProd_le_mul_generalProd`: the place-by-place comparison.
* `NumberField.exists_finset_submodule_of_generalProd_le`: **the milestone**, Vojta's refinement.
* `NumberField.exists_finset_submodule_setOf_generalProd_le_subset`: the same as an inclusion.

## Implementation notes

⚠ **One carrier type for the forms, and a finset per place for their number.** The families are
`L : AbsoluteValue K ℝ → κ → Dual F (ι → F)` together with `B : AbsoluteValue K ℝ → Finset κ`,
not a family of index *types* `κ v`. The forms at `v` are then `L v` restricted to `B v`, which
is as general — take `κ` large enough — and it is what makes the systems chosen at the places of
`S` range over a single `Fintype`, which the partition needs. `κ` is required finite for the same
reason and for no other.

⚠ **The constant is removed by halving `ε`, and that is why Northcott reappears.** The chosen
system's local factor is only *within a constant* of the given one, so the hypothesis of 6.3 is
met with `ε / 2` in place of `ε` and only above a height threshold; below it the solutions are
finite in projective space and are collected as the lines they span, exactly as in Layer 6.2.
This is the second and last place in the roadmap where Northcott enters the Subspace Theorem.

⚠ **The systems that are not independent are patched, not excluded.** A choice function may name
a system that fails to be independent; there the coordinate forms are substituted, so that 6.3
applies to *every* choice and the union of its answers is a single finite set of subspaces. The
patched choices are never used, and nothing has to be said about them.

⚠ **General position is stated with `Nat.card`.** `Module.Dual.IsGeneralPosition` mentions the
number of coordinates but no product over them, so it needs no `Fintype` instance; `Nat.card`
keeps the definition free of one and agrees with `Fintype.card` wherever both are available.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Definition 7.2.8 and Theorem 7.2.9.

P. Vojta, *Diophantine Approximations and Value Distribution Theory*, Lecture Notes in
Mathematics **1239**, Springer (1987).

This is Layer 6.5 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Finset Height Module Module.Dual

namespace NumberField

section Bridge

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {ι : Type*}

/-- Along an absolute value of `F` over `u`, the local factor of a point of `Kⁱ` is computed in
`K`. -/
theorem iSup_apply_algebraMap_eq {u : AbsoluteValue K ℝ} {W : AbsoluteValue F ℝ}
    (hW : W.LiesOver u) (x : ι → K) :
    (⨆ j, W (algebraMap K F (x j))) = ⨆ j, u (x j) := by
  have := hW
  have h : ∀ j, W (algebraMap K F (x j)) = u (x j) := fun j ↦
    AbsoluteValue.apply_algebraMap_of_liesOver (v := u) W (x j)
  simp only [h]

end Bridge

variable {K F : Type*} [Field K] [NumberField K] [Field F] [Algebra K F] {ι κ : Type*}

/-- **The central quantity of Vojta's refinement**: the same product as `approxProd`, but over a
family of forms of any finite size at every place. -/
noncomputable def generalProd (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (B : AbsoluteValue K ℝ → Finset κ)
    (L : AbsoluteValue K ℝ → κ → Dual F (ι → F)) (x : ι → K) : ℝ :=
  (∏ v ∈ Sinf, (∏ k ∈ B v.1, w v.1 (L v.1 k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j))
      ^ v.mult) *
    ∏ v ∈ Sfin, ∏ k ∈ B v.1, w v.1 (L v.1 k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)

/-- The central quantity of Vojta's refinement is a product of quotients of nonnegative reals. -/
theorem generalProd_nonneg (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (B : AbsoluteValue K ℝ → Finset κ)
    (L : AbsoluteValue K ℝ → κ → Dual F (ι → F)) (x : ι → K) :
    0 ≤ generalProd Sinf Sfin w B L x := by
  have hfac : ∀ (v : AbsoluteValue K ℝ) (W : AbsoluteValue F ℝ) (s : Finset κ),
      (0 : ℝ) ≤ ∏ k ∈ s, W (L v k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) := fun v W s ↦
    Finset.prod_nonneg fun k _ ↦ div_nonneg (W.nonneg _) (Real.iSup_nonneg fun j ↦ v.nonneg _)
  exact mul_nonneg (Finset.prod_nonneg fun v _ ↦ pow_nonneg (hfac v.1 (w v.1) _) _)
    (Finset.prod_nonneg fun v _ ↦ hfac v.1 (w v.1) _)

variable [NumberField F] [Fintype ι]

omit [NumberField F] in
/-- **The comparison that Vojta's refinement runs on**: a system of `#ι` forms whose local factor
is, at every place, at most a constant times the local factor of the given family. -/
theorem approxProd_le_mul_generalProd (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (B : AbsoluteValue K ℝ → Finset κ) (L : AbsoluteValue K ℝ → κ → Dual F (ι → F))
    (L' : AbsoluteValue K ℝ → ι → Dual F (ι → F)) (c : AbsoluteValue K ℝ → ℝ)
    (hc : ∀ u, 1 ≤ c u) (x : ι → K)
    (hI : ∀ v ∈ Sinf, (∏ i, w v.1 (L' v.1 i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j))
      ≤ c v.1 * ∏ k ∈ B v.1, w v.1 (L v.1 k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j))
    (hF : ∀ v ∈ Sfin, (∏ i, w v.1 (L' v.1 i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j))
      ≤ c v.1 * ∏ k ∈ B v.1, w v.1 (L v.1 k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)) :
    approxProd Sinf Sfin w L' x
      ≤ ((∏ v ∈ Sinf, c v.1 ^ v.mult) * ∏ v ∈ Sfin, c v.1) * generalProd Sinf Sfin w B L x := by
  have hanng : ∀ (v : AbsoluteValue K ℝ) (W : AbsoluteValue F ℝ) (s : Finset κ),
      (0 : ℝ) ≤ ∏ k ∈ s, W (L v k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) := fun v W s ↦
    Finset.prod_nonneg fun k _ ↦ div_nonneg (W.nonneg _) (Real.iSup_nonneg fun j ↦ v.nonneg _)
  have hanna : ∀ (v : AbsoluteValue K ℝ) (W : AbsoluteValue F ℝ),
      (0 : ℝ) ≤ ∏ i, W (L' v i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) := fun v W ↦
    Finset.prod_nonneg fun i _ ↦ div_nonneg (W.nonneg _) (Real.iSup_nonneg fun j ↦ v.nonneg _)
  have h1 : (∏ v ∈ Sinf, (∏ i, w v.1 (L' v.1 i fun j ↦ algebraMap K F (x j)) /
        ⨆ j, v (x j)) ^ v.mult)
      ≤ (∏ v ∈ Sinf, c v.1 ^ v.mult) * ∏ v ∈ Sinf,
        (∏ k ∈ B v.1, w v.1 (L v.1 k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)) ^ v.mult := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun v _ ↦ pow_nonneg (hanna _ _) _) fun v hv ↦ ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (hanna _ _) (hI v hv) _
  have h2 : (∏ v ∈ Sfin, ∏ i, w v.1 (L' v.1 i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j))
      ≤ (∏ v ∈ Sfin, c v.1) * ∏ v ∈ Sfin,
        ∏ k ∈ B v.1, w v.1 (L v.1 k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun v _ ↦ hanna _ _) fun v hv ↦ hF v hv
  have hnn1 : (0 : ℝ) ≤ (∏ v ∈ Sinf, c v.1 ^ v.mult) * ∏ v ∈ Sinf,
      (∏ k ∈ B v.1, w v.1 (L v.1 k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)) ^ v.mult :=
    mul_nonneg (Finset.prod_nonneg fun v _ ↦ pow_nonneg (by linarith [hc v.1]) _)
      (Finset.prod_nonneg fun v _ ↦ pow_nonneg (hanng _ _ _) _)
  rw [approxProd, generalProd]
  calc (∏ v ∈ Sinf, (∏ i, w v.1 (L' v.1 i fun j ↦ algebraMap K F (x j)) /
          ⨆ j, v (x j)) ^ v.mult) *
        ∏ v ∈ Sfin, ∏ i, w v.1 (L' v.1 i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)
      ≤ ((∏ v ∈ Sinf, c v.1 ^ v.mult) * ∏ v ∈ Sinf,
            (∏ k ∈ B v.1, w v.1 (L v.1 k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)) ^ v.mult) *
          ((∏ v ∈ Sfin, c v.1) * ∏ v ∈ Sfin,
            ∏ k ∈ B v.1, w v.1 (L v.1 k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)) :=
        mul_le_mul h1 h2 (Finset.prod_nonneg fun v _ ↦ hanna _ _) hnn1
    _ = _ := by ring


open scoped Classical in
/-- **The Subspace Theorem for forms in general position** (Vojta 1987; Bombieri-Gubler,
Theorem 7.2.9). -/
theorem exists_finset_submodule_of_generalProd_le [Nontrivial ι] [Finite κ]
    (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwI : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwF : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (B : AbsoluteValue K ℝ → Finset κ) (L : AbsoluteValue K ℝ → κ → Dual F (ι → F))
    (hLI : ∀ v ∈ Sinf, IsGeneralPosition F (B v.1) (L v.1))
    (hLF : ∀ v ∈ Sfin, IsGeneralPosition F (B v.1) (L v.1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x : ι → K, x ≠ 0 →
        generalProd Sinf Sfin w B L x ≤ mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) →
        ∃ W ∈ T, x ∈ W := by
  have _i : Fintype κ := Fintype.ofFinite κ
  classical
  have hne : Nonempty ι := ⟨Classical.arbitrary ι⟩
  -- the local constant at every absolute value
  have hloc : ∀ u : AbsoluteValue K ℝ, ∃ c : ℝ, 1 ≤ c ∧ (IsGeneralPosition F (B u) (L u) →
      ∀ y : ι → F, y ≠ 0 → ∃ f : ι → κ ⊕ ι,
        LinearIndependent F (fun i ↦ extendProj (L u) (f i)) ∧
        (∏ i, w u (extendProj (L u) (f i) y) / ⨆ j, w u (y j))
          ≤ c * ∏ k ∈ B u, w u (L u k y) / ⨆ j, w u (y j)) := by
    intro u
    by_cases h : IsGeneralPosition F (B u) (L u)
    · obtain ⟨c, hc1, hc⟩ := exists_one_le_forall_exists_index_prod_le (w u) (B u) (L u) h
      exact ⟨c, hc1, fun _ ↦ hc⟩
    · exact ⟨1, le_refl 1, fun h' ↦ absurd h' h⟩
  choose cloc hcloc1 hcloc using hloc
  set Cglob : ℝ := (∏ v ∈ Sinf, cloc v.1 ^ v.mult) * ∏ v ∈ Sfin, cloc v.1 with hCglobdef
  have hCglob1 : 1 ≤ Cglob := by
    refine one_le_mul_of_one_le_of_one_le ?_ ?_
    · exact Finset.one_le_prod₀ fun v _ ↦ one_le_pow₀ (hcloc1 v.1)
    · exact Finset.one_le_prod₀ fun v _ ↦ hcloc1 v.1
  -- the finitely many systems of `#ι` forms
  set P : Finset (AbsoluteValue K ℝ) := Sinf.image (·.1) ∪ Sfin.image (·.1) with hPdef
  set Lg : (P → ι → κ ⊕ ι) → AbsoluteValue K ℝ → ι → Dual F (ι → F) :=
    fun g u ↦ if h : u ∈ P then
      (if LinearIndependent F (fun i ↦ extendProj (L u) (g ⟨u, h⟩ i))
        then fun i ↦ extendProj (L u) (g ⟨u, h⟩ i) else fun i ↦ LinearMap.proj i)
      else fun i ↦ LinearMap.proj i with hLgdef
  have hLgind : ∀ (g : P → ι → κ ⊕ ι) (u : AbsoluteValue K ℝ), LinearIndependent F (Lg g u) := by
    intro g u
    by_cases h : u ∈ P
    · simp only [hLgdef, dite_eq_left h]
      split_ifs with hh
      · exact hh
      · exact linearIndependent_proj
    · simp only [hLgdef, dite_eq_right h]
      exact linearIndependent_proj
  have hfam : ∀ g : P → ι → κ ⊕ ι, ∃ T : Finset (Submodule K (ι → K)),
      (∀ W ∈ T, W ≠ ⊤) ∧ ∀ x : ι → K, x ≠ 0 →
        approxProd Sinf Sfin w (Lg g) x ≤ mulHeight x ^ (-(Fintype.card ι : ℝ) - ε / 2) →
        ∃ W ∈ T, x ∈ W := fun g ↦
    exists_finset_submodule_of_approxProd_le_extension Sinf Sfin w hwI hwF (Lg g)
      (fun v _ ↦ hLgind g v.1) (fun v _ ↦ hLgind g v.1) (by linarith)
  choose Tg hTg1 hTg2 using hfam
  -- the solutions of small height, collected as lines
  set Q₀ : ℝ := max 1 (Cglob ^ ((2 : ℝ) / ε)) with hQ₀def
  have hNor : {Q : Projectivization K (ι → K) | Projectivization.mulHeight Q ≤ Q₀}.Finite :=
    Projectivization.finite_setOfPred_mulHeight_le Q₀
  set Tsmall : Finset (Submodule K (ι → K)) :=
    (hNor.image Projectivization.submodule).toFinset with hTsmalldef
  refine ⟨Tsmall ∪ (Finset.univ : Finset (P → ι → κ ⊕ ι)).biUnion Tg, ?_, ?_⟩
  · intro W hW
    rcases Finset.mem_union.1 hW with hW | hW
    · rw [hTsmalldef, Set.Finite.mem_toFinset] at hW
      obtain ⟨Q, -, rfl⟩ := hW
      intro h
      have h1 : finrank K Q.submodule = 1 := by
        rw [Projectivization.submodule_eq]
        exact finrank_span_singleton Q.rep_nonzero
      rw [h] at h1
      have htop : finrank K (⊤ : Submodule K (ι → K)) = Fintype.card ι := by simp [finrank_top]
      have h2 : 2 ≤ Fintype.card ι := Fintype.one_lt_card
      omega
    · obtain ⟨g, -, hg⟩ := Finset.mem_biUnion.1 hW
      exact hTg1 g W hg
  · intro x hx hbound
    rcases le_or_gt (mulHeight x) Q₀ with hsmall | hlarge
    · refine ⟨(Projectivization.mk K x hx).submodule, Finset.mem_union_left _ ?_, ?_⟩
      · rw [hTsmalldef, Set.Finite.mem_toFinset]
        exact ⟨Projectivization.mk K x hx, by
          simpa [Projectivization.mulHeight_mk] using hsmall, rfl⟩
      · rw [Projectivization.submodule_mk]
        exact Submodule.mem_span_singleton_self x
    · have hy : (fun j ↦ algebraMap K F (x j)) ≠ 0 := by
        intro h
        refine hx (funext fun j ↦ ?_)
        exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective K F)).1 (congrFun h j)
      have hchoice : ∀ p : P, ∃ f : ι → κ ⊕ ι,
          LinearIndependent F (fun i ↦ extendProj (L p.1) (f i)) ∧
          (∏ i, w p.1 (extendProj (L p.1) (f i) fun j ↦ algebraMap K F (x j)) /
              ⨆ j, w p.1 (algebraMap K F (x j)))
            ≤ cloc p.1 * ∏ k ∈ B p.1, w p.1 (L p.1 k fun j ↦ algebraMap K F (x j)) /
              ⨆ j, w p.1 (algebraMap K F (x j)) := by
        intro p
        have hgp : IsGeneralPosition F (B p.1) (L p.1) := by
          rcases Finset.mem_union.1 p.2 with h | h
          · obtain ⟨v, hv, hveq⟩ := Finset.mem_image.1 h
            exact hveq ▸ hLI v hv
          · obtain ⟨v, hv, hveq⟩ := Finset.mem_image.1 h
            exact hveq ▸ hLF v hv
        exact hcloc p.1 hgp _ hy
      choose g hg1 hg2 using hchoice
      have hlocal : ∀ (u : AbsoluteValue K ℝ) (hu : u ∈ P), (w u).LiesOver u →
          (∏ i, w u (Lg g u i fun j ↦ algebraMap K F (x j)) / ⨆ j, u (x j))
            ≤ cloc u * ∏ k ∈ B u, w u (L u k fun j ↦ algebraMap K F (x j)) / ⨆ j, u (x j) := by
        intro u hu hlo
        have hLgu : Lg g u = fun i ↦ extendProj (L u) (g ⟨u, hu⟩ i) := by
          simp only [hLgdef, dite_eq_left hu, ite_eq_left (hg1 ⟨u, hu⟩)]
        rw [hLgu, ← iSup_apply_algebraMap_eq hlo x]
        exact hg2 ⟨u, hu⟩
      have hcmp : approxProd Sinf Sfin w (Lg g) x ≤ Cglob * generalProd Sinf Sfin w B L x :=
        approxProd_le_mul_generalProd Sinf Sfin w B L (Lg g) cloc hcloc1 x
          (fun v hv ↦ hlocal v.1 (Finset.mem_union_left _
            (Finset.mem_image.2 ⟨v, hv, rfl⟩)) (hwI v hv))
          (fun v hv ↦ hlocal v.1 (Finset.mem_union_right _
            (Finset.mem_image.2 ⟨v, hv, rfl⟩)) (hwF v hv))
      have hHpos : (0 : ℝ) < mulHeight x := lt_of_lt_of_le zero_lt_one (one_le_mulHeight x)
      have hCle : Cglob ≤ mulHeight x ^ (ε / 2) := by
        have h1 : Cglob ^ ((2 : ℝ) / ε) ≤ mulHeight x := le_trans (le_max_right _ _) hlarge.le
        have h2 : (Cglob ^ ((2 : ℝ) / ε)) ^ (ε / 2) ≤ mulHeight x ^ (ε / 2) :=
          Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) h1 (by linarith)
        have h3 : (Cglob ^ ((2 : ℝ) / ε)) ^ (ε / 2) = Cglob := by
          rw [← Real.rpow_mul (by linarith), show (2 : ℝ) / ε * (ε / 2) = 1 by field_simp,
            Real.rpow_one]
        rwa [h3] at h2
      have hfinal : approxProd Sinf Sfin w (Lg g) x
          ≤ mulHeight x ^ (-(Fintype.card ι : ℝ) - ε / 2) := by
        calc approxProd Sinf Sfin w (Lg g) x ≤ Cglob * generalProd Sinf Sfin w B L x := hcmp
          _ ≤ mulHeight x ^ (ε / 2) * mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) :=
              mul_le_mul hCle hbound (generalProd_nonneg _ _ _ _ _ _)
                (Real.rpow_nonneg hHpos.le _)
          _ = mulHeight x ^ (-(Fintype.card ι : ℝ) - ε / 2) := by
              rw [← Real.rpow_add hHpos]
              ring_nf
      obtain ⟨W, hWT, hWx⟩ := hTg2 g x hx hfinal
      exact ⟨W, Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨g, Finset.mem_univ g, hWT⟩), hWx⟩

omit [NumberField F] in
/-- **When every place carries `#ι` forms, the central quantity of Vojta's refinement is the one
of Layer 6.3.** The two are the same product, not merely equal ones. -/
theorem generalProd_univ_eq_approxProd (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F)) (x : ι → K) :
    generalProd Sinf Sfin w (fun _ ↦ (Finset.univ : Finset ι)) L x = approxProd Sinf Sfin w L x :=
  rfl

open scoped Classical in
/-- **Vojta's refinement read as an inclusion**: the solution set is contained in a finite union
of proper subspaces. This is the shape the literature states. -/
theorem exists_finset_submodule_setOf_generalProd_le_subset [Nontrivial ι] [Finite κ]
    (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwI : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwF : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (B : AbsoluteValue K ℝ → Finset κ) (L : AbsoluteValue K ℝ → κ → Dual F (ι → F))
    (hLI : ∀ v ∈ Sinf, IsGeneralPosition F (B v.1) (L v.1))
    (hLF : ∀ v ∈ Sfin, IsGeneralPosition F (B v.1) (L v.1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, W ≠ ⊤) ∧
      {x : ι → K | x ≠ 0 ∧ generalProd Sinf Sfin w B L x ≤
          mulHeight x ^ (-(Fintype.card ι : ℝ) - ε)} ⊆ ⋃ W ∈ T, (W : Set (ι → K)) := by
  obtain ⟨T, hT, hx⟩ := exists_finset_submodule_of_generalProd_le Sinf Sfin w hwI hwF B L
    hLI hLF hε
  refine ⟨T, hT, fun x hxmem ↦ ?_⟩
  obtain ⟨W, hWT, hxW⟩ := hx x hxmem.1 hxmem.2
  exact Set.mem_biUnion hWT hxW

section Examples

/-! ### Acceptance criteria -/

open scoped Classical in
/-- **The milestone in the book's display** (Bombieri–Gubler, Theorem 7.2.9): the left-hand side
is `NumberField.generalProd` written out. -/
example [Nontrivial ι] [Finite κ] (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwI : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwF : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (B : AbsoluteValue K ℝ → Finset κ) (L : AbsoluteValue K ℝ → κ → Dual F (ι → F))
    (hLI : ∀ v ∈ Sinf, IsGeneralPosition F (B v.1) (L v.1))
    (hLF : ∀ v ∈ Sfin, IsGeneralPosition F (B v.1) (L v.1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x : ι → K, x ≠ 0 →
        (∏ v ∈ Sinf, (∏ k ∈ B v.1, w v.1 (L v.1 k fun j ↦ algebraMap K F (x j)) /
              ⨆ j, v (x j)) ^ v.mult) *
          ∏ v ∈ Sfin, ∏ k ∈ B v.1, w v.1 (L v.1 k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)
          ≤ mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) →
        ∃ W ∈ T, x ∈ W :=
  exists_finset_submodule_of_generalProd_le Sinf Sfin w hwI hwF B L hLI hLF hε

/-- **Layer 6.3 is the case of equal sizes.** For `#ι` forms at every place, general position is
linear independence and the two central quantities are the same product, so Vojta's refinement
contains the theorem it is proved from: the two are equivalent, and the library carries one. -/
example [Nontrivial ι] (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwI : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwF : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    (hLI : ∀ v ∈ Sinf, LinearIndependent F (L v.1))
    (hLF : ∀ v ∈ Sfin, LinearIndependent F (L v.1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x : ι → K, x ≠ 0 →
        approxProd Sinf Sfin w L x ≤ mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) →
        ∃ W ∈ T, x ∈ W :=
  exists_finset_submodule_of_generalProd_le Sinf Sfin w hwI hwF (fun _ ↦ Finset.univ) L
    (fun v hv ↦ .of_linearIndependent _ (hLI v hv))
    (fun v hv ↦ .of_linearIndependent _ (hLF v hv)) hε

end Examples

end NumberField
