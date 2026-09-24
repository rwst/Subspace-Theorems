/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.AffineProd
public import DiophantineApproximation.SubspaceAlgebraic

-- Used only inside proofs.
import DiophantineApproximation.PlacesOver
import DiophantineApproximation.SubspaceReduction

/-!
# The Subspace Theorem for `S`-integral points

**Layer 6.4.** For a number field `K`, a finite set `S` of finite places carried as height-one
primes of `𝓞 K`, an absolute value `w v` of a finite extension `F` over every infinite place and
every place of `S`, forms `L v i : Module.Dual F (Fⁱ)` independent over `F` at each of them, and
`ε > 0`, the points `x ≠ 0` of `Kⁱ` with **`S`-integral coordinates** and

```text
(∏_{v | ∞} (∏ᵢ ‖L_{v,i} x‖_v) ^ mult v) * ∏_{v ∈ S} ∏ᵢ ‖L_{v,i} x‖_v ≤ H(x) ^ (-ε)
```

lie in finitely many proper subspaces of `Kⁱ`. This is Bombieri–Gubler's Corollary 7.2.5, the
form every application quotes: the inequality has no local denominators, the exponent is `-ε`
rather than `-#ι - ε`, and all of the arithmetic sits in the words "`S`-integral".

It is Layer 6.3 and the dictionary of `AffineProd.lean`, and nothing else. In one direction the
`S`-part of the height dominates the height, so the affine inequality implies the projective one
and 6.3 applies. In the other — Theorem 7.2.6, proved here so that the library carries one
theorem and not two — every solution of the projective inequality is, after one scaling to an
`S`-primitive point and after enlarging the data, an `S`-integral solution of the affine one; so
the affine form is no weaker, and composing the two recovers 6.3.

## Main results

* `NumberField.exists_finset_submodule_of_integer_of_affineProd_le`: **the milestone**.
* `NumberField.exists_finset_submodule_setOf_integer_of_affineProd_le_subset`: the same read as
  an inclusion of the solution set in a finite union of proper subspaces.
* `NumberField.exists_finset_forall_exists_smul_affineProd_le`: the converse — the data of the
  affine form that catches every solution of the projective one.
* `NumberField.exists_finset_superset_forall_exists_isPrimitive_smul`: Layer 0.3's normalisation
  in the form the converse needs.
* `NumberField.approxProd_congr`: the central quantity depends on the absolute values and the
  forms only at the places it is taken over.

## Implementation notes

⚠ **The affine form is 6.3 plus the `S`-part of the height, and no new estimate.** The whole of
the forward direction is `AffineProd.lean`'s factorisation together with `H(x) ≤ Hs x`: the
`#ι` local denominators of `approxProd`, which the affine statement drops, are exactly the `#ι`
copies of the height that the exponent `-#ι - ε` carries against the affine `-ε`.

⚠ **`S`-integrality suffices forwards and does not suffice backwards.** For an `S`-integral point
`Hs x` can exceed `H(x)` — the height lost at a place of `S` the coordinates do not fill — and
then the affine inequality is *stronger* than the projective one, which is the direction the
milestone needs. The converse therefore normalises to an `S`-primitive point, where Layer 0.3
makes the two equal. This asymmetry is why Bombieri–Gubler state Corollary 7.2.5 for `S`-integers
and Theorem 7.2.6 for primitive points.

⚠ **The converse enlarges three things at once**, and each is a different layer: every infinite
place must be present and every finite place outside `S` must be harmless, which is Layer 5.1's
coordinate forms, whose local factor is at most `1`; `S` must be large enough for a primitive
multiple to exist, which is Layer 0.3's localisation; and `w` must be defined and lie over `v` at
the added places, which is Layer 0.1's fibre. The third is why the converse returns a new family
`w'` instead of reusing `w`: the affine statement asks for an absolute value of `F` at *every*
infinite place, and the projective one only on `Sinf`.

⚠ **Scaling is invisible to both statements but not to the passage between them.** The projective
inequality and the subspaces are invariant under `x ↦ c • x`; the affine inequality is not, and a
point satisfies it only after being scaled to be primitive. So the converse returns the multiple,
and the subspace it lands in is the subspace of the original point.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Corollary 7.2.5 and Theorem 7.2.6.

This is Layer 6.4 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Finset Height IsDedekindDomain Module

namespace NumberField

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]

/-- **Every finite set of finite places is contained in one over which every nonzero point has an
`S`-primitive multiple.** This is Layer 0.3's normalisation — Bombieri–Gubler's Theorem 7.2.6 —
returning the primitivity itself rather than the height identity it implies, which is what the
converse below needs. -/
theorem exists_finset_superset_forall_exists_isPrimitive_smul {ι : Type*} [Finite ι]
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ S' : Finset (HeightOneSpectrum (𝓞 K)), S ⊆ S' ∧
      ∀ x : ι → K, x ≠ 0 → ∃ c : K, c ≠ 0 ∧
        (S' : Set (HeightOneSpectrum (𝓞 K))).IsPrimitive (c • x) := by
  classical
  obtain ⟨T, hST, hTfin, hTprin⟩ :=
    exists_finite_superset_isPrincipalIdealRing (S : Set (HeightOneSpectrum (𝓞 K)))
      S.finite_toSet
  have hcoe : (hTfin.toFinset : Set (HeightOneSpectrum (𝓞 K))) = T := hTfin.coe_toFinset
  refine ⟨hTfin.toFinset, fun v hv ↦ by simpa [hTfin.mem_toFinset] using hST hv, fun x hx ↦ ?_⟩
  have : IsPrincipalIdealRing ↥(T.integer K) := hTprin
  obtain ⟨c, hc0, hprim⟩ := exists_isPrimitive_mul T hx
  refine ⟨c, hc0, ?_⟩
  rw [hcoe, show (c • x) = fun i ↦ c * x i from funext fun i ↦ by simp]
  exact hprim

variable {ι : Type*} [Fintype ι]

omit [NumberField F] in
/-- **The central quantity sees the absolute values and the forms only at the places it is taken
over.** -/
theorem approxProd_congr (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    {w w' : AbsoluteValue K ℝ → AbsoluteValue F ℝ}
    {L L' : AbsoluteValue K ℝ → ι → Dual F (ι → F)}
    (hwI : ∀ v ∈ Sinf, w' v.1 = w v.1) (hwF : ∀ v ∈ Sfin, w' v.1 = w v.1)
    (hLI : ∀ v ∈ Sinf, L' v.1 = L v.1) (hLF : ∀ v ∈ Sfin, L' v.1 = L v.1) (x : ι → K) :
    approxProd Sinf Sfin w' L' x = approxProd Sinf Sfin w L x := by
  unfold approxProd
  congr 1
  · exact Finset.prod_congr rfl fun v hv ↦ by rw [hwI v hv, hLI v hv]
  · exact Finset.prod_congr rfl fun v hv ↦ by rw [hwF v hv, hLF v hv]

open scoped Classical in
/-- **The Subspace Theorem for `S`-integral points** (Bombieri–Gubler, Corollary 7.2.5) — the
affine form, and the form every application in Layer 8 consumes. The points `x ≠ 0` of `Kⁱ` whose
coordinates are `S`-integers and whose affine product is at most `H(x) ^ (-ε)` lie in finitely
many proper subspaces of `Kⁱ`. `[Nontrivial ι]` is `n ≥ 1`, without which the statement is
false. -/
theorem exists_finset_submodule_of_integer_of_affineProd_le [Nontrivial ι]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    (hLInf : ∀ v : InfinitePlace K, LinearIndependent F (L v.1))
    (hLFin : ∀ v ∈ S, LinearIndependent F (L (FinitePlace.mk v).1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x : ι → K, x ≠ 0 → (∀ j, x j ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) →
        affineProd S w L x ≤ mulHeight x ^ (-ε) → ∃ W ∈ T, x ∈ W := by
  obtain ⟨T, hT, hcov⟩ := exists_finset_submodule_of_approxProd_le_extension
    (Finset.univ : Finset (InfinitePlace K)) (S.image FinitePlace.mk) w
    (fun v _ ↦ hwInf v)
    (fun v hv ↦ by obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hv; exact hwFin P hP)
    L (fun v _ ↦ hLInf v)
    (fun v hv ↦ by obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hv; exact hLFin P hP) hε
  exact ⟨T, hT, fun x hx hxS hb ↦ hcov x hx (approxProd_le_of_affineProd_le S w L hx hxS hb)⟩

/-- **The affine Subspace Theorem, read as an inclusion**: the solution set is contained in a
finite union of proper subspaces. -/
theorem exists_finset_submodule_setOf_integer_of_affineProd_le_subset [Nontrivial ι]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    (hLInf : ∀ v : InfinitePlace K, LinearIndependent F (L v.1))
    (hLFin : ∀ v ∈ S, LinearIndependent F (L (FinitePlace.mk v).1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, W ≠ ⊤) ∧
      {x : ι → K | x ≠ 0 ∧ (∀ j, x j ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) ∧
          affineProd S w L x ≤ mulHeight x ^ (-ε)} ⊆ ⋃ W ∈ T, (W : Set (ι → K)) := by
  obtain ⟨T, hT, hcov⟩ := exists_finset_submodule_of_integer_of_affineProd_le S w hwInf hwFin
    L hLInf hLFin hε
  refine ⟨T, hT, fun x hxmem ↦ ?_⟩
  obtain ⟨W, hWT, hxW⟩ := hcov x hxmem.1 hxmem.2.1 hxmem.2.2
  exact Set.mem_biUnion hWT hxW

open scoped Classical in
/-- **The affine form catches every solution of the projective one** (Bombieri–Gubler, Theorem
7.2.6). Given the data of Layer 6.3 there are a larger `S`, an absolute value `w' v` of `F` over
*every* infinite place and every place of `S`, and forms `L'` independent at each of them —
agreeing with `w` and `L` where those are given — such that every solution `x` of the projective
inequality has a nonzero multiple that is `S`-primitive and solves the affine inequality. With
the milestone above this recovers Layer 6.3, so the two forms of the Subspace Theorem are
equivalent. -/
theorem exists_finset_forall_exists_smul_affineProd_le
    (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwI : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwF : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    (hLI : ∀ v ∈ Sinf, LinearIndependent F (L v.1))
    (hLF : ∀ v ∈ Sfin, LinearIndependent F (L v.1)) (ε : ℝ) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (w' : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
        (L' : AbsoluteValue K ℝ → ι → Dual F (ι → F)),
      (∀ v : InfinitePlace K, (w' v.1).LiesOver v.1) ∧
      (∀ v ∈ S, (w' (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1) ∧
      (∀ v : InfinitePlace K, LinearIndependent F (L' v.1)) ∧
      (∀ v ∈ S, LinearIndependent F (L' (FinitePlace.mk v).1)) ∧
      ∀ x : ι → K, x ≠ 0 →
        approxProd Sinf Sfin w L x ≤ mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) →
        ∃ c : K, c ≠ 0 ∧ (S : Set (HeightOneSpectrum (𝓞 K))).IsPrimitive (c • x) ∧
          affineProd S w' L' (c • x) ≤ mulHeight (c • x) ^ (-ε) := by
  obtain ⟨S, hS₀S, hprim⟩ := exists_finset_superset_forall_exists_isPrimitive_smul
    (ι := ι) (Sfin.image FinitePlace.maximalIdeal)
  have hsub : Sfin ⊆ S.image FinitePlace.mk := fun v hv ↦
    Finset.mem_image.2 ⟨FinitePlace.maximalIdeal v,
      hS₀S (Finset.mem_image_of_mem _ hv), FinitePlace.mk_maximalIdeal v⟩
  have hext : ∀ u : AbsoluteValue K ℝ, ∃ V : AbsoluteValue F ℝ,
      (IsInfinitePlace u ∨ IsFinitePlace u) → V.LiesOver u := by
    intro u
    by_cases h : IsInfinitePlace u ∨ IsFinitePlace u
    · obtain ⟨V, hV⟩ := (finite_nonempty_setOf_liesOver (F := F) u h).2
      exact ⟨V, fun _ ↦ hV⟩
    · exact ⟨(Classical.arbitrary (InfinitePlace F)).1, fun h' ↦ absurd h' h⟩
  choose V hV using hext
  set P : Set (AbsoluteValue K ℝ) := (fun v : InfinitePlace K ↦ v.1) '' (Sinf : Set _) ∪
    (fun v : FinitePlace K ↦ v.1) '' (Sfin : Set _) with hP
  have hPI : ∀ v : InfinitePlace K, v.1 ∈ P ↔ v ∈ Sinf := by
    intro v
    refine ⟨fun h ↦ ?_, fun h ↦ Or.inl ⟨v, h, rfl⟩⟩
    rcases h with ⟨v', hv', h⟩ | ⟨u, -, h⟩
    · rwa [← Subtype.ext h]
    · exact absurd h.symm (InfinitePlace.val_ne_finitePlace_val v u)
  have hPF : ∀ v : FinitePlace K, v.1 ∈ P ↔ v ∈ Sfin := by
    intro v
    refine ⟨fun h ↦ ?_, fun h ↦ Or.inr ⟨v, h, rfl⟩⟩
    rcases h with ⟨u, -, h⟩ | ⟨v', hv', h⟩
    · exact absurd h (InfinitePlace.val_ne_finitePlace_val u v)
    · rwa [← Subtype.ext h]
  set w' : AbsoluteValue K ℝ → AbsoluteValue F ℝ := fun u ↦ if u ∈ P then w u else V u with hw'
  set L' : AbsoluteValue K ℝ → ι → Dual F (ι → F) :=
    fun u ↦ if u ∈ P then L u else fun i ↦ LinearMap.proj i with hL'
  have hw'I : ∀ v : InfinitePlace K, w' v.1 = if v ∈ Sinf then w v.1 else V v.1 :=
    fun v ↦ by simp only [hw', hPI]
  have hw'F : ∀ v : FinitePlace K, w' v.1 = if v ∈ Sfin then w v.1 else V v.1 :=
    fun v ↦ by simp only [hw', hPF]
  have hL'I : ∀ v : InfinitePlace K, L' v.1 = if v ∈ Sinf then L v.1 else
      fun i ↦ LinearMap.proj i := fun v ↦ by simp only [hL', hPI]
  have hL'F : ∀ v : FinitePlace K, L' v.1 = if v ∈ Sfin then L v.1 else
      fun i ↦ LinearMap.proj i := fun v ↦ by simp only [hL', hPF]
  have hloInf : ∀ v : InfinitePlace K, (w' v.1).LiesOver v.1 := by
    intro v
    rw [hw'I]
    split_ifs with hv
    · exact hwI v hv
    · exact hV v.1 (Or.inl v.isInfinitePlace)
  have hloFin : ∀ v : FinitePlace K, (w' v.1).LiesOver v.1 := by
    intro v
    rw [hw'F]
    split_ifs with hv
    · exact hwF v hv
    · exact hV v.1 (Or.inr v.isFinitePlace)
  refine ⟨S, w', L', hloInf, fun v _ ↦ hloFin (FinitePlace.mk v), fun v ↦ ?_,
    fun v _ ↦ ?_, fun x hx hb ↦ ?_⟩
  · rw [hL'I]
    split_ifs with hv
    · exact hLI v hv
    · exact linearIndependent_proj
  · rw [hL'F]
    split_ifs with hv
    · exact hLF _ hv
    · exact linearIndependent_proj
  · obtain ⟨c, hc0, hprimx⟩ := hprim x hx
    refine ⟨c, hc0, hprimx, ?_⟩
    rw [affineProd_le_iff_of_isPrimitive S w' L' hprimx]
    calc approxProd Finset.univ (S.image FinitePlace.mk) w' L' (c • x)
        ≤ approxProd Sinf Sfin w' L' (c • x) := by
          refine approxProd_le_approxProd_of_subset (Finset.subset_univ _) hsub w'
            (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (c • x) (fun v _ hv ↦ ?_) (fun v _ hv ↦ ?_)
          · have := hloInf v
            simp only [hL'I, hv, ↓reduceIte]
            exact prod_proj_div_iSup_le_one (w' v.1) v.1 (c • x)
          · have := hloFin v
            simp only [hL'F, hv, ↓reduceIte]
            exact prod_proj_div_iSup_le_one (w' v.1) v.1 (c • x)
      _ = approxProd Sinf Sfin w L (c • x) :=
          approxProd_congr Sinf Sfin (fun v hv ↦ by rw [hw'I]; simp [hv])
            (fun v hv ↦ by rw [hw'F]; simp [hv]) (fun v hv ↦ by rw [hL'I]; simp [hv])
            (fun v hv ↦ by rw [hL'F]; simp [hv]) (c • x)
      _ = approxProd Sinf Sfin w L x := approxProd_smul Sinf Sfin w hwI hwF L x hc0
      _ ≤ mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) := hb
      _ = mulHeight (c • x) ^ (-(Fintype.card ι : ℝ) - ε) := by
          rw [Height.mulHeight_smul_eq_mulHeight x hc0]

end NumberField

section Examples

/-! ### Acceptance criteria -/

open Height IsDedekindDomain Module NumberField

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
variable {ι : Type*} [Fintype ι]

/-- **The affine product written out.** The milestone is the statement of Bombieri–Gubler's
Corollary 7.2.5 verbatim, with no denominators and with the product over the infinite places and
`S`. -/
example [Nontrivial ι] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    (hLInf : ∀ v : InfinitePlace K, LinearIndependent F (L v.1))
    (hLFin : ∀ v ∈ S, LinearIndependent F (L (FinitePlace.mk v).1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x : ι → K, x ≠ 0 → (∀ j, x j ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) →
        (∏ v : InfinitePlace K,
            (∏ i, w v.1 (L v.1 i fun j ↦ algebraMap K F (x j))) ^ v.mult) *
          ∏ v ∈ S, ∏ i, w (FinitePlace.mk v).1
            (L (FinitePlace.mk v).1 i fun j ↦ algebraMap K F (x j)) ≤ mulHeight x ^ (-ε) →
        ∃ W ∈ T, x ∈ W :=
  exists_finset_submodule_of_integer_of_affineProd_le S w hwInf hwFin L hLInf hLFin hε

/-- **The affine form implies Layer 6.3**, which with the milestone makes the two equivalent: the
converse produces the data and the scaling, the milestone produces the subspaces, and the
subspaces of the multiple are the subspaces of the point. -/
example [Nontrivial ι] (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwI : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwF : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    (hLI : ∀ v ∈ Sinf, LinearIndependent F (L v.1))
    (hLF : ∀ v ∈ Sfin, LinearIndependent F (L v.1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x : ι → K, x ≠ 0 →
        approxProd Sinf Sfin w L x ≤ mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) →
        ∃ W ∈ T, x ∈ W := by
  obtain ⟨S, w', L', hloI, hloF, hliI, hliF, hkey⟩ :=
    exists_finset_forall_exists_smul_affineProd_le Sinf Sfin w hwI hwF L hLI hLF ε
  obtain ⟨T, hT, hcov⟩ :=
    exists_finset_submodule_of_integer_of_affineProd_le S w' hloI hloF L' hliI hliF hε
  refine ⟨T, hT, fun x hx hb ↦ ?_⟩
  obtain ⟨c, hc0, hprimx, haff⟩ := hkey x hx hb
  obtain ⟨W, hWT, hmem⟩ := hcov (c • x) (smul_ne_zero hc0 hx)
    ((Set.isPrimitive_iff _ _).mp hprimx).1 haff
  refine ⟨W, hWT, ?_⟩
  rw [← inv_smul_smul₀ hc0 x]
  exact W.smul_mem c⁻¹ hmem

end Examples
