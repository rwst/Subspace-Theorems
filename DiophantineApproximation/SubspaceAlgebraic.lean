/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.ExtensionApproxProd
public import DiophantineApproximation.SubspaceTheorem

-- Used only inside proofs.
import ArithmeticHeights.Extension
import DiophantineApproximation.PlacesOver
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Closure

/-!
# The Subspace Theorem, with algebraic coefficients

For number fields `K ⊆ F`, finite sets `Sinf` of infinite and `Sfin` of finite places of `K`,
an absolute value `w v` of `F` over each of them, forms `L v i : Module.Dual F (Fⁱ)` linearly
independent over `F`, and `ε > 0`, the points `x ≠ 0` of **`Kⁱ`** with

```text
approxProd Sinf Sfin w L x ≤ H(x) ^ (-#ι - ε)
```

lie in finitely many proper linear subspaces of `Kⁱ`. This is Bombieri–Gubler's Theorem 7.2.2
with Remark 7.2.3 — Schmidt's Subspace Theorem in the form its consumers apply, since the
coefficients of the forms are algebraic numbers and not elements of the field the solutions live
in.

The route is the book's. Pass to the Galois closure `E` of `F / K`; extend each `w v` to `E`; at
**every** place of `E` above `v` put the conjugate, under the automorphism that moves the chosen
absolute value to that place, of the system at `v`. A point of `Kⁱ` is fixed by every such
automorphism, so it sees the same local factor at every place above `v`, and the local degrees
above `v` sum to `[E : K]`; the same degree relates the height over `E` to the height over `K`.
So the inequality over `E` is the inequality over `K` raised to `[E : K]`, Layer 6.2 applies over
`E`, and the subspaces of `Eⁱ` it returns are intersected back with `Kⁱ`, where they stay proper.

## Main results

* `NumberField.exists_finset_submodule_of_approxProd_le_of_isGalois`: the theorem for `F / K`
  Galois, which is where all the work is.
* `NumberField.exists_finset_submodule_of_approxProd_le_extension`: **the milestone**, for any
  finite extension.
* `NumberField.exists_finset_submodule_setOf_approxProd_le_extension_subset`: the same read as an
  inclusion of the solution set in a finite union of proper subspaces.

## Implementation notes

⚠ **The conjugation is a ring homomorphism applied to the coefficients, and so is the base
change.** A form on `Fⁱ` is its vector of coefficients, so `Module.Dual.compRingHom` carries it
along any `f : F →+* E`; the base change is `f = algebraMap F E` and the conjugation is
`f = σ`, and a conjugated base change is the single homomorphism `σ ∘ algebraMap F E`
(`FormBaseChange.lean`). Nothing here needs a semilinear map or a tensor product.

⚠ **Intersecting a subspace of `Eⁱ` with `Kⁱ` is a `comap`, and properness is the standard
basis.** `W ∩ Kⁱ` is `(W.restrictScalars K).comap φ` for the `K`-linear `φ : Kⁱ → Eⁱ`; if that is
everything then `W` contains every `Pi.single j 1`, which span `Eⁱ` over `E`, so `W = ⊤`. The
degree of `E / K` plays no part in this step.

⚠ **The extension of `w v` to the Galois closure exists but is not canonical, and need not be.**
Layer 0.1's `NumberField.exists_liesOver_of_liesOver` supplies one; which one is chosen changes
the systems of forms at every place above `v` but not the value of any local factor at a point of
`Kⁱ`, which is why the identity of `ExtensionApproxProd.lean` is an identity.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Theorem 7.2.2 and Remark 7.2.3.

W. M. Schmidt, "Norm form equations", *Annals of Mathematics* **96** (1972), 526–551.

H. P. Schlickewei, "The `𝔭`-adic Thue–Siegel–Roth–Schmidt theorem", *Archiv der Mathematik* **29**
(1977), 267–270.

This is Layer 6.3 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Finset Height Module NumberField

namespace NumberField

variable {K E : Type*} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
variable {ι : Type*} [Fintype ι]

section Galois

open scoped Classical in
/-- **The Subspace Theorem over a Galois extension** (Bombieri–Gubler, Theorem 7.2.2 with
Remark 7.2.3). For `E / K` Galois and forms with coefficients in `E`, the solutions in `Kⁱ` lie in
finitely many proper subspaces of `Kⁱ`. This is where the work is: the conjugated systems of
`ExtensionApproxProd.lean` turn the inequality over `K` into the inequality over `E` raised to the
degree, Layer 6.2 applies over `E`, and its subspaces are intersected back with `Kⁱ`. -/
theorem exists_finset_submodule_of_approxProd_le_of_isGalois [Nontrivial ι] [IsGalois K E]
    (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w' : AbsoluteValue K ℝ → AbsoluteValue E ℝ)
    (hwI : ∀ v ∈ Sinf, (w' v.1).LiesOver v.1) (hwF : ∀ v ∈ Sfin, (w' v.1).LiesOver v.1)
    (L : AbsoluteValue K ℝ → ι → Dual E (ι → E))
    (hLI : ∀ v ∈ Sinf, LinearIndependent E (L v.1))
    (hLF : ∀ v ∈ Sfin, LinearIndependent E (L v.1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x : ι → K, x ≠ 0 →
        approxProd Sinf Sfin w' L x ≤ mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) →
        ∃ W ∈ T, x ∈ W := by
  classical
  have hne : Nonempty ι := ⟨Classical.arbitrary ι⟩
  obtain ⟨T', hT', hcov⟩ := exists_finset_submodule_of_approxProd_le
    (K := E) (ι := ι) (Sinf.biUnion (InfinitePlace.placesOverFinset E))
    (Sfin.biUnion (FinitePlace.placesOverFinset E)) (conjSystem Sinf Sfin w' L)
    (fun V hV ↦ by
      obtain ⟨v, hv, hVv⟩ := Finset.mem_biUnion.1 hV
      exact linearIndependent_conjSystem_inf hwI hLI hv (InfinitePlace.mem_placesOverFinset.1 hVv))
    (fun V hV ↦ by
      obtain ⟨v, hv, hVv⟩ := Finset.mem_biUnion.1 hV
      exact linearIndependent_conjSystem_fin hwF hLF hv (FinitePlace.mem_placesOverFinset.1 hVv))
    hε
  set φ : (ι → K) →ₗ[K] (ι → E) :=
    LinearMap.pi fun j ↦ (Algebra.linearMap K E).comp (LinearMap.proj j) with hφ
  refine ⟨T'.image fun W ↦ (W.restrictScalars K).comap φ, ?_, ?_⟩
  · intro W hW
    obtain ⟨W', hW'T, rfl⟩ := Finset.mem_image.1 hW
    intro h
    refine hT' W' hW'T (top_le_iff.1 ?_)
    have hsingle : ∀ j : ι, (Pi.single j (1 : E)) ∈ W' := by
      intro j
      have hx : (Pi.single j (1 : K)) ∈ (W'.restrictScalars K).comap φ := by rw [h]; trivial
      have hval : φ (Pi.single j (1 : K)) = Pi.single j (1 : E) := by
        funext k
        by_cases hk : k = j
        · subst hk; simp [hφ]
        · simp [hφ, Pi.single_eq_of_ne hk]
      rw [Submodule.mem_comap, Submodule.restrictScalars_mem, hval] at hx
      exact hx
    rw [← (Pi.basisFun E ι).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    simpa [Pi.basisFun_apply] using hsingle j
  · intro x hx hbound
    have hyne : (fun j ↦ algebraMap K E (x j)) ≠ 0 := by
      intro h
      refine hx (funext fun j ↦ ?_)
      have := congrFun h j
      exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective K E)).1 this
    have hH : (1 : ℝ) ≤ mulHeight x := Height.one_le_mulHeight x
    have hnn : 0 ≤ approxProd Sinf Sfin w' L x := approxProd_nonneg _ _ _ _ _
    have hle : approxProd (Sinf.biUnion (InfinitePlace.placesOverFinset E))
        (Sfin.biUnion (FinitePlace.placesOverFinset E)) (fun V ↦ V)
        (conjSystem Sinf Sfin w' L) (fun j ↦ algebraMap K E (x j))
        ≤ mulHeight (fun j ↦ algebraMap K E (x j)) ^ (-(Fintype.card ι : ℝ) - ε) := by
      rw [approxProd_conjSystem hwI hwF x,
        show mulHeight (fun j ↦ algebraMap K E (x j)) = mulHeight x ^ finrank K E from
          (NumberField.mulHeight_pow_finrank (L := E) x).symm,
        ← Real.rpow_natCast (mulHeight x) (finrank K E), ← Real.rpow_mul (by linarith),
        mul_comm, Real.rpow_mul (by linarith), Real.rpow_natCast]
      exact pow_le_pow_left₀ hnn hbound _
    obtain ⟨W', hW'T, hmem⟩ := hcov _ hyne hle
    exact ⟨(W'.restrictScalars K).comap φ, Finset.mem_image.2 ⟨W', hW'T, rfl⟩, hmem⟩

end Galois

section Extension

variable {F : Type*} [Field F] [NumberField F] [Algebra K F]

open scoped Classical in
/-- **The Subspace Theorem with algebraic coefficients** (Schmidt 1972; Schlickewei 1977;
Bombieri–Gubler, Theorem 7.2.2 with Remark 7.2.3) — **the form consumers apply**. For any finite
extension `F / K`, an absolute value of `F` over each place of `Sinf` and `Sfin`, forms with
coefficients in `F` independent over `F`, and `ε > 0`, the points `x ≠ 0` of `Kⁱ` with
`approxProd Sinf Sfin w L x ≤ H(x) ^ (-#ι - ε)` lie in finitely many proper subspaces of `Kⁱ`.

Both forms in print are instances: `F = K` is Layer 6.2, and `K = ℚ` is Schmidt's theorem for
linear forms with algebraic coefficients in rational points. -/
theorem exists_finset_submodule_of_approxProd_le_extension [Nontrivial ι]
    (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwI : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwF : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    (hLI : ∀ v ∈ Sinf, LinearIndependent F (L v.1))
    (hLF : ∀ v ∈ Sfin, LinearIndependent F (L v.1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x : ι → K, x ≠ 0 →
        approxProd Sinf Sfin w L x ≤ mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) →
        ∃ W ∈ T, x ∈ W := by
  classical
  set E := IntermediateField.normalClosure K F (AlgebraicClosure F) with hE
  have hfd : FiniteDimensional ℚ E := FiniteDimensional.trans ℚ K E
  have hnf : NumberField E := ⟨⟩
  have hext : ∀ u : AbsoluteValue K ℝ, ∃ W : AbsoluteValue E ℝ,
      ((∃ v ∈ Sinf, u = v.1) ∨ (∃ v ∈ Sfin, u = v.1)) →
        W.LiesOver u ∧ ∀ z : F, W (algebraMap F E z) = w u z := by
    intro u
    by_cases h : (∃ v ∈ Sinf, u = v.1) ∨ (∃ v ∈ Sfin, u = v.1)
    · have hplace : IsInfinitePlace u ∨ IsFinitePlace u := by
        rcases h with ⟨v, -, rfl⟩ | ⟨v, -, rfl⟩
        · exact Or.inl v.isInfinitePlace
        · exact Or.inr v.isFinitePlace
      have hlo : (w u).LiesOver u := by
        rcases h with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
        · exact hwI v hv
        · exact hwF v hv
      obtain ⟨W, hW⟩ := exists_liesOver_of_liesOver (F' := E) u hplace (w u)
      have hWF : ∀ z : F, W (algebraMap F E z) = w u z := fun z ↦
        congrFun (congrArg (fun (a : AbsoluteValue F ℝ) ↦ (a : F → ℝ))
          (AbsoluteValue.LiesOver.under_eq W (w u) (K := F))) z
      have hwK : ∀ y : K, w u (algebraMap K F y) = u y := fun y ↦
        congrFun (congrArg (fun (a : AbsoluteValue K ℝ) ↦ (a : K → ℝ))
          (AbsoluteValue.LiesOver.under_eq (w u) u (K := K))) y
      refine ⟨W, fun _ ↦ ⟨⟨AbsoluteValue.ext fun y ↦ ?_⟩, hWF⟩⟩
      change W (algebraMap K E y) = u y
      rw [IsScalarTower.algebraMap_apply K F E y, hWF, hwK]
    · exact ⟨(Classical.arbitrary (InfinitePlace E)).1, fun h' ↦ absurd h' h⟩
  choose w' hw using hext
  set L' : AbsoluteValue K ℝ → ι → Dual E (ι → E) :=
    fun u i ↦ (L u i).compRingHom (algebraMap F E) with hL'
  have hval : ∀ u : AbsoluteValue K ℝ, ((∃ v ∈ Sinf, u = v.1) ∨ (∃ v ∈ Sfin, u = v.1)) →
      ∀ (i : ι) (x : ι → K), w' u (L' u i fun j ↦ algebraMap K E (x j))
        = w u (L u i fun j ↦ algebraMap K F (x j)) := by
    intro u hu i x
    have hcomp : (fun j ↦ algebraMap K E (x j))
        = fun j ↦ algebraMap F E (algebraMap K F (x j)) := by
      funext j
      rw [IsScalarTower.algebraMap_apply K F E]
    have hstep : L' u i (fun j ↦ algebraMap K E (x j))
        = algebraMap F E (L u i fun j ↦ algebraMap K F (x j)) := by
      rw [hL', hcomp]
      exact Module.Dual.compRingHom_comp (L u i) (algebraMap F E) _
    rw [hstep, (hw u hu).2]
  have hEq : ∀ x : ι → K, approxProd Sinf Sfin w' L' x = approxProd Sinf Sfin w L x := by
    intro x
    simp only [approxProd]
    congr 1
    · exact Finset.prod_congr rfl fun v hv ↦ by
        congr 1
        exact Finset.prod_congr rfl fun i _ ↦ by rw [hval v.1 (Or.inl ⟨v, hv, rfl⟩) i x]
    · exact Finset.prod_congr rfl fun v hv ↦
        Finset.prod_congr rfl fun i _ ↦ by rw [hval v.1 (Or.inr ⟨v, hv, rfl⟩) i x]
  obtain ⟨T, hT, hcov⟩ := exists_finset_submodule_of_approxProd_le_of_isGalois (E := E)
    Sinf Sfin w' (fun v hv ↦ (hw v.1 (Or.inl ⟨v, hv, rfl⟩)).1)
    (fun v hv ↦ (hw v.1 (Or.inr ⟨v, hv, rfl⟩)).1) L'
    (fun v hv ↦ Module.Dual.linearIndependent_compRingHom (hLI v hv) _)
    (fun v hv ↦ Module.Dual.linearIndependent_compRingHom (hLF v hv) _) hε
  exact ⟨T, hT, fun x hx hb ↦ hcov x hx (by rw [hEq x]; exact hb)⟩


/-- **The Subspace Theorem with algebraic coefficients, read as an inclusion**: the solution set
is contained in a finite union of proper subspaces. -/
theorem exists_finset_submodule_setOf_approxProd_le_extension_subset [Nontrivial ι]
    (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwI : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwF : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    (hLI : ∀ v ∈ Sinf, LinearIndependent F (L v.1))
    (hLF : ∀ v ∈ Sfin, LinearIndependent F (L v.1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, W ≠ ⊤) ∧
      {x : ι → K | x ≠ 0 ∧ approxProd Sinf Sfin w L x ≤
          mulHeight x ^ (-(Fintype.card ι : ℝ) - ε)} ⊆ ⋃ W ∈ T, (W : Set (ι → K)) := by
  classical
  obtain ⟨T, hT, hx⟩ := exists_finset_submodule_of_approxProd_le_extension Sinf Sfin w hwI hwF
    L hLI hLF hε
  refine ⟨T, hT, fun x hxmem ↦ ?_⟩
  obtain ⟨W, hWT, hxW⟩ := hx x hxmem.1 hxmem.2
  exact Set.mem_biUnion hWT hxW

end Extension

section Examples

/-! ### Acceptance criteria -/

/-- **Layer 6.2 is the case `F = K` of the milestone**, with the identity as the family of
absolute values: every absolute value of `K` lies over itself. The two statements in print are
instances of this one, and this is the first of them. -/
example [Nontrivial ι] (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K))
    (hLI : ∀ v ∈ Sinf, LinearIndependent K (L v.1))
    (hLF : ∀ v ∈ Sfin, LinearIndependent K (L v.1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x : ι → K, x ≠ 0 →
        approxProd Sinf Sfin (fun v ↦ v) L x ≤ mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) →
        ∃ W ∈ T, x ∈ W :=
  exists_finset_submodule_of_approxProd_le_extension (F := K) Sinf Sfin (fun v ↦ v)
    (fun _ _ ↦ ⟨AbsoluteValue.ext fun _ ↦ rfl⟩) (fun _ _ ↦ ⟨AbsoluteValue.ext fun _ ↦ rfl⟩)
    L hLI hLF hε

end Examples

end NumberField
