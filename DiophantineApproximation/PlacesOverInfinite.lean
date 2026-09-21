/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Analysis.Normed.Algebra.GelfandMazur
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

-- Used only inside proofs.
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The absolute values of a field lying over an infinite place

Let `K ⊆ F` be fields, `v` an infinite place of `K` and `w` an absolute value of `F` with
`w.LiesOver v` — Mathlib's `AbsoluteValue.LiesOver`. Then `w` is the absolute value of an
**infinite place of `F`**: there is a ring homomorphism `φ : F →+* ℂ` with `w = |φ ·|`.

⚠ Unlike the finite case, no power appears and **no finiteness hypothesis is needed**: `F` may be
any extension field of `K` whatsoever. The reason is that the whole argument happens inside the
completion `F_w`, which is a normed `ℝ`-algebra and a field, hence `ℝ` or `ℂ` by Gelfand–Mazur —
Mathlib's `NormedAlgebra.Real.nonempty_algEquiv_or`, which asks neither for completeness nor for
finite dimension.

The archimedean half of Ostrowski's theorem over a number field, which Mathlib's
`NumberTheory/Ostrowski.lean` proves over `ℚ` and records extending to number fields as a TODO.

## Main results

* `NumberField.isInfinitePlace_of_liesOver` and `NumberField.exists_infinitePlace_eq_of_liesOver`:
  the milestone, in the two shapes.
* `NumberField.exists_liesOver_infinitePlace`: above an infinite place of `K` there is an absolute
  value of `F`, for `F / K` algebraic. Here, unlike at a finite place, the witness *is* an
  infinite place of `F`.
* `AbsoluteValue.isInfinitePlace_of_realRingHom`: the step that does the work — if the completion
  of `F` at `w` contains an isometric copy of `ℝ`, then `w` is an infinite place.
* `NumberField.exists_realRingHom_completion_of_liesOver`: that isometric copy, imported from
  `K_v`. This is the only place where `v` is used at all.
* `AbsoluteValue.eq_norm_of_apply_ofReal`: an absolute value of `ℂ` that restricts to the usual
  one on `ℝ` is the usual one. This is what turns Gelfand–Mazur's `ℝ`-algebra isomorphism into an
  isometry, and Mathlib does not have it.

## Implementation notes

Getting `NormedAlgebra ℝ F_w` is the only place where `v` is used, and it is used only to know
that `K_v` is `ℝ` or `ℂ` — `NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal` and
`ringEquivComplexOfIsComplex`. The completion of `ℚ` at its archimedean place would do just as
well, but Mathlib does not identify it with `ℝ`, whereas it does identify `K_v`.

⚠ The `Algebra` instance on the completions is *not* taken from Mathlib's
`AbsoluteValue.Completion.algebraOfLiesOver`, which is deliberately not an instance (it makes
non-defeq diamonds at `K = F`). The underlying ring homomorphism
`UniformSpace.Completion.mapRingHom` is used directly, which is all the proof wants.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
§1.3. K. Conrad, *Ostrowski for number fields*.

This is the archimedean half of Layer 0.1 of the `DiophantineApproximation` roadmap.
-/

public section

open Filter NumberField

/-- An absolute value of `ℂ` that restricts to the usual absolute value on `ℝ` is the usual
absolute value. -/
theorem AbsoluteValue.eq_norm_of_apply_ofReal {N : AbsoluteValue ℂ ℝ}
    (h : ∀ r : ℝ, N (r : ℂ) = |r|) (z : ℂ) : N z = ‖z‖ := by
  have hI : N Complex.I = 1 := by
    have h2 : N Complex.I ^ 2 = 1 := by
      rw [← map_pow, Complex.I_sq, show ((-1 : ℂ)) = ((-1 : ℝ) : ℂ) by norm_num, h]
      norm_num
    nlinarith [N.nonneg Complex.I]
  have hupper : ∀ y : ℂ, N y ≤ 2 * ‖y‖ := by
    intro y
    have hy : y = (y.re : ℂ) + (y.im : ℂ) * Complex.I := (Complex.re_add_im y).symm
    calc N y ≤ N ((y.re : ℂ)) + N ((y.im : ℂ) * Complex.I) := by
          conv_lhs => rw [hy]
          exact N.add_le _ _
      _ = |y.re| + |y.im| := by rw [map_mul, hI, mul_one, h, h]
      _ ≤ 2 * ‖y‖ := by
          have h1 := Complex.abs_re_le_norm y
          have h2 := Complex.abs_im_le_norm y
          linarith
  have hle : ∀ y : ℂ, N y ≤ ‖y‖ := by
    intro y
    by_contra hcon
    push Not at hcon
    have hNy : 0 < N y := lt_of_le_of_lt (norm_nonneg y) hcon
    set q := ‖y‖ / N y with hq
    have hq0 : 0 ≤ q := div_nonneg (norm_nonneg y) hNy.le
    have hq1 : q < 1 := (div_lt_one hNy).mpr hcon
    have hone : ∀ n : ℕ, (1 : ℝ) ≤ 2 * q ^ n := by
      intro n
      have hn := hupper (y ^ n)
      rw [map_pow, norm_pow] at hn
      rw [hq, div_pow, ← mul_div_assoc, le_div_iff₀ (pow_pos hNy n), one_mul]
      exact hn
    have hlim : Tendsto (fun n : ℕ => 2 * q ^ n) atTop (nhds 0) := by
      simpa using
        (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by rwa [abs_of_nonneg hq0])).const_mul 2
    linarith [ge_of_tendsto' hlim hone]
  rcases eq_or_ne z 0 with rfl | hz0
  · simp
  · refine le_antisymm (hle z) ?_
    have h1 := hle z⁻¹
    rw [map_inv₀, norm_inv] at h1
    have hNz : 0 < N z := N.pos hz0
    have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    exact (inv_le_inv₀ hNz hnz).mp h1

theorem AbsoluteValue.isInfinitePlace_of_realRingHom {F : Type*} [Field F]
    {w : AbsoluteValue F ℝ} (ι : ℝ →+* w.Completion) (hι : ∀ r : ℝ, ‖ι r‖ = ‖r‖) :
    IsInfinitePlace w := by
  let _ : Algebra ℝ w.Completion := ι.toAlgebra
  have hmap : ∀ r : ℝ, algebraMap ℝ w.Completion r = ι r := fun _ => rfl
  let _ : NormedAlgebra ℝ w.Completion :=
    { norm_smul_le := fun r x => by
        rw [Algebra.smul_def, hmap, norm_mul, hι] }
  obtain ⟨ψ, hψ⟩ : ∃ ψ : w.Completion →+* ℂ, ∀ x, ‖ψ x‖ = ‖x‖ := by
    rcases NormedAlgebra.Real.nonempty_algEquiv_or w.Completion with hr | hr
    · obtain ⟨e⟩ := hr
      have hs : ∀ r : ℝ, ‖e.symm r‖ = ‖r‖ := fun r => by
        rw [show e.symm r = algebraMap ℝ w.Completion r by simpa using e.symm.commutes r, hmap, hι]
      refine ⟨Complex.ofRealHom.comp e.toRingHom, fun x => ?_⟩
      rw [RingHom.comp_apply]
      rw [show (Complex.ofRealHom (e.toRingHom x)) = ((e x : ℝ) : ℂ) from rfl,
        Complex.norm_real, ← hs (e x), AlgEquiv.symm_apply_apply]
    · obtain ⟨e⟩ := hr
      have hs : ∀ r : ℝ, ‖e.symm (r : ℂ)‖ = ‖r‖ := fun r => by
        rw [show e.symm (r : ℂ) = algebraMap ℝ w.Completion r by
          simpa using e.symm.commutes r, hmap, hι]
      let N : AbsoluteValue ℂ ℝ :=
        { toFun := fun z => ‖e.symm z‖,
          map_mul' := fun x y => by rw [map_mul, norm_mul],
          nonneg' := fun _ => norm_nonneg _,
          eq_zero' := fun z => by rw [norm_eq_zero, EmbeddingLike.map_eq_zero_iff],
          add_le' := fun x y => by rw [map_add]; exact norm_add_le _ _ }
      have hNr : ∀ r : ℝ, N (r : ℂ) = |r| := fun r => by
        change ‖e.symm (r : ℂ)‖ = |r|
        rw [hs r, Real.norm_eq_abs]
      have hN : ∀ z : ℂ, ‖e.symm z‖ = ‖z‖ := AbsoluteValue.eq_norm_of_apply_ofReal hNr
      refine ⟨e.toRingHom, fun x => ?_⟩
      change ‖e x‖ = ‖x‖
      rw [← hN (e x), AlgEquiv.symm_apply_apply]
  refine ⟨ψ.comp ((UniformSpace.Completion.coeRingHom).comp (WithAbs.equiv w).symm.toRingHom), ?_⟩
  refine AbsoluteValue.ext fun x => ?_
  rw [place_apply, RingHom.comp_apply, hψ]
  change ‖((WithAbs.toAbs w x : WithAbs w) : w.Completion)‖ = w x
  rw [UniformSpace.Completion.norm_coe, WithAbs.norm_eq_apply_ofAbs]

open NumberField.InfinitePlace in
/-- An isometric copy of `ℝ` inside the completion of `F` at an absolute value lying over an
infinite place of `K`. -/
theorem NumberField.exists_realRingHom_completion_of_liesOver
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : NumberField.InfinitePlace K) (w : AbsoluteValue F ℝ) [w.LiesOver v.1] :
    ∃ ι : ℝ →+* w.Completion, ∀ r : ℝ, ‖ι r‖ = ‖r‖ := by
  let g : (v.1).Completion →+* w.Completion :=
    UniformSpace.Completion.mapRingHom (WithAbs.map v.1 w (algebraMap K F))
      (WithAbs.isometry_map v.1 w).continuous
  have hg : ∀ y : (v.1).Completion, ‖g y‖ = ‖y‖ :=
    (AddMonoidHomClass.isometry_iff_norm g).mp
      (UniformSpace.Completion.isometry_mapRingHom (WithAbs.isometry_map v.1 w))
  have hq : ∀ y : NumberField.InfinitePlace.Completion v,
      ‖(NumberField.InfinitePlace.Completion.equiv v) y‖ = ‖y‖ := fun y =>
    NumberField.InfinitePlace.Completion.norm_toCompletion v y
  rcases v.isReal_or_isComplex with hv | hv
  · refine ⟨g.comp ((NumberField.InfinitePlace.Completion.equiv v).toRingHom.comp
      (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm.toRingHom),
      fun r => ?_⟩
    have hemb : ∀ y : NumberField.InfinitePlace.Completion v,
        ‖NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hv y‖ = ‖y‖ :=
      (AddMonoidHomClass.isometry_iff_norm _).mp
        (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv)
    have hr : ‖(NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm r‖ = ‖r‖ := by
      rw [← hemb ((NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm r),
        ← NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal_apply hv,
        RingEquiv.apply_symm_apply]
    change ‖g ((NumberField.InfinitePlace.Completion.equiv v)
      ((NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm r))‖ = ‖r‖
    rw [hg, hq, hr]
  · refine ⟨g.comp ((NumberField.InfinitePlace.Completion.equiv v).toRingHom.comp
      ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm.toRingHom.comp
        Complex.ofRealHom)), fun r => ?_⟩
    have hemb : ∀ y : NumberField.InfinitePlace.Completion v,
        ‖NumberField.InfinitePlace.Completion.extensionEmbedding v y‖ = ‖y‖ :=
      (AddMonoidHomClass.isometry_iff_norm _).mp
        (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v)
    have hr : ‖(NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm
        (r : ℂ)‖ = ‖r‖ := by
      rw [← hemb ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm
          (r : ℂ)),
        ← NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply hv,
        RingEquiv.apply_symm_apply, Complex.norm_real]
    change ‖g ((NumberField.InfinitePlace.Completion.equiv v)
      ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm
        (Complex.ofRealHom r)))‖ = ‖r‖
    rw [hg, hq]
    exact hr

namespace NumberField

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- **Layer 0.1, the archimedean half.** An absolute value of `F` lying over an infinite place of
`K` is the absolute value of an infinite place of `F`. ⚠ No finiteness of `F / K` is used. -/
theorem isInfinitePlace_of_liesOver (v : InfinitePlace K) (w : AbsoluteValue F ℝ)
    [w.LiesOver v.1] : IsInfinitePlace w :=
  let ⟨ι, hι⟩ := exists_realRingHom_completion_of_liesOver v w
  AbsoluteValue.isInfinitePlace_of_realRingHom ι hι

/-- **Layer 0.1, the archimedean half**, in the shape the roadmap pins. -/
theorem exists_infinitePlace_eq_of_liesOver (v : InfinitePlace K) (w : AbsoluteValue F ℝ)
    [w.LiesOver v.1] : ∃ w' : InfinitePlace F, w'.1 = w :=
  (isInfinitePlace_iff w).mp (isInfinitePlace_of_liesOver v w)

/-- **Above an infinite place there is an infinite place.** Unlike at a finite place, the witness
needs no root taken: the extension of an infinite place is an infinite place on the nose. -/
theorem exists_liesOver_infinitePlace [Algebra.IsAlgebraic K F] (v : InfinitePlace K) :
    ∃ w : InfinitePlace F, (w.1).LiesOver v.1 := by
  let _ : Algebra K ℂ := v.embedding.toAlgebra
  let ψ : F →ₐ[K] ℂ := IsAlgClosed.lift
  refine ⟨InfinitePlace.mk ψ.toRingHom, ⟨AbsoluteValue.ext fun u => ?_⟩⟩
  change ‖ψ (algebraMap K F u)‖ = v.1 u
  rw [ψ.commutes u, RingHom.algebraMap_toAlgebra]
  conv_rhs => rw [← v.mk_embedding]
  rfl

end NumberField

section Examples

/-! ### Acceptance criteria -/

/-- **No finiteness hypothesis is used.** The archimedean half of Layer 0.1 holds for an arbitrary
field extension `F / K`: no `NumberField F`, no `FiniteDimensional K F`, not even algebraicity.
Contrast the nonarchimedean half, whose statement mentions the ramification index and the inertia
degree and so needs `F / K` finite. -/
example {K F : Type*} [Field K] [Field F] [Algebra K F] (v : NumberField.InfinitePlace K)
    (w : AbsoluteValue F ℝ) [w.LiesOver v.1] : NumberField.IsInfinitePlace w :=
  NumberField.isInfinitePlace_of_liesOver v w

/-- **The exponent is `1`.** At an infinite place the absolute values above `v` are the infinite
places above `v` on the nose, with no root taken — the one structural difference from the
nonarchimedean half. -/
example {K F : Type*} [Field K] [Field F] [Algebra K F] (v : NumberField.InfinitePlace K)
    (w : AbsoluteValue F ℝ) [w.LiesOver v.1] :
    ∃ w' : NumberField.InfinitePlace F, ∀ y : F, w y = w' y := by
  obtain ⟨w', hw'⟩ := NumberField.exists_infinitePlace_eq_of_liesOver v w
  exact ⟨w', fun y => by rw [← hw']; rfl⟩

/-- **The complex lemma is what makes Gelfand–Mazur an isometry.** Without it one knows only that
`F_w` is `ℝ`-algebra isomorphic to `ℂ`, which says nothing about norms; with it, conjugation —
any `ℝ`-algebra automorphism of `ℂ` — is norm-preserving. -/
example (f : ℂ ≃ₐ[ℝ] ℂ) (z : ℂ) : ‖f z‖ = ‖z‖ := by
  refine AbsoluteValue.eq_norm_of_apply_ofReal (N :=
    { toFun := fun u => ‖f u‖,
      map_mul' := fun x y => by rw [map_mul, norm_mul],
      nonneg' := fun _ => norm_nonneg _,
      eq_zero' := fun u => by rw [norm_eq_zero, EmbeddingLike.map_eq_zero_iff],
      add_le' := fun x y => by rw [map_add]; exact norm_add_le _ _ }) ?_ z
  intro r
  change ‖f ((r : ℝ) : ℂ)‖ = |r|
  rw [show ((r : ℝ) : ℂ) = algebraMap ℝ ℂ r from rfl, f.commutes r]
  simp

end Examples
