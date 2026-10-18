/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.SubspaceGeneralPosition

-- Used only inside proofs.
import ArithmeticHeights.Matrix
import ArithmeticHeights.Northcott

/-!
# The Subspace Theorem on a subspace

For a `K`-subspace `U ⊆ Kⁱ` of dimension `d ≥ 2`, and at every place of `S` a family of `d`
linear forms `L v k : Module.Dual F (Fⁱ)` whose restrictions to `U` are linearly independent, the
points `x ≠ 0` of `U` with

```text
∏_{v ∈ S} (∏_k ‖L_{v,k} x‖_v / ‖x‖_v) ^ mult v ≤ H(x) ^ (-d - ε)
```

lie in finitely many proper subspaces of `U`. Layer 6.3 is the case `U = Kⁱ`.

The proof is 6.3 in coordinates. A basis of `U` is a matrix `M : Kⁱˣᵏ` with `x = M y`, the forms
become `L v k ∘ M`, and two quantities change by bounded factors only: the local factor `‖x‖_v`,
at most `c_v ‖y‖_v` by the triangle inequality, and the height, `H(y) ≤ C H(x)` through a left
inverse of `M`. The constant in front of `H(y)^{-d-ε}` is removed by halving `ε` above a height
threshold, and the points below it are finitely many lines by Northcott, as in Layer 6.5.

## Main results

* `NumberField.iSup_mulVec_le`: the local comparison `‖M y‖_v ≤ c_v ‖y‖_v`.
* `NumberField.exists_finset_submodule_lt_of_generalProd_le`: **the theorem**.

## Implementation notes

⚠ **Independence on `U` is stated for functions on `U`.** The forms `L v k` live on `Fⁱ`; their
restrictions to the `K`-points of `U`, as functions `U → F`, are asked to be `F`-linearly
independent. That is independence on `U_F = span_F U`, without forming `U_F`, and it is exactly
what transports to independence of the forms `L v k ∘ M` on `Fᵏ`.

⚠ **The central quantity is `generalProd` with all forms.** With `d` forms on `Fⁱ`, the product
of 6.3 is not an `approxProd` (that needs `#ι` forms), but it is Layer 6.5's `generalProd` over
`Finset.univ`, which takes forms of any index type.

This is milestone FW.1 of `FaltingsWustholz1994/README.md`, placed in the
`DiophantineApproximation` roadmap after Layer 6.5 because nothing in it is specific to that
paper.
-/

@[expose] public section

open Finset Height Module Module.Dual

namespace NumberField

section Local

variable {K : Type*} [Field K] {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **The local factor of `M y` is at most a constant times that of `y`**, at any absolute
value; the constant is `max 1 (∑ⱼ ∑ₖ |M j k|)`. -/
theorem iSup_mulVec_le [Nonempty ι] (u : AbsoluteValue K ℝ) (M : Matrix ι κ K) (y : κ → K) :
    (⨆ j, u (M.mulVec y j)) ≤ max 1 (∑ j, ∑ k, u (M j k)) * ⨆ k, u (y k) := by
  have hS : 0 ≤ ⨆ k, u (y k) := Real.iSup_nonneg fun k ↦ u.nonneg _
  refine ciSup_le fun j ↦ ?_
  calc u (M.mulVec y j) = u (∑ k, M j k * y k) := rfl
    _ ≤ ∑ k, u (M j k * y k) := u.sum_le _ _
    _ = ∑ k, u (M j k) * u (y k) := by simp only [map_mul]
    _ ≤ ∑ k, u (M j k) * ⨆ k, u (y k) := by
        gcongr with k
        exact le_ciSup (f := fun k ↦ u (y k)) (Finite.bddAbove_range _) k
    _ = (∑ k, u (M j k)) * ⨆ k, u (y k) := by rw [Finset.sum_mul]
    _ ≤ (∑ j, ∑ k, u (M j k)) * ⨆ k, u (y k) := by
        gcongr
        exact Finset.single_le_sum (f := fun j ↦ ∑ k, u (M j k))
          (fun j _ ↦ Finset.sum_nonneg fun k _ ↦ u.nonneg _) (Finset.mem_univ j)
    _ ≤ max 1 (∑ j, ∑ k, u (M j k)) * ⨆ k, u (y k) := by
        gcongr
        exact le_max_right _ _

end Local

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
  {ι κ : Type*} [Finite ι] [Fintype κ]

open scoped Classical in
/-- **The Subspace Theorem on a subspace**: for a subspace `U` of dimension `#κ ≥ 2` and, at
every place of `S`, `#κ` forms linearly independent on `U`, the points `x ≠ 0` of `U` with
`∏_{v ∈ S} (∏_k ‖L_{v,k} x‖_v / ‖x‖_v) ^ mult v ≤ H(x) ^ (-#κ - ε)` lie in finitely many proper
subspaces of `U`. -/
theorem exists_finset_submodule_lt_of_generalProd_le [Nontrivial κ]
    (U : Submodule K (ι → K)) (hU : Fintype.card κ = finrank K U)
    (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwI : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwF : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (L : AbsoluteValue K ℝ → κ → Dual F (ι → F))
    (hLI : ∀ v ∈ Sinf, LinearIndependent F
      fun k (x : U) ↦ L v.1 k fun j ↦ algebraMap K F ((x : ι → K) j))
    (hLF : ∀ v ∈ Sfin, LinearIndependent F
      fun k (x : U) ↦ L v.1 k fun j ↦ algebraMap K F ((x : ι → K) j))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule K (ι → K)), (∀ W ∈ T, W < U) ∧
      ∀ x ∈ U, x ≠ 0 →
        generalProd Sinf Sfin w (fun _ ↦ Finset.univ) L x
          ≤ mulHeight x ^ (-(Fintype.card κ : ℝ) - ε) →
        ∃ W ∈ T, x ∈ W := by
  have := Fintype.ofFinite ι
  -- coordinates on `U`
  let b : Basis κ K U := (Module.finBasis K U).reindex (Fintype.equivFinOfCardEq hU).symm
  set M : Matrix ι κ K := fun j k ↦ (b k : ι → K) j with hMdef
  have hMy : ∀ y : κ → K, M.mulVec y = ((∑ k, y k • b k : U) : ι → K) := by
    intro y
    ext j
    simp [Matrix.mulVec, dotProduct, hMdef, mul_comm]
  have hMU : ∀ y : κ → K, M.mulVec y ∈ U := fun y ↦ by rw [hMy]; exact Submodule.coe_mem _
  have hMrepr : ∀ x : U, M.mulVec (b.repr x) = x := by
    intro x
    rw [hMy]
    congr 1
    simp
  set φ : (κ → K) →ₗ[K] (ι → K) := M.mulVecLin with hφdef
  have hφinj : Function.Injective φ := by
    intro y y' h
    have h' : (∑ k, y k • b k : U) = ∑ k, y' k • b k := by
      apply Subtype.ext
      rw [← hMy, ← hMy]
      exact h
    have := congrArg b.repr h'
    simp only [map_sum, map_smul, Basis.repr_self] at this
    ext k
    simpa [Finsupp.single_apply] using congrFun (congrArg (⇑) this) k
  have hφU : Submodule.map φ ⊤ ≤ U := by
    rintro _ ⟨y, -, rfl⟩
    exact hMU y
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h0 : finrank K (ι → K) = 0 := by simp
    have h1 : 2 ≤ Fintype.card κ := Fintype.one_lt_card
    have h2 := Submodule.finrank_le U
    omega
  -- the forms in coordinates
  set MF : Matrix ι κ F := M.map (algebraMap K F) with hMFdef
  set L' : AbsoluteValue K ℝ → κ → Dual F (κ → F) :=
    fun v k ↦ (L v k).comp MF.mulVecLin with hL'def
  have hL'apply : ∀ v k (y : κ → K),
      L' v k (fun i ↦ algebraMap K F (y i)) = L v k fun j ↦ algebraMap K F (M.mulVec y j) := by
    intro v k y
    simp only [hL'def, LinearMap.comp_apply, Matrix.mulVecLin_apply]
    congr 1
    ext j
    rw [RingHom.map_mulVec]
    rfl
  have hind : ∀ v : AbsoluteValue K ℝ, LinearIndependent F
      (fun k (x : U) ↦ L v k fun j ↦ algebraMap K F ((x : ι → K) j)) →
      LinearIndependent F (L' v) := by
    intro v hv
    let f : Dual F (κ → F) →ₗ[F] (U → F) :=
      { toFun := fun l x ↦ l fun i ↦ algebraMap K F (b.repr x i)
        map_add' := fun l l' ↦ rfl
        map_smul' := fun a l ↦ rfl }
    refine LinearIndependent.of_comp f ?_
    convert hv using 1
    ext k x
    simp only [Function.comp_apply, f, LinearMap.coe_mk, AddHom.coe_mk, hL'apply, hMrepr]
  -- Layer 6.3 in coordinates
  obtain ⟨T', hT'1, hT'2⟩ := exists_finset_submodule_of_approxProd_le_extension Sinf Sfin w hwI
    hwF L' (fun v hv ↦ hind v.1 (hLI v hv)) (fun v hv ↦ hind v.1 (hLF v hv))
    (ε := ε / 2) (by linarith)
  -- the constants
  set cM : AbsoluteValue K ℝ → ℝ := fun u ↦ max 1 (∑ j, ∑ k, u (M j k)) with hcMdef
  have hcM1 : ∀ u, 1 ≤ cM u := fun u ↦ le_max_left _ _
  set d : ℕ := Fintype.card κ with hd
  set Cg : ℝ := (∏ v ∈ Sinf, (cM v.1 ^ d) ^ v.mult) * ∏ v ∈ Sfin, cM v.1 ^ d with hCgdef
  have hCg1 : 1 ≤ Cg := one_le_mul_of_one_le_of_one_le
    (Finset.one_le_prod₀ fun v _ ↦ one_le_pow₀ (one_le_pow₀ (hcM1 _)))
    (Finset.one_le_prod₀ fun v _ ↦ one_le_pow₀ (hcM1 _))
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective φ (LinearMap.ker_eq_bot.2 hφinj)
  set N : Matrix κ ι K := LinearMap.toMatrix' g with hNdef
  have hNM : ∀ y : κ → K, N.mulVec (M.mulVec y) = y := by
    intro y
    rw [hNdef, LinearMap.toMatrix'_mulVec]
    exact congrFun (congrArg (⇑) hg) y
  set CH : ℝ := (Fintype.card ι : ℝ) ^ totalWeight K * Matrix.mulHeight N with hCHdef
  have hCH : ∀ y : κ → K, mulHeight y ≤ CH * mulHeight (M.mulVec y) := by
    intro y
    have := Matrix.mulHeight_mulVec_le N (M.mulVec y)
    rwa [hNM] at this
  have hCHpos : 0 < CH := by
    have h := hCH 0
    have h1 := one_le_mulHeight (0 : κ → K)
    have h2 := one_le_mulHeight (M.mulVec (0 : κ → K))
    by_contra hneg
    have := not_lt.1 hneg
    nlinarith
  set C₁ : ℝ := Cg * CH ^ ((d : ℝ) + ε) with hC₁def
  have hC₁pos : 0 < C₁ := mul_pos (by linarith) (Real.rpow_pos_of_pos hCHpos _)
  -- the solutions of small height, as lines in coordinates
  set Q₀ : ℝ := max 1 (C₁ ^ ((2 : ℝ) / ε)) with hQ₀def
  have hNor : {Q : Projectivization K (κ → K) | Projectivization.mulHeight Q ≤ Q₀}.Finite :=
    Projectivization.finite_setOfPred_mulHeight_le Q₀
  set Tsmall : Finset (Submodule K (κ → K)) :=
    (hNor.image Projectivization.submodule).toFinset with hTsmalldef
  refine ⟨(Tsmall ∪ T').image (Submodule.map φ), ?_, ?_⟩
  · intro W hW
    obtain ⟨W', hW', rfl⟩ := Finset.mem_image.1 hW
    refine lt_of_lt_of_le ?_ hφU
    refine Submodule.map_strictMono_of_injective hφinj (lt_top_iff_ne_top.2 ?_)
    rcases Finset.mem_union.1 hW' with hW' | hW'
    · rw [hTsmalldef, Set.Finite.mem_toFinset] at hW'
      obtain ⟨Q, -, rfl⟩ := hW'
      intro h
      have h1 : finrank K Q.submodule = 1 := by
        rw [Projectivization.submodule_eq]
        exact finrank_span_singleton Q.rep_nonzero
      rw [h] at h1
      have htop : finrank K (⊤ : Submodule K (κ → K)) = Fintype.card κ := by simp [finrank_top]
      have h2 : 2 ≤ Fintype.card κ := Fintype.one_lt_card
      omega
    · exact hT'1 W' hW'
  · intro x hxU hx hbound
    set y : κ → K := ⇑(b.repr ⟨x, hxU⟩) with hydef
    have hxy : M.mulVec y = x := hMrepr ⟨x, hxU⟩
    have hy : y ≠ 0 := by
      rintro h
      apply hx
      rw [← hxy, h, Matrix.mulVec_zero]
    have hmem : ∀ W' : Submodule K (κ → K), y ∈ W' → x ∈ Submodule.map φ W' := fun W' h ↦
      ⟨y, h, by rw [hφdef, Matrix.mulVecLin_apply, hxy]⟩
    rcases le_or_gt (mulHeight y) Q₀ with hsmall | hlarge
    · refine ⟨Submodule.map φ (Projectivization.mk K y hy).submodule,
        Finset.mem_image.2 ⟨_, Finset.mem_union_left _ ?_, rfl⟩, hmem _ ?_⟩
      · rw [hTsmalldef, Set.Finite.mem_toFinset]
        exact ⟨Projectivization.mk K y hy, by
          simpa [Projectivization.mulHeight_mk] using hsmall, rfl⟩
      · rw [Projectivization.submodule_mk]
        exact Submodule.mem_span_singleton_self y
    · -- the local comparison
      have hxpos : ∀ u : AbsoluteValue K ℝ, 0 < ⨆ j, u (x j) := by
        intro u
        obtain ⟨j, hj⟩ := Function.ne_iff.1 hx
        exact lt_of_lt_of_le (u.pos hj)
          (le_ciSup (f := fun j ↦ u (x j)) (Finite.bddAbove_range _) j)
      have hloc : ∀ u : AbsoluteValue K ℝ, (w u).LiesOver u →
          (∏ k, w u (L' u k fun i ↦ algebraMap K F (y i)) / ⨆ i, u (y i))
            ≤ cM u ^ d * ∏ k, w u (L u k fun j ↦ algebraMap K F (x j)) / ⨆ j, u (x j) := by
        intro u _
        have hle : (⨆ j, u (x j)) ≤ cM u * ⨆ i, u (y i) := by
          rw [← hxy]
          exact iSup_mulVec_le u M y
        have hyS : 0 < ⨆ i, u (y i) := by
          have := hxpos u
          nlinarith [hcM1 u, Real.iSup_nonneg fun i ↦ u.nonneg (y i)]
        rw [show cM u ^ d = ∏ _k : κ, cM u by simp [hd], ← Finset.prod_mul_distrib]
        refine Finset.prod_le_prod₀ (fun k _ ↦ div_nonneg (AbsoluteValue.nonneg _ _)
          (Real.iSup_nonneg fun i ↦ u.nonneg _)) fun k _ ↦ ?_
        rw [hL'apply, hxy, mul_div_assoc', div_le_div_iff₀ hyS (hxpos u)]
        have h0 := (w u).nonneg (L u k fun j ↦ algebraMap K F (x j))
        nlinarith
      have hfac : ∀ (v : AbsoluteValue K ℝ) (W : AbsoluteValue F ℝ),
          (0 : ℝ) ≤ ∏ k, W (L v k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) := fun v W ↦
        Finset.prod_nonneg fun k _ ↦ div_nonneg (W.nonneg _) (Real.iSup_nonneg fun j ↦ v.nonneg _)
      have hfac' : ∀ (v : AbsoluteValue K ℝ) (W : AbsoluteValue F ℝ),
          (0 : ℝ) ≤ ∏ k, W (L' v k fun i ↦ algebraMap K F (y i)) / ⨆ i, v (y i) := fun v W ↦
        Finset.prod_nonneg fun k _ ↦ div_nonneg (W.nonneg _) (Real.iSup_nonneg fun i ↦ v.nonneg _)
      have hcmp :
          approxProd Sinf Sfin w L' y ≤ Cg * generalProd Sinf Sfin w (fun _ ↦ univ) L x := by
        have h1 : (∏ v ∈ Sinf, (∏ k, w v.1 (L' v.1 k fun i ↦ algebraMap K F (y i)) /
              ⨆ i, v (y i)) ^ v.mult)
            ≤ (∏ v ∈ Sinf, (cM v.1 ^ d) ^ v.mult) * ∏ v ∈ Sinf,
              (∏ k, w v.1 (L v.1 k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)) ^ v.mult := by
          rw [← Finset.prod_mul_distrib]
          refine Finset.prod_le_prod₀ (fun v _ ↦ pow_nonneg (hfac' _ _) _) fun v hv ↦ ?_
          rw [← mul_pow]
          exact pow_le_pow_left₀ (hfac' _ _) (hloc v.1 (hwI v hv)) _
        have h2 : (∏ v ∈ Sfin, ∏ k, w v.1 (L' v.1 k fun i ↦ algebraMap K F (y i)) /
              ⨆ i, v (y i))
            ≤ (∏ v ∈ Sfin, cM v.1 ^ d) * ∏ v ∈ Sfin,
              ∏ k, w v.1 (L v.1 k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) := by
          rw [← Finset.prod_mul_distrib]
          exact Finset.prod_le_prod₀ (fun v _ ↦ hfac' _ _) fun v hv ↦ hloc v.1 (hwF v hv)
        have hnn : (0 : ℝ) ≤ (∏ v ∈ Sinf, (cM v.1 ^ d) ^ v.mult) * ∏ v ∈ Sinf,
            (∏ k, w v.1 (L v.1 k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)) ^ v.mult :=
          mul_nonneg (Finset.prod_nonneg fun v _ ↦ pow_nonneg (pow_nonneg (by linarith [hcM1 v.1])
            _) _) (Finset.prod_nonneg fun v _ ↦ pow_nonneg (hfac _ _) _)
        rw [approxProd, generalProd, hCgdef]
        calc _ ≤ ((∏ v ∈ Sinf, (cM v.1 ^ d) ^ v.mult) * ∏ v ∈ Sinf,
                (∏ k, w v.1 (L v.1 k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)) ^ v.mult) *
              ((∏ v ∈ Sfin, cM v.1 ^ d) * ∏ v ∈ Sfin,
                ∏ k, w v.1 (L v.1 k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)) :=
            mul_le_mul h1 h2 (Finset.prod_nonneg fun v _ ↦ hfac' _ _) hnn
          _ = _ := by ring
      -- the height comparison
      have hHy : 0 < mulHeight y := lt_of_lt_of_le zero_lt_one (one_le_mulHeight y)
      have hHx : 0 < mulHeight x := lt_of_lt_of_le zero_lt_one (one_le_mulHeight x)
      have hheight : mulHeight x ^ (-(d : ℝ) - ε)
          ≤ CH ^ ((d : ℝ) + ε) * mulHeight y ^ (-(d : ℝ) - ε) := by
        have h := hCH y
        rw [hxy] at h
        have hpos : (0 : ℝ) < (d : ℝ) + ε := by positivity
        have key : mulHeight y ^ ((d : ℝ) + ε)
            ≤ CH ^ ((d : ℝ) + ε) * mulHeight x ^ ((d : ℝ) + ε) := by
          rw [← Real.mul_rpow hCHpos.le hHx.le]
          exact Real.rpow_le_rpow hHy.le h hpos.le
        rw [show (-(d : ℝ) - ε) = -((d : ℝ) + ε) by ring, Real.rpow_neg hHx.le,
          Real.rpow_neg hHy.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hHy _),
          inv_mul_le_iff₀ (Real.rpow_pos_of_pos hHx _)]
        linarith [mul_comm (CH ^ ((d : ℝ) + ε)) (mulHeight x ^ ((d : ℝ) + ε))]
      have hC₁le : C₁ ≤ mulHeight y ^ (ε / 2) := by
        have h1 : C₁ ^ ((2 : ℝ) / ε) ≤ mulHeight y := le_trans (le_max_right _ _) hlarge.le
        have h2 : (C₁ ^ ((2 : ℝ) / ε)) ^ (ε / 2) ≤ mulHeight y ^ (ε / 2) :=
          Real.rpow_le_rpow (Real.rpow_nonneg hC₁pos.le _) h1 (by linarith)
        rwa [← Real.rpow_mul hC₁pos.le, show (2 : ℝ) / ε * (ε / 2) = 1 by field_simp,
          Real.rpow_one] at h2
      have hfinal : approxProd Sinf Sfin w L' y ≤ mulHeight y ^ (-(d : ℝ) - ε / 2) := by
        calc approxProd Sinf Sfin w L' y ≤ Cg * generalProd Sinf Sfin w (fun _ ↦ univ) L x := hcmp
          _ ≤ Cg * (CH ^ ((d : ℝ) + ε) * mulHeight y ^ (-(d : ℝ) - ε)) := by
              gcongr
              exact hbound.trans hheight
          _ = C₁ * mulHeight y ^ (-(d : ℝ) - ε) := by rw [hC₁def]; ring
          _ ≤ mulHeight y ^ (ε / 2) * mulHeight y ^ (-(d : ℝ) - ε) := by
              gcongr
          _ = mulHeight y ^ (-(d : ℝ) - ε / 2) := by
              rw [← Real.rpow_add hHy]
              ring_nf
      obtain ⟨W', hW'T, hW'y⟩ := hT'2 y hy hfinal
      exact ⟨_, Finset.mem_image.2 ⟨W', Finset.mem_union_right _ hW'T, rfl⟩, hmem W' hW'y⟩

end NumberField
