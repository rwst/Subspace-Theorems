/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import CorvajaZannier2004.SubspaceStep

-- Used only inside proofs.
import ArithmeticHeights.Absolute
import ArithmeticHeights.Extension
import ArithmeticHeights.SUnit
import CorvajaZannier2004.LinearRelation
import CorvajaZannier2004.RothMultiples
import CorvajaZannier2004.TwoTermRelation
import DiophantineApproximation.FundamentalInequality

/-!
# Lemma 3 of Corvaja–Zannier: the descent to a smaller subfield

**Lemma 3** (Corvaja–Zannier 2004, p. 4). Let `k ⊆ K ∩ ℝ` be a subfield of degree `d`, `δ ∈ K×`,
`ε > 0`, and let `Σ` be an infinite set of pairs `(q, u) ∈ ℤ × (O_S× ∩ k)` with `|δ q u| > 1`,
`δ q u` not pseudo-Pisot and `0 < ‖δ q u‖ < H(u) ^ (-ε) q ^ (-d - ε)`. Then there are a proper
subfield `k' ⊂ k`, an element `δ' ∈ k×` and an infinite `Σ' ⊆ Σ` with `u / δ' ∈ k'` on `Σ'`.

## Main results

* `NumberField.finite_setOf_absMulHeight₁_le`: along such a family the heights `H(u)` tend to
  infinity ("by Roth's theorem, `u` cannot be fixed").
* `NumberField.exists_ne_zero_infinite_setOf_sum_eq_zero_of_tendsto`: Lemma 1 for families of
  `S`-units whose heights tend to infinity, every `n ≥ 1`.
* `NumberField.exists_lt_infinite_setOf_div_mem`: Lemma 3, with a constant `C` in (2.1).

## Implementation notes

⚠ **The constant `C`.** The Main Theorem descends through subfields by replacing `u` with `δ' v`,
and `H(δ' v) ≥ H(δ')⁻¹ H(v)` costs a constant; carrying it in (2.1) replaces the paper's shrinking
of `ε` in (2.12). Lemma 3 as printed is the case `C = 1`.

⚠ **`δ` real.** The paper's `‖·‖` is the distance of a *real* number to `ℤ`; `δ` is taken real
under `φ`, as it is at every step of the Main Theorem's induction.

## References

P. Corvaja and U. Zannier, Acta Math. **193** (2004), 175–191, Lemma 3.
-/

@[expose] public section

open IsDedekindDomain Height Module

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **Lemma 1 along a family of growing height**, every `n ≥ 1`. If the heights `Hf u` tend to
infinity along `Ξ`, bound the projective height of the points polynomially, and
`w (∑ c i y u i) < max_i w (y u i) · Hf u ^ (-ε)`, then one nonzero relation holds infinitely
often. For `n = 1` the hypothesis bounds `Hf u`, which leaves only finitely many `u`. -/
theorem exists_ne_zero_infinite_setOf_sum_eq_zero_of_tendsto {ι : Type*} [Fintype ι]
    [Nonempty ι] {α : Type*} (S : Finset (HeightOneSpectrum (𝓞 K))) (y : α → ι → Kˣ)
    (c : ι → K) (hc : ∀ i, c i ≠ 0) (w : InfinitePlace K) {ε : ℝ} (hε : 0 < ε) {Ξ : Set α}
    (hΞ : Ξ.Infinite) (hS : ∀ u ∈ Ξ, ∀ i, y u i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K)
    (Hf : α → ℝ) (hHf1 : ∀ u, 1 ≤ Hf u) (hHf : ∀ B : ℝ, {u ∈ Ξ | Hf u ≤ B}.Finite) {N : ℕ}
    (hN : 0 < N) (hmul : ∀ u ∈ Ξ, mulHeight (fun i ↦ (y u i : K)) ≤ Hf u ^ N)
    (h : ∀ u ∈ Ξ, w (∑ i, c i * y u i) < (⨆ i, w (y u i : K)) * Hf u ^ (-ε)) :
    ∃ a : ι → K, a ≠ 0 ∧ {u ∈ Ξ | ∑ i, a i * y u i = 0}.Infinite := by
  classical
  rcases subsingleton_or_nontrivial ι with hι | hι
  · -- `n = 1`: the hypothesis bounds the height
    exfalso
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    have : Unique ι := uniqueOfSubsingleton i₀
    have hc0 : 0 < w (c i₀) := InfinitePlace.pos_iff.mpr (hc i₀)
    refine hΞ ((hHf (w (c i₀) ^ (-ε⁻¹))).subset fun u hu ↦ ⟨hu, ?_⟩)
    have hlt := h u hu
    rw [Fintype.sum_subsingleton _ i₀, ciSup_unique, Subsingleton.elim default i₀, map_mul,
      mul_comm, mul_lt_mul_iff_right₀ (InfinitePlace.pos_iff.mpr (Units.ne_zero _))] at hlt
    have hA : 0 < Hf u := zero_lt_one.trans_le (hHf1 u)
    have h2 := Real.rpow_le_rpow_of_nonpos hc0 hlt.le (neg_nonpos.mpr (inv_pos.mpr hε).le)
    rwa [← Real.rpow_mul hA.le, neg_mul_neg, mul_inv_cancel₀ hε.ne', Real.rpow_one] at h2
  · refine exists_ne_zero_infinite_setOf_sum_eq_zero S y c hc w (ε := ε / N) (by positivity) hΞ
      hS fun u hu ↦ (h u hu).trans_le (mul_le_mul_of_nonneg_left ?_ (Real.iSup_nonneg fun i ↦
        apply_nonneg _ _))
    have hA : 0 < Hf u := zero_lt_one.trans_le (hHf1 u)
    calc Hf u ^ (-ε) = (Hf u ^ N) ^ (-(ε / N)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hA.le]
          congr 1
          field_simp
      _ ≤ _ := Real.rpow_le_rpow_of_nonpos (mulHeight_pos _) (hmul u hu)
          (neg_nonpos.mpr (by positivity))

/-- A complex number which is real under `φ` and algebraic has an algebraic real part. -/
theorem isAlgebraic_re_of_im_eq_zero {z : ℂ} (hz : IsAlgebraic ℚ z) (him : z.im = 0) :
    IsAlgebraic ℚ z.re := by
  have hre : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simp [him])
  rw [← hre] at hz
  exact (isAlgebraic_algHom_iff ((Algebra.ofId ℝ ℂ).restrictScalars ℚ)
    Complex.ofReal_injective).mp hz

/-- **"By Roth's theorem, `u` cannot be fixed"** (Corvaja–Zannier, proof of Lemma 3): along a
family of pairs `(q, u)` with `|δ q u| > 1`, `δ q u` not pseudo-Pisot and
`‖δ q u - m‖ < C H(u) ^ (-ε) |q| ^ (-d - ε)`, `d ≥ 1`, only finitely many pairs have bounded
`H(u)`: finitely many `u` by Northcott, and finitely many `q` for each `u` by Roth. -/
theorem finite_setOf_absMulHeight₁_le (φ : K →+* ℂ) {δ : K} (hδ : (φ δ).im = 0) {C ε : ℝ}
    (hC : 0 < C) (hε : 0 < ε) {d : ℕ} (hd : 1 ≤ d) {Z : Set (ℤ × Kˣ)}
    (hZr : ∀ x ∈ Z, (φ (x.2 : K)).im = 0) (h1 : ∀ x ∈ Z, 1 < ‖φ (δ * x.1 * x.2)‖)
    (hPP : ∀ x ∈ Z, ¬ IsPseudoPisot (φ (δ * x.1 * x.2)).re)
    (happrox : ∀ x ∈ Z, ∃ m : ℤ, ‖(m : ℂ) - φ (δ * x.1 * x.2)‖ <
      C * absMulHeight₁ (x.2 : K) ^ (-ε) * |(x.1 : ℝ)| ^ (-(d : ℝ) - ε)) (B : ℝ) :
    {x ∈ Z | absMulHeight₁ (x.2 : K) ≤ B}.Finite := by
  classical
  -- finitely many `u`
  have hU : {u : Kˣ | mulHeight₁ (u : K) ≤ max B 1 ^ finrank ℚ K}.Finite :=
    (finite_setOfPred_mulHeight₁_le (K := K) _).preimage Units.val_injective.injOn
  refine (hU.biUnion fun u₀ _ ↦ (?_ : {x ∈ Z | x.2 = u₀}.Finite)).subset fun x hx ↦
    Set.mem_biUnion (x := x.2) ?_ ⟨hx.1, rfl⟩
  swap
  · change mulHeight₁ (x.2 : K) ≤ _
    rw [← absMulHeight₁_pow_finrank]
    exact pow_le_pow_left₀ (zero_le_one.trans (one_le_absMulHeight₁ _))
      (hx.2.trans (le_max_left _ _)) _
  -- finitely many `q` for each `u`, by Roth
  rcases Set.eq_empty_or_nonempty {x ∈ Z | x.2 = u₀} with hE | ⟨x₀, hx₀, rfl⟩
  · rw [hE]
    exact Set.finite_empty
  have hu₀r := hZr x₀ hx₀
  have him : (φ (δ * x₀.2)).im = 0 := by rw [map_mul, Complex.mul_im, hδ, hu₀r]; ring
  set α : ℝ := (φ (δ * x₀.2)).re with hα
  have hαC : ((α : ℝ) : ℂ) = φ (δ * x₀.2) :=
    Complex.ext (by simp [hα]) (by rw [Complex.ofReal_im]; exact him.symm)
  have hαalg : IsAlgebraic ℚ α := isAlgebraic_re_of_im_eq_zero
    ((Algebra.IsIntegral.isIntegral (δ * (x₀.2 : K))).isAlgebraic.algHom φ.toRatAlgHom) him
  refine Set.Finite.of_finite_image (f := Prod.fst)
    ((Real.finite_setOf_abs_mul_sub_lt hαalg C hε).subset ?_)
    fun x hx y hy hxy ↦ Prod.ext hxy (hx.2.trans hy.2.symm)
  rintro _ ⟨x, ⟨hx, hxu⟩, rfl⟩
  obtain ⟨m, hm⟩ := happrox x hx
  have hval : φ (δ * x.1 * x.2) = ((α * x.1 : ℝ) : ℂ) := by
    rw [hxu, mul_right_comm, map_mul, ← hαC, map_intCast]
    push_cast
    ring
  have hnorm : ‖(m : ℂ) - φ (δ * x.1 * x.2)‖ = |α * x.1 - m| := by
    rw [hval, ← Complex.ofReal_intCast, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_sub_comm]
  have hq0 : x.1 ≠ 0 := by
    rintro h0
    have := h1 x hx
    simp [h0] at this
    linarith
  have hq1 : (1 : ℝ) ≤ |(x.1 : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hq0
  refine ⟨m, ?_, ?_⟩
  · -- `δ q u` is not an integer, being not pseudo-Pisot of modulus `> 1`
    rcases (abs_nonneg (α * x.1 - m)).lt_or_eq with h | h
    · exact h
    exfalso
    have hint : α * x.1 = m := by linarith [abs_eq_zero.mp h.symm]
    have hre : (φ (δ * x.1 * x.2)).re = ((m : ℚ) : ℝ) := by rw [hval, hint]; simp
    refine hPP x hx ?_
    rw [hre, isPseudoPisot_ratCast_iff]
    refine ⟨?_, m, rfl⟩
    have := h1 x hx
    rw [hval, Complex.norm_real, Real.norm_eq_abs, hint] at this
    exact_mod_cast this
  · rw [← hnorm]
    refine (hm).trans_le ?_
    have hH : absMulHeight₁ (x.2 : K) ^ (-ε) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (one_le_absMulHeight₁ _) (by linarith)
    have hQ : |(x.1 : ℝ)| ^ (-(d : ℝ) - ε) ≤ |(x.1 : ℝ)| ^ (-1 - ε) :=
      Real.rpow_le_rpow_of_exponent_le hq1 (by
        have : (1 : ℝ) ≤ d := by exact_mod_cast hd
        linarith)
    calc C * absMulHeight₁ (x.2 : K) ^ (-ε) * |(x.1 : ℝ)| ^ (-(d : ℝ) - ε)
        ≤ C * 1 * |(x.1 : ℝ)| ^ (-1 - ε) := by gcongr
      _ = C * |(x.1 : ℝ)| ^ (-1 - ε) := by ring

section Galois

variable [IsGalois ℚ K]

/-- Applying an automorphism `τ` to `∑ₑ μ e · e(u)` permutes the conjugates: the result is
`∑ₑ τ (μ (τ⁻¹ ∘ e)) · e(u)`. -/
theorem algEquiv_sum_mul_extAut (k : IntermediateField ℚ K) (τ : K ≃ₐ[ℚ] K)
    (μ : (k →ₐ[ℚ] K) → K) {u : K} (hu : u ∈ k) :
    τ (∑ e, μ e * extAut e u) =
      ∑ e, τ (μ ((algHomCompEquiv k τ).symm e)) * extAut e u := by
  rw [map_sum, ← (algHomCompEquiv k τ).sum_comp
    (fun e' ↦ τ (μ ((algHomCompEquiv k τ).symm e')) * extAut e' u)]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [Equiv.symm_apply_apply, map_mul, extAut_apply _ ⟨u, hu⟩, extAut_apply _ ⟨u, hu⟩,
    algHomCompEquiv_apply]

/-- **The equivariant case of the Claim**: if `μ (τ ∘ e) = τ (μ e)` for all `τ` and `e`, then
`λ = μ id` lies in `k` and `μ e = e(λ)`. -/
theorem mem_and_eq_extAut_of_equivariant {k : IntermediateField ℚ K} {μ : (k →ₐ[ℚ] K) → K}
    (h : ∀ τ e, μ (algHomCompEquiv k τ e) = τ (μ e)) :
    μ k.val ∈ k ∧ ∀ e, μ e = extAut e (μ k.val) := by
  refine ⟨mem_of_forall_algEquiv_apply_eq fun τ hτ ↦ ?_, fun e ↦ ?_⟩
  · have hval : algHomCompEquiv k τ k.val = k.val := AlgHom.ext fun x ↦ by
      simp [hτ x x.2]
    rw [← h, hval]
  · have hval : algHomCompEquiv k (extAut e) k.val = e := AlgHom.ext fun x ↦ by
      simp [extAut_apply]
    rw [← h, hval]

/-- **The subfield of Lemma 3's conclusion**: the elements of `k` on which two embeddings agree,
computed through the chosen extensions to automorphisms. -/
noncomputable def eqField (k : IntermediateField ℚ K) (e₁ e₂ : k →ₐ[ℚ] K) :
    IntermediateField ℚ K where
  carrier := {t | t ∈ k ∧ extAut e₁ t = extAut e₂ t}
  mul_mem' {a b} ha hb := ⟨k.mul_mem ha.1 hb.1, by rw [map_mul, map_mul, ha.2, hb.2]⟩
  add_mem' {a b} ha hb := ⟨k.add_mem ha.1 hb.1, by rw [map_add, map_add, ha.2, hb.2]⟩
  algebraMap_mem' r := ⟨k.algebraMap_mem r, by simp⟩
  inv_mem' a ha := ⟨k.inv_mem ha.1, by rw [map_inv₀, map_inv₀, ha.2]⟩

/-- Two distinct embeddings of `k` agree on a proper subfield. -/
theorem eqField_lt {k : IntermediateField ℚ K} {e₁ e₂ : k →ₐ[ℚ] K} (h : e₁ ≠ e₂) :
    eqField k e₁ e₂ < k := by
  refine lt_of_le_of_ne (fun t ht ↦ ht.1) fun heq ↦ h (AlgHom.ext fun x ↦ ?_)
  have hx : (x : K) ∈ eqField k e₁ e₂ := by rw [heq]; exact x.2
  rw [← extAut_apply, ← extAut_apply]
  exact hx.2

/-- **Both cases of the Claim, after the Galois reduction** (Corvaja–Zannier, p. 6). Suppose that
on an infinite `Z₁ ⊆ Z` the conjugates `e(u)`, `e` ranging over the embeddings with `p e`, satisfy
`q ∑ c e e(u) = m - δ q u` with all `c e ≠ 0`, and that one of them is not too small,
`1 ≤ |q| M |e(u)|`. Then Lemma 1 gives a nonzero relation `∑ₑ b e e(u) = 0` on infinitely many
members of `Z`. -/
theorem exists_ne_zero_infinite_setOf_sum_extAut_eq_zero (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : K →+* ℂ) (k : IntermediateField ℚ K) {δ : K} {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε)
    {Z Z₁ : Set (ℤ × Kˣ)} (hZ₁ : Z₁ ⊆ Z) (hZ₁inf : Z₁.Infinite)
    (hS : ∀ x ∈ Z, ∀ τ : K ≃ₐ[ℚ] K,
      Units.map (τ : K →* K) x.2 ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K)
    (hH : ∀ B : ℝ, {x ∈ Z | absMulHeight₁ (x.2 : K) ≤ B}.Finite) (m : ℤ × Kˣ → ℤ)
    (hm : ∀ x ∈ Z, ‖(m x : ℂ) - φ (δ * x.1 * x.2)‖ <
      C * absMulHeight₁ (x.2 : K) ^ (-ε) * |(x.1 : ℝ)| ^ (-(finrank ℚ k : ℝ) - ε))
    (hq : ∀ x ∈ Z, x.1 ≠ 0) (p : (k →ₐ[ℚ] K) → Prop) [DecidablePred p]
    (c : {e // p e} → K) (hc : ∀ i, c i ≠ 0) {M : ℝ} (hM : 0 < M)
    (hrel : ∀ x ∈ Z₁, (x.1 : K) * ∑ i, c i * extAut i.1 x.2 = m x - δ * x.1 * x.2)
    (hlow : ∀ x ∈ Z₁, ∃ i : {e // p e}, 1 ≤ |(x.1 : ℝ)| * M * ‖φ (extAut i.1 x.2)‖) :
    ∃ b : (k →ₐ[ℚ] K) → K, b ≠ 0 ∧ {x ∈ Z | ∑ e, b e * extAut e x.2 = 0}.Infinite := by
  classical
  obtain ⟨x₀, hx₀⟩ := hZ₁inf.nonempty
  have : Nonempty {e // p e} := ⟨(hlow x₀ hx₀).choose⟩
  set D := finrank ℚ K
  set n := Fintype.card {e // p e}
  have hN : 0 < D * n := Nat.mul_pos finrank_pos Fintype.card_pos
  set B : ℝ := (C * M) ^ (2 / ε)
  set Z₁' := {x ∈ Z₁ | B < absMulHeight₁ (x.2 : K)}
  have hZ₁' : Z₁'.Infinite := fun hfin ↦ hZ₁inf ((hfin.union (hH B)).subset fun x hx ↦ by
    by_cases h : B < absMulHeight₁ (x.2 : K)
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hZ₁ hx, not_lt.mp h⟩)
  have hmul : ∀ x ∈ Z₁', mulHeight (fun i : {e // p e} ↦
      ((Units.map (extAut i.1 : K →* K) x.2 : Kˣ) : K)) ≤ absMulHeight₁ (x.2 : K) ^ (D * n) := by
    intro x hx
    have hx0 : (fun i : {e // p e} ↦ ((Units.map (extAut i.1 : K →* K) x.2 : Kˣ) : K)) ≠ 0 :=
      fun h0 ↦ (Units.map (extAut this.some.1 : K →* K) x.2).ne_zero (congrFun h0 this.some)
    refine (mulHeight_le_prod_mulHeight₁ S hx0 fun i ↦
      Set.mem_integer_of_mem_unit (hS x (hZ₁ hx.1) _)).trans (le_of_eq ?_)
    rw [Finset.prod_congr rfl fun i _ ↦ mulHeight₁_algEquiv (extAut i.1) (x.2 : K),
      Finset.prod_const, Finset.card_univ, ← absMulHeight₁_pow_finrank, ← pow_mul]
  have hsmall : ∀ x ∈ Z₁', InfinitePlace.mk φ (∑ i, c i * extAut i.1 x.2) <
      (⨆ i : {e // p e}, InfinitePlace.mk φ (extAut i.1 x.2)) *
        absMulHeight₁ (x.2 : K) ^ (-(ε / 2)) := by
    intro x hx
    have hxZ := hZ₁ hx.1
    have hq0 := hq x hxZ
    set Q : ℝ := |(x.1 : ℝ)| with hQdef
    have hQ1 : 1 ≤ Q := by rw [hQdef, ← Int.cast_abs]; exact_mod_cast Int.one_le_abs hq0
    have hQ0 : 0 < Q := zero_lt_one.trans_le hQ1
    set H := absMulHeight₁ (x.2 : K) with hHdef
    have hH1 : 1 ≤ H := one_le_absMulHeight₁ _
    have hH0 : 0 < H := zero_lt_one.trans_le hH1
    set sup := ⨆ i : {e // p e}, InfinitePlace.mk φ (extAut i.1 x.2)
    -- the sum is `(m - δ q u) / q`
    have hsum : InfinitePlace.mk φ (∑ i, c i * extAut i.1 x.2) =
        ‖(m x : ℂ) - φ (δ * x.1 * x.2)‖ / Q := by
      have h := congrArg (fun z ↦ ‖φ z‖) (hrel x hx.1)
      simp only [map_mul, map_intCast, norm_mul, Complex.norm_intCast, map_sub] at h
      rw [InfinitePlace.apply, eq_div_iff hQ0.ne', mul_comm, h]
      simp only [map_mul, map_intCast]
    -- one conjugate is not too small
    obtain ⟨i₁, hi₁⟩ := hlow x hx.1
    have hsup : 1 ≤ Q * M * sup := hi₁.trans (mul_le_mul_of_nonneg_left (by
      rw [← InfinitePlace.apply]
      exact le_ciSup (f := fun i : {e // p e} ↦ InfinitePlace.mk φ (extAut i.1 x.2))
        (Finite.bddAbove_range _) i₁) (by positivity))
    have hsup0 : 0 < sup := by
      by_contra h0
      push Not at h0
      nlinarith [mul_nonneg hQ0.le hM.le]
    have hB : C * M ≤ H ^ (ε / 2) := by
      have h := Real.rpow_le_rpow (by positivity) hx.2.le (by positivity : 0 ≤ ε / 2)
      rwa [← Real.rpow_mul (by positivity), div_mul_div_comm, mul_comm 2 ε,
        div_self (by positivity), Real.rpow_one] at h
    have hQle : Q ^ (-(finrank ℚ k : ℝ) - ε) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by
        linarith [(Nat.cast_nonneg (finrank ℚ k) : (0 : ℝ) ≤ _)])
    rw [hsum, div_lt_iff₀ hQ0]
    calc ‖(m x : ℂ) - φ (δ * x.1 * x.2)‖
        < C * H ^ (-ε) * Q ^ (-(finrank ℚ k : ℝ) - ε) := hm x hxZ
      _ ≤ C * H ^ (-ε) * 1 := by gcongr
      _ = (C * M) * H ^ (-(ε / 2)) * H ^ (-(ε / 2)) * M⁻¹ := by
          have hsplit : H ^ (-ε) = H ^ (-(ε / 2)) * H ^ (-(ε / 2)) := by
            rw [← Real.rpow_add hH0]
            ring_nf
          rw [hsplit]
          field_simp
      _ ≤ H ^ (ε / 2) * H ^ (-(ε / 2)) * H ^ (-(ε / 2)) * M⁻¹ := by gcongr
      _ = H ^ (-(ε / 2)) * M⁻¹ := by rw [← Real.rpow_add hH0]; simp
      _ ≤ H ^ (-(ε / 2)) * M⁻¹ * (Q * M * sup) := le_mul_of_one_le_right (by positivity) hsup
      _ = sup * H ^ (-(ε / 2)) * Q := by field_simp
  set y : ℤ × Kˣ → {e // p e} → Kˣ := fun x i ↦ Units.map (extAut i.1 : K →* K) x.2 with hy
  have hyv : ∀ x i, ((y x i : Kˣ) : K) = extAut i.1 x.2 := fun _ _ ↦ rfl
  have hsmall' : ∀ x ∈ Z₁', InfinitePlace.mk φ (∑ i, c i * y x i) <
      (⨆ i, InfinitePlace.mk φ (y x i : K)) * absMulHeight₁ (x.2 : K) ^ (-(ε / 2)) := by
    intro x hx
    simp only [hyv]
    exact hsmall x hx
  have hmul' : ∀ x ∈ Z₁', mulHeight (fun i ↦ (y x i : K)) ≤
      absMulHeight₁ (x.2 : K) ^ (D * n) := hmul
  have hS' : ∀ x ∈ Z₁', ∀ i, y x i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K :=
    fun x hx i ↦ hS x (hZ₁ hx.1) _
  have hHf : ∀ B' : ℝ, {x ∈ Z₁' | absMulHeight₁ (x.2 : K) ≤ B'}.Finite :=
    fun B' ↦ (hH B').subset fun x hx ↦ ⟨hZ₁ hx.1.1, hx.2⟩
  obtain ⟨a', ha'0, ha'⟩ := exists_ne_zero_infinite_setOf_sum_eq_zero_of_tendsto S y c hc
    (InfinitePlace.mk φ) (ε := ε / 2) (by positivity) hZ₁' hS' (fun x ↦ absMulHeight₁ (x.2 : K))
    (fun x ↦ one_le_absMulHeight₁ _) hHf (N := D * n) hN hmul' hsmall'
  refine ⟨fun e ↦ if h : p e then a' ⟨e, h⟩ else 0, fun h0 ↦ ha'0 (funext fun i ↦ ?_),
    ha'.mono fun x hx ↦ ⟨hZ₁ hx.1.1, ?_⟩⟩
  · simpa [i.2] using congrFun h0 i.1
  · rw [← Fintype.sum_subtype_add_sum_subtype p]
    have h2 : ∑ e : {e // ¬ p e}, (fun e ↦ if h : p e then a' ⟨e, h⟩ else 0) e.1 *
        extAut e.1 x.2 = 0 :=
      Finset.sum_eq_zero fun e _ ↦ by simp only [dite_eq_right e.2, zero_mul]
    rw [h2, add_zero, ← hx.2]
    exact Finset.sum_congr rfl fun i _ ↦ by simp only [dite_eq_left i.2, hyv]

/-- `extAut` of the identity embedding fixes `k`. -/
theorem extAut_val_apply {k : IntermediateField ℚ K} {x : K} (hx : x ∈ k) :
    extAut k.val x = x :=
  extAut_apply k.val ⟨x, hx⟩

/-- **Lemma 3 of Corvaja–Zannier** (p. 4), with a constant `C` in (2.1), and with `δ'` one of the
`u` of the family. Let `k` be a subfield of `K`, real under `φ`, `δ ≠ 0` real, and `Z` an infinite
set of pairs `(q, u)`, `u ∈ k` an `S`-unit all of whose conjugates are `S`-units, with
`|δ q u| > 1`, `δ q u` not pseudo-Pisot, and `‖δ q u - m‖ < C H(u) ^ (-ε) |q| ^ (-[k:ℚ] - ε)` for
some `m ∈ ℤ`. Then there are a proper subfield `k' < k` and a member `(q₀, u₀)` of `Z` with
`u / u₀ ∈ k'` for infinitely many members `(q, u)`. -/
theorem exists_lt_exists_mem_infinite_setOf_div_mem (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : K →+* ℂ) (k : IntermediateField ℚ K) (hk : ∀ x ∈ k, (φ x).im = 0) {δ : K}
    (hδ0 : δ ≠ 0) (hδ : (φ δ).im = 0) {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε)
    {Z : Set (ℤ × Kˣ)} (hZ : Z.Infinite) (hZk : ∀ x ∈ Z, (x.2 : K) ∈ k)
    (hS : ∀ x ∈ Z, ∀ τ : K ≃ₐ[ℚ] K,
      Units.map (τ : K →* K) x.2 ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K)
    (h1 : ∀ x ∈ Z, 1 < ‖φ (δ * x.1 * x.2)‖)
    (hPP : ∀ x ∈ Z, ¬ IsPseudoPisot (φ (δ * x.1 * x.2)).re)
    (happrox : ∀ x ∈ Z, ∃ m : ℤ, ‖(m : ℂ) - φ (δ * x.1 * x.2)‖ <
      C * absMulHeight₁ (x.2 : K) ^ (-ε) * |(x.1 : ℝ)| ^ (-(finrank ℚ k : ℝ) - ε)) :
    ∃ k' : IntermediateField ℚ K, k' < k ∧ ∃ x₀ ∈ Z,
      {x ∈ Z | (x.2 : K) / x₀.2 ∈ k'}.Infinite := by
  classical
  have hd1 : 1 ≤ finrank ℚ k := Module.finrank_pos
  have hq : ∀ x ∈ Z, x.1 ≠ 0 := fun x hx h0 ↦ by
    have := h1 x hx
    simp [h0] at this
    linarith
  have hH := finite_setOf_absMulHeight₁_le φ hδ hC hε hd1 (fun x hx ↦ hk _ (hZk x hx)) h1 hPP
    happrox
  choose! m hm using happrox
  -- (2.7): one relation `a₀ m + ∑ₑ aₑ q e(u) = 0`
  obtain ⟨a, ha0, ha⟩ := exists_ne_zero_infinite_setOf_czPoint S φ k δ hC hε hZ hZk hS hq hH m hm
  set Z₁ := {x ∈ Z | ∑ o, a o * czPoint k (m x) x.1 x.2 o = 0} with hZ₁def
  have hZ₁Z : Z₁ ⊆ Z := fun x hx ↦ hx.1
  have hrel₀ : ∀ x ∈ Z₁,
      a none * m x + ∑ e, a (some e) * ((x.1 : K) * extAut e x.2) = 0 := fun x hx ↦ by
    have h := hx.2
    rwa [Fintype.sum_option] at h
  -- the Claim: a relation among the conjugates of `u` alone
  obtain ⟨b, hb0, hb⟩ : ∃ b : (k →ₐ[ℚ] K) → K, b ≠ 0 ∧
      {x ∈ Z | ∑ e, b e * extAut e x.2 = 0}.Infinite := by
    by_cases han : a none = 0
    · refine ⟨fun e ↦ a (some e), fun h0 ↦ ha0 (funext fun o ↦ ?_),
        ha.mono fun x hx ↦ ⟨hx.1, ?_⟩⟩
      · rcases o with _ | e
        · exact han
        · exact congrFun h0 e
      · have h := hrel₀ x hx
        rw [han, zero_mul, zero_add] at h
        have hq0 : (x.1 : K) ≠ 0 := Int.cast_ne_zero.mpr (hq x hx.1)
        have h' : (x.1 : K) * ∑ e, a (some e) * extAut e x.2 = 0 := by
          rw [Finset.mul_sum, ← h]
          exact Finset.sum_congr rfl fun e _ ↦ by ring
        exact (mul_eq_zero.mp h').resolve_left hq0
    set μ : (k →ₐ[ℚ] K) → K := fun e ↦ -a (some e) / a none with hμdef
    have hmμ : ∀ x ∈ Z₁, (m x : K) = x.1 * ∑ e, μ e * extAut e x.2 := fun x hx ↦ by
      have h := hrel₀ x hx
      have hsa : ∑ e, a (some e) * ((x.1 : K) * extAut e x.2) =
          x.1 * ∑ e, a (some e) * extAut e x.2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun e _ ↦ by ring
      have hμs : ∑ e, μ e * extAut e x.2 = -(∑ e, a (some e) * extAut e x.2) / a none := by
        rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun e _ ↦ by simp only [hμdef]; ring
      rw [hsa] at h
      rw [hμs]
      field_simp
      linear_combination h
    have hsumμ : ∀ x ∈ Z₁, ∑ e, μ e * extAut e x.2 = (m x : K) / x.1 := fun x hx ↦ by
      have hq0 : (x.1 : K) ≠ 0 := Int.cast_ne_zero.mpr (hq x hx.1)
      rw [hmμ x hx]
      field_simp
    by_cases hi : ∃ τ e, μ (algHomCompEquiv k τ e) ≠ τ (μ e)
    · -- some conjugate relation is not equivariant: apply `τ` and subtract
      obtain ⟨τ, e₀, hne⟩ := hi
      refine ⟨fun e ↦ μ e - τ (μ ((algHomCompEquiv k τ).symm e)), fun h0 ↦ hne ?_,
        ha.mono fun x hx ↦ ⟨hx.1, ?_⟩⟩
      · have h := congrFun h0 (algHomCompEquiv k τ e₀)
        simpa [sub_eq_zero] using h
      · have hτ := algEquiv_sum_mul_extAut k τ μ (hZk x hx.1)
        simp only [sub_mul, Finset.sum_sub_distrib]
        rw [← hτ, hsumμ x hx, map_div₀, map_intCast, map_intCast, sub_self]
    push Not at hi
    obtain ⟨hlk, hμ⟩ := mem_and_eq_extAut_of_equivariant hi
    set l := μ k.val with hldef
    -- `m = q ∑ₑ e(l) e(u)`, and the identity term is `l u`
    have hsplit : ∀ x ∈ Z₁, ∑ e, μ e * extAut e x.2 =
        l * x.2 + ∑ e ∈ Finset.univ.erase k.val, μ e * extAut e x.2 := fun x hx ↦ by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k.val), extAut_val_apply (hZk x hx.1)]
    by_cases hlδ : l = δ
    · -- first case: `δ ∈ k`, and a conjugate of `q δ u` other than itself is not small
      have hδk : δ ∈ k := hlδ ▸ hlk
      set M : ℝ := 1 + ∑ e : k →ₐ[ℚ] K, ‖φ (extAut e δ)‖ with hMdef
      have hM : 0 < M := by positivity
      have hMe : ∀ e : k →ₐ[ℚ] K, ‖φ (extAut e δ)‖ ≤ M := fun e ↦ by
        have := Finset.single_le_sum (f := fun e : k →ₐ[ℚ] K ↦ ‖φ (extAut e δ)‖)
          (fun e _ ↦ norm_nonneg _) (Finset.mem_univ e)
        rw [hMdef]
        linarith
      refine exists_ne_zero_infinite_setOf_sum_extAut_eq_zero S φ k hC hε hZ₁Z ha hS hH m hm hq
        (fun e ↦ e ≠ k.val) (fun i ↦ extAut i.1 δ) (fun i ↦ (map_ne_zero _).mpr hδ0) hM
        (fun x hx ↦ ?_) (fun x hx ↦ ?_)
      · have hq0 : (x.1 : K) ≠ 0 := Int.cast_ne_zero.mpr (hq x hx.1)
        have hsub : ∑ i : {e // e ≠ k.val}, extAut i.1 δ * extAut i.1 x.2 =
            ∑ e ∈ Finset.univ.erase k.val, μ e * extAut e x.2 := by
          rw [Finset.sum_subtype (Finset.univ.erase k.val) (p := fun e ↦ e ≠ k.val)
            (fun e ↦ by simp) (fun e ↦ μ e * extAut e x.2)]
          exact Finset.sum_congr rfl fun i _ ↦ by rw [hμ, hlδ]
        have h := hsplit x hx
        rw [hsumμ x hx] at h
        rw [hsub, ← hlδ]
        have h' : ∑ e ∈ Finset.univ.erase k.val, μ e * extAut e x.2 =
            (m x : K) / x.1 - l * x.2 := by
          rw [h]; ring
        rw [h']
        field_simp
      · have hu := hZk x hx.1
        have hy : δ * x.1 * x.2 ∈ k := k.mul_mem (k.mul_mem hδk (intCast_mem k x.1)) hu
        have htr : ∑ e : k →ₐ[ℚ] K, e ⟨δ * x.1 * x.2, hy⟩ = m x := by
          rw [hmμ x hx, Finset.mul_sum]
          refine Finset.sum_congr rfl fun e _ ↦ ?_
          rw [← extAut_apply, map_mul, map_mul, map_intCast, hμ, hlδ]
          ring
        obtain ⟨e₁, he₁, hle⟩ := exists_ne_val_one_le_norm φ hy (hk _ hy) (h1 x hx.1)
          (hPP x hx.1) htr
        have hexp : ‖φ (extAut e₁ (δ * x.1 * x.2))‖ =
            ‖φ (extAut e₁ δ)‖ * |(x.1 : ℝ)| * ‖φ (extAut e₁ x.2)‖ := by
          simp only [map_mul, map_intCast, norm_mul, Complex.norm_intCast]
        rw [← extAut_apply, hexp] at hle
        refine ⟨⟨e₁, he₁⟩, hle.trans ?_⟩
        have := hMe e₁
        have hQ : 0 ≤ |(x.1 : ℝ)| := abs_nonneg _
        calc ‖φ (extAut e₁ δ)‖ * |(x.1 : ℝ)| * ‖φ (extAut e₁ x.2)‖
            ≤ M * |(x.1 : ℝ)| * ‖φ (extAut e₁ x.2)‖ := by gcongr
          _ = |(x.1 : ℝ)| * M * ‖φ (extAut e₁ x.2)‖ := by ring
    · -- second case: `λ ≠ δ`, and `u` itself is not small
      have hl0 : l ≠ 0 := by
        intro hl0
        obtain ⟨x, hx, hxH⟩ : ∃ x ∈ Z₁, C ^ (1 / ε) < absMulHeight₁ (x.2 : K) := by
          by_contra hcon
          push Not at hcon
          exact ha ((hH (C ^ (1 / ε))).subset fun x hx ↦ ⟨hx.1, hcon x hx⟩)
        have hm0 : m x = 0 := by
          have h := hmμ x hx
          simp only [hμ, hl0, map_zero, zero_mul, Finset.sum_const_zero, mul_zero] at h
          exact_mod_cast h
        have hlt := hm x hx.1
        rw [hm0, Int.cast_zero, zero_sub, norm_neg] at hlt
        have hH0 : 0 < absMulHeight₁ (x.2 : K) := zero_lt_one.trans_le (one_le_absMulHeight₁ _)
        have hCH : C * absMulHeight₁ (x.2 : K) ^ (-ε) < 1 := by
          have h := Real.rpow_lt_rpow (by positivity) hxH hε
          rw [← Real.rpow_mul hC.le, one_div_mul_cancel hε.ne', Real.rpow_one] at h
          rw [Real.rpow_neg hH0.le, ← div_eq_mul_inv, div_lt_one (by positivity)]
          exact h
        have hq0 := hq x hx.1
        have hQ1 : (1 : ℝ) ≤ |(x.1 : ℝ)| := by
          rw [← Int.cast_abs]
          exact_mod_cast Int.one_le_abs hq0
        have hQle : |(x.1 : ℝ)| ^ (-(finrank ℚ k : ℝ) - ε) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by
            linarith [(Nat.cast_nonneg (finrank ℚ k) : (0 : ℝ) ≤ _)])
        have hle : C * absMulHeight₁ (x.2 : K) ^ (-ε) * |(x.1 : ℝ)| ^ (-(finrank ℚ k : ℝ) - ε) ≤
            C * absMulHeight₁ (x.2 : K) ^ (-ε) :=
          mul_le_of_le_one_right (by positivity) hQle
        linarith [h1 x hx.1]
      refine exists_ne_zero_infinite_setOf_sum_extAut_eq_zero S φ k hC hε hZ₁Z ha hS hH m hm hq
        (fun _ ↦ True) (fun i ↦ extAut i.1 l - if i.1 = k.val then δ else 0) (fun i ↦ ?_)
        (M := ‖φ δ‖) (by simpa using hδ0) (fun x hx ↦ ?_) (fun x hx ↦ ?_)
      · by_cases hi : i.1 = k.val
        · rw [ite_eq_left hi, hi, extAut_val_apply hlk, sub_ne_zero]
          exact hlδ
        · rw [ite_eq_right hi, sub_zero]
          exact (map_ne_zero _).mpr hl0
      · have hq0 : (x.1 : K) ≠ 0 := Int.cast_ne_zero.mpr (hq x hx.1)
        have hsub : ∑ i : {e // True}, (extAut i.1 l - if i.1 = k.val then δ else 0) *
            extAut i.1 x.2 = ∑ e, μ e * extAut e x.2 - δ * x.2 := by
          rw [← Finset.sum_subtype Finset.univ (fun e ↦ by simp)
            (fun e ↦ (extAut e l - if e = k.val then δ else 0) * extAut e x.2)]
          simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
            Finset.mem_univ, ite_true, extAut_val_apply (hZk x hx.1)]
          congr 1
          exact Finset.sum_congr rfl fun e _ ↦ by rw [hμ]
        rw [hsub, hsumμ x hx]
        field_simp
      · refine ⟨⟨k.val, trivial⟩, ?_⟩
        have h := (h1 x hx.1).le
        rw [map_mul, map_mul, norm_mul, norm_mul, map_intCast, Complex.norm_intCast] at h
        rw [extAut_val_apply (hZk x hx.1)]
        linarith [h]
  -- Lemma 2: two conjugates are proportional infinitely often
  set Z₂ := {x ∈ Z | ∑ e, b e * extAut e x.2 = 0} with hZ₂def
  obtain ⟨e₀, he₀⟩ := Function.ne_iff.mp hb0
  have : Nonempty {e // b e ≠ 0} := ⟨⟨e₀, he₀⟩⟩
  have hsum2 : ∀ x ∈ Z₂, ∑ i : {e // b e ≠ 0},
      b i.1 * ((Units.map (extAut i.1 : K →* K) x.2 : Kˣ) : K) = 0 := fun x hx ↦ by
    have h0 : ∑ e : {e // ¬ b e ≠ 0}, b e.1 * extAut e.1 x.2 = 0 :=
      Finset.sum_eq_zero fun e _ ↦ by rw [not_not.mp e.2, zero_mul]
    have h := hx.2
    rw [← Fintype.sum_subtype_add_sum_subtype (fun e ↦ b e ≠ 0)
      (fun e ↦ b e * extAut e x.2), h0, add_zero] at h
    exact h
  obtain ⟨i, j, hij, a', b', ha', hb', hinf⟩ := exists_ne_infinite_setOf_add_eq_zero S
    (fun (i : {e // b e ≠ 0}) (x : ℤ × Kˣ) ↦ Units.map (extAut i.1 : K →* K) x.2)
    (fun i ↦ b i.1) (fun i ↦ i.2) hb (fun x hx i ↦ hS x hx.1 _) hsum2
  -- the ratio of two members is fixed by `τ_j⁻¹ τ_i`, so lies in a proper subfield
  have hr : ∀ y ∈ {x ∈ Z₂ | a' * ((Units.map (extAut i.1 : K →* K) x.2 : Kˣ) : K) +
      b' * ((Units.map (extAut j.1 : K →* K) x.2 : Kˣ) : K) = 0},
      extAut i.1 (y.2 : K) = -b' / a' * extAut j.1 y.2 := fun y hy ↦ by
    have h := hy.2
    change a' * extAut i.1 (y.2 : K) + b' * extAut j.1 (y.2 : K) = 0 at h
    field_simp
    linear_combination h
  obtain ⟨x₀, hx₀⟩ := hinf.nonempty
  refine ⟨eqField k i.1 j.1, eqField_lt fun h ↦ hij (Subtype.ext h), x₀, hx₀.1.1,
    hinf.mono fun x hx ↦ ⟨hx.1.1, ?_⟩⟩
  refine ⟨k.div_mem (hZk x hx.1.1) (hZk x₀ hx₀.1.1), ?_⟩
  have hj0 : extAut j.1 (x₀.2 : K) ≠ 0 := (map_ne_zero _).mpr (Units.ne_zero _)
  have hc : -b' / a' ≠ 0 := div_ne_zero (neg_ne_zero.mpr hb') ha'
  rw [map_div₀, map_div₀, hr x hx, hr x₀ hx₀, mul_div_mul_left _ _ hc]

/-- **Lemma 3 of Corvaja–Zannier** (p. 4), as printed, with a constant `C` in (2.1): there are a
proper subfield `k' < k`, an element `δ' ∈ k×` and infinitely many pairs with `u / δ' ∈ k'`. -/
theorem exists_lt_infinite_setOf_div_mem (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : K →+* ℂ) (k : IntermediateField ℚ K) (hk : ∀ x ∈ k, (φ x).im = 0) {δ : K}
    (hδ0 : δ ≠ 0) (hδ : (φ δ).im = 0) {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε)
    {Z : Set (ℤ × Kˣ)} (hZ : Z.Infinite) (hZk : ∀ x ∈ Z, (x.2 : K) ∈ k)
    (hS : ∀ x ∈ Z, ∀ τ : K ≃ₐ[ℚ] K,
      Units.map (τ : K →* K) x.2 ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K)
    (h1 : ∀ x ∈ Z, 1 < ‖φ (δ * x.1 * x.2)‖)
    (hPP : ∀ x ∈ Z, ¬ IsPseudoPisot (φ (δ * x.1 * x.2)).re)
    (happrox : ∀ x ∈ Z, ∃ m : ℤ, ‖(m : ℂ) - φ (δ * x.1 * x.2)‖ <
      C * absMulHeight₁ (x.2 : K) ^ (-ε) * |(x.1 : ℝ)| ^ (-(finrank ℚ k : ℝ) - ε)) :
    ∃ k' : IntermediateField ℚ K, k' < k ∧ ∃ δ' ∈ k, δ' ≠ 0 ∧
      {x ∈ Z | (x.2 : K) / δ' ∈ k'}.Infinite := by
  obtain ⟨k', hk', x₀, hx₀, hinf⟩ := exists_lt_exists_mem_infinite_setOf_div_mem S φ k hk hδ0
    hδ hC hε hZ hZk hS h1 hPP happrox
  exact ⟨k', hk', x₀.2, hZk x₀ hx₀, Units.ne_zero _, hinf⟩

end Galois

end NumberField
