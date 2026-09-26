/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import CorvajaZannier2004.Conjugates
public import CorvajaZannier2004.GaloisSetting
public import DiophantineApproximation.AffineProd
public import Mathlib.RingTheory.DedekindDomain.SInteger

-- Used only inside proofs.
import ArithmeticHeights.Absolute
import ArithmeticHeights.Extension
import ArithmeticHeights.SUnit
import CorvajaZannier2004.LinearRelation
import DiophantineApproximation.FundamentalInequality
import DiophantineApproximation.PlacesOver
import DiophantineApproximation.SAdicHeight
import DiophantineApproximation.SubspaceAffine

/-!
# The Subspace step in the proof of Lemma 3 of Corvaja–Zannier

Let `u ∈ k` be an `S`-unit all of whose conjugates are `S`-units, `q ∈ ℤ`, and `p ∈ ℤ` close to
`δ q u`. Corvaja and Zannier consider the point

```text
x = (p, q σ₁(u), …, q σ_d(u)) ∈ K^{d+1}
```

(here indexed by `Option (k →ₐ[ℚ] K)`: `none` for `p`, `some e` for `q e(u)`), and at each
archimedean place `v` the forms `x₀ - ρ_v(δ) x_{σ_v}`, `x_σ`; at the finite places of `S`, the
coordinates. The double product is at most `|q| ^ d ‖δ q u‖`, in their normalization, and the
Subspace Theorem puts the points in finitely many hyperplanes (p. 5).

## Main definitions

* `NumberField.extAut`, `NumberField.placeAut`: chosen automorphisms extending an embedding of `k`,
  and presenting an infinite place as `x ↦ ‖φ (τ x)‖`.
* `NumberField.czPoint`: the point `x`.
* `NumberField.czForms`: the forms.

## Main results

* `NumberField.affineProd_czForms_le`: the affine product is at most
  `‖φ (δ q u) - p‖ ^ [K:ℚ] * |q| ^ (d [K:ℚ])`.
* `NumberField.exists_ne_zero_infinite_setOf_czPoint`: along an infinite family satisfying the
  inequality (2.1) with a constant, one nonzero relation `a₀ p + ∑ₑ aₑ q e(u) = 0` holds infinitely
  often. This is (2.7).

## Implementation notes

⚠ **Each archimedean place picks its own conjugate.** With `v x = ‖φ (τ x)‖`, the form at `v` is
`x₀ - τ⁻¹(δ) x_{τ⁻¹|_k}`, whose value at the point is `τ⁻¹ (p - δ q u)`, so `v` of it is
`‖p - φ (δ q u)‖` at every archimedean place. The paper's sets `S_i` and formula (2.4) are not
needed: the product over the archimedean places is `‖p - φ (δ q u)‖ ^ [K:ℚ]` because
`∑ mult v = [K:ℚ]`.

⚠ **The inequality carries a constant `C`.** The Main Theorem's induction replaces `u` by `δ' v`,
and `H(δ' v) ≥ H(δ')⁻¹ H(v)` costs a constant. Rather than shrinking `ε` at each step as the paper
does (2.12), the constant is carried, and this step absorbs it along with the height of the point,
using that only finitely many pairs have bounded `|q| H(u)`.

## References

P. Corvaja and U. Zannier, Acta Math. **193** (2004), 175–191, proof of Lemma 3, (2.5)–(2.7).
-/

@[expose] public section

open IsDedekindDomain Height Module

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]

/-- A chosen automorphism of `K` extending the embedding `e` of `k`. -/
noncomputable def extAut {k : IntermediateField ℚ K} (e : k →ₐ[ℚ] K) : K ≃ₐ[ℚ] K :=
  (exists_algEquiv_apply_eq_of_algHom e).choose

theorem extAut_apply {k : IntermediateField ℚ K} (e : k →ₐ[ℚ] K) (x : k) :
    extAut e x = e x :=
  ((exists_algEquiv_apply_eq_of_algHom e).choose_spec x).symm

/-- A chosen automorphism `τ` with `v x = ‖φ (τ x)‖`. -/
noncomputable def placeAut (φ : K →+* ℂ) (v : InfinitePlace K) : K ≃ₐ[ℚ] K :=
  (InfinitePlace.exists_algEquiv_apply_eq_norm φ v).choose

theorem apply_eq_norm_placeAut (φ : K →+* ℂ) (v : InfinitePlace K) (x : K) :
    v x = ‖φ (placeAut φ v x)‖ :=
  (InfinitePlace.exists_algEquiv_apply_eq_norm φ v).choose_spec x

/-- **The point of Lemma 3**: `p` at `none`, `q e(u)` at `some e`. -/
noncomputable def czPoint (k : IntermediateField ℚ K) (p q : ℤ) (u : K) :
    Option (k →ₐ[ℚ] K) → K :=
  fun o ↦ o.elim (p : K) fun e ↦ (q : K) * extAut e u

/-- The embedding of `k` seen by the infinite place `v`: `τ⁻¹` restricted to `k`. -/
noncomputable def placeEmb (φ : K →+* ℂ) (k : IntermediateField ℚ K) (v : InfinitePlace K) :
    k →ₐ[ℚ] K :=
  ((placeAut φ v).symm : K →ₐ[ℚ] K).comp k.val

open scoped Classical in
/-- **The forms of Lemma 3 at an infinite place `v`**: `x₀ - τ⁻¹(δ) x_{τ⁻¹|_k}` in place of `x₀`,
the coordinates otherwise. -/
noncomputable def czForm (φ : K →+* ℂ) (k : IntermediateField ℚ K) (δ : K) (v : InfinitePlace K) :
    Option (k →ₐ[ℚ] K) → Module.Dual K (Option (k →ₐ[ℚ] K) → K) :=
  Function.update (fun o ↦ LinearMap.proj o) none
    (LinearMap.proj none - (placeAut φ v).symm δ • LinearMap.proj (some (placeEmb φ k v)))

open scoped Classical in
/-- **The forms of Lemma 3**: `czForm` at the infinite places, the coordinates elsewhere. -/
noncomputable def czForms (φ : K →+* ℂ) (k : IntermediateField ℚ K) (δ : K) :
    AbsoluteValue K ℝ → Option (k →ₐ[ℚ] K) → Module.Dual K (Option (k →ₐ[ℚ] K) → K) :=
  fun w ↦ if h : ∃ v : InfinitePlace K, v.1 = w then czForm φ k δ h.choose
    else fun o ↦ LinearMap.proj o

theorem czForms_infinitePlace (φ : K →+* ℂ) (k : IntermediateField ℚ K) (δ : K)
    (v : InfinitePlace K) : czForms φ k δ v.1 = czForm φ k δ v := by
  have h : ∃ v' : InfinitePlace K, v'.1 = v.1 := ⟨v, rfl⟩
  rw [czForms, dite_eq_left h]
  congr
  exact Subtype.ext h.choose_spec

theorem czForms_finitePlace (φ : K →+* ℂ) (k : IntermediateField ℚ K) (δ : K)
    (P : HeightOneSpectrum (𝓞 K)) :
    czForms φ k δ (FinitePlace.mk P).1 = fun o ↦ LinearMap.proj o := by
  have h : ¬ ∃ v : InfinitePlace K, v.1 = (FinitePlace.mk P).1 := fun ⟨v, hv⟩ ↦
    InfinitePlace.val_ne_finitePlace_val v (FinitePlace.mk P) hv
  rw [czForms, dite_eq_right h]

omit [NumberField K] [IsGalois ℚ K] in
/-- The coordinate forms are linearly independent. -/
theorem linearIndependent_coordProj {ι : Type*} [Finite ι] [Nonempty ι] :
    LinearIndependent K (fun i ↦ (LinearMap.proj i : Module.Dual K (ι → K))) := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have h := linearIndependent_update_proj (K := K) (i₀ := i₀) (f := LinearMap.proj i₀) (by simp)
  rwa [Function.update_eq_self] at h

/-- **The forms of Lemma 3 are linearly independent at every place.** -/
theorem linearIndependent_czForms (φ : K →+* ℂ) (k : IntermediateField ℚ K) (δ : K)
    (w : AbsoluteValue K ℝ) : LinearIndependent K (czForms φ k δ w) := by
  classical
  by_cases h : ∃ v : InfinitePlace K, v.1 = w
  · obtain ⟨v, rfl⟩ := h
    rw [czForms_infinitePlace]
    refine linearIndependent_update_proj ?_
    have h1 : (LinearMap.proj none : Module.Dual K (Option (k →ₐ[ℚ] K) → K))
        (Pi.single none 1) = 1 := by simp
    have h2 : (LinearMap.proj (some (placeEmb φ k v)) : Module.Dual K (Option (k →ₐ[ℚ] K) → K))
        (Pi.single none 1) = 0 := by simp
    rw [LinearMap.sub_apply, LinearMap.smul_apply, h1, h2, smul_zero, sub_zero]
    exact one_ne_zero
  · rw [czForms, dite_eq_right h]
    exact linearIndependent_coordProj

/-- **The value of the form at `v` is a conjugate of `p - δ q u`**, so its size at `v` is
`‖p - φ (δ q u)‖`. -/
theorem apply_czForm_none (φ : K →+* ℂ) {k : IntermediateField ℚ K} (δ : K)
    (v : InfinitePlace K) (p q : ℤ) {u : K} (hu : u ∈ k) :
    v (czForm φ k δ v none (czPoint k p q u)) = ‖(p : ℂ) - φ (δ * q * u)‖ := by
  have hext : extAut (placeEmb φ k v) u = (placeAut φ v).symm u :=
    extAut_apply (placeEmb φ k v) ⟨u, hu⟩
  have hval : czForm φ k δ v none (czPoint k p q u) =
      (placeAut φ v).symm ((p : K) - δ * q * u) := by
    simp only [czForm, Function.update_self, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, czPoint, Option.elim_none, Option.elim_some, hext, smul_eq_mul,
      map_sub, map_mul, map_intCast]
    ring
  rw [hval, apply_eq_norm_placeAut, AlgEquiv.apply_symm_apply]
  simp

omit [IsGalois ℚ K] in
/-- An integer has absolute value at most `1` at every finite place. -/
theorem FinitePlace.mk_intCast_le_one (P : HeightOneSpectrum (𝓞 K)) (n : ℤ) :
    FinitePlace.mk P (n : K) ≤ 1 := by
  rw [FinitePlace.mk_apply_le_one_iff]
  have h := P.valuation_le_one (K := K) (n : 𝓞 K)
  convert h using 2
  exact (map_intCast (algebraMap (𝓞 K) K) n).symm

/-- **The affine product of Lemma 3**, formulas (2.5)–(2.6): at the point `(p, q e(u))ₑ` it is
at most `‖p - φ (δ q u)‖ ^ [K:ℚ] |q| ^ (d [K:ℚ])`, `d` the number of embeddings of `k`. Every
conjugate `e(u)` cancels by the product formula; the finite places see `p` and `q` as integers. -/
theorem affineProd_czForms_le (S : Finset (HeightOneSpectrum (𝓞 K))) (φ : K →+* ℂ)
    (k : IntermediateField ℚ K) (δ : K) (p q : ℤ) {u : Kˣ} (hu : (u : K) ∈ k)
    (hS : ∀ τ : K ≃ₐ[ℚ] K, Units.map (τ : K →* K) u ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    affineProd S (fun w ↦ w) (czForms φ k δ) (czPoint k p q u) ≤
      ‖(p : ℂ) - φ (δ * q * u)‖ ^ finrank ℚ K *
        |(q : ℝ)| ^ (Fintype.card (k →ₐ[ℚ] K) * finrank ℚ K) := by
  classical
  set A := ‖(p : ℂ) - φ (δ * q * u)‖
  set y : (k →ₐ[ℚ] K) → Kˣ := fun e ↦ Units.map (extAut e : K →* K) u
  have hy : ∀ e, ((y e : Kˣ) : K) = extAut e u := fun e ↦ rfl
  have hinf : ∀ v : InfinitePlace K,
      ∏ o, v.1 (czForms φ k δ v.1 o fun j ↦ algebraMap K K (czPoint k p q u j)) =
        A * ∏ e, (|(q : ℝ)| * v (y e : K)) := by
    intro v
    simp only [Algebra.algebraMap_self, RingHom.id_apply, czForms_infinitePlace,
      Fintype.prod_option]
    congr 1
    · exact apply_czForm_none φ δ v p q hu
    · refine Finset.prod_congr rfl fun e _ ↦ ?_
      rw [czForm, Function.update_of_ne (Option.some_ne_none e)]
      simp only [LinearMap.proj_apply, czPoint, Option.elim_some, hy]
      rw [show v.1 ((q : K) * extAut e u) = v ((q : K) * extAut e u) from rfl, map_mul,
        InfinitePlace.map_intCast, Int.norm_eq_abs]
  have hfin : ∀ P ∈ S,
      ∏ o, (FinitePlace.mk P).1 (czForms φ k δ (FinitePlace.mk P).1 o
        fun j ↦ algebraMap K K (czPoint k p q u j)) =
        FinitePlace.mk P (p : K) *
          ∏ e, (FinitePlace.mk P (q : K) * FinitePlace.mk P (y e : K)) := by
    intro P _
    simp only [Algebra.algebraMap_self, RingHom.id_apply, czForms_finitePlace,
      Fintype.prod_option, LinearMap.proj_apply, czPoint, Option.elim_none, Option.elim_some,
      hy]
    rw [Finset.prod_congr rfl fun e _ ↦ (FinitePlace.mk P).1.map_mul _ _]
    rfl
  unfold affineProd
  rw [Finset.prod_congr rfl fun v _ ↦ by rw [hinf v], Finset.prod_congr rfl hfin]
  -- separate the three kinds of factor
  have hsplit : (∏ v : InfinitePlace K, (A * ∏ e, (|(q : ℝ)| * v (y e : K))) ^ v.mult) *
      ∏ P ∈ S, (FinitePlace.mk P (p : K) *
        ∏ e, (FinitePlace.mk P (q : K) * FinitePlace.mk P (y e : K))) =
      (A ^ finrank ℚ K * |(q : ℝ)| ^ (Fintype.card (k →ₐ[ℚ] K) * finrank ℚ K)) *
        ((∏ P ∈ S, FinitePlace.mk P (p : K)) *
          (∏ P ∈ S, FinitePlace.mk P (q : K)) ^ Fintype.card (k →ₐ[ℚ] K)) *
        ∏ e, ((∏ v : InfinitePlace K, v (y e : K) ^ v.mult) *
          ∏ P ∈ S, FinitePlace.mk P (y e : K)) := by
    simp only [Finset.prod_mul_distrib, mul_pow, ← Finset.prod_pow, Finset.prod_const,
      Finset.card_univ]
    rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq, Finset.prod_comm (s := S),
      Finset.prod_comm (s := Finset.univ) (t := Finset.univ)]
    simp only [← pow_mul, Finset.prod_pow_eq_pow_sum]
    rw [← Finset.mul_sum, InfinitePlace.sum_mult_eq]
    ring
  rw [hsplit, Finset.prod_congr rfl fun e _ ↦ prod_apply_eq_one_of_mem_unit S (hS (extAut e)),
    Finset.prod_const_one, mul_one]
  have hp1 : ∏ P ∈ S, FinitePlace.mk P (p : K) ≤ 1 :=
    Finset.prod_le_one₀ (fun P _ ↦ apply_nonneg _ _) fun P _ ↦ FinitePlace.mk_intCast_le_one P p
  have hq1 : (∏ P ∈ S, FinitePlace.mk P (q : K)) ^ Fintype.card (k →ₐ[ℚ] K) ≤ 1 :=
    pow_le_one₀ (Finset.prod_nonneg fun P _ ↦ apply_nonneg _ _)
      (Finset.prod_le_one₀ (fun P _ ↦ apply_nonneg _ _) fun P _ ↦
        FinitePlace.mk_intCast_le_one P q)
  refine mul_le_of_le_one_right (by positivity) ?_
  calc (∏ P ∈ S, FinitePlace.mk P (p : K)) *
        (∏ P ∈ S, FinitePlace.mk P (q : K)) ^ Fintype.card (k →ₐ[ℚ] K)
      ≤ 1 * 1 := mul_le_mul hp1 hq1 (by positivity) zero_le_one
    _ = 1 := one_mul 1

omit [IsGalois ℚ K] in
/-- The height of an element is invariant under automorphisms. -/
theorem mulHeight₁_algEquiv (τ : K ≃ₐ[ℚ] K) (x : K) : mulHeight₁ (τ x) = mulHeight₁ x := by
  rw [← absMulHeight₁_pow_finrank, ← absMulHeight₁_pow_finrank]
  exact congrArg (· ^ finrank ℚ K) (absMulHeight₁_comp (τ : K →ₐ[ℚ] K) x)

omit [IsGalois ℚ K] in
/-- The height of a rational integer in `K` is `max |n| 1 ^ [K:ℚ]`. -/
theorem mulHeight₁_intCast (n : ℤ) :
    mulHeight₁ (n : K) = max |(n : ℝ)| 1 ^ finrank ℚ K := by
  have h := mulHeight₁_pow_finrank (K := ℚ) (L := K) (n : ℚ)
  rw [map_intCast] at h
  rw [← h, Rat.mulHeight₁_eq_max]
  congr 1
  simp only [Rat.num_intCast, Rat.den_intCast, Nat.cast_max, Nat.cast_natAbs, Int.cast_abs,
    Nat.cast_one]

/-- The point of Lemma 3 is not zero: its coordinate at the identity embedding is `q u ≠ 0`. -/
theorem czPoint_ne_zero (k : IntermediateField ℚ K) (p : ℤ) {q : ℤ} (hq : q ≠ 0) {u : K}
    (hu : u ≠ 0) : czPoint k p q u ≠ 0 := fun h ↦ by
  have := congrFun h (some k.val)
  simp only [czPoint, Option.elim_some, Pi.zero_apply, mul_eq_zero, Int.cast_eq_zero, hq,
    false_or] at this
  exact (map_ne_zero _).mpr hu this

/-- The coordinates of the point of Lemma 3 are `S`-integers. -/
theorem czPoint_mem_integer {S : Finset (HeightOneSpectrum (𝓞 K))}
    (k : IntermediateField ℚ K) (p q : ℤ) {u : Kˣ}
    (hS : ∀ τ : K ≃ₐ[ℚ] K, Units.map (τ : K →* K) u ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K)
    (o : Option (k →ₐ[ℚ] K)) :
    czPoint k p q u o ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K := by
  rcases o with _ | e
  · exact (Set.integer _ K).intCast_mem p
  · exact (Set.integer _ K).mul_mem ((Set.integer _ K).intCast_mem q)
      (Set.mem_integer_of_mem_unit (hS (extAut e)))

/-- **The height of the point of Lemma 3**: at most `max |p| 1 ^ [K:ℚ] (|q| ^ [K:ℚ] H_K(u)) ^ d`. -/
theorem mulHeight_czPoint_le (S : Finset (HeightOneSpectrum (𝓞 K)))
    (k : IntermediateField ℚ K) (p q : ℤ) {u : Kˣ} (hq : q ≠ 0)
    (hS : ∀ τ : K ≃ₐ[ℚ] K, Units.map (τ : K →* K) u ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    mulHeight (czPoint k p q u) ≤ max |(p : ℝ)| 1 ^ finrank ℚ K *
      (|(q : ℝ)| ^ finrank ℚ K * mulHeight₁ (u : K)) ^ Fintype.card (k →ₐ[ℚ] K) := by
  classical
  have hx0 := czPoint_ne_zero k p hq u.ne_zero
  have hint : ∀ o, _ := fun o ↦ czPoint_mem_integer (S := S) k p q hS o
  refine (mulHeight_le_prod_mulHeight₁ S hx0 hint).trans ?_
  rw [Fintype.prod_option]
  refine mul_le_mul (by simp [czPoint, mulHeight₁_intCast]) ?_
    (Finset.prod_nonneg fun _ _ ↦ mulHeight₁_nonneg _) (by positivity)
  rw [← Finset.card_univ, ← Finset.prod_const]
  refine Finset.prod_le_prod₀ (fun _ _ ↦ mulHeight₁_nonneg _) fun e _ ↦ ?_
  simp only [czPoint, Option.elim_some]
  refine (mulHeight₁_mul_le _ _).trans ?_
  rw [mulHeight₁_intCast, mulHeight₁_algEquiv, max_eq_left (by exact_mod_cast Int.one_le_abs hq)]

/-- **The numerics of the Subspace step.** With `R = Q H`, the affine bound
`E ^ D Q ^ (d D)` with `E Q ^ d < C R ^ (-ε)` beats `M ^ (-ε')`, `M ≤ B ^ D R ^ N`,
`ε' = ε D / (2 N)`, as soon as `R` exceeds a threshold depending on `B`, `C` and the exponents. -/
theorem exists_forall_pow_le_rpow {C B ε : ℝ} (hC : 0 < C) (hB : 1 ≤ B) (hε : 0 < ε)
    {D N : ℕ} (hD : 0 < D) (hN : 0 < N) :
    ∃ R₀ : ℝ, ∀ {E R M : ℝ}, 0 ≤ E → R₀ ≤ R → 1 ≤ R → 0 < M → E < C * R ^ (-ε) →
      M ≤ B ^ D * R ^ N → E ^ D ≤ M ^ (-(ε * D / (2 * N))) := by
  set ε' : ℝ := ε * D / (2 * N) with hε'
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hε'pos : 0 < ε' := by positivity
  refine ⟨(C ^ D * (B ^ D) ^ ε') ^ (2 / (ε * D)), fun {E R M} hE hR₀ hR1 hM hEC hMB ↦ ?_⟩
  have hR : 0 < R := zero_lt_one.trans_le hR1
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  -- `E ^ D ≤ C ^ D R ^ (-ε D)`
  have h1 : E ^ D ≤ C ^ D * R ^ (-(ε * D)) := by
    calc E ^ D ≤ (C * R ^ (-ε)) ^ D := pow_le_pow_left₀ hE hEC.le D
      _ = C ^ D * R ^ (-(ε * D)) := by
          rw [mul_pow, ← Real.rpow_natCast (R ^ (-ε)), ← Real.rpow_mul hR.le, neg_mul]
  -- `C ^ D (B ^ D) ^ ε' ≤ R ^ (ε D / 2)`
  have h2 : C ^ D * (B ^ D) ^ ε' ≤ R ^ (ε * D / 2) := by
    have := Real.rpow_le_rpow (by positivity) hR₀ (by positivity : 0 ≤ ε * D / 2)
    rwa [← Real.rpow_mul (by positivity), div_mul_div_comm, mul_comm (2 : ℝ),
      div_self (by positivity), Real.rpow_one] at this
  -- `(B ^ D R ^ N) ^ (-ε') ≤ M ^ (-ε')`
  have h3 : (B ^ D * R ^ N) ^ (-ε') ≤ M ^ (-ε') :=
    Real.rpow_le_rpow_of_nonpos hM hMB (by linarith)
  have h4 : (B ^ D * R ^ N) ^ (-ε') = ((B ^ D) ^ ε')⁻¹ * R ^ (-(ε * D / 2)) := by
    rw [Real.mul_rpow (by positivity) (by positivity), Real.rpow_neg (by positivity),
      ← Real.rpow_natCast R N, ← Real.rpow_mul hR.le]
    congr 2
    rw [hε']
    field_simp
  refine h1.trans (le_trans ?_ (h4 ▸ h3))
  have hRpos : 0 < R ^ (ε * D / 2) := Real.rpow_pos_of_pos hR _
  have hBpos : 0 < (B ^ D) ^ ε' := by positivity
  rw [show -(ε * D) = -(ε * D / 2) - ε * D / 2 by ring, Real.rpow_sub hR,
    Real.rpow_neg hR.le]
  rw [le_inv_mul_iff₀ hBpos]
  calc (B ^ D) ^ ε' * (C ^ D * ((R ^ (ε * D / 2))⁻¹ / R ^ (ε * D / 2)))
      = (C ^ D * (B ^ D) ^ ε') * (R ^ (ε * D / 2))⁻¹ * (R ^ (ε * D / 2))⁻¹ := by ring
    _ ≤ R ^ (ε * D / 2) * (R ^ (ε * D / 2))⁻¹ * (R ^ (ε * D / 2))⁻¹ := by gcongr
    _ = (R ^ (ε * D / 2))⁻¹ := by field_simp

/-- **The Subspace step of Lemma 3**, formula (2.7). Along an infinite family `Z` of pairs
`(q, u)`, with `u ∈ k` an `S`-unit all of whose conjugates are `S`-units, heights `H(u)` tending to
infinity along `Z`, and integers `m (q, u)` with `‖m - δ q u‖ < C H(u) ^ (-ε) |q| ^ (-[k:ℚ] - ε)`,
one nonzero linear relation `a₀ m + ∑ₑ aₑ q e(u) = 0` holds for infinitely many members of `Z`. -/
theorem exists_ne_zero_infinite_setOf_czPoint (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : K →+* ℂ) (k : IntermediateField ℚ K) (δ : K) {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε)
    {Z : Set (ℤ × Kˣ)} (hZ : Z.Infinite) (hk : ∀ x ∈ Z, (x.2 : K) ∈ k)
    (hS : ∀ x ∈ Z, ∀ τ : K ≃ₐ[ℚ] K,
      Units.map (τ : K →* K) x.2 ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K)
    (hq : ∀ x ∈ Z, x.1 ≠ 0) (hH : ∀ B : ℝ, {x ∈ Z | absMulHeight₁ (x.2 : K) ≤ B}.Finite)
    (m : ℤ × Kˣ → ℤ)
    (hm : ∀ x ∈ Z, ‖(m x : ℂ) - φ (δ * x.1 * x.2)‖ <
      C * absMulHeight₁ (x.2 : K) ^ (-ε) * |(x.1 : ℝ)| ^ (-(finrank ℚ k : ℝ) - ε)) :
    ∃ a : Option (k →ₐ[ℚ] K) → K, a ≠ 0 ∧
      {x ∈ Z | ∑ o, a o * czPoint k (m x) x.1 x.2 o = 0}.Infinite := by
  classical
  set D := finrank ℚ K with hDdef
  set d := Fintype.card (k →ₐ[ℚ] K) with hddef
  have hd : d = finrank ℚ k := AlgHom.card_of_splits ℚ k K fun z ↦ by
    rw [← minpoly.algHom_eq k.val Subtype.val_injective z]
    exact Normal.splits IsGalois.to_normal (z : K)
  have hD : 0 < D := finrank_pos
  set N := D * (D + d) with hNdef
  have hN : 0 < N := Nat.mul_pos hD (by omega)
  set B : ℝ := ‖φ δ‖ + C + 1 with hBdef
  have hB : 1 ≤ B := by rw [hBdef]; linarith [norm_nonneg (φ δ)]
  obtain ⟨R₀, hR₀⟩ := exists_forall_pow_le_rpow hC hB hε hD hN
  have : Nonempty (k →ₐ[ℚ] K) := ⟨k.val⟩
  obtain ⟨T, hT, hcovT⟩ := exists_finset_submodule_of_integer_of_affineProd_le S (fun w ↦ w)
    (fun _ ↦ ⟨AbsoluteValue.ext fun _ ↦ rfl⟩) (fun _ _ ↦ ⟨AbsoluteValue.ext fun _ ↦ rfl⟩)
    (czForms φ k δ) (fun v ↦ linearIndependent_czForms φ k δ v.1)
    (fun _ _ ↦ linearIndependent_czForms φ k δ _) (ε := ε * D / (2 * N)) (by positivity)
  -- every member of large height lies in one of the subspaces
  have hkey : ∀ x ∈ Z, max R₀ 1 < absMulHeight₁ (x.2 : K) →
      ∃ W ∈ T, czPoint k (m x) x.1 x.2 ∈ W := by
    intro x hx hHx
    have hq0 := hq x hx
    set Q : ℝ := |(x.1 : ℝ)| with hQdef
    have hQ1 : 1 ≤ Q := by rw [hQdef, ← Int.cast_abs]; exact_mod_cast Int.one_le_abs hq0
    have hQ0 : 0 < Q := zero_lt_one.trans_le hQ1
    set H := absMulHeight₁ (x.2 : K) with hHdef
    have hH1 : 1 ≤ H := one_le_absMulHeight₁ _
    set E := ‖(m x : ℂ) - φ (δ * x.1 * x.2)‖ with hEdef
    set R := Q * H with hRdef
    have hR1 : 1 ≤ R := one_le_mul_of_one_le_of_one_le hQ1 hH1
    have hRR₀ : R₀ ≤ R := ((le_max_left _ _).trans hHx.le).trans (le_mul_of_one_le_left
      (zero_le_one.trans hH1) hQ1)
    refine hcovT _ (czPoint_ne_zero k _ hq0 x.2.ne_zero)
      (czPoint_mem_integer k _ _ (hS x hx)) ?_
    -- `E |q| ^ d < C R ^ (-ε)`
    have hEq : E * Q ^ d < C * R ^ (-ε) := by
      have h := hm x hx
      rw [← hd] at h
      calc E * Q ^ d < C * H ^ (-ε) * Q ^ (-(d : ℝ) - ε) * Q ^ d :=
            mul_lt_mul_of_pos_right h (pow_pos hQ0 d)
        _ = C * R ^ (-ε) := by
            rw [hRdef, Real.mul_rpow hQ0.le (zero_lt_one.trans_le hH1).le, ← Real.rpow_natCast,
              mul_assoc, mul_assoc, ← Real.rpow_add hQ0]
            ring_nf
    -- the height of the point
    have hEC : E ≤ C := by
      refine (hm x hx).le.trans ?_
      calc C * H ^ (-ε) * Q ^ (-(finrank ℚ k : ℝ) - ε) ≤ C * 1 * 1 := by
            gcongr
            · exact Real.rpow_le_one_of_one_le_of_nonpos hH1 (by linarith)
            · exact Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith [
                (Nat.cast_nonneg (finrank ℚ k) : (0 : ℝ) ≤ _)])
        _ = C := by ring
    have hu : ‖φ (x.2 : K)‖ ≤ H ^ D := by
      rw [absMulHeight₁_pow_finrank, ← InfinitePlace.apply]
      exact (le_max_left _ _).trans (InfinitePlace.max_apply_one_le_mulHeight₁ _ _)
    have hm_le : max |((m x : ℤ) : ℝ)| 1 ≤ B * R ^ D := by
      have hQH : Q * H ^ D ≤ R ^ D := by
        rw [hRdef, mul_pow]
        exact mul_le_mul_of_nonneg_right (le_self_pow₀ hQ1 hD.ne') (by positivity)
      have h1 : 1 ≤ Q * H ^ D := one_le_mul_of_one_le_of_one_le hQ1 (one_le_pow₀ hH1)
      have habs : |((m x : ℤ) : ℝ)| ≤ ‖φ δ‖ * (Q * H ^ D) + C := by
        have htri : ‖((m x : ℤ) : ℂ)‖ ≤ ‖φ (δ * x.1 * x.2)‖ + E := by
          have := norm_add_le (φ (δ * x.1 * x.2)) ((m x : ℂ) - φ (δ * x.1 * x.2))
          rwa [add_sub_cancel] at this
        rw [Complex.norm_intCast] at htri
        have hφ : ‖φ (δ * x.1 * x.2)‖ = ‖φ δ‖ * Q * ‖φ (x.2 : K)‖ := by
          rw [map_mul, map_mul, norm_mul, norm_mul, map_intCast, Complex.norm_intCast]
        rw [hφ] at htri
        have := mul_le_mul_of_nonneg_left hu (mul_nonneg (norm_nonneg (φ δ)) hQ0.le)
        nlinarith
      refine max_le ?_ ?_
      · calc |((m x : ℤ) : ℝ)| ≤ ‖φ δ‖ * (Q * H ^ D) + C * (Q * H ^ D) := by nlinarith
          _ ≤ B * (Q * H ^ D) := by rw [hBdef]; nlinarith
          _ ≤ B * R ^ D := mul_le_mul_of_nonneg_left hQH (by linarith)
      · calc (1 : ℝ) ≤ 1 * 1 := by norm_num
          _ ≤ B * R ^ D := mul_le_mul hB (one_le_pow₀ hR1) zero_le_one (by linarith)
    have hMH : mulHeight (czPoint k (m x) x.1 x.2) ≤ B ^ D * R ^ N := by
      refine (mulHeight_czPoint_le S k (m x) x.1 hq0 (hS x hx)).trans ?_
      rw [← absMulHeight₁_pow_finrank, ← hHdef]
      calc max |((m x : ℤ) : ℝ)| 1 ^ D * (Q ^ D * H ^ D) ^ d
          ≤ (B * R ^ D) ^ D * (Q ^ D * H ^ D) ^ d := by
            gcongr
        _ = B ^ D * R ^ N := by
            rw [hNdef, ← mul_pow, ← hRdef, mul_pow, ← pow_mul, ← pow_mul, mul_assoc, ← pow_add,
              mul_add]
    have haff := affineProd_czForms_le S φ k δ (m x) x.1 (hk x hx) (hS x hx)
    calc affineProd S (fun w ↦ w) (czForms φ k δ) (czPoint k (m x) x.1 x.2)
        ≤ E ^ D * Q ^ (d * D) := haff
      _ = (E * Q ^ d) ^ D := by rw [mul_pow, ← pow_mul]
      _ ≤ _ := hR₀ (by positivity) hRR₀ hR1 (mulHeight_pos _) hEq hMH
  -- one subspace carries infinitely many points
  set Z' := {x ∈ Z | max R₀ 1 < absMulHeight₁ (x.2 : K)} with hZ'
  have hZ'inf : Z'.Infinite := fun hfin ↦ hZ ((hfin.union (hH (max R₀ 1))).subset fun x hx ↦ by
    by_cases h : max R₀ 1 < absMulHeight₁ (x.2 : K)
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, not_lt.mp h⟩)
  obtain ⟨W, hWT, hWinf⟩ : ∃ W ∈ T, {x ∈ Z' | czPoint k (m x) x.1 x.2 ∈ W}.Infinite := by
    by_contra hne
    push Not at hne
    refine hZ'inf ((T.finite_toSet.biUnion fun W hW ↦ hne W hW).subset fun x hx ↦ ?_)
    obtain ⟨W, hW, hxW⟩ := hkey x hx.1 hx.2
    exact Set.mem_biUnion hW ⟨hx, hxW⟩
  obtain ⟨a, ha0, ha⟩ := exists_ne_zero_forall_mem_sum_eq_zero (hT W hWT)
  exact ⟨a, ha0, hWinf.mono fun x hx ↦ ⟨hx.1.1, ha _ hx.2⟩⟩

end NumberField
