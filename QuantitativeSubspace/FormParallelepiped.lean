/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.WedgeDomainAt
public import QuantitativeSubspace.FormSuccessiveInfima
import ArithmeticHeights.Extension
import Mathlib.Algebra.FiniteSupport.Basic

/-!
# Scaling into a parallelepiped

A point of height below a product of local budgets has a nonzero multiple, over a finite
extension, that satisfies the budgets place by place. This is ES02 Lemma 6.2 / 7.3 and EF13
Lemma 11.2, and it rests on ES02 Lemma 6.3 = EF13 Lemma 11.1: positive reals `A_u`, `1` almost
everywhere, with product `> 1`, are local bounds for some `α` in an extension.

ES02 prove Lemma 6.3 with the `S`-unit theorem: an `S`-unit `g` whose logarithmic embedding is
within a constant of `k (log A_u - (1/t) log A)`, and `α = g^{1/k}`. Here Minkowski's theorem for
one scalar replaces the `S`-units (`exists_ne_zero_le_of_mul_le`, Layer 4.1's approximation domain
for the coordinate form on `K¹` with finite places): `g ∈ K` with `|g|_u ≤ A_u ^ k` exists as soon
as `(∏ A_u) ^ k` beats `2 ^ [K:ℚ] √|D_K|` times the norms of the finite places where `A_u ≠ 1`,
which pay for rounding `A_u ^ k` to a value of `u`. The `k`-th root then lands in `E = K(g^{1/k})`
with `|α|_w ≤ A_u ^ {d(w|u)}` (`le_of_pow_eq_algebraMap`).

For points the budgets are divided by the local factors of `x` over `F = K(x)`; the product of
the quotients is the budget product over the height, `> 1`, and Lemma 6.3 over `F` gives the
scalar. Normalizations are Mathlib's relative ones (`FormHeight.lean`): at an infinite place `w`
of `E` above `v` the local factor `max_i |L_i(y)|_w / a_iv` is compared with `ρa_v`, at a finite
place `w` above `v` the factor `max_i |L_i(y)|_w / a_iv ^ {e f}` with `ρf_v ^ {e f}`, `e f` the
local degree; EF13's `‖·‖_w ≤ ‖ρ‖_v ^ {d(w|v)}` in the absolute normalization.

## Main results

* `NumberField.exists_ne_zero_le_of_mul_le`: Minkowski's first theorem for one scalar with finite
  places.
* `NumberField.exists_pow_le_of_one_lt`, `NumberField.exists_le_of_one_lt`: ES02 Lemma 6.3 =
  EF13 Lemma 11.1 (`g ∈ K` with `k`-th power bounds; `α` in an extension `E ⊆ Ω`).
* `NumberField.FormSystem.LocallyLe`: local bounds for a point over a finite extension;
  `mulHeight_le_of_locallyLe`, `absMulHeight_le_of_locallyLe`: they bound the height.
* `NumberField.FormSystem.exists_locallyLe_smul`: ES02 Lemma 6.2 / 7.3, general budgets, for
  finitely many points at once in one extension.
* `NumberField.FormSystem.exists_smul_le_of_lt`: EF13 Lemma 11.2, (11.3) and (11.4), with
  `n^{-1}` at the infinite places and `(n μ_j) ^ {d(w|v₀)}` above `v₀`.
* `NumberField.FormSystem.paraSet`, `paraSpace`, `paraInf`: ES02's `μ ∗ Π(A)` (scaled at a finite
  place `v₀`), `U_A(μ)` and the successive minima of `Π`; `exists_smul_mem_paraSet` (ES02
  Lemma 7.3) and `paraInf_eq_successiveInf` (ES02 Cor. 7.4).

## References

J.-H. Evertse and H. P. Schlickewei, "A quantitative version of the absolute subspace theorem",
*J. reine angew. Math.* **548** (2002), 21–127, Lemmas 6.2, 6.3, 7.3 and Cor. 7.4.

J.-H. Evertse and R. G. Ferretti, "A further improvement of the Quantitative Subspace Theorem",
*Ann. of Math.* **177** (2013), 513–590, Lemmas 11.1 and 11.2.

This is milestone Q2.4d of `QuantitativeSubspace/README.md`.
-/

@[expose] public section

open Finset Function Module

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-! ### Minkowski's theorem for one scalar, with finite places -/

/-- **Minkowski's first theorem for one scalar, with finite places.** If the product of positive
bounds `B w` at the infinite places and `C v` at the places of `Sfin` is at least
`unitConst K · ∏_{v ∈ Sfin} N(𝔭_v)`, some nonzero `β ∈ K` has `|β|_w ^ mult w ≤ B w` at every
infinite place, `|β|_v ≤ C v` on `Sfin` and `|β|_v ≤ 1` at the other finite places. The norms
pay for rounding the `C v` to values of `v`. -/
theorem exists_ne_zero_le_of_mul_le (Sfin : Finset (FinitePlace K)) {B : InfinitePlace K → ℝ}
    {C : FinitePlace K → ℝ} (hB : ∀ w, 0 < B w) (hC : ∀ v, 0 < C v)
    (h : unitConst K * ∏ v ∈ Sfin, (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) ≤
      (∏ w, B w) * ∏ v ∈ Sfin, C v) :
    ∃ β : K, β ≠ 0 ∧ (∀ v ∈ Sfin, v β ≤ C v) ∧ (∀ v ∉ Sfin, v β ≤ 1) ∧
      ∀ w : InfinitePlace K, w β ^ w.mult ≤ B w := by
  classical
  set L₀ : AbsoluteValue K ℝ → Unit → Dual K (Unit → K) := fun _ _ ↦ LinearMap.proj ()
    with hL₀
  have hdisj : ∀ v : FinitePlace K, ¬∃ w : InfinitePlace K, w.1 = v.1 := fun v ⟨w, hw⟩ ↦
    InfinitePlace.val_ne_finitePlace_val w v hw
  have hinjInf : Injective fun w : InfinitePlace K ↦ w.1 := fun _ _ h ↦ Subtype.ext h
  have hinjFin : Injective fun v : FinitePlace K ↦ v.1 := fun _ _ h ↦ Subtype.ext h
  set c : AbsoluteValue K ℝ → Unit → ℝ := fun a _ ↦
    extend (fun w : InfinitePlace K ↦ w.1) (fun w ↦ Real.log (B w) / w.mult)
      (extend (fun v : FinitePlace K ↦ v.1) (fun v ↦ Real.log (C v)) 0) a with hc
  have hcInf : ∀ (w : InfinitePlace K) i, c w.1 i = Real.log (B w) / w.mult := fun w _ ↦
    hinjInf.extend_apply _ _ _
  have hcFin : ∀ (v : FinitePlace K) i, c v.1 i = Real.log (C v) := fun v _ ↦ by
    simp only [hc]
    rw [extend_apply' _ _ _ (hdisj v)]
    exact hinjFin.extend_apply _ _ _
  set Q := Real.exp 1 with hQ
  have hQ0 : 0 < Q := Real.exp_pos 1
  have hLI : ∀ a, LinearIndependent K (L₀ a) := fun a ↦ linearIndependent_unique_iff.2 fun h0 ↦ by
    have := LinearMap.congr_fun h0 fun _ ↦ 1
    simp [hL₀] at this
  have hw : approxWeight Sfin c = ∑ w, Real.log (B w) + ∑ v ∈ Sfin, Real.log (C v) := by
    rw [approxWeight]
    congr 1
    · refine Finset.sum_congr rfl fun w _ ↦ ?_
      simp only [Finset.univ_unique, Finset.sum_singleton, PUnit.default_eq_unit, hcInf w ()]
      field_simp [w.mult_pos.ne']
    · refine Finset.sum_congr rfl fun v _ ↦ ?_
      simp [hcFin v ()]
  have hpow : ∀ (w : InfinitePlace K) (a : ℝ), 0 ≤ a → a ≤ Q ^ c w.1 () →
      a ^ w.mult ≤ B w := fun w a ha hle ↦ by
    have hm : (0 : ℝ) < w.mult := by exact_mod_cast w.mult_pos
    rw [hcInf w (), hQ, Real.exp_one_rpow] at hle
    calc a ^ w.mult ≤ Real.exp (Real.log (B w) / w.mult) ^ w.mult := pow_le_pow_left₀ ha hle _
      _ = B w := by
          rw [← Real.exp_nat_mul, mul_div_cancel₀ _ hm.ne', Real.exp_log (hB w)]
  have hprod := prod_successiveMinimum_approx_le (Sfin := Sfin) (L := L₀) (fun w ↦ hLI w.1)
    (fun v _ ↦ hLI v.1) c hQ0
  simp only [Fintype.card_unit, Finset.range_one, Finset.prod_singleton, mul_one, pow_one] at hprod
  rw [approxConst_proj, hw] at hprod
  set P := ∏ v ∈ Sfin, (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ)
  have hP : 0 < P := Finset.prod_pos fun v _ ↦ zero_lt_one.trans v.one_lt_absNorm
  set M := (∏ w, B w) * ∏ v ∈ Sfin, C v
  have hQB : Q ^ (-(∑ w, Real.log (B w) + ∑ v ∈ Sfin, Real.log (C v))) = M⁻¹ := by
    rw [hQ, Real.exp_one_rpow, Real.exp_neg, Real.exp_add, Real.exp_sum, Real.exp_sum]
    simp only [Real.exp_log (hB _), Real.exp_log (hC _), M]
  rw [hQB] at hprod
  have hMpos : 0 < M := mul_pos (Finset.prod_pos fun w _ ↦ hB w) (Finset.prod_pos fun v _ ↦ hC v)
  have hcov : ZLattice.covolume (mixedEmbedding.integerLattice K) ≤ √|(discr K : ℝ)| := by
    rw [mixedEmbedding.covolume_integerLattice]
    exact mul_le_of_le_one_left (Real.sqrt_nonneg _) (pow_le_one₀ (by norm_num) (by norm_num))
  have hcov0 := ZLattice.covolume_pos (mixedEmbedding.integerLattice K)
  have hpi : (1 : ℝ) ≤
      2 ^ InfinitePlace.nrRealPlaces K * Real.pi ^ InfinitePlace.nrComplexPlaces K :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two)
      (one_le_pow₀ (by linarith [Real.pi_gt_three]))
  have hRHS : 2 ^ finrank ℚ K * P /
      (2 ^ InfinitePlace.nrRealPlaces K * Real.pi ^ InfinitePlace.nrComplexPlaces K /
        ZLattice.covolume (mixedEmbedding.integerLattice K)) * M⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hMpos, div_div_eq_mul_div]
    refine (div_le_of_le_mul₀ (by positivity)
      (mul_nonneg (zero_le_one.trans one_le_unitConst) hP.le) ?_).trans h
    rw [unitConst]
    calc 2 ^ finrank ℚ K * P * ZLattice.covolume (mixedEmbedding.integerLattice K)
        ≤ 2 ^ finrank ℚ K * P * √|(discr K : ℝ)| := mul_le_mul_of_nonneg_left hcov (by positivity)
      _ = 2 ^ finrank ℚ K * √|(discr K : ℝ)| * P * 1 := by ring
      _ ≤ 2 ^ finrank ℚ K * √|(discr K : ℝ)| * P *
          (2 ^ InfinitePlace.nrRealPlaces K * Real.pi ^ InfinitePlace.nrComplexPlaces K) :=
        mul_le_mul_of_nonneg_left hpi (by positivity)
  have hμ0 := successiveMinimum_nonneg (approxModule Sfin L₀ c Q) (approxBody L₀ c Q) 0
  have hμ : successiveMinimum (approxModule Sfin L₀ c Q) (approxBody L₀ c Q) 0 ≤ 1 :=
    (pow_le_one_iff_of_nonneg hμ0 (finrank_pos (R := ℚ) (M := K)).ne').1 (hprod.trans hRHS)
  rw [successiveMinimum_approx_le_one_iff (fun w ↦ hLI w.1) (fun v _ ↦ hLI v.1) c hQ0
    (by simp)] at hμ
  obtain ⟨y, hy, hy0⟩ : ∃ y ∈ approxDomain Sfin L₀ c Q, y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 : approxSpan Sfin L₀ c Q = ⊥ := Submodule.span_eq_bot.2 hcon
    rw [h0, finrank_bot] at hμ
    exact lt_irrefl _ hμ
  refine ⟨y (), fun h0 ↦ hy0 (funext fun _ ↦ h0), fun v hv ↦ ?_, fun v hv ↦ hy.2.2 v hv (),
    fun w ↦ hpow w _ (apply_nonneg _ _) (hy.1 w ())⟩
  have := hy.2.1 v hv ()
  rwa [hcFin v (), hQ, Real.exp_one_rpow, Real.exp_log (hC v)] at this

/-! ### ES02 Lemma 6.3 = EF13 Lemma 11.1 -/

/-- **ES02 Lemma 6.3 over `K`**: for positive `A` on the infinite places and `C` on the finite
places, `1` almost everywhere, with `∏_w A_w ^ mult w · ∏_v C_v > 1`, some nonzero `g ∈ K` has
`|g|_w ≤ A_w ^ k` and `|g|_v ≤ C_v ^ k` everywhere, for some `k > 0`. ES02 take an `S`-unit;
Minkowski's theorem for one scalar (`exists_ne_zero_le_of_mul_le`) does it once `k` is large. -/
theorem exists_pow_le_of_one_lt {A : InfinitePlace K → ℝ} {C : FinitePlace K → ℝ}
    (hA : ∀ w, 0 < A w) (hC : ∀ v, 0 < C v) (hCf : C.HasFiniteMulSupport)
    (h : 1 < (∏ w, A w ^ w.mult) * ∏ᶠ v, C v) :
    ∃ k : ℕ, 0 < k ∧ ∃ g : K, g ≠ 0 ∧ (∀ w : InfinitePlace K, w g ≤ A w ^ k) ∧
      ∀ v : FinitePlace K, v g ≤ C v ^ k := by
  classical
  set S := hCf.toFinset
  have hmemS : ∀ v, v ∉ S → C v = 1 := fun v hv ↦ by
    by_contra h'
    exact hv ((Set.Finite.mem_toFinset hCf).2 h')
  rw [finprod_eq_prod_of_mulSupport_subset C (Set.Finite.coe_toFinset hCf).symm.subset] at h
  set N := ∏ v ∈ S, (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ)
  have hN : 1 ≤ N := by
    calc (1 : ℝ) = ∏ v ∈ S, (1 : ℝ) := Finset.prod_const_one.symm
      _ ≤ N := Finset.prod_le_prod₀ (fun _ _ ↦ zero_le_one) fun v _ ↦ v.one_lt_absNorm.le
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (unitConst K * N) h
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [pow_zero] at hk
      linarith [one_le_mul_of_one_le_of_one_le (one_le_unitConst (K := K)) hN]
    · exact hk0
  obtain ⟨g, hg0, hgS, hgS', hgw⟩ := exists_ne_zero_le_of_mul_le S
    (B := fun w ↦ (A w ^ k) ^ w.mult) (C := fun v ↦ C v ^ k) (fun w ↦ by have := hA w; positivity)
    (fun v ↦ pow_pos (hC v) k) <| by
      refine hk.le.trans (le_of_eq ?_)
      rw [mul_pow, ← Finset.prod_pow, ← Finset.prod_pow]
      congr 1
      exact Finset.prod_congr rfl fun w _ ↦ by rw [← pow_mul, ← pow_mul, mul_comm]
  refine ⟨k, hk0, g, hg0, fun w ↦ ?_, fun v ↦ ?_⟩
  · exact (pow_le_pow_iff_left₀ (apply_nonneg _ _) (pow_nonneg (hA w).le _)
      w.mult_pos.ne').1 (hgw w)
  · by_cases hv : v ∈ S
    · exact hgS v hv
    · rw [hmemS v hv, one_pow]
      exact hgS' v hv

/-- **Taking a `k`-th root.** If `|g|_w ≤ A_w ^ k` and `|g|_v ≤ C_v ^ k` at the places of `F`,
a `k`-th root `γ` of `g` in an extension `E` has `|γ|_w ≤ A_{w|F}` at the infinite places and
`|γ|_q ≤ C_{q|F} ^ {e f}` at the finite ones, `e f` the local degree: in absolute values,
`‖γ‖_q ≤ ‖C‖^{d(q|v)}` (ES02 (6.27)). -/
theorem le_of_pow_eq_algebraMap {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {A : InfinitePlace F → ℝ} {C : FinitePlace F → ℝ} (hA : ∀ w, 0 ≤ A w)
    (hC : ∀ v, 0 ≤ C v) {k : ℕ} (hk : 0 < k) {g : F} (hgA : ∀ w, w g ≤ A w ^ k)
    (hgC : ∀ v, v g ≤ C v ^ k) {γ : E} (hγ : γ ^ k = algebraMap F E g) :
    (∀ w : InfinitePlace E, w γ ≤ A (w.comap (algebraMap F E))) ∧
      ∀ q : FinitePlace E, q γ ≤ C (q.under F) ^ q.localDegree F := by
  refine ⟨fun w ↦ ?_, fun q ↦ ?_⟩
  · refine (pow_le_pow_iff_left₀ (apply_nonneg _ _) (hA _) hk.ne').1 ?_
    rw [← map_pow, hγ, ← InfinitePlace.comap_apply]
    exact hgA _
  · refine (pow_le_pow_iff_left₀ (apply_nonneg _ _) (pow_nonneg (hC _) _) hk.ne').1 ?_
    rw [← map_pow, hγ, FinitePlace.apply_algebraMap q (q.under F), ← pow_mul, mul_comm, pow_mul]
    exact pow_le_pow_left₀ (apply_nonneg _ _) (hgC _) _

/-- **EF13 Lemma 11.1 = ES02 Lemma 6.3**, in the relative normalization: for positive `A` on the
infinite places and `C` on the finite places of `K`, `1` almost everywhere, with
`∏_w A_w ^ mult w · ∏_v C_v > 1`, some nonzero `α` in a finite extension `E ⊆ Ω` has
`|α|_w ≤ A_{w|K}` at the infinite places and `|α|_q ≤ C_{q|K} ^ {e f}` at the finite ones (EF13's
`‖α‖_w ≤ A_u ^ {d(w|u)}`). -/
theorem exists_le_of_one_lt (Ω : Type*) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    {A : InfinitePlace K → ℝ} {C : FinitePlace K → ℝ} (hA : ∀ w, 0 < A w) (hC : ∀ v, 0 < C v)
    (hCf : C.HasFiniteMulSupport) (h : 1 < (∏ w, A w ^ w.mult) * ∏ᶠ v, C v) :
    ∃ (E : IntermediateField K Ω) (_ : NumberField E) (α : E), α ≠ 0 ∧
      (∀ w : InfinitePlace E, w α ≤ A (w.comap (algebraMap K E))) ∧
      ∀ q : FinitePlace E, q α ≤ C (q.under K) ^ q.localDegree K := by
  obtain ⟨k, hk, g, hg0, hgA, hgC⟩ := exists_pow_le_of_one_lt hA hC hCf h
  obtain ⟨γ, hγ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K Ω g) hk
  have hint : IsIntegral K γ :=
    IsIntegral.of_pow hk (hγ ▸ isIntegral_algebraMap)
  set E := IntermediateField.adjoin K {γ}
  have : FiniteDimensional K E := IntermediateField.adjoin.finiteDimensional hint
  have : NumberField E := { to_finiteDimensional := Module.Finite.trans K _ }
  have hγE : γ ∈ E := IntermediateField.mem_adjoin_simple_self K γ
  have hγ' : (⟨γ, hγE⟩ : E) ^ k = algebraMap K E g := Subtype.ext hγ
  obtain ⟨h1, h2⟩ := le_of_pow_eq_algebraMap (fun w ↦ (hA w).le) (fun v ↦ (hC v).le) hk hgA hgC hγ'
  refine ⟨E, inferInstance, ⟨γ, hγE⟩, fun h0 ↦ hg0 ?_, h1, h2⟩
  have : γ = 0 := congrArg Subtype.val h0
  rw [this, zero_pow hk.ne', eq_comm, map_eq_zero] at hγ
  exact hγ

/-! ### Scaling a point into local bounds -/

namespace FormSystem

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (L : FormSystem K ι) (a : FormWeight K ι)

/-- **Local bounds** for `y ∈ Eⁿ`: the local factor of `y` is at most `ρa_{w|K}` at each infinite
place `w` of `E` and at most `ρf_{w|K} ^ {e f}` at each finite place, `e f` the local degree. In
EF13's absolute normalization: `max_i ‖L_i^{(w)}(y)‖_w / ‖c_iw‖ ≤ ‖ρ‖_u ^ {d(w|u)}`. -/
def LocallyLe {E : Type*} [Field E] [NumberField E] [Algebra K E] (ρa : InfinitePlace K → ℝ)
    (ρf : FinitePlace K → ℝ) (y : ι → E) : Prop :=
  (∀ w : InfinitePlace E, L.archFactor a w y ≤ ρa (w.comap (algebraMap K E))) ∧
    ∀ w : FinitePlace E, L.finFactor a w y ≤ ρf (w.under K) ^ w.localDegree K

variable {L a}

/-- **Local bounds bound the height**: `H_E(y) ≤ (∏_v ρa_v ^ mult v · ∏_v ρf_v) ^ [E : K]`. -/
theorem mulHeight_le_of_locallyLe {E : Type*} [Field E] [NumberField E] [Algebra K E]
    {ρa : InfinitePlace K → ℝ} {ρf : FinitePlace K → ℝ} (hρa : ∀ v, 0 ≤ ρa v)
    (hρf : ∀ v, 0 ≤ ρf v) (hρff : ρf.HasFiniteMulSupport) {y : ι → E}
    (hy : L.LocallyLe a ρa ρf y) :
    L.mulHeight a y ≤ ((∏ v, ρa v ^ v.mult) * ∏ᶠ v, ρf v) ^ finrank K E := by
  have hfin0 : 0 ≤ ∏ᶠ v, ρf v := finprod_nonneg hρf
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [mulHeight_zero]
    exact pow_nonneg (mul_nonneg (Finset.prod_nonneg fun v _ ↦ pow_nonneg (hρa v) _) hfin0) _
  rw [mulHeight, mul_pow]
  refine mul_le_mul ?_ ?_ (finprod_nonneg fun w ↦ L.finFactor_nonneg a w y)
    (pow_nonneg (Finset.prod_nonneg fun v _ ↦ pow_nonneg (hρa v) _) _)
  · rw [← prod_infinitePlace_pow_mult_eq ρa (fun w ↦ ρa (w.comap (algebraMap K E)))
      fun φ ↦ by rw [InfinitePlace.comap_mk]]
    exact Finset.prod_le_prod₀ (fun w _ ↦ pow_nonneg (L.archFactor_nonneg a w y) _)
      fun w _ ↦ pow_le_pow_left₀ (L.archFactor_nonneg a w y) (hy.1 w) _
  · rw [← FinitePlace.finprod_under_pow_localDegree ρf hρff]
    exact Twist.finprod_le_finprod_of_nonneg (L.hasFiniteMulSupport_finFactor a hy0)
      (FinitePlace.hasFiniteMulSupport_comp_under hρff _) (fun w ↦ L.finFactor_nonneg a w y) hy.2

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]

/-- `(t ^ [E:K]) ^ {1/[E:ℚ]} = t ^ {1/[K:ℚ]}`, also for `t = 0`. -/
private theorem rpow_finrank_inv' {E : Type*} [Field E] [NumberField E] [Algebra K E] {t : ℝ}
    (ht : 0 ≤ t) : (t ^ finrank K E) ^ ((finrank ℚ E : ℝ))⁻¹ = t ^ ((finrank ℚ K : ℝ))⁻¹ := by
  rcases ht.eq_or_lt with rfl | ht
  · have : Module.Finite K E := Module.Finite.of_restrictScalars_finite ℚ K E
    rw [zero_pow finrank_pos.ne', Real.zero_rpow (inv_ne_zero (by exact_mod_cast finrank_pos.ne')),
      Real.zero_rpow (inv_ne_zero (by exact_mod_cast finrank_pos.ne'))]
  · exact rpow_finrank_inv ht

/-- **Local bounds bound the absolute height**: if `x ∈ Ωⁿ` has coordinates in `E` and satisfies
the local bounds there, `H(x) ≤ (∏_v ρa_v ^ mult v · ∏_v ρf_v) ^ {1/[K:ℚ]}`. -/
theorem absMulHeight_le_of_locallyLe {E : IntermediateField K Ω} [NumberField E]
    {ρa : InfinitePlace K → ℝ} {ρf : FinitePlace K → ℝ} (hρa : ∀ v, 0 ≤ ρa v)
    (hρf : ∀ v, 0 ≤ ρf v) (hρff : ρf.HasFiniteMulSupport) {y : ι → E}
    (hy : L.LocallyLe a ρa ρf y) :
    L.absMulHeight a (fun i ↦ (y i : Ω)) ≤
      ((∏ v, ρa v ^ v.mult) * ∏ᶠ v, ρf v) ^ ((finrank ℚ K : ℝ))⁻¹ := by
  have ht : 0 ≤ (∏ v, ρa v ^ v.mult) * ∏ᶠ v, ρf v :=
    mul_nonneg (Finset.prod_nonneg fun v _ ↦ pow_nonneg (hρa v) _) (finprod_nonneg hρf)
  rw [L.absMulHeight_eq_of_mem a (fun i ↦ (y i).2), ← rpow_finrank_inv' (E := E) ht]
  exact Real.rpow_le_rpow (L.mulHeight_nonneg a _) (mulHeight_le_of_locallyLe hρa hρf hρff hy)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

variable [IsAlgClosed Ω]

variable (L a) in
/-- **ES02 Lemma 6.2 / 7.3, EF13 Lemma 11.2, general form.** Points `x_j ≠ 0` of `Ωⁿ` (finitely
many) whose heights are below the products of positive local budgets `ρa_j`, `ρf_j` (`ρf_j` equal
to `1` almost everywhere) have nonzero multiples `β_j x_j`, all in one finite extension `E ⊆ Ω`,
satisfying the local bounds. The proof applies ES02 Lemma 6.3 (`exists_pow_le_of_one_lt`) over
`F = K(x)` to the budgets divided by the local factors of `x_j`, whose product exceeds `1`, and
takes `β_j` a `k`-th root in `Ω`. -/
theorem exists_locallyLe_smul {κ : Type*} [Finite κ] {x : κ → ι → Ω} (hx : ∀ j, x j ≠ 0)
    {ρa : κ → InfinitePlace K → ℝ} {ρf : κ → FinitePlace K → ℝ} (hρa : ∀ j v, 0 < ρa j v)
    (hρf : ∀ j v, 0 < ρf j v) (hρff : ∀ j, (ρf j).HasFiniteMulSupport)
    (h : ∀ j, L.absMulHeight a (x j) <
      ((∏ v, ρa j v ^ v.mult) * ∏ᶠ v, ρf j v) ^ ((finrank ℚ K : ℝ))⁻¹) :
    ∃ (E : IntermediateField K Ω) (_ : NumberField E) (y : κ → ι → E),
      (∀ j, ∃ β : Ω, β ≠ 0 ∧ ∀ i, (y j i : Ω) = β * x j i) ∧
      ∀ j, L.LocallyLe a (ρa j) (ρf j) (y j) := by
  classical
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  -- The field `F = K(x)` and the points over it.
  set z : κ × ι → Ω := fun p ↦ x p.1 p.2
  set F := IntermediateField.adjoin K (Set.range z)
  have : NumberField F := Twist.numberField_adjoin_range (K := K) z
  have : Module.Finite K F := Module.Finite.of_restrictScalars_finite ℚ K F
  have hxF : ∀ j i, x j i ∈ F := fun j i ↦ IntermediateField.subset_adjoin K _ ⟨(j, i), rfl⟩
  set yF : κ → ι → F := fun j i ↦ ⟨x j i, hxF j i⟩
  have hyF0 : ∀ j, yF j ≠ 0 := fun j h0 ↦
    hx j (funext fun i ↦ congrArg Subtype.val (congrFun h0 i))
  set P : κ → ℝ := fun j ↦ (∏ v, ρa j v ^ v.mult) * ∏ᶠ v, ρf j v
  have hP : ∀ j, 0 < P j := fun j ↦ mul_pos (Finset.prod_pos fun v _ ↦ pow_pos (hρa j v) _)
    (by rw [finprod_eq_prod _ (hρff j)]; exact Finset.prod_pos fun v _ ↦ hρf j v)
  -- The budgets over `F`, divided by the local factors.
  set A : κ → InfinitePlace F → ℝ := fun j w ↦
    ρa j (w.comap (algebraMap K F)) / L.archFactor a w (yF j)
  set C : κ → FinitePlace F → ℝ := fun j q ↦
    ρf j (q.under K) ^ q.localDegree K / L.finFactor a q (yF j)
  have hA : ∀ j w, 0 < A j w := fun j w ↦ div_pos (hρa _ _) (L.archFactor_pos a (hyF0 j) w)
  have hC : ∀ j q, 0 < C j q := fun j q ↦
    div_pos (pow_pos (hρf _ _) _) (L.finFactor_pos a (hyF0 j) q)
  have hCf : ∀ j, (C j).HasFiniteMulSupport := fun j ↦
    Function.HasFiniteMulSupport.fun_div (FinitePlace.hasFiniteMulSupport_comp_under (hρff j) _)
      (L.hasFiniteMulSupport_finFactor a (hyF0 j))
  have hprod : ∀ j, 1 < (∏ w, A j w ^ w.mult) * ∏ᶠ q, C j q := fun j ↦ by
    have hH : L.mulHeight a (yF j) < P j ^ finrank K F := by
      have h1 := h j
      rw [L.absMulHeight_eq_of_mem a (hxF j), ← rpow_finrank_inv (E := F) (hP j)] at h1
      exact (Real.rpow_lt_rpow_iff (L.mulHeight_nonneg a _) (pow_nonneg (hP j).le _)
        (inv_pos.mpr (by exact_mod_cast finrank_pos))).1 h1
    have hinf : ∏ w : InfinitePlace F, ρa j (w.comap (algebraMap K F)) ^ w.mult =
        (∏ v, ρa j v ^ v.mult) ^ finrank K F :=
      prod_infinitePlace_pow_mult_eq _ _ fun φ ↦ by rw [InfinitePlace.comap_mk]
    have hfin : ∏ᶠ q : FinitePlace F, ρf j (q.under K) ^ q.localDegree K =
        (∏ᶠ v, ρf j v) ^ finrank K F :=
      FinitePlace.finprod_under_pow_localDegree _ (hρff j)
    have hmh : L.mulHeight a (yF j) = (∏ w, L.archFactor a w (yF j) ^ w.mult) *
        ∏ᶠ q, L.finFactor a q (yF j) := rfl
    simp only [A, C, div_pow, Finset.prod_div_distrib]
    rw [finprod_div_distrib (FinitePlace.hasFiniteMulSupport_comp_under (hρff j) _)
      (L.hasFiniteMulSupport_finFactor a (hyF0 j)), hinf, hfin, div_mul_div_comm, ← mul_pow,
      ← hmh]
    exact (one_lt_div (L.mulHeight_pos a (hyF0 j))).2 hH
  -- ES02 Lemma 6.3 over `F`, and `k`-th roots in `Ω`.
  choose k hk g hg0 hgA hgC using fun j ↦ exists_pow_le_of_one_lt (hA j) (hC j) (hCf j) (hprod j)
  choose γ hγ using fun j ↦ IsAlgClosed.exists_pow_nat_eq ((g j : F) : Ω) (hk j)
  set E := IntermediateField.adjoin K (Set.range z ∪ Set.range γ)
  have : FiniteDimensional K E := IntermediateField.finiteDimensional_adjoin fun y _ ↦
    (Algebra.IsAlgebraic.isAlgebraic (R := K) y).isIntegral
  have : NumberField E := { to_finiteDimensional := Module.Finite.trans K _ }
  have hFE : F ≤ E := IntermediateField.adjoin.mono _ _ _ Set.subset_union_left
  let : Algebra F E := (IntermediateField.inclusion hFE).toAlgebra
  have : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hγE : ∀ j, γ j ∈ E := fun j ↦ IntermediateField.subset_adjoin K _ (Or.inr ⟨j, rfl⟩)
  set γE : κ → E := fun j ↦ ⟨γ j, hγE j⟩
  have hγE' : ∀ j, γE j ^ k j = algebraMap F E (g j) := fun j ↦ Subtype.ext (hγ j)
  refine ⟨E, inferInstance, fun j ↦ γE j • (algebraMap F E ∘ yF j), fun j ↦ ⟨γ j, ?_, fun i ↦ rfl⟩,
    fun j ↦ ?_⟩
  · intro h0
    have := hγ j
    rw [h0, zero_pow (hk j).ne', eq_comm] at this
    exact hg0 j (Subtype.ext this)
  obtain ⟨hrA, hrC⟩ := le_of_pow_eq_algebraMap (fun w ↦ (hA j w).le) (fun q ↦ (hC j q).le) (hk j)
    (hgA j) (hgC j) (hγE' j)
  refine ⟨fun w ↦ ?_, fun q ↦ ?_⟩
  · rw [archFactor_smul, archFactor_algebraMap]
    have hc : (w.comap (algebraMap F E)).comap (algebraMap K F) = w.comap (algebraMap K E) := by
      rw [← InfinitePlace.comap_comp, ← IsScalarTower.algebraMap_eq]
    calc w (γE j) * L.archFactor a (w.comap (algebraMap F E)) (yF j)
        ≤ A j (w.comap (algebraMap F E)) * L.archFactor a (w.comap (algebraMap F E)) (yF j) :=
          mul_le_mul_of_nonneg_right (hrA w) (L.archFactor_nonneg a _ _)
      _ = ρa j (w.comap (algebraMap K E)) := by
          simp only [A]
          rw [div_mul_cancel₀ _ (L.archFactor_pos a (hyF0 j) _).ne', hc]
  · rw [finFactor_smul, finFactor_algebraMap]
    calc q (γE j) * L.finFactor a (q.under F) (yF j) ^ q.localDegree F
        ≤ C j (q.under F) ^ q.localDegree F * L.finFactor a (q.under F) (yF j) ^ q.localDegree F :=
          mul_le_mul_of_nonneg_right (hrC q) (pow_nonneg (L.finFactor_nonneg a _ _) _)
      _ = ρf j (q.under K) ^ q.localDegree K := by
          simp only [C]
          rw [← mul_pow, div_mul_cancel₀ _ (L.finFactor_pos a (hyF0 j) _).ne', ← pow_mul,
            FinitePlace.under_under (K := K) (E := F) q,
            FinitePlace.localDegree_tower (K := K) (E := F) q, mul_comm]

/-- **EF13 Lemma 11.2**: points `x_j ≠ 0` with `H(x_j) < μ_j` have nonzero multiples `y_j = β_j x_j`
in one finite extension `E ⊆ Ω` with local factors at most `1/n` at the infinite places, at most
`1` at the finite places not above `v₀`, and at most `((n μ_j) ^ [K:ℚ]) ^ {e f}` at those above
`v₀`, `n = #ι`. In EF13's absolute normalization these are (11.3) (`n^{-s(w)}`) and (11.4)
(`(n μ_j) ^ {d(w|v₀)}`), with `μ_j = (1 + ε) λ_j`. -/
theorem exists_smul_le_of_lt [Nonempty ι] {κ : Type*} [Finite κ] {x : κ → ι → Ω}
    (hx : ∀ j, x j ≠ 0) (v₀ : FinitePlace K) {μ : κ → ℝ} (hμ : ∀ j, L.absMulHeight a (x j) < μ j) :
    ∃ (E : IntermediateField K Ω) (_ : NumberField E) (y : κ → ι → E),
      (∀ j, ∃ β : Ω, β ≠ 0 ∧ ∀ i, (y j i : Ω) = β * x j i) ∧
      (∀ j (w : InfinitePlace E), L.archFactor a w (y j) ≤ (Fintype.card ι : ℝ)⁻¹) ∧
      (∀ j (w : FinitePlace E), w.under K ≠ v₀ → L.finFactor a w (y j) ≤ 1) ∧
      ∀ j (w : FinitePlace E), w.under K = v₀ →
        L.finFactor a w (y j) ≤ ((Fintype.card ι * μ j) ^ finrank ℚ K) ^ w.localDegree K := by
  classical
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hμ0 : ∀ j, 0 < μ j := fun j ↦ (L.absMulHeight_pos a (hx j)).trans (hμ j)
  set ρf : κ → FinitePlace K → ℝ := fun j v ↦
    if v = v₀ then (Fintype.card ι * μ j) ^ finrank ℚ K else 1
  have hρf : ∀ j v, 0 < ρf j v := fun j v ↦ by
    simp only [ρf]
    split_ifs
    · exact pow_pos (mul_pos hn (hμ0 j)) _
    · exact one_pos
  have hρff : ∀ j, (ρf j).HasFiniteMulSupport := fun j ↦
    (Set.finite_singleton v₀).subset fun v hv ↦ by
      by_contra h
      have h' : v ≠ v₀ := h
      exact hv (by simp [ρf, h'])
  obtain ⟨E, hE, y, hy, hloc⟩ := L.exists_locallyLe_smul a hx (ρa := fun _ _ ↦ (Fintype.card ι)⁻¹)
    (fun _ _ ↦ inv_pos.mpr hn) hρf hρff fun j ↦ by
      have hfin : ∏ᶠ v, ρf j v = (Fintype.card ι * μ j) ^ finrank ℚ K :=
        (finprod_eq_single (ρf j) v₀ fun v hv ↦ by simp [ρf, hv]).trans (by simp [ρf])
      rw [hfin, Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq, ← mul_pow, ← mul_assoc,
        inv_mul_cancel₀ hn.ne', one_mul, Real.pow_rpow_inv_natCast (hμ0 j).le finrank_pos.ne']
      exact hμ j
  refine ⟨E, hE, y, hy, fun j w ↦ (hloc j).1 w, fun j w hw ↦ ?_, fun j w hw ↦ ?_⟩
  · have := (hloc j).2 w
    rwa [show ρf j (w.under K) = 1 by simp [ρf, hw], one_pow] at this
  · have := (hloc j).2 w
    rwa [show ρf j (w.under K) = (Fintype.card ι * μ j) ^ finrank ℚ K by simp [ρf, hw]] at this

/-! ### The parallelepiped `μ ∗ Π` (ES02 §7) -/

open scoped Classical in
/-- The budget of `μ ∗ Π` at the finite places: `μ ^ [K:ℚ]` at `v₀`, `1` elsewhere. -/
noncomputable def paraBudget (v₀ : FinitePlace K) (μ : ℝ) : FinitePlace K → ℝ :=
  fun v ↦ if v = v₀ then μ ^ finrank ℚ K else 1

theorem paraBudget_nonneg (v₀ : FinitePlace K) {μ : ℝ} (hμ : 0 ≤ μ) (v : FinitePlace K) :
    0 ≤ paraBudget v₀ μ v := by
  unfold paraBudget
  split_ifs
  · exact pow_nonneg hμ _
  · exact zero_le_one

theorem hasFiniteMulSupport_paraBudget (v₀ : FinitePlace K) (μ : ℝ) :
    (paraBudget v₀ μ).HasFiniteMulSupport :=
  (Set.finite_singleton v₀).subset fun v hv ↦ by
    by_contra h
    have h' : v ≠ v₀ := h
    exact hv (by simp [paraBudget, h'])

theorem finprod_paraBudget (v₀ : FinitePlace K) (μ : ℝ) :
    ∏ᶠ v, paraBudget v₀ μ v = μ ^ finrank ℚ K :=
  (finprod_eq_single _ v₀ fun _ hv ↦ by simp [paraBudget, hv]).trans (by simp [paraBudget])

variable (L a Ω) in
/-- **The parallelepiped `μ ∗ Π(A)`** of ES02 §7, with the scaling at a finite place `v₀` as in
ES02 (6.13), (6.14): the points of `Ωⁿ` with coordinates in some finite extension `E ⊆ Ω` whose
local factors are at most `1` at every place not above `v₀` and at most `(μ ^ [K:ℚ]) ^ {e f}`
above `v₀` (`‖·‖_w ≤ μ ^ {d(w|v₀)}` absolutely). -/
def paraSet (v₀ : FinitePlace K) (μ : ℝ) : Set (ι → Ω) :=
  {x | ∃ (E : IntermediateField K Ω) (_ : NumberField E) (y : ι → E),
    (∀ i, (y i : Ω) = x i) ∧ L.LocallyLe a (fun _ ↦ 1) (paraBudget v₀ μ) y}

variable (L a Ω) in
/-- **`U_A(μ)`**: the span of `μ ∗ Π`. -/
noncomputable def paraSpace (v₀ : FinitePlace K) (μ : ℝ) : Submodule Ω (ι → Ω) :=
  Submodule.span Ω (L.paraSet a Ω v₀ μ)

variable (L a Ω) in
/-- **The successive minima `μ_i = inf {μ ≥ 0 : dim U_A(μ) ≥ i}` of `Π`** (ES02 §7). -/
noncomputable def paraInf (v₀ : FinitePlace K) (i : ℕ) : ℝ :=
  sInf {μ | 0 ≤ μ ∧ i ≤ finrank Ω (L.paraSpace a Ω v₀ μ)}

variable {v₀ : FinitePlace K}

omit [IsAlgClosed Ω] in
/-- Points of `μ ∗ Π` have height at most `μ`. -/
theorem absMulHeight_le_of_mem_paraSet {μ : ℝ} (hμ : 0 ≤ μ) {x : ι → Ω}
    (hx : x ∈ L.paraSet a Ω v₀ μ) : L.absMulHeight a x ≤ μ := by
  obtain ⟨E, hE, y, hyx, hy⟩ := hx
  obtain rfl : (fun i ↦ (y i : Ω)) = x := funext hyx
  refine (absMulHeight_le_of_locallyLe (fun _ ↦ zero_le_one) (paraBudget_nonneg v₀ hμ)
    (hasFiniteMulSupport_paraBudget v₀ μ) hy).trans (le_of_eq ?_)
  simp only [one_pow, Finset.prod_const_one, one_mul, finprod_paraBudget]
  exact Real.pow_rpow_inv_natCast hμ finrank_pos.ne'

/-- **ES02 Lemma 7.3**: a point `x ≠ 0` with `H(x) < μ` has a nonzero multiple in `μ ∗ Π`. -/
theorem exists_smul_mem_paraSet {μ : ℝ} {x : ι → Ω} (hx : x ≠ 0)
    (hlt : L.absMulHeight a x < μ) : ∃ β : Ω, β ≠ 0 ∧ β • x ∈ L.paraSet a Ω v₀ μ := by
  have hμ : 0 < μ := (L.absMulHeight_pos a hx).trans hlt
  obtain ⟨E, hE, y, hy, hloc⟩ := L.exists_locallyLe_smul a (κ := Unit) (x := fun _ ↦ x)
    (fun _ ↦ hx) (ρa := fun _ _ ↦ 1) (ρf := fun _ ↦ paraBudget v₀ μ) (fun _ _ ↦ one_pos)
    (fun _ v ↦ by
      unfold paraBudget
      split_ifs
      · exact pow_pos hμ _
      · exact one_pos)
    (fun _ ↦ hasFiniteMulSupport_paraBudget v₀ μ) fun _ ↦ by
      simp only [one_pow, Finset.prod_const_one, one_mul, finprod_paraBudget]
      rwa [Real.pow_rpow_inv_natCast hμ.le finrank_pos.ne']
  obtain ⟨β, hβ, hβx⟩ := hy ()
  exact ⟨β, hβ, E, hE, y (), fun i ↦ hβx i, hloc ()⟩

variable (L a)

omit [IsAlgClosed Ω] in
/-- `U_A(μ) ⊆ V_A(μ)`. -/
theorem paraSpace_le_infSpace {μ : ℝ} (hμ : 0 ≤ μ) :
    L.paraSpace a Ω v₀ μ ≤ L.infSpace a Ω μ :=
  Submodule.span_le.mpr fun _ hx ↦ mem_heightSpace (absMulHeight_le_of_mem_paraSet hμ hx)

/-- `V_A(μ) ⊆ U_A(ν)` for `μ < ν`, by ES02 Lemma 7.3. -/
theorem infSpace_le_paraSpace {μ ν : ℝ} (hlt : μ < ν) :
    L.infSpace a Ω μ ≤ L.paraSpace a Ω v₀ ν := by
  refine Submodule.span_le.mpr fun x (hx : L.absMulHeight a x ≤ μ) ↦ ?_
  rcases eq_or_ne x 0 with rfl | hx0
  · exact zero_mem _
  obtain ⟨β, hβ, hβx⟩ := exists_smul_mem_paraSet (L := L) (a := a) (v₀ := v₀) hx0 (hx.trans_lt hlt)
  have : x = β⁻¹ • β • x := by rw [smul_smul, inv_mul_cancel₀ hβ, one_smul]
  rw [SetLike.mem_coe, this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hβx)

/-- **ES02 Cor. 7.4**: the successive minima of `Π` are the successive infima of the height. -/
theorem paraInf_eq_successiveInf {i : ℕ} (hi : i ≤ Fintype.card ι) :
    L.paraInf a Ω v₀ i = L.successiveInf a Ω i := by
  have hbdd : BddBelow {μ | 0 ≤ μ ∧ i ≤ finrank Ω (L.paraSpace a Ω v₀ μ)} :=
    ⟨0, fun _ hμ ↦ hμ.1⟩
  refine le_antisymm (le_of_forall_gt_imp_ge_of_dense fun ν hν ↦ ?_) ?_
  · have hν0 : 0 ≤ ν := (heightInf_nonneg i).trans hν.le
    set μ := (L.successiveInf a Ω i + ν) / 2
    have h1 : L.successiveInf a Ω i < μ := by simp only [μ]; linarith
    have h2 : μ < ν := by simp only [μ]; linarith
    refine csInf_le hbdd ⟨hν0, (le_finrank_heightSpace hi h1).trans ?_⟩
    exact Submodule.finrank_mono (L.infSpace_le_paraSpace a h2)
  · obtain ⟨M, hM0, hM⟩ := exists_heightSpace_eq_top Ω (L.absMulHeight a)
    have hne : {μ | 0 ≤ μ ∧ i ≤ finrank Ω (L.paraSpace a Ω v₀ μ)}.Nonempty := by
      refine ⟨M + 1, show 0 ≤ M + 1 ∧ _ from ⟨by linarith, ?_⟩⟩
      have htop : L.paraSpace a Ω v₀ (M + 1) = ⊤ :=
        eq_top_iff.mpr ((hM M le_rfl).ge.trans (L.infSpace_le_paraSpace a (by linarith)))
      rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card]
      exact hi
    exact le_csInf hne fun μ ⟨hμ0, hμi⟩ ↦ heightInf_le hμ0
      (hμi.trans (Submodule.finrank_mono (L.paraSpace_le_infSpace a hμ0)))

end FormSystem

end NumberField
