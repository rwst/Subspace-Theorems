/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.NumberTheory.Height.ResultantHeight
public import ForMathlib.RingTheory.MvPolynomial.ResultantPoint

/-!
# Heights of ideals over a point

**The point bound** (Evertse 1995, §5, p. 247): if the projection of `V(I)` to the block `h`
is the point `P`, then `h(α res_d(I)) ≥ D log H(P)`, where the first form is linear in the block
`h` and `res_d(I)` has degree `D` in it (`MvPolynomial.logHeight_mul_le_gaussHeight_resForm`).
Indeed `P_{s₀}^D res_d(I) = (u · P)^D g` (`MvPolynomial.C_mul_resForm_eq`), heights are
additive and nonnegative, and the height of the linear form `u · P` is at least `log H(P)`
(`MvPolynomial.logHeight_le_gaussHeight_linear`): its Gaussian Mahler measure is the `ℓ²` norm
of `P` (`MvPolynomial.gaussLogMahler_linear`).
-/

@[expose] public section

open Finset Height Height.AdmissibleAbsValues Real

namespace MvPolynomial

section Linear

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {τ υ : Type*} [Fintype τ] [Fintype υ]

omit [Fintype τ] in
/-- `v ↦ max_t v(c_t)` is `1` at almost all finite places (as in Mathlib's private
`Height.hasFiniteMulSupport_iSup_nonarchAbsVal`). -/
theorem hasFiniteMulSupport_iSup_nonarch [Finite τ] {c : τ → K} (hc : c ≠ 0) :
    (fun v : nonarchAbsVal (K := K) ↦ ⨆ t, v.val (c t)).HasFiniteMulSupport := by
  refine (Set.finite_iUnion fun j : {j // c j ≠ 0} ↦
    AdmissibleAbsValues.hasFiniteMulSupport j.2).subset fun v hv ↦ ?_
  by_contra hni
  simp only [Set.mem_iUnion, not_exists, Function.mem_mulSupport, not_not] at hni
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hc
  have : Nonempty τ := ⟨i⟩
  refine hv (le_antisymm (ciSup_le fun j ↦ ?_) ?_)
  · rcases eq_or_ne (c j) 0 with h | h
    · rw [h, v.val.map_zero]
      exact zero_le_one
    · exact (hni ⟨j, h⟩).le
  · exact (hni ⟨i, hi⟩).symm.le.trans (Finite.le_ciSup_of_le i le_rfl)

/-- **The height of a linear form** is at least the height of its coefficients. -/
theorem logHeight_le_gaussHeight_linear (hK : ArchEmbedded K) {e : τ → υ}
    (he : Function.Injective e) {w : υ → ℂ} (hw : ∀ t, w (e t) = 1) (c : τ → K) :
    logHeight c ≤ gaussHeight w (∑ t, C (c t) * X (e t) : MvPolynomial υ K) := by
  classical
  set F : MvPolynomial υ K := ∑ t, C (c t) * X (e t)
  have hcoeff : ∀ t, F.coeff (Finsupp.single (e t) 1) = c t := fun t ↦ by
    simp [F, coeff_C_mul, coeff_X, Finsupp.single_eq_single_iff, he.eq_iff]
  rcases eq_or_ne c 0 with rfl | hc
  · simp [logHeight_eq_log_mulHeight, F, gaussHeight]
  have hF : F ≠ 0 := fun h0 ↦ hc (funext fun t ↦ by rw [← hcoeff t, h0]; simp)
  have : Nonempty τ := ⟨(Function.ne_iff.1 hc).choose⟩
  rw [logHeight_eq_log_mulHeight]
  simp only [gaussHeight, hF, ↓reduceIte]
  refine log_le_log (mulHeight_pos c) ?_
  rw [mulHeight_eq hc]
  refine mul_le_mul ?_ ?_ (finprod_nonneg fun v ↦ Real.iSup_nonneg fun _ ↦ v.val.nonneg _)
    (Multiset.prod_nonneg fun x hx ↦ by
      obtain ⟨v, -, rfl⟩ := Multiset.mem_map.1 hx
      exact (archMahler_pos w v F).le)
  · refine Multiset.prod_map_le_prod_map₀ _ _ (fun v _ ↦ Real.iSup_nonneg fun _ ↦ v.nonneg _)
      fun v hv ↦ ciSup_le fun t ↦ ?_
    have h := hK v hv
    rw [archMahler_of h]
    set φ := h.choose
    have hφ : ∀ x, v x = ‖φ x‖ := h.choose_spec
    have hscale : scaleVars w (map φ F) = rename e (∑ t, C (φ (c t)) * X t) := by
      simp [F, scaleVars, hw]
    have hφc : (fun t ↦ φ (c t)) ≠ 0 := fun h0 ↦ hc (funext fun t ↦
      (map_eq_zero φ).1 (congrFun h0 t))
    rw [hscale, gaussLogMahler_rename he, gaussLogMahler_linear hφc,
      exp_log (Real.sqrt_pos.2 ?_), hφ]
    · exact Real.le_sqrt_of_sq_le (Finset.single_le_sum (f := fun t ↦ ‖φ (c t)‖ ^ 2)
        (fun _ _ ↦ by positivity) (Finset.mem_univ t))
    · obtain ⟨t₀, ht₀⟩ := Function.ne_iff.1 hφc
      have h0 : φ (c t₀) ≠ 0 := ht₀
      exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum
        (f := fun t ↦ ‖φ (c t)‖ ^ 2) (fun _ _ ↦ by positivity) (Finset.mem_univ t₀))
  · refine finprod_le_finprod₀ (hasFiniteMulSupport_iSup_nonarch hc)
      (fun v ↦ Real.iSup_nonneg fun _ ↦ v.val.nonneg _)
      (hasFiniteMulSupport_maxNorm hF) fun v ↦ ciSup_le fun t ↦ ?_
    rw [← hcoeff t]
    exact le_maxNorm F _

end Linear

section Block

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι} {κ : Type*}
  {d : Option κ → ι → ℕ}

/-- The block `h` as the monomials of multidegree `ε_h`. -/
noncomputable def blockEquiv {h : ι} (hd : d none = Pi.single h 1) :
    {t // b t = h} ≃ blockMonomials b (d none) :=
  Equiv.ofBijective (fun t ↦ ⟨Finsupp.single t 1, by
      rw [hd, mem_blockMonomials_single]
      exact ⟨t, t.2, rfl⟩⟩)
    ⟨fun t t' htt ↦ Subtype.ext (Finsupp.single_left_injective one_ne_zero
      (congrArg Subtype.val htt)), fun ⟨m, hm⟩ ↦ by
        have hm' : m ∈ blockMonomials b (Pi.single h 1) := by rwa [← hd]
        obtain ⟨t, ht, rfl⟩ := (mem_blockMonomials_single (b := b)).1 hm'
        exact ⟨⟨t, ht⟩, rfl⟩⟩

theorem remodelWeight_none_single {h : ι} (hd : d none = Pi.single h 1)
    (m : blockMonomials b (d none)) : remodelWeight (⟨none, m⟩ : GenericVar b d) = 1 := by
  classical
  have hm : (m : σ →₀ ℕ) ∈ blockMonomials b (Pi.single h 1) := by
    rw [← hd]
    exact m.2
  obtain ⟨t, -, ht⟩ := (mem_blockMonomials_single (b := b)).1 hm
  simp only [remodelWeight, blockMultinomial, ht]
  rw [Finset.prod_eq_one fun i _ ↦ by
    rw [Finsupp.single_eq_pi_single]
    exact Nat.multinomial_single _ _ _]
  simp

end Block

section Point

universe u

variable {σ ι : Type u} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι}
  {K : Type u} [Field K] [AdmissibleAbsValues K] {κ : Type u} [Fintype κ]
  {d : Option κ → ι → ℕ}

/-- **The point bound** (Evertse 1995, §5, p. 247): if `I` contains the `P_s X_t - P_t X_s`
(`b s = b t = h`), so that `V(I)` projects to the point `P` in the block `h`, the first form is
linear in the block `h` and `res_d(I)` has degree `D` in it, then
`h(α res_d(I)) ≥ D log H(P)`. -/
theorem logHeight_mul_le_gaussHeight_resForm (hK : ArchEmbedded K) (hb : Function.Surjective b)
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsWeightedHomogeneous (multiWeight b))
    (hdim : (hilbertPoly b I).totalDegree + 1 ≤ Nat.card (Option κ)) {h : ι}
    (hd : d none = Pi.single h 1) (P : σ → K) {s₀ : σ} (hs₀ : b s₀ = h) (hP₀ : P s₀ ≠ 0)
    (hPI : ∀ s t, b s = h → b t = h → C (P s) * X t - C (P t) * X s ∈ I) {D : ℕ}
    (hD : IsWeightedHomogeneous (groupWeight b d none) (resForm b K d I) D) :
    D * logHeight (fun t : {t // b t = h} ↦ P t) ≤ gaussHeight remodelWeight (resForm b K d I) := by
  classical
  have hw := remodelWeight_ne_zero (b := b) (d := d)
  have hF := resForm_ne_zero (d := d) hb hI hdim
  have hE := C_mul_resForm_eq hb hI hdim hd P hs₀ hP₀ hPI hD
  set Lin := firstPointForm b d P
  set g := firstSpec b d (fun v ↦ if (v.2 : σ →₀ ℕ) = Finsupp.single s₀ 1 then 1 else 0)
    (resForm b K d I)
  have hprod : Lin ^ D * g ≠ 0 := by
    rw [← hE]
    exact mul_ne_zero (C_ne_zero.2 (pow_ne_zero _ hP₀)) hF
  have hg : g ≠ 0 := right_ne_zero_of_mul hprod
  have hLin : Lin = ∑ m : blockMonomials b (d none),
      C (∏ s, P s ^ (m : σ →₀ ℕ) s) * X (⟨none, m⟩ : GenericVar b d) := rfl
  have hLlog := logHeight_le_gaussHeight_linear hK (e := fun m : blockMonomials b (d none) ↦
    (⟨none, m⟩ : GenericVar b d)) (fun m m' hmm ↦ by simpa using hmm)
    (remodelWeight_none_single hd) (fun m ↦ ∏ s, P s ^ (m : σ →₀ ℕ) s)
  rw [← hLin] at hLlog
  have hcomp : (fun m : blockMonomials b (d none) ↦ ∏ s, P s ^ (m : σ →₀ ℕ) s) ∘ blockEquiv hd =
      fun t : {t // b t = h} ↦ P t := by
    funext t
    simp only [Function.comp_apply, blockEquiv]
    exact prod_pow_single_one P t
  have hPh : logHeight (fun t : {t // b t = h} ↦ P t) =
      logHeight (fun m : blockMonomials b (d none) ↦ ∏ s, P s ^ (m : σ →₀ ℕ) s) := by
    rw [← hcomp, logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight, mulHeight_comp_equiv]
  have hFnn := gaussHeight_nonneg hK one_le_norm_remodelWeight (resForm b K d I)
  rcases Nat.eq_zero_or_pos D with rfl | hDpos
  · simpa using hFnn
  have hLne : Lin ≠ 0 := fun h0 ↦ hprod (by rw [h0, zero_pow hDpos.ne', zero_mul])
  rw [← gaussHeight_C_mul hK hw (pow_ne_zero D hP₀) (resForm b K d I), hE,
    gaussHeight_mul hK hw (pow_ne_zero _ hLne) hg, gaussHeight_pow hK hw hLne, hPh]
  have := gaussHeight_nonneg hK one_le_norm_remodelWeight g
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  nlinarith

end Point

end MvPolynomial
