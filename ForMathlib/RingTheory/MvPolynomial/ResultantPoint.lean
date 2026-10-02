/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.RingTheory.MvPolynomial.ResultantSpace
public import ForMathlib.RingTheory.MvPolynomial.ResultantSpecialization
public import ForMathlib.RingTheory.MvPolynomial.WeightedAeval

-- Used only inside proofs.
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Resultant forms of ideals over a point

Let the projection of `V(I)` to the block `h` be a point `P`, i.e. `I` contains the
`P_s X_t - P_t X_s` (`b s = b t = h`). If the first generic form is linear in the block `h`, then
`res_d(I)` is `(u · P)^D g` up to a constant, with `u · P = ∑_{b s = h} P_s u_s` and `g` free of
the first form (Rémond, LNM 1752, Ch. 7: "la forme résultante est `λ (u · P)^D`"; Evertse 1995,
§5, p. 247).

Specializing all forms but the first into an algebraically closed field, `res_d(I)` becomes
`c ∏_j U(z_j)` (`MvPolynomial.exists_specEval_resForm_eq`). Every zero of a factor `U(z_j)` is a
zero of `U(x)` for some zero `x` of `I` (`MvPolynomial.exists_zero_of_eval_specEval_resForm`),
and those are proportional to `P` in the block `h`; so each `U(z_j)` is proportional to `u · P`.

## Main results

* `MvPolynomial.exists_zero_of_eval_specEval_resForm`: the zeros of the specialized resultant
  form.
* `MvPolynomial.exists_specEval_resForm_eq_C_mul_pow`: the specialization is `c (u · P)^D`.
-/

@[expose] public section

namespace MvPolynomial

section Linear

variable {M L : Type*} [Fintype M] [Field L]

/-- Two linear forms such that `ℓ₁ = 0 ⇒ ℓ₂ = 0` are proportional. -/
theorem exists_eq_smul_of_forall_sum_eq_zero {α β : M → L} (hα : α ≠ 0)
    (h : ∀ a : M → L, ∑ m, a m * α m = 0 → ∑ m, a m * β m = 0) : ∃ μ : L, β = μ • α := by
  classical
  obtain ⟨m₀, hm₀⟩ := Function.ne_iff.1 hα
  refine ⟨β m₀ / α m₀, _root_.funext fun m ↦ ?_⟩
  have key := h (Pi.single m (α m₀) - Pi.single m₀ (α m)) (by
    simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, Pi.single_apply, ite_mul,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring)
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, Pi.single_apply, ite_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at key
  have hm : α m₀ ≠ 0 := hm₀
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [div_mul_eq_mul_div, eq_div_iff hm]
  linear_combination key

end Linear

section PointForm

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι} {L : Type*} [Field L]

theorem eval_pointForm_eq_sum (e : ι → ℕ) (x : σ → L)
    (a : GenericVar b (fun _ : Unit ↦ e) → L) :
    eval a (pointForm b e x) =
      ∑ m : blockMonomials b e, a ⟨(), m⟩ * ∏ s, x s ^ (m : σ →₀ ℕ) s := by
  simp [pointForm_eq, mul_comm]

omit [Fintype ι] [DecidableEq ι] in
theorem prod_pow_single_one (x : σ → L) (t : σ) :
    ∏ s, x s ^ (Finsupp.single t 1 : σ →₀ ℕ) s = x t := by
  classical
  rw [Finset.prod_eq_single t (fun s _ hs ↦ by simp [Ne.symm hs])
    (by simp)]
  simp

end PointForm

section Point

universe u

variable {σ ι : Type u} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι}
  {K : Type u} [Field K] {κ : Type u} [Finite κ] {d : Option κ → ι → ℕ}
  {L : Type u} [Field L] [IsAlgClosed L]

/-- **The zeros of a specialized resultant form**: if `res_d(I)` vanishes after specializing the
forms `U_l` (`l ≠ none`) at `y` and the first one at `a`, then `U(x)(a) = 0` for a zero `x` of
`I`, nonzero in every block. -/
theorem exists_zero_of_eval_specEval_resForm (hb : Function.Surjective b)
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsWeightedHomogeneous (multiWeight b))
    (hdim : (hilbertPoly b I).totalDegree + 1 ≤ Nat.card (Option κ)) (φ : K →+* L)
    (y : GenericVar b (fun l : κ ↦ d (some l)) → L) (a : GenericVar b (fun _ : Unit ↦ d none) → L)
    (h : eval a (specEval b φ y (resForm b K d I)) = 0) :
    ∃ x : σ → L, (∀ i, ∃ s, b s = i ∧ x s ≠ 0) ∧ (∀ p ∈ I, eval x (map φ p) = 0) ∧
      eval a (pointForm b (d none) x) = 0 := by
  classical
  set ψ : MvPolynomial (GenericVar b d) K →+* L := (eval a).comp (specEval b φ y)
  obtain ⟨-, S, ℓ, hS, -, hassoc⟩ := associated_resForm_prod (d := d) hb hI hdim
  have h0 : ψ (∏ 𝔭 ∈ S, resForm b K d 𝔭 ^ ℓ 𝔭) = 0 := by
    obtain ⟨v, hv⟩ := hassoc
    rw [← hv, map_mul]
    simp [ψ, h]
  rw [map_prod, Finset.prod_eq_zero_iff] at h0
  obtain ⟨𝔭, h𝔭, h𝔭0⟩ := h0
  rw [map_pow] at h𝔭0
  replace h𝔭0 := (pow_eq_zero_iff'.mp h𝔭0).1
  obtain ⟨hp, hh, hIp, hm, hd⟩ := (hS 𝔭).1 h𝔭
  obtain ⟨m, hm'⟩ := exists_associated_resForm_elimForm_pow (d := d) hb hh hm hd.le
  have he : ψ (elimForm K b d 𝔭) = 0 := by
    obtain ⟨v, hv⟩ := hm'
    have h1 : ψ (elimForm K b d 𝔭 ^ m) = 0 := by rw [← hv, map_mul, h𝔭0, zero_mul]
    rw [map_pow] at h1
    exact (pow_eq_zero_iff'.mp h1).1
  have hle : elimIdeal K b d 𝔭 ≤ RingHom.ker ψ := by
    by_cases hf : (elimIdeal K b d 𝔭).IsPrincipal ∧ elimIdeal K b d 𝔭 ≠ ⊤
    · rw [← span_elimForm_of_isPrincipal hf.1, Ideal.span_le, Set.singleton_subset_iff]
      exact he
    · rw [elimForm, dite_eq_right hf, map_one] at he
      exact absurd he one_ne_zero
  obtain ⟨x, hx, hxz⟩ := (elimIdeal_le_ker_iff hh ψ).1 hle
  refine ⟨x, hx, fun p hpI ↦ ?_, ?_⟩
  · have h1 := hxz _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem (map C) (hIp hpI)))
    rw [eval₂_map] at h1
    rw [eval_map, ← h1]
    congr 1
    exact RingHom.ext fun k ↦ by simp [ψ, specEval]
  · have h1 := hxz _ (Ideal.mem_sup_right (Ideal.subset_span ⟨none, rfl⟩))
    rw [← h1, eval_pointForm, eval₂_genericForm, eval₂_genericForm]
    simp [ψ, specEval]

/-- **The resultant form of an ideal over a point, specialized**: if `I` contains the
`P_s X_t - P_t X_s` of the block `h` and the first form is linear in the block `h`, then
specializing the other forms gives `c (u · P)^n`. -/
theorem exists_specEval_resForm_eq_C_mul_pow (hb : Function.Surjective b)
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsWeightedHomogeneous (multiWeight b))
    (hdim : (hilbertPoly b I).totalDegree + 1 ≤ Nat.card (Option κ)) {h : ι}
    (hd : d none = Pi.single h 1) (P : σ → K) {s₀ : σ} (hs₀ : b s₀ = h) (hP₀ : P s₀ ≠ 0)
    (hPI : ∀ s t, b s = h → b t = h → C (P s) * X t - C (P t) * X s ∈ I) (φ : K →+* L)
    (y : GenericVar b (fun l : κ ↦ d (some l)) → L) :
    ∃ (c : L) (n : ℕ), specEval b φ y (resForm b K d I) =
      C c * pointForm b (d none) (φ ∘ P) ^ n := by
  classical
  obtain ⟨c, Z, hZ, hG⟩ := exists_specEval_resForm_eq (d := d) hb hI hdim φ y
  by_cases hc : c = 0
  · exact ⟨0, 0, by rw [hG, hc]; simp⟩
  have hmem : ∀ t, b t = h → Finsupp.single t 1 ∈ blockMonomials b (d none) := fun t ht ↦ by
    rw [hd, mem_blockMonomials_single]
    exact ⟨t, ht, rfl⟩
  have hM : ∀ m ∈ blockMonomials b (d none), ∃ t, b t = h ∧ m = Finsupp.single t 1 :=
    fun m hm ↦ by
      rw [hd, mem_blockMonomials_single] at hm
      exact hm
  set β : blockMonomials b (d none) → L := fun m ↦ ∏ s, (φ ∘ P) s ^ (m : σ →₀ ℕ) s
  have key : ∀ z ∈ Z, ∃ μ : L, pointForm b (d none) z = C μ * pointForm b (d none) (φ ∘ P) := by
    intro z hz
    set α : blockMonomials b (d none) → L := fun m ↦ ∏ s, z s ^ (m : σ →₀ ℕ) s
    have hα : α ≠ 0 := by
      obtain ⟨t, ht, hzt⟩ := hZ z hz h
      refine Function.ne_iff.2 ⟨⟨_, hmem t ht⟩, ?_⟩
      simpa [α, prod_pow_single_one] using hzt
    have hβ : β ≠ 0 := by
      refine Function.ne_iff.2 ⟨⟨_, hmem s₀ hs₀⟩, ?_⟩
      simpa [β, prod_pow_single_one] using hP₀
    have himp : ∀ a' : blockMonomials b (d none) → L,
        ∑ m, a' m * α m = 0 → ∑ m, a' m * β m = 0 := by
      intro a' ha'
      set a : GenericVar b (fun _ : Unit ↦ d none) → L := fun v ↦ a' v.2
      have hGa : eval a (specEval b φ y (resForm b K d I)) = 0 := by
        rw [hG, eval_mul, map_multiset_prod, Multiset.map_map]
        refine mul_eq_zero_of_right _ (Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨z, hz, ?_⟩))
        rw [Function.comp_apply, eval_pointForm_eq_sum]
        exact ha'
      obtain ⟨x, hx, hxI, hxa⟩ := exists_zero_of_eval_specEval_resForm hb hI hdim φ y a hGa
      have hprop : ∀ t, b t = h → x t * φ (P s₀) = x s₀ * φ (P t) := fun t ht ↦ by
        have := hxI _ (hPI s₀ t hs₀ ht)
        simp only [map_sub, map_mul, map_C, map_X, eval_C, eval_X] at this
        linear_combination this
      have hφ₀ : φ (P s₀) ≠ 0 := (map_ne_zero φ).2 hP₀
      have hx₀ : x s₀ ≠ 0 := by
        intro h0
        obtain ⟨t, ht, hxt⟩ := hx h
        have := hprop t ht
        rw [h0, zero_mul] at this
        exact hxt ((mul_eq_zero.1 this).resolve_right hφ₀)
      have hcoef : ∀ m : blockMonomials b (d none),
          ∏ s, x s ^ (m : σ →₀ ℕ) s = x s₀ / φ (P s₀) * β m := fun m ↦ by
        obtain ⟨t, ht, hmt⟩ := hM m m.2
        simp only [β, hmt, prod_pow_single_one, Function.comp_apply]
        rw [div_mul_eq_mul_div, eq_div_iff hφ₀, hprop t ht]
      rw [eval_pointForm_eq_sum] at hxa
      simp only [a, hcoef] at hxa
      have : x s₀ / φ (P s₀) * ∑ m, a' m * β m = 0 := by
        rw [Finset.mul_sum]
        rw [← hxa]
        refine Finset.sum_congr rfl fun m _ ↦ ?_
        ring
      exact (mul_eq_zero.1 this).resolve_left (div_ne_zero hx₀ hφ₀)
    obtain ⟨μ, hμ⟩ := exists_eq_smul_of_forall_sum_eq_zero hα himp
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      exact hβ (by rw [hμ, zero_smul])
    refine ⟨μ⁻¹, ?_⟩
    rw [pointForm_eq, pointForm_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    have := congrFun hμ m
    simp only [Pi.smul_apply, smul_eq_mul] at this
    change C (α m) * _ = C μ⁻¹ * (C (β m) * _)
    rw [this, ← mul_assoc, ← C_mul, inv_mul_cancel_left₀ hμ0]
  choose! μ hμ using key
  refine ⟨c * (Z.map μ).prod, Z.card, ?_⟩
  rw [hG, Multiset.map_congr rfl hμ, Multiset.prod_map_mul, Multiset.map_const',
    Multiset.prod_replicate]
  have hC : (Z.map fun x ↦ (C (μ x) : MvPolynomial (GenericVar b fun _ : Unit ↦ d none) L)).prod =
      C (Z.map μ).prod := by
    rw [map_multiset_prod, Multiset.map_map]
    rfl
  rw [hC, C_mul]
  ring

end Point

section Lift

universe u

variable {σ ι : Type u} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι}
  {K : Type u} [Field K] {κ : Type u} {d : Option κ → ι → ℕ}

variable (b d) in
/-- `u^{(0)} · P = ∑_m P^m u^{(0)}_m`: the first generic form at the point `P`. -/
noncomputable def firstPointForm {R : Type*} [CommRing R] (P : σ → R) :
    MvPolynomial (GenericVar b d) R :=
  ∑ m : blockMonomials b (d none), C (∏ s, P s ^ (m : σ →₀ ℕ) s) * X ⟨none, m⟩

variable (b d) in
/-- Specializing the coefficients of the first generic form at `a`. -/
noncomputable def firstSpec {R : Type*} [CommRing R]
    (a : GenericVar b (fun _ : Unit ↦ d none) → R) :
    MvPolynomial (GenericVar b d) R →ₐ[R] MvPolynomial (GenericVar b d) R :=
  aeval fun
    | ⟨none, m⟩ => C (a ⟨(), m⟩)
    | ⟨some l, m⟩ => X ⟨some l, m⟩

/-- The point `w` of `L^{K[d]}`, split into the first form and the others. -/
def firstPart {L : Type*} (w : GenericVar b d → L) : GenericVar b (fun _ : Unit ↦ d none) → L :=
  fun v ↦ w ⟨none, v.2⟩

/-- The point `w` of `L^{K[d]}`, split into the first form and the others. -/
def restPart {L : Type*} (w : GenericVar b d → L) :
    GenericVar b (fun l : κ ↦ d (some l)) → L :=
  fun v ↦ w ⟨some v.1, v.2⟩

theorem eval_specEval_firstPart {L : Type*} [Field L] (φ : K →+* L) (w : GenericVar b d → L)
    (F : MvPolynomial (GenericVar b d) K) :
    eval (firstPart w) (specEval b φ (restPart w) F) = eval w (map φ F) := by
  have h : (eval (firstPart w)).comp (specEval b φ (restPart w)) = (eval w).comp (map φ) := by
    refine ringHom_ext (fun k ↦ by simp [specEval]) fun v ↦ ?_
    rcases v with ⟨_ | l, m⟩ <;> simp [specEval, firstPart, restPart]
  exact RingHom.congr_fun h F

theorem eval_map_firstSpec {L : Type*} [Field L] (φ : K →+* L) (w : GenericVar b d → L)
    (a : GenericVar b (fun _ : Unit ↦ d none) → K) (F : MvPolynomial (GenericVar b d) K) :
    eval w (map φ (firstSpec b d a F)) =
      eval (fun v ↦ match v with
        | ⟨none, m⟩ => φ (a ⟨(), m⟩)
        | ⟨some l, m⟩ => w ⟨some l, m⟩) (map φ F) := by
  have h : (eval w).comp ((map φ).comp (firstSpec b d a).toRingHom) =
      (eval (fun v ↦ match v with
        | ⟨none, m⟩ => φ (a ⟨(), m⟩)
        | ⟨some l, m⟩ => w ⟨some l, m⟩)).comp (map φ) := by
    refine ringHom_ext (fun k ↦ by simp [firstSpec]) fun v ↦ ?_
    rcases v with ⟨_ | l, m⟩ <;> simp [firstSpec]
  exact RingHom.congr_fun h F

theorem eval_map_firstPointForm {L : Type*} [Field L] (φ : K →+* L) (w : GenericVar b d → L)
    (P : σ → K) :
    eval w (map φ (firstPointForm b d P)) = eval (firstPart w) (pointForm b (d none) (φ ∘ P)) := by
  rw [eval_pointForm_eq_sum, firstPointForm]
  simp [firstPart, map_prod, mul_comm]

theorem specEval_eq_aeval_map {L : Type*} [Field L] (φ : K →+* L)
    (y : GenericVar b (fun l : κ ↦ d (some l)) → L) (F : MvPolynomial (GenericVar b d) K) :
    specEval b φ y F = aeval (fun v : GenericVar b d ↦ match v with
      | ⟨none, m⟩ => (X ⟨(), m⟩ : MvPolynomial (GenericVar b fun _ : Unit ↦ d none) L)
      | ⟨some l, m⟩ => C (y ⟨l, m⟩)) (map φ F) := by
  have h : specEval b φ y = (aeval (fun v : GenericVar b d ↦ match v with
      | ⟨none, m⟩ => (X ⟨(), m⟩ : MvPolynomial (GenericVar b fun _ : Unit ↦ d none) L)
      | ⟨some l, m⟩ => C (y ⟨l, m⟩))).toRingHom.comp (map φ) := by
    refine ringHom_ext (fun k ↦ by simp [specEval]) fun v ↦ ?_
    rcases v with ⟨_ | l, m⟩ <;> simp [specEval]
  exact RingHom.congr_fun h F

/-- The specialized resultant form is homogeneous of the degree of `res_d(I)` in the first
form. -/
theorem isHomogeneous_specEval {L : Type*} [Field L] (φ : K →+* L)
    (y : GenericVar b (fun l : κ ↦ d (some l)) → L) {F : MvPolynomial (GenericVar b d) K}
    {D : ℕ} (hD : IsWeightedHomogeneous (groupWeight b d none) F D) :
    (specEval b φ y F).IsHomogeneous D := by
  rw [specEval_eq_aeval_map]
  refine (hD.map φ).aeval_of_algebra _ fun v ↦ ?_
  rcases v with ⟨_ | l, m⟩
  · simp only [groupWeight, ↓reduceIte]
    exact isWeightedHomogeneous_X L _ _
  · simp only [groupWeight, reduceCtorEq, ↓reduceIte]
    exact isWeightedHomogeneous_C _ _

theorem isHomogeneous_pointForm {L : Type*} [Field L] (e : ι → ℕ) (x : σ → L) :
    (pointForm b e x).IsHomogeneous 1 := by
  rw [pointForm_eq]
  exact IsHomogeneous.sum _ _ _ fun m _ ↦ (isHomogeneous_X L _).C_mul _

variable [Finite κ] [DecidableEq σ]

/-- **The resultant form of an ideal over a point**: if `I` contains the `P_s X_t - P_t X_s` of
the block `h`, the first form is linear in the block `h` and `res_d(I)` has degree `D` in it,
then `P_{s₀}^D res_d(I) = (u^{(0)} · P)^D g` with `g` the specialization of the first form at
`X_{s₀}`. -/
theorem C_mul_resForm_eq (hb : Function.Surjective b)
    {I : Ideal (MvPolynomial σ K)} (hI : I.IsWeightedHomogeneous (multiWeight b))
    (hdim : (hilbertPoly b I).totalDegree + 1 ≤ Nat.card (Option κ)) {h : ι}
    (hd : d none = Pi.single h 1) (P : σ → K) {s₀ : σ} (hs₀ : b s₀ = h) (hP₀ : P s₀ ≠ 0)
    (hPI : ∀ s t, b s = h → b t = h → C (P s) * X t - C (P t) * X s ∈ I) {D : ℕ}
    (hD : IsWeightedHomogeneous (groupWeight b d none) (resForm b K d I) D) :
    C (P s₀ ^ D) * resForm b K d I = firstPointForm b d P ^ D *
      firstSpec b d (fun v ↦ if (v.2 : σ →₀ ℕ) = Finsupp.single s₀ 1 then 1 else 0)
        (resForm b K d I) := by
  set L := AlgebraicClosure K
  set φ : K →+* L := algebraMap K L
  set F := resForm b K d I
  set a₀ : GenericVar b (fun _ : Unit ↦ d none) → K :=
    fun v ↦ if (v.2 : σ →₀ ℕ) = Finsupp.single s₀ 1 then 1 else 0
  have hmem : Finsupp.single s₀ 1 ∈ blockMonomials b (d none) := by
    rw [hd, mem_blockMonomials_single]
    exact ⟨s₀, hs₀, rfl⟩
  set Lφ := pointForm b (d none) (φ ∘ P)
  have hφ₀ : φ (P s₀) ≠ 0 := (map_ne_zero φ).2 hP₀
  have hL₀ : eval (fun v ↦ φ (a₀ v)) Lφ = φ (P s₀) := by
    rw [eval_pointForm_eq_sum, Finset.sum_eq_single ⟨_, hmem⟩]
    · simp [a₀, prod_pow_single_one]
    · rintro ⟨m, hm⟩ _ hne
      have : m ≠ Finsupp.single s₀ 1 := fun h' ↦ hne (Subtype.ext h')
      simp [a₀, this]
    · simp
  have hLne : Lφ ≠ 0 := fun h0 ↦ hφ₀ (by rw [← hL₀, h0, map_zero])
  apply map_injective φ φ.injective
  refine MvPolynomial.funext fun w ↦ ?_
  simp only [map_mul, map_pow, map_C, eval_C]
  rw [eval_map_firstSpec, eval_map_firstPointForm, ← eval_specEval_firstPart,
    ← eval_specEval_firstPart]
  obtain ⟨c, n, hcn⟩ := exists_specEval_resForm_eq_C_mul_pow hb hI hdim hd P hs₀ hP₀ hPI φ
    (restPart w)
  have hrest : restPart (L := L) (fun v : GenericVar b d ↦ match v with
      | ⟨none, m⟩ => φ (a₀ ⟨(), m⟩)
      | ⟨some l, m⟩ => w ⟨some l, m⟩) = restPart w := rfl
  have hfirst : firstPart (L := L) (fun v : GenericVar b d ↦ match v with
      | ⟨none, m⟩ => φ (a₀ ⟨(), m⟩)
      | ⟨some l, m⟩ => w ⟨some l, m⟩) = fun v ↦ φ (a₀ v) := rfl
  rw [hrest, hfirst, hcn]
  simp only [eval_mul, eval_pow, eval_C]
  rw [hL₀]
  by_cases hc : c = 0
  · simp [hc]
  have hnD : D = n := by
    have h1 := isHomogeneous_specEval φ (restPart w) hD
    rw [hcn] at h1
    have h2 : (C c * Lφ ^ n).IsHomogeneous n := by
      simpa using (isHomogeneous_C _ c).mul ((isHomogeneous_pointForm _ (φ ∘ P)).pow n)
    exact h1.inj_right h2 (mul_ne_zero (C_ne_zero.2 hc) (pow_ne_zero _ hLne))
  subst hnD
  ring

end Lift

end MvPolynomial
