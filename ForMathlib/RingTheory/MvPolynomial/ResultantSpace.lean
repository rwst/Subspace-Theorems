/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.LinearAlgebra.Matrix.IrreducibleDet
public import ForMathlib.RingTheory.MvPolynomial.ResultantDegree

-- Used only inside proofs.
import ForMathlib.RingTheory.MvPolynomial.MultiprojectiveDegree
import ForMathlib.RingTheory.MvPolynomial.ResultantSection
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.Polynomial.Basic

/-!
# The resultant forms of the whole space

G. Rémond's Lemma 3.7 (*Élimination multihomogène*, Chapter 5 of Nesterenko–Philippon (eds.),
*Introduction to algebraic independence theory*, LNM 1752 (2001)) for linear forms: the
resultant form of the zero ideal of `ℙ^{n_1} × ⋯ × ℙ^{n_q}` with `n_i` generic linear forms in
the block `i ≠ j` and `n_j + 1` in the block `j` is the determinant of the coefficients of the
forms of the block `j`. These are the resultant forms entering the height of `ℙ` (LNM 1752,
Ch. 7, §2.3).

Rémond compares zero sets over an algebraic closure. Here: the determinant `D` lies in the
eliminant ideal (Cramer's rule), so `res ∣ D^N` (`Module.exists_charForm_dvd_pow`); `D` is
prime (`Matrix.prime_det_mvPolynomialX`), and `res` has degree `1` in the coefficients of one
form of the block `j` (Prop. 3.4, with the iterated differences of the Hilbert polynomial
`∏_i C(T_i + n_i, n_i)` computed by Pascal's rule).

## Main statements

* `MvPolynomial.diffPoly_binomProd`: `Δ_{ε_{i_1}} ⋯ Δ_{ε_{i_s}} ∏_i C(T_i + c_i, c_i)`.
* `MvPolynomial.C_det_linMatrix_mul_X_mem`, `MvPolynomial.det_linMatrix_mem_elimIdeal`: Cramer's
  rule for generic linear forms.
* `MvPolynomial.associated_resForm_bot`: **Rémond's Lemma 3.7** for linear forms.
* `MvPolynomial.isUnit_resForm_bot`: the resultant form is a unit for all other distributions
  of the linear forms over the blocks.
-/

@[expose] public section

open scoped Finset Matrix

namespace MvPolynomial

section Binom

variable {ι : Type*}

theorem eval_binomPoly_eq (n : ℕ) (i : ι) (x : ι → ℚ) :
    eval x (binomPoly n i) = (n.factorial : ℚ)⁻¹ * (ascPochhammer ℚ n).eval (x i + 1) := by
  have hev : ∀ q : Polynomial ℚ, eval x (Polynomial.aeval (X i + 1) q) = q.eval (x i + 1) := by
    intro q
    induction q using Polynomial.induction_on' with
    | add p q hp hq => simp [hp, hq]
    | monomial n a => simp
  rw [binomPoly, map_mul, eval_C, hev]

@[simp]
theorem binomPoly_zero (i : ι) : binomPoly 0 i = 1 := by
  simp [binomPoly]

theorem shiftPoly_one (a : ι → ℕ) : shiftPoly a 1 = 1 :=
  map_one _

theorem shiftPoly_prod {τ : Type*} (a : ι → ℕ) (s : Finset τ) (P : τ → MvPolynomial ι ℚ) :
    shiftPoly a (∏ t ∈ s, P t) = ∏ t ∈ s, shiftPoly a (P t) :=
  map_prod (aeval fun i ↦ X i - C (a i : ℚ)) _ _

/-- **Pascal's rule** `C(T + n + 1, n + 1) - C(T + n, n + 1) = C(T + n, n)`. -/
theorem sub_shiftPoly_binomPoly_succ [DecidableEq ι] (n : ℕ) (i : ι) :
    binomPoly (n + 1) i - shiftPoly (Pi.single i 1) (binomPoly (n + 1) i) = binomPoly n i := by
  refine MvPolynomial.funext fun x ↦ ?_
  rw [map_sub, eval_shiftPoly, eval_binomPoly_eq, eval_binomPoly_eq, eval_binomPoly_eq]
  simp only [Pi.single_eq_same, Nat.cast_one, sub_add_cancel]
  rw [ascPochhammer_succ_eval, ascPochhammer_succ_left, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one,
    Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem shiftPoly_binomPoly_of_ne [DecidableEq ι] {i j : ι} (h : j ≠ i) (n : ℕ) :
    shiftPoly (Pi.single i 1) (binomPoly n j) = binomPoly n j := by
  refine MvPolynomial.funext fun x ↦ ?_
  rw [eval_shiftPoly, eval_binomPoly_eq, eval_binomPoly_eq, Pi.single_eq_of_ne h]
  simp

variable [Fintype ι]

/-- The polynomial `∏_i C(T_i + c_i, c_i)`. -/
noncomputable def binomProd (c : ι → ℕ) : MvPolynomial ι ℚ :=
  ∏ i, binomPoly (c i) i

@[simp]
theorem binomProd_zero : binomProd (0 : ι → ℕ) = 1 := by
  simp [binomProd]

theorem sub_shiftPoly_binomProd [DecidableEq ι] (c : ι → ℕ) (i : ι) :
    binomProd c - shiftPoly (Pi.single i 1) (binomProd c) =
      if c i = 0 then 0 else binomProd (Function.update c i (c i - 1)) := by
  have hsplit : ∀ c' : ι → ℕ, binomProd c' =
      binomPoly (c' i) i * ∏ j ∈ Finset.univ.erase i, binomPoly (c' j) j :=
    fun c' ↦ (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  have hrest : shiftPoly (Pi.single i 1) (∏ j ∈ Finset.univ.erase i, binomPoly (c j) j) =
      ∏ j ∈ Finset.univ.erase i, binomPoly (c j) j := by
    rw [shiftPoly_prod]
    exact Finset.prod_congr rfl fun j hj ↦ shiftPoly_binomPoly_of_ne (Finset.ne_of_mem_erase hj) _
  rw [hsplit c, shiftPoly_mul, hrest, ← sub_mul]
  split_ifs with h
  · rw [h, binomPoly_zero, shiftPoly_one, sub_self, zero_mul]
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero h
    rw [hsplit, Function.update_self, hn, sub_shiftPoly_binomPoly_succ, Nat.succ_sub_one]
    congr 1
    exact Finset.prod_congr rfl fun j hj ↦ by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- **Iterated differences of `∏_i C(T_i + c_i, c_i)`** along unit vectors: each `Δ_{ε_i}`
lowers `c_i` by one, and the result is `0` once some `c_i` would become negative. -/
theorem diffPoly_binomProd [DecidableEq ι] {κ : Type*} {d : κ → ι → ℕ} {τ : κ → ι}
    (hd : ∀ l, d l = Pi.single (τ l) 1) (s : Finset κ) (c : ι → ℕ) :
    diffPoly d s (binomProd c) =
      if ∀ i, #{l ∈ s | τ l = i} ≤ c i then binomProd (fun i ↦ c i - #{l ∈ s | τ l = i})
      else 0 := by
  classical
  induction s using Finset.induction_on generalizing c with
  | empty => simp
  | insert a s ha ih =>
    have hcnt : ∀ i, #{l ∈ insert a s | τ l = i} =
        #{l ∈ s | τ l = i} + if τ a = i then 1 else 0 := by
      intro i
      rw [Finset.filter_insert]
      split_ifs with h
      · rw [Finset.card_insert_of_notMem (by simp [ha])]
      · rfl
    rw [diffPoly_insert d ha, hd, sub_shiftPoly_binomProd]
    split_ifs with h0 h1 h1
    · rw [diffPoly_zero]
      have := h1 (τ a)
      rw [hcnt, h0] at this
      simp at this
    · rw [diffPoly_zero]
    · rw [ih]
      have key : ∀ i, (#{l ∈ s | τ l = i} ≤ Function.update c (τ a) (c (τ a) - 1) i ↔
          #{l ∈ insert a s | τ l = i} ≤ c i) ∧
          Function.update c (τ a) (c (τ a) - 1) i - #{l ∈ s | τ l = i} =
            c i - #{l ∈ insert a s | τ l = i} := fun i ↦ by
        rw [hcnt]
        by_cases hi : i = τ a
        · subst hi
          simp only [Function.update_self, ↓reduceIte]
          omega
        · simp [Function.update_of_ne hi, Ne.symm hi]
      rw [ite_eq_left_iff.mpr fun h ↦ absurd (fun i ↦ (key i).1.mpr (h1 i)) h]
      exact congrArg binomProd (_root_.funext fun i ↦ (key i).2)
    · rw [ih, ite_eq_right_iff]
      intro h
      refine absurd (fun i ↦ ?_) h1
      have key : #{l ∈ s | τ l = i} ≤ Function.update c (τ a) (c (τ a) - 1) i := h i
      rw [hcnt]
      by_cases hi : i = τ a
      · subst hi
        simp only [Function.update_self] at key
        simp only [↓reduceIte]
        omega
      · simpa [Function.update_of_ne hi, Ne.symm hi] using key

end Binom

section Rename

variable {σ τ R : Type*} [CommRing R]

/-- Renaming the variables injectively preserves primality. -/
theorem prime_rename_of_injective {f : σ → τ} (hf : Function.Injective f)
    {p : MvPolynomial σ R} (hp : Prime p) : Prime (rename f p) := by
  let e := Equiv.ofInjective f hf
  have : rename f p = rename ((↑) : Set.range f → τ) (rename e p) := by
    rw [rename_rename]
    rfl
  rw [this, prime_rename_iff]
  exact (MulEquiv.prime_iff (renameEquiv R e).toMulEquiv).mpr hp

end Rename

section Weighted

variable {σ R : Type*} [CommRing R] {w : σ → ℕ}

/-- **A determinant whose `i`-th row consists of forms of degree `r i`** is a form of degree
`∑ i, r i`. -/
theorem _root_.Matrix.isWeightedHomogeneous_det_of_row {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n (MvPolynomial σ R)) (r : n → ℕ)
    (h : ∀ i j, IsWeightedHomogeneous w (M i j) (r i)) :
    IsWeightedHomogeneous w M.det (∑ i, r i) := by
  rw [Matrix.det_apply]
  refine IsWeightedHomogeneous.sum _ _ _ fun τ _ ↦ ?_
  have := IsWeightedHomogeneous.prod Finset.univ (fun i ↦ M (τ i) i) (fun i ↦ r (τ i))
    fun i _ ↦ h _ _
  rw [Equiv.sum_comp τ r] at this
  rw [Units.smul_def]
  exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp
    (zsmul_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr this) _)

end Weighted

section Linear

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι}

/-- The monomials of multidegree `ε_j` are the variables of the `j`-th block. -/
theorem mem_blockMonomials_single {j : ι} {m : σ →₀ ℕ} :
    m ∈ blockMonomials b (Pi.single j 1) ↔ ∃ t, b t = j ∧ m = Finsupp.single t 1 := by
  classical
  rw [mem_blockMonomials]
  constructor
  · intro h
    have hsum : m.sum (fun _ n ↦ n) = 1 := by
      have h1 := congrArg (fun f ↦ ∑ i, f i) h
      simp only [weight_multiWeight_apply, Finset.sum_fiberwise, Finset.sum_pi_single',
        Finset.mem_univ, ↓reduceIte] at h1
      rwa [Finsupp.sum_fintype _ _ fun _ ↦ rfl]
    obtain ⟨t, rfl⟩ := (Finsupp.sum_eq_one_iff m).mp hsum
    refine ⟨t, ?_, rfl⟩
    have h2 := congrFun h (b t)
    rw [Finsupp.weight_single, one_smul, multiWeight, Pi.single_eq_same] at h2
    by_contra hne
    rw [Pi.single_eq_of_ne hne] at h2
    exact one_ne_zero h2
  · rintro ⟨t, rfl, rfl⟩
    rw [Finsupp.weight_single, one_smul, multiWeight]

variable {κ : Type*} {d : κ → ι → ℕ} {τ : κ → ι}

/-- The coefficient `u^{(l)}_s` of `X_s` in a generic linear form `U_l`. -/
noncomputable def linVar (hd : ∀ l, d l = Pi.single (τ l) 1) (l : κ) (s : σ) (hs : b s = τ l) :
    GenericVar b d :=
  ⟨l, ⟨Finsupp.single s 1, by rw [hd, mem_blockMonomials_single]; exact ⟨s, hs, rfl⟩⟩⟩

variable (K : Type*) [CommRing K]

/-- A generic linear form `U_l = ∑_t u^{(l)}_t X_t` in the variables of the `j`-th block. -/
theorem genericForm_eq_sum (hd : ∀ l, d l = Pi.single (τ l) 1) {j : ι} {l : κ} (hl : τ l = j) :
    genericForm K b d l =
      ∑ t : {s // b s = j}, C (X (linVar hd l (t : σ) (t.2.trans hl.symm))) * X (t : σ) := by
  rw [genericForm]
  symm
  refine Fintype.sum_bijective
    (fun t : {s // b s = j} ↦ (⟨Finsupp.single (t : σ) 1, by
      rw [hd, hl, mem_blockMonomials_single]; exact ⟨t, t.2, rfl⟩⟩ : blockMonomials b (d l)))
    ⟨fun t t' h ↦ ?_, fun m ↦ ?_⟩ _ _ fun t ↦ ?_
  · exact Subtype.ext (Finsupp.single_left_injective one_ne_zero (congrArg Subtype.val h))
  · have hm : (m : σ →₀ ℕ) ∈ blockMonomials b (Pi.single j 1) := by
      rw [← hl, ← hd]
      exact m.2
    rw [mem_blockMonomials_single] at hm
    obtain ⟨t, ht, hmt⟩ := hm
    exact ⟨⟨t, ht⟩, Subtype.ext hmt.symm⟩
  · rw [C_mul_X_eq_monomial]
    rfl

variable [DecidableEq σ]

/-- The matrix `(u^{(e s)}_t)_{s, t}` of the generic linear forms `U_l` with `τ l = j`, indexed
by the variables of the `j`-th block through `e`. -/
noncomputable def linMatrix (hd : ∀ l, d l = Pi.single (τ l) 1) {j : ι}
    (e : {s // b s = j} ≃ {l // τ l = j}) :
    Matrix {s // b s = j} {s // b s = j} (MvPolynomial (GenericVar b d) K) :=
  Matrix.of fun s t ↦ X (linVar hd (e s) (t : σ) (t.2.trans (e s).2.symm))

/-- **Cramer's rule**: `det (u^{(l)}_t) X_t` is a combination of the generic linear forms. -/
theorem C_det_linMatrix_mul_X_mem (hd : ∀ l, d l = Pi.single (τ l) 1) {j : ι}
    (e : {s // b s = j} ≃ {l // τ l = j}) (t : {s // b s = j}) :
    C (linMatrix K hd e).det * X (t : σ) ∈ Ideal.span (Set.range (genericForm K b d)) := by
  classical
  let A := (linMatrix K hd e).map
    (C : MvPolynomial (GenericVar b d) K →+* MvPolynomial σ (MvPolynomial (GenericVar b d) K))
  let x : {s // b s = j} → MvPolynomial σ (MvPolynomial (GenericVar b d) K) := fun t ↦ X t
  have hU : ∀ s, (A *ᵥ x) s = genericForm K b d (e s) := fun s ↦ by
    rw [genericForm_eq_sum K hd (e s).2]
    simp [A, x, Matrix.mulVec, dotProduct, linMatrix]
  have key : (A.adjugate *ᵥ (A *ᵥ x)) t = C (linMatrix K hd e).det * X (t : σ) := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
      Pi.smul_apply, smul_eq_mul, RingHom.map_det]
    rfl
  rw [← key, show A *ᵥ x = fun s ↦ genericForm K b d (e s) from _root_.funext hU]
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun s _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨e s, rfl⟩)

/-- `det (u^{(l)}_t)` lies in the eliminant ideal of every ideal. -/
theorem det_linMatrix_mem_elimIdeal (hd : ∀ l, d l = Pi.single (τ l) 1) {j : ι}
    (e : {s // b s = j} ≃ {l // τ l = j}) (I : Ideal (MvPolynomial σ K)) :
    (linMatrix K hd e).det ∈ elimIdeal K b d I := by
  classical
  set D := (linMatrix K hd e).det
  rw [mem_elimIdeal]
  refine ⟨1, fun g hg ↦ ?_⟩
  rw [pow_one] at hg
  have hmem : g * C D ∈ irrelevantIdeal _ b * Ideal.span {C D} :=
    Ideal.mul_mem_mul hg (Ideal.mem_span_singleton_self _)
  refine (?_ : irrelevantIdeal _ b * Ideal.span {C D} ≤ genericIdeal K b d I) hmem
  rw [irrelevantIdeal, Ideal.span_mul_span, Ideal.span_le]
  rintro _ ⟨_, ⟨c, hc, rfl⟩, _, hD, rfl⟩
  rw [Set.mem_singleton_iff] at hD
  subst hD
  have hw := congrFun (mem_blockMonomials.mp (Finset.mem_coe.mp hc)) j
  rw [weight_multiWeight_apply, Pi.one_apply] at hw
  obtain ⟨t, ht, hct⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (by omega : ∑ s with b s = j, c s ≠ 0)
  have hle : Finsupp.single t 1 ≤ c := by
    rw [Finsupp.single_le_iff]
    omega
  have hc' : monomial c (1 : MvPolynomial (GenericVar b d) K) =
      monomial (c - Finsupp.single t 1) 1 * X t := by
    rw [X, monomial_mul_monomial, one_mul, tsub_add_cancel_of_le hle]
  change monomial c 1 * C D ∈ _
  rw [hc', mul_assoc, mul_comm (X t)]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_sup_right
    (C_det_linMatrix_mul_X_mem K hd e ⟨t, (Finset.mem_filter.mp ht).2⟩))

/-- `det (u^{(e s)}_t)` is a form of degree `1` in the coefficients of each `U_l`, `τ l = j`. -/
theorem isWeightedHomogeneous_det_linMatrix (hd : ∀ l, d l = Pi.single (τ l) 1) {j : ι}
    (e : {s // b s = j} ≃ {l // τ l = j}) (s₀ : {s // b s = j}) :
    IsWeightedHomogeneous (groupWeight b d (e s₀ : κ)) (linMatrix K hd e).det 1 := by
  classical
  have := Matrix.isWeightedHomogeneous_det_of_row (w := groupWeight b d (e s₀ : κ))
    (linMatrix K hd e) (fun s ↦ if s = s₀ then 1 else 0) fun s t ↦ ?_
  · simpa using this
  · rw [show linMatrix K hd e s t = X (linVar hd (e s) (t : σ) (t.2.trans (e s).2.symm)) from rfl]
    convert isWeightedHomogeneous_X K (groupWeight b d (e s₀ : κ)) _ using 1
    unfold groupWeight linVar
    simp only [Subtype.val_inj, e.injective.eq_iff]

end Linear

section Prime

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [DecidableEq ι] [DecidableEq σ] {b : σ → ι}
  {κ : Type*} {d : κ → ι → ℕ} {τ : κ → ι} {K : Type*} [Field K]

/-- `det (u^{(e s)}_t)` is prime. -/
theorem prime_det_linMatrix (hd : ∀ l, d l = Pi.single (τ l) 1) {j : ι}
    (e : {s // b s = j} ≃ {l // τ l = j}) [Nonempty {s // b s = j}] :
    Prime (linMatrix K hd e).det := by
  let φ : {s // b s = j} × {s // b s = j} → GenericVar b d := fun p ↦
    linVar hd (e p.1) (p.2 : σ) (p.2.2.trans (e p.1).2.symm)
  have hφ : Function.Injective φ := by
    rintro ⟨s, t⟩ ⟨s', t'⟩ h
    simp only [φ, linVar, Sigma.mk.inj_iff] at h
    obtain ⟨h1, h2⟩ := h
    obtain rfl : s = s' := e.injective (Subtype.ext h1)
    have := congrArg Subtype.val (eq_of_heq h2)
    exact Prod.ext rfl (Subtype.ext (Finsupp.single_left_injective one_ne_zero this))
  have : (linMatrix K hd e).det = rename φ (Matrix.mvPolynomialX _ _ K).det := by
    rw [AlgHom.map_det]
    congr 1
    ext s t
    simp [linMatrix, φ]
  rw [this]
  exact prime_rename_of_injective hφ Matrix.prime_det_mvPolynomialX

end Prime

section Main

universe u

variable {σ ι : Type u} [Fintype σ] [Fintype ι] [DecidableEq ι] [DecidableEq σ] {b : σ → ι}
  {K : Type u} [Field K] {κ : Type u} [Fintype κ] {d : κ → ι → ℕ} {τ : κ → ι}

/-- **Rémond's Lemma 3.7 for linear forms** (LNM 1752, Ch. 5): let all generic forms be
linear, `U_l` in the `τ l`-th block, with `n_i` forms in the block `i ≠ j` of `n_i + 1`
variables and `n_j + 1` forms in the block `j`. Then the resultant form of the whole space
`ℙ^{n_1} × ⋯ × ℙ^{n_q}` is the determinant of the coefficients of the forms of the block
`j`. -/
theorem associated_resForm_bot (hb : Function.Surjective b) (hd : ∀ l, d l = Pi.single (τ l) 1)
    {j : ι} (e : {s // b s = j} ≃ {l // τ l = j})
    (hcard : ∀ i ≠ j, #{l | τ l = i} + 1 = #{s | b s = i}) :
    Associated (resForm b K d ⊥) (linMatrix K hd e).det := by
  classical
  obtain ⟨s₀, hs₀⟩ := hb j
  let t₀ : {s // b s = j} := ⟨s₀, hs₀⟩
  have : Nonempty {s // b s = j} := ⟨t₀⟩
  set l₀ : κ := (e t₀ : κ)
  have hl₀ : τ l₀ = j := (e t₀).2
  have hcardj : #{l | τ l = j} = #{s | b s = j} := by
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    exact (Fintype.card_congr e).symm
  have hpos : 1 ≤ #{s | b s = j} := Finset.card_pos.mpr ⟨s₀, by simp [hs₀]⟩
  have hcnt : ∀ i, #{l ∈ Finset.univ.erase l₀ | τ l = i} = #{s | b s = i} - 1 := by
    intro i
    rw [Finset.filter_erase]
    by_cases hi : i = j
    · subst hi
      rw [Finset.card_erase_of_mem (by simp [hl₀]), hcardj]
    · rw [Finset.erase_eq_of_notMem (by simp [hl₀, Ne.symm hi]), ← hcard i hi]
      omega
  have hdeg : (hilbertPoly (K := K) b ⊥).totalDegree + 1 ≤ Fintype.card κ := by
    rw [hilbertPoly_bot hb]
    have h1 : (blockCountPoly b).totalDegree ≤ ∑ i, (#{s | b s = i} - 1) :=
      (totalDegree_finsetProd _ _).trans
        (Finset.sum_le_sum fun i _ ↦ totalDegree_binomPoly_le _ _)
    have h2 : Fintype.card κ = ∑ i, #{l | τ l = i} := by
      rw [← Finset.card_univ]
      exact Finset.card_eq_sum_card_fiberwise fun _ _ ↦ Finset.mem_univ _
    have h3 : ∑ i, #{l | τ l = i} = ∑ i, (#{s | b s = i} - 1) + 1 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
        ← Finset.add_sum_erase _ _ (Finset.mem_univ j),
        Finset.sum_congr rfl fun i hi ↦ (show #{l | τ l = i} = #{s | b s = i} - 1 by
          have := hcard i (Finset.ne_of_mem_erase hi); omega), hcardj]
      omega
    omega
  -- The degree in the coefficients of `U_{l₀}` is `1` (Prop. 3.4).
  obtain ⟨n₀, hn₀, hhom⟩ := exists_isWeightedHomogeneous_resForm (K := K) (d := d) hb l₀
    (isWeightedHomogeneous_bot _) hdeg
  have hcond : ∀ i, #{l ∈ Finset.univ.erase l₀ | τ l = i} ≤ #{s | b s = i} - 1 :=
    fun i ↦ (hcnt i).le
  have hB : blockCountPoly b = binomProd (fun i ↦ #{s | b s = i} - 1) := rfl
  rw [hilbertPoly_bot hb, hB, diffPoly_binomProd hd,
    ite_eq_left_iff.mpr fun h ↦ absurd hcond h] at hn₀
  simp only [hcnt, Nat.sub_self] at hn₀
  rw [show (fun _ : ι ↦ (0 : ℕ)) = 0 from rfl, binomProd_zero,
    AddMonoidAlgebra.coeff_one_zero] at hn₀
  have hn1 : n₀ = 1 := by exact_mod_cast hn₀
  -- `res` divides a power of the prime `det`.
  obtain ⟨k₀, hk₀⟩ := exists_elimIdeal_le_annihilator (b := b) (K := K) (d := d)
    (⊥ : Ideal (MvPolynomial σ K))
  have hdim : (hilbertPoly (K := K) b ⊥).totalDegree + 1 ≤ Nat.card κ := by
    rwa [Nat.card_eq_fintype_card]
  obtain ⟨⟨k₁, hk₁⟩, -⟩ := associated_resForm_prod (d := d) hb (isWeightedHomogeneous_bot _) hdim
  obtain ⟨N, hN⟩ := Module.exists_charForm_dvd_pow
    (hk₀ (k₀ ⊔ k₁) le_sup_left (det_linMatrix_mem_elimIdeal K hd e ⊥))
  have hdvd := (hk₁ (k₀ ⊔ k₁) le_sup_right).symm.dvd.trans hN
  obtain ⟨m, -, hm⟩ := (dvd_prime_pow (prime_det_linMatrix hd e) N).mp hdvd
  -- Comparing degrees in `u^{(l₀)}` gives `m = 1`.
  have hres := hm.isWeightedHomogeneous ((isWeightedHomogeneous_det_linMatrix K hd e t₀).pow m)
  have h0 := resForm_ne_zero (d := d) (K := K) hb (isWeightedHomogeneous_bot _) hdim
  have := hhom.inj_right h0 hres
  rw [hn1, smul_eq_mul, mul_one] at this
  rwa [← this, pow_one] at hm

omit [DecidableEq σ] in
/-- **Rémond's Lemma 3.7, degenerate case**: with linear forms, if for every form `U_{l₀}` some
block `i` of `n_i + 1` variables still carries at least `n_i + 1` of the other forms, the
resultant form of the whole space is a unit. -/
theorem isUnit_resForm_bot [DecidableEq κ] (hb : Function.Surjective b)
    (hd : ∀ l, d l = Pi.single (τ l) 1)
    (hκ : ∑ i, (#{s | b s = i} - 1) + 1 ≤ Fintype.card κ)
    (h : ∀ l₀, ∃ i, #{s | b s = i} ≤ #{l ∈ Finset.univ.erase l₀ | τ l = i}) :
    IsUnit (resForm b K d ⊥) := by
  classical
  have hdeg : (hilbertPoly (K := K) b ⊥).totalDegree + 1 ≤ Fintype.card κ := by
    rw [hilbertPoly_bot hb]
    have := (totalDegree_finsetProd (Finset.univ : Finset ι) _).trans
      (Finset.sum_le_sum fun i _ ↦ totalDegree_binomPoly_le (#{s | b s = i} - 1) i)
    exact (Nat.add_le_add_right this 1).trans hκ
  have hzero : ∀ l₀, IsWeightedHomogeneous (groupWeight b d l₀) (resForm b K d ⊥) 0 := by
    intro l₀
    obtain ⟨n₀, hn₀, hhom⟩ := exists_isWeightedHomogeneous_resForm (K := K) (d := d) hb l₀
      (isWeightedHomogeneous_bot _) hdeg
    obtain ⟨i, hi⟩ := h l₀
    have hpos : 1 ≤ #{s | b s = i} := by
      obtain ⟨s, hs⟩ := hb i
      exact Finset.card_pos.mpr ⟨s, by simp [hs]⟩
    have hB : blockCountPoly b = binomProd (fun i ↦ #{s | b s = i} - 1) := rfl
    rw [hilbertPoly_bot hb, hB, diffPoly_binomProd hd,
      ite_eq_right_iff.mpr fun h ↦ absurd (h i) (by omega)] at hn₀
    have hn : (n₀ : ℚ) = 0 := by simpa using hn₀
    rwa [show n₀ = 0 by exact_mod_cast hn] at hhom
  have h0 : resForm b K d ⊥ ≠ 0 := resForm_ne_zero (d := d) (K := K) hb
    (isWeightedHomogeneous_bot _) (by rwa [Nat.card_eq_fintype_card])
  have hhom := isHomogeneous_of_forall_groupWeight hzero
  simp only [Finset.sum_const_zero] at hhom
  have hC := totalDegree_eq_zero_iff_eq_C.mp (hhom.totalDegree h0)
  rw [hC] at h0 ⊢
  exact (Ne.isUnit fun h ↦ h0 (by rw [h, map_zero])).map C

end Main

end MvPolynomial
