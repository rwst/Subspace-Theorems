/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import FaltingsWustholz1994.LinearForms
public import STForMathlib.NumberTheory.Height.Veronese

-- Used only inside proofs.
import DiophantineApproximation.PlacesOverFinite

/-!
# Theorem 9.3 of Faltings–Wüstholz for one degree `t`

G. Faltings and G. Wüstholz, *Diophantine approximations on projective spaces*, Invent. Math.
**116** (1994), Theorem 9.3.

At every place `v` of `S`, forms `f_{v,k}` over `F` of degrees `d_{v,k}` (`k ∈ B v`) carry
exponents `c_{v,k}`, and the system is

```text
‖f_{v,k}(x)‖_v / ‖x‖_v^{d_{v,k}} ≤ H(x) ^ (-c_{v,k})      (v ∈ S, k ∈ B v).
```

Fix `t ≥ 1` and an ideal `I` of `K[X]`. The products `g = X^μ ∏_k f_k^{j_k}` of degree `t` carry
exponents `∑_k j_k c_k`; FW's filtration on `R_t` is spanned by them. As linear forms on the
Veronese space `F^{R_t}`, measured with exponent `(∑_k j_k c_k) / t`, they give the weight
`W(U)` of FW.2 for `U = U_t(I) = I_t^⊥ ⊆ K^{R_t}`, the dual of `(R/I)_t`. So `dim U < W(U)` is
FW's `∑_v W_v((R/I)_t) > t · dim (R/I)_t` for this one `t`, without the limit of §3.

**The theorem** (`NumberField.exists_finset_isHomogeneous_notMem`): if `2 ≤ dim U` and
`dim U < W(U)`, finitely many forms `q` of degree `t`, none in `I`, cover the solutions in
`V(I)(K)`. For a prime `I` their product is one form not in `I` vanishing at all solutions: the
solutions are not Zariski-dense in `V(I)` (`NumberField.exists_notMem_of_isPrime`).

The proof is the Veronese map `x ↦ y = x^{(t)}`. Since `‖y‖_v = ‖x‖_v^t` and `H(y) = H(x)^t`
(`STForMathlib/NumberTheory/Height/Veronese.lean`), a solution `x` gives a solution `y ∈ U` of
FW.3's linear system (`NumberField.isSystemSolution_veronese`). One step of FW.3
(`NumberField.exists_finset_submodule_lt_of_lt_maxWeight`) puts `y` into finitely many proper
subspaces of `U`. Each lies in the kernel of a linear form `λ` not vanishing on `U`, and `λ` is
a form `q` of degree `t` with `q(x) = λ(y)` (`MvPolynomial.eval_ofDual`). It is not in `I`, as
every form of degree `t` in `I` vanishes on `U`.

## Main definitions

* `NumberField.IsFormSystemSolution`: FW's system (1) for forms of any degrees.
* `NumberField.productPoly`, `NumberField.productIndex`, `NumberField.productExp`: the products
  of degree `t`, their indices and their exponents.
* `NumberField.formAnnihilator`: `U_t(I) = I_t^⊥`.
* `NumberField.veroneseWeight`: the weight of `U` for the products.

## Main results

* `NumberField.div_iSup_veronese_le`: the local bound of a product at the Veronese image.
* `NumberField.isSystemSolution_veronese`: **the Veronese transfer**.
* `NumberField.finrank_formAnnihilator`: `dim U_t(I) = dim (R/I)_t`.
* `NumberField.exists_finset_isHomogeneous_notMem`: **FW Theorem 9.3 for one `t`**.
* `NumberField.exists_notMem_of_isPrime`: the solutions are not Zariski-dense in `V(I)`.

## Implementation notes

⚠ **`2 ≤ dim U` is needed** (Finding 10 of the README): for `dim (R/I)_t = 1` the theorem is
false, and so is FW's for a zero-dimensional `X`. It holds once `dim V(I) ≥ 1`.

**`dim U_t(I) = dim (R/I)_t`** (`NumberField.finrank_formAnnihilator`): `U_t(I)` is the
annihilator of the forms of degree `t` in `I` under the coefficient pairing
(`MvPolynomial.homogeneousEquivDual`), and `(R/I)_t` is the forms of degree `t` modulo those in
`I`. So the hypotheses of the theorems may be read on `(R/I)_t`.

⚠ **No degree condition on the forms.** The exponents `j_k` range over `0, …, t`, which bounds
the family; forms of degree `0` only add products that a basis never needs. The ideal `I` need
not be homogeneous: only its forms of degree `t` enter, and `V(I)(K)` is the set of nonzero
`x ∈ K^ι` with `q(x) = 0` for all `q ∈ I`.

This is milestone FW.4 of `FaltingsWustholz1994/README.md`.
-/

@[expose] public section

open Finset Height Module Module.Dual MvPolynomial

namespace NumberField

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {ι κ : Type*} [Fintype ι] [Fintype κ]

section Products

/-- **A product of degree `t`**: `X^μ ∏_{k ∈ B} f_k^{j_k}` for the index `(j, μ)`. -/
noncomputable def productPoly (B : Finset κ) (f : κ → MvPolynomial ι F) (p : (κ → ℕ) × (ι → ℕ)) :
    MvPolynomial ι F :=
  (∏ j, X j ^ p.2 j) * ∏ k ∈ B, f k ^ p.1 k

variable (ι) in
/-- **The indices of the products of degree `t`**: `j_k, μ_j ≤ t` with
`∑_k j_k d_k + ∑_j μ_j = t`. -/
noncomputable def productIndex (B : Finset κ) (d : κ → ℕ) (t : ℕ) :
    Finset ((κ → ℕ) × (ι → ℕ)) := by
  classical
  exact Finset.filter (fun p : (κ → ℕ) × (ι → ℕ) ↦ ∑ k ∈ B, p.1 k * d k + ∑ j, p.2 j = t)
    ((Fintype.piFinset fun _ : κ ↦ range (t + 1)) ×ˢ
      (Fintype.piFinset fun _ : ι ↦ range (t + 1)))

/-- **The exponent of a product**, `(∑_k j_k c_k) / t` in the normalization of the Veronese
space. -/
noncomputable def productExp (B : Finset κ) (c : κ → ℝ) (t : ℕ) (p : (κ → ℕ) × (ι → ℕ)) : ℝ :=
  (∑ k ∈ B, (p.1 k : ℝ) * c k) / t

theorem degree_of_mem_productIndex {B : Finset κ} {d : κ → ℕ} {t : ℕ}
    {p : (κ → ℕ) × (ι → ℕ)} (hp : p ∈ productIndex ι B d t) :
    ∑ k ∈ B, p.1 k * d k + ∑ j, p.2 j = t := by
  classical
  unfold productIndex at hp
  exact (Finset.mem_filter.1 hp).2

/-- A product of an index of degree `t` is a form of degree `t`. -/
theorem isHomogeneous_productPoly {B : Finset κ} {f : κ → MvPolynomial ι F} {d : κ → ℕ}
    (hf : ∀ k ∈ B, (f k).IsHomogeneous (d k)) {t : ℕ} {p : (κ → ℕ) × (ι → ℕ)}
    (hp : p ∈ productIndex ι B d t) : (productPoly B f p).IsHomogeneous t := by
  have h := (IsHomogeneous.prod (univ : Finset ι) (fun j ↦ (X j : MvPolynomial ι F) ^ p.2 j)
    p.2 fun j _ ↦ isHomogeneous_X_pow j (p.2 j)).mul
    (IsHomogeneous.prod B (fun k ↦ f k ^ p.1 k) (fun k ↦ d k * p.1 k)
      fun k hk ↦ (hf k hk).pow (p.1 k))
  rw [← degree_of_mem_productIndex hp, add_comm,
    Finset.sum_congr rfl fun k _ ↦ Nat.mul_comm (p.1 k) (d k)]
  exact h

end Products

/-- **FW's system (1) for forms of any degrees**: at every place of `S` and for every form
`f_{v,k}`, `k ∈ B v`, of degree `d_{v,k}`, `‖f_{v,k}(x)‖_v / ‖x‖_v^{d_{v,k}} ≤ H(x)^{-c_{v,k}}`. -/
def IsFormSystemSolution [NumberField K] (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (B : AbsoluteValue K ℝ → Finset κ)
    (f : AbsoluteValue K ℝ → κ → MvPolynomial ι F) (d : AbsoluteValue K ℝ → κ → ℕ)
    (c : AbsoluteValue K ℝ → κ → ℝ) (x : ι → K) : Prop :=
  (∀ v ∈ Sinf, ∀ k ∈ B v.1, w v.1 (eval (fun j ↦ algebraMap K F (x j)) (f v.1 k)) /
      (⨆ j, v (x j)) ^ d v.1 k ≤ mulHeight x ^ (-c v.1 k)) ∧
  (∀ v ∈ Sfin, ∀ k ∈ B v.1, w v.1 (eval (fun j ↦ algebraMap K F (x j)) (f v.1 k)) /
      (⨆ j, v (x j)) ^ d v.1 k ≤ mulHeight x ^ (-c v.1 k))

/-- **The local bound at the Veronese image**: if `x ≠ 0` satisfies the inequalities of the
forms `f_k` at `u`, a product `g` of degree `t` satisfies
`‖g(x)‖_u / ‖x^{(t)}‖_u ≤ (H^t)^{-(∑ j_k c_k)/t}`. -/
theorem div_iSup_veronese_le {u : AbsoluteValue K ℝ} {W : AbsoluteValue F ℝ}
    (hW : W.LiesOver u) {B : Finset κ} {f : κ → MvPolynomial ι F} {d : κ → ℕ}
    (hf : ∀ k ∈ B, (f k).IsHomogeneous (d k)) {c : κ → ℝ} {t : ℕ} (ht : t ≠ 0) {x : ι → K}
    (hx : x ≠ 0) {H : ℝ} (hH : 1 ≤ H)
    (hloc : ∀ k ∈ B, W (eval (fun j ↦ algebraMap K F (x j)) (f k)) / (⨆ j, u (x j)) ^ d k ≤
      H ^ (-c k))
    {p : (κ → ℕ) × (ι → ℕ)} (hp : p ∈ productIndex ι B d t) :
    W (coeffForm t (productPoly B f p) fun μ ↦ algebraMap K F (veronese t x μ)) /
      ⨆ μ, u (veronese t x μ) ≤ (H ^ t) ^ (-productExp B c t p) := by
  have : Nonempty ι := (Function.ne_iff.mp hx).nonempty
  have hH0 : 0 < H := lt_of_lt_of_le zero_lt_one hH
  set N := ⨆ j, u (x j) with hN
  have hN0 : 0 < N := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hx
    exact (u.pos hj).trans_le (le_ciSup (f := fun j ↦ u (x j)) (Finite.bddAbove_range _) j)
  have hcomp : (fun μ ↦ algebraMap K F (veronese t x μ)) =
      veronese t fun j ↦ algebraMap K F (x j) :=
    (veronese_comp (algebraMap K F) t x).symm
  rw [hcomp, coeffForm_veronese (isHomogeneous_productPoly hf hp), u.iSup_veronese]
  simp only [productPoly, map_mul, map_prod, map_pow, eval_X,
    AbsoluteValue.apply_algebraMap_of_liesOver (v := u) W]
  -- split `N^t` along `t = ∑ μ_j + ∑ j_k d_k`
  have hNt : N ^ t = (∏ j, N ^ p.2 j) * ∏ k ∈ B, (N ^ d k) ^ p.1 k := by
    rw [Finset.prod_pow_eq_pow_sum, ← degree_of_mem_productIndex hp, pow_add, mul_comm]
    congr 1
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun k _ ↦ by rw [← pow_mul, mul_comm]
  rw [hNt, mul_div_mul_comm, ← Finset.prod_div_distrib, ← Finset.prod_div_distrib]
  simp only [← div_pow]
  have h1 : ∏ j, (u (x j) / N) ^ p.2 j ≤ 1 :=
    Finset.prod_le_one₀ (fun j _ ↦ pow_nonneg (div_nonneg (u.nonneg _) hN0.le) _) fun j _ ↦
      pow_le_one₀ (div_nonneg (u.nonneg _) hN0.le) ((div_le_one hN0).2
        (le_ciSup (f := fun j ↦ u (x j)) (Finite.bddAbove_range _) j))
  have h2 : ∏ k ∈ B, (W (eval (fun j ↦ algebraMap K F (x j)) (f k)) / N ^ d k) ^ p.1 k ≤
      H ^ (-∑ k ∈ B, (p.1 k : ℝ) * c k) := by
    rw [← Finset.sum_neg_distrib, Real.rpow_sum_of_pos hH0]
    refine Finset.prod_le_prod₀ (fun k _ ↦ pow_nonneg (div_nonneg (W.nonneg _)
      (pow_nonneg hN0.le _)) _) fun k hk ↦ ?_
    rw [show -((p.1 k : ℝ) * c k) = -c k * (p.1 k : ℕ) by ring, Real.rpow_mul_natCast hH0.le]
    exact pow_le_pow_left₀ (div_nonneg (W.nonneg _) (pow_nonneg hN0.le _)) (hloc k hk) _
  have hexp : (H ^ t) ^ (-productExp B c t p) = H ^ (-∑ k ∈ B, (p.1 k : ℝ) * c k) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hH0.le, productExp]
    congr 1
    field_simp
  rw [hexp]
  calc (∏ j, (u (x j) / N) ^ p.2 j) *
        ∏ k ∈ B, (W (eval (fun j ↦ algebraMap K F (x j)) (f k)) / N ^ d k) ^ p.1 k
      ≤ 1 * H ^ (-∑ k ∈ B, (p.1 k : ℝ) * c k) :=
        mul_le_mul h1 h2 (Finset.prod_nonneg fun k _ ↦ pow_nonneg (div_nonneg (W.nonneg _)
          (pow_nonneg hN0.le _)) _) zero_le_one
    _ = _ := one_mul _

variable [NumberField K]

/-- **The Veronese transfer**: a nonzero solution `x` of the system of forms gives the solution
`x^{(t)}` of FW.3's linear system of the products of degree `t`. -/
theorem isSystemSolution_veronese (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwI : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwF : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (B : AbsoluteValue K ℝ → Finset κ) (f : AbsoluteValue K ℝ → κ → MvPolynomial ι F)
    (d : AbsoluteValue K ℝ → κ → ℕ) (hf : ∀ v, ∀ k ∈ B v, (f v k).IsHomogeneous (d v k))
    (c : AbsoluteValue K ℝ → κ → ℝ) {t : ℕ} (ht : t ≠ 0) {x : ι → K} (hx : x ≠ 0)
    (hsol : IsFormSystemSolution Sinf Sfin w B f d c x) :
    IsSystemSolution Sinf Sfin w (fun v ↦ productIndex ι (B v) (d v) t)
      (fun v p ↦ coeffForm t (productPoly (B v) (f v) p)) (fun v ↦ productExp (B v) (c v) t)
      (veronese t x) := by
  rw [IsSystemSolution, mulHeight_veronese t hx]
  exact ⟨fun v hv p hp ↦ div_iSup_veronese_le (hwI v hv) (hf v.1) ht hx (one_le_mulHeight x)
      (hsol.1 v hv) hp,
    fun v hv p hp ↦ div_iSup_veronese_le (hwF v hv) (hf v.1) ht hx (one_le_mulHeight x)
      (hsol.2 v hv) hp⟩

omit [Fintype κ] [NumberField K] in
variable (K) in
/-- **`U_t(I) = I_t^⊥`**: the points of the Veronese space on which the forms of degree `t` in
`I` vanish, through the coefficient pairing. -/
noncomputable def formAnnihilator (I : Ideal (MvPolynomial ι K)) (t : ℕ) :
    Submodule K (degreeMonomials ι t → K) :=
  ⨅ q : {q : MvPolynomial ι K // q ∈ I ∧ q.IsHomogeneous t}, LinearMap.ker (coeffForm t q.1)

omit [Fintype κ] [NumberField K] in
/-- The Veronese image of a zero of `I` lies in `U_t(I)`. -/
theorem veronese_mem_formAnnihilator {I : Ideal (MvPolynomial ι K)} (t : ℕ) {x : ι → K}
    (hx : ∀ q ∈ I, eval x q = 0) : veronese t x ∈ formAnnihilator K I t := by
  refine Submodule.mem_iInf _ |>.2 fun q ↦ ?_
  rw [LinearMap.mem_ker, coeffForm_veronese q.2.2]
  exact hx q.1 q.2.1

omit [Fintype κ] [NumberField K] in
variable (K) in
/-- **`U_t(I)` is `(I_t)^⊥`** for `I_t` the forms of degree `t` in `I`, as linear forms on the
Veronese space. -/
theorem formAnnihilator_eq_dualCoannihilator (I : Ideal (MvPolynomial ι K)) (t : ℕ) :
    formAnnihilator K I t = (((I.restrictScalars K).comap
      (homogeneousSubmodule ι K t).subtype).map
        (homogeneousEquivDual ι K t).toLinearMap).dualCoannihilator := by
  ext y
  simp only [formAnnihilator, Submodule.mem_iInf, LinearMap.mem_ker,
    Submodule.mem_dualCoannihilator, Submodule.mem_map, Submodule.mem_comap,
    Submodule.restrictScalars_mem, Submodule.subtype_apply]
  constructor
  · rintro h _ ⟨p, hp, rfl⟩
    exact h ⟨p.1, hp, p.2⟩
  · intro h q
    exact h _ ⟨⟨q.1, q.2.2⟩, q.2.1, rfl⟩

omit [Fintype κ] [NumberField K] in
variable (K) in
/-- **`dim U_t(I) = dim (R/I)_t`**: `U_t(I)` is dual to the forms of degree `t` modulo those
in `I`. -/
theorem finrank_formAnnihilator (I : Ideal (MvPolynomial ι K)) (t : ℕ) :
    finrank K (formAnnihilator K I t) = finrank K (homogeneousSubmodule ι K t ⧸
      (I.restrictScalars K).comap (homogeneousSubmodule ι K t).subtype) := by
  set J := (I.restrictScalars K).comap (homogeneousSubmodule ι K t).subtype
  set e := homogeneousEquivDual ι K t
  have : Module.Finite K (homogeneousSubmodule ι K t) := Module.Finite.equiv e.symm
  have h1 := Subspace.finrank_add_finrank_dualCoannihilator_eq (J.map e.toLinearMap)
  have h2 := J.finrank_quotient_add_finrank
  have h3 : finrank K (degreeMonomials ι t → K) = finrank K (homogeneousSubmodule ι K t) := by
    rw [← Subspace.dual_finrank_eq, e.finrank_eq]
  rw [LinearEquiv.finrank_map_eq, ← formAnnihilator_eq_dualCoannihilator, h3] at h1
  omega

/-- **The weight of `U` for the products of degree `t`**: FW's `∑_v W_v((R/I)_t) / t` for
`U = U_t(I)`. -/
noncomputable def veroneseWeight (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (B : AbsoluteValue K ℝ → Finset κ) (f : AbsoluteValue K ℝ → κ → MvPolynomial ι F)
    (d : AbsoluteValue K ℝ → κ → ℕ) (c : AbsoluteValue K ℝ → κ → ℝ) (t : ℕ)
    (U : Submodule K (degreeMonomials ι t → K)) : ℝ :=
  maxWeight Sinf Sfin (fun v ↦ productIndex ι (B v) (d v) t)
    (fun v p ↦ coeffForm t (productPoly (B v) (f v) p)) (fun v ↦ productExp (B v) (c v) t) U

variable [NumberField F]

/-- **FW Theorem 9.3 for one degree `t`.** If `2 ≤ dim U_t(I) < W(U_t(I))`, finitely many forms
`q` of degree `t`, none in `I`, cover the nonzero solutions in `V(I)(K)`. -/
theorem exists_finset_isHomogeneous_notMem (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwI : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwF : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (B : AbsoluteValue K ℝ → Finset κ) (f : AbsoluteValue K ℝ → κ → MvPolynomial ι F)
    (d : AbsoluteValue K ℝ → κ → ℕ) (hf : ∀ v, ∀ k ∈ B v, (f v k).IsHomogeneous (d v k))
    (c : AbsoluteValue K ℝ → κ → ℝ) {t : ℕ} (ht : t ≠ 0) (I : Ideal (MvPolynomial ι K))
    (hdim : 2 ≤ finrank K (formAnnihilator K I t))
    (hW : (finrank K (formAnnihilator K I t) : ℝ) <
      veroneseWeight Sinf Sfin B f d c t (formAnnihilator K I t)) :
    ∃ T : Finset (MvPolynomial ι K), (∀ q ∈ T, q.IsHomogeneous t ∧ q ∉ I) ∧
      ∀ x : ι → K, x ≠ 0 → (∀ q ∈ I, eval x q = 0) →
        IsFormSystemSolution Sinf Sfin w B f d c x → ∃ q ∈ T, eval x q = 0 := by
  classical
  set U := formAnnihilator K I t
  obtain ⟨TU, hTU1, hTU2⟩ := exists_finset_submodule_lt_of_lt_maxWeight Sinf Sfin w hwI hwF
    _ _ _ U hdim hW
  -- a linear form vanishing on each proper subspace but not on `U`
  have hl : ∀ W' : Submodule K (degreeMonomials ι t → K), ∃ l : Dual K (degreeMonomials ι t → K),
      W' < U → (∃ u ∈ U, l u ≠ 0) ∧ ∀ y ∈ W', l y = 0 := by
    intro W'
    by_cases h : W' < U
    · obtain ⟨u, huU, huW⟩ := IsConcreteLE.exists_of_lt h
      obtain ⟨l, hlu, hlW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem huW inferInstance
      refine ⟨l, fun _ ↦ ⟨⟨u, huU, hlu⟩, fun y hy ↦ ?_⟩⟩
      have : l y ∈ W'.map l := ⟨y, hy, rfl⟩
      rw [hlW] at this
      exact (Submodule.mem_bot K).1 this
    · exact ⟨0, fun h' ↦ absurd h' h⟩
  choose l hlU using hl
  refine ⟨TU.image fun W' ↦ ofDual t (l W'), ?_, ?_⟩
  · intro q hq
    obtain ⟨W', hW', rfl⟩ := Finset.mem_image.1 hq
    refine ⟨isHomogeneous_ofDual t _, fun hqI ↦ ?_⟩
    obtain ⟨⟨u, huU, hlu⟩, -⟩ := hlU W' (hTU1 W' hW')
    have hker := (Submodule.mem_iInf _).1 huU ⟨_, hqI, isHomogeneous_ofDual t _⟩
    rw [LinearMap.mem_ker, coeffForm_ofDual] at hker
    exact hlu hker
  · intro x hx hxI hsol
    obtain ⟨W', hW'T, hyW'⟩ := hTU2 (veronese t x) (veronese_mem_formAnnihilator t hxI)
      (veronese_ne_zero t hx)
      (isSystemSolution_veronese Sinf Sfin w hwI hwF B f d hf c ht hx hsol)
    refine ⟨ofDual t (l W'), Finset.mem_image_of_mem _ hW'T, ?_⟩
    rw [eval_ofDual]
    exact (hlU W' (hTU1 W' hW'T)).2 _ hyW'

/-- **The solutions are not Zariski-dense in `V(I)`** for a prime `I`: one form not in `I`
vanishes at all of them. -/
theorem exists_notMem_of_isPrime (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwI : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwF : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (B : AbsoluteValue K ℝ → Finset κ) (f : AbsoluteValue K ℝ → κ → MvPolynomial ι F)
    (d : AbsoluteValue K ℝ → κ → ℕ) (hf : ∀ v, ∀ k ∈ B v, (f v k).IsHomogeneous (d v k))
    (c : AbsoluteValue K ℝ → κ → ℝ) {t : ℕ} (ht : t ≠ 0) (I : Ideal (MvPolynomial ι K))
    [I.IsPrime] (hdim : 2 ≤ finrank K (formAnnihilator K I t))
    (hW : (finrank K (formAnnihilator K I t) : ℝ) <
      veroneseWeight Sinf Sfin B f d c t (formAnnihilator K I t)) :
    ∃ q : MvPolynomial ι K, q ∉ I ∧ (∃ n, q.IsHomogeneous n) ∧
      ∀ x : ι → K, x ≠ 0 → (∀ q ∈ I, eval x q = 0) →
        IsFormSystemSolution Sinf Sfin w B f d c x → eval x q = 0 := by
  obtain ⟨T, hT1, hT2⟩ := exists_finset_isHomogeneous_notMem Sinf Sfin w hwI hwF B f d hf c ht
    I hdim hW
  refine ⟨∏ q ∈ T, q, fun h ↦ ?_, ⟨_, IsHomogeneous.prod T id (fun _ ↦ t)
    fun q hq ↦ (hT1 q hq).1⟩, fun x hx hxI hsol ↦ ?_⟩
  · obtain ⟨q, hq, hqI⟩ := Ideal.IsPrime.prod_mem_iff.1 h
    exact (hT1 q hq).2 hqI
  · obtain ⟨q, hq, hq0⟩ := hT2 x hx hxI hsol
    rw [map_prod]
    exact Finset.prod_eq_zero hq hq0

end NumberField
