/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring

-- Used only inside proofs.
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Basic

/-!
# The Gauss norm of multivariate polynomials

For a nonarchimedean absolute value `v` on a field `K`, the Gauss norm of `P ∈ K[X]` is the
maximum `max_m v(p_m)` of its coefficients (`MvPolynomial.maxNorm`). It is multiplicative
(**Gauss's lemma**, `MvPolynomial.maxNorm_mul`): normalize both factors to have coefficients in
the valuation ring `{v ≤ 1}`, one of them a unit, and reduce modulo its maximal ideal.

## Main definitions

* `AbsoluteValue.valuationSubring`: the valuation ring `{x | v x ≤ 1}` of a nonarchimedean `v`.
* `MvPolynomial.maxNorm`: `max_m v(p_m)`, and `0` for `P = 0`.

## Main results

* `MvPolynomial.maxNorm_mul`: Gauss's lemma.
* `MvPolynomial.maxNorm_C_mul`, `MvPolynomial.maxNorm_rename`, `MvPolynomial.maxNorm_add_le`.
* `MvPolynomial.maxNorm_aeval_le`: the Gauss norm of a substitution.
-/

@[expose] public section

namespace AbsoluteValue

variable {K : Type*} [Field K] (v : AbsoluteValue K ℝ)

/-- The valuation ring `{x | v x ≤ 1}` of a nonarchimedean absolute value. -/
def valuationSubring (hv : IsNonarchimedean v) : ValuationSubring K where
  carrier := {x | v x ≤ 1}
  mul_mem' {a b} ha hb := by
    change v (a * b) ≤ 1
    rw [map_mul]
    nlinarith [v.nonneg a, v.nonneg b, (show v a ≤ 1 from ha), (show v b ≤ 1 from hb)]
  one_mem' := by
    change v 1 ≤ 1
    simp
  add_mem' {a b} ha hb := (hv a b).trans (max_le ha hb)
  zero_mem' := by
    change v 0 ≤ 1
    simp
  neg_mem' {a} ha := by
    change v (-a) ≤ 1
    rwa [map_neg_eq_map]
  mem_or_inv_mem' x := by
    rcases le_total (v x) 1 with h | h
    · exact Or.inl h
    · right
      change v x⁻¹ ≤ 1
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ h

variable {v}

theorem mem_valuationSubring (hv : IsNonarchimedean v) {x : K} :
    x ∈ v.valuationSubring hv ↔ v x ≤ 1 :=
  Iff.rfl

theorem isUnit_valuationSubring_iff (hv : IsNonarchimedean v) (x : v.valuationSubring hv) :
    IsUnit x ↔ v x = 1 := by
  refine ⟨fun ⟨u, hu⟩ ↦ ?_, fun h ↦ ?_⟩
  · have h1 : v u * v ↑u⁻¹ = 1 := by
      rw [← map_mul]
      exact (congrArg (fun y : v.valuationSubring hv ↦ v (y : K)) u.mul_inv).trans (by simp)
    have h2 : v u ≤ 1 := u.1.2
    have h3 : v ↑u⁻¹ ≤ 1 := (↑u⁻¹ : v.valuationSubring hv).2
    rw [← hu]
    nlinarith [v.nonneg (u : K), v.nonneg ((↑u⁻¹ : v.valuationSubring hv) : K)]
  · have hx : (x : K) ≠ 0 := fun h0 ↦ by simp [h0] at h
    refine IsUnit.of_mul_eq_one ⟨(x : K)⁻¹, ?_⟩ (Subtype.ext ?_)
    · change v (x : K)⁻¹ ≤ 1
      rw [map_inv₀, h, inv_one]
    · simp [hx]

end AbsoluteValue

namespace MvPolynomial

section Residue

variable {τ R : Type*} [CommRing R] [IsLocalRing R]

theorem exists_isUnit_coeff_of_map_residue_ne_zero {P : MvPolynomial τ R}
    (h : map (IsLocalRing.residue R) P ≠ 0) : ∃ m, IsUnit (P.coeff m) := by
  by_contra! hc
  refine h (MvPolynomial.ext _ _ fun m ↦ ?_)
  rw [coeff_map]
  simpa [IsLocalRing.residue_eq_zero_iff] using hc m

theorem map_residue_ne_zero_of_isUnit_coeff {P : MvPolynomial τ R} {m : τ →₀ ℕ}
    (h : IsUnit (P.coeff m)) : map (IsLocalRing.residue R) P ≠ 0 := fun h0 ↦ by
  have := congrArg (fun Q ↦ Q.coeff m) h0
  simp only [coeff_map] at this
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 h (by simpa using this)

end Residue

variable {τ K : Type*} [Field K]

theorem exists_map_subtype_eq (O : ValuationSubring K) {F : MvPolynomial τ K}
    (h : ∀ m, F.coeff m ∈ O) : ∃ G : MvPolynomial τ O, map O.subtype G = F := by
  obtain ⟨G, hG⟩ := mem_range_map_iff_coeffs_subset (f := O.subtype).2 fun a ha ↦ by
    obtain ⟨m, -, rfl⟩ := mem_coeffs_iff.1 ha
    exact ⟨⟨_, h m⟩, rfl⟩
  exact ⟨G, hG⟩

/-- Gauss's lemma over a valuation ring: a product of polynomials with a unit coefficient has a
unit coefficient. -/
theorem exists_isUnit_coeff_mul {O : ValuationSubring K} {G H : MvPolynomial τ O}
    (hG : ∃ m, IsUnit (G.coeff m)) (hH : ∃ m, IsUnit (H.coeff m)) :
    ∃ m, IsUnit ((G * H).coeff m) := by
  obtain ⟨m, hm⟩ := hG
  obtain ⟨m', hm'⟩ := hH
  refine exists_isUnit_coeff_of_map_residue_ne_zero ?_
  rw [map_mul]
  exact mul_ne_zero (map_residue_ne_zero_of_isUnit_coeff hm)
    (map_residue_ne_zero_of_isUnit_coeff hm')

variable (v : AbsoluteValue K ℝ)

/-- The **Gauss norm** `max_m v(p_m)` (meaningful for nonarchimedean `v`), and `0` for `P = 0`. -/
noncomputable def maxNorm (P : MvPolynomial τ K) : ℝ :=
  ⨆ m : P.support, v (P.coeff m)

variable {v}

theorem maxNorm_nonneg (P : MvPolynomial τ K) : 0 ≤ maxNorm v P :=
  Real.iSup_nonneg fun _ ↦ v.nonneg _

@[simp]
theorem maxNorm_zero : maxNorm v (0 : MvPolynomial τ K) = 0 := by
  simp [maxNorm]

theorem le_maxNorm (P : MvPolynomial τ K) (m : τ →₀ ℕ) : v (P.coeff m) ≤ maxNorm v P := by
  by_cases hm : m ∈ P.support
  · exact le_ciSup (f := fun m : P.support ↦ v (P.coeff m)) (Set.finite_range _).bddAbove ⟨m, hm⟩
  · rw [notMem_support_iff.1 hm, map_zero]
    exact maxNorm_nonneg P

theorem maxNorm_le {P : MvPolynomial τ K} {a : ℝ} (ha : 0 ≤ a) (h : ∀ m, v (P.coeff m) ≤ a) :
    maxNorm v P ≤ a :=
  Real.iSup_le (fun m ↦ h m) ha

theorem exists_maxNorm_eq {P : MvPolynomial τ K} (hP : P ≠ 0) :
    ∃ m, P.coeff m ≠ 0 ∧ v (P.coeff m) = maxNorm v P := by
  obtain ⟨m, hm, hmax⟩ := P.support.exists_max_image (fun m ↦ v (P.coeff m))
    (support_nonempty.2 hP)
  exact ⟨m, mem_support_iff.1 hm, le_antisymm (le_maxNorm P m)
    (maxNorm_le (v.nonneg _) fun m' ↦ by
      by_cases hm' : m' ∈ P.support
      · exact hmax m' hm'
      · rw [notMem_support_iff.1 hm', map_zero]
        exact v.nonneg _)⟩

theorem maxNorm_pos {P : MvPolynomial τ K} (hP : P ≠ 0) : 0 < maxNorm v P := by
  obtain ⟨m, hm0, hm⟩ := exists_maxNorm_eq (v := v) hP
  rw [← hm]
  exact v.pos hm0

theorem maxNorm_eq_of {P : MvPolynomial τ K} {a : ℝ} (h1 : ∀ m, v (P.coeff m) ≤ a)
    (h2 : ∃ m, v (P.coeff m) = a) : maxNorm v P = a := by
  obtain ⟨m, hm⟩ := h2
  exact le_antisymm (maxNorm_le (hm ▸ v.nonneg _) h1) (hm ▸ le_maxNorm P m)

theorem maxNorm_C_mul (c : K) (P : MvPolynomial τ K) :
    maxNorm v (C c * P) = v c * maxNorm v P := by
  rcases eq_or_ne P 0 with rfl | hP
  · simp
  obtain ⟨m, -, hm⟩ := exists_maxNorm_eq (v := v) hP
  refine maxNorm_eq_of (fun m' ↦ ?_) ⟨m, by rw [coeff_C_mul, map_mul, hm]⟩
  rw [coeff_C_mul, map_mul]
  exact mul_le_mul_of_nonneg_left (le_maxNorm P m') (v.nonneg c)

theorem maxNorm_rename {υ : Type*} {f : τ → υ} (hf : Function.Injective f)
    (P : MvPolynomial τ K) : maxNorm v (rename f P) = maxNorm v P := by
  classical
  rcases eq_or_ne P 0 with rfl | hP
  · simp
  obtain ⟨m, -, hm⟩ := exists_maxNorm_eq (v := v) hP
  refine maxNorm_eq_of (fun m' ↦ ?_) ⟨m.mapDomain f, by rw [coeff_rename_mapDomain f hf, hm]⟩
  by_cases h : ∃ u : τ →₀ ℕ, u.mapDomain f = m'
  · obtain ⟨u, rfl⟩ := h
    rw [coeff_rename_mapDomain f hf]
    exact le_maxNorm P u
  · push Not at h
    rw [coeff_rename_eq_zero _ _ _ fun u hu ↦ absurd hu (h u), map_zero]
    exact maxNorm_nonneg P

variable (hv : IsNonarchimedean v)

include hv in
/-- A polynomial of Gauss norm `1` lifts to the valuation ring, with a unit coefficient. -/
theorem exists_lift_of_maxNorm_eq_one {P : MvPolynomial τ K} (hP : maxNorm v P = 1) :
    ∃ G : MvPolynomial τ (v.valuationSubring hv),
      map (v.valuationSubring hv).subtype G = P ∧ ∃ m, IsUnit (G.coeff m) := by
  obtain ⟨G, hG⟩ := exists_map_subtype_eq (v.valuationSubring hv) (F := P) fun m ↦
    (hP ▸ le_maxNorm P m : v (P.coeff m) ≤ 1)
  have hP0 : P ≠ 0 := fun h0 ↦ by simp [h0] at hP
  obtain ⟨m, -, hm⟩ := exists_maxNorm_eq (v := v) hP0
  refine ⟨G, hG, m, (AbsoluteValue.isUnit_valuationSubring_iff hv _).2 ?_⟩
  rw [← hP, ← hm, ← hG, coeff_map]
  rfl

include hv in
theorem maxNorm_map_eq_one {G : MvPolynomial τ (v.valuationSubring hv)}
    (hG : ∃ m, IsUnit (G.coeff m)) : maxNorm v (map (v.valuationSubring hv).subtype G) = 1 := by
  obtain ⟨m, hm⟩ := hG
  refine maxNorm_eq_of (fun m' ↦ (G.coeff m').2) ⟨m, ?_⟩
  rw [coeff_map]
  exact (AbsoluteValue.isUnit_valuationSubring_iff hv _).1 hm

/-- Normalizing a nonzero polynomial to Gauss norm `1`. -/
theorem exists_maxNorm_C_mul_eq_one {P : MvPolynomial τ K} (hP : P ≠ 0) :
    ∃ a : K, a ≠ 0 ∧ v a = maxNorm v P ∧ maxNorm v (C a⁻¹ * P) = 1 := by
  obtain ⟨m, hm0, hm⟩ := exists_maxNorm_eq (v := v) hP
  refine ⟨P.coeff m, hm0, hm, ?_⟩
  rw [maxNorm_C_mul, map_inv₀, ← hm, inv_mul_cancel₀ ((v.pos hm0).ne')]

include hv in
/-- **Gauss's lemma**: the Gauss norm is multiplicative. -/
theorem maxNorm_mul (P Q : MvPolynomial τ K) : maxNorm v (P * Q) = maxNorm v P * maxNorm v Q := by
  rcases eq_or_ne P 0 with rfl | hP
  · simp
  rcases eq_or_ne Q 0 with rfl | hQ
  · simp
  obtain ⟨a, ha, hva, hPa⟩ := exists_maxNorm_C_mul_eq_one hP
  obtain ⟨b, hb, hvb, hQb⟩ := exists_maxNorm_C_mul_eq_one hQ
  obtain ⟨G, hG, hGu⟩ := exists_lift_of_maxNorm_eq_one hv hPa
  obtain ⟨H, hH, hHu⟩ := exists_lift_of_maxNorm_eq_one hv hQb
  have h1 := maxNorm_map_eq_one hv (exists_isUnit_coeff_mul hGu hHu)
  rw [map_mul, hG, hH, show C a⁻¹ * P * (C b⁻¹ * Q) = C (a * b)⁻¹ * (P * Q) by
    rw [mul_inv, C_mul]; ring, maxNorm_C_mul, map_inv₀, map_mul] at h1
  rw [inv_mul_eq_one₀ (mul_pos (v.pos ha) (v.pos hb)).ne'] at h1
  rw [← hva, ← hvb, h1]

omit hv in
@[simp]
theorem maxNorm_C (c : K) : maxNorm v (C c : MvPolynomial τ K) = v c := by
  classical
  refine maxNorm_eq_of (fun m ↦ ?_) ⟨0, by simp⟩
  rw [coeff_C]
  split_ifs <;> simp

omit hv in
@[simp]
theorem maxNorm_one : maxNorm v (1 : MvPolynomial τ K) = 1 := by
  simpa using maxNorm_C (v := v) (τ := τ) (1 : K)

omit hv in
@[simp]
theorem maxNorm_X (s : τ) : maxNorm v (X s : MvPolynomial τ K) = 1 := by
  classical
  refine maxNorm_eq_of (fun m ↦ ?_) ⟨Finsupp.single s 1, by simp [coeff_X]⟩
  rw [coeff_X]
  split_ifs <;> simp

include hv in
theorem maxNorm_pow (P : MvPolynomial τ K) (n : ℕ) : maxNorm v (P ^ n) = maxNorm v P ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, maxNorm_mul hv, ih, pow_succ]

include hv in
theorem maxNorm_prod {α : Type*} (s : Finset α) (f : α → MvPolynomial τ K) :
    maxNorm v (∏ a ∈ s, f a) = ∏ a ∈ s, maxNorm v (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, maxNorm_mul hv, ih]

include hv in
/-- The ultrametric inequality for the Gauss norm. -/
theorem maxNorm_add_le (P Q : MvPolynomial τ K) :
    maxNorm v (P + Q) ≤ max (maxNorm v P) (maxNorm v Q) :=
  maxNorm_le (le_max_of_le_left (maxNorm_nonneg P)) fun m ↦ by
    rw [show (P + Q).coeff m = P.coeff m + Q.coeff m by simp]
    exact (hv _ _).trans (max_le_max (le_maxNorm P m) (le_maxNorm Q m))

include hv in
theorem maxNorm_sum_le {α : Type*} (s : Finset α) (f : α → MvPolynomial τ K) {B : ℝ}
    (hB : 0 ≤ B) (h : ∀ a ∈ s, maxNorm v (f a) ≤ B) : maxNorm v (∑ a ∈ s, f a) ≤ B := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hB
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (maxNorm_add_le hv _ _).trans (max_le (h a (Finset.mem_insert_self a s))
      (ih fun b hb ↦ h b (Finset.mem_insert_of_mem hb)))

include hv in
/-- **The Gauss norm of a substitution**: `‖P(g)‖ ≤ B` if every term `p_m g^m` has
`|p_m| ∏_x ‖g_x‖^{m_x} ≤ B`. -/
theorem maxNorm_aeval_le {υ : Type*} (g : υ → MvPolynomial τ K) (P : MvPolynomial υ K) {B : ℝ}
    (hB : 0 ≤ B)
    (h : ∀ m ∈ P.support, v (P.coeff m) * m.prod (fun x k ↦ maxNorm v (g x) ^ k) ≤ B) :
    maxNorm v (aeval g P) ≤ B := by
  conv_lhs => rw [P.as_sum, map_sum]
  refine maxNorm_sum_le hv _ _ hB fun m hm ↦ ?_
  rw [aeval_monomial, algebraMap_eq, maxNorm_C_mul, Finsupp.prod, maxNorm_prod hv]
  simp_rw [maxNorm_pow hv]
  exact h m hm

end MvPolynomial
