/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.RingTheory.Ideal.LocalLength
public import Mathlib.Data.Sym.Card

-- Used only inside proofs.
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Lengths of quotients by powers of an ideal

Two elementary inequalities for lengths, which together replace Samuel multiplicities in the
multiplicity estimate of the product theorem (Rémond 2001, Lemma 3.1 and Prop. 3.1).

* **Upper bound.** If `J = (x_1, …, x_d)`, then `J^k / J^{k+1}` is a quotient of `(A/J)^N`, with
  `N` the number of monomials of degree `k` in `d` variables. Hence
  `ℓ(A/J^n) ≤ ℓ(A/J) · ∑_{k < n} multichoose d k = ℓ(A/J) · C(n - 1 + d, d)`. This is the
  inequality `e_J(A) ≤ ℓ(A/J)` for parameter ideals, before passing to the limit.
* **Lower bound.** A chain `L = L_0 ⊆ L_1 ⊆ ⋯ ⊆ L_r`, `L_{k+1} = L_k + (f_k)`, all of whose colon
  ideals `(L_k : f_k)` lie in `𝔭`, gives `r ≤ ℓ(A_𝔭/L_𝔭)`: each step contributes at least one to
  the localized length, by the exact sequence of a colon ideal.

## Main statements

* `Ideal.span_range_pow_eq`: `(x_1, …, x_d)^k` is spanned by the monomials `∏ x_{m_i}`, `m` a
  multiset of size `k`.
* `Ideal.length_quotient_span_range_pow_le`: `ℓ(A/J^n) ≤ (∑_{k < n} multichoose d k) · ℓ(A/J)`.
* `Ideal.localLength_span_range_pow_le`: the same for localized lengths.
* `Ideal.localLength_sup_span_singleton_add_one_le`: `ℓ((L + (f))_𝔭) + 1 ≤ ℓ(L_𝔭)` when
  `(L : f) ⊆ 𝔭`.
* `Ideal.le_localLength_of_colon_le`: the chain bound.
* `Ideal.localLength_ne_top_of_mem_minimalPrimes`: `ℓ(A_𝔭/L_𝔭)` is finite when `𝔭` is a minimal
  prime of `L` and `A` is Noetherian.
-/

@[expose] public section

variable {A : Type*} [CommRing A]

namespace Ideal

open Set

section Pow

variable {d : ℕ} (x : Fin d → A)

/-- The monomial `∏_{i ∈ m} x_i` of a multiset `m` of indices. -/
def symProd {k : ℕ} (m : Sym (Fin d) k) : A :=
  (m.1.map x).prod

theorem symProd_cons {k : ℕ} (a : Fin d) (m : Sym (Fin d) k) :
    symProd x (a ::ₛ m) = x a * symProd x m := by
  simp [symProd, Sym.coe_cons]

/-- `(x_1, …, x_d)^k` is spanned by the monomials of degree `k` in the `x_i`. -/
theorem span_range_pow_eq (k : ℕ) :
    span (range x) ^ k = span (range (symProd x (k := k))) := by
  classical
  induction k with
  | zero =>
    rw [pow_zero, one_eq_top, eq_comm, eq_top_iff_one]
    refine subset_span ⟨Sym.nil, ?_⟩
    simp [symProd, Sym.coe_nil]
  | succ k ih =>
    rw [pow_succ, ih, span_mul_span]
    congr 1
    ext y
    constructor
    · rintro ⟨_, ⟨m, rfl⟩, _, ⟨a, rfl⟩, rfl⟩
      exact ⟨a ::ₛ m, by rw [symProd_cons, mul_comm]⟩
    · rintro ⟨m, rfl⟩
      obtain ⟨a, ha⟩ : ∃ a, a ∈ m := Multiset.exists_mem_of_ne_zero (by
        intro h
        have := congrArg Multiset.card h
        simp at this)
      refine ⟨_, ⟨m.erase a ha, rfl⟩, _, ⟨a, rfl⟩, ?_⟩
      conv_rhs => rw [← Sym.cons_erase ha]
      rw [symProd_cons, mul_comm]

theorem symProd_mem_pow {k : ℕ} (m : Sym (Fin d) k) : symProd x m ∈ span (range x) ^ k := by
  rw [span_range_pow_eq]
  exact subset_span ⟨m, rfl⟩

/-- Multiplication by the monomials of degree `k`, as a map `(A/J)^N → A/J^{k+1}`. Its range is
`J^k / J^{k+1}`. -/
noncomputable def symProdMap (k : ℕ) :
    (Sym (Fin d) k → A ⧸ span (range x)) →ₗ[A] A ⧸ span (range x) ^ (k + 1) :=
  LinearMap.lsum A (fun _ ↦ A ⧸ span (range x)) A fun m ↦
    (span (range x)).liftQ ((span (range x) ^ (k + 1)).mkQ ∘ₗ LinearMap.mulRight A (symProd x m))
      fun y hy ↦ by
        rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero, LinearMap.mulRight_apply, pow_succ']
        exact mul_mem_mul hy (symProd_mem_pow x m)

theorem symProdMap_mk (k : ℕ) (c : Sym (Fin d) k → A) :
    symProdMap x k (fun m ↦ Submodule.Quotient.mk (c m)) =
      Submodule.Quotient.mk (∑ m, c m * symProd x m) := by
  rw [← Submodule.mkQ_apply, map_sum]
  simp only [symProdMap, LinearMap.lsum_apply]
  rw [LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun m _ ↦ rfl

theorem exact_symProdMap (k : ℕ) :
    Function.Exact (symProdMap x k)
      (Submodule.factor (pow_le_pow_right (Nat.le_succ k) : span (range x) ^ (k + 1) ≤ _)) := by
  classical
  intro y
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
  have hh : Submodule.factor (pow_le_pow_right (Nat.le_succ k) : span (range x) ^ (k + 1) ≤ _)
      (Submodule.Quotient.mk y) = Submodule.Quotient.mk y := rfl
  rw [Submodule.mkQ_apply, hh, Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hy
    rw [span_range_pow_eq, Submodule.mem_span_range_iff_exists_fun] at hy
    obtain ⟨c, rfl⟩ := hy
    refine ⟨fun m ↦ Submodule.Quotient.mk (c m), ?_⟩
    rw [symProdMap_mk]
    simp only [smul_eq_mul]
  · rintro ⟨c, hc⟩
    have hc' : ∀ m, ∃ a : A, Submodule.Quotient.mk a = c m := fun m ↦
      Submodule.mkQ_surjective _ (c m)
    choose a ha using hc'
    have hsum : symProdMap x k c =
        Submodule.Quotient.mk (∑ m, a m * symProd x m) := by
      rw [← symProdMap_mk]
      exact congrArg _ (funext fun m ↦ (ha m).symm)
    rw [hsum, Submodule.Quotient.eq] at hc
    have hmem : ∑ m, a m * symProd x m ∈ span (range x) ^ k :=
      _root_.sum_mem fun m _ ↦ mul_mem_left _ _ (symProd_mem_pow x m)
    have := sub_mem hmem (pow_le_pow_right (Nat.le_succ k) hc)
    simpa using this

/-- **Lengths of quotients by powers.** For `J = (x_1, …, x_d)`,
`ℓ(A/J^n) ≤ (∑_{k < n} multichoose d k) · ℓ(A/J)`. -/
theorem length_quotient_span_range_pow_le (n : ℕ) :
    Module.length A (A ⧸ span (range x) ^ n) ≤
      ((∑ k ∈ Finset.range n, d.multichoose k : ℕ) : ℕ∞) *
        Module.length A (A ⧸ span (range x)) := by
  classical
  induction n with
  | zero =>
    rw [pow_zero, one_eq_top, Module.length_eq_zero_iff.mpr inferInstance]
    simp
  | succ n ih =>
    have hex := exact_symProdMap x n
    have hN := Module.length_eq_add_of_exact (LinearMap.range (symProdMap x n)).subtype
      (Submodule.factor (pow_le_pow_right (Nat.le_succ n) : span (range x) ^ (n + 1) ≤ _))
      (Submodule.injective_subtype _) (Submodule.factor_surjective _)
      (by
        intro y
        rw [hex y]
        exact ⟨fun ⟨c, hc⟩ ↦ ⟨⟨y, c, hc⟩, rfl⟩, fun ⟨⟨_, c, hc⟩, h⟩ ↦ ⟨c, hc.trans h⟩⟩)
    have hle : Module.length A (LinearMap.range (symProdMap x n)) ≤
        (d.multichoose n : ℕ∞) * Module.length A (A ⧸ span (range x)) := by
      refine (Module.length_le_of_surjective _ (symProdMap x n).surjective_rangeRestrict).trans ?_
      rw [Module.length_pi, ENat.card_eq_coe_fintype_card, Sym.card_sym_eq_multichoose,
        Fintype.card_fin]
    rw [hN, Finset.sum_range_succ, Nat.cast_add, add_mul,
      add_comm (Module.length A (LinearMap.range _))]
    exact add_le_add ih hle

end Pow

section Local

variable (𝔭 : Ideal A) [𝔭.IsPrime]

/-- **Localized lengths of quotients by powers.** For `J = (x_1, …, x_d)`,
`ℓ(A_𝔭/J^n_𝔭) ≤ (∑_{k < n} multichoose d k) · ℓ(A_𝔭/J_𝔭)`. -/
theorem localLength_span_range_pow_le {d : ℕ} (x : Fin d → A) (n : ℕ) :
    localLength 𝔭 (span (range x) ^ n) ≤
      ((∑ k ∈ Finset.range n, d.multichoose k : ℕ) : ℕ∞) * localLength 𝔭 (span (range x)) := by
  rw [localLength, localLength, Ideal.map_pow, map_span, ← range_comp]
  exact length_quotient_span_range_pow_le _ n

variable {𝔭} in
/-- One step of a chain: if `(L : f) ⊆ 𝔭`, then adding `f` lowers the localized length by at
least one. -/
theorem localLength_sup_span_singleton_add_one_le {L : Ideal A} {f : A}
    (h : L.colon {f} ≤ 𝔭) : localLength 𝔭 (L ⊔ span {f}) + 1 ≤ localLength 𝔭 L := by
  rw [localLength_eq_add_colon 𝔭 L f, add_comm (localLength 𝔭 (L.colon {f}))]
  gcongr
  exact Order.one_le_iff_ne_zero.mpr (localLength_ne_zero h)

variable {𝔭} in
/-- **Chains give lengths.** If `f_0, …, f_{r-1}` satisfy `(L + (f_j)_{j < k} : f_k) ⊆ 𝔭` for every
`k < r`, then `r ≤ ℓ(A_𝔭/L_𝔭)`. -/
theorem le_localLength_of_colon_le (L : Ideal A) (f : ℕ → A) (r : ℕ)
    (h : ∀ k < r, (L ⊔ span (f '' Iio k)).colon {f k} ≤ 𝔭) : (r : ℕ∞) ≤ localLength 𝔭 L := by
  suffices localLength 𝔭 (L ⊔ span (f '' Iio r)) + r ≤ localLength 𝔭 L from
    le_trans (by simp) this
  induction r with
  | zero => simp
  | succ r ih =>
    have hstep := localLength_sup_span_singleton_add_one_le (h r (Nat.lt_succ_self r))
    have hI : L ⊔ span (f '' Iio (r + 1)) = L ⊔ span (f '' Iio r) ⊔ span {f r} := by
      have : Iio (r + 1) = insert r (Iio r) := by
        ext k
        simp
      rw [this, image_insert_eq, span_insert, sup_comm (span {f r}), sup_assoc]
    rw [hI, Nat.cast_succ, ← add_assoc, add_right_comm]
    exact (add_le_add hstep le_rfl).trans (ih fun k hk ↦ h k (hk.trans (Nat.lt_succ_self r)))

variable {𝔭} in
/-- At a minimal prime `𝔭` of `L` in a Noetherian ring, `A_𝔭/L_𝔭` is Artinian, so its length is
finite. -/
theorem localLength_ne_top_of_mem_minimalPrimes [IsNoetherianRing A] {L : Ideal A}
    (h : 𝔭 ∈ L.minimalPrimes) : localLength 𝔭 L ≠ ⊤ := by
  set Ap := Localization.AtPrime 𝔭
  have hm : IsLocalRing.maximalIdeal Ap ∈ (L.map (algebraMap A Ap)).minimalPrimes := by
    rw [IsLocalization.minimalPrimes_map 𝔭.primeCompl Ap L, Set.mem_preimage,
      Localization.AtPrime.under_maximalIdeal]
    exact h
  have hA := IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ hm
  have : IsArtinian Ap (Ap ⧸ L.map (algebraMap A Ap)) :=
    isArtinian_of_surjective_algebraMap (R := Ap ⧸ L.map (algebraMap A Ap))
      Ideal.Quotient.mk_surjective
  exact Module.length_ne_top

end Local

end Ideal
