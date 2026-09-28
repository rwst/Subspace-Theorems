/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.RingTheory.PowerSeries.Expand

-- Used only inside proofs.
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Cartier operators on power series

For `q ≥ 1` and `r < q`, the **Cartier operator** `Λ_r` keeps the coefficients of a power series
in the residue class of `r` modulo `q`: `Λ_r (∑ h_n X ^ n) = ∑ h_(q n + r) X ^ n`. Over a finite
field with `q` elements, `A ^ q = A (X ^ q)`, and `Λ_r (A ^ q B) = A Λ_r B`: this is the identity
on which Christol's theorem runs (Christol–Kamae–Mendès France–Rauzy 1980, §6–§7).

Degrees are kept inside `K⟦X⟧`: `PowerSeries.IsBoundedBy N c` says that every coefficient of `c`
beyond `N` vanishes, i.e. `c` is a polynomial of degree at most `N`.

## Main results

* `PowerSeries.cartier_expand_mul`: `Λ_r (A (X ^ q) B) = A Λ_r B` for `r < q`, over any ring.
* `PowerSeries.cartier_pow_card_mul`: `Λ_r (A ^ q B) = A Λ_r B` over a field with `q` elements.
* `PowerSeries.eq_zero_of_forall_cartier_eq_zero`: a series all of whose `Λ_r` vanish is zero.
* `PowerSeries.IsBoundedBy.cartier`: `Λ_r` divides the degree by `q`.

## References

G. Christol, T. Kamae, M. Mendès France and G. Rauzy, *Suites algébriques, automates et
substitutions*, Bull. Soc. Math. France **108** (1980), 401–419, §6 (the operators `Λ_r`).
-/

@[expose] public section

open Finset

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- The **Cartier operator** `Λ_r`: `Λ_r (∑ h_n X ^ n) = ∑ h_(q n + r) X ^ n`. -/
noncomputable def cartier (q r : ℕ) (f : R⟦X⟧) : R⟦X⟧ :=
  mk fun n ↦ coeff (q * n + r) f

@[simp]
theorem coeff_cartier (q r n : ℕ) (f : R⟦X⟧) : coeff n (cartier q r f) = coeff (q * n + r) f :=
  coeff_mk _ _

theorem cartier_add (q r : ℕ) (f g : R⟦X⟧) :
    cartier q r (f + g) = cartier q r f + cartier q r g := by
  ext n
  simp

theorem cartier_sub (q r : ℕ) (f g : R⟦X⟧) :
    cartier q r (f - g) = cartier q r f - cartier q r g := by
  ext n
  simp

theorem cartier_zero (q r : ℕ) : cartier q r (0 : R⟦X⟧) = 0 := by
  ext n
  simp

theorem cartier_sum {ι : Type*} (q r : ℕ) (s : Finset ι) (f : ι → R⟦X⟧) :
    cartier q r (∑ i ∈ s, f i) = ∑ i ∈ s, cartier q r (f i) := by
  ext n
  simp [map_sum]

/-- **`Λ_r (A (X ^ q) B) = A Λ_r B`** for `r < q`. -/
theorem cartier_expand_mul {q : ℕ} (hq : q ≠ 0) {r : ℕ} (hr : r < q) (A B : R⟦X⟧) :
    cartier q r (expand q hq A * B) = A * cartier q r B := by
  ext n
  rw [coeff_cartier, coeff_mul, coeff_mul]
  symm
  refine sum_bij_ne_zero (fun x _ _ ↦ (q * x.1, q * x.2 + r)) ?_ ?_ ?_ ?_
  · intro x hx _
    rw [mem_antidiagonal] at hx ⊢
    rw [← hx]
    ring
  · intro x _ _ y _ _ h
    simp only [Prod.mk.injEq] at h
    have hq0 : 0 < q := Nat.pos_of_ne_zero hq
    exact Prod.ext (Nat.eq_of_mul_eq_mul_left hq0 h.1)
      (Nat.eq_of_mul_eq_mul_left hq0 (by omega))
  · intro y hy hne
    rw [mem_antidiagonal] at hy
    have hdvd : q ∣ y.1 := by
      by_contra h
      exact hne (by rw [coeff_expand_of_not_dvd q hq A h, zero_mul])
    obtain ⟨k, hk⟩ := hdvd
    have hkn : k ≤ n := by
      by_contra h
      have : q * (n + 1) ≤ q * k := Nat.mul_le_mul_left q (by omega)
      rw [mul_add, mul_one] at this
      omega
    have h2 : y.2 = q * (n - k) + r := by
      rw [Nat.mul_sub]
      have : q * k ≤ q * n := Nat.mul_le_mul_left q hkn
      omega
    refine ⟨(k, n - k), mem_antidiagonal.mpr (by omega), ?_, ?_⟩
    · rw [coeff_cartier, ← h2, ← coeff_expand_mul q hq A k, ← hk]
      exact hne
    · exact Prod.ext hk.symm h2.symm
  · intro x _ _
    simp [coeff_expand_mul]

section FiniteField

variable {K : Type*} [Field K] [Fintype K]

/-- **`Λ_r (A ^ q B) = A Λ_r B`** over a field with `q` elements, for `r < q`. -/
theorem cartier_pow_card_mul {q : ℕ} (hq : Fintype.card K = q) {r : ℕ} (hr : r < q)
    (A B : K⟦X⟧) : cartier q r (A ^ q * B) = A * cartier q r B := by
  subst hq
  rw [← FiniteField.PowerSeries.expand_card, cartier_expand_mul _ hr]

end FiniteField

/-- A series all of whose Cartier operators `Λ_r`, `r < q`, vanish is zero. -/
theorem eq_zero_of_forall_cartier_eq_zero {q : ℕ} (hq : q ≠ 0) {f : R⟦X⟧}
    (h : ∀ r < q, cartier q r f = 0) : f = 0 := by
  ext m
  have := congrArg (coeff (m / q)) (h (m % q) (Nat.mod_lt m (Nat.pos_of_ne_zero hq)))
  rwa [coeff_cartier, Nat.div_add_mod, map_zero] at this

/-- `c` is a polynomial of degree at most `N`: its coefficients beyond `N` vanish. -/
def IsBoundedBy (N : ℕ) (c : R⟦X⟧) : Prop :=
  ∀ m, N < m → coeff m c = 0

theorem IsBoundedBy.mono {N M : ℕ} {c : R⟦X⟧} (h : IsBoundedBy N c) (hNM : N ≤ M) :
    IsBoundedBy M c :=
  fun m hm ↦ h m (by omega)

theorem isBoundedBy_zero (N : ℕ) : IsBoundedBy N (0 : R⟦X⟧) :=
  fun _ _ ↦ map_zero _

theorem IsBoundedBy.add {N : ℕ} {c d : R⟦X⟧} (hc : IsBoundedBy N c) (hd : IsBoundedBy N d) :
    IsBoundedBy N (c + d) :=
  fun m hm ↦ by rw [map_add, hc m hm, hd m hm, add_zero]

theorem IsBoundedBy.sub {N : ℕ} {c d : R⟦X⟧} (hc : IsBoundedBy N c) (hd : IsBoundedBy N d) :
    IsBoundedBy N (c - d) :=
  fun m hm ↦ by rw [map_sub, hc m hm, hd m hm, sub_zero]

theorem IsBoundedBy.mul {N M : ℕ} {c d : R⟦X⟧} (hc : IsBoundedBy N c) (hd : IsBoundedBy M d) :
    IsBoundedBy (N + M) (c * d) := by
  intro m hm
  rw [coeff_mul]
  refine sum_eq_zero fun x hx ↦ ?_
  rw [mem_antidiagonal] at hx
  by_cases h : N < x.1
  · rw [hc _ h, zero_mul]
  · rw [hd _ (by omega), mul_zero]

theorem IsBoundedBy.pow {N : ℕ} {c : R⟦X⟧} (hc : IsBoundedBy N c) (k : ℕ) :
    IsBoundedBy (k * N) (c ^ k) := by
  induction k with
  | zero =>
    intro m hm
    rw [pow_zero, coeff_one]
    split_ifs with h
    · omega
    · rfl
  | succ k ih =>
    rw [pow_succ, add_mul, one_mul]
    exact ih.mul hc

/-- **`Λ_r` divides the degree by `q`.** -/
theorem IsBoundedBy.cartier {q N : ℕ} (hq : q ≠ 0) (r : ℕ) {d : R⟦X⟧}
    (hd : IsBoundedBy (q * N) d) : IsBoundedBy N (cartier q r d) := by
  intro n hn
  rw [coeff_cartier]
  refine hd _ ?_
  have : q * (N + 1) ≤ q * n := Nat.mul_le_mul_left q hn
  have : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq
  rw [mul_add, mul_one] at *
  omega

theorem isBoundedBy_coe (p : Polynomial R) : IsBoundedBy p.natDegree (p : R⟦X⟧) :=
  fun _ hm ↦ by rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt hm]

end PowerSeries
