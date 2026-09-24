/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Data.Int.Interval
public import DiophantineApproximation.MvHasseDeriv

/-!
# The grid lemma

A nonzero polynomial of degree at most `e j` in the variable `X j` cannot have all its Hasse
derivatives of order at most `e j / B` in each variable vanish at every point of the grid of
integers `|z j| ≤ B`: there are too many conditions for the degree. This is Bombieri–Gubler's
Lemma 7.5.24, the elementary ingredient of Step V of the proof of the Subspace Theorem, where the
polynomial is the auxiliary polynomial of Layer 5.2 restricted to a product of subspaces and the
grid is a box of lattice points in them.

The proof is an induction on the variables. In one variable it is a root count: each of the
`2 B + 1` integers of the grid is a root of multiplicity at least `e / B + 1`, so the polynomial
has more roots with multiplicity than its degree allows.

## Main results

* `Polynomial.exists_eval_hasseDeriv_ne_zero`: **the grid lemma in one variable**, over any
  integral domain of characteristic zero.
* `MvPolynomial.exists_eval_hasseDeriv_ne_zero`: **the grid lemma**, over a field of
  characteristic zero.
* `MvPolynomial.toPolynomial`: the specialization of all variables but one, with the degree bound
  `MvPolynomial.natDegree_toPolynomial_le` and the compatibility with the Hasse derivative in the
  surviving variable, `MvPolynomial.eval_hasseDeriv_toPolynomial`.

## Implementation notes

⚠ **The one-variable case is a count of roots, not a divisibility.** Bombieri–Gubler argue that
`f` cannot be divisible by `(∏_{|b| ≤ B} (x − b)) ^ (e/B + 1)`, whose degree exceeds `e`. Turning
that into a proof means knowing that the factors `x − b` are pairwise coprime, which over the
coefficient ring an induction on the variables would supply is a statement about a polynomial ring
in the remaining variables. Counting roots **with multiplicity** — `Polynomial.roots` already
carries them, and `Polynomial.card_roots'` bounds their number by the degree — needs no
coprimality and no unique factorization.

⚠ **The induction on the variables never substitutes a variable, and so never has to commute a
Hasse derivative past a substitution.** The statement carried along is that the derivative taken
so far does not vanish identically on the affine subspace on which the variables already handled
sit at their grid values; the inductive step specializes *all* the other variables, at an
arbitrary point of the field, to a polynomial in one variable and applies the one-variable lemma
to that. The only transport needed is `MvPolynomial.eval_hasseDeriv_toPolynomial`, between
`Polynomial.hasseDeriv` and `MvPolynomial.hasseDeriv` along a full specialization, and it is
proved monomial by monomial.

⚠ **Characteristic zero is used twice and for different reasons.** The `2 B + 1` integers of the
grid have to be distinct in the field, and a nonzero polynomial has to have a point where it does
not vanish — which is `MvPolynomial.funext` and needs the field to be infinite. Neither use needs
division, and the one-variable lemma is stated over an integral domain.

⚠ **`B` is a natural number here and a positive real in the book.** The conclusion is written
`B * i j ≤ e j` rather than `i j ≤ e j / B`, which is the same statement and avoids a floor; the
caller who wants a real bound takes the ceiling of it, and nothing in the proof cares.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Lemma 7.5.24.

This is part of Layer 5.5 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Finset

noncomputable section

namespace Polynomial

/-! ### One variable -/

/-- **The grid lemma in one variable**, Bombieri–Gubler, Lemma 7.5.24 for `N = 1`. A nonzero
polynomial of degree at most `e` over an integral domain of characteristic zero has, for every
`B ≥ 1`, an integer `z` with `|z| ≤ B` and an order `i` with `B i ≤ e` at which its `i`-th Hasse
derivative does not vanish. Otherwise each of the `2 B + 1` integers of the grid is a root of
multiplicity at least `e / B + 1`, and `(2 B + 1) (e / B + 1) > e` roots are more than the degree
allows. -/
theorem exists_eval_hasseDeriv_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    [CharZero R] {F : R[X]} (hF : F ≠ 0) {e B : ℕ} (hB : 0 < B) (hdeg : F.natDegree ≤ e) :
    ∃ z : ℤ, z.natAbs ≤ B ∧ ∃ i : ℕ, B * i ≤ e ∧ (hasseDeriv i F).eval (z : R) ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have hMB : B * (e / B) ≤ e := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_le_self e B
  have hdvd : ∀ z : ℤ, z.natAbs ≤ B → (X - C ((z : R))) ^ (e / B + 1) ∣ F := by
    intro z hz
    have h0 : (X : R[X]) ^ (e / B + 1) ∣ taylor (z : R) F := by
      rw [X_pow_dvd_iff]
      intro d hd
      rw [taylor_coeff]
      exact hcon z hz d (le_trans (Nat.mul_le_mul_left B (by omega)) hMB)
    obtain ⟨q, hq⟩ := h0
    refine ⟨taylor (-(z : R)) q, ?_⟩
    have hinv : taylor (-(z : R)) (taylor (z : R) F) = F := by
      rw [taylor_taylor, neg_add_cancel, taylor_zero]
    calc F = taylor (-(z : R)) (taylor (z : R) F) := hinv.symm
      _ = taylorAlgHom (-(z : R)) ((X : R[X]) ^ (e / B + 1) * q) := by rw [hq]; rfl
      _ = (X - C (z : R)) ^ (e / B + 1) * taylor (-(z : R)) q := by
          rw [map_mul, map_pow]
          have hx : (taylorAlgHom (-(z : R))) X = X - C (z : R) := by
            rw [show (taylorAlgHom (-(z : R))) X = taylor (-(z : R)) X from rfl, taylor_X, map_neg,
              ← sub_eq_add_neg]
          rw [hx]
          rfl
  have hmul : ∀ z : ℤ, z.natAbs ≤ B → e / B + 1 ≤ rootMultiplicity ((z : R)) F :=
    fun z hz ↦ (le_rootMultiplicity_iff hF).mpr (hdvd z hz)
  set Z : Finset R := (Finset.Icc (-(B : ℤ)) (B : ℤ)).image (fun z : ℤ ↦ (z : R)) with hZ
  have hcard : #Z = 2 * B + 1 := by
    rw [hZ, Finset.card_image_of_injective _ Int.cast_injective, Int.card_Icc]
    omega
  have hcount : ∀ z ∈ Z, e / B + 1 ≤ F.roots.count z := by
    intro z hzZ
    rw [hZ, Finset.mem_image] at hzZ
    obtain ⟨w, hw, rfl⟩ := hzZ
    rw [Finset.mem_Icc] at hw
    rw [count_roots]
    exact hmul w (by omega)
  have hsub : Z ⊆ F.roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, ← Multiset.count_pos]
    exact lt_of_lt_of_le (Nat.succ_pos _) (hcount z hz)
  have h1 : ∑ z ∈ Z, F.roots.count z ≤ Multiset.card F.roots := by
    rw [← Multiset.toFinset_sum_count_eq F.roots]
    exact Finset.sum_le_sum_of_subset hsub
  have h2 : #Z * (e / B + 1) ≤ ∑ z ∈ Z, F.roots.count z := by
    rw [Finset.card_eq_sum_ones, Finset.sum_mul]
    exact Finset.sum_le_sum fun z hz ↦ by simpa using hcount z hz
  have h3 : Multiset.card F.roots ≤ e := le_trans (card_roots' F) hdeg
  have h4 : e < B * (e / B + 1) := by
    have h5 := Nat.div_add_mod e B
    have h6 := Nat.mod_lt e hB
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have h7 : B * (e / B + 1) ≤ #Z * (e / B + 1) := by
    rw [hcard]
    exact Nat.mul_le_mul_right _ (by omega)
  omega


end Polynomial

namespace MvPolynomial

variable {σ R : Type*} [CommRing R] [DecidableEq σ]

/-! ### Specializing every variable but one -/

/-- Splitting a `Finsupp.prod` at one index, when the family has been updated there. The index
need not be in the support: the factor is then `t ^ 0`. -/
theorem prod_update_eq (n : σ →₀ ℕ) (g : σ → R) (a : σ) (t : R) :
    (n.prod fun j k ↦ (Function.update g a t) j ^ k)
      = t ^ n a * ∏ j ∈ n.support.erase a, g j ^ n j := by
  classical
  rw [Finsupp.prod]
  by_cases ha : a ∈ n.support
  · rw [← Finset.mul_prod_erase _ _ ha, Function.update_self]
    exact congrArg _ (Finset.prod_congr rfl fun j hj ↦ by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
  · rw [Finset.erase_eq_of_notMem ha, Finsupp.notMem_support_iff.mp ha, pow_zero, one_mul]
    exact Finset.prod_congr rfl fun j hj ↦ by
      rw [Function.update_of_ne (by rintro rfl; exact ha hj)]

/-- Lowering the exponent of `X a` changes the support only at `a`. -/
theorem erase_support_sub_single (m : σ →₀ ℕ) (a : σ) (i : ℕ) :
    (m - Finsupp.single a i).support.erase a = m.support.erase a := by
  ext j
  simp only [Finset.mem_erase, Finsupp.mem_support_iff, Finsupp.tsub_apply, ne_eq,
    and_congr_right_iff]
  intro hj
  rw [Finsupp.single_eq_of_ne hj, Nat.sub_zero]

/-- **Specializing every variable but one**: the `R`-algebra map `MvPolynomial σ R → R[X]` that
sends `X a` to `X` and every other variable to its value at `u`. -/
noncomputable def toPolynomial (a : σ) (u : σ → R) : MvPolynomial σ R →ₐ[R] Polynomial R :=
  aeval (Function.update (fun j ↦ Polynomial.C (u j)) a Polynomial.X)

/-- The specialization of a monomial is a monomial in the surviving variable. -/
theorem toPolynomial_monomial (a : σ) (u : σ → R) (m : σ →₀ ℕ) (b : R) :
    toPolynomial a u (monomial m b)
      = Polynomial.C (b * ∏ j ∈ m.support.erase a, u j ^ m j) * Polynomial.X ^ m a := by
  rw [toPolynomial, aeval_monomial, prod_update_eq]
  simp only [map_mul, map_prod, map_pow, Polynomial.algebraMap_eq]
  ring

/-- Specializing the other variables cannot raise the degree in the surviving one. -/
theorem natDegree_toPolynomial_le (a : σ) (u : σ → R) (P : MvPolynomial σ R) :
    (toPolynomial a u P).natDegree ≤ P.degreeOf a := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm ↦ ?_
  rw [toPolynomial_monomial, Polynomial.C_mul_X_pow_eq_monomial]
  exact le_trans (Polynomial.natDegree_monomial_le _) (degreeOf_le_iff.mp (le_refl _) m hm)

/-- **The specialization carries the Hasse derivative in the surviving variable to Mathlib's
one-variable Hasse derivative**, and its value at `t` to the value of the several-variable one at
the point that reads `t` in that variable. This is the only transport the induction on the
variables needs. -/
theorem eval_hasseDeriv_toPolynomial (a : σ) (u : σ → R) (t : R) (i : ℕ)
    (P : MvPolynomial σ R) :
    (Polynomial.hasseDeriv i (toPolynomial a u P)).eval t
      = eval (Function.update u a t) (hasseDeriv (Finsupp.single a i) P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial m b =>
      rw [toPolynomial_monomial, Polynomial.C_mul_X_pow_eq_monomial,
        Polynomial.hasseDeriv_monomial, Polynomial.eval_monomial, hasseDeriv_monomial,
        Finsupp.prod_single_index (by simp), eval_monomial, prod_update_eq,
        Finsupp.tsub_apply, Finsupp.single_eq_same, erase_support_sub_single]
      have hj : ∀ j ∈ m.support.erase a, u j ^ (m - Finsupp.single a i) j = u j ^ m j := by
        intro j hj
        rw [Finsupp.tsub_apply, Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hj), Nat.sub_zero]
      rw [Finset.prod_congr rfl hj]
      ring
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, Polynomial.eval_add, hp, hq]


/-! ### Several variables -/

/-- **The grid lemma**, Bombieri–Gubler, Lemma 7.5.24. A nonzero polynomial over a field of
characteristic zero, of degree at most `e j` in the variable `X j`, has for every `B ≥ 1` a Hasse
derivative of order `i` with `B * i j ≤ e j` in every variable that does not vanish at some point
of the grid of integers `|z j| ≤ B`.

The induction is on the set of variables already handled, and what it carries is that the
derivative taken so far does not vanish identically on the affine subspace on which those
variables sit at their grid values. -/
theorem exists_eval_hasseDeriv_ne_zero {k : Type*} [Field k] [CharZero k] {σ : Type*}
    [Finite σ] {f : MvPolynomial σ k} (hf : f ≠ 0) {e : σ → ℕ}
    (he : ∀ j, f.degreeOf j ≤ e j) {B : ℕ} (hB : 0 < B) :
    ∃ z : σ → ℤ, (∀ j, (z j).natAbs ≤ B) ∧ ∃ i : σ →₀ ℕ, (∀ j, B * i j ≤ e j) ∧
      eval (fun j ↦ ((z j : k))) (hasseDeriv i f) ≠ 0 := by
  classical
  have : Fintype σ := Fintype.ofFinite σ
  have : Infinite k := CharZero.infinite k
  obtain ⟨w, hw⟩ : ∃ w : σ → k, eval w f ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hf (MvPolynomial.funext fun x ↦ by rw [hcon x, map_zero])
  have key : ∀ s : Finset σ, ∃ z : σ → ℤ, (∀ j, (z j).natAbs ≤ B) ∧ ∃ i : σ →₀ ℕ,
      (∀ j, B * i j ≤ e j) ∧ (∀ j, j ∉ s → i j = 0) ∧
      eval (fun j ↦ if j ∈ s then ((z j : k)) else w j) (hasseDeriv i f) ≠ 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        refine ⟨fun _ ↦ 0, fun j ↦ by simp, 0, fun j ↦ by simp, fun j _ ↦ rfl, ?_⟩
        simpa [hasseDeriv_zero_apply] using hw
    | insert a s ha ih =>
        obtain ⟨z, hz, i, hi, hisupp, hne⟩ := ih
        set u : σ → k := fun j ↦ if j ∈ s then ((z j : k)) else w j with hu
        set g : MvPolynomial σ k := hasseDeriv i f with hg
        have hF0 : toPolynomial a u g ≠ 0 := by
          intro hc
          refine hne ?_
          have := eval_hasseDeriv_toPolynomial a u (u a) 0 g
          rw [hc] at this
          simp only [map_zero, Polynomial.eval_zero, Finsupp.single_zero,
            hasseDeriv_zero_apply] at this
          rw [Function.update_eq_self] at this
          exact this.symm
        have hdeg : (toPolynomial a u g).natDegree ≤ e a :=
          le_trans (natDegree_toPolynomial_le a u g)
            (le_trans (le_trans (degreeOf_hasseDeriv_le i f a) (Nat.sub_le _ _)) (he a))
        obtain ⟨za, hza, ia, hia, hval⟩ :=
          Polynomial.exists_eval_hasseDeriv_ne_zero hF0 hB hdeg
        rw [eval_hasseDeriv_toPolynomial] at hval
        refine ⟨Function.update z a za, ?_, Finsupp.single a ia + i, ?_, ?_, ?_⟩
        · intro j
          rcases eq_or_ne j a with rfl | hj
          · rwa [Function.update_self]
          · rw [Function.update_of_ne hj]; exact hz j
        · intro j
          rcases eq_or_ne j a with rfl | hj
          · rw [Finsupp.add_apply, Finsupp.single_eq_same, hisupp j ha, Nat.add_zero]
            exact hia
          · rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hj, Nat.zero_add]
            exact hi j
        · intro j hj
          rw [Finset.mem_insert] at hj
          push Not at hj
          rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hj.1, Nat.zero_add]
          exact hisupp j hj.2
        · have hdisj : Disjoint (Finsupp.single a ia).support i.support := by
            refine Finset.disjoint_left.mpr fun j hj1 hj2 ↦ ?_
            have hja : j = a := by simpa using Finsupp.support_single_subset hj1
            subst hja
            exact Finsupp.mem_support_iff.mp hj2 (hisupp j ha)
          rw [← hasseDeriv_comp_of_disjoint hdisj]
          have hpt : (fun j ↦ if j ∈ insert a s then ((Function.update z a za j : k)) else w j)
              = Function.update u a ((za : k)) := by
            funext j
            rcases eq_or_ne j a with rfl | hj
            · rw [Function.update_self, Function.update_self,
                ite_eq_left (Finset.mem_insert_self _ _)]
            · rw [Function.update_of_ne hj, Function.update_of_ne hj, hu]
              simp only [Finset.mem_insert, hj, false_or]
          rw [hpt]
          exact hval
  obtain ⟨z, hz, i, hi, _, hne⟩ := key Finset.univ
  exact ⟨z, hz, i, hi, by simpa using hne⟩

end MvPolynomial

/-! ### Acceptance criteria -/

section Acceptance

open Polynomial in
/-- **Acceptance test: a derivative of positive order is unavoidable.** The polynomial
`X ^ 3 - X` over `ℚ` is nonzero of degree `3` and vanishes at every integer of the grid `|z| ≤ 1`,
so the grid lemma cannot be strengthened to `i = 0`; with `B = 1` and `e = 3` it allows orders up
to `3`, and order `1` already works at `z = 0`. -/
example : (∀ z : ℤ, z.natAbs ≤ 1 → ((X : ℚ[X]) ^ 3 - X).eval ((z : ℚ)) = 0) ∧
    (hasseDeriv 1 ((X : ℚ[X]) ^ 3 - X)).eval 0 ≠ 0 := by
  constructor
  · intro z hz
    have h : z = -1 ∨ z = 0 ∨ z = 1 := by omega
    rcases h with rfl | rfl | rfl <;> norm_num
  · rw [hasseDeriv_one, derivative_sub, derivative_X_pow, derivative_X]
    norm_num

/-- **Acceptance test: the grid lemma.** -/
example {k : Type*} [Field k] [CharZero k] {σ : Type*} [Finite σ]
    {f : MvPolynomial σ k} (hf : f ≠ 0) {e : σ → ℕ} (he : ∀ j, f.degreeOf j ≤ e j)
    {B : ℕ} (hB : 0 < B) :
    ∃ z : σ → ℤ, (∀ j, (z j).natAbs ≤ B) ∧ ∃ i : σ →₀ ℕ, (∀ j, B * i j ≤ e j) ∧
      MvPolynomial.eval (fun j ↦ ((z j : k))) (MvPolynomial.hasseDeriv i f) ≠ 0 :=
  MvPolynomial.exists_eval_hasseDeriv_ne_zero hf he hB

end Acceptance
