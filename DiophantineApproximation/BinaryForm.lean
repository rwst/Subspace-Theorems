/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Algebra.Polynomial.Homogenize
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.Minpoly.Field

-- Used only inside proofs.
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Separable

/-!
# Binary forms over `ℤ`, their complex roots, and the multiplicity of an irrational root

Thue's theorem — Layer 3.6 — is a statement about a homogeneous `G ∈ ℤ[X, Y]` and a proof about
the complex roots of one polynomial in one variable. This file is the dictionary between the two:
the dehomogenization `g = G(X, 1)`, the identity

```text
G(x, y) = y ^ d · g(x / y) = a · y ^ d · ∏ r, (x / y - r) ^ μ(r)        (y ≠ 0),
```

over the distinct complex roots `r` of `g`, with multiplicities `μ(r)` and `a` the leading
coefficient; the value `G(x, 0) = g_d x ^ d` on the line at infinity; and the one arithmetic fact
the approximation argument needs about the multiplicities.

## Main results

* `MvPolynomial.IsHomogeneous.natDegree_aeval_X_one_le`: the dehomogenization of a form of
  degree `d` has degree at most `d`. With Mathlib's `Polynomial.homogenize_eq_of_isHomogeneous`
  this says every binary form of degree `d` is `g.homogenize d` for a `g` of degree `≤ d`.
* `Polynomial.eval_homogenize_eq_coeff_mul_pow`: `G(x, 0) = g_d x ^ d`.
* `Polynomial.intCast_eval_homogenize` and `Polynomial.eval_map_intCast_eq_prod`: the identity
  above, in its two halves.
* `Polynomial.two_mul_count_roots_lt_natDegree`: an irrational complex root of multiplicity `μ`
  of an integer polynomial `g` with at least three distinct complex roots has `2 μ < deg g`.

## Implementation notes

⚠ **Mathlib already has the binary form, and nothing is defined here.** `Polynomial.homogenize`
turns `g` into an element of `MvPolynomial (Fin 2)`, `Polynomial.eval_homogenize` evaluates it
off the line at infinity, and `Polynomial.homogenize_eq_of_isHomogeneous` says every homogeneous
form arises. So the roadmap's `G ∈ ℤ[X, Y]` is `MvPolynomial (Fin 2) ℤ` with `IsHomogeneous d`.
What was missing is the degree bound on the dehomogenization, which that lemma leaves to the
caller, and the value on the line at infinity, where `eval_homogenize` does not apply.

⚠ **The multiplicity bound is the price of not factoring first.** Bombieri–Gubler reduce to an
irreducible form before approximating: they factor `G` into irreducible binary forms over `ℤ`,
observe that along infinitely many solutions each factor takes one of finitely many values, so
that `x / y` accumulates at a zero of each and only one factor can occur, and run the
approximation argument on that one, which is separable. Layer 3.6 runs it on `G` itself,
repeated factors and all, and then the exponent at the root `r` nearest to `x / y` is `d / μ`,
not `d`. For an irrational `r`, `d / μ > 2` is `Polynomial.two_mul_count_roots_lt_natDegree`:
`(minpoly ℚ r) ^ μ` divides `g`, the minimal polynomial has degree at least `2`, and when its
degree is exactly `2` the third distinct root has to come from the cofactor. ⚠ For a rational
root the bound is false — `X ^ 2 (X ^ 2 - 2)` has the root `0` with `μ = 2` and `d = 4` — and
there Layer 3.6 uses Liouville's inequality with exponent `1` instead of Roth's theorem
(`DiophantineApproximation/ThueEquation.lean`).

⚠ **Only `≤` is needed from the multiplicity of a power.** `(minpoly ℚ r) ^ μ ∣ g` is proved by
induction on the exponent: if `(minpoly ℚ r) ^ j ∣ g` with `j < μ`, the cofactor must still vanish
at `r`, because the minimal polynomial is separable and so contributes multiplicity at most `1`
per factor. Mathlib has no `rootMultiplicity_pow`, and the upper bound
`rootMultiplicity r (p ^ j) ≤ j` from `rootMultiplicity_mul` is all the induction uses.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Section 6.2.

This is part of Layer 3.6 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Polynomial

/-- The dehomogenization `G(X, 1)` of a binary form of degree `d` has degree at most `d`. -/
theorem MvPolynomial.IsHomogeneous.natDegree_aeval_X_one_le {R : Type*} [CommRing R]
    {G : MvPolynomial (Fin 2) R} {d : ℕ} (hG : G.IsHomogeneous d) :
    (MvPolynomial.aeval ![(Polynomial.X : R[X]), 1] G).natDegree ≤ d := by
  rw [G.as_sum, map_sum]
  refine natDegree_sum_le_of_forall_le _ _ fun m hm ↦ ?_
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, mul_one]
  refine (natDegree_C_mul_le _ _).trans ((natDegree_X_pow_le _).trans ?_)
  have := hG (MvPolynomial.mem_support_iff.mp hm)
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two] at this
  omega

/-- On the line at infinity, `homogenize p n` is the coefficient of degree `n` times `x ^ n`. -/
theorem Polynomial.eval_homogenize_eq_coeff_mul_pow {R : Type*} [CommSemiring R] (p : R[X])
    (n : ℕ) (x : R) : MvPolynomial.eval ![x, 0] (p.homogenize n) = p.coeff n * x ^ n := by
  simp only [homogenize, MvPolynomial.eval_sum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    MvPolynomial.eval_monomial]
  rw [Finset.sum_range_succ, Finset.sum_eq_zero]
  · simp [Finsupp.prod_fintype, Fin.prod_univ_two]
  · intro k hk
    rw [Finset.mem_range] at hk
    rw [Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
    simp [zero_pow (Nat.sub_ne_zero_of_lt hk)]

/-- The value of an integer binary form, read in `ℂ` off the line at infinity:
`G(x, y) = g(x / y) y ^ d`. -/
theorem Polynomial.intCast_eval_homogenize {g : ℤ[X]} {d : ℕ} (hd : g.natDegree ≤ d) (x y : ℤ)
    (hy : y ≠ 0) : ((MvPolynomial.eval ![x, y] (g.homogenize d) : ℤ) : ℂ) =
      (g.map (Int.castRingHom ℂ)).eval ((x : ℂ) / y) * (y : ℂ) ^ d := by
  have h1 : ((MvPolynomial.eval ![x, y] (g.homogenize d) : ℤ) : ℂ) =
      MvPolynomial.eval ![(x : ℂ), (y : ℂ)] ((g.map (Int.castRingHom ℂ)).homogenize d) := by
    have hv : (Int.castRingHom ℂ) ∘ ![x, y] = ![(x : ℂ), (y : ℂ)] := by
      ext i; fin_cases i <;> simp
    rw [homogenize_map, ← eq_intCast (Int.castRingHom ℂ), MvPolynomial.map_eval, hv]
  rw [h1, eval_homogenize (natDegree_map_le.trans hd)]
  · simp
  · simpa using hy

/-- An integer polynomial, read in `ℂ`, is its leading coefficient times the product of
`X - r` over its distinct complex roots `r`, each to its multiplicity. -/
theorem Polynomial.eval_map_intCast_eq_prod (g : ℤ[X]) (t : ℂ) :
    (g.map (Int.castRingHom ℂ)).eval t = (g.leadingCoeff : ℂ) *
      ∏ r ∈ (g.map (Int.castRingHom ℂ)).roots.toFinset,
        (t - r) ^ (g.map (Int.castRingHom ℂ)).roots.count r := by
  classical
  set gc := g.map (Int.castRingHom ℂ) with hgc
  have hcard : Multiset.card gc.roots = gc.natDegree :=
    splits_iff_card_roots.mp (IsAlgClosed.splits gc)
  conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C hcard]
  rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, Finset.prod_multiset_map_count]
  have hlc : gc.leadingCoeff = (g.leadingCoeff : ℂ) := by
    rw [hgc, leadingCoeff_map_of_injective (RingHom.injective_int _)]
    simp
  rw [hlc]
  congr 1
  refine Finset.prod_congr rfl fun r _ ↦ ?_
  simp

/-- **The multiplicity of an irrational root.** If an integer polynomial `g` has at least three
distinct complex roots, then each root `r` that is not rational has multiplicity `μ` with
`2 μ < deg g`: `(minpoly ℚ r) ^ μ` divides `g`, the minimal polynomial has degree at least `2`,
and when its degree is exactly `2` the third root makes the cofactor nonconstant. For a rational
root the bound fails: `X ^ 2 (X ^ 2 - 2)` has the root `0` with `μ = 2` and degree `4`. -/
theorem Polynomial.two_mul_count_roots_lt_natDegree {g : ℤ[X]} (hg : g ≠ 0) {r : ℂ}
    (hr : r ∈ (g.map (Int.castRingHom ℂ)).roots) (hirr : r ∉ Set.range (algebraMap ℚ ℂ))
    (h3 : 3 ≤ (g.map (Int.castRingHom ℂ)).roots.toFinset.card) :
    2 * (g.map (Int.castRingHom ℂ)).roots.count r < g.natDegree := by
  classical
  set gq := g.map (Int.castRingHom ℚ) with hgq
  have hgq0 : gq ≠ 0 := (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).mpr hg
  have hgc : g.map (Int.castRingHom ℂ) = gq.map (algebraMap ℚ ℂ) := by
    rw [hgq, Polynomial.map_map]
    congr 1
  have hdeg : g.natDegree = gq.natDegree :=
    (natDegree_map_eq_of_injective (RingHom.injective_int _) g).symm
  rw [hgc] at hr h3 ⊢
  rw [hdeg]
  set gc := gq.map (algebraMap ℚ ℂ) with hgcdef
  have hgc0 : gc ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap ℚ ℂ).injective).mpr hgq0
  have hroot : gc.IsRoot r := (mem_roots hgc0).mp hr
  have hint : IsIntegral ℚ r := by
    refine IsAlgebraic.isIntegral ⟨gq, hgq0, ?_⟩
    rw [aeval_def, ← eval_map]
    exact hroot
  set p := minpoly ℚ r with hp
  have hpmon : p.Monic := minpoly.monic hint
  have hk : 2 ≤ p.natDegree := by
    have h0 : 0 < p.natDegree := minpoly.natDegree_pos hint
    have h1 : p.natDegree ≠ 1 := fun h ↦ hirr (minpoly.natDegree_eq_one_iff.mp h)
    omega
  have hsep : (p.map (algebraMap ℚ ℂ)).Separable :=
    (PerfectField.separable_of_irreducible (minpoly.irreducible hint)).map
  have hp0 : p.map (algebraMap ℚ ℂ) ≠ 0 := (hpmon.map _).ne_zero
  have hpow_le : ∀ j : ℕ, rootMultiplicity r ((p.map (algebraMap ℚ ℂ)) ^ j) ≤ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hp0) hp0)]
      have := rootMultiplicity_le_one_of_separable hsep r
      omega
  set μ := gc.roots.count r with hμ
  have hμr : μ = rootMultiplicity r gc := count_roots gc
  -- `(minpoly ℚ r) ^ μ ∣ g`, one factor at a time
  have hdvd : ∀ j ≤ μ, p ^ j ∣ gq := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      obtain ⟨h, hh⟩ := ih (by omega)
      suffices hph : p ∣ h by
        rw [pow_succ, hh]
        exact mul_dvd_mul_left _ hph
      refine minpoly.dvd ℚ r ?_
      by_contra hne
      have h0 : rootMultiplicity r (h.map (algebraMap ℚ ℂ)) = 0 :=
        rootMultiplicity_eq_zero (by rwa [IsRoot, eval_map, ← aeval_def])
      have hmap : gc = (p.map (algebraMap ℚ ℂ)) ^ j * h.map (algebraMap ℚ ℂ) := by
        rw [hgcdef, hh, Polynomial.map_mul, Polynomial.map_pow]
      have := hpow_le j
      rw [hmap, rootMultiplicity_mul (hmap ▸ hgc0)] at hμr
      omega
  obtain ⟨h, hh⟩ := hdvd μ le_rfl
  have hh0 : h ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hh
    exact hgq0 hh
  have hdegeq : gq.natDegree = μ * p.natDegree + h.natDegree := by
    rw [hh, natDegree_mul (pow_ne_zero _ hpmon.ne_zero) hh0, natDegree_pow]
  have hμ1 : 1 ≤ μ := Multiset.count_pos.mpr hr
  rcases Nat.eq_zero_or_pos h.natDegree with hh1 | hh1
  · -- a constant cofactor: every root of `g` is a root of the minimal polynomial
    have hsub : gc.roots.toFinset ⊆ (p.map (algebraMap ℚ ℂ)).roots.toFinset := by
      intro r' hr'
      rw [Multiset.mem_toFinset, mem_roots hgc0] at hr'
      rw [Multiset.mem_toFinset, mem_roots hp0]
      obtain ⟨c, hC⟩ : ∃ c, h = C c := ⟨_, eq_C_of_natDegree_eq_zero hh1⟩
      have hc : c ≠ 0 := by
        rintro rfl
        rw [map_zero] at hC
        exact hh0 hC
      have : gc = (p.map (algebraMap ℚ ℂ)) ^ μ * C (algebraMap ℚ ℂ c) := by
        rw [hgcdef, hh, Polynomial.map_mul, Polynomial.map_pow, hC, map_C]
      rw [this, IsRoot, eval_mul, eval_pow, eval_C, mul_eq_zero] at hr'
      rcases hr' with hr' | hr'
      · exact pow_eq_zero_iff (by omega) |>.mp hr'
      · exact absurd ((algebraMap ℚ ℂ).injective (hr'.trans (map_zero _).symm)) hc
    have hk3 : 3 ≤ p.natDegree := by
      refine h3.trans ((Finset.card_le_card hsub).trans ?_)
      refine (Multiset.toFinset_card_le _).trans ((card_roots' _).trans ?_)
      exact natDegree_map_le
    have : 3 * μ ≤ μ * p.natDegree := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hk3
    omega
  · have : 2 * μ ≤ μ * p.natDegree := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hk
    omega

end
