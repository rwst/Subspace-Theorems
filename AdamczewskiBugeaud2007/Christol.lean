/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import AdamczewskiBugeaud2007.AutomaticSequence
public import AdamczewskiBugeaud2007.CartierOperator
public import Mathlib.RingTheory.Algebraic.Defs

-- Used only inside proofs.
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic.LinearCombination

/-!
# Christol's theorem: algebraic power series over a finite field are automatic

**Christol (1979); Christol–Kamae–Mendès France–Rauzy (1980), Théorème 1, (iii) ⇒ (i).** Let `K`
be a finite field with `q` elements. If `f ∈ K⟦X⟧` is algebraic over `K[X]` (equivalently, over
`K(X)`), then the `q`-kernel of its coefficient sequence is finite: the sequence is `q`-automatic.

The proof is CKMR80's §7, kept inside `K⟦X⟧`.

* **A Frobenius relation.** The powers `f ^ (q ^ i)` span a finitely generated `K[X]`-module, so
  they are dependent: `∑_(i ≤ n) a_i f ^ (q ^ i) = 0` with polynomials `a_i` not all zero
  (`PowerSeries.exists_frobenius_relation`).
* **Ore's normalization.** If `a_0 = 0`, some Cartier operator `Λ_r` does not kill the first
  nonzero `a_j`, and `Λ_r (a_i (f ^ (q ^ (i - 1))) ^ q) = f ^ (q ^ (i - 1)) Λ_r a_i` lowers every
  index by one. So there is a relation with `a_0 ≠ 0`
  (`PowerSeries.exists_frobenius_relation_ne_zero`).
* **A finite stable set.** With `N` a bound on the degrees of the `a_i`, the set `H` of the `s`
  with `a_0 s = ∑_(i ≤ n) c_i f ^ (q ^ i)`, `deg c_i ≤ N`, is finite, since `a_0 ≠ 0` and
  `K` is finite. It contains `f`, and `Λ_r` maps it into itself: multiply by `a_0 ^ (q - 1)`,
  eliminate `c_0 a_0 f` with the relation, and apply `Λ_r (A ^ q B) = A Λ_r B`; the degrees
  come back to `≤ q N / q = N`. CKMR80 divide by `a_0` in `K((X))` instead; multiplying through
  keeps everything in `K⟦X⟧`.
* **The kernel.** `n ↦ f_(q ^ i n + r)` is `Λ` applied `i` times to `f`, so it lies in `H`.

## Main results

* `PowerSeries.finite_kKernel_coeff_of_isAlgebraic`: **Christol's theorem**, the direction
  algebraic ⇒ automatic.
* `PowerSeries.isAutomatic_coeff_of_isAlgebraic`: the same with `Function.IsAutomatic`.

## Implementation notes

Only the direction algebraic ⇒ automatic is formalized; Theorem 7 of Adamczewski–Bugeaud 2007
needs no other.

## References

G. Christol, *Ensembles presque périodiques `k`-reconnaissables*, Theoret. Comput. Sci. **9**
(1979), 141–145; G. Christol, T. Kamae, M. Mendès France and G. Rauzy, *Suites algébriques,
automates et substitutions*, Bull. Soc. Math. France **108** (1980), 401–419, §7.
-/

@[expose] public section

open Finset Polynomial

namespace PowerSeries

variable {K : Type*} [Field K] [Fintype K] {f : K⟦X⟧}

omit [Fintype K] in
theorem algebraMap_polynomial_eq_coe (P : K[X]) : algebraMap K[X] K⟦X⟧ P = (P : K⟦X⟧) := by
  rw [algebraMap_apply', Algebra.algebraMap_self, map_id]
  rfl

/-- **A Frobenius relation.** An algebraic `f` satisfies `∑_(i ≤ n) a_i f ^ (q ^ i) = 0` with
polynomial coefficients of degree at most `N`, the first nonzero one being `a_j`. -/
theorem exists_frobenius_relation (hf : IsAlgebraic K[X] f) :
    ∃ n N j : ℕ, ∃ a : ℕ → K⟦X⟧, (∀ i, IsBoundedBy N (a i)) ∧ (∀ i < j, a i = 0) ∧
      a j ≠ 0 ∧ j ≤ n ∧ ∑ i ∈ range (n + 1), a i * f ^ (Fintype.card K ^ i) = 0 := by
  classical
  set q := Fintype.card K
  obtain ⟨y, hy0, hint⟩ := hf.exists_integral_multiple
  set z := y • f
  obtain ⟨s, hs⟩ := hint.fg_adjoin_singleton
  set m := s.card + 1
  set v : Fin m → K⟦X⟧ := fun i ↦ z ^ (q ^ (i : ℕ))
  have hv : Set.range v ≤ Submodule.span K[X] (s : Set K⟦X⟧) := by
    rintro _ ⟨i, rfl⟩
    rw [hs]
    exact (Algebra.adjoin K[X] {z}).pow_mem (Algebra.subset_adjoin rfl) _
  have hdep : ¬ LinearIndependent K[X] v := by
    intro hli
    have := linearIndependent_le_span' v hli (s : Set K⟦X⟧) hv
    have hcard : Fintype.card (s : Set K⟦X⟧) = s.card := by simp
    simp only [Cardinal.mk_fintype, Fintype.card_fin, Nat.cast_le, m, hcard] at this
    omega
  obtain ⟨g, hg, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hdep
  set P : ℕ → K[X] := fun i ↦ if h : i < m then g ⟨i, h⟩ * y ^ (q ^ i) else 0
  set a : ℕ → K⟦X⟧ := fun i ↦ (P i : K⟦X⟧)
  have hsum : ∑ i ∈ range m, a i * f ^ (q ^ i) = 0 := by
    rw [← hg, ← Fin.sum_univ_eq_sum_range]
    refine sum_congr rfl fun i _ ↦ ?_
    simp only [a, P, i.2, ↓reduceDIte, v, z, Algebra.smul_def,
      algebraMap_polynomial_eq_coe, Polynomial.coe_mul, Polynomial.coe_pow]
    ring
  have hex : ∃ i, a i ≠ 0 := by
    refine ⟨i₀, ?_⟩
    simp only [a, P, i₀.2, ↓reduceDIte, ne_eq, Polynomial.coe_eq_zero_iff]
    exact mul_ne_zero hi₀ (pow_ne_zero _ hy0)
  set j := Nat.find hex
  have hj : a j ≠ 0 := Nat.find_spec hex
  have hjm : j < m := by
    by_contra h
    exact hj (by simp only [a, P, h, ↓reduceDIte, Polynomial.coe_zero])
  refine ⟨s.card, ∑ i ∈ range m, (P i).natDegree, j, a, fun i ↦ ?_,
    fun i hi ↦ not_not.mp (Nat.find_min hex hi), hj, by omega, hsum⟩
  by_cases hi : i < m
  · exact (isBoundedBy_coe (P i)).mono
      (single_le_sum (f := fun i ↦ (P i).natDegree) (fun _ _ ↦ Nat.zero_le _) (mem_range.mpr hi))
  · simp only [a, P, hi, ↓reduceDIte, Polynomial.coe_zero]
    exact isBoundedBy_zero _

/-- **Ore's normalization**: a Frobenius relation can be taken with `a_0 ≠ 0`. -/
theorem exists_frobenius_relation_ne_zero (hf : IsAlgebraic K[X] f) :
    ∃ n N : ℕ, ∃ a : ℕ → K⟦X⟧, (∀ i, IsBoundedBy N (a i)) ∧ a 0 ≠ 0 ∧
      ∑ i ∈ range (n + 1), a i * f ^ (Fintype.card K ^ i) = 0 := by
  set q := Fintype.card K with hqdef
  have hq : q ≠ 0 := Fintype.card_ne_zero
  obtain ⟨n, N, j, a, hN, hlt, hj, hjn, hrel⟩ := exists_frobenius_relation hf
  induction j generalizing n a with
  | zero => exact ⟨n, N, a, hN, hj, hrel⟩
  | succ j ih =>
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨r, hr, hr0⟩ : ∃ r < q, cartier q r (a (j + 1)) ≠ 0 := by
      by_contra h
      push Not at h
      exact hj (eq_zero_of_forall_cartier_eq_zero hq h)
    refine ih n (fun i ↦ cartier q r (a (i + 1))) (fun i ↦ ((hN (i + 1)).mono ?_).cartier hq r)
      (fun i hi ↦ by rw [hlt (i + 1) (by omega), cartier_zero]) hr0 (by omega) ?_
    · exact Nat.le_mul_of_pos_left N (Nat.pos_of_ne_zero hq)
    · rw [sum_range_succ', hlt 0 (by omega), zero_mul, add_zero] at hrel
      have := congrArg (cartier q r) hrel
      rw [cartier_sum, cartier_zero] at this
      rw [← this]
      refine sum_congr rfl fun i _ ↦ ?_
      rw [pow_succ, pow_mul, mul_comm (a (i + 1)), cartier_pow_card_mul hqdef.symm hr,
        mul_comm]

/-- **Christol's theorem**, algebraic ⇒ automatic: the coefficients of a power series algebraic
over `K[X]`, `K` a finite field with `q` elements, have a finite `q`-kernel. -/
theorem finite_kKernel_coeff_of_isAlgebraic (hf : IsAlgebraic K[X] f) :
    (Function.kKernel (Fintype.card K) fun m ↦ coeff m f).Finite := by
  classical
  set q := Fintype.card K with hqdef
  have hq2 : 2 ≤ q := Fintype.one_lt_card
  obtain ⟨k, hk⟩ : ∃ k, q = k + 2 := ⟨q - 2, by omega⟩
  obtain ⟨n, N, a, hN, ha0, hrel⟩ := exists_frobenius_relation_ne_zero hf
  set S : Set K⟦X⟧ := {s | ∃ c : ℕ → K⟦X⟧, (∀ i, IsBoundedBy N (c i)) ∧
    a 0 * s = ∑ i ∈ range (n + 1), c i * f ^ (q ^ i)}
  -- `H` is finite
  have hfin : S.Finite := by
    let φ : S → (Fin (n + 1) → Fin (N + 1) → K) :=
      fun s i m ↦ coeff (m : ℕ) (Classical.choose s.2 i)
    refine Set.finite_coe_iff.mp (Finite.of_injective φ fun s s' h ↦ Subtype.ext ?_)
    obtain ⟨hb, hs⟩ := Classical.choose_spec s.2
    obtain ⟨hb', hs'⟩ := Classical.choose_spec s'.2
    have hc : ∀ i < n + 1, Classical.choose s.2 i = Classical.choose s'.2 i := by
      intro i hi
      ext m
      by_cases hm : m ≤ N
      · exact congrFun (congrFun h ⟨i, hi⟩) ⟨m, by omega⟩
      · rw [hb i m (by omega), hb' i m (by omega)]
    refine mul_left_cancel₀ ha0 ?_
    rw [hs, hs']
    exact sum_congr rfl fun i hi ↦ by rw [hc i (mem_range.mp hi)]
  -- `f ∈ H`
  have hf : f ∈ S := by
    refine ⟨fun i ↦ if i = 0 then a 0 else 0, fun i ↦ ?_, ?_⟩
    · beta_reduce
      split_ifs
      · exact hN 0
      · exact isBoundedBy_zero N
    · simp [sum_ite_eq', ite_mul]
  -- `H` is stable under the Cartier operators
  have hstab : ∀ s ∈ S, ∀ r < q, cartier q r s ∈ S := by
    rintro s ⟨c, hc, hs⟩ r hr
    set d : ℕ → K⟦X⟧ := fun i ↦ a 0 ^ (k + 1) * c (i + 1) - a 0 ^ k * c 0 * a (i + 1)
    have hd : ∀ i, IsBoundedBy (q * N) (d i) := by
      intro i
      refine (((hN 0).pow (k + 1)).mul (hc (i + 1))).mono (le_of_eq (by rw [hk]; ring)) |>.sub
        ((((hN 0).pow k).mul (hc 0)).mul (hN (i + 1)) |>.mono (le_of_eq (by rw [hk]; ring)))
    refine ⟨fun i ↦ if i < n then cartier q r (d i) else 0, fun i ↦ ?_, ?_⟩
    · beta_reduce
      split_ifs
      · exact (hd i).cartier (by omega) r
      · exact isBoundedBy_zero N
    have hrel' : a 0 * f + ∑ i ∈ range n, a (i + 1) * f ^ (q ^ (i + 1)) = 0 := by
      rw [sum_range_succ', pow_zero, pow_one] at hrel
      rw [← hrel, add_comm]
    have hs' : a 0 * s = c 0 * f + ∑ i ∈ range n, c (i + 1) * f ^ (q ^ (i + 1)) := by
      rw [hs, sum_range_succ', pow_zero, pow_one, add_comm]
    have key : a 0 ^ q * s = ∑ i ∈ range n, (f ^ (q ^ i)) ^ q * d i := by
      have e : ∑ i ∈ range n, (f ^ (q ^ i)) ^ q * d i =
          a 0 ^ (k + 1) * ∑ i ∈ range n, c (i + 1) * f ^ (q ^ (i + 1)) -
            a 0 ^ k * c 0 * ∑ i ∈ range n, a (i + 1) * f ^ (q ^ (i + 1)) := by
        rw [mul_sum, mul_sum, ← sum_sub_distrib]
        refine sum_congr rfl fun i _ ↦ ?_
        rw [← pow_mul, ← pow_succ]
        simp only [d]
        ring
      rw [e, show a 0 ^ q = a 0 * a 0 ^ (k + 1) by rw [hk, ← pow_succ']]
      linear_combination a 0 ^ (k + 1) * hs' + a 0 ^ k * c 0 * hrel'
    rw [← cartier_pow_card_mul hqdef.symm hr, key, cartier_sum, sum_range_succ]
    simp only [lt_self_iff_false, ↓reduceIte, zero_mul, add_zero]
    refine sum_congr rfl fun i hi ↦ ?_
    simp only [cartier_pow_card_mul hqdef.symm hr, mem_range.mp hi, ↓reduceIte, mul_comm]
  -- the kernel lies in `H`
  have hker : ∀ i r, r < q ^ i →
      ∃ s ∈ S, (fun m ↦ coeff (q ^ i * m + r) f) = fun m ↦ coeff m s := by
    intro i
    induction i with
    | zero =>
      intro r hr
      obtain rfl : r = 0 := by simpa using hr
      exact ⟨f, hf, by simp⟩
    | succ i ih =>
      intro r hr
      have hqi : 0 < q ^ i := pow_pos (by omega) i
      obtain ⟨s, hs, hseq⟩ := ih (r % q ^ i) (Nat.mod_lt r hqi)
      have hr0 : r / q ^ i < q := Nat.div_lt_of_lt_mul (by rwa [← pow_succ])
      refine ⟨cartier q (r / q ^ i) s, hstab s hs _ hr0, funext fun m ↦ ?_⟩
      have e : q ^ (i + 1) * m + r = q ^ i * (q * m + r / q ^ i) + r % q ^ i := by
        conv_lhs => rw [← Nat.div_add_mod r (q ^ i)]
        ring
      rw [coeff_cartier, ← congrFun hseq, e]
  refine (hfin.image fun s m ↦ coeff m s).subset ?_
  rintro _ ⟨i, r, hr, rfl⟩
  obtain ⟨s, hs, hseq⟩ := hker i r hr
  exact ⟨s, hs, hseq.symm⟩

/-- **Christol's theorem**, algebraic ⇒ automatic, with `Function.IsAutomatic`. -/
theorem isAutomatic_coeff_of_isAlgebraic {K : Type*} [Field K] [Finite K] {f : K⟦X⟧}
    (hf : IsAlgebraic K[X] f) : Function.IsAutomatic fun m ↦ coeff m f :=
  have := Fintype.ofFinite K
  ⟨Fintype.card K, Fintype.one_lt_card, finite_kKernel_coeff_of_isAlgebraic hf⟩

end PowerSeries
