/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.RingTheory.MvPolynomial.EliminantForm
public import Mathlib.FieldTheory.IsAlgClosed.Basic

-- Used only inside proofs.
import ForMathlib.RingTheory.MvPolynomial.Associativity
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

/-!
# Specializations of eliminant forms

Rémond's Proposition 2.16 (G. Rémond, *Élimination multihomogène*, Chapter 5 of
Nesterenko–Philippon (eds.), *Introduction to algebraic independence theory*, LNM 1752 (2001)):
when all forms but the first are specialized into an algebraically closed field `L`, the
eliminant form `elim_d(𝔭)` becomes a product `c ∏_i U(z_i)` of specializations
`U(z) = ∑_m z^m u_m` of the first generic form at points `z_i`
(`exists_specEval_elimForm_eq`). This is what makes Mahler measures of resultant forms
computable from points (LNM 1752, Ch. 7).

## Main results

* `exists_X_sub_C_mul_X_mem`: if the variables of a block have rank one modulo a multihomogeneous
  prime `q` over `L`, they are proportional modulo `q`: the projection to that block is a point.
* `exists_pointForm_mem_elimIdeal`: hence `𝔈_{(e)}(q)` contains some `U(z)` when every block
  meeting the support of `e` has rank one.
* `irreducible_pointForm`: `U(z)` is irreducible when `z` has a nonzero coordinate in every block.
* `exists_blockRank_le_one_of_elimIdeal_ne_bot`: Thm 2.13 (1) for a single form.
* `exists_specEval_elimForm_eq`: Prop. 2.16. By the elimination theorem, the zeros of the
  specialization are the `u` with `U(x)(u) = 0` for some zero `x` of the specialized ideal `I`.
  By the Nullstellensatz, each prime factor then contains `𝔈_{(d₀)}(q)` for a minimal prime
  `q` of `I`, and that ideal contains some `U(z)`.

Rémond reduces to `L`-points of each component; here the components are the minimal primes of
`I`, and only the zero sets of their eliminant ideals are compared.
-/

@[expose] public section

open Finset

namespace MvPolynomial

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι}

section Point

variable {L : Type*} [Field L] [IsAlgClosed L] {q : Ideal (MvPolynomial σ L)} [q.IsPrime]

omit [Fintype σ] [Fintype ι] in
/-- **A block of rank one is a point**: if the variables of the block `j` have rank at most one
modulo a multihomogeneous prime `q` over an algebraically closed field and `x_t ∉ q`, then every
`x_s` of that block is a multiple of `x_t` modulo `q`. A relation between `x_t` and `x_s` has a
nonzero homogeneous component; dehomogenized, it makes `x_s / x_t` algebraic over `L`. -/
theorem exists_X_sub_C_mul_X_mem [Finite σ] (hq : q.IsWeightedHomogeneous (multiWeight b)) {j : ι}
    (hj : blockRank q b {j} ≤ 1) {t s : σ} (ht : b t = j) (hs : b s = j) (htq : X t ∉ q) :
    ∃ c : L, X s - C c * X t ∈ q := by
  classical
  have := Fintype.ofFinite σ
  by_cases hst : s = t
  · refine ⟨1, ?_⟩
    rw [hst, map_one, one_mul, sub_self]
    exact q.zero_mem
  set A := MvPolynomial σ L ⧸ q
  set x : σ → A := fun r ↦ Ideal.Quotient.mk q (X r)
  have hmk : ∀ P : MvPolynomial σ L, Ideal.Quotient.mk q P = aeval x P := fun P ↦ by
    change Ideal.Quotient.mkₐ L q P = _
    rw [MvPolynomial.aeval_unique (Ideal.Quotient.mkₐ L q)]
    rfl
  -- a nonzero polynomial relation `Q` between `x_t` and `x_s`
  have hdep : ¬AlgebraicIndepOn L x ↑({t, s} : Finset σ) := fun hind ↦ by
    have := card_le_blockRank_of_algebraicIndepOn (b := b) (J := {j}) hind (by
      intro r hr
      rcases Finset.mem_insert.mp hr with rfl | hr
      · simp [ht]
      · rw [Finset.mem_singleton.mp hr]
        simp [hs])
    rw [Finset.card_pair (Ne.symm hst)] at this
    omega
  rw [AlgebraicIndepOn, AlgebraicIndependent, injective_iff_map_eq_zero] at hdep
  push Not at hdep
  obtain ⟨P, hP, hP0⟩ := hdep
  set Q : MvPolynomial σ L := rename Subtype.val P
  have hQ : Q ∈ q := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, hmk, aeval_rename]
    exact hP
  have hQ0 : Q ≠ 0 := fun h ↦
    hP0 (rename_injective _ Subtype.val_injective (h.trans (map_zero _).symm))
  have hsupp : ∀ m ∈ Q.support, ∀ r, m r ≠ 0 → r = t ∨ r = s := by
    intro m hm r hr
    rw [support_rename_of_injective Subtype.val_injective, Finset.mem_image] at hm
    obtain ⟨n, -, rfl⟩ := hm
    by_contra hrs
    refine hr (Finsupp.mapDomain_of_notMem_range _ _ ?_)
    rintro ⟨⟨r', hr'⟩, rfl⟩
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hr'
    exact hrs hr'
  have hweight : ∀ m ∈ Q.support, Finsupp.weight (multiWeight b) m j = m t + m s := by
    intro m hm
    rw [weight_multiWeight_apply, ← Finset.sum_pair (Ne.symm hst)]
    refine (Finset.sum_subset (fun r hr ↦ ?_) fun r _ hr ↦ ?_).symm
    · rcases Finset.mem_insert.mp hr with rfl | hr
      · simp [ht]
      · rw [Finset.mem_singleton.mp hr]
        simp [hs]
    · by_contra h
      rcases hsupp m hm r h with rfl | rfl <;> simp at hr
  -- a nonzero homogeneous component `Qk ∈ q`, of degree `N` in `x_t, x_s`
  obtain ⟨m₀, hm₀⟩ := MvPolynomial.ne_zero_iff.mp hQ0
  set Qk := weightedHomogeneousComponent (multiWeight b)
    (Finsupp.weight (multiWeight b) m₀) Q
  have hQk : Qk ∈ q := hq hQ _
  have hcoeff : ∀ m, Qk.coeff m =
      if Finsupp.weight (multiWeight b) m = Finsupp.weight (multiWeight b) m₀ then Q.coeff m
      else 0 := fun m ↦ coeff_weightedHomogeneousComponent _ Q m
  have hsuppk : ∀ m ∈ Qk.support, m ∈ Q.support ∧ m t + m s = m₀ t + m₀ s := by
    intro m hm
    rw [mem_support_iff, hcoeff] at hm
    split_ifs at hm with hw
    · refine ⟨mem_support_iff.mpr hm, ?_⟩
      rw [← hweight m (mem_support_iff.mpr hm), ← hweight m₀ (mem_support_iff.mpr hm₀), hw]
    · exact absurd rfl hm
  have hm₀k : Qk.coeff m₀ ≠ 0 := by rwa [hcoeff, ite_eq_left rfl]
  -- the dehomogenized polynomial `p(S) = Qk(1, S)`
  set p : Polynomial L := ∑ m ∈ Qk.support, Polynomial.C (Qk.coeff m) * Polynomial.X ^ (m s)
  have hp0 : p ≠ 0 := by
    intro h0
    have := congrArg (Polynomial.coeff · (m₀ s)) h0
    simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero] at this
    rw [Finset.sum_eq_single m₀ (fun m hm hne ↦ ?_) (fun h ↦ absurd (mem_support_iff.mpr hm₀k) h),
      ite_eq_left rfl] at this
    · exact hm₀k this
    · rw [ite_eq_right]
      intro hms
      refine hne (Finsupp.ext fun r ↦ ?_)
      obtain ⟨hmQ, hN⟩ := hsuppk m hm
      by_cases hr : r = t ∨ r = s
      · rcases hr with rfl | rfl <;> omega
      · push Not at hr
        have h1 : m r = 0 := by_contra fun h ↦ (hsupp m hmQ r h).elim hr.1 hr.2
        have h2 : m₀ r = 0 := by_contra fun h ↦ (hsupp m₀ (mem_support_iff.mpr hm₀) r h).elim
          hr.1 hr.2
        rw [h1, h2]
  -- `x_s / x_t` is a root of `p`
  set F := FractionRing A
  set u : F := algebraMap A F (x t)
  set v : F := algebraMap A F (x s)
  have hu : u ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective A F), Ideal.Quotient.eq_zero_iff_mem]
    exact htq
  have hpw : Polynomial.aeval (v / u) p = 0 := by
    have h1 : algebraMap A F (aeval x Qk) = 0 := by
      rw [← hmk, Ideal.Quotient.eq_zero_iff_mem.mpr hQk, map_zero]
    rw [aeval_def, eval₂_eq, map_sum] at h1
    refine (mul_eq_zero.mp ?_).resolve_left (pow_ne_zero (m₀ t + m₀ s) hu)
    rw [← h1, map_sum (Polynomial.aeval (v / u)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm ↦ ?_
    obtain ⟨hmQ, hN⟩ := hsuppk m hm
    have hprod : ∏ i ∈ m.support, x i ^ m i = x t ^ m t * x s ^ m s := by
      rw [← Finset.prod_pair (f := fun i ↦ x i ^ m i) (Ne.symm hst)]
      refine Finset.prod_subset (fun r hr ↦ ?_) fun r _ hr ↦ ?_
      · rcases hsupp m hmQ r (Finsupp.mem_support_iff.mp hr) with rfl | rfl <;> simp
      · rw [Finsupp.notMem_support_iff.mp hr, pow_zero]
    rw [hprod]
    simp only [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
      ← IsScalarTower.algebraMap_apply]
    rw [← hN, div_pow]
    change _ = _ * (u ^ m t * v ^ m s)
    have h2 : u ^ m s * (v ^ m s / u ^ m s) = v ^ m s := mul_div_cancel₀ _ (pow_ne_zero _ hu)
    rw [pow_add]
    linear_combination (u ^ m t * algebraMap L F (Qk.coeff m)) * h2
  have hint : IsIntegral L (v / u) := (IsAlgebraic.isIntegral ⟨p, hp0, hpw⟩)
  have hdeg : (minpoly L (v / u)).natDegree = 1 :=
    Polynomial.natDegree_eq_of_degree_eq_some
      (IsAlgClosed.degree_eq_one_of_irreducible L (minpoly.irreducible hint))
  obtain ⟨c, hc⟩ := minpoly.natDegree_eq_one_iff.mp hdeg
  refine ⟨c, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem,
    ← map_eq_zero_iff (algebraMap A F) (IsFractionRing.injective A F), map_sub, map_mul,
    ← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap, map_sub, map_mul,
    ← IsScalarTower.algebraMap_apply L A F, hc]
  change v - v / u * u = 0
  rw [div_mul_cancel₀ v hu, sub_self]

end Point

section PointForm

variable {L : Type*} [Field L]

variable (b) in
/-- The specialization `U(z) = ∑_m z^m u_m` of a generic form of multidegree `e` at a point `z`:
the form in the coefficients `u_m` that vanishes when the form vanishes at `z`. -/
noncomputable def pointForm (e : ι → ℕ) (z : σ → L) :
    MvPolynomial (GenericVar b fun _ : Unit ↦ e) L :=
  eval (fun s ↦ C (z s)) (genericForm L b (fun _ : Unit ↦ e) ())

theorem pointForm_eq (e : ι → ℕ) (z : σ → L) :
    pointForm b e z = ∑ m : blockMonomials b e, C (∏ s, z s ^ (m : σ →₀ ℕ) s) * X ⟨(), m⟩ := by
  classical
  rw [pointForm, genericForm, map_sum]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun s ↦ pow_zero _), map_prod, mul_comm]
  simp only [map_pow]

theorem eval_pointForm (e : ι → ℕ) (z : σ → L) (a : GenericVar b (fun _ : Unit ↦ e) → L) :
    eval a (pointForm b e z) = eval₂ (eval a) z (genericForm L b (fun _ : Unit ↦ e) ()) := by
  rw [pointForm_eq, genericForm, map_sum, eval₂_sum]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [eval₂_monomial, eval_X, map_mul, eval_C, eval_X, mul_comm,
    Finsupp.prod_fintype _ _ (fun s ↦ pow_zero _)]

/-- `U(z)` is irreducible when `z` has a nonzero coordinate in every block: it is linear. -/
theorem irreducible_pointForm (e : ι → ℕ) {z : σ → L} (hz : ∀ i, ∃ s, b s = i ∧ z s ≠ 0) :
    Irreducible (pointForm b e z) := by
  classical
  choose t ht hzt using hz
  have hm₀ : ∑ i, Finsupp.single (t i) (e i) ∈ blockMonomials b e := by
    refine mem_blockMonomials.mpr ?_
    simp only [map_sum, Finsupp.weight_single, multiWeight, ht]
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  set m₀ : blockMonomials b e := ⟨_, hm₀⟩
  have hzm : ∏ s, z s ^ (m₀ : σ →₀ ℕ) s ≠ 0 := by
    have h1 : ∏ s, z s ^ (m₀ : σ →₀ ℕ) s = eval z (∏ i, X (t i) ^ e i) := by
      rw [← monomial_sum_single_eq_prod, eval_monomial, one_mul,
        Finsupp.prod_fintype _ _ (fun s ↦ pow_zero _)]
    rw [h1, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ by simpa using pow_ne_zero _ (hzt i)
  have hcoeff : (pointForm b e z).coeff (Finsupp.single ⟨(), m₀⟩ 1) =
      ∏ s, z s ^ (m₀ : σ →₀ ℕ) s := by
    rw [pointForm_eq, coeff_sum, Finset.sum_eq_single m₀]
    · rw [coeff_C_mul, coeff_X, ite_eq_left rfl, mul_one]
    · intro m _ hm
      have hne : Finsupp.single (⟨(), m⟩ : GenericVar b fun _ : Unit ↦ e) 1 ≠
          Finsupp.single ⟨(), m₀⟩ 1 := fun h ↦
        hm (eq_of_heq (Sigma.mk.inj_iff.mp (Finsupp.single_left_injective one_ne_zero h)).2)
      rw [coeff_C_mul, coeff_X, ite_eq_right hne, mul_zero]
    · simp
  refine irreducible_of_totalDegree_eq_one (le_antisymm ?_ ?_) fun x hx ↦ ?_
  · rw [pointForm_eq]
    refine totalDegree_finsetSum_le fun m _ ↦ ?_
    rw [C_mul_X_eq_monomial]
    exact (totalDegree_monomial_le _ _).trans (by simp)
  · have := le_totalDegree (mem_support_iff.mpr (hcoeff ▸ hzm))
    simpa using this
  · have := hx (Finsupp.single ⟨(), m₀⟩ 1)
    rw [hcoeff] at this
    exact isUnit_iff_ne_zero.mpr fun h0 ↦ hzm (zero_dvd_iff.mp (h0 ▸ this))

variable [IsAlgClosed L]

/-- **Point forms in eliminant ideals**: if every block meeting the support of `e` has rank one
modulo the multihomogeneous prime `q`, with `𝔪 ⊄ q`, then `𝔈_{(e)}(q)` contains `U(z)` for a
point `z` with a nonzero coordinate in every block. The variables of those blocks are multiples
of one of them modulo `q`, so `U ≡ U(z) x_t^e` modulo `q[u]`. -/
theorem exists_pointForm_mem_elimIdeal {q : Ideal (MvPolynomial σ L)} [q.IsPrime]
    (hq : q.IsWeightedHomogeneous (multiWeight b)) (hm : ¬irrelevantIdeal L b ≤ q)
    {e : ι → ℕ} {J : Set ι} (hJe : ∀ i, e i ≠ 0 → i ∈ J) (hJ : ∀ j ∈ J, blockRank q b {j} ≤ 1) :
    ∃ z : σ → L, (∀ i, ∃ s, b s = i ∧ z s ≠ 0) ∧
      pointForm b e z ∈ elimIdeal L b (fun _ : Unit ↦ e) q := by
  classical
  obtain ⟨t, ht, htq⟩ := exists_forall_X_notMem_of_not_le hm
  have hc : ∀ s, ∃ c : L, b s ∈ J → X s - C c * X (t (b s)) ∈ q := fun s ↦ by
    by_cases hs : b s ∈ J
    · obtain ⟨c, hc⟩ := exists_X_sub_C_mul_X_mem hq (hJ _ hs) (ht (b s)) rfl (htq (b s))
      exact ⟨c, fun _ ↦ hc⟩
    · exact ⟨1, fun h ↦ absurd h hs⟩
  choose c hc using hc
  set z : σ → L := fun s ↦ if b s ∈ J then c s else if s = t (b s) then 1 else 0
  refine ⟨z, fun i ↦ ⟨t i, ht i, ?_⟩, ?_⟩
  · by_cases hi : i ∈ J
    · have hz : z (t i) = c (t i) := by simp only [z, ht i, hi, ↓reduceIte]
      intro h0
      have := hc (t i) (by rwa [ht i])
      rw [ht i, ← hz, h0, map_zero, zero_mul, sub_zero] at this
      exact htq i this
    · simp only [z, ht i, hi, ↓reduceIte]
      exact one_ne_zero
  -- `x_s = z_s x_{t(b s)}` modulo `q`
  set y : σ → MvPolynomial σ L ⧸ q := fun s ↦ Ideal.Quotient.mk q (X s)
  have hy : ∀ s, b s ∈ J → y s = Ideal.Quotient.mk q (C (z s)) * y (t (b s)) := by
    intro s hs
    have := hc s hs
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, sub_eq_zero] at this
    simp only [y, z, hs, ↓reduceIte]
    exact this
  set T : MvPolynomial σ L := ∏ i, X (t i) ^ e i
  have hT : T ∉ q := by
    intro hmem
    obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact htq i (Ideal.IsPrime.mem_of_pow_mem inferInstance _ hi)
  set zm : (σ →₀ ℕ) → L := fun m ↦ ∏ s, z s ^ m s
  -- `x^m ≡ z^m x_t^e` modulo `q`
  have hmon : ∀ m ∈ blockMonomials b e, monomial m 1 - C (zm m) * T ∈ q := by
    intro m hm
    have hw := mem_blockMonomials.mp hm
    have h1 : ∀ s, y s ^ m s = (Ideal.Quotient.mk q (C (z s)) * y (t (b s))) ^ m s := by
      intro s
      by_cases hms : m s = 0
      · rw [hms, pow_zero, pow_zero]
      · refine congrArg (· ^ m s) (hy s (hJe _ fun h0 ↦ hms ?_))
        rw [← hw, weight_multiWeight_apply] at h0
        exact (Finset.sum_eq_zero_iff.mp h0) s (by simp)
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, monomial_eq, C_1, one_mul,
      Finsupp.prod_fintype _ _ (fun s ↦ pow_zero _)]
    simp only [T, zm, map_mul, map_prod, map_pow]
    change ∏ s, y s ^ m s = (∏ s, Ideal.Quotient.mk q (C (z s)) ^ m s) * ∏ i, y (t i) ^ e i
    rw [Finset.prod_congr rfl fun s _ ↦ h1 s]
    simp only [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [← Finset.prod_fiberwise Finset.univ b (fun s ↦ y (t (b s)) ^ m s)]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [Finset.prod_congr rfl (fun s hs ↦ by rw [(Finset.mem_filter.mp hs).2]),
      Finset.prod_pow_eq_pow_sum, ← weight_multiWeight_apply, hw]
  -- `U(z) x_t^e ∈ q[u] + (U)`
  have hgen : C (pointForm b e z) * map C T ∈ genericIdeal L b (fun _ : Unit ↦ e) q := by
    have heq : C (pointForm b e z) * map C T = genericForm L b (fun _ : Unit ↦ e) () -
        ∑ m : blockMonomials b e, C (X ⟨(), m⟩) *
          map C (monomial (m : σ →₀ ℕ) 1 - C (zm m) * T) := by
      rw [pointForm_eq, genericForm, map_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun m _ ↦ ?_
      simp only [zm, map_sub, map_mul, map_monomial, map_C, map_one]
      have h : (C (X ⟨(), m⟩) : MvPolynomial σ (MvPolynomial (GenericVar b fun _ : Unit ↦ e) L)) *
          monomial (m : σ →₀ ℕ) 1 = monomial (m : σ →₀ ℕ) (X ⟨(), m⟩) := by
        rw [C_mul_monomial, mul_one]
      linear_combination h
    rw [heq]
    exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.subset_span ⟨(), rfl⟩))
      (Ideal.mem_sup_left (Ideal.sum_mem _ fun m _ ↦
        Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hmon m m.2))))
  have := isPrime_charIdeal (d := fun _ : Unit ↦ e) hm
  have hTc : map C T ∉ charIdeal L b (fun _ : Unit ↦ e) q := fun h ↦ hT (by
    have h' : T ∈ (charIdeal L b (fun _ : Unit ↦ e) q).comap (map C) := h
    rwa [comap_map_C_charIdeal hm] at h')
  exact (Ideal.IsPrime.mem_or_mem this (le_saturation _ hgen)).resolve_right hTc

end PointForm

/-- Products of associated factors are associated. -/
theorem _root_.Multiset.prod_associated_prod_map {M : Type*} [CommMonoid M] (s : Multiset M)
    (f : M → M) (h : ∀ a ∈ s, Associated a (f a)) : Associated s.prod (s.map f).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons]
    exact (h a (Multiset.mem_cons_self a s)).mul_mul
      (ih fun c hc ↦ h c (Multiset.mem_cons_of_mem hc))

theorem eval₂_genericForm {R S : Type*} [CommRing R] [CommRing S] {κ : Type*}
    {d : κ → ι → ℕ} (ψ : MvPolynomial (GenericVar b d) R →+* S) (x : σ → S) (l : κ) :
    eval₂ ψ x (genericForm R b d l) =
      ∑ m : blockMonomials b (d l), ψ (X ⟨l, m⟩) * ∏ s, x s ^ (m : σ →₀ ℕ) s := by
  rw [genericForm, eval₂_sum]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [eval₂_monomial, Finsupp.prod_fintype _ _ (fun s ↦ pow_zero _)]

section SpecEval

variable {K L : Type*} [Field K] [Field L] {κ : Type*} {d : Option κ → ι → ℕ}

variable (b) in
/-- Specializing the coefficients of the forms `d (some l)` to `y` and the coefficients of `K`
along `φ`, keeping the coefficients `u_m` of the form `d none`:
`K[d] → L[u^{(0)}]`. -/
noncomputable def specEval (φ : K →+* L) (y : GenericVar b (fun l : κ ↦ d (some l)) → L) :
    MvPolynomial (GenericVar b d) K →+* MvPolynomial (GenericVar b fun _ : Unit ↦ d none) L :=
  eval₂Hom (C.comp φ) fun
    | ⟨none, m⟩ => X ⟨(), m⟩
    | ⟨some l, m⟩ => C (y ⟨l, m⟩)

end SpecEval

section Specialize

universe u

variable {σ ι : Type u} [Fintype σ] [Fintype ι] [DecidableEq ι] {b : σ → ι}

/-- **A single form with a nonzero eliminant ideal**: by Thm 2.13 (1), the support of its
multidegree lies in a set of blocks `J` with `blockRank = |J|`, so each block of `J` has rank
one. -/
theorem exists_blockRank_le_one_of_elimIdeal_ne_bot (hb : Function.Surjective b) {L : Type u}
    [Field L] {q : Ideal (MvPolynomial σ L)} [q.IsPrime]
    (hq : q.IsWeightedHomogeneous (multiWeight b)) (hm : ¬irrelevantIdeal L b ≤ q)
    {e : ι → ℕ} (h : elimIdeal L b (fun _ : Unit ↦ e) q ≠ ⊥) :
    ∃ J : Finset ι, (∀ i, e i ≠ 0 → i ∈ J) ∧ ∀ j ∈ J, blockRank q b ({j} : Set ι) ≤ 1 := by
  classical
  have h' : elimIdeal L b (fun _ : PUnit.{u + 1} ↦ e) q ≠ ⊥ := fun h0 ↦
    h ((elimIdeal_comp_eq_bot_iff Equiv.punitEquivPUnit (fun _ : PUnit.{u + 1} ↦ e) q).mpr h0)
  rw [Ne, elimIdeal_eq_bot_iff hb hq] at h'
  push Not at h'
  obtain ⟨J, hJ⟩ := h' hm
  have hne := hilbertPoly_ne_zero_of_not_le hb hq hm
  have hcard := card_le_blockRank hb hq hne J
  have hle : numForms (fun _ : PUnit.{u + 1} ↦ e) (J : Set ι) ≤ 1 :=
    (Nat.card_le_card_of_injective (fun x ↦ x.1) fun _ _ h ↦ Subtype.ext h).trans (by simp)
  have hpos : 0 < numForms (fun _ : PUnit.{u + 1} ↦ e) (J : Set ι) := by omega
  obtain ⟨⟨_, hl⟩⟩ := (Nat.card_pos_iff.mp hpos).1
  refine ⟨J, hl, fun j hj ↦ ?_⟩
  obtain ⟨α, -, -, h1, h2⟩ := exists_coeff_hilbertPoly_ne_zero_blockRank hb hq hne
    (Finset.singleton_subset_iff.mpr hj)
  have hαj : α j ≤ ∑ i ∈ J, α i := Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hj
  rw [Finset.sum_singleton, Finset.card_singleton, Finset.coe_singleton] at h1
  omega

variable {K L : Type u} [Field K] [Field L] [IsAlgClosed L] {κ : Type u}

/-- **Rémond's Prop. 2.16**: specializing all forms but the first into an algebraically closed
field, the eliminant form becomes `c ∏_i U(z_i)` for points `z_i` with a nonzero coordinate in
every block. The zeros of the specialization are the `u` with `U(x)(u) = 0` for a zero `x` of
`I = (φ(𝔭), U_l(y))` (elimination theorem); so each prime factor contains `𝔈_{(d₀)}(q)` for a
minimal prime `q` of `I` (Nullstellensatz). This ideal is not zero, so the blocks of `d₀` have
rank one modulo `q` (Thm 2.13 (1)), and it contains some `U(z)`. Rémond states this for primes;
with `elimForm` it holds for any multihomogeneous ideal. -/
theorem exists_specEval_elimForm_eq (hb : Function.Surjective b) {𝔭 : Ideal (MvPolynomial σ K)}
    (h𝔭 : 𝔭.IsWeightedHomogeneous (multiWeight b)) (d : Option κ → ι → ℕ)
    (φ : K →+* L) (y : GenericVar b (fun l : κ ↦ d (some l)) → L) :
    ∃ (c : L) (Z : Multiset (σ → L)), (∀ z ∈ Z, ∀ i, ∃ s, b s = i ∧ z s ≠ 0) ∧
      specEval b φ y (elimForm K b d 𝔭) = C c * (Z.map (pointForm b (d none))).prod := by
  classical
  obtain ⟨G, hGdef⟩ : ∃ G, G = specEval b φ y (elimForm K b d 𝔭) := ⟨_, rfl⟩
  rw [← hGdef]
  by_cases hG : G = 0
  · exact ⟨0, 0, by simp, by rw [hG, map_zero, zero_mul]⟩
  by_cases hf : (elimIdeal K b d 𝔭).IsPrincipal ∧ elimIdeal K b d 𝔭 ≠ ⊤
  swap
  · refine ⟨1, 0, by simp, ?_⟩
    rw [hGdef, elimForm, dite_eq_right hf]
    simp
  have hspan := span_elimForm_of_isPrincipal hf.1
  -- the specialized ideal `I = (φ(𝔭), U_l(y))` of `L[X]`
  set yU : κ → MvPolynomial σ L := fun l ↦
    map (eval₂Hom φ y) (genericForm K b (fun l : κ ↦ d (some l)) l)
  set I : Ideal (MvPolynomial σ L) := 𝔭.map (map φ) ⊔ Ideal.span (Set.range yU)
  have hI : I.IsWeightedHomogeneous (multiWeight b) := by
    refine (h𝔭.map φ).sup (isWeightedHomogeneous_span ?_)
    rintro _ ⟨l, rfl⟩
    refine ⟨d (some l), fun m hm ↦ isWeightedHomogeneous_genericForm (R := K)
      (d := fun l : κ ↦ d (some l)) l fun h0 ↦ hm ?_⟩
    rw [coeff_map, h0, map_zero]
  -- zeros of `G`: `G(a) = 0` iff `U(x)(a) = 0` for a zero `x` of `I`
  have E1 : ∀ a (x : σ → L) (p : MvPolynomial σ K),
      eval₂ ((eval a).comp (specEval b φ y)) x (map C p) = eval x (map φ p) := by
    intro a x p
    rw [eval₂_map, eval_map]
    congr 1
    exact RingHom.ext fun k ↦ by simp [specEval]
  have E2 : ∀ a (x : σ → L) (l : κ),
      eval₂ ((eval a).comp (specEval b φ y)) x (genericForm K b d (some l)) = eval x (yU l) := by
    intro a x l
    rw [eval_map, eval₂_genericForm, eval₂_genericForm]
    simp [specEval]
  have E3 : ∀ a (x : σ → L),
      eval₂ ((eval a).comp (specEval b φ y)) x (genericForm K b d none) =
        eval a (pointForm b (d none) x) := by
    intro a x
    rw [eval_pointForm, eval₂_genericForm, eval₂_genericForm]
    simp [specEval]
  have KZ : ∀ a, eval a G = 0 ↔ ∃ x : σ → L, (∀ i, ∃ s, b s = i ∧ x s ≠ 0) ∧
      I ≤ RingHom.ker (eval x) ∧ eval a (pointForm b (d none) x) = 0 := by
    intro a
    have h1 : eval a G = 0 ↔
        elimIdeal K b d 𝔭 ≤ RingHom.ker ((eval a).comp (specEval b φ y)) := by
      rw [← hspan, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, hGdef]
      rfl
    rw [h1, elimIdeal_le_ker_iff h𝔭]
    refine exists_congr fun x ↦ and_congr_right fun _ ↦
      ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨h, h'⟩ P hP ↦ ?_⟩
    · refine sup_le (Ideal.map_le_iff_le_comap.mpr fun p hp ↦ ?_) (Ideal.span_le.mpr ?_)
      · rw [Ideal.mem_comap, RingHom.mem_ker, ← E1 a x]
        exact h _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hp))
      · rintro _ ⟨l, rfl⟩
        rw [SetLike.mem_coe, RingHom.mem_ker, ← E2 a x]
        exact h _ (Ideal.mem_sup_right (Ideal.subset_span ⟨some l, rfl⟩))
    · rw [← E3 a x]
      exact h _ (Ideal.mem_sup_right (Ideal.subset_span ⟨none, rfl⟩))
    · have hle : genericIdeal K b d 𝔭 ≤
          RingHom.ker (eval₂Hom ((eval a).comp (specEval b φ y)) x) := by
        refine sup_le (Ideal.map_le_iff_le_comap.mpr fun p hp ↦ ?_) (Ideal.span_le.mpr ?_)
        · rw [Ideal.mem_comap, RingHom.mem_ker, coe_eval₂Hom, E1 a x]
          exact h (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hp))
        · rintro _ ⟨_ | l, rfl⟩
          · rw [SetLike.mem_coe, RingHom.mem_ker, coe_eval₂Hom, E3 a x]
            exact h'
          · rw [SetLike.mem_coe, RingHom.mem_ker, coe_eval₂Hom, E2 a x]
            exact h (Ideal.mem_sup_right (Ideal.subset_span ⟨l, rfl⟩))
      exact RingHom.mem_ker.mp (hle hP)
  -- the same for the minimal primes `q` of `I` and `P_q = 𝔈_{(d₀)}(q)`
  have hMfin : I.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ I
  have hcomp : ∀ a : GenericVar b (fun _ : Unit ↦ d none) → L, (eval a).comp C = RingHom.id L :=
    fun a ↦ RingHom.ext fun c ↦ eval_C c
  have KZq : ∀ q ∈ I.minimalPrimes, ∀ a, elimIdeal L b (fun _ : Unit ↦ d none) q ≤
      RingHom.ker (eval a) ↔ ∃ x : σ → L, (∀ i, ∃ s, b s = i ∧ x s ≠ 0) ∧
        q ≤ RingHom.ker (eval x) ∧ eval a (pointForm b (d none) x) = 0 := by
    intro q hq a
    rw [elimIdeal_le_ker_iff (Ideal.IsWeightedHomogeneous.of_mem_minimalPrimes hI hq)]
    refine exists_congr fun x ↦ and_congr_right fun _ ↦
      ⟨fun h ↦ ⟨fun p hp ↦ ?_, ?_⟩, fun ⟨h, h'⟩ P hP ↦ ?_⟩
    · have := h _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem (map C) hp))
      rw [eval₂_map, hcomp] at this
      exact this
    · rw [eval_pointForm]
      exact h _ (Ideal.mem_sup_right (Ideal.subset_span ⟨(), rfl⟩))
    · have hle : genericIdeal L b (fun _ : Unit ↦ d none) q ≤
          RingHom.ker (eval₂Hom (eval a) x) := by
        refine sup_le (Ideal.map_le_iff_le_comap.mpr fun p hp ↦ ?_) (Ideal.span_le.mpr ?_)
        · rw [Ideal.mem_comap, RingHom.mem_ker, coe_eval₂Hom, eval₂_map, hcomp]
          exact h hp
        · rintro _ ⟨⟨⟩, rfl⟩
          rw [SetLike.mem_coe, RingHom.mem_ker, coe_eval₂Hom, ← eval_pointForm]
          exact h'
      exact RingHom.mem_ker.mp (hle hP)
  -- `V(G) = ⋃_q V(𝔈_{(d₀)}(q))`
  have hVa : ∀ a, eval a G = 0 → ∃ q ∈ I.minimalPrimes,
      elimIdeal L b (fun _ : Unit ↦ d none) q ≤ RingHom.ker (eval a) := by
    intro a ha
    obtain ⟨x, hx, hIx, hax⟩ := (KZ a).mp ha
    have := RingHom.ker_isPrime (eval x)
    obtain ⟨q, hq, hqx⟩ := Ideal.exists_minimalPrimes_le hIx
    exact ⟨q, hq, (KZq q hq a).mpr ⟨x, hx, hqx, hax⟩⟩
  have hVb : ∀ q ∈ I.minimalPrimes, ∀ a,
      elimIdeal L b (fun _ : Unit ↦ d none) q ≤ RingHom.ker (eval a) → eval a G = 0 := by
    intro q hq a ha
    obtain ⟨x, hx, hqx, hax⟩ := (KZq q hq a).mp ha
    exact (KZ a).mpr ⟨x, hx, hq.1.2.trans hqx, hax⟩
  -- the Nullstellensatz
  have hNS : ∀ (E : Ideal (MvPolynomial (GenericVar b fun _ : Unit ↦ d none) L)) h,
      (∀ a, E ≤ RingHom.ker (eval a) → eval a h = 0) → h ∈ E.radical := by
    intro E h hh
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := L)]
    intro a ha
    exact hh a fun p hp ↦ ha p hp
  -- each prime factor of `G` is associated to some `U(z)`
  have key : ∀ g ∈ UniqueFactorizationMonoid.factors G, ∃ z : σ → L,
      (∀ i, ∃ s, b s = i ∧ z s ≠ 0) ∧ Associated g (pointForm b (d none) z) := by
    intro g hg
    have hgirr := UniqueFactorizationMonoid.irreducible_of_factor g hg
    have hgp : (Ideal.span {g}).IsPrime := (Ideal.span_singleton_prime hgirr.ne_zero).mpr
      (UniqueFactorizationMonoid.prime_of_factor g hg)
    have hgG : G ∈ Ideal.span {g} :=
      Ideal.mem_span_singleton.mpr (UniqueFactorizationMonoid.dvd_of_mem_factors hg)
    have hinf : hMfin.toFinset.inf (fun q ↦ elimIdeal L b (fun _ : Unit ↦ d none) q) ≤
        Ideal.span {g} := by
      intro h hh
      obtain ⟨n, hn⟩ := hNS _ h fun a ha ↦ by
        obtain ⟨q, hq, hqa⟩ := hVa a (ha (Ideal.mem_span_singleton_self G))
        exact hqa (Finset.inf_le (f := fun q ↦ elimIdeal L b (fun _ : Unit ↦ d none) q)
          (hMfin.mem_toFinset.mpr hq) hh)
      exact hgp.mem_of_pow_mem n ((Ideal.span_singleton_le_iff_mem _).mpr hgG hn)
    obtain ⟨q, hq, hqg⟩ := (hgp.inf_le').mp hinf
    rw [Set.Finite.mem_toFinset] at hq
    have : q.IsPrime := hq.1.1
    have hqh := Ideal.IsWeightedHomogeneous.of_mem_minimalPrimes hI hq
    have hmq : ¬irrelevantIdeal L b ≤ q := fun hle ↦ by
      rw [elimIdeal_eq_top_of_le hle, top_le_iff, Ideal.span_singleton_eq_top] at hqg
      exact hgirr.not_isUnit hqg
    have hGq : G ∈ elimIdeal L b (fun _ : Unit ↦ d none) q := by
      have hpr := isPrime_elimIdeal (d := fun _ : Unit ↦ d none) hmq
      rw [← hpr.radical]
      exact hNS _ G fun a ha ↦ hVb q hq a ha
    have hne : elimIdeal L b (fun _ : Unit ↦ d none) q ≠ ⊥ := fun h0 ↦
      hG (Ideal.mem_bot.mp (h0 ▸ hGq))
    obtain ⟨J, hJe, hJ⟩ := exists_blockRank_le_one_of_elimIdeal_ne_bot hb hqh hmq hne
    obtain ⟨z, hz, hzq⟩ := exists_pointForm_mem_elimIdeal hqh hmq (J := (J : Set ι)) hJe
      fun j hj ↦ hJ j hj
    exact ⟨z, hz, hgirr.associated_of_dvd (irreducible_pointForm (d none) hz)
      (Ideal.mem_span_singleton.mp (hqg hzq))⟩
  choose! zf hzf hzg using key
  have hassoc : Associated ((UniqueFactorizationMonoid.factors G).map
      (pointForm b (d none) ∘ zf)).prod G :=
    (Multiset.prod_associated_prod_map _ _ hzg).symm.trans
      (UniqueFactorizationMonoid.factors_prod hG)
  obtain ⟨v, hv⟩ := hassoc
  obtain ⟨c, -, hc⟩ := isUnit_iff_eq_C_of_isReduced.mp v.isUnit
  refine ⟨c, (UniqueFactorizationMonoid.factors G).map zf, fun z hz ↦ ?_, ?_⟩
  · obtain ⟨g, hg, rfl⟩ := Multiset.mem_map.mp hz
    exact hzf g hg
  · rw [Multiset.map_map]
    calc G = _ * ↑v := hv.symm
      _ = _ := by rw [hc, mul_comm]

end Specialize

end MvPolynomial

end
