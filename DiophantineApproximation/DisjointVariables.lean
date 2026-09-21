/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.Polynomial
public import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Polynomials in disjoint sets of variables

The height of a product is not the product of the heights — Gelfond's inequality has a constant
in it, and the constant is not removable. In **one** situation it is: when the two factors use
disjoint sets of variables. Then no cancellation and no addition can happen between coefficients,
because the antidiagonal of an exponent of `σ ⊕ τ` meets the two supports in exactly one point,
so the coefficients of the product are precisely the pairwise products of the coefficients of the
factors. That makes the height of the product the height of a *multiplication table*, which is
Mathlib's Segre relation `Height.mulHeight_fun_mul_eq`, and the identity is exact at every
absolute value at once.

This is the identity `h(U · V) = h(U) + h(V)` on which Roth's lemma turns: the induction there
splits an auxiliary polynomial as `∑ f_j(x_1, …, x_{m-1}) g_j(x_m)` and multiplies two
generalized Wronskians in disjoint variables, and a constant lost at that step would accumulate
over the `m` steps of the induction and destroy the bound.

## Main results

* `Finsupp.iSup_apply_eq_iSup_mul_iSup` and `Finsupp.mulHeight_eq_mulHeight_mul_mulHeight`: the
  statement with nothing about polynomials in it. A finitely supported family that is the
  multiplication table of two others along an injection has, at every absolute value, the product
  of their local factors, and its height is the product of their heights.
* `MvPolynomial.coeff_sumElim_rename_mul_rename`: **the coefficients of a product in disjoint
  variables are the pairwise products of the coefficients**, an identity over any commutative
  semiring.
* `MvPolynomial.iSup_coeff_rename_inl_mul_rename_inr`: the local factor is multiplicative at
  **every** absolute value, archimedean or not, with no hypothesis on either factor.
* `MvPolynomial.mulHeight_rename_inl_mul_rename_inr` and its logarithmic form: **Bombieri–Gubler,
  Proposition 1.6.2**, the exact height identity.
* `MvPolynomial.mulHeight_rename_of_injective`: renaming the variables injectively leaves the
  height alone — the coefficients are permuted and nothing else happens.
* `MvPolynomial.mulHeight_rename_mul_rename_of_disjoint`: the form Layer 2.7 consumes, with the
  two factors embedded into one variable set along injections with disjoint ranges.

## Implementation notes

⚠ **The local factor needs no hypothesis; the height needs two.** At an absolute value the
identity `⨆ v (coeff (F G)) = (⨆ v (coeff F)) (⨆ v (coeff G))` holds for all `f` and `g`,
including `f = 0`, where both sides are `0`. The height identity does not: `mulHeight 0 = 1` is a
junk value, so at `f = 0` the left side is `1` and the right side is `mulHeight g`, which is
anything at all. This is the same asymmetry as in Gauss's lemma, and it is pinned by a rejection
test below.

⚠ **No ultrametric hypothesis appears anywhere.** Gauss's lemma —
`MvPolynomial.iSup_coeff_mul` of the `ArithmeticHeights` roadmap — needs `IsNonarchimedean` and
is false without it. Here the archimedean places behave exactly as the finite ones do, because
there is no sum of several terms to which a triangle inequality could be applied: the
antidiagonal contributes one term.

⚠ **Nothing needs `NoZeroDivisors`, and nothing needs a field until a height is mentioned.** The
coefficient identity holds over a commutative semiring, so the support of the product is the
image of the product of the supports as soon as the ring has no zero divisors — that statement is
not made here, because no consumer needs it and the coefficient identity is strictly stronger.

⚠ **The first section belongs to the other roadmap.** `Finsupp.iSup_apply_eq_iSup_mul_iSup` and
`Finsupp.mulHeight_eq_mulHeight_mul_mulHeight` say nothing about polynomials; they are the
companion of `ArithmeticHeights`'s `Finsupp.mulHeight_le_of_forall_iSup_le` for the case where
the comparison is an equality on the nose, and they are written so that they can move into
`ArithmeticHeights/Polynomial.lean` unchanged if that roadmap wants them.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Proposition 1.6.2 and §1.5.14 for the Segre relation behind it.

This is Layer 2.2 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

noncomputable section

namespace Finsupp

open Height

variable {K : Type*} [Field K] {α β γ : Type*}

/-!
### A multiplication table, abstractly

A family `z : γ →₀ K` is a multiplication table of `x` and `y` when an injection
`e : α × β → γ` carries `(a, b)` to an index where `z` is `x a * y b`, and `z` vanishes off the
range of `e`. Nothing below is special to polynomials.
-/

/-- The restriction of a nonzero `Finsupp` to its support is a nonzero tuple. -/
theorem restrict_ne_zero {x : α →₀ K} (hx : x ≠ 0) : (fun i : x.support ↦ x i.val) ≠ 0 := by
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hx
  exact Function.ne_iff.mpr ⟨⟨i, hi⟩, Finsupp.mem_support_iff.mp hi⟩

/-- **The local factor of a multiplication table is the product of the local factors.** No
absolute value is assumed nonarchimedean and no family is assumed nonzero: at `x = 0` both sides
are `0`. -/
theorem iSup_apply_eq_iSup_mul_iSup {x : α →₀ K} {y : β →₀ K} {z : γ →₀ K} {e : α × β → γ}
    (hmul : ∀ p : α × β, z (e p) = x p.1 * y p.2) (hzero : ∀ c, c ∉ Set.range e → z c = 0)
    (v : AbsoluteValue K ℝ) :
    (⨆ c : γ, v (z c)) = (⨆ a : α, v (x a)) * ⨆ b : β, v (y b) := by
  have hx0 : (0 : ℝ) ≤ ⨆ a : α, v (x a) := Real.iSup_nonneg fun _ ↦ v.nonneg _
  have hy0 : (0 : ℝ) ≤ ⨆ b : β, v (y b) := Real.iSup_nonneg fun _ ↦ v.nonneg _
  refine le_antisymm (Real.iSup_le (fun c ↦ ?_) (by positivity)) ?_
  · rcases em (c ∈ Set.range e) with ⟨p, rfl⟩ | hc
    · rw [hmul p, map_mul]
      exact mul_le_mul (le_ciSup (bddAbove_range_apply x v) p.1)
        (le_ciSup (bddAbove_range_apply y v) p.2) (v.nonneg _) hx0
    · rw [hzero c hc, map_zero]
      positivity
  · rw [iSup_apply_eq_iSup_support x v, iSup_apply_eq_iSup_support y v,
      ← Real.iSup_fun_mul_eq_iSup_mul_iSup_of_nonneg v (fun i : x.support ↦ x i.val)
        (fun i : y.support ↦ y i.val)]
    refine Real.iSup_le (fun p ↦ ?_) (Real.iSup_nonneg fun _ ↦ v.nonneg _)
    rw [← hmul (p.1.val, p.2.val)]
    exact le_ciSup (bddAbove_range_apply z v) _

variable [AdmissibleAbsValues K]

/-- **The height of a multiplication table is the product of the heights.** The nonvanishing
hypotheses are not removable: at `x = 0` the left side is the junk value `1` and the right side
is `y.mulHeight`. -/
theorem mulHeight_eq_mulHeight_mul_mulHeight {x : α →₀ K} {y : β →₀ K} {z : γ →₀ K}
    {e : α × β → γ} (he : Function.Injective e) (hmul : ∀ p : α × β, z (e p) = x p.1 * y p.2)
    (hzero : ∀ c, c ∉ Set.range e → z c = 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    z.mulHeight = x.mulHeight * y.mulHeight := by
  have hinj : Function.Injective fun p : x.support × y.support ↦ e (p.1.val, p.2.val) := by
    intro p q h
    have h' := he h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h')) (Subtype.ext (congrArg Prod.snd h'))
  have hcov : ∀ c ∈ z.support,
      c ∈ Set.range fun p : x.support × y.support ↦ e (p.1.val, p.2.val) := by
    intro c hc
    have hc' : z c ≠ 0 := Finsupp.mem_support_iff.mp hc
    obtain ⟨p, rfl⟩ : c ∈ Set.range e := by
      by_contra h
      exact hc' (hzero c h)
    rw [hmul p] at hc'
    exact ⟨⟨⟨p.1, mem_support_iff.mpr (left_ne_zero_of_mul hc')⟩,
      ⟨p.2, mem_support_iff.mpr (right_ne_zero_of_mul hc')⟩⟩, rfl⟩
  have h1 : z.mulHeight
      = Height.mulHeight fun p : x.support × y.support ↦ z (e (p.1.val, p.2.val)) :=
    mulHeight_eq_mulHeight_comp z _ hinj hcov
  have h2 : (fun p : x.support × y.support ↦ z (e (p.1.val, p.2.val)))
      = fun p : x.support × y.support ↦ x p.1.val * y p.2.val :=
    funext fun p ↦ hmul _
  have h3 : Height.mulHeight (fun p : x.support × y.support ↦ x p.1.val * y p.2.val)
      = Height.mulHeight (fun i : x.support ↦ x i.val)
        * Height.mulHeight (fun i : y.support ↦ y i.val) :=
    Height.mulHeight_fun_mul_eq (restrict_ne_zero hx) (restrict_ne_zero hy)
  rw [h1, h2, h3, ← mulHeight_eq_mulHeight_subtype x (Finset.Subset.refl _),
    ← mulHeight_eq_mulHeight_subtype y (Finset.Subset.refl _)]

/-- The logarithmic form of `Finsupp.mulHeight_eq_mulHeight_mul_mulHeight`. -/
theorem logHeight_eq_logHeight_add_logHeight {x : α →₀ K} {y : β →₀ K} {z : γ →₀ K}
    {e : α × β → γ} (he : Function.Injective e) (hmul : ∀ p : α × β, z (e p) = x p.1 * y p.2)
    (hzero : ∀ c, c ∉ Set.range e → z c = 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    z.logHeight = x.logHeight + y.logHeight := by
  rw [logHeight_eq, logHeight_eq, logHeight_eq,
    mulHeight_eq_mulHeight_mul_mulHeight he hmul hzero hx hy,
    Real.log_mul (mulHeight_ne_zero x) (mulHeight_ne_zero y)]

end Finsupp

namespace Finsupp

variable {M : Type*} [AddCommMonoid M] {α β : Type*}

/-- An exponent carried by the left variables is not one carried by the right variables. -/
theorem mapDomain_inl_apply_inr (m : α →₀ M) (b : β) :
    Finsupp.mapDomain (Sum.inl : α → α ⊕ β) m (Sum.inr b) = 0 :=
  Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨a, ha⟩; simp at ha)

/-- An exponent carried by the right variables is not one carried by the left variables. -/
theorem mapDomain_inr_apply_inl (n : β →₀ M) (a : α) :
    Finsupp.mapDomain (Sum.inr : β → α ⊕ β) n (Sum.inl a) = 0 :=
  Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨b, hb⟩; simp at hb)

/-- The family that is `m` on the left indices and `n` on the right ones is the sum of the two
transported separately. This is the additive content of `Finsupp.sumFinsuppAddEquivProdFinsupp`,
in the form the antidiagonal of a product of polynomials needs. -/
theorem sumElim_eq_mapDomain_add (m : α →₀ M) (n : β →₀ M) :
    Finsupp.sumElim m n
      = Finsupp.mapDomain (Sum.inl : α → α ⊕ β) m + Finsupp.mapDomain (Sum.inr : β → α ⊕ β) n := by
  ext c
  cases c with
  | inl a =>
      rw [Finsupp.add_apply, Finsupp.mapDomain_apply_of_injective Sum.inl_injective,
        mapDomain_inr_apply_inl, add_zero]
      rfl
  | inr b =>
      rw [Finsupp.add_apply, Finsupp.mapDomain_apply_of_injective Sum.inr_injective,
        mapDomain_inl_apply_inr, zero_add]
      rfl

/-- A pairing of two halves determines both halves. -/
theorem sumElim_inj {m m' : α →₀ M} {n n' : β →₀ M}
    (h : Finsupp.sumElim m n = Finsupp.sumElim m' n') : m = m' ∧ n = n' :=
  ⟨by ext a; exact congrArg (fun t : α ⊕ β →₀ M ↦ t (Sum.inl a)) h,
    by ext b; exact congrArg (fun t : α ⊕ β →₀ M ↦ t (Sum.inr b)) h⟩

/-- The pairing of the two halves of an index is injective. -/
theorem sumElim_injective :
    Function.Injective fun p : (α →₀ M) × (β →₀ M) ↦ Finsupp.sumElim p.1 p.2 :=
  fun _ _ h ↦ Prod.ext (sumElim_inj h).1 (sumElim_inj h).2

/-- Every index of `α ⊕ β` splits into its two halves. -/
theorem sumElim_surjective :
    Function.Surjective fun p : (α →₀ M) × (β →₀ M) ↦ Finsupp.sumElim p.1 p.2 := by
  intro k
  refine ⟨⟨k.comapDomain Sum.inl Sum.inl_injective.injOn,
    k.comapDomain Sum.inr Sum.inr_injective.injOn⟩, ?_⟩
  ext c
  cases c <;> simp

end Finsupp

namespace MvPolynomial

open Height

variable {σ τ υ : Type*}

section Coeff

variable {R : Type*} [CommSemiring R]

/-- **The coefficients of a product in disjoint variables are the pairwise products of the
coefficients.** The antidiagonal of `Finsupp.sumElim m n` meets the two supports in the single
point `(mapDomain Sum.inl m, mapDomain Sum.inr n)`, so no sum survives. -/
theorem coeff_sumElim_rename_mul_rename (f : MvPolynomial σ R) (g : MvPolynomial τ R)
    (m : σ →₀ ℕ) (n : τ →₀ ℕ) :
    (rename Sum.inl f * rename Sum.inr g).coeff (Finsupp.sumElim m n) = f.coeff m * g.coeff n := by
  classical
  have hsum : Finsupp.mapDomain (Sum.inl : σ → σ ⊕ τ) m
      + Finsupp.mapDomain (Sum.inr : τ → σ ⊕ τ) n = Finsupp.sumElim m n :=
    (Finsupp.sumElim_eq_mapDomain_add m n).symm
  have key : ∀ p ∈ Finset.antidiagonal (Finsupp.sumElim m n),
      p ≠ (Finsupp.mapDomain (Sum.inl : σ → σ ⊕ τ) m,
        Finsupp.mapDomain (Sum.inr : τ → σ ⊕ τ) n) →
      (rename Sum.inl f).coeff p.1 * (rename Sum.inr g).coeff p.2 = 0 := by
    intro p hp hne
    rw [Finset.mem_antidiagonal] at hp
    by_contra hc
    obtain ⟨u, hu, -⟩ := coeff_rename_ne_zero (Sum.inl : σ → σ ⊕ τ) f p.1 (left_ne_zero_of_mul hc)
    obtain ⟨w, hw, -⟩ := coeff_rename_ne_zero (Sum.inr : τ → σ ⊕ τ) g p.2 (right_ne_zero_of_mul hc)
    rw [← hu, ← hw, ← Finsupp.sumElim_eq_mapDomain_add] at hp
    obtain ⟨rfl, rfl⟩ := Finsupp.sumElim_inj hp
    exact hne (Prod.ext hu.symm hw.symm)
  rw [coeff_mul, Finset.sum_eq_single_of_mem
      (f := fun p : (σ ⊕ τ →₀ ℕ) × (σ ⊕ τ →₀ ℕ) ↦
        (rename Sum.inl f).coeff p.1 * (rename Sum.inr g).coeff p.2)
      _ (Finset.mem_antidiagonal.mpr hsum) key,
    coeff_rename_mapDomain _ Sum.inl_injective, coeff_rename_mapDomain _ Sum.inr_injective]

/-- A nonzero polynomial has a nonzero coefficient `Finsupp`. -/
theorem coeff_ne_zero_of_ne_zero {p : MvPolynomial σ R} (hp : p ≠ 0) : p.coeff ≠ 0 :=
  fun h ↦ hp (MvPolynomial.ext _ _ fun m ↦ by rw [h]; simp)

/-- Embedding two disjoint sets of variables into one is the same as embedding `σ ⊕ τ`. -/
theorem rename_mul_rename_eq_rename_sumElim {u : σ → υ} {w : τ → υ} (f : MvPolynomial σ R)
    (g : MvPolynomial τ R) :
    rename u f * rename w g = rename (Sum.elim u w) (rename Sum.inl f * rename Sum.inr g) := by
  rw [map_mul, rename_rename, rename_rename, Sum.elim_comp_inl, Sum.elim_comp_inr]

/-- Two injections with disjoint ranges are one injection of the disjoint union. -/
theorem sumElim_injective_of_disjoint {u : σ → υ} {w : τ → υ} (hu : Function.Injective u)
    (hw : Function.Injective w) (hd : Disjoint (Set.range u) (Set.range w)) :
    Function.Injective (Sum.elim u w) :=
  Sum.elim_injective.mpr ⟨hu, hw, fun a b h ↦ Set.disjoint_left.mp hd ⟨a, rfl⟩ ⟨b, h.symm⟩⟩

end Coeff

section LocalFactor

variable {K : Type*} [Field K]

/-- **At every absolute value the local factor is multiplicative in disjoint variables.** No
factor is assumed nonzero and no absolute value is assumed nonarchimedean. -/
theorem iSup_coeff_rename_inl_mul_rename_inr (f : MvPolynomial σ K) (g : MvPolynomial τ K)
    (v : AbsoluteValue K ℝ) :
    (⨆ k : σ ⊕ τ →₀ ℕ, v ((rename Sum.inl f * rename Sum.inr g).coeff k))
      = (⨆ m : σ →₀ ℕ, v (f.coeff m)) * ⨆ n : τ →₀ ℕ, v (g.coeff n) :=
  Finsupp.iSup_apply_eq_iSup_mul_iSup (x := f.coeff) (y := g.coeff)
    (z := (rename Sum.inl f * rename Sum.inr g).coeff)
    (e := fun p : (σ →₀ ℕ) × (τ →₀ ℕ) ↦ Finsupp.sumElim p.1 p.2)
    (fun p ↦ coeff_sumElim_rename_mul_rename f g p.1 p.2)
    (fun c hc ↦ absurd (Finsupp.sumElim_surjective c) (by simpa using hc)) v

/-- **Renaming the variables injectively permutes the coefficients**, so it leaves the local
factor alone. -/
theorem iSup_coeff_rename_of_injective {e : σ → τ} (he : Function.Injective e)
    (v : AbsoluteValue K ℝ) (P : MvPolynomial σ K) :
    (⨆ d : τ →₀ ℕ, v ((rename e P).coeff d)) = ⨆ m : σ →₀ ℕ, v (P.coeff m) := by
  refine le_antisymm (Real.iSup_le (fun d ↦ ?_) (Real.iSup_nonneg fun _ ↦ v.nonneg _))
    (Real.iSup_le (fun m ↦ ?_) (Real.iSup_nonneg fun _ ↦ v.nonneg _))
  · rcases eq_or_ne ((rename e P).coeff d) 0 with h | h
    · rw [h, map_zero]
      exact Real.iSup_nonneg fun _ ↦ v.nonneg _
    · obtain ⟨u, rfl, -⟩ := coeff_rename_ne_zero e P d h
      rw [coeff_rename_mapDomain e he P u]
      exact le_ciSup (Finsupp.bddAbove_range_apply P.coeff v) u
  · rw [← coeff_rename_mapDomain e he P m]
    exact le_ciSup (Finsupp.bddAbove_range_apply (rename e P).coeff v) _

/-- **The local factor, in the form with two injections of disjoint range.** -/
theorem iSup_coeff_rename_mul_rename_of_disjoint {u : σ → υ} {w : τ → υ}
    (hu : Function.Injective u) (hw : Function.Injective w)
    (hd : Disjoint (Set.range u) (Set.range w)) (f : MvPolynomial σ K) (g : MvPolynomial τ K)
    (v : AbsoluteValue K ℝ) :
    (⨆ k : υ →₀ ℕ, v ((rename u f * rename w g).coeff k))
      = (⨆ m : σ →₀ ℕ, v (f.coeff m)) * ⨆ n : τ →₀ ℕ, v (g.coeff n) := by
  rw [rename_mul_rename_eq_rename_sumElim,
    iSup_coeff_rename_of_injective (sumElim_injective_of_disjoint hu hw hd),
    iSup_coeff_rename_inl_mul_rename_inr]

end LocalFactor

section Height

variable {K : Type*} [Field K] [AdmissibleAbsValues K]

/-- **Bombieri–Gubler, Proposition 1.6.2.** The height of a product of polynomials in disjoint
sets of variables is the product of the heights, exactly. -/
theorem mulHeight_rename_inl_mul_rename_inr {f : MvPolynomial σ K} {g : MvPolynomial τ K}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    (rename Sum.inl f * rename Sum.inr g).mulHeight = f.mulHeight * g.mulHeight := by
  change Finsupp.mulHeight (rename Sum.inl f * rename Sum.inr g).coeff
    = Finsupp.mulHeight f.coeff * Finsupp.mulHeight g.coeff
  exact Finsupp.mulHeight_eq_mulHeight_mul_mulHeight
    (e := fun p : (σ →₀ ℕ) × (τ →₀ ℕ) ↦ Finsupp.sumElim p.1 p.2) Finsupp.sumElim_injective
    (fun p ↦ coeff_sumElim_rename_mul_rename f g p.1 p.2)
    (fun c hc ↦ absurd (Finsupp.sumElim_surjective c) (by simpa using hc))
    (coeff_ne_zero_of_ne_zero hf) (coeff_ne_zero_of_ne_zero hg)

/-- The logarithmic form of `MvPolynomial.mulHeight_rename_inl_mul_rename_inr`: the identity
`h(U · V) = h(U) + h(V)` that Roth's lemma uses. -/
theorem logHeight_rename_inl_mul_rename_inr {f : MvPolynomial σ K} {g : MvPolynomial τ K}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    (rename Sum.inl f * rename Sum.inr g).logHeight = f.logHeight + g.logHeight := by
  rw [logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight,
    mulHeight_rename_inl_mul_rename_inr hf hg,
    Real.log_mul (mulHeight_ne_zero f) (mulHeight_ne_zero g)]

/-- **Renaming the variables injectively leaves the height alone.** -/
theorem mulHeight_rename_of_injective {e : σ → τ} (he : Function.Injective e)
    (P : MvPolynomial σ K) : (rename e P).mulHeight = P.mulHeight := by
  have hinj : Function.Injective fun m : P.coeff.support ↦ Finsupp.mapDomain e m.val :=
    fun m n h ↦ Subtype.ext (Finsupp.mapDomain_injective he h)
  have hcov : ∀ d ∈ (rename e P).coeff.support,
      d ∈ Set.range fun m : P.coeff.support ↦ Finsupp.mapDomain e m.val := by
    intro d hd
    obtain ⟨u, hu, hu0⟩ := coeff_rename_ne_zero e P d (Finsupp.mem_support_iff.mp hd)
    exact ⟨⟨u, Finsupp.mem_support_iff.mpr hu0⟩, hu⟩
  have hfun : (fun m : P.coeff.support ↦ (rename e P).coeff (Finsupp.mapDomain e m.val))
      = fun m : P.coeff.support ↦ P.coeff m.val :=
    funext fun m ↦ coeff_rename_mapDomain e he P m.val
  change Finsupp.mulHeight (rename e P).coeff = Finsupp.mulHeight P.coeff
  rw [Finsupp.mulHeight_eq_mulHeight_comp _ _ hinj hcov, hfun,
    Finsupp.mulHeight_eq_mulHeight_subtype P.coeff (Finset.Subset.refl _)]

/-- The logarithmic form of `MvPolynomial.mulHeight_rename_of_injective`. -/
theorem logHeight_rename_of_injective {e : σ → τ} (he : Function.Injective e)
    (P : MvPolynomial σ K) : (rename e P).logHeight = P.logHeight :=
  congrArg Real.log (mulHeight_rename_of_injective he P)

/-- **The form Layer 2.7 consumes.** Two polynomials embedded into one set of variables along
injections with disjoint ranges have the product of their heights. -/
theorem mulHeight_rename_mul_rename_of_disjoint {u : σ → υ} {w : τ → υ}
    (hu : Function.Injective u) (hw : Function.Injective w)
    (hd : Disjoint (Set.range u) (Set.range w)) {f : MvPolynomial σ K} {g : MvPolynomial τ K}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    (rename u f * rename w g).mulHeight = f.mulHeight * g.mulHeight := by
  rw [rename_mul_rename_eq_rename_sumElim,
    mulHeight_rename_of_injective (sumElim_injective_of_disjoint hu hw hd),
    mulHeight_rename_inl_mul_rename_inr hf hg]

/-- The logarithmic form of `MvPolynomial.mulHeight_rename_mul_rename_of_disjoint`. -/
theorem logHeight_rename_mul_rename_of_disjoint {u : σ → υ} {w : τ → υ}
    (hu : Function.Injective u) (hw : Function.Injective w)
    (hd : Disjoint (Set.range u) (Set.range w)) {f : MvPolynomial σ K} {g : MvPolynomial τ K}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    (rename u f * rename w g).logHeight = f.logHeight + g.logHeight := by
  rw [logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight,
    mulHeight_rename_mul_rename_of_disjoint hu hw hd hf hg,
    Real.log_mul (mulHeight_ne_zero f) (mulHeight_ne_zero g)]

end Height

end MvPolynomial

/-!
### Acceptance criteria

The tests the roadmap pins for this layer: the coefficient identity, the exactness of the height
identity at a numerical instance, and the two hypotheses that are not decoration.
-/

section Examples

open Height MvPolynomial

/-- The zero exponent is not the exponent of `x`. -/
private theorem zero_ne_single_one : (0 : Unit →₀ ℕ) ≠ Finsupp.single () 1 :=
  fun h ↦ by simpa using h.symm

/-- Over `ℚ`, the one-variable polynomial `x + a` has the height of `a`. The tests below need a
polynomial whose height is not the junk value `1`. -/
private theorem mulHeight_X_add_C_unit (a : ℚ) :
    (X () + C a : MvPolynomial Unit ℚ).mulHeight = Height.mulHeight₁ a := by
  have h01 := zero_ne_single_one
  have hinj : Function.Injective (![0, Finsupp.single () 1] : Fin 2 → (Unit →₀ ℕ)) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all
  have hcov : ∀ k ∈ (X () + C a : MvPolynomial Unit ℚ).coeff.support,
      k ∈ Set.range (![0, Finsupp.single () 1] : Fin 2 → (Unit →₀ ℕ)) := by
    intro k hk
    by_cases h0 : (0 : Unit →₀ ℕ) = k
    · exact ⟨0, by simp [h0]⟩
    by_cases h1 : (Finsupp.single () 1 : Unit →₀ ℕ) = k
    · exact ⟨1, by simp [h1]⟩
    · exact absurd (by simp [coeff_X, coeff_C, h0, h1]) (Finsupp.mem_support_iff.mp hk)
  have hfun : (fun i : Fin 2 ↦ (X () + C a : MvPolynomial Unit ℚ).coeff
      (![0, Finsupp.single () 1] i)) = ![a, 1] := by
    funext i
    fin_cases i <;> simp [coeff_X, coeff_C, h01, Ne.symm h01]
  change Finsupp.mulHeight (X () + C a : MvPolynomial Unit ℚ).coeff = Height.mulHeight₁ a
  rw [Finsupp.mulHeight_eq_mulHeight_comp _ _ hinj hcov, hfun,
    ← Height.mulHeight₁_eq_mulHeight]

/-- **Acceptance test: the coefficient identity.** -/
example {σ τ R : Type*} [CommSemiring R] (f : MvPolynomial σ R) (g : MvPolynomial τ R)
    (m : σ →₀ ℕ) (n : τ →₀ ℕ) :
    (rename Sum.inl f * rename Sum.inr g).coeff (Finsupp.sumElim m n) = f.coeff m * g.coeff n :=
  coeff_sumElim_rename_mul_rename f g m n

/-- **Acceptance test: at every place, with no hypothesis at all.** -/
example {σ τ K : Type*} [Field K] (f : MvPolynomial σ K) (g : MvPolynomial τ K)
    (v : AbsoluteValue K ℝ) :
    (⨆ k : σ ⊕ τ →₀ ℕ, v ((rename Sum.inl f * rename Sum.inr g).coeff k))
      = (⨆ m : σ →₀ ℕ, v (f.coeff m)) * ⨆ n : τ →₀ ℕ, v (g.coeff n) :=
  iSup_coeff_rename_inl_mul_rename_inr f g v

/-- **Acceptance test: Proposition 1.6.2 itself.** -/
example {σ τ K : Type*} [Field K] [AdmissibleAbsValues K] {f : MvPolynomial σ K}
    {g : MvPolynomial τ K} (hf : f ≠ 0) (hg : g ≠ 0) :
    (rename Sum.inl f * rename Sum.inr g).mulHeight = f.mulHeight * g.mulHeight :=
  mulHeight_rename_inl_mul_rename_inr hf hg

/-- **Acceptance test, numerical.** Over `ℚ`, `(x + 2)(y + 3)` in two disjoint variables has
height `6`, which is `2 * 3` on the nose. Compare `ArithmeticHeights/Gelfond.lean`, where the same
product in *one* variable is allowed a factor `2 ^ (deg p + deg q)`. -/
example : ((rename Sum.inl (X () + C 2 : MvPolynomial Unit ℚ)) *
    rename Sum.inr (X () + C 3 : MvPolynomial Unit ℚ)).mulHeight = 6 := by
  have h2 : (X () + C 2 : MvPolynomial Unit ℚ).mulHeight = 2 := by
    rw [mulHeight_X_add_C_unit]
    simpa using Rat.mulHeight₁_natCast 2
  have h3 : (X () + C 3 : MvPolynomial Unit ℚ).mulHeight = 3 := by
    rw [mulHeight_X_add_C_unit]
    simpa using Rat.mulHeight₁_natCast 3
  have hne2 : (X () + C 2 : MvPolynomial Unit ℚ) ≠ 0 := by
    intro h
    rw [h, MvPolynomial.mulHeight_zero] at h2
    norm_num at h2
  have hne3 : (X () + C 3 : MvPolynomial Unit ℚ) ≠ 0 := by
    intro h
    rw [h, MvPolynomial.mulHeight_zero] at h3
    norm_num at h3
  rw [mulHeight_rename_inl_mul_rename_inr hne2 hne3, h2, h3]
  norm_num

/-- **Rejection test: the nonvanishing hypotheses are not decoration.** At `f = 0` the left side
of Proposition 1.6.2 is the junk value `1` and the right side is the height of `g`, here `2`. The
*local* identity is unaffected — it reads `0 = 0 * 2` — which is why only the height statement
carries the hypotheses. -/
example : ((rename Sum.inl (0 : MvPolynomial Unit ℚ)) *
      rename Sum.inr (X () + C 2 : MvPolynomial Unit ℚ)).mulHeight = 1 ∧
    (0 : MvPolynomial Unit ℚ).mulHeight * (X () + C 2 : MvPolynomial Unit ℚ).mulHeight = 2 := by
  refine ⟨by rw [map_zero, zero_mul, MvPolynomial.mulHeight_zero], ?_⟩
  rw [MvPolynomial.mulHeight_zero, one_mul, mulHeight_X_add_C_unit]
  simpa using Rat.mulHeight₁_natCast 2

/-- **Rejection test: the variables must be disjoint.** In one variable the coefficients of a
product are *sums* over the antidiagonal, not single products: `(x + 1) ^ 2` has middle
coefficient `2`, while `coeff (single () 1)` of each factor is `1`. This is the whole reason the
exact identity is restricted to disjoint variable sets, and what it costs in height is the
rejection test of `ArithmeticHeights/Polynomial.lean`: `x + 1` has height `1` over `ℚ` and its
square has height `2`. -/
example : ((X () + 1 : MvPolynomial Unit ℚ) * (X () + 1)).coeff (Finsupp.single () 1) = 2 ∧
    (X () + 1 : MvPolynomial Unit ℚ).coeff (Finsupp.single () 1) *
      (X () + 1 : MvPolynomial Unit ℚ).coeff (Finsupp.single () 1) = 1 := by
  have h01 := zero_ne_single_one
  have h21 : (Finsupp.single () 2 : Unit →₀ ℕ) ≠ Finsupp.single () 1 := by
    intro h
    have h' := congrArg (fun t : Unit →₀ ℕ ↦ t ()) h
    simp at h'
  refine ⟨?_, by simp [coeff_X, coeff_one, h01]⟩
  have h : (X () + 1 : MvPolynomial Unit ℚ) * (X () + 1)
      = monomial (Finsupp.single () 2) 1 + (X () + X ()) + 1 := by
    rw [← X_pow_eq_monomial]
    ring
  rw [h]
  simp [coeff_monomial, coeff_X, coeff_one, h01, h21]
  norm_num

end Examples

end
