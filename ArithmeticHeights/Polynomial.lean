/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.Extension
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Eval.Coeff

/-!
# The height of a polynomial

The height of a polynomial is the height of its tuple of coefficients. A univariate polynomial
over `K` *is* a `ℕ →₀ K` and a multivariate one *is* a `(σ →₀ ℕ) →₀ K`, so Mathlib's
`Finsupp.mulHeight` is the definition and nothing new is constructed:
`Polynomial.mulHeight p = Finsupp.mulHeight p.coeff`, and likewise for `MvPolynomial`.

What has to be built is the API, because `Finsupp.mulHeight` has none: Mathlib declares it and
its logarithmic companion and stops. The first section below supplies it, on top of the one lemma
everything else follows from — `Finsupp.mulHeight_eq_mulHeight_comp`, which computes the height of
a `Finsupp` as the height of the tuple obtained by any injective reindexing whose range covers the
support. Every statement about polynomials in this file is a corollary of that lemma.

## Main definitions

* `Polynomial.mulHeight` and `Polynomial.logHeight`: the height of a univariate polynomial.
* `MvPolynomial.mulHeight` and `MvPolynomial.logHeight`: the multivariate form.

## Main results

* `Finsupp.mulHeight_eq_mulHeight_comp` and `Finsupp.mulHeight_eq_mulHeight_subtype`: the height
  of a finitely supported function is the height of the tuple it induces on any index set that
  covers its support.
* `Finsupp.bddAbove_range_apply` and `Finsupp.iSup_apply_eq_iSup_support`: the local factor
  `⨆ i, v (x i)` of the height is bounded and is the supremum over the support, for an index type
  that is not assumed finite. Layer 2.2 uses both.
* `Finsupp.mulHeight_coe_eq`: the height of a `Finsupp` is the height of the *function* it
  coerces to, over the whole — possibly infinite — index type. This is what makes
  `Finsupp.logHeight` the logarithm of `Finsupp.mulHeight`; see the implementation notes.
* `Polynomial.mulHeight_eq_mulHeight_coeff`: the height of `p` is the height of its coefficient
  vector on `Fin (p.natDegree + 1)`.
* `Polynomial.mulHeight_monomial` and `Polynomial.mulHeight_C`: monomials, and in particular
  constants, have height `1`.
* `Polynomial.mulHeight_smul` and `Polynomial.mulHeight_C_mul`: invariance under scaling by a
  nonzero constant, and `Polynomial.mulHeight_mul_X_pow` under multiplication by a power of `X`.
* `Polynomial.mulHeight_X_sub_C`: the compatibility with Mathlib's affine height,
  `mulHeight (X - C a) = mulHeight₁ a`.
* `Polynomial.mulHeight_map` and `Polynomial.mulHeight_pow_finrank`: the behaviour under
  `Polynomial.map` along a field embedding, and its number-field form — the polynomial shadow of
  Layer 0.3.

## Implementation notes

⚠ `Finsupp.mulHeight` and `Finsupp.logHeight` are declared inside Mathlib's `namespace Height`,
where the bare name `mulHeight` resolves to `Height.mulHeight`. So `Finsupp.logHeight x` unfolds
to `log (Height.mulHeight ⇑x)` — the height of the *coerced function on the whole index type* —
and the lemma named `Finsupp.logHeight_eq_log_mulHeight` does not mention `Finsupp.logHeight` at
all. The two heights do agree, but that is a theorem, `Finsupp.mulHeight_coe_eq`, and it is not a
corollary of `Height.mulHeight_eq_mulHeight_restrict_support`, which assumes a finite index type:
for polynomials the index type is `ℕ`. The local factor `⨆ i : α, v (x i)` is computed instead
directly, using that `v` is nonnegative and vanishes off the support. Without this lemma
`Polynomial.logHeight` could not be defined as the logarithm of `Polynomial.mulHeight` and still
be connected to `Finsupp.logHeight`.

Mathlib's `Polynomial.coeff` and `MvPolynomial.coeff` are the coefficient `Finsupp` itself, not a
function, so `p.coeff.support = p.support` holds by `rfl` and no `toFinsupp` or
`AddMonoidAlgebra.coeff` detour is needed in the definition.

The zero polynomial takes the junk value `1`, as everywhere in Mathlib's height API. This is why
`Polynomial.mulHeight_smul` needs `c ≠ 0`: at `c = 0` the left side collapses to `1`.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
§1.6. M. Hindry and J. H. Silverman, *Diophantine Geometry: An Introduction*, Springer (2000),
§B.7.

This is Layer 2.1 of the `ArithmeticHeights` roadmap.
-/

public section

namespace Finsupp

open Height

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {α : Type*}

/-!
### The height of a finitely supported function

Mathlib defines `Finsupp.mulHeight` and `Finsupp.logHeight` and proves nothing about them. This
section is the missing API.
-/

omit [AdmissibleAbsValues K] in
/-- The values of an absolute value on a finitely supported function are bounded: off the
support they are `0`, and the support is finite. -/
lemma bddAbove_range_apply (x : α →₀ K) (v : AbsoluteValue K ℝ) :
    BddAbove (Set.range fun i : α ↦ v (x i)) := by
  classical
  refine (Set.Finite.subset (Finset.finite_toSet
    (insert 0 (x.support.image fun a ↦ v (x a)))) ?_).bddAbove
  rintro _ ⟨i, rfl⟩
  rcases eq_or_ne (x i) 0 with h | h
  · simp [h]
  · exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem _ (Finsupp.mem_support_iff.mpr h)))

omit [AdmissibleAbsValues K] in
/-- The supremum of an absolute value over the whole index type is the supremum over the
support. The index type is not assumed finite, and `x` is not assumed nonzero: at `x = 0` both
sides are `0`, since an absolute value vanishes only at `0`. -/
lemma iSup_apply_eq_iSup_support (x : α →₀ K) (v : AbsoluteValue K ℝ) :
    (⨆ i : α, v (x i)) = ⨆ i : x.support, v (x i.val) := by
  refine le_antisymm (Real.iSup_le (fun i ↦ ?_) (Real.iSup_nonneg fun _ ↦ v.nonneg _))
    (Real.iSup_le (fun i ↦ le_ciSup (bddAbove_range_apply x v) i.val)
      (Real.iSup_nonneg fun _ ↦ v.nonneg _))
  rcases eq_or_ne (x i) 0 with h | h
  · simp only [h, map_zero]
    exact Real.iSup_nonneg fun _ ↦ v.nonneg _
  · exact Finite.le_ciSup_of_le (⟨i, Finsupp.mem_support_iff.mpr h⟩ : x.support) le_rfl

/-- The height of a finitely supported function is the height of the function it coerces to, over
the whole index type. The index type is not assumed finite — it is `ℕ` for a polynomial — so this
is not `Height.mulHeight_eq_mulHeight_restrict_support`; the local suprema are compared directly,
using that an absolute value is nonnegative and vanishes off the support. -/
theorem mulHeight_coe_eq (x : α →₀ K) : Height.mulHeight ⇑x = x.mulHeight := by
  rcases eq_or_ne x 0 with rfl | hx
  · have : IsEmpty ((0 : α →₀ K).support : Type _) := by
      simp only [Finsupp.support_zero]; infer_instance
    rw [Finsupp.coe_zero, Height.mulHeight_zero, Finsupp.mulHeight]
    exact (Height.mulHeight_eq_one_of_subsingleton _).symm
  have hx' : ⇑x ≠ 0 := fun h ↦ hx (DFunLike.coe_injective h)
  have hxs : (fun i : x.support ↦ x i.val) ≠ 0 := by
    obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hx
    exact Function.ne_iff.mpr ⟨⟨i, hi⟩, Finsupp.mem_support_iff.mp hi⟩
  rw [Height.mulHeight_eq hx', Finsupp.mulHeight, Height.mulHeight_eq hxs]
  congr 1
  · congr 2
    ext1 v
    exact iSup_apply_eq_iSup_support x v
  · exact finprod_congr fun v ↦ iSup_apply_eq_iSup_support x v.val

/-- The logarithmic form of `Finsupp.mulHeight_coe_eq`. -/
theorem logHeight_coe_eq (x : α →₀ K) : Height.logHeight ⇑x = x.logHeight := rfl

/-- The logarithmic height of a `Finsupp` is the logarithm of its multiplicative height. This is
**not** what `Finsupp.logHeight_eq_log_mulHeight` says: that lemma's `mulHeight` is
`Height.mulHeight` applied to the coercion. -/
theorem logHeight_eq (x : α →₀ K) : x.logHeight = Real.log x.mulHeight :=
  congrArg Real.log (mulHeight_coe_eq x)

/-- **The height of a `Finsupp` along a reindexing.** If `f` is injective and its range contains
the support of `x`, then the height of `x` is the height of the tuple `fun i ↦ x (f i)`. Every
statement about the height of a polynomial in this file is an instance of this lemma. -/
theorem mulHeight_eq_mulHeight_comp {ι : Type*} [Finite ι] (x : α →₀ K) (f : ι → α)
    (hf : Function.Injective f) (hx : ∀ a ∈ x.support, a ∈ Set.range f) :
    x.mulHeight = Height.mulHeight fun i ↦ x (f i) := by
  have hbij : Function.Bijective
      (fun i : Function.support (fun i ↦ x (f i)) ↦
        (⟨f i.val, Finsupp.mem_support_iff.mpr i.prop⟩ : x.support)) := by
    refine ⟨fun i j h ↦ Subtype.ext (hf (congrArg Subtype.val h)), fun ⟨a, ha⟩ ↦ ?_⟩
    obtain ⟨i, rfl⟩ := hx a ha
    exact ⟨⟨i, Finsupp.mem_support_iff.mp ha⟩, rfl⟩
  rw [Height.mulHeight_eq_mulHeight_restrict_support fun i ↦ x (f i), Finsupp.mulHeight,
    ← Height.mulHeight_comp_equiv (Equiv.ofBijective _ hbij)]
  rfl

/-- The height of a `Finsupp` is the height of its restriction to any finite set containing its
support. -/
theorem mulHeight_eq_mulHeight_subtype {s : Finset α} (x : α →₀ K) (hx : x.support ⊆ s) :
    x.mulHeight = Height.mulHeight fun i : s ↦ x i.val :=
  x.mulHeight_eq_mulHeight_comp Subtype.val Subtype.val_injective fun _ ha ↦ ⟨⟨_, hx ha⟩, rfl⟩

@[simp]
theorem mulHeight_zero : (0 : α →₀ K).mulHeight = 1 := by
  rw [← mulHeight_coe_eq, Finsupp.coe_zero, Height.mulHeight_zero]

@[simp]
theorem logHeight_zero : (0 : α →₀ K).logHeight = 0 := by
  rw [logHeight_eq, mulHeight_zero, Real.log_one]

theorem one_le_mulHeight (x : α →₀ K) : 1 ≤ x.mulHeight :=
  Height.one_le_mulHeight _

theorem mulHeight_pos (x : α →₀ K) : 0 < x.mulHeight :=
  Height.mulHeight_pos _

theorem mulHeight_ne_zero (x : α →₀ K) : x.mulHeight ≠ 0 :=
  Height.mulHeight_ne_zero _

theorem logHeight_nonneg (x : α →₀ K) : 0 ≤ x.logHeight :=
  (logHeight_eq x).symm ▸ Real.log_nonneg x.one_le_mulHeight

/-- The height of a `Finsupp` is invariant under scaling by a nonzero constant. -/
theorem mulHeight_smul (x : α →₀ K) {c : K} (hc : c ≠ 0) : (c • x).mulHeight = x.mulHeight := by
  rw [mulHeight_eq_mulHeight_subtype (c • x) (Finsupp.support_smul_eq hc).subset,
    mulHeight_eq_mulHeight_subtype x subset_rfl,
    ← Height.mulHeight_smul_eq_mulHeight (fun i : x.support ↦ x i.val) hc]
  congr 1

/-- The logarithmic form of `Finsupp.mulHeight_smul`. -/
theorem logHeight_smul (x : α →₀ K) {c : K} (hc : c ≠ 0) : (c • x).logHeight = x.logHeight := by
  rw [logHeight_eq, logHeight_eq, mulHeight_smul x hc]

@[simp]
theorem mulHeight_neg (x : α →₀ K) : (-x).mulHeight = x.mulHeight := by
  rw [← neg_one_smul K x, mulHeight_smul x (neg_ne_zero.mpr one_ne_zero)]

@[simp]
theorem logHeight_neg (x : α →₀ K) : (-x).logHeight = x.logHeight := by
  rw [logHeight_eq, logHeight_eq, mulHeight_neg]

/-- A `Finsupp` supported at one point has height `1`: a one-entry tuple has height `1` by the
product formula. -/
@[simp]
theorem mulHeight_single (a : α) (b : K) : (Finsupp.single a b).mulHeight = 1 := by
  rw [mulHeight_eq_mulHeight_comp _ (fun _ : Fin 1 ↦ a) (fun i j _ ↦ Subsingleton.elim i j)
    fun _ ha ↦ ⟨0, (Finset.mem_singleton.mp (Finsupp.support_single_subset ha)).symm⟩]
  exact Height.mulHeight_eq_one_of_subsingleton _

@[simp]
theorem logHeight_single (a : α) (b : K) : (Finsupp.single a b).logHeight = 0 := by
  rw [logHeight_eq, mulHeight_single, Real.log_one]

end Finsupp

namespace Polynomial

open Height

section General

variable {K : Type*} [Field K] [AdmissibleAbsValues K]

/-!
### The height of a univariate polynomial
-/

/-- **The height of a polynomial** is the height of its coefficient `Finsupp`. `Polynomial.coeff`
*is* that `Finsupp`, so this constructs nothing new. The zero polynomial takes the junk value `1`,
as `Height.mulHeight` does. -/
@[expose] noncomputable def mulHeight (p : K[X]) : ℝ := Finsupp.mulHeight p.coeff

/-- The logarithmic height of a polynomial. As everywhere in this development, it is *defined* as
the logarithm of the multiplicative height and never independently. -/
@[expose] noncomputable def logHeight (p : K[X]) : ℝ := Real.log p.mulHeight

theorem logHeight_eq_log_mulHeight (p : K[X]) : p.logHeight = Real.log p.mulHeight := rfl

/-- The height of `p` is the height of its coefficient vector on `Fin (p.natDegree + 1)`. -/
theorem mulHeight_eq_mulHeight_coeff (p : K[X]) :
    p.mulHeight = Height.mulHeight fun i : Fin (p.natDegree + 1) ↦ p.coeff i.val :=
  Finsupp.mulHeight_eq_mulHeight_comp _ Fin.val Fin.val_injective fun n hn ↦
    ⟨⟨n, Nat.lt_succ_of_le (le_natDegree_of_mem_supp n hn)⟩, rfl⟩

/-- The logarithmic form of `Polynomial.mulHeight_eq_mulHeight_coeff`. -/
theorem logHeight_eq_logHeight_coeff (p : K[X]) :
    p.logHeight = Height.logHeight fun i : Fin (p.natDegree + 1) ↦ p.coeff i.val :=
  congrArg Real.log (mulHeight_eq_mulHeight_coeff p)

theorem one_le_mulHeight (p : K[X]) : 1 ≤ p.mulHeight := Finsupp.one_le_mulHeight _

theorem mulHeight_pos (p : K[X]) : 0 < p.mulHeight := Finsupp.mulHeight_pos _

theorem mulHeight_ne_zero (p : K[X]) : p.mulHeight ≠ 0 := Finsupp.mulHeight_ne_zero _

theorem logHeight_nonneg (p : K[X]) : 0 ≤ p.logHeight := Real.log_nonneg p.one_le_mulHeight

@[simp]
theorem mulHeight_zero : (0 : K[X]).mulHeight = 1 := Finsupp.mulHeight_zero

@[simp]
theorem logHeight_zero : (0 : K[X]).logHeight = 0 := by
  rw [logHeight_eq_log_mulHeight, mulHeight_zero, Real.log_one]

/-- A monomial has height `1`: its coefficient tuple has one entry, and a one-entry tuple has
height `1` by the product formula. -/
@[simp]
theorem mulHeight_monomial (n : ℕ) (a : K) : (monomial n a).mulHeight = 1 := by
  have hcov : ∀ m ∈ (monomial n a : K[X]).coeff.support, m ∈ Set.range fun _ : Fin 1 ↦ n :=
    fun m hm ↦ ⟨0, (Finset.mem_singleton.mp (support_monomial_subset n a hm)).symm⟩
  rw [Polynomial.mulHeight,
    Finsupp.mulHeight_eq_mulHeight_comp _ _ (fun i j _ ↦ Subsingleton.elim i j) hcov]
  exact Height.mulHeight_eq_one_of_subsingleton _

@[simp]
theorem logHeight_monomial (n : ℕ) (a : K) : (monomial n a).logHeight = 0 := by
  rw [logHeight_eq_log_mulHeight, mulHeight_monomial, Real.log_one]

/-- ⚠ A constant polynomial has height `1`, whatever the constant. It is **not**
`Height.mulHeight₁ a`, which is the height of the two-entry tuple `![a, 1]`. -/
@[simp]
theorem mulHeight_C (a : K) : (C a).mulHeight = 1 := by
  rw [← monomial_zero_left, mulHeight_monomial]

@[simp]
theorem logHeight_C (a : K) : (C a).logHeight = 0 := by
  rw [logHeight_eq_log_mulHeight, mulHeight_C, Real.log_one]

@[simp]
theorem mulHeight_one : (1 : K[X]).mulHeight = 1 := by rw [← C_1, mulHeight_C]

@[simp]
theorem mulHeight_X_pow (n : ℕ) : ((X : K[X]) ^ n).mulHeight = 1 := by
  rw [X_pow_eq_monomial, mulHeight_monomial]

@[simp]
theorem mulHeight_X : (X : K[X]).mulHeight = 1 := by
  rw [← monomial_one_one_eq_X, mulHeight_monomial]

/-- The height of a polynomial is invariant under scaling by a nonzero constant. -/
theorem mulHeight_smul (p : K[X]) {c : K} (hc : c ≠ 0) : (c • p).mulHeight = p.mulHeight := by
  rw [Polynomial.mulHeight, Polynomial.mulHeight,
    show (c • p).coeff = c • p.coeff from Finsupp.ext fun n ↦ by simp,
    Finsupp.mulHeight_smul _ hc]

/-- The logarithmic form of `Polynomial.mulHeight_smul`. -/
theorem logHeight_smul (p : K[X]) {c : K} (hc : c ≠ 0) : (c • p).logHeight = p.logHeight := by
  rw [logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight, mulHeight_smul p hc]

theorem mulHeight_C_mul (p : K[X]) {c : K} (hc : c ≠ 0) : (C c * p).mulHeight = p.mulHeight := by
  rw [← smul_eq_C_mul, mulHeight_smul p hc]

theorem logHeight_C_mul (p : K[X]) {c : K} (hc : c ≠ 0) : (C c * p).logHeight = p.logHeight := by
  rw [← smul_eq_C_mul, logHeight_smul p hc]

@[simp]
theorem mulHeight_neg (p : K[X]) : (-p).mulHeight = p.mulHeight := by
  rw [← neg_one_smul K p, mulHeight_smul p (neg_ne_zero.mpr one_ne_zero)]

@[simp]
theorem logHeight_neg (p : K[X]) : (-p).logHeight = p.logHeight := by
  rw [logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight, mulHeight_neg]

/-- The height sees the coefficients, not where they sit: multiplying by a power of `X` shifts the
support and leaves the height alone. -/
@[simp]
theorem mulHeight_mul_X_pow (p : K[X]) (n : ℕ) : (p * X ^ n).mulHeight = p.mulHeight := by
  have hinj : Function.Injective fun i : p.support ↦ i.val + n :=
    fun i j h ↦ Subtype.ext (Nat.add_right_cancel h)
  have hcov : ∀ m ∈ (p * X ^ n).coeff.support, m ∈ Set.range fun i : p.support ↦ i.val + n := by
    intro m hm
    have hm' : (p * X ^ n).coeff m ≠ 0 := Finsupp.mem_support_iff.mp hm
    rw [coeff_mul_X_pow'] at hm'
    split_ifs at hm' with h
    · exact ⟨⟨m - n, mem_support_iff.mpr hm'⟩, show m - n + n = m by omega⟩
    · exact absurd rfl hm'
  have hfun : (fun i : p.support ↦ (p * X ^ n).coeff (i.val + n))
      = fun i : p.support ↦ p.coeff i.val := by
    funext i
    exact coeff_mul_X_pow p n i.val
  rw [Polynomial.mulHeight, Finsupp.mulHeight_eq_mulHeight_comp _ _ hinj hcov, hfun,
    Polynomial.mulHeight,
    Finsupp.mulHeight_eq_mulHeight_subtype p.coeff (Finset.Subset.refl p.support)]

@[simp]
theorem logHeight_mul_X_pow (p : K[X]) (n : ℕ) : (p * X ^ n).logHeight = p.logHeight := by
  rw [logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight, mulHeight_mul_X_pow]

/-- **The compatibility with Mathlib's affine height.** The monic linear polynomial with root `a`
has the height of `a`: its coefficient tuple is `![-a, 1]`, which has the height of `![a, 1]`. -/
theorem mulHeight_X_sub_C (a : K) : ((X : K[X]) - C a).mulHeight = Height.mulHeight₁ a := by
  have hcov : ∀ m ∈ ((X : K[X]) - C a).coeff.support, m ∈ Set.range (Fin.val : Fin 2 → ℕ) := by
    intro m hm
    have hm2 : m ∈ ((X : K[X]) - C a).support := hm
    have h1 := le_natDegree_of_mem_supp m hm2
    rw [natDegree_X_sub_C] at h1
    exact ⟨⟨m, by omega⟩, rfl⟩
  have hfun : (fun i : Fin 2 ↦ ((X : K[X]) - C a).coeff i.val) = ![-a, 1] := by
    funext i
    fin_cases i <;> simp
  rw [Polynomial.mulHeight, Finsupp.mulHeight_eq_mulHeight_comp _ _ Fin.val_injective hcov, hfun,
    ← Height.mulHeight₁_eq_mulHeight, Height.mulHeight₁_neg]

/-- The logarithmic form of `Polynomial.mulHeight_X_sub_C`. -/
theorem logHeight_X_sub_C (a : K) : ((X : K[X]) - C a).logHeight = Height.logHeight₁ a :=
  congrArg Real.log (mulHeight_X_sub_C a)

omit [AdmissibleAbsValues K] in
/-- **The behaviour under `Polynomial.map`.** Along an embedding of fields the support is
unchanged, so the height of the image is the height of the tuple of mapped coefficients. Heights
over different fields are not comparable in general; `Polynomial.mulHeight_pow_finrank` is the
case where they are. -/
theorem mulHeight_map {L : Type*} [Field L] [AdmissibleAbsValues L] (f : K →+* L) (p : K[X]) :
    (p.map f).mulHeight = Height.mulHeight fun i : p.support ↦ f (p.coeff i.val) := by
  have hsupp : (p.map f).coeff.support ⊆ p.support :=
    (support_map_of_injective p f.injective).subset
  have hfun : (fun i : p.support ↦ (p.map f).coeff i.val)
      = fun i : p.support ↦ f (p.coeff i.val) := by
    funext i
    exact coeff_map f i.val
  rw [Polynomial.mulHeight, Finsupp.mulHeight_eq_mulHeight_subtype (p.map f).coeff hsupp, hfun]

omit [AdmissibleAbsValues K] in
/-- The logarithmic form of `Polynomial.mulHeight_map`. -/
theorem logHeight_map {L : Type*} [Field L] [AdmissibleAbsValues L] (f : K →+* L) (p : K[X]) :
    (p.map f).logHeight = Height.logHeight fun i : p.support ↦ f (p.coeff i.val) :=
  congrArg Real.log (mulHeight_map f p)

end General

section NumberField

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **The height of a polynomial over `L` is the `[L : K]`-th power of its height over `K`.** The
polynomial form of `NumberField.mulHeight_pow_finrank`. -/
theorem mulHeight_pow_finrank (p : K[X]) :
    p.mulHeight ^ Module.finrank K L = (p.map (algebraMap K L)).mulHeight := by
  rw [mulHeight_map, Polynomial.mulHeight, Finsupp.mulHeight,
    NumberField.mulHeight_pow_finrank (L := L) fun i : p.coeff.support ↦ p.coeff i.val]
  rfl

/-- The logarithmic form of `Polynomial.mulHeight_pow_finrank`. -/
theorem finrank_nsmul_logHeight (p : K[X]) :
    Module.finrank K L • p.logHeight = (p.map (algebraMap K L)).logHeight := by
  rw [logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight, ← mulHeight_pow_finrank (L := L),
    Real.log_pow, nsmul_eq_mul]

end NumberField

end Polynomial

namespace MvPolynomial

open Height

section General

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {σ : Type*}

/-!
### The height of a multivariate polynomial
-/

/-- **The height of a multivariate polynomial** is the height of its coefficient `Finsupp`, as in
the univariate case. -/
@[expose] noncomputable def mulHeight (p : MvPolynomial σ K) : ℝ := Finsupp.mulHeight p.coeff

/-- The logarithmic height of a multivariate polynomial. -/
@[expose] noncomputable def logHeight (p : MvPolynomial σ K) : ℝ := Real.log p.mulHeight

theorem logHeight_eq_log_mulHeight (p : MvPolynomial σ K) :
    p.logHeight = Real.log p.mulHeight := rfl

theorem one_le_mulHeight (p : MvPolynomial σ K) : 1 ≤ p.mulHeight := Finsupp.one_le_mulHeight _

theorem mulHeight_pos (p : MvPolynomial σ K) : 0 < p.mulHeight := Finsupp.mulHeight_pos _

theorem mulHeight_ne_zero (p : MvPolynomial σ K) : p.mulHeight ≠ 0 := Finsupp.mulHeight_ne_zero _

theorem logHeight_nonneg (p : MvPolynomial σ K) : 0 ≤ p.logHeight :=
  Real.log_nonneg p.one_le_mulHeight

@[simp]
theorem mulHeight_zero : (0 : MvPolynomial σ K).mulHeight = 1 := Finsupp.mulHeight_zero

@[simp]
theorem logHeight_zero : (0 : MvPolynomial σ K).logHeight = 0 := by
  rw [logHeight_eq_log_mulHeight, mulHeight_zero, Real.log_one]

/-- A monomial has height `1`, whatever its exponent vector and coefficient. -/
@[simp]
theorem mulHeight_monomial (m : σ →₀ ℕ) (a : K) : (monomial m a).mulHeight = 1 := by
  have hcov : ∀ s ∈ (monomial m a : MvPolynomial σ K).coeff.support,
      s ∈ Set.range fun _ : Fin 1 ↦ m :=
    fun s hs ↦ ⟨0, (Finset.mem_singleton.mp (support_monomial_subset hs)).symm⟩
  rw [MvPolynomial.mulHeight,
    Finsupp.mulHeight_eq_mulHeight_comp _ _ (fun i j _ ↦ Subsingleton.elim i j) hcov]
  exact Height.mulHeight_eq_one_of_subsingleton _

@[simp]
theorem logHeight_monomial (m : σ →₀ ℕ) (a : K) : (monomial m a).logHeight = 0 := by
  rw [logHeight_eq_log_mulHeight, mulHeight_monomial, Real.log_one]

/-- ⚠ As in the univariate case, a constant has height `1`, not `Height.mulHeight₁` of it. -/
@[simp]
theorem mulHeight_C (a : K) : (C a : MvPolynomial σ K).mulHeight = 1 := by
  rw [← monomial_zero', mulHeight_monomial]

@[simp]
theorem logHeight_C (a : K) : (C a : MvPolynomial σ K).logHeight = 0 := by
  rw [logHeight_eq_log_mulHeight, mulHeight_C, Real.log_one]

@[simp]
theorem mulHeight_one : (1 : MvPolynomial σ K).mulHeight = 1 := by rw [← C_1, mulHeight_C]

/-- The height of a multivariate polynomial is invariant under scaling by a nonzero constant. -/
theorem mulHeight_smul (p : MvPolynomial σ K) {c : K} (hc : c ≠ 0) :
    (c • p).mulHeight = p.mulHeight := by
  rw [MvPolynomial.mulHeight, MvPolynomial.mulHeight,
    show (c • p).coeff = c • p.coeff from Finsupp.ext fun n ↦ by simp,
    Finsupp.mulHeight_smul _ hc]

/-- The logarithmic form of `MvPolynomial.mulHeight_smul`. -/
theorem logHeight_smul (p : MvPolynomial σ K) {c : K} (hc : c ≠ 0) :
    (c • p).logHeight = p.logHeight := by
  rw [logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight, mulHeight_smul p hc]

theorem mulHeight_C_mul (p : MvPolynomial σ K) {c : K} (hc : c ≠ 0) :
    (C c * p).mulHeight = p.mulHeight := by
  rw [C_mul', mulHeight_smul p hc]

@[simp]
theorem mulHeight_neg (p : MvPolynomial σ K) : (-p).mulHeight = p.mulHeight := by
  rw [← neg_one_smul K p, mulHeight_smul p (neg_ne_zero.mpr one_ne_zero)]

@[simp]
theorem logHeight_neg (p : MvPolynomial σ K) : (-p).logHeight = p.logHeight := by
  rw [logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight, mulHeight_neg]

omit [AdmissibleAbsValues K] in
/-- The multivariate form of `Polynomial.mulHeight_map`. -/
theorem mulHeight_map {L : Type*} [Field L] [AdmissibleAbsValues L] (f : K →+* L)
    (p : MvPolynomial σ K) :
    (map f p).mulHeight = Height.mulHeight fun i : p.support ↦ f (p.coeff i.val) := by
  have hsupp : (map f p).coeff.support ⊆ p.support :=
    (support_map_of_injective p f.injective).subset
  have hfun : (fun i : p.support ↦ (map f p).coeff i.val)
      = fun i : p.support ↦ f (p.coeff i.val) := by
    funext i
    exact coeff_map f p i.val
  rw [MvPolynomial.mulHeight, Finsupp.mulHeight_eq_mulHeight_subtype (map f p).coeff hsupp, hfun]

end General

section NumberField

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {σ : Type*}

/-- The multivariate form of `Polynomial.mulHeight_pow_finrank`. -/
theorem mulHeight_pow_finrank (p : MvPolynomial σ K) :
    p.mulHeight ^ Module.finrank K L = (map (algebraMap K L) p).mulHeight := by
  rw [mulHeight_map, MvPolynomial.mulHeight, Finsupp.mulHeight,
    NumberField.mulHeight_pow_finrank (L := L) fun i : p.coeff.support ↦ p.coeff i.val]
  rfl

/-- The logarithmic form of `MvPolynomial.mulHeight_pow_finrank`. -/
theorem finrank_nsmul_logHeight (p : MvPolynomial σ K) :
    Module.finrank K L • p.logHeight = (map (algebraMap K L) p).logHeight := by
  rw [logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight, ← mulHeight_pow_finrank (L := L),
    Real.log_pow, nsmul_eq_mul]

end NumberField

end MvPolynomial

/-!
### Examples

The rejection tests the roadmap pins for this layer, and the ones that fix the shape of the
statements above.
-/

section Examples

open Height Polynomial

/-- **Rejection test.** A constant polynomial has height `1`, whatever the constant, so
`mulHeight (C a) = mulHeight₁ a` is false: at `a = 2` over `ℚ` the left side is `1` and the right
side is `2`. -/
example : (C (2 : ℚ)).mulHeight = 1 ∧ Height.mulHeight₁ (2 : ℚ) = 2 :=
  ⟨mulHeight_C 2, by simpa using Rat.mulHeight₁_natCast 2⟩

/-- **Acceptance test.** The monic linear polynomial with root `2` has height `2`. -/
example : ((X : ℚ[X]) - C 2).mulHeight = 2 := by
  rw [mulHeight_X_sub_C]
  simpa using Rat.mulHeight₁_natCast 2

/-- **Rejection test.** Scaling invariance needs `c ≠ 0`: at `c = 0` the left side collapses to
the junk value of the zero polynomial. -/
example : (C (0 : ℚ) * ((X : ℚ[X]) - C 2)).mulHeight = 1 ∧ ((X : ℚ[X]) - C 2).mulHeight = 2 := by
  refine ⟨by rw [map_zero, zero_mul, Polynomial.mulHeight_zero], ?_⟩
  rw [mulHeight_X_sub_C]
  simpa using Rat.mulHeight₁_natCast 2

/-- **Rejection test.** The height is not multiplicative: `X + 1` has height `1` over `ℚ`, while
its square, with coefficient vector `![1, 2, 1]`, has height at least `2`. This is why Layer 2.3
carries a factor `2 ^ (deg p + deg q)` and why the Mahler measure, which *is* multiplicative, is
the sharper tool. -/
example : ((X : ℚ[X]) + 1).mulHeight = 1 ∧ 2 ≤ (((X : ℚ[X]) + 1) ^ 2).mulHeight := by
  have hdeg : (((X : ℚ[X]) + 1) ^ 2).natDegree = 2 := by
    rw [← C_1, natDegree_pow, natDegree_X_add_C]
  have hcoeff : (fun i : Fin 3 ↦ (((X : ℚ[X]) + 1) ^ 2).coeff i.val) = ![1, 2, 1] := by
    have h : ((X : ℚ[X]) + 1) ^ 2 = X ^ 2 + C 2 * X + C 1 := by
      rw [map_ofNat, map_one]; ring
    funext i
    fin_cases i <;> simp [h, coeff_one]
  have hcov : ∀ m ∈ (((X : ℚ[X]) + 1) ^ 2).coeff.support,
      m ∈ Set.range (Fin.val : Fin 3 → ℕ) := by
    intro m hm
    have hm2 : m ∈ (((X : ℚ[X]) + 1) ^ 2).support := hm
    have h1 := le_natDegree_of_mem_supp m hm2
    rw [hdeg] at h1
    exact ⟨⟨m, by omega⟩, rfl⟩
  have h2 : Height.mulHeight ![(2 : ℚ), 1] = 2 := by
    rw [← Height.mulHeight₁_eq_mulHeight]
    simpa using Rat.mulHeight₁_natCast 2
  have hle : Height.mulHeight ![(2 : ℚ), 1] ≤ Height.mulHeight ![(1 : ℚ), 2, 1] := by
    have h : (![(1 : ℚ), 2, 1] ∘ ![1, 0]) = ![(2 : ℚ), 1] := by
      funext i
      fin_cases i <;> simp
    calc Height.mulHeight ![(2 : ℚ), 1]
        = Height.mulHeight (![(1 : ℚ), 2, 1] ∘ ![1, 0]) := by rw [h]
      _ ≤ Height.mulHeight ![(1 : ℚ), 2, 1] := Height.mulHeight_comp_le _ _
  refine ⟨by rw [show ((X : ℚ[X]) + 1) = X - C (-1) by simp, mulHeight_X_sub_C,
    Height.mulHeight₁_neg, Height.mulHeight₁_one], ?_⟩
  rw [Polynomial.mulHeight, Finsupp.mulHeight_eq_mulHeight_comp _ _ Fin.val_injective hcov, hcoeff]
  exact le_of_eq_of_le h2.symm hle

/-- **Conformance.** The height sees neither the degree nor the position of the coefficients: a
scaled power of `X` still has height `1`. -/
example : (C (3 : ℚ) * X ^ 7).mulHeight = 1 := by
  rw [mulHeight_C_mul _ (by norm_num), mulHeight_X_pow]

end Examples

end
