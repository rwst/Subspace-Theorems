/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ForMathlib.RingTheory.MvPolynomial.Associativity
public import ForMathlib.RingTheory.MvPolynomial.Bezout
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Height.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Polynomial.Basic

-- Used only inside proofs.
import ForMathlib.RingTheory.Ideal.LengthPow

/-!
# Multiprojective heights: the interface

The height bounds of the product theorem (G. Rémond, *Sur le théorème du produit*, J. Théor.
Nombres Bordeaux **13** (2001), Thm 1.1 and Cor. 1.1) use the heights `h_β(V)` of subvarieties `V`
of `ℙ^{n_1} × ⋯ × ℙ^{n_m}` defined by Rémond in *Géométrie diophantienne multiprojective*,
Chapter 7 of Nesterenko–Philippon (eds.), *Introduction to algebraic independence theory*, LNM
**1752** (2001). They are the heights of resultant forms, with Philippon's sphere Mahler measure at
the infinite places, and are not formalized here. Instead, `MvPolynomial.MultiprojectiveHeight`
records the properties of them that the product theorem uses, as the fields of a structure; the
height bounds are then proved for every such structure. The fields are:

* `height_nonneg`: heights of (relevant) varieties are nonnegative. Rémond's heights agree with
  the Faltings multiheights of the closures in `ℙ_{O_K}` for the Fubini–Study metrics (LNM 1752,
  Ch. 7, Prop. 2.5), which are nonnegative because the coordinates are sections of sup norm `≤ 1`
  (J.-B. Bost, H. Gillet, C. Soulé, J. Amer. Math. Soc. **7** (1994), Prop. 3.2.4).
* `height_bot_single`, `height_bot_of_ne`: the heights of `ℙ^{n_1} × ⋯ × ℙ^{n_m}` itself are the
  Stoll numbers `h(ℙ^n) = ∑_{j ≤ n} ∑_{i ≤ j} 1/(2i)` in the indices `n + ε_l`, and `0` otherwise
  (LNM 1752, Ch. 7, Cor. 2.4).
* `cycleHeight_sup_le`: **the arithmetic intersection inequality**. For a multihomogeneous `p` of
  multidegree `δ`, a nonzerodivisor modulo `J`, and `|β| = dim V(J)`,
  `h_β(V(J) · div p) ≤ ∑_i δ_i h_{β + ε_i}(V(J)) + d_β(V(J)) h_m(p)`. For `J` prime this is
  Rémond's exact intersection formula (LNM 1752, Ch. 7, Thm 3.4) with his estimate
  `h_{V,β}(p) ≤ h_m(p)` (ibid., Cor. 3.6). For general `J` it follows by summing over the
  components of maximal dimension, by the length formula
  `ℓ_𝔯(J + (p)) = ∑_𝔮 ℓ_𝔮(J) ℓ_𝔯(𝔮 + (p))` for a nonzerodivisor `p` (Rémond 2001, proof of
  Prop. 3.2, §5).

Heights of cycles (`MvPolynomial.cycleHeight`) are defined here from the heights of primes: the
height of index `β` of `V(J)` is `∑_𝔮 ℓ(K[X]_𝔮/J_𝔮) h_β(𝔮)`, over the minimal primes `𝔮` of `J`
of dimension `|β| - 1` with `H_𝔮 ≠ 0`. The polynomial height `h_m` of LNM 1752, Ch. 7, §3.2 is
also concrete (`MvPolynomial.bombieriLogHeight`): the maximum of the coefficients at the finite
places, and the norm `(∑_m |p_m|_v² / C(δ, m))^{1/2}` at the infinite ones, with the
multinomial coefficients `C(δ, m) = ∏_i δ_i! / ∏_s m_s!` (`MvPolynomial.blockMultinomial`).

All heights are relative to `K`, in Mathlib's normalization (`Height.AdmissibleAbsValues`): they
are `[K : ℚ]` times Rémond's absolute heights, so that `h(ℙ^n) = [K : ℚ] s_n` in the field
`height_bot_single` (with `[K : ℚ] = Height.totalWeight K`).

## Main definitions

* `MvPolynomial.blockMultinomial`, `MvPolynomial.bombieriNorm`, `MvPolynomial.bombieriLogHeight`:
  the polynomial height `h_m`.
* `MvPolynomial.stollNumber`: `s_n = ∑_{j ≤ n} ∑_{i ≤ j} 1/(2i)`.
* `MvPolynomial.components`, `MvPolynomial.primeMult`, `MvPolynomial.cycleHeight`: the components
  of dimension `d`, their multiplicities, and the heights of cycles.
* `MvPolynomial.MultiprojectiveHeight`: the interface.

## Main statements

* `MvPolynomial.cycleHeight_bot`: `h_β(ℙ) = h(⊥, β)`.
* `MvPolynomial.components_subset_of_le`, `MvPolynomial.cycleHeight_le_of_le`: a larger ideal of
  no larger dimension has fewer components and smaller heights.
* `MvPolynomial.cycleHeight_eq_of_forall_le`: the height of a `𝔭`-primary ideal is
  `ℓ_𝔭 · h_β(𝔭)`.
-/

@[expose] public section

open Finset Height Height.AdmissibleAbsValues

variable {σ ι K : Type*}

namespace MvPolynomial

section PolynomialHeight

variable [Fintype σ] [Fintype ι] [DecidableEq ι] [Field K]

/-- The multinomial coefficient `C(δ, m) = ∏_i δ_i! / ∏_{b s = i} m_s!` of a monomial `m`, where
`δ_i` is its degree in block `i`. -/
noncomputable def blockMultinomial (b : σ → ι) (m : σ →₀ ℕ) : ℕ :=
  ∏ i, Nat.multinomial {s | b s = i} m

theorem blockMultinomial_pos (b : σ → ι) (m : σ →₀ ℕ) : 0 < blockMultinomial b m :=
  Finset.prod_pos fun _ _ ↦ Nat.multinomial_pos _ _

/-- The local norm `‖P‖_{v,2} = (∑_m |p_m|_v² / C(δ, m))^{1/2}` at an archimedean place (LNM 1752,
Ch. 7, §3.2). -/
noncomputable def bombieriNorm (b : σ → ι) (v : AbsoluteValue K ℝ) (P : MvPolynomial σ K) : ℝ :=
  √(∑ m ∈ P.support, v (P.coeff m) ^ 2 / blockMultinomial b m)

open Classical in
/-- **The polynomial height `h_m(P)`** of LNM 1752, Ch. 7, §3.2, relative to `K`: the logarithm of
`∏_{v | ∞} ‖P‖_{v,2} · ∏_{v ∤ ∞} max_m |p_m|_v`, and `0` for `P = 0`. -/
noncomputable def bombieriLogHeight [AdmissibleAbsValues K] (b : σ → ι) (P : MvPolynomial σ K) :
    ℝ :=
  if P = 0 then 0 else
    Real.log ((archAbsVal.map fun v ↦ bombieriNorm b v P).prod *
      ∏ᶠ v : nonarchAbsVal, ⨆ m : P.support, v.val (P.coeff m))

@[simp]
theorem bombieriLogHeight_zero [AdmissibleAbsValues K] (b : σ → ι) :
    bombieriLogHeight b (0 : MvPolynomial σ K) = 0 := by
  simp [bombieriLogHeight]

theorem bombieriLogHeight_of_ne_zero [AdmissibleAbsValues K] (b : σ → ι) {P : MvPolynomial σ K}
    (hP : P ≠ 0) :
    bombieriLogHeight b P = Real.log ((archAbsVal.map fun v ↦ bombieriNorm b v P).prod *
      ∏ᶠ v : nonarchAbsVal, ⨆ m : P.support, v.val (P.coeff m)) := by
  simp [bombieriLogHeight, hP]

end PolynomialHeight

/-- The Stoll number `s_n = ∑_{j=1}^{n} ∑_{i=1}^{j} 1/(2i)`, the height of `ℙ^n`. -/
noncomputable def stollNumber (n : ℕ) : ℝ :=
  ∑ j ∈ Icc 1 n, ∑ i ∈ Icc 1 j, 1 / (2 * (i : ℝ))

section Cycles

variable [Finite σ] [DecidableEq ι] [Field K]

open Classical in
/-- The components of dimension `d` of `V(J)`: the minimal primes `𝔮` of `J` with `H_𝔮 ≠ 0` and
`deg H_𝔮 = d`. -/
noncomputable def components (b : σ → ι) (J : Ideal (MvPolynomial σ K)) (d : ℕ) :
    Finset (Ideal (MvPolynomial σ K)) :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing _ J).toFinset.filter
    fun 𝔮 ↦ hilbertPoly b 𝔮 ≠ 0 ∧ (hilbertPoly b 𝔮).totalDegree = d

open Classical in
/-- The multiplicity `ℓ(K[X]_𝔮 / J_𝔮)` of `𝔮` in `J`, as a natural number (`0` if `𝔮` is not
prime or the length is infinite). -/
noncomputable def primeMult (𝔮 J : Ideal (MvPolynomial σ K)) : ℕ :=
  if h : 𝔮.IsPrime then (@Ideal.localLength _ _ 𝔮 h J).toNat else 0

/-- **The height of a cycle.** For a function `h` on primes, the height of index `β` of `V(J)` is
`∑_𝔮 ℓ(K[X]_𝔮/J_𝔮) h(𝔮, β)`, over the components `𝔮` of dimension `|β| - 1`. -/
noncomputable def cycleHeight (b : σ → ι) (h : Ideal (MvPolynomial σ K) → (ι →₀ ℕ) → ℝ)
    (J : Ideal (MvPolynomial σ K)) (β : ι →₀ ℕ) : ℝ :=
  ∑ 𝔮 ∈ components b J (β.degree - 1), (primeMult 𝔮 J : ℝ) * h 𝔮 β

theorem mem_components {b : σ → ι} {J 𝔮 : Ideal (MvPolynomial σ K)} {d : ℕ} :
    𝔮 ∈ components b J d ↔
      𝔮 ∈ J.minimalPrimes ∧ hilbertPoly b 𝔮 ≠ 0 ∧ (hilbertPoly b 𝔮).totalDegree = d := by
  classical
  simp [components]

omit [Finite σ] [DecidableEq ι] in
theorem primeMult_eq {𝔮 J : Ideal (MvPolynomial σ K)} [h : 𝔮.IsPrime] :
    primeMult 𝔮 J = (Ideal.localLength 𝔮 J).toNat := by
  simp [primeMult, h]

end Cycles

section Interface

variable [Fintype σ] [Fintype ι] [DecidableEq ι] [Field K] [AdmissibleAbsValues K]

/-- **A multiprojective height theory** on `ℙ^{n_1} × ⋯ × ℙ^{n_m}` over `K`, for the blocks of
variables `b`: heights `h_β(𝔮)` of multihomogeneous primes, with the properties of Rémond's
heights (LNM 1752, Ch. 7) that the product theorem uses. See the module docstring for the
sources. -/
structure MultiprojectiveHeight (b : σ → ι) where
  /-- The height `h_β(𝔮)` of index `β` (meaningful for `|β| = dim 𝔮 + 1`) of a prime. -/
  height : Ideal (MvPolynomial σ K) → (ι →₀ ℕ) → ℝ
  /-- Heights of varieties are nonnegative. -/
  height_nonneg : ∀ 𝔮 : Ideal (MvPolynomial σ K), 𝔮.IsPrime →
    𝔮.IsWeightedHomogeneous (multiWeight b) → hilbertPoly b 𝔮 ≠ 0 → ∀ β, 0 ≤ height 𝔮 β
  /-- The height of `ℙ` in the index `n + ε_l` is the Stoll number of `ℙ^{n_l}`. -/
  height_bot_single : ∀ l : ι,
    height ⊥ (bottomType b + Finsupp.single l 1) = totalWeight K * stollNumber (bottomType b l)
  /-- The other heights of `ℙ` vanish. -/
  height_bot_of_ne : ∀ β : ι →₀ ℕ, β.degree = (bottomType b).degree + 1 →
    (∀ l, β ≠ bottomType b + Finsupp.single l 1) → height ⊥ β = 0
  /-- **The arithmetic intersection inequality** (LNM 1752, Ch. 7, Thm 3.4 and Cor. 3.6, summed
  over the components). -/
  cycleHeight_sup_le : ∀ (J : Ideal (MvPolynomial σ K)) (p : MvPolynomial σ K) (δ : ι → ℕ),
    J.IsWeightedHomogeneous (multiWeight b) → IsWeightedHomogeneous (multiWeight b) p δ →
    J.colon {p} = J → ∀ β : ι →₀ ℕ, 1 ≤ β.degree → β.degree = (hilbertPoly b J).totalDegree →
    cycleHeight b height (J ⊔ Ideal.span {p}) β ≤
      ∑ i, (δ i : ℝ) * cycleHeight b height J (β + Finsupp.single i 1) +
        (multidegree b J β : ℝ) * bombieriLogHeight b p

end Interface

section CycleLemmas

variable [Finite σ] [Finite ι] [DecidableEq ι] [Field K] {b : σ → ι}

/-- The only component of `ℙ` is `⊥`, with multiplicity `1`: `h_β(ℙ) = h(⊥, β)` for
`|β| = |n| + 1`. -/
theorem cycleHeight_bot (hb : Function.Surjective b) (h : Ideal (MvPolynomial σ K) → (ι →₀ ℕ) → ℝ)
    {β : ι →₀ ℕ} (hβ : β.degree = (bottomType b).degree + 1) :
    cycleHeight b h ⊥ β = h ⊥ β := by
  have := Fintype.ofFinite ι
  have hmin : (⊥ : Ideal (MvPolynomial σ K)).minimalPrimes = {⊥} :=
    Ideal.minimalPrimes_eq_subsingleton_self
  have hne : hilbertPoly (K := K) b ⊥ ≠ 0 := by
    intro h0
    have := multidegree_bot (K := K) hb (α := bottomType b) le_rfl
    rw [multidegree, h0] at this
    simp at this
  have hcomp : components b (⊥ : Ideal (MvPolynomial σ K)) (β.degree - 1) = {⊥} := by
    ext 𝔮
    rw [mem_components, hmin, Set.mem_singleton_iff, mem_singleton]
    constructor
    · exact fun h ↦ h.1
    · rintro rfl
      exact ⟨rfl, hne, by rw [totalDegree_hilbertPoly_bot hb, hβ, Nat.add_sub_cancel]⟩
  rw [cycleHeight, hcomp, sum_singleton, primeMult_eq, Ideal.localLength_self]
  simp


/-- The components of dimension `d` of a larger ideal `L ⊇ J` are components of `J`, when `V(J)`
has dimension at most `d`. -/
theorem components_subset_of_le (hb : Function.Surjective b) {J L : Ideal (MvPolynomial σ K)}
    (hJ : J.IsWeightedHomogeneous (multiWeight b)) (hL : L.IsWeightedHomogeneous (multiWeight b))
    (hJL : J ≤ L) {d : ℕ} (hd : (hilbertPoly b J).totalDegree ≤ d) :
    components b L d ⊆ components b J d := by
  intro 𝔮 h𝔮
  rw [mem_components] at h𝔮 ⊢
  obtain ⟨h𝔮L, hne, hdeg⟩ := h𝔮
  have := h𝔮L.1.1
  have h𝔮h := hL.of_mem_minimalPrimes h𝔮L
  refine ⟨⟨⟨this, hJL.trans h𝔮L.1.2⟩, fun 𝔮' h𝔮' h𝔮'𝔮 ↦ ?_⟩, hne, hdeg⟩
  have := h𝔮'.1
  obtain ⟨𝔮'', h𝔮'', h𝔮''𝔮'⟩ := Ideal.exists_minimalPrimes_le h𝔮'.2
  have := h𝔮''.1.1
  by_cases heq : 𝔮'' = 𝔮
  · exact heq ▸ h𝔮''𝔮'
  have hlt : 𝔮'' < 𝔮 := lt_of_le_of_ne (h𝔮''𝔮'.trans h𝔮'𝔮) heq
  have h1 := totalDegree_hilbertPoly_lt_of_lt hb (hJ.of_mem_minimalPrimes h𝔮'') h𝔮h hlt hne
  have h2 := totalDegree_hilbertPoly_le_of_le hb hJ (hJ.of_mem_minimalPrimes h𝔮'') h𝔮''.1.2
  omega

/-- **A larger ideal of no larger dimension has smaller heights**, for nonnegative heights of
primes: `h_β(L) ≤ h_β(J)` for multihomogeneous `J ≤ L` with `dim V(J) < |β|`. -/
theorem cycleHeight_le_of_le (hb : Function.Surjective b)
    {h : Ideal (MvPolynomial σ K) → (ι →₀ ℕ) → ℝ}
    (hnn : ∀ 𝔮 : Ideal (MvPolynomial σ K), 𝔮.IsPrime → 𝔮.IsWeightedHomogeneous (multiWeight b) →
      hilbertPoly b 𝔮 ≠ 0 → ∀ β, 0 ≤ h 𝔮 β)
    {J L : Ideal (MvPolynomial σ K)} (hJ : J.IsWeightedHomogeneous (multiWeight b))
    (hL : L.IsWeightedHomogeneous (multiWeight b)) (hJL : J ≤ L) {β : ι →₀ ℕ}
    (hβ : (hilbertPoly b J).totalDegree + 1 ≤ β.degree) :
    cycleHeight b h L β ≤ cycleHeight b h J β := by
  have hsub := components_subset_of_le hb hJ hL hJL (d := β.degree - 1) (by omega)
  have hnn' : ∀ 𝔮 ∈ components b J (β.degree - 1), 0 ≤ h 𝔮 β := by
    intro 𝔮 h𝔮
    rw [mem_components] at h𝔮
    exact hnn 𝔮 h𝔮.1.1.1 (hJ.of_mem_minimalPrimes h𝔮.1) h𝔮.2.1 β
  refine (sum_le_sum fun 𝔮 h𝔮 ↦ ?_).trans
    (sum_le_sum_of_subset_of_nonneg hsub fun 𝔮 h𝔮 _ ↦
      mul_nonneg (Nat.cast_nonneg _) (hnn' 𝔮 h𝔮))
  have h𝔮J := (mem_components.mp (hsub h𝔮)).1
  have := h𝔮J.1.1
  refine mul_le_mul_of_nonneg_right ?_ (hnn' 𝔮 (hsub h𝔮))
  rw [primeMult_eq, primeMult_eq, Nat.cast_le]
  exact ENat.toNat_le_toNat (Ideal.localLength_le_of_le hJL)
    (Ideal.localLength_ne_top_of_mem_minimalPrimes h𝔮J)

omit [Finite ι] in
/-- **The height of a `𝔭`-primary ideal.** If `J ≤ 𝔭` and every prime containing `J` contains `𝔭`,
then `h_β(J) = ℓ(K[X]_𝔭/J_𝔭) · h(𝔭, β)` for `|β| = dim 𝔭 + 1`. -/
theorem cycleHeight_eq_of_forall_le (h : Ideal (MvPolynomial σ K) → (ι →₀ ℕ) → ℝ)
    {J 𝔭 : Ideal (MvPolynomial σ K)} [𝔭.IsPrime] (hJ𝔭 : J ≤ 𝔭)
    (hall : ∀ 𝔮 : Ideal (MvPolynomial σ K), 𝔮.IsPrime → J ≤ 𝔮 → 𝔭 ≤ 𝔮)
    (hne : hilbertPoly b 𝔭 ≠ 0) {β : ι →₀ ℕ} (hβ : (hilbertPoly b 𝔭).totalDegree + 1 = β.degree) :
    cycleHeight b h J β = (primeMult 𝔭 J : ℝ) * h 𝔭 β := by
  have hmin : J.minimalPrimes = {𝔭} := by
    ext 𝔮
    rw [Set.mem_singleton_iff]
    constructor
    · intro h𝔮
      exact le_antisymm (h𝔮.2 ⟨inferInstance, hJ𝔭⟩ (hall 𝔮 h𝔮.1.1 h𝔮.1.2))
        (hall 𝔮 h𝔮.1.1 h𝔮.1.2)
    · rintro rfl
      exact ⟨⟨inferInstance, hJ𝔭⟩, fun 𝔮' h𝔮' _ ↦ hall 𝔮' h𝔮'.1 h𝔮'.2⟩
  have hcomp : components b J (β.degree - 1) = {𝔭} := by
    ext 𝔮
    rw [mem_components, hmin, Set.mem_singleton_iff, mem_singleton]
    constructor
    · exact fun h ↦ h.1
    · rintro rfl
      exact ⟨rfl, hne, by omega⟩
  rw [cycleHeight, hcomp, sum_singleton]

end CycleLemmas

end MvPolynomial
