/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import CorvajaZannier2004Thue.Engine
public import Mathlib.FieldTheory.Galois.Basic

-- Used only inside proofs.
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import STForMathlib.RingTheory.MvPolynomial.EvalBound
import STForMathlib.RingTheory.MvPolynomial.GenericLinear
import STForMathlib.RingTheory.MvPolynomial.HomogeneousRegular

/-!
# Theorem 3 and Corollary 2

P. Corvaja and U. Zannier, *On a general Thue's equation*, Amer. J. Math. 126 (2004), §§1, 3: a
Subspace Theorem for polynomials, and its application to one polynomial at integer points.

* **Theorem 3, first part** (`NumberField.exists_ne_zero_eval_eq_zero_of_prod_rpow_le`): at each
  place `v` of `S∞ ∪ S` let `f_{1v}, …, f_{n-1,v}` have degrees `δ_{jv} > 0`, with `X₀` and the
  `f_{jv}^h` having finitely many common zeros in `ℙⁿ`. The `S`-integral solutions of
  `∏_v ∏_j |f_{jv}(x)|_v^{1/δ_v} ≤ H(x)^{μ - n - ε}` (1.4), `δ_v = max_j δ_{jv}`,
  `μ ≤ ∑_j δ_{jv}/δ_v`, lie on one hypersurface `q = 0`.
* **Theorem 3, second part** (`NumberField.exists_eval_eq_zero_of_prod_rpow_le_of_irreducible`):
  on an irreducible `G = 0` cut in finitely many points by the `f_v` at every place, the
  solutions lie on one `q = 0`, `q ∉ (G)`.
* **Corollary 2** (`NumberField.exists_finset_eval_eq_zero_of_abv_lt`): the `x ∈ ℤⁿ` with
  `0 < |f(x)|_ν < H(x)^{-δ(n-1)-ε}` lie in finitely many `{G = q = 0}`, `G` irreducible,
  `q ∉ (G)`: a variety of dimension `≤ n - 2`.

The equal-degree forms, which the engine takes directly, are
`NumberField.exists_ne_zero_eval_eq_zero_of_prod_le` and
`NumberField.exists_eval_eq_zero_of_prod_le_of_irreducible`; the reduction to them is
`NumberField.exists_prod_le_of_prod_rpow_le`.

## Implementation notes

⚠ **The first part is the engine with the constant `1` as an `n`-th polynomial.** The paper
sketches a "two-level" filtration on `ℙⁿ`: powers of the `n - 1` polynomials `γ_j`, then the degree
of the remaining factor, with `Δ(i) ∼ δ^{n-1} (N - δ σ(i))` and the count
`∑ deg q ∼ δ^{n-1} (N - δ σ(i))² / 2`. With `γ_n = 1`, whose homogenization in degree `δ` is
`X₀^δ`, the filtration of the engine (`Engine.lean`, `b = 0`, `t = n`) by powers of
`(γ₁, …, γ_{n-1}, 1)` is that filtration, the second level in steps of `δ`:
`γ^i · 1^k V_{N - δσ(i) - δk}`. Lemmas 3.1 and 3.2 apply because `(X₀^δ, γ^h)` has the height
of `(X₀, γ^h)`, which is the hypothesis, and `|1|_v = 1` leaves the inequality unchanged. Steps of
`δ` instead of `1` change only the constants. So no new filtration, count or Subspace Theorem step
is needed.

⚠ **Unequal degrees.** The paper reduces to `δ_{jv} = δ_v` "as in the deduction of Theorem 2 from
Prop. 3.1". Here `f_{jv}` is padded to `f_{jv} ρ_{jv}^{δ_v - δ_{jv}}` with generic linear forms
(`MvPolynomial.exists_le_height_span_mul_pow`), then raised to the power `D/δ_v`,
`D = ∏_v δ_v`, so that one degree `D` serves at all places. The padding costs
`‖x‖_v^{(n - 1) - ∑_j δ_{jv}/δ_v} ≤ ‖x‖_v^{n - 1 - μ}`, which is what `μ` is for.

⚠ **The normalization.** Mathlib's absolute values, the infinite places with their multiplicity:
(1.4) reads `∏_v (∏_j |f_{jv}(x)|_v)^{m_v/δ_v} ≤ H(x)^{μ - n - ε}`, `H` the affine height relative
to `K`. That is the paper's inequality raised to the power `[K : ℚ]`. `μ` is any lower bound of
the `∑_j δ_{jv}/δ_v` (the paper's `μ` is their minimum).

⚠ **The second part, as its contrapositive.** The paper: if `H` is a component of dimension `n - 1`
of the Zariski closure of the solutions, the `f_{jv}` of some `v` cut `H` in a curve. Here: if they
cut the irreducible `G = 0` in finitely many points at every `v` (`(G^h, f_v^h)` of height `n`),
one `q ∉ (G)` vanishes at all solutions on `G = 0`.

⚠ **Corollary 2 over a Galois field, with `S = ∅`.** `x ∈ ℤⁿ ⊂ O_K^n`. At the place `w = τ_w • ν`
the first polynomial is the conjugate `τ_w(f)`, so `|τ_w(f)(x)|_w = |f(x)|_ν`, and the product over
the places is `|f(x)|_ν^{[K : ℚ]}` up to the other factors. Those other factors are the paper's
"generic" `f₂, …, f_{n-1}` of degree `δ`, taken as `ρ^δ` with generic linear forms `ρ`
(`MvPolynomial.exists_le_height_sup_span_range`), place by place. They need not be conjugate, since
`|ρ(x)|_w^δ ≤ c ‖x‖^δ` is all that is used. Every `f` with algebraic coefficients has them in a
Galois number field, and `|f(x)|_ν` depends only on the embedding. An irreducible factor `G` of
`q₀` that divides a conjugate of `f` carries no solution, since `f(x) ≠ 0`; for the others,
`(G^h, τ_w(f)^h)` has height `2` because `G^h` is prime (`MvPolynomial.prime_homogenization`),
and the generic `ρ` raise it to `n`.
-/

@[expose] public section

open Finset

namespace NumberField

open Height IsDedekindDomain MvPolynomial

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
/-- **Theorem 3, first part, equal degrees** (Corvaja–Zannier 2004): the engine with the constant
`1` as an `n`-th polynomial. Let `|σ| = t + 1` and at each place `v` of `S∞ ∪ S` let `γ_v` be `t`
polynomials of degree `≤ δ` such that `X₀` and the `γ_v^h = homogenize δ γ_v` have finitely many
common zeros in `ℙ^{t+1}`. For `η > 0` and any `C₀`, one `q ≠ 0` vanishes at every `S`-integral
`P` with `∏_v ∏_j |γ_{jv}(P)|_v ≤ C₀ H(P)^{-(1 + η) δ}`. -/
theorem exists_ne_zero_eval_eq_zero_of_prod_le {σ : Type*} [Fintype σ] {t δ : ℕ}
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hδ : 0 < δ) (hcard : Fintype.card σ = t + 1)
    (γ : AbsoluteValue K ℝ → Fin t → MvPolynomial σ K)
    (hγ : ∀ p j, (γ (systemPlace S p) j).totalDegree ≤ δ)
    (hht : ∀ p, (Ideal.span (insert (X none)
      (Set.range fun j ↦ homogenize δ (γ (systemPlace S p) j)))).height = (t + 1 : ℕ))
    {η : ℝ} (hη : 0 < η) (C₀ : ℝ) :
    ∃ q ≠ 0, ∀ P : σ → K, (∀ s, P s ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) →
      ∏ p, (∏ j, systemPlace S p (eval P (γ (systemPlace S p) j))) ^ systemMult S p ≤
        C₀ * mulHeightAff P ^ (-((1 + η) * δ)) → eval P q = 0 := by
  set G : Fin 0 → MvPolynomial σ K := Fin.elim0 with hGdef
  set γ' : AbsoluteValue K ℝ → Fin (t + 1) → MvPolynomial σ K := fun v ↦ Fin.cons 1 (γ v)
    with hγ'def
  have hrGh : (Set.range fun l ↦ homogenization (G l)) = ∅ := Set.range_eq_empty _
  have hspanG : Ideal.span (Set.range G) = ⊥ := by
    rw [Set.range_eq_empty, Ideal.span_empty]
  have hG : (Ideal.span (Set.range G)).IsPrime := by
    rw [hspanG]
    exact Ideal.isPrime_bot
  have hXh : (Ideal.span (insert (X none) (Set.range fun l ↦ homogenization (G l)))).height =
      0 + 1 := by
    rw [hrGh, insert_empty_eq, zero_add]
    exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero (X_ne_zero _)) X_prime.not_isUnit
  have hγ' : ∀ p j, (γ' (systemPlace S p) j).totalDegree ≤ δ := by
    intro p j
    induction j using Fin.cases with
    | zero => simp [γ']
    | succ j => simpa [γ'] using hγ p j
  have hht' : ∀ p, (Ideal.span (Set.range (Fin.append (fun l ↦ homogenization (G l))
      fun j ↦ homogenize δ (γ' (systemPlace S p) j)))).height = (0 + (t + 1) : ℕ) := by
    intro p
    have hr : Set.range (fun j ↦ homogenize δ (γ' (systemPlace S p) j)) =
        insert (X none ^ δ) (Set.range fun j ↦ homogenize δ (γ (systemPlace S p) j)) := by
      rw [show (fun j ↦ homogenize δ (γ' (systemPlace S p) j)) =
        Fin.cons (homogenize δ 1) (fun j ↦ homogenize δ (γ (systemPlace S p) j)) from
          funext fun j ↦ by induction j using Fin.cases <;> simp [γ'],
        Fin.range_cons, homogenize_one]
    rw [range_append, hrGh, Set.empty_union, hr, Ideal.height_span_insert_pow hδ, hht p,
      zero_add]
  obtain ⟨q, hq, hqP⟩ := exists_eval_eq_zero_of_prod_le S hG hδ t.succ_pos
    (by rw [hcard, zero_add]) hXh γ' hγ' hht' hη C₀
  refine ⟨q, fun h ↦ hq (by rw [hspanG, h]; exact Submodule.zero_mem _), fun P hP hprod ↦
    hqP P hP (fun l ↦ l.elim0) ?_⟩
  simpa [γ', Fin.prod_univ_succ] using hprod

open scoped Classical in
/-- **Theorem 3, second part, equal degrees** (Corvaja–Zannier 2004): the engine with `b = 1`. Let
`|σ| = t + 1`, `t > 0`, `G` irreducible, and at each place `v` of `S∞ ∪ S` let `γ_v` be `t`
polynomials of degree `≤ δ` cutting `cl {G = 0}` in finitely many points: `(G^h, γ_v^h)` of
height `t + 1`. For `η > 0` and any `C₀`, one `q ∉ (G)` vanishes at every `S`-integral zero `P`
of `G` with `∏_v ∏_j |γ_{jv}(P)|_v ≤ C₀ H(P)^{-(1 + η) δ}`. -/
theorem exists_eval_eq_zero_of_prod_le_of_irreducible {σ : Type*} [Fintype σ] {t δ : ℕ}
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hδ : 0 < δ) (ht : 0 < t)
    (hcard : Fintype.card σ = t + 1) {G : MvPolynomial σ K} (hG : Irreducible G)
    (γ : AbsoluteValue K ℝ → Fin t → MvPolynomial σ K)
    (hγ : ∀ p j, (γ (systemPlace S p) j).totalDegree ≤ δ)
    (hht : ∀ p, (Ideal.span (insert (homogenization G)
      (Set.range fun j ↦ homogenize δ (γ (systemPlace S p) j)))).height = (t + 1 : ℕ))
    {η : ℝ} (hη : 0 < η) (C₀ : ℝ) :
    ∃ q ∉ Ideal.span {G}, ∀ P : σ → K,
      (∀ s, P s ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) → eval P G = 0 →
      ∏ p, (∏ j, systemPlace S p (eval P (γ (systemPlace S p) j))) ^ systemMult S p ≤
        C₀ * mulHeightAff P ^ (-((1 + η) * δ)) → eval P q = 0 := by
  have hG0 : G ≠ 0 := hG.ne_zero
  have hGdeg : 0 < G.totalDegree := totalDegree_pos_of_irreducible hG
  have hspan : Ideal.span (Set.range ![G]) = Ideal.span {G} := by
    rw [Matrix.range_cons, Matrix.range_empty, Set.union_empty]
  have hrangeh : (Set.range fun l ↦ homogenization (![G] l)) = {homogenization G} := by
    ext x
    simp
  have hG' : (Ideal.span (Set.range ![G])).IsPrime := by
    rw [hspan]
    exact (Ideal.span_singleton_prime hG0).mpr hG.prime
  have hXh : (Ideal.span (insert (X none) (Set.range fun l ↦ homogenization (![G] l)))).height =
      (1 : ℕ) + 1 := by
    rw [hrangeh, height_span_X_none_homogenization hGdeg]
    rfl
  have hht' : ∀ p, (Ideal.span (Set.range (Fin.append (fun l ↦ homogenization (![G] l))
      fun j ↦ homogenize δ (γ (systemPlace S p) j)))).height = (1 + t : ℕ) := by
    intro p
    rw [range_append, hrangeh, Set.singleton_union, hht p, add_comm]
  obtain ⟨q, hq, hqP⟩ := exists_eval_eq_zero_of_prod_le S hG' hδ ht
    (by rw [hcard, add_comm]) hXh γ hγ hht' hη C₀
  refine ⟨q, hspan ▸ hq, fun P hP hGP hprod ↦ hqP P hP (fun l ↦ ?_) hprod⟩
  rw [Fin.fin_one_eq_zero l]
  exact hGP

open scoped Classical in
/-- **Reduction to equal degrees** (Corvaja–Zannier 2004, proof of Theorem 3: "it suffices to
work with `δ_iv = δ_v`"). Let `f_{jv}` have degree `≤ δ_{jv}`, `δ_v = max_j δ_{jv}`, and let a form
`φ` of positive degree and the `f_{jv}^h = homogenize δ_{jv} f_{jv}` generate an ideal of height
`t + 1 = |σ|`. Padding `f_{jv}` by generic linear forms, `f_{jv} ρ_{jv}^{δ_v - δ_{jv}}`, and raising
it to the power `D / δ_v`, `D = ∏_v δ_v`, gives polynomials `γ_{jv}` of degree `≤ D` with the same
property, and the inequality (1.4), `∏_v ∏_j |f_{jv}(P)|_v^{1/δ_v} ≤ H(P)^{μ - (t + 1) - ε}` with
`μ ≤ ∑_j δ_{jv}/δ_v`, becomes the engine's `∏_v ∏_j |γ_{jv}(P)|_v ≤ C H(P)^{-(1 + ε) D}`. -/
theorem exists_prod_le_of_prod_rpow_le {σ : Type*} [Fintype σ] {t : ℕ}
    (S : Finset (HeightOneSpectrum (𝓞 K))) (ht : 0 < t) (hcard : Fintype.card σ = t + 1)
    (f : AbsoluteValue K ℝ → Fin t → MvPolynomial σ K) (δ : AbsoluteValue K ℝ → Fin t → ℕ)
    (hf : ∀ p j, (f (systemPlace S p) j).totalDegree ≤ δ (systemPlace S p) j)
    (hδ : ∀ p j, 0 < δ (systemPlace S p) j)
    {φ : MvPolynomial (Option σ) K} {d : ℕ} (hd : 0 < d) (hφ : φ.IsHomogeneous d)
    (hht : ∀ p, (Ideal.span (insert φ (Set.range fun j ↦
      homogenize (δ (systemPlace S p) j) (f (systemPlace S p) j)))).height = (t + 1 : ℕ))
    {μ : ℝ} (hμ : ∀ p, μ ≤ ∑ j, (δ (systemPlace S p) j : ℝ) / univ.sup (δ (systemPlace S p)))
    (ε : ℝ) :
    ∃ (D : ℕ) (γ : AbsoluteValue K ℝ → Fin t → MvPolynomial σ K) (C : ℝ), 0 < D ∧
      (∀ p j, (γ (systemPlace S p) j).totalDegree ≤ D) ∧
      (∀ p, (Ideal.span (insert φ (Set.range fun j ↦
        homogenize D (γ (systemPlace S p) j)))).height = (t + 1 : ℕ)) ∧
      ∀ P : σ → K, (∀ s, P s ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) →
        ∏ p, (∏ j, systemPlace S p (eval P (f (systemPlace S p) j))) ^
            ((systemMult S p : ℝ) / univ.sup (δ (systemPlace S p))) ≤
          mulHeightAff P ^ (μ - (t + 1) - ε) →
        ∏ p, (∏ j, systemPlace S p (eval P (γ (systemPlace S p) j))) ^ systemMult S p ≤
          C * mulHeightAff P ^ (-((1 + ε) * D)) := by
  set sp := systemPlace S with hsp
  set δm : AbsoluteValue K ℝ → ℕ := fun v ↦ univ.sup (δ v) with hδmdef
  have hδle : ∀ v j, δ v j ≤ δm v := fun v j ↦ le_sup (f := δ v) (mem_univ j)
  have hδm : ∀ p, 0 < δm (sp p) := fun p ↦ (hδ p ⟨0, ht⟩).trans_le (hδle _ _)
  set D : ℕ := ∏ p, δm (sp p) with hDdef
  have hD : 0 < D := prod_pos fun p _ ↦ hδm p
  set k : AbsoluteValue K ℝ → ℕ := fun v ↦ D / δm v with hkdef
  have hk : ∀ p, δm (sp p) * k (sp p) = D := fun p ↦
    Nat.mul_div_cancel' (dvd_prod_of_mem _ (mem_univ p))
  set fh : AbsoluteValue K ℝ → Fin t → MvPolynomial (Option σ) K :=
    fun v j ↦ homogenize (δ v j) (f v j) with hfhdef
  -- The linear forms, place by place.
  set good : AbsoluteValue K ℝ → Prop := fun v ↦ (∀ j, (f v j).totalDegree ≤ δ v j) ∧
    (Ideal.span (insert φ (Set.range (fh v)))).height = (t + 1 : ℕ) with hgooddef
  have hgood : ∀ p, good (sp p) := fun p ↦ ⟨hf p, hht p⟩
  have hρex : ∀ v, ∃ ρ : Fin t → MvPolynomial (Option σ) K, good v →
      (∀ j, ρ j ∈ Submodule.span K (X '' Set.range some : Set (MvPolynomial (Option σ) K))) ∧
      ∀ a : Fin t → ℕ, ((1 + t : ℕ) : ℕ∞) ≤
        (Ideal.span (Set.range ![φ] ∪ Set.range fun j ↦ fh v j * ρ j ^ a j)).height := by
    intro v
    by_cases hv : good v
    · obtain ⟨ρ, h⟩ := exists_le_height_span_mul_pow (Set.range some) (G := ![φ]) (f := fh v)
        (fun l ↦ ⟨d, by rw [Fin.fin_one_eq_zero l]; exact hφ⟩)
        (fun j ↦ ⟨_, isHomogeneous_homogenize (hv.1 j)⟩)
        (by rw [Set.ncard_range_of_injective (Option.some_injective σ), Nat.card_eq_fintype_card,
          hcard, add_comm])
        (by rw [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union,
          hv.2, add_comm])
      exact ⟨ρ, fun _ ↦ h⟩
    · exact ⟨0, fun h ↦ absurd h hv⟩
  choose ρ hρ using hρex
  have hρ1 : ∀ p j, (ρ (sp p) j).IsHomogeneous 1 := fun p j ↦
    isHomogeneous_of_mem_span_X ((hρ (sp p) (hgood p)).1 j)
  -- The padding and the powers.
  set ρa : AbsoluteValue K ℝ → Fin t → MvPolynomial σ K := fun v j ↦ dehomogenize (ρ v j)
    with hρadef
  have hρa : ∀ p j, (ρa (sp p) j).totalDegree ≤ 1 := fun p j ↦
    totalDegree_dehomogenize_le (hρ1 p j)
  have hρah : ∀ p j, homogenize 1 (ρa (sp p) j) = ρ (sp p) j := fun p j ↦
    homogenize_dehomogenize (hρ1 p j)
  set a : AbsoluteValue K ℝ → Fin t → ℕ := fun v j ↦ δm v - δ v j with hadef
  set γ : AbsoluteValue K ℝ → Fin t → MvPolynomial σ K :=
    fun v j ↦ (f v j * ρa v j ^ a v j) ^ k v with hγdef
  have hpow : ∀ p j, (ρa (sp p) j ^ a (sp p) j).totalDegree ≤ 1 * a (sp p) j := fun p j ↦
    (totalDegree_pow _ _).trans (by have := hρa p j; nlinarith)
  have hmul : ∀ p j, (f (sp p) j * ρa (sp p) j ^ a (sp p) j).totalDegree ≤ δm (sp p) := by
    intro p j
    refine (totalDegree_mul _ _).trans ?_
    have := hpow p j
    have := hf p j
    have := hδle (sp p) j
    simp only [a] at *
    omega
  have hγdeg : ∀ p j, (γ (sp p) j).totalDegree ≤ D := fun p j ↦ by
    rw [← hk p, mul_comm]
    exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hmul p j))
  have hγh : ∀ p j, homogenize D (γ (sp p) j) =
      (fh (sp p) j * ρ (sp p) j ^ a (sp p) j) ^ k (sp p) := by
    intro p j
    have h1 : δm (sp p) = δ (sp p) j + 1 * a (sp p) j := by
      have := hδle (sp p) j
      simp only [a]
      omega
    change homogenize D ((f (sp p) j * ρa (sp p) j ^ a (sp p) j) ^ k (sp p)) = _
    rw [← hk p, homogenize_pow (hmul p j)]
    congr 1
    rw [h1, homogenize_mul (hf p j) (hpow p j), homogenize_pow (hρa p j), hρah]
  -- The heights.
  have hγht : ∀ p, (Ideal.span (insert φ (Set.range fun j ↦
      homogenize D (γ (sp p) j)))).height = (t + 1 : ℕ) := by
    intro p
    refine le_antisymm ?_ ?_
    · refine (height_span_le_ncard_of_isHomogeneous (Set.toFinite _) ?_).trans ?_
      · rintro _ (rfl | ⟨j, rfl⟩)
        exacts [⟨d, hd, hφ⟩, ⟨D, hD, isHomogeneous_homogenize (hγdeg p j)⟩]
      · have : (Set.range fun j ↦ homogenize D (γ (sp p) j)).ncard ≤ t := by
          rw [← Set.image_univ]
          exact (Set.ncard_image_le (Set.toFinite _)).trans (by simp)
        exact_mod_cast (Set.ncard_insert_le _ _).trans (by omega)
    · have h := (hρ (sp p) (hgood p)).2 (a (sp p))
      rw [add_comm] at h
      refine h.trans (Ideal.height_le_height_of_forall_isPrime fun Q hQ hle ↦
        Ideal.span_le.mpr ?_)
      rintro _ (⟨l, rfl⟩ | ⟨j, rfl⟩)
      · rw [Fin.fin_one_eq_zero l]
        exact hle (Ideal.subset_span (Set.mem_insert _ _))
      · have hmem : homogenize D (γ (sp p) j) ∈ Q :=
          hle (Ideal.subset_span (Set.mem_insert_of_mem _ ⟨j, rfl⟩))
        rw [hγh] at hmem
        exact hQ.mem_of_pow_mem _ hmem
  -- The inequality.
  set c : AbsoluteValue K ℝ → Fin t → ℝ := fun v j ↦
    ∑ e ∈ (ρa v j).support, v ((ρa v j).coeff e) with hcdef
  have hc0 : ∀ v j, 0 ≤ c v j := fun v j ↦ sum_nonneg fun e _ ↦ apply_nonneg _ _
  set C : ℝ := ∏ p, (∏ j, c (sp p) j ^ a (sp p) j) ^ (k (sp p) * systemMult S p) with hCdef
  refine ⟨D, γ, C, hD, hγdeg, hγht, fun P hPS hP ↦ ?_⟩
  set nP : InfinitePlace K ⊕ S → ℝ := fun p ↦ ⨆ o : Option σ, sp p (o.elim 1 P) with hnPdef
  have hnP1 : ∀ p, 1 ≤ nP p := fun p ↦ one_le_iSup_abv_optionElim _ P
  set F : InfinitePlace K ⊕ S → ℝ := fun p ↦ ∏ j, sp p (eval P (f (sp p) j)) with hFdef
  have hF0 : ∀ p, 0 ≤ F p := fun p ↦ prod_nonneg fun j _ ↦ apply_nonneg _ _
  set E : ℝ := D * (t - μ) with hEdef
  have hloc : ∀ p, (∏ j, sp p (eval P (γ (sp p) j))) ^ systemMult S p ≤
      (∏ j, c (sp p) j ^ a (sp p) j) ^ (k (sp p) * systemMult S p) *
        (F p ^ ((systemMult S p : ℝ) / δm (sp p))) ^ (D : ℝ) *
        (nP p ^ systemMult S p) ^ E := by
    intro p
    set v := sp p
    set m := systemMult S p
    set A := ∑ j, a v j with hAdef
    set Cc := ∏ j, c v j ^ a v j with hCcdef
    have hCc0 : 0 ≤ Cc := prod_nonneg fun j _ ↦ pow_nonneg (hc0 v j) _
    have hstep : ∏ j, v (eval P (γ v j)) ≤ (F p * Cc * nP p ^ A) ^ k v := by
      calc ∏ j, v (eval P (γ v j))
          ≤ ∏ j, (v (eval P (f v j)) * (c v j * nP p) ^ a v j) ^ k v := by
            refine prod_le_prod₀ (fun j _ ↦ apply_nonneg _ _) fun j _ ↦ ?_
            simp only [γ, map_pow, map_mul]
            gcongr
            simpa using abv_eval_le v P (ρa v j) (hρa p j)
        _ = (F p * Cc * nP p ^ A) ^ k v := by
            simp only [F, Cc, A, prod_pow, mul_pow, prod_mul_distrib, prod_pow_eq_pow_sum]
            rw [← mul_assoc]
    have hD' : (D : ℝ) = δm v * k v := by exact_mod_cast (hk p).symm
    have hδm' : (0 : ℝ) < δm v := by exact_mod_cast hδm p
    -- The exponent of `‖P‖_v`.
    have hAk : ((A * k v : ℕ) : ℝ) ≤ E := by
      have hA : (A : ℝ) = t * δm v - ∑ j, (δ v j : ℝ) := by
        simp only [A, a]
        push_cast [Nat.cast_sub (hδle v _)]
        rw [sum_sub_distrib]
        simp
      have hdiv : ∑ j, (δ v j : ℝ) / δm v = (∑ j, (δ v j : ℝ)) / δm v := (sum_div _ _ _).symm
      have hμp := hμ p
      rw [hdiv] at hμp
      have : (A : ℝ) * k v = D * (t - (∑ j, (δ v j : ℝ)) / δm v) := by
        rw [hA, hD']
        field_simp
      push_cast
      rw [this, hEdef]
      exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg D)
    calc (∏ j, v (eval P (γ v j))) ^ m
        ≤ ((F p * Cc * nP p ^ A) ^ k v) ^ m :=
          pow_le_pow_left₀ (prod_nonneg fun j _ ↦ apply_nonneg _ _) hstep m
      _ = Cc ^ (k v * m) * F p ^ (k v * m) * (nP p ^ m) ^ (A * k v) := by ring
      _ ≤ Cc ^ (k v * m) * (F p ^ ((m : ℝ) / δm v)) ^ (D : ℝ) * (nP p ^ m) ^ E := by
          have h1 : F p ^ (k v * m) = (F p ^ ((m : ℝ) / δm v)) ^ (D : ℝ) := by
            rw [← Real.rpow_mul (hF0 p), ← Real.rpow_natCast]
            congr 1
            rw [hD']
            push_cast
            field_simp
          have h2 : (nP p ^ m) ^ (A * k v) ≤ (nP p ^ m) ^ E := by
            rw [← Real.rpow_natCast]
            exact Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (hnP1 p)) hAk
          rw [h1]
          gcongr
  -- The product over the places.
  have hH : mulHeightAff P = ∏ p, nP p ^ systemMult S p := mulHeightAff_eq_prod_systemPlace S hPS
  set H := mulHeightAff P with hHdef
  have hH0 : 0 < H := mulHeightAff_pos P
  calc ∏ p, (∏ j, sp p (eval P (γ (sp p) j))) ^ systemMult S p
      ≤ ∏ p, ((∏ j, c (sp p) j ^ a (sp p) j) ^ (k (sp p) * systemMult S p) *
          (F p ^ ((systemMult S p : ℝ) / δm (sp p))) ^ (D : ℝ) *
          (nP p ^ systemMult S p) ^ E) :=
        prod_le_prod₀ (fun p _ ↦ pow_nonneg (prod_nonneg fun j _ ↦ apply_nonneg _ _) _)
          fun p _ ↦ hloc p
    _ = C * (∏ p, F p ^ ((systemMult S p : ℝ) / δm (sp p))) ^ (D : ℝ) * H ^ E := by
        rw [prod_mul_distrib, prod_mul_distrib, Real.finsetProd_rpow _ _
          (fun p _ ↦ Real.rpow_nonneg (hF0 p) _), Real.finsetProd_rpow _ _
          (fun p _ ↦ pow_nonneg (zero_le_one.trans (hnP1 p)) _), ← hH]
    _ ≤ C * (H ^ (μ - (t + 1) - ε)) ^ (D : ℝ) * H ^ E := by
        gcongr
    _ = C * H ^ (-((1 + ε) * D)) := by
        rw [← Real.rpow_mul hH0.le, mul_assoc, ← Real.rpow_add hH0]
        congr 2
        rw [hEdef]
        ring

open scoped Classical in
/-- **Theorem 3, first part** (Corvaja–Zannier 2004). Let `|σ| = n = t + 1 ≥ 2` and at each place
`v` of `S∞ ∪ S` let `f_{1v}, …, f_{tv}` have degrees `≤ δ_{jv}`, `δ_{jv} > 0`, such that `X₀` and
the `f_{jv}^h = homogenize δ_{jv} f_{jv}` have finitely many common zeros in `ℙⁿ`. Let
`δ_v = max_j δ_{jv}` and `μ ≤ ∑_j δ_{jv}/δ_v` for every `v`. For `ε > 0` the `S`-integral solutions
of `∏_v ∏_j |f_{jv}(x)|_v^{1/δ_v} ≤ H(x)^{μ - n - ε}` (1.4) are not Zariski-dense: one `q ≠ 0`
vanishes at all of them. -/
theorem exists_ne_zero_eval_eq_zero_of_prod_rpow_le {σ : Type*} [Fintype σ] {t : ℕ}
    (S : Finset (HeightOneSpectrum (𝓞 K))) (ht : 0 < t) (hcard : Fintype.card σ = t + 1)
    (f : AbsoluteValue K ℝ → Fin t → MvPolynomial σ K) (δ : AbsoluteValue K ℝ → Fin t → ℕ)
    (hf : ∀ p j, (f (systemPlace S p) j).totalDegree ≤ δ (systemPlace S p) j)
    (hδ : ∀ p j, 0 < δ (systemPlace S p) j)
    (hX : ∀ p, (Ideal.span (insert (X none) (Set.range fun j ↦
      homogenize (δ (systemPlace S p) j) (f (systemPlace S p) j)))).height = (t + 1 : ℕ))
    {μ : ℝ} (hμ : ∀ p, μ ≤ ∑ j, (δ (systemPlace S p) j : ℝ) / univ.sup (δ (systemPlace S p)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q ≠ 0, ∀ P : σ → K, (∀ s, P s ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) →
      ∏ p, (∏ j, systemPlace S p (eval P (f (systemPlace S p) j))) ^
          ((systemMult S p : ℝ) / univ.sup (δ (systemPlace S p))) ≤
        mulHeightAff P ^ (μ - (t + 1) - ε) → eval P q = 0 := by
  obtain ⟨D, γ, C, hD, hγ, hγht, hle⟩ := exists_prod_le_of_prod_rpow_le S ht hcard f δ hf hδ
    one_pos (isHomogeneous_X K none) hX hμ ε
  obtain ⟨q, hq, hqP⟩ := exists_ne_zero_eval_eq_zero_of_prod_le S hD hcard γ hγ hγht hε C
  exact ⟨q, hq, fun P hP h ↦ hqP P hP (hle P hP h)⟩

open scoped Classical in
/-- **Theorem 3, second part** (Corvaja–Zannier 2004), as its contrapositive. Under the hypotheses
of the first part, let `G` be irreducible and suppose that at every place `v` the `f_{jv}` cut
`cl {G = 0}` in finitely many points: `(G^h, f_v^h)` has height `n`. Then one `q ∉ (G)` vanishes
at every `S`-integral solution of (1.4) on `G = 0`, so `G = 0` is not a component of the Zariski
closure of the solutions. -/
theorem exists_eval_eq_zero_of_prod_rpow_le_of_irreducible {σ : Type*} [Fintype σ] {t : ℕ}
    (S : Finset (HeightOneSpectrum (𝓞 K))) (ht : 0 < t) (hcard : Fintype.card σ = t + 1)
    {G : MvPolynomial σ K} (hG : Irreducible G)
    (f : AbsoluteValue K ℝ → Fin t → MvPolynomial σ K) (δ : AbsoluteValue K ℝ → Fin t → ℕ)
    (hf : ∀ p j, (f (systemPlace S p) j).totalDegree ≤ δ (systemPlace S p) j)
    (hδ : ∀ p j, 0 < δ (systemPlace S p) j)
    (hfin : ∀ p, (Ideal.span (insert (homogenization G) (Set.range fun j ↦
      homogenize (δ (systemPlace S p) j) (f (systemPlace S p) j)))).height = (t + 1 : ℕ))
    {μ : ℝ} (hμ : ∀ p, μ ≤ ∑ j, (δ (systemPlace S p) j : ℝ) / univ.sup (δ (systemPlace S p)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q ∉ Ideal.span {G}, ∀ P : σ → K,
      (∀ s, P s ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) → eval P G = 0 →
      ∏ p, (∏ j, systemPlace S p (eval P (f (systemPlace S p) j))) ^
          ((systemMult S p : ℝ) / univ.sup (δ (systemPlace S p))) ≤
        mulHeightAff P ^ (μ - (t + 1) - ε) → eval P q = 0 := by
  obtain ⟨D, γ, C, hD, hγ, hγht, hle⟩ := exists_prod_le_of_prod_rpow_le S ht hcard f δ hf hδ
    (totalDegree_pos_of_irreducible hG) (isHomogeneous_homogenization G) hfin hμ ε
  obtain ⟨q, hq, hqP⟩ :=
    exists_eval_eq_zero_of_prod_le_of_irreducible S hD ht hcard hG γ hγ hγht hε C
  exact ⟨q, hq, fun P hP hGP h ↦ hqP P hP hGP (hle P hP h)⟩

open scoped Classical in
/-- **Corollary 2** (Corvaja–Zannier 2004). Let `K` be a number field, Galois over `ℚ`, `ν` an
infinite place of `K`, `f ∈ K[X_s | s ∈ σ]` of degree `δ > 0`, `n = |σ| ≥ 2` and `ε > 0`. The
`x ∈ ℤⁿ` with `0 < |f(x)|_ν < H(x)^{-δ(n - 1) - ε}`, `H(x) = max (1, |x_s|)`, lie in a variety of
dimension `≤ n - 2`: there are finitely many pairs `(G, q)`, `G` irreducible and `q ∉ (G)`, and
every such `x` is a common zero of one pair. -/
theorem exists_finset_eval_eq_zero_of_abv_lt [IsGalois ℚ K] {σ : Type*} [Fintype σ]
    (hn : 2 ≤ Fintype.card σ) (ν : InfinitePlace K) {f : MvPolynomial σ K}
    (hf : 0 < f.totalDegree) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (MvPolynomial σ K × MvPolynomial σ K),
      (∀ y ∈ T, Irreducible y.1 ∧ y.2 ∉ Ideal.span {y.1}) ∧
      ∀ x : σ → ℤ, 0 < ν (eval (fun s ↦ (x s : K)) f) →
        ν (eval (fun s ↦ (x s : K)) f) <
          max 1 (⨆ s, |(x s : ℝ)|) ^ (-(f.totalDegree * (Fintype.card σ - 1 : ℝ)) - ε) →
        ∃ y ∈ T, eval (fun s ↦ (x s : K)) y.1 = 0 ∧ eval (fun s ↦ (x s : K)) y.2 = 0 := by
  set δ := f.totalDegree with hδdef
  set m := Fintype.card σ - 2 with hmdef
  have hcard : Fintype.card σ = m + 1 + 1 := by omega
  have hne : Nonempty σ := Fintype.card_pos_iff.mp (by omega)
  set S : Finset (HeightOneSpectrum (𝓞 K)) := ∅ with hSdef
  set sp := systemPlace S with hsp
  set Pt : (σ → ℤ) → σ → K := fun x s ↦ (x s : K) with hPtdef
  set Hx : (σ → ℤ) → ℝ := fun x ↦ max 1 (⨆ s, |(x s : ℝ)|) with hHxdef
  set sol : (σ → ℤ) → Prop := fun x ↦ 0 < ν (eval (Pt x) f) ∧
    ν (eval (Pt x) f) < Hx x ^ (-(δ * (Fintype.card σ - 1 : ℝ)) - ε) with hsoldef
  -- The Galois conjugates of `ν`.
  have hτex : ∀ v : AbsoluteValue K ℝ, ∃ τ : K ≃ₐ[ℚ] K,
      (∃ p, sp p = v) → ∀ a, v (τ a) = ν a := by
    intro v
    by_cases hv : ∃ p, sp p = v
    · obtain ⟨p, rfl⟩ := hv
      rcases p with w | ⟨w, hw⟩
      · obtain ⟨τ, hτ⟩ := InfinitePlace.exists_smul_eq_of_comap_eq (k := ℚ) (w := ν) (w' := w)
          (Subsingleton.elim _ _)
        refine ⟨τ, fun _ a ↦ ?_⟩
        change w (τ a) = ν a
        rw [← hτ, InfinitePlace.smul_apply, AlgEquiv.symm_apply_apply]
      · simp [S] at hw
    · exact ⟨AlgEquiv.refl, fun h ↦ absurd h hv⟩
  choose τ hτ using hτex
  set F : AbsoluteValue K ℝ → MvPolynomial σ K := fun v ↦ map (τ v : K →+* K) f with hFdef
  have hFdeg : ∀ v, (F v).totalDegree = δ := fun v ↦ by
    simp only [F, totalDegree, support_map_of_injective _ (τ v : K →+* K).injective]
    rfl
  have hFeval : ∀ p x, sp p (eval (Pt x) (F (sp p))) = ν (eval (Pt x) f) := by
    intro p x
    have hcomm : ∀ g : MvPolynomial σ K,
        eval (Pt x) (map (τ (sp p) : K →+* K) g) = τ (sp p) (eval (Pt x) g) := by
      intro g
      induction g using MvPolynomial.induction_on with
      | C a => simp
      | add g g' hg hg' => simp [hg, hg']
      | mul_X g s hg => simp [hg, Pt]
    rw [hcomm, hτ _ ⟨p, rfl⟩]
  -- The points.
  have hPS : ∀ x s, Pt x s ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K := fun x s ↦
    intCast_mem _ _
  have hnP : ∀ x p, (⨆ o : Option σ, sp p (o.elim 1 (Pt x))) = Hx x := by
    intro x p
    rcases p with w | ⟨w, hw⟩
    · have hval : ∀ s, sp (.inl w) (Pt x s) = |(x s : ℝ)| := fun s ↦ by
        change w (x s : K) = _
        rw [InfinitePlace.map_intCast, Int.norm_eq_abs]
      have hbdd : BddAbove (Set.range fun o : Option σ ↦ sp (.inl w) (o.elim 1 (Pt x))) :=
        (Set.finite_range _).bddAbove
      have hbdd' : BddAbove (Set.range fun s ↦ |(x s : ℝ)|) := (Set.finite_range _).bddAbove
      refine le_antisymm (ciSup_le fun o ↦ ?_) (max_le ?_ (ciSup_le fun s ↦ ?_))
      · cases o with
        | none =>
          rw [Option.elim_none, map_one]
          exact le_max_left _ _
        | some s =>
          rw [Option.elim_some, hval]
          exact le_max_of_le_right (le_ciSup hbdd' s)
      · exact le_ciSup_of_le hbdd none (by rw [Option.elim_none, map_one])
      · exact le_ciSup_of_le hbdd (some s) (by rw [Option.elim_some, hval])
    · simp [S] at hw
  set d : ℕ := ∑ p, systemMult S p with hddef
  have hH : ∀ x, mulHeightAff (Pt x) = Hx x ^ d := fun x ↦ by
    rw [mulHeightAff_eq_prod_systemPlace S (hPS x), hddef, ← prod_pow_eq_pow_sum]
    exact prod_congr rfl fun p _ ↦ by rw [hnP x p]
  have hHx1 : ∀ x, 1 ≤ Hx x := fun x ↦ le_max_left _ _
  have hδ0 : (0 : ℝ) < δ := Nat.cast_pos.mpr hf
  -- The forms at the places: `F_v` and `t - 1` generic linear forms to the power `δ`.
  have hfam : ∀ (φ : MvPolynomial (Option σ) K) (dφ : ℕ), 0 < dφ → φ.IsHomogeneous dφ →
      (∀ p, (2 : ℕ∞) ≤ (Ideal.span {φ, homogenization (F (sp p))}).height) →
      ∃ (γ : AbsoluteValue K ℝ → Fin (m + 1) → MvPolynomial σ K) (C₀ : ℝ),
        (∀ p j, (γ (sp p) j).totalDegree ≤ δ) ∧
        (∀ p, (Ideal.span (insert φ (Set.range fun j ↦
          homogenize δ (γ (sp p) j)))).height = (m + 1 + 1 : ℕ)) ∧
        ∀ x, sol x → ∏ p, (∏ j, sp p (eval (Pt x) (γ (sp p) j))) ^ systemMult S p ≤
          C₀ * mulHeightAff (Pt x) ^ (-((1 + ε / δ) * δ)) := by
    intro φ dφ hdφ hφ h2
    set good : AbsoluteValue K ℝ → Prop := fun v ↦
      (2 : ℕ∞) ≤ (Ideal.span {φ, homogenization (F v)}).height with hgooddef
    have hρex : ∀ v, ∃ ρ : Fin m → MvPolynomial (Option σ) K, good v →
        (∀ i, ρ i ∈ Submodule.span K (X '' Set.range some : Set (MvPolynomial (Option σ) K))) ∧
        ((2 + m : ℕ) : ℕ∞) ≤
          (Ideal.span {φ, homogenization (F v)} ⊔ Ideal.span (Set.range ρ)).height := by
      intro v
      by_cases hv : good v
      · obtain ⟨ρ, h⟩ := exists_le_height_sup_span_range (Set.range some) _ (k := 2)
          (by exact_mod_cast hv) m (by
            rw [Set.ncard_range_of_injective (Option.some_injective σ), Nat.card_eq_fintype_card,
              hcard]
            omega)
        exact ⟨ρ, fun _ ↦ h⟩
      · exact ⟨0, fun h ↦ absurd h hv⟩
    choose ρ hρ using hρex
    have hρ1 : ∀ p i, (ρ (sp p) i).IsHomogeneous 1 := fun p i ↦
      isHomogeneous_of_mem_span_X ((hρ _ (h2 p)).1 i)
    set ρa : AbsoluteValue K ℝ → Fin m → MvPolynomial σ K := fun v i ↦ dehomogenize (ρ v i)
      with hρadef
    have hρa : ∀ p i, (ρa (sp p) i).totalDegree ≤ 1 := fun p i ↦
      totalDegree_dehomogenize_le (hρ1 p i)
    have hρah : ∀ p i, homogenize 1 (ρa (sp p) i) = ρ (sp p) i := fun p i ↦
      homogenize_dehomogenize (hρ1 p i)
    set γ : AbsoluteValue K ℝ → Fin (m + 1) → MvPolynomial σ K :=
      fun v ↦ Fin.cons (F v) fun i ↦ ρa v i ^ δ with hγdef
    set c : AbsoluteValue K ℝ → Fin m → ℝ := fun v i ↦
      ∑ e ∈ (ρa v i).support, v ((ρa v i).coeff e) with hcdef
    have hc0 : ∀ v i, 0 ≤ c v i := fun v i ↦ sum_nonneg fun e _ ↦ apply_nonneg _ _
    refine ⟨γ, ∏ p, (∏ i, c (sp p) i ^ δ) ^ systemMult S p, fun p j ↦ ?_, fun p ↦ ?_,
      fun x hx ↦ ?_⟩
    -- The degrees.
    · induction j using Fin.cases with
      | zero => simp [γ, hFdeg]
      | succ i =>
        simp only [γ, Fin.cons_succ]
        exact (totalDegree_pow _ _).trans (by have := hρa p i; nlinarith)
    -- The heights.
    · have hr : (Set.range fun j ↦ homogenize δ (γ (sp p) j)) =
          insert (homogenization (F (sp p))) (Set.range fun i ↦ ρ (sp p) i ^ δ) := by
        rw [show (fun j ↦ homogenize δ (γ (sp p) j)) =
            Fin.cons (homogenization (F (sp p))) (fun i ↦ ρ (sp p) i ^ δ) from
          funext fun j ↦ ?_, Fin.range_cons]
        induction j using Fin.cases with
        | zero => simp [γ, homogenization, hFdeg]
        | succ i =>
          simp only [γ, Fin.cons_succ]
          rw [← hρah p i, ← homogenize_pow (hρa p i), one_mul]
      rw [hr]
      refine le_antisymm ?_ ?_
      · refine (height_span_le_ncard_of_isHomogeneous (Set.toFinite _) ?_).trans ?_
        · rintro _ (rfl | rfl | ⟨i, rfl⟩)
          · exact ⟨dφ, hdφ, hφ⟩
          · exact ⟨_, by rw [hFdeg]; exact hf, isHomogeneous_homogenization _⟩
          · exact ⟨1 * δ, by omega, (hρ1 p i).pow δ⟩
        · have : (Set.range fun i ↦ ρ (sp p) i ^ δ).ncard ≤ m := by
            rw [← Set.image_univ]
            exact (Set.ncard_image_le (Set.toFinite _)).trans (by simp)
          exact_mod_cast ((Set.ncard_insert_le _ _).trans
            (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1)).trans (by omega)
      · refine (le_of_eq_of_le (by push_cast; ring) (hρ (sp p) (h2 p)).2).trans
          (Ideal.height_le_height_of_forall_isPrime fun Q hQ hle ↦
            sup_le (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_))
        · rintro _ (rfl | rfl)
          · exact hle (Ideal.subset_span (Set.mem_insert _ _))
          · exact hle (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
        · rintro _ ⟨i, rfl⟩
          exact hQ.mem_of_pow_mem δ (hle (Ideal.subset_span
            (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨i, rfl⟩))))
    -- The inequality.
    · set P := Pt x with hPdef
      have hHx0 : 0 < Hx x := zero_lt_one.trans_le (hHx1 x)
      set B := ν (eval P f) * Hx x ^ (δ * m) with hBdef
      have hB0 : 0 ≤ B := mul_nonneg (apply_nonneg _ _) (pow_nonneg hHx0.le _)
      have hloc : ∀ p, (∏ j, sp p (eval P (γ (sp p) j))) ^ systemMult S p ≤
          (∏ i, c (sp p) i ^ δ) ^ systemMult S p * B ^ systemMult S p := by
        intro p
        rw [← mul_pow]
        refine pow_le_pow_left₀ (prod_nonneg fun j _ ↦ apply_nonneg _ _) ?_ _
        rw [Fin.prod_univ_succ]
        simp only [γ, Fin.cons_zero, Fin.cons_succ, map_pow]
        rw [hFeval p x]
        calc ν (eval P f) * ∏ i, sp p (eval P (ρa (sp p) i)) ^ δ
            ≤ ν (eval P f) * ∏ i, (c (sp p) i * Hx x) ^ δ := by
              gcongr with i
              have := abv_eval_le (sp p) P (ρa (sp p) i) (hρa p i)
              rwa [hnP x p, pow_one] at this
          _ = (∏ i, c (sp p) i ^ δ) * B := by
              simp only [B, mul_pow, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin,
                ← pow_mul]
              ring
      have hBle : B ≤ Hx x ^ (-(δ : ℝ) - ε) := by
        have hcardR : (Fintype.card σ : ℝ) = m + 2 := by rw [hcard]; push_cast; ring
        calc B ≤ Hx x ^ (-(δ * (Fintype.card σ - 1 : ℝ)) - ε) * Hx x ^ ((δ * m : ℕ) : ℝ) := by
              rw [Real.rpow_natCast]
              exact mul_le_mul_of_nonneg_right hx.2.le (pow_nonneg hHx0.le _)
          _ = Hx x ^ (-(δ : ℝ) - ε) := by
              rw [← Real.rpow_add hHx0, hcardR]
              congr 1
              push_cast
              ring
      calc ∏ p, (∏ j, sp p (eval P (γ (sp p) j))) ^ systemMult S p
          ≤ ∏ p, ((∏ i, c (sp p) i ^ δ) ^ systemMult S p * B ^ systemMult S p) :=
            prod_le_prod₀ (fun p _ ↦ pow_nonneg (prod_nonneg fun j _ ↦ apply_nonneg _ _) _)
              fun p _ ↦ hloc p
        _ = (∏ p, (∏ i, c (sp p) i ^ δ) ^ systemMult S p) * B ^ d := by
            rw [prod_mul_distrib, prod_pow_eq_pow_sum]
        _ ≤ (∏ p, (∏ i, c (sp p) i ^ δ) ^ systemMult S p) * (Hx x ^ (-(δ : ℝ) - ε)) ^ d := by
            gcongr
        _ = (∏ p, (∏ i, c (sp p) i ^ δ) ^ systemMult S p) *
              mulHeightAff P ^ (-((1 + ε / δ) * δ)) := by
            rw [hH x, Real.rpow_pow_comm hHx0.le]
            congr 2
            field_simp
            ring
  have hη : 0 < ε / δ := div_pos hε hδ0
  -- The first part of Theorem 3: the solutions lie on `q₀ = 0`.
  obtain ⟨γ₀, C₀, hγ₀, hγ₀ht, hγ₀le⟩ := hfam (X none) 1 one_pos (isHomogeneous_X K none)
    fun p ↦ (height_span_X_none_homogenization (by rw [hFdeg]; exact hf)).ge
  obtain ⟨q₀, hq₀, hq₀P⟩ := exists_ne_zero_eval_eq_zero_of_prod_le S hf hcard γ₀ hγ₀ hγ₀ht hη C₀
  have hsol0 : ∀ x, sol x → eval (Pt x) q₀ = 0 := fun x hx ↦
    hq₀P (Pt x) (hPS x) (hγ₀le x hx)
  -- The second part, on each irreducible factor `G` of `q₀`.
  have hpair : ∀ G ∈ UniqueFactorizationMonoid.factors q₀, ∃ q ∉ Ideal.span {G},
      ∀ x, sol x → eval (Pt x) G = 0 → eval (Pt x) q = 0 := by
    intro G hGm
    have hG := UniqueFactorizationMonoid.irreducible_of_factor G hGm
    by_cases hdiv : ∃ p, G ∣ F (sp p)
    -- `G` divides a conjugate of `f`: no solution on `G = 0`.
    · refine ⟨1, fun h ↦ hG.not_isUnit (Ideal.span_singleton_eq_top.mp
        ((Ideal.eq_top_iff_one _).mpr h)), fun x hx hGx ↦ absurd ?_ hx.1.ne'⟩
      obtain ⟨p, c, hc⟩ := hdiv
      rw [← hFeval p x, hc, map_mul, hGx, zero_mul, map_zero]
    · push Not at hdiv
      have h2 : ∀ p, (2 : ℕ∞) ≤
          (Ideal.span {homogenization G, homogenization (F (sp p))}).height := fun p ↦
        two_le_height_span_pair (prime_homogenization hG.prime) fun hmem ↦ hdiv p (by
          have := map_dvd (dehomogenize (R := K) (σ := σ)) (Ideal.mem_span_singleton.mp hmem)
          rwa [dehomogenize_homogenization, dehomogenize_homogenization] at this)
      obtain ⟨γ, C, hγ, hγht, hγle⟩ := hfam (homogenization G) G.totalDegree
        (totalDegree_pos_of_irreducible hG) (isHomogeneous_homogenization G) h2
      obtain ⟨q, hq, hqP⟩ := exists_eval_eq_zero_of_prod_le_of_irreducible S hf m.succ_pos
        hcard hG γ hγ hγht hη C
      exact ⟨q, hq, fun x hx hGx ↦ hqP (Pt x) (hPS x) hGx (hγle x hx)⟩
  choose! qG hqG hqGP using hpair
  refine ⟨(UniqueFactorizationMonoid.factors q₀).toFinset.image fun G ↦ (G, qG G),
    fun y hy ↦ ?_, fun x h1 h2 ↦ ?_⟩
  · obtain ⟨G, hG, rfl⟩ := mem_image.mp hy
    have hG' := Multiset.mem_toFinset.mp hG
    exact ⟨UniqueFactorizationMonoid.irreducible_of_factor G hG', hqG G hG'⟩
  · have hx : sol x := ⟨h1, h2⟩
    obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hq₀
    have hprod : eval (Pt x) (UniqueFactorizationMonoid.factors q₀).prod = 0 := by
      have h := congrArg (eval (Pt x)) hu
      rw [map_mul, hsol0 x hx] at h
      exact (mul_eq_zero.mp h).resolve_right ((u.isUnit.map (eval (Pt x))).ne_zero)
    rw [map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hprod
    obtain ⟨G, hG, hGx⟩ := hprod
    exact ⟨(G, qG G), mem_image.mpr ⟨G, Multiset.mem_toFinset.mpr hG, rfl⟩, hGx,
      hqGP G hG x hx hGx⟩

end NumberField
