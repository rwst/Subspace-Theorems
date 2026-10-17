/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import CorvajaZannier2004Thue.Engine

-- Used only inside proofs.
import DiophantineApproximation.LocalNullstellensatz
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic.FieldSimp
import STForMathlib.RingTheory.MvPolynomial.EvalBound

/-!
# Proposition 3.1: equal degrees

P. Corvaja and U. Zannier, *On a general Thue's equation*, Amer. J. Math. 126 (2004), §3.

Let `Z = {G₁ = ⋯ = G_b = 0} ⊆ 𝔸^{b + t}` with `(G)` prime and `(G^h, X₀)` of height `b + 1`, and
`f₁, …, f_r, g` with `f₁ ⋯ f_r = g` on `Z`, `deg fᵢ ≤ δ`, `deg g ≤ e`. Suppose that any `t` of the
`fᵢ^h = homogenize δ fᵢ` cut the projective closure `cl Z` in finitely many points
(`(G^h, f^h_J)` of height `b + t`), that no `s + 1` of them have a common zero on `cl Z ∖ Z`, and
that `r > s (t + 1)/t + e/δ`. Then one `q ∉ (G)` vanishes at every `S`-integral point of `Z`
(`NumberField.exists_eval_eq_zero_of_prod_sub_mem`): `Z(O_S)` is not Zariski-dense in `Z`
(Finding 2 of the README).

## Main results

* `Finset.prod_range_pow_le_prod_range_pow`: the geometric mean of the `t` smallest of a sorted
  list is at most that of the `s ≥ t` smallest, the paper's (3.3).
* `MvPolynomial.exists_prod_mul_pow_le_of_monotone`: **Lemma 3.3**, at one absolute value and
  uniformly in `P`: the `s` smallest `|fᵢ(P)|_v` have product `≤ C ‖P‖_v ^ (e - δ (r - s))`.
* `NumberField.exists_eval_eq_zero_of_prod_sub_mem`: **Proposition 3.1**.

## Implementation notes

⚠ **No sequences, no compactness of `Z(k_v)`** (Finding 3). Lemma 3.3 comes from the local
Nullstellensatz inequality (`MvPolynomial.exists_le_abv_eval_of_pow_mem`): for the `s + 1`
smallest `|fᵢ(P)|_v`, one of them, hence the `(s + 1)`-st, is `≥ c ‖P‖_v ^ δ` once `‖P‖_v ≥ R`,
and for `‖P‖_v < R` everything is bounded. The hypothesis "no `s + 1` of the `fᵢ^h` have a common
zero on `cl Z ∖ Z`" is stated in ideal form: each `X_x` has a power in `(X₀, G^h, f^h_J)`.

⚠ **The classes are the orderings.** For each `P` and each place `v` of the system, the
permutation `Tuple.sort` of `i ↦ |fᵢ(P)|_v` is chosen; a class is a choice of one permutation per
place, there are finitely many, and the engine (CZ.4, prime version) is applied once per class
with `γ_v` the `t` first `f`s in that order. The product of the `q`s is outside `(G)` because
`(G)` is prime.

⚠ **"Any `t` of the `fᵢ` define in `Z` a finite set" is taken projectively**, as Lemma 3.2 uses
it: `(G^h, f^h_J)` of height `b + t` for every `t`-subset `J`, so the common zeros on `cl Z` are
finite at infinity too.

⚠ **`t ≤ s` is assumed.** The paper derives it from `cl Z ∖ Z` having dimension `t - 1`; here it
is a hypothesis. `s < r` follows from the inequality on `r`.

⚠ **The exponent.** With `η = (t r δ − s (t + 1) δ − t e)/(s δ) > 0`,
`t (e − δ (r − s))/s = −(1 + η) δ`, so Lemma 3.3 and (3.3), multiplied over the places, are the
engine's hypothesis `∏_v ∏_j |γ_{jv}(P)|_v ≤ C₀ H(P) ^ (-(1 + η) δ)`.
-/

@[expose] public section

open Finset

namespace Finset

/-- **The paper's (3.3)**: for a list `μ₀ ≤ μ₁ ≤ ⋯` of nonnegative reals and `t ≤ s`,
`(μ₀ ⋯ μ_{t-1})^s ≤ (μ₀ ⋯ μ_{s-1})^t`. -/
theorem prod_range_pow_le_prod_range_pow {μ : ℕ → ℝ} (h0 : ∀ k, 0 ≤ μ k) {t s : ℕ}
    (hts : t ≤ s) (hμ : ∀ j k, j ≤ k → k < s → μ j ≤ μ k) :
    (∏ k ∈ range t, μ k) ^ s ≤ (∏ k ∈ range s, μ k) ^ t := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hts
  rcases Nat.eq_zero_or_pos u with rfl | hu
  · exact le_rfl
  have hlt : t < t + u := by omega
  rw [← prod_range_mul_prod_Ico μ hts, mul_pow, pow_add]
  have hP0 : 0 ≤ ∏ k ∈ range t, μ k := prod_nonneg fun k _ ↦ h0 k
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hP0 _)
  have h1 : ∏ k ∈ range t, μ k ≤ μ t ^ t := by
    calc ∏ k ∈ range t, μ k ≤ ∏ _k ∈ range t, μ t :=
          prod_le_prod₀ (fun k _ ↦ h0 k) fun k hk ↦ hμ k t (mem_range.mp hk).le hlt
      _ = μ t ^ t := by rw [prod_const, card_range]
  have h2 : μ t ^ u ≤ ∏ k ∈ Ico t (t + u), μ k := by
    calc μ t ^ u = ∏ _k ∈ Ico t (t + u), μ t := by
          rw [prod_const, Nat.card_Ico, Nat.add_sub_cancel_left]
      _ ≤ ∏ k ∈ Ico t (t + u), μ k := prod_le_prod₀ (fun _ _ ↦ h0 t) fun k hk ↦
          hμ t k (mem_Ico.mp hk).1 (mem_Ico.mp hk).2
  calc (∏ k ∈ range t, μ k) ^ u ≤ (μ t ^ t) ^ u := pow_le_pow_left₀ hP0 h1 _
    _ = (μ t ^ u) ^ t := by rw [← pow_mul, ← pow_mul, mul_comm]
    _ ≤ _ := pow_le_pow_left₀ (pow_nonneg (h0 t) _) h2 _

end Finset

namespace MvPolynomial

variable {K σ κ : Type*} [Field K] [Finite σ] [Finite κ]

/-- The product of the first `s` values of `k ↦ μ (τ k)` on `Fin r`, as a product over
`range s`. -/
theorem prod_castLE_eq_prod_range {r s : ℕ} (hsr : s ≤ r) (m : Fin r → ℝ) :
    ∏ k : Fin s, m (Fin.castLE hsr k) =
      ∏ k ∈ range s, if h : k < r then m ⟨k, h⟩ else 1 := by
  rw [← Fin.prod_univ_eq_prod_range]
  refine prod_congr rfl fun k _ ↦ ?_
  have hk : (k : ℕ) < r := k.2.trans_le hsr
  simp only [hk, ↓reduceDIte]
  rfl

open scoped Classical in
/-- **Lemma 3.3** of Corvaja–Zannier 2004, at one absolute value `v` and uniformly in `P`. Let
`f₁ ⋯ f_r - g ∈ (G)`, `deg fᵢ ≤ δ`, `deg g ≤ e`, `s < r`, and suppose that for every set `J` of
`s + 1` indices each `X_x` has a power in `(X₀, G^h, f^h_J)` (no `s + 1` of the `f^h` have a common
zero at infinity on `G^h = 0`). Then there is `C` such that for every zero `P` of `G` and every
ordering `τ` with `|f_{τ 0}(P)|_v ≤ |f_{τ 1}(P)|_v ≤ ⋯`,
`|f_{τ 0}(P) ⋯ f_{τ (s-1)}(P)|_v ‖P‖_v ^ (δ (r - s)) ≤ C ‖P‖_v ^ e`. -/
theorem exists_prod_mul_pow_le_of_monotone (v : AbsoluteValue K ℝ) (G : κ → MvPolynomial σ K)
    {r s δ e : ℕ} {f : Fin r → MvPolynomial σ K} {g : MvPolynomial σ K}
    (hf : ∀ i, (f i).totalDegree ≤ δ) (hg : g.totalDegree ≤ e)
    (heq : ∏ i, f i - g ∈ Ideal.span (Set.range G)) (hsr : s < r)
    (hinf : ∀ J : Finset (Fin r), J.card = s + 1 → ∀ x, ∃ M, X (some x) ^ M ∈
      Ideal.span (insert (X none) (Set.range (fun l ↦ homogenization (G l)) ∪
        Set.range fun i : J ↦ homogenize δ (f i)))) :
    ∃ C, ∀ P : σ → K, (∀ l, eval P (G l) = 0) → ∀ τ : Equiv.Perm (Fin r),
      Monotone (fun k ↦ v (eval P (f (τ k)))) →
      (∏ k : Fin s, v (eval P (f (τ (Fin.castLE hsr.le k))))) *
          (⨆ o : Option σ, v (o.elim 1 P)) ^ (δ * (r - s)) ≤
        C * (⨆ o : Option σ, v (o.elim 1 P)) ^ e := by
  -- The local Nullstellensatz inequality for each set of `s + 1` indices, made uniform.
  have hJ : ∀ J : Finset (Fin r), ∃ c > 0, ∃ R, J.card = s + 1 → ∀ P : σ → K,
      (∀ l, eval P (G l) = 0) → R ≤ ⨆ o : Option σ, v (o.elim 1 P) →
      ∃ i ∈ J, c * (⨆ o : Option σ, v (o.elim 1 P)) ^ δ ≤ v (eval P (f i)) := by
    intro J
    by_cases hJ : J.card = s + 1
    · obtain ⟨c, hc, R, hR⟩ := exists_le_abv_eval_of_pow_mem v G (f := fun i : J ↦ f i)
        (fun i ↦ hf i) (hinf J hJ)
      refine ⟨c, hc, R, fun _ P hP hRP ↦ ?_⟩
      obtain ⟨i, hi⟩ := hR P hP hRP
      exact ⟨i, i.2, hi⟩
    · exact ⟨1, one_pos, 0, fun h ↦ absurd h hJ⟩
  choose c hc R hR using hJ
  obtain ⟨J₀, -, hJ₀⟩ := exists_min_image univ c univ_nonempty
  obtain ⟨J₁, -, hJ₁⟩ := exists_max_image univ R univ_nonempty
  set c₀ := c J₀
  set R₀ := max (R J₁) 1
  -- The constants: `Γ` bounds the values of the `f i` and of `g`.
  set Γf : ℝ := ∑ i, ∑ m ∈ (f i).support, v ((f i).coeff m) with hΓf
  have hΓf : ∀ i, ∑ m ∈ (f i).support, v ((f i).coeff m) ≤ Γf := fun i ↦
    single_le_sum (f := fun i ↦ ∑ m ∈ (f i).support, v ((f i).coeff m))
      (fun i _ ↦ sum_nonneg fun _ _ ↦ apply_nonneg _ _) (mem_univ i)
  have hΓf0 : 0 ≤ Γf := sum_nonneg fun i _ ↦ sum_nonneg fun _ _ ↦ apply_nonneg _ _
  set Γg : ℝ := ∑ m ∈ g.support, v (g.coeff m) with hΓg
  have hΓg0 : 0 ≤ Γg := sum_nonneg fun _ _ ↦ apply_nonneg _ _
  refine ⟨Γg / c₀ ^ (r - s) + (Γf * R₀ ^ δ) ^ s * R₀ ^ (δ * (r - s)),
    fun P hP τ hτ ↦ ?_⟩
  set n := ⨆ o : Option σ, v (o.elim 1 P) with hn
  have hn1 : 1 ≤ n := one_le_iSup_abv_optionElim v P
  have hn0 : 0 < n := zero_lt_one.trans_le hn1
  set m : Fin r → ℝ := fun k ↦ v (eval P (f (τ k))) with hm
  set μ : ℕ → ℝ := fun k ↦ if h : k < r then m ⟨k, h⟩ else 1 with hμ
  have hU : ∏ k : Fin s, v (eval P (f (τ (Fin.castLE hsr.le k)))) = ∏ k ∈ range s, μ k :=
    prod_castLE_eq_prod_range hsr.le m
  have hμ0 : ∀ k, 0 ≤ μ k := fun k ↦ by
    simp only [μ]
    split_ifs
    exacts [apply_nonneg _ _, zero_le_one]
  have hU0 : 0 ≤ ∏ k ∈ range s, μ k := prod_nonneg fun k _ ↦ hμ0 k
  have hC1 : 0 ≤ Γg / c₀ ^ (r - s) := div_nonneg hΓg0 (pow_nonneg (hc J₀).le _)
  have hC2 : 0 ≤ (Γf * R₀ ^ δ) ^ s * R₀ ^ (δ * (r - s)) := by positivity
  rw [hU]
  by_cases hnR : R₀ ≤ n
  · -- `‖P‖_v` large: the `(s + 1)`-st smallest value is `≥ c ‖P‖_v ^ δ`.
    set J := univ.map ((Fin.castLEEmb (Nat.succ_le_of_lt hsr)).trans τ.toEmbedding) with hJdef
    have hJcard : J.card = s + 1 := by rw [card_map, card_univ, Fintype.card_fin]
    obtain ⟨i, hiJ, hi⟩ := hR J hJcard P hP ((hJ₁ J (mem_univ _)).trans
      ((le_max_left _ _).trans hnR))
    obtain ⟨k₀, -, rfl⟩ := mem_map.mp hiJ
    have hbig : ∀ k, s ≤ k → k < r → c₀ * n ^ δ ≤ μ k := by
      intro k hsk hkr
      simp only [μ, hkr, ↓reduceDIte]
      refine (mul_le_mul_of_nonneg_right (hJ₀ J (mem_univ _)) (pow_nonneg hn0.le _)).trans
        (hi.trans ?_)
      have hle : Fin.castLE (Nat.succ_le_of_lt hsr) k₀ ≤ ⟨k, hkr⟩ := by
        change (k₀ : ℕ) ≤ k
        have := k₀.2
        omega
      exact hτ hle
    have hall : ∏ k ∈ range r, μ k = v (eval P g) := by
      have hgP : eval P (∏ i, f i) = eval P g := by
        have := (Ideal.span_le.mpr (by rintro _ ⟨l, rfl⟩; exact hP l) :
          Ideal.span (Set.range G) ≤ RingHom.ker (eval P)) heq
        rwa [RingHom.mem_ker, map_sub, sub_eq_zero] at this
      rw [← hgP, map_prod, map_prod, ← Fin.prod_univ_eq_prod_range]
      calc ∏ k : Fin r, μ k = ∏ k : Fin r, v (eval P (f (τ k))) :=
            prod_congr rfl fun k _ ↦ by simp only [μ, k.2, ↓reduceDIte, Fin.eta, m]
        _ = ∏ i, v (eval P (f i)) := Equiv.prod_comp τ fun i ↦ v (eval P (f i))
    have hlow : (c₀ * n ^ δ) ^ (r - s) ≤ ∏ k ∈ Ico s r, μ k := by
      calc (c₀ * n ^ δ) ^ (r - s) = ∏ _k ∈ Ico s r, c₀ * n ^ δ := by
            rw [prod_const, Nat.card_Ico]
        _ ≤ _ := prod_le_prod₀ (fun _ _ ↦ mul_nonneg (hc J₀).le (pow_nonneg hn0.le _))
            fun k hk ↦
            hbig k (mem_Ico.mp hk).1 (mem_Ico.mp hk).2
    have hgle : v (eval P g) ≤ Γg * n ^ e := abv_eval_le v P g hg
    have key : (∏ k ∈ range s, μ k) * (c₀ ^ (r - s) * n ^ (δ * (r - s))) ≤ Γg * n ^ e := by
      calc (∏ k ∈ range s, μ k) * (c₀ ^ (r - s) * n ^ (δ * (r - s)))
          = (∏ k ∈ range s, μ k) * (c₀ * n ^ δ) ^ (r - s) := by rw [mul_pow, pow_mul]
        _ ≤ (∏ k ∈ range s, μ k) * ∏ k ∈ Ico s r, μ k := mul_le_mul_of_nonneg_left hlow hU0
        _ = v (eval P g) := by rw [prod_range_mul_prod_Ico μ hsr.le, hall]
        _ ≤ Γg * n ^ e := hgle
    have hc0 : 0 < c₀ ^ (r - s) := pow_pos (hc J₀) _
    have : (∏ k ∈ range s, μ k) * n ^ (δ * (r - s)) ≤ Γg / c₀ ^ (r - s) * n ^ e := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
      linarith
    exact this.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC2)
      (pow_nonneg hn0.le _))
  · -- `‖P‖_v` small: everything is bounded.
    push Not at hnR
    have hR₀ : 1 ≤ R₀ := le_max_right _ _
    have hmle : ∀ k ∈ range s, μ k ≤ Γf * R₀ ^ δ := by
      intro k hk
      have hkr : k < r := (mem_range.mp hk).trans hsr
      simp only [μ, hkr, ↓reduceDIte, m]
      refine (abv_eval_le v P _ (hf _)).trans ?_
      exact mul_le_mul (hΓf _) (pow_le_pow_left₀ hn0.le hnR.le _) (pow_nonneg hn0.le _) hΓf0
    have h1 : ∏ k ∈ range s, μ k ≤ (Γf * R₀ ^ δ) ^ s := by
      calc ∏ k ∈ range s, μ k ≤ ∏ _k ∈ range s, Γf * R₀ ^ δ := prod_le_prod₀ (fun k _ ↦ hμ0 k) hmle
        _ = _ := by rw [prod_const, card_range]
    have h2 : n ^ (δ * (r - s)) ≤ R₀ ^ (δ * (r - s)) := pow_le_pow_left₀ hn0.le hnR.le _
    have h3 : 1 ≤ n ^ e := one_le_pow₀ hn1
    calc (∏ k ∈ range s, μ k) * n ^ (δ * (r - s))
        ≤ (Γf * R₀ ^ δ) ^ s * R₀ ^ (δ * (r - s)) := mul_le_mul h1 h2 (pow_nonneg hn0.le _)
          (by positivity)
      _ ≤ (Γf * R₀ ^ δ) ^ s * R₀ ^ (δ * (r - s)) * n ^ e := le_mul_of_one_le_right hC2 h3
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC1) (pow_nonneg hn0.le _)

end MvPolynomial

namespace NumberField

open Height IsDedekindDomain MvPolynomial

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
/-- **Proposition 3.1** of Corvaja–Zannier 2004 (Theorem 2 for equal degrees), with the
conclusion in algebraic form (Finding 2 of the README). Let `G₁, …, G_b ∈ K[X_x | x ∈ σ]`,
`|σ| = b + t`, `t > 0`, with `(G)` prime and `(G^h, X₀)` of height `b + 1`, and let
`f₁ ⋯ f_r - g ∈ (G)` with `deg fᵢ ≤ δ`, `δ > 0`, `deg g ≤ e`. Suppose that
* any `t` of the `f^h = homogenize δ f` together with the `G^h` generate an ideal of height
  `b + t`;
* for any `s + 1` of the `f`, `t ≤ s`, each `X_x` has a power in `(X₀, G^h, f^h_J)`;
* `r > s (t + 1)/t + e/δ`.

Then one `q ∉ (G)` vanishes at every `S`-integral zero of `G`. -/
theorem exists_eval_eq_zero_of_prod_sub_mem {σ : Type*} [Fintype σ] {b t r s δ e : ℕ}
    (S : Finset (HeightOneSpectrum (𝓞 K))) {G : Fin b → MvPolynomial σ K}
    (hG : (Ideal.span (Set.range G)).IsPrime) (hδ : 0 < δ) (ht : 0 < t)
    (hcard : Fintype.card σ = b + t)
    (hXh : (Ideal.span (insert (X none) (Set.range fun l ↦ homogenization (G l)))).height =
      b + 1)
    {f : Fin r → MvPolynomial σ K} {g : MvPolynomial σ K}
    (hf : ∀ i, (f i).totalDegree ≤ δ) (hg : g.totalDegree ≤ e)
    (heq : ∏ i, f i - g ∈ Ideal.span (Set.range G))
    (hht : ∀ j : Fin t ↪ Fin r, (Ideal.span (Set.range (Fin.append
      (fun l ↦ homogenization (G l)) fun k ↦ homogenize δ (f (j k))))).height = (b + t : ℕ))
    (hts : t ≤ s)
    (hinf : ∀ J : Finset (Fin r), J.card = s + 1 → ∀ x, ∃ M, X (some x) ^ M ∈
      Ideal.span (insert (X none) (Set.range (fun l ↦ homogenization (G l)) ∪
        Set.range fun i : J ↦ homogenize δ (f i))))
    (hr : s * (t + 1) * δ + t * e < t * (r * δ)) :
    ∃ q ∉ Ideal.span (Set.range G), ∀ P : σ → K,
      (∀ x, P x ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) →
      (∀ l, eval P (G l) = 0) → eval P q = 0 := by
  have hsr : s < r := by
    by_contra h
    push Not at h
    have : t * (r * δ) ≤ s * (t + 1) * δ :=
      calc t * (r * δ) ≤ t * (s * δ) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h)
        _ ≤ s * (t + 1) * δ := by
          rw [show s * (t + 1) * δ = t * (s * δ) + s * δ by ring]
          omega
    omega
  have htr : t ≤ r := hts.trans hsr.le
  have hs0 : 0 < s := ht.trans_le hts
  -- Lemma 3.3 at each place.
  have h33 := fun p : InfinitePlace K ⊕ S ↦
    exists_prod_mul_pow_le_of_monotone (systemPlace S p) G hf hg heq hsr hinf
  choose C3 hC3 using h33
  -- The exponent and the constant.
  set η : ℝ := (((t * (r * δ) : ℕ) : ℝ) - ((s * (t + 1) * δ + t * e : ℕ) : ℝ)) / (s * δ)
    with hηdef
  have hη : 0 < η := by
    have : ((s * (t + 1) * δ + t * e : ℕ) : ℝ) < (t * (r * δ) : ℕ) := Nat.cast_lt.mpr hr
    exact div_pos (sub_pos.mpr this) (by positivity)
  set Cs : ℝ := ∏ p, max (C3 p) 0 ^ systemMult S p with hCs
  have hCs0 : 0 ≤ Cs := prod_nonneg fun p _ ↦ pow_nonneg (le_max_right _ _) _
  set C₀ : ℝ := (Cs ^ t) ^ ((s : ℝ)⁻¹) with hC₀
  -- The classes: one ordering of the `f` per place, and the `t` first `f` in it.
  set pick : InfinitePlace K ⊕ S → InfinitePlace K ⊕ S := fun p ↦
    (⟨p, rfl⟩ : ∃ p', systemPlace S p' = systemPlace S p).choose with hpickdef
  have hpick : ∀ p, systemPlace S (pick p) = systemPlace S p := fun p ↦
    (⟨p, rfl⟩ : ∃ p', systemPlace S p' = systemPlace S p).choose_spec
  set γ : (InfinitePlace K ⊕ S → Equiv.Perm (Fin r)) → AbsoluteValue K ℝ → Fin t →
      MvPolynomial σ K := fun c v j ↦
    if h : ∃ p, systemPlace S p = v then f (c h.choose (Fin.castLE htr j)) else 0 with hγdef
  have hγ : ∀ c p, γ c (systemPlace S p) = fun j ↦ f (c (pick p) (Fin.castLE htr j)) := by
    intro c p
    have h : ∃ p', systemPlace S p' = systemPlace S p := ⟨p, rfl⟩
    funext j
    simp only [γ, h, ↓reduceDIte, pick]
  -- The engine, once per class.
  have heng : ∀ c : InfinitePlace K ⊕ S → Equiv.Perm (Fin r), ∃ q ∉ Ideal.span (Set.range G),
      ∀ P : σ → K, (∀ x, P x ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) →
        (∀ l, eval P (G l) = 0) →
        ∏ p, (∏ j, systemPlace S p (eval P (γ c (systemPlace S p) j))) ^ systemMult S p ≤
          C₀ * mulHeightAff P ^ (-((1 + η) * δ)) →
        eval P q = 0 := fun c ↦
    exists_eval_eq_zero_of_prod_le S hG hδ ht hcard hXh (γ c)
      (fun p j ↦ by rw [hγ]; exact hf _)
      (fun p ↦ by rw [hγ]; exact hht ((Fin.castLEEmb htr).trans (c (pick p)).toEmbedding))
      hη C₀
  choose q hqG hq using heng
  refine ⟨∏ c, q c, fun h ↦ ?_, fun P hPS hP ↦ ?_⟩
  · have := hG
    obtain ⟨c, -, hc⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hqG c hc
  -- The class of `P`.
  set τ : InfinitePlace K ⊕ S → Equiv.Perm (Fin r) := fun p ↦
    Tuple.sort fun i ↦ systemPlace S p (eval P (f i)) with hτdef
  have hτ : ∀ p, Monotone fun k ↦ systemPlace S p (eval P (f (τ p k))) := fun p ↦
    Tuple.monotone_sort fun i ↦ systemPlace S p (eval P (f i))
  rw [map_prod]
  refine prod_eq_zero (mem_univ τ) (hq τ P hPS hP ?_)
  -- The local factors.
  set nP : InfinitePlace K ⊕ S → ℝ := fun p ↦ ⨆ o : Option σ, systemPlace S p (o.elim 1 P)
    with hnP
  have hnP1 : ∀ p, 1 ≤ nP p := fun p ↦ one_le_iSup_abv_optionElim _ P
  set T : InfinitePlace K ⊕ S → ℝ := fun p ↦
    ∏ j : Fin t, systemPlace S p (eval P (f (τ p (Fin.castLE htr j)))) with hTdef
  set U : InfinitePlace K ⊕ S → ℝ := fun p ↦
    ∏ k : Fin s, systemPlace S p (eval P (f (τ p (Fin.castLE hsr.le k)))) with hUdef
  have hT0 : ∀ p, 0 ≤ T p := fun p ↦ prod_nonneg fun _ _ ↦ apply_nonneg _ _
  have hU0 : ∀ p, 0 ≤ U p := fun p ↦ prod_nonneg fun _ _ ↦ apply_nonneg _ _
  have hLHS : ∏ p, (∏ j, systemPlace S p (eval P (γ τ (systemPlace S p) j))) ^ systemMult S p =
      ∏ p, T p ^ systemMult S p := by
    refine prod_congr rfl fun p _ ↦ ?_
    rw [hγ]
    simp only [T, τ, hpick]
  rw [hLHS]
  -- (3.3) at each place.
  have hTU : ∀ p, T p ^ s ≤ U p ^ t := by
    intro p
    simp only [T, U]
    rw [prod_castLE_eq_prod_range htr (fun k ↦ systemPlace S p (eval P (f (τ p k)))),
      prod_castLE_eq_prod_range hsr.le (fun k ↦ systemPlace S p (eval P (f (τ p k))))]
    refine prod_range_pow_le_prod_range_pow (fun k ↦ ?_) hts fun j k hjk hks ↦ ?_
    · split_ifs
      exacts [apply_nonneg _ _, zero_le_one]
    · have hkr : k < r := hks.trans hsr
      have hjr : j < r := hjk.trans_lt hkr
      simp only [hjr, hkr, ↓reduceDIte]
      exact hτ p (show (⟨j, hjr⟩ : Fin r) ≤ ⟨k, hkr⟩ from hjk)
  -- The product over the places.
  have hH := mulHeightAff_eq_prod_systemPlace S hPS
  set H := mulHeightAff P with hHdef
  have hH0 : 0 < H := zero_lt_one.trans_le (one_le_mulHeightAff P)
  set Γ := ∏ p, T p ^ systemMult S p with hΓdef
  set Uall := ∏ p, U p ^ systemMult S p with hUalldef
  have hΓ0 : 0 ≤ Γ := prod_nonneg fun p _ ↦ pow_nonneg (hT0 p) _
  have hUall0 : 0 ≤ Uall := prod_nonneg fun p _ ↦ pow_nonneg (hU0 p) _
  have h1 : Γ ^ s ≤ Uall ^ t := by
    rw [← prod_pow, ← prod_pow]
    refine prod_le_prod₀ (fun p _ ↦ pow_nonneg (pow_nonneg (hT0 p) _) _) fun p _ ↦ ?_
    calc (T p ^ systemMult S p) ^ s = (T p ^ s) ^ systemMult S p := by
          rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ (U p ^ t) ^ systemMult S p := pow_le_pow_left₀ (pow_nonneg (hT0 p) _) (hTU p) _
      _ = (U p ^ systemMult S p) ^ t := by rw [← pow_mul, ← pow_mul, mul_comm]
  have h2 : Uall * H ^ (δ * (r - s)) ≤ Cs * H ^ e := by
    rw [hH, ← prod_pow, ← prod_pow, hCs, ← prod_mul_distrib, ← prod_mul_distrib]
    refine prod_le_prod₀ (fun p _ ↦ mul_nonneg (pow_nonneg (hU0 p) _)
      (pow_nonneg (pow_nonneg (zero_le_one.trans (hnP1 p)) _) _)) fun p _ ↦ ?_
    have hloc : U p * nP p ^ (δ * (r - s)) ≤ max (C3 p) 0 * nP p ^ e :=
      (hC3 p P hP (τ p) (hτ p)).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (pow_nonneg (zero_le_one.trans (hnP1 p)) _))
    calc U p ^ systemMult S p * (nP p ^ systemMult S p) ^ (δ * (r - s))
        = (U p * nP p ^ (δ * (r - s))) ^ systemMult S p := by ring
      _ ≤ (max (C3 p) 0 * nP p ^ e) ^ systemMult S p :=
          pow_le_pow_left₀ (mul_nonneg (hU0 p) (pow_nonneg (zero_le_one.trans (hnP1 p)) _))
            hloc _
      _ = max (C3 p) 0 ^ systemMult S p * (nP p ^ systemMult S p) ^ e := by ring
  set x : ℝ := (e : ℝ) - ((δ * (r - s) : ℕ) : ℝ) with hx
  have h3 : Γ ^ s ≤ Cs ^ t * H ^ (x * t) := by
    have hUle : Uall ≤ Cs * H ^ x := by
      rw [hx, Real.rpow_sub hH0, Real.rpow_natCast, Real.rpow_natCast, ← mul_div_assoc,
        le_div_iff₀ (pow_pos hH0 _)]
      exact h2
    calc Γ ^ s ≤ Uall ^ t := h1
      _ ≤ (Cs * H ^ x) ^ t := pow_le_pow_left₀ hUall0 hUle t
      _ = Cs ^ t * H ^ (x * t) := by rw [mul_pow, Real.rpow_mul_natCast hH0.le]
  calc Γ = (Γ ^ s) ^ ((s : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hΓ0 hs0.ne').symm
    _ ≤ (Cs ^ t * H ^ (x * t)) ^ ((s : ℝ)⁻¹) :=
        Real.rpow_le_rpow (pow_nonneg hΓ0 _) h3 (by positivity)
    _ = C₀ * H ^ (x * t * (s : ℝ)⁻¹) := by
        rw [Real.mul_rpow (pow_nonneg hCs0 _) (Real.rpow_nonneg hH0.le _),
          ← Real.rpow_mul hH0.le]
    _ = C₀ * H ^ (-((1 + η) * δ)) := by
        congr 2
        rw [hx, hηdef]
        push_cast [Nat.cast_sub hsr.le]
        field_simp
        ring

end NumberField
