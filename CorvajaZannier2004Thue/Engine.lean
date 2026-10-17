/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.Affine
public import DiophantineApproximation.SubspaceSystem
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.RingTheory.DedekindDomain.SInteger
public import Mathlib.RingTheory.Ideal.Height
public import STForMathlib.RingTheory.MvPolynomial.DehomogenizeIdeal

-- Used only inside proofs.
import DiophantineApproximation.SAdicHeight
import DiophantineApproximation.SubspaceAffine
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import STForMathlib.Data.Nat.Choose.SimplexCount
import STForMathlib.RingTheory.MvPolynomial.EvalBound
import STForMathlib.RingTheory.MvPolynomial.PowerFiltration

/-!
# The engine of Corvaja–Zannier's method

P. Corvaja and U. Zannier, *On a general Thue's equation*, Amer. J. Math. 126 (2004), §3: the
proof of Proposition 3.1, with the equation's only contribution, the inequality that Lemma 3.3
derives from it, taken as a hypothesis (Finding 9 of the README).

Let `G₁, …, G_b ∈ K[X_s | s ∈ σ]` with `|σ| = b + t`, `t ≥ 1`, and `(G^h, X₀)` of height `b + 1`.
At each place `v` of `S∞ ∪ S` let `γ_v` be `t` polynomials of degree `≤ δ` with `(G^h, γ_v^h)` of
height `b + t` (so `γ_v = 0` cuts `Z = {G = 0}` in finitely many points, none at infinity). For
`η > 0` and any constant `C₀` the `S`-integral points `P` of `Z` with

```text
∏_{v ∈ S∞ ∪ S} ∏_j |γ_{jv}(P)|_v ≤ C₀ H(P) ^ (-(1 + η) δ)
```

(Mathlib's normalization, the infinite places with their multiplicity, `H` the affine height)
lie on finitely many hypersurfaces `q = 0`, `q ∉ (G)`
(`NumberField.exists_finset_eval_eq_zero_of_prod_le`), and on one if `(G)` is prime
(`NumberField.exists_eval_eq_zero_of_prod_le`). Since `∏_v ‖P‖_v = H(P)` for an `S`-integral `P`,
the hypothesis is the paper's `∑_v ∑_j log (|γ_{jv}(P)|_v / ‖P‖_v^δ) ≤ -(t + 1 + η) δ h(P) + O(1)`.

## Main results

* `Finset.prod_mul_pow_le_of_le`: the local estimate behind (3.2), with the label sums `A_j`
  replaced by a common lower bound `A` (Finding 4).
* `NumberField.exists_finset_eval_eq_zero_of_prod_le`: the engine.
* `NumberField.exists_eval_eq_zero_of_prod_le`: the same with one `q`, for `(G)` prime.

## Implementation notes

⚠ **One application of DA 6.4, over `K` itself.** The point is `Q(P) = (P^{m_i})_i`, the monomials
of a basis of `V_N^*` evaluated at `P` (`MvPolynomial.exists_monomial_basis`), one of them `1`.
So `Q(P)` is `S`-primitive and `H(Q(P)) ≤ H(P)^N` with no constant; the forms at `v` are the
coordinates, in that basis, of the basis adapted to `γ_v` (CZ.2), so `L_{v,x}(Q(P)) = ψ_{v,x}(P)`
on `Z`. The absolute values of `F = K` are those of `K`.

⚠ **The adapted bases differ from place to place, their number does not**: each has
`d = dim V_N^*` members and is reindexed by `Fin d` (`MvPolynomial.exists_adapted_basis_fin`).

⚠ **`N` is chosen once** (`Finset.exists_forall_choose_mul_add_mul_choose_lt_zero`, CZ.3), large
enough also for `⌊(N - N₀)/δ⌋ ≥ 1`, which with `t ≥ 1` gives `d ≥ 2`: the points of small height
(finitely many, by Northcott) then each lie on a proper line, as in Evertse's Theorem A
(`NumberField.exists_finset_submodule_of_systemWeight_neg`). A proper subspace gives a nonzero
functional `λ`, and `q = ∑ λ_i X^{m_i} ∉ (G)` because the `X^{m_i}` are independent modulo `(G)`.

⚠ **`D = E δ^t > 0` is not assumed.** If `(G) = (1)` there is no point; otherwise `d ≥ 1` and
`d ≤ D C(⌊N/δ⌋ + t, t)`.

⚠ **A constant `C₀` in the hypothesis costs nothing**: it multiplies the constant of (3.2) by
`max C₀ 0 ^ A`, and the points of small height are handled by Northcott anyway. Lemma 3.3 gives
the inequality only up to such a constant (`CorvajaZannier2004Thue/EqualDegrees.lean`).
-/

@[expose] public section

open Finset

namespace Finset

/-- **The local estimate behind (3.2)** of Corvaja–Zannier 2004. If `a x ≤ c x · g^{ℓ x} ·
n^{N - δ σ(ℓ x)}` for every member `x` of a family labelled by exponents `ℓ x` with
`δ σ(ℓ x) ≤ N`, `g j ≤ Γ j · n^δ`, and every label sum `A_j = ∑_x ℓ x j` is at least `A`, then
`∏ a · n^{t δ A} ≤ ∏ c · ∏ Γ^{A_j - A} · (∏ g)^A · n^{d N}`, `d` the number of members. The
exponents `A_j` are replaced by their common lower bound `A` at the cost of a constant, because
`g j / n^δ` is bounded. -/
theorem prod_mul_pow_le_of_le {ι : Type*} [Fintype ι] {t δ N A : ℕ} (ℓ : ι → Fin t → ℕ)
    (hℓ : ∀ x, δ * ∑ j, ℓ x j ≤ N) (hA : ∀ j, A ≤ ∑ x, ℓ x j) {n : ℝ} (hn : 1 ≤ n)
    {a c : ι → ℝ} {g Γ : Fin t → ℝ} (ha0 : ∀ x, 0 ≤ a x) (hc0 : ∀ x, 0 ≤ c x)
    (hg0 : ∀ j, 0 ≤ g j)
    (ha : ∀ x, a x ≤ c x * (∏ j, g j ^ ℓ x j) * n ^ (N - δ * ∑ j, ℓ x j))
    (hg : ∀ j, g j ≤ Γ j * n ^ δ) :
    (∏ x, a x) * n ^ (t * δ * A) ≤
      (∏ x, c x) * (∏ j, Γ j ^ (∑ x, ℓ x j - A)) * (∏ j, g j) ^ A *
        n ^ (Fintype.card ι * N) := by
  have hn0 : 0 ≤ n := zero_le_one.trans hn
  -- The exponents of `n`.
  have hexp : (∑ x, (N - δ * ∑ j, ℓ x j)) + δ * ∑ j, (∑ x, ℓ x j - A) + t * δ * A =
      Fintype.card ι * N := by
    have h1 : δ * ∑ j, (∑ x, ℓ x j - A) + t * δ * A = ∑ x, δ * ∑ j, ℓ x j := by
      have : ∑ j, (∑ x, ℓ x j - A) + t * A = ∑ j, ∑ x, ℓ x j := by
        rw [show t * A = ∑ _j : Fin t, A by simp, ← sum_add_distrib]
        exact sum_congr rfl fun j _ ↦ Nat.sub_add_cancel (hA j)
      rw [← mul_sum, sum_comm, ← this]
      ring
    rw [add_assoc, h1, ← sum_add_distrib, sum_congr rfl fun x _ ↦ Nat.sub_add_cancel (hℓ x),
      sum_const, card_univ, smul_eq_mul]
  -- Step 1: the product of the bounds.
  have h1 : ∏ x, a x ≤ (∏ x, c x) * (∏ j, g j ^ ∑ x, ℓ x j) *
      n ^ (∑ x, (N - δ * ∑ j, ℓ x j)) := by
    calc ∏ x, a x ≤ ∏ x, (c x * (∏ j, g j ^ ℓ x j) * n ^ (N - δ * ∑ j, ℓ x j)) :=
          prod_le_prod₀ (fun x _ ↦ ha0 x) fun x _ ↦ ha x
      _ = _ := by
          rw [prod_mul_distrib, prod_mul_distrib, prod_comm, prod_pow_eq_pow_sum]
          simp only [prod_pow_eq_pow_sum]
  -- Step 2: `g j ^ A_j ≤ g j ^ A · Γ j ^ (A_j - A) · n ^ (δ (A_j - A))`.
  have h2 : ∏ j, g j ^ ∑ x, ℓ x j ≤
      (∏ j, Γ j ^ (∑ x, ℓ x j - A)) * (∏ j, g j) ^ A * n ^ (δ * ∑ j, (∑ x, ℓ x j - A)) := by
    calc ∏ j, g j ^ ∑ x, ℓ x j
        = ∏ j, (g j ^ A * g j ^ (∑ x, ℓ x j - A)) :=
          prod_congr rfl fun j _ ↦ by rw [← pow_add, Nat.add_sub_cancel' (hA j)]
      _ ≤ ∏ j, (g j ^ A * (Γ j ^ (∑ x, ℓ x j - A) * n ^ (δ * (∑ x, ℓ x j - A)))) := by
          refine prod_le_prod₀ (fun j _ ↦ mul_nonneg (pow_nonneg (hg0 j) _)
            (pow_nonneg (hg0 j) _)) fun j _ ↦ ?_
          gcongr
          · exact pow_nonneg (hg0 j) _
          rw [pow_mul, ← mul_pow]
          exact pow_le_pow_left₀ (hg0 j) (hg j) _
      _ = _ := by
          rw [prod_mul_distrib, prod_mul_distrib, prod_pow, mul_sum]
          simp only [prod_pow_eq_pow_sum]
          ring
  calc (∏ x, a x) * n ^ (t * δ * A)
      ≤ ((∏ x, c x) * (∏ j, g j ^ ∑ x, ℓ x j) * n ^ (∑ x, (N - δ * ∑ j, ℓ x j))) *
          n ^ (t * δ * A) := by gcongr
    _ ≤ ((∏ x, c x) * ((∏ j, Γ j ^ (∑ x, ℓ x j - A)) * (∏ j, g j) ^ A *
          n ^ (δ * ∑ j, (∑ x, ℓ x j - A))) * n ^ (∑ x, (N - δ * ∑ j, ℓ x j))) *
          n ^ (t * δ * A) := by
        gcongr
        · exact prod_nonneg fun x _ ↦ hc0 x
    _ = (∏ x, c x) * (∏ j, Γ j ^ (∑ x, ℓ x j - A)) * (∏ j, g j) ^ A *
          n ^ ((∑ x, (N - δ * ∑ j, ℓ x j)) + δ * ∑ j, (∑ x, ℓ x j - A) + t * δ * A) := by
        rw [pow_add, pow_add]; ring
    _ = _ := by rw [hexp]

end Finset

namespace NumberField

open Height IsDedekindDomain Module MvPolynomial

variable {K : Type*} [Field K] [NumberField K]

/-- A product over the places of a system, with multiplicities, is the product over the infinite
places with multiplicities times the product over `S`. -/
theorem prod_systemPlace_pow (S : Finset (HeightOneSpectrum (𝓞 K)))
    (f : AbsoluteValue K ℝ → ℝ) :
    ∏ p, f (systemPlace S p) ^ systemMult S p =
      (∏ v : InfinitePlace K, f v.1 ^ v.mult) * ∏ v ∈ S, f (FinitePlace.mk v).1 := by
  rw [Fintype.prod_sum_type, ← Finset.prod_coe_sort S]
  congr 1
  exact Finset.prod_congr rfl fun v _ ↦ pow_one _

/-- **The height of an `S`-primitive tuple over the places of a system.** -/
theorem mulHeight_eq_prod_systemPlace {ι : Type*} [Finite ι] (S : Finset (HeightOneSpectrum (𝓞 K)))
    {x : ι → K} (hx : (S : Set (HeightOneSpectrum (𝓞 K))).IsPrimitive x) :
    mulHeight x = ∏ p, (⨆ i, systemPlace S p (x i)) ^ systemMult S p := by
  rw [mulHeight_eq_prod_of_isPrimitive S hx]
  exact (prod_systemPlace_pow S fun v ↦ ⨆ i, v (x i)).symm

/-- **The affine height of an `S`-integral point over the places of a system**:
`H(P) = ∏_v ‖P‖_v`, `‖P‖_v = max (1, |P_s|_v)`. -/
theorem mulHeightAff_eq_prod_systemPlace {σ : Type*} [Finite σ]
    (S : Finset (HeightOneSpectrum (𝓞 K))) {P : σ → K}
    (hP : ∀ s, P s ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) :
    mulHeightAff P = ∏ p, (⨆ o : Option σ, systemPlace S p (o.elim 1 P)) ^ systemMult S p := by
  have := Fintype.ofFinite σ
  exact mulHeight_eq_prod_systemPlace S <| (Set.isPrimitive_iff _ _).mpr
    ⟨fun o ↦ by cases o; exacts [one_mem _, hP _], fun o ↦ if o = none then 1 else 0,
      fun o ↦ by dsimp only; split_ifs; exacts [one_mem _, zero_mem _], by simp⟩

open scoped Classical in
/-- **The engine** (Corvaja–Zannier 2004, the proof of Prop. 3.1 with (1.1) replaced by the
inequality it is used for). Let `G₁, …, G_b ∈ K[X_s | s ∈ σ]`, `|σ| = b + t`, `t > 0`, with
`(G^h, X₀)` of height `b + 1`, and at each place `v` of `S∞ ∪ S` a tuple `γ_v` of `t` polynomials
of degree `≤ δ` with `(G^h, γ_v^h)` of height `b + t`. For `η > 0` and any `C₀`, there are
finitely many `q ∉ (G)` such that every `S`-integral zero `P` of `G` with
`∏_v ∏_j |γ_{jv}(P)|_v ≤ C₀ H(P)^{-(1 + η) δ}` (the affine height, the infinite places counted
with their multiplicity) is a zero of one of them. -/
theorem exists_finset_eval_eq_zero_of_prod_le {σ : Type*} [Fintype σ] {b t δ : ℕ}
    (S : Finset (HeightOneSpectrum (𝓞 K))) {G : Fin b → MvPolynomial σ K} (hδ : 0 < δ)
    (ht : 0 < t) (hcard : Fintype.card σ = b + t)
    (hXh : (Ideal.span (insert (X none) (Set.range fun l ↦ homogenization (G l)))).height =
      b + 1)
    (γ : AbsoluteValue K ℝ → Fin t → MvPolynomial σ K)
    (hγ : ∀ p j, (γ (systemPlace S p) j).totalDegree ≤ δ)
    (hht : ∀ p, (Ideal.span (Set.range (Fin.append (fun l ↦ homogenization (G l))
      fun j ↦ homogenize δ (γ (systemPlace S p) j)))).height = (b + t : ℕ))
    {η : ℝ} (hη : 0 < η) (C₀ : ℝ) :
    ∃ T : Finset (MvPolynomial σ K), (∀ q ∈ T, q ∉ Ideal.span (Set.range G)) ∧
      ∀ P : σ → K, (∀ s, P s ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) →
        (∀ l, eval P (G l) = 0) →
        ∏ p, (∏ j, systemPlace S p (eval P (γ (systemPlace S p) j))) ^ systemMult S p ≤
          C₀ * mulHeightAff P ^ (-((1 + η) * δ)) →
        ∃ q ∈ T, eval P q = 0 := by
  set I := Ideal.span (Set.range G) with hI
  have hevalI : ∀ P : σ → K, (∀ l, eval P (G l) = 0) → ∀ q ∈ I, eval P q = 0 := by
    intro P hP q hq
    have : I ≤ RingHom.ker (eval P) := Ideal.span_le.mpr (by rintro _ ⟨l, rfl⟩; exact hP l)
    exact this hq
  by_cases h1 : (1 : MvPolynomial σ K) ∈ I
  · exact ⟨∅, by simp, fun P _ hP _ ↦ absurd (hevalI P hP 1 h1) (by simp)⟩
  -- The constants of Lemma 3.2 and the choice of `N` (CZ.3).
  set D := (∏ l, (G l).totalDegree) * δ ^ t with hDdef
  set N₀ := t * (δ - 1) + ∑ l, ((G l).totalDegree - 1) with hN₀def
  set θ : ℝ := -(δ * (t + 1) + η * δ) with hθdef
  have hθ : θ < -(δ * (t + 1) : ℝ) := by
    have : (0 : ℝ) < η * δ := by positivity
    linarith
  obtain ⟨N₁, hN₁⟩ := Finset.exists_forall_choose_mul_add_mul_choose_lt_zero (N₀ := N₀) hδ hθ
  set N := max N₁ (N₀ + δ) with hNdef
  have hNN₀ : N₀ + δ ≤ N := le_max_right _ _
  set M' := (N - N₀) / δ with hM'def
  have hM' : 1 ≤ M' := (Nat.le_div_iff_mul_le hδ).mpr (by omega)
  have hN0 : 0 < N := by omega
  set d := finrank K (quotDegLE I N) with hd
  -- The adapted bases, one for each place (CZ.2).
  set good : AbsoluteValue K ℝ → Prop := fun v ↦ (∀ j, (γ v j).totalDegree ≤ δ) ∧
    (Ideal.span (Set.range (Fin.append (fun l ↦ homogenization (G l))
      fun j ↦ homogenize δ (γ v j)))).height = (b + t : ℕ) with hgood
  have hgoodp : ∀ p, good (systemPlace S p) := fun p ↦ ⟨hγ p, hht p⟩
  have hab : ∀ v, ∃ (ℓ : Fin d → Fin t → ℕ) (q : Fin d → MvPolynomial σ K), good v →
      (∀ x, δ * ∑ j, ℓ x j ≤ N) ∧ (∀ x, (q x).totalDegree ≤ N - δ * ∑ j, ℓ x j) ∧
      LinearIndependent K (fun x ↦ Ideal.Quotient.mk I ((∏ j, γ v j ^ ℓ x j) * q x)) ∧
      Submodule.span K (Set.range fun x ↦ Ideal.Quotient.mk I ((∏ j, γ v j ^ ℓ x j) * q x)) =
        quotDegLE I N ∧
      (∀ i, (univ.filter (ℓ · = i)).card ≤ D) ∧
      ∀ i, δ * ∑ j, i j + N₀ ≤ N → (univ.filter (ℓ · = i)).card = D := by
    intro v
    by_cases hv : good v
    · obtain ⟨ℓ, q, h⟩ := exists_adapted_basis_fin (N := N) hδ hv.1 hcard hv.2 hXh
      exact ⟨ℓ, q, fun _ ↦ h⟩
    · exact ⟨fun _ _ ↦ 0, fun _ ↦ 0, fun h ↦ absurd h hv⟩
  choose ℓ q hℓq using hab
  -- The monomial basis.
  obtain ⟨m, hmdeg, hmli, hmspan, i₀, hi₀⟩ := exists_monomial_basis h1 N
  -- `D > 0` and `d ≥ 2`.
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace K))
  obtain ⟨hℓ₀, -, -, -, hle₀, heq₀⟩ := hℓq w₀.1 (hgoodp (.inl w₀))
  have hdle : d ≤ D * (N / δ + t).choose t := by
    simpa using Finset.card_le_mul_choose hδ hℓ₀ hle₀
  have hdge : D * (M' + t).choose t ≤ d := by
    simpa using Finset.mul_choose_le_card hδ (by omega : N₀ ≤ N) hℓ₀ heq₀
  have hD : 0 < D := by
    rcases Nat.eq_zero_or_pos D with h | h
    · rw [h, zero_mul] at hdle
      exact absurd (Fin.pos i₀) (by omega)
    · exact h
  have hd2 : 2 ≤ d := by
    have : (1 + t).choose t ≤ (M' + t).choose t := Nat.choose_le_choose t (by omega)
    rw [show 1 + t = t + 1 by omega, Nat.choose_succ_self_right] at this
    nlinarith
  have : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr hd2
  -- The coordinates of the adapted bases in the monomial basis.
  set φ : Fin d → MvPolynomial σ K ⧸ I := fun i ↦ Ideal.Quotient.mk I (monomial (m i) 1)
    with hφ
  set ψ : AbsoluteValue K ℝ → Fin d → MvPolynomial σ K := fun v x ↦
    (∏ j, γ v j ^ ℓ v x j) * q v x with hψ
  have hcoef : ∀ v x, ∃ c : Fin d → K, good v →
      ∑ i, c i • φ i = Ideal.Quotient.mk I (ψ v x) := by
    intro v x
    by_cases hv : good v
    · have hmem : Ideal.Quotient.mk I (ψ v x) ∈ Submodule.span K (Set.range φ) := by
        rw [hmspan, ← (hℓq v hv).2.2.2.1]
        exact Submodule.subset_span ⟨x, rfl⟩
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hmem
      exact ⟨c, fun _ ↦ hc⟩
    · exact ⟨0, fun h ↦ absurd h hv⟩
  choose c hc using hcoef
  -- The linear forms.
  set L : AbsoluteValue K ℝ → Fin d → Dual K (Fin d → K) := fun v x ↦
    ∑ i, c v x i • LinearMap.proj i with hLdef
  have hL : ∀ v x y, L v x y = ∑ i, c v x i * y i := by
    intro v x y
    simp [L]
  have hLli : ∀ v, good v → LinearIndependent K (L v) := by
    intro v hv
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hi : ∀ i, ∑ x, g x * c v x i = 0 := by
      intro i
      have := congrArg (fun f : Dual K (Fin d → K) ↦ f (Pi.single i 1)) hg
      simpa [hL, Pi.single_apply] using this
    refine Fintype.linearIndependent_iff.mp (hℓq v hv).2.2.1 g ?_
    calc ∑ x, g x • Ideal.Quotient.mk I ((∏ j, γ v j ^ ℓ v x j) * q v x)
        = ∑ x, g x • ∑ i, c v x i • φ i := sum_congr rfl fun x _ ↦ by rw [hc v x hv]
      _ = ∑ i, (∑ x, g x * c v x i) • φ i := by
          simp only [smul_sum, smul_smul, sum_smul]
          exact sum_comm
      _ = 0 := by simp [hi]
  -- The point `Q(P)`, the monomials of the basis evaluated at `P`.
  set Q : (σ → K) → Fin d → K := fun P i ↦ eval P (monomial (m i) 1) with hQdef
  have hLQ : ∀ v, good v → ∀ P : σ → K, (∀ l, eval P (G l) = 0) → ∀ x,
      L v x (Q P) = eval P (ψ v x) := by
    intro v hv P hP x
    have hmk : Ideal.Quotient.mk I (∑ i, c v x i • monomial (m i) (1 : K)) =
        Ideal.Quotient.mk I (ψ v x) := by
      rw [← hc v x hv]
      change Ideal.Quotient.mkₐ K I _ = _
      rw [map_sum]
      simp only [map_smul]
      rfl
    have := hevalI P hP _ (Ideal.Quotient.eq.mp hmk)
    rw [map_sub, sub_eq_zero] at this
    rw [hL, ← this, map_sum]
    simp [Q, smul_eval]
  have hQS : ∀ P : σ → K, (∀ s, P s ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) →
      ∀ i, Q P i ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K := by
    intro P hP i
    simp only [Q, eval_monomial, one_mul, Finsupp.prod]
    exact prod_mem fun s _ ↦ pow_mem (hP s) _
  have hQ1 : ∀ P, Q P i₀ = 1 := by
    intro P
    simp [Q, hi₀]
  have hQ0 : ∀ P, Q P ≠ 0 := fun P h ↦ one_ne_zero ((hQ1 P).symm.trans (congrFun h i₀))
  have hQprim : ∀ P : σ → K, (∀ s, P s ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) →
      (S : Set (HeightOneSpectrum (𝓞 K))).IsPrimitive (Q P) := fun P hP ↦
    (Set.isPrimitive_iff _ _).mpr ⟨hQS P hP, fun i ↦ if i = i₀ then 1 else 0,
      fun i ↦ by dsimp only; split_ifs; exacts [one_mem _, zero_mem _], by simp [hQ1 P]⟩
  -- The local factors `‖P‖_v` of the affine height.
  set nP : (σ → K) → InfinitePlace K ⊕ S → ℝ := fun P p ↦
    ⨆ o : Option σ, systemPlace S p (o.elim 1 P) with hnP
  have hnP1 : ∀ P p, 1 ≤ nP P p := fun P p ↦ one_le_iSup_abv_optionElim _ P
  have hH : ∀ P : σ → K, (∀ s, P s ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) →
      mulHeightAff P = ∏ p, nP P p ^ systemMult S p := fun P hP ↦
    mulHeightAff_eq_prod_systemPlace S hP
  have hHQ : ∀ P : σ → K, (∀ s, P s ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) →
      mulHeight (Q P) ≤ mulHeightAff P ^ N := by
    intro P hP
    rw [mulHeight_eq_prod_systemPlace S (hQprim P hP), hH P hP, ← prod_pow]
    refine prod_le_prod₀ (fun p _ ↦ pow_nonneg (Real.iSup_nonneg fun i ↦ apply_nonneg _ _) _)
      fun p _ ↦ ?_
    rw [← pow_mul, mul_comm, pow_mul]
    refine pow_le_pow_left₀ (Real.iSup_nonneg fun i ↦ apply_nonneg _ _) ?_ _
    exact ciSup_le fun i ↦ abv_eval_monomial_le _ P (m i) (hmdeg i)
  -- The local estimate at each place.
  set A : ℕ := D * (M' + t).choose (t + 1) with hAdef
  set cst : AbsoluteValue K ℝ → ℝ := fun v ↦
    (∏ x, ∑ e ∈ (q v x).support, v ((q v x).coeff e)) *
      ∏ j, (∑ e ∈ (γ v j).support, v ((γ v j).coeff e)) ^ (∑ x, ℓ v x j - A) with hcst
  have hcst0 : ∀ v, 0 ≤ cst v := fun v ↦
    mul_nonneg (prod_nonneg fun x _ ↦ sum_nonneg fun e _ ↦ apply_nonneg _ _)
      (prod_nonneg fun j _ ↦ pow_nonneg (sum_nonneg fun e _ ↦ apply_nonneg _ _) _)
  have hloc : ∀ p, ∀ P : σ → K,
      (∏ x, systemPlace S p (eval P (ψ (systemPlace S p) x))) * nP P p ^ (t * δ * A) ≤
        cst (systemPlace S p) *
          (∏ j, systemPlace S p (eval P (γ (systemPlace S p) j))) ^ A * nP P p ^ (d * N) := by
    intro p P
    set v := systemPlace S p
    obtain ⟨hℓv, hqv, -, -, -, heqv⟩ := hℓq v (hgoodp p)
    have hA : ∀ j, A ≤ ∑ x, ℓ v x j := fun j ↦ Finset.mul_choose_le_sum_apply hδ hℓv heqv j
    have := Finset.prod_mul_pow_le_of_le (ℓ v) hℓv hA (one_le_iSup_abv_optionElim v P)
      (a := fun x ↦ v (eval P (ψ v x)))
      (c := fun x ↦ ∑ e ∈ (q v x).support, v ((q v x).coeff e))
      (g := fun j ↦ v (eval P (γ v j)))
      (Γ := fun j ↦ ∑ e ∈ (γ v j).support, v ((γ v j).coeff e))
      (fun x ↦ apply_nonneg _ _) (fun x ↦ sum_nonneg fun e _ ↦ apply_nonneg _ _)
      (fun j ↦ apply_nonneg _ _) (fun x ↦ ?_) (fun j ↦ abv_eval_le v P (γ v j) (hγ p j))
    · rw [Fintype.card_fin] at this
      exact this
    · simp only [ψ, map_mul, map_prod, map_pow]
      calc (∏ j, v (eval P (γ v j)) ^ ℓ v x j) * v (eval P (q v x))
          ≤ (∏ j, v (eval P (γ v j)) ^ ℓ v x j) *
            ((∑ e ∈ (q v x).support, v ((q v x).coeff e)) *
              (⨆ o : Option σ, v (o.elim 1 P)) ^ (N - δ * ∑ j, ℓ v x j)) :=
            mul_le_mul_of_nonneg_left (abv_eval_le v P (q v x) (hqv x))
              (prod_nonneg fun j _ ↦ pow_nonneg (apply_nonneg _ _) _)
        _ = _ := by ring
  -- The global estimate: the affine product of `Q(P)` against the height of `P`.
  set w : AbsoluteValue K ℝ → AbsoluteValue K ℝ := fun w ↦ w with hw
  have haff : ∀ P : σ → K, (∀ l, eval P (G l) = 0) → affineProd S w L (Q P) =
      ∏ p, (∏ x, systemPlace S p (eval P (ψ (systemPlace S p) x))) ^ systemMult S p := by
    intro P hP
    rw [affineProd_eq_prod_systemValue]
    refine prod_congr rfl fun p _ ↦ ?_
    rw [← prod_pow]
    refine prod_congr rfl fun x _ ↦ ?_
    simp only [systemValue, systemAbs, w, Algebra.algebraMap_self, RingHom.id_apply]
    rw [hLQ _ (hgoodp p) P hP x]
  set Cg : ℝ := ∏ p, cst (systemPlace S p) ^ systemMult S p with hCg
  have hCg0 : 0 ≤ Cg := prod_nonneg fun p _ ↦ pow_nonneg (hcst0 _) _
  have hglob : ∀ P : σ → K, (∀ s, P s ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) →
      (∀ l, eval P (G l) = 0) →
      affineProd S w L (Q P) * mulHeightAff P ^ (t * δ * A) ≤
        Cg * (∏ p, (∏ j, systemPlace S p (eval P (γ (systemPlace S p) j))) ^
          systemMult S p) ^ A * mulHeightAff P ^ (d * N) := by
    intro P hPS hP
    rw [haff P hP, hH P hPS, ← prod_pow _ (t * δ * A), ← prod_pow _ A, ← prod_pow _ (d * N),
      hCg, ← prod_mul_distrib, ← prod_mul_distrib, ← prod_mul_distrib]
    refine prod_le_prod₀ (fun p _ ↦ mul_nonneg (pow_nonneg (prod_nonneg fun x _ ↦
      apply_nonneg _ _) _) (pow_nonneg (pow_nonneg (zero_le_one.trans (hnP1 P p)) _) _))
      fun p _ ↦ ?_
    have h := pow_le_pow_left₀ (mul_nonneg (prod_nonneg fun x _ ↦ apply_nonneg _ _)
      (pow_nonneg (zero_le_one.trans (hnP1 P p)) _)) (hloc p P) (systemMult S p)
    calc _ = ((∏ x, systemPlace S p (eval P (ψ (systemPlace S p) x))) *
          nP P p ^ (t * δ * A)) ^ systemMult S p := by ring
      _ ≤ _ := h
      _ = _ := by ring
  -- The exponent.
  set P₀ : ℕ := (N / δ + t).choose t with hP₀
  set Q₀ : ℕ := (M' + t).choose (t + 1) with hQ₀
  have hneg : (P₀ : ℝ) * N + θ * Q₀ < 0 := hN₁ N (le_max_left _ _)
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  set κ : ℝ := -(D * ((P₀ : ℝ) * N + θ * Q₀)) with hκdef
  have hκ : 0 < κ := neg_pos.mpr (mul_neg_of_pos_of_neg hD' hneg)
  have hexp : ((d * N : ℕ) : ℝ) - (t * δ * A : ℕ) - (1 + η) * δ * A ≤ -κ := by
    have hdN : ((d * N : ℕ) : ℝ) ≤ D * P₀ * N := by
      push_cast
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdle) (Nat.cast_nonneg _)
    have hA' : (A : ℝ) = D * Q₀ := by simp [A, Q₀]
    have : ((t * δ * A : ℕ) : ℝ) + (1 + η) * δ * A = -θ * (D * Q₀) := by
      push_cast
      rw [hA', hθdef]
      ring
    rw [hκdef]
    nlinarith
  have hbound : ∀ P : σ → K, (∀ s, P s ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) →
      (∀ l, eval P (G l) = 0) →
      ∏ p, (∏ j, systemPlace S p (eval P (γ (systemPlace S p) j))) ^ systemMult S p ≤
        C₀ * mulHeightAff P ^ (-((1 + η) * δ)) →
      affineProd S w L (Q P) ≤ Cg * max C₀ 0 ^ A * mulHeightAff P ^ (-κ) := by
    intro P hPS hP hprod
    set H := mulHeightAff P with hHdef
    have hH1 : 1 ≤ H := one_le_mulHeightAff P
    have hH0 : 0 < H := zero_lt_one.trans_le hH1
    set Γp := ∏ p, (∏ j, systemPlace S p (eval P (γ (systemPlace S p) j))) ^ systemMult S p
    have hΓp0 : 0 ≤ Γp := prod_nonneg fun p _ ↦ pow_nonneg (prod_nonneg fun j _ ↦
      apply_nonneg _ _) _
    have hΓA : Γp ^ A ≤ max C₀ 0 ^ A * H ^ (-((1 + η) * δ) * A) := by
      rw [Real.rpow_mul hH0.le, Real.rpow_natCast, ← mul_pow]
      refine pow_le_pow_left₀ hΓp0 (hprod.trans ?_) A
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hH0.le _)
    have h := hglob P hPS hP
    have hpos : 0 < H ^ (t * δ * A) := pow_pos hH0 _
    have key : affineProd S w L (Q P) * H ^ (t * δ * A) ≤
        Cg * max C₀ 0 ^ A * H ^ (((d * N : ℕ) : ℝ) - (1 + η) * δ * A) := by
      calc affineProd S w L (Q P) * H ^ (t * δ * A) ≤ Cg * Γp ^ A * H ^ (d * N) := h
        _ ≤ Cg * (max C₀ 0 ^ A * H ^ (-((1 + η) * δ) * A)) * H ^ (d * N) := by gcongr
        _ = Cg * max C₀ 0 ^ A * H ^ (((d * N : ℕ) : ℝ) - (1 + η) * δ * A) := by
          rw [mul_assoc, mul_assoc, ← Real.rpow_natCast H (d * N), ← Real.rpow_add hH0,
            ← mul_assoc]
          congr 2
          ring
    have key2 : affineProd S w L (Q P) ≤
        Cg * max C₀ 0 ^ A * H ^ (((d * N : ℕ) : ℝ) - (t * δ * A : ℕ) - (1 + η) * δ * A) := by
      rw [show ((d * N : ℕ) : ℝ) - (t * δ * A : ℕ) - (1 + η) * δ * A =
          (((d * N : ℕ) : ℝ) - (1 + η) * δ * A) - (t * δ * A : ℕ) by ring,
        Real.rpow_sub hH0, Real.rpow_natCast, ← mul_div_assoc, le_div_iff₀ hpos]
      exact key
    exact key2.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hH1 hexp)
      (mul_nonneg hCg0 (pow_nonneg (le_max_right _ _) _)))
  -- The Subspace Theorem (DA 6.4).
  set ε : ℝ := κ / (2 * N) with hεdef
  have hε : 0 < ε := div_pos hκ (by positivity)
  obtain ⟨T₁, hT₁, hcov⟩ := exists_finset_submodule_of_integer_of_affineProd_le (K := K)
    (F := K) (ι := Fin d) S w (fun _ ↦ ⟨AbsoluteValue.ext fun _ ↦ rfl⟩)
    (fun _ _ ↦ ⟨AbsoluteValue.ext fun _ ↦ rfl⟩) L (fun v ↦ hLli _ (hgoodp (.inl v)))
    (fun v hv ↦ hLli _ (hgoodp (.inr ⟨v, hv⟩))) hε
  -- The points of small height (Northcott), each on a line.
  set Cg' : ℝ := Cg * max C₀ 0 ^ A with hCg'
  have hCg'0 : 0 ≤ Cg' := mul_nonneg hCg0 (pow_nonneg (le_max_right _ _) _)
  set B : ℝ := max 1 (Cg' ^ (2 / κ)) with hB
  have hfin : {P : σ → K | ∀ s, mulHeight₁ (P s) ≤ B}.Finite :=
    (Set.Finite.pi (t := fun _ : σ ↦ {a : K | mulHeight₁ a ≤ B})
      fun _ ↦ NumberField.finite_setOfPred_mulHeight₁_le K B).subset fun P hP s _ ↦ hP s
  set T₂ := T₁ ∪ hfin.toFinset.image fun P ↦ K ∙ Q P with hT₂def
  have hT₂ : ∀ W ∈ T₂, W ≠ ⊤ := by
    intro W hW
    rcases mem_union.1 hW with hW | hW
    · exact hT₁ W hW
    obtain ⟨P, -, rfl⟩ := mem_image.1 hW
    intro htop
    have h1 : finrank K (K ∙ Q P) ≤ 1 := (finrank_span_singleton (hQ0 P)).le
    rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h1
    omega
  -- A nonzero functional vanishing on each proper subspace, and its polynomial.
  have hfun : ∀ W : Submodule K (Fin d → K), ∃ f : Dual K (Fin d → K), W ≠ ⊤ →
      f ≠ 0 ∧ W.map f = ⊥ := by
    intro W
    by_cases hW : W = ⊤
    · exact ⟨0, fun h ↦ absurd hW h⟩
    · obtain ⟨f, hf, hf'⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
        (lt_top_iff_ne_top.mpr hW) inferInstance
      exact ⟨f, fun _ ↦ ⟨hf, hf'⟩⟩
  choose f hf using hfun
  set qW : Submodule K (Fin d → K) → MvPolynomial σ K := fun W ↦
    ∑ i, f W (fun j ↦ if i = j then 1 else 0) • monomial (m i) 1 with hqWdef
  have hqW_eval : ∀ W P, eval P (qW W) = f W (Q P) := by
    intro W P
    rw [LinearMap.pi_apply_eq_sum_univ (f W) (Q P)]
    simp [qW, smul_eval, mul_comm, Q]
  have hqW : ∀ W, W ≠ ⊤ → qW W ∉ I := by
    intro W hW hmem
    have h0 : ∑ i, f W (fun j ↦ if i = j then 1 else 0) • φ i = 0 := by
      have : Ideal.Quotient.mk I (qW W) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      rw [← this]
      change _ = Ideal.Quotient.mkₐ K I _
      rw [map_sum]
      simp only [map_smul]
      rfl
    have hall := Fintype.linearIndependent_iff.mp hmli _ h0
    refine (hf W hW).1 (LinearMap.ext fun y ↦ ?_)
    rw [LinearMap.pi_apply_eq_sum_univ]
    simp [hall]
  refine ⟨T₂.image qW, fun q hq ↦ ?_, fun P hPS hP hprod ↦ ?_⟩
  · obtain ⟨W, hW, rfl⟩ := mem_image.mp hq
    exact hqW W (hT₂ W hW)
  have hW : ∃ W ∈ T₂, Q P ∈ W := by
    by_cases hsmall : mulHeightAff P ≤ B
    · exact ⟨K ∙ Q P, mem_union_right _ (mem_image.mpr ⟨P, hfin.mem_toFinset.mpr fun s ↦
        (mulHeight₁_le_mulHeightAff P s).trans hsmall, rfl⟩),
        Submodule.mem_span_singleton_self _⟩
    push Not at hsmall
    set H := mulHeightAff P with hHdef
    have hH0 : 0 < H := zero_lt_one.trans_le (one_le_mulHeightAff P)
    have hCle : Cg' ≤ H ^ (κ / 2) :=
      calc Cg' = (Cg' ^ (2 / κ)) ^ (κ / 2) := by
            rw [← Real.rpow_mul hCg'0, div_mul_div_comm, mul_comm 2 κ, div_self (by positivity),
              Real.rpow_one]
        _ ≤ H ^ (κ / 2) := Real.rpow_le_rpow (Real.rpow_nonneg hCg'0 _)
            ((le_max_right _ _).trans hsmall.le) (by positivity)
    obtain ⟨W, hW, hQW⟩ := hcov (Q P) (hQ0 P) (hQS P hPS) <|
      calc affineProd S w L (Q P) ≤ Cg' * H ^ (-κ) := hbound P hPS hP hprod
        _ ≤ H ^ (κ / 2) * H ^ (-κ) :=
            mul_le_mul_of_nonneg_right hCle (Real.rpow_nonneg hH0.le _)
        _ = (H ^ N) ^ (-ε) := by
            rw [← Real.rpow_add hH0, ← Real.rpow_natCast, ← Real.rpow_mul hH0.le, hεdef]
            congr 1
            field_simp
            ring
        _ ≤ mulHeight (Q P) ^ (-ε) :=
            Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le (one_le_mulHeight _))
              (hHQ P hPS) (by linarith)
    exact ⟨W, mem_union_left _ hW, hQW⟩
  obtain ⟨W, hW, hQW⟩ := hW
  refine ⟨qW W, mem_image_of_mem _ hW, ?_⟩
  have hmap : f W (Q P) ∈ W.map (f W) := Submodule.mem_map_of_mem hQW
  rw [(hf W (hT₂ W hW)).2, Submodule.mem_bot] at hmap
  exact (hqW_eval W P).trans hmap

open scoped Classical in
/-- **The engine for prime `(G)`**: one `q ∉ (G)` vanishes at every `S`-integral zero `P` of `G`
with `∏_v ∏_j |γ_{jv}(P)|_v ≤ C₀ H(P)^{-(1 + η) δ}` (Corvaja–Zannier 2004, Finding 2 of the
README). -/
theorem exists_eval_eq_zero_of_prod_le {σ : Type*} [Fintype σ] {b t δ : ℕ}
    (S : Finset (HeightOneSpectrum (𝓞 K))) {G : Fin b → MvPolynomial σ K}
    (hG : (Ideal.span (Set.range G)).IsPrime) (hδ : 0 < δ)
    (ht : 0 < t) (hcard : Fintype.card σ = b + t)
    (hXh : (Ideal.span (insert (X none) (Set.range fun l ↦ homogenization (G l)))).height =
      b + 1)
    (γ : AbsoluteValue K ℝ → Fin t → MvPolynomial σ K)
    (hγ : ∀ p j, (γ (systemPlace S p) j).totalDegree ≤ δ)
    (hht : ∀ p, (Ideal.span (Set.range (Fin.append (fun l ↦ homogenization (G l))
      fun j ↦ homogenize δ (γ (systemPlace S p) j)))).height = (b + t : ℕ))
    {η : ℝ} (hη : 0 < η) (C₀ : ℝ) :
    ∃ q ∉ Ideal.span (Set.range G),
      ∀ P : σ → K, (∀ s, P s ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K) →
        (∀ l, eval P (G l) = 0) →
        ∏ p, (∏ j, systemPlace S p (eval P (γ (systemPlace S p) j))) ^ systemMult S p ≤
          C₀ * mulHeightAff P ^ (-((1 + η) * δ)) →
        eval P q = 0 := by
  obtain ⟨T, hT, hP⟩ := exists_finset_eval_eq_zero_of_prod_le S hδ ht hcard hXh γ hγ hht hη C₀
  refine ⟨T.prod fun q ↦ q, fun h ↦ ?_, fun P hPS hPG hprod ↦ ?_⟩
  · obtain ⟨q, hq, hqI⟩ := (hG.prod_mem_iff_exists_mem T).mp h
    exact hT q hq hqI
  · obtain ⟨q, hq, hq0⟩ := hP P hPS hPG hprod
    rw [map_prod]
    exact Finset.prod_eq_zero hq hq0

end NumberField
