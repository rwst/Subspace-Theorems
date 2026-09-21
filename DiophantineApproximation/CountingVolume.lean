/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Counting and volume

Three elementary estimates, all needed with explicit constants, behind the auxiliary polynomial
of Roth's theorem and of the Subspace Theorem. Write `𝒱_m(t)` for the part of the unit cube below
a hyperplane, `{x ∈ [0,1]^m | ∑ j, x j ≤ t}`, and `V_m(t)` for its volume.

*Lattice points.* For `d : Fin m → ℕ` with every `d j` positive, the number of `i : Fin m → ℕ`
with `i j ≤ d j` and `∑ j, i j / d j ≤ t` lies between `V_m(t) ∏ j, d j` and
`V_m(t) (1 + max 1 t⁻¹ ∑ j, 1 / d j) ^ m ∏ j, d j`. This is the count of linear conditions the
auxiliary polynomial of Bombieri–Gubler's Lemma 6.3.4 has to satisfy.

*The tail.* `V_m((1/2 - ε) m) ≤ exp (-6 m ε²)`.

*The multihomogeneous tail.* For a fixed coordinate of each of `m` blocks of `n + 1` variables,
the proportion of exponent tuples whose weighted sum is below `m / (n + 1) - m η` is at most
`exp (-(n+1)(n+2) η² m / 4)`.

All three rest on one **exponential-moment estimate**,
`MeasureTheory.setIntegral_prod_le_exp_mul_pow`: for a nonnegative weight `g` on the line,
`∫_{∑ x j ≤ s} ∏ j, g (x j) ≤ exp (λ s) (∫ exp (-λ x) g x) ^ m`. The two tails are that lemma at
two weights — the indicator of `[0, 1]`, and the density `n (1 - x) ^ (n - 1)` of one coordinate
of a point taken uniformly in the standard `n`-simplex — and each needs exactly one pointwise
inequality about `exp` to finish.

The file imports no number theory.

## Main results

* `MeasureTheory.cubeSimplex` and `MeasureTheory.cubeSimplexVolume`: the region and `V_m(t)`.
* `MeasureTheory.cubeSimplexVolume_mul_prod_le_card` and
  `MeasureTheory.card_latticePoints_le`: **the lattice-point comparison**, both directions.
* `MeasureTheory.setIntegral_prod_le_exp_mul_pow`: **the Chernoff bound**, the one lemma the two
  tails share.
* `MeasureTheory.cubeSimplexVolume_le_exp_neg`: **the tail**, `V_m((1/2-ε)m) ≤ exp (-6 m ε²)`.
* `MeasureTheory.setIntegral_prod_simplexCoordDensity_le_exp`: **the multihomogeneous tail**.
* `Real.sinh_le_mul_exp_sq_div_six` and `Real.exp_neg_le_one_sub_add_sq_div_two`: the two
  pointwise bounds on `exp` that the two tails turn on, and
  `Nat.six_pow_mul_factorial_le` for the first.
* `MeasureTheory.simplexCoordDensity` and `MeasureTheory.integral_simplexCoordDensity`: the
  density, and the fact that it is a probability density — which is what makes the third
  estimate a statement about a proportion.

## Implementation notes

⚠ **The two tails are the same lemma at two weights.** The milestone said "one exponential-moment
estimate each"; it is one estimate for both, and what separates them is a pointwise bound on
`exp` — `sinh u ≤ u exp (u²/6)` for the uniform weight, `exp (-u) ≤ 1 - u + u²/2` for the simplex
weight. The first is the termwise comparison `6 ^ k * k ! ≤ (2k+1)!`, sharp at `k = 1`, which is
where the `6` in `exp (-6 m ε²)` comes from.

⚠ **Every restriction the book puts on the parameters is an artefact of its proof.** Lemma 6.3.5
assumes `ε ≤ 1/2` and (7.24)–(7.25) assume `0 < λ ≤ n + 4` and `η ≤ 2/(n+1)`; none of the three is
needed. The first is vacuous — beyond `ε = 1/2` the region is empty — and the other two are the
price of the book's argument, which truncates the alternating series `∑ (-λ)^k / (n+k)!` after
three terms and so has to pair off the tail. The pointwise inequality
`exp (-u) ≤ 1 - u + u²/2` gives the same three terms for **every** `u ≥ 0`, and it follows in
three lines from Mathlib's `Real.quadratic_le_exp_of_nonneg` and the identity
`(1 + u + u²/2)(1 - u + u²/2) = 1 + u⁴/4`.

⚠ **The multihomogeneous tail is stated as a proportion, not as a volume.** The book's `V` is an
`m n`-dimensional volume, which it reduces in the very next display to an integral over `[0,1]^m`
against the density of one simplex coordinate; that reduction is the volume `r ^ k / k !` of a
simplex, which Mathlib does not have. Against the *normalised* density `n (1 - x)^(n-1)` the
factor `V₀ = (n !)^(-m)` cancels from both sides of the book's `V / V₀`, and what is left is
literally the proportion the milestone asks for.

⚠ **Only the upper lattice-point bound needs `t > 0`, and it needs it.** At `t = 0` the origin is
always an admissible lattice point while `V_m(0) = 0`, so the bound fails; the acceptance criteria
below record this. The lower bound holds at every `t`, with no hypothesis beyond `0 < d j`.

⚠ **Both lattice-point bounds are one covering argument.** Attach to each admissible `i` the
half-open box `∏ j, [i j / d j, (i j + 1) / d j)`. Rounding each coordinate of a point of `𝒱_m(t)`
down lands in such a box, which gives the lower bound with no disjointness needed; and the boxes,
which are disjoint, fit inside `(1 + ρ) 𝒱_m(t)` for `ρ = max 1 t⁻¹ ∑ j, 1/d j`, which gives the
upper bound from `Measure.addHaar_smul` alone.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
6.3.3 and the counting inside the proof of Lemma 6.3.4, Lemma 6.3.5, and (7.23)–(7.25).

This is Layer 2.5 of the `DiophantineApproximation` roadmap.
-/
@[expose] public section

noncomputable section

open Set
open scoped Pointwise ENNReal Nat

namespace Nat

/-- `6 ^ k * k ! ≤ (2 k + 1)!`: the termwise comparison between the series of `sinh` and the
series of `exp (u ^ 2 / 6)`. -/
theorem six_pow_mul_factorial_le (k : ℕ) : 6 ^ k * k ! ≤ (2 * k + 1)! := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e1 : 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 := by ring
    rw [e1, Nat.factorial_succ, Nat.factorial_succ, pow_succ, Nat.factorial_succ]
    calc 6 ^ k * 6 * ((k + 1) * k !)
        = 6 * (k + 1) * (6 ^ k * k !) := by ring
      _ ≤ (2 * k + 1 + 1 + 1) * (2 * k + 1 + 1) * (2 * k + 1)! :=
          Nat.mul_le_mul (by nlinarith) ih
      _ = (2 * k + 1 + 1 + 1) * ((2 * k + 1 + 1) * (2 * k + 1)!) := by ring

end Nat

namespace Real

/-- **`sinh u ≤ u exp (u ² / 6)`** for `u ≥ 0`. Comparing the two power series term by term,
this is `6 ^ k * k ! ≤ (2 k + 1)!`. -/
theorem sinh_le_mul_exp_sq_div_six {u : ℝ} (hu : 0 ≤ u) : sinh u ≤ u * exp (u ^ 2 / 6) := by
  have hexp : ∀ v : ℝ, HasSum (fun n : ℕ ↦ v ^ n / n !) (exp v) := fun v ↦ by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp v
  have hAB : HasSum (fun n : ℕ ↦ (u ^ n / (n ! : ℝ) - (-u) ^ n / (n ! : ℝ)) / 2) (sinh u) := by
    rw [Real.sinh_eq]; exact ((hexp u).sub (hexp (-u))).div_const 2
  have hinj : Function.Injective (fun k : ℕ ↦ 2 * k + 1) := fun a b h ↦ by
    dsimp only at h; omega
  have hzero : ∀ n ∉ Set.range (fun k : ℕ ↦ 2 * k + 1),
      (u ^ n / (n ! : ℝ) - (-u) ^ n / (n ! : ℝ)) / 2 = 0 := by
    intro n hn
    have hn' : Even n := by
      rcases Nat.even_or_odd n with h | h
      · exact h
      · obtain ⟨k, hk⟩ := h
        exact absurd (⟨k, by dsimp only; omega⟩ : n ∈ Set.range (fun k : ℕ ↦ 2 * k + 1)) hn
    rw [hn'.neg_pow]
    ring
  rw [← hinj.hasSum_iff hzero] at hAB
  have hodd : HasSum (fun k : ℕ ↦ u ^ (2 * k + 1) / ((2 * k + 1)! : ℝ)) (sinh u) := by
    refine hAB.congr_fun fun k ↦ ?_
    have : Odd (2 * k + 1) := ⟨k, by ring⟩
    simp only [Function.comp_apply, this.neg_pow]
    ring
  have hC : HasSum (fun k : ℕ ↦ u * ((u ^ 2 / 6) ^ k / (k ! : ℝ))) (u * exp (u ^ 2 / 6)) :=
    (hexp (u ^ 2 / 6)).mul_left u
  refine hasSum_le (fun k ↦ ?_) hodd hC
  have h1 : u * ((u ^ 2 / 6) ^ k / (k ! : ℝ)) = u ^ (2 * k + 1) / (6 ^ k * (k ! : ℝ)) := by
    rw [div_pow, ← pow_mul]
    field_simp
    ring
  have h2 : ((6 ^ k * k ! : ℕ) : ℝ) ≤ (((2 * k + 1)! : ℕ) : ℝ) := by
    exact_mod_cast Nat.six_pow_mul_factorial_le k
  push_cast at h2
  rw [h1]
  gcongr

/-- `exp (-u) ≤ 1 - u + u ² / 2` for `u ≥ 0`. From `Real.quadratic_le_exp_of_nonneg` and the
identity `(1 + u + u²/2) (1 - u + u²/2) = 1 + u⁴/4`. -/
theorem exp_neg_le_one_sub_add_sq_div_two {u : ℝ} (hu : 0 ≤ u) :
    exp (-u) ≤ 1 - u + u ^ 2 / 2 := by
  have hq : 1 + u + u ^ 2 / 2 ≤ exp u := quadratic_le_exp_of_nonneg hu
  have hpos : (0 : ℝ) < 1 - u + u ^ 2 / 2 := by nlinarith [sq_nonneg (u - 1)]
  have key : 1 ≤ exp u * (1 - u + u ^ 2 / 2) := by
    have h3 := mul_le_mul_of_nonneg_right hq hpos.le
    rw [show (1 + u + u ^ 2 / 2) * (1 - u + u ^ 2 / 2) = 1 + u ^ 4 / 4 by ring] at h3
    nlinarith [pow_nonneg hu 4]
  have he : (0 : ℝ) < exp u := exp_pos u
  have h2 : exp (-u) * exp u = 1 := by rw [← exp_add]; simp
  nlinarith [key, h2, he]

/-- **The exponential moment of the uniform distribution on `[0, 1]`**:
`(1 - exp (-λ)) / λ ≤ exp (-λ/2 + λ²/24)`. This is the whole analytic content of the tail
estimate; `λ = 12 ε` turns it into `exp (-6 m ε²)`. -/
theorem one_sub_exp_neg_div_le_exp {lam : ℝ} (hlam : 0 < lam) :
    (1 - exp (-lam)) / lam ≤ exp (-(lam / 2) + lam ^ 2 / 24) := by
  have h := sinh_le_mul_exp_sq_div_six (u := lam / 2) (by linarith)
  rw [Real.sinh_eq, show (lam / 2) ^ 2 / 6 = lam ^ 2 / 24 by ring] at h
  have h2 : exp (lam / 2) - exp (-(lam / 2)) ≤ lam * exp (lam ^ 2 / 24) := by linarith
  have h3 := mul_le_mul_of_nonneg_right h2 (exp_pos (-(lam / 2))).le
  have e1 : (exp (lam / 2) - exp (-(lam / 2))) * exp (-(lam / 2)) = 1 - exp (-lam) := by
    rw [sub_mul, ← exp_add, ← exp_add, show lam / 2 + -(lam / 2) = 0 by ring,
      show -(lam / 2) + -(lam / 2) = -lam by ring, exp_zero]
  have e2 : lam * exp (lam ^ 2 / 24) * exp (-(lam / 2))
      = lam * exp (-(lam / 2) + lam ^ 2 / 24) := by
    rw [mul_assoc, ← exp_add, add_comm]
  rw [e1, e2] at h3
  rwa [div_le_iff₀ hlam, mul_comm]

end Real

namespace MeasureTheory

/-! ### The region and its volume -/

variable {m : ℕ}

/-- The part of the unit cube below the hyperplane `∑ x j = t`, Bombieri–Gubler's `𝒱_m(t)`. -/
def cubeSimplex (m : ℕ) (t : ℝ) : Set (Fin m → ℝ) :=
  (univ.pi fun _ ↦ Icc (0 : ℝ) 1) ∩ {x | ∑ j, x j ≤ t}

/-- The volume `V_m(t)` of `MeasureTheory.cubeSimplex`. -/
def cubeSimplexVolume (m : ℕ) (t : ℝ) : ℝ := (volume (cubeSimplex m t)).toReal

theorem mem_cubeSimplex {t : ℝ} {x : Fin m → ℝ} :
    x ∈ cubeSimplex m t ↔ (∀ j, x j ∈ Icc (0 : ℝ) 1) ∧ ∑ j, x j ≤ t := by
  simp [cubeSimplex, Pi.le_def, forall_and]

theorem measurableSet_cubeSimplex (m : ℕ) (t : ℝ) : MeasurableSet (cubeSimplex m t) :=
  (MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc).inter
    (measurableSet_le (by fun_prop) measurable_const)

/-- The unit cube has volume one. -/
theorem volume_unitCube (m : ℕ) : volume (univ.pi fun _ : Fin m ↦ Icc (0 : ℝ) 1) = 1 := by
  rw [volume_pi_pi]
  simp

theorem cubeSimplex_subset_unitCube (m : ℕ) (t : ℝ) :
    cubeSimplex m t ⊆ univ.pi fun _ ↦ Icc (0 : ℝ) 1 := inter_subset_left

theorem volume_cubeSimplex_ne_top (m : ℕ) (t : ℝ) : volume (cubeSimplex m t) ≠ ⊤ :=
  ne_top_of_le_ne_top (by rw [volume_unitCube]; exact ENNReal.one_ne_top)
    (measure_mono (cubeSimplex_subset_unitCube m t))

theorem cubeSimplexVolume_nonneg (m : ℕ) (t : ℝ) : 0 ≤ cubeSimplexVolume m t :=
  ENNReal.toReal_nonneg

theorem cubeSimplexVolume_le_one (m : ℕ) (t : ℝ) : cubeSimplexVolume m t ≤ 1 := by
  rw [cubeSimplexVolume, ← ENNReal.toReal_one]
  exact ENNReal.toReal_mono ENNReal.one_ne_top
    ((measure_mono (cubeSimplex_subset_unitCube m t)).trans_eq (volume_unitCube m))

/-- **The region has positive volume as soon as `t` is positive**: it contains the cube of side
`min 1 (t / m)`, which is nondegenerate. This is what makes the hypothesis
`r * ∑ k, V_m (t k) < 1` of Layer 2.6 a genuine restriction on the number of points. -/
theorem cubeSimplexVolume_pos (m : ℕ) {t : ℝ} (ht : 0 < t) : 0 < cubeSimplexVolume m t := by
  set c : ℝ := min 1 (t / m) with hcdef
  have hc0 : 0 ≤ c := le_min zero_le_one (by positivity)
  have hsub : (univ.pi fun _ : Fin m ↦ Icc (0 : ℝ) c) ⊆ cubeSimplex m t := by
    intro x hx
    simp only [mem_univ_pi, mem_Icc] at hx
    refine mem_cubeSimplex.mpr ⟨fun j ↦ ⟨(hx j).1, (hx j).2.trans (min_le_left _ _)⟩, ?_⟩
    have hle : ∑ j, x j ≤ (m : ℝ) * c := by
      calc ∑ j, x j ≤ ∑ _j : Fin m, c := Finset.sum_le_sum fun j _ ↦ (hx j).2
        _ = (m : ℝ) * c := by simp
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [Finset.univ_eq_empty, Finset.sum_empty]
      exact ht.le
    · have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
      have : (m : ℝ) * c ≤ t := by
        have : c ≤ t / m := min_le_right _ _
        calc (m : ℝ) * c ≤ (m : ℝ) * (t / m) := by nlinarith
          _ = t := by field_simp
      linarith
  have hvol : volume (univ.pi fun _ : Fin m ↦ Icc (0 : ℝ) c) = ENNReal.ofReal c ^ m := by
    rw [volume_pi_pi]
    simp [Real.volume_Icc]
  have hne : (ENNReal.ofReal c) ^ m ≠ 0 := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · refine pow_ne_zero _ ?_
      have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, hcdef]
      exact lt_min zero_lt_one (by positivity)
  rw [cubeSimplexVolume, ENNReal.toReal_pos_iff]
  refine ⟨lt_of_lt_of_le (pos_iff_ne_zero.mpr ?_) (measure_mono hsub),
    lt_top_iff_ne_top.mpr (volume_cubeSimplex_ne_top m t)⟩
  rw [hvol]
  exact hne

/-- The region is star-shaped about the origin: `c • 𝒱_m(t) ⊆ 𝒱_m(ct)` for `0 ≤ c ≤ 1`. -/
theorem smul_cubeSimplex_subset {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (m : ℕ) (t : ℝ) :
    c • cubeSimplex m t ⊆ cubeSimplex m (c * t) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_cubeSimplex] at hx ⊢
  simp only [Pi.smul_apply, smul_eq_mul]
  refine ⟨fun j ↦ ⟨by nlinarith [(hx.1 j).1], by nlinarith [(hx.1 j).1, (hx.1 j).2]⟩, ?_⟩
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hx.2 hc0

/-- The volume of the region shrinks by at most `c ^ m` when `t` is shrunk by `c ≤ 1`. -/
theorem pow_mul_cubeSimplexVolume_le {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (m : ℕ) (t : ℝ) :
    c ^ m * cubeSimplexVolume m t ≤ cubeSimplexVolume m (c * t) := by
  have hsm : volume (c • cubeSimplex m t) = ENNReal.ofReal (c ^ m) * volume (cubeSimplex m t) := by
    rw [Measure.addHaar_smul]
    simp [abs_of_nonneg (pow_nonneg hc0 m)]
  have hle : volume (c • cubeSimplex m t) ≤ volume (cubeSimplex m (c * t)) :=
    measure_mono (smul_cubeSimplex_subset hc0 hc1 m t)
  rw [hsm] at hle
  have := ENNReal.toReal_mono (volume_cubeSimplex_ne_top m (c * t)) hle
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hc0 m)] at this

/-! ### Lattice points -/

/-- The lattice points `i` of the box `∏ j, [0, d j]` with `∑ j, i j / d j ≤ t`: the conditions
that Bombieri–Gubler's auxiliary polynomial has to satisfy. -/
def latticePoints (d : Fin m → ℕ) (t : ℝ) : Finset (Fin m → ℕ) :=
  {i ∈ Fintype.piFinset fun j ↦ Finset.range (d j + 1) | ∑ j, (i j : ℝ) / (d j : ℝ) ≤ t}

@[simp] theorem mem_latticePoints {d : Fin m → ℕ} {t : ℝ} {i : Fin m → ℕ} :
    i ∈ latticePoints d t ↔ (∀ j, i j ≤ d j) ∧ ∑ j, (i j : ℝ) / (d j : ℝ) ≤ t := by
  simp [latticePoints]

/-- The half-open box of side `1 / d j` attached to a lattice point. -/
def latticeBox (d : Fin m → ℕ) (i : Fin m → ℕ) : Set (Fin m → ℝ) :=
  univ.pi fun j ↦ Ico ((i j : ℝ) / (d j : ℝ)) (((i j : ℝ) + 1) / (d j : ℝ))

theorem mem_latticeBox_iff {d : Fin m → ℕ} (hd : ∀ j, 0 < d j) {i : Fin m → ℕ} {x : Fin m → ℝ} :
    x ∈ latticeBox d i ↔ ∀ j, (i j : ℝ) ≤ x j * d j ∧ x j * d j < (i j : ℝ) + 1 := by
  have hpos : ∀ j, (0 : ℝ) < d j := fun j ↦ by exact_mod_cast hd j
  simp only [latticeBox, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Ico,
    div_le_iff₀ (hpos _), lt_div_iff₀ (hpos _)]

/-- A point lies in at most one of the boxes: the box determines the lattice point. -/
theorem eq_of_mem_latticeBox {d : Fin m → ℕ} (hd : ∀ j, 0 < d j) {i i' : Fin m → ℕ}
    {x : Fin m → ℝ} (h : x ∈ latticeBox d i) (h' : x ∈ latticeBox d i') : i = i' := by
  rw [mem_latticeBox_iff hd] at h h'
  funext j
  have h1 : (i j : ℝ) < (i' j : ℝ) + 1 := lt_of_le_of_lt (h j).1 (h' j).2
  have h2 : (i' j : ℝ) < (i j : ℝ) + 1 := lt_of_le_of_lt (h' j).1 (h j).2
  have h1' : i j < i' j + 1 := by exact_mod_cast h1
  have h2' : i' j < i j + 1 := by exact_mod_cast h2
  omega

/-- The boxes attached to distinct lattice points are disjoint. -/
theorem pairwiseDisjoint_latticeBox {d : Fin m → ℕ} (hd : ∀ j, 0 < d j) (s : Set (Fin m → ℕ)) :
    s.PairwiseDisjoint (latticeBox d) := fun i _ i' _ hne ↦ by
  rw [Function.onFun, Set.disjoint_left]
  exact fun x hx hx' ↦ hne (eq_of_mem_latticeBox hd hx hx')

theorem volume_latticeBox {d : Fin m → ℕ} (hd : ∀ j, 0 < d j) (i : Fin m → ℕ) :
    volume (latticeBox d i) = ENNReal.ofReal (∏ j, (d j : ℝ))⁻¹ := by
  have hpos : ∀ j, (0 : ℝ) < d j := fun j ↦ by exact_mod_cast hd j
  rw [latticeBox, volume_pi_pi]
  have : ∀ j : Fin m, volume (Ico ((i j : ℝ) / (d j : ℝ)) (((i j : ℝ) + 1) / (d j : ℝ)))
      = ENNReal.ofReal ((d j : ℝ))⁻¹ := by
    intro j
    rw [Real.volume_Ico, div_sub_div_same, add_sub_cancel_left, one_div]
  rw [Finset.prod_congr rfl fun j _ ↦ this j, ← ENNReal.ofReal_prod_of_nonneg
    (fun j _ ↦ by positivity), ← Finset.prod_inv_distrib]

theorem measurableSet_latticeBox (d : Fin m → ℕ) (i : Fin m → ℕ) :
    MeasurableSet (latticeBox d i) :=
  MeasurableSet.univ_pi fun _ ↦ measurableSet_Ico

/-- Rounding each coordinate down lands in a box attached to an admissible lattice point: the
boxes cover the region. -/
theorem cubeSimplex_subset_iUnion_latticeBox {d : Fin m → ℕ} (hd : ∀ j, 0 < d j) (t : ℝ) :
    cubeSimplex m t ⊆ ⋃ i ∈ latticePoints d t, latticeBox d i := by
  have hpos : ∀ j, (0 : ℝ) < d j := fun j ↦ by exact_mod_cast hd j
  intro x hx
  rw [mem_cubeSimplex] at hx
  have hxnn : ∀ j, (0 : ℝ) ≤ x j * d j := fun j ↦ mul_nonneg (hx.1 j).1 (hpos j).le
  have hle : ∀ j, ((⌊x j * d j⌋₊ : ℕ) : ℝ) ≤ x j * d j := fun j ↦ Nat.floor_le (hxnn j)
  have hlt : ∀ j, x j * d j < ((⌊x j * d j⌋₊ : ℕ) : ℝ) + 1 := fun j ↦ Nat.lt_floor_add_one _
  have hdiv : ∀ j, ((⌊x j * d j⌋₊ : ℕ) : ℝ) / (d j : ℝ) ≤ x j := fun j ↦
    (div_le_iff₀ (hpos j)).2 (hle j)
  simp only [Set.mem_iUnion, exists_prop]
  refine ⟨fun j ↦ ⌊x j * d j⌋₊, ?_, (mem_latticeBox_iff hd).2 fun j ↦ ⟨hle j, hlt j⟩⟩
  · refine mem_latticePoints.2 ⟨fun j ↦ ?_, ?_⟩
    · have : x j * d j ≤ (d j : ℝ) := by nlinarith [(hx.1 j).2, hpos j]
      simpa using Nat.floor_mono this
    · exact le_trans (Finset.sum_le_sum fun j _ ↦ hdiv j) hx.2

/-- **Lattice points, the lower bound** (Bombieri–Gubler 6.3.4): at least `V_m(t) ∏ d j` lattice
points of the box `∏ j, [0, d j]` satisfy `∑ j, i j / d j ≤ t`. -/
theorem cubeSimplexVolume_mul_prod_le_card {d : Fin m → ℕ} (hd : ∀ j, 0 < d j) (t : ℝ) :
    cubeSimplexVolume m t * ∏ j, (d j : ℝ) ≤ ((latticePoints d t).card : ℝ) := by
  have hpos : ∀ j, (0 : ℝ) < d j := fun j ↦ by exact_mod_cast hd j
  have hprod : (0 : ℝ) < ∏ j, (d j : ℝ) := Finset.prod_pos fun j _ ↦ hpos j
  have key : volume (cubeSimplex m t)
      ≤ ((latticePoints d t).card : ℝ≥0∞) * ENNReal.ofReal (∏ j, (d j : ℝ))⁻¹ := by
    refine (measure_mono (cubeSimplex_subset_iUnion_latticeBox hd t)).trans ?_
    refine (measure_biUnion_finset_le _ _).trans ?_
    rw [Finset.sum_congr rfl fun i _ ↦ volume_latticeBox hd i, Finset.sum_const, nsmul_eq_mul]
  have key' := ENNReal.toReal_mono (by finiteness) key
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (by positivity)] at key'
  rw [← le_div_iff₀ hprod, div_eq_mul_inv]
  exact key'

/-- **Lattice points, the upper bound** (Bombieri–Gubler 6.3.4): at most
`V_m(t) (1 + max 1 t⁻¹ ∑ j, 1 / d j) ^ m ∏ d j` of them do. -/
theorem card_latticePoints_le {d : Fin m → ℕ} (hd : ∀ j, 0 < d j) {t : ℝ} (ht : 0 < t) :
    ((latticePoints d t).card : ℝ)
      ≤ cubeSimplexVolume m t * (1 + max 1 t⁻¹ * ∑ j, (d j : ℝ)⁻¹) ^ m * ∏ j, (d j : ℝ) := by
  have hpos : ∀ j, (0 : ℝ) < d j := fun j ↦ by exact_mod_cast hd j
  have hprod : (0 : ℝ) < ∏ j, (d j : ℝ) := Finset.prod_pos fun j _ ↦ hpos j
  obtain ⟨del, hdel⟩ : ∃ del, del = ∑ j, (d j : ℝ)⁻¹ := ⟨_, rfl⟩
  obtain ⟨rho, hrho⟩ : ∃ rho, rho = max 1 t⁻¹ * del := ⟨_, rfl⟩
  have hdel0 : 0 ≤ del := hdel ▸ Finset.sum_nonneg fun j _ ↦ by positivity
  have hmax1 : (1 : ℝ) ≤ max 1 t⁻¹ := le_max_left _ _
  have hrho0 : 0 ≤ rho := hrho ▸ mul_nonneg (by linarith) hdel0
  have hdelrho : del ≤ rho := by rw [hrho]; nlinarith
  have hdrho : ∀ j, (d j : ℝ)⁻¹ ≤ rho := fun j ↦ le_trans
    (hdel ▸ Finset.single_le_sum (f := fun j ↦ (d j : ℝ)⁻¹) (fun j _ ↦ by positivity)
      (Finset.mem_univ j)) hdelrho
  have htrho : del ≤ t * rho := by
    have h1 : t⁻¹ * del ≤ max 1 t⁻¹ * del := mul_le_mul_of_nonneg_right (le_max_right _ _) hdel0
    calc del = t * (t⁻¹ * del) := by field_simp
      _ ≤ t * (max 1 t⁻¹ * del) := mul_le_mul_of_nonneg_left h1 ht.le
      _ = t * rho := by rw [hrho]
  have h1rho : (0 : ℝ) < 1 + rho := by linarith
  -- the boxes fit, after shrinking by `1 + rho`, inside the region
  have hsub : (⋃ i ∈ latticePoints d t, latticeBox d i) ⊆ (1 + rho) • cubeSimplex m t := by
    intro x hx
    simp only [Set.mem_iUnion, exists_prop] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    rw [mem_latticePoints] at hi
    rw [mem_latticeBox_iff hd] at hxi
    have hxl : ∀ j, (i j : ℝ) / (d j : ℝ) ≤ x j := fun j ↦ (div_le_iff₀ (hpos j)).2 (hxi j).1
    have hxu : ∀ j, x j < (i j : ℝ) / (d j : ℝ) + (d j : ℝ)⁻¹ := fun j ↦ by
      have h := (lt_div_iff₀ (hpos j)).2 (hxi j).2
      rwa [add_div, one_div] at h
    have hxnn : ∀ j, 0 ≤ x j := fun j ↦
      le_trans (by positivity : (0 : ℝ) ≤ (i j : ℝ) / (d j : ℝ)) (hxl j)
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ h1rho.ne']
    rw [mem_cubeSimplex]
    refine ⟨fun j ↦ ⟨?_, ?_⟩, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg (by positivity) (hxnn j)
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [inv_mul_le_iff₀ h1rho, mul_one]
      have h1 : (i j : ℝ) / (d j : ℝ) ≤ 1 :=
        (div_le_one (hpos j)).2 (by exact_mod_cast hi.1 j)
      linarith [hxu j, hdrho j]
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      rw [inv_mul_le_iff₀ h1rho]
      have hsum : ∑ j, x j ≤ (∑ j, (i j : ℝ) / (d j : ℝ)) + del := by
        rw [hdel, ← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun j _ ↦ (hxu j).le
      nlinarith [hi.2, htrho]
  -- volumes
  have hunion : volume (⋃ i ∈ latticePoints d t, latticeBox d i)
      = ((latticePoints d t).card : ℝ≥0∞) * ENNReal.ofReal (∏ j, (d j : ℝ))⁻¹ := by
    rw [measure_biUnion_finset (pairwiseDisjoint_latticeBox hd _)
      (fun i _ ↦ measurableSet_latticeBox d i),
      Finset.sum_congr rfl fun i _ ↦ volume_latticeBox hd i, Finset.sum_const, nsmul_eq_mul]
  have hsmulvol : volume ((1 + rho) • cubeSimplex m t)
      = ENNReal.ofReal ((1 + rho) ^ m) * volume (cubeSimplex m t) := by
    rw [Measure.addHaar_smul]
    simp [abs_of_nonneg (pow_nonneg h1rho.le m)]
  have hle : volume (⋃ i ∈ latticePoints d t, latticeBox d i)
      ≤ volume ((1 + rho) • cubeSimplex m t) := measure_mono hsub
  rw [hunion, hsmulvol] at hle
  have hle' := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by finiteness) (volume_cubeSimplex_ne_top m t)) hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)] at hle'
  rw [← hdel, ← hrho]
  calc ((latticePoints d t).card : ℝ)
      = ((latticePoints d t).card : ℝ) * (∏ j, (d j : ℝ))⁻¹ * ∏ j, (d j : ℝ) := by
        field_simp
    _ ≤ (1 + rho) ^ m * cubeSimplexVolume m t * ∏ j, (d j : ℝ) := by
        exact mul_le_mul_of_nonneg_right hle' hprod.le
    _ = cubeSimplexVolume m t * (1 + rho) ^ m * ∏ j, (d j : ℝ) := by ring

/-! ### The exponential-moment bound -/

/-- A continuous function cut down to a compact interval is integrable. -/
theorem integrable_indicator_Icc {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Icc a b)) :
    Integrable (Set.indicator (Icc a b) f) :=
  (hf.integrableOn_Icc).integrable_indicator measurableSet_Icc

/-- **The Chernoff bound in `m` coordinates.** For a nonnegative weight `g` on the line, the
integral of `∏ j, g (x j)` over the half-space `∑ j, x j ≤ s` is at most `exp (λ s)` times the
`m`-th power of the one-variable exponential moment `∫ exp (-λ x) g x`. Both estimates of this
file are this lemma at a different `g`: the indicator of `[0, 1]`, and the density of one
coordinate of a point of the standard simplex. -/
theorem setIntegral_prod_le_exp_mul_pow {g : ℝ → ℝ} (hg0 : ∀ x, 0 ≤ g x) (hg : Integrable g)
    {lam : ℝ} (hlam : 0 ≤ lam) (hgl : Integrable fun x ↦ Real.exp (-(lam * x)) * g x)
    (m : ℕ) (s : ℝ) :
    ∫ x in {y : Fin m → ℝ | ∑ j, y j ≤ s}, ∏ j, g (x j)
      ≤ Real.exp (lam * s) * (∫ x, Real.exp (-(lam * x)) * g x) ^ m := by
  have hS : MeasurableSet {y : Fin m → ℝ | ∑ j, y j ≤ s} :=
    measurableSet_le (by fun_prop) measurable_const
  have hvol : (volume : Measure (Fin m → ℝ)) = Measure.pi fun _ ↦ volume := volume_pi
  have hint1 : Integrable fun x : Fin m → ℝ ↦ ∏ j, g (x j) := by
    rw [hvol]; exact Integrable.fintype_prod fun _ ↦ hg
  have hint2 : Integrable fun x : Fin m → ℝ ↦ ∏ j, Real.exp (-(lam * x j)) * g (x j) := by
    rw [hvol]; exact Integrable.fintype_prod fun _ ↦ hgl
  rw [← integral_indicator hS]
  calc ∫ x : Fin m → ℝ, Set.indicator {y : Fin m → ℝ | ∑ j, y j ≤ s} (fun x ↦ ∏ j, g (x j)) x
      ≤ ∫ x : Fin m → ℝ, Real.exp (lam * s) * ∏ j, Real.exp (-(lam * x j)) * g (x j) := by
        refine integral_mono (hint1.indicator hS) (hint2.const_mul _) fun x ↦ ?_
        have hprodnn : 0 ≤ ∏ j, g (x j) := Finset.prod_nonneg fun j _ ↦ hg0 _
        have hfac : ∏ j, Real.exp (-(lam * x j)) * g (x j)
            = Real.exp (-(lam * ∑ j, x j)) * ∏ j, g (x j) := by
          rw [Finset.prod_mul_distrib, ← Real.exp_sum]
          congr 1
          simp [Finset.mul_sum]
        rcases le_or_gt (∑ j, x j) s with h | h
        · rw [Set.indicator_of_mem (show x ∈ {y : Fin m → ℝ | ∑ j, y j ≤ s} from h), hfac,
            ← mul_assoc, ← Real.exp_add]
          refine le_mul_of_one_le_left hprodnn (Real.one_le_exp ?_)
          have h2 := mul_nonneg hlam (sub_nonneg.2 h)
          rw [mul_sub] at h2
          linarith
        · rw [Set.indicator_of_notMem
            (show x ∉ {y : Fin m → ℝ | ∑ j, y j ≤ s} from not_le.2 h), hfac]
          positivity
    _ = Real.exp (lam * s) * ∫ x : Fin m → ℝ, ∏ j, Real.exp (-(lam * x j)) * g (x j) :=
        integral_const_mul _ _
    _ = Real.exp (lam * s) * (∫ x, Real.exp (-(lam * x)) * g x) ^ m := by
        rw [integral_fintype_prod_volume_eq_pow fun x ↦ Real.exp (-(lam * x)) * g x,
          Fintype.card_fin]

/-! ### The tail estimate -/

/-- The indicator of the unit cube is the product of the indicators of `[0, 1]`. -/
theorem prod_indicator_Icc (m : ℕ) (x : Fin m → ℝ) :
    ∏ j, Set.indicator (Icc (0 : ℝ) 1) (1 : ℝ → ℝ) (x j)
      = Set.indicator (univ.pi fun _ : Fin m ↦ Icc (0 : ℝ) 1) (1 : (Fin m → ℝ) → ℝ) x := by
  by_cases h : ∀ j, x j ∈ Icc (0 : ℝ) 1
  · rw [Set.indicator_of_mem (show x ∈ univ.pi fun _ : Fin m ↦ Icc (0 : ℝ) 1 from
      fun j _ ↦ h j)]
    exact Finset.prod_eq_one fun j _ ↦ Set.indicator_of_mem (h j) _
  · push Not at h
    obtain ⟨j, hj⟩ := h
    have hx : x ∉ univ.pi fun _ : Fin m ↦ Icc (0 : ℝ) 1 := fun hall ↦ hj (hall j (mem_univ j))
    rw [Set.indicator_of_notMem hx]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (Set.indicator_of_notMem hj _)

/-- `V_m(t)` as the integral of a product of one-variable weights: the form the Chernoff bound
consumes. -/
theorem cubeSimplexVolume_eq_setIntegral (m : ℕ) (t : ℝ) :
    cubeSimplexVolume m t
      = ∫ x in {y : Fin m → ℝ | ∑ j, y j ≤ t},
          ∏ j, Set.indicator (Icc (0 : ℝ) 1) (1 : ℝ → ℝ) (x j) := by
  have hS : MeasurableSet {y : Fin m → ℝ | ∑ j, y j ≤ t} :=
    measurableSet_le (by fun_prop) measurable_const
  rw [← integral_indicator hS]
  simp_rw [prod_indicator_Icc]
  rw [Set.indicator_indicator, integral_indicator_one (hS.inter
    (MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc)), measureReal_def, cubeSimplexVolume,
    cubeSimplex, Set.inter_comm]

theorem integrable_indicator_unitInterval :
    Integrable (Set.indicator (Icc (0 : ℝ) 1) (1 : ℝ → ℝ)) :=
  integrable_indicator_Icc (by fun_prop)

theorem integrable_exp_mul_indicator_unitInterval (lam : ℝ) :
    Integrable fun x ↦ Real.exp (-(lam * x)) * Set.indicator (Icc (0 : ℝ) 1) (1 : ℝ → ℝ) x := by
  have : (fun x ↦ Real.exp (-(lam * x)) * Set.indicator (Icc (0 : ℝ) 1) (1 : ℝ → ℝ) x)
      = Set.indicator (Icc (0 : ℝ) 1) fun x ↦ Real.exp (-(lam * x)) := by
    funext x
    by_cases hx : x ∈ Icc (0 : ℝ) 1 <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  rw [this]
  exact integrable_indicator_Icc (by fun_prop)

/-- The exponential moment of the unit interval: `∫_0^1 exp (-λ x) dx = (1 - exp (-λ)) / λ`. -/
theorem integral_exp_mul_indicator_unitInterval {lam : ℝ} (hlam : lam ≠ 0) :
    ∫ x, Real.exp (-(lam * x)) * Set.indicator (Icc (0 : ℝ) 1) (1 : ℝ → ℝ) x
      = (1 - Real.exp (-lam)) / lam := by
  have hrw : (fun x ↦ Real.exp (-(lam * x)) * Set.indicator (Icc (0 : ℝ) 1) (1 : ℝ → ℝ) x)
      = Set.indicator (Icc (0 : ℝ) 1) fun x ↦ Real.exp (-lam * x) := by
    funext x
    by_cases hx : x ∈ Icc (0 : ℝ) 1 <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx, neg_mul]
  rw [hrw, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_mul_left (fun x ↦ Real.exp x) (neg_ne_zero.2 hlam)]
  simp only [mul_zero, mul_one, integral_exp, Real.exp_zero, smul_eq_mul]
  field_simp
  ring

/-- **The tail estimate** (Bombieri–Gubler, Lemma 6.3.5): `V_m((1/2 - ε) m) ≤ exp (-6 m ε²)`.
The exponent `-6 m ε²` comes out of the Chernoff bound at `λ = 12 ε`, where
`Real.one_sub_exp_neg_div_le_exp` is sharp to second order. -/
theorem cubeSimplexVolume_le_exp_neg (m : ℕ) {eps : ℝ} (heps : 0 ≤ eps) :
    cubeSimplexVolume m ((1 / 2 - eps) * m) ≤ Real.exp (-(6 * m * eps ^ 2)) := by
  rcases eq_or_lt_of_le heps with h | h
  · rw [show -(6 * (m : ℝ) * eps ^ 2) = 0 by rw [← h]; ring, Real.exp_zero]
    exact cubeSimplexVolume_le_one _ _
  · have hlam : (0 : ℝ) < 12 * eps := by linarith
    have hmom := setIntegral_prod_le_exp_mul_pow
      (g := Set.indicator (Icc (0 : ℝ) 1) (1 : ℝ → ℝ))
      (Set.indicator_nonneg fun y _ ↦ zero_le_one) integrable_indicator_unitInterval
      hlam.le (integrable_exp_mul_indicator_unitInterval _) m ((1 / 2 - eps) * m)
    rw [← cubeSimplexVolume_eq_setIntegral,
      integral_exp_mul_indicator_unitInterval hlam.ne'] at hmom
    have hone : Real.exp (-(12 * eps)) ≤ 1 := by
      have := Real.exp_le_exp.2 (show -(12 * eps) ≤ 0 by linarith)
      rwa [Real.exp_zero] at this
    have hbase : (0 : ℝ) ≤ (1 - Real.exp (-(12 * eps))) / (12 * eps) :=
      div_nonneg (by linarith) hlam.le
    have hstep : (1 - Real.exp (-(12 * eps))) / (12 * eps)
        ≤ Real.exp (-((12 * eps) / 2) + (12 * eps) ^ 2 / 24) :=
      Real.one_sub_exp_neg_div_le_exp hlam
    refine hmom.trans ?_
    calc Real.exp (12 * eps * ((1 / 2 - eps) * m))
            * ((1 - Real.exp (-(12 * eps))) / (12 * eps)) ^ m
        ≤ Real.exp (12 * eps * ((1 / 2 - eps) * m))
            * Real.exp (-((12 * eps) / 2) + (12 * eps) ^ 2 / 24) ^ m := by gcongr
      _ = Real.exp (-(6 * m * eps ^ 2)) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]
          congr 1
          ring

/-! ### The multihomogeneous tail -/

/-- `∫_0^1 (1 - x) ^ k dx = 1 / (k + 1)`. -/
theorem integral_one_sub_pow (k : ℕ) : ∫ x in (0 : ℝ)..1, (1 - x) ^ k = 1 / ((k : ℝ) + 1) := by
  have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1) (fun u ↦ u ^ k) 1
  simp only [sub_zero, sub_self] at h
  rw [h, integral_pow]
  simp

/-- `∫_0^1 (1 - x) ^ k x dx = 1 / ((k + 1) (k + 2))`. -/
theorem integral_one_sub_pow_mul_self (k : ℕ) :
    ∫ x in (0 : ℝ)..1, (1 - x) ^ k * x = 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
  have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1)
    (fun u ↦ u ^ k * (1 - u)) 1
  simp only [sub_zero, sub_self, sub_sub_cancel] at h
  have i1 : IntervalIntegrable (fun x : ℝ ↦ x ^ k) volume 0 1 :=
    (by fun_prop : Continuous fun x : ℝ ↦ x ^ k).intervalIntegrable 0 1
  have i2 : IntervalIntegrable (fun x : ℝ ↦ x ^ (k + 1)) volume 0 1 :=
    (by fun_prop : Continuous fun x : ℝ ↦ x ^ (k + 1)).intervalIntegrable 0 1
  rw [h, intervalIntegral.integral_congr (g := fun x : ℝ ↦ x ^ k - x ^ (k + 1))
      (fun x _ ↦ by ring), intervalIntegral.integral_sub i1 i2, integral_pow, integral_pow]
  have h1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  have h2 : ((k : ℝ) + 2) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- `∫_0^1 (1 - x) ^ k x² dx = 2 / ((k + 1) (k + 2) (k + 3))`. -/
theorem integral_one_sub_pow_mul_sq (k : ℕ) :
    ∫ x in (0 : ℝ)..1, (1 - x) ^ k * x ^ 2
      = 2 / (((k : ℝ) + 1) * ((k : ℝ) + 2) * ((k : ℝ) + 3)) := by
  have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1)
    (fun u ↦ u ^ k * (1 - u) ^ 2) 1
  simp only [sub_zero, sub_self, sub_sub_cancel] at h
  have i1 : IntervalIntegrable (fun x : ℝ ↦ x ^ k - 2 * x ^ (k + 1)) volume 0 1 :=
    (by fun_prop : Continuous fun x : ℝ ↦ x ^ k - 2 * x ^ (k + 1)).intervalIntegrable 0 1
  have i2 : IntervalIntegrable (fun x : ℝ ↦ x ^ (k + 2)) volume 0 1 :=
    (by fun_prop : Continuous fun x : ℝ ↦ x ^ (k + 2)).intervalIntegrable 0 1
  have i3 : IntervalIntegrable (fun x : ℝ ↦ x ^ k) volume 0 1 :=
    (by fun_prop : Continuous fun x : ℝ ↦ x ^ k).intervalIntegrable 0 1
  have i4 : IntervalIntegrable (fun x : ℝ ↦ 2 * x ^ (k + 1)) volume 0 1 :=
    (by fun_prop : Continuous fun x : ℝ ↦ 2 * x ^ (k + 1)).intervalIntegrable 0 1
  rw [h, intervalIntegral.integral_congr
      (g := fun x : ℝ ↦ x ^ k - 2 * x ^ (k + 1) + x ^ (k + 2)) (fun x _ ↦ by ring),
    intervalIntegral.integral_add i1 i2, intervalIntegral.integral_sub i3 i4,
    intervalIntegral.integral_const_mul, integral_pow, integral_pow, integral_pow]
  have h1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  have h2 : ((k : ℝ) + 2) ≠ 0 := by positivity
  have h3 : ((k : ℝ) + 3) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- The quadratic moments of `(k + 1) (1 - x) ^ k` on `[0, 1]`, which is a probability density,
in the one combination the exponential-moment bound needs. -/
theorem integral_quadratic_mul_one_sub_pow (k : ℕ) (a b c : ℝ) :
    ∫ x in (0 : ℝ)..1, (a + b * x + c * x ^ 2) * (((k : ℝ) + 1) * (1 - x) ^ k)
      = a + b / ((k : ℝ) + 2) + c * 2 / (((k : ℝ) + 2) * ((k : ℝ) + 3)) := by
  have h1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  have h2 : ((k : ℝ) + 2) ≠ 0 := by positivity
  have h3 : ((k : ℝ) + 3) ≠ 0 := by positivity
  have i1 : IntervalIntegrable (fun x : ℝ ↦ ((k : ℝ) + 1) * a * (1 - x) ^ k) volume 0 1 :=
    (by fun_prop : Continuous fun x : ℝ ↦ ((k : ℝ) + 1) * a * (1 - x) ^ k).intervalIntegrable 0 1
  have i2 : IntervalIntegrable (fun x : ℝ ↦ ((k : ℝ) + 1) * b * ((1 - x) ^ k * x)
      + ((k : ℝ) + 1) * c * ((1 - x) ^ k * x ^ 2)) volume 0 1 :=
    (by fun_prop : Continuous fun x : ℝ ↦ ((k : ℝ) + 1) * b * ((1 - x) ^ k * x)
      + ((k : ℝ) + 1) * c * ((1 - x) ^ k * x ^ 2)).intervalIntegrable 0 1
  have i3 : IntervalIntegrable (fun x : ℝ ↦ ((k : ℝ) + 1) * b * ((1 - x) ^ k * x)) volume 0 1 :=
    (by fun_prop :
      Continuous fun x : ℝ ↦ ((k : ℝ) + 1) * b * ((1 - x) ^ k * x)).intervalIntegrable 0 1
  have i4 : IntervalIntegrable
      (fun x : ℝ ↦ ((k : ℝ) + 1) * c * ((1 - x) ^ k * x ^ 2)) volume 0 1 :=
    (by fun_prop :
      Continuous fun x : ℝ ↦ ((k : ℝ) + 1) * c * ((1 - x) ^ k * x ^ 2)).intervalIntegrable 0 1
  rw [intervalIntegral.integral_congr
      (g := fun x : ℝ ↦ ((k : ℝ) + 1) * a * (1 - x) ^ k
        + (((k : ℝ) + 1) * b * ((1 - x) ^ k * x) + ((k : ℝ) + 1) * c * ((1 - x) ^ k * x ^ 2)))
      (fun x _ ↦ by ring),
    intervalIntegral.integral_add i1 i2, intervalIntegral.integral_add i3 i4,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_one_sub_pow, integral_one_sub_pow_mul_self,
    integral_one_sub_pow_mul_sq]
  field_simp
  ring

/-- The density of one coordinate of a point taken uniformly in the standard `n`-dimensional
simplex: the Beta`(1, n)` density `n (1 - x) ^ (n - 1)` on `[0, 1]`. Its `j`-th moment is
`j ! n ! / (n + j)!`, and the two the estimate needs are `1 / (n + 1)` and `2 / ((n+1)(n+2))`. -/
def simplexCoordDensity (n : ℕ) : ℝ → ℝ :=
  Set.indicator (Icc (0 : ℝ) 1) fun x ↦ (n : ℝ) * (1 - x) ^ (n - 1)

theorem simplexCoordDensity_nonneg (n : ℕ) (x : ℝ) : 0 ≤ simplexCoordDensity n x :=
  Set.indicator_nonneg (fun y hy ↦ mul_nonneg (Nat.cast_nonneg n)
    (pow_nonneg (by linarith [hy.2]) _)) x

theorem integrable_simplexCoordDensity (n : ℕ) : Integrable (simplexCoordDensity n) :=
  integrable_indicator_Icc (by fun_prop)

theorem integrable_exp_mul_simplexCoordDensity (n : ℕ) (lam : ℝ) :
    Integrable fun x ↦ Real.exp (-(lam * x)) * simplexCoordDensity n x := by
  have hrw : (fun x ↦ Real.exp (-(lam * x)) * simplexCoordDensity n x)
      = Set.indicator (Icc (0 : ℝ) 1)
        fun x ↦ Real.exp (-(lam * x)) * ((n : ℝ) * (1 - x) ^ (n - 1)) := by
    funext x
    by_cases hx : x ∈ Icc (0 : ℝ) 1 <;>
      simp [simplexCoordDensity, Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  rw [hrw]
  exact integrable_indicator_Icc (by fun_prop)

/-- Every integral against the density is an integral over `[0, 1]`. -/
theorem integral_mul_simplexCoordDensity (f : ℝ → ℝ) (n : ℕ) :
    ∫ x, f x * simplexCoordDensity n x
      = ∫ x in (0 : ℝ)..1, f x * ((n : ℝ) * (1 - x) ^ (n - 1)) := by
  have hrw : (fun x ↦ f x * simplexCoordDensity n x)
      = Set.indicator (Icc (0 : ℝ) 1) fun x ↦ f x * ((n : ℝ) * (1 - x) ^ (n - 1)) := by
    funext x
    by_cases hx : x ∈ Icc (0 : ℝ) 1 <;>
      simp [simplexCoordDensity, Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  rw [hrw, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one]

/-- **The exponential moment of the simplex density.** ⚠ The pointwise bound
`exp (-u) ≤ 1 - u + u² / 2`, valid for every `u ≥ 0`, gives the book's estimate with no upper
restriction on `λ` at all; the book's `0 < λ ≤ n + 4` is forced by its alternating-series
argument, not by the statement. -/
theorem integral_exp_mul_simplexCoordDensity_le {n : ℕ} (hn : 1 ≤ n) {lam : ℝ} (hlam : 0 ≤ lam) :
    ∫ x, Real.exp (-(lam * x)) * simplexCoordDensity n x
      ≤ 1 - lam / (n + 1) + lam ^ 2 / ((n + 1) * (n + 2)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hpoint : ∀ x, Real.exp (-(lam * x)) * simplexCoordDensity (k + 1) x
      ≤ (1 + (-lam) * x + (lam ^ 2 / 2) * x ^ 2) * simplexCoordDensity (k + 1) x := by
    intro x
    by_cases hx : x ∈ Icc (0 : ℝ) 1
    · refine mul_le_mul_of_nonneg_right ?_ (simplexCoordDensity_nonneg _ x)
      have hux : 0 ≤ lam * x := mul_nonneg hlam hx.1
      have := Real.exp_neg_le_one_sub_add_sq_div_two hux
      nlinarith [this]
    · simp [simplexCoordDensity, Set.indicator_of_notMem, hx]
  have hint : ∫ x, (1 + (-lam) * x + (lam ^ 2 / 2) * x ^ 2) * simplexCoordDensity (k + 1) x
      = 1 - lam / ((k + 1 : ℕ) + 1) + lam ^ 2 / (((k + 1 : ℕ) + 1) * ((k + 1 : ℕ) + 2)) := by
    rw [integral_mul_simplexCoordDensity]
    have hcast : ∀ x : ℝ, ((k + 1 : ℕ) : ℝ) * (1 - x) ^ (k + 1 - 1)
        = ((k : ℝ) + 1) * (1 - x) ^ k := by
      intro x; push_cast; simp
    rw [intervalIntegral.integral_congr (g := fun x : ℝ ↦
      (1 + (-lam) * x + (lam ^ 2 / 2) * x ^ 2) * (((k : ℝ) + 1) * (1 - x) ^ k))
      (fun x _ ↦ by rw [hcast]), integral_quadratic_mul_one_sub_pow]
    have h2 : ((k : ℝ) + 2) ≠ 0 := by positivity
    have h3 : ((k : ℝ) + 3) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  calc ∫ x, Real.exp (-(lam * x)) * simplexCoordDensity (k + 1) x
      ≤ ∫ x, (1 + (-lam) * x + (lam ^ 2 / 2) * x ^ 2) * simplexCoordDensity (k + 1) x := by
        refine integral_mono (integrable_exp_mul_simplexCoordDensity _ _) ?_ hpoint
        have hrw : (fun x ↦ (1 + (-lam) * x + (lam ^ 2 / 2) * x ^ 2)
            * simplexCoordDensity (k + 1) x)
            = Set.indicator (Icc (0 : ℝ) 1) fun x ↦ (1 + (-lam) * x + (lam ^ 2 / 2) * x ^ 2)
              * ((((k : ℕ) + 1 : ℕ) : ℝ) * (1 - x) ^ (k + 1 - 1)) := by
          funext x
          by_cases hx : x ∈ Icc (0 : ℝ) 1 <;>
            simp [simplexCoordDensity, Set.indicator_of_mem, Set.indicator_of_notMem, hx]
        rw [hrw]
        exact integrable_indicator_Icc (by fun_prop)
    _ = _ := hint

/-- **The multihomogeneous tail, the exponential-moment form.** -/
theorem setIntegral_prod_simplexCoordDensity_le {n : ℕ} (hn : 1 ≤ n) {lam : ℝ} (hlam : 0 ≤ lam)
    (m : ℕ) (s : ℝ) :
    ∫ x in {y : Fin m → ℝ | ∑ j, y j ≤ s}, ∏ j, simplexCoordDensity n (x j)
      ≤ Real.exp (lam * s + m * (-(lam / (n + 1)) + lam ^ 2 / ((n + 1) * (n + 2)))) := by
  have hcher := setIntegral_prod_le_exp_mul_pow (g := simplexCoordDensity n)
    (simplexCoordDensity_nonneg n) (integrable_simplexCoordDensity n) hlam
    (integrable_exp_mul_simplexCoordDensity n lam) m s
  refine hcher.trans ?_
  have hmgf0 : 0 ≤ ∫ x, Real.exp (-(lam * x)) * simplexCoordDensity n x :=
    integral_nonneg fun x ↦ mul_nonneg (Real.exp_pos _).le (simplexCoordDensity_nonneg n x)
  have hexp : (∫ x, Real.exp (-(lam * x)) * simplexCoordDensity n x)
      ≤ Real.exp (-(lam / (n + 1)) + lam ^ 2 / ((n + 1) * (n + 2))) := by
    refine (integral_exp_mul_simplexCoordDensity_le hn hlam).trans ?_
    have := Real.add_one_le_exp (-(lam / ((n : ℝ) + 1)) + lam ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)))
    linarith
  calc Real.exp (lam * s) * (∫ x, Real.exp (-(lam * x)) * simplexCoordDensity n x) ^ m
      ≤ Real.exp (lam * s)
        * Real.exp (-(lam / (n + 1)) + lam ^ 2 / ((n + 1) * (n + 2))) ^ m := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]

/-- **The multihomogeneous tail** (Bombieri–Gubler (7.23)–(7.25)). ⚠ The hypothesis
`η ≤ 2 / (n + 1)` of the book is not needed. -/
theorem setIntegral_prod_simplexCoordDensity_le_exp {n : ℕ} (hn : 1 ≤ n) {eta : ℝ}
    (heta : 0 ≤ eta) (m : ℕ) :
    ∫ x in {y : Fin m → ℝ | ∑ j, y j ≤ m / (n + 1) - m * eta},
        ∏ j, simplexCoordDensity n (x j)
      ≤ Real.exp (-((n + 1) * (n + 2) * eta ^ 2 * m / 4)) := by
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hn2 : ((n : ℝ) + 2) ≠ 0 := by positivity
  refine (setIntegral_prod_simplexCoordDensity_le hn
    (lam := eta * ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2) (by positivity) m _).trans ?_
  refine le_of_eq (congrArg Real.exp ?_)
  field_simp
  ring

/-- The simplex density is a **probability** density: it integrates to `1`, so the third estimate
is a bound on a proportion. -/
theorem integral_simplexCoordDensity {n : ℕ} (hn : 1 ≤ n) :
    ∫ x, simplexCoordDensity n x = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h1 : ∫ x, simplexCoordDensity (k + 1) x
      = ∫ x, (1 + 0 * x + 0 * x ^ 2) * simplexCoordDensity (k + 1) x := by
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    ring
  have hcast : ∀ x : ℝ, ((k + 1 : ℕ) : ℝ) * (1 - x) ^ (k + 1 - 1)
      = ((k : ℝ) + 1) * (1 - x) ^ k := by
    intro x; push_cast; simp
  rw [h1, integral_mul_simplexCoordDensity, intervalIntegral.integral_congr
    (g := fun x : ℝ ↦ (1 + 0 * x + 0 * x ^ 2) * (((k : ℝ) + 1) * (1 - x) ^ k))
    (fun x _ ↦ by rw [hcast]), integral_quadratic_mul_one_sub_pow]
  ring

/-- **The region is the whole cube once `t` reaches `m`**: beyond the far corner of the cube the
hyperplane cuts nothing off. Layer 2.6 consumes the case `m = 0`, where the region has volume `1`
for every nonnegative `t` and the feasibility hypothesis of the index theorem therefore forbids
any point at all. -/
theorem cubeSimplexVolume_eq_one (m : ℕ) {t : ℝ} (ht : (m : ℝ) ≤ t) :
    cubeSimplexVolume m t = 1 := by
  have hset : cubeSimplex m t = univ.pi fun _ ↦ Icc (0 : ℝ) 1 := by
    refine Set.Subset.antisymm (cubeSimplex_subset_unitCube m t) fun x hx ↦ ?_
    refine mem_cubeSimplex.2 ⟨fun j ↦ hx j (mem_univ j), ?_⟩
    calc ∑ j, x j ≤ ∑ _j : Fin m, (1 : ℝ) :=
          Finset.sum_le_sum fun j _ ↦ (hx j (mem_univ j)).2
      _ = m := by simp
      _ ≤ t := ht
  rw [cubeSimplexVolume, hset, volume_unitCube]
  simp

/-! ### Acceptance criteria -/

/-- **Acceptance test: `V_m(t) = 1` once `t` reaches `m`.** -/
example (m : ℕ) {t : ℝ} (ht : (m : ℝ) ≤ t) : cubeSimplexVolume m t = 1 :=
  cubeSimplexVolume_eq_one m ht

/-- **Acceptance test: `V_m(t) = 0` for negative `t`.** -/
example (m : ℕ) {t : ℝ} (ht : t < 0) : cubeSimplexVolume m t = 0 := by
  have hset : cubeSimplex m t = ∅ := by
    ext x
    simp only [mem_cubeSimplex, Set.mem_empty_iff_false, iff_false, not_and]
    intro h1 h2
    have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) ↦ (h1 j).1
    linarith
  simp [cubeSimplexVolume, hset]

/-- **Acceptance test: in one variable `V_1(t)` is a length.** This is what pins the
normalisation: `V_1(t) = min 1 t`, and in particular `V_1(t) = t` on `[0, 1]`. -/
example {t : ℝ} (ht : 0 ≤ t) : cubeSimplexVolume 1 t = min 1 t := by
  have hset : cubeSimplex 1 t = univ.pi fun _ : Fin 1 ↦ Icc (0 : ℝ) (min 1 t) := by
    ext x
    simp only [mem_cubeSimplex, Fin.sum_univ_one, Set.mem_pi, Set.mem_univ, forall_const,
      Set.mem_Icc, le_min_iff, Fin.forall_fin_one]
    tauto
  rw [cubeSimplexVolume, hset, volume_pi_pi, Finset.prod_congr rfl fun j _ ↦ Real.volume_Icc,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one, sub_zero,
    ENNReal.toReal_ofReal (le_min zero_le_one ht)]

/-- **Rejection test: the upper lattice-point bound really does need `t > 0`.** At `t = 0` the
origin is an admissible lattice point while the region has no volume, so the count exceeds the
bound. The lower bound, which holds at every `t`, says only `0 ≤ 1`. -/
example : ¬ (((latticePoints (fun _ : Fin 1 ↦ 1) 0).card : ℝ)
    ≤ cubeSimplexVolume 1 0
      * (1 + max 1 (0 : ℝ)⁻¹ * ∑ _ : Fin 1, ((1 : ℕ) : ℝ)⁻¹) ^ 1
        * ∏ _ : Fin 1, ((1 : ℕ) : ℝ)) := by
  have hzero : cubeSimplexVolume 1 0 = 0 := by
    have hsub : cubeSimplex 1 0 ⊆ univ.pi fun _ : Fin 1 ↦ Icc (0 : ℝ) 0 := by
      intro x hx
      rw [mem_cubeSimplex, Fin.sum_univ_one] at hx
      exact fun j _ ↦ ⟨(hx.1 j).1, by simpa [Fin.eq_zero j] using hx.2⟩
    have : volume (cubeSimplex 1 0) = 0 := by
      refine measure_mono_null hsub ?_
      rw [volume_pi_pi]
      simp
    simp [cubeSimplexVolume, this]
  have hmem : (fun _ : Fin 1 ↦ 0) ∈ latticePoints (fun _ : Fin 1 ↦ 1) 0 :=
    mem_latticePoints.2 ⟨fun j ↦ by norm_num, by norm_num⟩
  have hcard : 1 ≤ (latticePoints (fun _ : Fin 1 ↦ 1) 0).card :=
    Finset.card_pos.2 ⟨_, hmem⟩
  rw [hzero]
  push Not
  have : (1 : ℝ) ≤ ((latticePoints (fun _ : Fin 1 ↦ 1) 0).card : ℝ) := by exact_mod_cast hcard
  linarith

/-- **Acceptance test: the density of the third estimate is a probability density.** Its mean is
`1 / (n + 1)` and its second moment `2 / ((n+1)(n+2))`, which are the two numbers the estimate
consumes; here is the zeroth. -/
example {n : ℕ} (hn : 1 ≤ n) : ∫ x, simplexCoordDensity n x = 1 :=
  integral_simplexCoordDensity hn

end MeasureTheory

end

end
