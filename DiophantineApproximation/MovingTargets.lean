/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.GapPrinciple
public import DiophantineApproximation.RothTheorem
public import Mathlib.Analysis.Asymptotics.Defs

-- Used only inside proofs.
import DiophantineApproximation.RationalPlaces
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Roth's theorem with moving targets

**Roth's theorem with moving targets** (Vojta; Bombieri–Gubler, Theorem 6.5.2). Let `K` be a
number field, `S` a finite set of places of `K` carried as two typed finsets, `F / K` a finite
extension and `w v` an absolute value of `F` over `v` for each `v ∈ S`. For every `κ > 2` and every
sequence of pairs `(α j, β j)`, with targets `α j : S → F` and `β j ∈ K`, such that

```text
1 + ∑ v ∈ S, h(α j v) = o(h(β j))        as j → ∞,
```

only finitely many `j` satisfy the inequality of Roth's theorem with the targets `α j`:

```text
(∏ v ∈ S∞, min 1 |β j − α j v|_v ^ mult v) * ∏ v ∈ S₀, min 1 |β j − α j v|_v  ≤  H(β j) ^ (−κ).
```

In particular the book's form holds: no infinite sequence satisfies both. Heights of the targets
and of the `β j` in the growth condition are absolute; the inequality is Layer 3.2's, in
Mathlib's relative heights.

The proof is the book's five lines, because Layer 3.2 is now structured for it:
`NumberField.roth_no_moving_chain` forbids a chain of `m + 1` solutions in one class, with heights
growing by the ratio `M`, *each with its own targets*, as soon as the targets are small against
the chain — `1 + ∑ v, h(α j v) ≤ δ h(β j)` for a `δ` that sees no target. The `o` supplies that
`δ` eventually, Mahler's reduction supplies the chain, and nothing else is needed.

## Main results

* `NumberField.finite_setOf_prod_min_one_le_of_isLittleO`: **Layer 3.8**, the finiteness of the
  set of indices.
* `NumberField.not_forall_prod_min_one_le_of_isLittleO`: the book's form, no infinite sequence.
* `NumberField.sum_sPlaceAbsValue`: a sum over the places of `S`, split into its two finsets.

## Implementation notes

⚠ **The targets enter Roth's proof in two places, not one.** The book's proof of 6.5.2 says that
only (6.11), the height of the auxiliary polynomial, changes. The Taylor expansion at a place of
`S` also carries the size of the target — the `log⁺ |α_v|_{v,K}` of (6.16), which is the
`2 |S| max log⁺ |α_v|` inside the `C₂` of (6.19) — and with moving targets it too must be `o(D)`.
It is bounded by the height of the target: an absolute value of `F` over a place of `K` is at most
the height, `max |x|_w 1 ≤ H(x)`, which is Layer 0.1's classification and
`NumberField.max_apply_one_le_mulHeight₁_of_liesOver_infinitePlace` with its finite twin. That
is the only new mathematics; the rest is 3.2 with `α` replaced by `α j`.

⚠ **Layer 3.2 was restructured, and nothing outside it had to change.** Steps I and II take the
index at a target *point* `(α 0 v, …, α m v)` rather than a diagonal, which Layer 2.6 already
allowed; Steps III to V take one target and one size bound per coordinate. Those statements were
generalized; Roth's theorem and every statement its consumers quote are unchanged. The core of
the proof is now `NumberField.roth_no_moving_chain`, and 3.7's `NumberField.roth_no_chain` is its
fixed-target case with `L = [K : ℚ] (1 + ∑ v, h(α v)) / δ` — so the targets of 3.2 enter only
through their heights, as the book claims.

⚠ **The conclusion is about indices, and the `1 +` is load-bearing.** A sequence may repeat a pair;
the statement counts the `j`, not the values `β j`. Without the `1`, the constant pair `(0, 0)`
at `S = {∞}` over `ℚ` satisfies `0 = o(0)` and is a solution at every `j`; with it, the growth
condition forces `h(β j) → ∞`. The acceptance criteria check both.

⚠ **A solution equal to one of its own targets is classified, not discarded.** In Layer 3.2 the
at most `|S|` such `β` are thrown away; with moving targets there may be infinitely many. The
class of a pair is `NumberField.approxClass` of Layer 3.7 at its own targets, which puts such a
`β j` in a corner of the simplex, where the bounds (6.9) and (6.10) still hold. So the proof never
needs that `β j = α j v` forces `h(α j v) = h(β j)`, which is height invariance under extension of
the base field.

⚠ **`o(h(β j))` cannot be weakened to `O(h(β j))`.** With the targets equal to the approximations,
every term is a solution and `1 + h(α j) = O(h(β j))`; the acceptance criteria check it. The
quantitative version, 6.5.3, replaces the `o` by `δ(κ) h(β j)` with an explicit `δ(κ)`; here
`δ` is an existential of `NumberField.roth_no_moving_chain` and depends on `K`, `S` and `[F : ℚ]`
as well as `κ`.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Theorem 6.5.2. P. Vojta, *Roth's theorem with moving targets*, Internat. Math. Res. Notices
(1996), 109–114.

This is Layer 3.8 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

open Asymptotics Filter Height Module

namespace NumberField

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]

/-- A sum over the places of `S`, split into its infinite and its finite part. -/
theorem sum_sPlaceAbsValue {Sinf : Finset (InfinitePlace K)} {Sfin : Finset (FinitePlace K)}
    (f : AbsoluteValue K ℝ → ℝ) :
    ∑ a : ↥Sinf ⊕ ↥Sfin, f (sPlaceAbsValue a) = ∑ v ∈ Sinf, f v.1 + ∑ v ∈ Sfin, f v.1 := by
  rw [Fintype.sum_sum_type, ← Finset.sum_coe_sort Sinf fun v ↦ f v.1,
    ← Finset.sum_coe_sort Sfin fun v ↦ f v.1]
  rfl

/-- **Layer 3.8: Roth's theorem with moving targets** (Vojta; Bombieri–Gubler, Theorem 6.5.2).
If the heights of the targets `α j` grow more slowly than the heights of the `β j` — precisely,
`1 + ∑ v ∈ S, h(α j v) = o(h(β j))` — then only finitely many `j` satisfy Roth's inequality with
the targets `α j`. Heights in the growth condition are absolute. -/
theorem finite_setOf_prod_min_one_le_of_isLittleO (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    {κ : ℝ} (hκ : 2 < κ) (α : ℕ → AbsoluteValue K ℝ → F) (β : ℕ → K)
    (hα : (fun j ↦ 1 + ∑ v ∈ Sinf, absLogHeight₁ (α j v.1) + ∑ v ∈ Sfin, absLogHeight₁ (α j v.1))
      =o[atTop] fun j ↦ absLogHeight₁ (β j)) :
    {j : ℕ | (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F (β j) - α j v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F (β j) - α j v.1))
          ≤ mulHeight₁ (β j) ^ (-κ)}.Finite := by
  classical
  by_contra hinf
  set s := Sinf.card + Sfin.card with hsdef
  set N := rothClassSize κ s with hNdef
  have hκ0 : (0 : ℝ) < κ := by linarith
  have hN : 0 < N := (rothClassSize_spec hκ s).1
  obtain ⟨δ, hδ0, hδ⟩ := roth_no_moving_chain Sinf Sfin w hwInf hwFin hκ
  set A : ℕ → ℝ := fun j ↦ ∑ v ∈ Sinf, absLogHeight₁ (α j v.1) + ∑ v ∈ Sfin, absLogHeight₁ (α j v.1)
    with hAdef
  have hA0 : ∀ j, 0 ≤ A j := fun j ↦
    add_nonneg (Finset.sum_nonneg fun v _ ↦ absLogHeight₁_nonneg _)
      (Finset.sum_nonneg fun v _ ↦ absLogHeight₁_nonneg _)
  -- the targets are eventually small against the approximations
  have hev : ∀ c : ℝ, 0 < c → ∀ᶠ j in atTop, 1 + A j ≤ c * absLogHeight₁ (β j) := by
    intro c hc
    filter_upwards [hα.def hc] with j hj
    rwa [Real.norm_of_nonneg (by rw [add_assoc]; linarith [hA0 j]),
      Real.norm_of_nonneg (absLogHeight₁_nonneg _), add_assoc] at hj
  have hfinbad : ∀ c : ℝ, 0 < c → {j : ℕ | ¬ 1 + A j ≤ c * absLogHeight₁ (β j)}.Finite := by
    intro c hc
    obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp (hev c hc)
    refine (Set.finite_lt_nat j₀).subset fun j hj ↦ ?_
    by_contra hlt
    exact hj (hj₀ j (not_lt.mp hlt))
  -- so the heights of the `β j` tend to infinity
  have hbig : ∀ C : ℝ, {j : ℕ | logHeight₁ (β j) ≤ C}.Finite := by
    intro C
    refine (hfinbad (1 / (|C| + 1)) (by positivity)).subset fun j hj ↦ ?_
    intro hsm
    have hC1 : (0 : ℝ) < |C| + 1 := by positivity
    have h1 : |C| + 1 ≤ absLogHeight₁ (β j) := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hC1] at hsm
      nlinarith [hA0 j]
    have htw : (1 : ℝ) ≤ totalWeight K := by exact_mod_cast totalWeight_pos K
    have h2 : absLogHeight₁ (β j) ≤ logHeight₁ (β j) := by
      rw [logHeight₁_eq_totalWeight_mul_absLogHeight₁]
      exact le_mul_of_one_le_left (absLogHeight₁_nonneg _) htw
    have h3 : C ≤ |C| := le_abs_self C
    have hj' : logHeight₁ (β j) ≤ C := hj
    linarith
  -- the solutions with small targets
  set J : Set ℕ := {j : ℕ | ((∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F (β j) - α j v.1)) ^ v.mult) *
      ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F (β j) - α j v.1)) ≤ mulHeight₁ (β j) ^ (-κ)) ∧
      1 + A j ≤ δ * absLogHeight₁ (β j)} with hJdef
  have hJ : J.Infinite := by
    intro hJfin
    refine hinf ((hJfin.union (hfinbad δ hδ0)).subset fun j hj ↦ ?_)
    by_cases hδj : 1 + A j ≤ δ * absLogHeight₁ (β j)
    · exact Or.inl ⟨hj, hδj⟩
    · exact Or.inr hδj
  -- one approximation class, each pair classified by its own targets
  obtain ⟨c, -, hc⟩ := Set.Infinite.exists_infinite_fiber hJ
    (f := fun j ↦ approxClass Sinf Sfin w (α j) N (β j)) (Set.finite_setOf_sum_le _ N)
    fun j _ ↦ sum_approxClass_le Sinf Sfin w (α j) N (β j)
  have hunb : ∀ C : ℝ, ∃ j ∈ {j ∈ J | approxClass Sinf Sfin w (α j) N (β j) = c},
      C < logHeight₁ (β j) := by
    intro C
    obtain ⟨j, hj, hjC⟩ := (hc.sdiff (hbig C)).nonempty
    exact ⟨j, hj, lt_of_not_ge hjC⟩
  obtain ⟨x, hxJ, hind⟩ := exists_isHeightIndependent_comp β hunb 1 (rothRatio κ s (finrank K F))
  -- what every member of the chain satisfies
  have hsolA : ∀ i, ∏ a, localApprox Sinf Sfin w (α (x i)) a (β (x i))
      ≤ mulHeight₁ (β (x i)) ^ (-κ) := fun i ↦ by
    rw [prod_localApprox]
    exact (hxJ i).1.1
  have hH : ∀ i, 1 < mulHeight₁ (β (x i)) := fun i ↦ by
    have h1 := (hxJ i).1.2
    have hpos : 0 < absLogHeight₁ (β (x i)) := by
      by_contra hneg
      push Not at hneg
      nlinarith [hA0 (x i), absLogHeight₁_nonneg (β (x i))]
    have hlog : 0 < logHeight₁ (β (x i)) := by
      rw [logHeight₁_eq_totalWeight_mul_absLogHeight₁]
      exact mul_pos (by exact_mod_cast totalWeight_pos K) hpos
    rw [logHeight₁_eq_log_mulHeight₁] at hlog
    exact (Real.log_pos_iff (mulHeight₁_pos _).le).mp hlog
  refine hδ (fun a ↦ (c a : ℝ) / N) (fun a ↦ by positivity) ?_ (fun i ↦ α (x i))
    (fun i ↦ β (x i)) (fun i ↦ ?_) (fun i ↦ ?_) fun i a ↦ ?_
  · have h := one_sub_card_div_le_sum_approxClass hκ0 hN (hsolA 0) (hH 0)
    rwa [(hxJ 0).2] at h
  · have hs : ∑ a : ↥Sinf ⊕ ↥Sfin, absLogHeight₁ (α (x i) (sPlaceAbsValue a)) = A (x i) :=
      sum_sPlaceAbsValue fun u ↦ absLogHeight₁ (α (x i) u)
    rw [hs]
    exact (hxJ i).1.2
  · simpa [Fin.val_succ, Fin.val_castSucc] using hind.2 i
  · have h := localApprox_le_rpow_approxClass hκ0 hN (hsolA i) (hH i) a
    rwa [(hxJ i).2] at h

/-- **Layer 3.8, in the book's form** (Bombieri–Gubler, Theorem 6.5.2): there is no infinite
sequence of pairs `(α j, β j)` with `1 + ∑ v ∈ S, h(α j v) = o(h(β j))` every term of which is a
solution. -/
theorem not_forall_prod_min_one_le_of_isLittleO (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    {κ : ℝ} (hκ : 2 < κ) (α : ℕ → AbsoluteValue K ℝ → F) (β : ℕ → K)
    (hα : (fun j ↦ 1 + ∑ v ∈ Sinf, absLogHeight₁ (α j v.1) + ∑ v ∈ Sfin, absLogHeight₁ (α j v.1))
      =o[atTop] fun j ↦ absLogHeight₁ (β j)) :
    ¬ ∀ j, (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F (β j) - α j v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F (β j) - α j v.1))
          ≤ mulHeight₁ (β j) ^ (-κ) := fun h ↦
  Set.infinite_univ ((finite_setOf_prod_min_one_le_of_isLittleO Sinf Sfin w hwInf hwFin hκ α β
    hα).subset fun j _ ↦ h j)

/-! ### Acceptance criteria -/

/-- **Conformance: constant targets give Roth's theorem back.** An infinite set of solutions of
Layer 3.2 enumerates as an injective sequence, whose heights tend to infinity by Northcott; a
constant `1 + ∑ v, h(α v)` is `o` of them, and Layer 3.8 bounds the indices. -/
example (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (α : AbsoluteValue K ℝ → F) {κ : ℝ} (hκ : 2 < κ) :
    {β : K | (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) ≤ mulHeight₁ β ^ (-κ)}.Finite := by
  by_contra hinf
  have : Infinite {β : K | (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
      ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) ≤ mulHeight₁ β ^ (-κ)} :=
    Set.infinite_coe_iff.mpr hinf
  set e := Infinite.natEmbedding {β : K | (∏ v ∈ Sinf,
      min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
      ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) ≤ mulHeight₁ β ^ (-κ)} with hedef
  have hinj : Function.Injective fun j ↦ (e j : K) := fun i j h ↦ e.injective (Subtype.ext h)
  have hlim : Tendsto (fun j ↦ absLogHeight₁ (e j : K)) atTop atTop := by
    rw [tendsto_atTop]
    intro C
    have hfin := (finite_setOfPred_logHeight₁_le (K := K) ((totalWeight K : ℝ) * C)).preimage
      hinj.injOn
    rw [← Nat.cofinite_eq_atTop]
    filter_upwards [hfin.eventually_cofinite_notMem] with j hj
    have hd : (0 : ℝ) < totalWeight K := by exact_mod_cast totalWeight_pos K
    have hj' : ¬ logHeight₁ (e j : K) ≤ (totalWeight K : ℝ) * C := hj
    rw [logHeight₁_eq_totalWeight_mul_absLogHeight₁] at hj'
    exact le_of_lt (lt_of_mul_lt_mul_left (lt_of_not_ge hj') hd.le)
  refine Set.infinite_univ ((finite_setOf_prod_min_one_le_of_isLittleO Sinf Sfin w hwInf hwFin hκ
    (fun _ ↦ α) (fun j ↦ (e j : K)) ?_).subset fun j _ ↦ (e j).2)
  exact isLittleO_const_left.2 (Or.inr (tendsto_norm_atTop_atTop.comp hlim))

/-- The absolute height of a positive integer, over `ℚ`. -/
private theorem absLogHeight₁_natCast_rat (n : ℕ) [NeZero n] :
    absLogHeight₁ (n : ℚ) = Real.log n := by
  rw [absLogHeight₁_eq_inv_mul_logHeight₁, Module.finrank_self, Rat.logHeight₁_natCast]
  simp

/-- **Rejection test: the `1 +` is load-bearing.** A sequence may repeat a pair. Without the `1`,
the constant pair `(0, 0)` over `ℚ` at `S = {∞}` satisfies the growth condition — `0 = o(0)` — and
is a solution at every index, the local factor `min 1 |0 − 0|` being `0`. -/
example (κ : ℝ) :
    ((fun _ : ℕ ↦ ∑ _v ∈ ({Rat.infinitePlace} : Finset (InfinitePlace ℚ)), absLogHeight₁ (0 : ℚ)
        + ∑ _v ∈ (∅ : Finset (FinitePlace ℚ)), absLogHeight₁ (0 : ℚ))
      =o[atTop] fun _ ↦ absLogHeight₁ (0 : ℚ)) ∧
    {_j : ℕ | (∏ v ∈ ({Rat.infinitePlace} : Finset (InfinitePlace ℚ)),
        min 1 ((id : AbsoluteValue ℚ ℝ → AbsoluteValue ℚ ℝ) v.1 (algebraMap ℚ ℚ 0 - 0)) ^ v.mult) *
      ∏ v ∈ (∅ : Finset (FinitePlace ℚ)),
        min 1 ((id : AbsoluteValue ℚ ℝ → AbsoluteValue ℚ ℝ) v.1 (algebraMap ℚ ℚ 0 - 0))
          ≤ mulHeight₁ (0 : ℚ) ^ (-κ)}.Infinite := by
  refine ⟨by simp [absLogHeight₁_zero], ?_⟩
  convert Set.infinite_univ (α := ℕ) using 1
  refine Set.eq_univ_of_forall fun _ ↦ ?_
  simp

/-- **Rejection test: `o` cannot be weakened to `O`.** With the targets equal to the
approximations — the constant pair `(2, 2)` over `ℚ` at `S = {∞}` — the growth condition holds
with `O` in place of `o`, and every index is a solution. -/
example (κ : ℝ) :
    ((fun _ : ℕ ↦ 1 + ∑ _v ∈ ({Rat.infinitePlace} : Finset (InfinitePlace ℚ)),
        absLogHeight₁ (2 : ℚ) + ∑ _v ∈ (∅ : Finset (FinitePlace ℚ)), absLogHeight₁ (2 : ℚ))
      =O[atTop] fun _ ↦ absLogHeight₁ (2 : ℚ)) ∧
    {_j : ℕ | (∏ v ∈ ({Rat.infinitePlace} : Finset (InfinitePlace ℚ)),
        min 1 ((id : AbsoluteValue ℚ ℝ → AbsoluteValue ℚ ℝ) v.1 (algebraMap ℚ ℚ 2 - 2)) ^ v.mult) *
      ∏ v ∈ (∅ : Finset (FinitePlace ℚ)),
        min 1 ((id : AbsoluteValue ℚ ℝ → AbsoluteValue ℚ ℝ) v.1 (algebraMap ℚ ℚ 2 - 2))
          ≤ mulHeight₁ (2 : ℚ) ^ (-κ)}.Infinite := by
  have h2 : absLogHeight₁ (2 : ℚ) = Real.log 2 := by
    have h := absLogHeight₁_natCast_rat 2
    push_cast at h
    exact h
  refine ⟨isBigO_const_const _ (by rw [h2]; exact (Real.log_pos (by norm_num)).ne') _, ?_⟩
  convert Set.infinite_univ (α := ℕ) using 1
  refine Set.eq_univ_of_forall fun _ ↦ ?_
  simp only [Set.mem_ofPred_eq, Algebra.algebraMap_self, RingHom.id_apply, sub_self, map_zero,
    Finset.prod_singleton, Finset.prod_empty, id, mul_one]
  rw [min_eq_right zero_le_one, zero_pow InfinitePlace.mult_ne_zero]
  positivity

end NumberField

end
