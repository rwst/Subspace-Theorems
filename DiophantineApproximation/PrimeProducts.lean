/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import DiophantineApproximation.RationalPlaces

/-!
# The primes of an integer, and products of `p`-adic sizes over them

Ridout's theorem — Layer 3.3 — multiplies the `p`-adic sizes of the numerator and of the
denominator of a rational number over two finite sets of primes. Its applications choose those
sets as *the* primes of one fixed integer, and then the two products are not estimates but
identities: if every prime factor of `d` lies in `S`, then

```text
∏ l ∈ S, padicNorm l d = d⁻¹,
```

because the product formula's missing factors are all `1`. This file is that identity, together
with the monotonicity `b ∣ a → ∏ l ∈ S, padicNorm l a ≤ ∏ l ∈ S, padicNorm l b` that turns a
divisibility into a bound on a product.

## Main results

* `Nat.primesOf`: the prime factors of a natural number, as a `Finset Nat.Primes`.
* `Rat.prod_padicNorm_natCast`: the identity above.
* `Rat.prod_padicNorm_le_of_dvd`: the monotonicity.

## Implementation notes

⚠ **`Nat.primeFactors` is a `Finset ℕ` and Ridout's theorem indexes by `Nat.Primes`.** The two
are the same data, but a `Finset Nat.Primes` is what makes `∏ l ∈ S, padicNorm l x` state without
a `Fact (l.Prime)` side condition — the reason Layer 3.3 chose that index type — so `primesOf`
carries `Nat.primeFactors` across, and `Nat.mem_primesOf` is the only fact about it that is ever
used.

⚠ **The identity is not the product formula.** The product formula runs over *all* places and
includes the infinite one; this is the finite part alone, and it is an identity only because the
hypothesis says the primes outside `S` miss `d`. Over any smaller `S` the product is `≥ d⁻¹`,
which is the wrong direction for every application, so the hypothesis is not decoration.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Section 1.4.

This is part of Layer 3.5 of the `DiophantineApproximation` roadmap.
-/

@[expose] public section

namespace Nat

/-- The primes dividing `n`, as a finite set of `Nat.Primes`: `Nat.primeFactors` read in the
index type Layer 3.3 uses. It is empty for `n = 0` and for `n = 1`. -/
def primesOf (n : ℕ) : Finset Nat.Primes :=
  n.primeFactors.attach.image
    fun l : {x // x ∈ n.primeFactors} ↦ (⟨(l : ℕ), prime_of_mem_primeFactors l.2⟩ : Nat.Primes)

theorem mem_primesOf {n : ℕ} {l : Nat.Primes} : l ∈ n.primesOf ↔ (l : ℕ) ∈ n.primeFactors := by
  rw [primesOf]
  constructor
  · intro h
    obtain ⟨a, -, ha⟩ := Finset.mem_image.mp h
    have hval : (l : ℕ) = (a : ℕ) := congrArg (fun x : Nat.Primes ↦ (x : ℕ)) ha.symm
    rw [hval]
    exact a.2
  · intro h
    exact Finset.mem_image.mpr ⟨⟨(l : ℕ), h⟩, Finset.mem_attach _ _, rfl⟩

/-- A prime belongs to `n.primesOf` exactly when it divides `n`, for `n ≠ 0`. -/
theorem mem_primesOf_iff_dvd {n : ℕ} (hn : n ≠ 0) {l : Nat.Primes} :
    l ∈ n.primesOf ↔ (l : ℕ) ∣ n := by
  rw [mem_primesOf, Nat.mem_primeFactors]
  exact ⟨fun h ↦ h.2.1, fun h ↦ ⟨l.2, h, hn⟩⟩

/-- A prime dividing a power of `n` belongs to `n.primesOf`. -/
theorem mem_primesOf_of_dvd_pow {n k : ℕ} (hn : n ≠ 0) {l : Nat.Primes} (h : (l : ℕ) ∣ n ^ k) :
    l ∈ n.primesOf :=
  (mem_primesOf_iff_dvd hn).mpr (l.2.dvd_of_dvd_pow h)

end Nat

namespace Rat

/-- **The finite part of the product formula, over the primes of the number itself.** If every
prime factor of `d` lies in `S`, then `∏ l ∈ S, padicNorm l d = d⁻¹`: the factors `S` adds
beyond the prime factors of `d` are `1`, and none is missing. -/
theorem prod_padicNorm_natCast (S : Finset Nat.Primes) :
    ∀ d : ℕ, d ≠ 0 → (∀ l : Nat.Primes, (l : ℕ) ∣ d → l ∈ S) →
      ∏ l ∈ S, padicNorm (l : ℕ) ((d : ℕ) : ℚ) = ((d : ℕ) : ℚ)⁻¹ := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd hS
    rcases eq_or_ne d 1 with rfl | hd1
    · simp
    obtain ⟨l₀, hl₀p, e, rfl⟩ : ∃ l₀ : ℕ, l₀.Prime ∧ ∃ e : ℕ, d = l₀ * e := by
      obtain ⟨l₀, hl₀p, hl₀d⟩ := Nat.exists_prime_and_dvd hd1
      exact ⟨l₀, hl₀p, hl₀d⟩
    have he0 : e ≠ 0 := by rintro rfl; simp at hd
    have hl₀0 : l₀ ≠ 0 := hl₀p.ne_zero
    have helt : e < l₀ * e :=
      lt_mul_of_one_lt_left (Nat.pos_of_ne_zero he0) hl₀p.one_lt
    have hSe : ∀ l : Nat.Primes, (l : ℕ) ∣ e → l ∈ S :=
      fun l hl ↦ hS l (hl.mul_left l₀)
    have hsingle : ∏ l ∈ S, padicNorm (l : ℕ) ((l₀ : ℕ) : ℚ) = ((l₀ : ℕ) : ℚ)⁻¹ := by
      have hmem : (⟨l₀, hl₀p⟩ : Nat.Primes) ∈ S := hS ⟨l₀, hl₀p⟩ ⟨e, rfl⟩
      refine Eq.trans (Finset.prod_eq_single (s := S)
        (f := fun l : Nat.Primes ↦ padicNorm (l : ℕ) ((l₀ : ℕ) : ℚ))
        (⟨l₀, hl₀p⟩ : Nat.Primes) (fun b _ hb ↦ ?_) (fun hcon ↦ absurd hmem hcon)) ?_
      · have hne : (b : ℕ) ≠ l₀ := fun hc ↦ hb (Subtype.ext hc)
        exact (padicNorm.nat_eq_one_iff _).mpr
          fun hdvd ↦ hne ((Nat.prime_dvd_prime_iff_eq b.2 hl₀p).mp hdvd)
      · change padicNorm l₀ ((l₀ : ℕ) : ℚ) = ((l₀ : ℕ) : ℚ)⁻¹
        exact padicNorm.padicNorm_p hl₀p.one_lt
    have hrec := ih e helt he0 hSe
    have hcast : ((l₀ * e : ℕ) : ℚ) = ((l₀ : ℕ) : ℚ) * ((e : ℕ) : ℚ) := by push_cast; ring
    calc ∏ l ∈ S, padicNorm (l : ℕ) ((l₀ * e : ℕ) : ℚ)
        = ∏ l ∈ S, padicNorm (l : ℕ) ((l₀ : ℕ) : ℚ) * padicNorm (l : ℕ) ((e : ℕ) : ℚ) := by
          refine Finset.prod_congr rfl fun l _ ↦ ?_
          rw [hcast, padicNorm.mul]
      _ = (∏ l ∈ S, padicNorm (l : ℕ) ((l₀ : ℕ) : ℚ))
            * ∏ l ∈ S, padicNorm (l : ℕ) ((e : ℕ) : ℚ) := Finset.prod_mul_distrib
      _ = ((l₀ : ℕ) : ℚ)⁻¹ * ((e : ℕ) : ℚ)⁻¹ := by rw [hsingle, hrec]
      _ = ((l₀ * e : ℕ) : ℚ)⁻¹ := by rw [hcast, mul_inv]

/-- **A divisor bounds the product from above.** Since every `p`-adic size of an integer is at
most `1`, passing from `b` to a multiple `a` can only shrink each factor. -/
theorem prod_padicNorm_le_of_dvd (S : Finset Nat.Primes) {a b : ℤ} (hb : b ∣ a) :
    ∏ l ∈ S, padicNorm (l : ℕ) ((a : ℤ) : ℚ) ≤ ∏ l ∈ S, padicNorm (l : ℕ) ((b : ℤ) : ℚ) := by
  obtain ⟨c, rfl⟩ := hb
  refine Finset.prod_le_prod₀ (fun l _ ↦ padicNorm.nonneg _) fun l _ ↦ ?_
  have hmul : (((b * c : ℤ)) : ℚ) = ((b : ℤ) : ℚ) * ((c : ℤ) : ℚ) := by push_cast; ring
  rw [hmul, padicNorm.mul]
  exact mul_le_of_le_one_right (padicNorm.nonneg _) (padicNorm.of_int _)

end Rat

/-! ### Acceptance criteria -/

/-- Conformance: `∏ l ∈ primesOf 12, |12|_l = 1 / 12`, the shape Layer 3.5 consumes. -/
example : (∏ l ∈ Nat.primesOf 12, padicNorm (l : ℕ) ((12 : ℕ) : ℚ)) = ((12 : ℕ) : ℚ)⁻¹ :=
  Rat.prod_padicNorm_natCast _ 12 (by norm_num)
    fun l hl ↦ (Nat.mem_primesOf_iff_dvd (by norm_num)).mpr hl

/-- **`d ≠ 0` is not removable.** The empty product is `1` and Lean's `(0 : ℚ)⁻¹` is `0`. -/
example : (∏ l ∈ Nat.primesOf 0, padicNorm (l : ℕ) ((0 : ℕ) : ℚ)) ≠ ((0 : ℕ) : ℚ)⁻¹ := by
  rw [show Nat.primesOf 0 = (∅ : Finset Nat.Primes) from
    Finset.eq_empty_of_forall_notMem fun l hl ↦ by
      rw [Nat.mem_primesOf, Nat.mem_primeFactors] at hl
      exact hl.2.2 rfl]
  norm_num

/-- **The divisibility hypothesis is not removable, and it fails in one direction only.** Over a
set of primes missing a factor of `d` the product is too *large*: here `1`, not `2⁻¹`. -/
example : (∏ l ∈ (∅ : Finset Nat.Primes), padicNorm (l : ℕ) ((2 : ℕ) : ℚ)) ≠ ((2 : ℕ) : ℚ)⁻¹ := by
  norm_num

/-- **Rejection test: a prime not dividing `n` is not one of its primes.** -/
example (l : Nat.Primes) (h : (l : ℕ) = 5) : l ∉ Nat.primesOf 12 := by
  rw [Nat.mem_primesOf_iff_dvd (by norm_num), h]
  norm_num

end
