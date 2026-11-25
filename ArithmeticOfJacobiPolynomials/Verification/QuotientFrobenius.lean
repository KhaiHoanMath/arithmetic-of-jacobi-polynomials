module

public import ArithmeticOfJacobiPolynomials.Verification.Frobenius
public import Mathlib.RingTheory.AdjoinRoot

/-! # Frobenius certificates in a polynomial quotient

In the quotient by the proposed irreducible polynomial, the Frobenius identity
is an equality of elements and each coprimality test is a multiplicative inverse.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial

/-- Frobenius fixes the coefficients in this quotient of a prime field polynomial ring. -/
theorem adjoinRoot_of_pow_prime {p : ℕ} [Fact p.Prime] (h : (ZMod p)[X]) (a : ZMod p) :
    (AdjoinRoot.of h a) ^ p = AdjoinRoot.of h a := by
  rw [← map_pow, ZMod.pow_card]

/-- Frobenius is additive in the polynomial quotient, including for a nonmonic modulus. -/
theorem adjoinRoot_add_pow_prime {p : ℕ} [Fact p.Prime] (h : (ZMod p)[X]) (u v : AdjoinRoot h) :
    (u + v) ^ p = u ^ p + v ^ p := by
  obtain ⟨a, rfl⟩ := AdjoinRoot.mk_surjective u
  obtain ⟨b, rfl⟩ := AdjoinRoot.mk_surjective v
  simpa only [map_add, map_pow] using congrArg (AdjoinRoot.mk h) (add_pow_char a b p)

/-- The equality and inverse witnesses of Rabin's criterion may both be supplied
in the quotient ring, without exhibiting polynomial division or Bézout coefficients. -/
theorem irreducible_of_quotient_frobenius {p : ℕ} [Fact p.Prime] {h : (ZMod p)[X]}
    (hd : 0 < h.natDegree)
    (hall : AdjoinRoot.root h ^ p ^ h.natDegree = AdjoinRoot.root h)
    (htest : ∀ q : ℕ, q.Prime → q ∣ h.natDegree → ∃ w : AdjoinRoot h,
      w * (AdjoinRoot.root h ^ p ^ (h.natDegree / q) - AdjoinRoot.root h) = 1) :
    Irreducible h := by
  apply irreducible_of_frobenius_tests hd
  · rw [Nat.card_eq_fintype_card, ZMod.card]
    apply AdjoinRoot.mk_eq_mk.mp
    simpa only [map_pow, AdjoinRoot.mk_X] using hall
  · intro q hq hdiv
    rw [Nat.card_eq_fintype_card, ZMod.card]
    obtain ⟨w, hw⟩ := htest q hq hdiv
    obtain ⟨b, rfl⟩ := AdjoinRoot.mk_surjective w
    let g : (ZMod p)[X] := X ^ p ^ (h.natDegree / q) - X
    have he : AdjoinRoot.mk h (1 - b * g) = 0 := by
      simp only [g, map_sub, map_one, map_mul, map_pow, AdjoinRoot.mk_X, hw, sub_self]
    obtain ⟨a, ha⟩ := AdjoinRoot.mk_eq_zero.mp he
    refine ⟨a, b, ?_⟩
    change a * h + b * g = 1
    rw [mul_comm a h, ← ha, sub_add_cancel]

end ArithmeticOfJacobiPolynomials
