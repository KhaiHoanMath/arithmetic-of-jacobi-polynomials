module

public import ArithmeticOfJacobiPolynomials.Polynomial.FactorDegrees
public import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Tactic

/-! # A single-prime certificate for Appendix C
A primitive integer polynomial is irreducible over the rationals if a full-degree
reduction passes the Frobenius irreducibility test.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial

/-- The Frobenius irreducibility criterion over a finite field. It applies to
nonmonic polynomials as well. -/
theorem irreducible_of_frobenius_tests {k : Type*} [Field k] [Finite k] {f : k[X]}
    (hd : 0 < f.natDegree) (hall : f ∣ X ^ (Nat.card k) ^ f.natDegree - X)
    (htest : ∀ q : ℕ, q.Prime → q ∣ f.natDegree →
      IsCoprime f (X ^ (Nat.card k) ^ (f.natDegree / q) - X)) : Irreducible f := by
  have hf : f ≠ 0 := by rintro rfl; simp at hd
  have hu : ¬ IsUnit f := fun h => (Nat.ne_of_gt hd) (natDegree_eq_zero_of_isUnit h)
  obtain ⟨g, hg, hgdiv⟩ := WfDvdMonoid.exists_irreducible_factor hu hf
  obtain ⟨c, hc⟩ := hg.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X (dvd_trans hgdiv hall)
  by_cases hc1 : c = 1
  · have he : f.natDegree = g.natDegree := by simpa [hc1] using hc
    exact (associated_of_dvd_of_natDegree_le hgdiv hf he.le).irreducible hg
  obtain ⟨q, hq, w, hw⟩ := Nat.exists_prime_and_dvd hc1
  have he : f.natDegree = q * (g.natDegree * w) := by rw [hc, hw]; ring
  have hqdiv : q ∣ f.natDegree := ⟨_, he⟩
  have hgd : g.natDegree ∣ f.natDegree / q := by
    rw [he, Nat.mul_div_cancel_left _ hq.pos]
    exact dvd_mul_right _ _
  exact False.elim (hg.not_isUnit ((htest q hq hqdiv).isUnit_of_dvd' hgdiv
    (hg.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.mp hgd)))

/-- Passing the Frobenius tests at a single prime proves rational irreducibility.
The leading-degree equality makes the statement applicable to the nonmonic polynomials
in Appendix C. -/
theorem irreducible_of_frobenius_reduction (H : ℤ[X]) (hprim : H.IsPrimitive)
    (p : ℕ) [Fact p.Prime] (hD : 0 < H.natDegree)
    (hdeg : (H.map (Int.castRingHom (ZMod p))).natDegree = H.natDegree)
    (hall : H.map (Int.castRingHom (ZMod p)) ∣ X ^ p ^ H.natDegree - X)
    (htest : ∀ q : ℕ, q.Prime → q ∣ H.natDegree →
      IsCoprime (H.map (Int.castRingHom (ZMod p))) (X ^ p ^ (H.natDegree / q) - X)) :
    Irreducible (H.map (Int.castRingHom ℚ)) := by
  let φ := Int.castRingHom (ZMod p)
  have hbar : Irreducible (H.map φ) := by
    apply irreducible_of_frobenius_tests
    · exact hdeg.symm ▸ hD
    · simpa [φ, hdeg, Nat.card_eq_fintype_card, ZMod.card] using hall
    · simpa [φ, hdeg, Nat.card_eq_fintype_card, ZMod.card] using htest
  by_contra hred
  obtain ⟨A, B, he, hA1, hA2⟩ := exists_factor_of_not_irreducible H hprim hD hred
  have hlc : φ H.leadingCoeff ≠ 0 := by
    rcases natDegree_map_eq_iff.mp hdeg with hp | h
    · exact hp
    · omega
  have preserve (F : ℤ[X]) (hf : F ∣ H) : (F.map φ).natDegree = F.natDegree := by
    apply natDegree_map_of_leadingCoeff_ne_zero
    rintro hz
    obtain ⟨G, hG⟩ := hf
    apply hlc
    rw [hG, leadingCoeff_mul, map_mul, hz, zero_mul]
  have ha := preserve A ⟨B, he⟩
  have hb := preserve B ⟨A, by simpa [mul_comm] using he⟩
  have hH : H ≠ 0 := by rintro rfl; simp at hD
  have hab : A ≠ 0 ∧ B ≠ 0 := mul_ne_zero_iff.mp (he ▸ hH)
  have hsum : H.natDegree = A.natDegree + B.natDegree := by rw [he, natDegree_mul hab.1 hab.2]
  have he' : H.map φ = A.map φ * B.map φ := by rw [he, Polynomial.map_mul]
  rcases hbar.isUnit_or_isUnit he' with h | h
  · have := natDegree_eq_zero_of_isUnit h
    omega
  · have := natDegree_eq_zero_of_isUnit h
    omega

end ArithmeticOfJacobiPolynomials
