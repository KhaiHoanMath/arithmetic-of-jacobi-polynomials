module

public import ArithmeticOfJacobiPolynomials.Polynomial.FactorDegrees
public import ArithmeticOfJacobiPolynomials.Verification.DerivativeCoeffs
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.Algebra.Polynomial.Reverse

/-! # Eisenstein certificates in either coefficient order

The primitive models in Appendix C need not be monic. When a prime divides all the
nonconstant coefficients, we apply Eisenstein's criterion to the reciprocal polynomial.
-/

public section

namespace ArithmeticOfJacobiPolynomials.DerivativeModel

open Polynomial

private theorem eisenstein_integer {f : ℤ[X]} (hprim : f.IsPrimitive) (hdeg : 0 < f.natDegree)
    {p : ℕ} (hp : p.Prime) (hlead : ¬ (p : ℤ) ∣ f.leadingCoeff)
    (hcoeff : ∀ i < f.natDegree, (p : ℤ) ∣ f.coeff i)
    (hconst : ¬ (p : ℤ) ^ 2 ∣ f.coeff 0) : Irreducible f := by
  let P : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hE : f.IsEisensteinAt P := by
    refine ⟨?_, fun {i} hi => Ideal.mem_span_singleton.mpr (hcoeff i hi), ?_⟩
    · exact fun h => hlead (Ideal.mem_span_singleton.mp h)
    · simpa [P, Ideal.span_singleton_pow, Ideal.mem_span_singleton] using hconst
  exact hE.irreducible ((Ideal.span_singleton_prime (Int.ofNat_ne_zero.mpr hp.ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp hp)) hprim hdeg

private theorem primitive_reverse {f : ℤ[X]} (h : f.IsPrimitive) : f.reverse.IsPrimitive := by
  intro r hr
  apply h r
  apply (C_dvd_iff_dvd_coeff r f).mpr
  intro i
  have := (C_dvd_iff_dvd_coeff r f.reverse).mp hr (revAt f.natDegree i)
  simpa [coeff_reverse] using this

private theorem degree_reverse_of_const {f : ℤ[X]} (h : f.coeff 0 ≠ 0) :
    f.reverse.natDegree = f.natDegree := by
  rw [reverse_natDegree, natTrailingDegree_eq_zero.mpr (.inr h), Nat.sub_zero]

/-- An Eisenstein check on either the coefficients of a primitive integral polynomial or
their reverse proves irreducibility over the rationals. -/
theorem irreducible_of_eisenstein_coeffs {f : ℤ[X]} (hprim : f.IsPrimitive)
    {D p : ℕ} (hD : f.natDegree = D) (hpos : 0 < D) (hp : p.Prime) (rev : Bool)
    (hlead : ¬ (p : ℤ) ∣ f.coeff (if rev then 0 else D))
    (hcoeff : ∀ i : Fin D, (p : ℤ) ∣ f.coeff (if rev then D - i.val else i.val))
    (hconst : ¬ (p : ℤ) ^ 2 ∣ f.coeff (if rev then D else 0)) :
    Irreducible (f.map (Int.castRingHom ℚ)) := by
  cases rev with
  | false =>
    apply (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp
    apply eisenstein_integer hprim (hD.symm ▸ hpos) hp
    · simpa [leadingCoeff, hD] using hlead
    · intro i hi
      exact hcoeff ⟨i, hD ▸ hi⟩
    · exact hconst
  | true =>
    have h0 : f.coeff 0 ≠ 0 := fun e => hlead (e ▸ dvd_zero _)
    have hr := degree_reverse_of_const h0
    have hi : Irreducible f.reverse := by
      apply eisenstein_integer (primitive_reverse hprim) (by omega) hp
      · simpa [reverse_leadingCoeff, trailingCoeff_eq_coeff_zero h0] using hlead
      · intro i h
        have hlt : i < D := by omega
        simpa [coeff_reverse, hD, revAt_le hlt.le] using hcoeff ⟨i, hlt⟩
      · simpa [coeff_zero_reverse, leadingCoeff, hD] using hconst
    by_contra h
    obtain ⟨a, b, hab, ha, habnd⟩ := exists_factor_of_not_irreducible f hprim (by omega) h
    have hcoeff0 : a.coeff 0 ≠ 0 ∧ b.coeff 0 ≠ 0 :=
      mul_ne_zero_iff.mp (by rwa [hab, mul_coeff_zero] at h0)
    have hsum : f.natDegree = a.natDegree + b.natDegree := by
      rw [hab, natDegree_mul (fun e => hcoeff0.1 (by simp [e])) (fun e => hcoeff0.2 (by simp [e]))]
    have hrev : f.reverse = a.reverse * b.reverse := by rw [hab, reverse_mul_of_domain]
    rcases hi.isUnit_or_isUnit hrev with u | u
    · have := natDegree_eq_zero_of_isUnit u
      rw [degree_reverse_of_const hcoeff0.1] at this
      omega
    · have := natDegree_eq_zero_of_isUnit u
      rw [degree_reverse_of_const hcoeff0.2] at this
      omega

end ArithmeticOfJacobiPolynomials.DerivativeModel
