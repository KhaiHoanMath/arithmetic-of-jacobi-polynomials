/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.LegendreDerivatives
public import ArithmeticOfJacobiPolynomials.Jacobi.SymmetricCriterion
public import ArithmeticOfJacobiPolynomials.Applications.FixedFactor
public import ArithmeticOfJacobiPolynomials.Applications.Jacobians
public import Mathlib.FieldTheory.Minpoly.IsConjRoot
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The nonzero critical points of `P_ℓ` form one Galois orbit (§1.2)

The manuscript reads the last two assertions of Theorem 1.5 as: for `ℓ ≥ 3` the nonzero critical
points of `P_ℓ` form a single rational Galois orbit. We prove this from the proved Theorem 1.5
(`legendreAndDerivativesStatement`): any two nonzero roots of `P_ℓ'` in `ℚ̄` are conjugate.
The Rolle interlacing half is `legendreP_criticalPoints_interlace` (Remarks/Prose).
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial

/-- **§1.2.** For `ℓ ≥ 3`, any two nonzero roots `ξ, η ∈ ℚ̄` of `P_ℓ'` are conjugate over
`ℚ`: there is `σ ∈ Gal(ℚ̄/ℚ)` with `σ ξ = η`. Conditional on the cited inputs of Theorem 1.5. -/
theorem exists_algEquiv_criticalPoint_legendreP (hI : FirstDerivativeIntegerInequalities)
    (hF : FirstDerivativeFactorDegreeChecks) (hDeng : DengLegendreIrreducibility)
    (hH : HansonLcmBound) (hZ : JacobiSimpleRealZeros)
    {ℓ : ℕ} (hℓ : 3 ≤ ℓ) {ξ η : AlgebraicClosure ℚ}
    (hξ : aeval ξ (derivative (legendreP ℓ)) = 0) (hξ0 : ξ ≠ 0)
    (hη : aeval η (derivative (legendreP ℓ)) = 0) (hη0 : η ≠ 0) :
    ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ξ = η := by
  obtain ⟨m, δ, hm, hδ, rfl⟩ : ∃ m δ : ℕ, 1 ≤ m ∧ δ ≤ 1 ∧ ℓ = 2 * m + δ + 1 :=
    ⟨(ℓ - 1) / 2, (ℓ - 1) % 2, by omega, by omega, by omega⟩
  set G := derivative (legendreP (2 * m + δ + 1)) /ₘ polyX ^ δ with hGdef
  have hfac : polyX ^ δ * G = derivative (legendreP (2 * m + δ + 1)) := by
    have h := X_pow_mul_reduced m 1 δ hδ
    simpa only [Function.iterate_one] using h
  have hirr : Irreducible G := by
    obtain ⟨-, -, h3, h4⟩ := legendreAndDerivativesStatement hI hF hDeng hH hZ m hm
    rcases (show δ = 0 ∨ δ = 1 by omega) with rfl | rfl
    · rw [hGdef, pow_zero, divByMonic_one]
      simpa using h3
    · rw [hGdef, pow_one, show 2 * m + 1 + 1 = 2 * m + 2 by ring]
      exact h4
  have hroot : ∀ z : AlgebraicClosure ℚ, z ≠ 0 →
      aeval z (derivative (legendreP (2 * m + δ + 1))) = 0 → aeval z G = 0 := by
    intro z hz h
    rw [← hfac, map_mul, map_pow, aeval_X] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hz)
  have hmξ := minpoly.eq_of_irreducible hirr (hroot ξ hξ0 hξ)
  have hmη := minpoly.eq_of_irreducible hirr (hroot η hη0 hη)
  have hconj : IsConjRoot ℚ η ξ := by
    change minpoly ℚ η = minpoly ℚ ξ
    rw [← hmξ, ← hmη]
  exact hconj.exists_algEquiv

/-- For `ℓ ≥ 3`, `P_ℓ'` has a nonzero root in `ℚ̄`, so the single orbit of
`exists_algEquiv_criticalPoint_legendreP` is nonempty. Conditional on the cited inputs of
Theorem 1.5. -/
theorem exists_criticalPoint_legendreP_ne_zero (hI : FirstDerivativeIntegerInequalities)
    (hF : FirstDerivativeFactorDegreeChecks) (hDeng : DengLegendreIrreducibility)
    (hH : HansonLcmBound) (hZ : JacobiSimpleRealZeros)
    {ℓ : ℕ} (hℓ : 3 ≤ ℓ) :
    ∃ ξ : AlgebraicClosure ℚ, aeval ξ (derivative (legendreP ℓ)) = 0 ∧ ξ ≠ 0 := by
  obtain ⟨m, δ, hm, hδ, rfl⟩ : ∃ m δ : ℕ, 1 ≤ m ∧ δ ≤ 1 ∧ ℓ = 2 * m + δ + 1 :=
    ⟨(ℓ - 1) / 2, (ℓ - 1) % 2, by omega, by omega, by omega⟩
  set G := derivative (legendreP (2 * m + δ + 1)) /ₘ polyX ^ δ with hGdef
  have hfac : polyX ^ δ * G = derivative (legendreP (2 * m + δ + 1)) := by
    have h := X_pow_mul_reduced m 1 δ hδ
    simpa only [Function.iterate_one] using h
  have hGF : G = C ((2 * 1 - 1).doubleFactorial : ℚ) * reducedGegenbauer m 1 δ := by
    have h := reducedDerivative_eq_C_mul_reducedGegenbauer m 1 δ hδ
    simpa only [Function.iterate_one] using h
  have hC : ((2 * 1 - 1).doubleFactorial : ℚ) = 1 := by decide
  rw [hC, C_1, one_mul] at hGF
  have hdeg : G.natDegree = 2 * m := by rw [hGF]; exact natDegree_reducedGegenbauer_eq_two_mul m 1 δ
  have hirr : Irreducible G := by
    obtain ⟨-, -, h3, h4⟩ := legendreAndDerivativesStatement hI hF hDeng hH hZ m hm
    rcases (show δ = 0 ∨ δ = 1 by omega) with rfl | rfl
    · rw [hGdef, pow_zero, divByMonic_one]
      simpa using h3
    · rw [hGdef, pow_one, show 2 * m + 1 + 1 = 2 * m + 2 by ring]
      exact h4
  have hGdeg : G.degree ≠ 0 := by
    rw [degree_eq_natDegree hirr.ne_zero, hdeg]
    exact_mod_cast (show 2 * m ≠ 0 by omega)
  obtain ⟨ξ, hξ⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure ℚ) G hGdeg
  refine ⟨ξ, ?_, ?_⟩
  · rw [← hfac, map_mul, hξ, mul_zero]
  · rintro rfl
    have h0 : G.IsRoot 0 := by
      have := hξ
      rw [aeval_def, eval₂_at_zero, map_eq_zero_iff _ (algebraMap ℚ _).injective,
        coeff_zero_eq_eval_zero] at this
      exact this
    have hX : polyX ∣ G := by simpa using dvd_iff_isRoot.mpr h0
    obtain ⟨q, hq⟩ := hX
    rcases hirr.isUnit_or_isUnit hq with h | h
    · exact not_isUnit_X h
    · have := natDegree_eq_zero_of_isUnit h
      have hq0 : q ≠ 0 := h.ne_zero
      rw [hq, natDegree_mul X_ne_zero hq0, natDegree_X, this] at hdeg
      omega

end ArithmeticOfJacobiPolynomials
