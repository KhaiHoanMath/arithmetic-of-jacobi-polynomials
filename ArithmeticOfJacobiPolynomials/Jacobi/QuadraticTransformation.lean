/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.Shift
public import ArithmeticOfJacobiPolynomials.MainResults
public import ArithmeticOfJacobiPolynomials.External
public import Mathlib.Algebra.Polynomial.Expand

/-!
# The Gegenbauer–Jacobi bridge (5.33)

Proof of Corollary 1.7, first step: from the quadratic
transformations [DLMF, 18.7.15–18.7.16] (the cited `GegenbauerQuadraticTransformation`) and
the Jacobi reflection (`jacobiP_comp_neg_X`),
`F_{m,r,δ}(X) = (-1)^m 2^δ (r+1/2)_{m+δ}/(δ+1/2)_m · J_m(1 - 2X²)`,
`J_m = P_m^{(δ-1/2, r)}` (§5.7), and correspondingly
`Q_{m,r,δ}(T) = (same scalar) · J_m(1 - 2T)` for the polynomial `Q_{m,r,δ}` with
`F_{m,r,δ}(x) = Q_{m,r,δ}(x²)`.
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial

/-- The scalar `(-1)^m 2^δ (r+1/2)_{m+δ} / (δ+1/2)_m` of (5.33). -/
noncomputable def gegenbauerBridgeScalar (m r δ : ℕ) : ℚ :=
  (-1) ^ m * 2 ^ δ * (ascPochhammer ℚ (m + δ)).eval ((r : ℚ) + 1 / 2) /
    (ascPochhammer ℚ m).eval ((δ : ℚ) + 1 / 2)

theorem gegenbauerBridgeScalar_eq (m r δ : ℕ) : gegenbauerBridgeScalar m r δ =
    (-1) ^ m * 2 ^ δ * (ascPochhammer ℚ (m + δ)).eval ((r : ℚ) + 1 / 2) /
      (ascPochhammer ℚ m).eval ((δ : ℚ) + 1 / 2) := (rfl)

theorem gegenbauerBridgeScalar_ne_zero (m r δ : ℕ) : gegenbauerBridgeScalar m r δ ≠ 0 := by
  rw [gegenbauerBridgeScalar_eq]
  have h1 : (0 : ℚ) < (ascPochhammer ℚ (m + δ)).eval ((r : ℚ) + 1 / 2) :=
    ascPochhammer_pos _ _ (by positivity)
  have h2 : (0 : ℚ) < (ascPochhammer ℚ m).eval ((δ : ℚ) + 1 / 2) :=
    ascPochhammer_pos _ _ (by positivity)
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
    (pow_ne_zero _ (by norm_num))) h1.ne') h2.ne'

/-- **The bridge (5.33)** (§5.7), conditional on the cited quadratic
transformations [DLMF, 18.7.15–18.7.16]: for `δ ∈ {0,1}`,
`F_{m,r,δ} = (-1)^m 2^δ (r+1/2)_{m+δ}/(δ+1/2)_m · P_m^{(δ-1/2, r)}(1 - 2X²)`. -/
theorem reducedGegenbauer_eq_jacobiP_comp (hQ : GegenbauerQuadraticTransformation)
    (m r δ : ℕ) (hδ : δ ≤ 1) :
    reducedGegenbauer m r δ = C (gegenbauerBridgeScalar m r δ) *
      (jacobiP ((δ : ℚ) - 1 / 2) r m).comp (1 - 2 * polyX ^ 2) := by
  have hl0 : (0 : ℚ) < (r : ℚ) + 1 / 2 := by positivity
  obtain ⟨h0, h1⟩ := hQ.rat ((r : ℚ) + 1 / 2) m
  have hrefl : ∀ β : ℚ, (jacobiP ((r : ℚ) + 1 / 2 - 1 / 2) β m).comp (2 * polyX ^ 2 - 1) =
      C ((-1 : ℚ) ^ m) * (jacobiP β r m).comp (1 - 2 * polyX ^ 2) := by
    intro β
    have h := jacobiP_comp_neg_X β (r : ℚ) m
    rw [show (r : ℚ) + 1 / 2 - 1 / 2 = r by ring,
      show (2 * polyX ^ 2 - 1 : ℚ[X]) = (-polyX).comp (1 - 2 * polyX ^ 2) by simp, ← comp_assoc, h,
      mul_comp, C_comp]
  have hP : (ascPochhammer ℚ (m + 1)).eval ((1 : ℚ) / 2) =
      (1 / 2) * (ascPochhammer ℚ m).eval ((1 : ℚ) + 1 / 2) := by
    rw [ascPochhammer_succ_left, eval_mul, eval_X, eval_comp, eval_add, eval_X, eval_one,
      add_comm ((1 : ℚ) / 2) 1]
  have hP0 : (0 : ℚ) < (ascPochhammer ℚ m).eval ((1 : ℚ) + 1 / 2) :=
    ascPochhammer_pos _ _ (by positivity)
  have hP1 : (0 : ℚ) < (ascPochhammer ℚ m).eval ((1 : ℚ) / 2) :=
    ascPochhammer_pos _ _ (by positivity)
  rcases (show δ = 0 ∨ δ = 1 by omega) with rfl | rfl
  · rw [reducedGegenbauer_eq, add_zero, pow_zero, divByMonic_one, h0, hrefl, ← mul_assoc, ← C_mul,
      gegenbauerBridgeScalar_eq, show ((0 : ℕ) : ℚ) - 1 / 2 = -1 / 2 by norm_num]
    congr 2
    simp only [Nat.cast_zero, zero_add, add_zero, pow_zero, mul_one]
    ring
  · rw [reducedGegenbauer_eq, pow_one, h1, mul_assoc, mul_left_comm, mul_divByMonic_cancel_left _
      (monic_X), hrefl, ← mul_assoc, ← C_mul, gegenbauerBridgeScalar_eq,
      show ((1 : ℕ) : ℚ) - 1 / 2 = 1 / 2 by norm_num]
    congr 2
    rw [hP, Nat.cast_one]
    field_simp

/-- `Q_{m,r,δ}(T) = (-1)^m 2^δ (r+1/2)_{m+δ}/(δ+1/2)_m · P_m^{(δ-1/2, r)}(1 - 2T)`, where
`F_{m,r,δ}(x) = Q_{m,r,δ}(x²)` (conditional on [DLMF, 18.7.15–18.7.16]). -/
theorem reducedGegenbauerSquare_eq_jacobiP_comp (hQ : GegenbauerQuadraticTransformation)
    (m r δ : ℕ) (hδ : δ ≤ 1) :
    reducedGegenbauerSquare m r δ = C (gegenbauerBridgeScalar m r δ) *
      (jacobiP ((δ : ℚ) - 1 / 2) r m).comp (1 - 2 * polyX) := by
  have e : (1 - 2 * polyX : ℚ[X]).comp (polyX ^ 2) = 1 - 2 * polyX ^ 2 := by simp
  have hexp : C (gegenbauerBridgeScalar m r δ) *
      (jacobiP ((δ : ℚ) - 1 / 2) r m).comp (1 - 2 * polyX ^ 2) =
      expand ℚ 2 (C (gegenbauerBridgeScalar m r δ) *
        (jacobiP ((δ : ℚ) - 1 / 2) r m).comp (1 - 2 * polyX)) := by
    rw [map_mul, expand_C, expand_eq_comp_X_pow, comp_assoc, e]
  rw [reducedGegenbauerSquare_eq, reducedGegenbauer_eq_jacobiP_comp hQ m r δ hδ, hexp,
    contract_expand 2 two_ne_zero]

end ArithmeticOfJacobiPolynomials
