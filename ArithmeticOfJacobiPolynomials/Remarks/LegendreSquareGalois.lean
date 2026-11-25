/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Remarks.DerivativeOrders
public import ArithmeticOfJacobiPolynomials.Galois.LegendreGaloisAll
public import ArithmeticOfJacobiPolynomials.Galois.GaloisBridge

/-!
# The quotient polynomials `Q_{m,0,δ}` in every degree

After Corollary 1.7 the manuscript notes that for `r = 0` and `E = ℚ` Theorem 1.2 gives every
degree. For the polynomial `Q_{m,0,δ}` with `F_{m,0,δ}(x) = Q_{m,0,δ}(x²)` this means
`Gal(Q_{m,0,δ}/ℚ) = S_m` for every `m ≥ 1` (`galoisGroupIsSymmetric_reducedGegenbauerSquare_zero`):
`Q_{m,0,δ}(T)` is a nonzero multiple of `J_m^ε(-T)` (5.14), `J_m^ε` is irreducible by Deng's
theorem and Theorem 5.9, which also gives `S_m` as its group.
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial

/-- `Q_{m,0,δ}(T) = ((-2)^m m!)⁻¹ J_m^ε(-T)` with `ε = 2δ - 1`. -/
theorem reducedGegenbauerSquare_zero_eq (m δ : ℕ) (hδ : δ ≤ 1) :
    reducedGegenbauerSquare m 0 δ =
      C ((-2) ^ m * (m.factorial : ℚ))⁻¹ *
        ((legendreJ (2 * (δ : ℤ) - 1) m).map (Int.castRingHom ℚ)).comp (C (-1) * polyX + C 0) := by
  have hk : ((-2 : ℚ) ^ m * m.factorial) ≠ 0 := by positivity
  have hJL := legendreJ_comp_neg_X_sq m δ hδ
  have hL : reducedLegendre m δ = expand ℚ 2 (C ((-2) ^ m * (m.factorial : ℚ))⁻¹ *
      ((legendreJ (2 * (δ : ℤ) - 1) m).map (Int.castRingHom ℚ)).comp (C (-1) * polyX + C 0)) := by
    rw [map_mul, expand_C, expand_eq_comp_X_pow, comp_assoc]
    have e : (C (-1 : ℚ) * polyX + C 0).comp (polyX ^ 2) = -polyX ^ 2 := by simp
    rw [e, hJL, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hk, C_1, one_mul]
  rw [reducedGegenbauerSquare_eq, reducedGegenbauer_zero_eq, hL, contract_expand 2 two_ne_zero]

/-- **`Gal(Q_{m,0,δ}/ℚ) = S_m` in every degree** (remark after Corollary 1.7). Conditional on the
cited inputs of Theorem 1.2. -/
theorem galoisGroupIsSymmetric_reducedGegenbauerSquare_zero (hDeng : DengLegendreIrreducibility)
    (hBMOR : BMORPrimeCountingBound) (hBT : BrunTitchmarshInequality)
    (hJones : JonesCycleTheorem) (hCHL : CullinanHajirLegendreGalois)
    (hCHL4 : PrimesModFourInDyadicInterval) {m δ : ℕ} (hm : 1 ≤ m) (hδ : δ ≤ 1) :
    GaloisGroupIsSymmetric (reducedGegenbauerSquare m 0 δ) := by
  have hε : 2 * (δ : ℤ) - 1 = 1 ∨ 2 * (δ : ℤ) - 1 = -1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hδ with h | h <;> simp [h]
  have hL : Irreducible (reducedLegendre m δ) := by
    obtain ⟨h0, h1⟩ := hDeng m hm
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hδ with h | h <;> subst h <;> assumption
  have hJ := (irreducible_legendreJ_iff_irreducible_reducedLegendre hBMOR hBT hJones hCHL hCHL4
    hδ hm).mpr hL
  have hS := galoisGroupIsSymmetric_legendreJ hBMOR hBT hJones hCHL hε hm hJ
  have hk : ((-2 : ℚ) ^ m * m.factorial)⁻¹ ≠ 0 := by positivity
  rw [reducedGegenbauerSquare_zero_eq m δ hδ]
  exact GaloisGroupIsSymmetric.affine _ _ hk (by norm_num) hS

end ArithmeticOfJacobiPolynomials
