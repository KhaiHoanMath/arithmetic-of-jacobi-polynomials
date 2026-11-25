/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.SourceStieltjesWronskian
public import ArithmeticOfJacobiPolynomials.Jacobi.Wronskian

/-!
# Lemma 2.1 for rational parameters, from the Stieltjes-integral proof

`jacobi_wronskian_stieltjes` proves the Wronskian identity (2.2) for real parameters from the
Stieltjes transform `∫_0^1 P(s)(t-s)^{-k} w(s) ds` of the Jacobi weight, as in the manuscript.
The rational-parameter statements used by the arithmetic chapters are obtained by transporting
that identity along the injective ring map `ℚ → ℝ`: the Jacobi polynomial, the moment quotient and
the constant `C_n` commute with coefficient transport.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial

/-- Coefficient transport of the Jacobi polynomial. -/
theorem map_jacobiP_generic {K L : Type*} [Field K] [CharZero K] [Field L] [CharZero L]
    (φ : K →+* L) (α β : K) (n : ℕ) :
    (JacobiGeneric.jacobiP α β n).map φ = JacobiGeneric.jacobiP (φ α) (φ β) n := by
  simp only [JacobiGeneric.jacobiP_eq, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_sum, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_X, Polynomial.map_one, Ring.map_choose φ, map_mul, map_pow, map_div₀, map_one,
    map_ofNat, map_add, map_natCast]

theorem cast_eval_ascPochhammer (a : ℚ) (j : ℕ) :
    (((ascPochhammer ℚ j).eval a : ℚ) : ℝ) = (ascPochhammer ℝ j).eval (a : ℝ) := by
  rw [← ascPochhammer_map (algebraMap ℚ ℝ) j, eval_map]
  have := Polynomial.eval₂_at_apply (p := ascPochhammer ℚ j) (algebraMap ℚ ℝ) a
  simpa using this.symm

/-- Coefficient transport of `y_n`. -/
theorem map_jacobiShifted_real (α β : ℚ) (n : ℕ) :
    (jacobiShifted α β n).map (algebraMap ℚ ℝ) =
      JacobiGeneric.jacobiShifted (α : ℝ) (β : ℝ) n := by
  have h := map_jacobiP_generic (algebraMap ℚ ℝ) α β n
  rw [jacobiShifted_eq, JacobiGeneric.jacobiShifted_eq, Polynomial.map_comp]
  simp only [eq_ratCast] at h
  have e : jacobiP α β n = JacobiGeneric.jacobiP α β n := by
    rw [jacobiP_eq, JacobiGeneric.jacobiP_eq]
  rw [e, h]
  simp

/-- Coefficient transport of the moments. -/
theorem jacobiMoment_real (α β : ℚ) (j : ℕ) :
    ((jacobiMoment α β j : ℚ) : ℝ) = JacobiGeneric.jacobiMoment (α : ℝ) (β : ℝ) j := by
  rw [jacobiMoment_eq, JacobiGeneric.jacobiMoment_eq, Rat.cast_div, cast_eval_ascPochhammer,
    cast_eval_ascPochhammer]
  push_cast
  rfl

/-- Coefficient transport of `Q_n`. -/
theorem map_jacobiSecondPoly_real (α β : ℚ) (n : ℕ) :
    (jacobiSecondPoly α β n).map (algebraMap ℚ ℝ) =
      JacobiGeneric.jacobiSecondPoly (α : ℝ) (β : ℝ) n := by
  rw [jacobiSecondPoly_eq, JacobiGeneric.jacobiSecondPoly_eq, ← momentQuotient_jacobiMoment_map,
    map_jacobiShifted_real]
  congr
  funext j
  exact jacobiMoment_real α β j

/-- Coefficient transport of `C_n`. -/
theorem jacobiWronskianConstant_real (α β : ℚ) (n : ℕ) :
    ((jacobiWronskianConstant α β n : ℚ) : ℝ) =
      JacobiGeneric.jacobiWronskianConstant (α : ℝ) (β : ℝ) n := by
  rw [jacobiWronskianConstant_eq, JacobiGeneric.jacobiWronskianConstant_eq]
  simp only [Rat.cast_div, Rat.cast_mul, cast_eval_ascPochhammer, Rat.cast_natCast]
  push_cast
  rfl

/-- **Lemma 2.1, identity (2.2)**, rational parameters, from the Stieltjes-integral proof
`jacobi_wronskian_stieltjes`. -/
theorem jacobi_wronskian_source {α β : ℚ} (hα : -1 < α) (hβ : -1 < β) {n : ℕ} (hn : 1 ≤ n) :
    C (α + β + 1) * jacobiShifted α β n ^ 2 +
      X * (1 - X) * (derivative (jacobiShifted α β n) * jacobiSecondPoly α β n -
        jacobiShifted α β n * derivative (jacobiSecondPoly α β n)) +
      (C α - C (α + β) * X) * jacobiShifted α β n * jacobiSecondPoly α β n =
    C (jacobiWronskianConstant α β n) := by
  apply Polynomial.map_injective (algebraMap ℚ ℝ) (algebraMap ℚ ℝ).injective
  have h := JacobiGeneric.Real.jacobi_wronskian_stieltjes (α := (α : ℝ)) (β := (β : ℝ))
    (by exact_mod_cast hα) (by exact_mod_cast hβ) hn
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_one, ← derivative_map,
    map_jacobiShifted_real, map_jacobiSecondPoly_real, eq_ratCast, Rat.cast_add, Rat.cast_one,
    jacobiWronskianConstant_real]
  exact h

/-- **Lemma 2.1, root bound (2.4)** for rational parameters, from the Stieltjes-integral proof. -/
theorem jacobi_root_derivative_lower_source {α β : ℚ} (hα : -1 < α) (hβ : -1 < β) {n : ℕ}
    (hn : 1 ≤ n) {t : ℝ} (ht : aeval t (jacobiShifted α β n) = 0) :
    2 * Real.sqrt (jacobiWronskianConstant α β n) ≤
        |aeval t (derivative (jacobiShifted α β n))| ∧ 0 < t ∧ t < 1 := by
  have hα' : (-1 : ℝ) < α := by exact_mod_cast hα
  have hβ' : (-1 : ℝ) < β := by exact_mod_cast hβ
  have h0 : aeval t (JacobiGeneric.jacobiShifted (α : ℝ) (β : ℝ) n) = 0 := by
    rw [← map_jacobiShifted_real, aeval_def, Algebra.algebraMap_self, eval₂_id,
      eval_map_algebraMap]
    exact ht
  have hW := JacobiGeneric.Real.jacobi_wronskian_stieltjes hα' hβ' hn
  have key := JacobiGeneric.Real.jacobi_root_derivative_lower_of_wronskian hα' hβ' hn hW h0
  rw [← jacobiWronskianConstant_real] at key
  have e : aeval t (derivative (jacobiShifted α β n)) =
      aeval t (derivative (JacobiGeneric.jacobiShifted (α : ℝ) (β : ℝ) n)) := by
    rw [← map_jacobiShifted_real, ← eval_map_algebraMap, ← derivative_map, aeval_def,
      Algebra.algebraMap_self, eval₂_id]
  rw [e]
  exact key

end ArithmeticOfJacobiPolynomials
