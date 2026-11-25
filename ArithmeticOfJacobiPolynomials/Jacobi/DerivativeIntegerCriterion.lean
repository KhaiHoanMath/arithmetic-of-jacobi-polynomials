/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.SymmetricIrreducibility
public import ArithmeticOfJacobiPolynomials.Analysis.SymmetricResultantBounds
public import ArithmeticOfJacobiPolynomials.Jacobi.LegendreDerivativeData

/-!
# Lemma C.2: from the integer inequality (C.2) to irreducibility (hand reduction)

For `n = 2m + δ` with `δ ∈ {0,1}` and `m ≥ 4`, the sufficient condition of Theorem 3.4 with
`r = 1` is exactly the integer inequality (C.2) `16^m V² > 64 m (m+1)² Z² U²`
(Appendix C.2), where `K = m + 1` and `A_{≤m} = U/V`; exponentiating and
squaring the criterion gives (C.2). This file proves that reduction. The inequality itself, for
the `318` pairs `(m, δ)` with `m ∉ E_δ`, is the computed statement
`FirstDerivativeIntegerInequalities` of
`ArithmeticOfJacobiPolynomials.Jacobi.LegendreDerivativeData`.

* `ArithmeticOfJacobiPolynomials.FirstDerivativeCriterion.exact_criterion_of_integer_inequality`:
(C.2) implies
  the hypothesis of
  `ArithmeticOfJacobiPolynomials.irreducible_reducedDerivative_of_exact_criterion` for `r = 1`;
* `ArithmeticOfJacobiPolynomials.irreducible_derivative_legendreP_of_integer_inequality`: (C.2) and
`m ≥ 4`
  imply that `P'_{2m+δ+1}/x^δ` is irreducible over `ℚ` (conditional on `JacobiSimpleRealZeros`;
  the interval Vandermonde bound `intervalVandermondeBound` is proved).
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset Real

namespace FirstDerivativeCriterion

/-! ### The bridge from the integer inequality (C.2) to the exact criterion -/

/-- `log ∏_{p ∈ s} p^{e(p)} = ∑_{p ∈ s} e(p) log p` for a finite set of primes. -/
theorem log_natCast_prod_pow (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (e : ℕ → ℕ) :
    log ((∏ p ∈ s, p ^ e p : ℕ) : ℝ) = ∑ p ∈ s, (e p : ℝ) * log p := by
  rw [Nat.cast_prod, Real.log_prod]
  · exact sum_congr rfl fun p _ => by rw [Nat.cast_pow, Real.log_pow]
  · intro p hp
    exact_mod_cast (pow_pos (hs p hp).pos _).ne'

theorem mem_primes_le {m p : ℕ} (hp : p ∈ (range (m + 1)).filter Nat.Prime) : p.Prime :=
  (mem_filter.mp hp).2

theorem partV_pos (m δ : ℕ) : 0 < partV m δ := by
  rw [partV_eq]
  exact prod_pos fun p hp => pow_pos (mem_primes_le hp).pos _

theorem partU_pos (m δ : ℕ) : 0 < partU m δ := by
  rw [partU_eq]
  exact prod_pos fun p hp => pow_pos (mem_primes_le hp).pos _

theorem partZ_pos (m δ : ℕ) : 0 < partZ m δ := by
  rw [partZ_eq]
  exact prod_pos fun p hp => pow_pos (mem_primes_le hp).pos _

/-- `Ψ_m(2n+3) = log Z`. -/
theorem primePowerLogSum_eq_log_partZ (m δ : ℕ) :
    primePowerLogSum m ((2 * (2 * m + δ) + 2 * 1 + 1 : ℕ) : ℝ) = log (partZ m δ) := by
  have h3 : 2 * (2 * m + δ) + 2 * 1 + 1 = 2 * (2 * m + δ) + 3 := by ring
  rw [h3, primePowerLogSum_natCast_eq, partZ_eq,
    log_natCast_prod_pow _ (fun p hp => mem_primes_le hp)]

/-- `log A_{≤m} = log U - log V` for `A = (n+1)/(n+2)` (the case `r = 1`). -/
theorem log_primeTruncation_eq (m δ : ℕ) :
    log (primeTruncation (symmetricRatio (2 * m + δ) 1) m) =
      log (partU m δ) - log (partV m δ) := by
  rw [log_primeTruncation, symmetricRatio_one, partU_eq, partV_eq,
    log_natCast_prod_pow _ (fun p hp => mem_primes_le hp),
    log_natCast_prod_pow _ (fun p hp => mem_primes_le hp), ← sum_sub_distrib]
  refine sum_congr rfl fun p hp => ?_
  have := Fact.mk (mem_primes_le hp)
  have e1 : padicValRat p ((2 * m + δ + 1 : ℕ) : ℚ) = padicValNat p (2 * m + δ + 1) :=
    padicValRat.of_nat
  have e2 : padicValRat p ((2 * m + δ + 2 : ℕ) : ℚ) = padicValNat p (2 * m + δ + 2) :=
    padicValRat.of_nat
  rw [padicValRat.div (q := ((2 * m + δ + 1 : ℕ) : ℚ)) (r := ((2 * m + δ + 2 : ℕ) : ℚ))
    (by positivity) (by positivity), e1, e2, Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
  ring

/-- **Integer form (C.2) of the exact criterion (Appendix C.2).** If
`16^m V^2 > 64 m (m+1)^2 Z^2 U^2`, then the exact criterion (3.13) of Theorem 3.4 holds for
`r = 1`, `n = 2m + δ`: `Ψ_m(2n+3) + log(8√m) + log(m+1) + log A_{≤m} < m log 4`. -/
theorem exact_criterion_of_integer_inequality {m δ : ℕ} (hm : 1 ≤ m)
    (hlt : 64 * m * (m + 1) ^ 2 * partZ m δ ^ 2 * partU m δ ^ 2 < 16 ^ m * partV m δ ^ 2) :
    primePowerLogSum m ((2 * (2 * m + δ) + 2 * 1 + 1 : ℕ) : ℝ) + log (8 * √(m : ℝ)) +
        log ((m + 1).choose 1 : ℝ) + log (primeTruncation (symmetricRatio (2 * m + δ) 1) m) <
      m * log 4 := by
  rw [primePowerLogSum_eq_log_partZ, log_primeTruncation_eq, Nat.choose_one_right]
  have hZ : (0 : ℝ) < partZ m δ := by exact_mod_cast partZ_pos m δ
  have hU : (0 : ℝ) < partU m δ := by exact_mod_cast partU_pos m δ
  have hV : (0 : ℝ) < partV m δ := by exact_mod_cast partV_pos m δ
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : (0 : ℝ) < √(m : ℝ) := Real.sqrt_pos.mpr hm0
  have hlt' : (64 * m * (m + 1) ^ 2 * partZ m δ ^ 2 * partU m δ ^ 2 : ℝ) <
      16 ^ m * partV m δ ^ 2 := by exact_mod_cast hlt
  have key : (partZ m δ : ℝ) * partU m δ * ((m : ℝ) + 1) * (8 * √(m : ℝ)) <
      4 ^ m * partV m δ := by
    refine lt_of_pow_lt_pow_left₀ 2 (by positivity) ?_
    have e1 : ((partZ m δ : ℝ) * partU m δ * ((m : ℝ) + 1) * (8 * √(m : ℝ))) ^ 2 =
        64 * m * (m + 1) ^ 2 * partZ m δ ^ 2 * partU m δ ^ 2 := by
      have := Real.sq_sqrt hm0.le
      calc _ = (partZ m δ : ℝ) ^ 2 * partU m δ ^ 2 * ((m : ℝ) + 1) ^ 2 * 64 *
            (√(m : ℝ)) ^ 2 := by ring
        _ = _ := by rw [this]; ring
    have e2 : ((4 : ℝ) ^ m * partV m δ) ^ 2 = 16 ^ m * partV m δ ^ 2 := by
      rw [mul_pow, ← pow_mul, mul_comm m 2, pow_mul]
      norm_num
    rw [e1, e2]
    exact hlt'
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have h8 : (0 : ℝ) < 8 * √(m : ℝ) := mul_pos (by norm_num) hs
  have hlog := Real.log_lt_log (mul_pos (mul_pos (mul_pos hZ hU) hm1) h8) key
  rw [Real.log_mul (mul_pos (mul_pos hZ hU) hm1).ne' h8.ne',
    Real.log_mul (mul_pos hZ hU).ne' hm1.ne', Real.log_mul hZ.ne' hU.ne',
    Real.log_mul (pow_pos (by norm_num : (0 : ℝ) < 4) m).ne' hV.ne', Real.log_pow] at hlog
  push_cast
  linarith

/-- **The converse of `exact_criterion_of_integer_inequality`.** The exact criterion (3.13) of
Theorem 3.4 for `r = 1`, `n = 2m + δ` is *equivalent* to the integer inequality (C.2): the proof of
Lemma C.2 says that the sufficient condition "is exactly" (C.2) (exponentiate and square). -/
theorem exact_criterion_iff_integer_inequality {m δ : ℕ} (hm : 1 ≤ m) :
    (primePowerLogSum m ((2 * (2 * m + δ) + 2 * 1 + 1 : ℕ) : ℝ) + log (8 * √(m : ℝ)) +
        log ((m + 1).choose 1 : ℝ) + log (primeTruncation (symmetricRatio (2 * m + δ) 1) m) <
      m * log 4) ↔
    64 * m * (m + 1) ^ 2 * partZ m δ ^ 2 * partU m δ ^ 2 < 16 ^ m * partV m δ ^ 2 := by
  refine ⟨fun h => ?_, exact_criterion_of_integer_inequality hm⟩
  rw [primePowerLogSum_eq_log_partZ, log_primeTruncation_eq, Nat.choose_one_right] at h
  have hZ : (0 : ℝ) < partZ m δ := by exact_mod_cast partZ_pos m δ
  have hU : (0 : ℝ) < partU m δ := by exact_mod_cast partU_pos m δ
  have hV : (0 : ℝ) < partV m δ := by exact_mod_cast partV_pos m δ
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : (0 : ℝ) < √(m : ℝ) := Real.sqrt_pos.mpr hm0
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have h8 : (0 : ℝ) < 8 * √(m : ℝ) := mul_pos (by norm_num) hs
  have hA : (0 : ℝ) < (partZ m δ : ℝ) * partU m δ * ((m : ℝ) + 1) * (8 * √(m : ℝ)) :=
    mul_pos (mul_pos (mul_pos hZ hU) hm1) h8
  have hB : (0 : ℝ) < 4 ^ m * partV m δ := mul_pos (pow_pos (by norm_num) m) hV
  have hlog : log ((partZ m δ : ℝ) * partU m δ * ((m : ℝ) + 1) * (8 * √(m : ℝ))) <
      log (4 ^ m * partV m δ) := by
    rw [Real.log_mul (mul_pos (mul_pos hZ hU) hm1).ne' h8.ne',
      Real.log_mul (mul_pos hZ hU).ne' hm1.ne', Real.log_mul hZ.ne' hU.ne',
      Real.log_mul (pow_pos (by norm_num : (0 : ℝ) < 4) m).ne' hV.ne', Real.log_pow]
    push_cast at h
    linarith
  have key := (Real.log_lt_log_iff hA hB).mp hlog
  have hsq := pow_lt_pow_left₀ key hA.le (two_ne_zero)
  have e1 : ((partZ m δ : ℝ) * partU m δ * ((m : ℝ) + 1) * (8 * √(m : ℝ))) ^ 2 =
      64 * m * (m + 1) ^ 2 * partZ m δ ^ 2 * partU m δ ^ 2 := by
    have := Real.sq_sqrt hm0.le
    calc _ = (partZ m δ : ℝ) ^ 2 * partU m δ ^ 2 * ((m : ℝ) + 1) ^ 2 * 64 *
          (√(m : ℝ)) ^ 2 := by ring
      _ = _ := by rw [this]; ring
  have e2 : ((4 : ℝ) ^ m * partV m δ) ^ 2 = 16 ^ m * partV m δ ^ 2 := by
    rw [mul_pow, ← pow_mul, mul_comm m 2, pow_mul]
    norm_num
  rw [e1, e2] at hsq
  exact_mod_cast hsq

end FirstDerivativeCriterion

open FirstDerivativeCriterion in
/-- **Theorem 3.4 with `r = 1` in the integer form (C.2).** For `m ≥ 4` and `δ ≤ 1`, if
`16^m V^2 > 64 m (m+1)^2 Z^2 U^2`, then `P'_{2m+δ+1}/x^δ` is irreducible over `ℚ`. Conditional
on `JacobiSimpleRealZeros`; Lemma 2.5 supplies the interval bound.
([DLMF, §18.2(vi)]). -/
theorem irreducible_derivative_legendreP_of_integer_inequality (hZ : JacobiSimpleRealZeros)
    {m δ : ℕ} (hδ : δ ≤ 1) (hm : 4 ≤ m)
    (hlt : 64 * m * (m + 1) ^ 2 * partZ m δ ^ 2 * partU m δ ^ 2 < 16 ^ m * partV m δ ^ 2) :
    Irreducible (derivative (legendreP (2 * m + δ + 1)) /ₘ polyX ^ δ) := by
  have h := irreducible_reducedDerivative_of_exact_criterion hZ (r := 1) hδ
    (max_le (by omega) hm) (exact_criterion_of_integer_inequality (by omega) hlt)
  simpa using h

end ArithmeticOfJacobiPolynomials
