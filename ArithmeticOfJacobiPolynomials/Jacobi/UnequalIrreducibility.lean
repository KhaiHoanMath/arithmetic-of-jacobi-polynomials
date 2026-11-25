/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.AsymmetricCriterion
public import ArithmeticOfJacobiPolynomials.Analysis.AsymmetricEnergy
public import ArithmeticOfJacobiPolynomials.Analysis.AsymmetricAsymptotics
public import ArithmeticOfJacobiPolynomials.Galois.GaloisBridge

/-!
# Irreducibility for unequal integral parameters (Theorem 3.1; Theorem 1.3, irreducibility)

* `ArithmeticOfJacobiPolynomials.irreducible_jacobiP_of_criterion`: **Theorem 3.1**
in the
  manuscript's form (3.5), with `c_{a,b}` of (3.4) (`asymmetricEnergyConstant`).
* `ArithmeticOfJacobiPolynomials.exists_forall_irreducible_jacobiP`: the irreducibility assertion of
  **Theorem 1.3**: for distinct nonnegative integers `a, b` there is `N` such that
  `P_n^{(a,b)}` is irreducible over `ℚ` for every `n ≥ N`.

Both are conditional on the cited `HansonLcmBound` ([Hanson, Theorem 1]),
`JacobiSimpleRealZeros`
([DLMF, §18.2(vi)]). The case `a < b` follows by the reflection
`P_n^{(b,a)}(-x) = (-1)^n P_n^{(a,b)}(x)`.
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset Real

/-- **Theorem 3.1.** Let `a > b ≥ 0`, `s = a+b`, `n = 2m+δ` with
`δ ∈ {0,1}`, `m ≥ 2s+10` and `A_δ(m) ≠ 0`. With `M = m+s+2`, `S = 2n+s+1`,
`T = ∏_{j=1}^{s}(n+j)`, `B = binom(n+a,a)` and `c_{a,b}` of (3.4), if
`n log 2 > (M + √S) log 3 + 3 log T + log |A_δ(m)| + log(8(m+1) S B D_δ(m) / (c_{a,b} √m))`,
then `P_n^{(a,b)}` is irreducible over `ℚ`. -/
theorem irreducible_jacobiP_of_criterion (hH : HansonLcmBound)
     (hZ : JacobiSimpleRealZeros) {a b m δ : ℕ} (hab : b < a)
    (hδ : δ ≤ 1) (hm : 2 * (a + b) + 10 ≤ m) (hA : (centralA a b δ).eval (m : ℤ) ≠ 0)
    (hcrit : (((m + (a + b) + 2 : ℕ) : ℝ) + √((2 * (2 * m + δ) + (a + b) + 1 : ℕ) : ℝ)) * log 3 +
        3 * log ((∏ j ∈ Icc 1 (a + b), (2 * m + δ + j) : ℕ) : ℝ) +
        log |(((centralA a b δ).eval (m : ℤ) : ℤ) : ℝ)| +
        log (8 * ((m : ℝ) + 1) * ((2 * (2 * m + δ) + (a + b) + 1 : ℕ) : ℝ) *
          ((2 * m + δ + a).choose a : ℝ) * (((centralD a b δ).eval (m : ℤ) : ℤ) : ℝ) /
            (asymmetricEnergyConstant a b * √(m : ℝ))) <
      ((2 * m + δ : ℕ) : ℝ) * log 2) :
    Irreducible (jacobiP a b (2 * m + δ)) := by
  have hm1 : 1 ≤ m := by omega
  have hc := asymmetricEnergyConstant_pos a b
  have hD : (0 : ℝ) < (((centralD a b δ).eval (m : ℤ) : ℤ) : ℝ) := by
    exact_mod_cast centralD_eval_pos a b δ m
  have hsm : (0 : ℝ) < √(m : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hm1)
  refine irreducible_jacobiP_of_criterion_of_gamma hH hZ hab hδ hm hA
    (γ := asymmetricEnergyConstant a b * √(m : ℝ) / (((centralD a b δ).eval (m : ℤ) : ℤ) : ℝ))
    (by positivity) (fun α hα hroot => asymmetric_gamma_lt_abs_derivative a b m δ hab hδ hm1 hA
      hα hroot) ?_
  rw [div_div_eq_mul_div]
  exact hcrit

/-- Irreducibility of `P_n^{(a,b)}` is symmetric in `(a, b)` (reflection). -/
theorem irreducible_jacobiP_comm (α β : ℚ) (n : ℕ) :
    Irreducible (jacobiP α β n) ↔ Irreducible (jacobiP β α n) := by
  have h := jacobiP_comp_neg_X α β n
  have e : jacobiP α β n = C ((-1 : ℚ) ^ n) * (jacobiP β α n).comp (C (-1) * polyX + C 0) := by
    rw [show (C (-1 : ℚ) * polyX + C 0) = -polyX by simp, h, ← mul_assoc, ← C_mul, ← mul_pow]
    norm_num
  rw [e]
  exact irreducible_C_mul_comp_affine_iff (jacobiP β α n) 0 (pow_ne_zero _ (by norm_num))
    (by norm_num)

/-- **Theorem 1.3, irreducibility.** For distinct nonnegative integers `a, b` there is `N` such
that `P_n^{(a,b)}` is irreducible over `ℚ` for every `n ≥ N`. -/
theorem exists_forall_irreducible_jacobiP (hH : HansonLcmBound)
     (hZ : JacobiSimpleRealZeros) {a b : ℕ} (hab : a ≠ b) :
    ∃ N : ℕ, ∀ n ≥ N, Irreducible (jacobiP a b n) := by
  wlog hlt : b < a generalizing a b
  · obtain ⟨N, hN⟩ := this hab.symm (by omega)
    exact ⟨N, fun n hn => (irreducible_jacobiP_comm _ _ n).mpr (hN n hn)⟩
  have hc := asymmetricEnergyConstant_pos a b
  obtain ⟨N0, h0⟩ := exists_forall_asymmetric_criterion a b 0 (by norm_num) hc
  obtain ⟨N1, h1⟩ := exists_forall_asymmetric_criterion a b 1 le_rfl hc
  obtain ⟨A0, hA0⟩ := exists_forall_centralA_ne_zero a b 0 hlt (by norm_num)
  obtain ⟨A1, hA1⟩ := exists_forall_centralA_ne_zero a b 1 hlt le_rfl
  set K := N0 + N1 + A0 + A1 + 2 * (a + b) + 10 with hK
  refine ⟨2 * K, fun n hn => ?_⟩
  obtain ⟨m, δ, hδ, rfl⟩ : ∃ m δ, δ ≤ 1 ∧ n = 2 * m + δ :=
    ⟨n / 2, n % 2, by omega, by omega⟩
  have hmK : K ≤ m := by omega
  have hm1 : 1 ≤ m := by omega
  have hsm : (0 : ℝ) < √(m : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hm1)
  rcases (show δ = 0 ∨ δ = 1 by omega) with rfl | rfl
  · exact irreducible_jacobiP_of_criterion_of_gamma hH hZ hlt (by norm_num) (by omega)
      (hA0 m (by omega))
      (γ := asymmetricEnergyConstant a b * √(m : ℝ) / (((centralD a b 0).eval (m : ℤ) : ℤ) : ℝ))
      (div_pos (mul_pos hc hsm) (by exact_mod_cast centralD_eval_pos a b 0 m))
      (fun α hα hroot => asymmetric_gamma_lt_abs_derivative a b m 0 hlt (by norm_num) hm1
        (hA0 m (by omega)) hα hroot) (h0 m (by omega))
  · exact irreducible_jacobiP_of_criterion_of_gamma hH hZ hlt le_rfl (by omega)
      (hA1 m (by omega))
      (γ := asymmetricEnergyConstant a b * √(m : ℝ) / (((centralD a b 1).eval (m : ℤ) : ℤ) : ℝ))
      (div_pos (mul_pos hc hsm) (by exact_mod_cast centralD_eval_pos a b 1 m))
      (fun α hα hroot => asymmetric_gamma_lt_abs_derivative a b m 1 hlt le_rfl hm1
        (hA1 m (by omega)) hα hroot) (h1 m (by omega))

end ArithmeticOfJacobiPolynomials
