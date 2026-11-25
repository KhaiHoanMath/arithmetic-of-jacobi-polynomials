/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.KanekoZagier.SourceCutoffUpper

/-!
# Proposition B.1

For every `n ≥ 250000` and `λ, μ ∈ {-1, 1}`, `P_n^{(λ/3, μ/2)}` is irreducible over `ℚ`
(`kanekoZagier_explicit_cutoff`).

The proof follows the manuscript. The exact criterion (`kz_lower_bound_of_not_irreducible'`),
with `|T_{2,n} - T_{3,n}| < 3/10` (`abs_kzT2_sub_kzT3_lt`), bounds `S_n + log g_n` from below by
`n(L_* - E) - 6 log(12n)` (`kz_arch_source`, with the printed estimates `kz_nL_ge`,
`kz_logKappa_sub_ge`, `kzJ_le`, `kz_brace_le`). The content and carry calculation gives
`S_n + log g_n ≤ T_0(n) + 3 H(M)` (`kz_content_goodPrime_le`, with the small primes `5, 7, 11`
contributing `log 385` and the discarded primes `p ≥ 13`, `7p ≤ n`, bounded by `θ(n/7)`), where
`H(M) < 11 √n`
(`kzHigherPowerLogSum_lt_eleven_sqrt`) and `T_0(n)` is bounded through [Hanson, Theorem 1] and the
retained intervals by [BMOR, Theorem 1.9] for `n ≤ 10^13` (`kz_upper_small`, with `61 √n` for the
retained error) and by [BMOR, Corollary 1.7] for `n > 10^13` (`kz_upper_large`, with
`21n/1000`). With `L_* - E > 3/2` (`kzLStar_sub_kzE_gt_three_halves`) the two bounds are
incompatible, by the printed numerical comparison: below `10^13` it uses
`23/20 + log 3/7 + 95/√n + (12 + 6 log(12n))/n < 3/2`, above it
`23/20 + log 3/7 + 21/1000 + 33/√n + (12 + 6 log(12n))/n < 3/2`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Finset

theorem exp_thirtythree_gt : (120000000000000 : ℝ) < Real.exp 33 := by
  have h : Real.exp 1 ^ 33 = Real.exp 33 := by rw [Real.exp_one_pow]; norm_num
  rw [← h]
  calc (120000000000000 : ℝ) < (2.7182818283 : ℝ) ^ 33 := by norm_num
    _ < Real.exp 1 ^ 33 := pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)

/-- `√x ≤ x / 3000000` for `x ≥ 10^13`. -/
theorem sqrt_le_div_three_million {x : ℝ} (hx : 10 ^ 13 ≤ x) : √x ≤ x / 3000000 := by
  have h0 : (0 : ℝ) ≤ x := by linarith
  have hs := Real.sq_sqrt h0
  have h5 : (3000000 : ℝ) ≤ √x := by
    rw [Real.le_sqrt (by norm_num) h0]; linarith
  rw [le_div_iff₀ (by norm_num)]
  nlinarith

/-- **Proposition B.1**, conditional on [Hanson, Theorem 1],
[BMOR, Corollary 1.7 and Theorem 1.9], and the inputs of the archimedean inequality (4.17)
(`JacobiSimpleRealZeros` and `NewtonPolygonRootSlopes`): for every `n ≥ 250000` and
`λ, μ ∈ {-1, 1}`, `P_n^{(λ/3, μ/2)}` is irreducible over `ℚ`. -/
theorem kanekoZagier_explicit_cutoff (hZ : JacobiSimpleRealZeros) (hNP : NewtonPolygonRootSlopes)
    (hH : HansonLcmBound) (hT : BMORThetaBound) (hS : BMORThetaSmallBound) {l μ : ℤ}
    (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) {n : ℕ} (hn : 250000 ≤ n) :
    Irreducible (kanekoZagierJacobi l μ n) := by
  by_contra hred
  have hn1 : 1 ≤ n := by omega
  have hN : (250000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlow := kz_lower_bound_of_not_irreducible' hZ hNP hl hμ (by omega)
    ((abs_kzT2_sub_kzT3_lt hl hμ hn).le.trans (by norm_num)) hred
  have harch := kz_arch_source hl hμ hn1
  have hE := kzLStar_sub_kzE_gt_three_halves
  have hm := mul_le_mul_of_nonneg_left hE.le hn0.le
  have hl3 : Real.log 3 < 1.1 := lt_trans Real.log_three_lt_d9 (by norm_num)
  rcases le_or_gt n (10 ^ 13) with hs | hl'
  · have hup := kz_upper_small hH hS hl hμ hn hs
    -- the printed comparison `23/20 + log 3/7 + 95/√n + (12 + 6 log(12n))/n < 3/2`
    have h1log : 1 ≤ Real.log (12 * 250000) := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      linarith [Real.exp_one_lt_d9]
    have hmono := log_mul_div_le_of_le (c := 12) (n := n) (N := 250000) (by norm_num)
      (by norm_num) hN h1log
    have h15 : Real.log (12 * 250000) < 15 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      linarith [exp_fifteen_gt]
    rw [div_le_iff₀ hn0] at hmono
    have hsq := sqrt_le_div_five_hundred hN
    have hlog : Real.log (12 * n) ≤ 15 / 250000 * n := by
      have : Real.log (12 * 250000) / 250000 < 15 / 250000 :=
        div_lt_div_of_pos_right h15 (by norm_num)
      nlinarith
    nlinarith
  · have hup := kz_upper_large hH hT hl hμ hl'.le
    have hN' : (10 ^ 13 : ℝ) ≤ n := by exact_mod_cast hl'.le
    have h1log : 1 ≤ Real.log (12 * 10 ^ 13) := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      linarith [Real.exp_one_lt_d9]
    have hmono := log_mul_div_le_of_le (c := 12) (n := n) (N := 10 ^ 13) (by norm_num)
      (by norm_num) hN' h1log
    have h33 : Real.log (12 * 10 ^ 13) < 33 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      linarith [exp_thirtythree_gt]
    rw [div_le_iff₀ hn0] at hmono
    have hsq := sqrt_le_div_three_million hN'
    have hlog : Real.log (12 * n) ≤ 33 / 10 ^ 13 * n := by
      have : Real.log (12 * 10 ^ 13) / 10 ^ 13 < 33 / 10 ^ 13 :=
        div_lt_div_of_pos_right h33 (by norm_num)
      nlinarith
    nlinarith

end ArithmeticOfJacobiPolynomials
