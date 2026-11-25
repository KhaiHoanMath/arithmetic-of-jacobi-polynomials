/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.KanekoZagier.FiniteCriterion
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Appendix B: the common reduction of Propositions B.1 and B.2

Propositions B.1 and B.2 both start from the exact
criterion of Proposition 4.8 with the possible factor degree eliminated. This file proves that
step, for `λ, μ ∈ {-1, 1}` (the argument `l` is `λ`):

* `one_third_le_jacobiWronskianConstant_kz` — the Wronskian constant satisfies `C_n ≥ 1/3`
  (Appendix B.1, through `C_{m+1}/C_m = 1 + αβ/((m+1)(m+c+1))`, `c = α + β`).
* `kzCriterionFn_eq_add` — `ℋ_n(z) = Λ_n + (log 2 + log √C_n) + (a_n z + 2 log 2 / z - log z)`
  with `Λ_n = log κ_n - log g_n - J_n + n(L_n - T_{2,n} - T_{3,n} - E) - 4 log 2` and
  `a_n = T_{2,n} + T_{3,n} + E - 2 L_n + 2 log 2` (`kzSlope`).
* `kzSlope_eq_cosh` — `a_n = E - 2 log cosh((T_{2,n} - T_{3,n})/2)`, and
  `half_lt_kzSlope` — `a_n > 1/2` whenever `|T_{2,n} - T_{3,n}| ≤ 9/10`.
* `kz_lower_bound_of_not_irreducible` — if `n ≥ 11`, (4.17) holds at `n`,
  `|T_{2,n} - T_{3,n}| ≤ 9/10` and `P_n^{(λ/3, μ/2)}` is reducible, then
  `S_n + log g_n > log κ_n - J_n + n(L_n - T_{2,n} - T_{3,n} - E) - 4 log 2`.

This is the first inequality of the chain proving (Appendix B.1) in Proposition B.1 (where
`|T_{2,n} - T_{3,n}| < 3/10`), and the elimination of `k` in the proof of Proposition B.2.
The exact inequality (4.17) of Proposition 4.7 enters as the hypothesis
`KanekoZagierArchimedeanBound l μ n`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset

/-! ### The Wronskian constant -/

theorem jacobiWronskianConstant_zero (α β : ℚ) : jacobiWronskianConstant α β 0 = 1 := by
  rw [jacobiWronskianConstant_eq]
  simp

theorem jacobiWronskianConstant_one (α β : ℚ) :
    jacobiWronskianConstant α β 1 = (α + 1) * (β + 1) := by
  rw [jacobiWronskianConstant_eq]
  simp

/-- `C_{m+1} = C_m (α+1+m)(β+1+m) / ((m+1)(α+β+1+m))` for `m ≥ 1`. -/
theorem jacobiWronskianConstant_succ {α β : ℚ} (hα : -1 < α) (hβ : -1 < β) (m : ℕ)
    (hm : 1 ≤ m) : jacobiWronskianConstant α β (m + 1) = jacobiWronskianConstant α β m *
      ((α + 1 + m) * (β + 1 + m) / ((m + 1) * (α + β + 1 + m))) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hD := ascPochhammer_eval_pos_of_pos k (show (0 : ℚ) < α + β + 2 by linarith)
  have hk : (0 : ℚ) ≤ k := Nat.cast_nonneg k
  have hs : α + β + 2 + (k : ℚ) ≠ 0 := by linarith
  have hs' : α + β + 1 + ((k : ℚ) + 1) ≠ 0 := by linarith
  have hk2 : (k : ℚ) + 1 + 1 ≠ 0 := by linarith
  have hf : ((k + 1).factorial : ℚ) ≠ 0 := by positivity
  have hD' := hD.ne'
  rw [jacobiWronskianConstant_eq, jacobiWronskianConstant_eq, show k + 1 + 1 - 1 = k + 1 by omega,
    show k + 1 - 1 = k by omega, ascPochhammer_succ_eval (k + 1) (α + 1),
    ascPochhammer_succ_eval (k + 1) (β + 1), ascPochhammer_succ_eval k (α + β + 2),
    Nat.factorial_succ (k + 1)]
  push_cast
  field_simp
  ring

theorem jacobiWronskianConstant_ge_of_mul_nonneg {α β : ℚ} (hα : -1 < α) (hβ : -1 < β)
    (hab : 0 ≤ α * β) (h1 : 1 / 3 ≤ (α + 1) * (β + 1)) (n : ℕ) (hn : 1 ≤ n) :
    1 / 3 ≤ jacobiWronskianConstant α β n := by
  induction n, hn using Nat.le_induction with
  | base => rw [jacobiWronskianConstant_one]; exact h1
  | succ m hm ih =>
    rw [jacobiWronskianConstant_succ hα hβ m hm]
    have hm0 : (1 : ℚ) ≤ m := by exact_mod_cast hm
    have hden : 0 < ((m : ℚ) + 1) * (α + β + 1 + m) := mul_pos (by linarith) (by linarith)
    have hnum : (α + 1 + m) * (β + 1 + m) = ((m : ℚ) + 1) * (α + β + 1 + m) + α * β := by ring
    have hr : 1 ≤ (α + 1 + m) * (β + 1 + m) / (((m : ℚ) + 1) * (α + β + 1 + m)) := by
      rw [le_div_iff₀ hden, one_mul, hnum]
      linarith
    calc (1 : ℚ) / 3 ≤ jacobiWronskianConstant α β m := ih
      _ ≤ _ := le_mul_of_one_le_right (by linarith) hr

theorem jacobiWronskianConstant_ge_of_mul_eq {α β : ℚ} (hα : -1 < α) (hβ : -1 < β)
    (hab : α * β = -1 / 6) (hc : -1 / 6 ≤ α + β) (n : ℕ) (hn : 1 ≤ n) :
    5 / 9 * ((5 * (n : ℚ) + 1) / (5 * n)) ≤ jacobiWronskianConstant α β n := by
  induction n, hn using Nat.le_induction with
  | base =>
    have e : (α + 1) * (β + 1) = α * β + (α + β) + 1 := by ring
    have e' : (5 : ℚ) / 9 * ((5 * ((1 : ℕ) : ℚ) + 1) / (5 * ((1 : ℕ) : ℚ))) = 2 / 3 := by norm_num
    rw [jacobiWronskianConstant_one, e', e, hab]
    linarith
  | succ m hm ih =>
    rw [jacobiWronskianConstant_succ hα hβ m hm]
    have hm1 : (1 : ℚ) ≤ m := by exact_mod_cast hm
    have hden : 0 < ((m : ℚ) + 1) * (α + β + 1 + m) := mul_pos (by linarith) (by linarith)
    have hnum : (α + 1 + m) * (β + 1 + m) = ((m : ℚ) + 1) * (α + β + 1 + m) + α * β := by ring
    have hr0 : 0 ≤ (α + 1 + m) * (β + 1 + m) / (((m : ℚ) + 1) * (α + β + 1 + m)) := by
      refine div_nonneg ?_ hden.le
      rw [hnum, hab]
      nlinarith
    have h5m : (0 : ℚ) < 5 * m := by linarith
    have hinner : (5 * ((m : ℚ) + 1) + 1) / (5 * ((m : ℚ) + 1)) ≤
        (5 * (m : ℚ) + 1) / (5 * m) *
          ((α + 1 + m) * (β + 1 + m) / (((m : ℚ) + 1) * (α + β + 1 + m))) := by
      rw [div_mul_div_comm, div_le_div_iff₀ (by linarith) (mul_pos h5m hden), hnum, hab]
      nlinarith [mul_nonneg (show (0 : ℚ) ≤ m + 1 by linarith)
        (show (0 : ℚ) ≤ α + β + (m + 5) / 6 by linarith)]
    calc 5 / 9 * ((5 * ((m + 1 : ℕ) : ℚ) + 1) / (5 * ((m + 1 : ℕ) : ℚ)))
        = 5 / 9 * ((5 * ((m : ℚ) + 1) + 1) / (5 * ((m : ℚ) + 1))) := by push_cast; ring
      _ ≤ 5 / 9 * ((5 * (m : ℚ) + 1) / (5 * m) *
          ((α + 1 + m) * (β + 1 + m) / (((m : ℚ) + 1) * (α + β + 1 + m)))) :=
        mul_le_mul_of_nonneg_left hinner (by norm_num)
      _ = 5 / 9 * ((5 * (m : ℚ) + 1) / (5 * m)) *
          ((α + 1 + m) * (β + 1 + m) / (((m : ℚ) + 1) * (α + β + 1 + m))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ih hr0

/-- **`C_n ≥ 1/3`** (Appendix B.1) for the four Kaneko–Zagier parameter pairs. -/
theorem one_third_le_jacobiWronskianConstant_kz {l μ : ℤ} (hl : l = 1 ∨ l = -1)
    (hμ : μ = 1 ∨ μ = -1) (n : ℕ) :
    1 / 3 ≤ jacobiWronskianConstant ((l : ℚ) / 3) ((μ : ℚ) / 2) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [jacobiWronskianConstant_zero]; norm_num
  have hα := kz_alpha_gt hl
  have hβ := kz_beta_gt hμ
  have h59 : ∀ α β : ℚ, -1 < α → -1 < β → α * β = -1 / 6 → -1 / 6 ≤ α + β →
      1 / 3 ≤ jacobiWronskianConstant α β n := by
    intro α β hα hβ hab hc
    have h := jacobiWronskianConstant_ge_of_mul_eq hα hβ hab hc n hn
    have hn1 : (1 : ℚ) ≤ n := by exact_mod_cast hn
    have hq : 1 ≤ (5 * (n : ℚ) + 1) / (5 * n) := by
      rw [le_div_iff₀ (by linarith)]; linarith
    nlinarith
  rcases hl with rfl | rfl <;> rcases hμ with rfl | rfl
  · exact jacobiWronskianConstant_ge_of_mul_nonneg hα hβ (by norm_num) (by norm_num) n hn
  · exact h59 _ _ hα hβ (by norm_num) (by norm_num)
  · exact h59 _ _ hα hβ (by norm_num) (by norm_num)
  · exact jacobiWronskianConstant_ge_of_mul_nonneg hα hβ (by norm_num) (by norm_num) n hn

/-- `log 2 + log √C_n ≥ 0`, i.e. `2 √C_n ≥ 1`. -/
theorem log_two_add_log_sqrt_kzWronskian_nonneg {l μ : ℤ} (hl : l = 1 ∨ l = -1)
    (hμ : μ = 1 ∨ μ = -1) (n : ℕ) :
    0 ≤ Real.log 2 +
      Real.log √((jacobiWronskianConstant ((l : ℚ) / 3) ((μ : ℚ) / 2) n : ℚ) : ℝ) := by
  have hC : ((1 : ℚ) / 3 : ℝ) ≤
      ((jacobiWronskianConstant ((l : ℚ) / 3) ((μ : ℚ) / 2) n : ℚ) : ℝ) := by
    exact_mod_cast one_third_le_jacobiWronskianConstant_kz hl hμ n
  have hC' : ((1 : ℝ) / 2) ^ 2 ≤
      ((jacobiWronskianConstant ((l : ℚ) / 3) ((μ : ℚ) / 2) n : ℚ) : ℝ) := by
    push_cast at hC
    rw [show ((1 : ℝ) / 2) ^ 2 = 1 / 4 by norm_num]
    linarith
  have hs : (1 : ℝ) / 2 ≤ √((jacobiWronskianConstant ((l : ℚ) / 3) ((μ : ℚ) / 2) n : ℚ) : ℝ) := by
    have := Real.sqrt_le_sqrt hC'
    rwa [Real.sqrt_sq (by norm_num)] at this
  have hs0 : (0 : ℝ) < √((jacobiWronskianConstant ((l : ℚ) / 3) ((μ : ℚ) / 2) n : ℚ) : ℝ) := by
    linarith
  rw [← Real.log_mul two_ne_zero hs0.ne']
  exact Real.log_nonneg (by linarith)

/-! ### The slope `a_n` -/

/-- `a_n = T_{2,n} + T_{3,n} + E - 2 L_n + 2 log 2`, the coefficient of `z` in `ℋ_n(z)`. -/
noncomputable def kzSlope (l μ : ℤ) (n : ℕ) : ℝ :=
  kzT2 l n + kzT3 μ n + kzE - 2 * kzL l μ n + 2 * Real.log 2

theorem kzSlope_eq (l μ : ℤ) (n : ℕ) :
    kzSlope l μ n = kzT2 l n + kzT3 μ n + kzE - 2 * kzL l μ n + 2 * Real.log 2 := (rfl)

/-- `a_n = E - 2 log cosh((T_{2,n} - T_{3,n})/2)`. -/
theorem kzSlope_eq_cosh (l μ : ℤ) (n : ℕ) :
    kzSlope l μ n = kzE - 2 * Real.log (Real.cosh ((kzT2 l n - kzT3 μ n) / 2)) := by
  have h1 : Real.exp ((kzT2 l n + kzT3 μ n) / 2) * Real.exp ((kzT2 l n - kzT3 μ n) / 2) =
      Real.exp (kzT2 l n) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp ((kzT2 l n + kzT3 μ n) / 2) * Real.exp (-((kzT2 l n - kzT3 μ n) / 2)) =
      Real.exp (kzT3 μ n) := by
    rw [← Real.exp_add]; congr 1; ring
  have hsum : Real.exp (kzT2 l n) + Real.exp (kzT3 μ n) =
      2 * Real.exp ((kzT2 l n + kzT3 μ n) / 2) * Real.cosh ((kzT2 l n - kzT3 μ n) / 2) := by
    rw [Real.cosh_eq]
    linear_combination -h1 - h2
  have hcosh := Real.cosh_pos ((kzT2 l n - kzT3 μ n) / 2)
  rw [kzSlope_eq, kzL_eq, hsum,
    Real.log_mul (mul_ne_zero two_ne_zero (Real.exp_pos _).ne') hcosh.ne',
    Real.log_mul two_ne_zero (Real.exp_pos _).ne', Real.log_exp]
  ring

/-- If `|T_{2,n} - T_{3,n}| ≤ 9/10`, then `a_n ≥ E - 81/400 > 1/2`. -/
theorem half_lt_kzSlope {l μ : ℤ} {n : ℕ} (hT : |kzT2 l n - kzT3 μ n| ≤ 9 / 10) :
    1 / 2 < kzSlope l μ n := by
  have hcosh : Real.log (Real.cosh ((kzT2 l n - kzT3 μ n) / 2)) ≤
      ((kzT2 l n - kzT3 μ n) / 2) ^ 2 / 2 := by
    have := Real.log_le_log (Real.cosh_pos _) (Real.cosh_le_exp_half_sq ((kzT2 l n - kzT3 μ n) / 2))
    rwa [Real.log_exp] at this
  have hd2 : ((kzT2 l n - kzT3 μ n) / 2) ^ 2 ≤ 81 / 400 := by
    have h := abs_le.mp hT
    nlinarith [h.1, h.2]
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_three_gt_d9
  rw [kzSlope_eq_cosh, kzE_eq]
  norm_num at h2 h3
  linarith

/-- If `a > 1/2` and `z > 0`, then `a z + 2 log 2 / z - log z > 0`
(as `z/2 - log z ≥ 1 - log 2 > 0`). -/
theorem slope_add_pos {a z : ℝ} (ha : 1 / 2 < a) (hz : 0 < z) :
    0 < a * z + 2 * Real.log 2 / z - Real.log z := by
  have hlog : Real.log (z / 2) ≤ z / 2 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div hz.ne' two_ne_zero] at hlog
  have h2 := Real.log_two_lt_d9
  have h2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : 0 < 2 * Real.log 2 / z := by positivity
  have haz : z / 2 < a * z := by nlinarith
  norm_num at h2
  linarith

/-! ### Eliminating the factor degree -/

/-- `ℋ_n(z) = Λ_n + (log 2 + log √C_n) + (a_n z + 2 log 2 / z - log z)` for `z ≠ 0`, with
`Λ_n = log κ_n - log g_n - J_n + n(L_n - T_{2,n} - T_{3,n} - E) - 4 log 2`. -/
theorem kzCriterionFn_eq_add {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) (n : ℕ)
    {z : ℝ} (hz : z ≠ 0) : kzCriterionFn l μ n z =
      (Real.log (kzKappa n) - Real.log (kzContent l μ n) - kzJ μ n +
          n * (kzL l μ n - kzT2 l n - kzT3 μ n - kzE) - 4 * Real.log 2) +
        (Real.log 2 +
          Real.log √((jacobiWronskianConstant ((l : ℚ) / 3) ((μ : ℚ) / 2) n : ℚ) : ℝ)) +
        (kzSlope l μ n * z + 2 * Real.log 2 / z - Real.log z) := by
  have hκ : (kzKappa n : ℝ) ≠ 0 := by exact_mod_cast (kzKappa_pos n).ne'
  have hg : (kzContent l μ n : ℝ) ≠ 0 := by exact_mod_cast (kzContent_pos hl hμ n).ne'
  have hC : (0 : ℝ) < ((jacobiWronskianConstant ((l : ℚ) / 3) ((μ : ℚ) / 2) n : ℚ) : ℝ) := by
    exact_mod_cast jacobiWronskianConstant_pos (kz_alpha_gt hl) (kz_beta_gt hμ) n
  have hs := (Real.sqrt_pos.mpr hC).ne'
  rw [kzCriterionFn_eq, kzSlope_eq, kzGamma_eq,
    Real.log_mul (mul_ne_zero two_ne_zero (div_ne_zero hκ hg)) hs,
    Real.log_mul two_ne_zero (div_ne_zero hκ hg), Real.log_div hκ hg]
  field_simp
  ring

/-- **The degree-free consequence of Proposition 4.8** (Appendix B). Let `n ≥ 11`, assume the
exact inequality (4.17) at `n` and `|T_{2,n} - T_{3,n}| ≤ 9/10`. If `P_n^{(λ/3, μ/2)}` is
reducible over `ℚ`, then
`S_n + log g_n > log κ_n - J_n + n(L_n - T_{2,n} - T_{3,n} - E) - 4 log 2`. -/
theorem kz_lower_bound_of_not_irreducible {l μ : ℤ} (hl : l = 1 ∨ l = -1)
    (hμ : μ = 1 ∨ μ = -1) {n : ℕ} (hn : 11 ≤ n) (harch : KanekoZagierArchimedeanBound l μ n)
    (hT : |kzT2 l n - kzT3 μ n| ≤ 9 / 10) (hred : ¬ Irreducible (kanekoZagierJacobi l μ n)) :
    Real.log (kzKappa n) - kzJ μ n + n * (kzL l μ n - kzT2 l n - kzT3 μ n - kzE) -
        4 * Real.log 2 < kzGoodPrimeSum l μ n + Real.log (kzContent l μ n) := by
  by_contra hle
  rw [not_lt] at hle
  apply hred
  refine irreducible_kanekoZagierJacobi_of_finite_criterion hl hμ hn harch fun k hk _ => ?_
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [kzCriterionFn_eq_add hl hμ n hk0.ne']
  have h1 := log_two_add_log_sqrt_kzWronskian_nonneg hl hμ n
  have h2 := slope_add_pos (half_lt_kzSlope hT) hk0
  linarith

/-- `kz_lower_bound_of_not_irreducible` with (4.17) supplied by Proposition 4.7
(`kanekoZagierArchimedeanBound_holds`); conditional on [DLMF, §18.2(vi)] and
[Berger, Theorem 2.4] (the interval Vandermonde bound, Lemma 2.5, is proved). -/
theorem kz_lower_bound_of_not_irreducible'
    (hZ : JacobiSimpleRealZeros)
    (hNP : NewtonPolygonRootSlopes) {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) {n : ℕ}
    (hn : 11 ≤ n) (hT : |kzT2 l n - kzT3 μ n| ≤ 9 / 10)
    (hred : ¬ Irreducible (kanekoZagierJacobi l μ n)) :
    Real.log (kzKappa n) - kzJ μ n + n * (kzL l μ n - kzT2 l n - kzT3 μ n - kzE) -
        4 * Real.log 2 < kzGoodPrimeSum l μ n + Real.log (kzContent l μ n) :=
  kz_lower_bound_of_not_irreducible hl hμ hn (kanekoZagierArchimedeanBound_holds hZ hNP hl hμ n) hT
    hred

end ArithmeticOfJacobiPolynomials
