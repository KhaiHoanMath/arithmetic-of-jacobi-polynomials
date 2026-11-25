/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.KanekoZagier.ExplicitCutoffLower
public import ArithmeticOfJacobiPolynomials.KanekoZagier.ArithmeticAsymptotics

/-!
# The asymptotic archimedean bound (4.18) (§4.4)

Proposition 4.7, second part: uniformly in `λ, μ ∈ {-1, 1}` and in the factorizations
`H_n = A B` in `ℤ[t]` with `1 ≤ k = deg A ≤ n/2`,
`log R^{(6)} ≥ (𝔩 - o(1)) k n`, where `R = |Res(A, B)|` and
`𝔩 = log(4 + 3√3) - ½ log 2 - ⅓ log 3 - π/(2√3)` (`kanekoZagierArchimedeanAsymptotics`).

The proof follows the manuscript. The exact inequality (4.17) (`KanekoZagierArchimedeanBound`,
from `kanekoZagierArchimedeanBound_holds`) gives `log R^{(6)} / k ≥ ℋ_n(k)`. Write
`ℋ_n(k) = Λ_n - log g_n + (log 2 + log √C_n) + (a_n k + 2 log 2 / k - log k)`
(`kzCriterionFn_eq_add`). Then:

* the last bracket is positive, because `a_n > 1/2` for `n ≥ 250000` (`half_lt_kzSlope`,
  `slope_add_pos`);
* the Wronskian bracket is nonnegative (`log_two_add_log_sqrt_kzWronskian_nonneg`);
* `Λ_n ≥ n (log(4 + 3√3) - E) - 6 log(3n + 1) - 10` (`kz_lambda_ge_log`);
* `log g_n ≤ (π/(2√3) + o(1)) n` by Proposition 4.5 (`eventually_log_kzContent_le`,
  conditional on [BMOR, Corollary 1.7], `BMORPrimeCountingBound`).
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial Filter

/-- **(4.18), statement** (§4.4): for every `ε > 0`, for all large `n`,
uniformly in `λ, μ ∈ {-1, 1}` and in the factorizations `H_n = A B` in `ℤ[t]` with
`1 ≤ k = deg A ≤ n/2`, `log R^{(6)} ≥ (𝔩 - ε) k n`, where
`𝔩 = log(4 + 3√3) - ½ log 2 - ⅓ log 3 - π/(2√3)` and `R = |Res(A, B)|`. -/
def KanekoZagierArchimedeanAsymptotics : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ l μ : ℤ, (l = 1 ∨ l = -1) → (μ = 1 ∨ μ = -1) →
    ∀ A B : ℤ[X], kzPrimitive l μ n = A * B → 1 ≤ A.natDegree → 2 * A.natDegree ≤ n →
      (Real.log (4 + 3 * √3) - Real.log 2 / 2 - Real.log 3 / 3 - Real.pi / (2 * √3) - ε) *
          A.natDegree * n ≤ Real.log (primeToSixPart (resultant A B))

theorem kanekoZagierArchimedeanAsymptotics_iff : KanekoZagierArchimedeanAsymptotics ↔
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ l μ : ℤ, (l = 1 ∨ l = -1) → (μ = 1 ∨ μ = -1) →
      ∀ A B : ℤ[X], kzPrimitive l μ n = A * B → 1 ≤ A.natDegree → 2 * A.natDegree ≤ n →
        (Real.log (4 + 3 * √3) - Real.log 2 / 2 - Real.log 3 / 3 - Real.pi / (2 * √3) - ε) *
            A.natDegree * n ≤ Real.log (primeToSixPart (resultant A B)) := Iff.rfl

/-- `Λ_n ≥ n (log(4 + 3√3) - E) - 6 log(3n + 1) - 10`. -/
theorem kz_lambda_ge_log {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) {n : ℕ}
    (hn : 1 ≤ n) :
    n * (Real.log (4 + 3 * √3) - kzE) - 6 * Real.log (3 * n + 1) - 10 ≤
      Real.log (kzKappa n) - kzJ μ n + n * (kzL l μ n - kzT2 l n - kzT3 μ n - kzE) -
        4 * Real.log 2 := by
  have h0 := kz_lambda_ge_sub hl hμ hn
  obtain ⟨h1, h2, h3, h4, -, -, -, hδ, hδ0⟩ := kz_log_facts hμ hn
  have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hln : Real.log n ≤ Real.log (3 * n + 1) := Real.log_le_log (by linarith) (by linarith)
  have hln2 : Real.log (2 * n + kzDelta μ) ≤ Real.log (3 * n + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have p4 := mul_le_mul_of_nonneg_right hδ hl3.le
  have l2 := Real.log_two_lt_d9
  have l3 := Real.log_three_lt_d9
  norm_num at l2 l3
  have hpos : 0 ≤ Real.log (3 * n + 1) := Real.log_nonneg (by linarith)
  linarith

/-- `6 log(3n + 1) + 10 ≤ ε n` for all large `n`. -/
theorem eventually_six_log_add_ten_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 6 * Real.log (3 * n + 1) + 10 ≤ ε * n := by
  set K : ℝ := 36 / ε with hK
  have hK0 : 0 < K := by positivity
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (6 * Real.log K + 10 + ε / 6) * 2 / ε < N := exists_nat_gt _
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hy : (0 : ℝ) < 3 * n + 1 := by positivity
  have h1 := Real.log_le_sub_one_of_pos (show 0 < (3 * (n : ℝ) + 1) / K by positivity)
  rw [Real.log_div hy.ne' hK0.ne'] at h1
  have e : (3 * (n : ℝ) + 1) / K = ε * (3 * n + 1) / 36 := by
    rw [hK]; field_simp
  rw [e] at h1
  have h2 : (6 * Real.log K + 10 + ε / 6) * 2 < ε * n := by
    have := (div_lt_iff₀ hε).mp (lt_of_lt_of_le hN hnN)
    linarith
  nlinarith

/-- **(4.18)** (§4.4), conditional on the inputs of (4.17)
(`JacobiSimpleRealZeros` and `NewtonPolygonRootSlopes`) and on [BMOR, Corollary 1.7]
(`BMORPrimeCountingBound`, through Proposition 4.5). -/
theorem kanekoZagierArchimedeanAsymptotics (hZ : JacobiSimpleRealZeros)
    (hNP : NewtonPolygonRootSlopes) (hBMOR :
    BMORPrimeCountingBound) :
    KanekoZagierArchimedeanAsymptotics := by
  intro ε hε
  have one : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1 := Or.inl rfl
  have mone : (-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1 := Or.inr rfl
  have hε2 : 0 < ε / 2 := by positivity
  filter_upwards [eventually_log_kzContent_le hBMOR one one hε2,
    eventually_log_kzContent_le hBMOR one mone hε2,
    eventually_log_kzContent_le hBMOR mone one hε2,
    eventually_log_kzContent_le hBMOR mone mone hε2,
    eventually_six_log_add_ten_le hε2, eventually_ge_atTop 250000]
    with n g11 g1m gm1 gmm hlog hn l μ hl hμ A B hAB hk hk2
  have hg : Real.log (kzContent l μ n) ≤ (Real.pi / (2 * √3) + ε / 2) * n := by
    rcases hl with rfl | rfl <;> rcases hμ with rfl | rfl
    exacts [g11, g1m, gm1, gmm]
  have hn1 : 1 ≤ n := by omega
  have hkR : (0 : ℝ) < A.natDegree := by exact_mod_cast hk
  have harch := kanekoZagierArchimedeanBound_holds hZ hNP hl hμ n A B hAB hk hk2
  rw [kzCriterionFn_eq_add hl hμ n hkR.ne', le_div_iff₀ hkR] at harch
  have hX2 := log_two_add_log_sqrt_kzWronskian_nonneg hl hμ n
  have hX3 := slope_add_pos (half_lt_kzSlope (abs_kzT2_sub_kzT3_le hl hμ hn)) hkR
  have hX1 := kz_lambda_ge_log hl hμ hn1
  have hH : (Real.log (4 + 3 * √3) - Real.log 2 / 2 - Real.log 3 / 3 - Real.pi / (2 * √3) - ε) *
      n ≤ (Real.log (kzKappa n) - Real.log (kzContent l μ n) - kzJ μ n +
          n * (kzL l μ n - kzT2 l n - kzT3 μ n - kzE) - 4 * Real.log 2) +
        (Real.log 2 +
          Real.log √((jacobiWronskianConstant ((l : ℚ) / 3) ((μ : ℚ) / 2) n : ℚ) : ℝ)) +
        (kzSlope l μ n * A.natDegree + 2 * Real.log 2 / A.natDegree -
          Real.log A.natDegree) := by
    have hEn : (n : ℝ) * kzE = n * (Real.log 2 / 2 + Real.log 3 / 3) := by rw [kzE_eq]
    linarith
  have := mul_le_mul_of_nonneg_left hH hkR.le
  calc (Real.log (4 + 3 * √3) - Real.log 2 / 2 - Real.log 3 / 3 - Real.pi / (2 * √3) - ε) *
        A.natDegree * n = A.natDegree *
        ((Real.log (4 + 3 * √3) - Real.log 2 / 2 - Real.log 3 / 3 - Real.pi / (2 * √3) - ε) *
          n) := by ring
    _ ≤ _ := this
    _ ≤ _ := by linarith

end ArithmeticOfJacobiPolynomials
