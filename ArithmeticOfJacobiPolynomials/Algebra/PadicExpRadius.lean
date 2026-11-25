/- Assembled by AxiomProver. -/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# The `p`-adic exponential has positive radius of convergence

For a prime `p` and a normed `ℚ_[p]`-algebra `A`, the exponential series
`expSeries ℚ_[p] A = ∑ (1/n!) xⁿ` has positive radius of convergence. The input is Legendre's
formula `(p - 1) v_p(n!) = n - s_p(n)`, which gives `v_p(n!) ≤ n`, hence
`‖1/n!‖_p = p^{v_p(n!)} ≤ p^n`; so the radius is at least `1/p`.

Consequences, for complete `A` and a fixed `X : A`:
* `ArithmeticOfJacobiPolynomials.padic_continuousAt_exp_smul`: `t ↦ exp (t • X)` is continuous at
`0`;
* `ArithmeticOfJacobiPolynomials.padic_eventually_exp_add_smul`: near `(0, 0)`,
  `exp ((s + t) • X) = exp (s • X) * exp (t • X)`;
* `ArithmeticOfJacobiPolynomials.padic_eventually_exp_smul_mul_exp_neg_smul`: near `0`,
  `exp (t • X) * exp (-t • X) = 1 = exp (-t • X) * exp (t • X)`.
-/

public section

open NormedSpace Filter Topology
open scoped Nat NNReal ENNReal

namespace ArithmeticOfJacobiPolynomials

variable {p : ℕ} [hp : Fact p.Prime]

/-- `v_p(n!) ≤ n` (from Legendre's formula `(p - 1) v_p(n!) = n - s_p(n)`). -/
theorem padicValNat_factorial_le_self (n : ℕ) : padicValNat p n ! ≤ n := by
  have h := sub_one_mul_padicValNat_factorial (p := p) n
  have hp1 : 1 ≤ p - 1 := by have := hp.out.two_le; omega
  calc padicValNat p n ! ≤ (p - 1) * padicValNat p n ! := Nat.le_mul_of_pos_left _ hp1
    _ = n - (p.digits n).sum := h
    _ ≤ n := Nat.sub_le _ _

/-- `‖1/n!‖_p ≤ p^n`. -/
theorem padic_norm_inv_factorial_le (n : ℕ) :
    ‖((n ! : ℚ_[p]))⁻¹‖ ≤ (p : ℝ) ^ n := by
  have hne : (n ! : ℚ_[p]) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [norm_inv, Padic.norm_eq_zpow_neg_valuation hne, Padic.valuation_natCast, ← zpow_neg,
    neg_neg, zpow_natCast]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  exact pow_le_pow_right₀ hp1 (padicValNat_factorial_le_self n)

variable (p) in
/-- The exponential series of a normed `ℚ_[p]`-algebra has radius at least `1/p`. -/
theorem padic_inv_le_expSeries_radius (A : Type*) [NormedRing A] [NormedAlgebra ℚ_[p] A] :
    (((p : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) ≤ (expSeries ℚ_[p] A).radius := by
  refine FormalMultilinearSeries.le_radius_of_bound _ (max 1 ‖(1 : A)‖) fun n => ?_
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hmk : ‖ContinuousMultilinearMap.mkPiAlgebraFin ℚ_[p] n A‖ ≤ max 1 ‖(1 : A)‖ := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [ContinuousMultilinearMap.norm_mkPiAlgebraFin_zero]; exact le_max_right _ _
    · exact (ContinuousMultilinearMap.norm_mkPiAlgebraFin_le_of_pos hn).trans (le_max_left _ _)
  have hterm : ‖expSeries ℚ_[p] A n‖ ≤ (p : ℝ) ^ n * max 1 ‖(1 : A)‖ := by
    rw [expSeries]
    refine (norm_smul_le ((n ! : ℚ_[p]))⁻¹
      (ContinuousMultilinearMap.mkPiAlgebraFin ℚ_[p] n A)).trans ?_
    exact mul_le_mul (padic_norm_inv_factorial_le n) hmk (norm_nonneg _) (by positivity)
  have hr : (((p : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) = (p : ℝ)⁻¹ := by simp
  rw [hr]
  calc ‖expSeries ℚ_[p] A n‖ * (p : ℝ)⁻¹ ^ n
      ≤ (p : ℝ) ^ n * max 1 ‖(1 : A)‖ * (p : ℝ)⁻¹ ^ n :=
        mul_le_mul_of_nonneg_right hterm (by positivity)
    _ = max 1 ‖(1 : A)‖ := by
        rw [mul_comm, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hp0.ne', one_pow, one_mul]

variable (p) in
/-- **The `p`-adic exponential series has positive radius of convergence.** -/
theorem padic_expSeries_radius_pos (A : Type*) [NormedRing A] [NormedAlgebra ℚ_[p] A] :
    0 < (expSeries ℚ_[p] A).radius := by
  refine lt_of_lt_of_le ?_ (padic_inv_le_expSeries_radius p A)
  have : (0 : ℝ≥0) < (p : ℝ≥0)⁻¹ := inv_pos.mpr (by exact_mod_cast hp.out.pos)
  exact_mod_cast this

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ_[p] A] [CompleteSpace A]

omit [CompleteSpace A] in
/-- Near `0`, `t • X` lies in the disc of convergence of the exponential series. -/
theorem padic_eventually_smul_mem_eball (X : A) :
    ∀ᶠ t in 𝓝 (0 : ℚ_[p]), t • X ∈ Metric.eball (0 : A) (expSeries ℚ_[p] A).radius := by
  have hc : Tendsto (fun t : ℚ_[p] => t • X) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous fun t : ℚ_[p] => t • X := continuous_id.smul continuous_const
    have := hcont.tendsto 0
    rwa [zero_smul] at this
  exact hc.eventually (Metric.eball_mem_nhds _ (padic_expSeries_radius_pos p A))

/-- `t ↦ exp (t • X)` is continuous at `0` (where it takes the value `1`). -/
theorem padic_continuousAt_exp_smul (X : A) :
    ContinuousAt (fun t : ℚ_[p] => exp (t • X)) 0 := by
  have hexp : ContinuousAt (exp : A → A) 0 :=
    (hasFPowerSeriesAt_exp_zero_of_radius_pos (padic_expSeries_radius_pos p A)).continuousAt
  have hsmul : ContinuousAt (fun t : ℚ_[p] => t • X) 0 :=
    (continuous_id.smul continuous_const).continuousAt
  have h0 : (0 : ℚ_[p]) • X = 0 := zero_smul _ _
  exact ContinuousAt.comp (g := exp) (by rwa [h0]) hsmul

/-- `exp (t • X) → 1` as `t → 0`. -/
theorem padic_tendsto_exp_smul_one (X : A) :
    Tendsto (fun t : ℚ_[p] => exp (t • X)) (𝓝 0) (𝓝 1) := by
  simpa [ContinuousAt] using padic_continuousAt_exp_smul (p := p) X

/-- `t ↦ exp (t • X)` is a homomorphism from `(ℚ_[p], +)` near `0`. -/
theorem padic_eventually_exp_add_smul (X : A) :
    ∀ᶠ st in 𝓝 ((0 : ℚ_[p]), (0 : ℚ_[p])),
      exp ((st.1 + st.2) • X) = exp (st.1 • X) * exp (st.2 • X) := by
  have h := padic_eventually_smul_mem_eball (p := p) X
  filter_upwards [(continuous_fst.tendsto _).eventually h,
    (continuous_snd.tendsto _).eventually h] with st h1 h2
  rw [add_smul]
  exact exp_add_of_commute_of_mem_ball (((Commute.refl X).smul_left _).smul_right _) h1 h2

/-- Near `0`, `exp (t • X)` is invertible with inverse `exp (-t • X)`. -/
theorem padic_eventually_exp_smul_mul_exp_neg_smul (X : A) :
    ∀ᶠ t in 𝓝 (0 : ℚ_[p]),
      exp (t • X) * exp ((-t) • X) = 1 ∧ exp ((-t) • X) * exp (t • X) = 1 := by
  have h := padic_eventually_smul_mem_eball (p := p) X
  have hneg : Tendsto (fun t : ℚ_[p] => -t) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_neg.tendsto (0 : ℚ_[p]))
  filter_upwards [h, hneg.eventually h] with t h1 h2
  have hc : Commute (t • X) ((-t) • X) := ((Commute.refl X).smul_left _).smul_right _
  refine ⟨?_, ?_⟩
  · rw [← exp_add_of_commute_of_mem_ball hc h1 h2, ← add_smul, add_neg_cancel, zero_smul,
      exp_zero]
  · rw [← exp_add_of_commute_of_mem_ball hc.symm h2 h1, ← add_smul, neg_add_cancel, zero_smul,
      exp_zero]

end ArithmeticOfJacobiPolynomials
