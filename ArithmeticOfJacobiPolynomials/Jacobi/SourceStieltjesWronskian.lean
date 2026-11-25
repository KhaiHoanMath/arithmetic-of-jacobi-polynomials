/- Assembled by AxiomProver. -/
module

import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import ArithmeticOfJacobiPolynomials.Jacobi.RealWronskian

/-!
# Lemma 2.1 by the manuscript's Stieltjes-transform argument

For real `α, β > -1` the manuscript proves the identity
`(c+1) y_n² + σ (y_n' Q_n - y_n Q_n') + ρ y_n Q_n = C_n` through the Stieltjes transforms
`m(t) = I_s((t-s)⁻¹)` and `q(t) = I_s(y_n(s)/(t-s))` for real `t > 1`: integration by parts
(`σ w` vanishes at both endpoints) gives their differential equations, the left side is constant,
and the large-`t` behaviour of `q` together with orthogonality and the Jacobi norm formula gives
the constant.  This file follows that argument.
-/

public section

-- the hypotheses `hα hβ ht` are carried uniformly by the Stieltjes lemmas
set_option linter.unusedSectionVars false

namespace ArithmeticOfJacobiPolynomials.JacobiGeneric.Real

open Polynomial Finset Filter Topology MeasureTheory

/-! ### The analytic Pearson identity (integration by parts) -/

/-- **Integration by parts against the Jacobi weight**: since `σ w = s^{α+1}(1-s)^{β+1}` vanishes at
both endpoints and `(σ w)' = τ w`, `∫_0^1 (σ φ' + τ φ) w = 0` for `φ` of class `C¹` on `[0,1]`. -/
theorem integral_pearson {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) {φ φ' : ℝ → ℝ}
    (hφ : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt φ (φ' x) x)
    (hφ' : ContinuousOn φ' (Set.Icc 0 1)) :
    ∫ x in (0 : ℝ)..1, (x * (1 - x) * φ' x + (α + 1 - (α + β + 2) * x) * φ x) *
      jacobiWeight α β x = 0 := by
  have hφc : ContinuousOn φ (Set.Icc 0 1) := fun x hx => (hφ x hx).continuousAt.continuousWithinAt
  have h1 : Continuous fun x : ℝ => x ^ (α + 1) := Real.continuous_rpow_const (by linarith)
  have h2 : Continuous fun x : ℝ => (1 - x) ^ (β + 1) :=
    (Real.continuous_rpow_const (by linarith)).comp (continuous_const.sub continuous_id)
  set G : ℝ → ℝ := fun x => φ x * (x ^ (α + 1) * (1 - x) ^ (β + 1)) with hG
  have hcont : ContinuousOn G (Set.Icc 0 1) := hφc.mul (h1.mul h2).continuousOn
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt G
      ((x * (1 - x) * φ' x + (α + 1 - (α + β + 2) * x) * φ x) * jacobiWeight α β x) x := by
    intro x hx
    have hx1 : (1 - x) ≠ 0 := by linarith [hx.2]
    have d1 : HasDerivAt (fun x : ℝ => x ^ (α + 1)) ((α + 1) * x ^ (α + 1 - 1)) x :=
      Real.hasDerivAt_rpow_const (Or.inl hx.1.ne')
    have d2 : HasDerivAt (fun x : ℝ => (1 - x) ^ (β + 1))
        ((β + 1) * (1 - x) ^ (β + 1 - 1) * (-1)) x :=
      (Real.hasDerivAt_rpow_const (Or.inl hx1)).comp x ((hasDerivAt_id x).const_sub 1)
    have d := (hφ x ⟨hx.1.le, hx.2.le⟩).mul (d1.mul d2)
    convert d using 1
    simp only [Pi.mul_apply]
    rw [jacobiWeight_eq, add_sub_cancel_right, add_sub_cancel_right, Real.rpow_add_one hx.1.ne',
      Real.rpow_add_one hx1]
    ring
  have hc : ContinuousOn (fun x => x * (1 - x) * φ' x + (α + 1 - (α + β + 2) * x) * φ x)
      (Set.uIcc 0 1) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact ((continuousOn_id.mul (continuousOn_const.sub continuousOn_id)).mul hφ').add
      ((continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).mul hφc)
  have hint := (intervalIntegrable_jacobiWeight hα hβ).continuousOn_mul hc
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv hint]
  have e1 : (0 : ℝ) ^ (α + 1) = 0 := Real.zero_rpow (by linarith)
  have e2 : (0 : ℝ) ^ (β + 1) = 0 := Real.zero_rpow (by linarith)
  simp [hG, e1, e2]

/-! ### The Stieltjes-type integrals -/

/-- `T_t(P, k) = ∫_0^1 P(s) (t-s)^{-k} w(s) ds` for real `t > 1`: `m(t) = T_t(1,1)/Z` and
`q(t) = T_t(y_n, 1)/Z` are the Stieltjes transforms of the manuscript. -/
noncomputable def stj (α β t : ℝ) (P : ℝ[X]) (k : ℕ) : ℝ :=
  ∫ s in (0 : ℝ)..1, P.eval s * ((t - s)⁻¹) ^ k * jacobiWeight α β s

section StjLinear

variable {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) {t : ℝ} (ht : 1 < t)
include hα hβ ht

theorem stj_integrable (P : ℝ[X]) (k : ℕ) :
    IntervalIntegrable (fun s => P.eval s * ((t - s)⁻¹) ^ k * jacobiWeight α β s) volume 0 1 := by
  refine (intervalIntegrable_jacobiWeight hα hβ).continuousOn_mul ?_
  rw [Set.uIcc_of_le zero_le_one]
  refine P.continuous.continuousOn.mul (ContinuousOn.pow ?_ k)
  refine ContinuousOn.inv₀ (by fun_prop) fun s hs => ?_
  exact (by linarith [hs.2] : 0 < t - s).ne'

theorem stj_add (P Q : ℝ[X]) (k : ℕ) :
    stj α β t (P + Q) k = stj α β t P k + stj α β t Q k := by
  unfold stj
  rw [← intervalIntegral.integral_add (stj_integrable hα hβ ht P k) (stj_integrable hα hβ ht Q k)]
  exact intervalIntegral.integral_congr fun s _ => by simp only [eval_add]; ring

theorem stj_sub (P Q : ℝ[X]) (k : ℕ) :
    stj α β t (P - Q) k = stj α β t P k - stj α β t Q k := by
  unfold stj
  rw [← intervalIntegral.integral_sub (stj_integrable hα hβ ht P k) (stj_integrable hα hβ ht Q k)]
  exact intervalIntegral.integral_congr fun s _ => by simp only [eval_sub]; ring

theorem stj_C_mul (a : ℝ) (P : ℝ[X]) (k : ℕ) :
    stj α β t (C a * P) k = a * stj α β t P k := by
  unfold stj
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr fun s _ => by simp only [eval_mul, eval_C]; ring

/-- `(t - s) · (t-s)^{-(k+1)} = (t-s)^{-k}`: multiplying by `t - X` lowers the power. -/
theorem stj_sub_X_mul (P : ℝ[X]) (k : ℕ) :
    stj α β t ((C t - X) * P) (k + 1) = stj α β t P k := by
  unfold stj
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le zero_le_one] at hs
  have hu : (t - s) * (t - s)⁻¹ = 1 := mul_inv_cancel₀ (by linarith [hs.2])
  simp only [eval_mul, eval_sub, eval_C, eval_X]
  linear_combination (P.eval s * ((t - s)⁻¹) ^ k * jacobiWeight α β s) * hu

/-- `σ P` for `σ = X (1 - X)`: `σ(s) = σ(t) - σ'(t)(t-s) - (t-s)²`. -/
theorem stj_sigma_mul (P : ℝ[X]) (k : ℕ) :
    stj α β t (X * (1 - X) * P) (k + 2) =
      t * (1 - t) * stj α β t P (k + 2) - (1 - 2 * t) * stj α β t P (k + 1) - stj α β t P k := by
  have e : X * (1 - X) * P = C (t * (1 - t)) * P - C (1 - 2 * t) * ((C t - X) * P) -
      (C t - X) * ((C t - X) * P) := by
    simp only [C_mul, C_sub, C_1, C_ofNat]
    ring
  have r1 : stj α β t ((C t - X) * P) (k + 2) = stj α β t P (k + 1) :=
    stj_sub_X_mul hα hβ ht P (k + 1)
  have r2 : stj α β t ((C t - X) * ((C t - X) * P)) (k + 2) = stj α β t P k := by
    rw [show k + 2 = (k + 1) + 1 from rfl, stj_sub_X_mul hα hβ ht, stj_sub_X_mul hα hβ ht]
  rw [e, stj_sub hα hβ ht, stj_sub hα hβ ht, stj_C_mul hα hβ ht, stj_C_mul hα hβ ht, r1, r2]

/-- `τ P` for `τ = (α+1) - (α+β+2) X`: `τ(s) = τ(t) + (c+2)(t-s)`. -/
theorem stj_tau_mul (P : ℝ[X]) (k : ℕ) :
    stj α β t ((C (α + 1) - C (α + β + 2) * X) * P) (k + 1) =
      (α + 1 - (α + β + 2) * t) * stj α β t P (k + 1) + (α + β + 2) * stj α β t P k := by
  have e : (C (α + 1) - C (α + β + 2) * X) * P =
      C (α + 1 - (α + β + 2) * t) * P + C (α + β + 2) * ((C t - X) * P) := by
    simp only [C_mul, C_sub]
    ring
  rw [e, stj_add hα hβ ht, stj_C_mul hα hβ ht, stj_C_mul hα hβ ht, stj_sub_X_mul hα hβ ht]

/-- The analytic Pearson identity for `φ = p · (t-s)^{-k}`:
`T(σ p' + τ p, k) + k T(σ p, k+1) = 0`. -/
theorem stj_pearson (p : ℝ[X]) (k : ℕ) :
    stj α β t (X * (1 - X) * derivative p + (C (α + 1) - C (α + β + 2) * X) * p) k +
      k * stj α β t (X * (1 - X) * p) (k + 1) = 0 := by
  set φ : ℝ → ℝ := fun s => p.eval s * ((t - s)⁻¹) ^ k with hφ
  set φ' : ℝ → ℝ := fun s => (derivative p).eval s * ((t - s)⁻¹) ^ k +
    k * (p.eval s * ((t - s)⁻¹) ^ (k + 1)) with hφ'
  have hne : ∀ s ∈ Set.Icc (0 : ℝ) 1, t - s ≠ 0 := fun s hs => (by linarith [hs.2] : 0 < t - s).ne'
  have hder : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt φ (φ' x) x := by
    intro x hx
    have h1 : HasDerivAt (fun s : ℝ => (t - s)⁻¹ ^ k) (k * ((t - x)⁻¹) ^ (k + 1)) x := by
      have a : HasDerivAt (fun s : ℝ => t - s) (-1) x := (hasDerivAt_id x).const_sub t
      have a2 : HasDerivAt (fun s : ℝ => (t - s)⁻¹) (((t - x)⁻¹) ^ 2) x := by
        convert a.inv (hne x hx) using 1
        field_simp
      rcases k with _ | j
      · simpa using hasDerivAt_const x (1 : ℝ)
      · convert a2.pow (j + 1) using 1
        simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
        ring
    have := (p.hasDerivAt x).mul h1
    convert this using 1
    simp only [hφ']
    ring
  have hcont : ContinuousOn φ' (Set.Icc 0 1) := by
    refine ContinuousOn.add ?_ ?_
    · exact (derivative p).continuous.continuousOn.mul
        (ContinuousOn.pow (ContinuousOn.inv₀ (by fun_prop) hne) k)
    · exact continuousOn_const.mul (p.continuous.continuousOn.mul
        (ContinuousOn.pow (ContinuousOn.inv₀ (by fun_prop) hne) (k + 1)))
  have key := integral_pearson hα hβ hder hcont
  have i1 := stj_integrable hα hβ ht
    (X * (1 - X) * derivative p + (C (α + 1) - C (α + β + 2) * X) * p) k
  have i2 := stj_integrable hα hβ ht (X * (1 - X) * p) (k + 1)
  unfold stj
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add i1
    (i2.const_mul (k : ℝ))]
  refine Eq.trans ?_ key
  refine intervalIntegral.integral_congr fun s hs => ?_
  simp only [hφ, hφ', eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one]
  ring

end StjLinear

/-- `T_t(P, 0) = I(P) · Z`. -/
theorem stj_zero {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (t : ℝ) (P : ℝ[X]) :
    stj α β t P 0 = jacobiFunctional α β P * jacobiWeightMoment α β 0 := by
  rw [jacobiFunctional_mul_integral hα hβ]
  unfold stj
  simp

/-! ### The differential equations of the Stieltjes transforms -/

section Odes

variable {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) {t : ℝ} (ht : 1 < t)
include hα hβ ht

/-- `T_t(1, 0) = Z`. -/
theorem stj_one_zero : stj α β t 1 0 = jacobiWeightMoment α β 0 := by
  rw [stj_zero hα hβ, show (1 : ℝ[X]) = C 1 from C_1.symm, jacobiFunctional_C, one_mul]

/-- **The equation of `m`**: `σ m' - ρ m = c + 1`, in terms of `m = T(1,1)/Z`, `m' = -T(1,2)/Z`:
`σ T(1,2) + ρ T(1,1) + (c+1) Z = 0`. -/
theorem stj_m_ode :
    t * (1 - t) * stj α β t 1 2 + (α - (α + β) * t) * stj α β t 1 1 +
      (α + β + 1) * jacobiWeightMoment α β 0 = 0 := by
  have hp := stj_pearson hα hβ ht (1 : ℝ[X]) 1
  simp only [derivative_one, mul_zero, zero_add, Nat.cast_one, one_mul, Nat.reduceAdd] at hp
  have h1 : stj α β t ((C (α + 1) - C (α + β + 2) * X) * 1) 1 =
      (α + 1 - (α + β + 2) * t) * stj α β t 1 1 + (α + β + 2) * stj α β t 1 0 :=
    stj_tau_mul hα hβ ht 1 0
  have h2 : stj α β t (X * (1 - X) * 1) 2 =
      t * (1 - t) * stj α β t 1 2 - (1 - 2 * t) * stj α β t 1 1 - stj α β t 1 0 :=
    stj_sigma_mul hα hβ ht 1 0
  have h0 := stj_one_zero hα hβ ht
  rw [h1, h2, h0] at hp
  linear_combination hp

/-- **The equation of `q`**: `σ q'' + (σ' - ρ) q' + (Λ + c) q = 0`, in terms of
`q = T(y,1)/Z`, `q' = -T(y,2)/Z`, `q'' = 2 T(y,3)/Z`. -/
theorem stj_q_ode (y : ℝ[X]) (L : ℝ)
    (hode : X * (1 - X) * derivative (derivative y) +
      (C (α + 1) - C (α + β + 2) * X) * derivative y + C L * y = 0) :
    2 * (t * (1 - t)) * stj α β t y 3 +
        ((α - (α + β) * t) - (1 - 2 * t)) * stj α β t y 2 +
        (L + (α + β)) * stj α β t y 1 = 0 := by
  have hR := stj_pearson hα hβ ht (derivative y) 1
  have e : X * (1 - X) * derivative (derivative y) +
      (C (α + 1) - C (α + β + 2) * X) * derivative y = C (-L) * y := by
    rw [C_neg]; linear_combination hode
  rw [e, stj_C_mul hα hβ ht] at hR
  have hP := stj_pearson hα hβ ht y 2
  rw [stj_add hα hβ ht] at hP
  have h1 : stj α β t ((C (α + 1) - C (α + β + 2) * X) * y) 2 =
      (α + 1 - (α + β + 2) * t) * stj α β t y 2 + (α + β + 2) * stj α β t y 1 :=
    stj_tau_mul hα hβ ht y 1
  have h2 : stj α β t (X * (1 - X) * y) 3 =
      t * (1 - t) * stj α β t y 3 - (1 - 2 * t) * stj α β t y 2 - stj α β t y 1 :=
    stj_sigma_mul hα hβ ht y 1
  simp only [Nat.cast_one, one_mul, Nat.reduceAdd] at hR
  simp only [Nat.cast_ofNat, Nat.reduceAdd] at hP
  rw [h1, h2] at hP
  linear_combination hP - hR

end Odes

/-! ### Differentiation under the integral sign -/

section Deriv

variable {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) {t : ℝ} (ht : 1 < t)
include hα hβ ht

/-- `d/dt T_t(P, k) = -k T_t(P, k+1)` for `t > 1`. -/
theorem hasDerivAt_stj (P : ℝ[X]) (k : ℕ) :
    HasDerivAt (fun t' => stj α β t' P k) (-(k : ℝ) * stj α β t P (k + 1)) t := by
  set δ : ℝ := (t - 1) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hint : ∀ {t' : ℝ}, 1 < t' → ∀ (j : ℕ),
      Integrable (fun a => P.eval a * ((t' - a)⁻¹) ^ j * jacobiWeight α β a)
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) := fun {t'} ht' j => by
    have := stj_integrable hα hβ ht' P j
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this
  have hint0 : Integrable (fun a => P.eval a * jacobiWeight α β a)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    have := stj_integrable hα hβ ht P 0
    simp only [pow_zero, mul_one] at this
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioc (0 : ℝ) 1))
    (F := fun t' a => P.eval a * ((t' - a)⁻¹) ^ k * jacobiWeight α β a)
    (F' := fun t' a => -(k : ℝ) * (P.eval a * ((t' - a)⁻¹) ^ (k + 1) * jacobiWeight α β a))
    (bound := fun a => k * (δ⁻¹) ^ (k + 1) * ‖P.eval a * jacobiWeight α β a‖)
    (x₀ := t) (s := Metric.ball t δ) (Metric.ball_mem_nhds t hδ)
    (by filter_upwards [Ioi_mem_nhds ht] with t' ht' using (hint ht' k).aestronglyMeasurable)
    (hint ht k)
    ((hint ht (k + 1)).const_mul (-(k : ℝ))).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha x hx
      have hxt := abs_lt.mp (Metric.mem_ball.mp hx)
      have hxa : δ < x - a := by linarith [ha.2, hxt.1]
      have hu0 : 0 < (x - a)⁻¹ := inv_pos.mpr (by linarith)
      have hu1 : (x - a)⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ hxa.le
      have hpow : ((x - a)⁻¹) ^ (k + 1) ≤ (δ⁻¹) ^ (k + 1) := pow_le_pow_left₀ hu0.le hu1 _
      calc ‖-(k : ℝ) * (P.eval a * ((x - a)⁻¹) ^ (k + 1) * jacobiWeight α β a)‖
          = k * (((x - a)⁻¹) ^ (k + 1) * (|P.eval a| * |jacobiWeight α β a|)) := by
            rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (Nat.cast_nonneg k), abs_mul,
              abs_mul, abs_of_pos (pow_pos hu0 _)]
            ring
        _ ≤ k * ((δ⁻¹) ^ (k + 1) * (|P.eval a| * |jacobiWeight α β a|)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow (by positivity))
              (Nat.cast_nonneg k)
        _ = k * (δ⁻¹) ^ (k + 1) * ‖P.eval a * jacobiWeight α β a‖ := by
            rw [Real.norm_eq_abs, abs_mul]; ring)
    ((hint0.norm).const_mul _)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha x hx
      have hxt := abs_lt.mp (Metric.mem_ball.mp hx)
      have hxa : 0 < x - a := by linarith [ha.2, hxt.1]
      have hne : x - a ≠ 0 := hxa.ne'
      have h0 : HasDerivAt (fun s : ℝ => s - a) 1 x := (hasDerivAt_id x).sub_const a
      have h1 : HasDerivAt (fun s : ℝ => (s - a)⁻¹) (-(((x - a)⁻¹) ^ 2)) x := by
        convert h0.inv hne using 1
        field_simp
      have h2 : HasDerivAt (fun s : ℝ => ((s - a)⁻¹) ^ k) (-(k : ℝ) * ((x - a)⁻¹) ^ (k + 1)) x := by
        rcases k with _ | j
        · simpa using hasDerivAt_const x (1 : ℝ)
        · convert h1.pow (j + 1) using 1
          simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
          ring
      convert (h2.const_mul (P.eval a)).mul_const (jacobiWeight α β a) using 1
      ring)
  have e : (fun t' => stj α β t' P k) = fun t' => ∫ a in Set.Ioc (0 : ℝ) 1,
      P.eval a * ((t' - a)⁻¹) ^ k * jacobiWeight α β a := by
    funext t'
    unfold stj
    rw [intervalIntegral.integral_of_le zero_le_one]
  rw [e]
  have e2 : -(k : ℝ) * stj α β t P (k + 1) = ∫ a in Set.Ioc (0 : ℝ) 1,
      -(k : ℝ) * (P.eval a * ((t - a)⁻¹) ^ (k + 1) * jacobiWeight α β a) := by
    rw [integral_const_mul]
    unfold stj
    rw [intervalIntegral.integral_of_le zero_le_one]
  rw [e2]
  exact key.2

end Deriv

/-! ### `Q_n = y_n m - q` -/

section SecondPoly

variable {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) {t : ℝ} (ht : 1 < t)
include hα hβ ht

/-- `Q_n(t) Z = y_n(t) T(1,1) - T(y_n,1)`, i.e. `Q_n = y_n m - q`. -/
theorem eval_jacobiSecondPoly_mul (n : ℕ) :
    (jacobiSecondPoly α β n).eval t * jacobiWeightMoment α β 0 =
      (jacobiShifted α β n).eval t * stj α β t 1 1 - stj α β t (jacobiShifted α β n) 1 := by
  set y := jacobiShifted α β n with hy
  have hroot : (y - C (y.eval t)).IsRoot t := by simp
  set g := (y - C (y.eval t)) /ₘ (X - C t) with hg
  have hyg : (X - C t) * g = y - C (y.eval t) := mul_divByMonic_eq_iff_isRoot.mpr hroot
  have hQ : (jacobiSecondPoly α β n).eval t = jacobiFunctional α β g := by
    have h1 : y = (X - C t) * g + C (y.eval t) := by rw [hyg]; ring
    rw [jacobiSecondPoly_eq, ← hy, h1, map_add, momentQuotient_X_sub_C_mul, momentQuotient_C,
      add_zero, ← jacobiFunctional_eq]
    simp
  rw [hQ, jacobiFunctional_mul_integral hα hβ]
  have i1 := stj_integrable hα hβ ht 1 1
  have i2 := stj_integrable hα hβ ht y 1
  unfold stj
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub (i1.const_mul _) i2]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le zero_le_one] at hs
  have hts : (t - s) ≠ 0 := (by linarith [hs.2] : 0 < t - s).ne'
  have hgs : g.eval s * (t - s) = y.eval t - y.eval s := by
    have := congrArg (eval s) hyg
    simp only [eval_mul, eval_sub, eval_X, eval_C] at this
    linarith
  have hgs' : g.eval s = (y.eval t - y.eval s) * (t - s)⁻¹ := by
    rw [← hgs]; field_simp
  simp only [eval_one, pow_one, hgs']
  ring

/-- The polynomial `Q_n` is differentiable with the derivative of `(y_n m - q)`: for `t > 1`,
`Q_n'(t) Z = y_n'(t) T(1,1) - y_n(t) T(1,2) + T(y_n,2)`. -/
theorem eval_derivative_jacobiSecondPoly_mul (n : ℕ) :
    (derivative (jacobiSecondPoly α β n)).eval t * jacobiWeightMoment α β 0 =
      (derivative (jacobiShifted α β n)).eval t * stj α β t 1 1 -
        (jacobiShifted α β n).eval t * stj α β t 1 2 + stj α β t (jacobiShifted α β n) 2 := by
  set y := jacobiShifted α β n with hy
  set Z := jacobiWeightMoment α β 0 with hZ
  have hQ1 : HasDerivAt (fun t' => (jacobiSecondPoly α β n).eval t')
      ((derivative (jacobiSecondPoly α β n)).eval t) t := (jacobiSecondPoly α β n).hasDerivAt t
  have hf : HasDerivAt (fun t' => (y.eval t' * stj α β t' 1 1 - stj α β t' y 1) / Z)
      (((derivative y).eval t * stj α β t 1 1 + y.eval t * (-(1 : ℕ) * stj α β t 1 2) -
        (-(1 : ℕ) * stj α β t y 2)) / Z) t := by
    refine HasDerivAt.div_const (HasDerivAt.sub ((y.hasDerivAt t).mul ?_) ?_) Z
    · exact hasDerivAt_stj hα hβ ht 1 1
    · exact hasDerivAt_stj hα hβ ht y 1
  have hZ0 : Z ≠ 0 := (jacobiWeightMoment_zero_pos hα hβ).ne'
  have hev : (fun t' => (y.eval t' * stj α β t' 1 1 - stj α β t' y 1) / Z) =ᶠ[𝓝 t]
      fun t' => (jacobiSecondPoly α β n).eval t' := by
    filter_upwards [Ioi_mem_nhds ht] with t' ht'
    have := eval_jacobiSecondPoly_mul hα hβ (Set.mem_Ioi.mp ht') n
    rw [← hy] at this
    rw [div_eq_iff hZ0]
    exact this.symm
  have hQ2 := hf.congr_of_eventuallyEq hev.symm
  rw [hQ1.unique hQ2]
  field_simp
  push_cast
  ring

end SecondPoly

/-! ### The Wronskian expression is constant -/

/-- The left side of the identity (2.2),
`(c+1) y_n² + σ (y_n' Q_n - y_n Q_n') + ρ y_n Q_n`. -/
noncomputable def wronskianPoly (α β : ℝ) (n : ℕ) : ℝ[X] :=
  C (α + β + 1) * jacobiShifted α β n ^ 2 +
    X * (1 - X) * (derivative (jacobiShifted α β n) * jacobiSecondPoly α β n -
      jacobiShifted α β n * derivative (jacobiSecondPoly α β n)) +
    (C α - C (α + β) * X) * jacobiShifted α β n * jacobiSecondPoly α β n

/-- The function `σ (y q' - y' q) - ρ y q` with `q = T(y,1)/Z`: the left side of (2.2) for `t > 1`
after the equation of `m` is used. -/
noncomputable def wronskianFun (α β : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (-(t * (1 - t)) * (jacobiShifted α β n).eval t * stj α β t (jacobiShifted α β n) 2 -
    t * (1 - t) * (derivative (jacobiShifted α β n)).eval t * stj α β t (jacobiShifted α β n) 1 -
    (α - (α + β) * t) * (jacobiShifted α β n).eval t * stj α β t (jacobiShifted α β n) 1) /
      jacobiWeightMoment α β 0

section Constancy

variable {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) {t : ℝ} (ht : 1 < t)
include hα hβ ht

/-- For `t > 1` the left side of (2.2) equals `σ (y q' - y' q) - ρ y q`. -/
theorem eval_wronskianPoly (n : ℕ) :
    (wronskianPoly α β n).eval t = wronskianFun α β n t := by
  have hZ0 : jacobiWeightMoment α β 0 ≠ 0 := (jacobiWeightMoment_zero_pos hα hβ).ne'
  have hQ := eval_jacobiSecondPoly_mul hα hβ ht n
  have hQ' := eval_derivative_jacobiSecondPoly_mul hα hβ ht n
  have hm := stj_m_ode hα hβ ht
  unfold wronskianPoly wronskianFun
  simp only [eval_add, eval_mul, eval_sub, eval_pow, eval_C, eval_X, eval_one]
  set Z := jacobiWeightMoment α β 0
  set y := jacobiShifted α β n
  set Q := jacobiSecondPoly α β n
  have e1 : Q.eval t = ((y.eval t) * stj α β t 1 1 - stj α β t y 1) / Z := by
    rw [eq_div_iff hZ0]; exact hQ
  have e2 : (derivative Q).eval t = ((derivative y).eval t * stj α β t 1 1 -
      y.eval t * stj α β t 1 2 + stj α β t y 2) / Z := by
    rw [eq_div_iff hZ0]; exact hQ'
  rw [e1, e2]
  field_simp
  linear_combination (y.eval t) ^ 2 * hm

/-- The function `σ (y q' - y' q) - ρ y q` has zero derivative for `t > 1`: this uses the two
differential equations of the Stieltjes transforms and the Jacobi equation. -/
theorem hasDerivAt_wronskianFun_zero (n : ℕ) : HasDerivAt (wronskianFun α β n) 0 t := by
  have hZ0 : jacobiWeightMoment α β 0 ≠ 0 := (jacobiWeightMoment_zero_pos hα hβ).ne'
  set Z := jacobiWeightMoment α β 0
  set y := jacobiShifted α β n with hy
  have hσ : HasDerivAt (fun t' : ℝ => t' * (1 - t')) (1 * (1 - t) + t * (-1)) t :=
    (hasDerivAt_id' t).mul ((hasDerivAt_id' t).const_sub 1)
  have hρ : HasDerivAt (fun t' : ℝ => α - (α + β) * t') (-((α + β) * 1)) t :=
    ((hasDerivAt_id' t).const_mul (α + β)).const_sub α
  have hy1 := y.hasDerivAt t
  have hy2 := (derivative y).hasDerivAt t
  have hU1 := hasDerivAt_stj hα hβ ht y 1
  have hU2 := hasDerivAt_stj hα hβ ht y 2
  have hG := ((((hσ.neg.mul hy1).mul hU2).sub ((hσ.mul hy2).mul hU1)).sub
    ((hρ.mul hy1).mul hU1)).div_const Z
  have hode0 : X * (1 - X) * derivative (derivative y) +
      (C (α + 1) - C (α + β + 2) * X) * derivative y +
        C ((n : ℝ) * (n + α + β + 1)) * y = 0 := jacobiShifted_ode α β n
  have hode := congrArg (Polynomial.eval t) hode0
  simp only [eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_zero] at hode
  have hq := stj_q_ode hα hβ ht y ((n : ℝ) * (n + α + β + 1))
    hode0
  have hG' : HasDerivAt (wronskianFun α β n) _ t := hG
  refine hG'.congr_deriv ?_
  simp only [Pi.neg_apply, Pi.mul_apply, Nat.reduceAdd, Nat.cast_one, Nat.cast_ofNat]
  field_simp
  linear_combination (Polynomial.eval t y) * hq - (stj α β t y 1) * hode

omit hα hβ ht in
/-- The left side of (2.2) is a constant polynomial: its derivative vanishes at every `t > 1`. -/
theorem wronskianPoly_eq_C (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    wronskianPoly α β n = C ((wronskianPoly α β n).coeff 0) := by
  have hd : derivative (wronskianPoly α β n) = 0 := by
    refine eq_zero_of_infinite_isRoot _ (Set.Infinite.mono (fun t (ht : 1 < t) => ?_)
      (Set.Ioi_infinite (1 : ℝ)))
    have h1 := (wronskianPoly α β n).hasDerivAt t
    have h2 := (hasDerivAt_wronskianFun_zero hα hβ ht n).congr_of_eventuallyEq
      (f₁ := fun t' => (wronskianPoly α β n).eval t') (by
        filter_upwards [Ioi_mem_nhds ht] with t' ht'
        exact eval_wronskianPoly hα hβ (Set.mem_Ioi.mp ht') n)
    exact h1.unique h2
  exact eq_C_of_natDegree_eq_zero (derivative_eq_zero.mp hd)

end Constancy

/-! ### The large-`t` behaviour -/

section Asymptotics

variable {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) {t : ℝ} (ht : 1 < t)
include hα hβ ht

/-- `t T(P, k+1) = T(P, k) + T(X P, k+1)`: from `u = (1 + s u)/t`. -/
theorem stj_mul_succ (P : ℝ[X]) (k : ℕ) :
    t * stj α β t P (k + 1) = stj α β t P k + stj α β t (X * P) (k + 1) := by
  have h := stj_sub_X_mul hα hβ ht P k
  rw [show (C t - X) * P = C t * P - X * P by ring, stj_sub hα hβ ht, stj_C_mul hα hβ ht] at h
  linarith

/-- Orthogonality: `T(y_n X^j, 0) = 0` for `j < n`. -/
theorem stj_jacobiShifted_mul_X_pow_zero (n j : ℕ) (hj : j < n) :
    stj α β t (jacobiShifted α β n * X ^ j) 0 = 0 := by
  rw [stj_zero hα hβ, jacobiFunctional_jacobiShifted_mul_X_pow n hα hβ j hj, zero_mul]

/-- The expansions of the Stieltjes transform `q = T(y_n, 1)/Z` and of `q' = -T(y_n, 2)/Z` at
infinity: by orthogonality the first `n` terms of `(t-s)⁻¹ = ∑ s^j t^{-j-1}` do not contribute,
so
`t^{n+1} T(y_n,1) = Z I(y_n X^n) + T(y_n X^{n+1}, 1)` and
`t^{n+2} T(y_n,2) = (n+1)(Z I(y_n X^n) + T(y_n X^{n+1},1)) + t T(y_n X^{n+1}, 2)`. -/
theorem stj_expansion (n : ℕ) :
    t ^ (n + 1) * stj α β t (jacobiShifted α β n) 1 =
        jacobiWeightMoment α β 0 * jacobiFunctional α β (jacobiShifted α β n * X ^ n) +
          stj α β t (jacobiShifted α β n * X ^ (n + 1)) 1 ∧
      t ^ (n + 2) * stj α β t (jacobiShifted α β n) 2 =
        (n + 1) * (jacobiWeightMoment α β 0 * jacobiFunctional α β (jacobiShifted α β n * X ^ n) +
          stj α β t (jacobiShifted α β n * X ^ (n + 1)) 1) +
          t * stj α β t (jacobiShifted α β n * X ^ (n + 1)) 2 := by
  set y := jacobiShifted α β n with hy
  -- `t A_m = A_{m+1}` for `m < n`
  have hA : ∀ m < n, t * stj α β t (y * X ^ m) 1 = stj α β t (y * X ^ (m + 1)) 1 := by
    intro m hm
    have h : t * stj α β t (y * X ^ m) 1 =
        stj α β t (y * X ^ m) 0 + stj α β t (X * (y * X ^ m)) 1 :=
      stj_mul_succ hα hβ ht (y * X ^ m) 0
    rw [stj_jacobiShifted_mul_X_pow_zero hα hβ ht n m hm, zero_add,
      show X * (y * X ^ m) = y * X ^ (m + 1) by ring] at h
    exact h
  have hB : ∀ m, t * stj α β t (y * X ^ m) 2 =
      stj α β t (y * X ^ m) 1 + stj α β t (y * X ^ (m + 1)) 2 := by
    intro m
    have h : t * stj α β t (y * X ^ m) 2 =
        stj α β t (y * X ^ m) 1 + stj α β t (X * (y * X ^ m)) 2 :=
      stj_mul_succ hα hβ ht (y * X ^ m) 1
    rw [h, show X * (y * X ^ m) = y * X ^ (m + 1) by ring]
  have hn0 : t * stj α β t (y * X ^ n) 1 =
      jacobiWeightMoment α β 0 * jacobiFunctional α β (y * X ^ n) +
        stj α β t (y * X ^ (n + 1)) 1 := by
    have h : t * stj α β t (y * X ^ n) 1 =
        stj α β t (y * X ^ n) 0 + stj α β t (X * (y * X ^ n)) 1 :=
      stj_mul_succ hα hβ ht (y * X ^ n) 0
    rw [stj_zero hα hβ, show X * (y * X ^ n) = y * X ^ (n + 1) by ring] at h
    linarith
  have c1 : ∀ m ≤ n, t ^ m * stj α β t y 1 = stj α β t (y * X ^ m) 1 := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      rw [pow_succ, mul_comm (t ^ m) t, mul_assoc, ih (by omega), hA m (by omega)]
  have c2 : ∀ m ≤ n, t ^ (m + 1) * stj α β t y 2 =
      t * stj α β t (y * X ^ m) 2 + m * stj α β t (y * X ^ m) 1 := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have h1 := ih (by omega)
      have h2 := hB m
      have h3 := hA m (by omega)
      have e : t ^ (m + 1 + 1) * stj α β t y 2 = t * (t ^ (m + 1) * stj α β t y 2) := by ring
      rw [e, h1]
      push_cast
      linear_combination t * h2 + ((m : ℝ) + 1) * h3
  have e1 := c1 n le_rfl
  have e2 := c2 n le_rfl
  have h2n := hB n
  refine ⟨?_, ?_⟩
  · rw [pow_succ, mul_comm (t ^ n) t, mul_assoc, e1, hn0]
  · have e : t ^ (n + 2) * stj α β t y 2 = t * (t ^ (n + 1) * stj α β t y 2) := by ring
    rw [e, e2]
    linear_combination t * h2n + (n + 1 : ℝ) * hn0

/-- `|T_t(P, k)| ≤ (∫_0^1 |P w|) (t-1)^{-k}`. -/
theorem abs_stj_le (P : ℝ[X]) (k : ℕ) :
    |stj α β t P k| ≤
      (∫ s in (0 : ℝ)..1, |P.eval s * jacobiWeight α β s|) * ((t - 1)⁻¹) ^ k := by
  have h0 : IntervalIntegrable (fun s => P.eval s * jacobiWeight α β s) volume 0 1 := by
    simpa using stj_integrable hα hβ ht P 0
  have hg : IntervalIntegrable (fun s => |P.eval s * jacobiWeight α β s| * ((t - 1)⁻¹) ^ k)
      volume 0 1 := h0.abs.mul_const _
  have := intervalIntegral.norm_integral_le_of_norm_le (a := 0) (b := 1) zero_le_one
    (f := fun s => P.eval s * ((t - s)⁻¹) ^ k * jacobiWeight α β s)
    (g := fun s => |P.eval s * jacobiWeight α β s| * ((t - 1)⁻¹) ^ k)
    (ae_of_all _ fun s hs => ?_) hg
  · rw [intervalIntegral.integral_mul_const] at this
    simpa [stj, Real.norm_eq_abs] using this
  · have hs1 := hs.2
    have hu0 : 0 < (t - s)⁻¹ := inv_pos.mpr (by linarith)
    have hu1 : (t - s)⁻¹ ≤ (t - 1)⁻¹ := inv_anti₀ (by linarith) (by linarith)
    have hpow : ((t - s)⁻¹) ^ k ≤ ((t - 1)⁻¹) ^ k := pow_le_pow_left₀ hu0.le hu1 k
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (pow_pos hu0 k)]
    calc |P.eval s| * ((t - s)⁻¹) ^ k * |jacobiWeight α β s|
        = (|P.eval s| * |jacobiWeight α β s|) * ((t - s)⁻¹) ^ k := by ring
      _ ≤ (|P.eval s| * |jacobiWeight α β s|) * ((t - 1)⁻¹) ^ k :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = |P.eval s * jacobiWeight α β s| * ((t - 1)⁻¹) ^ k := by rw [abs_mul]

omit hα hβ ht in
theorem tendsto_inv_sub_one : Tendsto (fun t : ℝ => (t - 1)⁻¹) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => t - 1) atTop atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id
  exact tendsto_inv_atTop_zero.comp h1

omit ht in
/-- `T_t(P, k) → 0` as `t → ∞`, for `k ≥ 1`. -/
theorem tendsto_stj_zero_of_pos (P : ℝ[X]) (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (fun t => stj α β t P k) atTop (𝓝 0) := by
  set K := ∫ s in (0 : ℝ)..1, |P.eval s * jacobiWeight α β s|
  have hb : Tendsto (fun t : ℝ => K * ((t - 1)⁻¹) ^ k) atTop (𝓝 0) := by
    have := ((tendsto_inv_sub_one).pow k).const_mul K
    simpa [zero_pow (by omega : k ≠ 0)] using this
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [eventually_gt_atTop 1] with t ht
  rw [Real.norm_eq_abs]
  exact abs_stj_le hα hβ ht P k

omit ht in
/-- `t T_t(P, 2) → 0` as `t → ∞`. -/
theorem tendsto_mul_stj_two (P : ℝ[X]) :
    Tendsto (fun t => t * stj α β t P 2) atTop (𝓝 0) := by
  set K := ∫ s in (0 : ℝ)..1, |P.eval s * jacobiWeight α β s|
  have hb : Tendsto (fun t : ℝ => K * ((t - 1)⁻¹ + ((t - 1)⁻¹) ^ 2)) atTop (𝓝 0) := by
    have := ((tendsto_inv_sub_one).add ((tendsto_inv_sub_one).pow 2)).const_mul K
    simpa using this
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [eventually_gt_atTop 1] with t ht
  have hb := abs_stj_le hα hβ ht P 2
  have ht0 : 0 < t := by linarith
  have hK : 0 ≤ K := intervalIntegral.integral_nonneg zero_le_one fun s _ => abs_nonneg _
  have hu : (t - 1) * (t - 1)⁻¹ = 1 := mul_inv_cancel₀ (by linarith)
  have e : t * ((t - 1)⁻¹) ^ 2 = (t - 1)⁻¹ + ((t - 1)⁻¹) ^ 2 := by
    linear_combination ((t - 1)⁻¹) * hu
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos ht0]
  calc t * |stj α β t P 2| ≤ t * (K * ((t - 1)⁻¹) ^ 2) := mul_le_mul_of_nonneg_left hb ht0.le
    _ = K * (t * ((t - 1)⁻¹) ^ 2) := by ring
    _ = K * ((t - 1)⁻¹ + ((t - 1)⁻¹) ^ 2) := by rw [e]

omit hα hβ ht in
/-- `P(t)/t^d → coeff_d P` for `deg P ≤ d`. -/
theorem tendsto_eval_div_pow (P : ℝ[X]) (d : ℕ) (hd : P.natDegree ≤ d) :
    Tendsto (fun t : ℝ => P.eval t / t ^ d) atTop (𝓝 (P.coeff d)) := by
  have h : ∀ t : ℝ, t ≠ 0 → P.eval t / t ^ d =
      ∑ i ∈ range d, P.coeff i * (t ^ i / t ^ d) + P.coeff d := by
    intro t ht0
    rw [eval_eq_sum_range' (by omega : P.natDegree < d + 1), sum_div, sum_range_succ]
    congr 1
    · refine sum_congr rfl fun i _ => ?_
      ring
    · field_simp
  have hi : ∀ i ∈ range d, Tendsto (fun t : ℝ => P.coeff i * (t ^ i / t ^ d)) atTop (𝓝 0) := by
    intro i hi
    have hid : i < d := mem_range.mp hi
    have h2 : Tendsto (fun t : ℝ => (t ^ (d - i))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by omega))
    have h3 : Tendsto (fun t : ℝ => t ^ i / t ^ d) atTop (𝓝 0) := by
      refine h2.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with t ht0
      have : t ^ d = t ^ i * t ^ (d - i) := by rw [← pow_add]; congr 1; omega
      rw [this]
      field_simp
    simpa using h3.const_mul (P.coeff i)
  have hsum := tendsto_finsetSum (range d) hi
  simp only [sum_const_zero] at hsum
  have hsum' := hsum.add_const (P.coeff d)
  rw [zero_add] at hsum'
  refine hsum'.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht0
  exact (h t ht0.ne').symm

omit ht in
/-- **The large-`t` limit.** `σ (y q' - y' q) - ρ y q → (2n + c + 1) · lc(y_n) · I(y_n X^n)`:
this is the manuscript's "orthogonality gives `q(t) = I(y_n²)/lc(y_n) · t^{-n-1} + O(t^{-n-2})`"
(with `lc(y_n) I(y_n X^n) = I(y_n²)`). -/
theorem tendsto_wronskianFun (m : ℕ) :
    Tendsto (wronskianFun α β (m + 1)) atTop
      (𝓝 ((2 * ((m + 1 : ℕ) : ℝ) + α + β + 1) * (jacobiShifted α β (m + 1)).coeff (m + 1) *
        jacobiFunctional α β (jacobiShifted α β (m + 1) * X ^ (m + 1)))) := by
  set n := m + 1 with hn
  set y := jacobiShifted α β n with hy
  set Z := jacobiWeightMoment α β 0 with hZ
  set ℓ := y.coeff n with hℓ
  set I := jacobiFunctional α β (y * X ^ n) with hI
  have hZ0 : Z ≠ 0 := (jacobiWeightMoment_zero_pos hα hβ).ne'
  have ha : Tendsto (fun t : ℝ => y.eval t / t ^ n) atTop (𝓝 ℓ) :=
    tendsto_eval_div_pow y n (natDegree_jacobiShifted_le α β n)
  have hb : Tendsto (fun t : ℝ => (derivative y).eval t / t ^ m) atTop (𝓝 (n * ℓ)) := by
    have hdd : (derivative y).natDegree ≤ m := by
      have := natDegree_derivative_le y
      have h2 : y.natDegree ≤ n := natDegree_jacobiShifted_le α β n
      omega
    have := tendsto_eval_div_pow (derivative y) m hdd
    rw [coeff_derivative] at this
    convert this using 2
    simp only [hℓ, hn]
    push_cast
    ring
  have hV1 : Tendsto (fun t : ℝ => t ^ (n + 1) * stj α β t y 1) atTop (𝓝 (Z * I)) := by
    have h1 := tendsto_stj_zero_of_pos hα hβ (y * X ^ (n + 1)) 1 le_rfl
    have h' := h1.const_add (Z * I)
    rw [add_zero] at h'
    refine h'.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with t ht
    exact ((stj_expansion hα hβ ht n).1).symm
  have hV2 : Tendsto (fun t : ℝ => t ^ (n + 2) * stj α β t y 2) atTop
      (𝓝 ((n + 1) * (Z * I))) := by
    have h1 := tendsto_stj_zero_of_pos hα hβ (y * X ^ (n + 1)) 1 le_rfl
    have h2 := tendsto_mul_stj_two hα hβ (y * X ^ (n + 1))
    have h' := (((h1.const_add (Z * I)).const_mul ((n : ℝ) + 1)).add h2)
    simp only [add_zero] at h'
    refine h'.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with t ht
    exact ((stj_expansion hα hβ ht n).2).symm
  have hs1 : Tendsto (fun t : ℝ => t⁻¹ - 1) atTop (𝓝 (-1)) := by
    simpa using tendsto_inv_atTop_zero.sub_const (1 : ℝ)
  have hr1 : Tendsto (fun t : ℝ => α * t⁻¹ - (α + β)) atTop (𝓝 (-(α + β))) := by
    simpa using (tendsto_inv_atTop_zero.const_mul α).sub_const (α + β)
  have hF := ((((hs1.neg.mul ha).mul hV2).sub ((hs1.mul hb).mul hV1)).sub
    ((hr1.mul ha).mul hV1)).div_const Z
  have e : (2 * ((m + 1 : ℕ) : ℝ) + α + β + 1) * ℓ * I =
      (((- -1 * ℓ) * ((n + 1) * (Z * I)) - (-1 * (n * ℓ)) * (Z * I)) -
        (-(α + β) * ℓ) * (Z * I)) / Z := by
    field_simp
    simp only [hn]
    push_cast
    ring
  rw [e]
  refine hF.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with t ht
  have ht0 : t ≠ 0 := by linarith
  simp only [wronskianFun, ← hy, ← hZ]
  field_simp
  simp only [hn]
  ring

end Asymptotics

/-! ### The constant and the identity -/

section Final

variable {α β : ℝ}

/-- **The Jacobi norm formula, in the form of the manuscript**: `(2n + c + 1) lc(y_n) I(y_n X^n)
= (2n + c + 1) I(y_n²) = C_n`. (`lc(y_n) = (-1)^n binom(2n + c, n)` and
`I(y_n X^n) = (-1)^n (α+1)_n (β+1)_n / (c+2)_{2n}`.) -/
theorem norm_constant_eq (hα : -1 < α) (hβ : -1 < β) (m : ℕ) :
    (2 * ((m + 1 : ℕ) : ℝ) + α + β + 1) * (jacobiShifted α β (m + 1)).coeff (m + 1) *
        jacobiFunctional α β (jacobiShifted α β (m + 1) * X ^ (m + 1)) =
      jacobiWronskianConstant α β (m + 1) := by
  have e : (2 * ((m + 1 : ℕ) : ℝ) + α + β + 1) = 2 * (m : ℝ) + α + β + 3 := by push_cast; ring
  rw [e, coeff_jacobiShifted_self,
    jacobiFunctional_jacobiShifted_mul_X_pow_self (m + 1) hα hβ, jacobiWronskianConstant_eq,
    add_tsub_cancel_right]
  have hc2 : (0 : ℝ) < α + β + 2 := by linarith
  set z : ℝ := 2 * ((m + 1 : ℕ) : ℝ) + α + β
  have hch : Ring.choose z (m + 1) * ((m + 1).factorial : ℝ) =
      (ascPochhammer ℝ (m + 1)).eval (α + β + 2 + m) := by
    have h1 := Ring.descPochhammer_eq_factorial_smul_choose z (m + 1)
    rw [descPochhammer_smeval_eq_ascPochhammer, ascPochhammer_smeval_eq_eval, nsmul_eq_mul]
      at h1
    rw [mul_comm, ← h1]
    congr 1
    simp only [z]; push_cast; ring
  have hsplitP : (ascPochhammer ℝ (2 * (m + 1))).eval (α + β + 2) =
      (ascPochhammer ℝ m).eval (α + β + 2) *
        ((ascPochhammer ℝ (m + 1)).eval (α + β + 2 + m) * (α + β + 2 * m + 3)) := by
    have h := congrArg (fun p => p.eval (α + β + 2)) (ascPochhammer_mul ℝ m (m + 2))
    simp only [eval_mul, eval_comp, eval_add, eval_X, eval_natCast] at h
    rw [show 2 * (m + 1) = m + (m + 2) by ring, ← h, show m + 2 = (m + 1) + 1 from rfl,
      ascPochhammer_succ_eval]
    push_cast; ring_nf
  have hP1 := ascPochhammer_eval_pos_of_pos m hc2
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hP2 := ascPochhammer_eval_pos_of_pos (m + 1) (show (0 : ℝ) < α + β + 2 + m by
    linarith)
  have hfac : (0 : ℝ) < ((m + 1).factorial : ℝ) := by positivity
  have h3 : (0 : ℝ) < α + β + 2 * m + 3 := by linarith
  have hs : ((-1 : ℝ) ^ (m + 1)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hchoose : Ring.choose z (m + 1) =
      (ascPochhammer ℝ (m + 1)).eval (α + β + 2 + m) / ((m + 1).factorial : ℝ) :=
    eq_div_of_mul_eq hfac.ne' hch
  rw [hsplitP, hchoose]
  field_simp
  rw [hs]
  ring

/-- **Lemma 2.1, identity (2.2), by the Stieltjes-transform argument of the manuscript** (for real
`α, β > -1`): `(c+1) y_n² + σ (y_n' Q_n - y_n Q_n') + ρ y_n Q_n = C_n`. The left side is constant
(`wronskianPoly_eq_C`: differentiate and use the equations of `m` and `q`), its value is the limit
as `t → ∞` computed from the expansion of `q` (`tendsto_wronskianFun`), which is
`(2n+c+1) I(y_n²) = C_n` (`norm_constant_eq`). -/
theorem jacobi_wronskian_stieltjes (hα : -1 < α) (hβ : -1 < β) {n : ℕ} (hn : 1 ≤ n) :
    C (α + β + 1) * jacobiShifted α β n ^ 2 +
      X * (1 - X) * (derivative (jacobiShifted α β n) * jacobiSecondPoly α β n -
        jacobiShifted α β n * derivative (jacobiSecondPoly α β n)) +
      (C α - C (α + β) * X) * jacobiShifted α β n * jacobiSecondPoly α β n =
    C (jacobiWronskianConstant α β n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hW := wronskianPoly_eq_C hα hβ (m + 1)
  have hlim := tendsto_wronskianFun hα hβ m
  have hconst : Tendsto (wronskianFun α β (m + 1)) atTop
      (𝓝 ((wronskianPoly α β (m + 1)).coeff 0)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with t ht
    rw [← eval_wronskianPoly hα hβ ht, hW]
    simp
  have := tendsto_nhds_unique hconst hlim
  rw [norm_constant_eq hα hβ m] at this
  change wronskianPoly α β (m + 1) = C (jacobiWronskianConstant α β (m + 1))
  rw [hW, this]

end Final

end ArithmeticOfJacobiPolynomials.JacobiGeneric.Real
