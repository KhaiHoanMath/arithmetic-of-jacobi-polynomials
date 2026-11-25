/- Assembled by AxiomProver. -/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The sharp remainder of the artanh series (Appendix B.2)

For `0 ≤ t < 1` (the manuscript uses `0 ≤ t ≤ 1/3`) and every `r`,
`log ((1+t)/(1-t)) = 2 ∑_{j<r} t^{2j+1}/(2j+1) + 𝓔_r(t)` with
`0 ≤ 𝓔_r(t) ≤ 2 t^{2r+1} / ((2r+1)(1-t²))`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Real Finset

/-- The remainder `𝓔_r(t)` of the artanh series. -/
noncomputable def artanhRemainder (r : ℕ) (t : ℝ) : ℝ :=
  log ((1 + t) / (1 - t)) - 2 * ∑ j ∈ range r, t ^ (2 * j + 1) / (2 * j + 1)

theorem artanhRemainder_eq (r : ℕ) (t : ℝ) : artanhRemainder r t =
    log ((1 + t) / (1 - t)) - 2 * ∑ j ∈ range r, t ^ (2 * j + 1) / (2 * j + 1) := (rfl)

/-- The remainder is the tail `2 ∑_{j ≥ r} t^{2j+1}/(2j+1)`. -/
theorem hasSum_artanhRemainder (r : ℕ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) :
    HasSum (fun j : ℕ => 2 * (t ^ (2 * (j + r) + 1) / (2 * ((j + r : ℕ) : ℝ) + 1)))
      (artanhRemainder r t) := by
  have habs : |t| < 1 := by rw [abs_of_nonneg h0]; exact h1
  have h := Real.hasSum_log_sub_log_of_abs_lt_one habs
  have h' := (hasSum_nat_add_iff' (f := fun k : ℕ => (2 : ℝ) * (1 / (2 * k + 1)) *
    t ^ (2 * k + 1)) r).mpr h
  have e1 : log (1 + t) - log (1 - t) = log ((1 + t) / (1 - t)) :=
    (log_div (by linarith) (by linarith)).symm
  rw [artanhRemainder_eq, ← e1, mul_sum]
  convert h' using 1
  · funext j
    push_cast
    ring
  · congr 1
    refine sum_congr rfl fun j _ => ?_
    ring

/-- **Appendix B.2.** `0 ≤ 𝓔_r(t) ≤ 2 t^{2r+1} / ((2r+1)(1-t²))` for `0 ≤ t < 1`. -/
theorem artanhRemainder_bounds (r : ℕ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) :
    0 ≤ artanhRemainder r t ∧
      artanhRemainder r t ≤ 2 * t ^ (2 * r + 1) / ((2 * r + 1) * (1 - t ^ 2)) := by
  have hS := hasSum_artanhRemainder r h0 h1
  have ht2 : t ^ 2 < 1 := by nlinarith
  have hr : (0 : ℝ) < 2 * r + 1 := by positivity
  constructor
  · exact hS.nonneg fun j => by positivity
  · -- compare with the geometric series `2 t^{2r+1}/(2r+1) ∑ (t²)^j`
    have hG := (hasSum_geometric_of_lt_one (sq_nonneg t) ht2).mul_left
      (2 * t ^ (2 * r + 1) / (2 * r + 1))
    have hle := hasSum_le (fun j : ℕ => ?_) hS hG
    · calc artanhRemainder r t ≤ 2 * t ^ (2 * r + 1) / (2 * r + 1) * (1 - t ^ 2)⁻¹ := hle
        _ = 2 * t ^ (2 * r + 1) / ((2 * r + 1) * (1 - t ^ 2)) := by
          have h3 : (1 - t ^ 2) ≠ 0 := by linarith
          field_simp
    · have hpow : t ^ (2 * (j + r) + 1) = t ^ (2 * r + 1) * (t ^ 2) ^ j := by
        rw [← pow_mul, ← pow_add]; ring_nf
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have hden : (2 * (r : ℝ) + 1) ≤ 2 * ((j + r : ℕ) : ℝ) + 1 := by push_cast; linarith
      rw [hpow]
      have hnum : 0 ≤ t ^ (2 * r + 1) * (t ^ 2) ^ j := by positivity
      calc 2 * (t ^ (2 * r + 1) * (t ^ 2) ^ j / (2 * ((j + r : ℕ) : ℝ) + 1))
          ≤ 2 * (t ^ (2 * r + 1) * (t ^ 2) ^ j / (2 * r + 1)) := by
            gcongr
        _ = 2 * t ^ (2 * r + 1) / (2 * r + 1) * (t ^ 2) ^ j := by ring

/-- The manuscript's range `0 ≤ t ≤ 1/3`. -/
theorem artanhRemainder_bounds_third (r : ℕ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 3) :
    0 ≤ artanhRemainder r t ∧
      artanhRemainder r t ≤ 2 * t ^ (2 * r + 1) / ((2 * r + 1) * (1 - t ^ 2)) :=
  artanhRemainder_bounds r h0 (by linarith)

end ArithmeticOfJacobiPolynomials
