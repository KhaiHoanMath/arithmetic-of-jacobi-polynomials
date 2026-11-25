/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.MomentFunctional
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The limit of the Wronskian constant (Lemma 2.1)

Lemma 2.1 of the manuscript states that for `α, β > -1` the constant
`C_n = (α+1)_n (β+1)_n / (n! (α+β+2)_{n-1})` tends to
`Γ(α+β+2) / (Γ(α+1) Γ(β+1)) > 0`. We derive this from Mathlib's Gauss product formula
`Real.GammaSeq_tendsto_Gamma`, with no further input.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset Filter Topology

/-- The rising factorial as a finite product. -/
theorem ascPochhammer_eval_eq_prod_range (s : ℝ) (n : ℕ) :
    (ascPochhammer ℝ n).eval s = ∏ j ∈ range n, (s + j) := by
  induction n with
  | zero => simp
  | succ n ih => rw [ascPochhammer_succ_eval, ih, prod_range_succ]

/-- The rising factorial commutes with the cast `ℚ → ℝ`. -/
theorem ascPochhammer_eval_ratCast (q : ℚ) (n : ℕ) :
    (((ascPochhammer ℚ n).eval q : ℚ) : ℝ) = (ascPochhammer ℝ n).eval (q : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih => rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval]; push_cast; rw [ih]

/-- `Real.GammaSeq s n = n^s n! / (s)_{n+1}`. -/
theorem gammaSeq_eq_ascPochhammer (s : ℝ) (n : ℕ) :
    Real.GammaSeq s n = (n : ℝ) ^ s * n.factorial / (ascPochhammer ℝ (n + 1)).eval s := by
  rw [Real.GammaSeq, ascPochhammer_eval_eq_prod_range]

/-- For `n ≥ 1`, the real Wronskian constant is a ratio of Gauss sequences times an explicit
rational factor. -/
theorem jacobiWronskianConstant_eq_gammaSeq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {n : ℕ}
    (hn : 1 ≤ n) :
    (ascPochhammer ℝ n).eval a * (ascPochhammer ℝ n).eval b /
        ((n.factorial : ℝ) * (ascPochhammer ℝ (n - 1)).eval (a + b)) =
      Real.GammaSeq (a + b) n / (Real.GammaSeq a n * Real.GammaSeq b n) *
        ((n / (n + a)) * (n / (n + b)) / ((n / (n + (a + b - 1))) * (n / (n + (a + b))))) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [gammaSeq_eq_ascPochhammer, gammaSeq_eq_ascPochhammer, gammaSeq_eq_ascPochhammer]
  have hx : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hpow : ((m + 1 : ℕ) : ℝ) ^ (a + b) =
      ((m + 1 : ℕ) : ℝ) ^ a * ((m + 1 : ℕ) : ℝ) ^ b := Real.rpow_add hx a b
  have hPa := ascPochhammer_pos (m + 1) a ha
  have hPb := ascPochhammer_pos (m + 1) b hb
  have hPs := ascPochhammer_pos m (a + b) (by linarith)
  have hxa : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) ^ a := Real.rpow_pos_of_pos hx a
  have hxb : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) ^ b := Real.rpow_pos_of_pos hx b
  have hf : (0 : ℝ) < ((m + 1).factorial : ℝ) := by positivity
  rw [ascPochhammer_succ_eval (m + 1) a, ascPochhammer_succ_eval (m + 1) b,
    ascPochhammer_succ_eval (m + 1) (a + b), ascPochhammer_succ_eval m (a + b), hpow]
  push_cast
  have h1 : (0 : ℝ) < a + b + m := by positivity
  have h2 : (0 : ℝ) < a + b + (m + 1) := by positivity
  have h3 : (0 : ℝ) < a + (m + 1) := by positivity
  have h4 : (0 : ℝ) < b + (m + 1) := by positivity
  have h5 : (0 : ℝ) < (m + 1 : ℝ) + (a + b - 1) := by linarith
  have h6 : (0 : ℝ) < (m + 1 : ℝ) + (a + b) := by linarith
  have h7 : (0 : ℝ) < (m + 1 : ℝ) + a := by linarith
  have h8 : (0 : ℝ) < (m + 1 : ℝ) + b := by linarith
  push_cast at hxa hxb hf hx
  field_simp
  ring

/-- **Lemma 2.1, the limit of `C_n`.** For rational `α, β > -1`,
`C_n → Γ(α+β+2) / (Γ(α+1) Γ(β+1))`, and this limit is positive. -/
theorem tendsto_jacobiWronskianConstant {α β : ℚ} (hα : -1 < α) (hβ : -1 < β) :
    Tendsto (fun n => (jacobiWronskianConstant α β n : ℝ)) atTop
        (𝓝 (Real.Gamma (α + β + 2) / (Real.Gamma (α + 1) * Real.Gamma (β + 1)))) ∧
      0 < Real.Gamma (α + β + 2) / (Real.Gamma (α + 1) * Real.Gamma (β + 1)) := by
  set a : ℝ := (α : ℝ) + 1 with hadef
  set b : ℝ := (β : ℝ) + 1 with hbdef
  have ha : 0 < a := by rw [hadef]; exact_mod_cast (show (0 : ℚ) < α + 1 by linarith)
  have hb : 0 < b := by rw [hbdef]; exact_mod_cast (show (0 : ℚ) < β + 1 by linarith)
  have hs : (α : ℝ) + β + 2 = a + b := by rw [hadef, hbdef]; ring
  rw [hs]
  have hGa := Real.Gamma_pos_of_pos ha
  have hGb := Real.Gamma_pos_of_pos hb
  have hGs := Real.Gamma_pos_of_pos (add_pos ha hb)
  refine ⟨?_, by positivity⟩
  have hlim : Tendsto (fun n : ℕ => Real.GammaSeq (a + b) n /
      (Real.GammaSeq a n * Real.GammaSeq b n) *
        (((n : ℝ) / (n + a)) * ((n : ℝ) / (n + b)) /
          (((n : ℝ) / (n + (a + b - 1))) * ((n : ℝ) / (n + (a + b))))))
      atTop (𝓝 (Real.Gamma (a + b) / (Real.Gamma a * Real.Gamma b) * (1 * 1 / (1 * 1)))) := by
    refine Tendsto.mul (Tendsto.div (Real.GammaSeq_tendsto_Gamma _)
      ((Real.GammaSeq_tendsto_Gamma _).mul (Real.GammaSeq_tendsto_Gamma _)) (by positivity)) ?_
    exact Tendsto.div ((tendsto_natCast_div_add_atTop a).mul (tendsto_natCast_div_add_atTop b))
      ((tendsto_natCast_div_add_atTop _).mul (tendsto_natCast_div_add_atTop _)) (by norm_num)
  simp only [mul_one, div_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [← jacobiWronskianConstant_eq_gammaSeq ha hb hn, jacobiWronskianConstant_eq]
  push_cast
  rw [ascPochhammer_eval_ratCast, ascPochhammer_eval_ratCast, ascPochhammer_eval_ratCast]
  push_cast
  first
    | done
    | (simp only [hadef, hbdef]; ring_nf)

end ArithmeticOfJacobiPolynomials
