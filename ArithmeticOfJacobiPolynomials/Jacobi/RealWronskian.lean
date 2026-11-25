/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.OrderedWronskian
public import ArithmeticOfJacobiPolynomials.Jacobi.WronskianLimit

/-!
# Lemma 2.1 for the manuscript's real parameters

The coefficient and Wronskian proofs in `Wronskian` work over ordered fields.
Here the paper's positive-measure quadrature argument gives the real root bound.
`jacobi_root_derivative_lower_of_wronskian` takes the identity (2.2) as a hypothesis; the main
chain supplies it from the manuscript's Stieltjes argument (`SourceStieltjesRational`). The
algebraic proofs of (2.2) in `Wronskian` and `OrderedWronskian` give independent versions of the
root bound.
-/

public section

namespace ArithmeticOfJacobiPolynomials.JacobiGeneric.Real

open Polynomial Finset Filter Topology MeasureTheory

/-- The Jacobi moments are the normalized moments of the Jacobi weight:
`μ_j = ∫_0^1 t^j t^α (1-t)^β dt / ∫_0^1 t^α (1-t)^β dt` (2.2). -/
theorem jacobiWeightMoment_eq_jacobiMoment {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (j : ℕ) :
    jacobiWeightMoment α β j = (jacobiMoment α β j : ℝ) * jacobiWeightMoment α β 0 := by
  have hα' : (-1 : ℝ) < α := by exact hα
  have hβ' : (-1 : ℝ) < β := by exact hβ
  induction j with
  | zero => rw [jacobiMoment_zero]; simp
  | succ j ih =>
    have h1 := jacobiWeightMoment_succ hα' hβ' j
    have h2 := jacobiMoment_succ (α := α) (β := β) (by linarith) j
    have h2' : jacobiMoment α β (j + 1) * ((α : ℝ) + β + 2 + j) =
        (jacobiMoment α β j : ℝ) * ((α : ℝ) + 1 + j) := by exact h2
    have hpos : (0 : ℝ) < (α : ℝ) + β + 2 + j := by
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    apply mul_right_cancel₀ hpos.ne'
    rw [h1, ih]
    linear_combination (jacobiWeightMoment α β 0) * h2'.symm

/-- **Integral representation** of the Jacobi functional:
`I(f) · ∫_0^1 t^α (1-t)^β dt = ∫_0^1 f(t) t^α (1-t)^β dt`. -/
theorem jacobiFunctional_mul_integral {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (f : ℝ[X]) :
    jacobiFunctional α β f * jacobiWeightMoment α β 0 =
      ∫ x in (0 : ℝ)..1, f.eval x * jacobiWeight α β x := by
  have hα' : (-1 : ℝ) < α := by exact hα
  have hβ' : (-1 : ℝ) < β := by exact hβ
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, add_mul, hp, hq, ← intervalIntegral.integral_add
      (intervalIntegrable_eval_mul_jacobiWeight hα' hβ' p)
      (intervalIntegrable_eval_mul_jacobiWeight hα' hβ' q)]
    simp only [eval_add, add_mul]
  | monomial j c =>
    rw [jacobiFunctional_eq, momentFunctional_monomial]
    simp only [eval_monomial]
    rw [show (fun x => c * x ^ j * jacobiWeight α β x) =
        fun x => c * (x ^ j * jacobiWeight α β x) by ext; ring,
      intervalIntegral.integral_const_mul, ← jacobiWeightMoment_eq,
      jacobiWeightMoment_eq_jacobiMoment hα hβ j]
    ring

/-- Positivity: `I(f²) > 0` for every nonzero real polynomial `f`. -/
theorem jacobiFunctional_mul_self_pos {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) {f : ℝ[X]}
    (hf : f ≠ 0) : 0 < jacobiFunctional α β (f * f) := by
  have hα' : (-1 : ℝ) < α := by exact hα
  have hβ' : (-1 : ℝ) < β := by exact hβ
  have hZ := jacobiWeightMoment_zero_pos hα' hβ'
  have hI := jacobiFunctional_mul_integral hα hβ (f * f)
  suffices h : 0 < ∫ x in (0 : ℝ)..1, (f * f).eval x * jacobiWeight α β x by
    rw [← hI] at h; exact pos_of_mul_pos_left h hZ.le
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae'
    (ae_restrict_of_forall_mem measurableSet_uIoc fun x hx => ?_)
    (intervalIntegrable_eval_mul_jacobiWeight hα' hβ' _)]
  · refine ⟨zero_lt_one, ?_⟩
    have hS := Polynomial.finite_setOfPred_isRoot hf
    have hsub : Set.Ioo (0 : ℝ) 1 \ {x | f.IsRoot x} ⊆
        Function.support (fun x => (f * f).eval x * jacobiWeight α β x) ∩ Set.Ioc 0 1 := by
      intro x ⟨hx, hxr⟩
      refine ⟨?_, hx.1, hx.2.le⟩
      have hfx : f.eval x ≠ 0 := hxr
      simp only [Function.mem_support, eval_mul]
      exact (mul_pos (mul_self_pos.mpr hfx) (jacobiWeight_pos _ _ hx)).ne'
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [measure_sdiff_null (hS.measure_zero _), Real.volume_Ioo]
    norm_num
  · rw [Set.uIoc_of_le zero_le_one] at hx
    simp only [Pi.zero_apply, eval_mul]
    exact mul_nonneg (mul_self_nonneg _) (jacobiWeight_nonneg _ _ hx.1.le hx.2)

/-- Nonnegativity: `I(f²) ≥ 0` for every real polynomial `f`. -/
theorem jacobiFunctional_mul_self_nonneg {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (f : ℝ[X]) : 0 ≤ jacobiFunctional α β (f * f) := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · exact (jacobiFunctional_mul_self_pos hα hβ hf).le

/-- Orthogonality against every polynomial of degree less than `n`. -/
theorem jacobiFunctional_jacobiShifted_mul_of_natDegree_lt {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (n : ℕ) {h : ℝ[X]} (hh : h.natDegree < n) :
    jacobiFunctional α β (jacobiShifted α β n * h) = 0 := by
  conv_lhs => rw [as_sum_range' h n hh]
  rw [mul_sum, map_sum]
  refine sum_eq_zero fun k hk => ?_
  rw [← C_mul_X_pow_eq_monomial, mul_left_comm, jacobiFunctional_C_mul,
    jacobiFunctional_jacobiShifted_mul_X_pow n hα hβ k (by simpa using hk), mul_zero]

/-- **Lemma 2.1, root bound (2.4)**, for any proof of the Wronskian identity (2.2). At every real
root `t` of `y_n` one has `|y_n'(t)| ≥ 2 √C_n`; moreover `0 < t < 1`. The proof uses the Gaussian
quadrature weight `ω = I(ℓ) = I(ℓ²) > 0` of `t`, where `ℓ = y_n / ((X - t) y_n'(t))`, and the
root identity `C_n = t(1-t) y_n'(t)² ω`. -/
theorem jacobi_root_derivative_lower_of_wronskian {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) {n : ℕ}
    (hn : 1 ≤ n)
    (hWr : C (α + β + 1) * jacobiShifted α β n ^ 2 +
      X * (1 - X) * (derivative (jacobiShifted α β n) * jacobiSecondPoly α β n -
        jacobiShifted α β n * derivative (jacobiSecondPoly α β n)) +
      (C α - C (α + β) * X) * jacobiShifted α β n * jacobiSecondPoly α β n =
    C (jacobiWronskianConstant α β n)) {t : ℝ} (ht : aeval t (jacobiShifted α β n) = 0) :
    2 * Real.sqrt (jacobiWronskianConstant α β n) ≤
        |aeval t (derivative (jacobiShifted α β n))| ∧ 0 < t ∧ t < 1 := by
  set y := jacobiShifted α β n with hy
  set yR := y with hyR
  have hroot : yR.IsRoot t := by simpa [IsRoot, hyR] using ht
  set g := yR /ₘ (X - C t) with hg
  have hyg : (X - C t) * g = yR := mul_divByMonic_eq_iff_isRoot.mpr hroot
  have hder : aeval t (derivative y) = g.eval t := by
    rw [aeval_def, Algebra.algebraMap_self, eval₂_id, ← hyR, ← hyg, derivative_mul]; simp
  have hQ : aeval t (jacobiSecondPoly α β n) = jacobiFunctional α β g := by
    rw [aeval_def, Algebra.algebraMap_self, eval₂_id, jacobiSecondPoly_eq, ← hy,
      ← hyg, momentQuotient_X_sub_C_mul, ← jacobiFunctional_eq]
    simp
  have hW := congrArg (aeval t) hWr
  simp only [map_add, map_mul, map_sub, map_pow, aeval_C, aeval_X, map_one, ht] at hW
  rw [hder, hQ] at hW
  set u := g.eval t
  set v := jacobiFunctional α β g
  set Cn : ℝ := (jacobiWronskianConstant α β n : ℝ)
  have hC : 0 < Cn := by
    simp only [Cn]; exact jacobiWronskianConstant_pos hα hβ n
  have key : t * (1 - t) * (u * v) = Cn := by
    have : algebraMap ℝ ℝ (jacobiWronskianConstant α β n) = Cn := by simp [Cn]
    rw [this] at hW
    linear_combination hW
  -- degrees
  have hgdeg : g.natDegree < n := by
    rw [hg, natDegree_divByMonic _ (monic_X_sub_C t), natDegree_X_sub_C]
    have : yR.natDegree ≤ n := natDegree_jacobiShifted_le α β n
    omega
  set h := (g - C u) /ₘ (X - C t) with hh
  have hgh : (X - C t) * h = g - C u :=
    mul_divByMonic_eq_iff_isRoot.mpr (by simp [IsRoot, u])
  have hhdeg : h.natDegree < n := by
    rw [hh, natDegree_divByMonic _ (monic_X_sub_C t), natDegree_sub_C]; omega
  -- `I(g²) = g(t) I(g)`
  have hgg : jacobiFunctional α β (g * g) = u * v := by
    have e : g * g = C u * g + yR * h := by
      rw [← hyg]; linear_combination (-g) * hgh
    rw [e, map_add, jacobiFunctional_eq, momentFunctional_C_mul, ← jacobiFunctional_eq,
      jacobiFunctional_jacobiShifted_mul_of_natDegree_lt hα hβ n hhdeg, add_zero]
  have hg0 : g ≠ 0 := by
    intro h0
    have : u = 0 := by simp [u, h0]
    rw [this] at key; simp at key; linarith
  have hpos : 0 < u * v := hgg ▸ jacobiFunctional_mul_self_pos hα hβ hg0
  -- Cauchy–Schwarz: `I(g)² ≤ I(g²)`
  have hCS : v ^ 2 ≤ u * v := by
    have h0 := jacobiFunctional_mul_self_nonneg hα hβ (g - C v)
    have e : (g - C v) * (g - C v) = g * g - C (2 * v) * g + C (v ^ 2) := by
      simp only [C_mul, C_pow, C_ofNat]; ring
    rw [e, map_add, map_sub, jacobiFunctional_eq, momentFunctional_C_mul, momentFunctional_C,
      ← jacobiFunctional_eq, hgg] at h0
    simp only [jacobiMoment_zero, one_mul] at h0
    nlinarith
  have hσ : 0 < t * (1 - t) := by
    by_contra hcon
    rw [not_lt] at hcon
    nlinarith
  have ht0 : 0 < t := by
    by_contra h'; rw [not_lt] at h'; nlinarith
  have ht1 : t < 1 := by
    by_contra h'; rw [not_lt] at h'; nlinarith
  refine ⟨?_, ht0, ht1⟩
  rw [hder]
  have h4 : 4 * Cn ≤ u ^ 2 := by nlinarith [sq_nonneg (t - 1 / 2), sq_nonneg (u - v)]
  have hs := Real.sq_sqrt hC.le
  have hs0 := Real.sqrt_nonneg Cn
  nlinarith [abs_nonneg u, sq_abs u]

/-- **Lemma 2.1, root bound (2.4)**, from the algebraic Wronskian identity (2.2). -/
theorem jacobi_root_derivative_lower {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) {n : ℕ}
    (hn : 1 ≤ n) {t : ℝ} (ht : aeval t (jacobiShifted α β n) = 0) :
    2 * Real.sqrt (jacobiWronskianConstant α β n) ≤
        |aeval t (derivative (jacobiShifted α β n))| ∧ 0 < t ∧ t < 1 :=
  jacobi_root_derivative_lower_of_wronskian hα hβ hn (jacobi_wronskian hα hβ hn) ht

/-- **Lemma 2.1, the limit of `C_n`.** For real `α, β > -1`,
`C_n → Γ(α+β+2) / (Γ(α+1) Γ(β+1))`, and this limit is positive. -/
theorem tendsto_jacobiWronskianConstant {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    Tendsto (fun n => (jacobiWronskianConstant α β n : ℝ)) atTop
        (𝓝 (Real.Gamma (α + β + 2) / (Real.Gamma (α + 1) * Real.Gamma (β + 1)))) ∧
      0 < Real.Gamma (α + β + 2) / (Real.Gamma (α + 1) * Real.Gamma (β + 1)) := by
  set a : ℝ := (α : ℝ) + 1 with hadef
  set b : ℝ := (β : ℝ) + 1 with hbdef
  have ha : 0 < a := by rw [hadef]; exact (show (0 : ℝ) < α + 1 by linarith)
  have hb : 0 < b := by rw [hbdef]; exact (show (0 : ℝ) < β + 1 by linarith)
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
  simp only [hadef, hbdef]
  congr 3
  ring

end ArithmeticOfJacobiPolynomials.JacobiGeneric.Real
