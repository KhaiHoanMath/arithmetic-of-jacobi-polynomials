/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.External
public import ArithmeticOfJacobiPolynomials.Jacobi.Legendre
public import ArithmeticOfJacobiPolynomials.Jacobi.SymmetricCoefficients
public import ArithmeticOfJacobiPolynomials.Analysis.Margins
public import Mathlib.Analysis.Calculus.LocalExtr.Rolle
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Prose claims of the manuscript outside the theorem environments

* **Rolle interlacing of the critical points of `P_ℓ`** (§1.2: "Rolle's theorem places
  these critical points between consecutive zeros"). For a real polynomial
  `c ∏_{s ∈ S} (X - s)` with distinct real roots, every critical point lies strictly between
  two consecutive roots, and between two consecutive roots there is exactly one critical point
  (`prod_X_sub_C_criticalPoints_interlace`, using Rolle and the strict decrease of
  `∑_s 1/(t - s)` between consecutive roots). For the Legendre polynomials this is
  `legendreP_criticalPoints_interlace`, conditional on `JacobiSimpleRealZeros`
  ([DLMF, §18.2(vi)], the zeros of `P_ℓ` are real and simple).
* **The minimizer `q_n` of the finite criterion** (§4.5). The part
  `h(z) = a z + 2 log 2 / z - log z` of `𝓗_n(z)` depending on `z` is strictly decreasing on
  `(0, ∞)` if `a ≤ 0` (`finiteCriterionProfile_strictAntiOn_of_nonpos`); if `a > 0`, it is
  strictly decreasing on `(0, q]` and strictly increasing on `[q, ∞)` with
  `q = (1 + √(1 + 8 a log 2)) / (2a)` (`finiteCriterionProfile_strictAntiOn_Ioc`,
  `finiteCriterionProfile_strictMonoOn_Ici`), so `q` is its unique minimizer on `(0, ∞)`
  (`finiteCriterionProfile_lt_of_ne`).
* **The associated-Legendre constraint on the cone** (§6.3): if `1 ≤ r ≤ ℓ` and
  `P_ℓ^{(r)}(1/√3) = 0`, then `r² < (2/3) ℓ(ℓ+1)` (`sq_lt_of_aeval_inv_sqrt_three_eq_zero`),
  by the manuscript's integration by parts on `[1/√3, 1]` in polynomial form
  (`derivative_associatedLegendreFlux`). Unconditional.
* **The decimal values** (§4.4) of `𝔩 = log(4 + 3√3) - ½ log 2 - ⅓ log 3 - π/(2√3)`
  and `𝔲 = 43/20 - π/√3`, certified by rational bounds: `0.5991078130 < 𝔩 < 0.5991078131`
  (`frakL_bounds`), `0.3362006357 < 𝔲 < 0.3362006358` (`frakU_bounds`; the true value is
  `0.33620063576…`, so the manuscript's `0.3362006358…` is rounded rather than truncated) and
  `0.2629071772 < 𝔩 - 𝔲 < 0.2629071773` (`frakL_sub_frakU_bounds`). The inputs are `π` to
  twenty digits, `√3` to sixteen digits and the series bounds `two_mul_sum_le_log_div`,
  `log_div_le_two_mul_sum_add` for `log 2`, `log(3/2)` and
  `log((4 + 3√3)/9) = log((1 + z)/(1 - z))`, `z = (27√3 - 46)/71`, bracketed by rational `z`.
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset Real

/-! ### Rolle interlacing for a polynomial with distinct real roots -/

section Interlacing

theorem eval_prod_X_sub_C_mul (S : Finset ℝ) (c t : ℝ) :
    (C c * ∏ s ∈ S, (polyX - C s)).eval t = c * ∏ s ∈ S, (t - s) := by
  rw [eval_mul, eval_C, eval_prod]
  simp only [eval_sub, eval_X, eval_C]

theorem eval_derivative_prod_X_sub_C_mul (S : Finset ℝ) (c t : ℝ) :
    (derivative (C c * ∏ s ∈ S, (polyX - C s))).eval t =
      c * ∑ s ∈ S, ∏ u ∈ S.erase s, (t - u) := by
  rw [derivative_C_mul, derivative_prod_finset, eval_mul, eval_C, eval_finsetSum]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [derivative_sub, derivative_X, derivative_C, sub_zero, mul_one, eval_prod]
  simp only [eval_sub, eval_X, eval_C]

theorem isRoot_prod_X_sub_C_mul_iff {S : Finset ℝ} {c : ℝ} (hc : c ≠ 0) {t : ℝ} :
    (C c * ∏ s ∈ S, (polyX - C s)).IsRoot t ↔ t ∈ S := by
  rw [IsRoot.def, eval_prod_X_sub_C_mul, mul_eq_zero, prod_eq_zero_iff]
  simp [hc, sub_eq_zero]

/-- The roots are simple: the derivative does not vanish at a root. -/
theorem eval_derivative_prod_X_sub_C_mul_ne_zero {S : Finset ℝ} {c : ℝ} (hc : c ≠ 0) {t : ℝ}
    (ht : t ∈ S) : (derivative (C c * ∏ s ∈ S, (polyX - C s))).eval t ≠ 0 := by
  rw [eval_derivative_prod_X_sub_C_mul, Finset.sum_eq_single t]
  · exact mul_ne_zero hc
      (prod_ne_zero_iff.mpr fun u hu => sub_ne_zero.mpr (ne_of_mem_erase hu).symm)
  · intro s _ hst
    exact prod_eq_zero (mem_erase.mpr ⟨fun h => hst h.symm, ht⟩) (sub_self t)
  · intro h
    exact absurd ht h

/-- Away from the roots, `p'(t) = p(t) ∑_s 1/(t - s)`. -/
theorem eval_derivative_prod_X_sub_C_mul_eq {S : Finset ℝ} (c : ℝ) {t : ℝ} (ht : t ∉ S) :
    (derivative (C c * ∏ s ∈ S, (polyX - C s))).eval t =
      (C c * ∏ s ∈ S, (polyX - C s)).eval t * ∑ s ∈ S, (t - s)⁻¹ := by
  rw [eval_derivative_prod_X_sub_C_mul, eval_prod_X_sub_C_mul, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hts : t - s ≠ 0 := sub_ne_zero.mpr fun h => ht (h ▸ hs)
  have e : (t - s) * (t - s)⁻¹ = 1 := mul_inv_cancel₀ hts
  have hsplit : ∏ u ∈ S, (t - u) = (t - s) * ∏ u ∈ S.erase s, (t - u) :=
    (Finset.mul_prod_erase S (fun u => t - u) hs).symm
  rw [hsplit]
  linear_combination (-(c * ∏ u ∈ S.erase s, (t - u))) * e

/-- A critical point is not a root, and there `∑_s 1/(ξ - s) = 0`. -/
theorem sum_inv_eq_zero_of_isRoot_derivative {S : Finset ℝ} {c : ℝ} (hc : c ≠ 0) {ξ : ℝ}
    (hξ : (derivative (C c * ∏ s ∈ S, (polyX - C s))).IsRoot ξ) :
    ξ ∉ S ∧ ∑ s ∈ S, (ξ - s)⁻¹ = 0 := by
  have hξ0 := IsRoot.def.mp hξ
  have hξS : ξ ∉ S := fun h => eval_derivative_prod_X_sub_C_mul_ne_zero hc h hξ0
  have hp0 : (C c * ∏ s ∈ S, (polyX - C s)).eval ξ ≠ 0 := fun h =>
    hξS ((isRoot_prod_X_sub_C_mul_iff hc).mp (IsRoot.def.mpr h))
  have h := eval_derivative_prod_X_sub_C_mul_eq c hξS
  rw [hξ0] at h
  exact ⟨hξS, (mul_eq_zero.mp h.symm).resolve_left hp0⟩

theorem inv_sub_eq_neg_inv_sub (a s : ℝ) : (a - s)⁻¹ = -(s - a)⁻¹ := by
  rw [← neg_sub, inv_neg]

/-- Between consecutive roots, `t ↦ ∑_s 1/(t - s)` is strictly decreasing. -/
theorem sum_inv_sub_lt_of_consecutive {S : Finset ℝ} (hS : S.Nonempty) {x y : ℝ}
    (hcons : ∀ t, x < t → t < y → t ∉ S) {ξ₁ ξ₂ : ℝ} (h1 : x < ξ₁) (h12 : ξ₁ < ξ₂)
    (h2 : ξ₂ < y) : ∑ s ∈ S, (ξ₂ - s)⁻¹ < ∑ s ∈ S, (ξ₁ - s)⁻¹ := by
  refine Finset.sum_lt_sum_of_nonempty hS fun s hs => ?_
  rcases le_or_gt s x with hsx | hsx
  · exact (inv_lt_inv₀ (by linarith) (by linarith)).mpr (by linarith)
  · rcases le_or_gt y s with hys | hys
    · rw [inv_sub_eq_neg_inv_sub ξ₂ s, inv_sub_eq_neg_inv_sub ξ₁ s, neg_lt_neg_iff]
      exact (inv_lt_inv₀ (by linarith) (by linarith)).mpr (by linarith)
    · exact absurd hs (hcons s hsx hys)

/-- **Rolle interlacing.** Let `p = c ∏_{s ∈ S} (X - s)` with `c ≠ 0` and `S` a nonempty finite
set of reals. Every critical point of `p` lies strictly between two consecutive roots, and
between two consecutive roots `p` has exactly one critical point. -/
theorem prod_X_sub_C_criticalPoints_interlace {S : Finset ℝ} (hS : S.Nonempty) {c : ℝ}
    (hc : c ≠ 0) :
    (∀ ξ : ℝ, (derivative (C c * ∏ s ∈ S, (polyX - C s))).IsRoot ξ →
      ∃ x ∈ S, ∃ y ∈ S, x < ξ ∧ ξ < y ∧ ∀ t, x < t → t < y → t ∉ S) ∧
    (∀ x ∈ S, ∀ y ∈ S, x < y → (∀ t, x < t → t < y → t ∉ S) →
      ∃! ξ : ℝ, x < ξ ∧ ξ < y ∧ (derivative (C c * ∏ s ∈ S, (polyX - C s))).IsRoot ξ) := by
  constructor
  · intro ξ hξ
    obtain ⟨hξS, hsum⟩ := sum_inv_eq_zero_of_isRoot_derivative hc hξ
    have hne : ∀ s ∈ S, s ≠ ξ := fun s hs h => hξS (h ▸ hs)
    have hlow : (S.filter (· < ξ)).Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty, filter_eq_empty_iff] at h
      have hpos : 0 < ∑ s ∈ S, (s - ξ)⁻¹ := Finset.sum_pos (fun s hs => inv_pos.mpr
        (sub_pos.mpr (lt_of_le_of_ne (not_lt.mp (h hs)) (hne s hs).symm))) hS
      rw [Finset.sum_congr rfl (fun s _ => inv_sub_eq_neg_inv_sub ξ s),
        Finset.sum_neg_distrib] at hsum
      linarith
    have hhigh : (S.filter (ξ < ·)).Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty, filter_eq_empty_iff] at h
      have hpos : 0 < ∑ s ∈ S, (ξ - s)⁻¹ := Finset.sum_pos (fun s hs => inv_pos.mpr
        (sub_pos.mpr (lt_of_le_of_ne (not_lt.mp (h hs)) (hne s hs)))) hS
      linarith
    have hx := mem_filter.mp ((S.filter (· < ξ)).max'_mem hlow)
    have hy := mem_filter.mp ((S.filter (ξ < ·)).min'_mem hhigh)
    refine ⟨_, hx.1, _, hy.1, hx.2, hy.2, fun t hxt hty htS => ?_⟩
    rcases lt_trichotomy t ξ with htξ | rfl | htξ
    · have := (S.filter (· < ξ)).le_max' t (mem_filter.mpr ⟨htS, htξ⟩)
      linarith
    · exact hξS htS
    · have := (S.filter (ξ < ·)).min'_le t (mem_filter.mpr ⟨htS, htξ⟩)
      linarith
  · intro x hx y hy hxy hcons
    obtain ⟨ξ, hξ, hd⟩ := exists_deriv_eq_zero hxy
      (Polynomial.continuous (C c * ∏ s ∈ S, (polyX - C s))).continuousOn
      (by simp only [IsRoot.def.mp ((isRoot_prod_X_sub_C_mul_iff hc).mpr hx),
        IsRoot.def.mp ((isRoot_prod_X_sub_C_mul_iff hc).mpr hy)])
    rw [Polynomial.deriv] at hd
    refine ⟨ξ, ⟨hξ.1, hξ.2, IsRoot.def.mpr hd⟩, fun ξ' hξ' => ?_⟩
    obtain ⟨-, h0⟩ := sum_inv_eq_zero_of_isRoot_derivative hc (IsRoot.def.mpr hd)
    obtain ⟨-, h0'⟩ := sum_inv_eq_zero_of_isRoot_derivative hc hξ'.2.2
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := sum_inv_sub_lt_of_consecutive hS hcons hξ'.1 hlt hξ.2
      linarith
    · have := sum_inv_sub_lt_of_consecutive hS hcons hξ.1 hlt hξ'.2.1
      linarith

end Interlacing

/-! ### The critical points of `P_ℓ` -/

/-- Under `JacobiSimpleRealZeros`, `P_ℓ = c ∏_{s ∈ S} (X - s)` over `ℝ` with `|S| = ℓ`. -/
theorem legendreP_map_eq_prod (hZ : JacobiSimpleRealZeros) (ℓ : ℕ) :
    ∃ c : ℝ, c ≠ 0 ∧ ∃ S : Finset ℝ, S.card = ℓ ∧
      (legendreP ℓ).map (algebraMap ℚ ℝ) = C c * ∏ s ∈ S, (polyX - C s) := by
  obtain ⟨hnd, hcard, -⟩ := hZ.rat 0 0 (by norm_num) (by norm_num) ℓ
  rw [← legendreP_eq] at hnd hcard
  have hdeg : ((legendreP ℓ).map (algebraMap ℚ ℝ)).natDegree = ℓ := by
    rw [natDegree_map, natDegree_legendreP]
  have hne : (legendreP ℓ).map (algebraMap ℚ ℝ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective).mpr (legendreP_ne_zero ℓ)
  refine ⟨_, leadingCoeff_ne_zero.mpr hne, ⟨_, hnd⟩, Finset.card_mk.trans hcard, ?_⟩
  rw [Finset.prod_eq_multiset_prod]
  exact (C_leadingCoeff_mul_prod_multiset_X_sub_C (hcard.trans hdeg.symm)).symm

/-- **Rolle interlacing for `P_ℓ`** (§1.2). For `ℓ ≥ 1`, every real critical point of
the Legendre polynomial `P_ℓ` lies strictly between two consecutive zeros of `P_ℓ`, and between
two consecutive zeros there is exactly one critical point. Conditional on
`JacobiSimpleRealZeros` ([DLMF, §18.2(vi)]). -/
theorem legendreP_criticalPoints_interlace (hZ : JacobiSimpleRealZeros) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    (∀ ξ : ℝ, ((derivative (legendreP ℓ)).map (algebraMap ℚ ℝ)).IsRoot ξ →
      ∃ x y : ℝ, ((legendreP ℓ).map (algebraMap ℚ ℝ)).IsRoot x ∧
        ((legendreP ℓ).map (algebraMap ℚ ℝ)).IsRoot y ∧ x < ξ ∧ ξ < y ∧
        ∀ t, x < t → t < y → ¬ ((legendreP ℓ).map (algebraMap ℚ ℝ)).IsRoot t) ∧
    (∀ x y : ℝ, ((legendreP ℓ).map (algebraMap ℚ ℝ)).IsRoot x →
      ((legendreP ℓ).map (algebraMap ℚ ℝ)).IsRoot y → x < y →
      (∀ t, x < t → t < y → ¬ ((legendreP ℓ).map (algebraMap ℚ ℝ)).IsRoot t) →
      ∃! ξ : ℝ, x < ξ ∧ ξ < y ∧ ((derivative (legendreP ℓ)).map (algebraMap ℚ ℝ)).IsRoot ξ) := by
  obtain ⟨c, hc, S, hS, hP⟩ := legendreP_map_eq_prod hZ ℓ
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hD : (derivative (legendreP ℓ)).map (algebraMap ℚ ℝ) =
      derivative (C c * ∏ s ∈ S, (polyX - C s)) := by
    rw [← derivative_map, hP]
  rw [hD, hP]
  obtain ⟨h1, h2⟩ := prod_X_sub_C_criticalPoints_interlace hSne hc
  have hiff : ∀ t, (C c * ∏ s ∈ S, (polyX - C s)).IsRoot t ↔ t ∈ S := fun t =>
    isRoot_prod_X_sub_C_mul_iff hc
  constructor
  · intro ξ hξ
    obtain ⟨x, hx, y, hy, hxξ, hξy, hcons⟩ := h1 ξ hξ
    exact ⟨x, y, (hiff x).mpr hx, (hiff y).mpr hy, hxξ, hξy,
      fun t hxt hty ht => hcons t hxt hty ((hiff t).mp ht)⟩
  · intro x y hx hy hxy hcons
    exact h2 x ((hiff x).mp hx) y ((hiff y).mp hy) hxy
      fun t hxt hty ht => hcons t hxt hty ((hiff t).mpr ht)

/-! ### The minimizer `q_n` of the finite criterion (§4.5) -/

/-- The part `a z + 2 log 2 / z - log z` of `𝓗_n(z)` that depends on `z`. -/
noncomputable def finiteCriterionProfile (a z : ℝ) : ℝ := a * z + 2 * log 2 / z - log z

theorem finiteCriterionProfile_eq (a z : ℝ) :
    finiteCriterionProfile a z = a * z + 2 * log 2 / z - log z := (rfl)

/-- `q = (1 + √(1 + 8 a log 2)) / (2a)`. -/
noncomputable def finiteCriterionMinimizer (a : ℝ) : ℝ := (1 + √(1 + 8 * a * log 2)) / (2 * a)

theorem finiteCriterionMinimizer_eq (a : ℝ) :
    finiteCriterionMinimizer a = (1 + √(1 + 8 * a * log 2)) / (2 * a) := (rfl)

/-- **§4.5.** The profile `a z + 2 log 2 / z - log z` is strictly convex for `z > 0`. -/
theorem strictConvexOn_finiteCriterionProfile (a : ℝ) :
    StrictConvexOn ℝ (Set.Ioi 0) (finiteCriterionProfile a) := by
  have h1 : ConvexOn ℝ (Set.Ioi (0 : ℝ)) fun z : ℝ => a * z :=
    (LinearMap.mul ℝ ℝ a).convexOn (convex_Ioi 0)
  have h2 : ConvexOn ℝ (Set.Ioi (0 : ℝ)) fun z : ℝ => (2 * log 2) • z ^ (-1 : ℤ) :=
    (convexOn_zpow (-1)).smul (by positivity)
  have h3 : StrictConvexOn ℝ (Set.Ioi (0 : ℝ)) fun z : ℝ => -log z := strictConcaveOn_log_Ioi.neg
  have h := (h1.add h2).add_strictConvexOn h3
  convert h using 1
  funext z
  simp only [Pi.add_apply, finiteCriterionProfile_eq, smul_eq_mul, zpow_neg, zpow_one,
    div_eq_mul_inv]
  ring

theorem hasDerivAt_finiteCriterionProfile (a : ℝ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (finiteCriterionProfile a) ((a * z ^ 2 - z - 2 * log 2) / z ^ 2) z := by
  have h := (((hasDerivAt_id' z).const_mul a).add
    ((hasDerivAt_inv hz.ne').const_mul (2 * log 2))).sub (Real.hasDerivAt_log hz.ne')
  have hfun : finiteCriterionProfile a = fun y => a * y + 2 * log 2 * y⁻¹ - log y := by
    funext y
    rw [finiteCriterionProfile_eq, div_eq_mul_inv]
  rw [hfun]
  convert h using 1
  have hz' : z ≠ 0 := hz.ne'
  field_simp
  try ring

theorem deriv_finiteCriterionProfile (a : ℝ) {z : ℝ} (hz : 0 < z) :
    deriv (finiteCriterionProfile a) z = (a * z ^ 2 - z - 2 * log 2) / z ^ 2 :=
  (hasDerivAt_finiteCriterionProfile a hz).deriv

theorem continuousOn_finiteCriterionProfile (a : ℝ) {D : Set ℝ} (hD : D ⊆ Set.Ioi 0) :
    ContinuousOn (finiteCriterionProfile a) D := fun _ hz =>
  (hasDerivAt_finiteCriterionProfile a (hD hz)).continuousAt.continuousWithinAt

/-- If `a ≤ 0`, the profile is strictly decreasing on `(0, ∞)`. -/
theorem finiteCriterionProfile_strictAntiOn_of_nonpos {a : ℝ} (ha : a ≤ 0) :
    StrictAntiOn (finiteCriterionProfile a) (Set.Ioi 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0)
    (continuousOn_finiteCriterionProfile a subset_rfl) fun z hz => ?_
  rw [interior_Ioi] at hz
  have hz0 : (0 : ℝ) < z := hz
  rw [deriv_finiteCriterionProfile a hz0]
  have hl := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have : a * z ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha (sq_nonneg z)
  exact div_neg_of_neg_of_pos (by linarith) (pow_pos hz0 2)

/-- For `a > 0`, `a z² - z - 2 log 2` is negative on `(0, q)` and positive on `(q, ∞)`. -/
theorem finiteCriterion_quadratic_sign {a : ℝ} (ha : 0 < a) {z : ℝ} (hz : 0 < z) :
    (z < finiteCriterionMinimizer a → a * z ^ 2 - z - 2 * log 2 < 0) ∧
      (finiteCriterionMinimizer a < z → 0 < a * z ^ 2 - z - 2 * log 2) := by
  have hl := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  obtain ⟨s, hs⟩ : ∃ s, s = √(1 + 8 * a * log 2) := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 1 + 8 * a * log 2 := by
    rw [hs]
    exact Real.sq_sqrt (by have := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 8) ha) hl; linarith)
  have hq : finiteCriterionMinimizer a = (1 + s) / (2 * a) := by
    rw [finiteCriterionMinimizer_eq, hs]
  have h2a : 0 < 2 * a := by linarith
  have key : 4 * a * (a * z ^ 2 - z - 2 * log 2) = (2 * a * z - 1) ^ 2 - s ^ 2 := by
    rw [hs2]; ring
  have hs1 : 1 ≤ s := by nlinarith
  constructor
  · intro h
    rw [hq, lt_div_iff₀ h2a] at h
    have hlow : -s < 2 * a * z - 1 := by nlinarith
    have hneg : (2 * a * z - 1) ^ 2 - s ^ 2 < 0 := by nlinarith
    have h4a : 0 < 4 * a := by linarith
    by_contra hc
    push Not at hc
    nlinarith
  · intro h
    rw [hq, div_lt_iff₀ h2a] at h
    have hpos : 0 < (2 * a * z - 1) ^ 2 - s ^ 2 := by nlinarith
    have h4a : 0 < 4 * a := by linarith
    by_contra hc
    push Not at hc
    nlinarith

theorem finiteCriterionMinimizer_pos {a : ℝ} (ha : 0 < a) : 0 < finiteCriterionMinimizer a := by
  rw [finiteCriterionMinimizer_eq]
  have := Real.sqrt_nonneg (1 + 8 * a * log 2)
  exact div_pos (by linarith) (by linarith)

/-- For `a > 0`, the profile is strictly decreasing on `(0, q]`. -/
theorem finiteCriterionProfile_strictAntiOn_Ioc {a : ℝ} (ha : 0 < a) :
    StrictAntiOn (finiteCriterionProfile a) (Set.Ioc 0 (finiteCriterionMinimizer a)) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioc 0 _)
    (continuousOn_finiteCriterionProfile a fun z hz => hz.1) fun z hz => ?_
  rw [interior_Ioc] at hz
  rw [deriv_finiteCriterionProfile a hz.1]
  exact div_neg_of_neg_of_pos ((finiteCriterion_quadratic_sign ha hz.1).1 hz.2)
    (pow_pos hz.1 2)

/-- For `a > 0`, the profile is strictly increasing on `[q, ∞)`. -/
theorem finiteCriterionProfile_strictMonoOn_Ici {a : ℝ} (ha : 0 < a) :
    StrictMonoOn (finiteCriterionProfile a) (Set.Ici (finiteCriterionMinimizer a)) := by
  have hq := finiteCriterionMinimizer_pos ha
  refine strictMonoOn_of_deriv_pos (convex_Ici _)
    (continuousOn_finiteCriterionProfile a fun z (hz : _ ≤ z) => lt_of_lt_of_le hq hz)
    fun z hz => ?_
  rw [interior_Ici] at hz
  have hz0 : 0 < z := lt_trans hq hz
  rw [deriv_finiteCriterionProfile a hz0]
  exact div_pos ((finiteCriterion_quadratic_sign ha hz0).2 hz) (pow_pos hz0 2)

/-- **`q_n` is the unique minimizer** (§4.5): for `a > 0` and `z > 0`, `z ≠ q`,
`h(q) < h(z)`. -/
theorem finiteCriterionProfile_lt_of_ne {a : ℝ} (ha : 0 < a) {z : ℝ} (hz : 0 < z)
    (hzq : z ≠ finiteCriterionMinimizer a) :
    finiteCriterionProfile a (finiteCriterionMinimizer a) < finiteCriterionProfile a z := by
  have hq := finiteCriterionMinimizer_pos ha
  rcases lt_or_gt_of_ne hzq with h | h
  · exact finiteCriterionProfile_strictAntiOn_Ioc ha (Set.mem_Ioc.mpr ⟨hz, h.le⟩)
      (Set.mem_Ioc.mpr ⟨hq, le_rfl⟩) h
  · exact finiteCriterionProfile_strictMonoOn_Ici ha (Set.mem_Ici.mpr le_rfl)
      (Set.mem_Ici.mpr h.le) h

/-! ### The associated-Legendre constraint on the cone (§6.3) -/

/-- The integration-by-parts identity behind the associated-Legendre constraint, in polynomial
form. For `p = P_{n+r}^{(r)}` over `ℝ`, `r = k + 1`, `w = 1 - X²` and `U = w p' - r X p`, the
polynomial `G = w^r p U` (the function `(1 - x²) y y'` for `y = (1 - x²)^{r/2} p`) satisfies
`G' = w^k U² + r² w^k p² - ℓ(ℓ+1) w^r p²` with `ℓ = n + r`. -/
theorem derivative_associatedLegendreFlux (n k : ℕ) {p w U : ℝ[X]}
    (hp : p = (derivative^[k + 1] (legendreP (n + (k + 1)))).map (algebraMap ℚ ℝ))
    (hw : w = 1 - polyX ^ 2) (hU : U = w * derivative p - ((k : ℝ[X]) + 1) * polyX * p) :
    derivative (w ^ (k + 1) * p * U) = w ^ k * U ^ 2 + ((k : ℝ[X]) + 1) ^ 2 * w ^ k * p ^ 2 -
      ((n : ℝ[X]) + k + 1) * ((n : ℝ[X]) + k + 2) * w ^ (k + 1) * p ^ 2 := by
  have hode := congrArg (Polynomial.map (algebraMap ℚ ℝ))
    (iterate_derivative_legendreP_differential_equation n (k + 1))
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_one, map_X, Polynomial.map_C, Polynomial.map_zero, ← derivative_map,
    ← hp] at hode
  simp only [map_add, map_mul, map_natCast, map_ofNat, map_one, Nat.cast_add, Nat.cast_one]
    at hode
  rw [← hw] at hode
  have hdw : derivative w = -(2 * polyX) := by
    rw [hw, derivative_sub, derivative_one, derivative_X_pow]
    simpa using map_ofNat C 2
  rw [hU]
  simp only [derivative_mul, derivative_pow, derivative_sub, derivative_X,
    derivative_natCast, derivative_one, hdw, add_tsub_cancel_right, map_natCast, map_add,
    map_one, Nat.cast_add, Nat.cast_one]
  linear_combination (w ^ (k + 1) * p) * hode + (((k : ℝ[X]) + 1) ^ 2 * w ^ k * p ^ 2) * hw

/-- **The associated-Legendre constraint** (§6.3). If `1 ≤ r ≤ ℓ` and
`P_ℓ^{(r)}(1/√3) = 0`, then `r² < (2/3) ℓ(ℓ+1)`. The proof is the integration by parts of the
manuscript on `[1/√3, 1]`, written for the polynomial `G = (1 - x²)^r P (… )` of
`derivative_associatedLegendreFlux`: `∫ G' = G(1) - G(1/√3) = 0`, while `r² ≥ (2/3) ℓ(ℓ+1)`
would make `G' ≥ r² (1 - x²)^{r-1} P² (1 - (3/2)(1 - x²)) ≥ 0` on `[1/√3, 1]`, positive off the
finitely many zeros of `P`. -/
theorem sq_lt_of_aeval_inv_sqrt_three_eq_zero {ℓ r : ℕ} (hr : 1 ≤ r) (hrℓ : r ≤ ℓ)
    (h : aeval (1 / Real.sqrt 3) (derivative^[r] (legendreP ℓ)) = 0) :
    (r : ℝ) ^ 2 < 2 / 3 * ℓ * (ℓ + 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, ℓ = n + r := ⟨ℓ - r, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 1 / Real.sqrt 3 := ⟨_, rfl⟩
  have hs3 : 1 < Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have ha0 : 0 < a := by rw [ha]; positivity
  have ha1 : a < 1 := by rw [ha, div_lt_one (by linarith)]; exact hs3
  have ha2 : a ^ 2 = 1 / 3 := by rw [ha, div_pow, one_pow, Real.sq_sqrt (by norm_num)]
  obtain ⟨p, hp⟩ : ∃ p : ℝ[X],
      p = (derivative^[k + 1] (legendreP (n + (k + 1)))).map (algebraMap ℚ ℝ) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℝ[X], w = 1 - polyX ^ 2 := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : ℝ[X], U = w * derivative p - ((k : ℝ[X]) + 1) * polyX * p := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℝ[X], G = w ^ (k + 1) * p * U := ⟨_, rfl⟩
  have hdG := derivative_associatedLegendreFlux n k hp hw hU
  rw [← hG] at hdG
  have hpa : p.eval a = 0 := by
    rw [hp, eval_map, ← aeval_def, ha]
    exact h
  have hp0 : p ≠ 0 := by
    rw [hp]
    refine (Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective).mpr fun h0 => ?_
    have := coeff_iterate_derivative_legendreP_self_ne_zero n (k + 1)
    rw [h0, coeff_zero] at this
    exact this rfl
  have hwx : ∀ x, w.eval x = 1 - x ^ 2 := fun x => by rw [hw]; simp
  -- `∫_a^1 G' = G(1) - G(a) = 0`
  have hG1 : G.eval 1 = 0 := by
    have : w.eval 1 = 0 := by rw [hwx]; norm_num
    simp [hG, this]
  have hGa : G.eval a = 0 := by simp [hG, hpa]
  have hint : ∫ x in a..1, (derivative G).eval x = 0 := by
    have e := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => G.eval x)
      (f' := fun x => (derivative G).eval x) (fun x _ => G.hasDerivAt x)
      ((derivative G).continuous.intervalIntegrable a 1)
    simp only [hG1, hGa, sub_zero] at e
    exact e
  -- the pointwise form of `G'`
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = ((n : ℝ) + k + 1) * ((n : ℝ) + k + 2) := ⟨_, rfl⟩
  have hf : ∀ x, (derivative G).eval x = (w.eval x) ^ k * (U.eval x) ^ 2 +
      ((k : ℝ) + 1) ^ 2 * (w.eval x) ^ k * (p.eval x) ^ 2 -
      L * (w.eval x) ^ (k + 1) * (p.eval x) ^ 2 := by
    intro x
    rw [hdG, hL]
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_natCast, eval_one, eval_ofNat]
  by_contra hcon
  push Not at hcon
  push_cast at hcon
  have hLr : L ≤ 3 / 2 * ((k : ℝ) + 1) ^ 2 := by rw [hL]; nlinarith
  have hsplit : ∀ x, (derivative G).eval x = (w.eval x) ^ k * (U.eval x) ^ 2 +
      (w.eval x) ^ k * (p.eval x) ^ 2 * (((k : ℝ) + 1) ^ 2 * (1 - 3 / 2 * w.eval x)) +
      (w.eval x) ^ k * (p.eval x) ^ 2 * w.eval x * (3 / 2 * ((k : ℝ) + 1) ^ 2 - L) := by
    intro x
    rw [hf x]
    ring
  have hle : ∀ x ∈ Set.Icc a 1, 0 ≤ (derivative G).eval x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le ha0 hx.1
    have hxa : a ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ ha0.le hx.1 2
    have hx1 : x ^ 2 ≤ 1 := by nlinarith [hx.2]
    have hw0 : 0 ≤ w.eval x := by rw [hwx]; linarith
    have hw23 : 0 ≤ 1 - 3 / 2 * w.eval x := by rw [hwx]; linarith
    rw [hsplit x]
    have hwk : 0 ≤ (w.eval x) ^ k := pow_nonneg hw0 k
    have t1 : 0 ≤ (w.eval x) ^ k * (U.eval x) ^ 2 := mul_nonneg hwk (sq_nonneg _)
    have t2 : 0 ≤ (w.eval x) ^ k * (p.eval x) ^ 2 * (((k : ℝ) + 1) ^ 2 * (1 - 3 / 2 * w.eval x)) :=
      mul_nonneg (mul_nonneg hwk (sq_nonneg _)) (mul_nonneg (sq_nonneg _) hw23)
    have t3 : 0 ≤ (w.eval x) ^ k * (p.eval x) ^ 2 * w.eval x * (3 / 2 * ((k : ℝ) + 1) ^ 2 - L) :=
      mul_nonneg (mul_nonneg (mul_nonneg hwk (sq_nonneg _)) hw0) (by linarith)
    linarith
  obtain ⟨x₀, hx₀, hx₀r⟩ := (Set.Ioo_infinite ha1).exists_notMem_finset p.roots.toFinset
  have hpx₀ : p.eval x₀ ≠ 0 := fun h0 =>
    hx₀r (Multiset.mem_toFinset.mpr ((mem_roots hp0).mpr h0))
  have hpos : 0 < (derivative G).eval x₀ := by
    have hx0 : 0 < x₀ := lt_trans ha0 hx₀.1
    have hxa : a ^ 2 < x₀ ^ 2 := pow_lt_pow_left₀ hx₀.1 ha0.le two_ne_zero
    have hx1 : x₀ ^ 2 < 1 := by nlinarith [hx₀.2]
    have hw0 : 0 < w.eval x₀ := by rw [hwx]; linarith
    have hw23 : 0 < 1 - 3 / 2 * w.eval x₀ := by rw [hwx]; linarith
    rw [hsplit x₀]
    have hwk : 0 < (w.eval x₀) ^ k := pow_pos hw0 k
    have hp2 : 0 < (p.eval x₀) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hpx₀).symm
    have t1 : 0 ≤ (w.eval x₀) ^ k * (U.eval x₀) ^ 2 := mul_nonneg hwk.le (sq_nonneg _)
    have t2 : 0 < (w.eval x₀) ^ k * (p.eval x₀) ^ 2 *
        (((k : ℝ) + 1) ^ 2 * (1 - 3 / 2 * w.eval x₀)) :=
      mul_pos (mul_pos hwk hp2) (mul_pos (by positivity) hw23)
    have t3 : 0 ≤ (w.eval x₀) ^ k * (p.eval x₀) ^ 2 * w.eval x₀ *
        (3 / 2 * ((k : ℝ) + 1) ^ 2 - L) :=
      mul_nonneg (mul_nonneg (mul_nonneg hwk.le hp2.le) hw0.le) (by linarith)
    linarith
  have := intervalIntegral.integral_pos ha1 (derivative G).continuous.continuousOn
    (fun x hx => hle x (Set.Ioc_subset_Icc_self hx)) ⟨x₀, Set.Ioo_subset_Icc_self hx₀, hpos⟩
  linarith

/-! ### The decimal values of `𝔩`, `𝔲` and `𝔩 - 𝔲` (§4.4) -/

/-- `π/(2√3)` and `π/√3` to fifteen digits. -/
theorem pi_div_sqrt_three_bounds :
    (0.906899682117108 : ℝ) < π / (2 * √3) ∧ π / (2 * √3) < 0.906899682117109 ∧
    (1.81379936423421 : ℝ) < π / √3 ∧ π / √3 < 1.81379936423422 := by
  have hs₁ : (1.7320508075688772 : ℝ) < √3 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hs₂ : √3 < (1.7320508075688773 : ℝ) := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hs0 : 0 < √3 := by positivity
  have hp₁ := Real.pi_gt_d20
  have hp₂ := Real.pi_lt_d20
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [lt_div_iff₀ (by positivity)]; linarith
  · rw [div_lt_iff₀ (by positivity)]; linarith
  · rw [lt_div_iff₀ hs0]; linarith
  · rw [div_lt_iff₀ hs0]; linarith

/-- The logarithmic part `𝔩 + π/(2√3) = (7/6) log 2 + (5/3) log(3/2) + log((4 + 3√3)/9)` to
eleven digits. -/
theorem frak_log_combination_bounds :
    (1.50600749515 : ℝ) < 7 / 6 * log 2 + 5 / 3 * log (3 / 2) + log ((4 + 3 * √3) / 9) ∧
      7 / 6 * log 2 + 5 / 3 * log (3 / 2) + log ((4 + 3 * √3) / 9) < 1.50600749516 := by
  have hs₁ : (1.7320508075688772 : ℝ) < √3 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hs₂ : √3 < (1.7320508075688773 : ℝ) := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have h2l := two_mul_sum_le_log_div (z := 1 / 3) (by norm_num) (by norm_num) 13
  have h2u := log_div_le_two_mul_sum_add (z := 1 / 3) (by norm_num) (by norm_num) 13
  have h3l := two_mul_sum_le_log_div (z := 1 / 5) (by norm_num) (by norm_num) 9
  have h3u := log_div_le_two_mul_sum_add (z := 1 / 5) (by norm_num) (by norm_num) 9
  have e2 : (1 + 1 / 3 : ℝ) / (1 - 1 / 3) = 2 := by norm_num
  have e3 : (1 + 1 / 5 : ℝ) / (1 - 1 / 5) = 3 / 2 := by norm_num
  rw [e2] at h2l h2u
  rw [e3] at h3l h3u
  have hy0 : (0 : ℝ) < (4 + 3 * √3) / 9 := by positivity
  have hyl : (1 + 2155976913689 / 200000000000000 : ℝ) / (1 - 2155976913689 / 200000000000000) ≤
      (4 + 3 * √3) / 9 := by
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
    linarith
  have hyu : (4 + 3 * √3) / 9 ≤
      (1 + 10779884568447 / 1000000000000000 : ℝ) / (1 - 10779884568447 / 1000000000000000) := by
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
    linarith
  have hyl' := (two_mul_sum_le_log_div (z := 2155976913689 / 200000000000000) (by norm_num)
    (by norm_num) 3).trans (Real.log_le_log (by norm_num) hyl)
  have hyu' := (Real.log_le_log hy0 hyu).trans
    (log_div_le_two_mul_sum_add (z := 10779884568447 / 1000000000000000) (by norm_num)
      (by norm_num) 3)
  obtain ⟨Y, hY⟩ : ∃ Y, Y = log ((4 + 3 * √3) / 9) := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, T = log (2 : ℝ) := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H, H = log (3 / 2 : ℝ) := ⟨_, rfl⟩
  rw [← hY] at hyl' hyu' ⊢
  rw [← hT] at h2l h2u ⊢
  rw [← hH] at h3l h3u ⊢
  norm_num [Finset.sum_range_succ] at h2l h2u h3l h3u hyl' hyu'
  constructor <;> linarith

/-- **`𝔩 = 0.5991078130…`** (§4.4): `0.5991078130 < 𝔩 < 0.5991078131`. -/
theorem frakL_bounds :
    (0.5991078130 : ℝ) < log (4 + 3 * √3) - 1 / 2 * log 2 - 1 / 3 * log 3 - π / (2 * √3) ∧
      log (4 + 3 * √3) - 1 / 2 * log 2 - 1 / 3 * log 3 - π / (2 * √3) < 0.5991078131 := by
  obtain ⟨hp₁, hp₂, -, -⟩ := pi_div_sqrt_three_bounds
  obtain ⟨hC₁, hC₂⟩ := frak_log_combination_bounds
  have hpos : (0 : ℝ) < 4 + 3 * √3 := by positivity
  have hsplit : log ((4 + 3 * √3) / 9) = log (4 + 3 * √3) - log 9 :=
    Real.log_div hpos.ne' (by norm_num)
  have h9 : log 9 = 2 * log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h32 : log (3 / 2 : ℝ) = log 3 - log 2 := Real.log_div (by norm_num) (by norm_num)
  constructor <;> linarith

/-- **`𝔲 = 0.33620063576…`** (§4.4): `0.3362006357 < 𝔲 < 0.3362006358`. -/
theorem frakU_bounds :
    (0.3362006357 : ℝ) < 43 / 20 - π / √3 ∧ 43 / 20 - π / √3 < 0.3362006358 := by
  obtain ⟨-, -, hp₁, hp₂⟩ := pi_div_sqrt_three_bounds
  constructor <;> linarith

/-- **`𝔩 - 𝔲 = 0.2629071772…`** (§4.4), in the form of `positive_gap`:
`0.2629071772 < log(4 + 3√3) - ½ log 2 - ⅓ log 3 - 43/20 + π/(2√3) < 0.2629071773`. -/
theorem frakL_sub_frakU_bounds :
    (0.2629071772 : ℝ) <
        log (4 + 3 * √3) - 1 / 2 * log 2 - 1 / 3 * log 3 - 43 / 20 + π / (2 * √3) ∧
      log (4 + 3 * √3) - 1 / 2 * log 2 - 1 / 3 * log 3 - 43 / 20 + π / (2 * √3) <
        0.2629071773 := by
  obtain ⟨hp₁, hp₂, -, -⟩ := pi_div_sqrt_three_bounds
  obtain ⟨hC₁, hC₂⟩ := frak_log_combination_bounds
  have hpos : (0 : ℝ) < 4 + 3 * √3 := by positivity
  have hsplit : log ((4 + 3 * √3) / 9) = log (4 + 3 * √3) - log 9 :=
    Real.log_div hpos.ne' (by norm_num)
  have h9 : log 9 = 2 * log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h32 : log (3 / 2 : ℝ) = log 3 - log 2 := Real.log_div (by norm_num) (by norm_num)
  constructor <;> linarith

end ArithmeticOfJacobiPolynomials
