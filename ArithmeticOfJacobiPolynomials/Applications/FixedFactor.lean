/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Analysis.SymmetricAsymptotics
public import ArithmeticOfJacobiPolynomials.Jacobi.SymmetricParameters

/-!
# Excluding a prescribed factor (Proposition 6.3) and rational roots (Corollary 6.4)

Section 6.2 of the manuscript. For a primitive `F ∈ ℤ[x]` of degree `d ≥ 1` with positive
leading coefficient `u`, `d` distinct real roots in `(-1,1)` and `F(0) ≠ 0`, put
`c_F = min_j v_2([X^j] F(2X+1))` (`shiftedTwoAdicOrder`) and
`β(F) = log 4 + (2/d) log(u / 2^{c_F})` (`fixedFactorExponent`).

* `fixedFactor_resultant_comparison`: the comparison of the two resultant estimates of the
  proof of Theorem 3.4 for a factorization `H = F G` with a prescribed factor `F`, keeping the
  term `V_F` and `u / 2^{c_F}` of the first inequality (2.11) of Lemma 2.6 (the inequality
  preceding (6.2) of the manuscript, before the asymptotic estimate);
* `not_dvd_reducedGegenbauer_of_fixedFactor`: **Proposition 6.3**: if
  `c ≥ 2` and `c (β(F) - 1) > g(c)`, then for all large `m`, uniformly in `0 ≤ r ≤ m/c` and
  `δ ∈ {0,1}`, `F ∤ C_{2m+δ}^{r+1/2}(x)/x^δ`;
* `noRationalRootsStatement_of`: **Corollary 6.4**, the statement
  `NoRationalRootsStatement`.

All results are conditional on the proved `intervalVandermondeBound` (Lemma 2.5),
`JacobiSimpleRealZeros` ([DLMF, §18.2(vi)]) and `DusartThetaBound` ([Dusart10, Theorem 5.2]),
the inputs of Theorem 3.4 and Lemma 3.5.
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset Real Filter

/-! ### Numerical margins for `g` -/

/-- The margin used for `F = 3x^2 - 1`: `(19/8)(log 6 - 1) - g(19/8) > 0.0042`
(Appendix C.3; the same computation as `margin_at_nineteen_eighths`). -/
theorem margin_asymptoticGapFunction_nineteen_eighths :
    19 / 8 * (log 6 - 1) - asymptoticGapFunction (19 / 8) > 0.0042 := by
  have hg : asymptoticGapFunction (19 / 8) =
      23 / 2 * log (23 / 8) - 57 / 8 * log (19 / 8) - 27 / 8 * log (27 / 8) := by
    rw [asymptoticGapFunction_eq]; norm_num
  have h6 : log 6 = log 2 + log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have h27 : log 27 = 3 * log 3 := by
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]; norm_num
  have h238 : log (23 / 8) = log 23 - 3 * log 2 := by
    have := log_nat_div_pow_two 23 3 (by norm_num); norm_num at this; exact this
  have h198 : log (19 / 8) = log 19 - 3 * log 2 := by
    have := log_nat_div_pow_two 19 3 (by norm_num); norm_num at this; exact this
  have h278 : log (27 / 8) = log 27 - 3 * log 2 := by
    have := log_nat_div_pow_two 27 3 (by norm_num); norm_num at this; exact this
  have h1916 : log (19 / 16) = log 19 - 4 * log 2 := by
    have := log_nat_div_pow_two 19 4 (by norm_num); norm_num at this; exact this
  have h32 : log (3 / 2) = log 3 - log 2 := Real.log_div (by norm_num) (by norm_num)
  have h2423 : log (24 / 23) = log 24 - log 23 := Real.log_div (by norm_num) (by norm_num)
  have h24 : log 24 = 3 * log 2 + log 3 := by
    rw [show (24 : ℝ) = 2 ^ 3 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]; norm_num
  linarith [log_three_div_two_gt, log_nineteen_div_sixteen_gt,
    log_twentyfour_div_twentythree_gt, Real.log_two_gt_d9]

/-- The margin of Corollary 6.4: `2(log 9 - 1) - g(2) > 0` (the same computation as
`margin_at_two`, via `2(log 9 - 1) - g(2) = log(3^7 2^16 / 5^10) - 2`). -/
theorem margin_asymptoticGapFunction_two : 2 * (log 9 - 1) - asymptoticGapFunction 2 > 0 := by
  have hg : asymptoticGapFunction 2 = 10 * log (5 / 2) - 6 * log 2 - 3 * log 3 := by
    rw [asymptoticGapFunction_eq]; norm_num
  have h52 : log (5 / 2) = log 5 - log 2 := Real.log_div (by norm_num) (by norm_num)
  have hbig : log ((3 : ℝ) ^ 7 * 2 ^ 16 / 5 ^ 10) = 7 * log 3 + 16 * log 2 - 10 * log 5 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast; ring
  have h9 : log 9 = 2 * log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
  have heq : 2 * (log 9 - 1) - asymptoticGapFunction 2 =
      log (3 ^ 7 * 2 ^ 16 / 5 ^ 10) - 2 := by
    rw [hg, h52, hbig, h9]; ring
  rw [heq]
  have h2 : (2 : ℝ) < log 9 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have h := Real.exp_one_lt_d9
    have h0 := Real.exp_pos 1
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith
  have hmono : log 9 < log (3 ^ 7 * 2 ^ 16 / 5 ^ 10) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  linarith

/-! ### The polynomial `h = P_{2m+δ+r}^{(r)} / x^δ` and `F_{m,r,δ}` -/

/-- `P_{2m+δ+r}^{(r)}/x^δ = (2r-1)!! F_{m,r,δ}`. -/
theorem reducedDerivative_eq_C_mul_reducedGegenbauer (m r δ : ℕ) (hδ : δ ≤ 1) :
    derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ =
      C ((2 * r - 1).doubleFactorial : ℚ) * reducedGegenbauer m r δ := by
  have hD : ((2 * r - 1).doubleFactorial : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.doubleFactorial_pos _).ne'
  have h1 := X_pow_mul_reduced m r δ hδ
  rw [iterate_derivative_legendreP_eq_gegenbauerC] at h1 ⊢
  rw [reducedGegenbauer_eq]
  have h2 : gegenbauerC ((r : ℚ) + 1 / 2) (2 * m + δ) =
      polyX ^ δ * (C (1 / ((2 * r - 1).doubleFactorial : ℚ)) *
        (C ((2 * r - 1).doubleFactorial : ℚ) * gegenbauerC ((r : ℚ) + 1 / 2) (2 * m + δ) /ₘ
          polyX ^ δ)) := by
    rw [mul_left_comm, h1, ← mul_assoc, ← C_mul, one_div_mul_cancel hD, C_1, one_mul]
  conv_rhs => rw [h2, mul_divByMonic_cancel_left _ (monic_X_pow δ)]
  rw [← mul_assoc, ← C_mul, mul_one_div_cancel hD, C_1, one_mul]

/-- `P_{2m+δ+r}^{(r)} = x^δ (2r-1)!! F_{m,r,δ}`. -/
theorem iterate_derivative_legendreP_eq_X_pow_mul (m r δ : ℕ) (hδ : δ ≤ 1) :
    derivative^[r] (legendreP (2 * m + δ + r)) =
      polyX ^ δ * (C ((2 * r - 1).doubleFactorial : ℚ) * reducedGegenbauer m r δ) := by
  rw [← reducedDerivative_eq_C_mul_reducedGegenbauer m r δ hδ, X_pow_mul_reduced m r δ hδ]

/-- `F_{m,r,δ}` has degree `2m`. -/
theorem natDegree_reducedGegenbauer (m r δ : ℕ) (hδ : δ ≤ 1) :
    (reducedGegenbauer m r δ).natDegree = 2 * m := by
  have hD : ((2 * r - 1).doubleFactorial : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.doubleFactorial_pos _).ne'
  have h := natDegree_reduced m r δ hδ
  rw [reducedDerivative_eq_C_mul_reducedGegenbauer m r δ hδ, natDegree_C_mul hD] at h
  exact h

/-! ### A primitive factorization with a prescribed factor -/

/-- **Gauss's lemma with a prescribed factor.** Let `h ∈ ℚ[X]` be nonzero with positive leading
coefficient and `P = c h` integral for some `c > 0`. If a primitive `F ∈ ℤ[X]` with positive
leading coefficient divides `h` in `ℚ[X]`, then there are `κ > 0` and a primitive `H ∈ ℤ[X]`
with `H = κ h` and `H = F G` for a primitive `G ∈ ℤ[X]` with positive leading coefficient. -/
theorem exists_primitive_factorization_of_dvd {h : ℚ[X]} (hh : h ≠ 0)
    (hlc : 0 < h.leadingCoeff) {c : ℚ} (hc : 0 < c) {P : ℤ[X]}
    (hP : P.map (Int.castRingHom ℚ) = C c * h) {F : ℤ[X]} (hFprim : F.IsPrimitive)
    (hFlc : 0 < F.leadingCoeff) (hdvd : F.map (Int.castRingHom ℚ) ∣ h) :
    ∃ (κ : ℚ) (H G : ℤ[X]), 0 < κ ∧ H.map (Int.castRingHom ℚ) = C κ * h ∧ H.IsPrimitive ∧
      H = F * G ∧ G.IsPrimitive ∧ 0 < G.leadingCoeff := by
  have hinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  have hP0 : P ≠ 0 := by
    rintro rfl
    simp only [Polynomial.map_zero] at hP
    exact mul_ne_zero (C_ne_zero.mpr hc.ne') hh hP.symm
  have hHprim : P.primPart.IsPrimitive := isPrimitive_primPart P
  have hcont0 : P.content ≠ 0 := content_eq_zero_iff.not.mpr hP0
  have hcont : 0 < P.content :=
    lt_of_le_of_ne (Int.nonneg_of_normalize_eq_self normalize_content) (Ne.symm hcont0)
  have hκpos : 0 < c / P.content := div_pos hc (by exact_mod_cast hcont)
  have hcq : ((P.content : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hcont0
  have e : C c * h = C ((P.content : ℤ) : ℚ) * P.primPart.map (Int.castRingHom ℚ) := by
    rw [← hP]
    conv_lhs => rw [P.eq_C_content_mul_primPart]
    rw [Polynomial.map_mul, Polynomial.map_C, eq_intCast]
  have hHmap : P.primPart.map (Int.castRingHom ℚ) = C (c / P.content) * h := by
    calc P.primPart.map (Int.castRingHom ℚ) = C (1 / ((P.content : ℤ) : ℚ)) *
          (C ((P.content : ℤ) : ℚ) * P.primPart.map (Int.castRingHom ℚ)) := by
          rw [← mul_assoc, ← C_mul, one_div_mul_cancel hcq, C_1, one_mul]
      _ = C (c / P.content) * h := by
          rw [← e, ← mul_assoc, ← C_mul]
          congr 2
          ring
  have hHlc : 0 < P.primPart.leadingCoeff := by
    have e := leadingCoeff_map_of_injective hinj P.primPart
    rw [hHmap, leadingCoeff_mul, leadingCoeff_C, eq_intCast] at e
    have : (0 : ℚ) < (P.primPart.leadingCoeff : ℚ) := by
      rw [← e]; exact mul_pos hκpos hlc
    exact_mod_cast this
  have hFH : F ∣ P.primPart := by
    rw [hFprim.dvd_iff_fraction_map_dvd_fraction_map (K := ℚ), algebraMap_int_eq, hHmap]
    exact dvd_mul_of_dvd_right hdvd _
  obtain ⟨G, hG⟩ := hFH
  have hGprim : G.IsPrimitive := isPrimitive_of_dvd hHprim (Dvd.intro_left F hG.symm)
  have hGlc : 0 < G.leadingCoeff := by
    have hlcFG : P.primPart.leadingCoeff = F.leadingCoeff * G.leadingCoeff := by
      rw [hG, leadingCoeff_mul]
    by_contra hneg
    push Not at hneg
    nlinarith
  exact ⟨c / P.content, P.primPart, G, hκpos, hHmap, hHprim, hG, hGprim, hGlc⟩

/-! ### The resultant comparison with a prescribed factor -/

/-- **The comparison in the proof of Proposition 6.3.** Let `r ≥ 0`, `m ≥ max{2r, 4}`,
`δ ∈ {0,1}`, `h = P_{2m+δ+r}^{(r)}/x^δ`, and let `F ∈ ℤ[x]` be primitive with positive leading
coefficient `u`, of degree `1 ≤ d ≤ m`, dividing `h` in `ℚ[x]`, with distinct real roots
`α_1, …, α_d`. Put `V_F = ∏_{i<j} (α_i - α_j)^2` and `K = binom(m+r, r)`. Then `u > 2^{c_F}`
and, comparing (2.11) of Lemma 2.6 (with (3.21)) with the upper bound (3.20),
`(2m-d) log 2 - log V_F / d + (1/2) log m - log K + ((2m-2d)/d) log(u/2^{c_F})
  < Ψ_m(S) + log A_{≤m}`. -/
theorem fixedFactor_resultant_comparison (hZ : JacobiSimpleRealZeros) {m r δ : ℕ} (hδ : δ ≤ 1) (hm :
    max (2 * r) 4 ≤ m)
    {F : ℤ[X]} (hFprim : F.IsPrimitive) (hFlc : 0 < F.leadingCoeff) {d : ℕ}
    (hdF : F.natDegree = d) (hd : 1 ≤ d) (hdm : d ≤ m)
    (hdvd : F.map (Int.castRingHom ℚ) ∣ derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ)
    {α : Fin d → ℝ} (hα : Function.Injective α)
    (hαF : ∀ i, (F.map (Int.castRingHom ℝ)).eval (α i) = 0) :
    (2 : ℤ) ^ shiftedTwoAdicOrder F < F.leadingCoeff ∧
    ((2 * m : ℝ) - d) * log 2 -
        log (∏ i, ∏ j ∈ univ.filter (fun j => i < j), (α i - α j) ^ 2) / d +
        log m / 2 - log ((m + r).choose r : ℝ) +
        ((2 * m : ℝ) - d - d) / d * log (F.leadingCoeff / 2 ^ shiftedTwoAdicOrder F) <
      primePowerLogSum m ((2 * (2 * m + δ) + 2 * r + 1 : ℕ) : ℝ) +
        log (primeTruncation (symmetricRatio (2 * m + δ) r) m) := by
  subst hdF
  obtain ⟨hr2, hm4⟩ : 2 * r ≤ m ∧ 4 ≤ m := ⟨le_of_max_le_left hm, le_of_max_le_right hm⟩
  have hm1 : 1 ≤ m := by omega
  obtain ⟨hnd, hcard, hroots⟩ := reduced_real_roots m r δ hZ hδ
  have hdeg := natDegree_reduced m r δ hδ
  have hh0 := reduced_ne_zero m r δ hδ
  have hXh := X_pow_mul_reduced m r δ hδ
  have hlc : 0 < (derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ).leadingCoeff := by
    have e := congrArg leadingCoeff hXh
    rw [leadingCoeff_mul, leadingCoeff_X_pow, one_mul,
      leadingCoeff_iterate_derivative_legendreP] at e
    rw [e]
    have : (0 : ℚ) < ((2 * (2 * m + δ) + 2 * r - 1).doubleFactorial : ℚ) := by
      exact_mod_cast Nat.doubleFactorial_pos _
    positivity
  -- an integral multiple
  obtain ⟨g, hg⟩ := exists_int_two_pow_mul_iterate_derivative_legendreP (2 * m + δ + r) r
  have hgh : (g /ₘ polyX ^ δ).map (Int.castRingHom ℚ) =
      C ((2 : ℚ) ^ (2 * m + δ + r)) * (derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ)
        := by
    rw [map_divByMonic _ (monic_X_pow δ), hg, Polynomial.map_pow, map_X]
    have e : C ((2 : ℚ) ^ (2 * m + δ + r)) * derivative^[r] (legendreP (2 * m + δ + r)) =
        polyX ^ δ * (C ((2 : ℚ) ^ (2 * m + δ + r)) *
          (derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ)) := by
      rw [mul_left_comm, hXh]
    rw [e, mul_divByMonic_cancel_left _ (monic_X_pow δ)]
  obtain ⟨κ, H, G, hκ, hH, hHprim, hHFG, hGprim, hGlc⟩ :=
    exists_primitive_factorization_of_dvd hh0 hlc (by positivity) hgh hFprim hFlc hdvd
  have hF0 : F ≠ 0 := hFprim.ne_zero
  have hG0 : G ≠ 0 := hGprim.ne_zero
  have hHdeg : H.natDegree = 2 * m := by
    rw [← natDegree_map_eq_of_injective (f := Int.castRingHom ℚ) Int.cast_injective H, hH,
      natDegree_C_mul hκ.ne', hdeg]
  have hdeN : F.natDegree + G.natDegree = 2 * m := by
    rw [← hHdeg, hHFG, natDegree_mul hF0 hG0]
  have hde : F.natDegree ≤ G.natDegree := by omega
  have hFGmap : (F * G).map (Int.castRingHom ℚ) =
      C κ * (derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ) := by
    rw [← hHFG]; exact hH
  -- the resultant is nonzero
  have hsep : (C κ * (derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ)).Separable :=
    Separable.unit_mul (isUnit_C.mpr (IsUnit.mk0 _ hκ.ne')) (reduced_separable hZ m r δ hδ)
  have hR : resultant F G ≠ 0 := by
    have hcop : IsCoprime (F.map (Int.castRingHom ℚ)) (G.map (Int.castRingHom ℚ)) := by
      apply Separable.isCoprime
      rw [← Polynomial.map_mul, hFGmap]; exact hsep
    intro h0
    apply resultant_ne_zero _ _ hcop
    rw [← intCast_resultant, h0, Int.cast_zero]
  -- Lemma 2.6
  have hbpos : 0 < (2 * m + δ + 2 * r).choose (2 * r) * (2 * r - 1).doubleFactorial :=
    Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.doubleFactorial_pos _)
  have hh1 : (derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ).eval 1 =
      (derivative^[r] (legendreP (2 * m + δ + r))).eval 1 := by
    have := congrArg (eval 1) hXh
    rw [eval_mul, eval_pow, eval_X, one_pow, one_mul] at this
    exact this
  have hb1 : (derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ).eval 1 =
      (((2 * m + δ + 2 * r).choose (2 * r) * (2 * r - 1).doubleFactorial : ℕ) : ℚ) := by
    rw [hh1, eval_one_iterate_derivative_legendreP_eq_choose]; push_cast; ring
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = Real.sqrt (((2 * m + δ : ℕ) : ℝ) *
      ((2 * m + δ : ℕ) + 2 * r + 1) *
      (aeval (0 : ℝ) (derivative^[r] (legendreP (2 * m + δ + r)))) ^ 2 +
      (aeval (0 : ℝ) (derivative (derivative^[r] (legendreP (2 * m + δ + r))))) ^ 2) := ⟨_, rfl⟩
  have hγpos : 0 < γ := by rw [hγ]; exact Real.sqrt_pos.mpr (symmetric_gammaSq_pos m r δ hm1 hδ)
  have hγ' : ∀ x ∈ ((derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ).map
      (algebraMap ℚ ℝ)).roots, γ < |(derivative ((derivative^[r] (legendreP (2 * m + δ + r)) /ₘ
        polyX ^ δ).map (algebraMap ℚ ℝ))).eval x| := by
    intro x hx
    obtain ⟨hx0, hx1, hx2⟩ := hroots x hx
    have hroot : aeval x (derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ) = 0 := by
      rw [aeval_def, eval₂_eq_eval_map]
      exact (mem_roots ((Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective).mpr hh0)).mp hx
    rw [derivative_map, eval_map, ← aeval_def, hγ]
    exact symmetric_gamma_lt_abs_derivative m r δ hm1 hδ ⟨hx1, hx2⟩ hx0 hroot
  have hrow := reduced_comp_row_bound_two m r δ hδ hm1
  obtain ⟨hcF, h211, -⟩ := realResultant_lowerBound (h := derivative^[r] (legendreP (2 * m + δ + r))
      /ₘ polyX ^ δ) (N := 2 * m)
    ⟨2 * m + δ + r, g /ₘ polyX ^ δ, hgh⟩ hdeg hlc hcard hnd hroots hbpos hb1 hγpos hγ' hrow hκ hH
    hHprim hHFG hFprim hGprim hFlc hGlc rfl rfl hd hde hdeN hα hαF
  -- the upper bound
  have hsupp : ∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℤ) ∣ resultant F G → p ≤ m := by
    intro p hp _ hdvd
    by_contra hpm
    push Not at hpm
    have hode : (1 - polyX ^ 2) * derivative (derivative (legendreP (2 * m + δ + r))) -
        2 * polyX * derivative (legendreP (2 * m + δ + r)) +
        C (((2 * m + δ + r : ℕ) : ℚ) * ((2 * m + δ + r : ℕ) + 1)) *
          legendreP (2 * m + δ + r) = 0 := by
      have h0 := jacobiP_ode 0 0 (2 * m + δ + r)
      rw [← legendreP_eq] at h0
      simp only [sub_self, map_zero, zero_add, zero_sub, add_zero] at h0
      rw [show (C (2 : ℚ)) = 2 from rfl] at h0
      linear_combination h0
    have hcoeff := iterate_derivative_legendreP (2 * m + δ) r
    rw [show (2 * m + δ) / 2 = m by omega] at hcoeff
    exact symmetric_prime_support hδ rfl hm hode hcoeff hFprim hGprim hFGmap hp hpm hdvd
  have hup := log_oddPart_le hR (by omega) hsupp (fun p hp hp2 _ => by
    have := Fact.mk hp
    exact padicValInt_resultant_le_symmetric m r δ hδ hm1 hκ.ne' hFGmap hFprim hGprim hR p hp2)
  have h2P : 2 ∈ (range (m + 1)).filter Nat.Prime :=
    mem_filter.mpr ⟨mem_range.mpr (by omega), Nat.prime_two⟩
  rw [Finset.sum_erase_eq_sub h2P] at hup
  have hsumD : ∑ p ∈ (range (m + 1)).filter Nat.Prime, (F.natDegree : ℝ) *
      ((Nat.log p (2 * (2 * m + δ) + 2 * r + 1) : ℝ) +
        padicValRat p (symmetricRatio (2 * m + δ) r)) * log p =
      F.natDegree * (primePowerLogSum m ((2 * (2 * m + δ) + 2 * r + 1 : ℕ) : ℝ) +
        log (primeTruncation (symmetricRatio (2 * m + δ) r) m)) := by
    rw [log_primeTruncation, primePowerLogSum_eq, ← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun p _ => ?_
    rw [floor_logb_natCast_eq]
    ring
  rw [hsumD] at hup
  -- the energy estimate
  have hdpos : (0 : ℝ) < F.natDegree := by exact_mod_cast hd
  have hγb : Real.sqrt m / ((m + r).choose r : ℝ) <
      γ / (((2 * m + δ + 2 * r).choose (2 * r) * (2 * r - 1).doubleFactorial : ℕ) : ℝ) := by
    have := sqrt_div_choose_lt_symmetric_gamma_div_eval_one m r δ hm1 hδ
    rw [aeval_one_eq_eval_one, ← hh1, hb1, ← hγ] at this
    simpa using this
  have hK : (0 : ℝ) < ((m + r).choose r : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  have hlogγ : log (Real.sqrt m / ((m + r).choose r : ℝ)) <
      log (γ / (((2 * m + δ + 2 * r).choose (2 * r) * (2 * r - 1).doubleFactorial : ℕ) : ℝ)) :=
    Real.log_lt_log (div_pos (Real.sqrt_pos.mpr hmpos) hK) hγb
  rw [Real.log_div (Real.sqrt_pos.mpr hmpos).ne' hK.ne', Real.log_sqrt hmpos.le] at hlogγ
  have hupd : log (|((resultant F G : ℤ) : ℝ)| / 2 ^ padicValInt 2 (resultant F G)) /
      F.natDegree ≤
      primePowerLogSum m ((2 * (2 * m + δ) + 2 * r + 1 : ℕ) : ℝ) +
        log (primeTruncation (symmetricRatio (2 * m + δ) r) m) -
        ((Nat.log 2 (2 * (2 * m + δ) + 2 * r + 1) : ℝ) +
          padicValRat 2 (symmetricRatio (2 * m + δ) r)) * log 2 := by
    rw [div_le_iff₀ hdpos]
    push_cast at hup ⊢
    linarith
  have hGe : (G.natDegree : ℝ) = 2 * m - F.natDegree := by
    have : ((F.natDegree + G.natDegree : ℕ) : ℝ) = ((2 * m : ℕ) : ℝ) := by rw [hdeN]
    push_cast at this
    linarith
  rw [hGe] at h211
  refine ⟨hcF, ?_⟩
  push_cast at hupd hlogγ h211 ⊢
  linarith

/-! ### Lemma 3.5 in the form used here -/

/-- **The upper half of Lemma 3.5, including `r = 0`.** For every `η > 0`, for all large `m`,
uniformly in `0 ≤ r ≤ m/2` and `δ ∈ {0,1}`,
`Ψ_m(S) + log K + log A_{≤m} ≤ m + r g(m/r) + η m` (for `r = 0` the term `r g(m/r)` is `0`).
Conditional on [Dusart10, Theorem 5.2] (`hPNT`). -/
theorem eventually_symmetric_upper (hPNT : ∀ x : ℝ, 3594641 ≤ x →
      |(∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, log (p : ℝ)) - x| < 0.2 * x / log x ^ 2)
    {η : ℝ} (hη : 0 < η) :
    ∃ M : ℕ, ∀ m r δ : ℕ, δ ≤ 1 → 2 * r ≤ m → M ≤ m →
      primePowerLogSum m ((2 * (2 * m + δ) + 2 * r + 1 : ℕ) : ℝ) + log ((m + r).choose r : ℝ) +
          log (primeTruncation (symmetricRatio (2 * m + δ) r) m) ≤
        m + r * asymptoticGapFunction ((m : ℝ) / r) + η * m := by
  obtain ⟨M₁, hM₁⟩ := symmetric_uniform_asymptotics hPNT hη
  have hκ : 1 ≤ 42 / η + 1 := by
    have : 0 < 42 / η := by positivity
    linarith
  obtain ⟨M₂, hM₂⟩ := eventually_atTop.mp (eventually_log_le_sqrt (42 / η + 1) hκ)
  refine ⟨max M₁ M₂, fun m r δ hδ hrm hm => ?_⟩
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · obtain ⟨hx, hL, hLu, hu⟩ := hM₂ m (le_of_max_le_right hm)
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have herr := symmetric_error_le hκ hm0.le hL hLu hu
    have hΨ := primePowerLogSum_symmetric_le hPNT hδ (r := 0) (by omega) hx
    have hK0 : log (((m + 0).choose 0 : ℕ) : ℝ) = 0 := by simp
    have hA0 : log (primeTruncation (symmetricRatio (2 * m + δ) 0) m) = 0 := by
      rw [symmetricRatio_zero_right, log_primeTruncation_one]
    have hsmall : 42 / (42 / η + 1) * m ≤ η * m := by
      apply mul_le_mul_of_nonneg_right _ hm0.le
      rw [div_le_iff₀ (by positivity)]
      have : η * (42 / η + 1) = 42 + η := by field_simp
      linarith
    have hu1 : 1 ≤ √(m : ℝ) := hκ.trans hu
    have hL0 : 0 ≤ log (m : ℝ) := by linarith
    have h8 : 0 ≤ log (8 * √(m : ℝ)) := Real.log_nonneg (by linarith)
    have hε0 : 0 ≤ 0.2 / log (m : ℝ) ^ 2 * m := by positivity
    have huL : 0 ≤ √(m : ℝ) * log (m : ℝ) := by positivity
    rw [hK0, hA0, Nat.cast_zero, zero_mul]
    linarith
  · have h := (abs_le.mp (hM₁ m r δ hδ hr hrm (le_of_max_le_left hm))).2
    linarith

/-- For `c ≥ 1` with `c r ≤ m`: `r g(m/r) ≤ m G` whenever `g(c)/c ≤ G` and `0 ≤ G`
(the case `r = 0` included). -/
theorem mul_asymptoticGapFunction_le_of_le {c G : ℝ} (hc : 1 ≤ c)
    (hG : asymptoticGapFunction c / c ≤ G) (hG0 : 0 ≤ G) {m r : ℕ} (hcr : c * r ≤ m) :
    (r : ℝ) * asymptoticGapFunction ((m : ℝ) / r) ≤ m * G := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · rw [Nat.cast_zero, zero_mul]; exact mul_nonneg (Nat.cast_nonneg _) hG0
  · exact (mul_asymptoticGapFunction_le hc (by exact_mod_cast hr) hcr).trans
      (mul_le_mul_of_nonneg_left hG (Nat.cast_nonneg _))

/-! ### Proposition 6.3 -/

/-- `β(F) = log 4 + (2/d) log(u / 2^{c_F})` of Proposition 6.3, with `d = deg F`, `u = lc F`
and `c_F = min_j v_2([X^j] F(2X+1))`. -/
noncomputable def fixedFactorExponent (F : ℤ[X]) : ℝ :=
  log 4 + 2 / F.natDegree * log (F.leadingCoeff / 2 ^ shiftedTwoAdicOrder F)

theorem fixedFactorExponent_eq (F : ℤ[X]) : fixedFactorExponent F =
    log 4 + 2 / F.natDegree * log (F.leadingCoeff / 2 ^ shiftedTwoAdicOrder F) := (rfl)

/-- **Proposition 6.3.** Let `F ∈ ℤ[x]` be primitive, of degree
`d ≥ 1`, with positive leading coefficient `u`, `d` distinct roots in `(-1,1)` and `F(0) ≠ 0`.
Put `c_F = min_j v_2([X^j] F(2X+1))` and `β(F) = log 4 + (2/d) log(u/2^{c_F})`. Let `c ≥ 2`
satisfy `c(β(F) - 1) > g(c)`. For all sufficiently large `m`, uniformly for `0 ≤ r ≤ m/c` and
`δ ∈ {0,1}`, `F ∤ C_{2m+δ}^{r+1/2}(x)/x^δ` (in `ℚ[x]`). Conditional on the cited
`JacobiSimpleRealZeros` ([DLMF, §18.2(vi)])
and `DusartThetaBound` ([Dusart10, Theorem 5.2]). -/
theorem not_dvd_reducedGegenbauer_of_fixedFactor (hZ : JacobiSimpleRealZeros) (hD :
    DusartThetaBound) {F : ℤ[X]} (hFprim : F.IsPrimitive)
    (hd : 1 ≤ F.natDegree) (hFlc : 0 < F.leadingCoeff)
    (hnd : (F.map (Int.castRingHom ℝ)).roots.Nodup)
    (hcard : (F.map (Int.castRingHom ℝ)).roots.card = F.natDegree)
    (hroots : ∀ x ∈ (F.map (Int.castRingHom ℝ)).roots, -1 < x ∧ x < 1) (hF0 : F.eval 0 ≠ 0)
    {c : ℝ} (hc : 2 ≤ c) (hgap : asymptoticGapFunction c < c * (fixedFactorExponent F - 1)) :
    ∃ M : ℕ, ∀ m r δ : ℕ, δ ≤ 1 → M ≤ m → c * r ≤ m →
      ¬ F.map (Int.castRingHom ℚ) ∣ reducedGegenbauer m r δ := by
  have hPNT := dusartThetaBound_sum hD
  have hinj : Function.Injective (Int.castRingHom ℝ) := Int.cast_injective
  have hFr0 : F.map (Int.castRingHom ℝ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff hinj).mpr hFprim.ne_zero
  -- the roots of `F`
  obtain ⟨α, hα, hαF⟩ := exists_injective_roots_of_mul (F := F) (G := 1)
    (by rw [mul_one]; exact hFprim.ne_zero) (by rw [mul_one]; exact hnd)
    (by rw [mul_one]; exact hcard)
  -- `u > 2^{c_F}`
  have hroots' : ∀ x ∈ (F.map (Int.castRingHom ℝ)).roots, x ≠ 0 ∧ -1 < x ∧ x < 1 := by
    intro x hx
    refine ⟨?_, hroots x hx⟩
    rintro rfl
    apply hF0
    have h0 : (F.map (Int.castRingHom ℝ)).eval 0 = 0 := (mem_roots hFr0).mp hx
    rw [eval_zero_map, eq_intCast, Int.cast_eq_zero] at h0
    exact h0
  have hz := two_pow_shiftedTwoAdicOrder_lt_leadingCoeff (by omega) hFlc hcard hroots'
  have hzR : (1 : ℝ) < (F.leadingCoeff : ℝ) / 2 ^ shiftedTwoAdicOrder F := by
    rw [one_lt_div (by positivity)]
    exact_mod_cast hz
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = log ((F.leadingCoeff : ℝ) / 2 ^ shiftedTwoAdicOrder F) :=
    ⟨_, rfl⟩
  have hL0 : 0 < L := by rw [hL]; exact Real.log_pos hzR
  have hdR : (0 : ℝ) < F.natDegree := by exact_mod_cast hd
  have h4 : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hl2 := Real.log_two_gt_d9
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = 2 * log 2 + 2 / F.natDegree * L := ⟨_, rfl⟩
  have hβF : fixedFactorExponent F = β := by rw [fixedFactorExponent_eq, h4, hβ, hL]
  rw [hβF] at hgap
  have hβ1 : 1 < β := by
    have : 0 < 2 / (F.natDegree : ℝ) * L := mul_pos (div_pos two_pos hdR) hL0
    linarith
  have hc0 : 0 < c := by linarith
  have hgc : asymptoticGapFunction c / c < β - 1 := by
    rw [div_lt_iff₀ hc0]; linarith
  -- the margin
  obtain ⟨η, hη0, hη1, hη2⟩ : ∃ η : ℝ, 0 < η ∧ 2 * η ≤ β - 1 - asymptoticGapFunction c / c ∧
      2 * η ≤ β - 1 :=
    ⟨min (β - 1 - asymptoticGapFunction c / c) (β - 1) / 2,
      div_pos (lt_min (by linarith) (by linarith)) two_pos,
      by linarith [min_le_left (β - 1 - asymptoticGapFunction c / c) (β - 1)],
      by linarith [min_le_right (β - 1 - asymptoticGapFunction c / c) (β - 1)]⟩
  obtain ⟨M₁, hM₁⟩ := eventually_symmetric_upper hPNT hη0
  -- the constant `C_F = d log 2 + 2 log z + (1/d) log V_F`
  obtain ⟨CF, hCF⟩ : ∃ CF : ℝ, CF = F.natDegree * log 2 + 2 * L +
      log (∏ i, ∏ j ∈ univ.filter (fun j => i < j), (α i - α j) ^ 2) / F.natDegree :=
    ⟨_, rfl⟩
  refine ⟨max (max M₁ (⌈CF / η⌉₊ + 1)) (max 4 F.natDegree), fun m r δ hδ hm hcr hdvd => ?_⟩
  obtain ⟨⟨hm1, hm2⟩, hm3, hm4⟩ : (M₁ ≤ m ∧ ⌈CF / η⌉₊ + 1 ≤ m) ∧ 4 ≤ m ∧ F.natDegree ≤ m := by
    simp only [max_le_iff] at hm; exact hm
  have hr2 : 2 * r ≤ m := by
    have : (2 : ℝ) * r ≤ m := le_trans (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg r)) hcr
    exact_mod_cast this
  have hdvd' : F.map (Int.castRingHom ℚ) ∣
      derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ := by
    rw [reducedDerivative_eq_C_mul_reducedGegenbauer m r δ hδ]
    exact dvd_mul_of_dvd_right hdvd _
  obtain ⟨-, hcmp⟩ := fixedFactor_resultant_comparison hZ hδ (max_le hr2 hm3) hFprim hFlc
    rfl hd hm4 hdvd' hα hαF
  rw [← hL] at hcmp
  have hup := hM₁ m r δ hδ hr2 hm1
  have hG0 : 0 ≤ β - 1 - 2 * η := by linarith
  have hrg := mul_asymptoticGapFunction_le_of_le (G := β - 1 - 2 * η) (by linarith)
    (by linarith) hG0 hcr
  have hmR : (4 : ℝ) ≤ m := by exact_mod_cast hm3
  have hlogm : 0 ≤ log (m : ℝ) := Real.log_nonneg (by linarith)
  have hid : ((2 * m : ℝ) - F.natDegree) * log 2 +
      ((2 * m : ℝ) - F.natDegree - F.natDegree) / F.natDegree * L =
      m * β - (F.natDegree * log 2 + 2 * L) := by
    have hdne : (F.natDegree : ℝ) ≠ 0 := hdR.ne'
    rw [hβ]; field_simp; ring
  have hMR : CF / η + 1 ≤ (m : ℝ) := by
    have h1 : CF / η ≤ (⌈CF / η⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈CF / η⌉₊ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm2
    push_cast at h2
    linarith
  have hηm : CF < η * m := by
    have : CF / η < m := by linarith
    rw [div_lt_iff₀ hη0] at this
    linarith
  have hmβ : (m : ℝ) * (β - 1 - 2 * η) = m * β - m - 2 * η * m := by ring
  rw [hmβ] at hrg
  rw [hCF] at hηm
  linarith

/-! ### Corollary 6.4 -/

/-- **Corollary 6.4.** There is an absolute integer `M₁` such that for
`m ≥ M₁` and `0 ≤ r ≤ m/2`, neither `C_{2m}^{r+1/2}` nor `C_{2m+1}^{r+1/2}/x` has a rational
root. Conditional on `JacobiSimpleRealZeros`
([DLMF, §18.2(vi)]) and `DusartThetaBound` ([Dusart10, Theorem 5.2]). -/
theorem noRationalRootsStatement_of (hZ : JacobiSimpleRealZeros)
    (hD : DusartThetaBound) : NoRationalRootsStatement := by
  have hPNT := dusartThetaBound_sum hD
  have hgap := margin_asymptoticGapFunction_two
  have h9 : log (9 : ℝ) = 2 * log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h3 := log_three_gt
  have h3u : log (3 : ℝ) ≤ 3 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have hl2 := Real.log_two_gt_d9
  have h32 : log (3 / 2 : ℝ) = log 3 - log 2 := Real.log_div (by norm_num) (by norm_num)
  obtain ⟨η, hη0, hη1, hη2⟩ : ∃ η : ℝ, 0 < η ∧
      2 * η ≤ log 9 - 1 - asymptoticGapFunction 2 / 2 ∧ 2 * η ≤ log 9 - 1 :=
    ⟨min (log 9 - 1 - asymptoticGapFunction 2 / 2) (log 9 - 1) / 2,
      div_pos (lt_min (by linarith) (by linarith)) two_pos,
      by linarith [min_le_left (log 9 - 1 - asymptoticGapFunction 2 / 2) (log 9 - 1)],
      by linarith [min_le_right (log 9 - 1 - asymptoticGapFunction 2 / 2) (log 9 - 1)]⟩
  obtain ⟨M₁, hM₁⟩ := eventually_symmetric_upper hPNT hη0
  refine ⟨max (max M₁ (⌈4 / η⌉₊ + 1)) 4, fun m r δ hm hr2 hδ q hq => ?_⟩
  obtain ⟨⟨hm1, hm2⟩, hm3⟩ : (M₁ ≤ m ∧ ⌈4 / η⌉₊ + 1 ≤ m) ∧ 4 ≤ m := by
    simp only [max_le_iff] at hm; exact hm
  -- the primitive linear factor `F = u x - v` with `q = v/u`
  have hden : (0 : ℤ) < q.den := by exact_mod_cast q.den_pos
  obtain ⟨F, hF⟩ : ∃ F : ℤ[X], F = C (q.den : ℤ) * polyX + C (-q.num) := ⟨_, rfl⟩
  have hFdeg : F.natDegree = 1 := by rw [hF]; exact natDegree_linear hden.ne'
  have hFlc : F.leadingCoeff = q.den := by rw [hF]; exact leadingCoeff_linear hden.ne'
  have hFprim : F.IsPrimitive := by
    refine isPrimitive_iff_isUnit_of_C_dvd.mpr fun a ha => ?_
    rw [C_dvd_iff_dvd_coeff] at ha
    have c1 : F.coeff 1 = q.den := by
      rw [hF, coeff_add, coeff_C_mul, coeff_X_one, coeff_C]; simp
    have c0 : F.coeff 0 = -q.num := by
      rw [hF, coeff_add, coeff_C_mul, coeff_X_zero, coeff_C_zero]; simp
    have h1 := ha 1
    have h0 := ha 0
    rw [c1] at h1
    rw [c0, dvd_neg] at h0
    exact (Rat.isCoprime_num_den q).isUnit_of_dvd' h0 h1
  have hnum : (q.den : ℚ) * q = q.num := by rw [mul_comm]; exact Rat.mul_den_eq_num q
  have hFmap : F.map (Int.castRingHom ℚ) = C (q.den : ℚ) * (polyX - C q) := by
    rw [hF, mul_sub, ← C_mul, hnum, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_C, map_X]
    simp only [eq_intCast, Int.cast_natCast, Int.cast_neg, C_neg, sub_eq_add_neg]
  have hdenQ : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hdvd : F.map (Int.castRingHom ℚ) ∣ reducedGegenbauer m r δ := by
    rw [hFmap]
    exact (isUnit_C.mpr (IsUnit.mk0 _ hdenQ)).mul_left_dvd.mpr (dvd_iff_isRoot.mpr hq)
  have hdvd' : F.map (Int.castRingHom ℚ) ∣
      derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ := by
    rw [reducedDerivative_eq_C_mul_reducedGegenbauer m r δ hδ]
    exact dvd_mul_of_dvd_right hdvd _
  -- its root
  have hαF : ∀ i : Fin 1, (F.map (Int.castRingHom ℝ)).eval ((fun _ => (q : ℝ)) i) = 0 := by
    intro _
    have hnumR : (q.den : ℝ) * q = q.num := by exact_mod_cast hnum
    rw [hF, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C, map_X]
    simp only [eval_add, eval_mul, eval_C, eval_X, eq_intCast, Int.cast_natCast, Int.cast_neg,
      hnumR]
    ring
  have hα : Function.Injective (fun _ : Fin 1 => (q : ℝ)) := fun i j _ => Subsingleton.elim i j
  obtain ⟨hcF, hcmp⟩ := fixedFactor_resultant_comparison hZ hδ (max_le hr2 hm3) hFprim
    (by rw [hFlc]; exact hden) hFdeg le_rfl (by omega) hdvd' hα hαF
  have hV1 : ∏ i : Fin 1, ∏ j ∈ univ.filter (fun j => i < j), ((q : ℝ) - q) ^ 2 = 1 :=
    prod_eq_one fun i _ => prod_eq_one fun j hj =>
      absurd (mem_filter.mp hj).2 (by rw [Subsingleton.elim i j]; exact lt_irrefl j)
  rw [hV1, Real.log_one] at hcmp
  -- `c_F ≤ 1`, hence `z = u / 2^{c_F} ≥ 3/2`
  have hs1 : shiftedTwoAdicOrder F ≤ 1 := by
    have e1 : F.eval 1 = q.den - q.num := by
      rw [hF]; simp only [eval_add, eval_mul, eval_C, eval_X]; ring
    have em1 : F.eval (-1) = -q.den - q.num := by
      rw [hF]; simp only [eval_add, eval_mul, eval_C, eval_X]; ring
    have hd1 := two_pow_dvd_eval_one F
    have hdm1 := two_pow_dvd_eval_neg_one F
    rw [e1] at hd1
    rw [em1] at hdm1
    have h2den : (2 : ℤ) ^ shiftedTwoAdicOrder F ∣ 2 * (q.den : ℤ) := by
      have := dvd_sub hd1 hdm1
      convert this using 1; ring
    have h2num : (2 : ℤ) ^ shiftedTwoAdicOrder F ∣ 2 * q.num := by
      have := dvd_neg.mpr (dvd_add hd1 hdm1)
      convert this using 1; ring
    obtain ⟨a, b, hab⟩ := Rat.isCoprime_num_den q
    have h2 : (2 : ℤ) ^ shiftedTwoAdicOrder F ∣ 2 := by
      have := dvd_add (h2num.mul_left a) (h2den.mul_left b)
      convert this using 1
      linear_combination -2 * hab
    by_contra hs
    push Not at hs
    have h4 : (2 : ℤ) ^ 2 ∣ 2 := (pow_dvd_pow 2 hs).trans h2
    norm_num at h4
  have key : ∀ s : ℕ, s ≤ 1 → (2 : ℤ) ^ s < q.den →
      (3 / 2 : ℝ) ≤ ((q.den : ℤ) : ℝ) / 2 ^ s := by
    intro s hs h
    rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
    · have h2 : (2 : ℤ) ≤ q.den := by rw [pow_zero] at h; omega
      have : (2 : ℝ) ≤ ((q.den : ℤ) : ℝ) := by exact_mod_cast h2
      rw [pow_zero, div_one]; linarith
    · have h3' : (3 : ℤ) ≤ q.den := by rw [pow_one] at h; omega
      have : (3 : ℝ) ≤ ((q.den : ℤ) : ℝ) := by exact_mod_cast h3'
      rw [pow_one, le_div_iff₀ (by norm_num)]; linarith
  have hzge : (3 / 2 : ℝ) ≤ (F.leadingCoeff : ℝ) / 2 ^ shiftedTwoAdicOrder F := by
    rw [hFlc]; exact key _ hs1 (hFlc ▸ hcF)
  have hlogz : log (3 / 2 : ℝ) ≤ log ((F.leadingCoeff : ℝ) / 2 ^ shiftedTwoAdicOrder F) :=
    Real.log_le_log (by norm_num) hzge
  have hmR : (4 : ℝ) ≤ m := by exact_mod_cast hm3
  have hmul : ((2 * m : ℝ) - 1 - 1) * log (3 / 2 : ℝ) ≤
      ((2 * m : ℝ) - 1 - 1) * log ((F.leadingCoeff : ℝ) / 2 ^ shiftedTwoAdicOrder F) :=
    mul_le_mul_of_nonneg_left hlogz (by linarith)
  simp only [Nat.cast_one, div_one, sub_zero] at hcmp
  have hup := hM₁ m r δ hδ hr2 hm1
  have hG0 : 0 ≤ log 9 - 1 - 2 * η := by linarith
  have hrg := mul_asymptoticGapFunction_le_of_le (c := 2) (G := log 9 - 1 - 2 * η)
    (by norm_num) (by linarith) hG0 (m := m) (r := r) (by exact_mod_cast hr2)
  have hlogm : 0 ≤ log (m : ℝ) := Real.log_nonneg (by linarith)
  have hMR : 4 / η + 1 ≤ (m : ℝ) := by
    have h1 : 4 / η ≤ (⌈4 / η⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈4 / η⌉₊ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm2
    push_cast at h2
    linarith
  have hηm : 4 < η * m := by
    have : 4 / η < m := by linarith
    rw [div_lt_iff₀ hη0] at this
    linarith
  have hmβ : (m : ℝ) * (log 9 - 1 - 2 * η) = m * log 9 - m - 2 * η * m := by ring
  rw [hmβ, h9] at hrg
  rw [h32] at hmul
  linarith

end ArithmeticOfJacobiPolynomials
