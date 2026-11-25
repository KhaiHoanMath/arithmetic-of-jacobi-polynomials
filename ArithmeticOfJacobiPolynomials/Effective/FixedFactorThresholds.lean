/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Effective.SymmetricThresholds
public import ArithmeticOfJacobiPolynomials.Applications.ConeModes

/-!
# Explicit thresholds for Proposition 6.3, Corollary 6.4 and Corollary 6.5 (2), (3)

* **Lemma 3.5, upper half, explicit** (`symmetric_upper_of_logSqrtThreshold_le`): the upper
  bound `Ψ_m(S) + log K + log A_{≤m} ≤ m + r g(m/r) + η m`, including `r = 0`, for every
  `m ≥ logSqrtThreshold k`, `42/η + 1 ≤ k` (from
  `symmetric_uniform_asymptotics_of_logSqrtThreshold_le`).
* **Proposition 6.3, effective** ("for rational `c`, the
  threshold is effective in `F, c`"): for `F` of degree `d` with leading coefficient `u`, and a
  positive rational `η` with `2η ≤ β(F) - 1 - g(c)/c` and `2η ≤ β(F) - 1` (such `η` exists
  under (6.3), `exists_rat_fixedFactor_margin`), the explicit computable threshold is
  `fixedFactorThreshold d u η = max (max (logSqrtThreshold (⌈42/η⌉₊ + 1)) (⌈(3d + 2u)/η⌉₊ + 1))
  (max 4 d)` (`not_dvd_reducedGegenbauer_of_fixedFactorThreshold_le`). The constant
  `C_F = d log 2 + 2 log z + (1/d) log V_F` of the proof is bounded by `3d + 2u`, since the
  roots lie in `(-1, 1)`, so `V_F ≤ 4^{d²}`, and `log z ≤ u - 1`.
* **Corollary 6.4, effective** ("an effective absolute integer
  `M₁`"): `rationalRootsThreshold = logSqrtThreshold 841 + 81`, using the explicit margin
  `2(log 9 - 1) - g(2) ≥ 1/5` (`noRationalRoots_of_rationalRootsThreshold_le`).
* **Corollary 6.5 (2)** ("an effective absolute threshold"):
  `coneModesSqrtThreeThreshold = 3 · fixedFactorThreshold 2 3 (1/1200) + 3`
  (`coneModes_sqrt_three_effective`), with `F = 3x² - 1`, `c = 19/8`, `η = 1/1200`.
* **Corollary 6.5 (3)**: `coneModesRationalThreshold = 3 · rationalRootsThreshold + 3`
  (`coneModes_rational_effective`).

All are conditional on the proved `intervalVandermondeBound` (Lemma 2.5),
`JacobiSimpleRealZeros` ([DLMF, §18.2(vi)]) and `DusartThetaBound` ([Dusart10, Theorem 5.2]).
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset Real

/-! ### The upper half of Lemma 3.5 with an explicit threshold -/

/-- **The upper half of Lemma 3.5, explicit, including `r = 0`.** If `η > 0`, `42/η + 1 ≤ k`
and `m ≥ logSqrtThreshold k`, then for `2r ≤ m`, `δ ≤ 1`:
`Ψ_m(S) + log K + log A_{≤m} ≤ m + r g(m/r) + η m`. -/
theorem symmetric_upper_of_logSqrtThreshold_le (hD : DusartThetaBound) {η : ℝ} (hη : 0 < η)
    {k : ℕ} (hk : 42 / η + 1 ≤ k) :
    ∀ m r δ : ℕ, δ ≤ 1 → 2 * r ≤ m → logSqrtThreshold k ≤ m →
      primePowerLogSum m ((2 * (2 * m + δ) + 2 * r + 1 : ℕ) : ℝ) + log ((m + r).choose r : ℝ) +
          log (primeTruncation (symmetricRatio (2 * m + δ) r) m) ≤
        m + r * asymptoticGapFunction ((m : ℝ) / r) + η * m := by
  have hPNT := dusartThetaBound_sum hD
  have hκ : 1 ≤ 42 / η + 1 := by
    have : 0 < 42 / η := by positivity
    linarith
  intro m r δ hδ hrm hm
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · obtain ⟨hx, hL, hLu, hu⟩ := log_le_sqrt_of_logSqrtThreshold_le hκ hk hm
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
  · have h := (abs_le.mp (symmetric_uniform_asymptotics_of_logSqrtThreshold_le hD hη hk m r δ
      hδ hr hrm hm)).2
    linarith

/-! ### Proposition 6.3 with an explicit threshold -/

/-- `β(F) > 1` under the hypotheses of Proposition 6.3 (`u > 2^{c_F}`). -/
theorem one_lt_fixedFactorExponent {F : ℤ[X]} (hFprim : F.IsPrimitive)
    (hd : 1 ≤ F.natDegree) (hFlc : 0 < F.leadingCoeff)
    (hcard : (F.map (Int.castRingHom ℝ)).roots.card = F.natDegree)
    (hroots : ∀ x ∈ (F.map (Int.castRingHom ℝ)).roots, -1 < x ∧ x < 1) (hF0 : F.eval 0 ≠ 0) :
    1 < fixedFactorExponent F := by
  have hinj : Function.Injective (Int.castRingHom ℝ) := Int.cast_injective
  have hFr0 : F.map (Int.castRingHom ℝ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff hinj).mpr hFprim.ne_zero
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
  have hL0 : 0 < log ((F.leadingCoeff : ℝ) / 2 ^ shiftedTwoAdicOrder F) := Real.log_pos hzR
  have hdR : (0 : ℝ) < F.natDegree := by exact_mod_cast hd
  have h4 : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hl2 := Real.log_two_gt_d9
  have : 0 < 2 / (F.natDegree : ℝ) * log ((F.leadingCoeff : ℝ) / 2 ^ shiftedTwoAdicOrder F) :=
    mul_pos (div_pos two_pos hdR) hL0
  rw [fixedFactorExponent_eq, h4]
  linarith

/-- Under (6.3), a rational margin as required by
`not_dvd_reducedGegenbauer_of_fixedFactorThreshold_le` exists. -/
theorem exists_rat_fixedFactor_margin {F : ℤ[X]} {c : ℝ} (hc : 2 ≤ c)
    (hβ : 1 < fixedFactorExponent F)
    (hgap : asymptoticGapFunction c < c * (fixedFactorExponent F - 1)) :
    ∃ η : ℚ, 0 < η ∧ 2 * (η : ℝ) ≤ fixedFactorExponent F - 1 - asymptoticGapFunction c / c ∧
      2 * (η : ℝ) ≤ fixedFactorExponent F - 1 := by
  have hc0 : 0 < c := by linarith
  have hgc : asymptoticGapFunction c / c < fixedFactorExponent F - 1 := by
    rw [div_lt_iff₀ hc0]; linarith
  obtain ⟨q, hq0, hq1⟩ := exists_rat_btwn (show (0 : ℝ) <
    min (fixedFactorExponent F - 1 - asymptoticGapFunction c / c) (fixedFactorExponent F - 1) / 2
    from div_pos (lt_min (by linarith) (by linarith)) two_pos)
  refine ⟨q, by exact_mod_cast hq0, ?_, ?_⟩
  · linarith [min_le_left (fixedFactorExponent F - 1 - asymptoticGapFunction c / c)
      (fixedFactorExponent F - 1)]
  · linarith [min_le_right (fixedFactorExponent F - 1 - asymptoticGapFunction c / c)
      (fixedFactorExponent F - 1)]

/-- The explicit computable threshold of Proposition 6.3 for `F` of degree `d`, leading
coefficient `u` and a rational margin `η`:
`max (max (logSqrtThreshold (⌈42/η⌉₊ + 1)) (⌈(3d + 2u)/η⌉₊ + 1)) (max 4 d)`. -/
def fixedFactorThreshold (d u : ℕ) (η : ℚ) : ℕ :=
  max (max (logSqrtThreshold (⌈42 / η⌉₊ + 1)) (⌈(3 * d + 2 * u : ℚ) / η⌉₊ + 1)) (max 4 d)

theorem fixedFactorThreshold_eq (d u : ℕ) (η : ℚ) : fixedFactorThreshold d u η =
    max (max (logSqrtThreshold (⌈42 / η⌉₊ + 1)) (⌈(3 * d + 2 * u : ℚ) / η⌉₊ + 1))
      (max 4 d) := (rfl)

/-- `log V_F ≤ d · log 4 · d` for `d` roots in `(-1, 1)`. -/
theorem log_prod_sq_sub_le {d : ℕ} (α : Fin d → ℝ) (hα : ∀ i, -1 < α i ∧ α i < 1) :
    log (∏ i, ∏ j ∈ univ.filter (fun j => i < j), (α i - α j) ^ 2) ≤ d * (d * log 4) := by
  have hf0 : ∀ i j, 0 ≤ (α i - α j) ^ 2 := fun i j => sq_nonneg _
  have hf4 : ∀ i j, (α i - α j) ^ 2 ≤ 4 := by
    intro i j
    obtain ⟨hi1, hi2⟩ := hα i
    obtain ⟨hj1, hj2⟩ := hα j
    nlinarith
  have hinner : ∀ i, ∏ j ∈ univ.filter (fun j => i < j), (α i - α j) ^ 2 ≤ (4 : ℝ) ^ d := by
    intro i
    calc ∏ j ∈ univ.filter (fun j => i < j), (α i - α j) ^ 2
        ≤ ∏ _j ∈ univ.filter (fun j => i < j), (4 : ℝ) :=
          prod_le_prod₀ (fun j _ => hf0 i j) (fun j _ => hf4 i j)
      _ = 4 ^ (univ.filter (fun j => i < j)).card := prod_const _
      _ ≤ 4 ^ d := by
          refine pow_le_pow_right₀ (by norm_num) ?_
          exact (card_filter_le _ _).trans_eq (by rw [card_univ, Fintype.card_fin])
  have hV : ∏ i, ∏ j ∈ univ.filter (fun j => i < j), (α i - α j) ^ 2 ≤ ((4 : ℝ) ^ d) ^ d := by
    calc ∏ i, ∏ j ∈ univ.filter (fun j => i < j), (α i - α j) ^ 2
        ≤ ∏ _i : Fin d, (4 : ℝ) ^ d :=
          prod_le_prod₀ (fun i _ => prod_nonneg fun j _ => hf0 i j) (fun i _ => hinner i)
      _ = ((4 : ℝ) ^ d) ^ d := by rw [prod_const, card_univ, Fintype.card_fin]
  have hV0 : 0 ≤ ∏ i, ∏ j ∈ univ.filter (fun j => i < j), (α i - α j) ^ 2 :=
    prod_nonneg fun i _ => prod_nonneg fun j _ => hf0 i j
  have hrhs : log (((4 : ℝ) ^ d) ^ d) = d * (d * log 4) := by rw [Real.log_pow, Real.log_pow]
  have hl4 : 0 ≤ log (4 : ℝ) := Real.log_nonneg (by norm_num)
  rcases hV0.eq_or_lt with h0 | hpos
  · rw [← h0, Real.log_zero]
    positivity
  · rw [← hrhs]
    exact Real.log_le_log hpos hV

/-- **Proposition 6.3, effective form.** Let `F ∈ ℤ[x]` be primitive of
degree `d ≥ 1` with leading coefficient `u > 0`, `d` distinct roots in `(-1,1)` and
`F(0) ≠ 0`, let `c ≥ 2`, and let `η` be a positive rational with
`2η ≤ β(F) - 1 - g(c)/c` and `2η ≤ β(F) - 1` (a rational lower bound for the margin of (6.3),
`exists_rat_fixedFactor_margin`). For every `m ≥ fixedFactorThreshold d u η`, `δ ∈ {0,1}` and
`r` with `c r ≤ m`, `F ∤ C_{2m+δ}^{r+1/2}(x)/x^δ`. Conditional on
`JacobiSimpleRealZeros` and `DusartThetaBound`. -/
theorem not_dvd_reducedGegenbauer_of_fixedFactorThreshold_le (hZ : JacobiSimpleRealZeros) (hD :
    DusartThetaBound) {F : ℤ[X]} (hFprim : F.IsPrimitive)
    {d u : ℕ} (hdF : F.natDegree = d) (huF : F.leadingCoeff = u) (hd : 1 ≤ d) (hu : 0 < u)
    (hnd : (F.map (Int.castRingHom ℝ)).roots.Nodup)
    (hcard : (F.map (Int.castRingHom ℝ)).roots.card = F.natDegree)
    (hroots : ∀ x ∈ (F.map (Int.castRingHom ℝ)).roots, -1 < x ∧ x < 1)
    {c : ℝ} (hc : 2 ≤ c) {η : ℚ} (hη : 0 < η)
    (hη1 : 2 * (η : ℝ) ≤ fixedFactorExponent F - 1 - asymptoticGapFunction c / c)
    (hη2 : 2 * (η : ℝ) ≤ fixedFactorExponent F - 1) :
    ∀ m r δ : ℕ, δ ≤ 1 → fixedFactorThreshold d u η ≤ m → c * r ≤ m →
      ¬ F.map (Int.castRingHom ℚ) ∣ reducedGegenbauer m r δ := by
  have hFlc : 0 < F.leadingCoeff := by rw [huF]; exact_mod_cast hu
  have hinj : Function.Injective (Int.castRingHom ℝ) := Int.cast_injective
  have hFr0 : F.map (Int.castRingHom ℝ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff hinj).mpr hFprim.ne_zero
  -- the roots of `F`
  obtain ⟨α, hα, hαF⟩ := exists_injective_roots_of_mul (F := F) (G := 1)
    (by rw [mul_one]; exact hFprim.ne_zero) (by rw [mul_one]; exact hnd)
    (by rw [mul_one]; exact hcard)
  have hαI : ∀ i, -1 < α i ∧ α i < 1 := fun i => hroots _ ((mem_roots hFr0).mpr (hαF i))
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = log ((F.leadingCoeff : ℝ) / 2 ^ shiftedTwoAdicOrder F) :=
    ⟨_, rfl⟩
  have hdR : (0 : ℝ) < F.natDegree := by
    have : 1 ≤ F.natDegree := by omega
    exact_mod_cast this
  have h4 : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = 2 * log 2 + 2 / F.natDegree * L := ⟨_, rfl⟩
  have hβF : fixedFactorExponent F = β := by rw [fixedFactorExponent_eq, h4, hβ, hL]
  rw [hβF] at hη1 hη2
  obtain ⟨ηr, hηr⟩ : ∃ ηr : ℝ, ηr = (η : ℝ) := ⟨_, rfl⟩
  rw [← hηr] at hη1 hη2
  have hη0 : 0 < ηr := by rw [hηr]; exact_mod_cast hη
  -- `L ≤ u - 1`
  have hlcR : (0 : ℝ) < (F.leadingCoeff : ℝ) := by exact_mod_cast hFlc
  have hLu : L ≤ (F.leadingCoeff : ℝ) - 1 := by
    have h1 : (F.leadingCoeff : ℝ) / 2 ^ shiftedTwoAdicOrder F ≤ (F.leadingCoeff : ℝ) :=
      div_le_self hlcR.le (one_le_pow₀ (by norm_num))
    have h2 := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < (F.leadingCoeff : ℝ) / 2 ^ shiftedTwoAdicOrder F by positivity)
    rw [hL]
    linarith
  -- the constant `C_F = d log 2 + 2 log z + (1/d) log V_F ≤ 3d + 2u`
  obtain ⟨CF, hCF⟩ : ∃ CF : ℝ, CF = F.natDegree * log 2 + 2 * L +
      log (∏ i, ∏ j ∈ univ.filter (fun j => i < j), (α i - α j) ^ 2) / F.natDegree :=
    ⟨_, rfl⟩
  have hCFle : CF ≤ 3 * (F.natDegree : ℝ) + 2 * (F.leadingCoeff : ℝ) := by
    have hlogV := log_prod_sq_sub_le α hαI
    have hdiv : log (∏ i, ∏ j ∈ univ.filter (fun j => i < j), (α i - α j) ^ 2) /
        F.natDegree ≤ F.natDegree * log 4 := by
      rw [div_le_iff₀ hdR]
      nlinarith
    have hd2 : (F.natDegree : ℝ) * log 2 ≤ F.natDegree := by nlinarith
    have hd4 : (F.natDegree : ℝ) * log 4 ≤ 2 * F.natDegree := by rw [h4]; nlinarith
    rw [hCF]
    linarith
  intro m r δ hδ hm hcr hdvd
  obtain ⟨⟨hm1, hm2⟩, hm3, hm4⟩ : (logSqrtThreshold (⌈42 / η⌉₊ + 1) ≤ m ∧
      ⌈(3 * d + 2 * u : ℚ) / η⌉₊ + 1 ≤ m) ∧ 4 ≤ m ∧ d ≤ m := by
    rw [fixedFactorThreshold_eq] at hm
    simp only [max_le_iff] at hm
    exact hm
  have hm4' : F.natDegree ≤ m := by omega
  have hk : 42 / ηr + 1 ≤ ((⌈42 / η⌉₊ + 1 : ℕ) : ℝ) := by
    have h := rat_cast_le_ceil_add_one (42 / η)
    rw [hηr]
    push_cast at h ⊢
    linarith
  have hup := symmetric_upper_of_logSqrtThreshold_le hD hη0 hk
  have hηm : CF < ηr * m := by
    have h := rat_cast_le_ceil_add_one ((3 * d + 2 * u : ℚ) / η)
    have h2 : ((⌈(3 * d + 2 * u : ℚ) / η⌉₊ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm2
    have hdu : (3 * (F.natDegree : ℝ) + 2 * (F.leadingCoeff : ℝ)) / ηr < m := by
      rw [hdF, huF, hηr]
      push_cast at h h2 ⊢
      linarith
    rw [div_lt_iff₀ hη0] at hdu
    linarith
  have hr2 : 2 * r ≤ m := by
    have : (2 : ℝ) * r ≤ m := le_trans (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg r)) hcr
    exact_mod_cast this
  have hdvd' : F.map (Int.castRingHom ℚ) ∣
      derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ := by
    rw [reducedDerivative_eq_C_mul_reducedGegenbauer m r δ hδ]
    exact dvd_mul_of_dvd_right hdvd _
  obtain ⟨-, hcmp⟩ := fixedFactor_resultant_comparison hZ hδ (max_le hr2 hm3) hFprim hFlc
    rfl (by omega) hm4' hdvd' hα hαF
  rw [← hL] at hcmp
  have hupm := hup m r δ hδ hr2 hm1
  have hG0 : 0 ≤ β - 1 - 2 * ηr := by linarith
  have hrg := mul_asymptoticGapFunction_le_of_le (G := β - 1 - 2 * ηr) (by linarith)
    (by linarith) hG0 hcr
  have hmR : (4 : ℝ) ≤ m := by exact_mod_cast hm3
  have hlogm : 0 ≤ log (m : ℝ) := Real.log_nonneg (by linarith)
  have hid : ((2 * m : ℝ) - F.natDegree) * log 2 +
      ((2 * m : ℝ) - F.natDegree - F.natDegree) / F.natDegree * L =
      m * β - (F.natDegree * log 2 + 2 * L) := by
    have hdne : (F.natDegree : ℝ) ≠ 0 := hdR.ne'
    rw [hβ]; field_simp; ring
  have hmβ : (m : ℝ) * (β - 1 - 2 * ηr) = m * β - m - 2 * ηr * m := by ring
  rw [hmβ] at hrg
  rw [hCF] at hηm
  linarith

/-! ### Corollary 6.4 with an explicit absolute threshold -/

/-- The explicit margin of Corollary 6.4: `2(log 9 - 1) - g(2) ≥ 1/5`
(`2(log 9 - 1) - g(2) = log 9 - 2 + log(3^5 2^16 / 5^10)` and `log x ≥ 1 - 1/x`). -/
theorem margin_asymptoticGapFunction_two_ge :
    (1 / 5 : ℝ) ≤ 2 * (log 9 - 1) - asymptoticGapFunction 2 := by
  have hg : asymptoticGapFunction 2 = 10 * log (5 / 2) - 6 * log 2 - 3 * log 3 := by
    rw [asymptoticGapFunction_eq]; norm_num
  have h52 : log (5 / 2) = log 5 - log 2 := Real.log_div (by norm_num) (by norm_num)
  have hsmall : log ((3 : ℝ) ^ 5 * 2 ^ 16 / 5 ^ 10) = 5 * log 3 + 16 * log 2 - 10 * log 5 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast; ring
  have hlow := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 3 ^ 5 * 2 ^ 16 / 5 ^ 10 by
    norm_num)
  have hnum : (1 / 5 : ℝ) ≤ 1 - ((3 : ℝ) ^ 5 * 2 ^ 16 / 5 ^ 10)⁻¹ := by norm_num
  have h9 : log 9 = 2 * log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h2 : (2 : ℝ) < log 9 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have h := Real.exp_one_lt_d9
    have h0 := Real.exp_pos 1
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith
  rw [hg, h52]
  linarith

/-- The explicit absolute `M₁` of Corollary 6.4: `logSqrtThreshold 841 + 81`
(`= 3 594 641 + 3^841 + 256 · 841⁴ + 81`). -/
def rationalRootsThreshold : ℕ := logSqrtThreshold 841 + 81

theorem rationalRootsThreshold_eq : rationalRootsThreshold = logSqrtThreshold 841 + 81 := (rfl)

/-- **Corollary 6.4, effective form.** For `m ≥ rationalRootsThreshold`
and `0 ≤ r ≤ m/2`, neither `C_{2m}^{r+1/2}` nor `C_{2m+1}^{r+1/2}/x` has a rational root.
Conditional on `JacobiSimpleRealZeros` and `DusartThetaBound`. -/
theorem noRationalRoots_of_rationalRootsThreshold_le (hZ : JacobiSimpleRealZeros) (hD :
    DusartThetaBound) :
    ∀ m r δ : ℕ, rationalRootsThreshold ≤ m → 2 * r ≤ m → δ ≤ 1 → ∀ q : ℚ,
      (reducedGegenbauer m r δ).eval q ≠ 0 := by
  have hgap := margin_asymptoticGapFunction_two_ge
  have h9 : log (9 : ℝ) = 2 * log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h3 := log_three_gt
  have h3u : log (3 : ℝ) ≤ 3 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have hl2 := Real.log_two_gt_d9
  have h32 : log (3 / 2 : ℝ) = log 3 - log 2 := Real.log_div (by norm_num) (by norm_num)
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = 1 / 20 := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; norm_num
  have hη1 : 2 * η ≤ log 9 - 1 - asymptoticGapFunction 2 / 2 := by rw [hη]; linarith
  have hη2 : 2 * η ≤ log 9 - 1 := by rw [hη]; linarith
  have hM₁ := symmetric_upper_of_logSqrtThreshold_le hD hη0 (k := 841)
    (by rw [hη]; norm_num)
  intro m r δ hm hr2 hδ q hq
  have hm1 : logSqrtThreshold 841 ≤ m := by rw [rationalRootsThreshold_eq] at hm; omega
  have hm2 : 81 ≤ m := by rw [rationalRootsThreshold_eq] at hm; omega
  have hm3 : 4 ≤ m := by omega
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
  have hηm : 4 < η * m := by
    have h2 : (81 : ℝ) ≤ m := by exact_mod_cast hm2
    rw [hη]
    linarith
  have hmβ : (m : ℝ) * (log 9 - 1 - 2 * η) = m * log 9 - m - 2 * η * m := by ring
  rw [hmβ, h9] at hrg
  rw [h32] at hmul
  linarith

/-! ### Corollary 6.5 (2) and (3) with explicit thresholds -/

/-- The explicit absolute threshold of Corollary 6.5 (2) (`F = 3x² - 1`, `c = 19/8`,
`η = 1/1200`): `3 · fixedFactorThreshold 2 3 (1/1200) + 3`. -/
def coneModesSqrtThreeThreshold : ℕ := 3 * fixedFactorThreshold 2 3 (1 / 1200) + 3

theorem coneModesSqrtThreeThreshold_eq :
    coneModesSqrtThreeThreshold = 3 * fixedFactorThreshold 2 3 (1 / 1200) + 3 := (rfl)

/-- **Corollary 6.5 (2), effective form** (the cone `x² + y² - 2z² = 0`). For every
`ℓ ≥ coneModesSqrtThreeThreshold`, `r ≤ ℓ` and `P_ℓ^{(r)}(1/√3) = 0` imply `23r > 4(ℓ - 1)`.
Conditional on `JacobiSimpleRealZeros` and `DusartThetaBound`. -/
theorem coneModes_sqrt_three_effective (hZ : JacobiSimpleRealZeros) (hD : DusartThetaBound) :
    ∀ ℓ r : ℕ, coneModesSqrtThreeThreshold ≤ ℓ → r ≤ ℓ →
      aeval (1 / Real.sqrt 3) (derivative^[r] (legendreP ℓ)) = 0 → 4 * (ℓ - 1) < 23 * r := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 1 / Real.sqrt 3 := ⟨_, rfl⟩
  have hs3 : 1 < Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have ha0 : 0 < a := by rw [ha]; positivity
  have ha1 : a < 1 := by rw [ha, div_lt_one (by linarith)]; exact hs3
  have ha2 : a ^ 2 = 1 / 3 := by rw [ha, div_pow, one_pow, Real.sq_sqrt (by norm_num)]
  -- the factor `F = 3x^2 - 1`
  obtain ⟨F, hF⟩ : ∃ F : ℤ[X], F = C 3 * polyX ^ 2 - 1 := ⟨_, rfl⟩
  have hFdeg : F.natDegree = 2 := by rw [hF]; compute_degree!
  have hFlc : F.leadingCoeff = 3 := by
    rw [Polynomial.leadingCoeff, hFdeg, hF, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_one]
    norm_num
  have hc0 : F.coeff 0 = -1 := by
    rw [hF, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_one]; norm_num
  have hFprim : F.IsPrimitive := by
    refine isPrimitive_iff_isUnit_of_C_dvd.mpr fun x hx => isUnit_of_dvd_one ?_
    have := (C_dvd_iff_dvd_coeff _ _).mp hx 0
    rwa [hc0, dvd_neg] at this
  have hFmapR : F.map (Int.castRingHom ℝ) = C 3 * ((polyX - C a) * (polyX - C (-a))) := by
    have hX : (polyX - C a) * (polyX - C (-a)) = polyX ^ 2 - C (a ^ 2) := by
      rw [C_neg, map_pow]; ring
    rw [hX, mul_sub, ← C_mul, ha2, hF]
    norm_num
    exact (map_ofNat C 3).symm
  have hroots_eq : (F.map (Int.castRingHom ℝ)).roots = a ::ₘ {-a} := by
    rw [hFmapR, roots_C_mul _ (by norm_num),
      roots_mul (mul_ne_zero (X_sub_C_ne_zero a) (X_sub_C_ne_zero (-a))), roots_X_sub_C,
      roots_X_sub_C, Multiset.singleton_add]
  have hnd : (F.map (Int.castRingHom ℝ)).roots.Nodup := by
    rw [hroots_eq]
    refine Multiset.nodup_cons.mpr ⟨fun hmem => ?_, Multiset.nodup_singleton _⟩
    rw [Multiset.mem_singleton] at hmem
    linarith
  have hcard : (F.map (Int.castRingHom ℝ)).roots.card = F.natDegree := by
    rw [hroots_eq, Multiset.card_cons, Multiset.card_singleton, hFdeg]
  have hroots : ∀ x ∈ (F.map (Int.castRingHom ℝ)).roots, -1 < x ∧ x < 1 := by
    rw [hroots_eq]
    intro x hx
    rcases Multiset.mem_cons.mp hx with rfl | hx
    · exact ⟨by linarith, ha1⟩
    · rw [Multiset.mem_singleton] at hx
      subst hx
      exact ⟨by linarith, by linarith⟩
  -- `c_F ≤ 1` and `β(F) ≥ log 6`
  have hs1 : shiftedTwoAdicOrder F ≤ 1 := by
    have e1 : F.eval 1 = 2 := by rw [hF]; norm_num
    have h2 := two_pow_dvd_eval_one F
    rw [e1] at h2
    by_contra hs
    push Not at hs
    have h4 : (2 : ℤ) ^ 2 ∣ 2 := (pow_dvd_pow 2 hs).trans h2
    norm_num at h4
  have hβ : log 6 ≤ fixedFactorExponent F := by
    rw [fixedFactorExponent_eq, hFdeg, hFlc]
    have hs : (2 : ℝ) ^ shiftedTwoAdicOrder F ≤ 2 :=
      calc (2 : ℝ) ^ shiftedTwoAdicOrder F ≤ 2 ^ 1 := pow_le_pow_right₀ (by norm_num) hs1
        _ = 2 := pow_one 2
    have hz : (3 / 2 : ℝ) ≤ ((3 : ℤ) : ℝ) / 2 ^ shiftedTwoAdicOrder F := by
      rw [le_div_iff₀ (by positivity)]; push_cast; linarith
    have hlog := Real.log_le_log (by norm_num) hz
    have h6 : log 6 = log 4 + log (3 / 2) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
    have e : (2 : ℝ) / ((2 : ℕ) : ℝ) * log (((3 : ℤ) : ℝ) / 2 ^ shiftedTwoAdicOrder F) =
        log (((3 : ℤ) : ℝ) / 2 ^ shiftedTwoAdicOrder F) := by norm_num
    rw [e]
    linarith
  -- the explicit margin `η = 1/1200`
  have hmargin := margin_asymptoticGapFunction_nineteen_eighths
  have h6 : (1 + 1 / 600 : ℝ) < log 6 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith [Real.log_two_gt_d9, log_three_gt]
  have hgc : asymptoticGapFunction (19 / 8) / (19 / 8) =
      8 / 19 * asymptoticGapFunction (19 / 8) := by ring
  have hη1 : 2 * (((1 / 1200 : ℚ)) : ℝ) ≤
      fixedFactorExponent F - 1 - asymptoticGapFunction (19 / 8) / (19 / 8) := by
    rw [hgc]
    push_cast
    linarith
  have hη2 : 2 * (((1 / 1200 : ℚ)) : ℝ) ≤ fixedFactorExponent F - 1 := by
    push_cast
    linarith
  have hM := not_dvd_reducedGegenbauer_of_fixedFactorThreshold_le hZ hD hFprim hFdeg
    (hFlc.trans (by norm_num : (3 : ℤ) = ((3 : ℕ) : ℤ))) (by norm_num) (by norm_num) hnd hcard
    hroots (c := 19 / 8) (by norm_num) (by norm_num) hη1 hη2
  obtain ⟨M, hMe⟩ : ∃ M, M = fixedFactorThreshold 2 3 (1 / 1200) := ⟨_, rfl⟩
  rw [← hMe] at hM
  -- `F ∣ F_{m,r,δ}` from a zero at `1/√3`
  have hFQ : F.map (Int.castRingHom ℚ) = C 3 * (polyX ^ 2 - C (1 / 3 : ℚ)) := by
    rw [hF, mul_sub, ← C_mul]
    norm_num
    exact (map_ofNat C 3).symm
  have hpa : aeval a (polyX ^ 2 - C (1 / 3 : ℚ)) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, ha2, eq_ratCast]
    norm_num
  have hmin := minpoly.eq_of_irreducible_of_monic irreducible_X_sq_sub_one_third hpa
    (monic_X_pow_sub_C _ two_ne_zero)
  intro ℓ r hL hr h
  rw [coneModesSqrtThreeThreshold_eq, ← hMe] at hL
  rw [← ha] at h
  by_contra hcon
  push Not at hcon
  obtain ⟨m, δ, hδ, rfl⟩ : ∃ m δ : ℕ, δ ≤ 1 ∧ ℓ = 2 * m + δ + r :=
    ⟨(ℓ - r) / 2, (ℓ - r) % 2, by omega, by omega⟩
  have h19 : 19 * r ≤ 8 * m := by omega
  have hmM : M ≤ m := by omega
  have hcr : (19 / 8 : ℝ) * r ≤ m := by
    have : ((19 * r : ℕ) : ℝ) ≤ ((8 * m : ℕ) : ℝ) := by exact_mod_cast h19
    push_cast at this
    linarith
  have hR := aeval_reducedGegenbauer_eq_zero hδ ha0.ne' h
  have hdvd0 : polyX ^ 2 - C (1 / 3 : ℚ) ∣ reducedGegenbauer m r δ := by
    rw [hmin]; exact minpoly.dvd ℚ a hR
  apply hM m r δ hδ hmM hcr
  rw [hFQ]
  exact (isUnit_C.mpr (IsUnit.mk0 _ (by norm_num))).mul_left_dvd.mpr hdvd0

/-- The explicit absolute threshold of Corollary 6.5 (3): `3 · rationalRootsThreshold + 3`. -/
def coneModesRationalThreshold : ℕ := 3 * rationalRootsThreshold + 3

theorem coneModesRationalThreshold_eq :
    coneModesRationalThreshold = 3 * rationalRootsThreshold + 3 := (rfl)

/-- **Corollary 6.5 (3), effective form.** For nonzero rational `α ∈ (-1,1)`,
`ℓ ≥ coneModesRationalThreshold`, `r ≤ ℓ` and `P_ℓ^{(r)}(α) = 0` imply `5r > ℓ - 1`. -/
theorem coneModes_rational_effective (hZ : JacobiSimpleRealZeros) (hD : DusartThetaBound) :
    ∀ α : ℚ, α ≠ 0 → |α| < 1 → ∀ ℓ r : ℕ, coneModesRationalThreshold ≤ ℓ → r ≤ ℓ →
      (derivative^[r] (legendreP ℓ)).eval α = 0 → ℓ - 1 < 5 * r := by
  have hM₁ := noRationalRoots_of_rationalRootsThreshold_le hZ hD
  obtain ⟨M₁, hM₁e⟩ : ∃ M₁, M₁ = rationalRootsThreshold := ⟨_, rfl⟩
  rw [← hM₁e] at hM₁
  intro α hα0 _ ℓ r hL hr h
  rw [coneModesRationalThreshold_eq, ← hM₁e] at hL
  by_contra hcon
  push Not at hcon
  obtain ⟨m, δ, hδ, rfl⟩ : ∃ m δ : ℕ, δ ≤ 1 ∧ ℓ = 2 * m + δ + r :=
    ⟨(ℓ - r) / 2, (ℓ - r) % 2, by omega, by omega⟩
  exact hM₁ m r δ (by omega) (by omega) hδ α (eval_reducedGegenbauer_eq_zero hδ hα0 h)

end ArithmeticOfJacobiPolynomials
