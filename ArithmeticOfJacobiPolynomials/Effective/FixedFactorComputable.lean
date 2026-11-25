/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Effective.FixedFactorThresholds

/-!
# Proposition 6.3: the threshold as a computable function of `(F, c)`

Proposition 6.3 asserts: "For rational `c`, the threshold is
effective in `F, c`". `not_dvd_reducedGegenbauer_of_fixedFactorThreshold_le` gives the explicit
threshold `fixedFactorThreshold d u η` for a supplied positive rational margin `η` with
`2η ≤ β(F) - 1 - g(c)/c` and `2η ≤ β(F) - 1`. Here `η` is computed from `F` and `c`.

* `shiftedCoeff F j = 2^j ∑_i a_i binom(i,j)` is `[X^j] F(2X+1)`
  (`coeff_comp_two_mul_X_add_one`), and `shiftedTwoAdicMin F`, the minimum of
  `v_2(shiftedCoeff F j)` over the finitely many `j ≤ d` with `shiftedCoeff F j ≠ 0`, is a
  computable form of `c_F = shiftedTwoAdicOrder F` (`shiftedTwoAdicMin_eq`).
* `fixedFactorRatio F = u / 2^{c_F}` is the rational `z` of the proof, so
  `β(F) = log 4 + (2/d) log z` needs no root approximation.
* `fixedFactorMarginLower F c n` is a rational lower bound for both `β(F) - 1 - g(c)/c` and
  `β(F) - 1`, built from the rational bounds `logLower`, `logUpper` of
  `ArithmeticOfJacobiPolynomials.Effective.SymmetricThresholds` (`fixedFactorMarginLower_le`).
  Under (6.3) it is
  positive for large `n` (`exists_fixedFactorMarginLower_pos`).
* `fixedFactorThresholdOfRat F c` is `fixedFactorThreshold d u η` with `η` one quarter of the
  first positive `fixedFactorMarginLower F c n` (found by `Nat.find`), and
  `not_dvd_reducedGegenbauer_of_fixedFactorThresholdOfRat_le` is Proposition 6.3 beyond it.

The conclusion is conditional on the proved `intervalVandermondeBound` (Lemma 2.5),
`JacobiSimpleRealZeros` ([DLMF, §18.2(vi)]) and `DusartThetaBound` ([Dusart10, Theorem 5.2]).
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset Real

/-! ### `c_F` as a finite minimum -/

/-- `[X^j] F(2X+1) = 2^j ∑_{i ≤ d} a_i binom(i, j)`, computed from the coefficients of `F`. -/
def shiftedCoeff (F : ℤ[X]) (j : ℕ) : ℤ :=
  2 ^ j * ∑ i ∈ range (F.natDegree + 1), F.coeff i * (i.choose j : ℤ)

theorem shiftedCoeff_eq (F : ℤ[X]) (j : ℕ) : shiftedCoeff F j =
    2 ^ j * ∑ i ∈ range (F.natDegree + 1), F.coeff i * (i.choose j : ℤ) := (rfl)

/-- `[X^j] (2X+1)^i = 2^j binom(i, j)`. -/
theorem coeff_two_mul_X_add_one_pow (i j : ℕ) :
    (((2 : ℤ[X]) * polyX + 1) ^ i).coeff j = 2 ^ j * (i.choose j : ℤ) := by
  have h2 : (C (2 : ℤ) : ℤ[X]) = 2 := by simp
  have h : ((2 : ℤ[X]) * polyX + 1) ^ i = ((polyX + C (1 : ℤ)) ^ i).comp (C (2 : ℤ) * polyX) := by
    rw [pow_comp, add_comp, X_comp, C_comp, map_one, h2]
  rw [h, comp_C_mul_X_coeff, coeff_X_add_C_pow, one_pow, one_mul]
  ring

/-- `shiftedCoeff F j` is the coefficient of `X^j` in `F(2X+1)`. -/
theorem coeff_comp_two_mul_X_add_one (F : ℤ[X]) (j : ℕ) :
    (F.comp (2 * polyX + 1)).coeff j = shiftedCoeff F j := by
  rw [comp_eq_sum_left, sum_over_range _ (f := fun e a => C a * ((2 : ℤ[X]) * polyX + 1) ^ e)
    (fun n => by simp), finsetSum_coeff, shiftedCoeff_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [coeff_C_mul, coeff_two_mul_X_add_one_pow]
  ring

theorem shiftedCoeff_eq_zero_of_lt {F : ℤ[X]} {j : ℕ} (hj : F.natDegree < j) :
    shiftedCoeff F j = 0 := by
  rw [shiftedCoeff_eq, Finset.sum_eq_zero, mul_zero]
  intro i hi
  rw [mem_range] at hi
  rw [Nat.choose_eq_zero_of_lt (show i < j by omega), Nat.cast_zero, mul_zero]

/-- The indices `j ≤ d` with `shiftedCoeff F j ≠ 0`. -/
def shiftedSupport (F : ℤ[X]) : Finset ℕ :=
  (range (F.natDegree + 1)).filter fun j => shiftedCoeff F j ≠ 0

theorem shiftedSupport_def (F : ℤ[X]) : shiftedSupport F =
    (range (F.natDegree + 1)).filter fun j => shiftedCoeff F j ≠ 0 := (rfl)

/-- `shiftedSupport F` is the support of `F(2X+1)`. -/
theorem shiftedSupport_eq_support (F : ℤ[X]) :
    shiftedSupport F = (F.comp (2 * polyX + 1)).support := by
  ext j
  rw [shiftedSupport_def, mem_filter, mem_range, mem_support_iff, coeff_comp_two_mul_X_add_one]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    by_contra hj
    exact h (shiftedCoeff_eq_zero_of_lt (by omega))

/-- The finite set of the valuations `v_2([X^j] F(2X+1))` of the nonzero coefficients. -/
def shiftedValuations (F : ℤ[X]) : Finset ℕ :=
  (shiftedSupport F).image fun j => padicValInt 2 (shiftedCoeff F j)

theorem shiftedValuations_def (F : ℤ[X]) : shiftedValuations F =
    (shiftedSupport F).image fun j => padicValInt 2 (shiftedCoeff F j) := (rfl)

/-- The computable `c_F`: the minimum of `shiftedValuations F` (`0` if it is empty). -/
def shiftedTwoAdicMin (F : ℤ[X]) : ℕ :=
  if h : (shiftedValuations F).Nonempty then (shiftedValuations F).min' h else 0

theorem shiftedTwoAdicMin_def (F : ℤ[X]) : shiftedTwoAdicMin F =
    if h : (shiftedValuations F).Nonempty then (shiftedValuations F).min' h else 0 := (rfl)

/-- The infimum of a finite set of naturals is its minimum (`0` for the empty set). -/
theorem sInf_coe_finset_nat (T : Finset ℕ) :
    sInf (T : Set ℕ) = if h : T.Nonempty then T.min' h else 0 := by
  split_ifs with h
  · have hmem : sInf (T : Set ℕ) ∈ T :=
      Finset.mem_coe.mp (Nat.sInf_mem (Finset.coe_nonempty.mpr h))
    exact le_antisymm (Nat.sInf_le (Finset.mem_coe.mpr (T.min'_mem h))) (T.min'_le _ hmem)
  · rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.coe_empty, Nat.sInf_empty]

/-- The computable `shiftedTwoAdicMin F` equals `c_F = shiftedTwoAdicOrder F`. -/
theorem shiftedTwoAdicMin_eq (F : ℤ[X]) : shiftedTwoAdicMin F = shiftedTwoAdicOrder F := by
  have hf : (fun j => padicValInt 2 ((F.comp (2 * polyX + 1)).coeff j)) =
      fun j => padicValInt 2 (shiftedCoeff F j) := by
    funext j
    rw [coeff_comp_two_mul_X_add_one]
  rw [shiftedTwoAdicOrder_eq, hf, ← shiftedSupport_eq_support, ← Finset.coe_image,
    sInf_coe_finset_nat, shiftedTwoAdicMin_def, shiftedValuations_def]

/-! ### The rational `z = u / 2^{c_F}` -/

/-- `z = u / 2^{c_F}` as a rational, computed from `F`. -/
def fixedFactorRatio (F : ℤ[X]) : ℚ := (F.leadingCoeff : ℚ) / 2 ^ shiftedTwoAdicMin F

theorem fixedFactorRatio_eq (F : ℤ[X]) :
    fixedFactorRatio F = (F.leadingCoeff : ℚ) / 2 ^ shiftedTwoAdicMin F := (rfl)

theorem cast_fixedFactorRatio (F : ℤ[X]) :
    ((fixedFactorRatio F : ℚ) : ℝ) = (F.leadingCoeff : ℝ) / 2 ^ shiftedTwoAdicOrder F := by
  rw [fixedFactorRatio_eq, shiftedTwoAdicMin_eq, Rat.cast_div, Rat.cast_pow, Rat.cast_intCast,
    Rat.cast_ofNat]

theorem fixedFactorRatio_pos {F : ℤ[X]} (hFlc : 0 < F.leadingCoeff) : 0 < fixedFactorRatio F := by
  rw [fixedFactorRatio_eq]
  have : (0 : ℚ) < F.leadingCoeff := by exact_mod_cast hFlc
  exact div_pos this (by positivity)

/-! ### Rational lower bounds of logarithms of positive rationals -/

/-- A rational lower bound of `log x` for rational `x > 0`: `L_n(x)` for `x ≥ 1` and
`-U_n(1/x)` for `x < 1`. -/
def logLowerPos (x : ℚ) (n : ℕ) : ℚ := if 1 ≤ x then logLower x n else -logUpper x⁻¹ n

theorem logLowerPos_eq (x : ℚ) (n : ℕ) :
    logLowerPos x n = if 1 ≤ x then logLower x n else -logUpper x⁻¹ n := (rfl)

theorem logLowerPos_le_log {x : ℚ} (hx : 0 < x) (n : ℕ) : (logLowerPos x n : ℝ) ≤ log x := by
  rw [logLowerPos_eq]
  split_ifs with h
  · exact logLower_le_log h n
  · have h1 : 1 ≤ x⁻¹ := (one_le_inv₀ hx).mpr (not_le.mp h).le
    have hU := log_le_logUpper h1 n
    rw [Rat.cast_inv, Real.log_inv] at hU
    push_cast
    linarith

theorem eventually_log_sub_lt_logLowerPos {x : ℚ} (hx : 0 < x) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, log (x : ℝ) - ε < (logLowerPos x n : ℝ) := by
  by_cases h : 1 ≤ x
  · filter_upwards [eventually_logUpper_sub_logLower_lt h hε] with n hn
    have hU := log_le_logUpper h n
    rw [logLowerPos_eq, ite_eq_left h]
    linarith
  · have h1 : 1 ≤ x⁻¹ := (one_le_inv₀ hx).mpr (not_le.mp h).le
    filter_upwards [eventually_logUpper_sub_logLower_lt h1 hε] with n hn
    have hL := logLower_le_log h1 n
    rw [Rat.cast_inv, Real.log_inv] at hL
    rw [logLowerPos_eq, ite_eq_right h]
    push_cast
    linarith

/-- `asymptoticMarginLower c n` converges to `log 4 - 1 - g(c)/c` from below. -/
theorem eventually_asymptoticMarginLower_gt {c : ℚ} (hc : 2 ≤ c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      log 4 - 1 - asymptoticGapFunction c / c - ε < (asymptoticMarginLower c n : ℝ) := by
  have hc' : (2 : ℝ) ≤ c := by exact_mod_cast hc
  have hc0 : (0 : ℝ) < c := by linarith
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ε / 12 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have e4 : (1 : ℚ) ≤ 4 := by norm_num
  have ec2 : (1 : ℚ) ≤ c + 1 / 2 := by linarith
  have ec : (1 : ℚ) ≤ c := by linarith
  have ec1 : (1 : ℚ) ≤ c + 1 := by linarith
  filter_upwards [eventually_logUpper_sub_logLower_lt e4 hδ0,
    eventually_logUpper_sub_logLower_lt ec2 hδ0, eventually_logUpper_sub_logLower_lt ec hδ0,
    eventually_logUpper_sub_logLower_lt ec1 hδ0] with n g4 gU gc g1
  have u4 := log_le_logUpper e4 n
  have lU := logLower_le_log ec2 n
  have uc := log_le_logUpper ec n
  have u1 := log_le_logUpper ec1 n
  push_cast at u4 lU u1
  rw [asymptoticMarginLower_eq]
  push_cast
  have p1 := mul_le_mul_of_nonneg_left (show ((logUpper (c + 1 / 2) n : ℚ) : ℝ) ≤
    log ((c : ℝ) + 1 / 2) + δ by linarith) (show (0 : ℝ) ≤ 4 * c + 2 by linarith)
  have p2 := mul_le_mul_of_nonneg_left (show log (c : ℝ) ≤
    ((logLower c n : ℚ) : ℝ) + δ by linarith) (show (0 : ℝ) ≤ 3 * c by linarith)
  have p3 := mul_le_mul_of_nonneg_left (show log ((c : ℝ) + 1) ≤
    ((logLower (c + 1) n : ℚ) : ℝ) + δ by linarith) (show (0 : ℝ) ≤ c + 1 by linarith)
  have hg := asymptoticGapFunction_eq (c : ℝ)
  have hG : (4 * (c : ℝ) + 2) * ((logUpper (c + 1 / 2) n : ℚ) : ℝ) -
      3 * (c : ℝ) * ((logLower c n : ℚ) : ℝ) - ((c : ℝ) + 1) * ((logLower (c + 1) n : ℚ) : ℝ) ≤
      asymptoticGapFunction c + (8 * c + 3) * δ := by
    linarith
  have hdiv := div_le_div_of_nonneg_right hG hc0.le
  rw [add_div] at hdiv
  have hδc : (8 * (c : ℝ) + 3) * δ / c ≤ 10 * δ := by
    rw [div_le_iff₀ hc0]
    nlinarith
  have hε' : ε = 12 * δ := by rw [hδ]; ring
  linarith

/-! ### The rational margin of Proposition 6.3 -/

/-- The rational lower bound of the two margins `β(F) - 1 - g(c)/c` and `β(F) - 1`:
`min (M_n(c) + (2/d) λ_n(z)) (L_n(4) - 1 + (2/d) λ_n(z))`, with `M_n = asymptoticMarginLower`,
`λ_n = logLowerPos` and `z = fixedFactorRatio F`. -/
def fixedFactorMarginLower (F : ℤ[X]) (c : ℚ) (n : ℕ) : ℚ :=
  min (asymptoticMarginLower c n + 2 / F.natDegree * logLowerPos (fixedFactorRatio F) n)
    (logLower 4 n - 1 + 2 / F.natDegree * logLowerPos (fixedFactorRatio F) n)

theorem fixedFactorMarginLower_eq (F : ℤ[X]) (c : ℚ) (n : ℕ) : fixedFactorMarginLower F c n =
    min (asymptoticMarginLower c n + 2 / F.natDegree * logLowerPos (fixedFactorRatio F) n)
      (logLower 4 n - 1 + 2 / F.natDegree * logLowerPos (fixedFactorRatio F) n) := (rfl)

theorem fixedFactorMarginLower_le {F : ℤ[X]} {c : ℚ} (hc : 2 ≤ c) (hFlc : 0 < F.leadingCoeff)
    (n : ℕ) :
    (fixedFactorMarginLower F c n : ℝ) ≤
        fixedFactorExponent F - 1 - asymptoticGapFunction c / c ∧
      (fixedFactorMarginLower F c n : ℝ) ≤ fixedFactorExponent F - 1 := by
  have hz := logLowerPos_le_log (fixedFactorRatio_pos hFlc) n
  rw [cast_fixedFactorRatio] at hz
  have hk : (0 : ℝ) ≤ 2 / (F.natDegree : ℝ) := by positivity
  have hkz := mul_le_mul_of_nonneg_left hz hk
  have hA := asymptoticMarginLower_le hc n
  have h4 := logLower_le_log (x := 4) (by norm_num) n
  push_cast at h4
  rw [fixedFactorMarginLower_eq, Rat.cast_min]
  push_cast
  rw [fixedFactorExponent_eq]
  constructor
  · exact (min_le_left _ _).trans (by linarith)
  · exact (min_le_right _ _).trans (by linarith)

/-- Under (6.3), some `fixedFactorMarginLower F c n` is positive. -/
theorem exists_fixedFactorMarginLower_pos {F : ℤ[X]} {c : ℚ} (hc : 2 ≤ c)
    (hFlc : 0 < F.leadingCoeff) (hβ : 1 < fixedFactorExponent F)
    (hgap : asymptoticGapFunction c < c * (fixedFactorExponent F - 1)) :
    ∃ n, 0 < fixedFactorMarginLower F c n := by
  have hc' : (2 : ℝ) ≤ c := by exact_mod_cast hc
  have hc0 : (0 : ℝ) < c := by linarith
  have hM1 : 0 < fixedFactorExponent F - 1 - asymptoticGapFunction c / c := by
    have : asymptoticGapFunction c / c < fixedFactorExponent F - 1 := by
      rw [div_lt_iff₀ hc0]; linarith
    linarith
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = min (fixedFactorExponent F - 1 - asymptoticGapFunction c / c)
      (fixedFactorExponent F - 1) / 4 := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; exact div_pos (lt_min hM1 (by linarith)) (by norm_num)
  have hε1 : 4 * ε ≤ fixedFactorExponent F - 1 - asymptoticGapFunction c / c := by
    rw [hε]
    linarith [min_le_left (fixedFactorExponent F - 1 - asymptoticGapFunction c / c)
      (fixedFactorExponent F - 1)]
  have hε2 : 4 * ε ≤ fixedFactorExponent F - 1 := by
    rw [hε]
    linarith [min_le_right (fixedFactorExponent F - 1 - asymptoticGapFunction c / c)
      (fixedFactorExponent F - 1)]
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = 2 / (F.natDegree : ℝ) := ⟨_, rfl⟩
  have hk0 : 0 ≤ k := by rw [hk]; positivity
  have hεk : 0 < ε / (k + 1) := div_pos hε0 (by linarith)
  obtain ⟨n, hA, h4, hz⟩ := ((eventually_asymptoticMarginLower_gt hc hε0).and
    ((eventually_logUpper_sub_logLower_lt (x := 4) (by norm_num) hε0).and
      (eventually_log_sub_lt_logLowerPos (fixedFactorRatio_pos hFlc) hεk))).exists
  refine ⟨n, ?_⟩
  have u4 := log_le_logUpper (x := 4) (by norm_num) n
  push_cast at u4
  rw [cast_fixedFactorRatio] at hz
  have hkz := mul_le_mul_of_nonneg_left hz.le hk0
  have hkε : k * (ε / (k + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith
  have hβe : fixedFactorExponent F =
      log 4 + k * log ((F.leadingCoeff : ℝ) / 2 ^ shiftedTwoAdicOrder F) := by
    rw [hk]; exact fixedFactorExponent_eq F
  have hkz' : k * log ((F.leadingCoeff : ℝ) / 2 ^ shiftedTwoAdicOrder F) - ε ≤
      k * ((logLowerPos (fixedFactorRatio F) n : ℚ) : ℝ) := by
    have e : k * (log ((F.leadingCoeff : ℝ) / 2 ^ shiftedTwoAdicOrder F) - ε / (k + 1)) =
        k * log ((F.leadingCoeff : ℝ) / 2 ^ shiftedTwoAdicOrder F) - k * (ε / (k + 1)) := by
      ring
    linarith
  have h : (0 : ℝ) < (fixedFactorMarginLower F c n : ℝ) := by
    rw [fixedFactorMarginLower_eq, Rat.cast_min]
    push_cast
    rw [← hk]
    exact lt_min (by linarith) (by linarith)
  exact_mod_cast h

/-! ### The computable threshold -/

/-- The rational margin `η` of Proposition 6.3 computed from `(F, c)`: one quarter of the first
positive `fixedFactorMarginLower F c n` (found by `Nat.find`, a terminating search over `n`). -/
def fixedFactorMarginOfRat (F : ℤ[X]) (c : ℚ) (hc : 2 ≤ c) (hFlc : 0 < F.leadingCoeff)
    (hβ : 1 < fixedFactorExponent F)
    (hgap : asymptoticGapFunction c < c * (fixedFactorExponent F - 1)) : ℚ :=
  fixedFactorMarginLower F c (Nat.find (exists_fixedFactorMarginLower_pos hc hFlc hβ hgap)) / 4

theorem fixedFactorMarginOfRat_eq (F : ℤ[X]) (c : ℚ) (hc : 2 ≤ c) (hFlc : 0 < F.leadingCoeff)
    (hβ : 1 < fixedFactorExponent F)
    (hgap : asymptoticGapFunction c < c * (fixedFactorExponent F - 1)) :
    fixedFactorMarginOfRat F c hc hFlc hβ hgap =
      fixedFactorMarginLower F c (Nat.find (exists_fixedFactorMarginLower_pos hc hFlc hβ hgap)) /
        4 := (rfl)

/-- **The computable threshold of Proposition 6.3 for rational `c`**:
`fixedFactorThreshold d u η` with `d = deg F`, `u = lc F` and `η = fixedFactorMarginOfRat F c`.
The proof arguments only certify termination of the search; the value depends on `F` and `c`
alone. -/
def fixedFactorThresholdOfRat (F : ℤ[X]) (c : ℚ) (hc : 2 ≤ c) (hFlc : 0 < F.leadingCoeff)
    (hβ : 1 < fixedFactorExponent F)
    (hgap : asymptoticGapFunction c < c * (fixedFactorExponent F - 1)) : ℕ :=
  fixedFactorThreshold F.natDegree F.leadingCoeff.toNat
    (fixedFactorMarginOfRat F c hc hFlc hβ hgap)

theorem fixedFactorThresholdOfRat_eq (F : ℤ[X]) (c : ℚ) (hc : 2 ≤ c)
    (hFlc : 0 < F.leadingCoeff) (hβ : 1 < fixedFactorExponent F)
    (hgap : asymptoticGapFunction c < c * (fixedFactorExponent F - 1)) :
    fixedFactorThresholdOfRat F c hc hFlc hβ hgap = fixedFactorThreshold F.natDegree
      F.leadingCoeff.toNat (fixedFactorMarginOfRat F c hc hFlc hβ hgap) := (rfl)

/-- The margin `fixedFactorMarginOfRat F c` satisfies the hypotheses of
`not_dvd_reducedGegenbauer_of_fixedFactorThreshold_le`. -/
theorem fixedFactorMarginOfRat_spec {F : ℤ[X]} {c : ℚ} (hc : 2 ≤ c) (hFlc : 0 < F.leadingCoeff)
    (hβ : 1 < fixedFactorExponent F)
    (hgap : asymptoticGapFunction c < c * (fixedFactorExponent F - 1)) :
    0 < fixedFactorMarginOfRat F c hc hFlc hβ hgap ∧
      2 * (fixedFactorMarginOfRat F c hc hFlc hβ hgap : ℝ) ≤
        fixedFactorExponent F - 1 - asymptoticGapFunction c / c ∧
      2 * (fixedFactorMarginOfRat F c hc hFlc hβ hgap : ℝ) ≤ fixedFactorExponent F - 1 := by
  rw [fixedFactorMarginOfRat_eq]
  have hpos := Nat.find_spec (exists_fixedFactorMarginLower_pos hc hFlc hβ hgap)
  obtain ⟨h1, h2⟩ := fixedFactorMarginLower_le (F := F) hc hFlc
    (Nat.find (exists_fixedFactorMarginLower_pos hc hFlc hβ hgap))
  have hR : (0 : ℝ) < (fixedFactorMarginLower F c
      (Nat.find (exists_fixedFactorMarginLower_pos hc hFlc hβ hgap)) : ℝ) := by
    exact_mod_cast hpos
  refine ⟨div_pos hpos (by norm_num), ?_, ?_⟩
  · push_cast
    linarith
  · push_cast
    linarith

/-- **Proposition 6.3, with the threshold computed from `(F, c)`.** Let
`F ∈ ℤ[x]` be primitive of degree `d ≥ 1` with leading coefficient `u > 0`, `d` distinct roots
in `(-1,1)` and `F(0) ≠ 0`, and let `c ≥ 2` be rational with `c (β(F) - 1) > g(c)` (6.3). For
every `m ≥ fixedFactorThresholdOfRat F c`, `δ ∈ {0,1}` and `r` with `c r ≤ m`,
`F ∤ C_{2m+δ}^{r+1/2}(x)/x^δ`. Conditional on
`JacobiSimpleRealZeros` and `DusartThetaBound`. -/
theorem not_dvd_reducedGegenbauer_of_fixedFactorThresholdOfRat_le (hZ : JacobiSimpleRealZeros) (hD :
    DusartThetaBound)
    {F : ℤ[X]} (hFprim : F.IsPrimitive) (hd : 1 ≤ F.natDegree) (hFlc : 0 < F.leadingCoeff)
    (hnd : (F.map (Int.castRingHom ℝ)).roots.Nodup)
    (hcard : (F.map (Int.castRingHom ℝ)).roots.card = F.natDegree)
    (hroots : ∀ x ∈ (F.map (Int.castRingHom ℝ)).roots, -1 < x ∧ x < 1) (hF0 : F.eval 0 ≠ 0)
    {c : ℚ} (hc : 2 ≤ c) (hgap : asymptoticGapFunction c < c * (fixedFactorExponent F - 1)) :
    ∀ m r δ : ℕ, δ ≤ 1 →
      fixedFactorThresholdOfRat F c hc hFlc
          (one_lt_fixedFactorExponent hFprim hd hFlc hcard hroots hF0) hgap ≤ m →
        (c : ℝ) * r ≤ m → ¬ F.map (Int.castRingHom ℚ) ∣ reducedGegenbauer m r δ := by
  have hβ := one_lt_fixedFactorExponent hFprim hd hFlc hcard hroots hF0
  obtain ⟨hη, hη1, hη2⟩ := fixedFactorMarginOfRat_spec hc hFlc hβ hgap
  have hc' : (2 : ℝ) ≤ c := by exact_mod_cast hc
  have key := not_dvd_reducedGegenbauer_of_fixedFactorThreshold_le hZ hD hFprim rfl
    (Int.toNat_of_nonneg hFlc.le).symm hd (by omega) hnd hcard hroots hc' hη hη1 hη2
  intro m r δ hδ hm hcr
  rw [fixedFactorThresholdOfRat_eq] at hm
  exact key m r δ hδ hm hcr

end ArithmeticOfJacobiPolynomials
