/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.SymmetricParameters
public import ArithmeticOfJacobiPolynomials.Analysis.AsymmetricAsymptotics

/-!
# Explicit computable thresholds for Lemma 3.5, Proposition 3.6 and Theorem 1.4

Section 3.2 of the manuscript ("Uniform linear ranges") asserts effectivity three times:
Lemma 3.5 ("The error has an effective bound independent of `r` and `δ`"),
Proposition 3.6 ("For rational `c`, the threshold is effectively computable", with
"for rational `c` the strict margin can be bounded below by rational approximation", §3.2)
and Theorem 1.4 ("an effective absolute integer `M₀`").

`log_le_sqrt_of_logSqrtThreshold_le` gives an explicit threshold for the inequalities in
`eventually_log_le_sqrt`. For `1 ≤ κ ≤ k`, every
`m ≥ logSqrtThreshold k = 3 594 641 + 3^k + 256 k⁴` satisfies `κ ≤ log m`, `κ log m ≤ √m` and
`κ ≤ √m` (from `log 3 > 1` and `log x ≤ 4 x^{1/4}`). Consequently:

* `symmetric_uniform_asymptotics_of_logSqrtThreshold_le`, `uniformAsymptoticsThreshold`:
  Lemma 3.5 with the explicit computable threshold `logSqrtThreshold (⌈42/η⌉₊ + 1)` for
  rational `η > 0`;
* `irreducible_reducedGegenbauer_of_asymptoticRangeThreshold_le`: Proposition 3.6 with the
  explicit computable threshold `asymptoticRangeThreshold η` attached to a rational lower bound
  `η > 0` of the margin `log 4 - 1 - g(c)/c` (such `η` always exists,
  `exists_rat_margin_asymptoticGapFunction`);
* `symmetricAbsoluteThreshold = logSqrtThreshold 69280`: the explicit `M₀` of Theorem 1.4
  (`irreducible_reducedGegenbauer_of_symmetricAbsoluteThreshold_le`), from the rational margin
  `8 (log 4 - 1) - g(8) > 97/10000`.

The cited hypotheses are listed below.
`JacobiSimpleRealZeros` ([DLMF, §18.2(vi)]) and
`DusartThetaBound` ([Dusart10, Theorem 5.2]).
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Real Finset

/-! ### An explicit threshold for `eventually_log_le_sqrt` -/

/-- `3 594 641 + 3^k + 256 k⁴`. -/
def logSqrtThreshold (k : ℕ) : ℕ := 3594641 + 3 ^ k + 256 * k ^ 4

theorem logSqrtThreshold_eq (k : ℕ) : logSqrtThreshold k = 3594641 + 3 ^ k + 256 * k ^ 4 := (rfl)

/-- **Explicit form of `eventually_log_le_sqrt`.** If `1 ≤ κ ≤ k` and
`m ≥ 3 594 641 + 3^k + 256 k⁴`, then `3 594 641 ≤ m`, `κ ≤ log m`, `κ log m ≤ √m` and
`κ ≤ √m`. -/
theorem log_le_sqrt_of_logSqrtThreshold_le {κ : ℝ} {k m : ℕ} (hκ : 1 ≤ κ) (hκk : κ ≤ k)
    (hm : logSqrtThreshold k ≤ m) :
    3594641 ≤ m ∧ κ ≤ log (m : ℝ) ∧ κ * log (m : ℝ) ≤ √(m : ℝ) ∧ κ ≤ √(m : ℝ) := by
  rw [logSqrtThreshold_eq] at hm
  obtain ⟨A, hA⟩ : ∃ A : ℕ, A = 3 ^ k := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℕ, B = k ^ 4 := ⟨_, rfl⟩
  rw [← hA, ← hB] at hm
  have h3 : 3 ^ k ≤ m := by rw [← hA]; omega
  have h256 : 256 * k ^ 4 ≤ m := by rw [← hB]; omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hk1 : (1 : ℝ) ≤ k := hκ.trans hκk
  have hlog3 := log_three_gt
  have hlogm : (k : ℝ) ≤ log (m : ℝ) := by
    have h : ((3 ^ k : ℕ) : ℝ) ≤ m := by exact_mod_cast h3
    have h' := Real.log_le_log (by positivity) h
    push_cast at h'
    rw [Real.log_pow] at h'
    nlinarith
  have hsqm : 16 * (k : ℝ) ^ 2 ≤ √(m : ℝ) := by
    rw [Real.le_sqrt (by positivity) hm0.le]
    have h : ((256 * k ^ 4 : ℕ) : ℝ) ≤ m := by exact_mod_cast h256
    push_cast at h
    nlinarith
  have hsqsq : 4 * (k : ℝ) ≤ √(√(m : ℝ)) := by
    rw [Real.le_sqrt (by positivity) (Real.sqrt_nonneg _)]
    nlinarith
  have hlogsq : log (m : ℝ) ≤ 4 * √(√(m : ℝ)) := by
    have h := log_le_two_mul_sqrt (Real.sqrt_nonneg (m : ℝ))
    rw [Real.log_sqrt hm0.le] at h
    linarith
  have hsq2 : √(√(m : ℝ)) * √(√(m : ℝ)) = √(m : ℝ) :=
    Real.mul_self_sqrt (Real.sqrt_nonneg _)
  have hlog0 : 0 ≤ log (m : ℝ) := by linarith
  refine ⟨by omega, by linarith, ?_, by nlinarith⟩
  calc κ * log (m : ℝ) ≤ k * (4 * √(√(m : ℝ))) := mul_le_mul hκk hlogsq hlog0 hk0
    _ = (4 * k) * √(√(m : ℝ)) := by ring
    _ ≤ √(√(m : ℝ)) * √(√(m : ℝ)) := mul_le_mul_of_nonneg_right hsqsq (Real.sqrt_nonneg _)
    _ = √(m : ℝ) := hsq2

/-- `η ≤ ⌈η⌉₊` for rational `η`, cast to `ℝ`. -/
theorem rat_cast_le_ceil_add_one (q : ℚ) : (q : ℝ) + 1 ≤ ((⌈q⌉₊ + 1 : ℕ) : ℝ) := by
  have h1 : q ≤ (⌈q⌉₊ : ℚ) := Nat.le_ceil q
  have h2 : (q : ℝ) ≤ ((⌈q⌉₊ : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast
  linarith

/-! ### Lemma 3.5 with an explicit threshold -/

/-- **Lemma 3.5, explicit error.** If `η > 0`,
`42/η + 1 ≤ k` and `m ≥ logSqrtThreshold k`, then for all `1 ≤ r`, `2r ≤ m`, `δ ≤ 1`:
`|Ψ_m(S) + log K + log A_{≤m} - (m + r g(m/r))| ≤ η m`. -/
theorem symmetric_uniform_asymptotics_of_logSqrtThreshold_le (hD : DusartThetaBound)
    {η : ℝ} (hη : 0 < η) {k : ℕ} (hk : 42 / η + 1 ≤ k) :
    ∀ m r δ : ℕ, δ ≤ 1 → 1 ≤ r → 2 * r ≤ m → logSqrtThreshold k ≤ m →
      |primePowerLogSum m ((2 * (2 * m + δ) + 2 * r + 1 : ℕ) : ℝ) + log ((m + r).choose r : ℝ) +
          log (primeTruncation (symmetricRatio (2 * m + δ) r) m) -
          (m + r * asymptoticGapFunction ((m : ℝ) / r))| ≤ η * m := by
  have hPNT := dusartThetaBound_sum hD
  have hκ : 1 ≤ 42 / η + 1 := by
    have : 0 < 42 / η := by positivity
    linarith
  intro m r δ hδ hr hrm hm
  obtain ⟨hx, hL, hLu, hu⟩ := log_le_sqrt_of_logSqrtThreshold_le hκ hk hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have herr := symmetric_error_le hκ hm0.le hL hLu hu
  have hup := symmetric_uniform_asymptotics_upper_explicit hPNT hδ hr hrm hx
  have hlow := symmetric_uniform_asymptotics_lower_explicit hPNT hδ hr hrm hx
  have hsmall : 42 / (42 / η + 1) * m ≤ η * m := by
    apply mul_le_mul_of_nonneg_right _ hm0.le
    rw [div_le_iff₀ (by positivity)]
    have : η * (42 / η + 1) = 42 + η := by field_simp
    linarith
  have hu1 : 1 ≤ √(m : ℝ) := hκ.trans hu
  have hL0 : 0 ≤ log (m : ℝ) := by linarith
  have h8 : 0 ≤ log (8 * √(m : ℝ)) := Real.log_nonneg (by linarith)
  have huL : 0 ≤ √(m : ℝ) * log (m : ℝ) := by positivity
  rw [abs_le]
  constructor <;> linarith

/-- The explicit computable threshold of Lemma 3.5 for a rational error `η > 0`:
`logSqrtThreshold (⌈42/η⌉₊ + 1)`. -/
def uniformAsymptoticsThreshold (η : ℚ) : ℕ := logSqrtThreshold (⌈42 / η⌉₊ + 1)

theorem uniformAsymptoticsThreshold_eq (η : ℚ) :
    uniformAsymptoticsThreshold η = logSqrtThreshold (⌈42 / η⌉₊ + 1) := (rfl)

/-- **Lemma 3.5, effective.** For rational `η > 0` and all `m ≥ uniformAsymptoticsThreshold η`,
`1 ≤ r`, `2r ≤ m`, `δ ≤ 1`:
`|Ψ_m(S) + log K + log A_{≤m} - (m + r g(m/r))| ≤ η m`. Conditional on [Dusart10, Theorem 5.2]
(`DusartThetaBound`). -/
theorem symmetric_uniform_asymptotics_effective (hD : DusartThetaBound) {η : ℚ} (hη : 0 < η) :
    ∀ m r δ : ℕ, δ ≤ 1 → 1 ≤ r → 2 * r ≤ m → uniformAsymptoticsThreshold η ≤ m →
      |primePowerLogSum m ((2 * (2 * m + δ) + 2 * r + 1 : ℕ) : ℝ) + log ((m + r).choose r : ℝ) +
          log (primeTruncation (symmetricRatio (2 * m + δ) r) m) -
          (m + r * asymptoticGapFunction ((m : ℝ) / r))| ≤ (η : ℝ) * m := by
  have hη' : (0 : ℝ) < η := by exact_mod_cast hη
  have hk : 42 / (η : ℝ) + 1 ≤ ((⌈42 / η⌉₊ + 1 : ℕ) : ℝ) := by
    have h := rat_cast_le_ceil_add_one (42 / η)
    push_cast at h ⊢
    linarith
  exact symmetric_uniform_asymptotics_of_logSqrtThreshold_le hD hη' hk

/-! ### Proposition 3.6 with an explicit threshold -/

/-- **Proposition 3.6, explicit form.** Let `c ≥ 2` and let `η > 0`
satisfy `η ≤ log 4 - 1 - g(c)/c` and `η ≤ log 4 - 1`. If `84/η + 1 ≤ k`, then for every
`m ≥ logSqrtThreshold k`, `δ ∈ {0,1}` and `r` with `c r ≤ m`, `F_{m,r,δ}` is irreducible. -/
theorem irreducible_reducedGegenbauer_of_logSqrtThreshold_le (hZ : JacobiSimpleRealZeros) (hD :
    DusartThetaBound) {c η : ℝ} (hc : 2 ≤ c) (hη0 : 0 < η)
    (hη1 : η ≤ log 4 - 1 - asymptoticGapFunction c / c) (hη2 : η ≤ log 4 - 1) {k : ℕ}
    (hk : 84 / η + 1 ≤ k) :
    ∀ m r δ : ℕ, δ ≤ 1 → logSqrtThreshold k ≤ m → c * r ≤ m →
      Irreducible (reducedGegenbauer m r δ) := by
  have hPNT := dusartThetaBound_sum hD
  have hκ : 1 ≤ 84 / η + 1 := by
    have : 0 < 84 / η := by positivity
    linarith
  intro m r δ hδ hm hcr
  obtain ⟨hx, hL, hLu, hu⟩ := log_le_sqrt_of_logSqrtThreshold_le hκ hk hm
  have hr2 : 2 * r ≤ m := by
    have : (2 : ℝ) * r ≤ m := le_trans (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg r)) hcr
    exact_mod_cast this
  refine irreducible_reducedGegenbauer_of_exact_criterion hZ hδ (max_le hr2 (by omega)) ?_
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have herr := symmetric_error_le hκ hm0.le hL hLu hu
  have hsmall : 42 / (84 / η + 1) * m < η * m := by
    apply mul_lt_mul_of_pos_right _ hm0
    rw [div_lt_iff₀ (by positivity)]
    have : η * (84 / η + 1) = 84 + η := by field_simp
    linarith
  have hL0 : 0 ≤ log (m : ℝ) := by linarith
  have hε0 : 0 ≤ 0.2 / log (m : ℝ) ^ 2 * m := by positivity
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have hΨ := primePowerLogSum_symmetric_le hPNT hδ (r := 0) (by omega) hx
    have hK0 : log (((m + 0).choose 0 : ℕ) : ℝ) = 0 := by simp
    have hA0 : log (primeTruncation (symmetricRatio (2 * m + δ) 0) m) = 0 := by
      rw [symmetricRatio_zero_right, log_primeTruncation_one]
    have hη4 : η * m ≤ (log 4 - 1) * m := mul_le_mul_of_nonneg_right hη2 hm0.le
    rw [hK0, hA0]
    nlinarith
  · have hup := symmetric_uniform_asymptotics_upper_explicit hPNT hδ hr hr2 hx
    have hg := mul_asymptoticGapFunction_le (c := c) (m := m) (r := r) (by linarith)
      (by exact_mod_cast hr) hcr
    have hηm : η * m ≤ (log 4 - 1 - asymptoticGapFunction c / c) * m :=
      mul_le_mul_of_nonneg_right hη1 hm0.le
    nlinarith

theorem one_third_lt_log_four_sub_one : (1 / 3 : ℝ) < log 4 - 1 := by
  have h := Real.log_two_gt_d9
  have : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  linarith

/-- The explicit computable threshold of Proposition 3.6 attached to a rational margin `η > 0`:
`logSqrtThreshold (⌈84 / min(η, 1/3)⌉₊ + 1)`. -/
def asymptoticRangeThreshold (η : ℚ) : ℕ := logSqrtThreshold (⌈84 / min η (1 / 3)⌉₊ + 1)

theorem asymptoticRangeThreshold_eq (η : ℚ) :
    asymptoticRangeThreshold η = logSqrtThreshold (⌈84 / min η (1 / 3)⌉₊ + 1) := (rfl)

/-- **Proposition 3.6, effective.** Let `c ≥ 2`, and let `η` be a positive rational with
`η ≤ log 4 - 1 - g(c)/c` (a rational lower bound for the strict margin of (3.27)). For every
`m ≥ asymptoticRangeThreshold η`, `δ ∈ {0,1}` and `r` with `c r ≤ m`, `F_{m,r,δ}` is
irreducible over `ℚ`. Conditional on `JacobiSimpleRealZeros` and
`DusartThetaBound`. -/
theorem irreducible_reducedGegenbauer_of_asymptoticRangeThreshold_le (hZ : JacobiSimpleRealZeros)
    (hD : DusartThetaBound)
    {c : ℝ} (hc : 2 ≤ c) {η : ℚ} (hη : 0 < η)
    (hη1 : (η : ℝ) ≤ log 4 - 1 - asymptoticGapFunction c / c) :
    ∀ m r δ : ℕ, δ ≤ 1 → asymptoticRangeThreshold η ≤ m → c * r ≤ m →
      Irreducible (reducedGegenbauer m r δ) := by
  change ∀ m r δ : ℕ, δ ≤ 1 → logSqrtThreshold (⌈84 / min η (1 / 3)⌉₊ + 1) ≤ m → c * r ≤ m →
    Irreducible (reducedGegenbauer m r δ)
  obtain ⟨μ, hμ⟩ : ∃ μ : ℚ, μ = min η (1 / 3) := ⟨_, rfl⟩
  rw [← hμ]
  have hμ0 : (0 : ℝ) < μ := by
    have h : 0 < μ := by rw [hμ]; exact lt_min hη (by norm_num)
    exact_mod_cast h
  have hμ1 : (μ : ℝ) ≤ η := by
    have h : μ ≤ η := by rw [hμ]; exact min_le_left _ _
    exact_mod_cast h
  have hμ2 : (μ : ℝ) ≤ 1 / 3 := by
    have h : μ ≤ 1 / 3 := by rw [hμ]; exact min_le_right _ _
    have h' : (μ : ℝ) ≤ ((1 / 3 : ℚ) : ℝ) := Rat.cast_le.mpr h
    rwa [show ((1 / 3 : ℚ) : ℝ) = 1 / 3 by norm_num] at h'
  have hk : 84 / (μ : ℝ) + 1 ≤ ((⌈84 / μ⌉₊ + 1 : ℕ) : ℝ) := by
    have h := rat_cast_le_ceil_add_one (84 / μ)
    push_cast at h ⊢
    linarith
  exact irreducible_reducedGegenbauer_of_logSqrtThreshold_le hZ hD hc hμ0 (hμ1.trans hη1)
    (hμ2.trans one_third_lt_log_four_sub_one.le) hk

/-- A rational margin as required by `irreducible_reducedGegenbauer_of_asymptoticRangeThreshold_le`
exists whenever `g(c) < c (log 4 - 1)`. -/
theorem exists_rat_margin_asymptoticGapFunction {c : ℝ} (hc : 2 ≤ c)
    (hgap : asymptoticGapFunction c < c * (log 4 - 1)) :
    ∃ η : ℚ, 0 < η ∧ (η : ℝ) ≤ log 4 - 1 - asymptoticGapFunction c / c := by
  have hc0 : 0 < c := by linarith
  have hgc : 0 < log 4 - 1 - asymptoticGapFunction c / c := by
    have : asymptoticGapFunction c / c < log 4 - 1 := by rw [div_lt_iff₀ hc0]; linarith
    linarith
  obtain ⟨η, h1, h2⟩ := exists_rat_btwn hgc
  exact ⟨η, by exact_mod_cast h1, h2.le⟩

/-! ### Proposition 3.6 for rational `c`: the margin by rational approximation

For rational `x ≥ 1` put `z = (x-1)/(x+1) ∈ [0,1)`, so that `x = (1+z)/(1-z)`. The partial sums
`L_n(x) = 2 ∑_{i<n} z^{2i+1}/(2i+1)` and `U_n(x) = L_n(x) + 2 z^{2n+1}/(1-z²)` of the series of
`2 artanh z` are rationals with `L_n(x) ≤ log x ≤ U_n(x)` and `U_n(x) - L_n(x) → 0`. For rational
`c ≥ 2` they give the rational lower bound `asymptoticMarginLower c n` of the margin
`log 4 - 1 - g(c)/c`, positive for large `n` when the margin is positive; the first such `n`
(`Nat.find`) yields a computable threshold depending only on `c`. -/

/-- `z = (x-1)/(x+1)`. -/
def logSeriesArg (x : ℚ) : ℚ := (x - 1) / (x + 1)

/-- The rational lower bound `L_n(x) = 2 ∑_{i<n} z^{2i+1}/(2i+1)` of `log x`. -/
def logLower (x : ℚ) (n : ℕ) : ℚ :=
  2 * ∑ i ∈ range n, logSeriesArg x ^ (2 * i + 1) / (2 * i + 1)

/-- The rational upper bound `U_n(x) = L_n(x) + 2 z^{2n+1}/(1-z²)` of `log x`. -/
def logUpper (x : ℚ) (n : ℕ) : ℚ :=
  logLower x n + 2 * (logSeriesArg x ^ (2 * n + 1) / (1 - logSeriesArg x ^ 2))

theorem logSeriesArg_eq (x : ℚ) : logSeriesArg x = (x - 1) / (x + 1) := (rfl)

theorem logLower_eq (x : ℚ) (n : ℕ) :
    logLower x n = 2 * ∑ i ∈ range n, logSeriesArg x ^ (2 * i + 1) / (2 * i + 1) := (rfl)

theorem logUpper_eq (x : ℚ) (n : ℕ) : logUpper x n =
    logLower x n + 2 * (logSeriesArg x ^ (2 * n + 1) / (1 - logSeriesArg x ^ 2)) := (rfl)

theorem logSeriesArg_spec {x : ℚ} (hx : 1 ≤ x) :
    ∃ z : ℝ, 0 ≤ z ∧ z < 1 ∧ ((logSeriesArg x : ℚ) : ℝ) = z ∧ (1 + z) / (1 - z) = x := by
  have hx' : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have h1 : (x : ℝ) + 1 ≠ 0 := by linarith
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = ((x : ℝ) - 1) / ((x : ℝ) + 1) := ⟨_, rfl⟩
  have hzx : z * ((x : ℝ) + 1) = x - 1 := by rw [hz]; exact div_mul_cancel₀ _ h1
  have hz1 : z < 1 := by rw [hz, div_lt_one (by linarith)]; linarith
  refine ⟨z, by rw [hz]; exact div_nonneg (by linarith) (by linarith), hz1, ?_, ?_⟩
  · rw [hz, logSeriesArg_eq, Rat.cast_div, Rat.cast_sub, Rat.cast_add, Rat.cast_one]
  · rw [div_eq_iff (sub_pos.mpr hz1).ne']
    linarith

theorem logLower_le_log {x : ℚ} (hx : 1 ≤ x) (n : ℕ) : (logLower x n : ℝ) ≤ log x := by
  obtain ⟨z, hz0, hz1, hzc, hratio⟩ := logSeriesArg_spec hx
  rw [logLower_eq]
  push_cast
  rw [hzc]
  have h := two_mul_sum_le_log_div hz0 hz1 n
  rwa [hratio] at h

theorem log_le_logUpper {x : ℚ} (hx : 1 ≤ x) (n : ℕ) : log x ≤ (logUpper x n : ℝ) := by
  obtain ⟨z, hz0, hz1, hzc, hratio⟩ := logSeriesArg_spec hx
  rw [logUpper_eq, logLower_eq]
  push_cast
  rw [hzc]
  have h := log_div_le_two_mul_sum_add hz0 hz1 n
  rw [hratio] at h
  linarith

theorem eventually_logUpper_sub_logLower_lt {x : ℚ} (hx : 1 ≤ x) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, ((logUpper x n : ℚ) : ℝ) - ((logLower x n : ℚ) : ℝ) < ε := by
  obtain ⟨z, hz0, hz1, hzc, -⟩ := logSeriesArg_spec hx
  have hq : 0 < 1 - z ^ 2 := by nlinarith
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hz0 hz1).const_mul (2 / (1 - z ^ 2))
  rw [mul_zero] at ht
  filter_upwards [ht.eventually_lt_const hε] with n hn
  rw [logUpper_eq]
  push_cast
  rw [hzc]
  have hp : z ^ (2 * n + 1) ≤ z ^ n := pow_le_pow_of_le_one hz0 hz1.le (by omega)
  have e : 2 * (z ^ (2 * n + 1) / (1 - z ^ 2)) = 2 / (1 - z ^ 2) * z ^ (2 * n + 1) := by ring
  have hm := mul_le_mul_of_nonneg_left hp (div_pos two_pos hq).le
  linarith

/-- The rational lower bound
`L_n(4) - 1 - ((4c+2) U_n(c+1/2) - 3c L_n(c) - (c+1) L_n(c+1))/c` of the margin
`log 4 - 1 - g(c)/c` of Proposition 3.6. -/
def asymptoticMarginLower (c : ℚ) (n : ℕ) : ℚ :=
  logLower 4 n - 1 -
    ((4 * c + 2) * logUpper (c + 1 / 2) n - 3 * c * logLower c n -
      (c + 1) * logLower (c + 1) n) / c

theorem asymptoticMarginLower_eq (c : ℚ) (n : ℕ) : asymptoticMarginLower c n =
    logLower 4 n - 1 -
      ((4 * c + 2) * logUpper (c + 1 / 2) n - 3 * c * logLower c n -
        (c + 1) * logLower (c + 1) n) / c := (rfl)

theorem asymptoticMarginLower_le {c : ℚ} (hc : 2 ≤ c) (n : ℕ) :
    (asymptoticMarginLower c n : ℝ) ≤ log 4 - 1 - asymptoticGapFunction c / c := by
  have hc' : (2 : ℝ) ≤ c := by exact_mod_cast hc
  have h4 := logLower_le_log (x := 4) (by norm_num) n
  have hU := log_le_logUpper (x := c + 1 / 2) (by linarith) n
  have hLc := logLower_le_log (x := c) (by linarith) n
  have hL1 := logLower_le_log (x := c + 1) (by linarith) n
  push_cast at h4 hU hL1
  rw [asymptoticMarginLower_eq, asymptoticGapFunction_eq]
  push_cast
  have p1 := mul_le_mul_of_nonneg_left hU (show (0 : ℝ) ≤ 4 * c + 2 by linarith)
  have p2 := mul_le_mul_of_nonneg_left hLc (show (0 : ℝ) ≤ 3 * c by linarith)
  have p3 := mul_le_mul_of_nonneg_left hL1 (show (0 : ℝ) ≤ c + 1 by linarith)
  have hG : (4 * (c : ℝ) + 2) * log ((c : ℝ) + 1 / 2) - 3 * (c : ℝ) * log (c : ℝ) -
      ((c : ℝ) + 1) * log ((c : ℝ) + 1) ≤
      (4 * (c : ℝ) + 2) * ((logUpper (c + 1 / 2) n : ℚ) : ℝ) -
        3 * (c : ℝ) * ((logLower c n : ℚ) : ℝ) -
          ((c : ℝ) + 1) * ((logLower (c + 1) n : ℚ) : ℝ) := by
    linarith
  have := div_le_div_of_nonneg_right hG (by linarith : (0 : ℝ) ≤ c)
  linarith

/-- For rational `c ≥ 2` with `g(c) < c (log 4 - 1)`, some rational bound
`asymptoticMarginLower c n` is positive. -/
theorem exists_asymptoticMarginLower_pos {c : ℚ} (hc : 2 ≤ c)
    (hgap : asymptoticGapFunction c < c * (log 4 - 1)) : ∃ n, 0 < asymptoticMarginLower c n := by
  have hc' : (2 : ℝ) ≤ c := by exact_mod_cast hc
  have hc0 : (0 : ℝ) < c := by linarith
  have hM : 0 < log 4 - 1 - asymptoticGapFunction c / c := by
    have : asymptoticGapFunction c / c < log 4 - 1 := by rw [div_lt_iff₀ hc0]; linarith
    linarith
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (log 4 - 1 - asymptoticGapFunction c / c) / 12 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have e4 : (1 : ℚ) ≤ 4 := by norm_num
  have ec2 : (1 : ℚ) ≤ c + 1 / 2 := by linarith
  have ec : (1 : ℚ) ≤ c := by linarith
  have ec1 : (1 : ℚ) ≤ c + 1 := by linarith
  obtain ⟨n, g4, gU, gc, g1⟩ := ((eventually_logUpper_sub_logLower_lt e4 hδ0).and
    ((eventually_logUpper_sub_logLower_lt ec2 hδ0).and
      ((eventually_logUpper_sub_logLower_lt ec hδ0).and
        (eventually_logUpper_sub_logLower_lt ec1 hδ0)))).exists
  refine ⟨n, ?_⟩
  have u4 := log_le_logUpper e4 n
  have lU := logLower_le_log ec2 n
  have uc := log_le_logUpper ec n
  have u1 := log_le_logUpper ec1 n
  push_cast at u4 lU u1
  have h : (0 : ℝ) < (asymptoticMarginLower c n : ℝ) := by
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
    have hM' : log 4 - 1 - asymptoticGapFunction c / c = 12 * δ := by rw [hδ]; ring
    linarith
  exact_mod_cast h

/-- **The computable threshold of Proposition 3.6 for rational `c`.** For rational `c ≥ 2` with
`g(c) < c (log 4 - 1)`: `asymptoticRangeThreshold` of the first positive rational margin bound
`asymptoticMarginLower c n` (found by `Nat.find`, a terminating search over `n`). -/
def asymptoticRangeThresholdOfRat (c : ℚ) (hc : 2 ≤ c)
    (hgap : asymptoticGapFunction c < c * (log 4 - 1)) : ℕ :=
  asymptoticRangeThreshold
    (asymptoticMarginLower c (Nat.find (exists_asymptoticMarginLower_pos hc hgap)))

/-- **Proposition 3.6, effective for rational `c`.** Let `c ≥ 2` be
rational with `c (log 4 - 1) > g(c)`. For every `m ≥ asymptoticRangeThresholdOfRat c`,
`δ ∈ {0,1}` and `0 ≤ r ≤ m/c`, `F_{m,r,δ} = C_{2m+δ}^{r+1/2}(x)/x^δ` is irreducible over `ℚ`.
Conditional on `JacobiSimpleRealZeros` and `DusartThetaBound`. -/
theorem irreducible_reducedGegenbauer_of_asymptoticRangeThresholdOfRat_le (hZ :
    JacobiSimpleRealZeros) (hD : DusartThetaBound)
    {c : ℚ} (hc : 2 ≤ c) (hgap : asymptoticGapFunction c < c * (log 4 - 1)) :
    ∀ m r δ : ℕ, δ ≤ 1 → asymptoticRangeThresholdOfRat c hc hgap ≤ m → (c : ℝ) * r ≤ m →
      Irreducible (reducedGegenbauer m r δ) :=
  irreducible_reducedGegenbauer_of_asymptoticRangeThreshold_le hZ hD (by exact_mod_cast hc)
    (Nat.find_spec (exists_asymptoticMarginLower_pos hc hgap)) (asymptoticMarginLower_le hc _)

/-! ### Theorem 1.4 with an explicit absolute `M₀` -/

/-- The explicit absolute `M₀` of Theorem 1.4: `3 594 641 + 3^69280 + 256 · 69280⁴`. -/
def symmetricAbsoluteThreshold : ℕ := logSqrtThreshold 69280

theorem symmetricAbsoluteThreshold_eq :
    symmetricAbsoluteThreshold = 3594641 + 3 ^ 69280 + 256 * 69280 ^ 4 := (rfl)

/-- **Theorem 1.4, second assertion, effective.** `F_{m,r,δ}` is irreducible over `ℚ` for all
`δ ∈ {0,1}`, `m ≥ 1` and `m ≥ max{8r, M₀}` with the explicit
`M₀ = symmetricAbsoluteThreshold = 3 594 641 + 3^69280 + 256 · 69280⁴`. Conditional on
`JacobiSimpleRealZeros` and `DusartThetaBound`. -/
theorem irreducible_reducedGegenbauer_of_symmetricAbsoluteThreshold_le (hZ : JacobiSimpleRealZeros)
    (hD : DusartThetaBound) :
    ∀ m r δ : ℕ, δ ≤ 1 → 1 ≤ m → max (8 * r) symmetricAbsoluteThreshold ≤ m →
      Irreducible (reducedGegenbauer m r δ) := by
  have hmargin := margin_asymptoticGapFunction_eight
  have h1 : (97 / 80000 : ℝ) ≤ log 4 - 1 - asymptoticGapFunction 8 / 8 := by linarith
  have h2 : (97 / 80000 : ℝ) ≤ log 4 - 1 := by linarith [one_third_lt_log_four_sub_one]
  have h :=
    irreducible_reducedGegenbauer_of_logSqrtThreshold_le hZ hD (c := 8) (k := 69280)
      (by norm_num) (by norm_num) h1 h2 (by norm_num)
  intro m r δ hδ _ hm
  exact h m r δ hδ (le_of_max_le_right hm) (by exact_mod_cast le_of_max_le_left hm)

/-- **Theorem 1.4, effective form**: both assertions, with the explicit absolute
`M₀ = symmetricAbsoluteThreshold`. -/
theorem symmetricParametersStatement_effective (hH : HansonLcmBound)
     (hZ : JacobiSimpleRealZeros) (hD : DusartThetaBound) :
    (∀ m r δ : ℕ, δ ≤ 1 → max (100 * r) 1000 ≤ m → Irreducible (reducedGegenbauer m r δ)) ∧
      ∀ m r δ : ℕ, δ ≤ 1 → 1 ≤ m → max (8 * r) symmetricAbsoluteThreshold ≤ m →
        Irreducible (reducedGegenbauer m r δ) :=
  ⟨(symmetricParametersStatement hH hZ hD).1,
    irreducible_reducedGegenbauer_of_symmetricAbsoluteThreshold_le hZ hD⟩

end ArithmeticOfJacobiPolynomials
