/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.KanekoZagier.GoodPrimes
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import ArithmeticOfJacobiPolynomials.NumberTheory.LogIntegralBounds
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Proposition 4.5: statement and the good-prime reduction

For a factorization `H_n = A B` put `R = |Res(A,B)|` and `R^{(6)} = R / (2^{v_2(R)} 3^{v_3(R)})`
(`primeToSixPart`). Proposition 4.5 asserts the estimates (4.2)
`log g_n = (𝔠 + o(1)) n` and `log R^{(6)} ≤ (𝔲 + o(1)) k n`, `k = deg A ≤ deg B`, uniformly in
the four families and in the factorization, with `𝔠 = π/(2√3)` and `𝔲 = 43/20 - π/√3`
(`KanekoZagierArithmeticAsymptotics`).

Proved here: the reduction to good primes `5 ≤ p ≤ n` used in the proof of Proposition 4.5,
`log R^{(6)} ≤ k ∑_{5 ≤ p ≤ n} E_p(n) log p` for `n ≥ 11` (`log_primeToSixPart_le`), which
combines both parts of Lemma 4.4. The later sections give the analytic part (series
evaluations, the prime number theorem in the classes modulo `6` on intervals, the window and
table reductions) and the proof of Proposition 4.5, `kanekoZagierArithmeticAsymptotics`,
conditional on [BMOR, Corollary 1.7] (`BMORPrimeCountingBound`).
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset Filter

/-- `R^{(6)} = R / (2^{v_2(R)} 3^{v_3(R)})` with `R = |r|`. -/
noncomputable def primeToSixPart (r : ℤ) : ℕ :=
  r.natAbs / (2 ^ padicValNat 2 r.natAbs * 3 ^ padicValNat 3 r.natAbs)

theorem primeToSixPart_eq (r : ℤ) : primeToSixPart r =
    r.natAbs / (2 ^ padicValNat 2 r.natAbs * 3 ^ padicValNat 3 r.natAbs) := (rfl)

/-- **Proposition 4.5**, statement: uniformly in
`λ, μ ∈ {-1,1}` and in the factorization `H_n = A B` with `deg A ≤ deg B`,
`log g_n = (π/(2√3) + o(1)) n` and `log R^{(6)} ≤ (43/20 - π/√3 + o(1)) deg A · n`. -/
def KanekoZagierArithmeticAsymptotics : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ l μ : ℤ, (l = 1 ∨ l = -1) → (μ = 1 ∨ μ = -1) →
    |Real.log (kzContent l μ n) - Real.pi / (2 * √3) * n| ≤ ε * n ∧
    ∀ A B : ℤ[X], kzPrimitive l μ n = A * B → A.natDegree ≤ B.natDegree →
      Real.log (primeToSixPart (resultant A B)) ≤
        (43 / 20 - Real.pi / √3 + ε) * A.natDegree * n

theorem kanekoZagierArithmeticAsymptotics_iff : KanekoZagierArithmeticAsymptotics ↔
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ l μ : ℤ, (l = 1 ∨ l = -1) → (μ = 1 ∨ μ = -1) →
      |Real.log (kzContent l μ n) - Real.pi / (2 * √3) * n| ≤ ε * n ∧
      ∀ A B : ℤ[X], kzPrimitive l μ n = A * B → A.natDegree ≤ B.natDegree →
        Real.log (primeToSixPart (resultant A B)) ≤
          (43 / 20 - Real.pi / √3 + ε) * A.natDegree * n := Iff.rfl

/-- `2^{v_2(N)} 3^{v_3(N)}` divides `N`. -/
theorem two_three_pow_dvd (N : ℕ) :
    2 ^ padicValNat 2 N * 3 ^ padicValNat 3 N ∣ N :=
  Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.pow _ _ (by norm_num))
    pow_padicValNat_dvd pow_padicValNat_dvd

/-- The prime factors of `R^{(6)}` are primes `p ≥ 5` dividing `R`, with
`v_p(R^{(6)}) ≤ v_p(R)`. -/
theorem primeFactors_primeToSixPart {r : ℤ} (hr : r ≠ 0) {p : ℕ}
    (hp : p ∈ (primeToSixPart r).primeFactors) :
    p.Prime ∧ 5 ≤ p ∧ (primeToSixPart r).factorization p ≤ padicValInt p r ∧
      1 ≤ padicValInt p r := by
  have hN : r.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hr
  have hd := two_three_pow_dvd r.natAbs
  have hdpos : 0 < 2 ^ padicValNat 2 r.natAbs * 3 ^ padicValNat 3 r.natAbs := by positivity
  have hN6 : primeToSixPart r ≠ 0 := by
    rw [primeToSixPart_eq]
    exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hd) hdpos).ne'
  have hdvd : primeToSixPart r ∣ r.natAbs := by
    rw [primeToSixPart_eq]; exact Nat.div_dvd_of_dvd hd
  have hmul : (2 ^ padicValNat 2 r.natAbs * 3 ^ padicValNat 3 r.natAbs) * primeToSixPart r =
      r.natAbs := by
    rw [primeToSixPart_eq]; exact Nat.mul_div_cancel' hd
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  have h2 : p ≠ 2 := by
    rintro rfl
    apply pow_succ_padicValNat_not_dvd (p := 2) hN
    rw [pow_succ]
    exact dvd_trans (Nat.mul_dvd_mul (dvd_mul_right _ _) hpd) (dvd_of_eq hmul)
  have h3 : p ≠ 3 := by
    rintro rfl
    apply pow_succ_padicValNat_not_dvd (p := 3) hN
    rw [pow_succ]
    exact dvd_trans (Nat.mul_dvd_mul (dvd_mul_left _ _) hpd) (dvd_of_eq hmul)
  have h4 : p ≠ 4 := by
    rintro rfl
    have := hpp.eq_one_or_self_of_dvd 2 (by norm_num)
    omega
  have h5 : 5 ≤ p := by
    have := hpp.two_le
    omega
  have : Fact p.Prime := ⟨hpp⟩
  have hle : (primeToSixPart r).factorization p ≤ r.natAbs.factorization p :=
    (Nat.factorization_le_iff_dvd hN6 hN).mpr hdvd p
  rw [Nat.factorization_def r.natAbs hpp] at hle
  have hpos : 1 ≤ padicValNat p r.natAbs :=
    one_le_padicValNat_of_dvd hN (dvd_trans hpd hdvd)
  exact ⟨hpp, h5, hle, hpos⟩

/-- **Reduction to good primes** (proof of Proposition 4.5): for `n ≥ 11` and every
factorization `H_n = A B` in `ℤ[t]`, `log R^{(6)} ≤ deg A · ∑_{5 ≤ p ≤ n} E_p(n) log p`. -/
theorem log_primeToSixPart_le {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    {n : ℕ} (hn : 11 ≤ n) {A B : ℤ[X]} (hAB : kzPrimitive l μ n = A * B) :
    Real.log (primeToSixPart (resultant A B)) ≤
      A.natDegree * ∑ p ∈ (Icc 5 n).filter Nat.Prime,
        (kzBudget l μ n p : ℝ) * Real.log p := by
  have hterm : ∀ p ∈ (Icc 5 n).filter Nat.Prime, 0 ≤ (kzBudget l μ n p : ℝ) * Real.log p := by
    intro p hp
    obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
    have : Fact p.Prime := ⟨hpp⟩
    have h5 := (mem_Icc.mp hpI).1
    have hE : (0 : ℝ) ≤ kzBudget l μ n p := by exact_mod_cast kzBudget_nonneg hl hμ h5 n
    exact mul_nonneg hE (Real.log_nonneg (by exact_mod_cast hpp.one_lt.le))
  have hRHS : 0 ≤ (A.natDegree : ℝ) * ∑ p ∈ (Icc 5 n).filter Nat.Prime,
      (kzBudget l μ n p : ℝ) * Real.log p :=
    mul_nonneg (Nat.cast_nonneg _) (sum_nonneg hterm)
  by_cases hr : resultant A B = 0
  · rw [primeToSixPart_eq, hr, Int.natAbs_zero, Nat.zero_div, Nat.cast_zero, Real.log_zero]
    exact hRHS
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization, mul_sum]
  have hsub : (primeToSixPart (resultant A B)).primeFactors ⊆ (Icc 5 n).filter Nat.Prime := by
    intro p hp
    obtain ⟨hpp, h5, -, hpos⟩ := primeFactors_primeToSixPart hr hp
    have : Fact p.Prime := ⟨hpp⟩
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨h5, ?_⟩, hpp⟩
    by_contra hpn
    have := kz_padicValInt_resultant_eq_zero hl hμ hn hAB (p := p) (by omega)
    omega
  calc ∑ p ∈ (primeToSixPart (resultant A B)).primeFactors,
        ((primeToSixPart (resultant A B)).factorization p : ℝ) * Real.log p
      ≤ ∑ p ∈ (primeToSixPart (resultant A B)).primeFactors,
          (A.natDegree : ℝ) * ((kzBudget l μ n p : ℝ) * Real.log p) := by
        refine sum_le_sum fun p hp => ?_
        obtain ⟨hpp, h5, hle, -⟩ := primeFactors_primeToSixPart hr hp
        have : Fact p.Prime := ⟨hpp⟩
        have hb := kz_padicValInt_resultant_le hl hμ (by omega) hAB h5
        have h : ((primeToSixPart (resultant A B)).factorization p : ℝ) ≤
            (A.natDegree : ℝ) * (kzBudget l μ n p : ℝ) := by
          have h' : ((primeToSixPart (resultant A B)).factorization p : ℤ) ≤
              A.natDegree * kzBudget l μ n p := le_trans (by exact_mod_cast hle) hb
          exact_mod_cast h'
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right h (Real.log_nonneg (by exact_mod_cast hpp.one_lt.le))
    _ ≤ ∑ p ∈ (Icc 5 n).filter Nat.Prime,
          (A.natDegree : ℝ) * ((kzBudget l μ n p : ℝ) * Real.log p) :=
        sum_le_sum_of_subset_of_nonneg hsub fun p hp _ =>
          mul_nonneg (Nat.cast_nonneg _) (hterm p hp)

end ArithmeticOfJacobiPolynomials

/-!
## Series evaluations for Proposition 4.5

The two constants of Proposition 4.5 as limits of partial sums:

* `tendsto_cotThirdSum`: `∑_{k ≥ 0} (1/(3k+1) - 1/(3k+2)) = π/(3√3)`, from Mathlib's
  partial-fraction expansion of `π cot(πx)` at `x = 1/3` (`tendsto_logDeriv_euler_cot_sub`);
* `tendsto_sum_contentTerm`: `½ ∑_{ℓ ≥ 0} (1/(ℓ+2/3) - 1/(ℓ+1) + 1/(ℓ+1/2) - 1/(ℓ+5/6)) = π/(2√3)`
  (the logarithmic parts cancel, via `harmonic n - log n → γ`);
* `tendsto_sum_resultantTerm`:
  `½ ∑_{ℓ ≥ 1} (1/ℓ - 1/(ℓ+1/6) + 1/(ℓ+1/3) - 1/(ℓ+2/3) + 1/(ℓ+5/6) - 1/(ℓ+1)) = 43/20 - π/√3`;
* `sum_contentTerm_le`, `sum_resultantTerm_le`: the partial sums (of nonnegative terms) are at
  most the limits.
-/

namespace ArithmeticOfJacobiPolynomials

open Filter Topology Finset

/-- `A(N) = ∑_{k < N} (1/(3k+1) - 1/(3k+2))`. -/
noncomputable def cotThirdSum (N : ℕ) : ℝ :=
  ∑ k ∈ range N, (1 / (3 * (k : ℝ) + 1) - 1 / (3 * (k : ℝ) + 2))

theorem cotThirdSum_eq (N : ℕ) : cotThirdSum N =
    ∑ k ∈ range N, (1 / (3 * (k : ℝ) + 1) - 1 / (3 * (k : ℝ) + 2)) := (rfl)

theorem real_cot_pi_div_three : Real.cot (Real.pi / 3) = 1 / √3 := by
  rw [Real.cot_eq_cos_div_sin, Real.cos_pi_div_three, Real.sin_pi_div_three]
  have h3 : (0 : ℝ) < √3 := by positivity
  field_simp

theorem one_third_mem_integerComplement : ((1 / 3 : ℝ) : ℂ) ∈ Complex.integerComplement := by
  rw [Complex.mem_integerComplement_iff]
  rintro ⟨n, hn⟩
  have h : ((n : ℝ) : ℂ) = ((1 / 3 : ℝ) : ℂ) := by rw [← hn]; push_cast; rfl
  have h' : (n : ℝ) = 1 / 3 := Complex.ofReal_injective h
  have h1 : (3 : ℝ) * n = 1 := by rw [h']; norm_num
  have h2 : (3 : ℤ) * n = 1 := by exact_mod_cast h1
  omega

/-- The partial sums of the cotangent expansion at `x = 1/3`, as real numbers. -/
theorem cot_partial_third (N : ℕ) :
    1 / (1 / 3 : ℝ) + ∑ j ∈ range N, (1 / ((1 / 3 : ℝ) - (j + 1)) +
      1 / ((1 / 3 : ℝ) + (j + 1))) = 3 * cotThirdSum N + 3 / (3 * N + 1) := by
  induction N with
  | zero => simp [cotThirdSum_eq]
  | succ N ih =>
    rw [sum_range_succ, ← add_assoc, ih, cotThirdSum_eq, cotThirdSum_eq, sum_range_succ]
    push_cast
    have h1 : (0 : ℝ) < 3 * N + 1 := by positivity
    have h2 : (0 : ℝ) < 3 * N + 2 := by positivity
    have h4 : (0 : ℝ) < 3 * N + 4 := by positivity
    have e1 : (1 : ℝ) / (1 / 3 - (N + 1)) = -3 / (3 * N + 2) := by
      rw [show (1 : ℝ) / 3 - (N + 1) = -((3 * N + 2) / 3) by ring, div_neg, one_div_div,
        neg_div]
    have e2 : (1 : ℝ) / (1 / 3 + (N + 1)) = 3 / (3 * N + 4) := by
      field_simp; ring
    rw [e1, e2]
    field_simp
    ring

theorem tendsto_cot_partial_third : Tendsto (fun N : ℕ => 1 / (1 / 3 : ℝ) +
    ∑ j ∈ range N, (1 / ((1 / 3 : ℝ) - (j + 1)) + 1 / ((1 / 3 : ℝ) + (j + 1))))
    atTop (𝓝 (Real.pi / √3)) := by
  have h := tendsto_logDeriv_euler_cot_sub one_third_mem_integerComplement
  have h' := (Complex.continuous_re.tendsto _).comp h
  have h'' := h'.const_add ((1 / (1 / 3 : ℝ) : ℝ))
  convert h'' using 1
  · funext N
    simp only [Function.comp_apply, cotTerm]
    rw [Complex.re_sum]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    have e1 : ((1 / 3 : ℝ) : ℂ) - ((j : ℂ) + 1) = (((1 / 3 : ℝ) - (j + 1) : ℝ) : ℂ) := by
      push_cast; ring
    have e2 : ((1 / 3 : ℝ) : ℂ) + ((j : ℂ) + 1) = (((1 / 3 : ℝ) + (j + 1) : ℝ) : ℂ) := by
      push_cast; ring
    rw [e1, e2, ← Complex.ofReal_one, ← Complex.ofReal_div, ← Complex.ofReal_div,
      ← Complex.ofReal_add, Complex.ofReal_re]
  · have e : (Real.pi : ℂ) * ((1 / 3 : ℝ) : ℂ) = ((Real.pi / 3 : ℝ) : ℂ) := by
      push_cast; ring
    rw [e, ← Complex.ofReal_cot, real_cot_pi_div_three, ← Complex.ofReal_one,
      ← Complex.ofReal_div, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.ofReal_re]
    norm_num
    field_simp

/-- `∑_{k ≥ 0} (1/(3k+1) - 1/(3k+2)) = π/(3√3)`. -/
theorem tendsto_cotThirdSum : Tendsto cotThirdSum atTop (𝓝 (Real.pi / (3 * √3))) := by
  have h1 := tendsto_cot_partial_third.div_const 3
  have h2 : Tendsto (fun N : ℕ => 1 / (3 * (N : ℝ) + 1)) atTop (𝓝 0) := by
    have : Tendsto (fun N : ℕ => 3 * (N : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _
        (Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop)
    simpa [Pi.inv_def] using this.inv_tendsto_atTop
  have h3 := h1.sub h2
  rw [show Real.pi / √3 / 3 - 0 = Real.pi / (3 * √3) by ring] at h3
  refine h3.congr fun N => ?_
  rw [cot_partial_third]
  simp; ring

/-! ### The content series -/

/-- The `ℓ`-th term `½(1/(ℓ+2/3) - 1/(ℓ+1) + 1/(ℓ+1/2) - 1/(ℓ+5/6))` of the content series,
written as `3/(6ℓ+3) + 3/(6ℓ+4) - 3/(6ℓ+5) - 3/(6ℓ+6)`. -/
noncomputable def contentTerm (l : ℕ) : ℝ :=
  3 / (6 * (l : ℝ) + 3) + 3 / (6 * (l : ℝ) + 4) - 3 / (6 * (l : ℝ) + 5) - 3 / (6 * (l : ℝ) + 6)

theorem contentTerm_eq (l : ℕ) : contentTerm l =
    3 / (6 * (l : ℝ) + 3) + 3 / (6 * (l : ℝ) + 4) - 3 / (6 * (l : ℝ) + 5) -
      3 / (6 * (l : ℝ) + 6) := (rfl)

/-- `∑_{i < m} 1/(i+1)` as a real number. -/
noncomputable def harmonicReal (m : ℕ) : ℝ := ∑ i ∈ range m, 1 / ((i : ℝ) + 1)

theorem harmonicReal_eq (m : ℕ) : harmonicReal m = ∑ i ∈ range m, 1 / ((i : ℝ) + 1) := (rfl)

theorem harmonicReal_eq_harmonic (m : ℕ) : harmonicReal m = (harmonic m : ℝ) := by
  rw [harmonicReal_eq, harmonic]
  push_cast
  simp

theorem harmonicReal_succ (m : ℕ) :
    harmonicReal (m + 1) = harmonicReal m + 1 / ((m : ℝ) + 1) := by
  rw [harmonicReal_eq, harmonicReal_eq, sum_range_succ]

theorem sum_contentTerm_eq (N : ℕ) : ∑ l ∈ range N, contentTerm l =
    3 / 2 * (harmonicReal (3 * N) + harmonicReal (2 * N) - harmonicReal N -
      harmonicReal (6 * N)) + 3 / 2 * cotThirdSum (2 * N) := by
  induction N with
  | zero => simp [harmonicReal_eq, cotThirdSum_eq]
  | succ N ih =>
    rw [sum_range_succ, ih]
    rw [show 3 * (N + 1) = 3 * N + 1 + 1 + 1 by ring, show 2 * (N + 1) = 2 * N + 1 + 1 by ring,
      show 6 * (N + 1) = 6 * N + 1 + 1 + 1 + 1 + 1 + 1 by ring]
    simp only [harmonicReal_succ, cotThirdSum_eq, sum_range_succ, contentTerm_eq]
    push_cast
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    field_simp
    ring

theorem tendsto_harmonicReal_mul_sub_log {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun N : ℕ => harmonicReal (k * N) - Real.log ((k * N : ℕ) : ℝ)) atTop
      (𝓝 Real.eulerMascheroniConstant) := by
  have hkN : Tendsto (fun N : ℕ => k * N) atTop atTop :=
    tendsto_atTop_mono (fun N => Nat.le_mul_of_pos_left N hk) tendsto_id
  have h := Real.tendsto_harmonic_sub_log.comp hkN
  refine h.congr fun N => ?_
  simp [harmonicReal_eq_harmonic]

theorem log_combination_eq {N : ℕ} (hN : 1 ≤ N) :
    Real.log ((3 * N : ℕ) : ℝ) + Real.log ((2 * N : ℕ) : ℝ) - Real.log ((1 * N : ℕ) : ℝ) -
      Real.log ((6 * N : ℕ) : ℝ) = 0 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  push_cast
  rw [Real.log_mul (by norm_num) hN'.ne', Real.log_mul (by norm_num) hN'.ne',
    Real.log_mul (by norm_num) hN'.ne', Real.log_mul (by norm_num) hN'.ne',
    show (6 : ℝ) = 3 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  simp; ring

/-- `∑_{ℓ ≥ 0} ½(1/(ℓ+2/3) - 1/(ℓ+1) + 1/(ℓ+1/2) - 1/(ℓ+5/6)) = π/(2√3)`. -/
theorem tendsto_sum_contentTerm :
    Tendsto (fun N : ℕ => ∑ l ∈ range N, contentTerm l) atTop (𝓝 (Real.pi / (2 * √3))) := by
  have h3 := tendsto_harmonicReal_mul_sub_log (k := 3) (by norm_num)
  have h2 := tendsto_harmonicReal_mul_sub_log (k := 2) (by norm_num)
  have h1 := tendsto_harmonicReal_mul_sub_log (k := 1) (by norm_num)
  have h6 := tendsto_harmonicReal_mul_sub_log (k := 6) (by norm_num)
  have hA : Tendsto (fun N : ℕ => cotThirdSum (2 * N)) atTop (𝓝 (Real.pi / (3 * √3))) :=
    tendsto_cotThirdSum.comp
      (tendsto_atTop_mono (fun N => Nat.le_mul_of_pos_left N (by norm_num)) tendsto_id)
  have hcomb := ((((h3.add h2).sub h1).sub h6).const_mul (3 / 2)).add (hA.const_mul (3 / 2))
  have e : 3 / 2 * (Real.eulerMascheroniConstant + Real.eulerMascheroniConstant -
      Real.eulerMascheroniConstant - Real.eulerMascheroniConstant) +
      3 / 2 * (Real.pi / (3 * √3)) = Real.pi / (2 * √3) := by
    have : (0 : ℝ) < √3 := by positivity
    field_simp
    ring
  rw [e] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [sum_contentTerm_eq]
  have hl := log_combination_eq hN
  simp only [one_mul] at hl ⊢
  linarith

theorem contentTerm_nonneg (l : ℕ) : 0 ≤ contentTerm l := by
  rw [contentTerm_eq]
  have h1 : 3 / (6 * (l : ℝ) + 5) ≤ 3 / (6 * (l : ℝ) + 3) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have h2 : 3 / (6 * (l : ℝ) + 6) ≤ 3 / (6 * (l : ℝ) + 4) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  linarith

theorem sum_contentTerm_le (N : ℕ) : ∑ l ∈ range N, contentTerm l ≤ Real.pi / (2 * √3) :=
  Monotone.ge_of_tendsto (monotone_nat_of_le_succ fun N => by
    rw [sum_range_succ]; linarith [contentTerm_nonneg N]) tendsto_sum_contentTerm N

/-! ### The resultant series -/

/-- The `ℓ`-th term `½(1/ℓ - 1/(ℓ+1/6) + 1/(ℓ+1/3) - 1/(ℓ+2/3) + 1/(ℓ+5/6) - 1/(ℓ+1))` of the
resultant series, written with denominators `6ℓ + j`. -/
noncomputable def resultantTerm (l : ℕ) : ℝ :=
  3 / (6 * (l : ℝ)) - 3 / (6 * (l : ℝ) + 1) + 3 / (6 * (l : ℝ) + 2) - 3 / (6 * (l : ℝ) + 4) +
    3 / (6 * (l : ℝ) + 5) - 3 / (6 * (l : ℝ) + 6)

theorem resultantTerm_eq (l : ℕ) : resultantTerm l =
    3 / (6 * (l : ℝ)) - 3 / (6 * (l : ℝ) + 1) + 3 / (6 * (l : ℝ) + 2) - 3 / (6 * (l : ℝ) + 4) +
      3 / (6 * (l : ℝ) + 5) - 3 / (6 * (l : ℝ) + 6) := (rfl)

theorem sum_resultantTerm_eq (N : ℕ) : ∑ l ∈ range N, resultantTerm (l + 1) =
    3 * (1 / 6 - 1 / (6 * (N : ℝ) + 6) - cotThirdSum (2 * N + 2) + 11 / 20) := by
  induction N with
  | zero => simp [cotThirdSum_eq, sum_range_succ]; norm_num
  | succ N ih =>
    rw [sum_range_succ, ih, show 2 * (N + 1) + 2 = 2 * N + 2 + 1 + 1 by ring]
    simp only [cotThirdSum_eq, sum_range_succ, resultantTerm_eq]
    push_cast
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    field_simp
    ring

/-- `∑_{ℓ ≥ 1} ½(1/ℓ - 1/(ℓ+1/6) + 1/(ℓ+1/3) - 1/(ℓ+2/3) + 1/(ℓ+5/6) - 1/(ℓ+1))
= 43/20 - π/√3`. -/
theorem tendsto_sum_resultantTerm : Tendsto (fun N : ℕ => ∑ l ∈ range N, resultantTerm (l + 1))
    atTop (𝓝 (43 / 20 - Real.pi / √3)) := by
  have hA : Tendsto (fun N : ℕ => cotThirdSum (2 * N + 2)) atTop (𝓝 (Real.pi / (3 * √3))) :=
    tendsto_cotThirdSum.comp
      (tendsto_atTop_mono (fun N => show N ≤ 2 * N + 2 by omega) tendsto_id)
  have h2 : Tendsto (fun N : ℕ => 1 / (6 * (N : ℝ) + 6)) atTop (𝓝 0) := by
    have : Tendsto (fun N : ℕ => 6 * (N : ℝ) + 6) atTop atTop :=
      tendsto_atTop_add_const_right _ _
        (Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop)
    simpa [Pi.inv_def] using this.inv_tendsto_atTop
  have h := ((((tendsto_const_nhds (x := (1 / 6 : ℝ))).sub h2).sub hA).add
    (tendsto_const_nhds (x := (11 / 20 : ℝ)))).const_mul 3
  have e : 3 * (1 / 6 - 0 - Real.pi / (3 * √3) + 11 / 20) = 43 / 20 - Real.pi / √3 := by
    have : (0 : ℝ) < √3 := by positivity
    field_simp
    ring
  rw [e] at h
  exact h.congr fun N => (sum_resultantTerm_eq N).symm

theorem resultantTerm_nonneg {l : ℕ} (hl : 1 ≤ l) : 0 ≤ resultantTerm l := by
  rw [resultantTerm_eq]
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have h1 : 3 / (6 * (l : ℝ) + 1) ≤ 3 / (6 * (l : ℝ)) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have h2 : 3 / (6 * (l : ℝ) + 4) ≤ 3 / (6 * (l : ℝ) + 2) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have h3 : 3 / (6 * (l : ℝ) + 6) ≤ 3 / (6 * (l : ℝ) + 5) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  linarith

theorem sum_resultantTerm_le (N : ℕ) :
    ∑ l ∈ range N, resultantTerm (l + 1) ≤ 43 / 20 - Real.pi / √3 :=
  Monotone.ge_of_tendsto (monotone_nat_of_le_succ fun N => by
    rw [sum_range_succ]; linarith [resultantTerm_nonneg (l := N + 1) (by omega)])
    tendsto_sum_resultantTerm N

end ArithmeticOfJacobiPolynomials

/-!
## Prime sums in the reduced classes modulo `6` over intervals

From [BMOR, Corollary 1.7] (`BMORPrimeCountingBound`, used only for `q = 6`):

* `card_primesIoc_six_le`, `card_primesIoc_six_ge`: two-sided bounds for the number of primes
  `≡ r (mod 6)` in `(lo, hi]`;
* `abs_sum_log_primesIoc_six_sub_le`: `∑_{lo < p ≤ hi, p ≡ r} log p = (hi - lo)/2` up to
  `hi (log D + 1)/log lo` when `hi ≤ D lo`;
* `eventually_abs_primeLogSumSix_sub_le`: the prime number theorem in the two reduced classes
  modulo `6` on intervals `(y, x]` with `c x ≤ y ≤ x`, uniformly: `(x - y)/2 + o(x)`.
-/

namespace ArithmeticOfJacobiPolynomials

open Filter Topology Finset

theorem totient_six : (6 : ℕ).totient = 2 := by decide

/-- Upper bound for the number of primes `≡ r (mod 6)` in `(lo, hi]` ([BMOR, Corollary 1.7]). -/
theorem card_primesIoc_six_le (hBMOR : BMORPrimeCountingBound) {r : ℤ} (hr : Int.gcd r 6 = 1)
    {lo hi : ℕ} (hlo : 10 ^ 6 ≤ lo) (h : lo ≤ hi) :
    ((primesIoc lo hi 6 r).card : ℝ) ≤
      ((hi : ℝ) - lo) / (2 * Real.log lo) + 0.054 * hi / Real.log lo ^ 2 := by
  have hlo' : (10 : ℝ) ^ 6 ≤ lo := by exact_mod_cast hlo
  have hhl : (lo : ℝ) ≤ hi := by exact_mod_cast h
  have hhi' : (10 : ℝ) ^ 6 ≤ hi := hlo'.trans hhl
  have h1 := hBMOR 6 r (by norm_num) (by norm_num) hr hi hhi'
  have h2 := hBMOR 6 r (by norm_num) (by norm_num) hr lo hlo'
  rw [abs_lt, totient_six] at h1 h2
  have hLi := logIntegral_sub_le (a := lo) (b := hi) (by linarith) hhl
  have hΛ : 13.8 ≤ Real.log lo := log_ge_of_million_le hlo'
  have hΛ' : Real.log lo ≤ Real.log hi := Real.log_le_log (by linarith) hhl
  rw [card_primesIoc_eq_sub h]
  have e1 : (hi : ℝ) / Real.log hi ^ 2 ≤ hi / Real.log lo ^ 2 :=
    div_le_div_of_nonneg_left (by linarith) (by positivity) (by gcongr)
  have e2 : (lo : ℝ) / Real.log lo ^ 2 ≤ hi / Real.log lo ^ 2 :=
    div_le_div_of_nonneg_right hhl (by positivity)
  have e3 : ((hi : ℝ) - lo) / (2 * Real.log lo) = ((hi - lo) / Real.log lo) / 2 := by
    field_simp
  have e4 : (0.054 : ℝ) * hi / Real.log lo ^ 2 =
      0.027 * (hi / Real.log lo ^ 2) + 0.027 * (hi / Real.log lo ^ 2) := by ring
  have e5 : (0.027 : ℝ) * hi / Real.log hi ^ 2 = 0.027 * (hi / Real.log hi ^ 2) := by ring
  have e6 : (0.027 : ℝ) * lo / Real.log lo ^ 2 = 0.027 * (lo / Real.log lo ^ 2) := by ring
  rw [e3, e4]
  rw [e5] at h1
  rw [e6] at h2
  have : logIntegral hi / ((2 : ℕ) : ℝ) - logIntegral lo / ((2 : ℕ) : ℝ) ≤
      ((hi - lo) / Real.log lo) / 2 := by
    rw [← sub_div]; push_cast; linarith
  linarith [h1.2, h2.1]

/-- Lower bound for the number of primes `≡ r (mod 6)` in `(lo, hi]` ([BMOR, Corollary 1.7]). -/
theorem card_primesIoc_six_ge (hBMOR : BMORPrimeCountingBound) {r : ℤ} (hr : Int.gcd r 6 = 1)
    {lo hi : ℕ} (hlo : 10 ^ 6 ≤ lo) (h : lo ≤ hi) :
    ((hi : ℝ) - lo) / (2 * Real.log hi) - 0.054 * hi / Real.log lo ^ 2 ≤
      ((primesIoc lo hi 6 r).card : ℝ) := by
  have hlo' : (10 : ℝ) ^ 6 ≤ lo := by exact_mod_cast hlo
  have hhl : (lo : ℝ) ≤ hi := by exact_mod_cast h
  have hΛ : 13.8 ≤ Real.log lo := log_ge_of_million_le hlo'
  have hΛ' : Real.log lo ≤ Real.log hi := Real.log_le_log (by linarith) hhl
  have hc := card_primesIoc_gt hBMOR (q := 6) (a := r) (by norm_num) (by norm_num) hr hlo h
  rw [totient_six] at hc
  push_cast at hc
  have e1 : (hi : ℝ) / Real.log hi ^ 2 ≤ hi / Real.log lo ^ 2 :=
    div_le_div_of_nonneg_left (by linarith) (by positivity) (by gcongr)
  have e2 : (lo : ℝ) / Real.log lo ^ 2 ≤ hi / Real.log lo ^ 2 :=
    div_le_div_of_nonneg_right hhl (by positivity)
  have e4 : (0.054 : ℝ) * hi / Real.log lo ^ 2 =
      0.027 * (hi / Real.log lo ^ 2) + 0.027 * (hi / Real.log lo ^ 2) := by ring
  rw [e4]
  linarith

/-- `∑_{lo < p ≤ hi, p ≡ r (6)} log p` is `(hi - lo)/2` up to `hi (log D + 1) / log lo`
when `hi ≤ D lo`. -/
theorem abs_sum_log_primesIoc_six_sub_le (hBMOR : BMORPrimeCountingBound) {r : ℤ}
    (hr : Int.gcd r 6 = 1) {lo hi : ℕ} (hlo : 10 ^ 6 ≤ lo) (h : lo ≤ hi) {D : ℝ} (hD : 1 ≤ D)
    (hhiD : (hi : ℝ) ≤ D * lo) :
    |∑ p ∈ primesIoc lo hi 6 r, Real.log p - ((hi : ℝ) - lo) / 2| ≤
      hi * (Real.log D + 1) / Real.log lo := by
  have hlo' : (10 : ℝ) ^ 6 ≤ lo := by exact_mod_cast hlo
  have hhl : (lo : ℝ) ≤ hi := by exact_mod_cast h
  have hlo0 : (0 : ℝ) < lo := by linarith
  set Λ := Real.log lo with hΛdef
  set Λ' := Real.log hi with hΛ'def
  have hΛ : 13.8 ≤ Λ := log_ge_of_million_le hlo'
  have hΛΛ' : Λ ≤ Λ' := Real.log_le_log hlo0 hhl
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hΛ'D : Λ' ≤ Real.log D + Λ := by
    rw [hΛ'def, hΛdef, ← Real.log_mul (by linarith) hlo0.ne']
    exact Real.log_le_log (by linarith) hhiD
  set C : ℝ := ((primesIoc lo hi 6 r).card : ℝ) with hCdef
  have hC0 : 0 ≤ C := Nat.cast_nonneg _
  have hCu := card_primesIoc_six_le hBMOR hr hlo h
  have hCl := card_primesIoc_six_ge hBMOR hr hlo h
  rw [← hCdef, ← hΛdef] at hCu hCl
  rw [← hΛ'def] at hCl
  have hθu : ∑ p ∈ primesIoc lo hi 6 r, Real.log p ≤ Λ' * C := by
    rw [hCdef, mul_comm, ← nsmul_eq_mul, ← sum_const]
    refine sum_le_sum fun p hp => ?_
    obtain ⟨h1, h2, h3, -⟩ := mem_primesIoc.mp hp
    exact Real.log_le_log (by exact_mod_cast h3.pos) (by exact_mod_cast h2)
  have hθl : Λ * C ≤ ∑ p ∈ primesIoc lo hi 6 r, Real.log p := by
    rw [hCdef, mul_comm, ← nsmul_eq_mul, ← sum_const]
    refine sum_le_sum fun p hp => ?_
    obtain ⟨h1, h2, h3, -⟩ := mem_primesIoc.mp hp
    exact Real.log_le_log hlo0 (by exact_mod_cast h1.le)
  have hΛ0 : 0 < Λ := by linarith
  have hΛ'0 : 0 < Λ' := by linarith
  rw [abs_le]
  constructor
  · -- lower bound
    have k1 : Λ * (((hi : ℝ) - lo) / (2 * Λ') - 0.054 * hi / Λ ^ 2) ≤ Λ * C :=
      mul_le_mul_of_nonneg_left hCl hΛ0.le
    have k2 : Λ * (((hi : ℝ) - lo) / (2 * Λ') - 0.054 * hi / Λ ^ 2) =
        ((hi : ℝ) - lo) * Λ / (2 * Λ') - 0.054 * hi / Λ := by
      field_simp
    have k3 : ((hi : ℝ) - lo) / 2 - hi * Real.log D / (2 * Λ) ≤
        ((hi : ℝ) - lo) * Λ / (2 * Λ') := by
      rw [div_sub_div _ _ (by norm_num) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      have : ((hi : ℝ) - lo) * (Λ' - Λ) ≤ hi * Real.log D := by
        apply mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
      have hhi0 : (0 : ℝ) ≤ hi := by linarith
      nlinarith [mul_le_mul_of_nonneg_right this hΛ0.le,
        mul_le_mul_of_nonneg_left hΛΛ' (mul_nonneg hhi0 hlogD)]
    have k4 : hi * Real.log D / (2 * Λ) + 0.054 * hi / Λ ≤ hi * (Real.log D + 1) / Λ := by
      rw [div_add_div _ _ (by positivity) hΛ0.ne', div_le_div_iff₀ (by positivity) hΛ0]
      have : (0 : ℝ) ≤ hi := by linarith
      have q1 : 0 ≤ (hi : ℝ) * Λ * Λ := by positivity
      have q2 : 0 ≤ (hi : ℝ) * Real.log D * Λ * Λ := by positivity
      nlinarith
    linarith
  · -- upper bound
    have k1 : Λ' * C ≤ Λ' * (((hi : ℝ) - lo) / (2 * Λ) + 0.054 * hi / Λ ^ 2) :=
      mul_le_mul_of_nonneg_left hCu hΛ'0.le
    have k2 : Λ' * (((hi : ℝ) - lo) / (2 * Λ) + 0.054 * hi / Λ ^ 2) ≤
        ((hi : ℝ) - lo) / 2 + hi * (Real.log D + 1) / Λ := by
      have hhi0 : (0 : ℝ) ≤ hi := by linarith
      rw [div_add_div _ _ (by positivity) (by positivity), mul_div_assoc',
        div_add_div _ _ (by norm_num) hΛ0.ne', div_le_div_iff₀ (by positivity) (by positivity)]
      have a1 : ((hi : ℝ) - lo) * Λ' ≤ ((hi : ℝ) - lo) * (Real.log D + Λ) :=
        mul_le_mul_of_nonneg_left hΛ'D (by linarith)
      have a2 : (hi : ℝ) * Λ' ≤ hi * (Real.log D + Λ) := mul_le_mul_of_nonneg_left hΛ'D hhi0
      have a3 : ((hi : ℝ) - lo) * Real.log D ≤ hi * Real.log D :=
        mul_le_mul_of_nonneg_right (by linarith) hlogD
      have a4 : (hi : ℝ) * Real.log D ≤ hi * Real.log D * Λ :=
        le_mul_of_one_le_right (mul_nonneg hhi0 hlogD) (by linarith)
      nlinarith [mul_le_mul_of_nonneg_right a1 hΛ0.le, mul_le_mul_of_nonneg_right a3 hΛ0.le,
        mul_le_mul_of_nonneg_left a2 hΛ0.le, mul_nonneg hhi0 hΛ0.le]
    linarith

/-- `ϑ(y, x; 6, r) = ∑_{y < p ≤ x, p ≡ r (6)} log p`. -/
noncomputable def primeLogSumSix (r : ℤ) (y x : ℝ) : ℝ :=
  ∑ p ∈ primesIoc ⌊y⌋₊ ⌊x⌋₊ 6 r, Real.log p

theorem primeLogSumSix_eq (r : ℤ) (y x : ℝ) :
    primeLogSumSix r y x = ∑ p ∈ primesIoc ⌊y⌋₊ ⌊x⌋₊ 6 r, Real.log p := (rfl)

theorem mem_primesIoc_floor {y x : ℝ} (hy : 0 ≤ y) {r : ℤ} {p : ℕ} :
    p ∈ primesIoc ⌊y⌋₊ ⌊x⌋₊ 6 r ↔ y < p ∧ (p : ℝ) ≤ x ∧ p.Prime ∧ (p : ℤ) ≡ r [ZMOD 6] := by
  rw [mem_primesIoc, Nat.floor_lt hy]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hx : 0 ≤ x := by
      by_contra hx
      rw [Nat.floor_of_nonpos (by linarith)] at h2
      have := h3.1.pos
      omega
    exact ⟨h1, (Nat.le_floor_iff hx).mp h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    have hx : 0 ≤ x := le_trans (Nat.cast_nonneg p) h2
    exact ⟨h1, (Nat.le_floor_iff hx).mpr h2, h3⟩

theorem primeLogSumSix_nonneg (r : ℤ) (y x : ℝ) : 0 ≤ primeLogSumSix r y x :=
  sum_nonneg fun p _ => Real.log_natCast_nonneg p

/-- **Prime number theorem in the classes modulo `6`, on intervals** (from [BMOR, Corollary 1.7]):
for fixed `0 < c ≤ 1`, uniformly for `c x ≤ y ≤ x`,
`∑_{y < p ≤ x, p ≡ r (6)} log p = (x - y)/2 + o(x)`. -/
theorem eventually_abs_primeLogSumSix_sub_le (hBMOR : BMORPrimeCountingBound) {r : ℤ}
    (hr : Int.gcd r 6 = 1) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, c * x ≤ y → y ≤ x →
      |primeLogSumSix r y x - (x - y) / 2| ≤ ε * x := by
  have hlogt : Tendsto (fun x : ℝ => Real.log (c / 2 * x)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_id.const_mul_atTop (by positivity))
  set K : ℝ := 2 * (Real.log (2 / c) + 1) / ε with hK
  filter_upwards [eventually_ge_atTop ((2 * 10 ^ 6 + 2) / c), hlogt.eventually_ge_atTop K,
    eventually_ge_atTop (1 / ε), eventually_gt_atTop 0] with x hx1 hx2 hx3 hx0 y hy1 hy2
  have hcx : 2 * 10 ^ 6 + 2 ≤ c * x := by
    rw [div_le_iff₀ hc] at hx1; linarith
  have hy0 : 0 ≤ y := by linarith
  set lo := ⌊y⌋₊ with hlo
  set hi := ⌊x⌋₊ with hhi
  have hlo1 : y - 1 < lo := Nat.sub_one_lt_floor y
  have hlo2 : (lo : ℝ) ≤ y := Nat.floor_le hy0
  have hhi1 : x - 1 < hi := Nat.sub_one_lt_floor x
  have hhi2 : (hi : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hlohalf : c / 2 * x ≤ lo := by linarith
  have hlo6 : 10 ^ 6 ≤ lo := by
    have : ((10 ^ 6 : ℕ) : ℝ) ≤ lo := by push_cast; linarith
    exact_mod_cast this
  have hlohi : lo ≤ hi := Nat.floor_le_floor (by linarith)
  have hD : (1 : ℝ) ≤ 2 / c := by rw [le_div_iff₀ hc]; linarith
  have hhiD : (hi : ℝ) ≤ 2 / c * lo := by
    calc (hi : ℝ) ≤ x := hhi2
      _ = 2 / c * (c / 2 * x) := by field_simp
      _ ≤ 2 / c * lo := mul_le_mul_of_nonneg_left hlohalf (by positivity)
  have hmain := abs_sum_log_primesIoc_six_sub_le hBMOR hr hlo6 hlohi hD hhiD
  rw [← primeLogSumSix_eq] at hmain
  have hlog1 : K ≤ Real.log lo :=
    hx2.trans (Real.log_le_log (by positivity) hlohalf)
  have hK0 : 0 < K := by
    have : 0 ≤ Real.log (2 / c) := Real.log_nonneg hD
    positivity
  have herr : (hi : ℝ) * (Real.log (2 / c) + 1) / Real.log lo ≤ ε * x / 2 := by
    have hL : 0 < Real.log lo := hK0.trans_le hlog1
    rw [div_le_iff₀ hL]
    have h1 : (hi : ℝ) * (Real.log (2 / c) + 1) ≤ x * (Real.log (2 / c) + 1) :=
      mul_le_mul_of_nonneg_right hhi2 (by linarith [Real.log_nonneg hD])
    have h2 : x * (Real.log (2 / c) + 1) = ε * x / 2 * K := by
      rw [hK]; field_simp
    have h3 : ε * x / 2 * K ≤ ε * x / 2 * Real.log lo :=
      mul_le_mul_of_nonneg_left hlog1 (by positivity)
    linarith
  have hεx : 1 ≤ ε * x := by
    rw [div_le_iff₀ hε] at hx3; linarith
  rw [abs_le] at hmain ⊢
  constructor <;> linarith [hmain.1, hmain.2]

end ArithmeticOfJacobiPolynomials

/-!
## Summing indicator functions over windows of primes

The interval reduction in the proof of Proposition 4.5: for a prime `p` with `ℓ = ⌊n/p⌋`, the
condition `{n/p} ∈ [u, v)` places `p` in the window `(n/(ℓ+v), n/(ℓ+u)]`.

* `sum_mul_log_le_of_windows`, `sum_windows_le_sum_mul_log`: upper and lower bounds of
  `∑ f(p) log p` by sums of `ϑ(·; 6, r)` over windows;
* `eventually_abs_primeLogSumSix_window_sub_le`: the prime number theorem on one window;
* `mem_window_of_mod`, `mod_of_mem_window`: windows versus `n mod p`.
-/

namespace ArithmeticOfJacobiPolynomials

open Filter Topology Finset

/-- **Upper bound by windows**: if every prime `p ∈ S` with `f p ≠ 0` is `≤ z` or lies in one of
the windows `(lo i, hi i]` of class `r i` modulo `6`, then
`∑_{p ∈ S} f p log p ≤ ϑ(z) + ∑_i ϑ(lo i, hi i; 6, r i)` (for `0 ≤ f ≤ 1`). -/
theorem sum_mul_log_le_of_windows {S : Finset ℕ} {f : ℕ → ℝ}
    (hf1 : ∀ p ∈ S, f p ≤ 1) (hS : ∀ p ∈ S, p.Prime) {ι : Type*} (I : Finset ι)
    (r : ι → ℤ) (lo hi : ι → ℝ) (hlo : ∀ i, 0 ≤ lo i) (z : ℝ)
    (hcover : ∀ p ∈ S, f p ≠ 0 → (p : ℝ) ≤ z ∨
      ∃ i ∈ I, (p : ℤ) ≡ r i [ZMOD 6] ∧ lo i < p ∧ (p : ℝ) ≤ hi i) :
    ∑ p ∈ S, f p * Real.log p ≤
      Chebyshev.theta z + ∑ i ∈ I, primeLogSumSix (r i) (lo i) (hi i) := by
  classical
  set g0 : ℕ → ℝ := fun p => if (p : ℝ) ≤ z then Real.log p else 0 with hg0
  set g : ι → ℕ → ℝ := fun i p =>
    if (p : ℤ) ≡ r i [ZMOD 6] ∧ lo i < p ∧ (p : ℝ) ≤ hi i then Real.log p else 0 with hg
  have hg0n : ∀ p, 0 ≤ g0 p := fun p => by
    simp only [hg0]; split_ifs <;> simp [Real.log_natCast_nonneg]
  have hgn : ∀ i p, 0 ≤ g i p := fun i p => by
    simp only [hg]; split_ifs <;> simp [Real.log_natCast_nonneg]
  have hpt : ∀ p ∈ S, f p * Real.log p ≤ g0 p + ∑ i ∈ I, g i p := by
    intro p hp
    have hlog := Real.log_natCast_nonneg p
    by_cases hfp : f p = 0
    · rw [hfp, zero_mul]
      exact add_nonneg (hg0n p) (sum_nonneg fun i _ => hgn i p)
    have hfl : f p * Real.log p ≤ Real.log p := by
      have := hf1 p hp; nlinarith
    rcases hcover p hp hfp with hz | ⟨i, hi, hc⟩
    · have : g0 p = Real.log p := by simp only [hg0, hz, ↓reduceIte]
      linarith [sum_nonneg fun i (_ : i ∈ I) => hgn i p]
    · have h1 : g i p = Real.log p := by simp only [hg, hc, and_self, ↓reduceIte]
      have h2 : g i p ≤ ∑ j ∈ I, g j p :=
        single_le_sum (f := fun j => g j p) (fun j _ => hgn j p) hi
      linarith [hg0n p]
  refine (sum_le_sum hpt).trans ?_
  rw [sum_add_distrib, sum_comm]
  apply add_le_add
  · rw [Chebyshev.theta]
    simp only [hg0]
    rw [← sum_filter]
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [mem_filter] at hp ⊢
      refine ⟨mem_Ioc.mpr ⟨(hS p hp.1).pos, ?_⟩, hS p hp.1⟩
      have hz : 0 ≤ z := le_trans (Nat.cast_nonneg p) hp.2
      exact (Nat.le_floor_iff hz).mpr hp.2
    · intro p _ _; exact Real.log_natCast_nonneg p
  · refine sum_le_sum fun i _ => ?_
    simp only [hg]
    rw [← sum_filter, primeLogSumSix_eq]
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [mem_filter] at hp
      exact (mem_primesIoc_floor (hlo i)).mpr ⟨hp.2.2.1, hp.2.2.2, hS p hp.1, hp.2.1⟩
    · intro p _ _; exact Real.log_natCast_nonneg p

/-- **Lower bound by windows**: if the windows `(lo i, hi i]` of class `r i` modulo `6` are
pairwise disjoint (on primes) and every prime in a window lies in `S` with `f p = 1`, then
`∑_i ϑ(lo i, hi i; 6, r i) ≤ ∑_{p ∈ S} f p log p` (for `f ≥ 0`). -/
theorem sum_windows_le_sum_mul_log {S : Finset ℕ} {f : ℕ → ℝ} (hf0 : ∀ p ∈ S, 0 ≤ f p)
    {ι : Type*} (I : Finset ι) (r : ι → ℤ) (lo hi : ι → ℝ) (hlo : ∀ i, 0 ≤ lo i)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, ∀ p : ℕ, p.Prime → (p : ℤ) ≡ r i [ZMOD 6] → lo i < p →
      (p : ℝ) ≤ hi i → (p : ℤ) ≡ r j [ZMOD 6] → lo j < p → (p : ℝ) ≤ hi j → i = j)
    (hin : ∀ i ∈ I, ∀ p : ℕ, p.Prime → (p : ℤ) ≡ r i [ZMOD 6] → lo i < p → (p : ℝ) ≤ hi i →
      p ∈ S ∧ f p = 1) :
    ∑ i ∈ I, primeLogSumSix (r i) (lo i) (hi i) ≤ ∑ p ∈ S, f p * Real.log p := by
  classical
  set P : ι → Finset ℕ := fun i => primesIoc ⌊lo i⌋₊ ⌊hi i⌋₊ 6 (r i) with hP
  have hmem : ∀ i p, p ∈ P i ↔ lo i < p ∧ (p : ℝ) ≤ hi i ∧ p.Prime ∧ (p : ℤ) ≡ r i [ZMOD 6] :=
    fun i p => mem_primesIoc_floor (hlo i)
  have hpd : (I : Set ι).PairwiseDisjoint P := by
    intro i hi j hj hij
    rw [Function.onFun, Finset.disjoint_left]
    intro p hpi hpj
    obtain ⟨a1, a2, a3, a4⟩ := (hmem i p).mp hpi
    obtain ⟨b1, b2, -, b4⟩ := (hmem j p).mp hpj
    exact hij (hdisj i hi j hj p a3 a4 a1 a2 b4 b1 b2)
  have hsum : ∑ i ∈ I, primeLogSumSix (r i) (lo i) (hi i) =
      ∑ p ∈ I.biUnion P, Real.log p := by
    rw [sum_biUnion hpd]
    simp only [hP, primeLogSumSix_eq]
  have hsub : I.biUnion P ⊆ S := by
    intro p hp
    obtain ⟨i, hi, hpi⟩ := mem_biUnion.mp hp
    obtain ⟨a1, a2, a3, a4⟩ := (hmem i p).mp hpi
    exact (hin i hi p a3 a4 a1 a2).1
  have hf : ∀ p ∈ I.biUnion P, f p * Real.log p = Real.log p := by
    intro p hp
    obtain ⟨i, hi, hpi⟩ := mem_biUnion.mp hp
    obtain ⟨a1, a2, a3, a4⟩ := (hmem i p).mp hpi
    rw [(hin i hi p a3 a4 a1 a2).2, one_mul]
  rw [hsum, ← sum_congr rfl hf]
  exact sum_le_sum_of_subset_of_nonneg hsub fun p hp _ =>
    mul_nonneg (hf0 p hp) (Real.log_natCast_nonneg p)

/-- The prime number theorem in the classes modulo `6` on the window `(n/B, n/A]`. -/
theorem eventually_abs_primeLogSumSix_window_sub_le (hBMOR : BMORPrimeCountingBound) {r : ℤ}
    (hr : Int.gcd r 6 = 1) {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      |primeLogSumSix r (n / B) (n / A) - ((n : ℝ) / A - n / B) / 2| ≤ ε * n := by
  have hB : 0 < B := hA.trans_le hAB
  have h := eventually_abs_primeLogSumSix_sub_le hBMOR hr (c := A / B) (by positivity)
    ((div_le_one hB).mpr hAB) (ε := ε * A) (by positivity)
  have ht : Tendsto (fun n : ℕ => (n : ℝ) / A) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const hA
  filter_upwards [ht.eventually h] with n hn
  have e1 : A / B * ((n : ℝ) / A) = n / B := by field_simp
  have h1 := hn (n / B) e1.le (div_le_div_of_nonneg_left (Nat.cast_nonneg n) hA hAB)
  have e2 : ε * A * ((n : ℝ) / A) = ε * n := by field_simp
  rwa [e2] at h1

/-! ### Windows and the fractional part `{n/p}` -/

/-- If `ℓ = ⌊n/p⌋` and `u p ≤ n mod p < v p` with `ℓ + u > 0`, then `n/(ℓ+v) < p ≤ n/(ℓ+u)`. -/
theorem mem_window_of_mod {n p : ℕ} (hp : 0 < p) {u v : ℝ} (hu : 0 < (n / p : ℕ) + u)
    (h1 : u * p ≤ (n % p : ℕ)) (h2 : ((n % p : ℕ) : ℝ) < v * p) :
    (n : ℝ) / ((n / p : ℕ) + v) < p ∧ (p : ℝ) ≤ n / ((n / p : ℕ) + u) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have e : (n : ℝ) = (n / p : ℕ) * p + (n % p : ℕ) := by
    have := Nat.div_add_mod' n p
    exact_mod_cast this.symm
  have hv : 0 < ((n / p : ℕ) : ℝ) + v := by
    have : (0 : ℝ) ≤ (n % p : ℕ) := Nat.cast_nonneg _
    have : 0 < v := by nlinarith
    positivity
  constructor
  · rw [div_lt_iff₀ hv]; nlinarith
  · rw [le_div_iff₀ hu]; nlinarith

/-- Conversely, for `0 ≤ u < v ≤ 1`, a prime of the window `(n/(ℓ+v), n/(ℓ+u)]` has
`⌊n/p⌋ = ℓ` and `u p ≤ n mod p < v p`. -/
theorem mod_of_mem_window {n p ℓ : ℕ} (hp : 0 < p) {u v : ℝ} (hu : 0 ≤ u) (huv : u < v)
    (hv : v ≤ 1)
    (hℓu : 0 < ℓ + u) (h1 : (n : ℝ) / (ℓ + v) < p) (h2 : (p : ℝ) ≤ n / (ℓ + u)) :
    n / p = ℓ ∧ u * p ≤ (n % p : ℕ) ∧ ((n % p : ℕ) : ℝ) < v * p := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hℓv : 0 < (ℓ : ℝ) + v := by linarith
  have a1 := (div_lt_iff₀ hℓv).mp h1
  have a2 := (le_div_iff₀ hℓu).mp h2
  have b1 : (ℓ : ℝ) * p ≤ n := by nlinarith
  have b2 : (n : ℝ) < (ℓ + 1) * p := by nlinarith
  have c1 : ℓ * p ≤ n := by exact_mod_cast b1
  have c2 : n < (ℓ + 1) * p := by exact_mod_cast b2
  have hq : n / p = ℓ := Nat.div_eq_of_lt_le c1 c2
  have e : (n : ℝ) = (n / p : ℕ) * p + (n % p : ℕ) := by
    have := Nat.div_add_mod' n p
    exact_mod_cast this.symm
  rw [hq] at e
  exact ⟨hq, by nlinarith, by nlinarith⟩

end ArithmeticOfJacobiPolynomials

/-!
## The single-level indicators of Proposition 4.5 by residue class

For a prime `p ≥ 13` the residues `a_p, b_p` of `λ/3, μ/2` satisfy `2 b_p = p + μ` and
`3 a_p = p + λ` in the class `p ≡ 3 + 2λ (mod 6)` (`a_p/p ≈ 1/3`), `3 a_p = 2p + λ` in the class
`p ≡ 3 - 2λ (mod 6)` (`a_p/p ≈ 2/3`). The lemmas `levelM_caseA`, `levelE_caseA`,
`levelM_caseB`, `levelE_caseB` give the table of the proof of Proposition 4.5 with exact
integer endpoint perturbations (`s = n mod p`):

| `a_p/p` | `e_p = 1` | `m_p = 1` |
|---|---|---|
| `1/3` | `[0,1/6) ∪ [1/2,2/3)` | `[2/3,1)` |
| `2/3` | `[1/3,1/2) ∪ [5/6,1)` | `[1/2,5/6)` |

Also `padicValNat_kzContent_le_log`: `v_p(g_n) ≤ ⌊log_p (12n+5)⌋` for `p ≥ 5` (from the
leading coefficient).
-/

namespace ArithmeticOfJacobiPolynomials

open Finset Polynomial

/-! ### The indicators at one level, in the two cases `3a = q + λ` and `3a = 2q + λ` -/

section Levels

variable {q a b s : ℕ} {l μ : ℤ}

theorem levelM_le_one (q a b s : ℕ) : levelM q a b s ≤ 1 := by
  rw [levelM_eq]; split_ifs <;> omega

theorem add_lt_of_caseA (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) (hq : 13 ≤ q)
    (ha : 3 * (a : ℤ) = q + l) (hb : 2 * (b : ℤ) = q + μ) : a + b < q := by
  rcases hl with rfl | rfl <;> rcases hμ with rfl | rfl <;> omega

/-- Case `a ≈ q/3`: `m_q = 1` forces `{n/q} ≥ 2/3 - O(1/q)` and is implied by
`{n/q} ≥ 2/3 + O(1/q)`. -/
theorem levelM_caseA (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) (hq : 13 ≤ q)
    (ha : 3 * (a : ℤ) = q + l) (hb : 2 * (b : ℤ) = q + μ) :
    (levelM q a b s = 1 → 2 * q ≤ 3 * s + 1) ∧ (2 * q + 1 ≤ 3 * s → levelM q a b s = 1) := by
  have hab := add_lt_of_caseA hl hμ hq ha hb
  rw [levelM_eq, carryInd_eq, Nat.div_eq_of_lt hab, Nat.mod_eq_of_lt hab]
  rcases hl with rfl | rfl <;> rcases hμ with rfl | rfl <;> constructor <;> intro h <;>
    split_ifs at h ⊢ <;> omega

/-- Case `a ≈ q/3`: `e_q = 1` forces `{n/q} ∈ [0, 1/6) ∪ [1/2, 2/3)` up to `O(1/q)`. -/
theorem levelE_caseA (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) (hq : 13 ≤ q)
    (ha : 3 * (a : ℤ) = q + l) (hb : 2 * (b : ℤ) = q + μ) (he : levelE q a b s = 1) :
    6 * s < q + 5 ∨ (q ≤ 2 * s + 1 ∧ 3 * s < 2 * q + 1) := by
  have hab := add_lt_of_caseA hl hμ hq ha hb
  simp only [levelE_eq, levelEta_eq, levelBStar_eq, levelM_eq, carryInd_eq] at he
  rw [Nat.div_eq_of_lt hab, Nat.mod_eq_of_lt hab] at he
  rcases hl with rfl | rfl <;> rcases hμ with rfl | rfl <;> split_ifs at he <;> omega

theorem add_bounds_of_caseB (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) (hq : 13 ≤ q)
    (ha : 3 * (a : ℤ) = 2 * q + l) (hb : 2 * (b : ℤ) = q + μ) :
    (a + b) / q = 1 ∧ (a + b) % q = a + b - q ∧ q ≤ a + b := by
  have h1 : q ≤ a + b := by rcases hl with rfl | rfl <;> rcases hμ with rfl | rfl <;> omega
  have h2 : a + b < 2 * q := by rcases hl with rfl | rfl <;> rcases hμ with rfl | rfl <;> omega
  refine ⟨Nat.div_eq_of_lt_le (by omega) (by omega), ?_, h1⟩
  rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]

/-- Case `a ≈ 2q/3`: `m_q = 1` forces `{n/q} ∈ [1/2, 5/6)` up to `O(1/q)`, and is implied by
`{n/q} ∈ [1/2, 5/6)` shrunk by `O(1/q)`. -/
theorem levelM_caseB (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) (hq : 13 ≤ q)
    (ha : 3 * (a : ℤ) = 2 * q + l) (hb : 2 * (b : ℤ) = q + μ) :
    (levelM q a b s = 1 → q ≤ 2 * s + 1 ∧ 6 * s < 5 * q + 5) ∧
      (q + 1 ≤ 2 * s ∧ 6 * s + 5 < 5 * q → levelM q a b s = 1) := by
  obtain ⟨h1, h2, h3⟩ := add_bounds_of_caseB hl hμ hq ha hb
  rw [levelM_eq, carryInd_eq, h1, h2]
  rcases hl with rfl | rfl <;> rcases hμ with rfl | rfl <;> constructor <;> intro h <;>
    split_ifs at h ⊢ <;> omega

/-- Case `a ≈ 2q/3`: `e_q = 1` forces `{n/q} ∈ [1/3, 1/2) ∪ [5/6, 1)` up to `O(1/q)`. -/
theorem levelE_caseB (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) (hq : 13 ≤ q)
    (ha : 3 * (a : ℤ) = 2 * q + l) (hb : 2 * (b : ℤ) = q + μ) (he : levelE q a b s = 1) :
    (q ≤ 3 * s + 1 ∧ 2 * s < q + 1) ∨ 5 * q ≤ 6 * s + 5 := by
  obtain ⟨h1, h2, h3⟩ := add_bounds_of_caseB hl hμ hq ha hb
  simp only [levelE_eq, levelEta_eq, levelBStar_eq, levelM_eq, carryInd_eq] at he
  rw [h1, h2] at he
  rcases hl with rfl | rfl <;> rcases hμ with rfl | rfl <;> split_ifs at he <;> omega

end Levels

/-! ### The residues `a_p`, `b_p` and the classes modulo `6` -/

section Residues

variable {p : ℕ} [hp : Fact p.Prime]

theorem kzResA_prime_cases {l : ℤ} (hl : l = 1 ∨ l = -1) (hp5 : 5 ≤ p) :
    3 * (kzResA l p : ℤ) = p + l ∨ 3 * (kzResA l p : ℤ) = 2 * p + l := by
  have hd := kzResA_dvd l hp5 1
  obtain ⟨h1, h2⟩ := kzResA_spec hl hp5 (h := 1) le_rfl
  rw [pow_one] at hd h1 h2
  obtain ⟨k, hk⟩ := hd
  push_cast at hk
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
  have ha1 : (1 : ℤ) ≤ kzResA l p := by exact_mod_cast h1
  have ha2 : (kzResA l p : ℤ) + 1 ≤ p := by exact_mod_cast h2
  have hl' : -1 ≤ l ∧ l ≤ 1 := by rcases hl with rfl | rfl <;> norm_num
  have hk0 : 0 < k := by
    by_contra hk0; push Not at hk0; nlinarith
  have hk3 : k < 3 := by
    by_contra hk3; push Not at hk3; nlinarith
  interval_cases k
  · left; linarith
  · right; linarith

theorem kzResB_prime_eq {μ : ℤ} (hμ : μ = 1 ∨ μ = -1) (hp5 : 5 ≤ p) :
    2 * (kzResB μ p : ℤ) = p + μ := by
  have hd := kzResB_dvd μ hp5 1
  obtain ⟨h1, h2⟩ := kzResB_spec hμ hp5 (h := 1) le_rfl
  rw [pow_one] at hd h1 h2
  obtain ⟨k, hk⟩ := hd
  push_cast at hk
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
  have ha1 : (1 : ℤ) ≤ kzResB μ p := by exact_mod_cast h1
  have ha2 : (kzResB μ p : ℤ) + 1 ≤ p := by exact_mod_cast h2
  have hl' : -1 ≤ μ ∧ μ ≤ 1 := by rcases hμ with rfl | rfl <;> norm_num
  have hk0 : 0 < k := by
    by_contra hk0; push Not at hk0; nlinarith
  have hk2 : k < 2 := by
    by_contra hk2; push Not at hk2; nlinarith
  interval_cases k
  linarith

omit hp in
theorem prime_mod_six {p : ℕ} (hpp : p.Prime) (hp5 : 5 ≤ p) :
    (p : ℤ) ≡ 1 [ZMOD 6] ∨ (p : ℤ) ≡ 5 [ZMOD 6] := by
  have h2 : ¬ 2 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hpp).mp h; omega
  have h3 : ¬ 3 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hpp).mp h; omega
  simp only [Int.ModEq]
  omega

/-- In the class `p ≡ 3 + 2λ (mod 6)`, `3 a_p = p + λ` (so `a_p/p ≈ 1/3`). -/
theorem kzResA_of_classA {l : ℤ} (hl : l = 1 ∨ l = -1) (hp5 : 5 ≤ p)
    (hc : (p : ℤ) ≡ 3 + 2 * l [ZMOD 6]) : 3 * (kzResA l p : ℤ) = p + l := by
  rcases kzResA_prime_cases hl hp5 with h | h
  · exact h
  · simp only [Int.ModEq] at hc
    rcases hl with rfl | rfl <;> omega

/-- In the class `p ≡ 3 - 2λ (mod 6)`, `3 a_p = 2p + λ` (so `a_p/p ≈ 2/3`). -/
theorem kzResA_of_classB {l : ℤ} (hl : l = 1 ∨ l = -1) (hp5 : 5 ≤ p)
    (hc : (p : ℤ) ≡ 3 - 2 * l [ZMOD 6]) : 3 * (kzResA l p : ℤ) = 2 * p + l := by
  rcases kzResA_prime_cases hl hp5 with h | h
  · simp only [Int.ModEq] at hc
    rcases hl with rfl | rfl <;> omega
  · exact h

omit hp in
theorem prime_classA_or_classB {l : ℤ} (hl : l = 1 ∨ l = -1) {p : ℕ} (hpp : p.Prime)
    (hp5 : 5 ≤ p) : (p : ℤ) ≡ 3 + 2 * l [ZMOD 6] ∨ (p : ℤ) ≡ 3 - 2 * l [ZMOD 6] := by
  have := prime_mod_six hpp hp5
  simp only [Int.ModEq] at this ⊢
  rcases hl with rfl | rfl <;> omega

theorem gcd_classA {l : ℤ} (hl : l = 1 ∨ l = -1) : Int.gcd (3 + 2 * l) 6 = 1 := by
  rcases hl with rfl | rfl <;> decide

theorem gcd_classB {l : ℤ} (hl : l = 1 ∨ l = -1) : Int.gcd (3 - 2 * l) 6 = 1 := by
  rcases hl with rfl | rfl <;> decide

theorem classA_ne_classB {l : ℤ} (hl : l = 1 ∨ l = -1) {x : ℤ} (h1 : x ≡ 3 + 2 * l [ZMOD 6])
    (h2 : x ≡ 3 - 2 * l [ZMOD 6]) : False := by
  simp only [Int.ModEq] at h1 h2
  rcases hl with rfl | rfl <;> omega

/-! ### The content valuation at small primes -/

theorem kzCoeffLevel_self_le_one (l μ : ℤ) (n q : ℕ) (hq : 0 < q) :
    kzCoeffLevel l μ n n q ≤ 1 := by
  rw [kzCoeffLevel_eq]
  have e := add_div_eq_div_add (n := n) (x := n + kzResA l q + kzResB μ q) hq
  have f := kz_div_add_le_div_add_one (X := n + kzResA l q + kzResB μ q) (m := n % q) hq
    (Nat.mod_lt n hq)
  simp only [Nat.sub_self, Nat.zero_div, zero_add, Nat.cast_zero]
  omega

/-- For `p ≥ 5`, `v_p(g_n) ≤ ⌊log_p (12n+5)⌋`. -/
theorem padicValNat_kzContent_le_log {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    (hp5 : 5 ≤ p) (n : ℕ) :
    padicValNat p (kzContent l μ n) ≤ Nat.log p (12 * n + 5) := by
  set H := Nat.log p (12 * n + 5) with hHdef
  have hH : 12 * n + 5 < p ^ (H + 1) := Nat.lt_pow_succ_log_self hp.out.one_lt _
  have hval := padicValRat_kzKappa_mul_coeff_eq_sum hl hμ hp5 (le_refl n) hH
  have hne := (padicValRat_kzKappa_mul_coeff hl hμ (le_refl n) p).1
  rw [← coeff_kzScaled hl hμ] at hne hval
  have hK0 : (kzScaled l μ n).coeff n ≠ 0 := fun h0 => hne (by rw [h0, Int.cast_zero])
  have hdvd : ((p : ℤ) ^ padicValNat p (kzContent l μ n)) ∣ (kzScaled l μ n).coeff n := by
    refine dvd_trans ?_ (content_dvd_coeff n)
    rw [← kzContent_intCast, ← Nat.cast_pow, Int.natCast_dvd_natCast]
    exact pow_padicValNat_dvd
  have h1 := ((padicValInt_dvd_iff _ _).mp hdvd).resolve_left hK0
  rw [padicValRat.of_int] at hval
  have hsum : ∑ h ∈ Icc 1 H, kzCoeffLevel l μ n n (p ^ h) ≤ H := by
    calc ∑ h ∈ Icc 1 H, kzCoeffLevel l μ n n (p ^ h) ≤ ∑ _h ∈ Icc 1 H, (1 : ℤ) :=
          sum_le_sum fun h _ => kzCoeffLevel_self_le_one l μ n _ (pow_pos hp.out.pos h)
      _ = H := by simp
  have h2 : ((padicValNat p (kzContent l μ n) : ℕ) : ℤ) ≤
      (padicValInt p ((kzScaled l μ n).coeff n) : ℤ) := by exact_mod_cast h1
  have h3 : (padicValNat p (kzContent l μ n) : ℤ) ≤ H := by linarith
  exact_mod_cast h3

end Residues

end ArithmeticOfJacobiPolynomials

/-!
## Proposition 4.5: proof

Conditional on [BMOR, Corollary 1.7] (`BMORPrimeCountingBound`, used for the modulus `6` only),
`kanekoZagierArithmeticAsymptotics` proves `KanekoZagierArithmeticAsymptotics`:
uniformly in the four families and in the factorization,
`log g_n = (π/(2√3) + o(1)) n` and `log R^{(6)} ≤ (43/20 - π/√3 + o(1)) k n`.

The proof follows the manuscript: primes `p ≤ √(12n+5)` contribute `O(√n log n)`
(`sum_filter_sq_le_sqrt_mul_log`, `eventually_sqrt_mul_log_le`); for larger primes there is one
level, and the indicators are those of the table (section above), with
endpoints perturbed by `O(1/p) ≤ δ`. Primes `p ≤ n/(L+1)` contribute at most
`ϑ(n/(L+1)) ≤ n log 4/(L+1)`; for `ℓ = ⌊n/p⌋ ≤ L` the prime number theorem in the classes
modulo `6` on the finitely many windows gives the partial sums of the two series
(`resultant_windows_le`, `content_windows_le`, `content_windows_ge`), whose values are
computed in the series section above. Main steps:

* `eventually_sum_kzBudget_le`: `∑_{5 ≤ p ≤ n} E_p(n) log p ≤ (43/20 - π/√3 + ε) n`;
* `eventually_log_kzContent_le`, `eventually_le_log_kzContent`: the two bounds for `log g_n`;
* `kanekoZagierArithmeticAsymptotics`: Proposition 4.5.
-/

namespace ArithmeticOfJacobiPolynomials

open Filter Topology Finset

/-! ### Window data -/

/-- Left ends `u` of the resultant windows `{n/p} ∈ [u, v)` (classes A, A, B, B). -/
noncomputable def resU (δ : ℝ) : Fin 4 → ℝ := ![0, 1 / 2 - δ, 1 / 3 - δ, 5 / 6 - δ]

/-- Right ends `v` of the resultant windows. -/
noncomputable def resV (δ : ℝ) : Fin 4 → ℝ := ![1 / 6 + δ, 2 / 3 + δ, 1 / 2 + δ, 1]

/-- Classes modulo `6` of the resultant windows. -/
def resR (l : ℤ) : Fin 4 → ℤ := ![3 + 2 * l, 3 + 2 * l, 3 - 2 * l, 3 - 2 * l]

/-- Left ends of the content windows (classes A, B); `t = δ` (enlarged) or `t = -δ`
(shrunk). -/
noncomputable def conU (t : ℝ) : Fin 2 → ℝ := ![2 / 3 - t, 1 / 2 - t]

/-- Right ends of the content windows. -/
noncomputable def conV (t : ℝ) : Fin 2 → ℝ := ![1, 5 / 6 + t]

/-- Classes modulo `6` of the content windows. -/
def conR (l : ℤ) : Fin 2 → ℤ := ![3 + 2 * l, 3 - 2 * l]

theorem inv_sub_inv_le_sixteen {a b : ℝ} (ha : 1 / 4 ≤ a) (hab : a ≤ b) :
    1 / a - 1 / b ≤ 16 * (b - a) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  rw [div_sub_div _ _ ha0.ne' hb0.ne', div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul ha (ha.trans hab) (by norm_num) ha0.le]

theorem three_div_eq_half_inv (t : ℝ) (j : ℝ) :
    3 / (6 * t + j) = 1 / (t + j / 6) / 2 := by
  have : 6 * t + j = 6 * (t + j / 6) := by ring
  rw [this]; field_simp; ring

theorem resultant_windows_le (k : ℕ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 12) :
    ∑ w : Fin 4, (1 / ((k + 1 : ℝ) + resU δ w) - 1 / ((k + 1 : ℝ) + resV δ w)) / 2 ≤
      resultantTerm (k + 1) + 48 * δ := by
  rw [Fin.sum_univ_four]
  simp only [resU, resV, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, add_zero]
  rw [resultantTerm_eq]
  push_cast
  generalize ht : (k : ℝ) + 1 = t
  have ht1 : 1 ≤ t := by rw [← ht]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have r0 : 3 / (6 * t) = 1 / t / 2 := by
    have := three_div_eq_half_inv t 0; simpa using this
  have r1 : 3 / (6 * t + 1) = 1 / (t + 1 / 6) / 2 := three_div_eq_half_inv t 1
  have r2 : 3 / (6 * t + 2) = 1 / (t + 1 / 3) / 2 := by
    rw [three_div_eq_half_inv t 2]; norm_num
  have r4 : 3 / (6 * t + 4) = 1 / (t + 2 / 3) / 2 := by
    rw [three_div_eq_half_inv t 4]; norm_num
  have r5 : 3 / (6 * t + 5) = 1 / (t + 5 / 6) / 2 := three_div_eq_half_inv t 5
  have r6 : 3 / (6 * t + 6) = 1 / (t + 1) / 2 := by
    rw [three_div_eq_half_inv t 6]; norm_num
  rw [r0, r1, r2, r4, r5, r6]
  have h1 := inv_sub_inv_le_sixteen (a := t + 1 / 6) (b := t + (1 / 6 + δ)) (by linarith)
    (by linarith)
  have h2 := inv_sub_inv_le_sixteen (a := t + 2 / 3) (b := t + (2 / 3 + δ)) (by linarith)
    (by linarith)
  have h3 := inv_sub_inv_le_sixteen (a := t + (1 / 3 - δ)) (b := t + 1 / 3) (by linarith)
    (by linarith)
  have h4 := inv_sub_inv_le_sixteen (a := t + (5 / 6 - δ)) (b := t + 5 / 6) (by linarith)
    (by linarith)
  have h5 := inv_sub_inv_le_sixteen (a := t + (1 / 2 - δ)) (b := t + (1 / 2 + δ)) (by linarith)
    (by linarith)
  linarith

theorem contentTerm_eq_half (k : ℕ) : contentTerm k =
    (1 / ((k : ℝ) + 1 / 2) + 1 / ((k : ℝ) + 2 / 3) - 1 / ((k : ℝ) + 5 / 6) -
      1 / ((k : ℝ) + 1)) / 2 := by
  rw [contentTerm_eq, three_div_eq_half_inv, three_div_eq_half_inv, three_div_eq_half_inv,
    three_div_eq_half_inv]
  norm_num
  ring

theorem content_windows_le (k : ℕ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 12) :
    ∑ w : Fin 2, (1 / ((k : ℝ) + conU δ w) - 1 / ((k : ℝ) + conV δ w)) / 2 ≤
      contentTerm k + 48 * δ := by
  rw [Fin.sum_univ_two, contentTerm_eq_half]
  simp only [conU, conV, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 := inv_sub_inv_le_sixteen (a := (k : ℝ) + (2 / 3 - δ)) (b := k + 2 / 3) (by linarith)
    (by linarith)
  have h2 := inv_sub_inv_le_sixteen (a := (k : ℝ) + (1 / 2 - δ)) (b := k + 1 / 2) (by linarith)
    (by linarith)
  have h3 := inv_sub_inv_le_sixteen (a := (k : ℝ) + 5 / 6) (b := k + (5 / 6 + δ)) (by linarith)
    (by linarith)
  linarith

theorem content_windows_ge (k : ℕ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 12) :
    contentTerm k - 48 * δ ≤
      ∑ w : Fin 2, (1 / ((k : ℝ) + conU (-δ) w) - 1 / ((k : ℝ) + conV (-δ) w)) / 2 := by
  rw [Fin.sum_univ_two, contentTerm_eq_half]
  simp only [conU, conV, Matrix.cons_val_zero, Matrix.cons_val_one, sub_neg_eq_add,
    ← sub_eq_add_neg]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 := inv_sub_inv_le_sixteen (a := (k : ℝ) + 2 / 3) (b := k + (2 / 3 + δ)) (by linarith)
    (by linarith)
  have h2 := inv_sub_inv_le_sixteen (a := (k : ℝ) + 1 / 2) (b := k + (1 / 2 + δ)) (by linarith)
    (by linarith)
  have h3 := inv_sub_inv_le_sixteen (a := (k : ℝ) + (5 / 6 - δ)) (b := k + 5 / 6) (by linarith)
    (by linarith)
  linarith

/-! ### Small primes -/

/-- Primes `p ≤ √M` contribute at most `√M log M` when each contributes `≤ ⌊log_p M⌋ log p`. -/
theorem sum_filter_sq_le_sqrt_mul_log {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {M : ℕ}
    (hM : 1 ≤ M) (g : ℕ → ℝ) (hg : ∀ p ∈ S, p * p ≤ M → g p ≤ (Nat.log p M : ℝ) * Real.log p) :
    ∑ p ∈ S.filter (fun p => p * p ≤ M), g p ≤ √(M : ℝ) * Real.log M := by
  have hterm : ∀ p ∈ S.filter (fun p => p * p ≤ M), g p ≤ Real.log M := by
    intro p hp
    obtain ⟨hpS, hpM⟩ := mem_filter.mp hp
    refine (hg p hpS hpM).trans ?_
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hS p hpS).pos
    rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    exact_mod_cast Nat.pow_log_le_self p (by omega : M ≠ 0)
  have hcard : ((S.filter (fun p => p * p ≤ M)).card : ℝ) ≤ √(M : ℝ) := by
    have hsub : S.filter (fun p => p * p ≤ M) ⊆ Icc 1 (Nat.sqrt M) := by
      intro p hp
      obtain ⟨hpS, hpM⟩ := mem_filter.mp hp
      exact mem_Icc.mpr ⟨(hS p hpS).one_lt.le, Nat.le_sqrt.mpr hpM⟩
    have := card_le_card hsub
    rw [Nat.card_Icc, Nat.add_sub_cancel] at this
    exact (by exact_mod_cast this : ((S.filter (fun p => p * p ≤ M)).card : ℝ) ≤
      (Nat.sqrt M : ℝ)).trans Real.nat_sqrt_le_real_sqrt
  have hlog : 0 ≤ Real.log M := Real.log_natCast_nonneg M
  calc ∑ p ∈ S.filter (fun p => p * p ≤ M), g p ≤
        ∑ _p ∈ S.filter (fun p => p * p ≤ M), Real.log M := sum_le_sum hterm
    _ = ((S.filter (fun p => p * p ≤ M)).card : ℝ) * Real.log M := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ √(M : ℝ) * Real.log M := mul_le_mul_of_nonneg_right hcard hlog

/-- `√(12n+5) log(12n+5) = o(n)`. -/
theorem eventually_sqrt_mul_log_le {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, √((12 * n + 5 : ℕ) : ℝ) * Real.log ((12 * n + 5 : ℕ) : ℝ) ≤ η * n := by
  have hlo := (isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).bound
    (c := η / 17) (by positivity)
  have ht : Tendsto (fun n : ℕ => ((12 * n + 5 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (tendsto_atTop_mono (fun n => show n ≤ 12 * n + 5 by omega) tendsto_id)
  filter_upwards [ht.eventually hlo, eventually_ge_atTop 1] with n hn hn1
  set M : ℝ := ((12 * n + 5 : ℕ) : ℝ) with hMdef
  have hM0 : 0 ≤ M := Nat.cast_nonneg _
  have hM1 : 1 ≤ M := by rw [hMdef]; exact_mod_cast (by omega : 1 ≤ 12 * n + 5)
  have hlog0 : 0 ≤ Real.log M := Real.log_nonneg hM1
  rw [Real.norm_of_nonneg hlog0, Real.norm_of_nonneg (by positivity),
    ← Real.sqrt_eq_rpow] at hn
  have hsq : √M * √M = M := Real.mul_self_sqrt hM0
  have hMn : M ≤ 17 * n := by
    rw [hMdef]; push_cast
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    linarith
  calc √M * Real.log M ≤ √M * (η / 17 * √M) :=
        mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg _)
    _ = η / 17 * (√M * √M) := by ring
    _ = η / 17 * M := by rw [hsq]
    _ ≤ η / 17 * (17 * n) := mul_le_mul_of_nonneg_left hMn (by positivity)
    _ = η * n := by ring

/-! ### Window sums -/

theorem eventually_windows_abs_sub_le (hBMOR : BMORPrimeCountingBound) {ι : Type*}
    (I : Finset ι) (r : ι → ℤ) (hr : ∀ i ∈ I, Int.gcd (r i) 6 = 1) (A B : ι → ℝ)
    (hA : ∀ i ∈ I, 0 < A i) (hAB : ∀ i ∈ I, A i ≤ B i) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ i ∈ I,
      |primeLogSumSix (r i) (n / B i) (n / A i) - ((n : ℝ) / A i - n / B i) / 2| ≤ ε * n :=
  (eventually_all_finset I).mpr fun i hi =>
    eventually_abs_primeLogSumSix_window_sub_le hBMOR (hr i hi) (hA i hi) (hAB i hi) hε

theorem sum_windows_le_main {ι : Type*} (I : Finset ι) (θ A B : ι → ℝ) {n ε : ℝ}
    (h : ∀ i ∈ I, |θ i - (n / A i - n / B i) / 2| ≤ ε * n) :
    ∑ i ∈ I, θ i ≤ n * ∑ i ∈ I, (1 / A i - 1 / B i) / 2 + I.card * (ε * n) := by
  rw [mul_sum, ← nsmul_eq_mul, ← sum_const, ← sum_add_distrib]
  refine sum_le_sum fun i hi => ?_
  have := (abs_le.mp (h i hi)).2
  have e : n * ((1 / A i - 1 / B i) / 2) = (n / A i - n / B i) / 2 := by ring
  rw [e]; linarith

theorem main_le_sum_windows {ι : Type*} (I : Finset ι) (θ A B : ι → ℝ) {n ε : ℝ}
    (h : ∀ i ∈ I, |θ i - (n / A i - n / B i) / 2| ≤ ε * n) :
    n * ∑ i ∈ I, (1 / A i - 1 / B i) / 2 - I.card * (ε * n) ≤ ∑ i ∈ I, θ i := by
  rw [mul_sum, ← nsmul_eq_mul, ← sum_const, ← sum_sub_distrib]
  refine sum_le_sum fun i hi => ?_
  have := (abs_le.mp (h i hi)).1
  have e : n * ((1 / A i - 1 / B i) / 2) = (n / A i - n / B i) / 2 := by ring
  rw [e]; linarith

/-- A prime with `p² > 12n+5 ≥ K² + 1` exceeds `K`. -/
theorem lt_of_mul_self_gt {n p K : ℕ} (hnK : K * K + 1 ≤ n) (hpM : 12 * n + 5 < p * p) :
    K < p := by
  by_contra h
  push Not at h
  have := Nat.mul_self_le_mul_self h
  omega

theorem one_le_delta_mul {δ : ℝ} (hδ : 0 < δ) {p : ℕ} (hp : ⌈1 / δ⌉₊ + 13 < p) :
    1 ≤ δ * p := by
  have h1 : 1 / δ ≤ (⌈1 / δ⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : ((⌈1 / δ⌉₊ : ℕ) : ℝ) ≤ p := by exact_mod_cast (by omega : ⌈1 / δ⌉₊ ≤ p)
  rw [div_le_iff₀ hδ] at h1
  nlinarith

theorem theta_div_le {n : ℕ} {L : ℕ} {ε : ℝ} (hL : 4 * Real.log 4 / ε < L) (hε : 0 < ε) :
    Chebyshev.theta ((n : ℝ) / (L + 1)) ≤ ε / 4 * n := by
  have h := Chebyshev.theta_le_log4_mul_x (x := (n : ℝ) / (L + 1)) (by positivity)
  refine h.trans ?_
  have hL' : 4 * Real.log 4 < ε * L := by rw [div_lt_iff₀ hε] at hL; linarith
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith

/-! ### The resultant estimate -/

/-- **Proposition 4.5, resultant part, fixed family**:
`∑_{5 ≤ p ≤ n} E_p(n) log p ≤ (43/20 - π/√3 + ε) n` for large `n`. -/
theorem eventually_sum_kzBudget_le (hBMOR : BMORPrimeCountingBound) {l μ : ℤ}
    (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∑ p ∈ (Icc 5 n).filter Nat.Prime, (kzBudget l μ n p : ℝ) * Real.log p ≤
      (43 / 20 - Real.pi / √3 + ε) * n := by
  obtain ⟨L, hL⟩ : ∃ L : ℕ, 4 * Real.log 4 / ε < L := exists_nat_gt _
  set δ : ℝ := min (1 / 12) (ε / (4 * 48 * (L + 1))) with hδdef
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ12 : δ ≤ 1 / 12 := min_le_left _ _
  have hδL : 48 * δ * L ≤ ε / 4 := by
    have h1 : δ ≤ ε / (4 * 48 * (L + 1)) := min_le_right _ _
    have h2 : 48 * δ * (L + 1) ≤ ε / 4 := by
      rw [le_div_iff₀ (by positivity)] at h1
      nlinarith
    nlinarith
  set ε' : ℝ := ε / (16 * (L + 1)) with hε'def
  have hε'0 : 0 < ε' := by positivity
  set K : ℕ := ⌈1 / δ⌉₊ + 13 with hKdef
  set I : Finset (ℕ × Fin 4) := range L ×ˢ univ with hIdef
  set A : ℕ × Fin 4 → ℝ := fun i => (i.1 + 1 : ℝ) + resU δ i.2 with hAdef
  set B : ℕ × Fin 4 → ℝ := fun i => (i.1 + 1 : ℝ) + resV δ i.2 with hBdef
  set r : ℕ × Fin 4 → ℤ := fun i => resR l i.2 with hrdef
  have hU0 : ∀ w, 0 ≤ resU δ w := by
    intro w; fin_cases w <;> simp [resU] <;> linarith
  have hUV : ∀ w, resU δ w ≤ resV δ w := by
    intro w; fin_cases w <;> simp [resU, resV] <;> linarith
  have hApos : ∀ i, 0 < A i := fun i => by
    have := hU0 i.2; simp only [hAdef]; positivity
  have hAB : ∀ i, A i ≤ B i := fun i => by
    simp only [hAdef, hBdef]; linarith [hUV i.2]
  have hBpos : ∀ i, 0 < B i := fun i => (hApos i).trans_le (hAB i)
  have hrgcd : ∀ i ∈ I, Int.gcd (r i) 6 = 1 := by
    rintro ⟨k, w⟩ _; simp only [hrdef]
    fin_cases w <;> simp [resR, gcd_classA hl, gcd_classB hl]
  have hpnt := eventually_windows_abs_sub_le hBMOR I r hrgcd A B (fun i _ => hApos i)
    (fun i _ => hAB i) hε'0
  filter_upwards [hpnt, eventually_sqrt_mul_log_le (η := ε / 4) (by positivity),
    eventually_ge_atTop (K * K + 11)] with n hn hsq hnK
  have hn1 : 1 ≤ n := by omega
  set M := 12 * n + 5 with hMdef
  set S := (Icc 5 n).filter Nat.Prime with hSdef
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => (mem_filter.mp hp).2
  rw [← sum_filter_add_sum_filter_not S (fun p => p * p ≤ M)]
  -- small primes
  have hsmall : ∑ p ∈ S.filter (fun p => p * p ≤ M), (kzBudget l μ n p : ℝ) * Real.log p ≤
      √(M : ℝ) * Real.log M :=
    sum_filter_sq_le_sqrt_mul_log hSp (by omega) _ fun p hp _ => by
      obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
      have : Fact p.Prime := ⟨hpp⟩
      have h5 := (mem_Icc.mp hpI).1
      have hb := (kz_moment_content_budget hl hμ h5 hn1).2
      have hb' : (kzBudget l μ n p : ℝ) ≤ Nat.log p M := by exact_mod_cast hb
      exact mul_le_mul_of_nonneg_right hb' (Real.log_natCast_nonneg p)
  -- large primes: a single level
  have hbig_eq : ∀ p ∈ S.filter (fun p => ¬ p * p ≤ M),
      (kzBudget l μ n p : ℝ) = (kzLevelE l μ n p : ℝ) := by
    intro p hp
    obtain ⟨hpS, hpM⟩ := mem_filter.mp hp
    obtain ⟨hpI, hpp⟩ := mem_filter.mp hpS
    have hpn := (mem_Icc.mp hpI).2
    have hlog : Nat.log p M = 1 := by
      rw [Nat.log_eq_iff (Or.inl one_ne_zero)]
      refine ⟨by rw [pow_one]; omega, ?_⟩
      rw [show 1 + 1 = 2 by rfl, pow_two]; omega
    rw [kzBudget_eq, ← hMdef, hlog, Icc_self, sum_singleton, pow_one]
  have hbig : ∑ p ∈ S.filter (fun p => ¬ p * p ≤ M), (kzBudget l μ n p : ℝ) * Real.log p ≤
      Chebyshev.theta ((n : ℝ) / (L + 1)) +
        ∑ i ∈ I, primeLogSumSix (r i) (n / B i) (n / A i) := by
    refine sum_mul_log_le_of_windows ?_ (fun p hp => hSp p (mem_filter.mp hp).1) I r
      (fun i => (n : ℝ) / B i) (fun i => (n : ℝ) / A i)
      (fun i => div_nonneg (Nat.cast_nonneg _) (hBpos i).le) _ ?_
    · intro p hp
      rw [hbig_eq p hp]
      obtain ⟨hpS, -⟩ := mem_filter.mp hp
      obtain ⟨hpI, hpp⟩ := mem_filter.mp hpS
      have : Fact p.Prime := ⟨hpp⟩
      have h := (kzLevelE_mem hl hμ (mem_Icc.mp hpI).1 (h := 1) le_rfl n).1
      rw [pow_one] at h
      rcases h with h | h <;> rw [h] <;> norm_num
    · intro p hp hne
      rw [hbig_eq p hp] at hne
      obtain ⟨hpS, hpM⟩ := mem_filter.mp hp
      obtain ⟨hpI, hpp⟩ := mem_filter.mp hpS
      have : Fact p.Prime := ⟨hpp⟩
      have h5 := (mem_Icc.mp hpI).1
      have hpn := (mem_Icc.mp hpI).2
      have hpM' : 12 * n + 5 < p * p := by
        simp only [hMdef, not_le] at hpM; exact hpM
      have hKp : K < p := lt_of_mul_self_gt (K := K) (n := n) (p := p) (by omega) hpM'
      have hδp : 1 ≤ δ * p := one_le_delta_mul hδ0 hKp
      have hp13 : 13 ≤ p := by omega
      have hp0 : 0 < p := by omega
      have he : kzLevelE l μ n p = 1 := by
        have h := (kzLevelE_mem hl hμ h5 (h := 1) le_rfl n).1
        rw [pow_one] at h
        rcases h with h | h
        · rw [h] at hne; norm_num at hne
        · exact h
      rw [kzLevelE_eq] at he
      by_cases hz : (p : ℝ) ≤ n / (L + 1)
      · exact Or.inl hz
      right
      push Not at hz
      have hlt : n < (L + 1) * p := by
        rw [div_lt_iff₀ (by positivity)] at hz
        have : (n : ℝ) < ((L + 1) * p : ℕ) := by push_cast; linarith
        exact_mod_cast this
      have hℓL : n / p ≤ L := Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hp0).mpr hlt)
      have hℓ1 : 1 ≤ n / p := (Nat.one_le_div_iff hp0).mpr hpn
      have hk : ((n / p - 1 : ℕ) : ℝ) + 1 = ((n / p : ℕ) : ℝ) := by
        have : n / p - 1 + 1 = n / p := by omega
        exact_mod_cast this
      have hkL : n / p - 1 ∈ range L := mem_range.mpr (by omega)
      have hs : n % p < p := Nat.mod_lt _ hp0
      have hb := kzResB_prime_eq hμ h5
      have hwin : ∀ w : Fin 4, (p : ℤ) ≡ resR l w [ZMOD 6] → resU δ w * p ≤ ((n % p : ℕ) : ℝ) →
          ((n % p : ℕ) : ℝ) < resV δ w * p → ∃ i ∈ I, (p : ℤ) ≡ r i [ZMOD 6] ∧
            (n : ℝ) / B i < p ∧ (p : ℝ) ≤ n / A i := by
        intro w hcw h1 h2
        have hu : 0 < ((n / p : ℕ) : ℝ) + resU δ w := by
          have := hU0 w
          have : (1 : ℝ) ≤ (n / p : ℕ) := by exact_mod_cast hℓ1
          linarith
        obtain ⟨w1, w2⟩ := mem_window_of_mod hp0 hu h1 h2
        refine ⟨(n / p - 1, w), mem_product.mpr ⟨hkL, mem_univ _⟩, hcw, ?_, ?_⟩
        · simp only [hBdef]; rw [hk]; exact w1
        · simp only [hAdef]; rw [hk]; exact w2
      have hsR : (0 : ℝ) ≤ ((n % p : ℕ) : ℝ) := Nat.cast_nonneg _
      have hsp : ((n % p : ℕ) : ℝ) < p := by exact_mod_cast hs
      rcases prime_classA_or_classB hl hpp h5 with hc | hc
      · have ha := kzResA_of_classA hl h5 hc
        rcases levelE_caseA hl hμ hp13 ha hb he with h1 | ⟨h1, h2⟩
        · have h1' : 6 * ((n % p : ℕ) : ℝ) < p + 5 := by exact_mod_cast h1
          exact hwin 0 (by simpa [resR] using hc) (by simp [resU])
            (by simp only [resV, Matrix.cons_val_zero]; linarith)
        · have h1' : (p : ℝ) ≤ 2 * ((n % p : ℕ) : ℝ) + 1 := by exact_mod_cast h1
          have h2' : 3 * ((n % p : ℕ) : ℝ) < 2 * p + 1 := by exact_mod_cast h2
          exact hwin 1 (by simpa [resR] using hc)
            (by simp only [resU, Matrix.cons_val_one, Matrix.cons_val_zero]; linarith)
            (by simp only [resV, Matrix.cons_val_one, Matrix.cons_val_zero]; linarith)
      · have ha := kzResA_of_classB hl h5 hc
        rcases levelE_caseB hl hμ hp13 ha hb he with ⟨h1, h2⟩ | h1
        · have h1' : (p : ℝ) ≤ 3 * ((n % p : ℕ) : ℝ) + 1 := by exact_mod_cast h1
          have h2' : 2 * ((n % p : ℕ) : ℝ) < p + 1 := by exact_mod_cast h2
          exact hwin 2 (by simpa [resR] using hc)
            (by simp only [resU, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons];
                linarith)
            (by simp only [resV, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons];
                linarith)
        · have h1' : 5 * (p : ℝ) ≤ 6 * ((n % p : ℕ) : ℝ) + 5 := by exact_mod_cast h1
          exact hwin 3 (by simpa [resR] using hc)
            (by simp only [resU, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons];
                linarith)
            (by simp only [resV, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons];
                linarith)
  -- the main terms
  have hθ := theta_div_le (n := n) hL hε
  have hwsum := sum_windows_le_main I (fun i => primeLogSumSix (r i) (n / B i) (n / A i)) A B hn
  have hmain : ∑ i ∈ I, (1 / A i - 1 / B i) / 2 ≤ (43 / 20 - Real.pi / √3) + 48 * δ * L := by
    rw [hIdef, sum_product]
    calc ∑ k ∈ range L, ∑ w : Fin 4, (1 / A (k, w) - 1 / B (k, w)) / 2 ≤
          ∑ k ∈ range L, (resultantTerm (k + 1) + 48 * δ) :=
          sum_le_sum fun k _ => resultant_windows_le k hδ0.le hδ12
      _ = ∑ k ∈ range L, resultantTerm (k + 1) + 48 * δ * L := by
          rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]; ring
      _ ≤ (43 / 20 - Real.pi / √3) + 48 * δ * L := by
          linarith [sum_resultantTerm_le L]
  have hcard : (I.card : ℝ) = 4 * L := by
    rw [hIdef, card_product, card_range, card_univ, Fintype.card_fin]; push_cast; ring
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hε'L : 4 * L * ε' ≤ ε / 4 := by
    rw [hε'def, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have k1 := mul_le_mul_of_nonneg_left hmain hn0
  have k2 := mul_le_mul_of_nonneg_right hε'L hn0
  rw [hcard] at hwsum
  have hsq' : √(M : ℝ) * Real.log M ≤ ε / 4 * n := hsq
  nlinarith

/-! ### The content -/

/-- `log g_n = ∑_{5 ≤ p ≤ 12n+5} v_p(g_n) log p`. -/
theorem log_kzContent_eq_sum {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) (n : ℕ) :
    Real.log (kzContent l μ n) = ∑ p ∈ (Icc 5 (12 * n + 5)).filter Nat.Prime,
      (padicValNat p (kzContent l μ n) : ℝ) * Real.log p := by
  set g := kzContent l μ n with hg
  have hg0 : g ≠ 0 := (kzContent_pos hl hμ n).ne'
  have hcop : Nat.Coprime g 6 := coprime_kzContent_six hl hμ n
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
  have hsub : g.primeFactors ⊆ (Icc 5 (12 * n + 5)).filter Nat.Prime := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have : Fact p.Prime := ⟨hpp⟩
    have h2 : p ≠ 2 := by
      rintro rfl
      have := Nat.Coprime.coprime_dvd_left hpd hcop
      norm_num at this
    have h3 : p ≠ 3 := by
      rintro rfl
      have := Nat.Coprime.coprime_dvd_left hpd hcop
      norm_num at this
    have h5 : 5 ≤ p := by
      have := hpp.two_le
      have h4 : p ≠ 4 := by
        rintro rfl; exact absurd hpp (by decide)
      omega
    have hv1 : 1 ≤ padicValNat p g := one_le_padicValNat_of_dvd hg0 hpd
    have hvle := padicValNat_kzContent_le_log hl hμ h5 n
    rw [← hg] at hvle
    have hpM : p ≤ 12 * n + 5 := by
      have := Nat.pow_log_le_self p (by omega : 12 * n + 5 ≠ 0)
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ Nat.log p (12 * n + 5) := Nat.pow_le_pow_right hpp.pos (by omega)
        _ ≤ 12 * n + 5 := this
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨h5, hpM⟩, hpp⟩
  rw [sum_subset hsub]
  · refine sum_congr rfl fun p hp => ?_
    rw [Nat.factorization_def g (mem_filter.mp hp).2]
  · intro p hp hpn
    have : g.factorization p = 0 := Finsupp.notMem_support_iff.mp
      (by rwa [Nat.support_factorization])
    rw [this, Nat.cast_zero, zero_mul]

/-- **Proposition 4.5, content upper bound, fixed family**: `log g_n ≤ (π/(2√3) + ε) n`. -/
theorem eventually_log_kzContent_le (hBMOR : BMORPrimeCountingBound) {l μ : ℤ}
    (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Real.log (kzContent l μ n) ≤ (Real.pi / (2 * √3) + ε) * n := by
  obtain ⟨L, hL⟩ : ∃ L : ℕ, 4 * Real.log 4 / ε < L := exists_nat_gt _
  set δ : ℝ := min (1 / 12) (ε / (4 * 48 * (L + 1))) with hδdef
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ12 : δ ≤ 1 / 12 := min_le_left _ _
  have hδL : 48 * δ * (L + 1) ≤ ε / 4 := by
    have h1 : δ ≤ ε / (4 * 48 * (L + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  set ε' : ℝ := ε / (8 * (L + 1)) with hε'def
  have hε'0 : 0 < ε' := by positivity
  set K : ℕ := ⌈1 / δ⌉₊ + 13 with hKdef
  set I : Finset (ℕ × Fin 2) := range (L + 1) ×ˢ univ with hIdef
  set A : ℕ × Fin 2 → ℝ := fun i => (i.1 : ℝ) + conU δ i.2 with hAdef
  set B : ℕ × Fin 2 → ℝ := fun i => (i.1 : ℝ) + conV δ i.2 with hBdef
  set r : ℕ × Fin 2 → ℤ := fun i => conR l i.2 with hrdef
  have hU0 : ∀ w, 1 / 4 ≤ conU δ w := by
    intro w; fin_cases w <;> simp [conU] <;> linarith
  have hUV : ∀ w, conU δ w ≤ conV δ w := by
    intro w; fin_cases w <;> simp [conU, conV] <;> linarith
  have hApos : ∀ i, 0 < A i := fun i => by
    have := hU0 i.2; simp only [hAdef]; positivity
  have hAB : ∀ i, A i ≤ B i := fun i => by
    simp only [hAdef, hBdef]; linarith [hUV i.2]
  have hBpos : ∀ i, 0 < B i := fun i => (hApos i).trans_le (hAB i)
  have hrgcd : ∀ i ∈ I, Int.gcd (r i) 6 = 1 := by
    rintro ⟨k, w⟩ _; simp only [hrdef]
    fin_cases w <;> simp [conR, gcd_classA hl, gcd_classB hl]
  have hpnt := eventually_windows_abs_sub_le hBMOR I r hrgcd A B (fun i _ => hApos i)
    (fun i _ => hAB i) hε'0
  filter_upwards [hpnt, eventually_sqrt_mul_log_le (η := ε / 4) (by positivity),
    eventually_ge_atTop (K * K + 11)] with n hn hsq hnK
  have hn1 : 1 ≤ n := by omega
  set M := 12 * n + 5 with hMdef
  set S := (Icc 5 M).filter Nat.Prime with hSdef
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => (mem_filter.mp hp).2
  rw [log_kzContent_eq_sum hl hμ n, ← hMdef, ← hSdef,
    ← sum_filter_add_sum_filter_not S (fun p => p * p ≤ M)]
  have hsmall : ∑ p ∈ S.filter (fun p => p * p ≤ M),
      (padicValNat p (kzContent l μ n) : ℝ) * Real.log p ≤ √(M : ℝ) * Real.log M :=
    sum_filter_sq_le_sqrt_mul_log hSp (by omega) _ fun p hp _ => by
      obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
      have : Fact p.Prime := ⟨hpp⟩
      have h5 := (mem_Icc.mp hpI).1
      have hb := padicValNat_kzContent_le_log hl hμ h5 n
      have hb' : (padicValNat p (kzContent l μ n) : ℝ) ≤ Nat.log p M := by exact_mod_cast hb
      exact mul_le_mul_of_nonneg_right hb' (Real.log_natCast_nonneg p)
  have hbig_eq : ∀ p ∈ S.filter (fun p => ¬ p * p ≤ M),
      (padicValNat p (kzContent l μ n) : ℝ) = (kzLevelM l μ n p : ℝ) := by
    intro p hp
    obtain ⟨hpS, hpM⟩ := mem_filter.mp hp
    obtain ⟨hpI, hpp⟩ := mem_filter.mp hpS
    have : Fact p.Prime := ⟨hpp⟩
    have hpM' : 12 * n + 5 < p ^ 2 := by
      simp only [hMdef, not_le] at hpM; rw [pow_two]; exact hpM
    rw [padicValNat_kzContent_eq_kzLevelM hl hμ (mem_Icc.mp hpI).1 n hpM']
  have hbig : ∑ p ∈ S.filter (fun p => ¬ p * p ≤ M),
      (padicValNat p (kzContent l μ n) : ℝ) * Real.log p ≤
      Chebyshev.theta ((n : ℝ) / (L + 1)) +
        ∑ i ∈ I, primeLogSumSix (r i) (n / B i) (n / A i) := by
    refine sum_mul_log_le_of_windows ?_ (fun p hp => hSp p (mem_filter.mp hp).1) I r
      (fun i => (n : ℝ) / B i) (fun i => (n : ℝ) / A i)
      (fun i => div_nonneg (Nat.cast_nonneg _) (hBpos i).le) _ ?_
    · intro p hp
      rw [hbig_eq p hp, kzLevelM_eq]
      exact_mod_cast levelM_le_one _ _ _ _
    · intro p hp hne
      rw [hbig_eq p hp] at hne
      obtain ⟨hpS, hpM⟩ := mem_filter.mp hp
      obtain ⟨hpI, hpp⟩ := mem_filter.mp hpS
      have : Fact p.Prime := ⟨hpp⟩
      have h5 := (mem_Icc.mp hpI).1
      have hpM' : 12 * n + 5 < p * p := by
        simp only [hMdef, not_le] at hpM; exact hpM
      have hKp : K < p := lt_of_mul_self_gt (K := K) (n := n) (p := p) (by omega) hpM'
      have hδp : 1 ≤ δ * p := one_le_delta_mul hδ0 hKp
      have hp13 : 13 ≤ p := by omega
      have hp0 : 0 < p := by omega
      have he : kzLevelM l μ n p = 1 := by
        have := levelM_le_one p (kzResA l p) (kzResB μ p) (n % p)
        rw [kzLevelM_eq]
        have h0 : kzLevelM l μ n p ≠ 0 := by
          intro h; rw [h] at hne; norm_num at hne
        rw [kzLevelM_eq] at h0
        omega
      rw [kzLevelM_eq] at he
      by_cases hz : (p : ℝ) ≤ n / (L + 1)
      · exact Or.inl hz
      right
      push Not at hz
      have hlt : n < (L + 1) * p := by
        rw [div_lt_iff₀ (by positivity)] at hz
        have : (n : ℝ) < ((L + 1) * p : ℕ) := by push_cast; linarith
        exact_mod_cast this
      have hℓL : n / p ≤ L := Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hp0).mpr hlt)
      have hkL : n / p ∈ range (L + 1) := mem_range.mpr (by omega)
      have hs : n % p < p := Nat.mod_lt _ hp0
      have hb := kzResB_prime_eq hμ h5
      have hwin : ∀ w : Fin 2, (p : ℤ) ≡ conR l w [ZMOD 6] → conU δ w * p ≤ ((n % p : ℕ) : ℝ) →
          ((n % p : ℕ) : ℝ) < conV δ w * p → ∃ i ∈ I, (p : ℤ) ≡ r i [ZMOD 6] ∧
            (n : ℝ) / B i < p ∧ (p : ℝ) ≤ n / A i := by
        intro w hcw h1 h2
        have hu : 0 < ((n / p : ℕ) : ℝ) + conU δ w := by
          have := hU0 w
          have : (0 : ℝ) ≤ (n / p : ℕ) := Nat.cast_nonneg _
          linarith
        obtain ⟨w1, w2⟩ := mem_window_of_mod hp0 hu h1 h2
        exact ⟨(n / p, w), mem_product.mpr ⟨hkL, mem_univ _⟩, hcw, w1, w2⟩
      have hsp : ((n % p : ℕ) : ℝ) < p := by exact_mod_cast hs
      rcases prime_classA_or_classB hl hpp h5 with hc | hc
      · have ha := kzResA_of_classA hl h5 hc
        have h1 := (levelM_caseA hl hμ hp13 ha hb).1 he
        have h1' : 2 * (p : ℝ) ≤ 3 * ((n % p : ℕ) : ℝ) + 1 := by exact_mod_cast h1
        exact hwin 0 (by simpa [conR] using hc)
          (by simp only [conU, Matrix.cons_val_zero]; linarith)
          (by simp only [conV, Matrix.cons_val_zero]; linarith)
      · have ha := kzResA_of_classB hl h5 hc
        obtain ⟨h1, h2⟩ := (levelM_caseB hl hμ hp13 ha hb).1 he
        have h1' : (p : ℝ) ≤ 2 * ((n % p : ℕ) : ℝ) + 1 := by exact_mod_cast h1
        have h2' : 6 * ((n % p : ℕ) : ℝ) < 5 * p + 5 := by exact_mod_cast h2
        exact hwin 1 (by simpa [conR] using hc)
          (by simp only [conU, Matrix.cons_val_one, Matrix.cons_val_zero]; linarith)
          (by simp only [conV, Matrix.cons_val_one, Matrix.cons_val_zero]; linarith)
  have hθ := theta_div_le (n := n) hL hε
  have hwsum := sum_windows_le_main I (fun i => primeLogSumSix (r i) (n / B i) (n / A i)) A B hn
  have hmain : ∑ i ∈ I, (1 / A i - 1 / B i) / 2 ≤ Real.pi / (2 * √3) + 48 * δ * (L + 1) := by
    rw [hIdef, sum_product]
    calc ∑ k ∈ range (L + 1), ∑ w : Fin 2, (1 / A (k, w) - 1 / B (k, w)) / 2 ≤
          ∑ k ∈ range (L + 1), (contentTerm k + 48 * δ) :=
          sum_le_sum fun k _ => content_windows_le k hδ0.le hδ12
      _ = ∑ k ∈ range (L + 1), contentTerm k + 48 * δ * (L + 1) := by
          rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]; push_cast; ring
      _ ≤ Real.pi / (2 * √3) + 48 * δ * (L + 1) := by
          linarith [sum_contentTerm_le (L + 1)]
  have hcard : (I.card : ℝ) = 2 * (L + 1) := by
    rw [hIdef, card_product, card_range, card_univ, Fintype.card_fin]; push_cast; ring
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hε'L : 2 * (L + 1) * ε' ≤ ε / 4 := by
    rw [hε'def, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have k1 := mul_le_mul_of_nonneg_left hmain hn0
  have k2 := mul_le_mul_of_nonneg_right hε'L hn0
  have k3 := mul_le_mul_of_nonneg_right hδL hn0
  rw [hcard] at hwsum
  have hsq' : √(M : ℝ) * Real.log M ≤ ε / 4 * n := hsq
  nlinarith

/-- **Proposition 4.5, content lower bound, fixed family**: `(π/(2√3) - ε) n ≤ log g_n`. -/
theorem eventually_le_log_kzContent (hBMOR : BMORPrimeCountingBound) {l μ : ℤ}
    (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (Real.pi / (2 * √3) - ε) * n ≤ Real.log (kzContent l μ n) := by
  have hser : ∀ᶠ L : ℕ in atTop,
      Real.pi / (2 * √3) - ε / 4 < ∑ k ∈ range (L + 1), contentTerm k :=
    (tendsto_sum_contentTerm.comp (tendsto_add_atTop_nat 1)).eventually
      (lt_mem_nhds (by linarith))
  obtain ⟨L, hL⟩ := hser.exists
  set δ : ℝ := min (1 / 12) (ε / (4 * 48 * (L + 1))) with hδdef
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ12 : δ ≤ 1 / 12 := min_le_left _ _
  have hδL : 48 * δ * (L + 1) ≤ ε / 4 := by
    have h1 : δ ≤ ε / (4 * 48 * (L + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  set ε' : ℝ := ε / (8 * (L + 1)) with hε'def
  have hε'0 : 0 < ε' := by positivity
  set K : ℕ := ⌈1 / δ⌉₊ + 13 with hKdef
  set I : Finset (ℕ × Fin 2) := range (L + 1) ×ˢ univ with hIdef
  set A : ℕ × Fin 2 → ℝ := fun i => (i.1 : ℝ) + conU (-δ) i.2 with hAdef
  set B : ℕ × Fin 2 → ℝ := fun i => (i.1 : ℝ) + conV (-δ) i.2 with hBdef
  set r : ℕ × Fin 2 → ℤ := fun i => conR l i.2 with hrdef
  have hU0 : ∀ w, 1 / 2 ≤ conU (-δ) w := by
    intro w; fin_cases w <;> simp [conU] <;> linarith
  have hUV : ∀ w, conU (-δ) w < conV (-δ) w := by
    intro w; fin_cases w <;> simp [conU, conV] <;> linarith
  have hV1 : ∀ w, conV (-δ) w ≤ 1 := by
    intro w; fin_cases w
    · simp [conV]
    · simp [conV]; linarith
  have hApos : ∀ i, 0 < A i := fun i => by
    have := hU0 i.2; simp only [hAdef]; positivity
  have hAB : ∀ i, A i ≤ B i := fun i => by
    simp only [hAdef, hBdef]; linarith [hUV i.2]
  have hBpos : ∀ i, 0 < B i := fun i => (hApos i).trans_le (hAB i)
  have hrgcd : ∀ i ∈ I, Int.gcd (r i) 6 = 1 := by
    rintro ⟨k, w⟩ _; simp only [hrdef]
    fin_cases w <;> simp [conR, gcd_classA hl, gcd_classB hl]
  have hpnt := eventually_windows_abs_sub_le hBMOR I r hrgcd A B (fun i _ => hApos i)
    (fun i _ => hAB i) hε'0
  filter_upwards [hpnt, eventually_ge_atTop (17 * (L + 1) ^ 2 + (L + 1) * (K + 1) + 11)]
    with n hn hnL
  have hn1 : 1 ≤ n := by omega
  set M := 12 * n + 5 with hMdef
  set S := (Icc 5 M).filter Nat.Prime with hSdef
  rw [log_kzContent_eq_sum hl hμ n, ← hMdef, ← hSdef]
  -- primes in a window
  have hwin : ∀ i ∈ I, ∀ p : ℕ, p.Prime → (p : ℤ) ≡ r i [ZMOD 6] → (n : ℝ) / B i < p →
      (p : ℝ) ≤ n / A i → n / p = i.1 ∧ conU (-δ) i.2 * p ≤ ((n % p : ℕ) : ℝ) ∧
        ((n % p : ℕ) : ℝ) < conV (-δ) i.2 * p ∧ p ∈ S ∧ 12 * n + 5 < p * p ∧ K < p := by
    rintro ⟨k, w⟩ hi p hpp hc h1 h2
    have hk : k ≤ L := by have := (mem_product.mp hi).1; rw [mem_range] at this; omega
    have hp0 : 0 < p := hpp.pos
    have hu0 : 0 ≤ conU (-δ) w := by linarith [hU0 w]
    have hku : 0 < (k : ℝ) + conU (-δ) w := by
      have := hU0 w; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
    obtain ⟨e1, e2, e3⟩ := mod_of_mem_window hp0 hu0 (hUV w) (hV1 w) hku h1 h2
    refine ⟨e1, e2, e3, ?_⟩
    have hp0' : (0 : ℝ) < p := by exact_mod_cast hp0
    -- `n < (L+1) p`
    have hBle : B (k, w) ≤ L + 1 := by
      simp only [hBdef]
      have : (k : ℝ) ≤ L := by exact_mod_cast hk
      linarith [hV1 w]
    have hlt : n < (L + 1) * p := by
      have h1' := (div_lt_iff₀ (hBpos (k, w))).mp h1
      have h1'' : (p : ℝ) * B (k, w) ≤ p * (L + 1) := mul_le_mul_of_nonneg_left hBle hp0'.le
      have : (n : ℝ) < ((L + 1) * p : ℕ) := by
        push_cast
        linarith
      exact_mod_cast this
    -- `p ≤ 2n`
    have hp2n : p ≤ 2 * n := by
      have h2' := (le_div_iff₀ (hApos (k, w))).mp h2
      have hA : 1 / 2 ≤ A (k, w) := by
        simp only [hAdef]; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith [hU0 w]
      have h2'' : (p : ℝ) * (1 / 2) ≤ p * A (k, w) := mul_le_mul_of_nonneg_left hA hp0'.le
      have : (p : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have hKp : K < p := by
      have hle : (L + 1) * (K + 1) ≤ n := by omega
      have : (L + 1) * (K + 1) < (L + 1) * p := lt_of_le_of_lt hle hlt
      have := Nat.lt_of_mul_lt_mul_left this
      omega
    have hpM : 12 * n + 5 < p * p := by
      have hsq : n * n < ((L + 1) * p) * ((L + 1) * p) := Nat.mul_self_lt_mul_self hlt
      have h17 : 17 * (L + 1) ^ 2 ≤ n := by omega
      have h3a : (L + 1) ^ 2 * (12 * n + 5) ≤ (L + 1) ^ 2 * (17 * n) :=
        Nat.mul_le_mul_left _ (by omega)
      have h3b : (L + 1) ^ 2 * (17 * n) = 17 * (L + 1) ^ 2 * n := by ring
      have h3c : 17 * (L + 1) ^ 2 * n ≤ n * n := Nat.mul_le_mul_right n h17
      have h4e : ((L + 1) * p) * ((L + 1) * p) = (L + 1) ^ 2 * (p * p) := by ring
      have h4 : (L + 1) ^ 2 * (12 * n + 5) < (L + 1) ^ 2 * (p * p) := by
        rw [← h4e]; omega
      exact Nat.lt_of_mul_lt_mul_left h4
    have h5 : 5 ≤ p := by omega
    exact ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨h5, by omega⟩, hpp⟩, hpM, hKp⟩
  have hlower : ∑ i ∈ I, primeLogSumSix (r i) (n / B i) (n / A i) ≤
      ∑ p ∈ S, (padicValNat p (kzContent l μ n) : ℝ) * Real.log p := by
    refine sum_windows_le_sum_mul_log (fun p _ => Nat.cast_nonneg _) I r
      (fun i => (n : ℝ) / B i) (fun i => (n : ℝ) / A i)
      (fun i => div_nonneg (Nat.cast_nonneg _) (hBpos i).le) ?_ ?_
    · rintro ⟨k, w⟩ hi ⟨k', w'⟩ hi' p hpp hc h1 h2 hc' h1' h2'
      obtain ⟨e1, -⟩ := hwin _ hi p hpp hc h1 h2
      obtain ⟨e1', -⟩ := hwin _ hi' p hpp hc' h1' h2'
      have hkk : k = k' := by simp only at e1 e1'; omega
      subst hkk
      simp only [hrdef] at hc hc'
      fin_cases w <;> fin_cases w'
      · rfl
      · exact (classA_ne_classB hl (by simpa [conR] using hc) (by simpa [conR] using hc')).elim
      · exact (classA_ne_classB hl (by simpa [conR] using hc') (by simpa [conR] using hc)).elim
      · rfl
    · rintro ⟨k, w⟩ hi p hpp hc h1 h2
      obtain ⟨-, e2, e3, hpS, hpM, hKp⟩ := hwin _ hi p hpp hc h1 h2
      refine ⟨hpS, ?_⟩
      have : Fact p.Prime := ⟨hpp⟩
      have h5 : 5 ≤ p := by omega
      have hp13 : 13 ≤ p := by omega
      have hδp : 1 ≤ δ * p := one_le_delta_mul hδ0 hKp
      have hb := kzResB_prime_eq hμ h5
      rw [padicValNat_kzContent_eq_kzLevelM hl hμ h5 n (by rw [pow_two]; exact hpM),
        kzLevelM_eq]
      simp only [hrdef] at hc
      fin_cases w
      · have hc0 : (p : ℤ) ≡ 3 + 2 * l [ZMOD 6] := by simpa [conR] using hc
        have ha := kzResA_of_classA hl h5 hc0
        have e2' : (2 / 3 + δ) * (p : ℝ) ≤ ((n % p : ℕ) : ℝ) := by simpa [conU] using e2
        have : 2 * p + 1 ≤ 3 * (n % p) := by
          have : ((2 * p + 1 : ℕ) : ℝ) ≤ ((3 * (n % p) : ℕ) : ℝ) := by push_cast; linarith
          exact_mod_cast this
        rw [(levelM_caseA hl hμ hp13 ha hb).2 this]; norm_num
      · have hc0 : (p : ℤ) ≡ 3 - 2 * l [ZMOD 6] := by simpa [conR] using hc
        have ha := kzResA_of_classB hl h5 hc0
        have e2' : (1 / 2 + δ) * (p : ℝ) ≤ ((n % p : ℕ) : ℝ) := by simpa [conU] using e2
        have e3' : ((n % p : ℕ) : ℝ) < (5 / 6 - δ) * p := by
          rw [show (5 / 6 : ℝ) - δ = 5 / 6 + -δ by ring]
          simpa [conV] using e3
        have h1 : p + 1 ≤ 2 * (n % p) := by
          have : ((p + 1 : ℕ) : ℝ) ≤ ((2 * (n % p) : ℕ) : ℝ) := by push_cast; linarith
          exact_mod_cast this
        have h2 : 6 * (n % p) + 5 < 5 * p := by
          have : ((6 * (n % p) + 5 : ℕ) : ℝ) < ((5 * p : ℕ) : ℝ) := by push_cast; linarith
          exact_mod_cast this
        rw [(levelM_caseB hl hμ hp13 ha hb).2 ⟨h1, h2⟩]; norm_num
  have hwsum := main_le_sum_windows I (fun i => primeLogSumSix (r i) (n / B i) (n / A i)) A B hn
  have hmain : Real.pi / (2 * √3) - ε / 4 - 48 * δ * (L + 1) ≤
      ∑ i ∈ I, (1 / A i - 1 / B i) / 2 := by
    rw [hIdef, sum_product]
    calc Real.pi / (2 * √3) - ε / 4 - 48 * δ * (L + 1) ≤
          ∑ k ∈ range (L + 1), contentTerm k - 48 * δ * (L + 1) := by linarith
      _ = ∑ k ∈ range (L + 1), (contentTerm k - 48 * δ) := by
          rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]; push_cast; ring
      _ ≤ ∑ k ∈ range (L + 1), ∑ w : Fin 2, (1 / A (k, w) - 1 / B (k, w)) / 2 :=
          sum_le_sum fun k _ => content_windows_ge k hδ0.le hδ12
  have hcard : (I.card : ℝ) = 2 * (L + 1) := by
    rw [hIdef, card_product, card_range, card_univ, Fintype.card_fin]; push_cast; ring
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hε'L : 2 * (L + 1) * ε' ≤ ε / 4 := by
    rw [hε'def, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have k1 := mul_le_mul_of_nonneg_left hmain hn0
  have k2 := mul_le_mul_of_nonneg_right hε'L hn0
  have k3 := mul_le_mul_of_nonneg_right hδL hn0
  rw [hcard] at hwsum
  nlinarith

/-! ### Proposition 4.5 -/

/-- The two estimates of Proposition 4.5 for one family `(λ, μ)`. -/
theorem eventually_kzArithmeticAsymptotics_family (hBMOR : BMORPrimeCountingBound) {l μ : ℤ}
    (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      |Real.log (kzContent l μ n) - Real.pi / (2 * √3) * n| ≤ ε * n ∧
      ∀ A B : Polynomial ℤ, kzPrimitive l μ n = A * B → A.natDegree ≤ B.natDegree →
        Real.log (primeToSixPart (Polynomial.resultant A B)) ≤
          (43 / 20 - Real.pi / √3 + ε) * A.natDegree * n := by
  filter_upwards [eventually_log_kzContent_le hBMOR hl hμ hε,
    eventually_le_log_kzContent hBMOR hl hμ hε, eventually_sum_kzBudget_le hBMOR hl hμ hε,
    eventually_ge_atTop 11] with n h1 h2 h3 hn
  refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, fun A B hAB _ => ?_⟩
  have h := log_primeToSixPart_le hl hμ hn hAB
  calc Real.log (primeToSixPart (Polynomial.resultant A B)) ≤
        A.natDegree * ∑ p ∈ (Icc 5 n).filter Nat.Prime,
          (kzBudget l μ n p : ℝ) * Real.log p := h
    _ ≤ A.natDegree * ((43 / 20 - Real.pi / √3 + ε) * n) :=
        mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)
    _ = (43 / 20 - Real.pi / √3 + ε) * A.natDegree * n := by ring

/-- **Proposition 4.5**, conditional on [BMOR, Corollary 1.7]:
uniformly in `λ, μ ∈ {-1,1}` and in the factorization `H_n = A B` with `deg A ≤ deg B`,
`log g_n = (π/(2√3) + o(1)) n` and `log R^{(6)} ≤ (43/20 - π/√3 + o(1)) deg A · n`. -/
theorem kanekoZagierArithmeticAsymptotics (hBMOR : BMORPrimeCountingBound) :
    KanekoZagierArithmeticAsymptotics := by
  rw [kanekoZagierArithmeticAsymptotics_iff]
  intro ε hε
  have one : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1 := Or.inl rfl
  have mone : (-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1 := Or.inr rfl
  filter_upwards [eventually_kzArithmeticAsymptotics_family hBMOR one one hε,
    eventually_kzArithmeticAsymptotics_family hBMOR one mone hε,
    eventually_kzArithmeticAsymptotics_family hBMOR mone one hε,
    eventually_kzArithmeticAsymptotics_family hBMOR mone mone hε] with n a b c d l μ hl hμ
  rcases hl with rfl | rfl <;> rcases hμ with rfl | rfl
  exacts [a, b, c, d]

end ArithmeticOfJacobiPolynomials
