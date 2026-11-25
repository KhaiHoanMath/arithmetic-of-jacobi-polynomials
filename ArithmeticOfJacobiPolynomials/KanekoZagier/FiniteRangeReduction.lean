/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.KanekoZagier.ExplicitCutoff
public import ArithmeticOfJacobiPolynomials.KanekoZagier.CarryBudget
public import ArithmeticOfJacobiPolynomials.KanekoZagier.FiniteRangeQuantities
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Proposition B.2: the reduction to the criterion (B.6)

For `λ, μ ∈ {-1, 1}` (the argument `l` is `λ`), `M = 12 n + 5`, the proof of Proposition B.2
uses
* `T_0(n) = ∑_{p ≥ 5} (m_p^{(1)} + 1_{p ≤ n} e_p) log p` (`kzT0`, from (Appendix B.1);
  `m_p^{(1)} = kzLevelM l μ n p`, `e_p = kzLevelE l μ n p` are the first-level indicators of
  Lemma 4.2, and only primes `p ≤ M` occur),
* `Q(n) = ∑_{p ≥ 5 prime, h ≥ 2, p^h ≤ M} log p` (`kzQ`; the condition `p^h ≤ M` is
  `h ≤ ⌊log_p M⌋`),
* the integers `c_2 = 216n + 48 v_2(n!) - 24 s_2(n) - 27 D_{2,n} - 192` (`kzC2`),
  `c_3 = 48 v_3(n!) - 22n - 21 D_{3,n} - 8 s_3(2n + δ)` (`kzC3`), `c_7 = -21 n`, and
  `Δ_n = (c_2 log 2 + c_3 log 3 + c_7 log 7)/48 - T_0(n) - 3 Q(n)` (`kzFastDelta`).

Main results:
* `kz_content_budget` — (Appendix B.2): `S_n + log g_n ≤ T_0(n) + 3 Q(n)`, from
  `v_p(g_n) ≤ m_p^{(1)} + 2 #{h ≥ 2 : p^h ≤ M}` (each higher-level coefficient contribution is
  at most two, `level_coeff_le_two`) and `e_{p^h} ≤ 1`;
* `kz_log_add_exp_ge` — weighted AM–GM with weights `7/16`, `9/16`:
  `L_n ≥ (7/16) T_{2,n} + (9/16) T_{3,n} + 4 log 2 - (7/16) log 7 - (9/8) log 3`;
* `kz_fast_lower_bound` — `(c_2 log 2 + c_3 log 3 + c_7 log 7)/48 ≤
  log κ_n - J_n + n(L_n - T_{2,n} - T_{3,n} - E) - 4 log 2`;
* `irreducible_kanekoZagierJacobi_of_fast_criterion` — **the reduction of Proposition B.2**:
  for `n ≥ 11`, the two conditions (Appendix B.2)
  `|D_{2,n} log 2 - D_{3,n} log 3| ≤ (9/10) n` and `Δ_n > 0` imply that `P_n^{(λ/3, μ/2)}` is
  irreducible over `ℚ` (conditional on the cited [DLMF, §18.2(vi)] and [Berger, Theorem 2.4] and
  proved Lemma 2.5, through Proposition 4.7).
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Finset

/-! ### The content budget (Appendix B.2) -/

/-- Every level contribution to `v_p([t^j] y_n)` is at most two. -/
theorem level_coeff_le_two {q a b : ℕ} (hq : 0 < q) (haq : a < q) (hbq : b < q) {n j : ℕ}
    (hj : j ≤ n) :
    ((((n + a) / q : ℕ) : ℤ) - ((j + a) / q : ℕ)) +
        ((((j + (n + a + b)) / q : ℕ) : ℤ) - ((0 + (n + a + b)) / q : ℕ)) -
        ((n - j) / q : ℕ) - (j / q : ℕ) ≤ 2 := by
  rw [level_coeff_normal hq hj]
  have hs := Nat.mod_lt n hq
  have hu := Nat.mod_lt j hq
  have f1 := div_cases_two (x := n % q + a) (q := q) (by omega)
  have f2 := div_cases_two (x := j % q + a) (q := q) (by omega)
  have f3 := div_cases_four (x := n % q + (j % q + a + b)) (q := q) (by omega)
  have f4 := div_cases_four (x := n % q + (a + b)) (q := q) (by omega)
  split_ifs <;> omega

section Content

variable {p : ℕ} [hp : Fact p.Prime]

/-- Some coefficient index `j ≤ n` has `v_p(g_n) ≤ ∑_{h=1}^{H} (level-p^h contribution at j)`,
`H = ⌊log_p (12n+5)⌋`, with level-`p` contribution at most `m_p^{(1)}`. -/
theorem exists_padicValNat_kzContent_le {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    (hp5 : 5 ≤ p) (n : ℕ) : ∃ j ≤ n,
      (padicValNat p (kzContent l μ n) : ℤ) ≤
        ∑ h ∈ Icc 1 (Nat.log p (12 * n + 5)), kzCoeffLevel l μ n j (p ^ h) ∧
      kzCoeffLevel l μ n j p ≤ kzLevelM l μ n p := by
  have hH : 12 * n + 5 < p ^ (Nat.log p (12 * n + 5) + 1) :=
    Nat.lt_pow_succ_log_self hp.out.one_lt _
  obtain ⟨ha1, haq⟩ := kzResA_spec hl hp5 (h := 1) le_rfl
  obtain ⟨-, hbq⟩ := kzResB_spec hμ hp5 (h := 1) le_rfl
  rw [pow_one] at haq ha1 hbq
  obtain ⟨j, hj, hjle⟩ := level_coeff_attained (q := p) (n := n) hp.out.pos ha1 haq hbq
  have hval := padicValRat_kzKappa_mul_coeff_eq_sum hl hμ hp5 hj hH
  have hne := (padicValRat_kzKappa_mul_coeff hl hμ hj p).1
  rw [← coeff_kzScaled hl hμ] at hne hval
  have hK0 : (kzScaled l μ n).coeff j ≠ 0 := fun h0 => hne (by rw [h0, Int.cast_zero])
  have hdvd : ((p : ℤ) ^ padicValNat p (kzContent l μ n)) ∣ (kzScaled l μ n).coeff j := by
    refine dvd_trans ?_ (Polynomial.content_dvd_coeff j)
    rw [← kzContent_intCast, ← Nat.cast_pow, Int.natCast_dvd_natCast]
    exact pow_padicValNat_dvd
  have h1 := ((padicValInt_dvd_iff _ _).mp hdvd).resolve_left hK0
  rw [padicValRat.of_int] at hval
  have h2 : ((padicValNat p (kzContent l μ n) : ℕ) : ℤ) ≤
      (padicValInt p ((kzScaled l μ n).coeff j) : ℤ) := by
    exact_mod_cast h1
  refine ⟨j, hj, ?_, ?_⟩
  · rw [← hval]
    exact h2
  · rw [kzCoeffLevel_eq, kzLevelM_eq]
    exact hjle

/-- A sum over `Icc 1 H` (`H ≥ 1`) is the term at `1` plus the sum over `Icc 2 H`. -/
theorem sum_Icc_one_eq {H : ℕ} (hH : 1 ≤ H) (f : ℕ → ℤ) :
    ∑ h ∈ Icc 1 H, f h = f 1 + ∑ h ∈ Icc 2 H, f h := by
  have e : Icc 1 H = insert 1 (Icc 2 H) := by
    ext x
    simp only [mem_Icc, mem_insert]
    omega
  rw [e, sum_insert (by simp)]

/-- `v_p(g_n) ≤ m_p^{(1)} + 2 #{2 ≤ h ≤ H}` for `p ≤ 12n+5`. -/
theorem padicValNat_kzContent_le_levelM {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    (hp5 : 5 ≤ p) {n : ℕ} (hpM : p ≤ 12 * n + 5) :
    (padicValNat p (kzContent l μ n) : ℤ) ≤
      kzLevelM l μ n p + 2 * (#(Icc 2 (Nat.log p (12 * n + 5))) : ℤ) := by
  have hH : 1 ≤ Nat.log p (12 * n + 5) := Nat.log_pos hp.out.one_lt hpM
  obtain ⟨j, hj, hv, hm⟩ := exists_padicValNat_kzContent_le (p := p) hl hμ hp5 n
  have e := sum_Icc_one_eq hH (fun h => kzCoeffLevel l μ n j (p ^ h))
  simp only [pow_one] at e
  rw [e] at hv
  have h2 : ∑ h ∈ Icc 2 (Nat.log p (12 * n + 5)), kzCoeffLevel l μ n j (p ^ h) ≤
      ∑ _h ∈ Icc 2 (Nat.log p (12 * n + 5)), (2 : ℤ) := by
    refine sum_le_sum fun h hh => ?_
    have hh1 : 1 ≤ h := by have := (mem_Icc.mp hh).1; omega
    obtain ⟨-, haq'⟩ := kzResA_spec hl hp5 hh1
    obtain ⟨-, hbq'⟩ := kzResB_spec hμ hp5 hh1
    rw [kzCoeffLevel_eq]
    exact level_coeff_le_two (pow_pos hp.out.pos h) haq' hbq' hj
  rw [sum_const, nsmul_eq_mul] at h2
  linarith

/-- `v_p(g_n) = 0` for `p > 12n+5`. -/
theorem padicValNat_kzContent_eq_zero {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    (hp5 : 5 ≤ p) {n : ℕ} (hpM : 12 * n + 5 < p) : padicValNat p (kzContent l μ n) = 0 := by
  obtain ⟨j, -, hv, -⟩ := exists_padicValNat_kzContent_le (p := p) hl hμ hp5 n
  rw [Nat.log_of_lt hpM, Finset.Icc_eq_empty (by omega), sum_empty] at hv
  omega

/-- `E_p(n) ≤ e_p + #{2 ≤ h ≤ H}` for `p ≤ 12n+5`. -/
theorem kzBudget_le {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    (hp5 : 5 ≤ p) {n : ℕ} (hpM : p ≤ 12 * n + 5) :
    kzBudget l μ n p ≤ kzLevelE l μ n p + (#(Icc 2 (Nat.log p (12 * n + 5))) : ℤ) := by
  have hH : 1 ≤ Nat.log p (12 * n + 5) := Nat.log_pos hp.out.one_lt hpM
  have e := sum_Icc_one_eq hH (fun h => kzLevelE l μ n (p ^ h))
  simp only [pow_one] at e
  rw [kzBudget_eq, e]
  have : ∑ h ∈ Icc 2 (Nat.log p (12 * n + 5)), kzLevelE l μ n (p ^ h) ≤
      ∑ _h ∈ Icc 2 (Nat.log p (12 * n + 5)), (1 : ℤ) :=
    sum_le_sum fun h hh => by
      rcases (kzLevelE_mem hl hμ hp5 (by have := (mem_Icc.mp hh).1; omega : 1 ≤ h) n).1 with
        h0 | h1 <;> omega
  rw [sum_const, nsmul_eq_mul, mul_one] at this
  linarith

end Content

/-- **The content budget (Appendix B.2)**: `S_n + log g_n ≤ T_0(n) + 3 Q(n)`. -/
theorem kz_content_budget {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) (n : ℕ) :
    kzGoodPrimeSum l μ n + Real.log (kzContent l μ n) ≤ kzT0 l μ n + 3 * kzQ n := by
  have hS : kzGoodPrimeSum l μ n =
      ∑ p ∈ (Icc 5 (12 * n + 5)).filter Nat.Prime,
        if p ≤ n then (kzBudget l μ n p : ℝ) * Real.log p else 0 := by
    rw [kzGoodPrimeSum_eq, ← sum_filter]
    refine sum_congr ?_ fun _ _ => rfl
    ext p
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨⟨h1, by omega⟩, h3⟩, h2⟩
    · rintro ⟨⟨⟨h1, -⟩, h3⟩, h2⟩
      exact ⟨⟨h1, h2⟩, h3⟩
  have hg0 : kzContent l μ n ≠ 0 := (kzContent_pos hl hμ n).ne'
  have hcop := coprime_kzContent_six hl hμ n
  have hG : Real.log (kzContent l μ n) =
      ∑ p ∈ (Icc 5 (12 * n + 5)).filter Nat.Prime,
        (padicValNat p (kzContent l μ n) : ℝ) * Real.log p := by
    rw [Real.log_nat_eq_sum_factorization]
    rw [Finsupp.sum_of_support_subset _ (s := (Icc 5 (12 * n + 5)).filter Nat.Prime) ?_ _
      (fun _ _ => by simp)]
    · refine sum_congr rfl fun p hpP => ?_
      rw [Nat.factorization_def _ (mem_filter.mp hpP).2]
    · intro p hpf
      rw [Nat.support_factorization, Nat.mem_primeFactors] at hpf
      obtain ⟨hpr, hpd, -⟩ := hpf
      have := Fact.mk hpr
      have hp2 : p ≠ 2 := fun h => by
        subst h
        have := Nat.dvd_gcd hpd (by norm_num : 2 ∣ 6)
        rw [Nat.Coprime.gcd_eq_one hcop] at this
        omega
      have hp3 : p ≠ 3 := fun h => by
        subst h
        have := Nat.dvd_gcd hpd (by norm_num : 3 ∣ 6)
        rw [Nat.Coprime.gcd_eq_one hcop] at this
        omega
      have hp5 : 5 ≤ p := by
        have := hpr.two_le
        rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h | h | h | h
        · exact absurd h hp2
        · exact absurd h hp3
        · subst h
          rcases hpr.eq_one_or_self_of_dvd 2 (by norm_num) with h' | h' <;> omega
        · exact h
      have hpM : p ≤ 12 * n + 5 := by
        by_contra hlt
        have h0 := padicValNat_kzContent_eq_zero hl hμ hp5 (n := n) (by omega)
        have h1 : 1 ≤ padicValNat p (kzContent l μ n) :=
          one_le_padicValNat_of_dvd hg0 hpd
        omega
      simp only [mem_filter, mem_Icc]
      exact ⟨⟨hp5, hpM⟩, hpr⟩
  rw [hS, hG, kzT0_eq, kzQ_eq, ← sum_add_distrib, Finset.mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun p hpP => ?_
  obtain ⟨hpI, hpr⟩ := mem_filter.mp hpP
  obtain ⟨hp5, hpM⟩ := mem_Icc.mp hpI
  have := Fact.mk hpr
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpr.one_lt.le)
  have hv := padicValNat_kzContent_le_levelM (p := p) hl hμ hp5 hpM
  have hb := kzBudget_le (p := p) hl hμ hp5 hpM
  have hv' : (padicValNat p (kzContent l μ n) : ℝ) ≤
      kzLevelM l μ n p + 2 * (#(Icc 2 (Nat.log p (12 * n + 5))) : ℝ) := by exact_mod_cast hv
  have hb' : (kzBudget l μ n p : ℝ) ≤
      kzLevelE l μ n p + (#(Icc 2 (Nat.log p (12 * n + 5))) : ℝ) := by exact_mod_cast hb
  rw [sum_const, nsmul_eq_mul]
  split_ifs with hpn
  · have := mul_le_mul_of_nonneg_right (add_le_add hb' hv') hlog
    linarith
  · have := mul_le_mul_of_nonneg_right hv' hlog
    have hc : (0 : ℝ) ≤ #(Icc 2 (Nat.log p (12 * n + 5))) := by positivity
    linarith [mul_nonneg hc hlog]

/-! ### Weighted AM–GM -/

/-- `log(e^x + e^y) ≥ (7/16) x + (9/16) y + 4 log 2 - (7/16) log 7 - (9/8) log 3`. -/
theorem log_exp_add_exp_ge (x y : ℝ) :
    7 / 16 * x + 9 / 16 * y + 4 * Real.log 2 - 7 / 16 * Real.log 7 - 9 / 8 * Real.log 3 ≤
      Real.log (Real.exp x + Real.exp y) := by
  have hc := strictConcaveOn_log_Ioi.concaveOn.2
    (show (16 / 7 * Real.exp x) ∈ Set.Ioi (0 : ℝ) from by simp only [Set.mem_Ioi]; positivity)
    (show (16 / 9 * Real.exp y) ∈ Set.Ioi (0 : ℝ) from by simp only [Set.mem_Ioi]; positivity)
    (show (0 : ℝ) ≤ 7 / 16 by norm_num) (show (0 : ℝ) ≤ 9 / 16 by norm_num) (by norm_num)
  simp only [smul_eq_mul] at hc
  have e1 : 7 / 16 * (16 / 7 * Real.exp x) + 9 / 16 * (16 / 9 * Real.exp y) =
      Real.exp x + Real.exp y := by ring
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    push_cast
    ring
  have h9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have m1 := Real.log_mul (x := 16 / 7) (by norm_num) (Real.exp_pos x).ne'
  have m2 := Real.log_mul (x := 16 / 9) (by norm_num) (Real.exp_pos y).ne'
  have d1 := Real.log_div (x := 16) (y := 7) (by norm_num) (by norm_num)
  have d2 := Real.log_div (x := 16) (y := 9) (by norm_num) (by norm_num)
  rw [e1, m1, m2, Real.log_exp, Real.log_exp, d1, d2, h16, h9] at hc
  linarith

/-- **Weighted AM–GM**: `L_n ≥ (7/16) T_2 + (9/16) T_3 + 4 log 2 - (7/16) log 7 - (9/8) log 3`. -/
theorem kz_log_add_exp_ge (l μ : ℤ) (n : ℕ) :
    7 / 16 * kzT2 l n + 9 / 16 * kzT3 μ n + 4 * Real.log 2 - 7 / 16 * Real.log 7 -
      9 / 8 * Real.log 3 ≤ kzL l μ n := by
  rw [kzL_eq]
  exact log_exp_add_exp_ge _ _

/-! ### The lower bound and the reduction -/

theorem log_kzKappa (n : ℕ) : Real.log (kzKappa n) =
    (n + padicValNat 2 n.factorial) * Real.log 2 +
      (n + padicValNat 3 n.factorial) * Real.log 3 := by
  rw [kzKappa_eq]
  push_cast
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- `(c_2 log 2 + c_3 log 3 + c_7 log 7)/48 ≤ log κ_n - J_n + n(L_n - T_2 - T_3 - E) - 4 log 2`
for `n ≥ 1`. -/
theorem kz_fast_lower_bound (l μ : ℤ) {n : ℕ} (hn : 1 ≤ n) :
    (kzC2 l n * Real.log 2 + kzC3 μ n * Real.log 3 + (-21 * (n : ℝ)) * Real.log 7) / 48 ≤
      Real.log (kzKappa n) - kzJ μ n + n * (kzL l μ n - kzT2 l n - kzT3 μ n - kzE) -
        4 * Real.log 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hL := mul_le_mul_of_nonneg_left (kz_log_add_exp_ge l μ n) hn0.le
  have hn0' : (n : ℝ) ≠ 0 := hn0.ne'
  have h2 : (n : ℝ) * kzT2 l n = kzEndpointTwo l n * Real.log 2 := by
    rw [kzT2_eq]; field_simp
  have h3 : (n : ℝ) * kzT3 μ n = kzEndpointThree μ n * Real.log 3 := by
    rw [kzT3_eq]; field_simp
  rw [log_kzKappa, kzJ_eq, kzE_eq, kzC2_eq, kzC3_eq]
  simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]
  linarith [hL, h2, h3]

/-- `|T_{2,n} - T_{3,n}| ≤ 9/10` follows from `|D_{2,n} log 2 - D_{3,n} log 3| ≤ (9/10) n`. -/
theorem abs_kzT2_sub_kzT3_le_of_endpoint {l μ : ℤ} {n : ℕ} (hn : 1 ≤ n)
    (h : |kzEndpointTwo l n * Real.log 2 - kzEndpointThree μ n * Real.log 3| ≤ 9 / 10 * n) :
    |kzT2 l n - kzT3 μ n| ≤ 9 / 10 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have e : kzT2 l n - kzT3 μ n =
      (kzEndpointTwo l n * Real.log 2 - kzEndpointThree μ n * Real.log 3) / n := by
    rw [kzT2_eq, kzT3_eq]; ring
  rw [e, abs_div, abs_of_pos hn0, div_le_iff₀ hn0]
  exact h

/-- **The reduction of Proposition B.2**: for `n ≥ 11`, the conditions
(Appendix B.2) `|D_{2,n} log 2 - D_{3,n} log 3| ≤ (9/10) n` and `Δ_n > 0` imply
that `P_n^{(λ/3, μ/2)}` is irreducible over `ℚ`. Conditional on the cited
[DLMF, §18.2(vi)] and [Berger, Theorem 2.4] and proved Lemma 2.5 (through Proposition 4.7). -/
theorem irreducible_kanekoZagierJacobi_of_fast_criterion (hZ : JacobiSimpleRealZeros)
    (hNP : NewtonPolygonRootSlopes) {l μ : ℤ} (hl
    : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    {n : ℕ} (hn : 11 ≤ n)
    (h1 : |kzEndpointTwo l n * Real.log 2 - kzEndpointThree μ n * Real.log 3| ≤ 9 / 10 * n)
    (h2 : 0 < kzFastDelta l μ n) : Irreducible (kanekoZagierJacobi l μ n) := by
  by_contra hred
  have hT := abs_kzT2_sub_kzT3_le_of_endpoint (by omega) h1
  have hlow := kz_lower_bound_of_not_irreducible' hZ hNP hl hμ hn hT hred
  have hb := kz_content_budget hl hμ n
  have ham := kz_fast_lower_bound l μ (n := n) (by omega)
  rw [kzFastDelta_eq] at h2
  linarith

end ArithmeticOfJacobiPolynomials
