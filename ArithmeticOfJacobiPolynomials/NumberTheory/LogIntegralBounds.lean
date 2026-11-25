/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.NumberTheory.PrimeCounting
public import Mathlib.Analysis.Complex.ExponentialBounds
public import ArithmeticOfJacobiPolynomials.External
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Nat.Totient

/-!
# Elementary estimates for the logarithmic integral and prime counts in intervals

* `logIntegral_sub_ge`: `Li(b) - Li(a) ≥ (b - a) / log b` for `2 ≤ a ≤ b`;
* `logIntegral_sub_le`: `Li(b) - Li(a) ≤ (b - a) / log a` for `2 ≤ a ≤ b`.
* `primesIoc lo hi q a`: the primes `p` with `lo < p ≤ hi` and `p ≡ a (mod q)`, and its
  relation to `π(x; q, a)`.
* `card_primesIoc_gt`: the lower bound for that count supplied by [BMOR, Corollary 1.7].
* `card_le_of_forall_modEq`: at most `(hi - lo)/q + 2` integers of `(lo, hi]` lie in a single
  class modulo `q`.
* `card_le_of_forall_modEq_succ`: at most `(hi - lo)/q + 1` integers of `(lo, hi]` lie in a single
  class modulo `q`.
* numerical bounds: `log 2`-multiples, `13.8 < log (10^6) < 13.82`, `log 9 < 2.2`, and the
  monotonicity of `log x / x` at `10^6` and `31.6`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Real

/-- `1 / log t` is interval integrable between any two reals `≥ 2`. -/
theorem intervalIntegrable_one_div_log {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun t => 1 / Real.log t) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  have hmem : ∀ t ∈ Set.uIcc a b, 2 ≤ t := by
    intro t ht
    rcases Set.mem_uIcc.mp ht with h | h <;> linarith [h.1]
  apply ContinuousOn.div continuousOn_const (Real.continuousOn_log.mono ?_) ?_
  · intro t ht
    have := hmem t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith
  · intro t ht
    exact (Real.log_pos (by linarith [hmem t ht])).ne'

/-- `Li(b) - Li(a) ≥ (b - a) / log b` for `2 ≤ a ≤ b`. -/
theorem logIntegral_sub_ge {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    (b - a) / Real.log b ≤ logIntegral b - logIntegral a := by
  have hb : 2 ≤ b := ha.trans hab
  simp only [logIntegral_eq]
  rw [intervalIntegral.integral_interval_sub_left (intervalIntegrable_one_div_log le_rfl hb)
    (intervalIntegrable_one_div_log le_rfl ha)]
  have hlogb : 0 < Real.log b := Real.log_pos (by linarith)
  calc (b - a) / Real.log b = ∫ _ in a..b, 1 / Real.log b := by
        rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    _ ≤ ∫ t in a..b, 1 / Real.log t := by
      apply intervalIntegral.integral_mono_on hab intervalIntegrable_const
        (intervalIntegrable_one_div_log ha hb)
      intro t ht
      have ht2 : 2 ≤ t := ha.trans ht.1
      have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
      exact one_div_le_one_div_of_le hlogt (Real.log_le_log (by linarith) ht.2)

/-- `Li(b) - Li(a) ≤ (b - a) / log a` for `2 ≤ a ≤ b`. -/
theorem logIntegral_sub_le {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    logIntegral b - logIntegral a ≤ (b - a) / Real.log a := by
  have hb : 2 ≤ b := ha.trans hab
  simp only [logIntegral_eq]
  rw [intervalIntegral.integral_interval_sub_left (intervalIntegrable_one_div_log le_rfl hb)
    (intervalIntegrable_one_div_log le_rfl ha)]
  have hloga : 0 < Real.log a := Real.log_pos (by linarith)
  calc ∫ t in a..b, 1 / Real.log t ≤ ∫ _ in a..b, 1 / Real.log a := by
        apply intervalIntegral.integral_mono_on hab (intervalIntegrable_one_div_log ha hb)
          intervalIntegrable_const
        intro t ht
        exact one_div_le_one_div_of_le hloga (Real.log_le_log (by linarith) ht.1)
    _ = (b - a) / Real.log a := by
        rw [intervalIntegral.integral_const, smul_eq_mul]; ring

/-- The primes `p` with `lo < p ≤ hi` and `p ≡ a (mod q)`. -/
noncomputable def primesIoc (lo hi q : ℕ) (a : ℤ) : Finset ℕ :=
  (Finset.Ioc lo hi).filter fun p : ℕ => p.Prime ∧ (p : ℤ) ≡ a [ZMOD q]

theorem mem_primesIoc {lo hi q : ℕ} {a : ℤ} {p : ℕ} :
    p ∈ primesIoc lo hi q a ↔ lo < p ∧ p ≤ hi ∧ p.Prime ∧ (p : ℤ) ≡ a [ZMOD q] := by
  simp [primesIoc, and_assoc]

/-- `π(lo; q, a) + #{lo < p ≤ hi} = π(hi; q, a)`. -/
theorem primeCountingAP_add_card_primesIoc {lo hi : ℕ} (h : lo ≤ hi) (q : ℕ) (a : ℤ) :
    primeCountingAP lo q a + (primesIoc lo hi q a).card = primeCountingAP hi q a := by
  simp only [primeCountingAP_eq]
  unfold primesIoc
  rw [Nat.floor_natCast, Nat.floor_natCast, ← Finset.card_union_of_disjoint]
  · congr 1
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨⟨h1, h1'⟩, h2⟩)
      · exact ⟨by omega, h2⟩
      · exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩
      by_cases hp : p < lo + 1
      · exact Or.inl ⟨hp, h2⟩
      · exact Or.inr ⟨⟨by omega, by omega⟩, h2⟩
  · rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc] at hp hp'
    omega

theorem card_primesIoc_eq_sub {lo hi : ℕ} (h : lo ≤ hi) (q : ℕ) (a : ℤ) :
    ((primesIoc lo hi q a).card : ℝ) =
      (primeCountingAP (hi : ℝ) q a : ℝ) - primeCountingAP (lo : ℝ) q a := by
  rw [← primeCountingAP_add_card_primesIoc h q a]
  push_cast; ring

/-- The lower bound for the number of primes of a reduced class in `(lo, hi]` given by
[BMOR, Corollary 1.7]. -/
theorem card_primesIoc_gt (hBMOR : BMORPrimeCountingBound) {q : ℕ} {a : ℤ} (hq1 : 1 ≤ q)
    (hq : q ≤ 10 ^ 5) (ha : Int.gcd a q = 1) {lo hi : ℕ} (hlo : 10 ^ 6 ≤ lo) (h : lo ≤ hi) :
    ((hi : ℝ) - lo) / (q.totient * Real.log hi) -
        0.027 * ((lo : ℝ) / Real.log lo ^ 2 + (hi : ℝ) / Real.log hi ^ 2) <
      (primesIoc lo hi q a).card := by
  have hlo' : (10 : ℝ) ^ 6 ≤ lo := by exact_mod_cast hlo
  have hhi' : (10 : ℝ) ^ 6 ≤ hi := hlo'.trans (by exact_mod_cast h)
  have h1 := hBMOR q a hq1 hq ha hi hhi'
  have h2 := hBMOR q a hq1 hq ha lo hlo'
  rw [abs_lt, mul_div_assoc] at h1 h2
  have hLi := logIntegral_sub_ge (a := lo) (b := hi) (by linarith) (by exact_mod_cast h)
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hlog : 0 < Real.log hi := Real.log_pos (by linarith)
  rw [card_primesIoc_eq_sub h]
  have e : ((hi : ℝ) - lo) / (q.totient * Real.log hi) = ((hi - lo) / Real.log hi) / q.totient := by
    field_simp
  have hLi' : ((hi : ℝ) - lo) / Real.log hi / q.totient ≤
      logIntegral hi / q.totient - logIntegral lo / q.totient := by
    rw [← sub_div]; exact div_le_div_of_nonneg_right hLi hφ.le
  rw [e]
  linarith [h1.1, h2.2]

/-- At most `(hi - lo)/q + 2` naturals in `(lo, hi]` lie in a single class modulo `q`. -/
theorem card_le_of_forall_modEq {S : Finset ℕ} {lo hi q : ℕ} {c : ℤ} (hq : 0 < q) (hle : lo ≤ hi)
    (hS : ∀ p ∈ S, lo < p ∧ p ≤ hi ∧ (p : ℤ) ≡ c [ZMOD q]) :
    (S.card : ℝ) ≤ ((hi : ℝ) - lo) / q + 2 := by
  have hinj : Set.InjOn (fun p => p / q) S := by
    intro x hx y hy hxy
    have hmod : x % q = y % q := by
      have := ((hS x hx).2.2.trans (hS y hy).2.2.symm)
      exact Int.natCast_modEq_iff.mp this
    simp only at hxy
    rw [← Nat.div_add_mod x q, ← Nat.div_add_mod y q, hxy, hmod]
  have hmaps : ∀ p ∈ S, p / q ∈ Finset.Icc ((lo + 1) / q) (hi / q) := by
    intro p hp
    obtain ⟨h1, h2, -⟩ := hS p hp
    simp only [Finset.mem_Icc]
    exact ⟨Nat.div_le_div_right (by omega), Nat.div_le_div_right h2⟩
  have hcard : S.card ≤ hi / q + 1 - (lo + 1) / q := by
    rw [← Nat.card_Icc]
    exact Finset.card_le_card_of_injOn _ hmaps hinj
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have e1 := Nat.div_add_mod (lo + 1) q
  have e2 := Nat.div_add_mod hi q
  have m1 := Nat.mod_lt (lo + 1) hq
  have hdiv : (lo + 1) / q ≤ hi / q + 1 := by
    calc (lo + 1) / q ≤ (hi + q) / q := Nat.div_le_div_right (by omega)
      _ = hi / q + 1 := Nat.add_div_right hi hq
  have hcard' : S.card + (lo + 1) / q ≤ hi / q + 1 := by omega
  have r1 : ((q : ℝ) * ((lo + 1) / q : ℕ) + ((lo + 1) % q : ℕ)) = lo + 1 := by exact_mod_cast e1
  have r2 : ((q : ℝ) * (hi / q : ℕ) + (hi % q : ℕ)) = hi := by exact_mod_cast e2
  have rm1 : (((lo + 1) % q : ℕ) : ℝ) < q := by exact_mod_cast m1
  have rm2 : (0 : ℝ) ≤ ((hi % q : ℕ) : ℝ) := Nat.cast_nonneg _
  have rc : ((S.card : ℕ) : ℝ) + ((lo + 1) / q : ℕ) ≤ (hi / q : ℕ) + 1 := by exact_mod_cast hcard'
  rw [div_add' _ _ _ hq'.ne', le_div_iff₀ hq']
  nlinarith

/-! ### Numerical constants -/

theorem log_two_gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
theorem log_two_lt : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9

/-- `log (10^6) > 13.8`. -/
theorem log_ge_of_million_le {x : ℝ} (hx : 10 ^ 6 ≤ x) : 13.8 ≤ Real.log x := by
  have h1 : Real.log ((10 : ℝ) ^ 6) ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have h2 : Real.log ((10 : ℝ) ^ 6) = 20 * Real.log 2 + Real.log ((10 : ℝ) ^ 6 / 2 ^ 20) := by
    have e : ((10 : ℝ) ^ 6) = 2 ^ 20 * ((10 : ℝ) ^ 6 / 2 ^ 20) := by norm_num
    rw [e, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have h3 := Real.one_sub_inv_le_log_of_pos (x := (10 : ℝ) ^ 6 / 2 ^ 20) (by norm_num)
  have h4 : (1 : ℝ) - ((10 : ℝ) ^ 6 / 2 ^ 20)⁻¹ = 1 - 1048576 / 1000000 := by norm_num
  rw [h4] at h3
  have := log_two_gt
  have h5 : (13.8 : ℝ) ≤ 20 * 0.6931471803 + (1 - 1048576 / 1000000) := by norm_num
  calc (13.8 : ℝ) ≤ 20 * 0.6931471803 + (1 - 1048576 / 1000000) := h5
    _ ≤ 20 * Real.log 2 + Real.log ((10 : ℝ) ^ 6 / 2 ^ 20) := by linarith
    _ = Real.log ((10 : ℝ) ^ 6) := h2.symm
    _ ≤ Real.log x := h1

/-- At most `(hi - lo)/q + 1` naturals in `(lo, hi]` lie in a single class modulo `q`. -/
theorem card_le_of_forall_modEq_succ {S : Finset ℕ} {lo hi q : ℕ} {c : ℤ} (hq : 0 < q)
    (hle : lo ≤ hi) (hS : ∀ p ∈ S, lo < p ∧ p ≤ hi ∧ (p : ℤ) ≡ c [ZMOD q]) :
    (S.card : ℝ) ≤ ((hi : ℝ) - lo) / q + 1 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hnn : (0 : ℝ) ≤ ((hi : ℝ) - lo) / q :=
    div_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hle)) hq'.le
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.card_empty, Nat.cast_zero]
    linarith
  · have hm : S.min' hne ∈ S := S.min'_mem hne
    have hM : S.max' hne ∈ S := S.max'_mem hne
    have hmM : ∀ p ∈ S, S.min' hne ≤ p ∧ p ≤ S.max' hne :=
      fun p hp => ⟨S.min'_le p hp, S.le_max' p hp⟩
    have hdvd : ∀ p ∈ S, q ∣ p - S.min' hne := by
      intro p hp
      have hpm : S.min' hne ≡ p [MOD q] :=
        (Int.natCast_modEq_iff.mp ((hS p hp).2.2.trans (hS _ hm).2.2.symm)).symm
      exact (Nat.modEq_iff_dvd' (hmM p hp).1).mp hpm
    have hinj : Set.InjOn (fun p => (p - S.min' hne) / q) S := by
      intro x hx y hy hxy
      have h1 := Nat.mul_div_cancel' (hdvd x hx)
      have h2 := Nat.mul_div_cancel' (hdvd y hy)
      simp only at hxy
      have := (hmM x hx).1
      have := (hmM y hy).1
      rw [hxy] at h1
      omega
    have hmaps : ∀ p ∈ S, (fun p => (p - S.min' hne) / q) p ∈
        Finset.range ((S.max' hne - S.min' hne) / q + 1) := by
      intro p hp
      simp only [Finset.mem_range, Nat.lt_succ_iff]
      exact Nat.div_le_div_right (by have := hmM p hp; omega)
    have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
    rw [Finset.card_range] at hcard
    have h1 : q * ((S.max' hne - S.min' hne) / q) ≤ S.max' hne - S.min' hne :=
      Nat.mul_div_le _ q
    have h2 : S.max' hne ≤ hi := (hS _ hM).2.1
    have h3 : lo < S.min' hne := (hS _ hm).1
    have h4 : q * ((S.max' hne - S.min' hne) / q) ≤ hi - lo := by omega
    have h5 : ((q * ((S.max' hne - S.min' hne) / q) : ℕ) : ℝ) ≤ ((hi - lo : ℕ) : ℝ) := by
      exact_mod_cast h4
    rw [Nat.cast_sub hle] at h5
    push_cast at h5
    have h6 : (((S.max' hne - S.min' hne) / q : ℕ) : ℝ) ≤ ((hi : ℝ) - lo) / q := by
      rw [le_div_iff₀ hq']
      linarith
    have h7 : (S.card : ℝ) ≤ (((S.max' hne - S.min' hne) / q : ℕ) : ℝ) + 1 := by
      exact_mod_cast hcard
    linarith

/-! ### Further numerical constants -/

/-- `log (10^6) < 13.82`. -/
theorem log_million_lt : Real.log ((10 : ℝ) ^ 6) < 13.82 := by
  have h2 : Real.log ((10 : ℝ) ^ 6) = 20 * Real.log 2 + Real.log ((10 : ℝ) ^ 6 / 2 ^ 20) := by
    have e : ((10 : ℝ) ^ 6) = 2 ^ 20 * ((10 : ℝ) ^ 6 / 2 ^ 20) := by norm_num
    rw [e, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have h3 := Real.log_le_sub_one_of_pos (x := (10 : ℝ) ^ 6 / 2 ^ 20) (by norm_num)
  have h5 : (10 : ℝ) ^ 6 / 2 ^ 20 - 1 ≤ -0.0463 := by norm_num
  have := log_two_lt
  rw [h2]
  linarith

/-- `log 9 < 2.2`. -/
theorem log_nine_lt : Real.log 9 < 2.2 := by
  have h1 : (9 : ℝ) < Real.exp 2.2 := by
    have e1 := Real.exp_one_gt_d9
    have e2 : (1.2214 : ℝ) ≤ Real.exp 0.2 := by
      have := Real.sum_le_exp_of_nonneg (x := 0.2) (by norm_num) 5
      norm_num [Finset.sum_range_succ, Nat.factorial] at this
      linarith
    have e3 : Real.exp 2.2 = Real.exp 1 * Real.exp 1 * Real.exp 0.2 := by
      rw [← Real.exp_add, ← Real.exp_add]; norm_num
    have e4 : (7.38 : ℝ) ≤ Real.exp 1 * Real.exp 1 := by nlinarith
    rw [e3]
    calc (9 : ℝ) < 7.38 * 1.2214 := by norm_num
      _ ≤ Real.exp 1 * Real.exp 1 * Real.exp 0.2 :=
        mul_le_mul e4 e2 (by norm_num) (by positivity)
  exact (Real.log_lt_iff_lt_exp (by norm_num)).mpr h1

/-- `log x / x ≤ 13.82 / 10^6` for `x ≥ 10^6` (the quotient decreases). -/
theorem log_div_le_of_million {x : ℝ} (hx : 10 ^ 6 ≤ x) : Real.log x / x ≤ 13.82 / 10 ^ 6 := by
  have hx0 : 0 < x := by linarith
  have h := Real.log_le_sub_one_of_pos (x := x / 10 ^ 6) (by positivity)
  rw [Real.log_div hx0.ne' (by norm_num)] at h
  have hm := log_million_lt
  rw [div_le_div_iff₀ hx0 (by norm_num)]
  linarith

/-- `log b ≤ (691/6320) b` for `b ≥ 31.6` (`log b / b` decreases). -/
theorem log_le_mul_of_ge {b : ℝ} (hb : 31.6 ≤ b) : Real.log b ≤ 691 / 6320 * b := by
  have hb0 : 0 < b := by linarith
  have h := Real.log_le_sub_one_of_pos (x := b / 31.6) (by positivity)
  rw [Real.log_div hb0.ne' (by norm_num)] at h
  have h4 : 4 * Real.log 31.6 ≤ Real.log ((10 : ℝ) ^ 6) := by
    have e := Real.log_pow (31.6 : ℝ) 4
    push_cast at e
    rw [← e]
    exact Real.log_le_log (by positivity) (by norm_num)
  have h5 : 4 * Real.log 31.6 < 13.82 := lt_of_le_of_lt h4 log_million_lt
  generalize Real.log 31.6 = c at h h5
  generalize Real.log b = d at h ⊢
  have hb' : b / 31.6 = b * (5 / 158) := by norm_num [div_eq_mul_inv]
  rw [hb'] at h
  linarith

end ArithmeticOfJacobiPolynomials
