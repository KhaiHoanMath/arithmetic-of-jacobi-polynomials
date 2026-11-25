/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.SymmetricIrreducibility
public import ArithmeticOfJacobiPolynomials.Analysis.Margins
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Uniform asymptotics for symmetric parameters (Lemma 3.5, Proposition 3.6)

Section 3.2 of the manuscript ("Uniform linear ranges"). For integers `r ≥ 0`, `m ≥ 1`,
`δ ∈ {0,1}`, put `n = 2m+δ`, `S = 2n+2r+1`, `K = binom(m+r, r)`,
`A = (n+r)!²/(n!(n+2r)!)` and `A_{≤m} = ∏_{p ≤ m} p^{v_p(A)}`, and let
`g(t) = (4t+2) log(t+1/2) - 3t log t - (t+1) log(t+1)` (`asymptoticGapFunction`, (3.24);
the same formula as `symmetricGapFunction` of `Margins`).

The only analytic input is the explicit prime number theorem for `ϑ(x) = ∑_{p ≤ x} log p`
of [Dusart10, Theorem 5.2] (`k = 2`, `η_2 = 0.2`, `x_2 = 3 594 641`):
`|ϑ(x) - x| < 0.2 x / log² x` for `x ≥ 3 594 641`, taken as the explicit hypothesis `hPNT`.

Main results:
* `asymptoticGapFunction_div_strictAntiOn`: `g(t)/t` is strictly decreasing for `t ≥ 1`
  (Lemma 3.5, last assertion);
* `symmetric_uniform_asymptotics`: Lemma 3.5, (3.26), uniformly in `1 ≤ r ≤ m/2` and `δ`
  (with the explicit two-sided error bounds `symmetric_uniform_asymptotics_upper_explicit` and
  `symmetric_uniform_asymptotics_lower_explicit`);
* `irreducible_reducedGegenbauer_of_asymptotic_range`: Proposition 3.6;
* `irreducible_reducedGegenbauer_of_eight_mul_le`: the second assertion of Theorem 1.4,
  `∃ M₀, ∀ m r δ, δ ≤ 1 → 1 ≤ m → max (8r) M₀ ≤ m → F_{m,r,δ}` irreducible.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Real Finset Filter

/-! ### The Chebyshev function at integers -/

/-- `ϑ(k) = ∑_{p ≤ k} log p` for a natural number `k`. -/
noncomputable def primeLogSum (k : ℕ) : ℝ :=
  ∑ p ∈ (range (k + 1)).filter Nat.Prime, log (p : ℝ)

theorem primeLogSum_eq (k : ℕ) :
    primeLogSum k = ∑ p ∈ (range (k + 1)).filter Nat.Prime, log (p : ℝ) := (rfl)

/-- Splitting a sum over the primes `p ≤ b` at `a ≤ b`. -/
theorem sum_filter_prime_range_eq_add (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ p ∈ (range (b + 1)).filter Nat.Prime, f p =
      ∑ p ∈ (range (a + 1)).filter Nat.Prime, f p + ∑ p ∈ (Ioc a b).filter Nat.Prime, f p := by
  rw [← sum_union]
  · congr 1
    ext p
    simp only [mem_filter, mem_range, mem_union, mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h : p ≤ a
      · exact Or.inl ⟨by omega, h2⟩
      · exact Or.inr ⟨⟨by omega, by omega⟩, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨⟨_, h3⟩, h2⟩)
      · exact ⟨by omega, h2⟩
      · exact ⟨by omega, h2⟩
  · rw [disjoint_left]
    intro p hp hq
    simp only [mem_filter, mem_range, mem_Ioc] at hp hq
    omega

theorem sum_log_prime_Ioc_eq {a b : ℕ} (hab : a ≤ b) :
    ∑ p ∈ (Ioc a b).filter Nat.Prime, log (p : ℝ) = primeLogSum b - primeLogSum a := by
  rw [primeLogSum_eq, primeLogSum_eq, sum_filter_prime_range_eq_add _ hab]
  ring

/-- [Dusart10, Theorem 5.2] at integers `k ≥ m ≥ 3 594 641`:
`|ϑ(k) - k| ≤ (0.2 / log² m) k`. -/
theorem abs_primeLogSum_sub_le (hPNT : ∀ x : ℝ, 3594641 ≤ x →
      |(∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, log (p : ℝ)) - x| < 0.2 * x / log x ^ 2)
    {m k : ℕ} (hm : 3594641 ≤ m) (hk : m ≤ k) :
    |primeLogSum k - k| ≤ 0.2 / log (m : ℝ) ^ 2 * k := by
  have hk' : (3594641 : ℝ) ≤ k := by exact_mod_cast hm.trans hk
  have h := hPNT k hk'
  rw [Nat.floor_natCast, ← primeLogSum_eq] at h
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
  have hL : 0 < log (m : ℝ) := Real.log_pos hm1
  have hLk : log (m : ℝ) ≤ log k := Real.log_le_log (by linarith) (by exact_mod_cast hk)
  have hsq : log (m : ℝ) ^ 2 ≤ log k ^ 2 := pow_le_pow_left₀ hL.le hLk 2
  have hk0 : (0 : ℝ) ≤ k := by positivity
  calc |primeLogSum k - k| ≤ 0.2 * k / log k ^ 2 := h.le
    _ ≤ 0.2 * k / log m ^ 2 := div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
    _ = 0.2 / log (m : ℝ) ^ 2 * k := by ring

/-! ### The prime-power sum `Ψ_m(S)` -/

/-- `Ψ_m(S) ≤ ϑ(m) + (⌊√S⌋ + 1) log S`. -/
theorem primePowerLogSum_le_primeLogSum (m S : ℕ) (hS : 1 ≤ S) :
    primePowerLogSum m (S : ℝ) ≤ primeLogSum m + ((Nat.sqrt S : ℕ) + 1 : ℝ) * log S := by
  rw [primePowerLogSum_natCast_eq]
  have hlogS : 0 ≤ log (S : ℝ) := Real.log_nonneg (by exact_mod_cast hS)
  have hterm : ∀ p ∈ (range (m + 1)).filter Nat.Prime, ((Nat.log p S : ℕ) : ℝ) * log p ≤
      log (p : ℝ) + (if p ≤ Nat.sqrt S then log (S : ℝ) else 0) := by
    intro p hp
    have hpp := (mem_filter.mp hp).2
    have hlogp : 0 ≤ log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    split_ifs with h
    · have hpow : p ^ Nat.log p S ≤ S := Nat.pow_log_le_self p (by omega)
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      have : ((Nat.log p S : ℕ) : ℝ) * log p ≤ log S := by
        rw [← Real.log_pow]
        exact Real.log_le_log (pow_pos hp0 _) (by exact_mod_cast hpow)
      linarith
    · have hlt : S < p ^ 2 := by
        have := Nat.sqrt_lt.mp (not_le.mp h)
        rw [sq]; exact this
      have hL : Nat.log p S < 2 := Nat.log_lt_of_lt_pow (by omega) hlt
      have hL' : ((Nat.log p S : ℕ) : ℝ) ≤ 1 := by exact_mod_cast (by omega : Nat.log p S ≤ 1)
      nlinarith
  have hc : (((range (m + 1)).filter Nat.Prime).filter (· ≤ Nat.sqrt S)).card ≤
      Nat.sqrt S + 1 := by
    calc _ ≤ (range (Nat.sqrt S + 1)).card :=
          card_le_card fun p hp => mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hp).2)
      _ = _ := card_range _
  have hc' : ((((range (m + 1)).filter Nat.Prime).filter (· ≤ Nat.sqrt S)).card : ℝ) ≤
      (Nat.sqrt S : ℕ) + 1 := by exact_mod_cast hc
  calc _ ≤ ∑ p ∈ (range (m + 1)).filter Nat.Prime,
        (log (p : ℝ) + (if p ≤ Nat.sqrt S then log (S : ℝ) else 0)) := sum_le_sum hterm
    _ = primeLogSum m + ∑ p ∈ ((range (m + 1)).filter Nat.Prime).filter (· ≤ Nat.sqrt S),
          log (S : ℝ) := by
        have hite : ∑ p ∈ (range (m + 1)).filter Nat.Prime,
            (if p ≤ Nat.sqrt S then log (S : ℝ) else 0) =
            ∑ p ∈ ((range (m + 1)).filter Nat.Prime).filter (· ≤ Nat.sqrt S), log (S : ℝ) :=
          (sum_filter _ _).symm
        rw [sum_add_distrib, hite, primeLogSum_eq]
    _ ≤ primeLogSum m + ((Nat.sqrt S : ℕ) + 1 : ℝ) * log S := by
        rw [sum_const, nsmul_eq_mul]
        nlinarith

/-! ### The large primes in `A` ((3.25)) -/

/-- For `m < p` and `x < 3(m+1)`, `⌊x/p⌋ = [p ≤ x] + [2p ≤ x]`. -/
theorem div_eq_ite_add_ite {m x p : ℕ} (hmp : m < p) (hx : x < 3 * (m + 1)) :
    x / p = (if p ≤ x then 1 else 0) + (if 2 * p ≤ x then 1 else 0) := by
  split_ifs <;> first | (exfalso; omega) | exact Nat.div_eq_of_lt_le (by omega) (by omega)

/-- For `2m ≤ x ≤ N < 3(m+1)`: `∑_{m < p ≤ N} ⌊x/p⌋ log p = ϑ(x) + ϑ(x/2) - 2ϑ(m)`. -/
theorem sum_div_mul_log_prime_Ioc {m x N : ℕ} (hx : 2 * m ≤ x) (hxN : x ≤ N)
    (hN : N < 3 * (m + 1)) :
    ∑ p ∈ (Ioc m N).filter Nat.Prime, ((x / p : ℕ) : ℝ) * log p =
      primeLogSum x + primeLogSum (x / 2) - 2 * primeLogSum m := by
  have e : ∀ p ∈ (Ioc m N).filter Nat.Prime, ((x / p : ℕ) : ℝ) * log p =
      (if p ≤ x then log (p : ℝ) else 0) + (if p ≤ x / 2 then log (p : ℝ) else 0) := by
    intro p hp
    have hp' := mem_Ioc.mp (mem_filter.mp hp).1
    rw [div_eq_ite_add_ite hp'.1 (by omega)]
    split_ifs <;> first | (exfalso; omega) | (push_cast; ring)
  have h1 : ∑ p ∈ (Ioc m N).filter Nat.Prime, (if p ≤ x then log (p : ℝ) else 0) =
      ∑ p ∈ (Ioc m x).filter Nat.Prime, log (p : ℝ) := by
    rw [← sum_filter]
    apply sum_congr _ fun _ _ => rfl
    ext p
    by_cases hp : p.Prime <;> simp [hp]
    omega
  have h2 : ∑ p ∈ (Ioc m N).filter Nat.Prime, (if p ≤ x / 2 then log (p : ℝ) else 0) =
      ∑ p ∈ (Ioc m (x / 2)).filter Nat.Prime, log (p : ℝ) := by
    rw [← sum_filter]
    apply sum_congr _ fun _ _ => rfl
    ext p
    by_cases hp : p.Prime <;> simp [hp]
    omega
  rw [sum_congr rfl e, sum_add_distrib, h1, h2, sum_log_prime_Ioc_eq (by omega),
    sum_log_prime_Ioc_eq (by omega)]
  ring

/-- **(3.25)** (§3.2). For `2r ≤ m`, `m ≥ 2`, `n = 2m+δ`:
`∑_{m < p ≤ n+2r} v_p(A) log p = 2ϑ(n+r) - ϑ(n) - ϑ(n+2r) + 2ϑ((n+r)/2) - ϑ(n/2) - ϑ((n+2r)/2)`,
with integer halves. -/
theorem sum_padicValRat_symmetricRatio_Ioc (m r δ : ℕ) (hδ : δ ≤ 1) (hr : 2 * r ≤ m)
    (hm : 2 ≤ m) :
    ∑ p ∈ (Ioc m (2 * m + δ + 2 * r)).filter Nat.Prime,
        (padicValRat p (symmetricRatio (2 * m + δ) r) : ℝ) * log p =
      2 * primeLogSum (2 * m + δ + r) - primeLogSum (2 * m + δ) -
          primeLogSum (2 * m + δ + 2 * r) +
        (2 * primeLogSum ((2 * m + δ + r) / 2) - primeLogSum ((2 * m + δ) / 2) -
          primeLogSum ((2 * m + δ + 2 * r) / 2)) := by
  have e : ∀ p ∈ (Ioc m (2 * m + δ + 2 * r)).filter Nat.Prime,
      (padicValRat p (symmetricRatio (2 * m + δ) r) : ℝ) * log p =
        2 * ((((2 * m + δ + r) / p : ℕ) : ℝ) * log p) - (((2 * m + δ) / p : ℕ) : ℝ) * log p -
          (((2 * m + δ + 2 * r) / p : ℕ) : ℝ) * log p := by
    intro p hp
    obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
    have hpI := mem_Ioc.mp hpI
    have hmul : (m + 1) * (m + 1) ≤ p * p := Nat.mul_le_mul hpI.1 hpI.1
    have hsq : 2 * m + δ + 2 * r < p * p := by nlinarith
    rw [padicValRat_symmetricRatio_of_large hpp hsq]
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]
    ring
  rw [sum_congr rfl e, sum_sub_distrib, sum_sub_distrib, ← mul_sum,
    sum_div_mul_log_prime_Ioc (x := 2 * m + δ + r) (by omega) (by omega) (by omega),
    sum_div_mul_log_prime_Ioc (x := 2 * m + δ) (by omega) (by omega) (by omega),
    sum_div_mul_log_prime_Ioc (x := 2 * m + δ + 2 * r) (by omega) (by omega) (by omega)]
  ring

/-- `log A_{≤m} = log A - ∑_{m < p ≤ n+2r} v_p(A) log p`. -/
theorem log_primeTruncation_symmetricRatio_eq (m r δ : ℕ) :
    log (primeTruncation (symmetricRatio (2 * m + δ) r) m) =
      log (symmetricRatio (2 * m + δ) r : ℝ) -
        ∑ p ∈ (Ioc m (2 * m + δ + 2 * r)).filter Nat.Prime,
          (padicValRat p (symmetricRatio (2 * m + δ) r) : ℝ) * log p := by
  rw [log_primeTruncation, log_symmetricRatio,
    sum_filter_prime_range_eq_add _ (by omega : m ≤ 2 * m + δ + 2 * r)]
  ring

/-- The prime number theorem applied to (3.25): for `m ≥ 3 594 641` and `2r ≤ m`,
`log A_{≤m} - log A ≤ 1 + 27 (0.2 / log² m) m`. -/
theorem log_primeTruncation_symmetricRatio_le (hPNT : ∀ x : ℝ, 3594641 ≤ x →
      |(∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, log (p : ℝ)) - x| < 0.2 * x / log x ^ 2)
    (m r δ : ℕ) (hδ : δ ≤ 1) (hr : 2 * r ≤ m) (hm : 3594641 ≤ m) :
    log (primeTruncation (symmetricRatio (2 * m + δ) r) m) ≤
      log (symmetricRatio (2 * m + δ) r : ℝ) + 1 + 27 * (0.2 / log (m : ℝ) ^ 2) * m := by
  rw [log_primeTruncation_symmetricRatio_eq, sum_padicValRat_symmetricRatio_Ioc m r δ hδ hr
    (by omega)]
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
  have hε0 : 0 ≤ 0.2 / log (m : ℝ) ^ 2 := by positivity
  have b : ∀ k : ℕ, m ≤ k → -(0.2 / log (m : ℝ) ^ 2 * k) ≤ primeLogSum k - k ∧
      primeLogSum k - k ≤ 0.2 / log (m : ℝ) ^ 2 * k :=
    fun k hk => abs_le.mp (abs_primeLogSum_sub_le hPNT hm hk)
  obtain ⟨a1, a2⟩ := b (2 * m + δ) (by omega)
  obtain ⟨b1, b2⟩ := b (2 * m + δ + r) (by omega)
  obtain ⟨c1, c2⟩ := b (2 * m + δ + 2 * r) (by omega)
  obtain ⟨d1, d2⟩ := b ((2 * m + δ) / 2) (by omega)
  obtain ⟨e1, e2⟩ := b ((2 * m + δ + r) / 2) (by omega)
  obtain ⟨f1, f2⟩ := b ((2 * m + δ + 2 * r) / 2) (by omega)
  have hlin : (((2 * m + δ) / 2 : ℕ) : ℝ) + (((2 * m + δ + 2 * r) / 2 : ℕ) : ℝ) ≤
      2 * (((2 * m + δ + r) / 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (by omega : (2 * m + δ) / 2 + (2 * m + δ + 2 * r) / 2 ≤
      2 * ((2 * m + δ + r) / 2) + 1)
  have hcast : ((2 * m + δ + r : ℕ) : ℝ) * 2 =
      ((2 * m + δ : ℕ) : ℝ) + ((2 * m + δ + 2 * r : ℕ) : ℝ) := by push_cast; ring
  have htot : ((2 * m + δ : ℕ) : ℝ) + ((2 * m + δ + 2 * r : ℕ) : ℝ) +
      2 * ((2 * m + δ + r : ℕ) : ℝ) + (((2 * m + δ) / 2 : ℕ) : ℝ) +
      (((2 * m + δ + 2 * r) / 2 : ℕ) : ℝ) + 2 * (((2 * m + δ + r) / 2 : ℕ) : ℝ) ≤ 27 * m := by
    exact_mod_cast (by omega : 2 * m + δ + (2 * m + δ + 2 * r) + 2 * (2 * m + δ + r) +
      (2 * m + δ) / 2 + (2 * m + δ + 2 * r) / 2 + 2 * ((2 * m + δ + r) / 2) ≤ 27 * m)
  have hmul := mul_le_mul_of_nonneg_left htot hε0
  nlinarith

/-! ### Factorial estimates -/

/-- `log k! ≥ k log k - k`, by induction from `k log(1 + 1/k) ≤ 1`. -/
theorem stirling_le_log_factorial (k : ℕ) : (k : ℝ) * log k - k ≤ log (k.factorial : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · norm_num
    · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      have h := Real.log_le_sub_one_of_pos (x := ((k : ℝ) + 1) / k) (by positivity)
      rw [Real.log_div (by positivity) hk'.ne'] at h
      have e : (k : ℝ) * (((k : ℝ) + 1) / k - 1) = 1 := by field_simp; ring
      have h2 : (k : ℝ) * (log ((k : ℝ) + 1) - log k) ≤ 1 :=
        (mul_le_mul_of_nonneg_left h hk'.le).trans_eq e
      push_cast
      nlinarith

/-- `log k! ≤ k log k - k + log k + 1` for `k ≥ 1`, by induction from
`(k+1) log(1 + 1/k) ≥ 1`. -/
theorem log_factorial_le_stirling (k : ℕ) (hk : 1 ≤ k) :
    log (k.factorial : ℝ) ≤ k * log k - k + log k + 1 := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    have h := Real.one_sub_inv_le_log_of_pos (x := ((k : ℝ) + 1) / k) (by positivity)
    rw [Real.log_div (by positivity) hk'.ne', inv_div] at h
    have e : ((k : ℝ) + 1) * (1 - k / ((k : ℝ) + 1)) = 1 := by field_simp; ring
    have h2 : 1 ≤ ((k : ℝ) + 1) * (log ((k : ℝ) + 1) - log k) :=
      e.symm.trans_le (mul_le_mul_of_nonneg_left h (by positivity))
    push_cast
    nlinarith

/-- `log binom(m+r, r) = log (m+r)! - log m! - log r!`. -/
theorem log_choose_eq_log_factorial (m r : ℕ) : log ((m + r).choose r : ℝ) =
    log ((m + r).factorial : ℝ) - log (m.factorial : ℝ) - log (r.factorial : ℝ) := by
  have h := Nat.add_choose_mul_factorial_mul_factorial m r
  have pos : ∀ k : ℕ, (0 : ℝ) < k.factorial := fun k => by exact_mod_cast Nat.factorial_pos k
  have hc : (0 : ℝ) < ((m + r).choose r : ℕ) := by exact_mod_cast Nat.choose_pos (by omega)
  have e : ((m + r).factorial : ℝ) = ((m + r).choose r : ℕ) * m.factorial * r.factorial := by
    exact_mod_cast h.symm
  rw [e, Real.log_mul (mul_pos hc (pos m)).ne' (pos r).ne', Real.log_mul hc.ne' (pos m).ne']
  ring

/-- `log A = 2 log (n+r)! - log n! - log (n+2r)!`. -/
theorem log_symmetricRatio_eq_log_factorial (n r : ℕ) : log (symmetricRatio n r : ℝ) =
    2 * log ((n + r).factorial : ℝ) - log (n.factorial : ℝ) -
      log ((n + 2 * r).factorial : ℝ) := by
  have pos : ∀ k : ℕ, (0 : ℝ) < k.factorial := fun k => by exact_mod_cast Nat.factorial_pos k
  have hcast : (symmetricRatio n r : ℝ) =
      ((n + r).factorial : ℝ) ^ 2 / ((n.factorial : ℝ) * (n + 2 * r).factorial) := by
    rw [symmetricRatio_eq]; push_cast; ring
  rw [hcast, Real.log_div (pow_pos (pos _) 2).ne' (mul_pos (pos _) (pos _)).ne',
    Real.log_mul (pos _).ne' (pos _).ne', Real.log_pow]
  push_cast; ring

/-- Passing from `n` to `n+1` multiplies `A` by `(n+r+1)²/((n+1)(n+2r+1)) ≤ 2` (for `r ≤ n`). -/
theorem log_symmetricRatio_succ_le (n r : ℕ) (hr : r ≤ n) :
    log (symmetricRatio (n + 1) r : ℝ) ≤ log (symmetricRatio n r : ℝ) + log 2 := by
  rw [log_symmetricRatio_eq_log_factorial, log_symmetricRatio_eq_log_factorial,
    show n + 1 + r = n + r + 1 by ring, show n + 1 + 2 * r = n + 2 * r + 1 by ring,
    Nat.factorial_succ (n + r), Nat.factorial_succ n, Nat.factorial_succ (n + 2 * r)]
  have pos : ∀ k : ℕ, (0 : ℝ) < k.factorial := fun k => by exact_mod_cast Nat.factorial_pos k
  push_cast
  have hr' : (r : ℝ) ≤ n := by exact_mod_cast hr
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [Real.log_mul (by positivity) (pos _).ne', Real.log_mul (by positivity) (pos _).ne',
    Real.log_mul (by positivity) (pos _).ne']
  have key : log (((n : ℝ) + r + 1) ^ 2) ≤ log (2 * ((n : ℝ) + 1) * ((n : ℝ) + 2 * r + 1)) :=
    Real.log_le_log (by positivity) (by nlinarith)
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)] at key
  push_cast at key
  linarith

/-! ### The function `g` -/

/-- The function `g(t) = (4t+2) log(t+1/2) - 3t log t - (t+1) log(t+1)` of (3.24)
(§3.2). It has the same defining formula as `symmetricGapFunction`
(`ArithmeticOfJacobiPolynomials.Analysis.Margins`). -/
noncomputable def asymptoticGapFunction (t : ℝ) : ℝ :=
  (4 * t + 2) * log (t + 1 / 2) - 3 * t * log t - (t + 1) * log (t + 1)

theorem asymptoticGapFunction_eq (t : ℝ) : asymptoticGapFunction t =
    (4 * t + 2) * log (t + 1 / 2) - 3 * t * log t - (t + 1) * log (t + 1) := (rfl)

/-- The margin of Proposition 3.6 at `c = 8`: `8(log 4 - 1) - g(8) > 97/10000`
(as `margin_at_eight`). -/
theorem margin_asymptoticGapFunction_eight :
    8 * (log 4 - 1) - asymptoticGapFunction 8 > 97 / 10000 := by
  have hg : asymptoticGapFunction 8 = 34 * log (17 / 2) - 24 * log 8 - 9 * log 9 := by
    rw [asymptoticGapFunction_eq]; norm_num
  have h4 : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h8 : log 8 = 3 * log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have h9 : log 9 = 2 * log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h172 : log (17 / 2) = log 17 - log 2 := Real.log_div (by norm_num) (by norm_num)
  have h98 : log (9 / 8) = log 9 - log 8 := Real.log_div (by norm_num) (by norm_num)
  have h1716 : log (17 / 16) = log 17 - 4 * log 2 := by
    have := log_nat_div_pow_two 17 4 (by norm_num); norm_num at this; exact this
  linarith [log_nine_div_eight_gt, log_seventeen_div_sixteen_lt, Real.log_two_gt_d9]

/-- The main terms of the factorial estimate: with `t = m/r`,
`(m+r) log(m+r) - m log m - r log r + 2(2m+r) log(2m+r) - 2m log 2m - (2m+2r) log(2m+2r)
= r g(t)`. -/
theorem stirling_main_eq_mul_asymptoticGapFunction {m r : ℝ} (hm : 0 < m) (hr : 0 < r) :
    (m + r) * log (m + r) - m * log m - r * log r + 2 * ((2 * m + r) * log (2 * m + r)) -
        2 * m * log (2 * m) - (2 * m + 2 * r) * log (2 * m + 2 * r) =
      r * asymptoticGapFunction (m / r) := by
  obtain ⟨t, rfl⟩ : ∃ t, m = r * t := ⟨m / r, by field_simp⟩
  have ht : 0 < t := pos_of_mul_pos_right hm hr.le
  rw [show r * t / r = t by field_simp, asymptoticGapFunction_eq]
  have e1 : log (r * t + r) = log r + log (t + 1) := by
    rw [show r * t + r = r * (t + 1) by ring, Real.log_mul hr.ne' (by positivity)]
  have e2 : log (r * t) = log r + log t := Real.log_mul hr.ne' ht.ne'
  have e3 : log (2 * (r * t) + r) = log 2 + log r + log (t + 1 / 2) := by
    rw [show 2 * (r * t) + r = 2 * r * (t + 1 / 2) by ring,
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) hr.ne']
  have e4 : log (2 * (r * t)) = log 2 + log r + log t := by
    rw [show 2 * (r * t) = 2 * r * t by ring, Real.log_mul (by positivity) ht.ne',
      Real.log_mul (by norm_num) hr.ne']
  have e5 : log (2 * (r * t) + 2 * r) = log 2 + log r + log (t + 1) := by
    rw [show 2 * (r * t) + 2 * r = 2 * r * (t + 1) by ring,
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) hr.ne']
  rw [e1, e3, e5, e4, e2]
  ring

theorem hasDerivAt_asymptoticGapFunction {t : ℝ} (ht : 0 < t) :
    HasDerivAt asymptoticGapFunction (4 * log (t + 1 / 2) - 3 * log t - log (t + 1)) t := by
  have h1 : t + 1 / 2 ≠ 0 := by positivity
  have h2 : t + 1 ≠ 0 := by positivity
  have H := (((((hasDerivAt_id' t).const_mul 4).add_const 2).mul
      (((hasDerivAt_id' t).add_const (1 / 2)).log h1)).sub
    (((hasDerivAt_id' t).const_mul 3).mul ((hasDerivAt_id' t).log ht.ne'))).sub
    (((hasDerivAt_id' t).add_const 1).mul (((hasDerivAt_id' t).add_const 1).log h2))
  have hf : asymptoticGapFunction =
      fun y => (4 * y + 2) * log (y + 1 / 2) - 3 * y * log y - (y + 1) * log (y + 1) := by
    funext y; exact asymptoticGapFunction_eq y
  rw [hf]
  convert H using 1
  have a : (4 * t + 2) * (1 / (t + 1 / 2)) = 4 := by field_simp; ring
  have b : 3 * t * (1 / t) = 3 := by field_simp
  have c : (t + 1) * (1 / (t + 1)) = 1 := by field_simp
  linarith

/-- **Lemma 3.5, last assertion.** `g(t)/t` is strictly decreasing for `t ≥ 1`, since
`t g'(t) - g(t) = log((t+1)/(t+1/2)²) < 0`. -/
theorem asymptoticGapFunction_div_strictAntiOn :
    StrictAntiOn (fun t => asymptoticGapFunction t / t) (Set.Ici 1) := by
  have hd : ∀ t : ℝ, 0 < t → HasDerivAt (fun t => asymptoticGapFunction t / t)
      (((4 * log (t + 1 / 2) - 3 * log t - log (t + 1)) * t - asymptoticGapFunction t * 1) /
        t ^ 2) t :=
    fun t ht => (hasDerivAt_asymptoticGapFunction ht).div (hasDerivAt_id' t) ht.ne'
  apply strictAntiOn_of_deriv_neg (convex_Ici 1)
  · intro t ht
    exact (hd t (by linarith [Set.mem_Ici.mp ht])).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    have ht1 : 1 < t := ht
    rw [(hd t (by linarith)).deriv]
    apply div_neg_of_neg_of_pos _ (by positivity)
    have key : log (t + 1) < log ((t + 1 / 2) ^ 2) :=
      Real.log_lt_log (by linarith) (by nlinarith)
    rw [Real.log_pow] at key
    push_cast at key
    rw [asymptoticGapFunction_eq]
    nlinarith

theorem asymptoticGapFunction_div_le {c t : ℝ} (hc : 1 ≤ c) (hct : c ≤ t) :
    asymptoticGapFunction t / t ≤ asymptoticGapFunction c / c :=
  asymptoticGapFunction_div_strictAntiOn.antitoneOn (Set.mem_Ici.mpr hc)
    (Set.mem_Ici.mpr (hc.trans hct)) hct

/-- `r g(m/r) ≤ m g(c)/c` for `1 ≤ c ≤ m/r`. -/
theorem mul_asymptoticGapFunction_le {c m r : ℝ} (hc : 1 ≤ c) (hr : 0 < r) (hcm : c * r ≤ m) :
    r * asymptoticGapFunction (m / r) ≤ m * (asymptoticGapFunction c / c) := by
  have hct : c ≤ m / r := (le_div_iff₀ hr).mpr hcm
  have hm : 0 < m := lt_of_lt_of_le (by positivity) hcm
  have h := asymptoticGapFunction_div_le hc hct
  have e : r * asymptoticGapFunction (m / r) =
      m * (asymptoticGapFunction (m / r) / (m / r)) := by
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left h hm.le

/-! ### The factorial estimate for `log K + log A` -/

/-- **The factorial part of Lemma 3.5 (upper bound).** For `1 ≤ r`, `2r ≤ m`, `δ ≤ 1`:
`log K + log A ≤ r g(m/r) + 3 log(3m) + 4`. -/
theorem log_choose_add_log_symmetricRatio_le (m r δ : ℕ) (hδ : δ ≤ 1) (hr : 1 ≤ r)
    (hrm : 2 * r ≤ m) :
    log ((m + r).choose r : ℝ) + log (symmetricRatio (2 * m + δ) r : ℝ) ≤
      r * asymptoticGapFunction ((m : ℝ) / r) + 3 * log (3 * (m : ℝ)) + 4 := by
  have hδA : log (symmetricRatio (2 * m + δ) r : ℝ) ≤
      log (symmetricRatio (2 * m) r : ℝ) + log 2 := by
    rcases (by omega : δ = 0 ∨ δ = 1) with rfl | rfl
    · simp only [add_zero, le_add_iff_nonneg_right]
      exact Real.log_nonneg (by norm_num)
    · exact log_symmetricRatio_succ_le (2 * m) r (by omega)
  rw [log_choose_eq_log_factorial]
  have hA2 := log_symmetricRatio_eq_log_factorial (2 * m) r
  have u1 := log_factorial_le_stirling (m + r) (by omega)
  have l1 := stirling_le_log_factorial m
  have l2 := stirling_le_log_factorial r
  have u2 := log_factorial_le_stirling (2 * m + r) (by omega)
  have l3 := stirling_le_log_factorial (2 * m)
  have l4 := stirling_le_log_factorial (2 * m + 2 * r)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hmain := stirling_main_eq_mul_asymptoticGapFunction hm0 hr0
  have hr' : (r : ℝ) ≤ m := by exact_mod_cast (by omega : r ≤ m)
  have hlog1 : log ((m : ℝ) + r) ≤ log (3 * (m : ℝ)) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog2 : log (2 * (m : ℝ) + r) ≤ log (3 * (m : ℝ)) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog2' := Real.log_two_lt_d9
  push_cast at u1 l1 l2 u2 l3 l4 ⊢
  linarith

/-! ### Lemma 3.5 (upper bound) and the eventual estimates -/

/-- `Ψ_m(S) ≤ m + (0.2/L²) m + (3√m + 1)(2L)` for `m ≥ 3 594 641`, `2r ≤ m`, with
`L = log m` and `S = 2(2m+δ) + 2r + 1`. -/
theorem primePowerLogSum_symmetric_le (hPNT : ∀ x : ℝ, 3594641 ≤ x →
      |(∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, log (p : ℝ)) - x| < 0.2 * x / log x ^ 2)
    {m r δ : ℕ} (hδ : δ ≤ 1) (hrm : 2 * r ≤ m) (hm : 3594641 ≤ m) :
    primePowerLogSum m ((2 * (2 * m + δ) + 2 * r + 1 : ℕ) : ℝ) ≤
      m + 0.2 / log (m : ℝ) ^ 2 * m + (3 * √(m : ℝ) + 1) * (2 * log (m : ℝ)) := by
  have hΨ := primePowerLogSum_le_primeLogSum m (2 * (2 * m + δ) + 2 * r + 1) (by omega)
  have hθ := (abs_le.mp (abs_primeLogSum_sub_le hPNT hm le_rfl)).2
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hS5 : 2 * (2 * m + δ) + 2 * r + 1 ≤ 9 * m := by omega
  have hlogS : log ((2 * (2 * m + δ) + 2 * r + 1 : ℕ) : ℝ) ≤ 2 * log (m : ℝ) := by
    rw [show 2 * log (m : ℝ) = log ((m : ℝ) ^ 2) by rw [Real.log_pow]; norm_num]
    apply Real.log_le_log (by positivity)
    have : 2 * (2 * m + δ) + 2 * r + 1 ≤ m ^ 2 := by nlinarith
    exact_mod_cast this
  have hlogS0 : 0 ≤ log ((2 * (2 * m + δ) + 2 * r + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * (2 * m + δ) + 2 * r + 1))
  have hs : ((Nat.sqrt (2 * (2 * m + δ) + 2 * r + 1) : ℕ) : ℝ) ≤ 3 * √(m : ℝ) := by
    have h1 := Nat.sqrt_le' (2 * (2 * m + δ) + 2 * r + 1)
    have h2 : ((Nat.sqrt (2 * (2 * m + δ) + 2 * r + 1) : ℕ) : ℝ) ^ 2 ≤ 9 * m := by
      exact_mod_cast h1.trans hS5
    have h3 := Real.sq_sqrt hm0.le
    have h4 := Real.sqrt_nonneg (m : ℝ)
    nlinarith
  have hprod : (((Nat.sqrt (2 * (2 * m + δ) + 2 * r + 1) : ℕ) : ℝ) + 1) *
      log ((2 * (2 * m + δ) + 2 * r + 1 : ℕ) : ℝ) ≤ (3 * √(m : ℝ) + 1) * (2 * log (m : ℝ)) :=
    mul_le_mul (by linarith) hlogS hlogS0 (by positivity)
  linarith

/-- **Lemma 3.5, upper bound with explicit error.** For `m ≥ 3 594 641`, `1 ≤ r`, `2r ≤ m`,
`δ ≤ 1`, and `L = log m`:
`Ψ_m(S) + log K + log A_{≤m} ≤ m + r g(m/r) + 28 (0.2/L²) m + (3√m + 1)(2L) + 6L + 5`. -/
theorem symmetric_uniform_asymptotics_upper_explicit (hPNT : ∀ x : ℝ, 3594641 ≤ x →
      |(∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, log (p : ℝ)) - x| < 0.2 * x / log x ^ 2)
    {m r δ : ℕ} (hδ : δ ≤ 1) (hr : 1 ≤ r) (hrm : 2 * r ≤ m) (hm : 3594641 ≤ m) :
    primePowerLogSum m ((2 * (2 * m + δ) + 2 * r + 1 : ℕ) : ℝ) + log ((m + r).choose r : ℝ) +
        log (primeTruncation (symmetricRatio (2 * m + δ) r) m) ≤
      m + r * asymptoticGapFunction ((m : ℝ) / r) + 28 * (0.2 / log (m : ℝ) ^ 2) * m +
        (3 * √(m : ℝ) + 1) * (2 * log (m : ℝ)) + 6 * log (m : ℝ) + 5 := by
  have hΨ := primePowerLogSum_symmetric_le hPNT hδ hrm hm
  have hD := log_primeTruncation_symmetricRatio_le hPNT m r δ hδ hrm hm
  have hKA := log_choose_add_log_symmetricRatio_le m r δ hδ hr hrm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hlog3 : log (3 * (m : ℝ)) ≤ 2 * log (m : ℝ) := by
    rw [show 2 * log (m : ℝ) = log ((m : ℝ) ^ 2) by rw [Real.log_pow]; norm_num]
    apply Real.log_le_log (by positivity)
    have : (3 : ℝ) ≤ m := by exact_mod_cast (by omega : 3 ≤ m)
    nlinarith
  linarith

/-- For every `κ ≥ 1`, eventually `m ≥ 3 594 641`, `κ ≤ log m`, `κ log m ≤ √m` and `κ ≤ √m`. -/
theorem eventually_log_le_sqrt (κ : ℝ) (hκ : 1 ≤ κ) :
    ∀ᶠ m : ℕ in atTop, 3594641 ≤ m ∧ κ ≤ log (m : ℝ) ∧ κ * log (m : ℝ) ≤ √(m : ℝ) ∧
      κ ≤ √(m : ℝ) := by
  have hκ0 : 0 < κ := by linarith
  have h1 : ∀ᶠ x : ℝ in atTop, κ ≤ log x := Real.tendsto_log_atTop.eventually_ge_atTop κ
  have h2 : ∀ᶠ x : ℝ in atTop, ‖log x ^ 2‖ ≤ (1 / κ) ^ 2 * ‖id x‖ :=
    (Real.isLittleO_pow_log_id_atTop (n := 2)).bound (pow_pos (one_div_pos.mpr hκ0) 2)
  have h3 : ∀ᶠ x : ℝ in atTop, κ ^ 2 ≤ x := eventually_ge_atTop _
  have h4 : ∀ᶠ x : ℝ in atTop, 3594641 ≤ x := eventually_ge_atTop _
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (h1.and (h2.and (h3.and h4)))] with
    m hmP
  obtain ⟨hL, hlog, hx, hx'⟩ := hmP
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hsq := Real.sq_sqrt hm0
  have hu0 := Real.sqrt_nonneg (m : ℝ)
  have hlog' : log (m : ℝ) ^ 2 ≤ (1 / κ) ^ 2 * m := by
    have e1 : log (m : ℝ) ^ 2 ≤ ‖log (m : ℝ) ^ 2‖ := by
      rw [Real.norm_eq_abs]; exact le_abs_self _
    have e2 : ‖id (m : ℝ)‖ = m := by rw [id, Real.norm_eq_abs, abs_of_nonneg hm0]
    have := e1.trans hlog
    rwa [e2] at this
  refine ⟨by exact_mod_cast hx', hL, ?_, ?_⟩
  · by_contra hcon
    have hlt := not_le.mp hcon
    have hmul := mul_lt_mul'' hlt hlt hu0 hu0
    have hk2 : κ ^ 2 * (1 / κ) ^ 2 = 1 := by field_simp
    have hκL : κ ^ 2 * log (m : ℝ) ^ 2 ≤ m :=
      calc κ ^ 2 * log (m : ℝ) ^ 2 ≤ κ ^ 2 * ((1 / κ) ^ 2 * m) :=
            mul_le_mul_of_nonneg_left hlog' (by positivity)
        _ = m := by rw [← mul_assoc, hk2, one_mul]
    nlinarith
  · calc κ = √(κ ^ 2) := (Real.sqrt_sq hκ0.le).symm
      _ ≤ √(m : ℝ) := Real.sqrt_le_sqrt hx

/-- The explicit error of Lemma 3.5, together with `log(8√m)`, is at most `42 m / κ` under the
conditions of `eventually_log_le_sqrt`. -/
theorem symmetric_error_le {m κ : ℝ} (hκ : 1 ≤ κ) (hm : 0 ≤ m) (hL : κ ≤ log m)
    (hLu : κ * log m ≤ √m) (hu : κ ≤ √m) :
    28 * (0.2 / log m ^ 2) * m + (3 * √m + 1) * (2 * log m) + 6 * log m + 5 +
        log (8 * √m) ≤ 42 / κ * m := by
  have hκ0 : 0 < κ := by linarith
  have hsq : √m * √m = m := Real.mul_self_sqrt hm
  have hu1 : 1 ≤ √m := hκ.trans hu
  have hL0 : 0 < log m := lt_of_lt_of_le hκ0 hL
  have hκκ : κ * κ ≤ log m * log m := mul_le_mul hL hL hκ0.le hL0.le
  have hε : 0.2 / log m ^ 2 ≤ 0.2 / κ :=
    div_le_div_of_nonneg_left (by norm_num) hκ0 (by nlinarith)
  have hLu' : log m ≤ √m / κ := by rw [le_div_iff₀ hκ0]; linarith
  have h8 : log (8 * √m) = log 8 + log m / 2 := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_sqrt hm]
  have h8' : log (8 : ℝ) < 3 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9
    push_cast
    linarith
  have huL : √m * log m ≤ m / κ := by
    calc √m * log m ≤ √m * (√m / κ) := mul_le_mul_of_nonneg_left hLu' (by positivity)
      _ = m / κ := by rw [← mul_div_assoc, hsq]
  have hum : √m / κ ≤ m / κ := div_le_div_of_nonneg_right (by nlinarith) hκ0.le
  have hκu : κ * κ ≤ √m * √m := mul_le_mul hu hu hκ0.le (by positivity)
  have h1m : 1 ≤ m / κ := by rw [le_div_iff₀ hκ0]; nlinarith
  have hεm : 0.2 / log m ^ 2 * m ≤ 0.2 / κ * m := mul_le_mul_of_nonneg_right hε hm
  have e1 : 0.2 / κ * m = 0.2 * (m / κ) := by ring
  have e2 : 42 / κ * m = 42 * (m / κ) := by ring
  rw [h8, e2]
  nlinarith

/-! ### Lemma 3.5 (lower bound) -/

/-- `ϑ(m) ≤ Ψ_m(S)` for `m ≤ S`, since `⌊log_p S⌋ ≥ 1` for `p ≤ m`. -/
theorem primeLogSum_le_primePowerLogSum (m S : ℕ) (hmS : m ≤ S) :
    primeLogSum m ≤ primePowerLogSum m (S : ℝ) := by
  rw [primePowerLogSum_natCast_eq, primeLogSum_eq]
  refine sum_le_sum fun p hp => ?_
  have hpp := (mem_filter.mp hp).2
  have hpm := mem_range.mp (mem_filter.mp hp).1
  have hL : 1 ≤ Nat.log p S := Nat.log_pos hpp.one_lt (by omega)
  have hlogp : 0 ≤ log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
  have hL' : (1 : ℝ) ≤ ((Nat.log p S : ℕ) : ℝ) := by exact_mod_cast hL
  nlinarith

/-- `A` increases with `n`: passing from `n` to `n+1` multiplies `A` by
`(n+r+1)²/((n+1)(n+2r+1)) ≥ 1`. -/
theorem log_symmetricRatio_le_succ (n r : ℕ) :
    log (symmetricRatio n r : ℝ) ≤ log (symmetricRatio (n + 1) r : ℝ) := by
  rw [log_symmetricRatio_eq_log_factorial, log_symmetricRatio_eq_log_factorial,
    show n + 1 + r = n + r + 1 by ring, show n + 1 + 2 * r = n + 2 * r + 1 by ring,
    Nat.factorial_succ (n + r), Nat.factorial_succ n, Nat.factorial_succ (n + 2 * r)]
  have pos : ∀ k : ℕ, (0 : ℝ) < k.factorial := fun k => by exact_mod_cast Nat.factorial_pos k
  push_cast
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [Real.log_mul (by positivity) (pos _).ne', Real.log_mul (by positivity) (pos _).ne',
    Real.log_mul (by positivity) (pos _).ne']
  have key : log (((n : ℝ) + 1) * ((n : ℝ) + 2 * r + 1)) ≤ log (((n : ℝ) + r + 1) ^ 2) :=
    Real.log_le_log (by positivity) (by nlinarith)
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity)] at key
  push_cast at key
  linarith

/-- **The factorial part of Lemma 3.5 (lower bound).** For `1 ≤ r`, `2r ≤ m`, `δ ≤ 1`:
`r g(m/r) - 4 log(3m) - 4 ≤ log K + log A`. -/
theorem le_log_choose_add_log_symmetricRatio (m r δ : ℕ) (hδ : δ ≤ 1) (hr : 1 ≤ r)
    (hrm : 2 * r ≤ m) :
    r * asymptoticGapFunction ((m : ℝ) / r) - 4 * log (3 * (m : ℝ)) - 4 ≤
      log ((m + r).choose r : ℝ) + log (symmetricRatio (2 * m + δ) r : ℝ) := by
  have hδA : log (symmetricRatio (2 * m) r : ℝ) ≤
      log (symmetricRatio (2 * m + δ) r : ℝ) := by
    rcases (by omega : δ = 0 ∨ δ = 1) with rfl | rfl
    · simp only [add_zero, le_refl]
    · exact log_symmetricRatio_le_succ (2 * m) r
  rw [log_choose_eq_log_factorial]
  have hA2 := log_symmetricRatio_eq_log_factorial (2 * m) r
  have l1 := stirling_le_log_factorial (m + r)
  have u1 := log_factorial_le_stirling m (by omega)
  have u2 := log_factorial_le_stirling r hr
  have l2 := stirling_le_log_factorial (2 * m + r)
  have u3 := log_factorial_le_stirling (2 * m) (by omega)
  have u4 := log_factorial_le_stirling (2 * m + 2 * r) (by omega)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hmain := stirling_main_eq_mul_asymptoticGapFunction hm0 hr0
  have hr' : (r : ℝ) ≤ m := by exact_mod_cast (by omega : r ≤ m)
  have hr2' : 2 * (r : ℝ) ≤ m := by exact_mod_cast hrm
  have hlog1 : log (m : ℝ) ≤ log (3 * (m : ℝ)) := Real.log_le_log hm0 (by linarith)
  have hlog2 : log (r : ℝ) ≤ log (3 * (m : ℝ)) := Real.log_le_log hr0 (by linarith)
  have hlog3 : log (2 * (m : ℝ)) ≤ log (3 * (m : ℝ)) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog4 : log (2 * (m : ℝ) + 2 * r) ≤ log (3 * (m : ℝ)) :=
    Real.log_le_log (by positivity) (by linarith)
  push_cast at l1 u1 u2 l2 u3 u4 ⊢
  linarith

/-- The prime number theorem applied to (3.25), lower bound: for `m ≥ 3 594 641` and `2r ≤ m`,
`log A - 1 - 27 (0.2 / log² m) m ≤ log A_{≤m}`. -/
theorem le_log_primeTruncation_symmetricRatio (hPNT : ∀ x : ℝ, 3594641 ≤ x →
      |(∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, log (p : ℝ)) - x| < 0.2 * x / log x ^ 2)
    (m r δ : ℕ) (hδ : δ ≤ 1) (hr : 2 * r ≤ m) (hm : 3594641 ≤ m) :
    log (symmetricRatio (2 * m + δ) r : ℝ) - 1 - 27 * (0.2 / log (m : ℝ) ^ 2) * m ≤
      log (primeTruncation (symmetricRatio (2 * m + δ) r) m) := by
  rw [log_primeTruncation_symmetricRatio_eq, sum_padicValRat_symmetricRatio_Ioc m r δ hδ hr
    (by omega)]
  have hε0 : 0 ≤ 0.2 / log (m : ℝ) ^ 2 := by positivity
  have b : ∀ k : ℕ, m ≤ k → -(0.2 / log (m : ℝ) ^ 2 * k) ≤ primeLogSum k - k ∧
      primeLogSum k - k ≤ 0.2 / log (m : ℝ) ^ 2 * k :=
    fun k hk => abs_le.mp (abs_primeLogSum_sub_le hPNT hm hk)
  obtain ⟨a1, a2⟩ := b (2 * m + δ) (by omega)
  obtain ⟨b1, b2⟩ := b (2 * m + δ + r) (by omega)
  obtain ⟨c1, c2⟩ := b (2 * m + δ + 2 * r) (by omega)
  obtain ⟨d1, d2⟩ := b ((2 * m + δ) / 2) (by omega)
  obtain ⟨e1, e2⟩ := b ((2 * m + δ + r) / 2) (by omega)
  obtain ⟨f1, f2⟩ := b ((2 * m + δ + 2 * r) / 2) (by omega)
  have hlin : 2 * (((2 * m + δ + r) / 2 : ℕ) : ℝ) ≤
      (((2 * m + δ) / 2 : ℕ) : ℝ) + (((2 * m + δ + 2 * r) / 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (by omega : 2 * ((2 * m + δ + r) / 2) ≤
      (2 * m + δ) / 2 + (2 * m + δ + 2 * r) / 2 + 1)
  have hcast : ((2 * m + δ + r : ℕ) : ℝ) * 2 =
      ((2 * m + δ : ℕ) : ℝ) + ((2 * m + δ + 2 * r : ℕ) : ℝ) := by push_cast; ring
  have htot : ((2 * m + δ : ℕ) : ℝ) + ((2 * m + δ + 2 * r : ℕ) : ℝ) +
      2 * ((2 * m + δ + r : ℕ) : ℝ) + (((2 * m + δ) / 2 : ℕ) : ℝ) +
      (((2 * m + δ + 2 * r) / 2 : ℕ) : ℝ) + 2 * (((2 * m + δ + r) / 2 : ℕ) : ℝ) ≤ 27 * m := by
    exact_mod_cast (by omega : 2 * m + δ + (2 * m + δ + 2 * r) + 2 * (2 * m + δ + r) +
      (2 * m + δ) / 2 + (2 * m + δ + 2 * r) / 2 + 2 * ((2 * m + δ + r) / 2) ≤ 27 * m)
  have hmul := mul_le_mul_of_nonneg_left htot hε0
  linarith

/-- **Lemma 3.5, lower bound with explicit error.** For `m ≥ 3 594 641`, `1 ≤ r`, `2r ≤ m`,
`δ ≤ 1`, and `L = log m`:
`m + r g(m/r) - 28 (0.2/L²) m - 8L - 5 ≤ Ψ_m(S) + log K + log A_{≤m}`. -/
theorem symmetric_uniform_asymptotics_lower_explicit (hPNT : ∀ x : ℝ, 3594641 ≤ x →
      |(∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, log (p : ℝ)) - x| < 0.2 * x / log x ^ 2)
    {m r δ : ℕ} (hδ : δ ≤ 1) (hr : 1 ≤ r) (hrm : 2 * r ≤ m) (hm : 3594641 ≤ m) :
    m + r * asymptoticGapFunction ((m : ℝ) / r) - 28 * (0.2 / log (m : ℝ) ^ 2) * m -
        8 * log (m : ℝ) - 5 ≤
      primePowerLogSum m ((2 * (2 * m + δ) + 2 * r + 1 : ℕ) : ℝ) + log ((m + r).choose r : ℝ) +
        log (primeTruncation (symmetricRatio (2 * m + δ) r) m) := by
  have hΨ := primeLogSum_le_primePowerLogSum m (2 * (2 * m + δ) + 2 * r + 1) (by omega)
  have hθ := (abs_le.mp (abs_primeLogSum_sub_le hPNT hm le_rfl)).1
  have hD := le_log_primeTruncation_symmetricRatio hPNT m r δ hδ hrm hm
  have hKA := le_log_choose_add_log_symmetricRatio m r δ hδ hr hrm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hlog3 : log (3 * (m : ℝ)) ≤ 2 * log (m : ℝ) := by
    rw [show 2 * log (m : ℝ) = log ((m : ℝ) ^ 2) by rw [Real.log_pow]; norm_num]
    apply Real.log_le_log (by positivity)
    have : (3 : ℝ) ≤ m := by exact_mod_cast (by omega : 3 ≤ m)
    nlinarith
  linarith

/-- **Lemma 3.5, (3.26).** Uniformly for integers `1 ≤ r ≤ m/2`
and `δ ∈ {0,1}`, as `m → ∞`, `Ψ_m(S) + log K + log A_{≤m} = m + r g(m/r) + o(m)`: for every
`η > 0` there is `M` with `|Ψ_m(S) + log K + log A_{≤m} - (m + r g(m/r))| ≤ η m` for all
`m ≥ M`, `1 ≤ r`, `2r ≤ m` and `δ ≤ 1`. Conditional on [Dusart10, Theorem 5.2] (`hPNT`). -/
theorem symmetric_uniform_asymptotics (hPNT : ∀ x : ℝ, 3594641 ≤ x →
      |(∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, log (p : ℝ)) - x| < 0.2 * x / log x ^ 2)
    {η : ℝ} (hη : 0 < η) :
    ∃ M : ℕ, ∀ m r δ : ℕ, δ ≤ 1 → 1 ≤ r → 2 * r ≤ m → M ≤ m →
      |primePowerLogSum m ((2 * (2 * m + δ) + 2 * r + 1 : ℕ) : ℝ) + log ((m + r).choose r : ℝ) +
          log (primeTruncation (symmetricRatio (2 * m + δ) r) m) -
          (m + r * asymptoticGapFunction ((m : ℝ) / r))| ≤ η * m := by
  have hκ : 1 ≤ 42 / η + 1 := by
    have : 0 < 42 / η := by positivity
    linarith
  obtain ⟨M, hM⟩ := eventually_atTop.mp (eventually_log_le_sqrt (42 / η + 1) hκ)
  refine ⟨M, fun m r δ hδ hr hrm hm => ?_⟩
  obtain ⟨hx, hL, hLu, hu⟩ := hM m hm
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

/-! ### Proposition 3.6 and Theorem 1.4 -/

theorem symmetricRatio_zero_right (n : ℕ) : symmetricRatio n 0 = 1 := by
  rw [symmetricRatio_eq]
  simp only [mul_zero, add_zero]
  have h : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  rw [sq, div_self (mul_ne_zero h h)]

theorem log_primeTruncation_one (m : ℕ) : log (primeTruncation 1 m) = 0 := by
  rw [log_primeTruncation]
  simp

/-- **Proposition 3.6.** Let `c ≥ 2` satisfy
`c (log 4 - 1) > g(c)`. For all sufficiently large `m`, uniformly for `0 ≤ r ≤ m/c` and
`δ ∈ {0,1}`, `F_{m,r,δ} = C_{2m+δ}^{r+1/2}(x)/x^δ` is irreducible over `ℚ`. Conditional on the
cited `JacobiSimpleRealZeros`
([DLMF, §18.2(vi)]) and the explicit prime number theorem `hPNT` ([Dusart10, Theorem 5.2]). -/
theorem irreducible_reducedGegenbauer_of_asymptotic_range (hZ : JacobiSimpleRealZeros)
    (hPNT : ∀ x : ℝ, 3594641 ≤ x →
      |(∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, log (p : ℝ)) - x| < 0.2 * x / log x ^ 2)
    {c : ℝ} (hc : 2 ≤ c) (hgap : asymptoticGapFunction c < c * (log 4 - 1)) :
    ∃ M₀ : ℕ, ∀ m r δ : ℕ, δ ≤ 1 → M₀ ≤ m → c * r ≤ m →
      Irreducible (reducedGegenbauer m r δ) := by
  have hc0 : 0 < c := by linarith
  have h4 : 1 < log 4 := by
    have h := Real.log_two_gt_d9
    have : log (4 : ℝ) = 2 * log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    linarith
  have hgc : asymptoticGapFunction c / c < log 4 - 1 := by
    rw [div_lt_iff₀ hc0]; linarith
  obtain ⟨η, hη0, hη1, hη2⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ log 4 - 1 - asymptoticGapFunction c / c ∧
      η ≤ log 4 - 1 :=
    ⟨min (log 4 - 1 - asymptoticGapFunction c / c) (log 4 - 1),
      lt_min (by linarith) (by linarith), min_le_left _ _, min_le_right _ _⟩
  have hκ : 1 ≤ 84 / η + 1 := by
    have : 0 < 84 / η := by positivity
    linarith
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp (eventually_log_le_sqrt (84 / η + 1) hκ)
  refine ⟨M₀, fun m r δ hδ hm hcr => ?_⟩
  obtain ⟨hx, hL, hLu, hu⟩ := hM₀ m hm
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

/-- **Theorem 1.4, second assertion** (Proposition 3.6 with `c = 8`, using
`8(log 4 - 1) - g(8) > 0`). There is `M₀` such that `F_{m,r,δ} = C_{2m+δ}^{r+1/2}(x)/x^δ` is
irreducible over `ℚ` for all `δ ∈ {0,1}`, `m ≥ 1` and `m ≥ max{8r, M₀}`. Conditional on
`JacobiSimpleRealZeros` and [Dusart10, Theorem 5.2] (`hPNT`). -/
theorem irreducible_reducedGegenbauer_of_eight_mul_le (hZ : JacobiSimpleRealZeros)
    (hPNT : ∀ x : ℝ, 3594641 ≤ x →
      |(∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, log (p : ℝ)) - x| < 0.2 * x / log x ^ 2) :
    ∃ M₀ : ℕ, ∀ m r δ : ℕ, δ ≤ 1 → 1 ≤ m → max (8 * r) M₀ ≤ m →
      Irreducible (reducedGegenbauer m r δ) := by
  obtain ⟨M₀, h⟩ := irreducible_reducedGegenbauer_of_asymptotic_range hZ hPNT (c := 8)
    (by norm_num) (by linarith [margin_asymptoticGapFunction_eight])
  refine ⟨M₀, fun m r δ hδ _ hm => h m r δ hδ (le_of_max_le_right hm) ?_⟩
  exact_mod_cast le_of_max_le_left hm

end ArithmeticOfJacobiPolynomials
