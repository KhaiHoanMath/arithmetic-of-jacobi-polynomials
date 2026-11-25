/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.External
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Int.Log
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.NormNum.Prime

/-!
# Lemma 2.7: a bound for the prime powers

For an integer `B ≥ 1` and a real `S ≥ 1`, `Ψ_B(S) = ∑_{p ≤ B} ⌊log_p S⌋ log p`.
If `B ≥ 9` and `1 ≤ S ≤ 5B`, then
`Ψ_B(S) ≤ log lcm(1, …, B) + log lcm(1, …, ⌊√S⌋)`, and, by Hanson's bound
([Hanson, Theorem 1], the hypothesis `HansonLcmBound`), this is `< (B + √S) log 3`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Real Finset

/-- `Ψ_B(S) = ∑_{p ≤ B} ⌊log_p S⌋ log p`, the sum over primes `p ≤ B`. -/
noncomputable def primePowerLogSum (B : ℕ) (S : ℝ) : ℝ :=
  ∑ p ∈ (range (B + 1)).filter Nat.Prime, (⌊logb p S⌋ : ℝ) * log p

theorem primePowerLogSum_eq (B : ℕ) (S : ℝ) : primePowerLogSum B S =
    ∑ p ∈ (range (B + 1)).filter Nat.Prime, (⌊logb p S⌋ : ℝ) * log p := (rfl)

/-- If `p^{e(p)} ≤ N` for every prime `p` in `P`, then `∑_{p ∈ P} e(p) log p ≤ log lcm(1, …, N)`. -/
theorem sum_mul_log_le_log_lcmUpTo (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (e : ℕ → ℕ) (N : ℕ)
    (he : ∀ p ∈ P, p ^ e p ≤ N) :
    ∑ p ∈ P, (e p : ℝ) * log p ≤ log (Nat.lcmUpto N) := by
  have hdvd : (∏ p ∈ P, p ^ e p) ∣ Nat.lcmUpto N := by
    apply Finset.prod_dvd_of_isRelPrime
    · intro p hp q hq hpq
      rw [Function.onFun, ← Nat.coprime_iff_isRelPrime]
      exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq)
    · intro p hp
      have h1 : p ^ e p ∈ Icc 1 N :=
        Finset.mem_Icc.mpr ⟨Nat.one_le_pow _ _ (hP p hp).pos, he p hp⟩
      exact Finset.dvd_lcm (f := id) h1
  have hle : ((∏ p ∈ P, p ^ e p : ℕ) : ℝ) ≤ (Nat.lcmUpto N : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.lcmUpto_pos N) hdvd
  have hpos : (0 : ℝ) < ((∏ p ∈ P, p ^ e p : ℕ) : ℝ) := by
    have : 0 < ∏ p ∈ P, p ^ e p :=
      Finset.prod_pos fun p hp => pow_pos (hP p hp).pos _
    exact_mod_cast this
  have hlog : log ((∏ p ∈ P, p ^ e p : ℕ) : ℝ) = ∑ p ∈ P, (e p : ℝ) * log p := by
    push_cast
    rw [Real.log_prod]
    · refine Finset.sum_congr rfl fun p _ => ?_
      rw [Real.log_pow]
    · intro p hp
      exact pow_ne_zero _ (by exact_mod_cast (hP p hp).ne_zero)
  rw [← hlog]
  exact Real.log_le_log hpos hle

/-- For a prime `p ≤ B` with `B ≥ 9`, the largest power of `p` not exceeding `B` is at least `5`. -/
theorem five_le_pow_log {p B : ℕ} (hp : p.Prime) (hpB : p ≤ B) (hB : 9 ≤ B) :
    5 ≤ p ^ Nat.log p B := by
  by_cases h5 : 5 ≤ p
  · have hl : 1 ≤ Nat.log p B := Nat.log_pos hp.one_lt hpB
    calc 5 ≤ p := h5
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ Nat.log p B := Nat.pow_le_pow_right hp.pos hl
  · push Not at h5
    interval_cases p
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · have hl : 3 ≤ Nat.log 2 B := Nat.le_log_of_pow_le (by norm_num) (by omega)
      calc 5 ≤ 2 ^ 3 := by norm_num
        _ ≤ 2 ^ Nat.log 2 B := Nat.pow_le_pow_right (by norm_num) hl
    · have hl : 2 ≤ Nat.log 3 B := Nat.le_log_of_pow_le (by norm_num) (by omega)
      calc 5 ≤ 3 ^ 2 := by norm_num
        _ ≤ 3 ^ Nat.log 3 B := Nat.pow_le_pow_right (by norm_num) hl
    · exact absurd hp (by norm_num)

/-- **Lemma 2.7**, first inequality: for `B ≥ 9` and `1 ≤ S ≤ 5B`,
`Ψ_B(S) ≤ log lcm(1, …, B) + log lcm(1, …, ⌊√S⌋)`. -/
theorem primePowerLogSum_le_log_lcm (B : ℕ) (hB : 9 ≤ B) (S : ℝ) (hS₁ : 1 ≤ S)
    (hS : S ≤ 5 * B) :
    primePowerLogSum B S ≤ log (Nat.lcmUpto B) + log (Nat.lcmUpto ⌊√S⌋₊) := by
  set P := (range (B + 1)).filter Nat.Prime with hPdef
  have hPprime : ∀ p ∈ P, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  have hPle : ∀ p ∈ P, p ≤ B := fun p hp =>
    Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
  set s := ⌊S⌋₊ with hs
  have hs1 : 1 ≤ s := Nat.le_floor (by exact_mod_cast hS₁)
  have hs5 : s ≤ 5 * B := by
    have : (s : ℝ) ≤ 5 * B := (Nat.floor_le (by linarith)).trans hS
    exact_mod_cast this
  set k : ℕ → ℕ := fun p => Nat.log p s with hk
  set l : ℕ → ℕ := fun p => Nat.log p B with hl
  set j : ℕ → ℕ := fun p => k p / 2 with hj
  have hfloor : ∀ p ∈ P, (⌊logb p S⌋ : ℝ) = (k p : ℝ) := by
    intro p _
    rw [Real.floor_logb_natCast (by linarith), Int.log_of_one_le_right _ hS₁]
    rfl
  have hkl : ∀ p ∈ P, k p ≤ l p + j p := by
    intro p hp
    have hpp := hPprime p hp
    have h1 : p ^ k p ≤ s := Nat.pow_log_le_self p (by omega)
    have h2 : B < p ^ (l p + 1) := Nat.lt_pow_succ_log_self hpp.one_lt B
    have h3 : 5 ≤ p ^ l p := five_le_pow_log hpp (hPle p hp) hB
    have h4 : p ^ k p < p ^ (2 * l p + 1) := by
      calc p ^ k p ≤ 5 * B := h1.trans hs5
        _ < 5 * p ^ (l p + 1) := by omega
        _ ≤ p ^ l p * p ^ (l p + 1) := Nat.mul_le_mul_right _ h3
        _ = p ^ (2 * l p + 1) := by rw [← pow_add]; ring_nf
    have h5 : k p < 2 * l p + 1 := (Nat.pow_lt_pow_iff_right hpp.one_lt).mp h4
    change k p ≤ l p + k p / 2
    omega
  have hjle : ∀ p ∈ P, p ^ j p ≤ ⌊√S⌋₊ := by
    intro p hp
    have hpp := hPprime p hp
    apply Nat.le_floor
    rw [Real.le_sqrt (by positivity) (by linarith)]
    have h1 : p ^ k p ≤ s := Nat.pow_log_le_self p (by omega)
    have h2 : (p ^ j p) ^ 2 ≤ p ^ k p := by
      rw [← pow_mul]
      exact Nat.pow_le_pow_right hpp.pos (Nat.div_mul_le_self _ _)
    have h3 : ((p ^ j p : ℕ) : ℝ) ^ 2 ≤ s := by exact_mod_cast h2.trans h1
    exact h3.trans (Nat.floor_le (by linarith))
  have hlB : ∀ p ∈ P, p ^ l p ≤ B := fun p _ => Nat.pow_log_le_self p (by omega)
  have hA := sum_mul_log_le_log_lcmUpTo P hPprime l B hlB
  have hC := sum_mul_log_le_log_lcmUpTo P hPprime j ⌊√S⌋₊ hjle
  calc primePowerLogSum B S = ∑ p ∈ P, (k p : ℝ) * log p := by
        unfold primePowerLogSum
        exact Finset.sum_congr rfl fun p hp => by rw [hfloor p hp]
    _ ≤ ∑ p ∈ P, ((l p : ℝ) * log p + (j p : ℝ) * log p) := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hlog : 0 ≤ log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (hPprime p hp).one_lt.le)
        have : (k p : ℝ) ≤ l p + j p := by exact_mod_cast hkl p hp
        nlinarith
    _ = ∑ p ∈ P, (l p : ℝ) * log p + ∑ p ∈ P, (j p : ℝ) * log p := Finset.sum_add_distrib
    _ ≤ log (Nat.lcmUpto B) + log (Nat.lcmUpto ⌊√S⌋₊) := add_le_add hA hC

/-- **Lemma 2.7**, second inequality (conditional on [Hanson, Theorem 1]): for `B ≥ 1` and
`S ≥ 1`, `log lcm(1, …, B) + log lcm(1, …, ⌊√S⌋) < (B + √S) log 3`. -/
theorem log_lcm_add_log_lcm_lt (hH : HansonLcmBound) (B : ℕ) (hB : 1 ≤ B) (S : ℝ)
    (hS₁ : 1 ≤ S) :
    log (Nat.lcmUpto B) + log (Nat.lcmUpto ⌊√S⌋₊) < (B + √S) * log 3 := by
  have hlog3 : 0 < log (3 : ℝ) := Real.log_pos (by norm_num)
  have hbound : ∀ N : ℕ, 1 ≤ N → log (Nat.lcmUpto N) < N * log 3 := by
    intro N hN
    have h := hH N hN
    have hpos : (0 : ℝ) < Nat.lcmUpto N := by exact_mod_cast Nat.lcmUpto_pos N
    have h' : (Nat.lcmUpto N : ℝ) < (3 : ℝ) ^ N := by exact_mod_cast h
    calc log (Nat.lcmUpto N) < log ((3 : ℝ) ^ N) := Real.log_lt_log hpos h'
      _ = N * log 3 := Real.log_pow _ _
  have ht : 1 ≤ ⌊√S⌋₊ := Nat.le_floor (by simpa using Real.one_le_sqrt.mpr hS₁)
  have htS : (⌊√S⌋₊ : ℝ) ≤ √S := Nat.floor_le (Real.sqrt_nonneg _)
  have h1 := hbound B hB
  have h2 := hbound _ ht
  nlinarith

/-- **Lemma 2.7** (the second inequality conditional on [Hanson, Theorem 1]): for an integer
`B ≥ 9` and a real `1 ≤ S ≤ 5B`,
`Ψ_B(S) ≤ log lcm(1, …, B) + log lcm(1, …, ⌊√S⌋) < (B + √S) log 3`. -/
theorem lcm_bound (hH : HansonLcmBound) (B : ℕ) (hB : 9 ≤ B) (S : ℝ) (hS₁ : 1 ≤ S)
    (hS : S ≤ 5 * B) :
    primePowerLogSum B S ≤ log (Nat.lcmUpto B) + log (Nat.lcmUpto ⌊√S⌋₊) ∧
      log (Nat.lcmUpto B) + log (Nat.lcmUpto ⌊√S⌋₊) < (B + √S) * log 3 :=
  ⟨primePowerLogSum_le_log_lcm B hB S hS₁ hS,
    log_lcm_add_log_lcm_lt hH B (by omega) S hS₁⟩

end ArithmeticOfJacobiPolynomials
