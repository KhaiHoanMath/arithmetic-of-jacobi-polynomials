/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.KanekoZagier.ExplicitCutoff

/-!
# Proposition B.1: prime sums in residue classes modulo `6`, and Hanson's bound

Analytic tools for the proof of Proposition B.1:

* `classInd A B c p` is the indicator of `p ∈ (A, B]`, `p ≡ c (mod 6)`, and
  `sum_classInd_mul_log_le`: `∑_{p ∈ P} 1_{(A,B], c}(p) log p ≤ θ(B; 6, c) - θ(A; 6, c)` for a set
  `P` of primes and `0 ≤ A ≤ B`;
* `chebyshevThetaAP_six_sub_le_small`: the estimate of [BMOR, Theorem 1.9] (the hypothesis
  `BMORThetaSmallBound`) applied to such a difference;
* `sum_mul_log_le_of_pow_le`: Hanson's bound [Hanson, Theorem 1] (`HansonLcmBound`) in the form
  `∑_{p ∈ P} e_p log p ≤ N log 3` whenever `p^{e_p} ≤ N`;
* elementary numerics: `lt_exp_thirteen`, `log_le_div_add_twelve`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Finset

/-! ### Elementary numerics -/

theorem two_seven_lt_exp_one : (2.7 : ℝ) < Real.exp 1 :=
  lt_trans (by norm_num) Real.exp_one_gt_d9

theorem lt_exp_thirteen : (250000 : ℝ) < Real.exp 13 := by
  have h13 : Real.exp 1 ^ 13 = Real.exp 13 := by rw [Real.exp_one_pow]; norm_num
  rw [← h13]
  calc (250000 : ℝ) < (2.7 : ℝ) ^ 13 := by norm_num
    _ < Real.exp 1 ^ 13 := pow_lt_pow_left₀ two_seven_lt_exp_one (by norm_num) (by norm_num)

/-- `log x ≤ x / 250000 + 12` for `x > 0` (the tangent line at `250000`, with
`log 250000 < 13`). -/
theorem log_le_div_add_twelve {x : ℝ} (hx : 0 < x) : Real.log x ≤ x / 250000 + 12 := by
  have h1 := Real.log_le_sub_one_of_pos (show 0 < x / 250000 by positivity)
  rw [Real.log_div hx.ne' (by norm_num)] at h1
  have h2 : Real.log 250000 < 13 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    exact lt_exp_thirteen
  linarith

/-! ### Prime sums over intervals in a class modulo `6` -/

/-- The indicator of `p ∈ (A, B]` with `p ≡ c (mod 6)`. -/
noncomputable def classInd (A B : ℝ) (c : ℤ) (p : ℕ) : ℝ :=
  if A < p ∧ (p : ℝ) ≤ B ∧ (p : ℤ) ≡ c [ZMOD ((6 : ℕ) : ℤ)] then 1 else 0

theorem classInd_eq (A B : ℝ) (c : ℤ) (p : ℕ) : classInd A B c p =
    if A < p ∧ (p : ℝ) ≤ B ∧ (p : ℤ) ≡ c [ZMOD ((6 : ℕ) : ℤ)] then 1 else 0 := (rfl)

theorem classInd_nonneg (A B : ℝ) (c : ℤ) (p : ℕ) : 0 ≤ classInd A B c p := by
  rw [classInd_eq]
  split_ifs <;> norm_num

theorem classInd_eq_one {A B : ℝ} {c : ℤ} {p : ℕ} (h1 : A < p) (h2 : (p : ℝ) ≤ B)
    (h3 : (p : ℤ) ≡ c [ZMOD ((6 : ℕ) : ℤ)]) : classInd A B c p = 1 := by
  simp only [classInd_eq, h1, h2, h3, and_self, ↓reduceIte]

/-- `∑_{p ∈ P} 1_{(A,B], c}(p) log p ≤ θ(B; 6, c) - θ(A; 6, c)` for a set `P` of primes. -/
theorem sum_classInd_mul_log_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {A B : ℝ} (hA : 0 ≤ A)
    (hAB : A ≤ B) (c : ℤ) :
    ∑ p ∈ P, classInd A B c p * Real.log p ≤
      chebyshevThetaAP B 6 c - chebyshevThetaAP A 6 c := by
  classical
  have hsub : ((range (⌊A⌋₊ + 1)).filter
        fun p : ℕ => p.Prime ∧ (p : ℤ) ≡ c [ZMOD ((6 : ℕ) : ℤ)]) ⊆
      (range (⌊B⌋₊ + 1)).filter fun p : ℕ => p.Prime ∧ (p : ℤ) ≡ c [ZMOD ((6 : ℕ) : ℤ)] := by
    intro p hp
    simp only [mem_filter, mem_range] at hp ⊢
    have := Nat.floor_le_floor hAB
    exact ⟨by omega, hp.2⟩
  rw [chebyshevThetaAP_eq, chebyshevThetaAP_eq, ← sum_sdiff hsub, add_sub_cancel_right]
  calc ∑ p ∈ P, classInd A B c p * Real.log p
      = ∑ p ∈ P.filter (fun p : ℕ => A < p ∧ (p : ℝ) ≤ B ∧
          (p : ℤ) ≡ c [ZMOD ((6 : ℕ) : ℤ)]), Real.log p := by
        rw [sum_filter]
        refine sum_congr rfl fun p _ => ?_
        rw [classInd_eq]
        split_ifs <;> simp
    _ ≤ _ := by
        refine sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => Real.log_natCast_nonneg p
        intro p hp
        simp only [mem_filter, mem_sdiff, mem_range] at hp ⊢
        obtain ⟨hpP, h1, h2, h3⟩ := hp
        have hB : p ≤ ⌊B⌋₊ := Nat.le_floor h2
        refine ⟨⟨by omega, hP p hpP, h3⟩, fun h => ?_⟩
        have hpA : p ≤ ⌊A⌋₊ := by omega
        have : (p : ℝ) ≤ A := le_trans (by exact_mod_cast hpA) (Nat.floor_le hA)
        linarith

/-- [BMOR, Theorem 1.9] for an interval: for `1 ≤ A ≤ B ≤ 4·10^13` and `gcd(c, 6) = 1`,
`θ(B; 6, c) - θ(A; 6, c) ≤ (B - A)/2 + 2.072 (√A + √B)`. -/
theorem chebyshevThetaAP_six_sub_le_small (hS : BMORThetaSmallBound) {c : ℤ}
    (hc : Int.gcd c 6 = 1) {A B : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B) (hB : B ≤ 4 * 10 ^ 13) :
    chebyshevThetaAP B 6 c - chebyshevThetaAP A 6 c ≤ (B - A) / 2 + 2.072 * (√A + √B) := by
  have h1 := hS.modSix c hc B B (by linarith) le_rfl hB
  have h2 := hS.modSix c hc A A hA le_rfl (by linarith)
  rw [abs_le] at h1 h2
  linarith [h1.1, h1.2, h2.1, h2.2]

/-! ### Hanson's bound -/

/-- **Hanson's bound** for prime sums ([Hanson, Theorem 1]): if `p^{e_p} ≤ N` for every prime
`p ∈ P`, then `∑_{p ∈ P} e_p log p ≤ N log 3`. -/
theorem sum_mul_log_le_of_pow_le (hH : HansonLcmBound) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (e : ℕ → ℕ) {N : ℕ} (hN : 1 ≤ N) (he : ∀ p ∈ P, p ^ e p ≤ N) :
    ∑ p ∈ P, (e p : ℝ) * Real.log p ≤ N * Real.log 3 := by
  have hL : 0 < (Icc 1 N).lcm id := by
    rw [Nat.pos_iff_ne_zero, Ne, Finset.lcm_eq_zero_iff]
    rintro ⟨x, hx, rfl⟩
    simp at hx
  have hdvd : (∏ p ∈ P, p ^ e p) ∣ (Icc 1 N).lcm id := by
    apply Finset.prod_dvd_of_isRelPrime
    · intro p hp q hq hpq
      rw [Function.onFun, ← Nat.coprime_iff_isRelPrime]
      exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq)
    · intro p hp
      have h1 : p ^ e p ∈ Icc 1 N :=
        Finset.mem_Icc.mpr ⟨Nat.one_le_pow _ _ (hP p hp).pos, he p hp⟩
      exact Finset.dvd_lcm (f := id) h1
  have hle : ((∏ p ∈ P, p ^ e p : ℕ) : ℝ) ≤ ((Icc 1 N).lcm id : ℕ) := by
    exact_mod_cast Nat.le_of_dvd hL hdvd
  have hpos : (0 : ℝ) < ((∏ p ∈ P, p ^ e p : ℕ) : ℝ) := by
    have : 0 < ∏ p ∈ P, p ^ e p := Finset.prod_pos fun p hp => pow_pos (hP p hp).pos _
    exact_mod_cast this
  have hlog : Real.log ((∏ p ∈ P, p ^ e p : ℕ) : ℝ) = ∑ p ∈ P, (e p : ℝ) * Real.log p := by
    push_cast
    rw [Real.log_prod]
    · exact Finset.sum_congr rfl fun p _ => Real.log_pow _ _
    · intro p hp
      exact pow_ne_zero _ (by exact_mod_cast (hP p hp).ne_zero)
  have h3 : (((Icc 1 N).lcm id : ℕ) : ℝ) < (3 : ℝ) ^ N := by exact_mod_cast hH N hN
  have hLpos : (0 : ℝ) < ((Icc 1 N).lcm id : ℕ) := by exact_mod_cast hL
  have h4 := Real.log_lt_log hLpos h3
  rw [Real.log_pow] at h4
  rw [← hlog]
  linarith [Real.log_le_log hpos hle]

/-- `∑_{p ∈ P} log p ≤ N log 3` for a set `P` of primes `p ≤ N` ([Hanson, Theorem 1]). -/
theorem sum_log_le_of_le (hH : HansonLcmBound) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {N : ℕ} (hN : 1 ≤ N) (hle : ∀ p ∈ P, p ≤ N) :
    ∑ p ∈ P, Real.log p ≤ N * Real.log 3 := by
  have h := sum_mul_log_le_of_pow_le hH P hP (fun _ => 1) hN (fun p hp => by
    simpa using hle p hp)
  simpa using h

end ArithmeticOfJacobiPolynomials
