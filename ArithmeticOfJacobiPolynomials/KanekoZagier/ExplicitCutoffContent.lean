/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.KanekoZagier.ExplicitCutoffPrimes

/-!
# Proposition B.1: content and the good-prime sum (Appendix B.1)

For `λ, μ ∈ {-1, 1}` (the argument `l` is `λ`), `M = 12n + 5` and a prime `p ≥ 5`, write
`W_p = v_p(g_n) + 1_{p ≤ n} E_p(n)`, so that `S_n + log g_n = ∑_p W_p log p`
(`log_kzContent_eq_sum`, `kzGoodPrimeSum_eq_sum`). This file proves:

* `kz_weight_le`: `W_p ≤ 1 + 3(⌊log_p M⌋ - 1)` (every higher-level coefficient contribution is
  at most two, `kzCoeffLevel_le_two`, and `e_{p^h} ≤ 1`);
* `kz_weight_le_retained`: for `p ≥ 13`, `n < 7p` and `p² > M`, `W_p = m_p + 1_{p ≤ n} e_p` is at
  most the indicator of the retained intervals (`kzRetainedInd`): with `ℓ = ⌊n/p⌋`,
  `r = 2λ + 3μ`, the first class `p ≡ 3 + 2λ (mod 6)` and the second class `p ≡ 3 - 2λ`,
  `((6n+r)/(6ℓ+1), n/ℓ]` and `(n/(ℓ+1), (2n+μ)/(2ℓ+1)]` (first class),
  `(n/(ℓ+1), (3n+λ)/(3ℓ+1)]` (second class) for `p ≤ n`, and `(n, (3n+λ)/2]` (first class),
  `((6n+r)/5, 2n+μ]` (second class) for `p > n`;
* `kz_content_goodPrime_le`: for `n ≥ 250000`, with [Hanson, Theorem 1] (`HansonLcmBound`),
  `S_n + log g_n ≤ ⌊n/7⌋ log 3 + 3 ∑_p (⌊log_p M⌋ - 1) log p + ∑_p 1_{retained}(p) log p`
  (the manuscript's `T_0(n) + 3 H(M)`, with the discarded primes at most `n/7`);
* `sum_kzRetainedInd_mul_log_le`: the retained sum is bounded through any bound `F(A, B)` for
  `θ(B; 6, c) - θ(A; 6, c)` on intervals `n/7 ≤ A ≤ B ≤ 2n+1`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Finset

/-! ### The retained intervals -/

/-- `(6n + r)/(6t + 1)`, `r = 2λ + 3μ`. -/
noncomputable def kzEndA (l μ : ℤ) (n : ℕ) (t : ℝ) : ℝ := (6 * n + (2 * l + 3 * μ)) / (6 * t + 1)

theorem kzEndA_eq (l μ : ℤ) (n : ℕ) (t : ℝ) :
    kzEndA l μ n t = (6 * n + (2 * l + 3 * μ)) / (6 * t + 1) := (rfl)

/-- `(2n + μ)/(2t + 1)`. -/
noncomputable def kzEndC (μ : ℤ) (n : ℕ) (t : ℝ) : ℝ := (2 * n + μ) / (2 * t + 1)

theorem kzEndC_eq (μ : ℤ) (n : ℕ) (t : ℝ) : kzEndC μ n t = (2 * n + μ) / (2 * t + 1) := (rfl)

/-- `(3n + λ)/(3t + 1)`. -/
noncomputable def kzEndD (l : ℤ) (n : ℕ) (t : ℝ) : ℝ := (3 * n + l) / (3 * t + 1)

theorem kzEndD_eq (l : ℤ) (n : ℕ) (t : ℝ) : kzEndD l n t = (3 * n + l) / (3 * t + 1) := (rfl)

/-- The three retained intervals with `ℓ = k + 1`. -/
noncomputable def kzRetainedTerm (l μ : ℤ) (n p k : ℕ) : ℝ :=
  classInd (kzEndA l μ n (k + 1)) (n / (k + 1)) (3 + 2 * l) p +
    classInd (n / (k + 1 + 1)) (kzEndC μ n (k + 1)) (3 + 2 * l) p +
    classInd (n / (k + 1 + 1)) (kzEndD l n (k + 1)) (3 - 2 * l) p

theorem kzRetainedTerm_eq (l μ : ℤ) (n p k : ℕ) : kzRetainedTerm l μ n p k =
    classInd (kzEndA l μ n (k + 1)) (n / (k + 1)) (3 + 2 * l) p +
      classInd (n / (k + 1 + 1)) (kzEndC μ n (k + 1)) (3 + 2 * l) p +
      classInd (n / (k + 1 + 1)) (kzEndD l n (k + 1)) (3 - 2 * l) p := (rfl)

/-- The indicator of the retained intervals (`1 ≤ ℓ ≤ 6`, and the two intervals beyond `n`). -/
noncomputable def kzRetainedInd (l μ : ℤ) (n p : ℕ) : ℝ :=
  ∑ k ∈ range 6, kzRetainedTerm l μ n p k + classInd n ((3 * n + l) / 2) (3 + 2 * l) p +
    classInd ((6 * n + (2 * l + 3 * μ)) / 5) (2 * n + μ) (3 - 2 * l) p

theorem kzRetainedInd_eq (l μ : ℤ) (n p : ℕ) : kzRetainedInd l μ n p =
    ∑ k ∈ range 6, kzRetainedTerm l μ n p k + classInd n ((3 * n + l) / 2) (3 + 2 * l) p +
      classInd ((6 * n + (2 * l + 3 * μ)) / 5) (2 * n + μ) (3 - 2 * l) p := (rfl)

theorem kzRetainedTerm_nonneg (l μ : ℤ) (n p k : ℕ) : 0 ≤ kzRetainedTerm l μ n p k := by
  rw [kzRetainedTerm_eq]
  have := classInd_nonneg (kzEndA l μ n (k + 1)) (n / (k + 1)) (3 + 2 * l) p
  have := classInd_nonneg (n / (k + 1 + 1)) (kzEndC μ n (k + 1)) (3 + 2 * l) p
  have := classInd_nonneg (n / (k + 1 + 1)) (kzEndD l n (k + 1)) (3 - 2 * l) p
  linarith

theorem kzRetainedInd_nonneg (l μ : ℤ) (n p : ℕ) : 0 ≤ kzRetainedInd l μ n p := by
  rw [kzRetainedInd_eq]
  have := sum_nonneg fun k (_ : k ∈ range 6) => kzRetainedTerm_nonneg l μ n p k
  have := classInd_nonneg n ((3 * n + l) / 2) (3 + 2 * l) p
  have := classInd_nonneg ((6 * n + (2 * l + 3 * μ)) / 5) (2 * n + μ) (3 - 2 * l) p
  linarith

theorem one_le_kzRetainedInd_of_term {l μ : ℤ} {n p k : ℕ} (hk : k < 6)
    (h : 1 ≤ kzRetainedTerm l μ n p k) : 1 ≤ kzRetainedInd l μ n p := by
  have hs : kzRetainedTerm l μ n p k ≤ ∑ j ∈ range 6, kzRetainedTerm l μ n p j :=
    single_le_sum (fun j _ => kzRetainedTerm_nonneg l μ n p j) (mem_range.mpr hk)
  rw [kzRetainedInd_eq]
  have := classInd_nonneg n ((3 * n + l) / 2) (3 + 2 * l) p
  have := classInd_nonneg ((6 * n + (2 * l + 3 * μ)) / 5) (2 * n + μ) (3 - 2 * l) p
  linarith

/-- Sizes of the retained endpoints for `1 ≤ t ≤ 6` and `n ≥ 250000`. -/
theorem kz_endpoints_valid {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) {n : ℕ}
    (hn : 250000 ≤ n) {t : ℝ} (ht1 : 1 ≤ t) (ht6 : t ≤ 6) :
    (n : ℝ) / 7 ≤ kzEndA l μ n t ∧ kzEndA l μ n t ≤ n / t ∧ (n : ℝ) / t ≤ 2 * n + 1 ∧
      (n : ℝ) / 7 ≤ n / (t + 1) ∧ (n : ℝ) / (t + 1) ≤ kzEndC μ n t ∧
      kzEndC μ n t ≤ 2 * n + 1 ∧ (n : ℝ) / (t + 1) ≤ kzEndD l n t ∧
      kzEndD l n t ≤ 2 * n + 1 := by
  have hN : (250000 : ℝ) ≤ n := by exact_mod_cast hn
  have hl' : -1 ≤ (l : ℝ) ∧ (l : ℝ) ≤ 1 := by rcases hl with rfl | rfl <;> norm_num
  have hμ' : -1 ≤ (μ : ℝ) ∧ (μ : ℝ) ≤ 1 := by rcases hμ with rfl | rfl <;> norm_num
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have q1 := mul_le_mul_of_nonneg_left ht6 hn0
  have q2 := mul_le_mul_of_nonneg_left ht1 (show (0 : ℝ) ≤ 2 * n + 1 by linarith)
  have q3 := mul_le_mul_of_nonneg_right (show (2 * l + 3 * μ : ℝ) ≤ 5 by linarith) ht0
  have q4 := mul_le_mul_of_nonneg_right hμ'.1 ht0
  have q5 := mul_le_mul_of_nonneg_right hl'.1 ht0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [kzEndA_eq, div_le_div_iff₀ (by norm_num) (by linarith)]
    linarith
  · rw [kzEndA_eq, div_le_div_iff₀ (by linarith) (by linarith)]
    linarith
  · rw [div_le_iff₀ (by linarith)]
    linarith
  · rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    linarith
  · rw [kzEndC_eq, div_le_div_iff₀ (by linarith) (by linarith)]
    linarith
  · rw [kzEndC_eq, div_le_iff₀ (by linarith)]
    linarith
  · rw [kzEndD_eq, div_le_div_iff₀ (by linarith) (by linarith)]
    linarith
  · rw [kzEndD_eq, div_le_iff₀ (by linarith)]
    linarith

/-! ### Residues and the first-level indicators -/

section Weights

variable {p : ℕ} [hp : Fact p.Prime]

/-- `a_p ∈ {(p + λ)/3, (2p + λ)/3}` and `b_p = (p + μ)/2`. -/
theorem kz_residue_cases {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) (hp5 : 5 ≤ p) :
    (3 * (kzResA l p : ℤ) = p + l ∨ 3 * (kzResA l p : ℤ) = 2 * p + l) ∧
      2 * (kzResB μ p : ℤ) = p + μ := by
  have hA := kzResA_dvd (p := p) l hp5 1
  have hB := kzResB_dvd (p := p) μ hp5 1
  obtain ⟨hA1, hAp⟩ := kzResA_spec (p := p) hl hp5 (h := 1) le_rfl
  obtain ⟨hB1, hBp⟩ := kzResB_spec (p := p) hμ hp5 (h := 1) le_rfl
  simp only [pow_one, Nat.cast_ofNat] at hA hB hA1 hAp hB1 hBp
  obtain ⟨k, hk⟩ := hA
  obtain ⟨k', hk'⟩ := hB
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
  have hk1 : 0 < k := by
    by_contra h
    have h' : k ≤ 0 := by omega
    have : (p : ℤ) * k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp0.le h'
    rcases hl with rfl | rfl <;> omega
  have hk3 : k < 3 := by
    by_contra h
    have h' : 3 ≤ k := by omega
    have : (p : ℤ) * 3 ≤ p * k := mul_le_mul_of_nonneg_left h' hp0.le
    rcases hl with rfl | rfl <;> omega
  have hk'1 : 0 < k' := by
    by_contra h
    have h' : k' ≤ 0 := by omega
    have : (p : ℤ) * k' ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp0.le h'
    rcases hμ with rfl | rfl <;> omega
  have hk'2 : k' < 2 := by
    by_contra h
    have h' : 2 ≤ k' := by omega
    have : (p : ℤ) * 2 ≤ p * k' := mul_le_mul_of_nonneg_left h' hp0.le
    rcases hμ with rfl | rfl <;> omega
  have hk'e : k' = 1 := by omega
  subst hk'e
  refine ⟨?_, by linarith⟩
  rcases (show k = 1 ∨ k = 2 by omega) with rfl | rfl
  · left; linarith
  · right; linarith

/-- Below `n`: if `m_p + e_p = 1` then `p` lies in the corresponding first-level intervals. -/
theorem levelM_add_levelE_class {q A B s : ℕ} {l μ : ℤ} (hl : l = 1 ∨ l = -1)
    (hμ : μ = 1 ∨ μ = -1) (hq : 13 ≤ q)
    (hA : 3 * (A : ℤ) = q + l ∨ 3 * (A : ℤ) = 2 * q + l) (hB : 2 * (B : ℤ) = q + μ)
    (h1 : (levelM q A B s : ℤ) + levelE q A B s = 1) :
    (3 * (A : ℤ) = q + l ∧ (6 * (s : ℤ) + (2 * l + 3 * μ) < q ∨ (q : ℤ) ≤ 2 * s + μ)) ∨
      (3 * (A : ℤ) = 2 * q + l ∧ (q : ℤ) ≤ 3 * s + l) := by
  have hAq : A < q := by rcases hl with rfl | rfl <;> omega
  have hBq : B < q := by rcases hμ with rfl | rfl <;> omega
  have hcd := div_mod_cases_two (x := A + B) (q := q) (by omega)
  have hEa := carryInd_cases q s A
  have hEb := carryInd_cases q s B
  have hEc := carryInd_cases q s ((A + B) % q)
  have hM := levelM_cases q A B s
  have hEta := levelEta_cases q A B
  have hBs := levelBStar_cases q A B
  rw [levelE_eq] at h1
  rcases hl with rfl | rfl <;> rcases hμ with rfl | rfl <;> omega

/-- Beyond `n` (`s = n`): if `m_p = 1` then `p` lies in the corresponding content interval. -/
theorem levelM_class_of_gt {q A B s : ℕ} {l μ : ℤ} (hl : l = 1 ∨ l = -1)
    (hμ : μ = 1 ∨ μ = -1) (hq : 13 ≤ q)
    (hA : 3 * (A : ℤ) = q + l ∨ 3 * (A : ℤ) = 2 * q + l) (hB : 2 * (B : ℤ) = q + μ)
    (h1 : levelM q A B s = 1) :
    (3 * (A : ℤ) = q + l ∧ 2 * (q : ℤ) ≤ 3 * s + l) ∨
      (3 * (A : ℤ) = 2 * q + l ∧ (q : ℤ) ≤ 2 * s + μ ∧ 6 * (s : ℤ) + (2 * l + 3 * μ) < 5 * q) := by
  have hAq : A < q := by rcases hl with rfl | rfl <;> omega
  have hBq : B < q := by rcases hμ with rfl | rfl <;> omega
  have hcd := div_mod_cases_two (x := A + B) (q := q) (by omega)
  have hEa := carryInd_cases q s A
  have hEb := carryInd_cases q s B
  have hEc := carryInd_cases q s ((A + B) % q)
  have hM := levelM_cases q A B s
  rcases hl with rfl | rfl <;> rcases hμ with rfl | rfl <;> omega

theorem kz_class_first {q A : ℕ} {l : ℤ} (hl : l = 1 ∨ l = -1) (hA : 3 * (A : ℤ) = q + l)
    (hodd : q % 2 = 1) : (q : ℤ) ≡ 3 + 2 * l [ZMOD ((6 : ℕ) : ℤ)] := by
  unfold Int.ModEq
  push_cast
  rcases hl with rfl | rfl <;> omega

theorem kz_class_second {q A : ℕ} {l : ℤ} (hl : l = 1 ∨ l = -1) (hA : 3 * (A : ℤ) = 2 * q + l)
    (hodd : q % 2 = 1) : (q : ℤ) ≡ 3 - 2 * l [ZMOD ((6 : ℕ) : ℤ)] := by
  unfold Int.ModEq
  push_cast
  rcases hl with rfl | rfl <;> omega

/-- The retained indicator for `p ≤ n < 7p`. -/
theorem one_le_kzRetainedInd_of_le {l μ : ℤ} (hl : l = 1 ∨ l = -1)
    {n q A : ℕ} (hq : q.Prime) (hq13 : 13 ≤ q) (hqn : q ≤ n) (h7 : n < 7 * q)
    (h : (3 * (A : ℤ) = q + l ∧ (6 * ((n % q : ℕ) : ℤ) + (2 * l + 3 * μ) < q ∨
        (q : ℤ) ≤ 2 * ((n % q : ℕ) : ℤ) + μ)) ∨
      (3 * (A : ℤ) = 2 * q + l ∧ (q : ℤ) ≤ 3 * ((n % q : ℕ) : ℤ) + l)) :
    1 ≤ kzRetainedInd l μ n q := by
  have hodd := hq.eq_two_or_odd.resolve_left (by omega)
  obtain ⟨L, hL⟩ : ∃ L, L = n / q := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := by rw [hL]; exact Nat.div_pos hqn hq.pos
  have hL6 : L ≤ 6 := by
    have := (Nat.div_lt_iff_lt_mul hq.pos).mpr (show n < 7 * q by omega)
    omega
  have hdm : L * q + n % q = n := by rw [hL]; exact Nat.div_add_mod' n q
  obtain ⟨s, hs⟩ : ∃ s, s = n % q := ⟨_, rfl⟩
  rw [← hs] at h hdm
  have hsq : s < q := by rw [hs]; exact Nat.mod_lt n hq.pos
  have hnR : (n : ℝ) = (L : ℝ) * q + s := by exact_mod_cast hdm.symm
  have hsR : (s : ℝ) < q := by exact_mod_cast hsq
  have hL1R : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have ht : (((L - 1 : ℕ) : ℝ) + 1) = (L : ℝ) := by
    rw [Nat.cast_sub hL1, Nat.cast_one]; ring
  apply one_le_kzRetainedInd_of_term (k := L - 1) (by omega)
  rw [kzRetainedTerm_eq, ht]
  have c1 := classInd_nonneg (kzEndA l μ n L) (n / L) (3 + 2 * l) q
  have c2 := classInd_nonneg (n / (L + 1)) (kzEndC μ n L) (3 + 2 * l) q
  have c3 := classInd_nonneg (n / (L + 1)) (kzEndD l n L) (3 - 2 * l) q
  have hlow : (n : ℝ) / (L + 1) < q := by
    rw [div_lt_iff₀ (by linarith)]
    linarith
  rcases h with ⟨hA, h6 | h2⟩ | ⟨hA, h3⟩
  · have h6R : 6 * (s : ℝ) + (2 * l + 3 * μ) < q := by exact_mod_cast h6
    have e : classInd (kzEndA l μ n L) (n / L) (3 + 2 * l) q = 1 := by
      refine classInd_eq_one ?_ ?_ (kz_class_first hl hA hodd)
      · rw [kzEndA_eq, div_lt_iff₀ (by linarith)]
        linarith
      · rw [le_div_iff₀ (by linarith)]
        have : (0 : ℝ) ≤ s := Nat.cast_nonneg s
        linarith
    linarith
  · have h2R : (q : ℝ) ≤ 2 * s + μ := by exact_mod_cast h2
    have e : classInd (n / (L + 1)) (kzEndC μ n L) (3 + 2 * l) q = 1 := by
      refine classInd_eq_one hlow ?_ (kz_class_first hl hA hodd)
      rw [kzEndC_eq, le_div_iff₀ (by linarith)]
      linarith
    linarith
  · have h3R : (q : ℝ) ≤ 3 * s + l := by exact_mod_cast h3
    have e : classInd (n / (L + 1)) (kzEndD l n L) (3 - 2 * l) q = 1 := by
      refine classInd_eq_one hlow ?_ (kz_class_second hl hA hodd)
      rw [kzEndD_eq, le_div_iff₀ (by linarith)]
      linarith
    linarith

/-- The retained indicator for `p > n`. -/
theorem one_le_kzRetainedInd_of_gt {l μ : ℤ} (hl : l = 1 ∨ l = -1) {n q A : ℕ} (hq : q.Prime)
    (hq13 : 13 ≤ q) (hnq : n < q)
    (h : (3 * (A : ℤ) = q + l ∧ 2 * (q : ℤ) ≤ 3 * n + l) ∨
      (3 * (A : ℤ) = 2 * q + l ∧ (q : ℤ) ≤ 2 * n + μ ∧ 6 * (n : ℤ) + (2 * l + 3 * μ) < 5 * q)) :
    1 ≤ kzRetainedInd l μ n q := by
  have hodd := hq.eq_two_or_odd.resolve_left (by omega)
  have hnqR : (n : ℝ) < q := by exact_mod_cast hnq
  rw [kzRetainedInd_eq]
  have hs := sum_nonneg fun k (_ : k ∈ range 6) => kzRetainedTerm_nonneg l μ n q k
  have c4 := classInd_nonneg n ((3 * n + l) / 2) (3 + 2 * l) q
  have c5 := classInd_nonneg ((6 * n + (2 * l + 3 * μ)) / 5) (2 * n + μ) (3 - 2 * l) q
  rcases h with ⟨hA, h1⟩ | ⟨hA, h2, h3⟩
  · have h1R : 2 * (q : ℝ) ≤ 3 * n + l := by exact_mod_cast h1
    have e : classInd n ((3 * n + l) / 2) (3 + 2 * l) q = 1 := by
      refine classInd_eq_one hnqR ?_ (kz_class_first hl hA hodd)
      rw [le_div_iff₀ (by norm_num)]
      linarith
    linarith
  · have h2R : (q : ℝ) ≤ 2 * n + μ := by exact_mod_cast h2
    have h3R : 6 * (n : ℝ) + (2 * l + 3 * μ) < 5 * q := by exact_mod_cast h3
    have e : classInd ((6 * n + (2 * l + 3 * μ)) / 5) (2 * n + μ) (3 - 2 * l) q = 1 := by
      refine classInd_eq_one ?_ h2R (kz_class_second hl hA hodd)
      rw [div_lt_iff₀ (by norm_num)]
      linarith
    linarith

/-! ### The weights `W_p` -/

theorem kzCoeffLevel_le_two (l μ : ℤ) {n j q : ℕ} (hq : 0 < q) (hj : j ≤ n) :
    kzCoeffLevel l μ n j q ≤ 2 := by
  rw [kzCoeffLevel_eq, zero_add]
  have h1 := Nat.add_div (a := n - j) (b := j + kzResA l q) hq
  have h2 := Nat.add_div (a := j) (b := n + kzResA l q + kzResB μ q) hq
  rw [show n - j + (j + kzResA l q) = n + kzResA l q by omega] at h1
  split_ifs at h1 h2 <;> omega

theorem kzLevelM_le_one (l μ : ℤ) (n q : ℕ) : kzLevelM l μ n q ≤ 1 := by
  rw [kzLevelM_eq, levelM_eq]
  split_ifs <;> omega

/-- `v_p(g_n) ≤ m_p + 2(H - 1)` whenever `12n + 5 < p^{H+1}`, `H ≥ 1`. -/
theorem padicValNat_kzContent_le {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    (hp5 : 5 ≤ p) (n : ℕ) {H : ℕ} (hH1 : 1 ≤ H) (hH : 12 * n + 5 < p ^ (H + 1)) :
    padicValNat p (kzContent l μ n) ≤ kzLevelM l μ n p + 2 * (H - 1) := by
  obtain ⟨ha1, haq⟩ := kzResA_spec hl hp5 (h := 1) le_rfl
  obtain ⟨-, hbq⟩ := kzResB_spec hμ hp5 (h := 1) le_rfl
  rw [pow_one] at haq ha1 hbq
  obtain ⟨j, hj, hjle⟩ := level_coeff_attained (q := p) (n := n) hp.out.pos ha1 haq hbq
  have hval := padicValRat_kzKappa_mul_coeff_eq_sum hl hμ hp5 hj hH
  rw [Finset.Icc_eq_cons_Ioc hH1, Finset.sum_cons, pow_one] at hval
  have hrest : ∑ h ∈ Ioc 1 H, kzCoeffLevel l μ n j (p ^ h) ≤ 2 * ((H - 1 : ℕ) : ℤ) := by
    calc ∑ h ∈ Ioc 1 H, kzCoeffLevel l μ n j (p ^ h) ≤ ∑ _h ∈ Ioc 1 H, (2 : ℤ) :=
          sum_le_sum fun h _ => kzCoeffLevel_le_two l μ (pow_pos hp.out.pos h) hj
      _ = 2 * ((H - 1 : ℕ) : ℤ) := by rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_comm]
  have hlev : kzCoeffLevel l μ n j p ≤ (kzLevelM l μ n p : ℤ) := by
    rw [kzCoeffLevel_eq, kzLevelM_eq]
    exact hjle
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
      (padicValInt p ((kzScaled l μ n).coeff j) : ℤ) := by exact_mod_cast h1
  have h3 : (padicValNat p (kzContent l μ n) : ℤ) ≤
      kzLevelM l μ n p + 2 * ((H - 1 : ℕ) : ℤ) := by linarith
  exact_mod_cast h3

/-- `E_p(n) ≤ e_p + (⌊log_p M⌋ - 1)` when `p ≤ M`. -/
theorem kzBudget_le_kzLevelE {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    (hp5 : 5 ≤ p) (n : ℕ) (hK : 1 ≤ Nat.log p (12 * n + 5)) :
    kzBudget l μ n p ≤ kzLevelE l μ n p + ((Nat.log p (12 * n + 5) - 1 : ℕ) : ℤ) := by
  rw [kzBudget_eq, Finset.Icc_eq_cons_Ioc hK, Finset.sum_cons, pow_one]
  have : ∑ h ∈ Ioc 1 (Nat.log p (12 * n + 5)), kzLevelE l μ n (p ^ h) ≤
      ∑ _h ∈ Ioc 1 (Nat.log p (12 * n + 5)), (1 : ℤ) := by
    refine sum_le_sum fun h hh => ?_
    have hh1 : 1 ≤ h := by have := (mem_Ioc.mp hh).1; omega
    rcases (kzLevelE_mem hl hμ hp5 hh1 n).1 with h0 | h1 <;> omega
  rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one] at this
  linarith

/-- **`W_p ≤ 1 + 3(⌊log_p M⌋ - 1)`** for every prime `p ≥ 5`. -/
theorem kz_weight_le {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) (hp5 : 5 ≤ p)
    (n : ℕ) :
    (padicValNat p (kzContent l μ n) : ℝ) + (if p ≤ n then (kzBudget l μ n p : ℝ) else 0) ≤
      1 + 3 * ((Nat.log p (12 * n + 5) - 1 : ℕ) : ℝ) := by
  have hm1 := kzLevelM_le_one l μ n p
  obtain ⟨he, hme⟩ := kzLevelE_mem hl hμ hp5 (h := 1) le_rfl n
  rw [pow_one] at he hme
  by_cases hpn : p ≤ n
  · have hK : 1 ≤ Nat.log p (12 * n + 5) :=
      Nat.le_log_of_pow_le hp.out.one_lt (by rw [pow_one]; omega)
    have hv := padicValNat_kzContent_le hl hμ hp5 n hK
      (Nat.lt_pow_succ_log_self hp.out.one_lt _)
    have hE := kzBudget_le_kzLevelE hl hμ hp5 n hK
    simp only [hpn, ↓reduceIte]
    have hZ : (padicValNat p (kzContent l μ n) : ℤ) + kzBudget l μ n p ≤
        1 + 3 * ((Nat.log p (12 * n + 5) - 1 : ℕ) : ℤ) := by
      rcases he with h0 | h1 <;> omega
    have hZ' : (((padicValNat p (kzContent l μ n) : ℤ) + kzBudget l μ n p : ℤ) : ℝ) ≤
        ((1 + 3 * ((Nat.log p (12 * n + 5) - 1 : ℕ) : ℤ) : ℤ) : ℝ) := Int.cast_le.mpr hZ
    simp only [Int.cast_add, Int.cast_natCast, Int.cast_mul, Int.cast_one, Int.cast_ofNat] at hZ'
    exact hZ'
  · simp only [hpn, ↓reduceIte, add_zero]
    have hH : 12 * n + 5 < p ^ (max 1 (Nat.log p (12 * n + 5)) + 1) :=
      lt_of_lt_of_le (Nat.lt_pow_succ_log_self hp.out.one_lt _)
        (Nat.pow_le_pow_right hp.out.pos (by omega))
    have hv := padicValNat_kzContent_le hl hμ hp5 n (le_max_left 1 _) hH
    have : padicValNat p (kzContent l μ n) ≤ 1 + 3 * (Nat.log p (12 * n + 5) - 1) := by
      omega
    exact_mod_cast this

/-- For `p² > M`, `W_p = m_p + 1_{p ≤ n} e_p`. -/
theorem kz_weight_eq_of_sq_gt {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    (hp5 : 5 ≤ p) (n : ℕ) (hpM : 12 * n + 5 < p ^ 2) :
    (padicValNat p (kzContent l μ n) : ℝ) + (if p ≤ n then (kzBudget l μ n p : ℝ) else 0) =
      (kzLevelM l μ n p : ℝ) + (if p ≤ n then (kzLevelE l μ n p : ℝ) else 0) := by
  rw [padicValNat_kzContent_eq_kzLevelM hl hμ hp5 n hpM]
  by_cases hpn : p ≤ n
  · simp only [hpn, ↓reduceIte]
    have h2 := Nat.log_lt_of_lt_pow (b := p) (by omega) hpM
    have h1 : 1 ≤ Nat.log p (12 * n + 5) :=
      Nat.le_log_of_pow_le hp.out.one_lt (by rw [pow_one]; omega)
    have hK : Nat.log p (12 * n + 5) = 1 := by omega
    rw [kzBudget_eq, hK, Finset.Icc_self, Finset.sum_singleton, pow_one]
  · simp only [hpn, ↓reduceIte]

end Weights

/-- **`W_p` is at most the retained indicator** for a prime `p ≥ 13` with `n < 7p` and
`p² > 12n + 5`. -/
theorem kz_weight_le_retained {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    {n p : ℕ} (hp : p.Prime) (hp13 : 13 ≤ p) (h7 : n < 7 * p) (hpM : 12 * n + 5 < p ^ 2) :
    (padicValNat p (kzContent l μ n) : ℝ) + (if p ≤ n then (kzBudget l μ n p : ℝ) else 0) ≤
      kzRetainedInd l μ n p := by
  have := Fact.mk hp
  have hp5 : 5 ≤ p := by omega
  rw [kz_weight_eq_of_sq_gt hl hμ hp5 n hpM]
  obtain ⟨hA, hB⟩ := kz_residue_cases (p := p) hl hμ hp5
  obtain ⟨he, hme⟩ := kzLevelE_mem hl hμ hp5 (h := 1) le_rfl n
  rw [pow_one] at he hme
  have hm1 := kzLevelM_le_one l μ n p
  have hnn := kzRetainedInd_nonneg l μ n p
  by_cases hpn : p ≤ n
  · simp only [hpn, ↓reduceIte]
    rcases (show (kzLevelM l μ n p : ℤ) + kzLevelE l μ n p = 0 ∨
        (kzLevelM l μ n p : ℤ) + kzLevelE l μ n p = 1 by omega) with h0 | h1
    · have : (kzLevelM l μ n p : ℝ) + (kzLevelE l μ n p : ℝ) = 0 := by exact_mod_cast h0
      linarith
    · have hR : (kzLevelM l μ n p : ℝ) + (kzLevelE l μ n p : ℝ) = 1 := by exact_mod_cast h1
      rw [kzLevelM_eq, kzLevelE_eq] at h1
      have hc := levelM_add_levelE_class hl hμ hp13 hA hB h1
      have := one_le_kzRetainedInd_of_le (μ := μ) hl hp hp13 hpn h7 hc
      linarith
  · simp only [hpn, ↓reduceIte, add_zero]
    rcases (show kzLevelM l μ n p = 0 ∨ kzLevelM l μ n p = 1 by omega) with h0 | h1
    · rw [h0, Nat.cast_zero]
      exact hnn
    · have h1' := h1
      rw [kzLevelM_eq, Nat.mod_eq_of_lt (show n < p by omega)] at h1'
      have hc := levelM_class_of_gt hl hμ hp13 hA hB h1'
      have := one_le_kzRetainedInd_of_gt (μ := μ) hl hp hp13 (show n < p by omega) hc
      rw [h1, Nat.cast_one]
      exact this

/-! ### Summing over primes -/

/-- `S_n = ∑_{5 ≤ p ≤ X} 1_{p ≤ n} E_p(n) log p` for `X ≥ n`. -/
theorem kzGoodPrimeSum_eq_sum (l μ : ℤ) (n X : ℕ) (hX : n ≤ X) :
    kzGoodPrimeSum l μ n = ∑ p ∈ (Icc 5 X).filter Nat.Prime,
      (if p ≤ n then (kzBudget l μ n p : ℝ) else 0) * Real.log p := by
  rw [kzGoodPrimeSum_eq]
  have e : (Icc 5 n).filter Nat.Prime = ((Icc 5 X).filter Nat.Prime).filter (· ≤ n) := by
    ext p
    simp only [mem_filter, mem_Icc]
    exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨⟨h1, by omega⟩, h3⟩, h2⟩,
      fun ⟨⟨⟨h1, _⟩, h3⟩, h2⟩ => ⟨⟨h1, h2⟩, h3⟩⟩
  rw [e, sum_filter]
  refine sum_congr rfl fun p _ => ?_
  split_ifs <;> simp

/-- **(Appendix B.1), the combined inequality (B.6) with the small and discarded primes**
(conditional on [Hanson, Theorem 1]): for `n ≥ 250000` and `M = 12n + 5`,
`S_n + log g_n ≤ log 385 + ⌊n/7⌋ log 3 + 3 ∑_{5 ≤ p ≤ M} (⌊log_p M⌋ - 1) log p
  + ∑_{5 ≤ p ≤ M} 1_{retained}(p) log p`,
where `∑_p (⌊log_p M⌋ - 1) log p` is `H(M)` (restricted to `p ≥ 5`) and the other three terms are
`T_0(n)`: the small primes `5, 7, 11` contribute at most `log 385`, the discarded primes
`p ≥ 13` (`7p ≤ n`) are at most `n/7` and are bounded by Hanson's theorem. -/
theorem kz_content_goodPrime_le (hH : HansonLcmBound) {l μ : ℤ} (hl : l = 1 ∨ l = -1)
    (hμ : μ = 1 ∨ μ = -1) {n : ℕ} (hn : 250000 ≤ n) :
    kzGoodPrimeSum l μ n + Real.log (kzContent l μ n) ≤
      Real.log 385 + ((n / 7 : ℕ) : ℝ) * Real.log 3 +
      3 * ∑ p ∈ (Icc 5 (12 * n + 5)).filter Nat.Prime,
        ((Nat.log p (12 * n + 5) - 1 : ℕ) : ℝ) * Real.log p +
      ∑ p ∈ (Icc 5 (12 * n + 5)).filter Nat.Prime, kzRetainedInd l μ n p * Real.log p := by
  rw [kzGoodPrimeSum_eq_sum l μ n (12 * n + 5) (by omega),
    log_kzContent_eq_sum hl hμ n, ← sum_add_distrib]
  have hPmem : ∀ p ∈ (Icc 5 (12 * n + 5)).filter Nat.Prime, p.Prime ∧ 5 ≤ p :=
    fun p hp => ⟨(mem_filter.mp hp).2, (mem_Icc.mp (mem_filter.mp hp).1).1⟩
  generalize (Icc 5 (12 * n + 5)).filter Nat.Prime = P at hPmem ⊢
  have hterm : ∀ p ∈ P,
      (if p ≤ n then (kzBudget l μ n p : ℝ) else 0) * Real.log p +
          (padicValNat p (kzContent l μ n) : ℝ) * Real.log p ≤
        ((if p < 13 then 1 else 0) + (if 13 ≤ p ∧ 7 * p ≤ n then 1 else 0) +
          3 * ((Nat.log p (12 * n + 5) - 1 : ℕ) : ℝ) +
          kzRetainedInd l μ n p) * Real.log p := by
    intro p hp
    obtain ⟨hpr, hp5⟩ := hPmem p hp
    have := Fact.mk hpr
    have hlp := Real.log_natCast_nonneg p
    have hnn := kzRetainedInd_nonneg l μ n p
    have hK0 : (0 : ℝ) ≤ ((Nat.log p (12 * n + 5) - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have key : (padicValNat p (kzContent l μ n) : ℝ) +
        (if p ≤ n then (kzBudget l μ n p : ℝ) else 0) ≤
        (if p < 13 then 1 else 0) + (if 13 ≤ p ∧ 7 * p ≤ n then 1 else 0) +
          3 * ((Nat.log p (12 * n + 5) - 1 : ℕ) : ℝ) + kzRetainedInd l μ n p := by
      by_cases h13 : p < 13
      · simp only [h13, ↓reduceIte]
        have := kz_weight_le hl hμ hp5 n
        have h0 : ¬ (13 ≤ p ∧ 7 * p ≤ n) := fun h => by omega
        simp only [h0, ↓reduceIte]
        linarith
      · by_cases h7 : 7 * p ≤ n
        · have h0 : 13 ≤ p ∧ 7 * p ≤ n := ⟨by omega, h7⟩
          simp only [h13, h0, ↓reduceIte, and_self]
          have := kz_weight_le hl hμ hp5 n
          linarith
        · have h0 : ¬ (13 ≤ p ∧ 7 * p ≤ n) := fun h => h7 h.2
          simp only [h13, h0, ↓reduceIte, zero_add]
          have h7' : n < 7 * p := by omega
          have hp13 : 13 ≤ p := by omega
          have hsq : (n + 1) * (n + 1) ≤ (7 * p) * (7 * p) := Nat.mul_le_mul h7' h7'
          have hnn' : 250000 * n ≤ n * n := Nat.mul_le_mul_right n hn
          have hpM : 12 * n + 5 < p ^ 2 := by nlinarith
          have := kz_weight_le_retained hl hμ hpr hp13 h7' hpM
          linarith
    calc (if p ≤ n then (kzBudget l μ n p : ℝ) else 0) * Real.log p +
          (padicValNat p (kzContent l μ n) : ℝ) * Real.log p =
        ((padicValNat p (kzContent l μ n) : ℝ) +
          (if p ≤ n then (kzBudget l μ n p : ℝ) else 0)) * Real.log p := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right key hlp
  refine (sum_le_sum hterm).trans ?_
  have hsplit : ∑ p ∈ P,
      ((if p < 13 then 1 else 0) + (if 13 ≤ p ∧ 7 * p ≤ n then 1 else 0) +
          3 * ((Nat.log p (12 * n + 5) - 1 : ℕ) : ℝ) +
          kzRetainedInd l μ n p) * Real.log p =
      ∑ p ∈ P.filter (fun p => p < 13), Real.log p +
        ∑ p ∈ P.filter (fun p => 13 ≤ p ∧ 7 * p ≤ n), Real.log p +
        3 * ∑ p ∈ P, ((Nat.log p (12 * n + 5) - 1 : ℕ) : ℝ) * Real.log p +
        ∑ p ∈ P, kzRetainedInd l μ n p * Real.log p := by
    rw [sum_filter, sum_filter, mul_sum, ← sum_add_distrib, ← sum_add_distrib,
      ← sum_add_distrib]
    refine sum_congr rfl fun p _ => ?_
    split_ifs <;> ring
  rw [hsplit]
  have hA := sum_log_le_of_le hH (P.filter (fun p => 13 ≤ p ∧ 7 * p ≤ n))
      (fun p hp => (hPmem p (mem_filter.mp hp).1).1)
      (N := n / 7) ((Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega))
      (fun p hp => (Nat.le_div_iff_mul_le (by norm_num)).mpr (by
        have := (mem_filter.mp hp).2
        omega))
  have hB : ∑ p ∈ P.filter (fun p => p < 13), Real.log p ≤ Real.log 385 := by
    have hsub : P.filter (fun p => p < 13) ⊆ ({5, 7, 11} : Finset ℕ) := by
      intro p hp
      obtain ⟨hpP, hp13⟩ := mem_filter.mp hp
      obtain ⟨hpr, hp5⟩ := hPmem p hpP
      simp only [mem_insert, mem_singleton]
      interval_cases p <;> first | omega | (exfalso; revert hpr; decide)
    calc ∑ p ∈ P.filter (fun p => p < 13), Real.log p
        ≤ ∑ p ∈ ({5, 7, 11} : Finset ℕ), Real.log p :=
          sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => Real.log_natCast_nonneg p
      _ = Real.log 385 := by
          rw [sum_insert (by decide), sum_insert (by decide), sum_singleton,
            ← Real.log_mul (by norm_num) (by norm_num), ← Real.log_mul (by norm_num)
              (by norm_num)]
          norm_num
  linarith

/-- **The retained intervals**: if `F(A, B)` bounds `θ(B; 6, c) - θ(A; 6, c)` for both classes
and all `n/7 ≤ A ≤ B ≤ 2n + 1`, then the retained prime sum is at most the sum of `F` over the
twenty retained intervals. -/
theorem sum_kzRetainedInd_mul_log_le {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    {n : ℕ} (hn : 250000 ≤ n) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (F : ℝ → ℝ → ℝ)
    (hθ : ∀ (A B : ℝ) (c : ℤ), (c = 3 + 2 * l ∨ c = 3 - 2 * l) → (n : ℝ) / 7 ≤ A → A ≤ B →
      B ≤ 2 * n + 1 → chebyshevThetaAP B 6 c - chebyshevThetaAP A 6 c ≤ F A B) :
    ∑ p ∈ P, kzRetainedInd l μ n p * Real.log p ≤
      ∑ k ∈ range 6, (F (kzEndA l μ n (k + 1)) (n / (k + 1)) +
          F (n / (k + 1 + 1)) (kzEndC μ n (k + 1)) + F (n / (k + 1 + 1)) (kzEndD l n (k + 1))) +
        F n ((3 * n + l) / 2) + F ((6 * n + (2 * l + 3 * μ)) / 5) (2 * n + μ) := by
  have hN : (250000 : ℝ) ≤ n := by exact_mod_cast hn
  have hl' : -1 ≤ (l : ℝ) ∧ (l : ℝ) ≤ 1 := by rcases hl with rfl | rfl <;> norm_num
  have hμ' : -1 ≤ (μ : ℝ) ∧ (μ : ℝ) ≤ 1 := by rcases hμ with rfl | rfl <;> norm_num
  have hstep : ∀ (A B : ℝ) (c : ℤ), (c = 3 + 2 * l ∨ c = 3 - 2 * l) → (n : ℝ) / 7 ≤ A →
      A ≤ B → B ≤ 2 * n + 1 → ∑ p ∈ P, classInd A B c p * Real.log p ≤ F A B :=
    fun A B c hc h1 h2 h3 =>
      (sum_classInd_mul_log_le P hP (le_trans (by positivity) h1) h2 c).trans
        (hθ A B c hc h1 h2 h3)
  have e : ∀ p, kzRetainedInd l μ n p * Real.log p =
      ∑ k ∈ range 6, kzRetainedTerm l μ n p k * Real.log p +
        classInd n ((3 * n + l) / 2) (3 + 2 * l) p * Real.log p +
        classInd ((6 * n + (2 * l + 3 * μ)) / 5) (2 * n + μ) (3 - 2 * l) p * Real.log p := by
    intro p
    rw [kzRetainedInd_eq, add_mul, add_mul, sum_mul]
  have hdec : ∑ p ∈ P, kzRetainedInd l μ n p * Real.log p =
      ∑ k ∈ range 6, ∑ p ∈ P, kzRetainedTerm l μ n p k * Real.log p +
        ∑ p ∈ P, classInd n ((3 * n + l) / 2) (3 + 2 * l) p * Real.log p +
        ∑ p ∈ P, classInd ((6 * n + (2 * l + 3 * μ)) / 5) (2 * n + μ) (3 - 2 * l) p *
          Real.log p := by
    rw [sum_congr rfl fun p _ => e p, sum_add_distrib, sum_add_distrib, sum_comm]
  rw [hdec]
  refine add_le_add (add_le_add (sum_le_sum fun k hk => ?_) ?_) ?_
  · have hk6 : (k : ℝ) ≤ 5 := by
      have := mem_range.mp hk
      exact_mod_cast (show k ≤ 5 by omega)
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8⟩ :=
      kz_endpoints_valid hl hμ hn (t := (k : ℝ) + 1) (by linarith) (by linarith)
    simp only [kzRetainedTerm_eq, add_mul, sum_add_distrib]
    exact add_le_add (add_le_add (hstep _ _ _ (Or.inl rfl) v1 v2 v3)
      (hstep _ _ _ (Or.inl rfl) v4 v5 v6)) (hstep _ _ _ (Or.inr rfl) v4 v7 v8)
  · refine hstep _ _ _ (Or.inl rfl) (by linarith) ?_ ?_
    · rw [le_div_iff₀ (by norm_num)]; linarith
    · rw [div_le_iff₀ (by norm_num)]; linarith
  · refine hstep _ _ _ (Or.inr rfl) ?_ ?_ (by linarith)
    · rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; linarith
    · rw [div_le_iff₀ (by norm_num)]; linarith

end ArithmeticOfJacobiPolynomials
