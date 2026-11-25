/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.KanekoZagier.CarryLevels
public import ArithmeticOfJacobiPolynomials.KanekoZagier.PrimitiveIrreducibility
public import ArithmeticOfJacobiPolynomials.Jacobi.MomentFunctional

/-!
# Lemma 4.2: the carry budget at primes `p ≥ 5`

For `λ, μ ∈ {-1,1}`, `α = λ/3`, `β = μ/2`, a prime `p ≥ 5` and `q = p^h`, let
`a_q = kzResA λ q` and `b_q = kzResB μ q` be the least residues of `α` and `β` modulo `q`,
and put `M = 12 n + 5`, `E_p(n) = ∑_{1 ≤ h, p^h ≤ M} e_{p^h}` (`kzBudget`) and
`m_p = v_p(g_n)`.

Every relevant number is a quotient of products of progressions `d k + r` with `d ∈ {2,3,6}`
and of factorials (`kz_coeff_eq_prod`, `kz_wronskianConstant_eq`, `kz_jacobiMoment_eq`); all
factors are at most `M`. Counting multiples of `q` level by level gives the valuations as sums
of the level contributions of `CarryLevels`.

Main results:
* `kzLevelE_mem`: `e_q ∈ {0,1}` and `m_q + e_q ≤ 1`;
* `sum_kzLevelM_le_padicValNat_kzContent`: `∑_h m_{p^h} ≤ v_p(g_n)` (4.6);
* `kz_moment_content_budget`: (4.3), `v_p(C_n) - 2 m_p - v_p(μ_j) ≤ E_p(n) ≤ ⌊log_p M⌋` for every
  `j ≤ 2n - 1` (equivalently with `min_j v_p(μ_j)`);
* `padicValNat_kzContent_eq_kzLevelM`: if `p² > M` then `m_p` is the single-level indicator.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset

/-- `a_q`, the least residue of `λ/3` modulo `q`. -/
noncomputable def kzResA (l : ℤ) (q : ℕ) : ℕ := affineResidue l 3 q

theorem kzResA_eq (l : ℤ) (q : ℕ) : kzResA l q = affineResidue l 3 q := (rfl)

/-- `b_q`, the least residue of `μ/2` modulo `q`. -/
noncomputable def kzResB (μ : ℤ) (q : ℕ) : ℕ := affineResidue μ 2 q

theorem kzResB_eq (μ : ℤ) (q : ℕ) : kzResB μ q = affineResidue μ 2 q := (rfl)

/-- `e_q` for the Kaneko–Zagier parameters. -/
noncomputable def kzLevelE (l μ : ℤ) (n q : ℕ) : ℤ := levelE q (kzResA l q) (kzResB μ q) (n % q)

theorem kzLevelE_eq (l μ : ℤ) (n q : ℕ) :
    kzLevelE l μ n q = levelE q (kzResA l q) (kzResB μ q) (n % q) := (rfl)

/-- `m_q` for the Kaneko–Zagier parameters. -/
noncomputable def kzLevelM (l μ : ℤ) (n q : ℕ) : ℕ := levelM q (kzResA l q) (kzResB μ q) (n % q)

theorem kzLevelM_eq (l μ : ℤ) (n q : ℕ) :
    kzLevelM l μ n q = levelM q (kzResA l q) (kzResB μ q) (n % q) := (rfl)

/-- `E_p(n) = ∑_{h ≥ 1, p^h ≤ 12n+5} e_{p^h}`. -/
noncomputable def kzBudget (l μ : ℤ) (n p : ℕ) : ℤ :=
  ∑ h ∈ Icc 1 (Nat.log p (12 * n + 5)), kzLevelE l μ n (p ^ h)

theorem kzBudget_eq (l μ : ℤ) (n p : ℕ) :
    kzBudget l μ n p = ∑ h ∈ Icc 1 (Nat.log p (12 * n + 5)), kzLevelE l μ n (p ^ h) := (rfl)

/-- The level-`q` contribution to `v_p([t^j] y_n)`. -/
noncomputable def kzCoeffLevel (l μ : ℤ) (n j q : ℕ) : ℤ :=
  ((((n + kzResA l q) / q : ℕ) : ℤ) - ((j + kzResA l q) / q : ℕ)) +
    ((((j + (n + kzResA l q + kzResB μ q)) / q : ℕ) : ℤ) -
      ((0 + (n + kzResA l q + kzResB μ q)) / q : ℕ)) - ((n - j) / q : ℕ) - (j / q : ℕ)

theorem kzCoeffLevel_eq (l μ : ℤ) (n j q : ℕ) : kzCoeffLevel l μ n j q =
    ((((n + kzResA l q) / q : ℕ) : ℤ) - ((j + kzResA l q) / q : ℕ)) +
      ((((j + (n + kzResA l q + kzResB μ q)) / q : ℕ) : ℤ) -
        ((0 + (n + kzResA l q + kzResB μ q)) / q : ℕ)) - ((n - j) / q : ℕ) - (j / q : ℕ) :=
  (rfl)

/-- The level-`q` contribution to `v_p(C_n)`. -/
noncomputable def kzConstLevel (l μ : ℤ) (n q : ℕ) : ℤ :=
  (((n + kzResA l q) / q : ℕ) : ℤ) - ((0 + kzResA l q) / q : ℕ) + ((n + kzResB μ q) / q : ℕ) -
    ((0 + kzResB μ q) / q : ℕ) - (n / q : ℕ) -
    ((((n + (kzResA l q + kzResB μ q)) / q : ℕ) : ℤ) - ((1 + (kzResA l q + kzResB μ q)) / q : ℕ))

theorem kzConstLevel_eq (l μ : ℤ) (n q : ℕ) : kzConstLevel l μ n q =
    (((n + kzResA l q) / q : ℕ) : ℤ) - ((0 + kzResA l q) / q : ℕ) + ((n + kzResB μ q) / q : ℕ) -
      ((0 + kzResB μ q) / q : ℕ) - (n / q : ℕ) -
      ((((n + (kzResA l q + kzResB μ q)) / q : ℕ) : ℤ) -
        ((1 + (kzResA l q + kzResB μ q)) / q : ℕ)) := (rfl)

/-- The level-`q` contribution to `v_p(μ_j)`. -/
noncomputable def kzMomentLevel (l μ : ℤ) (j q : ℕ) : ℤ :=
  (((j + kzResA l q) / q : ℕ) : ℤ) - ((0 + kzResA l q) / q : ℕ) -
    ((((1 + j) + (kzResA l q + kzResB μ q)) / q : ℕ) - ((1 + (kzResA l q + kzResB μ q)) / q : ℕ))

theorem kzMomentLevel_eq (l μ : ℤ) (j q : ℕ) : kzMomentLevel l μ j q =
    (((j + kzResA l q) / q : ℕ) : ℤ) - ((0 + kzResA l q) / q : ℕ) -
      ((((1 + j) + (kzResA l q + kzResB μ q)) / q : ℕ) -
        ((1 + (kzResA l q + kzResB μ q)) / q : ℕ)) := (rfl)

/-- `B = ∏_{k ∈ (0,n]} (2k + μ)`, so that `(β+1)_n = B / 2^n`. -/
noncomputable def kzNumB (μ : ℤ) (n : ℕ) : ℚ := ∏ k ∈ Ioc 0 n, ((2 * (k : ℤ) + μ : ℤ) : ℚ)

theorem kzNumB_eq (μ : ℤ) (n : ℕ) : kzNumB μ n = ∏ k ∈ Ioc 0 n, ((2 * (k : ℤ) + μ : ℤ) : ℚ) :=
  (rfl)

/-- `D = ∏_{k ∈ (A,B]} (6k + 2λ + 3μ)`, so that `(c+2)_m = D / 6^m` for `(A, B) = (1, m+1)`. -/
noncomputable def kzNumD (l μ : ℤ) (A B : ℕ) : ℚ :=
  ∏ k ∈ Ioc A B, ((6 * (k : ℤ) + (2 * l + 3 * μ) : ℤ) : ℚ)

theorem kzNumD_eq (l μ : ℤ) (A B : ℕ) :
    kzNumD l μ A B = ∏ k ∈ Ioc A B, ((6 * (k : ℤ) + (2 * l + 3 * μ) : ℤ) : ℚ) := (rfl)

/-! ### Product formulas for `C_n` and `μ_j` -/

theorem prod_Ioc_ratCast_div {A B : ℕ} (d : ℕ) (hd : (d : ℚ) ≠ 0) (r : ℤ) (x : ℚ)
    (hx : x = (r : ℚ) / d) :
    ∏ k ∈ Ioc A B, (x + k) =
      (∏ k ∈ Ioc A B, (((d : ℤ) * (k : ℤ) + r : ℤ) : ℚ)) / (d : ℚ) ^ (B - A) := by
  rw [show (d : ℚ) ^ (B - A) = ∏ _k ∈ Ioc A B, (d : ℚ) by rw [prod_const, Nat.card_Ioc],
    ← prod_div_distrib]
  refine prod_congr rfl fun k _ => ?_
  rw [hx, div_add' _ _ _ hd]
  congr 1
  push_cast
  ring

theorem kz_jacobiMoment_eq (l μ : ℤ) (j : ℕ) :
    jacobiMoment ((l : ℚ) / 3) ((μ : ℚ) / 2) j =
      (kzNumA l j 0 / 3 ^ j) / (kzNumD l μ 1 (1 + j) / 6 ^ j) := by
  rw [jacobiMoment_eq]
  have e1 : (l : ℚ) / 3 + 1 = (l : ℚ) / 3 + ((0 : ℕ) : ℚ) + 1 := by push_cast; ring
  have e2 : (l : ℚ) / 3 + (μ : ℚ) / 2 + 2 = ((l : ℚ) / 3 + (μ : ℚ) / 2) + ((1 : ℕ) : ℚ) + 1 := by
    push_cast; ring
  rw [e1, e2, ascPochhammer_eval_eq_prod_Ioc, ascPochhammer_eval_eq_prod_Ioc, zero_add,
    prod_Ioc_ratCast_div 3 (by norm_num) l ((l : ℚ) / 3) (by norm_num),
    prod_Ioc_ratCast_div 6 (by norm_num) (2 * l + 3 * μ) ((l : ℚ) / 3 + (μ : ℚ) / 2)
      (by push_cast; ring), kzNumA_eq, kzNumD_eq]
  simp only [Nat.cast_ofNat, Nat.sub_zero, Nat.add_sub_cancel_left]

theorem kz_wronskianConstant_eq (l μ : ℤ) {n : ℕ} (hn : 1 ≤ n) :
    jacobiWronskianConstant ((l : ℚ) / 3) ((μ : ℚ) / 2) n =
      (kzNumA l n 0 / 3 ^ n) * (kzNumB μ n / 2 ^ n) /
        ((n.factorial : ℚ) * (kzNumD l μ 1 n / 6 ^ (n - 1))) := by
  rw [jacobiWronskianConstant_eq]
  have e1 : (l : ℚ) / 3 + 1 = (l : ℚ) / 3 + ((0 : ℕ) : ℚ) + 1 := by push_cast; ring
  have e3 : (μ : ℚ) / 2 + 1 = (μ : ℚ) / 2 + ((0 : ℕ) : ℚ) + 1 := by push_cast; ring
  have e2 : (l : ℚ) / 3 + (μ : ℚ) / 2 + 2 = ((l : ℚ) / 3 + (μ : ℚ) / 2) + ((1 : ℕ) : ℚ) + 1 := by
    push_cast; ring
  rw [e1, e3, e2, ascPochhammer_eval_eq_prod_Ioc, ascPochhammer_eval_eq_prod_Ioc,
    ascPochhammer_eval_eq_prod_Ioc, zero_add, Nat.add_sub_cancel' hn,
    prod_Ioc_ratCast_div 3 (by norm_num) l ((l : ℚ) / 3) (by norm_num),
    prod_Ioc_ratCast_div 2 (by norm_num) μ ((μ : ℚ) / 2) (by norm_num),
    prod_Ioc_ratCast_div 6 (by norm_num) (2 * l + 3 * μ) ((l : ℚ) / 3 + (μ : ℚ) / 2)
      (by push_cast; ring), kzNumA_eq, kzNumB_eq, kzNumD_eq]
  simp only [Nat.cast_ofNat, Nat.sub_zero]

theorem kzNumB_pos {μ : ℤ} (hμ : μ = 1 ∨ μ = -1) (n : ℕ) : 0 < kzNumB μ n := by
  rw [kzNumB_eq]
  exact prod_pos fun k hk => by
    have := (mem_Ioc.mp hk).1
    exact_mod_cast (show 0 < 2 * (k : ℤ) + μ by omega)

theorem kzNumD_pos {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) (A B : ℕ) :
    0 < kzNumD l μ A B := by
  rw [kzNumD_eq]
  exact prod_pos fun k hk => by
    have := (mem_Ioc.mp hk).1
    exact_mod_cast (show 0 < 6 * (k : ℤ) + (2 * l + 3 * μ) by omega)

/-! ### Residues -/

section Residues

variable {p : ℕ} [hp : Fact p.Prime]

theorem coprime_three_pow (hp5 : 5 ≤ p) (h : ℕ) : Nat.Coprime 3 (p ^ h) :=
  Nat.Coprime.pow_right h ((Nat.coprime_primes Nat.prime_three hp.out).mpr (by omega))

theorem coprime_two_pow (hp5 : 5 ≤ p) (h : ℕ) : Nat.Coprime 2 (p ^ h) :=
  Nat.Coprime.pow_right h ((Nat.coprime_primes Nat.prime_two hp.out).mpr (by omega))

omit hp in
theorem five_le_pow (hp5 : 5 ≤ p) {h : ℕ} (hh : 1 ≤ h) : 5 ≤ p ^ h :=
  le_trans hp5 (Nat.le_self_pow (by omega) p)

theorem kzResA_spec {l : ℤ} (hl : l = 1 ∨ l = -1) (hp5 : 5 ≤ p) {h : ℕ} (hh : 1 ≤ h) :
    1 ≤ kzResA l (p ^ h) ∧ kzResA l (p ^ h) < p ^ h := by
  have hq := five_le_pow hp5 hh
  rw [kzResA_eq]
  exact ⟨one_le_affineResidue hl (by omega) (coprime_three_pow hp5 h),
    affineResidue_lt l 3 (by omega)⟩

theorem kzResB_spec {μ : ℤ} (hμ : μ = 1 ∨ μ = -1) (hp5 : 5 ≤ p) {h : ℕ} (hh : 1 ≤ h) :
    1 ≤ kzResB μ (p ^ h) ∧ kzResB μ (p ^ h) < p ^ h := by
  have hq := five_le_pow hp5 hh
  rw [kzResB_eq]
  exact ⟨one_le_affineResidue hμ (by omega) (coprime_two_pow hp5 h),
    affineResidue_lt μ 2 (by omega)⟩

theorem kzResA_dvd (l : ℤ) (hp5 : 5 ≤ p) (h : ℕ) :
    ((p ^ h : ℕ) : ℤ) ∣ ((3 : ℕ) : ℤ) * (kzResA l (p ^ h) : ℤ) - l := by
  rw [kzResA_eq]
  exact dvd_mul_affineResidue_sub l (pow_pos hp.out.pos h) (coprime_three_pow hp5 h)

theorem kzResB_dvd (μ : ℤ) (hp5 : 5 ≤ p) (h : ℕ) :
    ((p ^ h : ℕ) : ℤ) ∣ ((2 : ℕ) : ℤ) * (kzResB μ (p ^ h) : ℤ) - μ := by
  rw [kzResB_eq]
  exact dvd_mul_affineResidue_sub μ (pow_pos hp.out.pos h) (coprime_two_pow hp5 h)

theorem kzRes_six_dvd (l μ : ℤ) (hp5 : 5 ≤ p) (h : ℕ) :
    ((p ^ h : ℕ) : ℤ) ∣ ((6 : ℕ) : ℤ) * ((kzResA l (p ^ h) + kzResB μ (p ^ h) : ℕ) : ℤ) -
      (2 * l + 3 * μ) := by
  have e : ((6 : ℕ) : ℤ) * ((kzResA l (p ^ h) + kzResB μ (p ^ h) : ℕ) : ℤ) - (2 * l + 3 * μ) =
      2 * (((3 : ℕ) : ℤ) * (kzResA l (p ^ h) : ℤ) - l) +
        3 * (((2 : ℕ) : ℤ) * (kzResB μ (p ^ h) : ℤ) - μ) := by push_cast; ring
  rw [e]
  exact dvd_add (dvd_mul_of_dvd_right (kzResA_dvd l hp5 h) 2)
    (dvd_mul_of_dvd_right (kzResB_dvd μ hp5 h) 3)

theorem kzRes_six_dvd_shift (l μ : ℤ) (hp5 : 5 ≤ p) (h n : ℕ) :
    ((p ^ h : ℕ) : ℤ) ∣ ((6 : ℕ) : ℤ) * ((n + kzResA l (p ^ h) + kzResB μ (p ^ h) : ℕ) : ℤ) -
      (6 * n + (2 * l + 3 * μ)) := by
  have e : ((6 : ℕ) : ℤ) * ((n + kzResA l (p ^ h) + kzResB μ (p ^ h) : ℕ) : ℤ) -
      (6 * n + (2 * l + 3 * μ)) =
      2 * (((3 : ℕ) : ℤ) * (kzResA l (p ^ h) : ℤ) - l) +
        3 * (((2 : ℕ) : ℤ) * (kzResB μ (p ^ h) : ℤ) - μ) := by push_cast; ring
  rw [e]
  exact dvd_add (dvd_mul_of_dvd_right (kzResA_dvd l hp5 h) 2)
    (dvd_mul_of_dvd_right (kzResB_dvd μ hp5 h) 3)

theorem not_dvd_three (hp5 : 5 ≤ p) : ¬ p ∣ 3 := fun h =>
  absurd ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp h) (by omega)

theorem not_dvd_two (hp5 : 5 ≤ p) : ¬ p ∣ 2 := fun h =>
  absurd ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h) (by omega)

theorem not_dvd_six (hp5 : 5 ≤ p) : ¬ p ∣ 6 := by
  intro h
  rw [show (6 : ℕ) = 2 * 3 by norm_num] at h
  rcases (Nat.Prime.dvd_mul hp.out).mp h with h | h
  · exact not_dvd_two hp5 h
  · exact not_dvd_three hp5 h

end Residues

/-! ### Valuations by levels -/

section Valuations

variable {p : ℕ} [hp : Fact p.Prime]

/-- Level counting for a progression with a prescribed residue at each level. -/
theorem padicValRat_prod_affine_eq_sum_of_dvd {d : ℕ} (hd : ¬ p ∣ d) (r : ℤ) (t : ℕ → ℕ)
    (ht : ∀ h, ((p ^ h : ℕ) : ℤ) ∣ (d : ℤ) * (t h : ℤ) - r) {A B : ℕ} (hAB : A ≤ B)
    (hpos : ∀ k ∈ Ioc A B, 0 < (d : ℤ) * (k : ℤ) + r) {H : ℕ}
    (hlt : ∀ k ∈ Ioc A B, (d : ℤ) * (k : ℤ) + r < (p : ℤ) ^ (H + 1)) :
    padicValRat p (∏ k ∈ Ioc A B, (((d : ℤ) * (k : ℤ) + r : ℤ) : ℚ)) =
      ∑ h ∈ Icc 1 H, ((((B + t h) / p ^ h : ℕ) : ℤ) - (((A + t h) / p ^ h : ℕ) : ℤ)) := by
  rw [padicValRat_prod_eq_sum_card (Ioc A B) (fun k : ℕ => (d : ℤ) * (k : ℤ) + r) hpos hlt]
  refine sum_congr rfl fun h _ => ?_
  have hcop : Nat.Coprime (p ^ h) d :=
    Nat.Coprime.pow_left h ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hd)
  have key := card_Ioc_filter_dvd_affine (q := p ^ h) hcop (ht h) hAB
  rw [← Nat.cast_pow, key, Nat.cast_sub (Nat.div_le_div_right (by omega : A + t h ≤ B + t h))]

theorem padicValRat_prodA_eq_sum {l : ℤ} (hl : l = 1 ∨ l = -1) (hp5 : 5 ≤ p) {A B : ℕ}
    (hAB : A ≤ B) {H : ℕ} (hBH : 3 * B + 1 < p ^ (H + 1)) :
    padicValRat p (∏ k ∈ Ioc A B, ((3 * (k : ℤ) + l : ℤ) : ℚ)) =
      ∑ h ∈ Icc 1 H, ((((B + kzResA l (p ^ h)) / p ^ h : ℕ) : ℤ) -
        (((A + kzResA l (p ^ h)) / p ^ h : ℕ) : ℤ)) := by
  have hz : (3 * (B : ℤ) + 1) < (p : ℤ) ^ (H + 1) := by exact_mod_cast hBH
  have h := padicValRat_prod_affine_eq_sum_of_dvd (p := p) (H := H)
    (d := 3) (not_dvd_three hp5) l
    (fun h => kzResA l (p ^ h)) (fun h => kzResA_dvd l hp5 h) hAB
    (fun k hk => by have := (mem_Ioc.mp hk).1; push_cast; omega)
    (fun k hk => by have := (mem_Ioc.mp hk).2; push_cast; omega)
  simp only [Nat.cast_ofNat] at h
  exact h

theorem padicValRat_kzNumB_eq_sum {μ : ℤ} (hμ : μ = 1 ∨ μ = -1) (hp5 : 5 ≤ p) {B : ℕ} {H : ℕ}
    (hBH : 2 * B + 1 < p ^ (H + 1)) :
    padicValRat p (kzNumB μ B) =
      ∑ h ∈ Icc 1 H, ((((B + kzResB μ (p ^ h)) / p ^ h : ℕ) : ℤ) -
        (((0 + kzResB μ (p ^ h)) / p ^ h : ℕ) : ℤ)) := by
  have hz : (2 * (B : ℤ) + 1) < (p : ℤ) ^ (H + 1) := by exact_mod_cast hBH
  have h := padicValRat_prod_affine_eq_sum_of_dvd (p := p) (H := H)
    (d := 2) (not_dvd_two hp5) μ
    (fun h => kzResB μ (p ^ h)) (fun h => kzResB_dvd μ hp5 h) (Nat.zero_le B)
    (fun k hk => by have := (mem_Ioc.mp hk).1; push_cast; omega)
    (fun k hk => by have := (mem_Ioc.mp hk).2; push_cast; omega)
  simp only [Nat.cast_ofNat] at h
  rw [kzNumB_eq]
  exact h

theorem padicValRat_kzNumD_eq_sum {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    (hp5 : 5 ≤ p) {A B : ℕ} (hAB : A ≤ B) {H : ℕ} (hBH : 6 * B + 5 < p ^ (H + 1)) :
    padicValRat p (kzNumD l μ A B) =
      ∑ h ∈ Icc 1 H, ((((B + (kzResA l (p ^ h) + kzResB μ (p ^ h))) / p ^ h : ℕ) : ℤ) -
        (((A + (kzResA l (p ^ h) + kzResB μ (p ^ h))) / p ^ h : ℕ) : ℤ)) := by
  have hz : (6 * (B : ℤ) + 5) < (p : ℤ) ^ (H + 1) := by exact_mod_cast hBH
  have h := padicValRat_prod_affine_eq_sum_of_dvd (p := p) (H := H)
    (d := 6) (not_dvd_six hp5)
    (2 * l + 3 * μ) (fun h => kzResA l (p ^ h) + kzResB μ (p ^ h))
    (fun h => kzRes_six_dvd l μ hp5 h) hAB
    (fun k hk => by have := (mem_Ioc.mp hk).1; push_cast; omega)
    (fun k hk => by have := (mem_Ioc.mp hk).2; push_cast; omega)
  simp only [Nat.cast_ofNat] at h
  rw [kzNumD_eq]
  exact h

theorem padicValRat_kzNumC_eq_sum {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    (hp5 : 5 ≤ p) {n j : ℕ} (hj : j ≤ n) {H : ℕ} (hH : 12 * n + 5 < p ^ (H + 1)) :
    padicValRat p (kzNumC l μ n j) =
      ∑ h ∈ Icc 1 H, ((((j + (n + kzResA l (p ^ h) + kzResB μ (p ^ h))) / p ^ h : ℕ) : ℤ) -
        (((0 + (n + kzResA l (p ^ h) + kzResB μ (p ^ h))) / p ^ h : ℕ) : ℤ)) := by
  have hz : (12 * (n : ℤ) + 5) < (p : ℤ) ^ (H + 1) := by exact_mod_cast hH
  have hjz : (j : ℤ) ≤ n := by exact_mod_cast hj
  have h := padicValRat_prod_affine_eq_sum_of_dvd (p := p) (H := H)
    (d := 6) (not_dvd_six hp5)
    (6 * n + (2 * l + 3 * μ)) (fun h => n + kzResA l (p ^ h) + kzResB μ (p ^ h))
    (fun h => kzRes_six_dvd_shift l μ hp5 h n) (Nat.zero_le j)
    (fun k hk => by have := (mem_Ioc.mp hk).1; push_cast; omega)
    (fun k hk => by have := (mem_Ioc.mp hk).2; push_cast; omega)
  simp only [Nat.cast_ofNat] at h
  rw [kzNumC_eq]
  exact h

/-- **Coefficients by levels**: for `p ≥ 5`, `j ≤ n` and `12n + 5 < p^{H+1}`,
`v_p(κ_n [t^j] y_n) = ∑_{h=1}^{H} (level-p^h contribution)`. -/
theorem padicValRat_kzKappa_mul_coeff_eq_sum {l μ : ℤ} (hl : l = 1 ∨ l = -1)
    (hμ : μ = 1 ∨ μ = -1) (hp5 : 5 ≤ p) {n j : ℕ} (hj : j ≤ n) {H : ℕ}
    (hH : 12 * n + 5 < p ^ (H + 1)) :
    padicValRat p ((kzKappa n : ℚ) * (jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n).coeff j) =
      ∑ h ∈ Icc 1 H, kzCoeffLevel l μ n j (p ^ h) := by
  obtain ⟨hc0, hc⟩ := padicValRat_kz_coeff hl hμ hj p
  have hk0 : (kzKappa n : ℚ) ≠ 0 := by exact_mod_cast (kzKappa_pos n).ne'
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  rw [padicValRat.mul hk0 hc0, hc, padicValRat_kzKappa, padicValRat_six_eq, padicValRat_two_eq,
    padicValRat_three_eq]
  simp only [hp2, hp3, ↓reduceIte]
  rw [kzNumA_eq, padicValRat_prodA_eq_sum hl hp5 hj (H := H) (by omega),
    padicValRat_kzNumC_eq_sum hl hμ hp5 hj hH,
    padicValRat_factorial_eq_sum (p := p) (m := n - j) (H := H) (by omega),
    padicValRat_factorial_eq_sum (p := p) (m := j) (H := H) (by omega)]
  simp only [kzCoeffLevel_eq, sum_add_distrib, sum_sub_distrib]
  ring

/-- **The constant by levels**: `v_p(C_n) = ∑_{h=1}^{H} (η + E_a + E_b - E_c)`-contributions. -/
theorem padicValRat_kz_constant_eq_sum {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    (hp5 : 5 ≤ p) {n : ℕ} (hn : 1 ≤ n) {H : ℕ} (hH : 12 * n + 5 < p ^ (H + 1)) :
    padicValRat p (jacobiWronskianConstant ((l : ℚ) / 3) ((μ : ℚ) / 2) n) =
      ∑ h ∈ Icc 1 H, kzConstLevel l μ n (p ^ h) := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hA := (kzNumA_pos hl n 0).ne'
  have hB := (kzNumB_pos hμ n).ne'
  have hD := (kzNumD_pos hl hμ 1 n).ne'
  have h3 : ((3 : ℚ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2 : ((2 : ℚ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h6 : ((6 : ℚ) ^ (n - 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hf : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [kz_wronskianConstant_eq l μ hn,
    padicValRat.div (mul_ne_zero (div_ne_zero hA h3) (div_ne_zero hB h2))
      (mul_ne_zero hf (div_ne_zero hD h6)),
    padicValRat.mul (div_ne_zero hA h3) (div_ne_zero hB h2),
    padicValRat.mul hf (div_ne_zero hD h6), padicValRat.div hA h3, padicValRat.div hB h2,
    padicValRat.div hD h6, padicValRat.pow, padicValRat.pow, padicValRat.pow, padicValRat_six_eq,
    padicValRat_two_eq, padicValRat_three_eq]
  simp only [hp2, hp3, ↓reduceIte]
  rw [kzNumA_eq, padicValRat_prodA_eq_sum hl hp5 (Nat.zero_le n) (H := H) (by omega),
    padicValRat_kzNumB_eq_sum hμ hp5 (B := n) (H := H) (by omega),
    padicValRat_kzNumD_eq_sum hl hμ hp5 hn (H := H) (by omega),
    padicValRat_factorial_eq_sum (p := p) (m := n) (H := H) (by omega)]
  simp only [kzConstLevel_eq, sum_add_distrib, sum_sub_distrib]
  ring

/-- **Moments by levels**: `v_p(μ_j) = ∑_{h=1}^{H}` (level contributions), `j < 2n`. -/
theorem padicValRat_kz_moment_eq_sum {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    (hp5 : 5 ≤ p) {n j : ℕ} (hj : j < 2 * n) {H : ℕ} (hH : 12 * n + 5 < p ^ (H + 1)) :
    padicValRat p (jacobiMoment ((l : ℚ) / 3) ((μ : ℚ) / 2) j) =
      ∑ h ∈ Icc 1 H, kzMomentLevel l μ j (p ^ h) := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hA := (kzNumA_pos hl j 0).ne'
  have hD := (kzNumD_pos hl hμ 1 (1 + j)).ne'
  have h3 : ((3 : ℚ) ^ j) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h6 : ((6 : ℚ) ^ j) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [kz_jacobiMoment_eq l μ j, padicValRat.div (div_ne_zero hA h3) (div_ne_zero hD h6),
    padicValRat.div hA h3, padicValRat.div hD h6, padicValRat.pow, padicValRat.pow,
    padicValRat_six_eq, padicValRat_two_eq, padicValRat_three_eq]
  simp only [hp2, hp3, ↓reduceIte]
  rw [kzNumA_eq, padicValRat_prodA_eq_sum hl hp5 (Nat.zero_le j) (H := H) (by omega),
    padicValRat_kzNumD_eq_sum hl hμ hp5 (by omega : 1 ≤ 1 + j) (H := H) (by omega)]
  simp only [kzMomentLevel_eq, sum_sub_distrib]
  ring

end Valuations

/-! ### Lemma 4.2 -/

section Budget

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Lemma 4.2, first part**: for `q = p^h`, `p ≥ 5`, `h ≥ 1`: `e_q ∈ {0,1}` and
`m_q + e_q ≤ 1`. -/
theorem kzLevelE_mem {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) (hp5 : 5 ≤ p)
    {h : ℕ} (hh : 1 ≤ h) (n : ℕ) :
    (kzLevelE l μ n (p ^ h) = 0 ∨ kzLevelE l μ n (p ^ h) = 1) ∧
      (kzLevelM l μ n (p ^ h) : ℤ) + kzLevelE l μ n (p ^ h) ≤ 1 := by
  obtain ⟨ha1, haq⟩ := kzResA_spec hl hp5 hh
  obtain ⟨hb1, hbq⟩ := kzResB_spec hμ hp5 hh
  rw [kzLevelE_eq, kzLevelM_eq]
  exact levelE_mem ha1 haq hb1 hbq

/-- The coefficient level contributions are at least `m_q`. -/
theorem kzLevelM_le_kzCoeffLevel {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    (hp5 : 5 ≤ p) {h : ℕ} (hh : 1 ≤ h) {n j : ℕ} (hj : j ≤ n) :
    (kzLevelM l μ n (p ^ h) : ℤ) ≤ kzCoeffLevel l μ n j (p ^ h) := by
  obtain ⟨-, haq⟩ := kzResA_spec hl hp5 hh
  obtain ⟨-, hbq⟩ := kzResB_spec hμ hp5 hh
  rw [kzLevelM_eq, kzCoeffLevel_eq]
  exact level_coeff_ge (by omega) haq hbq hj

/-- `(p : ℤ)^S` divides every coefficient of `κ_n y_n` once all valuations are `≥ S`. -/
theorem pow_dvd_kzContent {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) (n S : ℕ)
    (hS : ∀ j ≤ n, (S : ℤ) ≤
      padicValRat p ((kzKappa n : ℚ) * (jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n).coeff j)) :
    S ≤ padicValNat p (kzContent l μ n) := by
  have hdvd : ((p : ℤ) ^ S) ∣ (kzScaled l μ n).content := by
    rw [dvd_content_iff_C_dvd, C_dvd_iff_dvd_coeff]
    intro j
    by_cases hj : j ≤ n
    · have h := hS j hj
      rw [← coeff_kzScaled hl hμ, padicValRat.of_int] at h
      exact (padicValInt_dvd_iff S _).mpr (Or.inr (by exact_mod_cast h))
    · rw [coeff_eq_zero_of_natDegree_lt (p := kzScaled l μ n)
        (by rw [natDegree_kzScaled hl hμ]; omega)]
      exact dvd_zero _
  rw [← kzContent_intCast, (Nat.cast_pow p S).symm,
    Int.natCast_dvd_natCast] at hdvd
  exact (padicValNat_dvd_iff_le (kzContent_pos hl hμ n).ne').mp hdvd

/-- **(4.6)**: `∑_{h=1}^{H} m_{p^h} ≤ v_p(g_n)` whenever `12n + 5 < p^{H+1}`. -/
theorem sum_kzLevelM_le_padicValNat_kzContent {l μ : ℤ} (hl : l = 1 ∨ l = -1)
    (hμ : μ = 1 ∨ μ = -1) (hp5 : 5 ≤ p) (n : ℕ) {H : ℕ} (hH : 12 * n + 5 < p ^ (H + 1)) :
    ∑ h ∈ Icc 1 H, kzLevelM l μ n (p ^ h) ≤ padicValNat p (kzContent l μ n) := by
  refine pow_dvd_kzContent hl hμ n _ fun j hj => ?_
  rw [padicValRat_kzKappa_mul_coeff_eq_sum hl hμ hp5 hj hH]
  push_cast
  exact sum_le_sum fun h hh =>
    kzLevelM_le_kzCoeffLevel hl hμ hp5 (mem_Icc.mp hh).1 hj

/-- **Lemma 4.2, (4.3)**: for `p ≥ 5`, `n ≥ 1` and every `j ≤ 2n - 1`,
`v_p(C_n) - 2 v_p(g_n) - v_p(μ_j) ≤ E_p(n) ≤ ⌊log_p (12n+5)⌋`. -/
theorem kz_moment_content_budget {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    (hp5 : 5 ≤ p) {n : ℕ} (hn : 1 ≤ n) :
    (∀ j < 2 * n, padicValRat p (jacobiWronskianConstant ((l : ℚ) / 3) ((μ : ℚ) / 2) n) -
        2 * (padicValNat p (kzContent l μ n) : ℤ) -
        padicValRat p (jacobiMoment ((l : ℚ) / 3) ((μ : ℚ) / 2) j) ≤ kzBudget l μ n p) ∧
      kzBudget l μ n p ≤ Nat.log p (12 * n + 5) := by
  set H := Nat.log p (12 * n + 5) with hHdef
  have hH : 12 * n + 5 < p ^ (H + 1) := Nat.lt_pow_succ_log_self hp.out.one_lt _
  refine ⟨fun j hj => ?_, ?_⟩
  · have h1 := padicValRat_kz_constant_eq_sum hl hμ hp5 hn hH
    have h2 := padicValRat_kz_moment_eq_sum hl hμ hp5 hj hH
    have h3 := sum_kzLevelM_le_padicValNat_kzContent hl hμ hp5 n hH
    have h3' : (∑ h ∈ Icc 1 H, (kzLevelM l μ n (p ^ h) : ℤ)) ≤
        (padicValNat p (kzContent l μ n) : ℤ) := by exact_mod_cast h3
    have h4 : ∑ h ∈ Icc 1 H, (kzConstLevel l μ n (p ^ h) - 2 * (kzLevelM l μ n (p ^ h) : ℤ) -
        kzMomentLevel l μ j (p ^ h)) ≤ ∑ h ∈ Icc 1 H, kzLevelE l μ n (p ^ h) := by
      refine sum_le_sum fun h hh => ?_
      have hh1 := (mem_Icc.mp hh).1
      obtain ⟨-, haq⟩ := kzResA_spec hl hp5 hh1
      obtain ⟨-, hbq⟩ := kzResB_spec hμ hp5 hh1
      have hq : 0 < p ^ h := pow_pos hp.out.pos h
      have hc := level_constant_eq hq haq hbq n
      have hm := level_moment_ge hq haq hbq j
      rw [kzConstLevel_eq, kzMomentLevel_eq, kzLevelM_eq, kzLevelE_eq, levelE_eq]
      linarith
    have h5 : ∑ h ∈ Icc 1 H, (kzConstLevel l μ n (p ^ h) - 2 * (kzLevelM l μ n (p ^ h) : ℤ) -
        kzMomentLevel l μ j (p ^ h)) = ∑ h ∈ Icc 1 H, kzConstLevel l μ n (p ^ h) -
          2 * ∑ h ∈ Icc 1 H, (kzLevelM l μ n (p ^ h) : ℤ) -
          ∑ h ∈ Icc 1 H, kzMomentLevel l μ j (p ^ h) := by
      rw [sum_sub_distrib, sum_sub_distrib, mul_sum]
    rw [h1, h2, kzBudget_eq, ← hHdef]
    linarith
  · rw [kzBudget_eq, ← hHdef]
    calc ∑ h ∈ Icc 1 H, kzLevelE l μ n (p ^ h) ≤ ∑ _h ∈ Icc 1 H, (1 : ℤ) :=
          sum_le_sum fun h hh => by
            rcases (kzLevelE_mem hl hμ hp5 (mem_Icc.mp hh).1 n).1 with h0 | h1 <;> omega
      _ = H := by simp

/-- **Lemma 4.2, last part**: if `p > √(12n+5)`, then `v_p(g_n) = m_p`, the indicator at the
single level `q = p`. -/
theorem padicValNat_kzContent_eq_kzLevelM {l μ : ℤ} (hl : l = 1 ∨ l = -1)
    (hμ : μ = 1 ∨ μ = -1) (hp5 : 5 ≤ p) (n : ℕ) (hpM : 12 * n + 5 < p ^ 2) :
    padicValNat p (kzContent l μ n) = kzLevelM l μ n p := by
  have hH : 12 * n + 5 < p ^ (1 + 1) := hpM
  apply le_antisymm
  · obtain ⟨-, haq⟩ := kzResA_spec hl hp5 (h := 1) le_rfl
    obtain ⟨ha1, -⟩ := kzResA_spec hl hp5 (h := 1) le_rfl
    obtain ⟨-, hbq⟩ := kzResB_spec hμ hp5 (h := 1) le_rfl
    rw [pow_one] at haq ha1 hbq
    obtain ⟨j, hj, hjle⟩ := level_coeff_attained (q := p) (n := n) hp.out.pos ha1 haq hbq
    have hval := padicValRat_kzKappa_mul_coeff_eq_sum hl hμ hp5 hj hH
    rw [Finset.Icc_self, sum_singleton, pow_one, kzCoeffLevel_eq] at hval
    rw [kzLevelM_eq]
    -- `g_n` divides the `j`-th coefficient
    have hne := (padicValRat_kzKappa_mul_coeff hl hμ hj p).1
    rw [← coeff_kzScaled hl hμ] at hne hval
    have hK0 : (kzScaled l μ n).coeff j ≠ 0 := fun h0 => hne (by rw [h0, Int.cast_zero])
    have hdvd : ((p : ℤ) ^ padicValNat p (kzContent l μ n)) ∣ (kzScaled l μ n).coeff j := by
      refine dvd_trans ?_ (content_dvd_coeff j)
      rw [← kzContent_intCast, ← Nat.cast_pow, Int.natCast_dvd_natCast]
      exact pow_padicValNat_dvd
    have h1 := ((padicValInt_dvd_iff _ _).mp hdvd).resolve_left hK0
    rw [padicValRat.of_int] at hval
    have h2 : ((padicValNat p (kzContent l μ n) : ℕ) : ℤ) ≤
        (padicValInt p ((kzScaled l μ n).coeff j) : ℤ) := by
      exact_mod_cast h1
    have h3 : (padicValNat p (kzContent l μ n) : ℤ) ≤
        levelM p (kzResA l p) (kzResB μ p) (n % p) := by
      linarith
    exact_mod_cast h3
  · have h := sum_kzLevelM_le_padicValNat_kzContent hl hμ hp5 n (H := 1) hH
    rwa [Finset.Icc_self, sum_singleton, pow_one] at h

end Budget

end ArithmeticOfJacobiPolynomials
