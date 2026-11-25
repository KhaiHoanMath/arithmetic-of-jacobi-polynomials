/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.CentralValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Eventual validity of the criterion (3.5) for fixed unequal parameters

Proof of the irreducibility assertion of Theorem 1.3, first paragraph: for fixed
integers `a > b ≥ 0` and `δ ∈ {0,1}`, and any constant `c > 0`, the right side of (3.5),
`(M + √S) log 3 + 3 log T + log |A_δ(m)| + log(8 (m+1) S B D_δ(m) / (c √m))`, is
`m log 3 + O(√m)`, while the left side is `n log 2 = (2m+δ) log 2`; the margin
`log 2 - (1/2) log 3 > 0` gives (3.5) for all large `m`. Moreover `A_δ(m) ≠ 0` for all large `m`.

All error terms are bounded by `K √(m+1) + K'` through `log x ≤ 2 √x` and the bound
`|p(m)| ≤ (∑ |p_i|) (m+1)^{deg p}` for integer polynomials.

Main results:
* `ArithmeticOfJacobiPolynomials.exists_forall_asymmetric_criterion`;
* `ArithmeticOfJacobiPolynomials.exists_forall_centralA_ne_zero`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset Real

/-- `|p(m)| ≤ (∑_i |p_i|) (m+1)^{deg p}` for an integer polynomial `p` and `m ∈ ℕ`. -/
theorem abs_eval_natCast_le (p : ℤ[X]) (m : ℕ) :
    |((p.eval (m : ℤ) : ℤ) : ℝ)| ≤
      (∑ i ∈ range (p.natDegree + 1), |((p.coeff i : ℤ) : ℝ)|) * ((m : ℝ) + 1) ^ p.natDegree := by
  rw [eval_eq_sum_range, Int.cast_sum, sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
  rw [Int.cast_mul, Int.cast_pow, abs_mul, abs_pow, Int.cast_natCast,
    abs_of_nonneg (show (0 : ℝ) ≤ (m : ℝ) from Nat.cast_nonneg m)]
  have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.mp (mem_range.mp hi)
  have : (m : ℝ) ^ i ≤ ((m : ℝ) + 1) ^ p.natDegree :=
    (pow_le_pow_left₀ (Nat.cast_nonneg m) (by linarith) i).trans
      (pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]) hi')
  exact mul_le_mul_of_nonneg_left this (abs_nonneg _)

/-- `log x ≤ 2 √x` for `x ≥ 0`. -/
theorem log_le_two_mul_sqrt {x : ℝ} (hx : 0 ≤ x) : log x ≤ 2 * √x := by
  rcases hx.eq_or_lt with h | h
  · rw [← h]; simp
  · have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr h)
    rw [Real.log_sqrt hx] at h1
    linarith

/-- If `|x| ≤ K (m+1)^d` with `K ≥ 1`, then `log |x| ≤ log K + 2 d √(m+1)`. -/
theorem log_abs_le_of_le {x K : ℝ} {d m : ℕ} (hK : 1 ≤ K) (hx : |x| ≤ K * ((m : ℝ) + 1) ^ d) :
    log |x| ≤ log K + 2 * d * √((m : ℝ) + 1) := by
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hlogm := log_le_two_mul_sqrt hm.le
  have hK0 : 0 ≤ log K := Real.log_nonneg hK
  have hlm : 0 ≤ log ((m : ℝ) + 1) :=
    Real.log_nonneg (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  rcases (abs_nonneg x).eq_or_lt with h | h
  · rw [← h, Real.log_zero]; positivity
  · calc log |x| ≤ log (K * ((m : ℝ) + 1) ^ d) := Real.log_le_log h hx
      _ = log K + d * log ((m : ℝ) + 1) := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
      _ ≤ log K + 2 * d * √((m : ℝ) + 1) := by nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]

/-- A positive margin eventually beats `K √(m+1) + K'`. -/
theorem exists_forall_mul_gt_sqrt {ε K K' : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → K * √((m : ℝ) + 1) + K' < m * ε := by
  set X : ℝ := (|K| + |K'| + ε + 1) / ε with hX
  obtain ⟨N, hN⟩ := exists_nat_ge (X ^ 2)
  refine ⟨N, fun m hm => ?_⟩
  set x := √((m : ℝ) + 1) with hx
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hx1 : 1 ≤ x := by rw [hx, Real.one_le_sqrt]; linarith
  have hxsq : x ^ 2 = (m : ℝ) + 1 := Real.sq_sqrt (by linarith)
  have hX0 : 0 < X := by rw [hX]; positivity
  have hXx : X ≤ x := by
    have hNm : (N : ℝ) ≤ m := by exact_mod_cast hm
    have h1 : X ^ 2 ≤ x ^ 2 := by rw [hxsq]; linarith
    nlinarith [h1, hX0, hx1]
  have hεX : ε * X = |K| + |K'| + ε + 1 := by rw [hX]; field_simp
  have h1 : (|K| + |K'| + ε + 1) * x ≤ ε * x ^ 2 := by
    rw [← hεX, sq, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hXx (by linarith)) hε.le
  have hK : K * x ≤ |K| * x := mul_le_mul_of_nonneg_right (le_abs_self K) (by linarith)
  have hK' : K' ≤ |K'| * x := by nlinarith [le_abs_self K', abs_nonneg K']
  rw [hxsq] at h1
  linarith [mul_le_mul_of_nonneg_left hx1 hε.le]

/-- An integer polynomial satisfies `|p(m)| ≤ K (m+1)^{deg p}` for some `K ≥ 1`. -/
theorem exists_abs_eval_natCast_le (p : ℤ[X]) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ m : ℕ, |((p.eval (m : ℤ) : ℤ) : ℝ)| ≤ K * ((m : ℝ) + 1) ^ p.natDegree := by
  refine ⟨(∑ i ∈ range (p.natDegree + 1), |((p.coeff i : ℤ) : ℝ)|) + 1, ?_, fun m => ?_⟩
  · have := Finset.sum_nonneg (s := range (p.natDegree + 1))
      (f := fun i => |((p.coeff i : ℤ) : ℝ)|) (fun i _ => abs_nonneg _)
    linarith
  · refine (abs_eval_natCast_le p m).trans (mul_le_mul_of_nonneg_right (by linarith) ?_)
    positivity

/-- `A_δ(m) ≠ 0` for all large `m`. -/
theorem exists_forall_centralA_ne_zero (a b δ : ℕ) (hab : b < a) (hδ : δ ≤ 1) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → (centralA a b δ).eval (m : ℤ) ≠ 0 := by
  have hA0 : centralA a b δ ≠ 0 := fun h => by
    have := centralA_eval_zero_pos a b δ hab hδ
    rw [h, eval_zero] at this
    exact lt_irrefl _ this
  obtain ⟨N, hN⟩ := (((centralA a b δ).roots.toFinset.image Int.toNat).bddAbove)
  refine ⟨N + 1, fun m hm h0 => ?_⟩
  have hmem : (m : ℤ) ∈ (centralA a b δ).roots.toFinset :=
    Multiset.mem_toFinset.mpr ((mem_roots hA0).mpr h0)
  have := hN (Finset.mem_coe.mpr (Finset.mem_image_of_mem Int.toNat hmem))
  simp only [Int.toNat_natCast] at this
  omega

/-- **The criterion (3.5) holds for all large `m`** (proof of Theorem 1.3, irreducibility). For
fixed `a > b ≥ 0`, `δ ∈ {0,1}` and `c > 0`, with `s = a+b`, `n = 2m+δ`, `M = m+s+2`,
`S = 2n+s+1`, `T = ∏_{j=1}^{s}(n+j)`, `B = binom(n+a,a)` and `γ = c √m / D_δ(m)`:
for all large `m`,
`(M + √S) log 3 + 3 log T + log |A_δ(m)| + log(8 (m+1) S B / γ) < n log 2`. -/
theorem exists_forall_asymmetric_criterion (a b δ : ℕ) (hδ : δ ≤ 1) {c : ℝ} (hc : 0 < c) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      (((m + (a + b) + 2 : ℕ) : ℝ) + √((2 * (2 * m + δ) + (a + b) + 1 : ℕ) : ℝ)) * log 3 +
        3 * log ((∏ j ∈ Icc 1 (a + b), (2 * m + δ + j) : ℕ) : ℝ) +
        log |(((centralA a b δ).eval (m : ℤ) : ℤ) : ℝ)| +
        log (8 * ((m : ℝ) + 1) * ((2 * (2 * m + δ) + (a + b) + 1 : ℕ) : ℝ) *
          ((2 * m + δ + a).choose a : ℝ) /
            (c * √(m : ℝ) / (((centralD a b δ).eval (m : ℤ) : ℤ) : ℝ))) <
      ((2 * m + δ : ℕ) : ℝ) * log 2 := by
  obtain ⟨KA, hKA1, hAb⟩ := exists_abs_eval_natCast_le (centralA a b δ)
  obtain ⟨KD, hKD1, hDb⟩ := exists_abs_eval_natCast_le (centralD a b δ)
  generalize (centralA a b δ).natDegree = dA at hAb
  generalize (centralD a b δ).natDegree = dD at hDb
  generalize hs : a + b = s
  have hl43 : 0 < log (4 / 3 : ℝ) := Real.log_pos (by norm_num)
  obtain ⟨N, hN⟩ := exists_forall_mul_gt_sqrt
    (K := √((s : ℝ) + 4) * log 3 + 6 * s + 2 * dA + 4 + 2 * a + 2 * dD)
    (K' := (s + 2) * log 3 + 3 * (s * log (s + 2)) + log KA + log (8 / c) + log (s + 4) +
      a * log (a + 2) + log KD) hl43
  refine ⟨N + 1, fun m hm => ?_⟩
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hm0 : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have hsq : 0 ≤ √((m : ℝ) + 1) := Real.sqrt_nonneg _
  have hmain := hN m (by omega)
  have hδ' : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ
  -- `S`
  have hS : ((2 * (2 * m + δ) + s + 1 : ℕ) : ℝ) ≤ ((s : ℝ) + 4) * ((m : ℝ) + 1) ^ 1 := by
    push_cast; nlinarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)]
  have hSpos : (0 : ℝ) < ((2 * (2 * m + δ) + s + 1 : ℕ) : ℝ) := by positivity
  have hlogS := log_abs_le_of_le (K := (s : ℝ) + 4)
    (by linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)])
    (by rw [abs_of_pos hSpos]; exact hS)
  rw [abs_of_pos hSpos] at hlogS
  have hsqrtS : √((2 * (2 * m + δ) + s + 1 : ℕ) : ℝ) ≤ √((s : ℝ) + 4) * √((m : ℝ) + 1) := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (by simpa using hS)
  -- `T`
  have hT : ((∏ j ∈ Icc 1 s, (2 * m + δ + j) : ℕ) : ℝ) ≤
      ((s : ℝ) + 2) ^ s * ((m : ℝ) + 1) ^ s := by
    have h1 : ∏ j ∈ Icc 1 s, (2 * m + δ + j) ≤ (2 * m + δ + s) ^ s := by
      have := Finset.prod_le_pow_card (Icc 1 s) (fun j => 2 * m + δ + j) (2 * m + δ + s)
        fun j hj => by simp only [mem_Icc] at hj; omega
      rwa [Nat.card_Icc, show s + 1 - 1 = s by omega] at this
    have h2 : ((2 * m + δ + s : ℕ) : ℝ) ≤ ((s : ℝ) + 2) * ((m : ℝ) + 1) := by
      push_cast; nlinarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)]
    calc ((∏ j ∈ Icc 1 s, (2 * m + δ + j) : ℕ) : ℝ) ≤ ((2 * m + δ + s : ℕ) : ℝ) ^ s := by
          exact_mod_cast h1
      _ ≤ (((s : ℝ) + 2) * ((m : ℝ) + 1)) ^ s := pow_le_pow_left₀ (by positivity) h2 s
      _ = _ := mul_pow _ _ _
  have hTpos : (0 : ℝ) < ((∏ j ∈ Icc 1 s, (2 * m + δ + j) : ℕ) : ℝ) := by
    have : 0 < ∏ j ∈ Icc 1 s, (2 * m + δ + j) := Finset.prod_pos fun j hj => by
      simp only [mem_Icc] at hj; omega
    exact_mod_cast this
  have hlogT := log_abs_le_of_le (K := ((s : ℝ) + 2) ^ s)
    (one_le_pow₀ (by linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)]))
    (by rw [abs_of_pos hTpos]; exact hT)
  rw [abs_of_pos hTpos, Real.log_pow] at hlogT
  -- `A_δ(m)`
  have hlogA := log_abs_le_of_le hKA1 (hAb m)
  -- `B`
  have hB : ((2 * m + δ + a).choose a : ℝ) ≤ ((a : ℝ) + 2) ^ a * ((m : ℝ) + 1) ^ a := by
    have h1 := Nat.choose_le_pow (2 * m + δ + a) a
    have h2 : ((2 * m + δ + a : ℕ) : ℝ) ≤ ((a : ℝ) + 2) * ((m : ℝ) + 1) := by
      push_cast; nlinarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
    calc ((2 * m + δ + a).choose a : ℝ) ≤ ((2 * m + δ + a : ℕ) : ℝ) ^ a := by exact_mod_cast h1
      _ ≤ (((a : ℝ) + 2) * ((m : ℝ) + 1)) ^ a := pow_le_pow_left₀ (by positivity) h2 a
      _ = _ := mul_pow _ _ _
  have hBpos : (0 : ℝ) < ((2 * m + δ + a).choose a : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hlogB := log_abs_le_of_le (K := ((a : ℝ) + 2) ^ a)
    (one_le_pow₀ (by linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]))
    (by rw [abs_of_pos hBpos]; exact hB)
  rw [abs_of_pos hBpos, Real.log_pow] at hlogB
  -- `D_δ(m)`
  have hDpos : (0 : ℝ) < (((centralD a b δ).eval (m : ℤ) : ℤ) : ℝ) := by
    exact_mod_cast centralD_eval_pos a b δ m
  have hlogD := log_abs_le_of_le hKD1 (hDb m)
  rw [abs_of_pos hDpos] at hlogD
  -- the last logarithm
  have hsqm : (1 : ℝ) ≤ √(m : ℝ) := Real.one_le_sqrt.mpr hm1
  have hX : 8 * ((m : ℝ) + 1) * ((2 * (2 * m + δ) + s + 1 : ℕ) : ℝ) *
      ((2 * m + δ + a).choose a : ℝ) / (c * √(m : ℝ) / (((centralD a b δ).eval (m : ℤ) : ℤ) : ℝ))
      ≤ 8 / c * ((m : ℝ) + 1) * ((2 * (2 * m + δ) + s + 1 : ℕ) : ℝ) *
        ((2 * m + δ + a).choose a : ℝ) * (((centralD a b δ).eval (m : ℤ) : ℤ) : ℝ) := by
    rw [div_div_eq_mul_div, div_le_iff₀ (by positivity)]
    have hprod : 0 ≤ 8 / c * ((m : ℝ) + 1) * ((2 * (2 * m + δ) + s + 1 : ℕ) : ℝ) *
        ((2 * m + δ + a).choose a : ℝ) * (((centralD a b δ).eval (m : ℤ) : ℤ) : ℝ) := by positivity
    have e : 8 / c * ((m : ℝ) + 1) * ((2 * (2 * m + δ) + s + 1 : ℕ) : ℝ) *
        ((2 * m + δ + a).choose a : ℝ) * (((centralD a b δ).eval (m : ℤ) : ℤ) : ℝ) * c =
        8 * ((m : ℝ) + 1) * ((2 * (2 * m + δ) + s + 1 : ℕ) : ℝ) *
        ((2 * m + δ + a).choose a : ℝ) * (((centralD a b δ).eval (m : ℤ) : ℤ) : ℝ) := by
      field_simp
    nlinarith [mul_nonneg (mul_nonneg hprod hc.le) (sub_nonneg.mpr hsqm)]
  have hXpos : 0 < 8 * ((m : ℝ) + 1) * ((2 * (2 * m + δ) + s + 1 : ℕ) : ℝ) *
      ((2 * m + δ + a).choose a : ℝ) /
        (c * √(m : ℝ) / (((centralD a b δ).eval (m : ℤ) : ℤ) : ℝ)) := by positivity
  have hlogX := Real.log_le_log hXpos hX
  rw [Real.log_mul (by positivity) hDpos.ne', Real.log_mul (by positivity) hBpos.ne',
    Real.log_mul (by positivity) hSpos.ne', Real.log_mul (by positivity) hm0.ne'] at hlogX
  have hlogm1 := log_le_two_mul_sqrt hm0.le
  have hl3 : 0 < log (3 : ℝ) := Real.log_pos (by norm_num)
  have h43 : log (4 / 3 : ℝ) = 2 * log 2 - log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  have hsqS3 := mul_le_mul_of_nonneg_right hsqrtS hl3.le
  have hl2 : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
  rw [h43] at hmain
  push_cast at hlogS hlogT hlogB hlogX hsqS3 hmain ⊢
  linarith [mul_nonneg (Nat.cast_nonneg δ : (0 : ℝ) ≤ δ) hl2.le]

end ArithmeticOfJacobiPolynomials
