/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Galois.UnequalParametersGalois
public import ArithmeticOfJacobiPolynomials.Effective.UnequalThreshold
public import Mathlib.Analysis.Polynomial.CauchyBound

/-!
# An explicit computable threshold for Theorem 1.3 (Galois group `S_n`)

Theorem 1.3 asserts an *effectively computable* `N(a,b)` such that
for `n ≥ N(a,b)` the polynomial `P_n^{(a,b)}` is irreducible with Galois group `S_n`. The
proof of the Galois assertion (§5.6) needs, for `n = 2m + δ`, the hypotheses of
Proposition 5.17: `n ≥ 5 000 000`, `𝒲_δ(m) ≠ 0` and
`log |𝒲_δ(m)| < n/10`, where `𝒲_δ = A_δ C_δ` (`galoisNumerator`, (5.27)). We make both explicit
(`s = a + b`, `Q = (s+3)^{2s+1}`):

* **a coefficient bound** (`abs_coeff_centralA_le`, `centralMajorant_eval_one_le`): every
  coefficient of `A_δ` is at most `Q` in absolute value, by an explicit majorant polynomial with
  nonnegative coefficients whose value at `1` is at most `Q`;
* **a Cauchy root bound** (`abs_lt_of_eval_eq_zero`, from `Polynomial.IsRoot.norm_lt_cauchyBound`):
  the real roots of `A_{1-δ}` have absolute value `< Q + 1`, so
  `C_δ(m) = 2^{K_{1-δ}} A_{1-δ}(m + δ - 1/2) ≠ 0` for `m ≥ Q + 2`
  (`oppositeNumerator_eval_ne_zero`), and with the root bound for `A_δ`
  (`centralA_eval_ne_zero_of_lt`) `𝒲_δ(m) ≠ 0` (`galoisNumerator_eval_ne_zero`);
* **a value bound** (`abs_galoisNumerator_eval_le`): `|𝒲_δ(m)| ≤ Q² 2^{2s} (m+1)^{2s}`, hence
  `log |𝒲_δ(m)| ≤ 2(2s+1)(s+2) + 2s + 4s √(m+1)`, and the elementary square-root domination
  `mul_sqrt_add_lt_of_sq_le` gives `log |𝒲_δ(m)| < n/10` for `m ≥ (4P+2)²`,
  `P = 5 (2(2s+1)(s+2) + 2s)` (`log_abs_galoisNumerator_eval_lt`).

The prime of Proposition 5.17 (§5.6, (5.29)) is then provided by
`exists_prime_not_dvd_of_log_lt` ([Dusart10, Theorem 5.2]), for every `n` beyond the explicit
threshold (`exists_galoisPrime_of_unequalGaloisThreshold_le`).

The threshold is the plain natural-number expression
`unequalGaloisThreshold a b = 2 (unequalMThreshold a b + (4P+2)² + 2 500 000)`, a computable
function, combined with the irreducibility threshold
`unequalThreshold a b = 2 unequalMThreshold a b`.

Main results:
*
`irreducible_galoisGroupIsSymmetric_jacobiP_of_unequalGaloisThreshold_le`:
  **Theorem 1.3, effective form**;
* `ArithmeticOfJacobiPolynomials.exists_galoisPrime_of_unequalGaloisThreshold_le`: the prime of
  Proposition 5.17 for every `n ≥ unequalGaloisThreshold a b`.

Conditional on the cited literature of `unequalIntegralParameters`: [Hanson, Theorem 1]
(`HansonLcmBound`), [DLMF, §18.2(vi)]
(`JacobiSimpleRealZeros`), [Jones, Theorem 1.1] (`JordanPrimeCycleTheorem`), [Milne, ANT v3.08,
Proposition 3.53] (`EisensteinPrimeTotallyRamified`), the Jacobi
discriminant formula (`JacobiDiscriminantFormula`) and [Dusart10, Theorem 5.2]
(`DusartThetaBound`).
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset Real

/-! ### The explicit threshold -/

/-- The constant `P = 5 (2 (2s+1)(s+2) + 2s)` of the logarithmic estimate for `𝒲_δ`. -/
def galoisLogBound (s : ℕ) : ℕ := 5 * (2 * (2 * s + 1) * (s + 2) + 2 * s)

theorem galoisLogBound_eq (s : ℕ) :
    galoisLogBound s = 5 * (2 * (2 * s + 1) * (s + 2) + 2 * s) := (rfl)

/-- The explicit threshold in `m = ⌊n/2⌋` for the Galois assertion of Theorem 1.3:
`unequalMThreshold a b + (4P+2)² + 2 500 000`, `P = galoisLogBound (a + b)`. -/
def unequalGaloisMThreshold (a b : ℕ) : ℕ :=
  unequalMThreshold a b + (4 * galoisLogBound (a + b) + 2) ^ 2 + 2500000

/-- **The explicit computable threshold `N(a,b)` of Theorem 1.3** (irreducibility and
`Gal = S_n`): `N(a,b) = 2 (unequalMThreshold a b + (4P+2)² + 2 500 000)` with
`P = 5 (2(2s+1)(s+2) + 2s)`, `s = a + b`, and
`unequalMThreshold a b = (48 (s+2)² + 2)² + (s+3)^{2s+1} + 2s + 10`. -/
def unequalGaloisThreshold (a b : ℕ) : ℕ := 2 * unequalGaloisMThreshold a b

theorem unequalGaloisMThreshold_eq (a b : ℕ) : unequalGaloisMThreshold a b =
    unequalMThreshold a b + (4 * galoisLogBound (a + b) + 2) ^ 2 + 2500000 := (rfl)

theorem unequalGaloisThreshold_eq (a b : ℕ) :
    unequalGaloisThreshold a b = 2 * unequalGaloisMThreshold a b := (rfl)

theorem unequalGaloisThreshold_comm (a b : ℕ) :
    unequalGaloisThreshold a b = unequalGaloisThreshold b a := by
  rw [unequalGaloisThreshold_eq, unequalGaloisThreshold_eq, unequalGaloisMThreshold_eq,
    unequalGaloisMThreshold_eq, unequalMThreshold_eq, unequalMThreshold_eq, Nat.add_comm a b]

theorem unequalThreshold_le_unequalGaloisThreshold (a b : ℕ) :
    unequalThreshold a b ≤ unequalGaloisThreshold a b := by
  rw [unequalThreshold_eq, unequalGaloisThreshold_eq, unequalGaloisMThreshold_eq]
  omega

/-! ### Majorants of integer polynomials -/

namespace EffectiveGalois

/-- Coefficientwise majorants are multiplicative. -/
theorem abs_coeff_mul_le {P P' Q Q' : ℤ[X]} (h : ∀ i, |P.coeff i| ≤ Q.coeff i)
    (h' : ∀ i, |P'.coeff i| ≤ Q'.coeff i) : ∀ i, |(P * P').coeff i| ≤ (Q * Q').coeff i := by
  intro i
  rw [coeff_mul, coeff_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
  rw [abs_mul]
  exact mul_le_mul (h _) (h' _) (abs_nonneg _) ((abs_nonneg _).trans (h _))

theorem abs_coeff_one_le : ∀ i, |(1 : ℤ[X]).coeff i| ≤ (1 : ℤ[X]).coeff i := by
  intro i
  rw [coeff_one]
  split_ifs <;> simp

/-- Coefficientwise majorants of finite products. -/
theorem abs_coeff_prod_le {ι : Type*} (s : Finset ι) (f g : ι → ℤ[X])
    (h : ∀ j ∈ s, ∀ i, |(f j).coeff i| ≤ (g j).coeff i) :
    ∀ i, |(∏ j ∈ s, f j).coeff i| ≤ (∏ j ∈ s, g j).coeff i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [prod_empty, prod_empty]
    exact abs_coeff_one_le
  | insert x s hx ih =>
    rw [prod_insert hx, prod_insert hx]
    exact abs_coeff_mul_le (h x (mem_insert_self x s))
      (ih fun j hj => h j (mem_insert_of_mem hj))

/-- Coefficientwise majorants of finite sums. -/
theorem abs_coeff_sum_le {ι : Type*} (s : Finset ι) (f g : ι → ℤ[X])
    (h : ∀ j ∈ s, ∀ i, |(f j).coeff i| ≤ (g j).coeff i) :
    ∀ i, |(∑ j ∈ s, f j).coeff i| ≤ (∑ j ∈ s, g j).coeff i := by
  intro i
  rw [finsetSum_coeff, finsetSum_coeff]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => h j hj i)

theorem abs_coeff_le_self {P : ℤ[X]} (h : ∀ i, 0 ≤ P.coeff i) : ∀ i, |P.coeff i| ≤ P.coeff i :=
  fun i => (abs_of_nonneg (h i)).le

theorem coeff_C_mul_X_add_C_nonneg {u v : ℤ} (hu : 0 ≤ u) (hv : 0 ≤ v) (i : ℕ) :
    0 ≤ (C u * polyX + C v).coeff i := by
  rw [coeff_add, coeff_C_mul, coeff_X, coeff_C]
  split_ifs <;> omega

theorem coeff_X_add_C_nonneg {v : ℤ} (hv : 0 ≤ v) (i : ℕ) : 0 ≤ (polyX + C v).coeff i := by
  rw [coeff_add, coeff_X, coeff_C]
  split_ifs <;> omega

theorem abs_coeff_X_sub_C_le {c : ℤ} (hc : 0 ≤ c) :
    ∀ i, |(polyX - C c).coeff i| ≤ (polyX + C c).coeff i := by
  intro i
  rw [coeff_sub, coeff_add, coeff_X, coeff_C]
  split_ifs <;> exact abs_le.mpr ⟨by omega, by omega⟩

theorem abs_coeff_C_le {c d : ℤ} (h : |c| ≤ d) : ∀ i, |(C c).coeff i| ≤ (C d).coeff i := by
  intro i
  rw [coeff_C, coeff_C]
  split_ifs <;> simp [h]

/-- The falling factorial `z^{\underline h}` is majorized by `∏_{k<h} (z + k)`. -/
theorem abs_coeff_descPochhammer_le (h : ℕ) :
    ∀ i, |(descPochhammer ℤ h).coeff i| ≤ (∏ k ∈ range h, (polyX + C (k : ℤ))).coeff i := by
  induction h with
  | zero =>
    rw [descPochhammer_zero, prod_range_zero]
    exact abs_coeff_one_le
  | succ h ih =>
    rw [descPochhammer_succ_right, prod_range_succ, ← C_eq_natCast]
    exact abs_coeff_mul_le ih (abs_coeff_X_sub_C_le (by positivity))

/-- A polynomial with nonnegative coefficients has each coefficient at most its value at `1`. -/
theorem coeff_le_eval_one {Q : ℤ[X]} (hQ0 : ∀ i, 0 ≤ Q.coeff i) (i : ℕ) :
    Q.coeff i ≤ Q.eval 1 := by
  rw [eval_eq_sum_range]
  simp only [one_pow, mul_one]
  rcases le_or_gt i Q.natDegree with hi | hi
  · exact single_le_sum (fun j _ => hQ0 j) (mem_range.mpr (by omega))
  · rw [coeff_eq_zero_of_natDegree_lt hi]
    exact sum_nonneg fun j _ => hQ0 j

/-- **Evaluation bound from a majorant**: `|A(x)| ≤ Q(1) (|x|+1)^{deg A}`. -/
theorem abs_eval_map_le {A Q : ℤ[X]} (hQ : ∀ i, |A.coeff i| ≤ Q.coeff i) (x : ℝ) :
    |(A.map (Int.castRingHom ℝ)).eval x| ≤ ((Q.eval 1 : ℤ) : ℝ) * (|x| + 1) ^ A.natDegree := by
  have hQ0 : ∀ i, 0 ≤ Q.coeff i := fun i => (abs_nonneg _).trans (hQ i)
  have hsumQ : ∑ i ∈ range (A.natDegree + 1), Q.coeff i ≤ Q.eval 1 := by
    rw [eval_eq_sum_range' (p := Q) (n := max A.natDegree Q.natDegree + 1) (by omega)]
    simp only [one_pow, mul_one]
    exact sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega))
      fun i _ _ => hQ0 i
  have hx1 : 1 ≤ |x| + 1 := by linarith [abs_nonneg x]
  rw [eval_map, eval₂_eq_sum_range]
  calc _ ≤ ∑ i ∈ range (A.natDegree + 1), ((Q.coeff i : ℤ) : ℝ) * (|x| + 1) ^ A.natDegree := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
        rw [abs_mul, abs_pow, eq_intCast, ← Int.cast_abs]
        have hi' : i ≤ A.natDegree := Nat.lt_succ_iff.mp (mem_range.mp hi)
        exact mul_le_mul (by exact_mod_cast hQ i)
          ((pow_le_pow_left₀ (abs_nonneg x) (by linarith) i).trans (pow_le_pow_right₀ hx1 hi'))
          (by positivity) (by exact_mod_cast hQ0 i)
    _ = ((∑ i ∈ range (A.natDegree + 1), Q.coeff i : ℤ) : ℝ) * (|x| + 1) ^ A.natDegree := by
        rw [Int.cast_sum, sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hsumQ) (by positivity)

/-- **Cauchy's root bound from a majorant**: a real root `x` of a nonzero `A ∈ ℤ[X]` satisfies
`|x| < Q(1) + 1` (`Polynomial.IsRoot.norm_lt_cauchyBound`, with `|lc(A)| ≥ 1`). -/
theorem abs_lt_of_eval_eq_zero {A Q : ℤ[X]} (hA : A ≠ 0) (hQ : ∀ i, |A.coeff i| ≤ Q.coeff i)
    {x : ℝ} (hx : (A.map (Int.castRingHom ℝ)).eval x = 0) : |x| < ((Q.eval 1 : ℤ) : ℝ) + 1 := by
  have hinj : Function.Injective (Int.castRingHom ℝ) := RingHom.injective_int _
  have hP : A.map (Int.castRingHom ℝ) ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hA
  have hQ0 : ∀ i, 0 ≤ Q.coeff i := fun i => (abs_nonneg _).trans (hQ i)
  have h0 : (0 : ℝ) ≤ ((Q.eval 1 : ℤ) : ℝ) := by
    exact_mod_cast (hQ0 0).trans (coeff_le_eval_one hQ0 0)
  have hBi : ∀ i, ‖(A.map (Int.castRingHom ℝ)).coeff i‖ ≤ ((Q.eval 1 : ℤ) : ℝ) := fun i => by
    rw [coeff_map, eq_intCast, Real.norm_eq_abs, ← Int.cast_abs]
    exact_mod_cast (hQ i).trans (coeff_le_eval_one hQ0 i)
  have hlead : (1 : NNReal) ≤ ‖(A.map (Int.castRingHom ℝ)).leadingCoeff‖₊ := by
    rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one, leadingCoeff_map_of_injective hinj,
      eq_intCast, Real.norm_eq_abs, ← Int.cast_abs]
    have h1 : 1 ≤ |A.leadingCoeff| := Int.one_le_abs (leadingCoeff_ne_zero.mpr hA)
    exact_mod_cast h1
  have hsup : ((range (A.map (Int.castRingHom ℝ)).natDegree).sup
      fun i => ‖(A.map (Int.castRingHom ℝ)).coeff i‖₊) ≤ ((Q.eval 1 : ℤ) : ℝ).toNNReal :=
    Finset.sup_le fun i _ => by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ h0]
      exact hBi i
  have key : cauchyBound (A.map (Int.castRingHom ℝ)) ≤ ((Q.eval 1 : ℤ) : ℝ).toNNReal + 1 := by
    rw [cauchyBound]
    exact add_le_add (div_le_of_le_mul₀ (by positivity) (by positivity)
      (hsup.trans (le_mul_of_one_le_right (by positivity) hlead))) le_rfl
  have h1 := (Polynomial.IsRoot.norm_lt_cauchyBound hP hx).trans_le key
  have h2 : ((‖x‖₊ : NNReal) : ℝ) < ((((Q.eval 1 : ℤ) : ℝ).toNNReal + 1 : NNReal) : ℝ) :=
    NNReal.coe_lt_coe.mpr h1
  rwa [NNReal.coe_add, Real.coe_toNNReal _ h0, NNReal.coe_one, coe_nnnorm,
    Real.norm_eq_abs] at h2

/-! ### The majorant of `A_δ` -/

/-- A majorant of `A_δ` of (3.6), with nonnegative coefficients: the falling factorial is
replaced by `∏_{k<h} (z+k)` and the signs are dropped. -/
noncomputable def centralMajorant (a b δ : ℕ) : ℤ[X] :=
  (∏ j ∈ Icc 1 (b + δ), (C 2 * polyX + C (j : ℤ))) *
    ∑ h ∈ range (centralH a b δ + 1),
      C (((a - b).choose (δ + 2 * h) : ℕ) : ℤ) * (∏ k ∈ range h, (polyX + C (k : ℤ))) *
        ∏ j ∈ Icc (b + δ + h + 1) (centralK a b δ), (polyX + C (j : ℤ))

theorem abs_coeff_centralA_le (a b δ : ℕ) :
    ∀ i, |(centralA a b δ).coeff i| ≤ (centralMajorant a b δ).coeff i := by
  rw [centralA_eq, centralMajorant]
  refine abs_coeff_mul_le (abs_coeff_prod_le _ _ _ fun j _ => abs_coeff_le_self
    (coeff_C_mul_X_add_C_nonneg (by norm_num) (by positivity)))
    (abs_coeff_sum_le _ _ _ fun h _ => abs_coeff_mul_le (abs_coeff_mul_le
      (abs_coeff_C_le (by simp [abs_mul])) (abs_coeff_descPochhammer_le h))
      (abs_coeff_prod_le _ _ _ fun j _ => abs_coeff_le_self
        (coeff_X_add_C_nonneg (by positivity))))

theorem centralMajorant_eval_one (a b δ : ℕ) : (centralMajorant a b δ).eval 1 =
    (((∏ j ∈ Icc 1 (b + δ), (2 + j)) * ∑ h ∈ range (centralH a b δ + 1),
      (a - b).choose (δ + 2 * h) * (∏ k ∈ range h, (1 + k)) *
        ∏ j ∈ Icc (b + δ + h + 1) (centralK a b δ), (1 + j) : ℕ) : ℤ) := by
  rw [centralMajorant]
  simp only [eval_mul, eval_prod, eval_finsetSum, eval_add, eval_C, eval_X, mul_one]
  first | (push_cast; done) | (push_cast; rfl)

/-- `Q_δ(1) ≤ (s+3)^{2s+1}` for the majorant `Q_δ` of `A_δ`. -/
theorem centralMajorant_eval_one_le (a b δ : ℕ) (hab : b < a) (hδ : δ ≤ 1) :
    (centralMajorant a b δ).eval 1 ≤ (((a + b + 3) ^ (2 * (a + b) + 1) : ℕ) : ℤ) := by
  rw [centralMajorant_eval_one]
  have hK := centralK_eq a b δ
  have hH := centralH_eq a b δ
  have hKs := centralK_le_add a b δ hab hδ
  obtain ⟨Y, hY⟩ : ∃ Y, Y = a + b + 3 := ⟨_, rfl⟩
  have hterm : ∀ h ∈ range (centralH a b δ + 1),
      (a - b).choose (δ + 2 * h) * (∏ k ∈ range h, (1 + k)) *
        ∏ j ∈ Icc (b + δ + h + 1) (centralK a b δ), (1 + j) ≤
          Y ^ (a + b) * Y ^ centralH a b δ := by
    intro h hh
    have hh' : h ≤ centralH a b δ := Nat.lt_succ_iff.mp (mem_range.mp hh)
    calc (a - b).choose (δ + 2 * h) * (∏ k ∈ range h, (1 + k)) *
          ∏ j ∈ Icc (b + δ + h + 1) (centralK a b δ), (1 + j)
        ≤ Y ^ (a + b) * Y ^ h * Y ^ (Icc (b + δ + h + 1) (centralK a b δ)).card := by
          refine Nat.mul_le_mul (Nat.mul_le_mul ?_ ?_) ?_
          · exact (Nat.choose_le_two_pow _ _).trans ((Nat.pow_le_pow_right (by norm_num)
              (by omega)).trans (Nat.pow_le_pow_left (by omega) _))
          · have := Finset.prod_le_pow_card (range h) (fun k => 1 + k) Y fun k hk => by
              rw [mem_range] at hk
              omega
            rwa [card_range] at this
          · exact Finset.prod_le_pow_card _ _ _ fun j hj => by
              obtain ⟨_, hj2⟩ := mem_Icc.mp hj
              omega
      _ = Y ^ (a + b) * Y ^ centralH a b δ := by
          rw [mul_assoc, ← pow_add, Nat.card_Icc]
          congr 2
          omega
  have hsum : ∑ h ∈ range (centralH a b δ + 1),
      (a - b).choose (δ + 2 * h) * (∏ k ∈ range h, (1 + k)) *
        ∏ j ∈ Icc (b + δ + h + 1) (centralK a b δ), (1 + j) ≤
          (centralH a b δ + 1) * (Y ^ (a + b) * Y ^ centralH a b δ) := by
    refine (sum_le_sum hterm).trans_eq ?_
    rw [sum_const, card_range, smul_eq_mul]
  have hprod : ∏ j ∈ Icc 1 (b + δ), (2 + j) ≤ Y ^ (b + δ) := by
    have := Finset.prod_le_pow_card (Icc 1 (b + δ)) (fun j => 2 + j) Y fun j hj => by
      obtain ⟨_, hj2⟩ := mem_Icc.mp hj
      omega
    rwa [Nat.card_Icc, show b + δ + 1 - 1 = b + δ by omega] at this
  have hnat : Y ^ (b + δ) * ((centralH a b δ + 1) * (Y ^ (a + b) * Y ^ centralH a b δ)) ≤
      Y ^ (2 * (a + b) + 1) := by
    calc Y ^ (b + δ) * ((centralH a b δ + 1) * (Y ^ (a + b) * Y ^ centralH a b δ))
        = (centralH a b δ + 1) * Y ^ (a + b) * Y ^ centralK a b δ := by rw [hK]; ring
      _ ≤ Y * Y ^ (a + b) * Y ^ (a + b) :=
          Nat.mul_le_mul (Nat.mul_le_mul (by omega) le_rfl)
            (Nat.pow_le_pow_right (by omega) hKs)
      _ = Y ^ (2 * (a + b) + 1) := by ring
  have htot := (Nat.mul_le_mul hprod hsum).trans hnat
  rw [hY] at htot
  exact_mod_cast htot

/-! ### The numerator `𝒲_δ = A_δ C_δ` -/

theorem ratCast_eval_map (A : ℤ[X]) (w : ℚ) :
    (((A.map (Int.castRingHom ℚ)).eval w : ℚ) : ℝ) =
      (A.map (Int.castRingHom ℝ)).eval (w : ℝ) := by
  rw [eval_map, eval_map, eval₂_eq_sum_range, eval₂_eq_sum_range, Rat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eq_intCast, eq_intCast, Rat.cast_mul, Rat.cast_pow, Rat.cast_intCast]

/-- `C_δ(m) = 2^{K_{1-δ}} A_{1-δ}(m + δ - 1/2)` (5.27), as real numbers. -/
theorem intCast_oppositeNumerator_eval_eq (a b δ m : ℕ) :
    (((oppositeNumerator a b δ).eval (m : ℤ) : ℤ) : ℝ) = 2 ^ centralK a b (1 - δ) *
      ((centralA a b (1 - δ)).map (Int.castRingHom ℝ)).eval ((m : ℝ) + δ - 1 / 2) := by
  have h := congrArg (eval ((m : ℤ) : ℚ)) (oppositeNumerator_map a b δ)
  rw [eval_intCast_map, eval_mul, eval_C, eval_comp, eval_add, eval_X, eval_C, eq_intCast,
    Int.cast_id] at h
  replace h := congrArg (Rat.cast : ℚ → ℝ) h
  rw [Rat.cast_intCast, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, ratCast_eval_map] at h
  rw [h]
  congr 2
  push_cast
  ring

/-- **The root bound for `C_δ`**: `C_δ(m) ≠ 0` for `m ≥ (s+3)^{2s+1} + 2`. -/
theorem oppositeNumerator_eval_ne_zero (a b δ m : ℕ) (hab : b < a) (hδ : δ ≤ 1)
    (hm : (a + b + 3) ^ (2 * (a + b) + 1) + 2 ≤ m) :
    (oppositeNumerator a b δ).eval (m : ℤ) ≠ 0 := by
  intro h0
  have hreal := intCast_oppositeNumerator_eval_eq a b δ m
  rw [h0, Int.cast_zero, eq_comm, mul_eq_zero] at hreal
  have hroot := hreal.resolve_left (pow_ne_zero _ two_ne_zero)
  have hlt := abs_lt_of_eval_eq_zero (UnequalParameters.centralA_ne_zero_of_lt hab
    (show 1 - δ ≤ 1 by omega)) (abs_coeff_centralA_le a b (1 - δ)) hroot
  have hQ := centralMajorant_eval_one_le a b (1 - δ) hab (by omega)
  have hQr : (((centralMajorant a b (1 - δ)).eval 1 : ℤ) : ℝ) ≤
      (((a + b + 3) ^ (2 * (a + b) + 1) : ℕ) : ℝ) := by exact_mod_cast hQ
  have hmr : ((((a + b + 3) ^ (2 * (a + b) + 1) : ℕ) : ℝ)) + 2 ≤ m := by exact_mod_cast hm
  have hx := le_abs_self ((m : ℝ) + δ - 1 / 2)
  have hδ0 : (0 : ℝ) ≤ δ := Nat.cast_nonneg δ
  linarith

/-- **`𝒲_δ(m) ≠ 0`** for `m ≥ (s+3)^{2s+1} + 2`. -/
theorem galoisNumerator_eval_ne_zero (a b δ m : ℕ) (hab : b < a) (hδ : δ ≤ 1)
    (hm : (a + b + 3) ^ (2 * (a + b) + 1) + 2 ≤ m) :
    (galoisNumerator a b δ).eval (m : ℤ) ≠ 0 := by
  rw [galoisNumerator_eq, eval_mul]
  exact mul_ne_zero (centralA_eval_ne_zero_of_lt a b δ m hab hδ (by omega))
    (oppositeNumerator_eval_ne_zero a b δ m hab hδ hm)

/-- `|C_δ(m)| ≤ 2^s Q 2^s (m+1)^s`, `Q = (s+3)^{2s+1}`. -/
theorem abs_oppositeNumerator_eval_le (a b δ m : ℕ) (hab : b < a) (hδ : δ ≤ 1) :
    |(((oppositeNumerator a b δ).eval (m : ℤ) : ℤ) : ℝ)| ≤
      2 ^ (a + b) * (((a + b + 3) ^ (2 * (a + b) + 1) : ℕ) : ℝ) * 2 ^ (a + b) *
        ((m : ℝ) + 1) ^ (a + b) := by
  rw [intCast_oppositeNumerator_eval_eq, abs_mul, abs_pow, abs_two]
  have hδr : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hx : |(m : ℝ) + δ - 1 / 2| + 1 ≤ 2 * ((m : ℝ) + 1) := by
    rcases abs_cases ((m : ℝ) + δ - 1 / 2) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
      linarith [(Nat.cast_nonneg δ : (0 : ℝ) ≤ δ)]
  have hev := abs_eval_map_le (abs_coeff_centralA_le a b (1 - δ)) ((m : ℝ) + δ - 1 / 2)
  have hQ := centralMajorant_eval_one_le a b (1 - δ) hab (by omega)
  have hQr : (((centralMajorant a b (1 - δ)).eval 1 : ℤ) : ℝ) ≤
      (((a + b + 3) ^ (2 * (a + b) + 1) : ℕ) : ℝ) := by exact_mod_cast hQ
  have hK' := centralK_le_add a b (1 - δ) hab (by omega)
  have hdeg : (centralA a b (1 - δ)).natDegree ≤ a + b :=
    (UnequalParameters.natDegree_centralA_le a b (1 - δ)).trans hK'
  have hpow : (|(m : ℝ) + δ - 1 / 2| + 1) ^ (centralA a b (1 - δ)).natDegree ≤
      (2 * ((m : ℝ) + 1)) ^ (a + b) :=
    (pow_le_pow_left₀ (by positivity) hx _).trans (pow_le_pow_right₀ (by linarith) hdeg)
  have h2K : (2 : ℝ) ^ centralK a b (1 - δ) ≤ 2 ^ (a + b) :=
    pow_le_pow_right₀ (by norm_num) hK'
  calc _ ≤ 2 ^ (a + b) * ((((a + b + 3) ^ (2 * (a + b) + 1) : ℕ) : ℝ) *
          (2 * ((m : ℝ) + 1)) ^ (a + b)) :=
        mul_le_mul h2K (hev.trans (mul_le_mul hQr hpow (by positivity) (by positivity)))
          (abs_nonneg _) (by positivity)
    _ = _ := by rw [mul_pow]; ring

/-- **The value bound**: `|𝒲_δ(m)| ≤ Q² 2^{2s} (m+1)^{2s}`, `Q = (s+3)^{2s+1}`. -/
theorem abs_galoisNumerator_eval_le (a b δ m : ℕ) (hab : b < a) (hδ : δ ≤ 1) :
    |(((galoisNumerator a b δ).eval (m : ℤ) : ℤ) : ℝ)| ≤
      (((a + b + 3) ^ (2 * (a + b) + 1) : ℕ) : ℝ) ^ 2 * 2 ^ (2 * (a + b)) *
        ((m : ℝ) + 1) ^ (2 * (a + b)) := by
  rw [galoisNumerator_eq, eval_mul, Int.cast_mul, abs_mul]
  have hA : |(((centralA a b δ).eval (m : ℤ) : ℤ) : ℝ)| ≤
      (((a + b + 3) ^ (2 * (a + b) + 1) : ℕ) : ℝ) * ((m : ℝ) + 1) ^ (a + b) := by
    have h := abs_centralA_eval_le a b δ m hab hδ
    exact_mod_cast h
  have hC := abs_oppositeNumerator_eval_le a b δ m hab hδ
  calc _ ≤ ((((a + b + 3) ^ (2 * (a + b) + 1) : ℕ) : ℝ) * ((m : ℝ) + 1) ^ (a + b)) *
        (2 ^ (a + b) * (((a + b + 3) ^ (2 * (a + b) + 1) : ℕ) : ℝ) * 2 ^ (a + b) *
          ((m : ℝ) + 1) ^ (a + b)) := mul_le_mul hA hC (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- **The logarithmic estimate (5.28)**: `log |𝒲_δ(m)| < n/10` for
`m ≥ (4P+2)²`, `P = galoisLogBound s`. -/
theorem log_abs_galoisNumerator_eval_lt (a b δ m : ℕ) (hab : b < a) (hδ : δ ≤ 1)
    (hm : (4 * galoisLogBound (a + b) + 2) ^ 2 ≤ m) :
    Real.log |(((galoisNumerator a b δ).eval (m : ℤ) : ℤ) : ℝ)| < (2 * m + δ : ℝ) / 10 := by
  obtain ⟨s, hs⟩ : ∃ s, s = a + b := ⟨_, rfl⟩
  have hW := abs_galoisNumerator_eval_le a b δ m hab hδ
  rw [← hs] at hW hm
  have hQ1 : (1 : ℝ) ≤ (((s + 3) ^ (2 * s + 1) : ℕ) : ℝ) := by
    have : 1 ≤ (s + 3) ^ (2 * s + 1) := Nat.one_le_pow _ _ (by omega)
    exact_mod_cast this
  have hK1 : (1 : ℝ) ≤ (((s + 3) ^ (2 * s + 1) : ℕ) : ℝ) ^ 2 * 2 ^ (2 * s) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hQ1) (one_le_pow₀ (by norm_num))
  have hlogW := log_abs_le_of_le hK1 hW
  have hlogK : Real.log ((((s + 3) ^ (2 * s + 1) : ℕ) : ℝ) ^ 2 * 2 ^ (2 * s)) ≤
      2 * (2 * s + 1) * (s + 2) + 2 * s := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Nat.cast_pow,
      Real.log_pow]
    have h3 : Real.log ((((s + 3 : ℕ)) : ℝ)) ≤ (s : ℝ) + 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((s + 3 : ℕ) : ℝ) by positivity)
      push_cast at this ⊢
      linarith
    have h2 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9
      linarith
    have h3' := mul_le_mul_of_nonneg_left h3 (show (0 : ℝ) ≤ ((2 * s + 1 : ℕ) : ℝ) by positivity)
    have h2' := mul_le_mul_of_nonneg_left h2.le (show (0 : ℝ) ≤ ((2 * s : ℕ) : ℝ) by positivity)
    push_cast at h3' h2' ⊢
    linarith
  have hP := galoisLogBound_eq s
  obtain ⟨P, hPdef⟩ : ∃ P, P = galoisLogBound s := ⟨_, rfl⟩
  rw [← hPdef] at hm hP
  have hPr : (P : ℝ) = 5 * (2 * (2 * s + 1) * (s + 2) + 2 * s) := by rw [hP]; norm_cast
  have hmr : (4 * (P : ℝ) + 2) ^ 2 ≤ (m : ℝ) := by exact_mod_cast hm
  have hlt := mul_sqrt_add_lt_of_sq_le (K := 5 * (s : ℝ))
    (K' := 5 / 4 * Real.log ((((s + 3) ^ (2 * s + 1) : ℕ) : ℝ) ^ 2 * 2 ^ (2 * s)))
    (P := (P : ℝ)) (m := (m : ℝ)) (by positivity)
    (by nlinarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)])
    (by nlinarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)]) hmr
  rw [Nat.cast_mul, Nat.cast_ofNat] at hlogW
  linarith [(Nat.cast_nonneg δ : (0 : ℝ) ≤ δ)]

/-- **The hypotheses of Proposition 5.17 at an explicit range**: for `a > b ≥ 0` and
`m ≥ unequalGaloisMThreshold a b`, `n = 2m + δ ≥ 5 000 000`, `𝒲_δ(m) ≠ 0` and
`log |𝒲_δ(m)| < n/10`. -/
theorem galois_hypotheses_of_le {a b m δ : ℕ} (hab : b < a) (hδ : δ ≤ 1)
    (hm : unequalGaloisMThreshold a b ≤ m) :
    2 * (a + b) + 10 ≤ m ∧ 5000000 ≤ 2 * m + δ ∧ (galoisNumerator a b δ).eval (m : ℤ) ≠ 0 ∧
      Real.log |(((galoisNumerator a b δ).eval (m : ℤ) : ℤ) : ℝ)| < (2 * m + δ : ℝ) / 10 := by
  rw [unequalGaloisMThreshold_eq, unequalMThreshold_eq] at hm
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (a + b + 3) ^ (2 * (a + b) + 1) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = (4 * galoisLogBound (a + b) + 2) ^ 2 := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = (48 * (a + b + 2) ^ 2 + 2) ^ 2 := ⟨_, rfl⟩
  rw [← hQ, ← hP, ← hR] at hm
  exact ⟨by omega, by omega,
    galoisNumerator_eval_ne_zero a b δ m hab hδ (by rw [← hQ]; omega),
    log_abs_galoisNumerator_eval_lt a b δ m hab hδ (by rw [← hP]; omega)⟩

end EffectiveGalois

open EffectiveGalois

/-! ### The prime of Proposition 5.17 and Theorem 1.3 -/

/-- **The prime of Proposition 5.17 at an explicit range** (§5.6, (5.29)). For `a > b ≥ 0`
and `n = 2m + δ ≥ unequalGaloisThreshold a b` (`δ ∈ {0,1}`) there is a prime `p` with
`3n/4 < p ≤ 7n/8` and `p ∤ 𝒲_δ(m)`. Conditional on [Dusart10, Theorem 5.2] (`hDusart`). -/
theorem exists_galoisPrime_of_unequalGaloisThreshold_le (hDusart : DusartThetaBound)
    {a b m δ : ℕ} (hab : b < a) (hδ : δ ≤ 1) (hn : unequalGaloisThreshold a b ≤ 2 * m + δ) :
    2 * (a + b) + 10 ≤ m ∧ ∃ p : ℕ, p.Prime ∧ 3 * (2 * m + δ) < 4 * p ∧
      8 * p ≤ 7 * (2 * m + δ) ∧ ¬ (p : ℤ) ∣ (galoisNumerator a b δ).eval (m : ℤ) := by
  rw [unequalGaloisThreshold_eq] at hn
  obtain ⟨hm, hn5, hW0, hWlog⟩ := galois_hypotheses_of_le hab hδ (show
    unequalGaloisMThreshold a b ≤ m by omega)
  exact ⟨hm, UnequalParameters.exists_prime_not_dvd_of_log_lt hDusart hn5 hW0
    (by exact_mod_cast hWlog)⟩

/-- Theorem 1.3, effective form, for `a > b ≥ 0`. -/
theorem galoisSymmetric_of_unequalGaloisThreshold_le_of_lt (hH : HansonLcmBound) (hZ :
    JacobiSimpleRealZeros)
    (hJordan : JordanPrimeCycleTheorem) (hEis : EisensteinPrimeTotallyRamified)
    (hdisc : JacobiDiscriminantFormula)
    (hDusart : DusartThetaBound) {a b : ℕ} (hab : b < a) :
    ∀ n ≥ unequalGaloisThreshold a b,
      Irreducible (jacobiP a b n) ∧ GaloisGroupIsSymmetric (jacobiP a b n) := by
  intro n hn
  have hirr := irreducible_jacobiP_of_unequalThreshold_le hH hZ (show a ≠ b by omega) n
    ((unequalThreshold_le_unequalGaloisThreshold a b).trans hn)
  refine ⟨hirr, ?_⟩
  obtain ⟨m, δ, hδ, rfl⟩ : ∃ m δ, δ ≤ 1 ∧ n = 2 * m + δ :=
    ⟨n / 2, n % 2, by omega, by omega⟩
  obtain ⟨hm, p, hp, hp1, hp2, hpW⟩ :=
    exists_galoisPrime_of_unequalGaloisThreshold_le hDusart hab hδ hn
  exact galoisGroupIsSymmetric_jacobiP_of_prime hJordan hEis hdisc hab hδ hm hirr hp hp1 hp2 hpW

/-- **Theorem 1.3, effective form**. For distinct nonnegative
integers `a, b` and every `n ≥ unequalGaloisThreshold a b`, `P_n^{(a,b)}` is irreducible over
`ℚ` with Galois group `S_n`. Here
`unequalGaloisThreshold a b = 2 (unequalMThreshold a b + (4P+2)² + 2 500 000)`,
`P = 5 (2(2s+1)(s+2) + 2s)`, `unequalMThreshold a b = (48(s+2)²+2)² + (s+3)^{2s+1} + 2s + 10`,
`s = a + b`, is an explicit computable function of `a, b`. Conditional on [Hanson, Theorem 1]
(`hH`), [DLMF, §18.2(vi)] (`hZ`), [Jones, Theorem 1.1] (`hJordan`),
[Milne, ANT v3.08, Proposition 3.53] (`hEis`), the Jacobi discriminant formula
[DLMF, (18.16.19)] (`hdisc`) and [Dusart10, Theorem 5.2] (`hDusart`). -/
theorem irreducible_galoisGroupIsSymmetric_jacobiP_of_unequalGaloisThreshold_le (hH :
    HansonLcmBound) (hZ : JacobiSimpleRealZeros)
    (hJordan : JordanPrimeCycleTheorem) (hEis : EisensteinPrimeTotallyRamified)
    (hdisc : JacobiDiscriminantFormula)
    (hDusart : DusartThetaBound) {a b : ℕ} (hab : a ≠ b) :
    ∀ n ≥ unequalGaloisThreshold a b,
      Irreducible (jacobiP a b n) ∧ GaloisGroupIsSymmetric (jacobiP a b n) := by
  rcases lt_or_gt_of_ne hab with h | h
  · intro n hn
    rw [unequalGaloisThreshold_comm] at hn
    obtain ⟨h1, h2⟩ :=
      galoisSymmetric_of_unequalGaloisThreshold_le_of_lt hH hZ hJordan hEis hdisc hDusart h n hn
    exact ⟨(irreducible_jacobiP_comm _ _ n).mpr h1,
      galoisGroupIsSymmetric_jacobiP_comm (a : ℚ) b n h2⟩
  · exact galoisSymmetric_of_unequalGaloisThreshold_le_of_lt hH hZ hJordan hEis hdisc hDusart h

/-- The existence form of Theorem 1.3 with the explicit witness `unequalGaloisThreshold a b`. -/
theorem exists_forall_irreducible_galoisGroupIsSymmetric_jacobiP_effective (hH : HansonLcmBound) (hZ
    : JacobiSimpleRealZeros)
    (hJordan : JordanPrimeCycleTheorem) (hEis : EisensteinPrimeTotallyRamified)
    (hdisc : JacobiDiscriminantFormula)
    (hDusart : DusartThetaBound) {a b : ℕ} (hab : a ≠ b) :
    ∃ N : ℕ, N = unequalGaloisThreshold a b ∧ ∀ n ≥ N,
      Irreducible (jacobiP a b n) ∧ GaloisGroupIsSymmetric (jacobiP a b n) :=
  ⟨_, rfl, irreducible_galoisGroupIsSymmetric_jacobiP_of_unequalGaloisThreshold_le
    hH hZ hJordan hEis hdisc hDusart hab⟩

end ArithmeticOfJacobiPolynomials
