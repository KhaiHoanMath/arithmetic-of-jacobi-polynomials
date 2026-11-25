/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.Basic
public import ArithmeticOfJacobiPolynomials.Jacobi.DifferentialEquation
public import ArithmeticOfJacobiPolynomials.Polynomial.ReductionMultiplicity
public import Mathlib.Data.Nat.Choose.Lucas
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Data.Nat.Prime.Factorial
public import ArithmeticOfJacobiPolynomials.Jacobi.CentralValue
public import ArithmeticOfJacobiPolynomials.Jacobi.SymmetricPrimeDivisors

/-!
# Reduction of Jacobi polynomials with integral parameters modulo large primes (Lemma 3.3)

For a prime `p`, `ratReduction p P ∈ 𝔽_p[X]` is the coefficientwise reduction of `P ∈ ℚ[X]`
(each coefficient `u/v` is sent to `u v⁻¹`; this is the reduction map on `p`-integral
coefficients, and all coefficients of `P_n^{(a,b)}` are `p`-integral for odd `p`, see
`jacobiP_eq_C_mul_map_jacobiNum`).

Lemma 3.3: for `a > b ≥ 0`, `s = a + b`, `n = 2m + δ`, `M = m + s + 2`,
`T = ∏_{i=1}^{s} (n+i)`, `m ≥ 2s + 10`, an odd prime `p > M` with `p ∤ T`, and
`n = εp + j` with `ε ∈ {0,1}`, `0 ≤ j < p`: `j + s < p`,
`\bar{P_n} = x^{εp} \bar{P_j}`, every nonzero root of this reduction (in `\bar{𝔽}_p`) is
simple, and its values at `±1` are nonzero.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset
open scoped Nat

section Reduction

variable (p : ℕ) [Fact p.Prime]

/-- Coefficientwise reduction modulo `p` of a rational polynomial. -/
noncomputable def ratReduction (P : ℚ[X]) : (ZMod p)[X] :=
  ∑ i ∈ range (P.natDegree + 1), C ((P.coeff i : ℚ) : ZMod p) * X ^ i

theorem ratReduction_eq (P : ℚ[X]) : ratReduction p P =
    ∑ i ∈ range (P.natDegree + 1), C ((P.coeff i : ℚ) : ZMod p) * X ^ i := (rfl)

theorem coeff_ratReduction (P : ℚ[X]) (i : ℕ) :
    (ratReduction p P).coeff i = ((P.coeff i : ℚ) : ZMod p) := by
  rw [ratReduction_eq, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [mem_range, not_lt] at h
    rw [coeff_eq_zero_of_natDegree_lt (by omega), Rat.cast_zero]

theorem ratReduction_C_mul_map (c : ℚ) (hc : (c.den : ZMod p) ≠ 0) (g : ℤ[X]) :
    ratReduction p (C c * g.map (Int.castRingHom ℚ)) =
      C (c : ZMod p) * g.map (Int.castRingHom (ZMod p)) := by
  ext i
  rw [coeff_ratReduction, coeff_C_mul, coeff_C_mul, coeff_map, coeff_map, eq_intCast,
    eq_intCast, Rat.cast_mul_of_ne_zero hc (by simp), Rat.cast_intCast]

end Reduction

/-- The integral numerator `2^n P_n^{(a,b)} = ∑_k binom(n+a,n-k) binom(n+b,k) (x-1)^k
(x+1)^{n-k}` of (1.1) for natural parameters. -/
noncomputable def jacobiNum (a b n : ℕ) : ℤ[X] :=
  ∑ k ∈ range (n + 1), C (((n + a).choose (n - k) * (n + b).choose k : ℕ) : ℤ) *
    (X - 1) ^ k * (X + 1) ^ (n - k)

theorem jacobiNum_eq (a b n : ℕ) : jacobiNum a b n =
    ∑ k ∈ range (n + 1), C (((n + a).choose (n - k) * (n + b).choose k : ℕ) : ℤ) *
      (X - 1) ^ k * (X + 1) ^ (n - k) := (rfl)

theorem jacobiP_eq_C_mul_map_jacobiNum (a b n : ℕ) :
    jacobiP a b n = C ((1 / 2 : ℚ) ^ n) * (jacobiNum a b n).map (Int.castRingHom ℚ) := by
  rw [jacobiP_eq, jacobiNum_eq]
  congr 1
  simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub,
    Polynomial.map_add, Polynomial.map_X, Polynomial.map_one, Polynomial.map_C]
  refine sum_congr rfl fun k _ => ?_
  rw [show ((n : ℚ) + (a : ℚ)) = ((n + a : ℕ) : ℚ) by push_cast; ring,
    show ((n : ℚ) + (b : ℚ)) = ((n + b : ℕ) : ℚ) by push_cast; ring,
    Ring.choose_natCast, Ring.choose_natCast]
  simp

section Lucas

variable {p : ℕ} [hp : Fact p.Prime]

/-- Lucas's congruence in `𝔽_p`. -/
theorem natCast_choose_eq_lucas (N K : ℕ) : ((N.choose K : ℕ) : ZMod p) =
    ((N % p).choose (K % p) : ZMod p) * ((N / p).choose (K / p) : ZMod p) := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div (n := N) (k := K) (p := p)
  have := (ZMod.intCast_eq_intCast_iff _ _ p).mpr h
  push_cast at this
  exact this

theorem natCast_choose_prime_add (x y : ℕ) (hx : x < p) (hy : y < p) :
    (((p + x).choose y : ℕ) : ZMod p) = (x.choose y : ZMod p) := by
  have hp0 := hp.out.pos
  rw [natCast_choose_eq_lucas, Nat.add_mod_left, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy,
    add_comm, Nat.add_div_right _ hp0, Nat.div_eq_of_lt hx, Nat.div_eq_of_lt hy]
  simp

theorem natCast_choose_prime_add_prime_add (x y : ℕ) (hx : x < p) (hy : y < p) :
    (((p + x).choose (p + y) : ℕ) : ZMod p) = (x.choose y : ZMod p) := by
  have hp0 := hp.out.pos
  rw [natCast_choose_eq_lucas, Nat.add_mod_left, Nat.add_mod_left, Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt hy, add_comm p x, add_comm p y, Nat.add_div_right _ hp0,
    Nat.add_div_right _ hp0, Nat.div_eq_of_lt hx, Nat.div_eq_of_lt hy]
  simp

theorem map_jacobiNum_eq (a b n : ℕ) :
    (jacobiNum a b n).map (Int.castRingHom (ZMod p)) =
      ∑ k ∈ range (n + 1), C ((((n + a).choose (n - k) * (n + b).choose k : ℕ)) : ZMod p) *
        (X - 1) ^ k * (X + 1) ^ (n - k) := by
  simp only [jacobiNum_eq, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_sub, Polynomial.map_add, Polynomial.map_X, Polynomial.map_one,
    eq_intCast, Int.cast_natCast, Polynomial.map_natCast, C_eq_natCast]

/-- **The Lucas step of Lemma 3.3.** If `j + a + b < p`, then modulo `p`,
`2^{p+j} P_{p+j}^{(a,b)} ≡ 2 x^p · 2^j P_j^{(a,b)}`. -/
theorem map_jacobiNum_prime_add (a b j : ℕ) (hs : j + (a + b) < p) :
    (jacobiNum a b (p + j)).map (Int.castRingHom (ZMod p)) =
      C 2 * X ^ p * (jacobiNum a b j).map (Int.castRingHom (ZMod p)) := by
  rw [map_jacobiNum_eq, map_jacobiNum_eq,
    show p + j + 1 = (j + 1 + (p - (j + 1))) + (j + 1) by omega, sum_range_add, sum_range_add]
  have hS2 : ∑ i ∈ range (p - (j + 1)),
      C ((((p + j + a).choose (p + j - (j + 1 + i)) * (p + j + b).choose (j + 1 + i) : ℕ)) :
        ZMod p) * (X - 1) ^ (j + 1 + i) * (X + 1) ^ (p + j - (j + 1 + i)) = 0 := by
    refine sum_eq_zero fun i hi => ?_
    rw [mem_range] at hi
    rw [Nat.cast_mul, show p + j + a = p + (j + a) by ring, show p + j + b = p + (j + b) by ring,
      natCast_choose_prime_add _ _ (by omega) (by omega),
      natCast_choose_prime_add _ _ (by omega) (by omega)]
    rcases lt_or_ge (j + a) (p + j - (j + 1 + i)) with h | h
    · rw [Nat.choose_eq_zero_of_lt h]; simp
    · rw [Nat.choose_eq_zero_of_lt (n := j + b) (by omega)]; simp
  rw [hS2, add_zero]
  have hS1 : ∑ k ∈ range (j + 1),
      C ((((p + j + a).choose (p + j - k) * (p + j + b).choose k : ℕ)) : ZMod p) *
        (X - 1) ^ k * (X + 1) ^ (p + j - k) = (X + 1) ^ p * ∑ k ∈ range (j + 1),
      C ((((j + a).choose (j - k) * (j + b).choose k : ℕ)) : ZMod p) *
        (X - 1) ^ k * (X + 1) ^ (j - k) := by
    rw [mul_sum]
    refine sum_congr rfl fun k hk => ?_
    rw [mem_range] at hk
    rw [Nat.cast_mul, Nat.cast_mul, show p + j + a = p + (j + a) by ring,
      show p + j + b = p + (j + b) by ring, show p + j - k = p + (j - k) by omega,
      natCast_choose_prime_add_prime_add _ _ (by omega) (by omega),
      natCast_choose_prime_add _ _ (by omega) (by omega), pow_add]
    ring
  have hS3 : ∑ k ∈ range (j + 1),
      C ((((p + j + a).choose (p + j - (j + 1 + (p - (j + 1)) + k)) *
        (p + j + b).choose (j + 1 + (p - (j + 1)) + k) : ℕ)) : ZMod p) *
        (X - 1) ^ (j + 1 + (p - (j + 1)) + k) * (X + 1) ^ (p + j - (j + 1 + (p - (j + 1)) + k)) =
      (X - 1) ^ p * ∑ k ∈ range (j + 1),
      C ((((j + a).choose (j - k) * (j + b).choose k : ℕ)) : ZMod p) *
        (X - 1) ^ k * (X + 1) ^ (j - k) := by
    rw [mul_sum]
    refine sum_congr rfl fun k hk => ?_
    rw [mem_range] at hk
    rw [show j + 1 + (p - (j + 1)) + k = p + k by omega, show p + j - (p + k) = j - k by omega,
      Nat.cast_mul, Nat.cast_mul, show p + j + a = p + (j + a) by ring,
      show p + j + b = p + (j + b) by ring,
      natCast_choose_prime_add _ _ (by omega) (by omega),
      natCast_choose_prime_add_prime_add _ _ (by omega) (by omega), pow_add]
    ring
  rw [hS1, hS3, ← add_mul]
  congr 1
  rw [add_pow_char, sub_pow_char, one_pow]
  rw [show (C 2 : (ZMod p)[X]) = 2 from rfl]
  ring

theorem natDegree_jacobiNum_le (a b n : ℕ) : (jacobiNum a b n).natDegree ≤ n := by
  rw [jacobiNum_eq]
  refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  rw [mem_range] at hk
  refine (natDegree_mul_le).trans ?_
  have h1 : (C (((n + a).choose (n - k) * (n + b).choose k : ℕ) : ℤ) * (X - 1) ^ k).natDegree
      ≤ k := (natDegree_C_mul_le _ _).trans
    ((natDegree_pow_le).trans (by rw [← C_1, natDegree_X_sub_C, mul_one]))
  have h2 : ((X + 1 : ℤ[X]) ^ (n - k)).natDegree ≤ n - k :=
    (natDegree_pow_le).trans (by rw [← C_1, natDegree_X_add_C, mul_one])
  omega

theorem eval_one_map_jacobiNum {p : ℕ} [Fact p.Prime] (a b n : ℕ) :
    ((jacobiNum a b n).map (Int.castRingHom (ZMod p))).eval 1 =
      ((n + a).choose n : ZMod p) * 2 ^ n := by
  rw [map_jacobiNum_eq, eval_finsetSum, sum_eq_single 0]
  · simp only [Nat.sub_zero, Nat.choose_zero_right, mul_one, eval_mul, eval_C, eval_pow,
      eval_X, eval_one, pow_zero, eval_add]
    norm_num
  · intro k _ hk
    simp [zero_pow hk]
  · intro h; simp at h

theorem eval_neg_one_map_jacobiNum {p : ℕ} [Fact p.Prime] (a b n : ℕ) :
    ((jacobiNum a b n).map (Int.castRingHom (ZMod p))).eval (-1) =
      ((n + b).choose n : ZMod p) * (-2) ^ n := by
  rw [map_jacobiNum_eq, eval_finsetSum, sum_eq_single n]
  · simp only [Nat.sub_self, Nat.choose_zero_right, one_mul, eval_mul, eval_C, eval_pow,
      eval_sub, eval_X, eval_one, pow_zero, mul_one]
    norm_num
  · intro k hk hkn
    rw [mem_range] at hk
    simp [zero_pow (show n - k ≠ 0 by omega)]
  · intro h; simp at h

/-- The Jacobi differential equation (5.6) for `P_n^{(a,b)}` transfers to the integral
numerator `jacobiNum a b n`. -/
theorem jacobiNum_ode {a b n : ℕ}
    (hode : (1 - X ^ 2) * derivative (derivative (jacobiP a b n)) +
      (C ((b : ℚ) - a) - C ((a : ℚ) + b + 2) * X) * derivative (jacobiP a b n) +
      C ((n : ℚ) * (n + a + b + 1)) * jacobiP a b n = 0) :
    (1 - X ^ 2) * derivative (derivative (jacobiNum a b n)) +
      (C ((b : ℤ) - a) - C ((a : ℤ) + b + 2) * X) * derivative (jacobiNum a b n) +
      C ((n : ℤ) * (n + a + b + 1)) * jacobiNum a b n = 0 := by
  have hinj : Function.Injective (Polynomial.map (Int.castRingHom ℚ)) :=
    map_injective _ (RingHom.injective_int _)
  have hg : (jacobiNum a b n).map (Int.castRingHom ℚ) = C ((2 : ℚ) ^ n) * jacobiP a b n := by
    rw [jacobiP_eq_C_mul_map_jacobiNum, ← mul_assoc, ← C_mul, ← mul_pow]
    norm_num
  apply hinj
  simp only [C_sub, C_add, C_mul, C_eq_natCast, C_ofNat, C_1] at hode ⊢
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_pow, Polynomial.map_X, ← derivative_map, hg,
    derivative_C_mul, Polynomial.map_zero, Polynomial.map_natCast, Polynomial.map_ofNat]
  linear_combination C ((2 : ℚ) ^ n) * hode

end Lucas

section Main

variable {p : ℕ} [hp : Fact p.Prime]

theorem den_one_div_two_pow (n : ℕ) : ((1 / 2 : ℚ) ^ n).den = 2 ^ n := by
  rw [Rat.den_pow, one_div, show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num,
    Rat.inv_natCast_den_of_pos (by norm_num)]

theorem natCast_two_pow_ne_zero (hp2 : p ≠ 2) (n : ℕ) : ((2 ^ n : ℕ) : ZMod p) ≠ 0 := by
  rw [ne_eq, ZMod.natCast_eq_zero_iff]
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp (hp.out.dvd_of_dvd_pow h))

/-- The reduction of `2^{-n}` is the inverse of `2^n`. -/
theorem ratCast_one_div_two_pow_mul (hp2 : p ≠ 2) (n : ℕ) :
    (((1 / 2 : ℚ) ^ n : ℚ) : ZMod p) * 2 ^ n = 1 := by
  have h : ((((1 / 2 : ℚ) ^ n * ((2 ^ n : ℕ) : ℚ)) : ℚ) : ZMod p) = 1 := by
    rw [show (1 / 2 : ℚ) ^ n * ((2 ^ n : ℕ) : ℚ) = 1 by push_cast; rw [← mul_pow]; norm_num,
      Rat.cast_one]
  rw [Rat.cast_mul_of_ne_zero (by rw [den_one_div_two_pow]; exact natCast_two_pow_ne_zero hp2 n)
    (by simp), Rat.cast_natCast] at h
  exact_mod_cast h

theorem ratReduction_jacobiP (hp2 : p ≠ 2) (a b n : ℕ) :
    ratReduction p (jacobiP a b n) =
      C ((((1 / 2 : ℚ) ^ n : ℚ) : ZMod p)) * (jacobiNum a b n).map (Int.castRingHom (ZMod p)) := by
  rw [jacobiP_eq_C_mul_map_jacobiNum, ratReduction_C_mul_map]
  rw [den_one_div_two_pow]
  exact natCast_two_pow_ne_zero hp2 n

theorem natCast_choose_ne_zero {N k : ℕ} (hN : N < p) (hk : k ≤ N) :
    ((N.choose k : ℕ) : ZMod p) ≠ 0 := by
  rw [ne_eq, ZMod.natCast_eq_zero_iff]
  intro h
  have h2 : p ∣ N ! := h.trans ⟨k ! * (N - k)!, by
    rw [← Nat.choose_mul_factorial_mul_factorial hk]; ring⟩
  exact absurd ((Nat.Prime.dvd_factorial (hp.out : p.Prime)).mp h2) (by omega)

/-- **Lemma 3.3**. Let `a > b ≥ 0`, `s = a + b`, `n = 2m + δ` with
`δ ∈ {0,1}`, `m ≥ 2s + 10`, and let `p > M = m + s + 2` be an odd prime with
`p ∤ T = ∏_{i=1}^{s} (n+i)`. Write `n = εp + j` with `ε ∈ {0,1}`, `0 ≤ j < p`. Then
`j + s < p` and `(P_n^{(a,b)} mod p) = x^{εp} (P_j^{(a,b)} mod p)`; every nonzero root of this
reduction in the algebraic closure of `𝔽_p` is simple, and its values at `1` and `-1` are nonzero.

The Jacobi differential equation (5.6)/(3.13) `hode` is a hypothesis, to be discharged by
`ArithmeticOfJacobiPolynomials.Jacobi.DifferentialEquation`. -/
theorem jacobiP_reduction {a b m δ : ℕ} (_hab : b < a) (_hδ : δ ≤ 1)
    (_hm : 2 * (a + b) + 10 ≤ m) (hp2 : p ≠ 2) (_hpM : m + (a + b) + 2 < p)
    (hT : ¬ p ∣ ∏ i ∈ Icc 1 (a + b), (2 * m + δ + i))
    (hode : ∀ k : ℕ, (1 - X ^ 2) * derivative (derivative (jacobiP a b k)) +
      (C ((b : ℚ) - a) - C ((a : ℚ) + b + 2) * X) * derivative (jacobiP a b k) +
      C ((k : ℚ) * (k + a + b + 1)) * jacobiP a b k = 0)
    {ε j : ℕ} (hε : ε ≤ 1) (hj : j < p) (hn : 2 * m + δ = ε * p + j) :
    j + (a + b) < p ∧
    ratReduction p (jacobiP a b (2 * m + δ)) = X ^ (ε * p) * ratReduction p (jacobiP a b j) ∧
    (∀ ξ : AlgebraicClosure (ZMod p), ξ ≠ 0 →
      ((ratReduction p (jacobiP a b (2 * m + δ))).map
        (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))).rootMultiplicity ξ ≤ 1) ∧
    (ratReduction p (jacobiP a b (2 * m + δ))).eval 1 ≠ 0 ∧
    (ratReduction p (jacobiP a b (2 * m + δ))).eval (-1) ≠ 0 := by
  have hpr := hp.out
  -- `j + s < p`
  have hjs : j + (a + b) < p := by
    by_contra hcon
    apply hT
    refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ (show p - j ∈ Icc 1 (a + b) by
      rw [mem_Icc]; omega))
    rw [hn, show ε * p + j + (p - j) = (ε + 1) * p by
      rw [add_mul, one_mul]; omega]
    exact dvd_mul_left _ _
  -- the congruence
  set u : ℕ → ZMod p := fun k => (((1 / 2 : ℚ) ^ k : ℚ) : ZMod p) with hu
  have hu1 : ∀ k, u k * 2 ^ k = 1 := fun k => ratCast_one_div_two_pow_mul hp2 k
  have hred : ratReduction p (jacobiP a b (2 * m + δ)) =
      X ^ (ε * p) * ratReduction p (jacobiP a b j) := by
    rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
    · rw [zero_mul, pow_zero, one_mul, hn, zero_mul, zero_add]
    · rw [hn, one_mul, ratReduction_jacobiP hp2, ratReduction_jacobiP hp2,
        map_jacobiNum_prime_add a b j hjs]
      have h2p : (2 : ZMod p) ^ p = 2 := ZMod.pow_card 2
      have : u (p + j) * 2 = u j := by
        have e1 := hu1 (p + j)
        have e2 := hu1 j
        rw [pow_add, h2p] at e1
        linear_combination (u j) * e1 - (u (p + j) * 2) * e2
      simp only [hu] at this
      rw [← this, C_mul]
      ring
  -- values at `±1`
  set gj := (jacobiNum a b j).map (Int.castRingHom (ZMod p)) with hgj
  have h2 : (2 : ZMod p) ≠ 0 := by
    have := natCast_two_pow_ne_zero hp2 1
    simpa using this
  have hg1 : gj.eval 1 ≠ 0 := by
    rw [hgj, eval_one_map_jacobiNum]
    exact mul_ne_zero (natCast_choose_ne_zero (by omega) (by omega)) (pow_ne_zero _ h2)
  have hgm1 : gj.eval (-1) ≠ 0 := by
    rw [hgj, eval_neg_one_map_jacobiNum]
    exact mul_ne_zero (natCast_choose_ne_zero (by omega) (by omega))
      (pow_ne_zero _ (neg_ne_zero.mpr h2))
  have huj : u j ≠ 0 := fun h => by simpa [h] using hu1 j
  have hredj : ratReduction p (jacobiP a b j) = C (u j) * gj := ratReduction_jacobiP hp2 a b j
  rw [hredj] at hred
  rw [hred]
  refine ⟨hjs, by rw [hredj], ?_, ?_, ?_⟩
  · intro ξ hξ
    set red := algebraMap (ZMod p) (AlgebraicClosure (ZMod p))
    set icast := Int.castRingHom (AlgebraicClosure (ZMod p))
    have hgK : gj.map red = (jacobiNum a b j).map icast := by
      rw [hgj, Polynomial.map_map]
      congr 1
    have hgK1 : ((jacobiNum a b j).map icast).eval 1 ≠ 0 := by
      rw [← hgK, ← map_one red, eval_map, eval₂_hom]
      exact (map_ne_zero red).mpr hg1
    have hgKm1 : ((jacobiNum a b j).map icast).eval (-1) ≠ 0 := by
      rw [← hgK, ← map_one red, ← map_neg red, eval_map, eval₂_hom]
      exact (map_ne_zero red).mpr hgm1
    have hgK0 : (jacobiNum a b j).map icast ≠ 0 := fun h => hgK1 (by rw [h, eval_zero])
    have hodeK : (1 - X ^ 2) * derivative (derivative ((jacobiNum a b j).map icast)) +
        (C (((b : ℕ) : AlgebraicClosure (ZMod p)) - a) -
          C ((a : AlgebraicClosure (ZMod p)) + b + 2) * X) *
          derivative ((jacobiNum a b j).map icast) +
        C ((j : AlgebraicClosure (ZMod p)) * (j + a + b + 1)) * (jacobiNum a b j).map icast =
          0 := by
      have := congrArg (Polynomial.map icast) (jacobiNum_ode (hode j))
      simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_one,
        Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
        Polynomial.map_zero] at this
      simpa [icast] using this
    have hdegK : ((jacobiNum a b j).map icast).natDegree < p :=
      lt_of_le_of_lt (natDegree_map_le.trans (natDegree_jacobiNum_le a b j)) hj
    have hmultg : ((jacobiNum a b j).map icast).rootMultiplicity ξ ≤ 1 := by
      by_cases h1 : ξ = 1
      · rw [h1, rootMultiplicity_eq_zero hgK1]; omega
      by_cases hm1 : ξ = -1
      · rw [hm1, rootMultiplicity_eq_zero hgKm1]; omega
      refine rootMultiplicity_le_one_of_ode p hpr hodeK hgK0 hdegK ?_
      simp only [eval_sub, eval_one, eval_pow, eval_X]
      intro h
      have : (ξ - 1) * (ξ + 1) = 0 := by linear_combination -h
      rcases mul_eq_zero.mp this with h | h
      · exact h1 (sub_eq_zero.mp h)
      · exact hm1 (eq_neg_of_add_eq_zero_left h)
    have huK : red (u j) ≠ 0 := (map_ne_zero red).mpr huj
    rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_mul,
      Polynomial.map_C, hgK]
    have hne : X ^ (ε * p) * (C (red (u j)) * (jacobiNum a b j).map icast) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ X_ne_zero) (mul_ne_zero (C_ne_zero.mpr huK) hgK0)
    rw [rootMultiplicity_mul hne, rootMultiplicity_mul (mul_ne_zero_iff.mp hne).2,
      rootMultiplicity_eq_zero
        (by simp [hξ] : ¬ (X ^ (ε * p) : (AlgebraicClosure (ZMod p))[X]).IsRoot ξ),
      rootMultiplicity_eq_zero (by simp [huK] : ¬ (C (red (u j))).IsRoot ξ)]
    omega
  · rw [eval_mul, eval_pow, eval_X, one_pow, one_mul, eval_mul, eval_C]
    exact mul_ne_zero huj hg1
  · rw [eval_mul, eval_pow, eval_X, eval_mul, eval_C]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (mul_ne_zero huj hgm1)

/-- **Lemma 3.3**, with the Jacobi differential equation proved internally.
This has exactly the manuscript's parameter and prime hypotheses. -/
theorem jacobiP_reduction_proved {a b m δ : ℕ} (hab : b < a) (hδ : δ ≤ 1)
    (hm : 2 * (a + b) + 10 ≤ m) (hp2 : p ≠ 2) (hpM : m + (a + b) + 2 < p)
    (hT : ¬ p ∣ ∏ i ∈ Icc 1 (a + b), (2 * m + δ + i))
    {ε j : ℕ} (hε : ε ≤ 1) (hj : j < p) (hn : 2 * m + δ = ε * p + j) :
    j + (a + b) < p ∧
    ratReduction p (jacobiP a b (2 * m + δ)) = X ^ (ε * p) * ratReduction p (jacobiP a b j) ∧
    (∀ ξ : AlgebraicClosure (ZMod p), ξ ≠ 0 →
      ((ratReduction p (jacobiP a b (2 * m + δ))).map
        (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))).rootMultiplicity ξ ≤ 1) ∧
    (ratReduction p (jacobiP a b (2 * m + δ))).eval 1 ≠ 0 ∧
    (ratReduction p (jacobiP a b (2 * m + δ))).eval (-1) ≠ 0 :=
  jacobiP_reduction hab hδ hm hp2 hpM hT (fun k => jacobiP_ode (a : ℚ) b k) hε hj hn

/-- In the setting of Lemma 3.3 the decomposition `n = εp + j`, `ε ∈ {0,1}`, `0 ≤ j < p`
exists (as `n < 2p`). -/
theorem exists_eq_mul_add_of_lt {m δ s : ℕ} (hδ : δ ≤ 1) (hpM : m + s + 2 < p) :
    ∃ ε j, ε ≤ 1 ∧ j < p ∧ 2 * m + δ = ε * p + j := by
  have hp0 := hp.out.pos
  refine ⟨(2 * m + δ) / p, (2 * m + δ) % p, ?_, Nat.mod_lt _ hp0, ?_⟩
  · have : (2 * m + δ) / p < 2 := (Nat.div_lt_iff_lt_mul hp0).mpr (by omega)
    omega
  · exact (Nat.div_add_mod' _ _).symm

end Main

section Asymmetric

theorem coeff_jacobiNum_self (a b n : ℕ) :
    (jacobiNum a b n).coeff n = ((2 * n + a + b).choose n : ℤ) := by
  rw [jacobiNum_eq, finsetSum_coeff]
  have hterm : ∀ k ∈ range (n + 1), (C (((n + a).choose (n - k) * (n + b).choose k : ℕ) : ℤ) *
      (X - 1) ^ k * (X + 1) ^ (n - k)).coeff n =
        (((n + a).choose (n - k) * (n + b).choose k : ℕ) : ℤ) := by
    intro k hk
    rw [mem_range] at hk
    rw [mul_assoc, coeff_C_mul]
    have h1 : (X - 1 : ℤ[X]).Monic := by simpa using monic_X_sub_C (1 : ℤ)
    have h2 : (X + 1 : ℤ[X]).Monic := by simpa using monic_X_add_C (1 : ℤ)
    have hmon : ((X - 1 : ℤ[X]) ^ k * (X + 1) ^ (n - k)).Monic := (h1.pow k).mul (h2.pow _)
    have d1 : (X - 1 : ℤ[X]).natDegree = 1 := by rw [← C_1, natDegree_X_sub_C]
    have d2 : (X + 1 : ℤ[X]).natDegree = 1 := by rw [← C_1, natDegree_X_add_C]
    have hdeg : ((X - 1 : ℤ[X]) ^ k * (X + 1) ^ (n - k)).natDegree = n := by
      rw [(h1.pow k).natDegree_mul (h2.pow _), natDegree_pow, natDegree_pow, d1, d2]; omega
    have := hmon.coeff_natDegree
    rw [hdeg] at this
    rw [this, mul_one]
  rw [sum_congr rfl hterm]
  have hv := Nat.add_choose_eq (n + b) (n + a) n
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => (n + b).choose i *
    (n + a).choose j)] at hv
  rw [show 2 * n + a + b = n + b + (n + a) by ring, hv]
  push_cast
  refine sum_congr rfl fun k _ => ?_
  ring

theorem natDegree_jacobiNum (a b n : ℕ) : (jacobiNum a b n).natDegree = n := by
  refine le_antisymm (natDegree_jacobiNum_le a b n) (le_natDegree_of_ne_zero ?_)
  rw [coeff_jacobiNum_self]
  exact_mod_cast (Nat.choose_pos (by omega)).ne'

theorem eval_one_jacobiNum (a b n : ℕ) :
    (jacobiNum a b n).eval 1 = ((n + a).choose n : ℤ) * 2 ^ n := by
  rw [jacobiNum_eq, eval_finsetSum, sum_eq_single 0]
  · simp only [Nat.sub_zero, Nat.choose_zero_right, mul_one, eval_mul, eval_C, eval_pow,
      eval_X, eval_one, pow_zero, eval_add]
    norm_num
  · intro k _ hk
    simp [zero_pow hk]
  · intro h; simp at h

/-- **The prime support (3.2)** (§3.1, in the proof of Theorem 3.1).
Let `a > b ≥ 0`, `s = a+b`, `n = 2m+δ`, `m ≥ 2s+10`, and let `κ P_n^{(a,b)} = F G` be a
factorization into primitive integral factors. For an odd prime `p > M = m+s+2` with
`p ∤ T A_δ(m)`, `T = ∏_{i=1}^{s}(n+i)`: `v_p(Res(F,G)) = 0`.

The Jacobi differential equation (5.6) `hode` is a hypothesis (as in `jacobiP_reduction`). -/
theorem asymmetric_prime_support {a b m δ : ℕ} (hab : b < a) (hδ : δ ≤ 1)
    (hm : 2 * (a + b) + 10 ≤ m)
    (hode : ∀ k : ℕ, (1 - X ^ 2) * derivative (derivative (jacobiP a b k)) +
      (C ((b : ℚ) - a) - C ((a : ℚ) + b + 2) * X) * derivative (jacobiP a b k) +
      C ((k : ℚ) * (k + a + b + 1)) * jacobiP a b k = 0)
    {κ : ℚ} {F G : ℤ[X]} (hF : F.IsPrimitive) (hG : G.IsPrimitive)
    (hfac : (F * G).map (Int.castRingHom ℚ) = C κ * jacobiP a b (2 * m + δ))
    {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hpM : m + (a + b) + 2 < p)
    (hT : ¬ p ∣ ∏ i ∈ Icc 1 (a + b), (2 * m + δ + i))
    (hA : ¬ (p : ℤ) ∣ (centralA a b δ).eval (m : ℤ)) :
    ¬ (p : ℤ) ∣ resultant F G := by
  have hpr : p.Prime := hp.out
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hpr
  set n := 2 * m + δ with hn
  set g := jacobiNum a b n with hg
  set H := F * G with hH
  have hprim : H.IsPrimitive := hF.mul hG
  clear_value H
  -- `w H = u g` with `κ 2^{-n} = u / w`
  set κ' := κ * (1 / 2 : ℚ) ^ n with hκ'
  have hinj : Function.Injective (Polynomial.map (Int.castRingHom ℚ)) :=
    map_injective _ (RingHom.injective_int _)
  have hrel : C (κ'.den : ℤ) * H = C κ'.num * g := by
    apply hinj
    rw [Polynomial.map_mul, Polynomial.map_C, hfac, jacobiP_eq_C_mul_map_jacobiNum,
      Polynomial.map_mul, Polynomial.map_C, ← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul]
    congr 2
    simp only [eq_intCast, Int.cast_natCast]
    rw [← Rat.mul_den_eq_num, hκ']
    ring
  have hpu : ¬ (p : ℤ) ∣ κ'.num := by
    intro hpa
    have hCp : C (p : ℤ) ∣ H := by
      rw [C_dvd_iff_dvd_coeff]
      intro i
      have hi := congrArg (coeff · i) hrel
      simp only [coeff_C_mul] at hi
      have hpb : ¬ (p : ℤ) ∣ (κ'.den : ℤ) := by
        intro hpb
        have h1 : p ∣ κ'.num.natAbs := Int.natCast_dvd.mp hpa
        have h2 : p ∣ κ'.den := Int.natCast_dvd_natCast.mp hpb
        have := Nat.dvd_gcd h1 h2
        rw [κ'.reduced] at this
        exact hpr.one_lt.ne' (Nat.dvd_one.mp this)
      have : (p : ℤ) ∣ (κ'.den : ℤ) * H.coeff i := hi ▸ dvd_mul_of_dvd_left hpa _
      exact (hpZ.dvd_or_dvd this).resolve_left hpb
    exact hpZ.not_isUnit (hprim _ hCp)
  -- `p ∤ binom(n+a, n)`
  have hB : ¬ (p : ℤ) ∣ ((n + a).choose n : ℤ) := by
    intro h
    have h1 : p ∣ (n + a).choose n := by exact_mod_cast h
    apply hT
    have e1 := Nat.choose_mul_factorial_mul_factorial (show n ≤ n + a by omega)
    have e2 := prod_Icc_add_mul_factorial n 0 a (Nat.zero_le _)
    rw [zero_add, add_zero] at e2
    rw [show n + a - n = a by omega] at e1
    have e3 : (n + a).choose n * a ! = ∏ j ∈ Icc 1 a, (n + j) := by
      apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos n)
      rw [e2, ← e1]; ring
    exact (h1.trans ⟨a !, by rw [e3]⟩).trans
      (Finset.prod_dvd_prod_of_subset _ _ _ (Icc_subset_Icc_right (by omega)))
  have hp2n : ¬ (p : ℤ) ∣ 2 ^ n := by
    intro h
    have : (p : ℤ) ∣ 2 := hpZ.dvd_of_dvd_pow h
    have : p ∣ 2 := by exact_mod_cast this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).mp this)
  have hpw : ¬ (p : ℤ) ∣ (κ'.den : ℤ) := by
    intro hw
    have h1 := congrArg (eval 1) hrel
    simp only [eval_mul, eval_C] at h1
    rw [eval_one_jacobiNum] at h1
    have : (p : ℤ) ∣ κ'.num * (((n + a).choose n : ℤ) * 2 ^ n) :=
      h1 ▸ dvd_mul_of_dvd_left hw _
    rcases hpZ.dvd_or_dvd this with h | h
    · exact hpu h
    · rcases hpZ.dvd_or_dvd h with h | h
      · exact hB h
      · exact hp2n h
  have htrans : ∀ y z : ℤ, (κ'.den : ℤ) * y = κ'.num * z →
      ¬ (p : ℤ) ^ 2 ∣ z → ¬ (p : ℤ) ^ 2 ∣ y := by
    intro y z hyz hz hy
    exact hz (hpZ.pow_dvd_of_dvd_mul_left 2 hpu (hyz ▸ dvd_mul_of_dvd_right hy _))
  -- the reduction map
  set K := AlgebraicClosure (ZMod p)
  set redZ : ℤ →+* K := Int.castRingHom K
  have hredZ : ∀ x, redZ x = 0 ↔ (p : ℤ) ∣ x := fun x => CharP.intCast_eq_zero_iff K p x
  have hpu' : ¬ IsUnit (p : ℤ) := hpZ.not_isUnit
  have hH0 : H.map redZ ≠ 0 := map_ne_zero_of_isPrimitive redZ _ hredZ hpu' hprim
  have hnum0 : redZ κ'.num ≠ 0 := (hredZ _).not.mpr hpu
  have hden0 : redZ (κ'.den : ℤ) ≠ 0 := (hredZ _).not.mpr hpw
  -- simple roots away from `0`, from Lemma 3.3
  obtain ⟨ε, j, hε, hj, hnj⟩ := exists_eq_mul_add_of_lt (p := p) hδ hpM
  obtain ⟨-, -, hmult, -, -⟩ := jacobiP_reduction hab hδ hm hp2 hpM hT hode hε hj hnj
  rw [ratReduction_jacobiP hp2] at hmult
  have hun : (((1 / 2 : ℚ) ^ n : ℚ) : ZMod p) ≠ 0 := by
    intro h
    have := ratCast_one_div_two_pow_mul hp2 n
    rw [h, zero_mul] at this
    exact zero_ne_one this
  have hg1 : (g.map redZ).eval 1 ≠ 0 := by
    rw [← map_one redZ, eval_map, eval₂_hom, hg, eval_one_jacobiNum, ne_eq, hredZ]
    intro h
    rcases hpZ.dvd_or_dvd h with h | h
    · exact hB h
    · exact hp2n h
  have hgm0 : g.map redZ ≠ 0 := fun h => hg1 (by rw [h, eval_zero])
  have hgK : ∀ ξ : K, ξ ≠ 0 → (g.map redZ).rootMultiplicity ξ ≤ 1 := by
    intro ξ hξ
    have := hmult ξ hξ
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map] at this
    have e : (algebraMap (ZMod p) K).comp (Int.castRingHom (ZMod p)) = redZ :=
      RingHom.ext_int _ _
    rw [e, ← hg] at this
    have hu : algebraMap (ZMod p) K (((1 / 2 : ℚ) ^ n : ℚ) : ZMod p) ≠ 0 :=
      (_root_.map_ne_zero _).mpr hun
    rwa [rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr hu) hgm0), rootMultiplicity_C,
      zero_add] at this
  have hHK : C (redZ (κ'.den : ℤ)) * H.map redZ = C (redZ κ'.num) * g.map redZ := by
    have := congrArg (Polynomial.map redZ) hrel
    simpa only [Polynomial.map_mul, Polynomial.map_C] using this
  have hmultH : ∀ ξ : K, ξ ≠ 0 → (H.map redZ).rootMultiplicity ξ ≤ 1 := by
    intro ξ hξ
    have h1 := congrArg (rootMultiplicity ξ) hHK
    rw [rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr hden0) hH0),
      rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr hnum0) hgm0), rootMultiplicity_C,
      rootMultiplicity_C, zero_add, zero_add] at h1
    rw [h1]; exact hgK ξ hξ
  -- the central value
  have hp5 : 13 ≤ p := by omega
  have h0 : ¬ (p : ℤ) ^ 2 ∣ H.eval 0 := by
    refine htrans _ (g.eval 0) (by simpa only [eval_mul, eval_C] using congrArg (eval 0) hrel) ?_
    have hc2 : ¬ p ^ 2 ∣ (2 * m).choose m := by
      refine not_sq_dvd_of_mul_eq (D := m ! * m !) (E := (2 * m)!) ?_
        (Nat.factorial_ne_zero _) ?_
      · rw [← Nat.choose_mul_factorial_mul_factorial (show m ≤ 2 * m by omega),
          show 2 * m - m = m by omega]; ring
      · rw [padicValNat_factorial_eq_div (by nlinarith)]
        have : 2 * m / p < 2 := (Nat.div_lt_iff_lt_mul hpr.pos).mpr (by omega)
        omega
    have hcen := jacobiP_eval_zero_eq_central a b m δ hab hδ
    rw [jacobiP_eq_C_mul_map_jacobiNum, eval_mul, eval_C, eval_zero_map, eq_intCast,
      ← hn, ← hg] at hcen
    have hD := (centralD_eval_pos a b δ m).ne'
    have hrat : ((g.eval 0 * (centralD a b δ).eval (m : ℤ) : ℤ) : ℚ) =
        (((-1) ^ m * 2 ^ δ * ((2 * m).choose m : ℤ) * (centralA a b δ).eval (m : ℤ) : ℤ) : ℚ) := by
      push_cast
      rw [eq_div_iff hD] at hcen
      have h2 : (2 : ℚ) ^ n * (1 / 2) ^ n = 1 := by rw [← mul_pow]; norm_num
      have h4 : (2 : ℚ) ^ n * (1 / 4) ^ m = 2 ^ δ := by
        rw [hn, pow_add, pow_mul, mul_right_comm, ← mul_pow]; norm_num
      linear_combination (2 : ℚ) ^ n * hcen - ((g.eval 0 : ℤ) : ℚ) *
        (((centralD a b δ).eval (m : ℤ) : ℤ) : ℚ) * h2 +
        (-1) ^ m * ((2 * m).choose m : ℚ) * (((centralA a b δ).eval (m : ℤ) : ℤ) : ℚ) * h4
    have hint := Int.cast_injective (α := ℚ) hrat
    intro hdvd
    have : (p : ℤ) ^ 2 ∣ ((-1) ^ m * 2 ^ δ * (centralA a b δ).eval (m : ℤ)) *
        ((2 * m).choose m : ℤ) := by
      rw [show ((-1) ^ m * 2 ^ δ * (centralA a b δ).eval (m : ℤ)) * ((2 * m).choose m : ℤ) =
        (-1) ^ m * 2 ^ δ * ((2 * m).choose m : ℤ) * (centralA a b δ).eval (m : ℤ) by ring,
        ← hint]
      exact dvd_mul_of_dvd_left hdvd _
    have hnd : ¬ (p : ℤ) ∣ (-1) ^ m * 2 ^ δ * (centralA a b δ).eval (m : ℤ) := by
      intro h
      rcases hpZ.dvd_or_dvd h with h | h
      · rcases hpZ.dvd_or_dvd h with h | h
        · exact hpZ.not_isUnit (isUnit_of_dvd_unit h ((isUnit_neg_one).pow m))
        · exact hp2n (h.trans (pow_dvd_pow 2 (by omega)))
      · exact hA h
    have := hpZ.pow_dvd_of_dvd_mul_left 2 hnd this
    exact hc2 (by exact_mod_cast this)
  -- the leading coefficient
  have hHdeg : H.natDegree = n := by
    have := congrArg natDegree hrel
    have hnum : κ'.num ≠ 0 := fun h => hpu (by rw [h]; exact dvd_zero _)
    rwa [natDegree_C_mul (by exact_mod_cast κ'.den_nz), natDegree_C_mul hnum, hg,
      natDegree_jacobiNum] at this
  have hlc : ¬ (p : ℤ) ^ 2 ∣ H.leadingCoeff := by
    rw [leadingCoeff, hHdeg]
    refine htrans _ (g.coeff n) (by simpa only [coeff_C_mul] using congrArg (coeff · n) hrel) ?_
    rw [hg, coeff_jacobiNum_self]
    have hnat : ¬ p ^ 2 ∣ (2 * n + a + b).choose n := by
      refine not_sq_dvd_of_mul_eq (D := n ! * (n + (a + b))!) (E := (2 * n + a + b)!) ?_
        (Nat.factorial_ne_zero _) ?_
      · rw [← Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n + a + b by omega),
          show 2 * n + a + b - n = n + (a + b) by omega]; ring
      · rw [padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),
          padicValNat_factorial_eq_div (by nlinarith), padicValNat_factorial_eq_div (by nlinarith),
          padicValNat_factorial_eq_div (by nlinarith)]
        have := Nat.add_div_le_div_add_div_add_one n (n + (a + b)) p
        rw [show n + (n + (a + b)) = 2 * n + a + b by ring] at this
        omega
    intro h
    apply hnat
    have h' : ((p ^ 2 : ℕ) : ℤ) ∣ (((2 * n + a + b).choose n : ℕ) : ℤ) := by exact_mod_cast h
    exact Int.natCast_dvd_natCast.mp h'
  rw [← hredZ]
  subst hH
  refine map_resultant_ne_zero_of_reduction redZ _ hredZ hH0 (fun ξ hξ => ?_) hlc
  by_cases hξ0 : ξ = 0
  · exact ⟨0, by rw [hξ0, map_zero], h0⟩
  · have := hmultH ξ hξ0
    omega

end Asymmetric

end ArithmeticOfJacobiPolynomials
