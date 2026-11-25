/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Polynomial.ResultantReduction
public import ArithmeticOfJacobiPolynomials.Jacobi.Shift
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# The prime support (3.18) of factor resultants for symmetric parameters
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial
open scoped Nat

/-- **The parity argument behind (3.18)**, for integer polynomials. Let `p` be an odd prime and
`H = AB ∈ ℤ[X]` primitive. Suppose `Y = X^δ H` has degree `< 2p`, satisfies
`(1 - X²) Y'' + τ Y' + Λ Y = 0` and `Y(-X) = ε Y(X)` for a unit `ε`, and that `p²` divides none
of `H(0)`, `H(1)`, `H(-1)`, `lc H`. Then `p ∤ Res(A, B)`. -/
theorem int_not_dvd_resultant_of_symmetric_ode {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A B τ : ℤ[X]} {Λ ε : ℤ} (δ : ℕ) (hε : IsUnit ε)
    (hprim : (A * B).IsPrimitive)
    (hdeg : (X ^ δ * (A * B)).natDegree < 2 * p)
    (hode : (1 - X ^ 2) * derivative (derivative (X ^ δ * (A * B))) +
      τ * derivative (X ^ δ * (A * B)) + C Λ * (X ^ δ * (A * B)) = 0)
    (hpar : (X ^ δ * (A * B)).comp (-X) = C ε * (X ^ δ * (A * B)))
    (h0 : ¬ (p : ℤ) ^ 2 ∣ (A * B).eval 0) (h1 : ¬ (p : ℤ) ^ 2 ∣ (A * B).eval 1)
    (hm1 : ¬ (p : ℤ) ^ 2 ∣ (A * B).eval (-1)) (hlc : ¬ (p : ℤ) ^ 2 ∣ (A * B).leadingCoeff) :
    ¬ (p : ℤ) ∣ resultant A B := by
  have := Fact.mk hp
  set K := AlgebraicClosure (ZMod p)
  set red : ℤ →+* K := Int.castRingHom K
  have hred : ∀ a, red a = 0 ↔ (p : ℤ) ∣ a := fun a => CharP.intCast_eq_zero_iff K p a
  have hpu : ¬ IsUnit (p : ℤ) := by
    rw [Int.isUnit_iff]; have := hp.two_le; omega
  have hH : (A * B).map red ≠ 0 := map_ne_zero_of_isPrimitive red _ hred hpu hprim
  have hY : (X ^ δ * (A * B)).map red ≠ 0 := by
    rw [Polynomial.map_mul]
    exact mul_ne_zero (by simp) hH
  have hode' : (1 - X ^ 2) * derivative (derivative ((X ^ δ * (A * B)).map red)) +
      τ.map red * derivative ((X ^ δ * (A * B)).map red) +
      C (red Λ) * (X ^ δ * (A * B)).map red = 0 := by
    have := congrArg (Polynomial.map red) hode
    generalize X ^ δ * (A * B) = Y at this ⊢
    simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_one, Polynomial.map_pow, Polynomial.map_C, derivative_map,
      Polynomial.map_zero] using this
  have hpar' : ((X ^ δ * (A * B)).map red).comp (-X) = C (red ε) * (X ^ δ * (A * B)).map red := by
    have := congrArg (Polynomial.map red) hpar
    generalize X ^ δ * (A * B) = Y at this ⊢
    simpa only [map_comp, Polynomial.map_neg, Polynomial.map_X, Polynomial.map_mul,
      Polynomial.map_C] using this
  have hε' : red ε ≠ 0 := (hε.map red).ne_zero
  have hdeg' : ((X ^ δ * (A * B)).map red).natDegree < 2 * p :=
    lt_of_le_of_lt natDegree_map_le hdeg
  have h2 : (2 : K) ≠ 0 := by
    have : ((2 : ℕ) : K) ≠ 0 := by
      rw [ne_eq, CharP.cast_eq_zero_iff K p]
      intro h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    exact_mod_cast this
  rw [← hred]
  refine map_resultant_ne_zero_of_reduction red _ hred hH (fun ξ hξ => ?_) hlc
  by_cases h0ξ : ξ = 0
  · exact ⟨0, by simp [h0ξ], h0⟩
  by_cases h1ξ : ξ = 1
  · exact ⟨1, by simp [h1ξ], h1⟩
  by_cases hm1ξ : ξ = -1
  · exact ⟨-1, by simp [hm1ξ], hm1⟩
  exfalso
  have hσ : (1 - X ^ 2 : K[X]).eval ξ ≠ 0 := by
    simp only [eval_sub, eval_one, eval_pow, eval_X]
    intro h
    have : (ξ - 1) * (ξ + 1) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp this with h | h
    · exact h1ξ (sub_eq_zero.mp h)
    · exact hm1ξ (eq_neg_of_add_eq_zero_left h)
  have hneg : ξ ≠ -ξ := by
    intro h
    have : (2 : K) * ξ = 0 := by linear_combination h
    exact h0ξ ((mul_eq_zero.mp this).resolve_left h2)
  have hmY : 2 ≤ ((X ^ δ * (A * B)).map red).rootMultiplicity ξ := by
    rw [Polynomial.map_mul] at hY ⊢
    rw [rootMultiplicity_mul hY]
    omega
  have := two_mul_prime_le_natDegree_of_ode_of_parity p hp hode' hY hε' hpar' hneg hσ hmY
  omega

section Valuations

variable {p : ℕ} [hp : Fact p.Prime]

/-- Legendre's formula below `p²`: `v_p(k!) = ⌊k/p⌋`. -/
theorem padicValNat_factorial_eq_div {k : ℕ} (hk : k < p ^ 2) :
    padicValNat p k ! = k / p := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  rw [padicValNat_factorial (Nat.log_lt_of_lt_pow hk0.ne' hk)]
  simp

theorem padicValNat_two_pow_eq_zero (hp2 : p ≠ 2) (k : ℕ) : padicValNat p (2 ^ k) = 0 := by
  refine padicValNat.eq_zero_of_not_dvd fun h => hp2 ?_
  exact (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp (hp.out.dvd_of_dvd_pow h)

/-- If `z D = E` with `v_p(E) ≤ v_p(D) + 1`, then `p² ∤ z`. -/
theorem not_sq_dvd_of_mul_eq {z D E : ℕ} (h : z * D = E) (hE : E ≠ 0)
    (hv : padicValNat p E ≤ padicValNat p D + 1) : ¬ p ^ 2 ∣ z := by
  have hz : z ≠ 0 := by rintro rfl; exact hE (by rw [← h, zero_mul])
  have hD : D ≠ 0 := by rintro rfl; exact hE (by rw [← h, mul_zero])
  rw [padicValNat_dvd_iff_le hz]
  rw [← h, padicValNat.mul hz hD] at hv
  omega

/-- Integer version of `not_sq_dvd_of_mul_eq`, up to sign. -/
theorem int_not_sq_dvd_of_mul_eq {z : ℤ} {D E : ℕ} {s : ℚ} (hs : s = 1 ∨ s = -1)
    (h : (z : ℚ) * D = s * E) (hE : E ≠ 0)
    (hv : padicValNat p E ≤ padicValNat p D + 1) : ¬ (p : ℤ) ^ 2 ∣ z := by
  have h' : z.natAbs * D = E := by
    have : |(z : ℚ) * D| = |s * E| := by rw [h]
    rw [abs_mul, abs_mul, Nat.abs_cast, Nat.abs_cast] at this
    have hs1 : |s| = 1 := by rcases hs with rfl | rfl <;> simp
    rw [hs1, one_mul, ← Int.cast_abs, Int.abs_eq_natAbs] at this
    exact_mod_cast this
  have := not_sq_dvd_of_mul_eq h' hE hv
  intro hd
  apply this
  have : ((p ^ 2 : ℕ) : ℤ) ∣ z := by exact_mod_cast hd
  exact Int.natCast_dvd.mp this

/-- `v_p((2k)!) ≤ v_p(k!) + 1` when `2k < 3p`. -/
theorem padicValNat_factorial_two_mul_le {k : ℕ} (hp3 : 3 ≤ p) (hk : 2 * k < 3 * p) :
    padicValNat p (2 * k)! ≤ padicValNat p k ! + 1 := by
  have h3p : 3 * p ≤ p ^ 2 := by nlinarith
  rw [padicValNat_factorial_eq_div (by omega), padicValNat_factorial_eq_div (by omega)]
  have h1 : 2 * k / p < 3 := (Nat.div_lt_iff_lt_mul hp.out.pos).mpr (by linarith)
  have h2 : 2 * k / p ≤ k / p + k / p + 1 := by
    rw [two_mul]; exact Nat.add_div_le_div_add_div_add_one k k p
  omega

/-- `v_p((2N)!) ≤ v_p(N!) + v_p(n!) + 1` in the range of the leading coefficient in (3.18). -/
theorem padicValNat_factorial_two_mul_le_of_lc {n N : ℕ} (hp5 : 5 ≤ p) (hnN : n ≤ N)
    (hN : 2 * N < 5 * p) (hsmall : n < p → 2 * N < 3 * p) :
    padicValNat p (2 * N)! ≤ padicValNat p N ! + padicValNat p n ! + 1 := by
  have h5p : 5 * p ≤ p ^ 2 := by nlinarith
  rw [padicValNat_factorial_eq_div (k := 2 * N) (by omega),
    padicValNat_factorial_eq_div (k := N) (by omega),
    padicValNat_factorial_eq_div (k := n) (by omega)]
  have h1 : 2 * N / p < 5 := (Nat.div_lt_iff_lt_mul hp.out.pos).mpr (by linarith)
  have h2 : 2 * N / p ≤ N / p + N / p + 1 := by
    rw [two_mul]; exact Nat.add_div_le_div_add_div_add_one N N p
  have h3 : n / p ≤ N / p := Nat.div_le_div_right hnN
  have h0f := Nat.zero_le (N / p)
  have h0g := Nat.zero_le (n / p)
  rcases lt_or_ge n p with hnp | hnp
  · have h4 : 2 * N / p < 3 := (Nat.div_lt_iff_lt_mul hp.out.pos).mpr (by linarith [hsmall hnp])
    omega
  · have h4 : 0 < n / p := Nat.div_pos hnp hp.out.pos
    omega

/-- `v_p((n+2r)!) ≤ v_p(n!) + 1` when `2r < p` and `n + 2r < p²`. -/
theorem padicValNat_factorial_add_le {n r : ℕ} (hr : 2 * r < p) (hn : n + 2 * r < p ^ 2) :
    padicValNat p (n + 2 * r)! ≤ padicValNat p n ! + 1 := by
  rw [padicValNat_factorial_eq_div hn, padicValNat_factorial_eq_div (by omega)]
  have := Nat.add_div_le_div_add_div_add_one n (2 * r) p
  rw [Nat.div_eq_of_lt hr] at this
  omega

end Valuations

section CoefficientSum

variable {m δ n : ℕ} (c : ℕ → ℚ)

theorem coeff_sum_X_pow_sub_two_mul (hn : n = 2 * m + δ) {j : ℕ} (hj : j ≤ m) :
    (∑ k ∈ Finset.range (m + 1), C (c k) * X ^ (n - 2 * k)).coeff (n - 2 * j) = c j := by
  rw [finsetSum_coeff, Finset.sum_eq_single j]
  · simp
  · intro k hk hkj
    rw [coeff_C_mul_X_pow]
    simp at hk
    split_ifs with h
    · exfalso; omega
    · rfl
  · intro h; simp at h; omega

theorem coeff_zero_sum_X_pow_sub_two_mul (hn : n = 2 * m + 1) :
    (∑ k ∈ Finset.range (m + 1), C (c k) * X ^ (n - 2 * k)).coeff 0 = 0 := by
  rw [finsetSum_coeff]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [coeff_C_mul_X_pow]
  simp at hk
  split_ifs with h
  · exfalso; omega
  · rfl

theorem natDegree_sum_X_pow_sub_two_mul_le :
    (∑ k ∈ Finset.range (m + 1), C (c k) * X ^ (n - 2 * k)).natDegree ≤ n :=
  natDegree_sum_le_of_forall_le _ _ fun _ _ =>
    (natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le _ _)

theorem sum_X_pow_sub_two_mul_comp_neg_X (hn : n = 2 * m + δ) :
    (∑ k ∈ Finset.range (m + 1), C (c k) * X ^ (n - 2 * k)).comp (-X) =
      C ((-1) ^ n) * ∑ k ∈ Finset.range (m + 1), C (c k) * X ^ (n - 2 * k) := by
  rw [Polynomial.sum_comp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  replace hk : k < m + 1 := Finset.mem_range.mp hk
  rw [mul_comp, C_comp, pow_comp, X_comp, neg_pow, C_pow, C_neg, C_1]
  have : ((-1 : ℚ[X]) ^ n) = (-1) ^ (n - 2 * k) := by
    obtain ⟨t, ht⟩ : ∃ t, n = t + 2 * k := ⟨n - 2 * k, by omega⟩
    rw [ht, Nat.add_sub_cancel, pow_add, pow_mul]; simp
  rw [this]; ring

end CoefficientSum

/-- The Legendre polynomial `P_N` has denominators only at `2`: `2^N P_N^{(r)} ∈ ℤ[X]`. -/
theorem exists_int_two_pow_mul_iterate_derivative_legendreP (N r : ℕ) :
    ∃ g : ℤ[X], g.map (Int.castRingHom ℚ) = C ((2 : ℚ) ^ N) * derivative^[r] (legendreP N) := by
  refine ⟨derivative^[r] (∑ j ∈ Finset.range (N + 1),
    C (((N.choose (N - j) * N.choose j : ℕ)) : ℤ) * (X - 1) ^ j * (X + 1) ^ (N - j)), ?_⟩
  rw [← iterate_derivative_map, ← iterate_derivative_C_mul, legendreP_eq, jacobiP_eq,
    ← mul_assoc, ← C_mul, ← mul_pow, show (2 : ℚ) * (1 / 2) = 1 by norm_num, one_pow, C_1,
    one_mul]
  congr 1
  simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub,
    Polynomial.map_add, Polynomial.map_X, Polynomial.map_one, Polynomial.map_C, add_zero,
    Ring.choose_natCast]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

/-- The `r`-th derivative at `1` of a polynomial, from the coefficients of `P(2X+1)`:
`2^r P^{(r)}(1) = r! [X^r] P(2X+1)`. -/
theorem iterate_derivative_eval_one_eq (P : ℚ[X]) (r : ℕ) :
    (2 : ℚ) ^ r * (derivative^[r] P).eval 1 = r ! * (P.comp (2 * X + 1)).coeff r := by
  have hc : P.comp (2 * X + 1) = (taylor (1 : ℚ) P).comp (C 2 * X) := by
    rw [taylor_apply, comp_assoc]
    congr 1
    simp only [add_comp, X_comp, C_1, one_comp]
    rw [C_ofNat]
  rw [hc, comp_C_mul_X_coeff, taylor_coeff, ← factorial_smul_hasseDeriv, LinearMap.smul_apply,
    eval_smul, nsmul_eq_mul]
  ring

/-- **Endpoint value (3.19).** `P_{n+r}^{(r)}(1) = (n+2r)! / (2^r r! n!)`. -/
theorem iterate_derivative_legendreP_eval_one (n r : ℕ) :
    (derivative^[r] (legendreP (n + r))).eval 1 =
      ((n + 2 * r)! : ℚ) / (2 ^ r * r ! * n !) := by
  have h := iterate_derivative_eval_one_eq (legendreP (n + r)) r
  rw [legendreP_eq, jacobiP_comp_two_mul_X_add_one, finsetSum_coeff,
    Finset.sum_eq_single r] at h
  · rw [coeff_C_mul_X_pow, ite_eq_left_iff.mpr (fun h => absurd rfl h)] at h
    simp only [add_zero] at h
    rw [show ((n + r : ℕ) : ℚ) + r = ((n + r + r : ℕ) : ℚ) by push_cast; ring,
      show (((n + r : ℕ)) : ℚ) = ((n + r : ℕ) : ℚ) from rfl, Ring.choose_natCast,
      Ring.choose_natCast, show n + r - r = n by omega] at h
    have h1 := Nat.choose_mul_factorial_mul_factorial (show n ≤ n + r by omega)
    have h2 := Nat.choose_mul_factorial_mul_factorial (show r ≤ n + r + r by omega)
    rw [show n + r - n = r by omega] at h1
    rw [show n + r + r - r = n + r by omega, show n + r + r = n + 2 * r by ring] at h2
    have h1' : ((n + r).choose n : ℚ) * r ! * n ! = (n + r)! := by
      rw [mul_right_comm]; exact_mod_cast h1
    have h2' : ((n + 2 * r).choose r : ℚ) * r ! * (n + r)! = (n + 2 * r)! := by
      exact_mod_cast h2
    rw [show n + r + r = n + 2 * r by ring] at h
    have hr : (r ! : ℚ) ≠ 0 := by positivity
    have hn : (n ! : ℚ) ≠ 0 := by positivity
    rw [← legendreP_eq] at h
    rw [eq_div_iff (by positivity), ← h2', ← h1']
    linear_combination ((r ! : ℚ) * n !) * h
  · intro j _ hj
    rw [coeff_C_mul_X_pow, ite_eq_right_iff.mpr (fun h => absurd h.symm hj)]
  · intro h; simp at h

/-- Differentiating the Legendre equation `r` times: if
`(1 - X²) P'' - 2X P' + N(N+1) P = 0`, then `u = P^{(r)}` satisfies
`(1 - X²) u'' - 2(r+1) X u' + (N(N+1) - r(r+1)) u = 0`. -/
theorem iterate_derivative_legendre_ode {P : ℚ[X]} {N : ℕ}
    (h : (1 - X ^ 2) * derivative (derivative P) - 2 * X * derivative P +
      C ((N : ℚ) * (N + 1)) * P = 0) (r : ℕ) :
    (1 - X ^ 2) * derivative (derivative (derivative^[r] P)) -
      C (2 * ((r : ℚ) + 1)) * X * derivative (derivative^[r] P) +
      C ((N : ℚ) * (N + 1) - r * (r + 1)) * derivative^[r] P = 0 := by
  induction r with
  | zero =>
    simp only [Function.iterate_zero, id_eq, Nat.cast_zero, zero_add, mul_one, sub_zero]
    rw [show (C (2 : ℚ)) = 2 from rfl]
    exact h
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    have hd := congrArg derivative ih
    simp only [derivative_add, derivative_sub, derivative_mul, derivative_one, derivative_X_pow,
      derivative_C, derivative_X, derivative_zero, zero_mul, zero_add, mul_one, zero_sub] at hd
    push_cast
    rw [C_eq_natCast] at hd
    simp only [C_sub, C_mul, C_add, C_1, C_ofNat, C_eq_natCast] at hd ⊢
    linear_combination hd

/-- **The prime support (3.18)** (§3.2, in the proof of
Theorem 3.4). Let `n = 2m + δ` with `δ ∈ {0,1}`, `m ≥ max{2r, 4}`,
`f = P_{n+r}^{(r)}` and `h = f / x^δ`. For every factorization `κ h = F G` into primitive
integral factors and every prime `p > m`, `p ∤ Res(F, G)`.

The Legendre differential equation `hode` (the case `α = β = 0` of (5.6)) and the coefficient
formula `hcoeff` (3.16) are hypotheses, to be discharged by
`ArithmeticOfJacobiPolynomials.Jacobi`'s ODE and
Gegenbauer files. The endpoint value (3.19) is proved here
(`iterate_derivative_legendreP_eval_one`). -/
theorem symmetric_prime_support {r m δ n : ℕ} (hδ : δ ≤ 1) (hn : n = 2 * m + δ)
    (hm : max (2 * r) 4 ≤ m)
    (hode : (1 - X ^ 2) * derivative (derivative (legendreP (n + r))) -
      2 * X * derivative (legendreP (n + r)) +
      C (((n + r : ℕ) : ℚ) * ((n + r : ℕ) + 1)) * legendreP (n + r) = 0)
    (hcoeff : derivative^[r] (legendreP (n + r)) = C ((1 / 2 : ℚ) ^ (n + r)) *
      ∑ k ∈ Finset.range (m + 1), C ((-1) ^ k * ((2 * n + 2 * r - 2 * k)! : ℚ) /
        ((k ! : ℚ) * ((n + r - k)! : ℚ) * ((n - 2 * k)! : ℚ))) * X ^ (n - 2 * k))
    {κ : ℚ} {F G : ℤ[X]} (hF : F.IsPrimitive) (hG : G.IsPrimitive)
    (hfac : (F * G).map (Int.castRingHom ℚ) =
      C κ * (derivative^[r] (legendreP (n + r)) /ₘ X ^ δ))
    {p : ℕ} (hp : p.Prime) (hpm : m < p) :
    ¬ (p : ℤ) ∣ resultant F G := by
  have := Fact.mk hp
  obtain ⟨hr2, hm4⟩ : 2 * r ≤ m ∧ 4 ≤ m := ⟨le_of_max_le_left hm, le_of_max_le_right hm⟩
  have hp5 : 5 ≤ p := by omega
  have hp2 : p ≠ 2 := by omega
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  set f := derivative^[r] (legendreP (n + r)) with hf
  set c : ℕ → ℚ := fun k => (-1) ^ k * ((2 * n + 2 * r - 2 * k)! : ℚ) /
        ((k ! : ℚ) * ((n + r - k)! : ℚ) * ((n - 2 * k)! : ℚ)) with hc
  have hfS : f = C ((1 / 2 : ℚ) ^ (n + r)) *
      ∑ k ∈ Finset.range (m + 1), C (c k) * X ^ (n - 2 * k) := hcoeff
  -- consequences of the coefficient formula
  have hfdeg : f.natDegree ≤ n := by
    rw [hfS]; exact (natDegree_C_mul_le _ _).trans (natDegree_sum_X_pow_sub_two_mul_le c)
  have hfδ : f.coeff δ = (1 / 2 : ℚ) ^ (n + r) * c m := by
    rw [hfS, coeff_C_mul, show δ = n - 2 * m by omega, coeff_sum_X_pow_sub_two_mul c hn le_rfl]
  have hfn : f.coeff n = (1 / 2 : ℚ) ^ (n + r) * c 0 := by
    have := coeff_sum_X_pow_sub_two_mul c hn (Nat.zero_le m)
    rw [mul_zero, Nat.sub_zero] at this
    rw [hfS, coeff_C_mul, this]
  have hfpar : f.comp (-X) = C ((-1) ^ n) * f := by
    rw [hfS, mul_comp, C_comp, sum_X_pow_sub_two_mul_comp_neg_X c hn]; ring
  have hXf : X ^ δ ∣ f := by
    rcases (show δ = 0 ∨ δ = 1 by omega) with rfl | rfl
    · simp
    · rw [pow_one, X_dvd_iff, hfS, coeff_C_mul, coeff_zero_sum_X_pow_sub_two_mul c hn,
        mul_zero]
  have hXdiv : X ^ δ * (f /ₘ X ^ δ) = f := by
    have := modByMonic_add_div f (X ^ δ)
    rwa [(modByMonic_eq_zero_iff_dvd (monic_X_pow δ)).mpr hXf, zero_add] at this
  -- the integral polynomial `Y = x^δ F G`, a multiple of `f`
  set ι := Int.castRingHom ℚ with hι
  have hιinj : Function.Injective ι := RingHom.injective_int ι
  have hinj : Function.Injective (Polynomial.map ι) := map_injective ι hιinj
  have hprim : (F * G).IsPrimitive := hF.mul hG
  have hYprim : (X ^ δ * (F * G)).IsPrimitive := (monic_X_pow δ).isPrimitive.mul hprim
  have hYmap : (X ^ δ * (F * G)).map ι = C κ * f := by
    rw [Polynomial.map_mul, hfac, Polynomial.map_pow, Polynomial.map_X, mul_left_comm, hXdiv]
  set Y := X ^ δ * (F * G) with hYdef
  clear_value Y
  -- the differential equation for `Y`
  have hfode := iterate_derivative_legendre_ode hode r
  have hlam : (((n + r : ℕ) : ℚ) * ((n + r : ℕ) + 1) - r * (r + 1)) =
      (n : ℚ) * (n + 2 * r + 1) := by push_cast; ring
  rw [hlam] at hfode
  have hYode : (1 - X ^ 2) * derivative (derivative Y) +
      (-(C (2 * ((r : ℤ) + 1)) * X)) * derivative Y + C ((n : ℤ) * (n + 2 * r + 1)) * Y = 0 := by
    apply hinj
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_neg,
      Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      ← derivative_map, hYmap, derivative_C_mul, Polynomial.map_zero]
    simp only [hι, eq_intCast, Int.cast_mul, Int.cast_add, Int.cast_natCast, Int.cast_ofNat,
      Int.cast_one]
    linear_combination C κ * hfode
  have hYpar : Y.comp (-X) = C ((-1) ^ n) * Y := by
    apply hinj
    rw [map_comp, Polynomial.map_mul, Polynomial.map_neg, Polynomial.map_X, Polynomial.map_C,
      hYmap, mul_comp, C_comp, hfpar]
    simp only [map_pow, map_neg, map_one]
    ring
  have hYdeg : Y.natDegree ≤ n := by
    rw [← natDegree_map_eq_of_injective hιinj, hYmap]
    exact (natDegree_C_mul_le _ _).trans hfdeg
  -- integrality and the relation `b 2^N Y = a g`
  obtain ⟨g, hg⟩ := exists_int_two_pow_mul_iterate_derivative_legendreP (n + r) r
  rw [← hf] at hg
  have hrel : C ((κ.den : ℤ) * 2 ^ (n + r)) * Y = C κ.num * g := by
    apply hinj
    rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C, hYmap, hg,
      ← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul]
    congr 2
    simp only [hι, eq_intCast, Int.cast_mul, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat]
    rw [← Rat.mul_den_eq_num]
    ring
  have hpa : ¬ (p : ℤ) ∣ κ.num := by
    intro hpa
    have hpb : ¬ (p : ℤ) ∣ (κ.den : ℤ) := by
      intro hpb
      have h1 : p ∣ κ.num.natAbs := Int.natCast_dvd.mp hpa
      have h2 : p ∣ κ.den := Int.natCast_dvd_natCast.mp hpb
      have := Nat.dvd_gcd h1 h2
      rw [κ.reduced] at this
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    have hp2' : ¬ (p : ℤ) ∣ 2 ^ (n + r) := by
      intro h
      have := hpZ.dvd_of_dvd_pow h
      have : p ∣ 2 := by exact_mod_cast this
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
    have hCp : C (p : ℤ) ∣ Y := by
      rw [C_dvd_iff_dvd_coeff]
      intro i
      have hi := congrArg (coeff · i) hrel
      simp only [coeff_C_mul] at hi
      have : (p : ℤ) ∣ (κ.den : ℤ) * 2 ^ (n + r) * Y.coeff i := hi ▸ dvd_mul_of_dvd_left hpa _
      rcases hpZ.dvd_or_dvd this with h | h
      · rcases hpZ.dvd_or_dvd h with h | h
        · exact absurd h hpb
        · exact absurd h hp2'
      · exact h
    exact hpZ.not_isUnit (hYprim _ hCp)
  have htrans : ∀ y z : ℤ, (κ.den : ℤ) * 2 ^ (n + r) * y = κ.num * z →
      ¬ (p : ℤ) ^ 2 ∣ z → ¬ (p : ℤ) ^ 2 ∣ y := by
    intro y z hyz hz hy
    apply hz
    exact hpZ.pow_dvd_of_dvd_mul_left 2 hpa (hyz ▸ dvd_mul_of_dvd_right hy _)
  have hN2 : ((2 : ℚ) ^ (n + r)) * (1 / 2) ^ (n + r) = 1 := by
    rw [← mul_pow]; norm_num
  have hgcoeff : ∀ i, (g.coeff i : ℚ) = 2 ^ (n + r) * f.coeff i := by
    intro i
    have := congrArg (coeff · i) hg
    simpa only [coeff_map, coeff_C_mul, eq_intCast] using this
  -- the central coefficient
  have hY0 : ¬ (p : ℤ) ^ 2 ∣ Y.coeff δ := by
    refine htrans _ (g.coeff δ) (by simpa only [coeff_C_mul] using congrArg (coeff · δ) hrel) ?_
    refine int_not_sq_dvd_of_mul_eq (D := m ! * (n + r - m)!) (E := (2 * (n + r - m))!)
      (s := (-1) ^ m) (neg_one_pow_eq_or ℚ m) ?_ (Nat.factorial_ne_zero _) ?_
    · rw [hgcoeff, hfδ, ← mul_assoc, hN2, one_mul, hc]
      simp only
      rw [show 2 * n + 2 * r - 2 * m = 2 * (n + r - m) by omega, show n - 2 * m = δ by omega]
      have : (δ ! : ℚ) = 1 := by
        rcases (show δ = 0 ∨ δ = 1 by omega) with rfl | rfl <;> simp
      rw [this, mul_one]
      push_cast
      field_simp
    · rw [padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)]
      have := padicValNat_factorial_two_mul_le (p := p) (k := n + r - m) (by omega) (by omega)
      omega
  -- the leading coefficient
  have hYn : ¬ (p : ℤ) ^ 2 ∣ Y.coeff n := by
    refine htrans _ (g.coeff n) (by simpa only [coeff_C_mul] using congrArg (coeff · n) hrel) ?_
    refine int_not_sq_dvd_of_mul_eq (D := (n + r)! * n !) (E := (2 * (n + r))!)
      (s := 1) (Or.inl rfl) ?_ (Nat.factorial_ne_zero _) ?_
    · rw [hgcoeff, hfn, ← mul_assoc, hN2, one_mul, hc]
      simp only
      rw [show 2 * n + 2 * r - 2 * 0 = 2 * (n + r) by omega]
      simp only [mul_zero, Nat.sub_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul]
      push_cast
      field_simp
    · rw [padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)]
      exact padicValNat_factorial_two_mul_le_of_lc (by omega) (by omega) (by omega) (by omega)
  -- the endpoint value
  have hY1 : ¬ (p : ℤ) ^ 2 ∣ Y.eval 1 := by
    refine htrans _ (g.eval 1) (by simpa only [eval_mul, eval_C] using congrArg (eval 1) hrel) ?_
    refine int_not_sq_dvd_of_mul_eq (D := 2 ^ r * r ! * n !) (E := 2 ^ (n + r) * (n + 2 * r)!)
      (s := 1) (Or.inl rfl) ?_ (by positivity) ?_
    · have h1 : ((g.eval 1 : ℤ) : ℚ) = 2 ^ (n + r) * f.eval 1 := by
        have := congrArg (eval 1) hg
        rw [eval_mul, eval_C] at this
        rw [← this, eval_one_map]
        rfl
      rw [h1, hf, iterate_derivative_legendreP_eval_one]
      push_cast
      field_simp
    · rw [padicValNat.mul (by positivity) (Nat.factorial_ne_zero _),
        padicValNat.mul (by positivity) (Nat.factorial_ne_zero _),
        padicValNat.mul (by positivity) (Nat.factorial_ne_zero _),
        padicValNat_two_pow_eq_zero hp2, padicValNat_two_pow_eq_zero hp2]
      have := padicValNat_factorial_add_le (p := p) (n := n) (r := r) (by omega)
        (by nlinarith)
      omega
  -- back to `H = F G`
  have hYn0 : Y.coeff n ≠ 0 := fun h => hYn (h ▸ dvd_zero _)
  have hYnat : Y.natDegree = n := le_antisymm hYdeg (le_natDegree_of_ne_zero hYn0)
  have hlc : ¬ (p : ℤ) ^ 2 ∣ (F * G).leadingCoeff := by
    have : Y.leadingCoeff = (F * G).leadingCoeff := by
      rw [hYdef, leadingCoeff_mul, leadingCoeff_X_pow, one_mul]
    rw [← this, leadingCoeff, hYnat]
    exact hYn
  have h0 : ¬ (p : ℤ) ^ 2 ∣ (F * G).eval 0 := by
    have : Y.coeff δ = (F * G).eval 0 := by
      rw [hYdef, coeff_X_pow_mul', ite_eq_left_iff.mpr (fun h => absurd le_rfl h),
        Nat.sub_self, coeff_zero_eq_eval_zero]
    rw [← this]; exact hY0
  have h1 : ¬ (p : ℤ) ^ 2 ∣ (F * G).eval 1 := by
    have : Y.eval 1 = (F * G).eval 1 := by
      rw [hYdef, eval_mul, eval_pow, eval_X, one_pow, one_mul]
    rw [← this]; exact hY1
  have hm1 : ¬ (p : ℤ) ^ 2 ∣ (F * G).eval (-1) := by
    have e1 : Y.eval (-1) = (-1) ^ n * Y.eval 1 := by
      have := congrArg (eval 1) hYpar
      rwa [eval_comp, eval_neg, eval_X, eval_mul, eval_C] at this
    have e2 : Y.eval (-1) = (-1) ^ δ * (F * G).eval (-1) := by
      rw [hYdef, eval_mul, eval_pow, eval_X]
    intro h
    apply hY1
    have : (p : ℤ) ^ 2 ∣ (-1) ^ n * Y.eval 1 := by
      rw [← e1, e2]; exact dvd_mul_of_dvd_right h _
    exact ((isUnit_neg_one (α := ℤ)).pow n).dvd_mul_left.mp this
  have hdeg : Y.natDegree < 2 * p := by omega
  rw [hYdef] at hYode hYpar hdeg
  exact int_not_dvd_resultant_of_symmetric_ode hp hp2 δ ((isUnit_neg_one (α := ℤ)).pow n)
    hprim hdeg hYode hYpar h0 h1 hm1 hlc

end ArithmeticOfJacobiPolynomials
