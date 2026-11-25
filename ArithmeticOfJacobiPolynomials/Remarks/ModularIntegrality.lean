/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Remarks.Modular
public import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
# `ℓ`-integrality of the Kaneko–Zagier polynomials at prime indices (§6.4)

The manuscript asserts that for prime `ℓ = 12n + e ≥ 5`, `Y^a (Y-1728)^b F̃_{ℓ-1}(Y)` has
`ℓ`-integral coefficients (and then quotes [KZ, Theorem 1] for its reduction to the
supersingular polynomial, which is not formalized). We prove the integrality: the polynomial is
a rational constant of `ℓ`-adic valuation `≥ 0` times an integer polynomial, so every nonzero
coefficient has `v_ℓ ≥ 0`.
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial

/-- `F̃_{ℓ-1}` is a rational multiple of an integer polynomial, with an explicit constant:
`F̃_{ℓ-1} = (576^n / (n! · (-3456)^d)) · K̂` where `d = deg K_n^{λ,μ}` and
`K̂ = scaleRoots K_n^{λ,μ} (-3456) ∈ ℤ[X]`. -/
theorem kanekoZagierModularPoly_eq_C_mul_scaleRoots (l μ : ℤ) (n : ℕ) :
    kanekoZagierModularPoly l μ n =
      C ((576 : ℚ) ^ n / (n.factorial * (-3456 : ℚ) ^
          (integralJacobi l 3 6 (2 * l + 3 * μ) n).natDegree)) *
        ((integralJacobi l 3 6 (2 * l + 3 * μ) n).scaleRoots (-3456)).map
          (Int.castRingHom ℚ) := by
  rw [kanekoZagierModularPoly_eq_integralJacobi]
  set K := integralJacobi l 3 6 (2 * l + 3 * μ) n with hK
  have hf : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hs : (-3456 : ℚ) ≠ 0 := by norm_num
  have hdeg : (K.map (Int.castRingHom ℚ)).natDegree = K.natDegree :=
    natDegree_map_eq_of_injective (RingHom.injective_int _) K
  by_cases hK0 : K = 0
  · simp [hK0]
  have hsr : ((K.scaleRoots (-3456)).map (Int.castRingHom ℚ)) =
      (K.map (Int.castRingHom ℚ)).scaleRoots (-3456) := by
    rw [map_scaleRoots _ _ _ (by
      rw [eq_intCast, Int.cast_ne_zero]
      exact leadingCoeff_ne_zero.mpr hK0)]
    simp
  apply Polynomial.funext
  intro y
  have key := scaleRoots_eval_mul (K.map (Int.castRingHom ℚ)) (y / (-3456)) (-3456)
  rw [mul_div_cancel₀ _ hs, hdeg] at key
  rw [eval_mul, eval_C, eval_mul, eval_C, eval_comp, eval_mul, eval_C, eval_X, hsr, key]
  field_simp

/-- **§6.4, integrality.** If `ℓ = 12n + 6 + 2λ + 3μ` is prime, every nonzero
coefficient of `Y^a (Y - 1728)^b F̃_{ℓ-1}(Y)` (with `a = (λ+1)/2`, `b = (μ+1)/2`) has
nonnegative `ℓ`-adic valuation. -/
theorem padicValRat_coeff_kanekoZagier_nonneg {l μ : ℤ} (hl : l = 1 ∨ l = -1)
    (hμ : μ = 1 ∨ μ = -1) (n ℓ : ℕ) (hℓ : (ℓ : ℤ) = 12 * n + 6 + 2 * l + 3 * μ)
    (hp : ℓ.Prime) (a b : ℕ) (j : ℕ)
    (hj : (polyX ^ a * (polyX - C (1728 : ℚ)) ^ b * kanekoZagierModularPoly l μ n).coeff j ≠ 0) :
    0 ≤ padicValRat ℓ
      ((polyX ^ a * (polyX - C (1728 : ℚ)) ^ b * kanekoZagierModularPoly l μ n).coeff j) := by
  have : Fact ℓ.Prime := ⟨hp⟩
  set K := integralJacobi l 3 6 (2 * l + 3 * μ) n with hK
  set P : ℤ[X] := polyX ^ a * (polyX - C 1728) ^ b * K.scaleRoots (-3456) with hP
  set q : ℚ := (576 : ℚ) ^ n / (n.factorial * (-3456 : ℚ) ^ K.natDegree) with hq
  have hG : polyX ^ a * (polyX - C (1728 : ℚ)) ^ b * kanekoZagierModularPoly l μ n =
      C q * P.map (Int.castRingHom ℚ) := by
    rw [kanekoZagierModularPoly_eq_C_mul_scaleRoots, hP, Polynomial.map_mul, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C, eq_intCast, Int.cast_ofNat]
    exact mul_left_comm _ _ _
  rw [hG, coeff_C_mul, coeff_map, eq_intCast] at hj ⊢
  have hq0 : q ≠ 0 := left_ne_zero_of_mul hj
  have hc0 : ((P.coeff j : ℤ) : ℚ) ≠ 0 := right_ne_zero_of_mul hj
  rw [padicValRat.mul hq0 hc0, padicValRat.of_int]
  have hint : (0 : ℤ) ≤ padicValInt ℓ (P.coeff j) := Int.natCast_nonneg _
  -- `v_ℓ(q) ≥ 0`: `ℓ` divides neither `n!` nor `3456 = 2^7 3^3`
  have hℓ5 : 5 ≤ ℓ := by
    have h2 := hp.two_le
    rcases hl with rfl | rfl <;> rcases hμ with rfl | rfl <;> omega
  have hfac : padicValRat ℓ (n.factorial : ℚ) = 0 := by
    rw [padicValRat.of_nat]
    have : ¬ ℓ ∣ n.factorial := by
      rw [hp.dvd_factorial]
      rcases hl with rfl | rfl <;> rcases hμ with rfl | rfl <;> omega
    exact_mod_cast padicValNat.eq_zero_of_not_dvd this
  have h3456 : padicValRat ℓ (-3456 : ℚ) = 0 := by
    rw [show (-3456 : ℚ) = -((3456 : ℕ) : ℚ) by norm_num, padicValRat.neg, padicValRat.of_nat]
    have : ¬ ℓ ∣ 3456 := by
      intro hd
      have h3456 : (3456 : ℕ) = 2 ^ 7 * 3 ^ 3 := by norm_num
      rw [h3456] at hd
      rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega
    exact_mod_cast padicValNat.eq_zero_of_not_dvd this
  have h576 : padicValRat ℓ ((576 : ℚ) ^ n) = 0 := by
    rw [padicValRat.pow, show (576 : ℚ) = ((576 : ℕ) : ℚ) by norm_num,
      padicValRat.of_nat]
    have : ¬ ℓ ∣ 576 := by
      intro hd
      have h576 : (576 : ℕ) = 2 ^ 6 * 3 ^ 2 := by norm_num
      rw [h576] at hd
      rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega
    simp [padicValNat.eq_zero_of_not_dvd this]
  have hf0 : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hs0 : (-3456 : ℚ) ^ K.natDegree ≠ 0 := pow_ne_zero _ (by norm_num)
  have hvq : padicValRat ℓ q = 0 := by
    rw [hq, padicValRat.div (pow_ne_zero n (by norm_num : (576 : ℚ) ≠ 0)) (mul_ne_zero hf0 hs0),
      padicValRat.mul hf0 hs0, h576, hfac, padicValRat.pow, h3456]
    simp
  rw [hvq]
  linarith

end ArithmeticOfJacobiPolynomials
