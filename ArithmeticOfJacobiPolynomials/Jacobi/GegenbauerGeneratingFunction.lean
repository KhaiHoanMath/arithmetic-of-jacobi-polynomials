/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.Basic
public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.Binomial
public import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# The generating function of the Gegenbauer polynomials

The manuscript defines `C_j^λ(x)` as the coefficient of `t^j` in `(1 - 2xt + t²)^{-λ}`. The
polynomials `gegenbauerC` are defined by the explicit formula [DLMF, 18.5.10]; this file proves
that the two definitions agree, for every rational `λ`:
`∑_j gegenbauerC λ j · t^j = (1 + u)^{-λ}` with `u = t² - 2xt`, in `ℚ[x][[t]]`, where
`(1 + u)^{-λ}` is the binomial series `∑_k binom(-λ, k) u^k` substituted at `u`
(`gegenbauerC_generatingFunction`).
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset

/-- `binom(-ν, m) = (-1)^m (ν)_m / m!`. -/
theorem ring_choose_neg_eq_ascPochhammer_div (ν : ℚ) (m : ℕ) :
    Ring.choose (-ν) m = (-1) ^ m * (ascPochhammer ℚ m).eval ν / m.factorial := by
  rw [Ring.choose_eq_smul, Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_eq_eval, smul_eq_mul,
    show -ν - (m : ℚ) + 1 = -(ν + m - 1) by ring, ascPochhammer_eval_neg_eq_descPochhammer,
    descPochhammer_eval_eq_ascPochhammer, show ν + m - 1 - m + 1 = ν by ring]
  ring

/-- The power series `t² - 2xt = t (t - 2x)` over `ℚ[x]`, so that `1 + u = 1 - 2xt + t²`. -/
noncomputable def gegenbauerBase : PowerSeries ℚ[X] :=
  PowerSeries.X * (PowerSeries.X - PowerSeries.C (2 * Polynomial.X))

theorem hasSubst_gegenbauerBase : PowerSeries.HasSubst gegenbauerBase :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [gegenbauerBase])

theorem coeff_gegenbauerBase_pow (d n : ℕ) :
    PowerSeries.coeff n (gegenbauerBase ^ d) =
      if d ≤ n then (-(2 * Polynomial.X : ℚ[X])) ^ (d - (n - d)) * ((d.choose (n - d) : ℕ) : ℚ[X])
      else 0 := by
  have hp : (PowerSeries.X - PowerSeries.C (2 * Polynomial.X) : PowerSeries ℚ[X]) ^ d =
      (((Polynomial.X + Polynomial.C (-(2 * Polynomial.X : ℚ[X]))) ^ d : Polynomial ℚ[X]) :
        PowerSeries ℚ[X]) := by
    simp [sub_eq_add_neg]
  rw [gegenbauerBase, mul_pow, PowerSeries.coeff_X_pow_mul', hp]
  split_ifs with h
  · rw [Polynomial.coeff_coe, Polynomial.coeff_X_add_C_pow]
  · rfl

/-- The `k`-th term of the explicit formula equals the `(k+m)`-th term of the binomial series
composed with `u = t² - 2xt`, where `n = 2k + m`. -/
theorem gegenbauer_term (ν : ℚ) (k m : ℕ) :
    C ((-1) ^ k * (ascPochhammer ℚ (k + m)).eval ν / ((k.factorial : ℚ) * (m.factorial : ℚ)) *
        2 ^ m) * Polynomial.X ^ m =
      (Ring.choose (-ν) (k + m) • (1 : ℚ[X])) *
        ((-(2 * Polynomial.X : ℚ[X])) ^ m * (((k + m).choose k : ℕ) : ℚ[X])) := by
  have h1 : (-(2 * Polynomial.X) : ℚ[X]) ^ m = C ((-2 : ℚ) ^ m) * Polynomial.X ^ m := by
    rw [show (-(2 * Polynomial.X) : ℚ[X]) = C (-2) * Polynomial.X by
      rw [map_neg, map_ofNat]; ring, mul_pow, ← C_pow]
  have hc : (((k + m).choose k : ℕ) : ℚ) = ((k + m).factorial : ℚ) /
      ((k.factorial : ℚ) * (m.factorial : ℚ)) := by
    rw [Nat.cast_choose ℚ (Nat.le_add_right k m), Nat.add_sub_cancel_left]
  have hs : ((-1 : ℚ) ^ m) * ((-1) ^ m) = 1 := by rw [← mul_pow]; norm_num
  have hsg : (-1 : ℚ) ^ (k + m) * (-2) ^ m = (-1) ^ k * 2 ^ m := by
    rw [show (-2 : ℚ) = (-1) * 2 by norm_num, mul_pow, pow_add]
    linear_combination ((-1 : ℚ) ^ k * 2 ^ m) * hs
  have hf : ((k + m).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hk : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hm : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  rw [h1, Polynomial.smul_eq_C_mul, mul_one, ← map_natCast (C : ℚ →+* ℚ[X]),
    ring_choose_neg_eq_ascPochhammer_div, hc]
  have hscal : (-1 : ℚ) ^ k * (ascPochhammer ℚ (k + m)).eval ν /
      ((k.factorial : ℚ) * (m.factorial : ℚ)) * 2 ^ m =
      (-1) ^ (k + m) * (ascPochhammer ℚ (k + m)).eval ν / ((k + m).factorial : ℚ) *
        (-2) ^ m * (((k + m).factorial : ℚ) / ((k.factorial : ℚ) * (m.factorial : ℚ))) := by
    field_simp
    linear_combination ((ascPochhammer ℚ (k + m)).eval ν) * hsg.symm
  rw [hscal]
  simp only [map_mul]
  ring

/-- **The generating function of the Gegenbauer polynomials.** For every rational `ν`,
`∑_j C_j^ν(x) t^j = (1 - 2xt + t²)^{-ν}` in `ℚ[x][[t]]`; the right side is the binomial series
`(1 + u)^{-ν} = ∑_k binom(-ν, k) u^k` evaluated at `u = t² - 2xt`. This is the definition of
`C_j^ν` in the manuscript. -/
theorem gegenbauerC_generatingFunction (ν : ℚ) :
    PowerSeries.mk (gegenbauerC ν) =
      PowerSeries.subst gegenbauerBase (PowerSeries.binomialSeries ℚ[X] (-ν)) := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_subst' hasSubst_gegenbauerBase,
    finsum_eq_sum_of_support_subset (s := range (n + 1))]
  · simp only [PowerSeries.binomialSeries_coeff, coeff_gegenbauerBase_pow]
    rw [← Finset.sum_range_reflect _ (n + 1), gegenbauerC_eq]
    have hsub : range (n / 2 + 1) ⊆ range (n + 1) := by
      intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k ≤ n / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      obtain ⟨m, rfl⟩ : ∃ m, n = 2 * k + m := ⟨n - 2 * k, by omega⟩
      have hle : 2 * k + m + 1 - 1 - k ≤ 2 * k + m := by omega
      simp only [hle, ↓reduceIte]
      rw [show 2 * k + m + 1 - 1 - k = k + m by omega,
        show 2 * k + m - (k + m) = k by omega, show k + m - k = m by omega,
        show 2 * k + m - k = k + m by omega, show 2 * k + m - 2 * k = m by omega,
        Polynomial.smul_eq_C_mul, mul_one]
      rw [gegenbauer_term]
      simp [Polynomial.smul_eq_C_mul]
    · intro k hk hk'
      rw [Finset.mem_range] at hk hk'
      have hlt : n - k < n - (n - k) := by omega
      simp [Nat.choose_eq_zero_of_lt hlt]
  · intro d hd
    rw [Function.mem_support] at hd
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    apply hd
    simp [coeff_gegenbauerBase_pow, show ¬ d ≤ n by omega]

end ArithmeticOfJacobiPolynomials
