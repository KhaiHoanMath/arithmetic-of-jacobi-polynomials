/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Applications.FixedFactor
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.NumberTheory.Real.Irrational

/-!
# Vanishing modes on a circular cone (Corollary 6.5)

Section 6.3 of the manuscript. A homogeneous harmonic mode of degree `ℓ` and order `r` vanishes
on the latitude `cos θ = α` exactly when `P_ℓ^{(r)}(α) = 0`; the cone `x^2 + y^2 - 2z^2 = 0`
corresponds to `α = ±1/√3`.

* `coneModes_algebraic`: for algebraic `α ≠ 0` in `(-1,1)` of degree at most `D`, a zero
  `P_ℓ^{(r)}(α) = 0` with `ℓ ≥ L_D` forces `17r > ℓ - 1` (Theorem 1.4, second assertion);
* `coneModes_sqrt_three`: for `α = 1/√3`, `23r > 4(ℓ-1)` for all large `ℓ`
  (Proposition 6.3 for `F = 3x^2 - 1`, `c = 19/8`);
* `coneModes_rational`: for rational `α ≠ 0` in `(-1,1)`, `5r > ℓ - 1` for all `ℓ ≥ L`
  (Corollary 6.4);
* `coneModesStatement_of`: **Corollary 6.5**, the statement
  `ConeModesStatement`.

All are conditional on `JacobiSimpleRealZeros`
([DLMF, §18.2(vi)]) and `DusartThetaBound` ([Dusart10, Theorem 5.2]).
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset Real

/-- A nonzero real zero of `P_{2m+δ+r}^{(r)}` is a zero of `F_{m,r,δ}`. -/
theorem aeval_reducedGegenbauer_eq_zero {m r δ : ℕ} (hδ : δ ≤ 1) {α : ℝ} (hα : α ≠ 0)
    (h : aeval α (derivative^[r] (legendreP (2 * m + δ + r))) = 0) :
    aeval α (reducedGegenbauer m r δ) = 0 := by
  rw [iterate_derivative_legendreP_eq_X_pow_mul m r δ hδ, map_mul, map_mul, map_pow, aeval_X,
    aeval_C] at h
  have hD : ((2 * r - 1).doubleFactorial : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.doubleFactorial_pos _).ne'
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h (pow_ne_zero _ hα)
  · rcases mul_eq_zero.mp h with h | h
    · exact absurd h ((map_ne_zero (algebraMap ℚ ℝ)).mpr hD)
    · exact h

/-- A nonzero rational zero of `P_{2m+δ+r}^{(r)}` is a zero of `F_{m,r,δ}`. -/
theorem eval_reducedGegenbauer_eq_zero {m r δ : ℕ} (hδ : δ ≤ 1) {q : ℚ} (hq : q ≠ 0)
    (h : (derivative^[r] (legendreP (2 * m + δ + r))).eval q = 0) :
    (reducedGegenbauer m r δ).eval q = 0 := by
  rw [iterate_derivative_legendreP_eq_X_pow_mul m r δ hδ, eval_mul, eval_mul, eval_pow, eval_X,
    eval_C] at h
  have hD : ((2 * r - 1).doubleFactorial : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.doubleFactorial_pos _).ne'
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h (pow_ne_zero _ hq)
  · rcases mul_eq_zero.mp h with h | h
    · exact absurd h hD
    · exact h

/-- **Corollary 6.5, first assertion.** For every `D ≥ 1` there is `L_D` such that for every
nonzero real algebraic `α ∈ (-1,1)` of degree at most `D`, `ℓ ≥ L_D`, `r ≤ ℓ` and
`P_ℓ^{(r)}(α) = 0` imply `17r > ℓ - 1`. -/
theorem coneModes_algebraic (hZ : JacobiSimpleRealZeros)
    (hD : DusartThetaBound) (D : ℕ) :
    ∃ L : ℕ, ∀ α : ℝ, α ≠ 0 → -1 < α → α < 1 → IsAlgebraic ℚ α →
      (minpoly ℚ α).natDegree ≤ D → ∀ ℓ r : ℕ, L ≤ ℓ → r ≤ ℓ →
      aeval α (derivative^[r] (legendreP ℓ)) = 0 → ℓ - 1 < 17 * r := by
  obtain ⟨M₀, hM₀⟩ :=
    irreducible_reducedGegenbauer_of_eight_mul_le hZ (dusartThetaBound_sum hD)
  refine ⟨3 * (M₀ + D) + 6, fun α hα0 _ _ _ hdeg ℓ r hL hr h => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨m, δ, hδ, rfl⟩ : ∃ m δ : ℕ, δ ≤ 1 ∧ ℓ = 2 * m + δ + r :=
    ⟨(ℓ - r) / 2, (ℓ - r) % 2, by omega, by omega⟩
  have hm8 : 8 * r ≤ m := by omega
  have hmM : M₀ + D + 1 ≤ m := by omega
  have hirr := hM₀ m r δ hδ (by omega) (max_le hm8 (by omega))
  have hR := aeval_reducedGegenbauer_eq_zero hδ hα0 h
  have hmin := minpoly.eq_of_irreducible hirr hR
  have hR0 : reducedGegenbauer m r δ ≠ 0 := hirr.ne_zero
  rw [← hmin, natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr hR0)),
    natDegree_reducedGegenbauer m r δ hδ] at hdeg
  omega

/-- `3x^2 - 1` is the primitive integral minimal polynomial of `1/√3`; over `ℚ`,
`X^2 - 1/3` is irreducible since `√3` is irrational. -/
theorem irreducible_X_sq_sub_one_third : Irreducible (polyX ^ 2 - C (1 / 3 : ℚ)) := by
  refine X_pow_sub_C_irreducible_of_prime Nat.prime_two fun b hb => ?_
  have h3 : Irrational (√3 : ℝ) := by
    have := Nat.prime_three.irrational_sqrt
    simpa using this
  refine h3.ne_rat |3 * b| ?_
  have hb' : (b : ℝ) ^ 2 = 1 / 3 := by
    have := congrArg (Rat.cast : ℚ → ℝ) hb
    push_cast at this
    exact this
  rw [Rat.cast_abs, ← Real.sqrt_sq_eq_abs]
  congr 1
  push_cast
  linear_combination -9 * hb'

/-- **Corollary 6.5, second assertion** (the cone `x^2 + y^2 - 2z^2 = 0`). For all
sufficiently large `ℓ`, `r ≤ ℓ` and `P_ℓ^{(r)}(1/√3) = 0` imply `23r > 4(ℓ - 1)`. -/
theorem coneModes_sqrt_three (hZ : JacobiSimpleRealZeros)
    (hD : DusartThetaBound) :
    ∃ L : ℕ, ∀ ℓ r : ℕ, L ≤ ℓ → r ≤ ℓ →
      aeval (1 / Real.sqrt 3) (derivative^[r] (legendreP ℓ)) = 0 → 4 * (ℓ - 1) < 23 * r := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 1 / Real.sqrt 3 := ⟨_, rfl⟩
  have hs3 : 1 < Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have ha0 : 0 < a := by rw [ha]; positivity
  have ha1 : a < 1 := by rw [ha, div_lt_one (by linarith)]; exact hs3
  have ha2 : a ^ 2 = 1 / 3 := by rw [ha, div_pow, one_pow, Real.sq_sqrt (by norm_num)]
  -- the factor `F = 3x^2 - 1`
  obtain ⟨F, hF⟩ : ∃ F : ℤ[X], F = C 3 * polyX ^ 2 - 1 := ⟨_, rfl⟩
  have hFdeg : F.natDegree = 2 := by rw [hF]; compute_degree!
  have hFlc : F.leadingCoeff = 3 := by
    rw [Polynomial.leadingCoeff, hFdeg, hF, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_one]
    norm_num
  have hc0 : F.coeff 0 = -1 := by
    rw [hF, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_one]; norm_num
  have hFprim : F.IsPrimitive := by
    refine isPrimitive_iff_isUnit_of_C_dvd.mpr fun x hx => isUnit_of_dvd_one ?_
    have := (C_dvd_iff_dvd_coeff _ _).mp hx 0
    rwa [hc0, dvd_neg] at this
  have hF0 : F.eval 0 ≠ 0 := by rw [hF]; simp
  have hFmapR : F.map (Int.castRingHom ℝ) = C 3 * ((polyX - C a) * (polyX - C (-a))) := by
    have hX : (polyX - C a) * (polyX - C (-a)) = polyX ^ 2 - C (a ^ 2) := by
      rw [C_neg, map_pow]; ring
    rw [hX, mul_sub, ← C_mul, ha2, hF]
    norm_num
    exact (map_ofNat C 3).symm
  have hroots_eq : (F.map (Int.castRingHom ℝ)).roots = a ::ₘ {-a} := by
    rw [hFmapR, roots_C_mul _ (by norm_num),
      roots_mul (mul_ne_zero (X_sub_C_ne_zero a) (X_sub_C_ne_zero (-a))), roots_X_sub_C,
      roots_X_sub_C, Multiset.singleton_add]
  have hnd : (F.map (Int.castRingHom ℝ)).roots.Nodup := by
    rw [hroots_eq]
    refine Multiset.nodup_cons.mpr ⟨fun hmem => ?_, Multiset.nodup_singleton _⟩
    rw [Multiset.mem_singleton] at hmem
    linarith
  have hcard : (F.map (Int.castRingHom ℝ)).roots.card = F.natDegree := by
    rw [hroots_eq, Multiset.card_cons, Multiset.card_singleton, hFdeg]
  have hroots : ∀ x ∈ (F.map (Int.castRingHom ℝ)).roots, -1 < x ∧ x < 1 := by
    rw [hroots_eq]
    intro x hx
    rcases Multiset.mem_cons.mp hx with rfl | hx
    · exact ⟨by linarith, ha1⟩
    · rw [Multiset.mem_singleton] at hx
      subst hx
      exact ⟨by linarith, by linarith⟩
  -- `c_F ≤ 1` and `β(F) ≥ log 6`
  have hs1 : shiftedTwoAdicOrder F ≤ 1 := by
    have e1 : F.eval 1 = 2 := by rw [hF]; norm_num
    have h2 := two_pow_dvd_eval_one F
    rw [e1] at h2
    by_contra hs
    push Not at hs
    have h4 : (2 : ℤ) ^ 2 ∣ 2 := (pow_dvd_pow 2 hs).trans h2
    norm_num at h4
  have hβ : log 6 ≤ fixedFactorExponent F := by
    rw [fixedFactorExponent_eq, hFdeg, hFlc]
    have hs : (2 : ℝ) ^ shiftedTwoAdicOrder F ≤ 2 :=
      calc (2 : ℝ) ^ shiftedTwoAdicOrder F ≤ 2 ^ 1 := pow_le_pow_right₀ (by norm_num) hs1
        _ = 2 := pow_one 2
    have hz : (3 / 2 : ℝ) ≤ ((3 : ℤ) : ℝ) / 2 ^ shiftedTwoAdicOrder F := by
      rw [le_div_iff₀ (by positivity)]; push_cast; linarith
    have hlog := Real.log_le_log (by norm_num) hz
    have h6 : log 6 = log 4 + log (3 / 2) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
    have e : (2 : ℝ) / ((2 : ℕ) : ℝ) * log (((3 : ℤ) : ℝ) / 2 ^ shiftedTwoAdicOrder F) =
        log (((3 : ℤ) : ℝ) / 2 ^ shiftedTwoAdicOrder F) := by norm_num
    rw [e]
    linarith
  have hgap : asymptoticGapFunction (19 / 8) < 19 / 8 * (fixedFactorExponent F - 1) := by
    linarith [margin_asymptoticGapFunction_nineteen_eighths]
  obtain ⟨M, hM⟩ := not_dvd_reducedGegenbauer_of_fixedFactor hZ hD hFprim (by omega)
    (by rw [hFlc]; norm_num) hnd hcard hroots hF0 (by norm_num) hgap
  -- `F ∣ F_{m,r,δ}` from a zero at `1/√3`
  have hFQ : F.map (Int.castRingHom ℚ) = C 3 * (polyX ^ 2 - C (1 / 3 : ℚ)) := by
    rw [hF, mul_sub, ← C_mul]
    norm_num
    exact (map_ofNat C 3).symm
  have hpa : aeval a (polyX ^ 2 - C (1 / 3 : ℚ)) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, ha2, eq_ratCast]
    norm_num
  have hmin := minpoly.eq_of_irreducible_of_monic irreducible_X_sq_sub_one_third hpa
    (monic_X_pow_sub_C _ two_ne_zero)
  refine ⟨3 * M + 3, fun ℓ r hL hr h => ?_⟩
  rw [← ha] at h
  by_contra hcon
  push Not at hcon
  obtain ⟨m, δ, hδ, rfl⟩ : ∃ m δ : ℕ, δ ≤ 1 ∧ ℓ = 2 * m + δ + r :=
    ⟨(ℓ - r) / 2, (ℓ - r) % 2, by omega, by omega⟩
  have h19 : 19 * r ≤ 8 * m := by omega
  have hmM : M ≤ m := by omega
  have hcr : (19 / 8 : ℝ) * r ≤ m := by
    have : ((19 * r : ℕ) : ℝ) ≤ ((8 * m : ℕ) : ℝ) := by exact_mod_cast h19
    push_cast at this
    linarith
  have hR := aeval_reducedGegenbauer_eq_zero hδ ha0.ne' h
  have hdvd0 : polyX ^ 2 - C (1 / 3 : ℚ) ∣ reducedGegenbauer m r δ := by
    rw [hmin]; exact minpoly.dvd ℚ a hR
  apply hM m r δ hδ hmM hcr
  rw [hFQ]
  exact (isUnit_C.mpr (IsUnit.mk0 _ (by norm_num))).mul_left_dvd.mpr hdvd0

/-- **Corollary 6.5, third assertion.** There is an absolute `L` such that for nonzero rational
`α ∈ (-1,1)`, `ℓ ≥ L`, `r ≤ ℓ` and `P_ℓ^{(r)}(α) = 0` imply `5r > ℓ - 1`. -/
theorem coneModes_rational (hZ : JacobiSimpleRealZeros)
    (hD : DusartThetaBound) :
    ∃ L : ℕ, ∀ α : ℚ, α ≠ 0 → |α| < 1 → ∀ ℓ r : ℕ, L ≤ ℓ → r ≤ ℓ →
      (derivative^[r] (legendreP ℓ)).eval α = 0 → ℓ - 1 < 5 * r := by
  obtain ⟨M₁, hM₁⟩ := noRationalRootsStatement_of hZ hD
  refine ⟨3 * M₁ + 3, fun α hα0 _ ℓ r hL hr h => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨m, δ, hδ, rfl⟩ : ∃ m δ : ℕ, δ ≤ 1 ∧ ℓ = 2 * m + δ + r :=
    ⟨(ℓ - r) / 2, (ℓ - r) % 2, by omega, by omega⟩
  exact hM₁ m r δ (by omega) (by omega) hδ α (eval_reducedGegenbauer_eq_zero hδ hα0 h)

/-- **Corollary 6.5.** All three assertions, `ConeModesStatement`. Conditional
on `JacobiSimpleRealZeros`
([DLMF, §18.2(vi)]) and `DusartThetaBound` ([Dusart10, Theorem 5.2]). -/
theorem coneModesStatement_of (hZ : JacobiSimpleRealZeros)
    (hD : DusartThetaBound) : ConeModesStatement :=
  ⟨fun D _ => coneModes_algebraic hZ hD D, coneModes_sqrt_three hZ hD,
    coneModes_rational hZ hD⟩

end ArithmeticOfJacobiPolynomials
