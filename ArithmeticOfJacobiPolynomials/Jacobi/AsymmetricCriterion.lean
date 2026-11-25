/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.SymmetricCriterion
public import ArithmeticOfJacobiPolynomials.Jacobi.CentralValue
public import ArithmeticOfJacobiPolynomials.Jacobi.Reduction

/-!
# The irreducibility criterion for unequal parameters (Theorem 3.1)

Fix integers `a > b ≥ 0`, put `s = a + b`, `n = 2m + δ` (`δ ∈ {0,1}`), `M = m + s + 2`,
`S = 2n + s + 1`, `T = ∏_{j=1}^{s} (n+j)`, `B = binom(n+a, a)`, and let `A_δ, D_δ` be the
polynomials of Lemma 3.2 (`centralA`, `centralD`). Theorem 3.1 of the manuscript
(Theorem 3.1) states that for `m ≥ 2s + 10` with `A_δ(m) ≠ 0`, the inequality (3.5)
implies that `P_n^{(a,b)}` is irreducible over `ℚ`.

This file proves the comparison argument of the manuscript for a given derivative lower bound
`|f'(α)| > γ` at the roots (the energy estimate of the manuscript, with
`γ = c_{a,b} √m / D_δ(m)`, is proved separately):
* the odd local bound: `v_p(R) ≤ d (⌊log_p S⌋ + v_p(T))` (Lemma 2.4, coarse form, applied to
  `F(2X+1), G(2X+1)`);
* the prime support (3.8): `p > M`, `p ∤ T A_δ(m)` imply `p ∤ R`;
* (3.10): `log 𝓡 / d ≤ Ψ_M(S) + 2 log T + log |A_δ(m)|`;
* (3.11) through Lemma 2.6, with `b_h = B` and `D_2 = ⌊log_2 S⌋ + v_2(T)`.

Main results:
* `ArithmeticOfJacobiPolynomials.irreducible_jacobiP_of_criterion_of_gamma`.
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset Real

/-! ### A generic odd local bound -/

open Classical in
/-- **Odd local bound.** Let `F, G ∈ ℤ[X]` be primitive with `R = Res(F,G) ≠ 0` and
`(F G)(2X+1) ∣ Q = P_n^{(a,b)}(2X+1)/binom(n+a,a)` over `ℚ`. If every root of `Q` in
`PadicAlgCl p` has projective row sum at most `D`, then `v_p(R) ≤ deg F · D` for odd `p`. -/
theorem padicValInt_resultant_le_of_comp_dvd (a b : ℕ) {n : ℕ} (hn : 1 ≤ n) {F G : ℤ[X]}
    (hF : F.IsPrimitive) (hG : G.IsPrimitive) (hR : resultant F G ≠ 0)
    (hPQ : ((F * G).comp (2 * polyX + 1)).map (Int.castRingHom ℚ) ∣ integralWeightQ a b n)
    (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) {D : ℝ}
    (hD : ∀ z ∈ ((integralWeightQ a b n).map (algebraMap ℚ (PadicAlgCl p))).roots,
      ∑ w ∈ ((integralWeightQ a b n).map (algebraMap ℚ (PadicAlgCl p))).roots.toFinset.erase z,
        projDist p z w ≤ D) :
    (padicValInt p (resultant F G) : ℝ) ≤ F.natDegree * D := by
  obtain ⟨jF, hjF⟩ := exists_not_dvd_coeff_comp hp.out hp2 hF
  obtain ⟨jG, hjG⟩ := exists_not_dvd_coeff_comp hp.out hp2 hG
  have hres : resultant (F.comp (2 * polyX + 1)) (G.comp (2 * polyX + 1)) =
      2 ^ (F.natDegree * G.natDegree) * resultant F G := resultant_comp_two_mul_X_add_one F G
  have hR' : resultant (F.comp (2 * polyX + 1)) (G.comp (2 * polyX + 1)) ≠ 0 := by
    rw [hres]; exact mul_ne_zero (by positivity) hR
  have hval : padicValInt p (resultant (F.comp (2 * polyX + 1)) (G.comp (2 * polyX + 1))) =
      padicValInt p (resultant F G) := by
    rw [hres, padicValInt.mul (by positivity) hR]
    have : padicValInt p ((2 : ℤ) ^ (F.natDegree * G.natDegree)) = 0 := by
      rw [padicValInt, Int.natAbs_pow]
      exact padicValNat_two_pow_eq_zero hp2 _
    rw [this, zero_add]
  have hLdeg : (2 * polyX + 1 : ℤ[X]).natDegree = 1 := by
    rw [show (2 * polyX + 1 : ℤ[X]) = C 2 * polyX + C 1 by simp]
    exact natDegree_linear (by norm_num)
  have hA := isPrimitive_map_padicInt_of_not_dvd hjF
  have hB := isPrimitive_map_padicInt_of_not_dvd hjG
  have hAdeg : ((F.comp (2 * polyX + 1)).map (Int.castRingHom ℤ_[p])).natDegree = F.natDegree := by
    rw [natDegree_map_eq_of_injective Int.cast_injective, natDegree_comp, hLdeg, mul_one]
  have hdvd : ((F.comp (2 * polyX + 1)).map (Int.castRingHom ℤ_[p]) *
      (G.comp (2 * polyX + 1)).map (Int.castRingHom ℤ_[p])).map (algebraMap ℤ_[p] (PadicAlgCl p)) ∣
      (integralWeightQ a b n).map (algebraMap ℚ (PadicAlgCl p)) := by
    have e : ((F.comp (2 * polyX + 1)).map (Int.castRingHom ℤ_[p]) *
        (G.comp (2 * polyX + 1)).map (Int.castRingHom ℤ_[p])).map (algebraMap ℤ_[p] (PadicAlgCl
          p)) =
        (((F * G).comp (2 * polyX + 1)).map (Int.castRingHom ℚ)).map
          (algebraMap ℚ (PadicAlgCl p)) := by
      rw [← Polynomial.map_mul, map_padicInt_map_eq, Polynomial.map_map, mul_comp,
        show (algebraMap ℚ (PadicAlgCl p)).comp (Int.castRingHom ℚ) =
          Int.castRingHom (PadicAlgCl p) from RingHom.ext_int _ _]
    rw [e]
    exact Polynomial.map_dvd _ hPQ
  have key := integralWeight_resultant_le a b hn hA hB hdvd hD
  rw [padicVal_resultant_map_intCast hR', hval, hAdeg] at key
  exact key

/-! ### Properties of `P_n^{(a,b)}` -/

section Jacobi

variable (a b n : ℕ)

theorem jacobiP_nat_eval_one :
    (jacobiP a b n).eval 1 = ((n + a).choose a : ℚ) := by
  rw [jacobiP_eq_C_mul_map_jacobiNum, eval_mul, eval_C, eval_map, eval₂_at_one,
    eval_one_jacobiNum, Nat.choose_symm_add, eq_intCast]
  push_cast
  rw [one_div_pow]
  field_simp

theorem jacobiP_nat_ne_zero : jacobiP a b n ≠ 0 := by
  intro h
  have := jacobiP_nat_eval_one a b n
  rw [h, eval_zero] at this
  exact absurd this.symm (by exact_mod_cast (Nat.choose_pos (by omega)).ne')

theorem natDegree_jacobiP_nat : (jacobiP a b n).natDegree = n := by
  rw [jacobiP_eq_C_mul_map_jacobiNum, natDegree_C_mul (by positivity),
    natDegree_map_eq_of_injective Int.cast_injective, natDegree_jacobiNum]

theorem leadingCoeff_jacobiP_nat_pos : 0 < (jacobiP a b n).leadingCoeff := by
  rw [jacobiP_eq_C_mul_map_jacobiNum, leadingCoeff_mul, leadingCoeff_C,
    leadingCoeff_map_of_injective Int.cast_injective,
    leadingCoeff, natDegree_jacobiNum, coeff_jacobiNum_self, eq_intCast]
  have : (0 : ℚ) < ((2 * n + a + b).choose n : ℤ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  positivity

theorem map_jacobiNum_eq_C_mul :
    (jacobiNum a b n).map (Int.castRingHom ℚ) = C ((2 : ℚ) ^ n) * jacobiP a b n := by
  rw [jacobiP_eq_C_mul_map_jacobiNum, ← mul_assoc, ← C_mul, ← mul_pow]
  norm_num

/-- `P_n^{(a,b)}(2X+1) = binom(n+a,a) Q`. -/
theorem jacobiP_comp_eq_C_mul_integralWeightQ :
    (jacobiP a b n).comp (2 * polyX + 1) = C ((n + a).choose a : ℚ) * integralWeightQ a b n := by
  have hB : ((n + a).choose a : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  rw [integralWeightQ_eq, ← mul_assoc, ← C_mul, mul_one_div_cancel hB, C_1, one_mul]

theorem jacobiP_comp_dvd_integralWeightQ :
    (jacobiP a b n).comp (2 * polyX + 1) ∣ integralWeightQ a b n := by
  refine ⟨C (1 / ((n + a).choose a : ℚ)), ?_⟩
  rw [integralWeightQ_eq, mul_comm]

end Jacobi

/-! ### The upper bound (3.10) -/

/-- For `N ≥ 1`, `∑_{p ∣ N} log p ≤ log N`. -/
theorem sum_log_primeFactors_le {N : ℕ} (hN : N ≠ 0) :
    ∑ p ∈ N.primeFactors, log (p : ℝ) ≤ log N := by
  rw [← Real.log_prod (fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)]
  have h := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) (Nat.prod_primeFactors_dvd N)
  have hpos : (0 : ℝ) < ∏ p ∈ N.primeFactors, (p : ℝ) := by
    refine prod_pos fun p hp => ?_
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  refine Real.log_le_log hpos ?_
  rw [← Nat.cast_prod]
  exact_mod_cast h

/-- `log T = ∑_p v_p(T) log p`, over any finite set of primes containing the prime factors. -/
theorem log_eq_sum_factorization_of_subset {T : ℕ} {P : Finset ℕ}
    (hP : T.primeFactors ⊆ P) :
    log (T : ℝ) = ∑ p ∈ P, (T.factorization p : ℝ) * log p := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
  refine Finset.sum_subset hP fun p _ hp => ?_
  have h0 : T.factorization p = 0 := by
    by_contra h
    exact hp (Nat.support_factorization T ▸ Finsupp.mem_support_iff.mpr h)
  rw [h0, Nat.cast_zero, zero_mul]

/-! ### Theorem 3.1 for a given derivative bound -/

open Classical in
/-- **Theorem 3.1, comparison step.** Let `a > b ≥ 0`, `s = a+b`,
`n = 2m+δ`, `m ≥ 2s+10`, `A_δ(m) ≠ 0`, and suppose `|f'(α)| > γ > 0` at every root
`α ∈ (-1,1)` of `f = P_n^{(a,b)}`. With `M = m+s+2`, `S = 2n+s+1`, `T = ∏_{j=1}^{s}(n+j)` and
`B = binom(n+a, a)`, if
`n log 2 > (M + √S) log 3 + 3 log T + log |A_δ(m)| + log(8 (m+1) S B / γ)`, then `f` is
irreducible over `ℚ`. Conditional on `HansonLcmBound` and
`JacobiSimpleRealZeros`. -/
theorem irreducible_jacobiP_of_criterion_of_gamma (hH : HansonLcmBound)
     (hZ : JacobiSimpleRealZeros) {a b m δ : ℕ} (hab : b < a)
    (hδ : δ ≤ 1) (hm : 2 * (a + b) + 10 ≤ m) (hA : (centralA a b δ).eval (m : ℤ) ≠ 0)
    {γ : ℝ} (hγ : 0 < γ)
    (hγ' : ∀ α : ℝ, α ∈ Set.Ioo (-1 : ℝ) 1 → aeval α (jacobiP a b (2 * m + δ)) = 0 →
      γ < |aeval α (derivative (jacobiP a b (2 * m + δ)))|)
    (hcrit : (((m + (a + b) + 2 : ℕ) : ℝ) + √((2 * (2 * m + δ) + (a + b) + 1 : ℕ) : ℝ)) * log 3 +
        3 * log ((∏ j ∈ Icc 1 (a + b), (2 * m + δ + j) : ℕ) : ℝ) +
        log |(((centralA a b δ).eval (m : ℤ) : ℤ) : ℝ)| +
        log (8 * ((m : ℝ) + 1) * ((2 * (2 * m + δ) + (a + b) + 1 : ℕ) : ℝ) *
          ((2 * m + δ + a).choose a : ℝ) / γ) <
      ((2 * m + δ : ℕ) : ℝ) * log 2) :
    Irreducible (jacobiP a b (2 * m + δ)) := by
  have hm1 : 1 ≤ m := by omega
  have hn1 : 1 ≤ 2 * m + δ := by omega
  have hf0 := jacobiP_nat_ne_zero a b (2 * m + δ)
  have hdeg := natDegree_jacobiP_nat a b (2 * m + δ)
  have hlc := leadingCoeff_jacobiP_nat_pos a b (2 * m + δ)
  have ha1 : (-1 : ℚ) < a := by have := (Nat.cast_nonneg a : (0 : ℚ) ≤ a); linarith
  have hb1' : (-1 : ℚ) < b := by have := (Nat.cast_nonneg b : (0 : ℚ) ≤ b); linarith
  obtain ⟨hnd, hcard, hint⟩ := hZ.rat a b ha1 hb1' (2 * m + δ)
  have hfR0 : (jacobiP a b (2 * m + δ)).map (algebraMap ℚ ℝ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective).mpr hf0
  -- the central value is nonzero
  have hcen : (jacobiP a b (2 * m + δ)).eval 0 ≠ 0 := by
    intro h0
    have h := one_div_le_abs_jacobiP_eval_zero a b m δ hab hδ hm1 hA
    rw [h0, Rat.cast_zero, abs_zero] at h
    have hD : (0 : ℝ) < (((centralD a b δ).eval (m : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast centralD_eval_pos a b δ m
    have : (0 : ℝ) < 1 / (2 * Real.sqrt m * (((centralD a b δ).eval (m : ℤ) : ℤ) : ℝ)) := by
      have : (0 : ℝ) < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm1)
      positivity
    linarith
  have hroots : ∀ x ∈ ((jacobiP a b (2 * m + δ)).map (algebraMap ℚ ℝ)).roots,
      x ≠ 0 ∧ -1 < x ∧ x < 1 := by
    intro x hx
    refine ⟨?_, hint x hx⟩
    rintro rfl
    have hr : ((jacobiP a b (2 * m + δ)).map (algebraMap ℚ ℝ)).eval 0 = 0 :=
      (mem_roots hfR0).mp hx
    rw [← coeff_zero_eq_eval_zero, coeff_map, map_eq_zero, coeff_zero_eq_eval_zero] at hr
    exact hcen hr
  have hsepf : (jacobiP a b (2 * m + δ)).Separable := by
    rw [← separable_map (algebraMap ℚ ℝ)]
    refine (nodup_roots_iff_of_splits hfR0 ?_).mp hnd
    rw [splits_iff_card_roots, hcard, natDegree_map, hdeg]
  refine irreducible_of_forall_primitive_factorization (by omega) hlc (by positivity)
    (map_jacobiNum_eq_C_mul a b (2 * m + δ)) ?_
  intro κ H F G hκ hHmap hHprim hHFG hFprim hGprim hFlc hGlc hd hde
  have hF0 : F ≠ 0 := hFprim.ne_zero
  have hG0 : G ≠ 0 := hGprim.ne_zero
  have hHdeg : H.natDegree = 2 * m + δ := by
    rw [← natDegree_map_eq_of_injective (f := Int.castRingHom ℚ) Int.cast_injective H, hHmap,
      natDegree_C_mul hκ.ne', hdeg]
  have hdeN : F.natDegree + G.natDegree = 2 * m + δ := by
    rw [← hHdeg, hHFG, natDegree_mul hF0 hG0]
  have hdm : F.natDegree ≤ m := by omega
  have hFGmap : (F * G).map (Int.castRingHom ℚ) = C κ * jacobiP a b (2 * m + δ) := by
    rw [← hHFG]; exact hHmap
  have hR : resultant F G ≠ 0 := by
    have hcop : IsCoprime (F.map (Int.castRingHom ℚ)) (G.map (Int.castRingHom ℚ)) := by
      apply Separable.isCoprime
      rw [← Polynomial.map_mul, hFGmap]
      exact Separable.unit_mul (isUnit_C.mpr (IsUnit.mk0 _ hκ.ne')) hsepf
    intro h0
    apply resultant_ne_zero _ _ hcop
    rw [← intCast_resultant, h0, Int.cast_zero]
  have hFGR : (F * G).map (Int.castRingHom ℝ) =
      C (κ : ℝ) * (jacobiP a b (2 * m + δ)).map (algebraMap ℚ ℝ) := by
    have : (F * G).map (Int.castRingHom ℝ) =
        ((F * G).map (Int.castRingHom ℚ)).map (algebraMap ℚ ℝ) := by
      rw [Polynomial.map_map, show (algebraMap ℚ ℝ).comp (Int.castRingHom ℚ) =
        Int.castRingHom ℝ from RingHom.ext_int _ _]
    rw [this, hFGmap, Polynomial.map_mul, Polynomial.map_C, eq_ratCast]
  have hκR : (κ : ℝ) ≠ 0 := by exact_mod_cast hκ.ne'
  obtain ⟨α, hαinj, hαF⟩ := exists_injective_roots_of_mul (mul_ne_zero hF0 hG0)
    (by rw [hFGR, roots_C_mul _ hκR]; exact hnd)
    (by rw [hFGR, roots_C_mul _ hκR, hcard, natDegree_mul hF0 hG0, hdeN])
  -- Lemma 2.6
  have hbpos : 0 < (2 * m + δ + a).choose a := Nat.choose_pos (by omega)
  have hb1 := jacobiP_nat_eval_one a b (2 * m + δ)
  have hγ'' : ∀ x ∈ ((jacobiP a b (2 * m + δ)).map (algebraMap ℚ ℝ)).roots,
      γ < |(derivative ((jacobiP a b (2 * m + δ)).map (algebraMap ℚ ℝ))).eval x| := by
    intro x hx
    obtain ⟨-, hx1, hx2⟩ := hroots x hx
    have hroot : aeval x (jacobiP a b (2 * m + δ)) = 0 := by
      rw [aeval_def, eval₂_eq_eval_map]
      exact (mem_roots hfR0).mp hx
    rw [derivative_map, eval_map, ← aeval_def]
    exact hγ' x ⟨hx1, hx2⟩ hroot
  have hQroots : ∀ (p : ℕ) [Fact p.Prime],
      (((jacobiP a b (2 * m + δ)).comp (2 * polyX + 1)).map (algebraMap ℚ (PadicAlgCl p))).roots =
        ((integralWeightQ a b (2 * m + δ)).map (algebraMap ℚ (PadicAlgCl p))).roots := by
    intro p _
    have hB : ((2 * m + δ + a).choose a : ℚ) ≠ 0 := by exact_mod_cast hbpos.ne'
    rw [jacobiP_comp_eq_C_mul_integralWeightQ, Polynomial.map_mul, Polynomial.map_C]
    exact roots_C_mul _ ((_root_.map_ne_zero _).mpr hB)
  have hrow : ∀ z ∈ (((jacobiP a b (2 * m + δ)).comp (2 * polyX + 1)).map
      (algebraMap ℚ (PadicAlgCl 2))).roots,
      ∑ w ∈ (((jacobiP a b (2 * m + δ)).comp (2 * polyX + 1)).map
        (algebraMap ℚ (PadicAlgCl 2))).roots.toFinset.erase z, projDist 2 z w ≤
        (Nat.log 2 (2 * (2 * m + δ) + a + b + 1) : ℝ) +
          padicValNat 2 (∏ j ∈ Icc 1 (a + b), (2 * m + δ + j)) := by
    intro z hz
    rw [hQroots 2] at hz ⊢
    exact integralWeight_row_bound_coarse a b hn1 hz
  have hlow := (realResultant_lowerBound (h := jacobiP a b (2 * m + δ)) (N := 2 * m + δ)
    ⟨2 * m + δ, jacobiNum a b (2 * m + δ), map_jacobiNum_eq_C_mul a b (2 * m + δ)⟩ hdeg hlc
    hcard hnd hroots hbpos (by rw [hb1]) hγ hγ'' hrow hκ hHmap hHprim hHFG hFprim hGprim hFlc
    hGlc rfl rfl hd hde hdeN hαinj hαF).2.2
  -- notation for the upper bound
  set M := m + (a + b) + 2 with hM
  set S := 2 * (2 * m + δ) + (a + b) + 1 with hS
  set T := ∏ j ∈ Icc 1 (a + b), (2 * m + δ + j) with hT
  set Aint := (centralA a b δ).eval (m : ℤ) with hAint
  have hT0 : T ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j hj => by omega
  have hA0 : Aint.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hA
  set Nabs := T * Aint.natAbs with hNabs
  have hNabs0 : Nabs ≠ 0 := mul_ne_zero hT0 hA0
  set N0 := M + Nabs with hN0
  set P := (range (N0 + 1)).filter Nat.Prime with hP
  have hpsupp : ∀ p : ℕ, p.Prime → p ≠ 2 → M < p → (p : ℤ) ∣ resultant F G → p ∣ Nabs := by
    intro p hp hp2 hpM hdvd
    have := Fact.mk hp
    by_contra hcon
    have hT' : ¬ p ∣ T := fun h => hcon (dvd_mul_of_dvd_left h _)
    have hA' : ¬ (p : ℤ) ∣ Aint := fun h => hcon (dvd_mul_of_dvd_right (Int.natCast_dvd.mp h) _)
    exact asymmetric_prime_support hab hδ hm (fun k => jacobiP_ode a b k) hFprim hGprim hFGmap
      hp2 hpM hT' hA' hdvd
  have hsupp : ∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℤ) ∣ resultant F G → p ≤ N0 := by
    intro p hp hp2 hdvd
    by_cases hpM : p ≤ M
    · omega
    · have := Nat.le_of_dvd (Nat.pos_of_ne_zero hNabs0) (hpsupp p hp hp2 (by omega) hdvd)
      omega
  have hPQ : ((F * G).comp (2 * polyX + 1)).map (Int.castRingHom ℚ) ∣
      integralWeightQ a b (2 * m + δ) := by
    have hL : (2 * polyX + 1 : ℤ[X]).map (Int.castRingHom ℚ) = 2 * polyX + 1 := by simp
    rw [Polynomial.map_comp, hFGmap, hL, mul_comp, C_comp]
    refine dvd_trans ?_ (jacobiP_comp_dvd_integralWeightQ a b (2 * m + δ))
    exact ⟨C κ⁻¹, by rw [mul_comm (C κ), mul_assoc, ← C_mul, mul_inv_cancel₀ hκ.ne', C_1,
      mul_one]⟩
  have hbase : ∀ p : ℕ, p.Prime → p ≠ 2 → (padicValInt p (resultant F G) : ℝ) ≤
      F.natDegree * ((Nat.log p S : ℝ) + (T.factorization p : ℝ)) := by
    intro p hp hp2
    have := Fact.mk hp
    have h := padicValInt_resultant_le_of_comp_dvd a b hn1 hFprim hGprim hR hPQ p hp2
      (fun z hz => integralWeight_row_bound_coarse (p := p) a b hn1 hz)
    rw [Nat.factorization_def T hp]
    rw [show 2 * (2 * m + δ) + a + b + 1 = S by rw [hS]; ring] at h
    exact h
  set E : ℕ → ℝ := fun p => (F.natDegree : ℝ) * ((if p ≤ M then (Nat.log p S : ℝ) else 0) +
    (T.factorization p : ℝ) + (if M < p ∧ p ∣ Nabs then 1 else 0)) with hE
  have hS_lt : ∀ p : ℕ, M < p → S < p ^ 2 := by
    intro p hp
    have : M * M < p * p := Nat.mul_self_lt_mul_self hp
    have : S < M * M := by rw [hS, hM]; nlinarith
    rw [sq]; omega
  have hEp : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≤ N0 → (padicValInt p (resultant F G) : ℝ) ≤ E p := by
    intro p hp hp2 _
    have hb := hbase p hp hp2
    have hd0 : (0 : ℝ) ≤ F.natDegree := Nat.cast_nonneg _
    by_cases hpM : p ≤ M
    · have hnot : ¬ (M < p ∧ p ∣ Nabs) := fun h => by omega
      simp only [hE, ite_eq_left_of_eq_true _ _ (eq_true hpM),
        ite_eq_right_of_eq_false _ _ (eq_false hnot), add_zero]
      exact hb
    · push Not at hpM
      by_cases hdiv : p ∣ Nabs
      · simp only [hE, ite_eq_right_of_eq_false _ _ (eq_false (not_le.mpr hpM)),
          ite_eq_left_of_eq_true _ _ (eq_true (And.intro hpM hdiv)), zero_add]
        have hL : Nat.log p S ≤ 1 := by
          have h := hS_lt p hpM
          by_cases hS0 : S = 0
          · rw [hS0, Nat.log_zero_right]; omega
          · have := (Nat.log_lt_iff_lt_pow hp.one_lt hS0).mpr h; omega
        have hL' : (Nat.log p S : ℝ) ≤ 1 := by exact_mod_cast hL
        nlinarith
      · have hnd : ¬ (p : ℤ) ∣ resultant F G := fun h => hdiv (hpsupp p hp hp2 hpM h)
        rw [padicValInt.eq_zero_of_not_dvd hnd, Nat.cast_zero]
        simp only [hE, ite_eq_right_of_eq_false _ _ (eq_false (not_le.mpr hpM))]
        positivity
  have hup := log_oddPart_le hR (m := N0) (by omega) hsupp hEp
  have hE0 : ∀ p ∈ P, 0 ≤ E p * log p := fun p hp => by
    have : 0 ≤ log (p : ℝ) := Real.log_nonneg (by
      exact_mod_cast (mem_filter.mp hp).2.one_lt.le)
    simp only [hE]
    positivity
  have hup2 : ∑ p ∈ P.erase 2, E p * log p ≤ ∑ p ∈ P, E p * log p :=
    Finset.sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun p hp _ => hE0 p hp
  -- the three sums
  have hsplit : ∑ p ∈ P, E p * log p = F.natDegree *
      (∑ p ∈ P, (if p ≤ M then (Nat.log p S : ℝ) else 0) * log p +
        ∑ p ∈ P, (T.factorization p : ℝ) * log p +
        ∑ p ∈ P, (if M < p ∧ p ∣ Nabs then (1 : ℝ) else 0) * log p) := by
    rw [← sum_add_distrib, ← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun p _ => ?_
    simp only [hE]
    ring
  have hs1 : ∑ p ∈ P, (if p ≤ M then (Nat.log p S : ℝ) else 0) * log p =
      primePowerLogSum M (S : ℝ) := by
    rw [primePowerLogSum_eq]
    have e : ∑ p ∈ P, (if p ≤ M then (Nat.log p S : ℝ) else 0) * log p =
        ∑ p ∈ P.filter (· ≤ M), (Nat.log p S : ℝ) * log p := by
      rw [Finset.sum_filter (s := P) (fun p => p ≤ M) (fun p => (Nat.log p S : ℝ) * log p)]
      exact sum_congr rfl fun p _ => by split_ifs <;> simp
    rw [e]
    have hfilt : P.filter (· ≤ M) = (range (M + 1)).filter Nat.Prime := by
      ext p
      simp only [hP, mem_filter, mem_range]
      constructor
      · rintro ⟨⟨_, hp⟩, hpM⟩; exact ⟨by omega, hp⟩
      · rintro ⟨hpM, hp⟩; exact ⟨⟨by omega, hp⟩, by omega⟩
    rw [hfilt]
    exact sum_congr rfl fun p _ => by rw [floor_logb_natCast_eq]
  have hs2 : ∑ p ∈ P, (T.factorization p : ℝ) * log p = log (T : ℝ) := by
    refine (log_eq_sum_factorization_of_subset fun p hp => ?_).symm
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hT0) (Nat.dvd_of_mem_primeFactors hp)
    have : T ≤ Nabs := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hA0)
    exact mem_filter.mpr ⟨mem_range.mpr (by omega), hpp⟩
  have hs3 : ∑ p ∈ P, (if M < p ∧ p ∣ Nabs then (1 : ℝ) else 0) * log p ≤
      log (T : ℝ) + log |(Aint : ℝ)| := by
    have e : ∑ p ∈ P, (if M < p ∧ p ∣ Nabs then (1 : ℝ) else 0) * log p =
        ∑ p ∈ P.filter (fun p => M < p ∧ p ∣ Nabs), log (p : ℝ) := by
      rw [Finset.sum_filter (s := P) (fun p => M < p ∧ p ∣ Nabs) (fun p => log (p : ℝ))]
      exact sum_congr rfl fun p _ => by split_ifs <;> simp
    rw [e]
    calc ∑ p ∈ P.filter (fun p => M < p ∧ p ∣ Nabs), log (p : ℝ)
        ≤ ∑ p ∈ Nabs.primeFactors, log (p : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p hp _ =>
            Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le)
          obtain ⟨hpP, -, hpd⟩ := mem_filter.mp hp
          exact Nat.mem_primeFactors.mpr ⟨(mem_filter.mp hpP).2, hpd, hNabs0⟩
      _ ≤ log (Nabs : ℝ) := sum_log_primeFactors_le hNabs0
      _ = log (T : ℝ) + log |(Aint : ℝ)| := by
          rw [hNabs, Nat.cast_mul, Real.log_mul (by exact_mod_cast hT0)
            (by exact_mod_cast hA0), Nat.cast_natAbs, Int.cast_abs]
  -- Lemma 2.7
  have hS1 : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast (show 1 ≤ S by omega)
  have hS5 : (S : ℝ) ≤ 5 * (M : ℕ) := by
    have : S ≤ 5 * M := by rw [hS, hM]; omega
    exact_mod_cast this
  have hPsi := (lcm_bound hH M (by omega) (S : ℝ) hS1 hS5)
  -- the 2-adic term of the lower bound
  have hL2 : (Nat.log 2 S : ℝ) * log 2 ≤ log (S : ℝ) := by
    have h := Nat.pow_log_le_self 2 (show S ≠ 0 by omega)
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast h)
  have hT2 : (padicValNat 2 T : ℝ) * log 2 ≤ log (T : ℝ) := by
    have h := Nat.le_of_dvd (Nat.pos_of_ne_zero hT0) (pow_padicValNat_dvd (p := 2) (n := T))
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast h)
  have hdpos : (0 : ℝ) < F.natDegree := by exact_mod_cast hd
  have hlogd : log (F.natDegree : ℝ) ≤ log ((m : ℝ) + 1) :=
    Real.log_le_log hdpos (by have : (F.natDegree : ℝ) ≤ m := by exact_mod_cast hdm
                              linarith)
  have hBpos : (0 : ℝ) < ((2 * m + δ + a).choose a : ℝ) := by exact_mod_cast hbpos
  have hlogγb : log (γ / ((2 * m + δ + a).choose a : ℕ)) =
      log γ - log ((2 * m + δ + a).choose a : ℝ) := Real.log_div hγ.ne' hBpos.ne'
  have hm1' : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hSpos : (0 : ℝ) < (S : ℝ) := by linarith
  have hlogc : log (8 * ((m : ℝ) + 1) * (S : ℝ) * ((2 * m + δ + a).choose a : ℝ) / γ) =
      log 8 + log ((m : ℝ) + 1) + log (S : ℝ) + log ((2 * m + δ + a).choose a : ℝ) - log γ := by
    rw [Real.log_div (by positivity) hγ.ne', Real.log_mul (by positivity) hBpos.ne',
      Real.log_mul (by positivity) hSpos.ne', Real.log_mul (by norm_num) hm1'.ne']
  have h8 : log (8 : ℝ) = 3 * log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
  have hupd : log (|((resultant F G : ℤ) : ℝ)| / 2 ^ padicValInt 2 (resultant F G)) /
      F.natDegree ≤ primePowerLogSum M (S : ℝ) + log (T : ℝ) +
        (log (T : ℝ) + log |(Aint : ℝ)|) := by
    rw [div_le_iff₀ hdpos]
    rw [hsplit, hs1, hs2] at hup2
    have := mul_le_mul_of_nonneg_left hs3 hdpos.le
    linarith
  rw [hlogc, h8] at hcrit
  rw [hlogγb, show 2 * (2 * m + δ) + a + b + 1 = S by omega] at hlow
  push_cast at hlow hcrit hupd hT2 hL2
  linarith [hPsi.1, hPsi.2]

end ArithmeticOfJacobiPolynomials
