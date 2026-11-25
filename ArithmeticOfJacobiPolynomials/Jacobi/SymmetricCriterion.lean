/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.SymmetricBridge
public import ArithmeticOfJacobiPolynomials.Jacobi.SymmetricPrimeDivisors
public import ArithmeticOfJacobiPolynomials.Padic.IntegralLocalBound
public import ArithmeticOfJacobiPolynomials.Analysis.RealResultantExact
public import ArithmeticOfJacobiPolynomials.Analysis.SymmetricEnergy
public import ArithmeticOfJacobiPolynomials.NumberTheory.LcmBound
public import ArithmeticOfJacobiPolynomials.Polynomial.PrimitiveFactorization

/-!
# The exact criterion for symmetric parameters (Theorem 3.4)

Let `r ≥ 0`, `m ≥ max{2r, 4}`, `δ ∈ {0,1}`, `n = 2m + δ`, and let
`f = P_{n+r}^{(r)} = (2r-1)!! C_n^{r+1/2}` and `h = f / x^δ`. With
`S = 2n + 2r + 1`, `K = binom(m+r, r)`, `A = (n+r)!² / (n! (n+2r)!)` and
`A_{≤m} = ∏_{p ≤ m} p^{v_p(A)}` (signed exponents), Theorem 3.4 of the manuscript states that
`m log 4 > Ψ_m(S) + log(8√m) + log K + log A_{≤m}` implies that `h` is irreducible over `ℚ`.

The proof follows the manuscript. A primitive integral factorization `κ h = F G` with
`1 ≤ d = deg F ≤ e = deg G` gives `R = Res(F, G) ≠ 0`, and:
* for odd `p ≤ m`, `v_p(R) ≤ d D_p` with `D_p = ⌊log_p S⌋ + v_p(A)` (Lemma 2.4 applied to
  `F(2X+1), G(2X+1)`, which divide `Q = f(2X+1)/f(1)`);
* for odd `p > m`, `p ∤ R` (the prime support (3.18));
* hence `log 𝓡 / d ≤ Ψ_m(S) + log A_{≤m} - D_2 log 2` for the odd part `𝓡` of `|R|` (3.20);
* Lemma 2.6 and the energy bound (3.21) give `log 𝓡 / d > m log 4 - log(8√m) - log K - D_2 log 2`
  (3.22); the two estimates contradict the criterion.

The real input is the cited simplicity and location of the zeros of `P_n^{(r,r)}`
(`JacobiSimpleRealZeros`, [DLMF, §18.2(vi)]), transported to `h` through the proved identity
`f = (f(1)/binom(n+r,r)) P_n^{(r,r)}`; the interval Vandermonde bound of Lemma 2.5 is proved
(`intervalVandermondeBound`).

Main results:
* `ArithmeticOfJacobiPolynomials.irreducible_reducedDerivative_of_exact_criterion`: Theorem 3.4 for
`h`;
* `ArithmeticOfJacobiPolynomials.irreducible_reducedGegenbauer_of_exact_criterion`: Theorem 3.4 for
  `F_{m,r,δ} = C_{2m+δ}^{r+1/2}/x^δ`.
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset Real

local notation "K₂" => PadicAlgCl 2

/-! ### The truncated factorial ratio -/

/-- `A_{≤m} = ∏_{p ≤ m} p^{v_p(A)}`, with the signed exponents `v_p(A) ∈ ℤ`. -/
noncomputable def primeTruncation (A : ℚ) (m : ℕ) : ℝ :=
  ∏ p ∈ (range (m + 1)).filter Nat.Prime, (p : ℝ) ^ padicValRat p A

theorem primeTruncation_eq (A : ℚ) (m : ℕ) : primeTruncation A m =
    ∏ p ∈ (range (m + 1)).filter Nat.Prime, (p : ℝ) ^ padicValRat p A := (rfl)

theorem log_primeTruncation (A : ℚ) (m : ℕ) : log (primeTruncation A m) =
    ∑ p ∈ (range (m + 1)).filter Nat.Prime, (padicValRat p A : ℝ) * log p := by
  rw [primeTruncation_eq, Real.log_prod]
  · exact sum_congr rfl fun p _ => Real.log_zpow _ _
  · intro p hp
    have : (0 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.pos
    exact (zpow_pos this _).ne'

/-- `⌊log_p S⌋` is `Nat.log p S` for a natural number `S`. -/
theorem floor_logb_natCast_eq (p S : ℕ) : (⌊logb p (S : ℝ)⌋ : ℝ) = Nat.log p S := by
  rw [Real.floor_logb_natCast (Nat.cast_nonneg _), Int.log_natCast]
  norm_cast

/-! ### Logarithm of the odd part of an integer -/

/-- If every odd prime factor of `R ≠ 0` is at most `m` and `v_p(R) ≤ E_p` for odd primes
`p ≤ m`, then `log(|R| / 2^{v_2(R)}) ≤ ∑_{2 < p ≤ m} E_p log p`. -/
theorem log_oddPart_le {R : ℤ} (hR : R ≠ 0) {m : ℕ} (hm : 2 ≤ m)
    (hsupp : ∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℤ) ∣ R → p ≤ m) {E : ℕ → ℝ}
    (hE : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≤ m → (padicValInt p R : ℝ) ≤ E p) :
    log (|(R : ℝ)| / 2 ^ padicValInt 2 R) ≤
      ∑ p ∈ ((range (m + 1)).filter Nat.Prime).erase 2, E p * log p := by
  classical
  set N := R.natAbs with hN
  have hN0 : N ≠ 0 := Int.natAbs_ne_zero.mpr hR
  set P := (range (m + 1)).filter Nat.Prime with hP
  have h2P : 2 ∈ P := mem_filter.mpr ⟨mem_range.mpr (by omega), Nat.prime_two⟩
  have habs : |(R : ℝ)| = (N : ℝ) := by rw [hN, Nat.cast_natAbs, Int.cast_abs]
  have hv2 : padicValInt 2 R = N.factorization 2 := by
    rw [Nat.factorization_def N Nat.prime_two]; rfl
  have hsub : N.factorization.support ⊆ P := by
    intro p hp
    rw [Nat.support_factorization] at hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ N := Nat.dvd_of_mem_primeFactors hp
    refine mem_filter.mpr ⟨mem_range.mpr ?_, hpp⟩
    by_cases h2 : p = 2
    · omega
    · have := hsupp p hpp h2 (Int.natCast_dvd.mpr hpd); omega
  have hlogN : log (N : ℝ) = ∑ p ∈ P, (N.factorization p : ℝ) * log p := by
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum_of_support_subset _ hsub]
    intro i _; simp
  have hsum : ∑ p ∈ P.erase 2, (N.factorization p : ℝ) * log p ≤
      ∑ p ∈ P.erase 2, E p * log p := by
    refine sum_le_sum fun p hp => ?_
    obtain ⟨hp2, hpP⟩ := mem_erase.mp hp
    obtain ⟨hpm, hpp⟩ := mem_filter.mp hpP
    have hlog : 0 ≤ log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have hv : (N.factorization p : ℝ) = padicValInt p R := by
      rw [Nat.factorization_def N hpp]; rfl
    rw [hv]
    exact mul_le_mul_of_nonneg_right (hE p hpp hp2 (by simp only [mem_range] at hpm; omega)) hlog
  have hsplit := Finset.add_sum_erase P (fun p => (N.factorization p : ℝ) * log p) h2P
  rw [habs, Real.log_div (by exact_mod_cast hN0) (by positivity), Real.log_pow, hlogN, ← hsplit,
    hv2]
  push_cast
  linarith

/-! ### The polynomial `h = f / x^δ` -/

section Reduced

variable (m r δ : ℕ)

/-- The real zeros of `f = P_{n+r}^{(r)}` (from [DLMF, §18.2(vi)] for `P_n^{(r,r)}`). -/
theorem iterate_derivative_legendreP_real_roots (hZ : JacobiSimpleRealZeros) (n : ℕ) :
    ((derivative^[r] (legendreP (n + r))).map (algebraMap ℚ ℝ)).roots.Nodup ∧
    ((derivative^[r] (legendreP (n + r))).map (algebraMap ℚ ℝ)).roots.card = n ∧
    ∀ x ∈ ((derivative^[r] (legendreP (n + r))).map (algebraMap ℚ ℝ)).roots,
      -1 < x ∧ x < 1 := by
  have hr : (-1 : ℚ) < r := by have := (Nat.cast_nonneg r : (0 : ℚ) ≤ r); linarith
  have hB : ((n + r).choose r : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hc : (algebraMap ℚ ℝ) ((derivative^[r] (legendreP (n + r))).eval 1 /
      ((n + r).choose r : ℚ)) ≠ 0 := by
    rw [_root_.map_ne_zero]
    exact div_ne_zero (iterate_derivative_legendreP_eval_one_ne_zero n r) hB
  rw [iterate_derivative_legendreP_eq_jacobiP n r, Polynomial.map_mul, Polynomial.map_C,
    roots_C_mul _ hc]
  exact hZ.rat r r hr hr n

theorem X_pow_mul_reduced (hδ : δ ≤ 1) :
    polyX ^ δ * (derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ) =
      derivative^[r] (legendreP (2 * m + δ + r)) :=
  X_pow_mul_iterate_derivative_legendreP_divByMonic m r δ hδ

theorem reduced_ne_zero (hδ : δ ≤ 1) :
    derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ ≠ 0 := by
  intro h0
  have h := X_pow_mul_reduced m r δ hδ
  rw [h0, mul_zero] at h
  exact iterate_derivative_legendreP_eval_one_ne_zero (2 * m + δ) r (by rw [← h, eval_zero])

theorem natDegree_reduced (_hδ : δ ≤ 1) :
    (derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ).natDegree = 2 * m := by
  rw [natDegree_divByMonic _ (monic_X_pow δ), natDegree_iterate_derivative_legendreP,
    natDegree_X_pow]
  omega

theorem coeff_zero_reduced (hδ : δ ≤ 1) :
    (derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ).coeff 0 ≠ 0 := by
  have h := congrArg (fun q => q.coeff (0 + δ)) (X_pow_mul_reduced m r δ hδ)
  rw [coeff_X_pow_mul, zero_add, coeff_iterate_derivative_legendreP_center m r δ hδ] at h
  rw [h]
  have hdf : (0 : ℚ) < ((2 * m + 2 * r + 2 * δ - 1).doubleFactorial : ℚ) := by
    exact_mod_cast Nat.doubleFactorial_pos _
  have hpos : (0 : ℚ) < 2 ^ m * (m.factorial : ℚ) := by positivity
  exact mul_ne_zero (div_ne_zero (pow_ne_zero _ (by norm_num)) hpos.ne') hdf.ne'

/-- The real zeros of `h = f/x^δ`: `2m` simple zeros, all nonzero and in `(-1,1)`. -/
theorem reduced_real_roots (hZ : JacobiSimpleRealZeros) (hδ : δ ≤ 1) :
    ((derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ).map (algebraMap ℚ ℝ)).roots.Nodup ∧
    ((derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ).map
      (algebraMap ℚ ℝ)).roots.card = 2 * m ∧
    ∀ x ∈ ((derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ).map (algebraMap ℚ ℝ)).roots,
      x ≠ 0 ∧ -1 < x ∧ x < 1 := by
  obtain ⟨hnd, hcard, hint⟩ := iterate_derivative_legendreP_real_roots r hZ (2 * m + δ)
  have hhR0 : (derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ).map (algebraMap ℚ ℝ) ≠ 0
    := by
    rw [Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective]
    exact reduced_ne_zero m r δ hδ
  have e : (derivative^[r] (legendreP (2 * m + δ + r))).map (algebraMap ℚ ℝ) =
      (polyX : ℝ[X]) ^ δ * (derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ).map
        (algebraMap ℚ ℝ) := by
    conv_lhs => rw [← X_pow_mul_reduced m r δ hδ]
    rw [Polynomial.map_mul, Polynomial.map_pow, map_X]
  have hsplit : ((derivative^[r] (legendreP (2 * m + δ + r))).map (algebraMap ℚ ℝ)).roots =
      ((polyX : ℝ[X]) ^ δ).roots +
        ((derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ).map (algebraMap ℚ ℝ)).roots := by
    rw [e]; exact roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) hhR0)
  have hle : ((derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ).map (algebraMap ℚ
    ℝ)).roots ≤
      ((derivative^[r] (legendreP (2 * m + δ + r))).map (algebraMap ℚ ℝ)).roots := by
    rw [hsplit]; exact Multiset.le_add_left _ _
  refine ⟨Multiset.nodup_of_le hle hnd, ?_, fun x hx => ⟨?_, hint x (Multiset.mem_of_le hle hx)⟩⟩
  · rw [hsplit, Multiset.card_add, roots_X_pow, Multiset.card_nsmul, Multiset.card_singleton,
      mul_one] at hcard
    omega
  · rintro rfl
    have hr : ((derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ).map
        (algebraMap ℚ ℝ)).eval 0 = 0 := (mem_roots hhR0).mp hx
    rw [← coeff_zero_eq_eval_zero, coeff_map, map_eq_zero] at hr
    exact coeff_zero_reduced m r δ hδ hr

/-- `h(2X+1)` divides `Q = P_n^{(r,r)}(2X+1)/binom(n+r,r)` in `ℚ[X]`. -/
theorem reduced_comp_dvd (hδ : δ ≤ 1) :
    (derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ).comp (2 * polyX + 1) ∣
      integralWeightQ r r (2 * m + δ) := by
  have hb := iterate_derivative_legendreP_eval_one_ne_zero (2 * m + δ) r
  have e1 := iterate_derivative_legendreP_comp_eq (2 * m + δ) r
  have e2 : (derivative^[r] (legendreP (2 * m + δ + r))).comp (2 * polyX + 1) =
      (2 * polyX + 1) ^ δ * (derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ).comp (2 *
        polyX + 1) := by
    conv_lhs => rw [← X_pow_mul_reduced m r δ hδ]
    rw [mul_comp, X_pow_comp]
  refine ⟨C (1 / (derivative^[r] (legendreP (2 * m + δ + r))).eval 1) * (2 * polyX + 1) ^ δ, ?_⟩
  calc integralWeightQ r r (2 * m + δ) =
        C (1 / (derivative^[r] (legendreP (2 * m + δ + r))).eval 1) *
          (C ((derivative^[r] (legendreP (2 * m + δ + r))).eval 1) *
            integralWeightQ r r (2 * m + δ)) := by
        rw [← mul_assoc, ← C_mul, one_div_mul_cancel hb, C_1, one_mul]
    _ = _ := by rw [← e1, e2]; ring

/-- `Q = P_n^{(r,r)}(2X+1)/binom(n+r,r)` has degree `n`. -/
theorem natDegree_integralWeightQ (n : ℕ) : (integralWeightQ r r n).natDegree = n := by
  have e1 := iterate_derivative_legendreP_comp_eq n r
  have hb := iterate_derivative_legendreP_eval_one_ne_zero n r
  have hdeg : ((derivative^[r] (legendreP (n + r))).comp (2 * polyX + 1)).natDegree = n := by
    rw [natDegree_comp, natDegree_iterate_derivative_legendreP,
      show (2 * polyX + 1 : ℚ[X]) = C 2 * polyX + C 1 by simp [C_ofNat],
      natDegree_linear (by norm_num : (2 : ℚ) ≠ 0), mul_one]
  rw [e1, natDegree_C_mul hb] at hdeg
  exact hdeg

end Reduced

/-! ### Local estimates for a factorization -/

/-- The row bound `D_p = ⌊log_p S⌋ + v_p(A)` is nonnegative (it bounds a row sum). -/
theorem symmetricRowBound_nonneg (r : ℕ) {n : ℕ} (hn : 1 ≤ n) (p : ℕ) [Fact p.Prime] :
    0 ≤ (Nat.log p (2 * n + 2 * r + 1) : ℝ) + padicValRat p (symmetricRatio n r) := by
  classical
  set QK := (integralWeightQ r r n).map (algebraMap ℚ (PadicAlgCl p)) with hQK
  have hnat : 0 < QK.natDegree := by
    rw [hQK, natDegree_map, natDegree_integralWeightQ r n]
    omega
  have hdeg : QK.degree ≠ 0 := (natDegree_pos_iff_degree_pos.mp hnat).ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root QK hdeg
  have hQ0 : QK ≠ 0 := by
    rw [hQK, Polynomial.map_ne_zero_iff (algebraMap ℚ _).injective]
    exact integralWeightQ_ne_zero r r n
  have hmem : z ∈ QK.roots := (mem_roots hQ0).mpr hz
  exact le_trans (sum_nonneg fun w _ => projDist_nonneg z w)
    (integralWeight_row_bound_symmetric r hn hmem)

/-- An odd prime does not divide all coefficients of `F(2X+1)` when `F` is primitive. -/
theorem exists_not_dvd_coeff_comp {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {F : ℤ[X]}
    (hF : F.IsPrimitive) : ∃ j, ¬ (p : ℤ) ∣ (F.comp (2 * polyX + 1)).coeff j := by
  have := Fact.mk hp
  by_contra! h
  have h0 : (F.comp (2 * polyX + 1)).map (Int.castRingHom (ZMod p)) = 0 := by
    ext j
    rw [coeff_map, coeff_zero, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact h j
  rw [Polynomial.map_comp] at h0
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h2
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h2
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  rcases comp_eq_zero_iff.mp h0 with hF0 | ⟨-, hq⟩
  · have hdvd : C (p : ℤ) ∣ F := by
      refine (C_dvd_iff_dvd_coeff _ _).mpr fun j => ?_
      have := congrArg (fun q => q.coeff j) hF0
      simp only [coeff_map, coeff_zero, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at this
      exact this
    have hu := isPrimitive_iff_isUnit_of_C_dvd.mp hF _ hdvd
    rw [Int.isUnit_iff] at hu
    rcases hu with hu | hu
    · exact hp.one_lt.ne' (by exact_mod_cast hu)
    · have : (0 : ℤ) ≤ p := Int.natCast_nonneg p
      omega
  · have h1 : ((2 * polyX + 1 : ℤ[X]).map (Int.castRingHom (ZMod p))).coeff 1 = 2 := by
      simp [coeff_one]
    have h1' : (C (((2 * polyX + 1 : ℤ[X]).map (Int.castRingHom (ZMod p))).coeff 0)).coeff 1 = 0 :=
      coeff_C_of_ne_zero one_ne_zero
    exact h2 (h1.symm.trans ((congrArg (fun q => q.coeff 1) hq).trans h1'))

/-- **The odd local bound used in (3.20).** For a factorization `κ h = F G` into primitive integer
polynomials with `R = Res(F, G) ≠ 0` and an odd prime `p`, `v_p(R) ≤ deg F · D_p`. -/
theorem padicValInt_resultant_le_symmetric (m r δ : ℕ) (hδ : δ ≤ 1) (hm : 1 ≤ m) {κ : ℚ}
    (hκ : κ ≠ 0) {F G : ℤ[X]}
    (hFG : (F * G).map (Int.castRingHom ℚ) =
      C κ * (derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ))
    (hF : F.IsPrimitive) (hG : G.IsPrimitive) (hR : resultant F G ≠ 0) (p : ℕ) [hp : Fact p.Prime]
    (hp2 : p ≠ 2) :
    (padicValInt p (resultant F G) : ℝ) ≤ F.natDegree *
      ((Nat.log p (2 * (2 * m + δ) + 2 * r + 1) : ℝ) +
        padicValRat p (symmetricRatio (2 * m + δ) r)) := by
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
  have hPQ : ((F * G).comp (2 * polyX + 1)).map (Int.castRingHom ℚ) ∣
      integralWeightQ r r (2 * m + δ) := by
    have hL : (2 * polyX + 1 : ℤ[X]).map (Int.castRingHom ℚ) = 2 * polyX + 1 := by simp
    rw [Polynomial.map_comp, hFG, hL, mul_comp, C_comp]
    refine dvd_trans ?_ (reduced_comp_dvd m r δ hδ)
    exact ⟨C κ⁻¹, by rw [mul_comm (C κ), mul_assoc, ← C_mul, mul_inv_cancel₀ hκ, C_1, mul_one]⟩
  have hdvd : ((F.comp (2 * polyX + 1)).map (Int.castRingHom ℤ_[p]) *
      (G.comp (2 * polyX + 1)).map (Int.castRingHom ℤ_[p])).map (algebraMap ℤ_[p] (PadicAlgCl p)) ∣
      (integralWeightQ r r (2 * m + δ)).map (algebraMap ℚ (PadicAlgCl p)) := by
    have e : ((F.comp (2 * polyX + 1)).map (Int.castRingHom ℤ_[p]) *
        (G.comp (2 * polyX + 1)).map (Int.castRingHom ℤ_[p])).map (algebraMap ℤ_[p] (PadicAlgCl
          p)) =
        (((F * G).comp (2 * polyX + 1)).map (Int.castRingHom ℚ)).map (algebraMap ℚ (PadicAlgCl
          p)) := by
      rw [← Polynomial.map_mul, map_padicInt_map_eq, Polynomial.map_map, mul_comp,
        show (algebraMap ℚ (PadicAlgCl p)).comp (Int.castRingHom ℚ) =
          Int.castRingHom (PadicAlgCl p) from RingHom.ext_int _ _]
    rw [e]
    exact Polynomial.map_dvd _ hPQ
  have key := integralWeight_resultant_le r r (n := 2 * m + δ) (by omega) hA hB hdvd
    (fun z hz => integralWeight_row_bound_symmetric r (by omega) hz)
  rw [padicVal_resultant_map_intCast hR', hval, hAdeg] at key
  exact key

open Classical in
/-- **The 2-adic row bound for Lemma 2.6.** Every root `z` of `h(2X+1)` in `PadicAlgCl 2` has
projective row sum at most `D_2 = ⌊log_2 S⌋ + v_2(A)`. -/
theorem reduced_comp_row_bound_two (m r δ : ℕ) (hδ : δ ≤ 1) (hm : 1 ≤ m) :
    ∀ z ∈ (((derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ).comp (2 * polyX + 1)).map
        (algebraMap ℚ K₂)).roots,
      ∑ w ∈ (((derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ).comp (2 * polyX + 1)).map
          (algebraMap ℚ K₂)).roots.toFinset.erase z, projDist 2 z w ≤
        (Nat.log 2 (2 * (2 * m + δ) + 2 * r + 1) : ℝ) +
          padicValRat 2 (symmetricRatio (2 * m + δ) r) := by
  intro z hz
  set QK := (integralWeightQ r r (2 * m + δ)).map (algebraMap ℚ K₂) with hQK
  have hQ0 : QK ≠ 0 := by
    rw [hQK, Polynomial.map_ne_zero_iff (algebraMap ℚ _).injective]
    exact integralWeightQ_ne_zero r r _
  have hle := roots.le_of_dvd hQ0 (Polynomial.map_dvd (algebraMap ℚ K₂) (reduced_comp_dvd m r δ hδ))
  have hzQ : z ∈ QK.roots := Multiset.mem_of_le hle hz
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (fun w hw => ?_)
    fun w _ _ => projDist_nonneg z w) (integralWeight_row_bound_symmetric r (by omega) hzQ)
  obtain ⟨hwz, hw⟩ := mem_erase.mp hw
  exact mem_erase.mpr ⟨hwz, Multiset.mem_toFinset.mpr
    (Multiset.mem_of_le hle (Multiset.mem_toFinset.mp hw))⟩

/-! ### Real roots of a factor -/

/-- If `F G` maps to a real polynomial with `deg(FG)` simple real roots, then `F` has
`deg F` distinct real roots. -/
theorem exists_injective_roots_of_mul {F G : ℤ[X]} (hFG0 : F * G ≠ 0)
    (hnd : ((F * G).map (Int.castRingHom ℝ)).roots.Nodup)
    (hcard : ((F * G).map (Int.castRingHom ℝ)).roots.card = (F * G).natDegree) :
    ∃ α : Fin F.natDegree → ℝ, Function.Injective α ∧
      ∀ i, (F.map (Int.castRingHom ℝ)).eval (α i) = 0 := by
  classical
  have hinj : Function.Injective (Int.castRingHom ℝ) := Int.cast_injective
  have hF0 : F ≠ 0 := left_ne_zero_of_mul hFG0
  have hG0 : G ≠ 0 := right_ne_zero_of_mul hFG0
  have hm0 : F.map (Int.castRingHom ℝ) * G.map (Int.castRingHom ℝ) ≠ 0 := by
    rw [← Polynomial.map_mul]; exact (Polynomial.map_ne_zero_iff hinj).mpr hFG0
  have hroots : ((F * G).map (Int.castRingHom ℝ)).roots =
      (F.map (Int.castRingHom ℝ)).roots + (G.map (Int.castRingHom ℝ)).roots := by
    rw [Polynomial.map_mul]; exact roots_mul hm0
  have hcF := card_roots' (F.map (Int.castRingHom ℝ))
  have hcG := card_roots' (G.map (Int.castRingHom ℝ))
  rw [natDegree_map_eq_of_injective hinj] at hcF hcG
  rw [hroots, Multiset.card_add, natDegree_mul hF0 hG0] at hcard
  have hcardF : (F.map (Int.castRingHom ℝ)).roots.card = F.natDegree := by omega
  have hndF : (F.map (Int.castRingHom ℝ)).roots.Nodup := by
    rw [hroots] at hnd; exact (Multiset.nodup_add.mp hnd).1
  set s := (F.map (Int.castRingHom ℝ)).roots.toFinset
  have hs : s.card = F.natDegree := by
    rw [Multiset.toFinset_card_of_nodup hndF, hcardF]
  refine ⟨fun i => ((s.equivFin.symm (Fin.cast hs.symm i) : s) : ℝ), ?_, fun i => ?_⟩
  · intro i j hij
    have := Subtype.ext hij
    have := s.equivFin.symm.injective this
    exact Fin.cast_injective _ this
  · have hmem := (s.equivFin.symm (Fin.cast hs.symm i)).2
    have hmem' := Multiset.mem_toFinset.mp hmem
    exact (mem_roots (Polynomial.map_ne_zero_iff hinj |>.mpr hF0)).mp hmem'

/-! ### Theorem 3.4 -/

/-- The separability of `h = f/x^δ` (its real zeros are simple and as many as its degree). -/
theorem reduced_separable (hZ : JacobiSimpleRealZeros) (m r δ : ℕ) (hδ : δ ≤ 1) :
    (derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ).Separable := by
  obtain ⟨hnd, hcard, -⟩ := reduced_real_roots m r δ hZ hδ
  rw [← separable_map (algebraMap ℚ ℝ)]
  have h0 : (derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ).map (algebraMap ℚ ℝ) ≠ 0 := by
    rw [Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective]
    exact reduced_ne_zero m r δ hδ
  refine (nodup_roots_iff_of_splits h0 ?_).mp hnd
  rw [splits_iff_card_roots, hcard, natDegree_map, natDegree_reduced m r δ hδ]

/-- **Theorem 3.4, exact criterion (3.13), for `h = P_{n+r}^{(r)}/x^δ`.**
Let `r ≥ 0`, `m ≥ max{2r, 4}`, `δ ∈ {0,1}`, `n = 2m+δ`, `S = 2n+2r+1`, `K = binom(m+r, r)`,
`A = (n+r)!²/(n!(n+2r)!)` and `A_{≤m} = ∏_{p ≤ m} p^{v_p(A)}`. If
`m log 4 > Ψ_m(S) + log(8√m) + log K + log A_{≤m}`, then `P_{n+r}^{(r)}/x^δ` is irreducible
over `ℚ`. Conditional on the proved `intervalVandermondeBound` (Lemma 2.5) and
`JacobiSimpleRealZeros` ([DLMF, §18.2(vi)]). -/
theorem irreducible_reducedDerivative_of_exact_criterion (hZ : JacobiSimpleRealZeros) {m r δ : ℕ}
    (hδ : δ ≤ 1) (hm : max (2 * r) 4 ≤ m)
    (hcrit : primePowerLogSum m ((2 * (2 * m + δ) + 2 * r + 1 : ℕ) : ℝ) + log (8 * √(m : ℝ)) +
        log ((m + r).choose r : ℝ) + log (primeTruncation (symmetricRatio (2 * m + δ) r) m) <
      m * log 4) :
    Irreducible (derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ) := by
  obtain ⟨hr2, hm4⟩ : 2 * r ≤ m ∧ 4 ≤ m := ⟨le_of_max_le_left hm, le_of_max_le_right hm⟩
  have hm1 : 1 ≤ m := by omega
  obtain ⟨hnd, hcard, hroots⟩ := reduced_real_roots m r δ hZ hδ
  have hdeg := natDegree_reduced m r δ hδ
  have hh0 := reduced_ne_zero m r δ hδ
  have hXh := X_pow_mul_reduced m r δ hδ
  have hlc : 0 < (derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ).leadingCoeff := by
    have e := congrArg leadingCoeff hXh
    rw [leadingCoeff_mul, leadingCoeff_X_pow, one_mul,
      leadingCoeff_iterate_derivative_legendreP] at e
    rw [e]
    have : (0 : ℚ) < ((2 * (2 * m + δ) + 2 * r - 1).doubleFactorial : ℚ) := by
      exact_mod_cast Nat.doubleFactorial_pos _
    positivity
  -- an integral multiple
  obtain ⟨g, hg⟩ := exists_int_two_pow_mul_iterate_derivative_legendreP (2 * m + δ + r) r
  have hgh : (g /ₘ polyX ^ δ).map (Int.castRingHom ℚ) =
      C ((2 : ℚ) ^ (2 * m + δ + r)) * (derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ)
        := by
    rw [map_divByMonic _ (monic_X_pow δ), hg, Polynomial.map_pow, map_X]
    have e : C ((2 : ℚ) ^ (2 * m + δ + r)) * derivative^[r] (legendreP (2 * m + δ + r)) =
        polyX ^ δ * (C ((2 : ℚ) ^ (2 * m + δ + r)) *
          (derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ)) := by
      rw [mul_left_comm, hXh]
    rw [e, mul_divByMonic_cancel_left _ (monic_X_pow δ)]
  refine irreducible_of_forall_primitive_factorization (by omega) hlc (by positivity) hgh ?_
  intro κ H F G hκ hH hHprim hHFG hFprim hGprim hFlc hGlc hd hde
  have hF0 : F ≠ 0 := hFprim.ne_zero
  have hG0 : G ≠ 0 := hGprim.ne_zero
  have hHdeg : H.natDegree = 2 * m := by
    rw [← natDegree_map_eq_of_injective (f := Int.castRingHom ℚ) Int.cast_injective H, hH,
      natDegree_C_mul hκ.ne', hdeg]
  have hdeN : F.natDegree + G.natDegree = 2 * m := by
    rw [← hHdeg, hHFG, natDegree_mul hF0 hG0]
  have hdm : F.natDegree ≤ m := by omega
  have hFGmap : (F * G).map (Int.castRingHom ℚ) =
      C κ * (derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ) := by
    rw [← hHFG]; exact hH
  -- the resultant is nonzero
  have hsep : (C κ * (derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ)).Separable :=
    Separable.unit_mul (isUnit_C.mpr (IsUnit.mk0 _ hκ.ne')) (reduced_separable hZ m r δ hδ)
  have hR : resultant F G ≠ 0 := by
    have hcop : IsCoprime (F.map (Int.castRingHom ℚ)) (G.map (Int.castRingHom ℚ)) := by
      apply Separable.isCoprime
      rw [← Polynomial.map_mul, hFGmap]; exact hsep
    intro h0
    apply resultant_ne_zero _ _ hcop
    rw [← intCast_resultant, h0, Int.cast_zero]
  -- real roots of `F`
  have hFGR : (F * G).map (Int.castRingHom ℝ) = C (κ : ℝ) *
      (derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ).map (algebraMap ℚ ℝ) := by
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
  have hbpos : 0 < (2 * m + δ + 2 * r).choose (2 * r) * (2 * r - 1).doubleFactorial :=
    Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.doubleFactorial_pos _)
  have hh1 : (derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ).eval 1 =
      (derivative^[r] (legendreP (2 * m + δ + r))).eval 1 := by
    have := congrArg (eval 1) hXh
    rw [eval_mul, eval_pow, eval_X, one_pow, one_mul] at this
    exact this
  have hb1 : (derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ).eval 1 =
      (((2 * m + δ + 2 * r).choose (2 * r) * (2 * r - 1).doubleFactorial : ℕ) : ℚ) := by
    rw [hh1, eval_one_iterate_derivative_legendreP_eq_choose]; push_cast; ring
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = Real.sqrt (((2 * m + δ : ℕ) : ℝ) * ((2 * m + δ : ℕ) + 2 * r + 1) *
      (aeval (0 : ℝ) (derivative^[r] (legendreP (2 * m + δ + r)))) ^ 2 +
      (aeval (0 : ℝ) (derivative (derivative^[r] (legendreP (2 * m + δ + r))))) ^ 2) := ⟨_, rfl⟩
  have hγpos : 0 < γ := by rw [hγ]; exact Real.sqrt_pos.mpr (symmetric_gammaSq_pos m r δ hm1 hδ)
  have hγ' : ∀ x ∈ ((derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ).map
      (algebraMap ℚ ℝ)).roots, γ < |(derivative ((derivative^[r] (legendreP (2 * m + δ + r)) /ₘ
        polyX ^ δ).map (algebraMap ℚ ℝ))).eval x| := by
    intro x hx
    obtain ⟨hx0, hx1, hx2⟩ := hroots x hx
    have hroot : aeval x (derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ) = 0 := by
      rw [aeval_def, eval₂_eq_eval_map]
      exact (mem_roots ((Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective).mpr hh0)).mp hx
    rw [derivative_map, eval_map, ← aeval_def, hγ]
    exact symmetric_gamma_lt_abs_derivative m r δ hm1 hδ ⟨hx1, hx2⟩ hx0 hroot
  have hrow := reduced_comp_row_bound_two m r δ hδ hm1
  obtain ⟨-, -, hlow⟩ := realResultant_lowerBound (h := derivative^[r] (legendreP (2 * m + δ + r))
      /ₘ polyX ^ δ) (N := 2 * m)
    ⟨2 * m + δ + r, g /ₘ polyX ^ δ, hgh⟩ hdeg hlc hcard hnd hroots hbpos hb1 hγpos hγ' hrow hκ hH
    hHprim hHFG hFprim hGprim hFlc hGlc rfl rfl hd hde hdeN hαinj hαF
  -- the upper bound
  have hsupp : ∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℤ) ∣ resultant F G → p ≤ m := by
    intro p hp _ hdvd
    by_contra hpm
    push Not at hpm
    have hode : (1 - polyX ^ 2) * derivative (derivative (legendreP (2 * m + δ + r))) -
        2 * polyX * derivative (legendreP (2 * m + δ + r)) +
        C (((2 * m + δ + r : ℕ) : ℚ) * ((2 * m + δ + r : ℕ) + 1)) *
          legendreP (2 * m + δ + r) = 0 := by
      have h0 := jacobiP_ode 0 0 (2 * m + δ + r)
      rw [← legendreP_eq] at h0
      simp only [sub_self, map_zero, zero_add, zero_sub, add_zero] at h0
      rw [show (C (2 : ℚ)) = 2 from rfl] at h0
      linear_combination h0
    have hcoeff := iterate_derivative_legendreP (2 * m + δ) r
    rw [show (2 * m + δ) / 2 = m by omega] at hcoeff
    exact symmetric_prime_support hδ rfl hm hode hcoeff hFprim hGprim hFGmap hp hpm hdvd
  have hE0 : ∀ p : ℕ, p.Prime → 0 ≤ (F.natDegree : ℝ) *
      ((Nat.log p (2 * (2 * m + δ) + 2 * r + 1) : ℝ) +
        padicValRat p (symmetricRatio (2 * m + δ) r)) := by
    intro p hp
    have := Fact.mk hp
    exact mul_nonneg (Nat.cast_nonneg _)
      (symmetricRowBound_nonneg r (n := 2 * m + δ) (by omega) p)
  have hup := log_oddPart_le hR (by omega) hsupp (fun p hp hp2 _ => by
    have := Fact.mk hp
    exact padicValInt_resultant_le_symmetric m r δ hδ hm1 hκ.ne' hFGmap hFprim hGprim hR p hp2)
  have h2P : 2 ∈ (range (m + 1)).filter Nat.Prime :=
    mem_filter.mpr ⟨mem_range.mpr (by omega), Nat.prime_two⟩
  rw [Finset.sum_erase_eq_sub h2P] at hup
  have hsumD : ∑ p ∈ (range (m + 1)).filter Nat.Prime, (F.natDegree : ℝ) *
      ((Nat.log p (2 * (2 * m + δ) + 2 * r + 1) : ℝ) +
        padicValRat p (symmetricRatio (2 * m + δ) r)) * log p =
      F.natDegree * (primePowerLogSum m ((2 * (2 * m + δ) + 2 * r + 1 : ℕ) : ℝ) +
        log (primeTruncation (symmetricRatio (2 * m + δ) r) m)) := by
    rw [log_primeTruncation, primePowerLogSum_eq, ← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun p _ => ?_
    rw [floor_logb_natCast_eq]
    ring
  rw [hsumD] at hup
  -- the energy and degree estimates
  have hdpos : (0 : ℝ) < F.natDegree := by exact_mod_cast hd
  have hγb : Real.sqrt m / ((m + r).choose r : ℝ) <
      γ / (((2 * m + δ + 2 * r).choose (2 * r) * (2 * r - 1).doubleFactorial : ℕ) : ℝ) := by
    have := sqrt_div_choose_lt_symmetric_gamma_div_eval_one m r δ hm1 hδ
    rw [aeval_one_eq_eval_one, ← hh1, hb1, ← hγ] at this
    simpa using this
  have hK : (0 : ℝ) < ((m + r).choose r : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  have hlogγ : log (Real.sqrt m / ((m + r).choose r : ℝ)) <
      log (γ / (((2 * m + δ + 2 * r).choose (2 * r) * (2 * r - 1).doubleFactorial : ℕ) : ℝ)) :=
    Real.log_lt_log (div_pos (Real.sqrt_pos.mpr hmpos) hK) hγb
  rw [Real.log_div (Real.sqrt_pos.mpr hmpos).ne' hK.ne', Real.log_sqrt hmpos.le] at hlogγ
  have hlogd : log (F.natDegree : ℝ) ≤ log m := Real.log_le_log hdpos (by exact_mod_cast hdm)
  have hupd : log (|((resultant F G : ℤ) : ℝ)| / 2 ^ padicValInt 2 (resultant F G)) /
      F.natDegree ≤
      primePowerLogSum m ((2 * (2 * m + δ) + 2 * r + 1 : ℕ) : ℝ) +
        log (primeTruncation (symmetricRatio (2 * m + δ) r) m) -
        ((Nat.log 2 (2 * (2 * m + δ) + 2 * r + 1) : ℝ) +
          padicValRat 2 (symmetricRatio (2 * m + δ) r)) * log 2 := by
    rw [div_le_iff₀ hdpos]
    push_cast at hup ⊢
    linarith
  have h8 : log (8 * √(m : ℝ)) = 3 * log 2 + log m / 2 := by
    rw [Real.log_mul (by norm_num) (Real.sqrt_pos.mpr hmpos).ne', Real.log_sqrt hmpos.le,
      show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    push_cast; ring
  have h4 : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  rw [h8, h4] at hcrit
  push_cast at hlow hupd hcrit hlogγ
  linarith

/-- **Theorem 3.4, exact criterion (3.13).** Under the hypotheses of
`irreducible_reducedDerivative_of_exact_criterion`, `F_{m,r,δ} = C_{2m+δ}^{r+1/2}/x^δ` is
irreducible over `ℚ`. Conditional on `JacobiSimpleRealZeros`. -/
theorem irreducible_reducedGegenbauer_of_exact_criterion (hZ : JacobiSimpleRealZeros) {m r δ : ℕ}
    (hδ : δ ≤ 1) (hm : max (2 * r) 4 ≤ m)
    (hcrit : primePowerLogSum m ((2 * (2 * m + δ) + 2 * r + 1 : ℕ) : ℝ) + log (8 * √(m : ℝ)) +
        log ((m + r).choose r : ℝ) + log (primeTruncation (symmetricRatio (2 * m + δ) r) m) <
      m * log 4) :
    Irreducible (reducedGegenbauer m r δ) := by
  have hirr := irreducible_reducedDerivative_of_exact_criterion hZ hδ hm hcrit
  have hD : ((2 * r - 1).doubleFactorial : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.doubleFactorial_pos _).ne'
  have e : derivative^[r] (legendreP (2 * m + δ + r)) /ₘ polyX ^ δ =
      C ((2 * r - 1).doubleFactorial : ℚ) * reducedGegenbauer m r δ := by
    have h1 := X_pow_mul_reduced m r δ hδ
    rw [iterate_derivative_legendreP_eq_gegenbauerC] at h1 ⊢
    rw [reducedGegenbauer_eq]
    have h2 : gegenbauerC ((r : ℚ) + 1 / 2) (2 * m + δ) =
        polyX ^ δ * (C (1 / ((2 * r - 1).doubleFactorial : ℚ)) *
          (C ((2 * r - 1).doubleFactorial : ℚ) * gegenbauerC ((r : ℚ) + 1 / 2) (2 * m + δ) /ₘ
            polyX ^ δ)) := by
      rw [mul_left_comm, h1, ← mul_assoc, ← C_mul, one_div_mul_cancel hD, C_1, one_mul]
    conv_rhs => rw [h2, mul_divByMonic_cancel_left _ (monic_X_pow δ)]
    rw [← mul_assoc, ← C_mul, mul_one_div_cancel hD, C_1, one_mul]
  rw [e] at hirr
  exact (irreducible_isUnit_mul (isUnit_C.mpr (IsUnit.mk0 _ hD))).mp hirr

end ArithmeticOfJacobiPolynomials
