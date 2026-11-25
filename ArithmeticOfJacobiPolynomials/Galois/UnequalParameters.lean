/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Galois.UnequalParametersWild
public import ArithmeticOfJacobiPolynomials.Galois.SourceWildCycle
public import ArithmeticOfJacobiPolynomials.Galois.UnequalParametersSign
public import ArithmeticOfJacobiPolynomials.Jacobi.Reduction
public import ArithmeticOfJacobiPolynomials.Jacobi.DifferentialEquation
public import ArithmeticOfJacobiPolynomials.PermGroup.Blocks
public import ArithmeticOfJacobiPolynomials.PermGroup.SourcePrimitivity
public import ArithmeticOfJacobiPolynomials.External
public import ArithmeticOfJacobiPolynomials.Jacobi.UnequalIrreducibility

/-!
# Unequal integral parameters: Lemma 5.16 and Proposition 5.17 (Section 5.5)

Notation of Section 3 (§3.1): `a > b ≥ 0`, `s = a + b`, `n = 2m + δ`, `δ ∈ {0,1}`,
`K_δ = centralK a b δ`, `A_δ = centralA a b δ`.

* (5.27) §5.6: `C_δ(z) = 2^{K_{1-δ}} A_{1-δ}(z + δ - 1/2)` is the integral
  polynomial `oppositeNumerator a b δ` (`oppositeNumerator_map`), and
  `𝒲_δ = A_δ C_δ = galoisNumerator a b δ` has degree `≤ s` (`natDegree_galoisNumerator_le`).
* **Lemma 5.16** (`galoisGroupIsSymmetric_jacobiP_of_prime`): if
  `m ≥ 2s + 10`, `P_n^{(a,b)}` is irreducible and a prime `p` satisfies `3n/4 < p ≤ 7n/8` and
  `p ∤ 𝒲_δ(m)`, then `Gal(P_n^{(a,b)}/ℚ) = S_n`. Conditional on Jordan's theorem
  [Jones, Theorem 1.1] (`JordanPrimeCycleTheorem`: a primitive group containing a cycle of
  prime length with at least three fixed points, here a `p`-cycle with `p ≤ n - 3`, contains `A_n`),
  on [Milne, ANT v3.08, Proposition 3.53] (`EisensteinPrimeTotallyRamified`: a root of an
  Eisenstein polynomial generates an extension in which the prime is totally ramified, used for
  the wild `p`-cycle) and on the Jacobi discriminant formula (5.31) (`JacobiDiscriminantFormula`).
* **Proposition 5.17** (`galoisGroupIsSymmetric_jacobiP_explicit`): if
  moreover `n ≥ 5 000 000`, `𝒲_δ(m) ≠ 0` and `log |𝒲_δ(m)| < n/10`, such a prime exists
  (by [Dusart10, Theorem 5.2], `DusartThetaBound`), so `Gal(P_n^{(a,b)}/ℚ) = S_n`. The
  proposition assumes the hypotheses of Theorem 3.1, whose conclusion is
  irreducibility. `galoisGroupIsSymmetric_jacobiP_explicit` takes that conclusion as the
  hypothesis `Irreducible (jacobiP a b n)` (with `m ≥ 2s + 10`);
  `galoisGroupIsSymmetric_jacobiP_explicit_of_criterion` is the statement with the hypotheses of
  Theorem 3.1 themselves, via `irreducible_jacobiP_of_criterion` (additionally conditional on the
  inputs of Theorem 3.1).
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial

/-! ### The numerators (5.27) -/

/-- The opposite central numerator `C_δ(z) = 2^{K_{1-δ}} A_{1-δ}(z + δ - 1/2)` of (5.27)
(§5.6), written as the integral polynomial
`∑_{i ≤ K_{1-δ}} [z^i]A_{1-δ} · 2^{K_{1-δ} - i} (2z + 2δ - 1)^i`
(see `oppositeNumerator_map` for the defining identity). -/
noncomputable def oppositeNumerator (a b δ : ℕ) : ℤ[X] :=
  ∑ i ∈ Finset.range (centralK a b (1 - δ) + 1),
    C ((centralA a b (1 - δ)).coeff i * 2 ^ (centralK a b (1 - δ) - i)) *
      (C 2 * polyX + C (2 * (δ : ℤ) - 1)) ^ i

theorem oppositeNumerator_eq (a b δ : ℕ) : oppositeNumerator a b δ =
    ∑ i ∈ Finset.range (centralK a b (1 - δ) + 1),
      C ((centralA a b (1 - δ)).coeff i * 2 ^ (centralK a b (1 - δ) - i)) *
        (C 2 * polyX + C (2 * (δ : ℤ) - 1)) ^ i := (rfl)

/-- `𝒲_δ(z) = A_δ(z) C_δ(z)` of (5.27) (§5.6). -/
noncomputable def galoisNumerator (a b δ : ℕ) : ℤ[X] :=
  centralA a b δ * oppositeNumerator a b δ

theorem galoisNumerator_eq (a b δ : ℕ) :
    galoisNumerator a b δ = centralA a b δ * oppositeNumerator a b δ := (rfl)

namespace UnequalParameters

/-- `deg A_δ ≤ K_δ` (stated after (3.6)). -/
theorem natDegree_centralA_le (a b δ : ℕ) : (centralA a b δ).natDegree ≤ centralK a b δ := by
  have h1 : (∏ j ∈ Finset.Icc 1 (b + δ), (C (2 : ℤ) * polyX + C (j : ℤ))).natDegree ≤ b + δ := by
    refine le_trans (natDegree_prod_le _ _) ?_
    have h : ∀ j ∈ Finset.Icc 1 (b + δ), (C (2 : ℤ) * polyX + C (j : ℤ)).natDegree ≤ 1 :=
      fun j _ => natDegree_linear_le
    refine le_trans (Finset.sum_le_sum h) ?_
    simp
  have h2 : ∀ h ∈ Finset.range (centralH a b δ + 1),
      (C ((-1) ^ h * ((a - b).choose (δ + 2 * h) : ℤ)) * descPochhammer ℤ h *
        ∏ j ∈ Finset.Icc (b + δ + h + 1) (centralK a b δ), (polyX + C (j : ℤ))).natDegree ≤
        centralH a b δ := by
    intro h hh
    rw [Finset.mem_range] at hh
    have hlin : ∀ j ∈ Finset.Icc (b + δ + h + 1) (centralK a b δ),
        (polyX + C (j : ℤ)).natDegree ≤ 1 := fun j _ => (natDegree_X_add_C (j : ℤ)).le
    have hsum : ∑ j ∈ Finset.Icc (b + δ + h + 1) (centralK a b δ), (1 : ℕ) =
        centralK a b δ + 1 - (b + δ + h + 1) := by simp
    have hprod : (∏ j ∈ Finset.Icc (b + δ + h + 1) (centralK a b δ),
        (polyX + C (j : ℤ))).natDegree ≤ centralK a b δ + 1 - (b + δ + h + 1) :=
      le_trans (natDegree_prod_le _ _) (le_trans (Finset.sum_le_sum hlin) hsum.le)
    have hdesc : (C ((-1) ^ h * ((a - b).choose (δ + 2 * h) : ℤ)) *
        descPochhammer ℤ h).natDegree ≤ h :=
      (natDegree_C_mul_le _ _).trans (descPochhammer_natDegree (R := ℤ) h).le
    have hK := centralK_eq a b δ
    refine natDegree_mul_le.trans ((add_le_add hdesc hprod).trans ?_)
    omega
  rw [centralA_eq]
  refine natDegree_mul_le.trans ((add_le_add h1 (natDegree_sum_le_of_forall_le _ _ h2)).trans ?_)
  exact le_of_eq (centralK_eq a b δ).symm

/-- `deg C_δ ≤ K_{1-δ}`. -/
theorem natDegree_oppositeNumerator_le (a b δ : ℕ) :
    (oppositeNumerator a b δ).natDegree ≤ centralK a b (1 - δ) := by
  rw [oppositeNumerator_eq]
  refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  rw [Finset.mem_range] at hi
  refine (natDegree_C_mul_le _ _).trans (natDegree_pow_le.trans ?_)
  calc i * (C (2 : ℤ) * polyX + C (2 * (δ : ℤ) - 1)).natDegree ≤ i * 1 :=
        Nat.mul_le_mul_left _ natDegree_linear_le
    _ ≤ centralK a b (1 - δ) := by omega

/-- `K_0 + K_1 = s`. -/
theorem centralK_add_centralK (a b δ : ℕ) (hab : b < a) (hδ : δ ≤ 1) :
    centralK a b δ + centralK a b (1 - δ) = a + b := by
  rw [centralK_eq, centralK_eq, centralH_eq, centralH_eq]
  omega

end UnequalParameters

open UnequalParameters in
/-- **(5.27)** (§5.6): `C_δ(z) = 2^{K_{1-δ}} A_{1-δ}(z + δ - 1/2)`. -/
theorem oppositeNumerator_map (a b δ : ℕ) :
    (oppositeNumerator a b δ).map (Int.castRingHom ℚ) =
      C ((2 : ℚ) ^ centralK a b (1 - δ)) *
        ((centralA a b (1 - δ)).map (Int.castRingHom ℚ)).comp (polyX + C ((δ : ℚ) - 1 / 2)) := by
  have hdeg : ((centralA a b (1 - δ)).map (Int.castRingHom ℚ)).natDegree <
      centralK a b (1 - δ) + 1 :=
    Nat.lt_succ_of_le (natDegree_map_le.trans (natDegree_centralA_le a b (1 - δ)))
  apply Polynomial.funext
  intro r
  rw [eval_mul, eval_C, eval_comp, eval_eq_sum_range' hdeg, oppositeNumerator_eq,
    Polynomial.map_sum, eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have h2 : (2 : ℚ) ^ (centralK a b (1 - δ) - i) * 2 ^ i = 2 ^ centralK a b (1 - δ) :=
    pow_sub_mul_pow 2 (by omega)
  have hlin : (C (2 : ℤ) * polyX + C (2 * (δ : ℤ) - 1)).map (Int.castRingHom ℚ) =
      C 2 * (polyX + C ((δ : ℚ) - 1 / 2)) := by
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C,
      Polynomial.map_X]
    apply Polynomial.funext
    intro y
    simp only [eval_add, eval_mul, eval_C, eval_X, eq_intCast]
    push_cast
    ring
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, hlin, mul_pow]
  simp only [eval_mul, eval_C, eval_pow, eval_add, eval_X, coeff_map, eq_intCast]
  push_cast
  rw [← h2]
  ring

/-- `deg 𝒲_δ ≤ s` (after (5.27)). -/
theorem natDegree_galoisNumerator_le (a b δ : ℕ) (hab : b < a) (hδ : δ ≤ 1) :
    (galoisNumerator a b δ).natDegree ≤ a + b := by
  rw [galoisNumerator_eq, ← UnequalParameters.centralK_add_centralK a b δ hab hδ]
  exact natDegree_mul_le.trans (add_le_add (UnequalParameters.natDegree_centralA_le a b δ)
    (UnequalParameters.natDegree_oppositeNumerator_le a b δ))

namespace UnequalParameters

/-! ### Arithmetic of the central values -/

/-- Modulo `p`, `C_δ(z) ≡ 2^{K_{1-δ}} A_{1-δ}(w)` whenever `2w ≡ 2z + 2δ - 1`. -/
theorem intCast_oppositeNumerator_eval {p : ℕ} (a b δ z w : ℕ)
    (hzw : (2 : ZMod p) * w = 2 * z + (2 * δ - 1)) :
    (((oppositeNumerator a b δ).eval (z : ℤ) : ℤ) : ZMod p) =
      2 ^ centralK a b (1 - δ) * (((centralA a b (1 - δ)).eval (w : ℤ) : ℤ) : ZMod p) := by
  have hdeg := Nat.lt_succ_of_le (natDegree_centralA_le a b (1 - δ))
  have hlinZ : (((C (2 : ℤ) * polyX + C (2 * (δ : ℤ) - 1)).eval (z : ℤ) : ℤ) : ZMod p) =
      2 * (w : ZMod p) := by
    simp only [eval_add, eval_mul, eval_C, eval_X]
    push_cast
    linear_combination (-1 : ZMod p) * hzw
  rw [eval_eq_sum_range' hdeg, oppositeNumerator_eq, eval_finsetSum, Int.cast_sum, Int.cast_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have h2 : (2 : ZMod p) ^ (centralK a b (1 - δ) - i) * 2 ^ i = 2 ^ centralK a b (1 - δ) :=
    pow_sub_mul_pow 2 (by omega)
  rw [eval_mul, eval_C, eval_pow]
  simp only [Int.cast_mul, Int.cast_pow]
  rw [hlinZ]
  push_cast
  rw [← h2]
  ring

/-- The integral central-value identity: `F(0) D_δ(m) = (-1)^m 2^δ binom(2m,m) A_δ(m)` for the
integral numerator `F = 2^n P_n^{(a,b)}` (from (3.7)). -/
theorem coeff_zero_jacobiNum_mul (a b m δ : ℕ) (hab : b < a) (hδ : δ ≤ 1) :
    (jacobiNum a b (2 * m + δ)).coeff 0 * (centralD a b δ).eval (m : ℤ) =
      (-1) ^ m * 2 ^ δ * ((2 * m).choose m : ℤ) * (centralA a b δ).eval (m : ℤ) := by
  have h1 := jacobiP_eval_zero_eq_central a b m δ hab hδ
  have hD := (centralD_eval_pos a b δ m).ne'
  have h2 : (jacobiP a b (2 * m + δ)).eval 0 =
      (1 / 2 : ℚ) ^ (2 * m + δ) * ((jacobiNum a b (2 * m + δ)).coeff 0 : ℚ) := by
    rw [← coeff_zero_eq_eval_zero, jacobiP_eq_C_mul_map_jacobiNum, coeff_C_mul, coeff_map,
      eq_intCast]
  rw [h2, eq_div_iff hD] at h1
  have h4 : (2 : ℚ) ^ (2 * m + δ) * (1 / 2) ^ (2 * m + δ) = 1 := by
    rw [← mul_pow]; norm_num
  have h5 : (2 : ℚ) ^ (2 * m + δ) * (1 / 4) ^ m = 2 ^ δ := by
    rw [pow_add, pow_mul, mul_right_comm, ← mul_pow]; norm_num
  apply Int.cast_injective (α := ℚ)
  push_cast
  linear_combination (2 : ℚ) ^ (2 * m + δ) * h1 -
    (((jacobiNum a b (2 * m + δ)).coeff 0 : ℚ) * (((centralD a b δ).eval (m : ℤ) : ℤ) : ℚ)) * h4 +
    ((-1) ^ m * ((2 * m).choose m : ℚ) * (((centralA a b δ).eval (m : ℤ) : ℤ) : ℚ)) * h5

section Valuation

variable {p : ℕ} [hp : Fact p.Prime]

/-- Legendre's formula for `k < p²`: `v_p(k!) = ⌊k/p⌋`. -/
theorem padicValNat_factorial_eq_div {k : ℕ} (hk : k < p * p) :
    padicValNat p k.factorial = k / p := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  have hl : Nat.log p k < 2 := Nat.log_lt_of_lt_pow hk0.ne' (by rw [sq]; exact hk)
  rw [padicValNat_factorial hl]
  change ∑ i ∈ Finset.Ico 1 (1 + 1), k / p ^ i = k / p
  rw [Nat.Ico_succ_singleton, Finset.sum_singleton, pow_one]

/-- `v_p binom(N, k) + ⌊k/p⌋ + ⌊(N-k)/p⌋ = ⌊N/p⌋` for `N < p²`. -/
theorem padicValNat_choose_eq_div {N k : ℕ} (hk : k ≤ N) (hN : N < p * p) :
    padicValNat p (N.choose k) + k / p + (N - k) / p = N / p := by
  have h := congrArg (padicValNat p) (Nat.choose_mul_factorial_mul_factorial hk)
  rw [padicValNat.mul (mul_ne_zero (Nat.choose_pos hk).ne' (Nat.factorial_ne_zero _))
      (Nat.factorial_ne_zero _),
    padicValNat.mul (Nat.choose_pos hk).ne' (Nat.factorial_ne_zero _),
    padicValNat_factorial_eq_div (k := k) (lt_of_le_of_lt hk hN),
    padicValNat_factorial_eq_div (k := N - k) (lt_of_le_of_lt (Nat.sub_le N k) hN),
    padicValNat_factorial_eq_div hN] at h
  exact h

/-- `p ∥ binom(2m, m)` for `m < p ≤ 2m`. -/
theorem exists_choose_eq_mul {m : ℕ} (hmp : m < p) (hp2m : p ≤ 2 * m) :
    ∃ t : ℕ, (2 * m).choose m = p * t ∧ ¬ p ∣ t := by
  have hsq : 2 * m < p * p := by nlinarith
  have h := padicValNat_choose_eq_div (p := p) (show m ≤ 2 * m by omega) hsq
  rw [Nat.div_eq_of_lt hmp, show 2 * m - m = m by omega, Nat.div_eq_of_lt hmp,
    Nat.div_eq_of_lt_le (k := 1) (n := p) (m := 2 * m) (by omega) (by omega)] at h
  have hv : padicValNat p ((2 * m).choose m) = 1 := by omega
  have h0 : (2 * m).choose m ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hdvd : p ∣ (2 * m).choose m := by
    have := pow_padicValNat_dvd (p := p) (n := (2 * m).choose m)
    rwa [hv, pow_one] at this
  obtain ⟨t, ht⟩ := hdvd
  refine ⟨t, ht, fun ⟨u, hu⟩ => ?_⟩
  have := pow_succ_padicValNat_not_dvd (p := p) h0
  rw [hv] at this
  exact this ⟨u, by rw [ht, hu]; ring⟩

end Valuation

end UnequalParameters

/-! ### Lemma 5.16 -/

open UnequalParameters Classical in
/-- **Lemma 5.16**. Let `a > b ≥ 0`, `s = a + b`, `n = 2m + δ` with
`δ ∈ {0,1}` and `m ≥ 2s + 10`, and suppose `P_n^{(a,b)}` is irreducible over `ℚ`. If a prime `p`
satisfies `3n/4 < p ≤ 7n/8` and `p ∤ 𝒲_δ(m)`, then `Gal(P_n^{(a,b)}/ℚ) = S_n`.

Conditional on Jordan's theorem [Jones, Theorem 1.1] (`hJordan`: a primitive group containing a
cycle of prime length with at least three fixed points, here a `p`-cycle with `p ≤ n - 3`, contains
`A_n`), as in the source, on the fact that a root of an Eisenstein polynomial over `ℤ_[p]` generates
a totally ramified extension of `ℚ_[p]` of the degree of the polynomial (`hEis`, used for the wild
`p`-cycle by the source's Hensel/Eisenstein argument), and on the Jacobi discriminant formula
(5.31) ([Szego, Theorem 6.71], [DLMF, (18.16.19)]; `hdisc`). -/
theorem galoisGroupIsSymmetric_jacobiP_of_prime (hJordan : JordanPrimeCycleTheorem)
    (hEis : EisensteinPrimeTotallyRamified) (hdisc : JacobiDiscriminantFormula) {a b m δ : ℕ}
    (hab : b < a) (hδ : δ ≤ 1) (hm : 2 * (a + b) + 10 ≤ m)
    (hirr : Irreducible (jacobiP a b (2 * m + δ))) {p : ℕ} (hp : p.Prime)
    (hp1 : 3 * (2 * m + δ) < 4 * p) (hp2 : 8 * p ≤ 7 * (2 * m + δ))
    (hW : ¬ (p : ℤ) ∣ (galoisNumerator a b δ).eval (m : ℤ)) :
    GaloisGroupIsSymmetric (jacobiP a b (2 * m + δ)) := by
  have hpF : Fact p.Prime := ⟨hp⟩
  -- arithmetic
  have hpM : m + (a + b) + 2 < p := by omega
  have hp2' : p ≠ 2 := by omega
  have hp2m : p ≤ 2 * m := by omega
  have hp3 : 3 ≤ p := by omega
  have h3p : 2 * (2 * m + δ) + (a + b) < 3 * p := by omega
  have hKa : ∀ ε, ε ≤ 1 → centralK a b ε ≤ a := by
    intro ε hε; rw [centralK_eq, centralH_eq]; omega
  obtain ⟨t, ht⟩ := hp.odd_of_ne_two hp2'
  -- `j = n - p = 2k + (1 - δ)`
  obtain ⟨k, hk⟩ : ∃ k, k = m + δ - (t + 1) := ⟨_, rfl⟩
  have hj : 2 * m + δ - p = 2 * k + (1 - δ) := by omega
  have hk2 : 2 * k < p := by omega
  -- `p ∤ T`
  have hT : ¬ p ∣ ∏ i ∈ Finset.Icc 1 (a + b), (2 * m + δ + i) := by
    intro h
    obtain ⟨i, hi, hdvd⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp h
    rw [Finset.mem_Icc] at hi
    exact Nat.not_dvd_of_lt_of_lt_mul_succ (k := 1) (by omega) (by omega) hdvd
  -- the reduction `f̄ = x^p \bar{P_j}` (Lemma 3.3)
  have hred := (jacobiP_reduction (p := p) hab hδ hm hp2' hpM hT
    (fun k => jacobiP_ode (a : ℚ) b k) (ε := 1) (j := 2 * m + δ - p) le_rfl (by omega)
    (by omega)).2.1
  rw [ratReduction_jacobiP hp2', ratReduction_jacobiP hp2', one_mul, hj] at hred
  have hun : (((1 / 2 : ℚ) ^ (2 * m + δ) : ℚ) : ZMod p) ≠ 0 :=
    left_ne_zero_of_mul_eq_one (ratCast_one_div_two_pow_mul hp2' _)
  have huj : (((1 / 2 : ℚ) ^ (2 * k + (1 - δ)) : ℚ) : ZMod p) ≠ 0 :=
    left_ne_zero_of_mul_eq_one (ratCast_one_div_two_pow_mul hp2' _)
  have hcoeff : ∀ i, (((1 / 2 : ℚ) ^ (2 * m + δ) : ℚ) : ZMod p) *
      ((jacobiNum a b (2 * m + δ)).coeff i : ZMod p) =
      if p ≤ i then (((1 / 2 : ℚ) ^ (2 * k + (1 - δ)) : ℚ) : ZMod p) *
        ((jacobiNum a b (2 * k + (1 - δ))).coeff (i - p) : ZMod p) else 0 := by
    intro i
    have := congrArg (fun q : (ZMod p)[X] => q.coeff i) hred
    simp only [coeff_C_mul, coeff_map, eq_intCast, coeff_X_pow_mul'] at this
    exact this
  -- the coefficients below `x^p`
  have hlow : ∀ i < p, (p : ℤ) ∣ (jacobiNum a b (2 * m + δ)).coeff i := by
    intro i hi
    have h := hcoeff i
    rw [ite_eq_right (show ¬ p ≤ i by omega), mul_eq_zero] at h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (h.resolve_left hun)
  -- the numerators modulo `p`
  have hWZ : (((galoisNumerator a b δ).eval (m : ℤ) : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hW
  rw [galoisNumerator_eq, eval_mul, Int.cast_mul] at hWZ
  have hAm : (((centralA a b δ).eval (m : ℤ) : ℤ) : ZMod p) ≠ 0 := left_ne_zero_of_mul hWZ
  have hCm := right_ne_zero_of_mul hWZ
  have hzw : (2 : ZMod p) * k = 2 * m + (2 * δ - 1) := by
    have h := congrArg (Nat.cast : ℕ → ZMod p) (show 2 * k + p + 1 = 2 * m + 2 * δ by omega)
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, ZMod.natCast_self] at h
    linear_combination h
  rw [intCast_oppositeNumerator_eval a b δ m k hzw] at hCm
  have hAk : (((centralA a b (1 - δ)).eval (k : ℤ) : ℤ) : ZMod p) ≠ 0 :=
    right_ne_zero_of_mul hCm
  have h2ne : ∀ e : ℕ, (2 : ZMod p) ^ e ≠ 0 := fun e => by
    have := natCast_two_pow_ne_zero (p := p) hp2' e
    push_cast at this
    exact this
  have hsgn : ∀ e : ℕ, ((-1 : ZMod p)) ^ e ≠ 0 := fun e =>
    pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  -- the residual factor is a unit at zero
  have hg0 : ¬ (p : ℤ) ∣ (jacobiNum a b (2 * k + (1 - δ))).coeff 0 := by
    intro h
    have hZ := congrArg (Int.cast : ℤ → ZMod p)
      (coeff_zero_jacobiNum_mul a b k (1 - δ) hab (by omega))
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_ofNat,
      Int.cast_natCast] at hZ
    rw [(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h, zero_mul] at hZ
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (hsgn k) (h2ne _))
      (natCast_choose_ne_zero (N := 2 * k) (k := k) hk2 (by omega))) hAk hZ.symm
  have hpp : ¬ (p : ℤ) ∣ (jacobiNum a b (2 * m + δ)).coeff p := by
    intro h
    have hc := hcoeff p
    rw [ite_eq_left le_rfl, Nat.sub_self, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h,
      mul_zero] at hc
    exact hg0 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      ((mul_eq_zero.mp hc.symm).resolve_left huj))
  -- `p ∥ f(0)`
  have h0 : ¬ (p : ℤ) ^ 2 ∣ (jacobiNum a b (2 * m + δ)).coeff 0 := by
    intro h
    obtain ⟨u, hu, hpu⟩ := exists_choose_eq_mul (p := p) (m := m) (by omega) hp2m
    have hid := coeff_zero_jacobiNum_mul a b m δ hab hδ
    rw [hu] at hid
    have hdvd : (p : ℤ) * p ∣ (p : ℤ) * ((-1) ^ m * 2 ^ δ * (u : ℤ) *
        (centralA a b δ).eval (m : ℤ)) := by
      have := dvd_mul_of_dvd_left h ((centralD a b δ).eval (m : ℤ))
      rw [hid, sq] at this
      convert this using 1
      push_cast; ring
    rw [mul_dvd_mul_iff_left (Nat.cast_ne_zero.mpr hp.ne_zero : (p : ℤ) ≠ 0)] at hdvd
    have hZ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_ofNat,
      Int.cast_natCast] at hZ
    have hu0 : (u : ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hpu
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (hsgn m) (h2ne δ)) hu0) hAm hZ
  -- the leading coefficient is a unit
  have hlc : ¬ (p : ℤ) ∣ (jacobiNum a b (2 * m + δ)).leadingCoeff := by
    rw [leadingCoeff, natDegree_jacobiNum, coeff_jacobiNum_self]
    intro h
    have h' : p ∣ (2 * (2 * m + δ) + a + b).choose (2 * m + δ) := by exact_mod_cast h
    have hv := padicValNat_choose_eq_div (p := p) (N := 2 * (2 * m + δ) + a + b)
      (k := 2 * m + δ) (by omega) (by nlinarith)
    rw [Nat.div_eq_of_lt_le (k := 2) (n := p) (m := 2 * (2 * m + δ) + a + b) (by omega)
        (by omega),
      Nat.div_eq_of_lt_le (k := 1) (n := p) (m := 2 * m + δ) (by omega) (by omega),
      show 2 * (2 * m + δ) + a + b - (2 * m + δ) = 2 * m + δ + (a + b) by omega,
      Nat.div_eq_of_lt_le (k := 1) (n := p) (m := 2 * m + δ + (a + b)) (by omega)
        (by omega)] at hv
    exact ((dvd_iff_padicValNat_ne_zero (Nat.choose_pos (by omega)).ne').mp h') (by omega)
  -- the wild `p`-cycle
  have hc : ((1 / 2 : ℚ) ^ (2 * m + δ)) ≠ 0 := by positivity
  have hdegZ : (jacobiNum a b (2 * m + δ)).natDegree < 2 * p := by
    rw [natDegree_jacobiNum]; omega
  obtain ⟨σ, hσcyc, hσcard⟩ := SourceWild.exists_isCycle_galPerm_of_wild_source hEis hp hc
    (jacobiP_eq_C_mul_map_jacobiNum a b (2 * m + δ)) hdegZ hlc hlow h0 hpp
  -- the group
  have hfdeg : (jacobiP a b (2 * m + δ)).natDegree = 2 * m + δ := by
    rw [jacobiP_eq_C_mul_map_jacobiNum, natDegree_C_mul hc,
      natDegree_map_eq_of_injective (RingHom.injective_int _), natDegree_jacobiNum]
  have hcardα : Fintype.card ((jacobiP a b (2 * m + δ)).rootSet
      (jacobiP a b (2 * m + δ)).SplittingField) = 2 * m + δ := by
    rw [card_rootSet_of_irreducible hirr, hfdeg]
  have htrans := isPretransitive_range_galPerm hirr
  have hσG : galPerm (jacobiP a b (2 * m + δ)) σ ∈ (galPerm (jacobiP a b (2 * m + δ))).range :=
    MonoidHom.mem_range.mpr ⟨σ, rfl⟩
  have hσcard' : (galPerm (jacobiP a b (2 * m + δ)) σ).support.card = p := by convert hσcard
  -- primitivity: the counting argument of the manuscript with `n < 2p`
  have hprim : MulAction.IsPreprimitive (galPerm (jacobiP a b (2 * m + δ))).range
      ((jacobiP a b (2 * m + δ)).rootSet (jacobiP a b (2 * m + δ)).SplittingField) := by
    have := htrans
    exact isPreprimitive_of_prime_cycle hp hσG hσcyc hσcard' (by rw [hcardα]; omega)
  have hA : alternatingGroup ((jacobiP a b (2 * m + δ)).rootSet
      (jacobiP a b (2 * m + δ)).SplittingField) ≤ (galPerm (jacobiP a b (2 * m + δ))).range :=
    hJordan _ _ hprim _ hσG hσcyc (by rw [hσcard']; exact hp) (by rw [hcardα, hσcard']; omega)
  -- an odd permutation from the discriminant
  have hv := padicValRat_jacobiDiscriminant (p := p) (a := a) (b := b) (n := 2 * m + δ)
    (by omega) (by omega) (by omega) (by omega)
  have hodd : Odd (padicValRat p (jacobiDiscriminant a b (2 * m + δ))) := by
    rw [hv]; exact (Int.odd_coe_nat p).mpr ⟨t, ht⟩
  obtain ⟨τ, hτ⟩ := exists_sign_galPerm_eq_neg_one hdisc a b (2 * m + δ) hirr.separable hfdeg
    hodd
  rw [galoisGroupIsSymmetric_iff_range_eq_top, eq_top_iff]
  intro π _
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h
  · exact hA (Equiv.Perm.mem_alternatingGroup.mpr h)
  · have hτG : galPerm (jacobiP a b (2 * m + δ)) τ ∈ (galPerm (jacobiP a b (2 * m + δ))).range :=
      MonoidHom.mem_range.mpr ⟨τ, rfl⟩
    have hπτ : π * (galPerm (jacobiP a b (2 * m + δ)) τ)⁻¹ ∈
        (galPerm (jacobiP a b (2 * m + δ))).range :=
      hA (Equiv.Perm.mem_alternatingGroup.mpr (by rw [map_mul, map_inv, h, hτ]; rfl))
    simpa using (galPerm (jacobiP a b (2 * m + δ))).range.mul_mem hπτ hτG

open UnequalParameters in
/-- The discriminant valuation of Lemma 5.16, recorded for the fixed-field assertion of
Theorem 1.3: under the prime conditions of Lemma 5.16, `v_p(jacobiDiscriminant a b n) = p`
(`jacobiDiscriminant a b n` is the discriminant of `P_n^{(a,b)}` by (5.31)). -/
theorem padicValRat_jacobiDiscriminant_of_galois_prime {a b m δ : ℕ}
    (hm : 2 * (a + b) + 10 ≤ m) {p : ℕ} (hp : p.Prime)
    (hp1 : 3 * (2 * m + δ) < 4 * p) (hp2 : 8 * p ≤ 7 * (2 * m + δ)) :
    padicValRat p (jacobiDiscriminant a b (2 * m + δ)) = p := by
  have : Fact p.Prime := ⟨hp⟩
  exact padicValRat_jacobiDiscriminant (by omega) (by omega) (by omega) (by omega)

/-! ### Proposition 5.17 -/

namespace UnequalParameters

theorem five_le_log {x : ℝ} (hx : 3594641 < x) : 5 ≤ Real.log x := by
  have he : Real.exp 1 ^ 5 = Real.exp 5 := by rw [Real.exp_one_pow]; norm_num
  have h1 : Real.exp 5 < 3594641 := by
    rw [← he]
    have := Real.exp_one_lt_d9
    have h0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
    calc Real.exp 1 ^ 5 < 2.7182818286 ^ 5 := by gcongr
      _ < 3594641 := by norm_num
  rw [← Real.log_exp 5]
  exact Real.log_le_log (Real.exp_pos 5) (by linarith)

/-- Consequences of Dusart's bound: `0.992 x < θ(x) < 1.008 x` for `x > 3 594 641`. -/
theorem theta_bounds (hDusart : DusartThetaBound) {x : ℝ} (hx : 3594641 < x) :
    0.992 * x < Chebyshev.theta x ∧ Chebyshev.theta x < 1.008 * x := by
  have hL := five_le_log hx
  have hx0 : 0 < x := by linarith
  have hL2 : 25 ≤ Real.log x ^ 2 := by nlinarith
  have hb : 0.2 * x / Real.log x ^ 2 ≤ 0.2 * x / 25 :=
    div_le_div_of_nonneg_left (by linarith) (by norm_num) hL2
  have h := abs_lt.mp (hDusart x hx.le)
  constructor <;> linarith [h.1, h.2]

/-- If every prime `B < q ≤ A` divides `W ≠ 0`, the sum of their logarithms is at most
`log |W|`; stated for any `g` vanishing off the primes and equal to `log` on them. -/
theorem sum_sub_sum_le (g : ℕ → ℝ) {A B : ℕ} (hBA : B ≤ A) {W : ℤ} (hW : W ≠ 0)
    (hg : ∀ q, g q = 0 ∨ (q.Prime ∧ g q = Real.log q))
    (hdvd : ∀ q, B < q → q ≤ A → q.Prime → (q : ℤ) ∣ W) :
    ∑ q ∈ Finset.Icc 0 A, g q - ∑ q ∈ Finset.Icc 0 B, g q ≤ Real.log |(W : ℝ)| := by
  classical
  have hsub : Finset.Icc 0 B ⊆ Finset.Icc 0 A := Finset.Icc_subset_Icc le_rfl hBA
  rw [← Finset.sum_sdiff_eq_sub hsub]
  have hTmem : ∀ q ∈ Finset.Icc 0 A \ Finset.Icc 0 B, B < q ∧ q ≤ A := by
    intro q hq
    rw [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Icc] at hq
    omega
  have h1 : ∑ q ∈ Finset.Icc 0 A \ Finset.Icc 0 B, g q ≤
      ∑ q ∈ (Finset.Icc 0 A \ Finset.Icc 0 B).filter Nat.Prime, Real.log q := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun q _ => ?_
    rcases hg q with h | ⟨hq, h⟩
    · rw [h]
      split_ifs
      · exact Real.log_natCast_nonneg q
      · exact le_rfl
    · rw [h, ite_eq_left hq]
  have hmem : ∀ q ∈ (Finset.Icc 0 A \ Finset.Icc 0 B).filter Nat.Prime,
      q.Prime ∧ (q : ℤ) ∣ W := by
    intro q hq
    rw [Finset.mem_filter] at hq
    obtain ⟨h1, h2⟩ := hTmem q hq.1
    exact ⟨hq.2, hdvd q h1 h2 hq.2⟩
  have hdvdP : ∏ q ∈ (Finset.Icc 0 A \ Finset.Icc 0 B).filter Nat.Prime, q ∣ W.natAbs :=
    Finset.prod_primes_dvd _ (fun q hq => (hmem q hq).1.prime)
      (fun q hq => Int.natCast_dvd.mp (hmem q hq).2)
  have hle : (∏ q ∈ (Finset.Icc 0 A \ Finset.Icc 0 B).filter Nat.Prime, q : ℕ) ≤ W.natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hW) hdvdP
  have hpos : ∀ q ∈ (Finset.Icc 0 A \ Finset.Icc 0 B).filter Nat.Prime, (q : ℝ) ≠ 0 :=
    fun q hq => by exact_mod_cast (hmem q hq).1.ne_zero
  have habs : ((W.natAbs : ℕ) : ℝ) = |(W : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have h2 : ∑ q ∈ (Finset.Icc 0 A \ Finset.Icc 0 B).filter Nat.Prime, Real.log q ≤
      Real.log |(W : ℝ)| := by
    rw [← Real.log_prod hpos, ← habs, ← Nat.cast_prod]
    have hprod : 0 < ∏ q ∈ (Finset.Icc 0 A \ Finset.Icc 0 B).filter Nat.Prime, q :=
      Finset.prod_pos fun q hq => (hmem q hq).1.pos
    exact Real.log_le_log (by exact_mod_cast hprod) (by exact_mod_cast hle)
  linarith

/-- **The prime in the proof of Proposition 5.17.** Conditional on [Dusart10, Theorem 5.2]
(`hDusart`): if `n ≥ 5 000 000`, `W ≠ 0` and `log |W| < n/10`, some prime `p` with
`3n/4 < p ≤ 7n/8` does not divide `W`. -/
theorem exists_prime_not_dvd_of_log_lt (hDusart : DusartThetaBound) {n : ℕ}
    (hn : 5000000 ≤ n) {W : ℤ} (hW : W ≠ 0) (hlog : Real.log |(W : ℝ)| < n / 10) :
    ∃ p, p.Prime ∧ 3 * n < 4 * p ∧ 8 * p ≤ 7 * n ∧ ¬ (p : ℤ) ∣ W := by
  by_contra hcon
  push Not at hcon
  obtain ⟨g, hgx, hgy, hg⟩ : ∃ g : ℕ → ℝ,
      Chebyshev.theta (((7 * n : ℕ) : ℝ) / 8) = ∑ q ∈ Finset.Icc 0 (7 * n / 8), g q ∧
      Chebyshev.theta (((3 * n : ℕ) : ℝ) / 4) = ∑ q ∈ Finset.Icc 0 (3 * n / 4), g q ∧
      ∀ q, g q = 0 ∨ (q.Prime ∧ g q = Real.log q) := by
    refine ⟨fun q => if q.Prime then Real.log q else 0, ?_, ?_, fun q => ?_⟩
    · rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter, Nat.floor_div_ofNat, Nat.floor_natCast]
    · rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter, Nat.floor_div_ofNat, Nat.floor_natCast]
    · by_cases hq : q.Prime
      · exact Or.inr ⟨hq, ite_eq_left hq⟩
      · exact Or.inl (ite_eq_right hq)
  have key := sum_sub_sum_le g (A := 7 * n / 8) (B := 3 * n / 4) (by omega) hW hg
    (fun q h1 h2 h3 => hcon q h3 (by omega) (by omega))
  have hn' : (5000000 : ℝ) ≤ n := by exact_mod_cast hn
  have hx7 : ((7 * n : ℕ) : ℝ) = 7 * (n : ℝ) := by push_cast; ring
  have hy3 : ((3 * n : ℕ) : ℝ) = 3 * (n : ℝ) := by push_cast; ring
  have hx : (3594641 : ℝ) < ((7 * n : ℕ) : ℝ) / 8 := by rw [hx7]; linarith
  have hy : (3594641 : ℝ) < ((3 * n : ℕ) : ℝ) / 4 := by rw [hy3]; linarith
  have h1 := (theta_bounds hDusart hx).1
  have h2 := (theta_bounds hDusart hy).2
  rw [hx7] at h1
  rw [hy3] at h2
  rw [hx7] at hgx
  rw [hy3] at hgy
  linarith

end UnequalParameters

open UnequalParameters in
/-- **Proposition 5.17**. Let `a > b ≥ 0`, `s = a + b`, `n = 2m + δ`
with `δ ∈ {0,1}` and `m ≥ 2s + 10`, and suppose `P_n^{(a,b)}` is irreducible over `ℚ`. If
`n ≥ 5 000 000`, `𝒲_δ(m) ≠ 0` and `log |𝒲_δ(m)| < n/10`, then `Gal(P_n^{(a,b)}/ℚ) = S_n`.

The source assumes the hypotheses of Theorem 3.1; this form uses only their
consequence, irreducibility (`hirr`), together with `m ≥ 2s + 10` (see
`galoisGroupIsSymmetric_jacobiP_explicit_of_criterion` for the hypotheses of Theorem 3.1
themselves). Conditional on [Jones, Theorem 1.1] (`hJordan`),
[Milne, ANT v3.08, Proposition 3.53] (`hEis`), the Jacobi discriminant formula (5.31)
(`hdisc`) and [Dusart10, Theorem 5.2] (`hDusart`). -/
theorem galoisGroupIsSymmetric_jacobiP_explicit (hJordan : JordanPrimeCycleTheorem)
    (hEis : EisensteinPrimeTotallyRamified)
    (hdisc : JacobiDiscriminantFormula) (hDusart : DusartThetaBound) {a b m δ : ℕ}
    (hab : b < a) (hδ : δ ≤ 1) (hm : 2 * (a + b) + 10 ≤ m)
    (hirr : Irreducible (jacobiP a b (2 * m + δ))) (hn : 5000000 ≤ 2 * m + δ)
    (hW0 : (galoisNumerator a b δ).eval (m : ℤ) ≠ 0)
    (hWlog : Real.log |(((galoisNumerator a b δ).eval (m : ℤ) : ℤ) : ℝ)| <
      (2 * m + δ : ℝ) / 10) :
    GaloisGroupIsSymmetric (jacobiP a b (2 * m + δ)) := by
  obtain ⟨p, hp, hp1, hp2, hpW⟩ := exists_prime_not_dvd_of_log_lt hDusart hn hW0
    (by exact_mod_cast hWlog)
  exact galoisGroupIsSymmetric_jacobiP_of_prime hJordan hEis hdisc hab hδ hm hirr hp hp1 hp2 hpW

open UnequalParameters Real Finset in
/-- **Proposition 5.17**, with the hypotheses of Theorem 3.1
(Theorem 3.1, `irreducible_jacobiP_of_criterion`): let `a > b ≥ 0`, `s = a + b`,
`n = 2m + δ`, `δ ∈ {0,1}`, `m ≥ 2s + 10`, `A_δ(m) ≠ 0` and the inequality (3.5). If
`n ≥ 5 000 000`, `𝒲_δ(m) ≠ 0` and `log |𝒲_δ(m)| < n/10`, then `Gal(P_n^{(a,b)}/ℚ) = S_n`.
Conditional on the inputs of Theorem 3.1 (`hH`, `hV`, `hZ`) and those of
`galoisGroupIsSymmetric_jacobiP_explicit`. -/
theorem galoisGroupIsSymmetric_jacobiP_explicit_of_criterion (hH : HansonLcmBound)
    (hZ : JacobiSimpleRealZeros) (hJordan : JordanPrimeCycleTheorem)
    (hEis : EisensteinPrimeTotallyRamified)
    (hdisc : JacobiDiscriminantFormula) (hDusart : DusartThetaBound) {a b m δ : ℕ}
    (hab : b < a) (hδ : δ ≤ 1) (hm : 2 * (a + b) + 10 ≤ m)
    (hA : (centralA a b δ).eval (m : ℤ) ≠ 0)
    (hcrit : (((m + (a + b) + 2 : ℕ) : ℝ) + √((2 * (2 * m + δ) + (a + b) + 1 : ℕ) : ℝ)) * log 3 +
        3 * log ((∏ j ∈ Icc 1 (a + b), (2 * m + δ + j) : ℕ) : ℝ) +
        log |(((centralA a b δ).eval (m : ℤ) : ℤ) : ℝ)| +
        log (8 * ((m : ℝ) + 1) * ((2 * (2 * m + δ) + (a + b) + 1 : ℕ) : ℝ) *
          ((2 * m + δ + a).choose a : ℝ) * (((centralD a b δ).eval (m : ℤ) : ℤ) : ℝ) /
            (asymmetricEnergyConstant a b * √(m : ℝ))) <
      ((2 * m + δ : ℕ) : ℝ) * log 2)
    (hn : 5000000 ≤ 2 * m + δ) (hW0 : (galoisNumerator a b δ).eval (m : ℤ) ≠ 0)
    (hWlog : Real.log |(((galoisNumerator a b δ).eval (m : ℤ) : ℤ) : ℝ)| <
      (2 * m + δ : ℝ) / 10) :
    GaloisGroupIsSymmetric (jacobiP a b (2 * m + δ)) :=
  galoisGroupIsSymmetric_jacobiP_explicit hJordan hEis hdisc hDusart hab hδ hm
    (irreducible_jacobiP_of_criterion hH hZ hab hδ hm hA hcrit) hn hW0 hWlog

end ArithmeticOfJacobiPolynomials
