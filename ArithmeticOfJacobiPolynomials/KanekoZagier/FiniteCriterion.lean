/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.KanekoZagier.ArithmeticAsymptotics
public import ArithmeticOfJacobiPolynomials.KanekoZagier.PrimitiveIrreducibility
public import ArithmeticOfJacobiPolynomials.KanekoZagier.FiniteRangeQuantities
public import ArithmeticOfJacobiPolynomials.KanekoZagier.Archimedean
public import ArithmeticOfJacobiPolynomials.Galois.GaloisBridge
public import ArithmeticOfJacobiPolynomials.MainResults
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Proposition 4.8: the exact finite criterion

For `λ, μ ∈ {-1, 1}` (the argument `l` is `λ`), `y_n(t) = P_n^{(λ/3, μ/2)}(1 - 2t)`
(`jacobiShifted`) and `H_n = (κ_n / g_n) y_n` (`kzPrimitive`), Section 4.5 of the manuscript uses
the quantities (4.16) and (§4.4):

* `D_{2,n} = n + ∑_{j=1}^n v_2(3j + λ)` (`kzEndpointTwo`), `D_{3,n} = n + ∑_{j=1}^n v_3(2j + μ)`
  (`kzEndpointThree`), `T_{p,n} = D_{p,n} log p / n` (`kzT2`, `kzT3`);
* `L_n = log(e^{T_{2,n}} + e^{T_{3,n}})` (`kzL`), `E = (1/2) log 2 + (1/3) log 3` (`kzE`),
  `J_n = (1/2) s_2(n) log 2 + (1/6) s_3(2n + δ) log 3`, `δ = (μ + 1)/2` (`kzJ`, `kzDelta`);
* `γ_n = κ_n / g_n` (`kzGamma`) and the Wronskian constant `C_n`
  (`jacobiWronskianConstant (λ/3) (μ/2) n`);
* `S_n = ∑_{5 ≤ p ≤ n} E_p(n) log p` (`kzGoodPrimeSum`, with Lemma 4.2's budget `E_p(n)`,
  `kzBudget`), and the function (§4.5)
  `ℋ_n(z) = log(2 γ_n √C_n) - J_n + (n - 2z) L_n - (n - z)(T_{2,n} + T_{3,n} + E)
    + 2(z-1)²/z · log 2 - log z` (`kzCriterionFn`).

The exact archimedean inequality (4.17) of Proposition 4.7 (§4.4),
`log R^{(6)} / k ≥ ℋ_n(k)` for every factorization `H_n = A B` with `1 ≤ k = deg A ≤ n/2`, is
recorded as the statement `KanekoZagierArchimedeanBound l μ n`.
`kanekoZagierArchimedeanBound_holds` derives it for every `n` from Proposition 4.7
(`kanekoZagier_arch_resultant`, `ArithmeticOfJacobiPolynomials.KanekoZagier.Archimedean`) and Lemma
4.1; it is
conditional on `JacobiSimpleRealZeros` [DLMF, §18.2(vi)] and `NewtonPolygonRootSlopes`
[Berger, Theorem 2.4].

## Main results

* `irreducible_jacobiShifted_of_finite_criterion` — **Proposition 4.8**: for `n ≥ 11`, given
  (4.17) at `n`, if `ℋ_n(k) > S_n` for every `k` in a set `K` containing the degree of every
  factor `f ∣ y_n` with `1 ≤ deg f ≤ n/2`, then `y_n` is irreducible over `ℚ`.
* `irreducible_kanekoZagierJacobi_of_finite_criterion` — the case `K = ℕ`
  (`min_{1 ≤ k ≤ ⌊n/2⌋} ℋ_n(k) > S_n`), for `P_n^{(λ/3, μ/2)}` itself.
* `irreducible_kanekoZagierJacobi_of_finite_criterion'` — the same with (4.17) discharged by
  `kanekoZagierArchimedeanBound_holds` (hypotheses: `JacobiSimpleRealZeros` and
  `NewtonPolygonRootSlopes` only).
* `irreducible_kanekoZagierJacobi_iff_jacobiShifted` — `P_n` and `y_n` are irreducible together.

The proof combines (4.17) with the good-prime bound `log R^{(6)} ≤ k S_n`
(`log_primeToSixPart_le`, Lemma 4.4).
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset

/-- `T_{2,n} = D_{2,n} log 2 / n`. -/
noncomputable def kzT2 (l : ℤ) (n : ℕ) : ℝ := kzEndpointTwo l n * Real.log 2 / n

theorem kzT2_eq (l : ℤ) (n : ℕ) : kzT2 l n = kzEndpointTwo l n * Real.log 2 / n := (rfl)

/-- `T_{3,n} = D_{3,n} log 3 / n`. -/
noncomputable def kzT3 (μ : ℤ) (n : ℕ) : ℝ := kzEndpointThree μ n * Real.log 3 / n

theorem kzT3_eq (μ : ℤ) (n : ℕ) : kzT3 μ n = kzEndpointThree μ n * Real.log 3 / n := (rfl)

/-- `L_n = log(e^{T_{2,n}} + e^{T_{3,n}})`. -/
noncomputable def kzL (l μ : ℤ) (n : ℕ) : ℝ :=
  Real.log (Real.exp (kzT2 l n) + Real.exp (kzT3 μ n))

theorem kzL_eq (l μ : ℤ) (n : ℕ) :
    kzL l μ n = Real.log (Real.exp (kzT2 l n) + Real.exp (kzT3 μ n)) := (rfl)

/-- `E = (1/2) log 2 + (1/3) log 3`. -/
noncomputable def kzE : ℝ := Real.log 2 / 2 + Real.log 3 / 3

theorem kzE_eq : kzE = Real.log 2 / 2 + Real.log 3 / 3 := (rfl)

/-- `J_n = (1/2) s_2(n) log 2 + (1/6) s_3(2n + δ) log 3`. -/
noncomputable def kzJ (μ : ℤ) (n : ℕ) : ℝ :=
  ((Nat.digits 2 n).sum : ℝ) * Real.log 2 / 2 +
    ((Nat.digits 3 (2 * n + kzDelta μ)).sum : ℝ) * Real.log 3 / 6

theorem kzJ_eq (μ : ℤ) (n : ℕ) : kzJ μ n =
    ((Nat.digits 2 n).sum : ℝ) * Real.log 2 / 2 +
      ((Nat.digits 3 (2 * n + kzDelta μ)).sum : ℝ) * Real.log 3 / 6 := (rfl)

/-- `γ_n = κ_n / g_n`. -/
noncomputable def kzGamma (l μ : ℤ) (n : ℕ) : ℝ := (kzKappa n : ℝ) / kzContent l μ n

theorem kzGamma_eq (l μ : ℤ) (n : ℕ) : kzGamma l μ n = (kzKappa n : ℝ) / kzContent l μ n :=
  (rfl)

/-- The function `ℋ_n(z)` of (§4.5):
`log(2 γ_n √C_n) - J_n + (n - 2z) L_n - (n - z)(T_{2,n} + T_{3,n} + E)
  + 2(z-1)²/z · log 2 - log z`. -/
noncomputable def kzCriterionFn (l μ : ℤ) (n : ℕ) (z : ℝ) : ℝ :=
  Real.log (2 * kzGamma l μ n *
      √((jacobiWronskianConstant ((l : ℚ) / 3) ((μ : ℚ) / 2) n : ℚ) : ℝ)) - kzJ μ n +
    (n - 2 * z) * kzL l μ n - (n - z) * (kzT2 l n + kzT3 μ n + kzE) +
    2 * (z - 1) ^ 2 / z * Real.log 2 - Real.log z

theorem kzCriterionFn_eq (l μ : ℤ) (n : ℕ) (z : ℝ) : kzCriterionFn l μ n z =
    Real.log (2 * kzGamma l μ n *
        √((jacobiWronskianConstant ((l : ℚ) / 3) ((μ : ℚ) / 2) n : ℚ) : ℝ)) - kzJ μ n +
      (n - 2 * z) * kzL l μ n - (n - z) * (kzT2 l n + kzT3 μ n + kzE) +
      2 * (z - 1) ^ 2 / z * Real.log 2 - Real.log z := (rfl)

/-- `S_n = ∑_{5 ≤ p ≤ n, p prime} E_p(n) log p`. -/
noncomputable def kzGoodPrimeSum (l μ : ℤ) (n : ℕ) : ℝ :=
  ∑ p ∈ (Icc 5 n).filter Nat.Prime, (kzBudget l μ n p : ℝ) * Real.log p

theorem kzGoodPrimeSum_eq (l μ : ℤ) (n : ℕ) : kzGoodPrimeSum l μ n =
    ∑ p ∈ (Icc 5 n).filter Nat.Prime, (kzBudget l μ n p : ℝ) * Real.log p := (rfl)

/-- **The exact archimedean inequality (4.17)** of Proposition 4.7 (§4.4)
at degree `n`, as a statement: for every factorization `H_n = A B` in `ℤ[t]` with
`1 ≤ k = deg A ≤ n/2`, `log R^{(6)} / k ≥ ℋ_n(k)`, where `R = |Res(A, B)|`. -/
@[expose] def KanekoZagierArchimedeanBound (l μ : ℤ) (n : ℕ) : Prop :=
  ∀ A B : ℤ[X], kzPrimitive l μ n = A * B → 1 ≤ A.natDegree → 2 * A.natDegree ≤ n →
    kzCriterionFn l μ n A.natDegree ≤
      Real.log (primeToSixPart (resultant A B)) / A.natDegree

/-! ### Proposition 4.7 (4.17) for `H_n` -/

/-- `R^{(6)} = |R| / (2^{v_2 R} 3^{v_3 R})` as a real number. -/
theorem primeToSixPart_cast (r : ℤ) : (primeToSixPart r : ℝ) =
    |(r : ℝ)| / (2 ^ padicValInt 2 r * 3 ^ padicValInt 3 r) := by
  change _ = |(r : ℝ)| / (2 ^ padicValNat 2 r.natAbs * 3 ^ padicValNat 3 r.natAbs)
  rw [primeToSixPart_eq, Nat.cast_div (two_three_pow_dvd r.natAbs) (by positivity)]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_natAbs, Int.cast_abs]

theorem padicValRat_kzGamma_two {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    (n : ℕ) : padicValRat 2 ((kzKappa n : ℚ) / kzContent l μ n) =
      n + padicValNat 2 n.factorial := by
  have hκ : (kzKappa n : ℚ) ≠ 0 := by exact_mod_cast (kzKappa_pos n).ne'
  have hg : (kzContent l μ n : ℚ) ≠ 0 := by exact_mod_cast (kzContent_pos hl hμ n).ne'
  have hcop := coprime_kzContent_six hl hμ n
  have hg2 : padicValNat 2 (kzContent l μ n) = 0 := padicValNat.eq_zero_of_not_dvd fun h => by
    have := Nat.dvd_gcd h (by norm_num : 2 ∣ 6)
    rw [Nat.Coprime.gcd_eq_one hcop] at this
    omega
  have h22 : padicValRat 2 (2 : ℚ) = 1 := by
    have := padicValRat.self (p := 2) (by norm_num)
    exact_mod_cast this
  have h23 : padicValRat 2 (3 : ℚ) = 0 := by
    have : padicValRat 2 ((3 : ℕ) : ℚ) = 0 := by
      rw [padicValRat.of_nat, padicValNat_primes (p := 2) (q := 3) (by norm_num), Nat.cast_zero]
    exact_mod_cast this
  rw [padicValRat.div hκ hg, padicValRat_kzKappa 2 n, padicValRat.of_nat, hg2, h22, h23]
  push_cast
  ring

theorem padicValRat_kzGamma_three {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    (n : ℕ) : padicValRat 3 ((kzKappa n : ℚ) / kzContent l μ n) =
      n + padicValNat 3 n.factorial := by
  have hκ : (kzKappa n : ℚ) ≠ 0 := by exact_mod_cast (kzKappa_pos n).ne'
  have hg : (kzContent l μ n : ℚ) ≠ 0 := by exact_mod_cast (kzContent_pos hl hμ n).ne'
  have hcop := coprime_kzContent_six hl hμ n
  have hg3 : padicValNat 3 (kzContent l μ n) = 0 := padicValNat.eq_zero_of_not_dvd fun h => by
    have := Nat.dvd_gcd h (by norm_num : 3 ∣ 6)
    rw [Nat.Coprime.gcd_eq_one hcop] at this
    omega
  have h33 : padicValRat 3 (3 : ℚ) = 1 := by
    have := padicValRat.self (p := 3) (by norm_num)
    exact_mod_cast this
  have h32 : padicValRat 3 (2 : ℚ) = 0 := by
    have : padicValRat 3 ((2 : ℕ) : ℚ) = 0 := by
      rw [padicValRat.of_nat, padicValNat_primes (p := 3) (q := 2) (by norm_num), Nat.cast_zero]
    exact_mod_cast this
  rw [padicValRat.div hκ hg, padicValRat_kzKappa 3 n, padicValRat.of_nat, hg3, h33, h32]
  push_cast
  ring

/-- **Proposition 4.7, exact form (4.17), for `H_n`**: the statement
`KanekoZagierArchimedeanBound l μ n` holds for every `n`, given the proved interval Vandermonde
bound (Lemma 2.5, `intervalVandermondeBound`) and the simplicity and location of the Jacobi
zeros [DLMF, §18.2(vi)].
This specializes `kanekoZagier_arch_resultant` to `H = H_n`, `γ = γ_n = κ_n / g_n`, using
Lemma 4.1 (`v_p(γ_n) = n + v_p(n!)` for `p = 2, 3`, and `gcd(lc H_n, 6) = 1`). -/
theorem kanekoZagierArchimedeanBound_holds (hZ : JacobiSimpleRealZeros)
    (hNP : NewtonPolygonRootSlopes) {l μ : ℤ} (hl : l = 1 ∨ l =
    -1) (hμ : μ = 1 ∨ μ = -1)
    (n : ℕ) : KanekoZagierArchimedeanBound l μ n := by
  intro A B hAB hk hk2
  obtain ⟨δ, hδ, hμδ, hdel⟩ : ∃ δ : ℕ, δ ≤ 1 ∧ μ = 2 * δ - 1 ∧ kzDelta μ = δ := by
    rcases hμ with rfl | rfl
    · exact ⟨1, le_rfl, by norm_num, by rw [kzDelta_eq]; decide⟩
    · exact ⟨0, zero_le_one, by norm_num, by rw [kzDelta_eq]; decide⟩
  have hκ : (0 : ℚ) < kzKappa n := by exact_mod_cast kzKappa_pos n
  have hg : (0 : ℚ) < kzContent l μ n := by exact_mod_cast kzContent_pos hl hμ n
  have hlc := isCoprime_leadingCoeff_kzPrimitive_six hl hμ n
  have hlc2 : ¬ (2 : ℤ) ∣ (kzPrimitive l μ n).leadingCoeff := fun h => by
    have := Int.isUnit_iff.mp (hlc.isUnit_of_dvd' h (by norm_num))
    omega
  have hlc3 : ¬ (3 : ℤ) ∣ (kzPrimitive l μ n).leadingCoeff := fun h => by
    have := Int.isUnit_iff.mp (hlc.isUnit_of_dvd' h (by norm_num))
    omega
  have key := kanekoZagier_arch_resultant hZ hNP hl hδ hμδ (div_pos hκ hg)
    (padicValRat_kzGamma_two hl hμ n) (padicValRat_kzGamma_three hl hμ n)
    (map_kzPrimitive hl hμ n) hlc2 hlc3 hAB hk hk2 rfl rfl rfl rfl rfl
  refine Eq.trans_le ?_ (key.trans_eq ?_)
  · rw [kzCriterionFn_eq, kzGamma_eq, kzJ_eq, kzL_eq, kzT2_eq, kzT3_eq, kzEndpointTwo_eq,
      kzEndpointThree_eq, kzE_eq, hdel, digitSum3_eq]
    push_cast
    ring
  · rw [primeToSixPart_cast]

/-! ### Auxiliary facts -/

/-- `R^{(6)}` is symmetric in the two factors. -/
theorem primeToSixPart_resultant_comm (A B : ℤ[X]) :
    primeToSixPart (resultant B A) = primeToSixPart (resultant A B) := by
  have h : (resultant B A).natAbs = (resultant A B).natAbs := by
    rw [resultant_comm (f := B) (g := A), Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg,
      Int.natAbs_one, one_pow, one_mul]
  rw [primeToSixPart_eq, primeToSixPart_eq, h]

/-- A primitive integer polynomial of degree zero is a unit. -/
theorem isUnit_of_isPrimitive_of_natDegree_eq_zero {A : ℤ[X]} (hA : A.IsPrimitive)
    (h0 : A.natDegree = 0) : IsUnit A := by
  have hAC := eq_C_of_natDegree_eq_zero h0
  have hu : IsUnit (A.coeff 0) :=
    isPrimitive_iff_isUnit_of_C_dvd.mp hA _ ⟨1, by rw [mul_one]; exact hAC⟩
  rw [hAC]
  exact isUnit_C.mpr hu

/-- `y_n` and `P_n^{(λ/3, μ/2)}` are irreducible together (`y_n(t) = P_n(1 - 2t)`). -/
theorem irreducible_kanekoZagierJacobi_iff_jacobiShifted (l μ : ℤ) (n : ℕ) :
    Irreducible (kanekoZagierJacobi l μ n) ↔
      Irreducible (jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n) := by
  have h12 : (1 - 2 * polyX : ℚ[X]) = C (-2) * polyX + 1 := by
    rw [map_neg, C_ofNat]; ring
  have key := irreducible_C_mul_comp_affine_iff (f := kanekoZagierJacobi l μ n) (c := (1 : ℚ))
    (one_ne_zero) (show (-2 : ℚ) ≠ 0 by norm_num)
  rw [C_1, one_mul, ← h12] at key
  rw [← key, jacobiShifted_eq, kanekoZagierJacobi_eq]

/-- The core of Proposition 4.8: under (4.17) at `n ≥ 11`, every factorization `H_n = A B` with
`1 ≤ deg A ≤ n/2` satisfies `ℋ_n(deg A) ≤ S_n`. -/
theorem kzCriterionFn_le_kzGoodPrimeSum {l μ : ℤ} (hl : l = 1 ∨ l = -1)
    (hμ : μ = 1 ∨ μ = -1) {n : ℕ} (hn : 11 ≤ n) (harch : KanekoZagierArchimedeanBound l μ n)
    {A B : ℤ[X]} (hAB : kzPrimitive l μ n = A * B) (hk : 1 ≤ A.natDegree)
    (hk2 : 2 * A.natDegree ≤ n) :
    kzCriterionFn l μ n A.natDegree ≤ kzGoodPrimeSum l μ n := by
  have h1 := harch A B hAB hk hk2
  have h2 := log_primeToSixPart_le hl hμ hn hAB
  have hkpos : (0 : ℝ) < A.natDegree := by exact_mod_cast hk
  rw [← kzGoodPrimeSum_eq] at h2
  calc kzCriterionFn l μ n A.natDegree
      ≤ Real.log (primeToSixPart (resultant A B)) / A.natDegree := h1
    _ ≤ kzGoodPrimeSum l μ n := by rw [div_le_iff₀ hkpos, mul_comm]; exact h2

/-! ### Proposition 4.8 -/

/-- **Proposition 4.8.** Let `n ≥ 11`, and assume the exact
archimedean inequality (4.17) of Proposition 4.7 at `n`. Let `K` be a set containing the degree
of every factor `f` of `y_n` over `ℚ` with `1 ≤ deg f ≤ n/2`. If `ℋ_n(k) > S_n` for every
`k ∈ K` with `1 ≤ k ≤ n/2`, then `y_n` is irreducible over `ℚ`. -/
theorem irreducible_jacobiShifted_of_finite_criterion {l μ : ℤ} (hl : l = 1 ∨ l = -1)
    (hμ : μ = 1 ∨ μ = -1) {n : ℕ} (hn : 11 ≤ n) (harch : KanekoZagierArchimedeanBound l μ n)
    (K : Set ℕ)
    (hK : ∀ f : ℚ[X], f ∣ jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n → 1 ≤ f.natDegree →
      2 * f.natDegree ≤ n → f.natDegree ∈ K)
    (hcrit : ∀ k ∈ K, 1 ≤ k → 2 * k ≤ n → kzGoodPrimeSum l μ n < kzCriterionFn l μ n k) :
    Irreducible (jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n) := by
  have hκ : (kzKappa n : ℚ) ≠ 0 := by exact_mod_cast (kzKappa_pos n).ne'
  have hg : (kzContent l μ n : ℚ) ≠ 0 := by exact_mod_cast (kzContent_pos hl hμ n).ne'
  have hc : (kzKappa n : ℚ) / kzContent l μ n ≠ 0 := div_ne_zero hκ hg
  have hmap := map_kzPrimitive hl hμ n
  have hprim := isPrimitive_kzPrimitive hl hμ n
  have hdeg := natDegree_kzPrimitive hl hμ n
  rw [← irreducible_isUnit_mul (isUnit_C.mpr (Ne.isUnit hc)), ← hmap,
    ← IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim]
  refine irreducible_iff.mpr ⟨fun hu => ?_, ?_⟩
  · have := natDegree_eq_zero_of_isUnit hu
    omega
  intro A B hAB
  by_contra hnot
  obtain ⟨hA, hB⟩ := not_or.mp hnot
  have hApr : A.IsPrimitive := isPrimitive_of_dvd hprim ⟨B, hAB⟩
  have hBpr : B.IsPrimitive := isPrimitive_of_dvd hprim ⟨A, by rw [hAB, mul_comm]⟩
  have hA1 : 1 ≤ A.natDegree := by
    by_contra h
    exact hA (isUnit_of_isPrimitive_of_natDegree_eq_zero hApr (by omega))
  have hB1 : 1 ≤ B.natDegree := by
    by_contra h
    exact hB (isUnit_of_isPrimitive_of_natDegree_eq_zero hBpr (by omega))
  have hsum : A.natDegree + B.natDegree = n := by
    rw [← hdeg, hAB, natDegree_mul hApr.ne_zero hBpr.ne_zero]
  -- a factor of `H_n` gives a factor of `y_n` of the same degree
  have hfac : ∀ F G : ℤ[X], kzPrimitive l μ n = F * G →
      F.map (Int.castRingHom ℚ) ∣ jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n ∧
        (F.map (Int.castRingHom ℚ)).natDegree = F.natDegree := by
    intro F G hFG
    refine ⟨?_, natDegree_map_eq_of_injective (RingHom.injective_int _) F⟩
    have h := hmap
    rw [hFG, Polynomial.map_mul] at h
    refine ⟨C ((kzKappa n : ℚ) / kzContent l μ n)⁻¹ * G.map (Int.castRingHom ℚ), ?_⟩
    calc jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n
        = C ((kzKappa n : ℚ) / kzContent l μ n)⁻¹ * (C ((kzKappa n : ℚ) / kzContent l μ n) *
            jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n) := by
          rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hc, C_1, one_mul]
      _ = _ := by rw [← h]; ring
  -- the factor of smaller degree
  have key : ∀ F G : ℤ[X], kzPrimitive l μ n = F * G → 1 ≤ F.natDegree →
      2 * F.natDegree ≤ n → False := by
    intro F G hFG hF1 hF2
    obtain ⟨hdvd, hFdeg⟩ := hfac F G hFG
    have hKmem := hK _ hdvd (by rw [hFdeg]; exact hF1) (by rw [hFdeg]; exact hF2)
    rw [hFdeg] at hKmem
    have hlt := hcrit _ hKmem hF1 hF2
    have hle := kzCriterionFn_le_kzGoodPrimeSum hl hμ hn harch hFG hF1 hF2
    linarith
  rcases le_total A.natDegree B.natDegree with hle | hle
  · exact key A B hAB hA1 (by omega)
  · exact key B A (by rw [hAB, mul_comm]) hB1 (by omega)

/-- **Proposition 4.8**, including the arbitrary possible-factor-degree set `K`.
The archimedean estimate (4.17) is supplied by the proved Proposition 4.7. -/
theorem irreducible_jacobiShifted_of_finite_criterion'
    (hZ : JacobiSimpleRealZeros)
    (hNP : NewtonPolygonRootSlopes) {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    {n : ℕ} (hn : 11 ≤ n) (K : Set ℕ)
    (hK : ∀ f : ℚ[X], f ∣ jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n → 1 ≤ f.natDegree →
      2 * f.natDegree ≤ n → f.natDegree ∈ K)
    (hcrit : ∀ k ∈ K, 1 ≤ k → 2 * k ≤ n → kzGoodPrimeSum l μ n < kzCriterionFn l μ n k) :
    Irreducible (jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n) :=
  irreducible_jacobiShifted_of_finite_criterion hl hμ hn
    (kanekoZagierArchimedeanBound_holds hZ hNP hl hμ n) K hK hcrit

/-- **Proposition 4.8**, basic form: for `n ≥ 11`, given (4.17) at `n`, if
`min_{1 ≤ k ≤ ⌊n/2⌋} ℋ_n(k) > S_n`, then `P_n^{(λ/3, μ/2)}` is irreducible over `ℚ`. -/
theorem irreducible_kanekoZagierJacobi_of_finite_criterion {l μ : ℤ} (hl : l = 1 ∨ l = -1)
    (hμ : μ = 1 ∨ μ = -1) {n : ℕ} (hn : 11 ≤ n) (harch : KanekoZagierArchimedeanBound l μ n)
    (hcrit : ∀ k : ℕ, 1 ≤ k → 2 * k ≤ n → kzGoodPrimeSum l μ n < kzCriterionFn l μ n k) :
    Irreducible (kanekoZagierJacobi l μ n) :=
  (irreducible_kanekoZagierJacobi_iff_jacobiShifted l μ n).mpr
    (irreducible_jacobiShifted_of_finite_criterion hl hμ hn harch Set.univ
      (fun _ _ _ _ => Set.mem_univ _) (fun k _ hk hk2 => hcrit k hk hk2))

/-- **Proposition 4.8**, with (4.17) supplied by Proposition 4.7: for `n ≥ 11`, if
`min_{1 ≤ k ≤ ⌊n/2⌋} ℋ_n(k) > S_n`, then `P_n^{(λ/3, μ/2)}` is irreducible over `ℚ`.
Conditional on the cited [DLMF, §18.2(vi)] and [Berger, Theorem 2.4] and proved Lemma 2.5. -/
theorem irreducible_kanekoZagierJacobi_of_finite_criterion'
    (hZ : JacobiSimpleRealZeros)
    (hNP : NewtonPolygonRootSlopes) {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    {n : ℕ} (hn : 11 ≤ n)
    (hcrit : ∀ k : ℕ, 1 ≤ k → 2 * k ≤ n → kzGoodPrimeSum l μ n < kzCriterionFn l μ n k) :
    Irreducible (kanekoZagierJacobi l μ n) :=
  irreducible_kanekoZagierJacobi_of_finite_criterion hl hμ hn
    (kanekoZagierArchimedeanBound_holds hZ hNP hl hμ n) hcrit

end ArithmeticOfJacobiPolynomials
