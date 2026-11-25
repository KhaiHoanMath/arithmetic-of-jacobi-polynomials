/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Galois.UnequalParameters
public import ArithmeticOfJacobiPolynomials.MainResults

/-!
# Theorem 1.3, the rational Galois assertion

Proof of "The rational Galois assertion of Theorem 1.3" (Section 5.5): for distinct
nonnegative integers `a, b` and all sufficiently large `n`, `Gal(P_n^{(a,b)}/ℚ) = S_n`.

For `a > b ≥ 0` and each parity `δ`, the polynomial `𝒲_δ = A_δ C_δ` of (5.27) is a nonzero
integral polynomial (`galoisNumerator_ne_zero`), so it has no zeros `m` beyond an explicit
point (`exists_forall_galoisNumerator_eval_ne_zero`), and `|𝒲_δ(m)| ≤ C (m+1)^s` gives
`log |𝒲_δ(m)| < n/10` for all large `m` (`exists_forall_log_abs_galoisNumerator_lt`).
Hence (5.28) (§5.6) holds for all large `m`, and Proposition 5.17 (through its
prime, `exists_forall_galoisPrime`) applies, together with the irreducibility assertion of
Theorem 1.3 (`exists_forall_irreducible_jacobiP`). The case `b > a` follows by the reflection
`P_n^{(a,b)}(x) = (-1)^n P_n^{(b,a)}(-x)` (`galoisGroupIsSymmetric_jacobiP_comm`).

Main results:
* `ArithmeticOfJacobiPolynomials.exists_forall_galoisGroupIsSymmetric_jacobiP`;
* `ArithmeticOfJacobiPolynomials.unequalIntegralParameters`: **Theorem 1.3**
(`UnequalIntegralParametersStatement`).

Conditional on the cited literature used by Theorem 3.1 (`HansonLcmBound`,
`JacobiSimpleRealZeros`), by Lemma 5.16 (`JordanPrimeCycleTheorem`,
`EisensteinPrimeTotallyRamified`, `JacobiDiscriminantFormula`) and by Proposition 5.17
(`DusartThetaBound`).
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial

namespace UnequalParameters

/-- `A_δ` is a nonzero polynomial (`A_δ(0) > 0`). -/
theorem centralA_ne_zero_of_lt {a b δ : ℕ} (hab : b < a) (hδ : δ ≤ 1) : centralA a b δ ≠ 0 :=
  fun h => by
    have := centralA_eval_zero_pos a b δ hab hδ
    rw [h, eval_zero] at this
    exact lt_irrefl _ this

/-- `C_δ` of (5.27) is a nonzero polynomial. -/
theorem oppositeNumerator_ne_zero {a b δ : ℕ} (hab : b < a) (hδ : δ ≤ 1) :
    oppositeNumerator a b δ ≠ 0 := by
  intro h
  have hm := oppositeNumerator_map a b δ
  rw [h, Polynomial.map_zero, eq_comm, mul_eq_zero, C_eq_zero] at hm
  have hc := hm.resolve_left (pow_ne_zero _ two_ne_zero)
  have h2 : (((centralA a b (1 - δ)).map (Int.castRingHom ℚ)).comp
      (polyX + C ((δ : ℚ) - 1 / 2))).comp (polyX - C ((δ : ℚ) - 1 / 2)) = 0 := by
    rw [hc, zero_comp]
  rw [comp_assoc, add_comp, X_comp, C_comp, sub_add_cancel, comp_X] at h2
  exact centralA_ne_zero_of_lt hab (show 1 - δ ≤ 1 by omega)
    (Polynomial.map_injective (Int.castRingHom ℚ) (RingHom.injective_int _)
      (by rw [h2, Polynomial.map_zero]))

/-- `𝒲_δ = A_δ C_δ` is a nonzero polynomial (after (5.27)). -/
theorem galoisNumerator_ne_zero {a b δ : ℕ} (hab : b < a) (hδ : δ ≤ 1) :
    galoisNumerator a b δ ≠ 0 := by
  rw [galoisNumerator_eq]
  exact mul_ne_zero (centralA_ne_zero_of_lt hab hδ) (oppositeNumerator_ne_zero hab hδ)

/-- `𝒲_δ(m) ≠ 0` for all large `m`. -/
theorem exists_forall_galoisNumerator_eval_ne_zero {a b δ : ℕ} (hab : b < a) (hδ : δ ≤ 1) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → (galoisNumerator a b δ).eval (m : ℤ) ≠ 0 := by
  have hW0 := galoisNumerator_ne_zero hab hδ
  obtain ⟨N, hN⟩ := (((galoisNumerator a b δ).roots.toFinset.image Int.toNat).bddAbove)
  refine ⟨N + 1, fun m hm h0 => ?_⟩
  have hmem : (m : ℤ) ∈ (galoisNumerator a b δ).roots.toFinset :=
    Multiset.mem_toFinset.mpr ((mem_roots hW0).mpr h0)
  have := hN (Finset.mem_coe.mpr (Finset.mem_image_of_mem Int.toNat hmem))
  simp only [Int.toNat_natCast] at this
  omega

/-- `log |𝒲_δ(m)| < n/10` (`n = 2m + δ`) for all large `m`, from `|𝒲_δ(m)| ≤ C (m+1)^s`. -/
theorem exists_forall_log_abs_galoisNumerator_lt (a b δ : ℕ) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      Real.log |(((galoisNumerator a b δ).eval (m : ℤ) : ℤ) : ℝ)| < (2 * m + δ : ℝ) / 10 := by
  obtain ⟨K, hK, hKb⟩ := exists_abs_eval_natCast_le (galoisNumerator a b δ)
  obtain ⟨N, hN⟩ := exists_forall_mul_gt_sqrt (ε := 1 / 5)
    (K := 2 * ((galoisNumerator a b δ).natDegree : ℝ)) (K' := Real.log K) (by norm_num)
  refine ⟨N, fun m hm => ?_⟩
  have h1 := log_abs_le_of_le hK (hKb m)
  have h2 := hN m hm
  have hδ0 : (0 : ℝ) ≤ δ := Nat.cast_nonneg δ
  linarith

/-- **The prime of Proposition 5.17 for all large `n`** (proof of the rational Galois assertion
of Theorem 1.3). For `a > b ≥ 0` there is `N` such that for every `n = 2m + δ ≥ N`
(`δ ∈ {0,1}`): `m ≥ 2s + 10`, `P_n^{(a,b)}` is irreducible, and some prime `p` satisfies
(5.29) (§5.6): `3n/4 < p ≤ 7n/8` and `p ∤ 𝒲_δ(m)`. Conditional on the inputs of
Theorem 3.1 and [Dusart10, Theorem 5.2]. -/
theorem exists_forall_galoisPrime (hH : HansonLcmBound)
    (hZ : JacobiSimpleRealZeros) (hDusart : DusartThetaBound) {a b : ℕ} (hab : b < a) :
    ∃ N : ℕ, ∀ m δ : ℕ, δ ≤ 1 → N ≤ 2 * m + δ →
      2 * (a + b) + 10 ≤ m ∧ Irreducible (jacobiP a b (2 * m + δ)) ∧
      ∃ p : ℕ, p.Prime ∧ 3 * (2 * m + δ) < 4 * p ∧ 8 * p ≤ 7 * (2 * m + δ) ∧
        ¬ (p : ℤ) ∣ (galoisNumerator a b δ).eval (m : ℤ) := by
  obtain ⟨Ni, hNi⟩ := exists_forall_irreducible_jacobiP hH hZ (show a ≠ b by omega)
  obtain ⟨Z0, hZ0⟩ := exists_forall_galoisNumerator_eval_ne_zero (δ := 0) hab (by norm_num)
  obtain ⟨Z1, hZ1⟩ := exists_forall_galoisNumerator_eval_ne_zero (δ := 1) hab le_rfl
  obtain ⟨L0, hL0⟩ := exists_forall_log_abs_galoisNumerator_lt a b 0
  obtain ⟨L1, hL1⟩ := exists_forall_log_abs_galoisNumerator_lt a b 1
  refine ⟨Ni + 2 * (Z0 + Z1 + L0 + L1 + 2 * (a + b) + 10) + 5000000,
    fun m δ hδ hn => ?_⟩
  have hW : (galoisNumerator a b δ).eval (m : ℤ) ≠ 0 ∧
      Real.log |(((galoisNumerator a b δ).eval (m : ℤ) : ℤ) : ℝ)| < (2 * m + δ : ℝ) / 10 := by
    rcases (show δ = 0 ∨ δ = 1 by omega) with rfl | rfl
    · exact ⟨hZ0 m (by omega), hL0 m (by omega)⟩
    · exact ⟨hZ1 m (by omega), hL1 m (by omega)⟩
  obtain ⟨p, hp, hp1, hp2, hpW⟩ := exists_prime_not_dvd_of_log_lt hDusart (n := 2 * m + δ)
    (by omega) hW.1 (by exact_mod_cast hW.2)
  exact ⟨by omega, hNi _ (by omega), p, hp, hp1, hp2, hpW⟩

/-- The reflection `P_n^{(α,β)}(x) = (-1)^n P_n^{(β,α)}(-x)`, as an affine substitution. -/
theorem jacobiP_eq_C_mul_comp_neg (α β : ℚ) (n : ℕ) :
    jacobiP α β n = C ((-1 : ℚ) ^ n) * (jacobiP β α n).comp (C (-1) * polyX + C 0) := by
  have h := jacobiP_comp_neg_X α β n
  rw [show (C (-1 : ℚ) * polyX + C 0) = -polyX by simp, h, ← mul_assoc, ← C_mul, ← mul_pow]
  norm_num

end UnequalParameters

open UnequalParameters

/-- `Gal = S_n` passes from `P_n^{(β,α)}` to `P_n^{(α,β)}` (reflection). -/
theorem galoisGroupIsSymmetric_jacobiP_comm (α β : ℚ) (n : ℕ)
    (h : GaloisGroupIsSymmetric (jacobiP β α n)) : GaloisGroupIsSymmetric (jacobiP α β n) := by
  rw [jacobiP_eq_C_mul_comp_neg α β n]
  exact GaloisGroupIsSymmetric.affine _ _ (pow_ne_zero _ (by norm_num)) (by norm_num) h

/-- The rational Galois assertion of Theorem 1.3 for `a > b ≥ 0`. -/
theorem exists_forall_galoisGroupIsSymmetric_jacobiP_of_lt (hH : HansonLcmBound)
     (hZ : JacobiSimpleRealZeros) (hJordan : JordanPrimeCycleTheorem)
     (hEis : EisensteinPrimeTotallyRamified)
    (hdisc : JacobiDiscriminantFormula) (hDusart : DusartThetaBound) {a b : ℕ} (hab : b < a) :
    ∃ N : ℕ, ∀ n ≥ N, GaloisGroupIsSymmetric (jacobiP a b n) := by
  obtain ⟨N, hN⟩ := exists_forall_galoisPrime hH hZ hDusart hab
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨m, δ, hδ, rfl⟩ : ∃ m δ, δ ≤ 1 ∧ n = 2 * m + δ :=
    ⟨n / 2, n % 2, by omega, by omega⟩
  obtain ⟨hm, hirr, p, hp, hp1, hp2, hpW⟩ := hN m δ hδ hn
  exact galoisGroupIsSymmetric_jacobiP_of_prime hJordan hEis hdisc hab hδ hm hirr hp hp1 hp2 hpW

/-- **Theorem 1.3, the rational Galois assertion.** For distinct nonnegative integers `a, b`
there is `N` such that `Gal(P_n^{(a,b)}/ℚ) = S_n` for every `n ≥ N`. Conditional on the inputs
of Theorem 3.1 (`hH`, `hZ`), Lemma 5.16 (`hJordan`, `hEis`, `hdisc`) and Proposition 5.17
(`hDusart`). -/
theorem exists_forall_galoisGroupIsSymmetric_jacobiP (hH : HansonLcmBound)
     (hZ : JacobiSimpleRealZeros) (hJordan : JordanPrimeCycleTheorem)
     (hEis : EisensteinPrimeTotallyRamified)
    (hdisc : JacobiDiscriminantFormula) (hDusart : DusartThetaBound) {a b : ℕ} (hab : a ≠ b) :
    ∃ N : ℕ, ∀ n ≥ N, GaloisGroupIsSymmetric (jacobiP a b n) := by
  rcases lt_or_gt_of_ne hab with h | h
  · obtain ⟨N, hN⟩ :=
      exists_forall_galoisGroupIsSymmetric_jacobiP_of_lt hH hZ hJordan hEis hdisc hDusart h
    exact ⟨N, fun n hn => galoisGroupIsSymmetric_jacobiP_comm (a : ℚ) b n (hN n hn)⟩
  · exact exists_forall_galoisGroupIsSymmetric_jacobiP_of_lt hH hZ hJordan hEis hdisc hDusart h

/-- Theorem 1.3 for one pair `a ≠ b`: irreducibility and `Gal = S_n` for all large `n`. -/
theorem exists_forall_irreducible_galoisGroupIsSymmetric_jacobiP (hH : HansonLcmBound)
     (hZ : JacobiSimpleRealZeros) (hJordan : JordanPrimeCycleTheorem)
     (hEis : EisensteinPrimeTotallyRamified)
    (hdisc : JacobiDiscriminantFormula) (hDusart : DusartThetaBound) {a b : ℕ} (hab : a ≠ b) :
    ∃ N : ℕ, ∀ n ≥ N,
      Irreducible (jacobiP a b n) ∧ GaloisGroupIsSymmetric (jacobiP a b n) := by
  obtain ⟨N1, h1⟩ := exists_forall_irreducible_jacobiP hH hZ hab
  obtain ⟨N2, h2⟩ :=
    exists_forall_galoisGroupIsSymmetric_jacobiP hH hZ hJordan hEis hdisc hDusart hab
  exact ⟨max N1 N2, fun n hn =>
    ⟨h1 n (le_of_max_le_left hn), h2 n (le_of_max_le_right hn)⟩⟩

/-- **Theorem 1.3** (`UnequalIntegralParametersStatement`). For distinct
nonnegative integers `a, b` there is `N(a,b)` such that for every `n ≥ N(a,b)`, `P_n^{(a,b)}` is
irreducible over `ℚ` with Galois group `S_n`. Conditional on [Hanson, Theorem 1] (`hH`),
[DLMF, §18.2(vi)] (`hZ`), [Jones, Theorem 1.1] (`hJordan`),
[Milne, ANT v3.08, Proposition 3.53] (`hEis`),
the Jacobi discriminant formula [DLMF, (18.16.19)] (`hdisc`) and [Dusart10, Theorem 5.2]
(`hDusart`). -/
theorem unequalIntegralParameters (hH : HansonLcmBound)
    (hZ : JacobiSimpleRealZeros) (hJordan : JordanPrimeCycleTheorem)
    (hEis : EisensteinPrimeTotallyRamified)
    (hdisc : JacobiDiscriminantFormula) (hDusart : DusartThetaBound) :
    UnequalIntegralParametersStatement := by
  intro a b hab
  exact exists_forall_irreducible_galoisGroupIsSymmetric_jacobiP hH hZ hJordan hEis hdisc
    hDusart hab

end ArithmeticOfJacobiPolynomials
