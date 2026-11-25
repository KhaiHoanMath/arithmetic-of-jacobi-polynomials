/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Galois.KanekoZagierGalois
public import ArithmeticOfJacobiPolynomials.Jacobi.Legendre

/-!
# The Legendre quotient `J_n^ε` and its Galois group (Theorem 5.9, first assertion)

For `ε ∈ {-1, 1}`, `J_n^ε(T) = ∑_j binom(n,j) ∏_{k=1}^n (2j + 2k + ε) T^j`
((5.13), §5.3) is the
specialization `D = 2` of the integral normalization ((5.5), §5.1):
`J_n^ε = K_n^{ε/2, 0} = 2^n n! P_n^{(ε/2,0)}(2T + 1)` ((5.15), §5.3).
Proposition 5.2 with
`(a, u, b, v, D, r) = (ε, 2, 0, 1, 2, ε)` and Proposition 5.7 then show that for `n ≥ 10^6`
irreducibility of `J_n^ε` implies `Gal(J_n^ε/ℚ) = S_n`; for `n < 10^6` this is the cited
finite verification [CHL, Theorem 1.9(a)].

The wreath-group conclusion of Theorem 5.9 is proved in `LegendreWreath`.
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset

private lemma sign_cases' {l : ℤ} (hl : l = 1 ∨ l = -1) : -1 ≤ l ∧ l ≤ 1 := by
  rcases hl with rfl | rfl <;> norm_num

/-- The two products of (5.5) concatenate to the product of (5.13). -/
theorem prod_legendreJ_eq (ε : ℤ) {j n : ℕ} (hj : j ≤ n) :
    ∏ k ∈ Icc 1 n, (2 * (j : ℤ) + 2 * k + ε) =
      (∏ k ∈ Ioc j n, (2 * (k : ℤ) + ε)) * ∏ k ∈ Icc 1 j, (2 * (n : ℤ) + ε + 2 * k) := by
  set f : ℕ → ℤ := fun i => 2 * (i : ℤ) + ε with hf
  have h1 : ∏ k ∈ Icc 1 n, (2 * (j : ℤ) + 2 * k + ε) = ∏ i ∈ Ico (1 + j) (n + 1 + j), f i := by
    rw [← Ico_add_one_right_eq_Icc, ← prod_Ico_add' f 1 (n + 1) j]
    refine prod_congr rfl fun k _ => ?_
    simp only [hf]; push_cast; ring
  have h2 : ∏ k ∈ Ioc j n, (2 * (k : ℤ) + ε) = ∏ i ∈ Ico (j + 1) (n + 1), f i := by
    rw [← Ico_add_one_add_one_eq_Ioc]
  have h3 : ∏ k ∈ Icc 1 j, (2 * (n : ℤ) + ε + 2 * k) = ∏ i ∈ Ico (n + 1) (n + j + 1), f i := by
    rw [← Ico_add_one_right_eq_Icc, show n + j + 1 = j + 1 + n by omega,
      show n + 1 = 1 + n by omega, ← prod_Ico_add' f 1 (j + 1) n]
    refine prod_congr rfl fun k _ => ?_
    simp only [hf]; push_cast; ring
  rw [h1, h2, h3, prod_Ico_consecutive f (by omega) (by omega), show 1 + j = j + 1 by omega,
    show n + 1 + j = n + j + 1 by omega]

/-- (5.15), §5.3: `J_n^ε` is the `D = 2` integral normalization `K_n^{ε/2,0}`. -/
theorem legendreJ_eq_integralJacobi (ε : ℤ) (n : ℕ) :
    legendreJ ε n = integralJacobi ε 2 2 ε n := by
  rw [legendreJ_eq, integralJacobi_eq]
  refine sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [prod_legendreJ_eq ε hjn, mul_assoc]

/-- (5.15) over `ℚ`: `J_n^ε = 2^n n! P_n^{(ε/2,0)}(2T + 1)`. -/
theorem legendreJ_map_eq (ε : ℤ) (n : ℕ) :
    (legendreJ ε n).map (Int.castRingHom ℚ) =
      C ((2 : ℚ) ^ n * n.factorial) * (jacobiP ((ε : ℚ) / 2) 0 n).comp (C 2 * polyX + C 1) := by
  rw [legendreJ_eq_integralJacobi, integralJacobi_map ε 2 2 ε 0 n (by norm_num)
    (by push_cast; ring)]
  push_cast
  congr 2
  rw [show (2 * (2 : ℚ) / 2) = 2 by norm_num, add_comm, C_1]

/-- `J_n^ε` has degree `n`. -/
theorem natDegree_legendreJ_map {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (n : ℕ) :
    ((legendreJ ε n).map (Int.castRingHom ℚ)).natDegree = n := by
  rw [legendreJ_map_eq, natDegree_C_mul (by positivity), natDegree_comp]
  have hlin : (C (2 : ℚ) * polyX + C 1).natDegree = 1 := by
    rw [natDegree_add_C, natDegree_C_mul_X _ (by norm_num)]
  rw [hlin, mul_one]
  refine natDegree_jacobiP _ _ n (ring_choose_ne_zero_of_forall_ne_intCast (fun m hm => ?_) n)
  have h2 : (2 * m : ℚ) = 4 * n + ε := by rw [← hm]; ring
  have h2' : 2 * m = 4 * (n : ℤ) + ε := by exact_mod_cast h2
  rcases hε with rfl | rfl <;> omega

open Classical in
/-- The Legendre cycles for the quotient: for a prime `p ≡ ε (mod 2)` with `2n + 20 < p < 3n`,
`Gal(J_n^ε/ℚ)` contains a single cycle of length `2n + 1 - (p - ε)/2`. -/
theorem exists_isCycle_galPerm_legendreJ {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {n p : ℕ} (hn : 4 ≤ n)
    (hp : p.Prime) (hlo : 2 * n + 20 < p) (hhi : 2 * p < 6 * n) (hcong : (p : ℤ) ≡ ε [ZMOD 2]) :
    ∃ σ : ((legendreJ ε n).map (Int.castRingHom ℚ)).Gal, (galPerm _ σ).IsCycle ∧
      ((galPerm _ σ).support.card : ℤ) = 2 * n + 1 - ((p : ℤ) - ε) / 2 := by
  obtain ⟨hε1, hε2⟩ := sign_cases' hε
  have h : JacobiCycleHypotheses p n ε 2 0 1 2 ε := by
    refine ⟨hp, by omega, by norm_num, by norm_num, by norm_num, by push_cast; ring, by omega,
      ?_, ?_, ?_, ?_, ?_, hcong, ?_, ?_⟩
    · intro hd
      have := Int.le_of_dvd (by norm_num) hd
      omega
    · intro k hk1 hkn
      have hk : (k : ℤ) ≤ n := by exact_mod_cast hkn
      have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk1
      have hpos : 0 < 2 * (k : ℤ) + ε := by omega
      rw [abs_of_pos hpos]
      exact ⟨hpos, by omega⟩
    · intro k hk1 hkn
      have hk : (k : ℤ) ≤ n := by exact_mod_cast hkn
      have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk1
      have hpos : 0 < 1 * (k : ℤ) + 0 := by omega
      rw [abs_of_pos hpos]
      exact ⟨hpos, by omega⟩
    · omega
    · omega
    · rw [jacobiCycleIndex_eq]; omega
    · rw [jacobiCycleIndex_eq]; omega
  have hidx := h.cast_index
  rw [jacobiCycleIndex_eq] at hidx
  have hle := h.index_le_n
  have hd2 : 2 ≤ n + 1 - jacobiCycleIndexNat p n 2 ε := by
    have : (jacobiCycleIndexNat p n 2 ε : ℤ) ≤ n - 1 := by
      rw [hidx]; omega
    omega
  have hex := exists_isCycle_galPerm_jacobiP h hd2
  have e2 : ((2 : ℤ) : ℚ) = 2 := by norm_num
  have e0 : ((0 : ℤ) : ℚ) / ((1 : ℤ) : ℚ) = 0 := by norm_num
  rw [e2, e0] at hex
  obtain ⟨σ, hσ, hcard⟩ := hex
  have ha : (2 : ℚ) ^ n * n.factorial ≠ 0 := by positivity
  obtain ⟨τ, hτ, hτcard⟩ := exists_isCycle_galPerm_affine (jacobiP ((ε : ℚ) / 2) 0 n) 1 ha
    (by norm_num : (2 : ℚ) ≠ 0) σ hσ hcard
  rw [legendreJ_map_eq]
  refine ⟨τ, hτ, ?_⟩
  rw [hτcard, Nat.cast_sub (by omega), hidx]
  push_cast
  ring

/-- **Theorem 5.9, first assertion**. For `n ≥ 1` and `ε ∈ {-1, 1}`, if
`J_n^ε` is irreducible over `ℚ` then `Gal(J_n^ε/ℚ) = S_n`.

Conditional on the cited results [BMOR, Corollary 1.7], [MV, Theorem 2], [Jones,
Corollary 1.3] (through Proposition 5.7) and [CHL, Theorem 1.9(a)] (for `n < 10^6`). -/
theorem galoisGroupIsSymmetric_legendreJ (hBMOR : BMORPrimeCountingBound)
    (hBT : BrunTitchmarshInequality) (hJones : JonesCycleTheorem)
    (hCHL : CullinanHajirLegendreGalois) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {n : ℕ} (hn : 1 ≤ n)
    (hirr : Irreducible ((legendreJ ε n).map (Int.castRingHom ℚ))) :
    GaloisGroupIsSymmetric ((legendreJ ε n).map (Int.castRingHom ℚ)) := by
  obtain ⟨hε1, hε2⟩ := sign_cases' hε
  by_cases hbig : 10 ^ 6 ≤ n
  · classical
    rw [galoisGroupIsSymmetric_iff_range_eq_top]
    refine eq_top_of_forall_prime_exists_isCycle hBMOR hBT hJones (D := 2) (Or.inl rfl)
      (r := ε) ?_ ?_ hbig ?_ _ (isPretransitive_range_galPerm hirr) ?_
    · rw [abs_lt]; push_cast; constructor <;> omega
    · rcases hε with rfl | rfl <;> rfl
    · rw [card_rootSet_of_irreducible hirr, natDegree_legendreJ_map hε]
    · intro p hp hlo hhi hcong
      obtain ⟨σ, hσ, hcard⟩ := exists_isCycle_galPerm_legendreJ hε (n := n) (by omega) hp
        (by omega) (by omega) (by exact_mod_cast hcong)
      refine ⟨galPerm _ σ, ⟨σ, rfl⟩, hσ, ?_⟩
      convert hcard using 3
  · exact hCHL ε hε n hn (by omega) hirr

end ArithmeticOfJacobiPolynomials
