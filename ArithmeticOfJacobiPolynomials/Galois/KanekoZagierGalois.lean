/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Galois.JacobiCycle
public import ArithmeticOfJacobiPolynomials.Galois.GaloisBridge
public import ArithmeticOfJacobiPolynomials.PermGroup.PrimeCriterion
public import ArithmeticOfJacobiPolynomials.Jacobi.Endpoints
public import ArithmeticOfJacobiPolynomials.MainResults

/-!
# The Kaneko–Zagier Galois group (Theorem 5.12)

For `n ≥ 1` and `λ, μ ∈ {-1, 1}`, irreducibility of `P_n^{(λ/3,μ/2)}` over `ℚ` implies that its
Galois group is `S_n` (Theorem 5.12).

For `n ≥ 10^6` the proof is the manuscript's: every prime `p ≡ r (mod 6)`, `r = 2λ + 3μ`, with
`6n + 60 < p < 9n` satisfies the hypotheses of Proposition 5.2 with
`(a, u, b, v, D) = (λ, 3, μ, 2, 6)`, which gives a single cycle of length
`d_p = 2n + 1 - (p - r)/6`; Proposition 5.7 then gives `S_n`. For `1 ≤ n < 10^6` the modular
index `ℓ = 12n + 6 + r` is at most `11 999 999 < 10^9`, and the cited finite verification
[CHK, Theorem 1.8] applies to `F̃_{ℓ-1} = 1728^n P_n(1 - Y/864)`; the affine change of variable
transports irreducibility and the Galois group.

Irreducibility is a hypothesis: the unconditional Theorem 1.1 also needs the irreducibility
proof of Section 4 and Appendix B, which is not formalized.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial

/-- A rational ascending Pochhammer value at a non-integer does not vanish. -/
theorem ascPochhammer_eval_ne_zero_of_forall_ne_intCast {k : ℚ} (hk : ∀ m : ℤ, k ≠ m)
    (n : ℕ) : (ascPochhammer ℚ n).eval k ≠ 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval]
    refine mul_ne_zero ih fun h => hk (-(n : ℤ)) ?_
    push_cast
    linarith

/-- The generalized binomial coefficient `binom(z, n)` does not vanish at a non-integer `z`. -/
theorem ring_choose_ne_zero_of_forall_ne_intCast {z : ℚ} (hz : ∀ m : ℤ, z ≠ m) (n : ℕ) :
    Ring.choose z n ≠ 0 := by
  intro h
  have h1 := Ring.descPochhammer_eq_factorial_smul_choose z n
  rw [h, smul_zero, descPochhammer_smeval_eq_ascPochhammer, ascPochhammer_smeval_eq_eval] at h1
  refine ascPochhammer_eval_ne_zero_of_forall_ne_intCast (k := z - n + 1) (fun m hm => ?_) n h1
  exact hz (m + n - 1) (by push_cast; linarith)

private lemma sign_cases {l : ℤ} (hl : l = 1 ∨ l = -1) : -1 ≤ l ∧ l ≤ 1 := by
  rcases hl with rfl | rfl <;> norm_num

/-- `P_n^{(λ/3,μ/2)}` has degree `n`. -/
theorem natDegree_kanekoZagierJacobi {l μ : ℤ} (hμ : μ = 1 ∨ μ = -1) (n : ℕ) :
    (kanekoZagierJacobi l μ n).natDegree = n := by
  rw [kanekoZagierJacobi_eq]
  refine natDegree_jacobiP _ _ n (ring_choose_ne_zero_of_forall_ne_intCast (fun m hm => ?_) n)
  have h6 : (6 * m : ℚ) = 12 * n + 2 * l + 3 * μ := by rw [← hm]; ring
  have h6' : 6 * m = 12 * (n : ℤ) + 2 * l + 3 * μ := by exact_mod_cast h6
  rcases hμ with rfl | rfl <;> omega

open Classical in
/-- The Kaneko–Zagier cycles: for a prime `p ≡ 2λ + 3μ (mod 6)` with `6n + 60 < p < 9n`, the
Galois group of `P_n^{(λ/3,μ/2)}` contains a single cycle of length `2n + 1 - (p - r)/6`. -/
theorem exists_isCycle_galPerm_kanekoZagierJacobi {l μ : ℤ} (hl : l = 1 ∨ l = -1)
    (hμ : μ = 1 ∨ μ = -1) {n p : ℕ} (_hn : 4 ≤ n) (hp : p.Prime) (hlo : 6 * n + 60 < p)
    (hhi : 2 * p < 18 * n) (hcong : (p : ℤ) ≡ 2 * l + 3 * μ [ZMOD 6]) :
    ∃ σ : (kanekoZagierJacobi l μ n).Gal, (galPerm _ σ).IsCycle ∧
      ((galPerm _ σ).support.card : ℤ) = 2 * n + 1 - ((p : ℤ) - (2 * l + 3 * μ)) / 6 := by
  obtain ⟨hl1, hl2⟩ := sign_cases hl
  obtain ⟨hμ1, hμ2⟩ := sign_cases hμ
  have hp60 : (60 : ℤ) < p := by exact_mod_cast (show 60 < p by omega)
  have h : JacobiCycleHypotheses p n l 3 μ 2 6 (2 * l + 3 * μ) := by
    refine ⟨hp, by omega, by norm_num, by norm_num, by norm_num, by push_cast; ring, by omega,
      ?_, ?_, ?_, ?_, ?_, hcong, ?_, ?_⟩
    · intro hd
      have := Int.le_of_dvd (by norm_num) hd
      omega
    · intro k hk1 hkn
      have hk : (k : ℤ) ≤ n := by exact_mod_cast hkn
      have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk1
      have hpos : 0 < 3 * (k : ℤ) + l := by omega
      rw [abs_of_pos hpos]
      exact ⟨hpos, by omega⟩
    · intro k hk1 hkn
      have hk : (k : ℤ) ≤ n := by exact_mod_cast hkn
      have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk1
      have hpos : 0 < 2 * (k : ℤ) + μ := by omega
      rw [abs_of_pos hpos]
      exact ⟨hpos, by omega⟩
    · omega
    · omega
    · rw [jacobiCycleIndex_eq]; omega
    · rw [jacobiCycleIndex_eq]; omega
  have hidx := h.cast_index
  rw [jacobiCycleIndex_eq] at hidx
  have hle := h.index_le_n
  have hd2 : 2 ≤ n + 1 - jacobiCycleIndexNat p n 6 (2 * l + 3 * μ) := by
    have : (jacobiCycleIndexNat p n 6 (2 * l + 3 * μ) : ℤ) ≤ n - 1 := by
      rw [hidx]; omega
    omega
  have hex := exists_isCycle_galPerm_jacobiP h hd2
  have e3 : ((3 : ℤ) : ℚ) = 3 := by norm_num
  have e2 : ((2 : ℤ) : ℚ) = 2 := by norm_num
  rw [e3, e2] at hex
  rw [kanekoZagierJacobi_eq]
  obtain ⟨σ, hσ, hcard⟩ := hex
  refine ⟨σ, hσ, ?_⟩
  rw [hcard, Nat.cast_sub (by omega), hidx]
  push_cast
  ring

/-- **Theorem 5.12**. For `n ≥ 1` and `λ, μ ∈ {-1, 1}`, if `P_n^{(λ/3,μ/2)}` is
irreducible over `ℚ` then its Galois group is `S_n`.

Conditional on the cited results [BMOR, Corollary 1.7], [MV, Theorem 2], [Jones,
Corollary 1.3] (through Proposition 5.7) and [CHK, Theorem 1.8] (for `n < 10^6`). -/
theorem galoisGroupIsSymmetric_kanekoZagierJacobi (hBMOR : BMORPrimeCountingBound)
    (hBT : BrunTitchmarshInequality) (hJones : JonesCycleTheorem)
    (hCHK : CullinanHajirKanekoZagierGalois) {l μ : ℤ} (hl : l = 1 ∨ l = -1)
    (hμ : μ = 1 ∨ μ = -1) {n : ℕ} (hn : 1 ≤ n) (hirr : Irreducible (kanekoZagierJacobi l μ n)) :
    GaloisGroupIsSymmetric (kanekoZagierJacobi l μ n) := by
  obtain ⟨hl1, hl2⟩ := sign_cases hl
  obtain ⟨hμ1, hμ2⟩ := sign_cases hμ
  by_cases hbig : 10 ^ 6 ≤ n
  · classical
    rw [galoisGroupIsSymmetric_iff_range_eq_top]
    refine eq_top_of_forall_prime_exists_isCycle hBMOR hBT hJones (D := 6) (Or.inr rfl)
      (r := 2 * l + 3 * μ) ?_ ?_ hbig ?_ _ (isPretransitive_range_galPerm hirr) ?_
    · rw [abs_lt]; push_cast; constructor <;> omega
    · rcases hl with rfl | rfl <;> rcases hμ with rfl | rfl <;> rfl
    · rw [card_rootSet_of_irreducible hirr, natDegree_kanekoZagierJacobi hμ]
    · intro p hp hlo hhi hcong
      obtain ⟨σ, hσ, hcard⟩ :=
        exists_isCycle_galPerm_kanekoZagierJacobi hl hμ (n := n) (by omega) hp
        (by omega) (by omega) (by exact_mod_cast hcong)
      refine ⟨galPerm _ σ, ⟨σ, rfl⟩, hσ, ?_⟩
      convert hcard using 3
  · -- the finite range, through [CHK, Theorem 1.8]
    have hb : (-1 / 864 : ℚ) ≠ 0 := by norm_num
    have ha : (1728 : ℚ) ^ n ≠ 0 := by positivity
    have hirr' : Irreducible (kanekoZagierModularPoly l μ n) := by
      rw [kanekoZagierModularPoly_eq, ← kanekoZagierJacobi_eq,
        irreducible_C_mul_comp_affine_iff _ _ ha hb]
      exact hirr
    have hind : 12 * (n : ℤ) + 6 + 2 * l + 3 * μ ≤ 10 ^ 9 := by
      have : (n : ℤ) < 10 ^ 6 := by exact_mod_cast (show n < 10 ^ 6 by omega)
      omega
    have hsym := hCHK l μ hl hμ n hn hind hirr'
    rw [kanekoZagierModularPoly_eq, ← kanekoZagierJacobi_eq] at hsym
    exact GaloisGroupIsSymmetric.of_affine _ _ ha hb hsym

end ArithmeticOfJacobiPolynomials
