/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Galois.LegendreGalois
public import ArithmeticOfJacobiPolynomials.Galois.SquaresBridge
public import ArithmeticOfJacobiPolynomials.PermGroup.SignKernel
public import ArithmeticOfJacobiPolynomials.NumberTheory.OddLegendreCycle

/-!
# The Legendre Galois group `W_n` (Lemma 5.10 and Theorem 5.9, second assertion)

For `δ ∈ {0, 1}`, `ε = 2δ - 1` and `L_{2n+δ} = P_{2n+δ}/x^δ` (`reducedLegendre n δ`):

* (5.14)–(5.15) give `L_{2n+δ} = (-1)^n P_n^{(ε/2,0)}(1 - 2X²)`;
* **Lemma 5.10**: for a prime `p` with `2n + δ < p ≤ 4n + ε` and `d = 2n + 1 - (p - ε)/2`,
  the Galois group of `L_{2n+δ}` contains a single `2d`-cycle whose `d`-th power negates every
  root it moves (Proposition 5.2, quadratic form, with `c = -2`);
* **Theorem 5.9, second assertion**: if `J_n^ε` is irreducible, the Galois group of
  `L_{2n+δ}` is all of `W_n`, except in the case `(n, δ) = (2, 1)`, which the manuscript
  settles by a separate computation in `ℚ(√70)`, formalized in `LegendreQuartic`. The proof uses
  `Gal(J_n^ε/ℚ) = S_n` (first assertion), the squares bridge, and Lemma 5.5 with an odd `d`
  supplied by Lemma 5.11 (`n ≥ 4`), by the primes `7, 11, 13` (`(n, ε) = (2, -1), (3, ∓1)`), or
  by a direct count (`n = 1`).
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial

/-- (5.14)–(5.15): `L_{2n+δ} = (-1)^n P_n^{(ε/2,0)}(1 - 2X²)` with `ε = 2δ - 1`. -/
theorem reducedLegendre_eq_jacobiP_comp (n δ : ℕ) (hδ : δ ≤ 1) :
    reducedLegendre n δ = C ((-1 : ℚ) ^ n) *
      ((jacobiP (((2 * (δ : ℤ) - 1 : ℤ) : ℚ) / 2) 0 n).comp (1 + C (-2) * polyX ^ 2)).comp
        (C 1 * polyX + C 0) := by
  have h := legendreJ_comp_neg_X_sq n δ hδ
  rw [legendreJ_map_eq] at h
  have hb : ((-2 : ℚ) ^ n * n.factorial) ≠ 0 := by positivity
  apply mul_left_cancel₀ (C_ne_zero.mpr hb)
  rw [← h, mul_comp, C_comp, comp_assoc, comp_assoc, ← mul_assoc, ← C_mul]
  have hlin : (C (2 : ℚ) * polyX + C 1).comp (-polyX ^ 2) =
      ((1 : ℚ[X]) + C (-2 : ℚ) * polyX ^ 2).comp (C (1 : ℚ) * polyX + C 0) := by
    simp only [add_comp, mul_comp, C_comp, X_comp, one_comp, C_1, C_0, one_mul,
      add_zero, C_neg, comp_X]
    ring
  rw [hlin]
  congr 2
  rw [mul_right_comm, ← mul_pow]
  norm_num

private lemma not_dvd_four {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) : ¬ (p : ℤ) ∣ 2 * 1 * 2 := by
  intro hd
  have h4 : p ∣ 2 ^ 2 := by
    have : (p : ℤ) ∣ ((2 ^ 2 : ℕ) : ℤ) := by simpa using hd
    exact Int.natCast_dvd_natCast.mp this
  have := Nat.le_of_dvd two_pos (hp.dvd_of_dvd_pow h4)
  omega

open Classical in
/-- **Lemma 5.10**. Let `δ ∈ {0, 1}`, `ε = 2δ - 1`, `n ≥ 1`, and let `p`
be a prime with `2n + δ < p ≤ 4n + ε`. Then `d = 2n + 1 - (p - ε)/2` is a natural number with
`1 ≤ d ≤ n`, and the Galois group of `L_{2n+δ}` contains a single `2d`-cycle whose `d`-th power
negates every root it moves (so on opposite pairs it is a single `d`-cycle whose `d`-th power
flips exactly those `d` pairs). -/
theorem exists_isCycle_galPerm_reducedLegendre {n δ p : ℕ} (hδ : δ ≤ 1) (hn : 1 ≤ n)
    (hp : p.Prime) (hlo : 2 * n + δ < p) (hhi : (p : ℤ) ≤ 4 * n + (2 * δ - 1)) :
    ∃ d : ℕ, (d : ℤ) = 2 * n + 1 - ((p : ℤ) - (2 * δ - 1)) / 2 ∧ 1 ≤ d ∧ d ≤ n ∧
      ∃ σ : (reducedLegendre n δ).Gal, (galPerm _ σ).IsCycle ∧
        (galPerm _ σ).support.card = 2 * d ∧
        ∀ x ∈ (galPerm _ σ).support,
          (((galPerm _ σ ^ d) x : (reducedLegendre n δ).rootSet _) :
            (reducedLegendre n δ).SplittingField) = -(x : _) := by
  have hp2 : p ≠ 2 := by omega
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  set ε : ℤ := 2 * δ - 1 with hε
  have h : JacobiCycleHypotheses p n ε 2 0 1 2 ε := by
    refine ⟨hp, hp2, by norm_num, by norm_num, by norm_num, by push_cast; ring, by omega,
      not_dvd_four hp (by omega), ?_, ?_, by omega, by omega, ?_, ?_, ?_⟩
    · intro k hk1 hkn
      have hk : (k : ℤ) ≤ n := by exact_mod_cast hkn
      have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk1
      have hpos : 0 < 2 * (k : ℤ) + ε := by omega
      rw [abs_of_pos hpos]
      exact ⟨hpos, by omega⟩
    · intro k hk1 hkn
      have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk1
      have hpos : 0 < 1 * (k : ℤ) + 0 := by omega
      rw [abs_of_pos hpos]
      exact ⟨hpos, by omega⟩
    · rw [Int.ModEq]; omega
    · rw [jacobiCycleIndex_eq]; omega
    · rw [jacobiCycleIndex_eq]; omega
  have hidx := h.cast_index
  rw [jacobiCycleIndex_eq] at hidx
  have hle := h.index_le_n
  have h1 := h.one_le_index
  have h2d : 2 * (n + 1 - jacobiCycleIndexNat p n 2 ε) < p := by omega
  have hcp : padicValRat p (-2 : ℚ) = 0 := by
    rw [padicValRat.neg, show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd]
    · simp
    · intro hd; have := Nat.le_of_dvd two_pos hd; omega
  have hex := exists_isCycle_galPerm_jacobiP_comp h (by norm_num : (-2 : ℚ) ≠ 0) hcp h2d
  have e2 : ((2 : ℤ) : ℚ) = 2 := by norm_num
  have e0 : ((0 : ℤ) : ℚ) / ((1 : ℤ) : ℚ) = 0 := by norm_num
  rw [e2, e0] at hex
  obtain ⟨σ, hσ, hcard, hneg⟩ := hex
  refine ⟨n + 1 - jacobiCycleIndexNat p n 2 ε, ?_, by omega, by omega, ?_⟩
  · omega
  · exact exists_isCycle_galPerm_scale_of_eq _ (by positivity : ((-1 : ℚ) ^ n) ≠ 0)
      one_ne_zero (reducedLegendre_eq_jacobiP_comp n δ hδ) σ hσ hcard hneg

/-- The constant coefficient of `J_n^ε` does not vanish. -/
theorem coeff_zero_legendreJ_map_ne_zero {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (n : ℕ) :
    ((legendreJ ε n).map (Int.castRingHom ℚ)).coeff 0 ≠ 0 := by
  rw [coeff_zero_eq_eval_zero, legendreJ_map_eq, eval_mul, eval_C, eval_comp]
  simp only [eval_add, eval_mul, eval_C, eval_X, mul_zero, zero_add]
  refine mul_ne_zero (by positivity) ?_
  rw [jacobiP_eval_one]
  refine ring_choose_ne_zero_of_forall_ne_intCast (fun m hm => ?_) n
  have h2 : (2 * m : ℚ) = 2 * n + ε := by rw [← hm]; ring
  have h2' : 2 * m = 2 * (n : ℤ) + ε := by exact_mod_cast h2
  rcases hε with rfl | rfl <;> omega

/-- In a group of order `2`, a subgroup containing a nontrivial element is everything. -/
private lemma eq_top_of_card_two {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 2)
    {H : Subgroup G} {g : G} (hg : g ∈ H) (hg1 : g ≠ 1) : H = ⊤ := by
  apply Subgroup.eq_top_of_card_eq
  have hne : H ≠ ⊥ := fun h => hg1 (by rw [h] at hg; exact (Subgroup.mem_bot.mp hg))
  have h1 := (Subgroup.one_lt_card_iff_ne_bot H).mpr hne
  have h2 := Subgroup.card_subgroup_dvd_card H
  rw [hG] at h2 ⊢
  have := Nat.le_of_dvd two_pos h2
  omega

/-- **Theorem 5.9, second assertion**, outside the exceptional case
`(n, δ) = (2, 1)`. For `n ≥ 1` and `δ ∈ {0, 1}`, `ε = 2δ - 1`, if `J_n^ε` is irreducible over
`ℚ` then the Galois group of `L_{2n+δ} = P_{2n+δ}/x^δ` is `W_n = C_2 ≀ S_n`.

Conditional on [BMOR, Corollary 1.7], [MV, Theorem 2], [Jones, Corollary 1.3],
[CHL, Theorem 1.9(a)] (through the first assertion) and [CHL, Lemma 2.2] (through
Lemma 5.11). The case `(n, δ) = (2, 1)` (`L_5 ∝ 63X⁴ - 70X² + 15`) is excluded. -/
theorem galoisGroupIsWreath_reducedLegendre (hBMOR : BMORPrimeCountingBound)
    (hBT : BrunTitchmarshInequality) (hJones : JonesCycleTheorem)
    (hCHL : CullinanHajirLegendreGalois) (hCHL4 : PrimesModFourInDyadicInterval)
    {n δ : ℕ} (hδ : δ ≤ 1) (hn : 1 ≤ n) (hexc : (n, δ) ≠ (2, 1))
    (hirr : Irreducible ((legendreJ (2 * (δ : ℤ) - 1) n).map (Int.castRingHom ℚ))) :
    GaloisGroupIsWreath (reducedLegendre n δ) := by
  classical
  set ε : ℤ := 2 * δ - 1 with hε
  have hε' : ε = 1 ∨ ε = -1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hδ with h | h <;> simp [hε, h]
  set J := (legendreJ ε n).map (Int.castRingHom ℚ) with hJdef
  set L := reducedLegendre n δ with hLdef
  have hk : ((-2 : ℚ) ^ n * n.factorial) ≠ 0 := by positivity
  have hJL : J.comp (-polyX ^ 2) = C ((-2 : ℚ) ^ n * n.factorial) * L :=
    legendreJ_comp_neg_X_sq n δ hδ
  have hJsep : J.Separable := hirr.separable
  have hJ0 : J.coeff 0 ≠ 0 := coeff_zero_legendreJ_map_ne_zero hε' n
  have hsym := galoisGroupIsSymmetric_legendreJ hBMOR hBT hJones hCHL hε' hn hirr
  have hproj := map_pairPerm_range_galPerm_eq_top hk hJL hJsep hJ0 hsym
  have hΓ := range_galPerm_le_negCommPerm L
  have h0 := zero_not_mem_rootSet_of_comp_neg_X_sq hk hJL hJ0
  have hneg : ∀ x ∈ L.rootSet L.SplittingField, -x ∈ L.rootSet L.SplittingField :=
    fun x hx => neg_mem_rootSet_of_comp_neg_X_sq hk hJL hx
  have hN : Nat.card (squares (L.rootSet L.SplittingField)) = n := by
    rw [nat_card_squares_of_comp_neg_X_sq hk hJL hJsep hJ0, hJdef, natDegree_legendreJ_map hε']
  rw [galoisGroupIsWreath_iff]
  -- an odd cycle on the pairs finishes the proof through Lemma 5.5
  have finish : ∀ p : ℕ, p.Prime → 2 * n + δ < p → (p : ℤ) ≤ 4 * n + ε →
      Odd (2 * (n : ℤ) + 1 - ((p : ℤ) - ε) / 2) →
      2 * (n : ℤ) + 1 - ((p : ℤ) - ε) / 2 < n →
      (galPerm L).range = negCommPerm (L.rootSet L.SplittingField) := by
    intro p hp hlo hhi hodd hlt
    obtain ⟨d, hd, hd1, -, σ, hσ, hcard, -⟩ :=
      exists_isCycle_galPerm_reducedLegendre hδ hn hp hlo hhi
    refine eq_negCommPerm_of_isCycle_of_odd two_ne_zero h0 hneg hΓ hproj
      (MonoidHom.mem_range.mpr ⟨σ, rfl⟩) hσ (d := d) ?_ ?_ ?_
    · convert hcard using 2
    · rw [← Int.odd_coe_nat, hd]; exact hodd
    · rw [hN]; omega
  by_cases h4 : 4 ≤ n
  · obtain ⟨p, hp, -, hlo, hhi, hodd, -, hlt⟩ :=
      exists_prime_odd_legendre_cycle hCHL4 n h4 ε (by rcases hε' with h | h <;> simp [h])
    have hlo' : 2 * n + δ < p := by
      have : (ε + 1) / 2 = δ := by omega
      omega
    exact finish p hp hlo' hhi hodd hlt
  · interval_cases n
    · -- `n = 1`: a single transposition and a group of order `2`
      have hex := exists_isCycle_galPerm_reducedLegendre (p := 3 + 2 * δ) hδ le_rfl
          (by rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hδ with h | h <;> subst h <;> norm_num)
          (by omega) (by omega)
      rw [← hLdef] at hex
      obtain ⟨d, hd, hd1, hdn, σ, hσ, hcard, -⟩ := hex
      have hs : Nat.card (L.rootSet L.SplittingField) = 2 := by
        rw [nat_card_eq_two_mul_nat_card_squares two_ne_zero h0 hneg, hN]
      have hσ1 : galPerm L σ ≠ 1 := hσ.ne_one
      have htop := eq_top_of_card_two (by rw [Nat.card_perm, hs]; rfl)
        (MonoidHom.mem_range.mpr ⟨σ, rfl⟩) hσ1
      exact le_antisymm hΓ (htop ▸ le_top)
    · -- `n = 2`, `δ = 0`: the prime `7`
      have hδ0 : δ = 0 := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hδ with h | h
        · exact h
        · exact absurd (by rw [h] : ((2 : ℕ), δ) = (2, 1)) hexc
      subst hδ0
      exact finish 7 (by norm_num) (by norm_num) (by rw [hε]; norm_num)
        (by rw [hε]; exact ⟨0, by norm_num⟩) (by rw [hε]; norm_num)
    · -- `n = 3`: the primes `11` (`δ = 0`) and `13` (`δ = 1`)
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hδ with h | h <;> subst h
      · exact finish 11 (by norm_num) (by norm_num) (by rw [hε]; norm_num)
          (by rw [hε]; exact ⟨0, by norm_num⟩) (by rw [hε]; norm_num)
      · exact finish 13 (by norm_num) (by norm_num) (by rw [hε]; norm_num)
          (by rw [hε]; exact ⟨0, by norm_num⟩) (by rw [hε]; norm_num)

end ArithmeticOfJacobiPolynomials
