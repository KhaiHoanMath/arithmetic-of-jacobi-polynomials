/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Galois.LegendreQuartic
public import ArithmeticOfJacobiPolynomials.Galois.Transitivity
public import ArithmeticOfJacobiPolynomials.External
public import ArithmeticOfJacobiPolynomials.MainResults

/-!
# The Legendre Galois groups (Theorem 1.2)

Combining Theorem 5.9 with the irreducibility of `P_{2m}` and `P_{2m+1}/x` ([Deng,
Theorem 1.1]) gives `Gal(P_{2m+δ}(x)/x^δ / ℚ) = W_m` for every `m ≥ 1` and `δ ∈ {0, 1}`
(`legendreGaloisStatement`, Theorem 1.2). The exceptional degree `P_5/x ∝ 63x⁴ - 70x² + 15` is
`galoisGroupIsWreath_reducedLegendre_two_one`, which needs no cited input.

Irreducibility passes from `L` to `J` when `J(-X²) = k L` (`irreducible_of_comp_neg_X_sq`);
this is the direction of the irreducibility equivalence in Theorem 5.9 used here.
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial

variable {F : Type*} [Field F]

/-- If `J(-X²) = k L` with `k ≠ 0` and `L` irreducible, then `J` is irreducible. -/
theorem irreducible_of_comp_neg_X_sq {J L : F[X]} {k : F} (hk : k ≠ 0)
    (hJL : J.comp (-polyX ^ 2) = C k * L) (hL : Irreducible L) : Irreducible J := by
  have hdeg := natDegree_of_comp_neg_X_sq hk hJL
  have hL' : Irreducible (J.comp (-polyX ^ 2)) := by
    rw [hJL, irreducible_isUnit_mul (isUnit_C.mpr (Ne.isUnit hk))]
    exact hL
  have hJ0 : J ≠ 0 := by
    rintro rfl
    rw [zero_comp] at hL'
    exact not_irreducible_zero hL'
  have hunit : ∀ a : F[X], a ≠ 0 → IsUnit (a.comp (-polyX ^ 2)) → IsUnit a := by
    intro a ha h
    have h0 := natDegree_eq_zero_of_isUnit h
    rw [natDegree_comp, natDegree_neg, natDegree_X_pow, mul_eq_zero] at h0
    have ha0 : a.natDegree = 0 := h0.resolve_right (by norm_num)
    rw [eq_C_of_natDegree_eq_zero ha0] at ha ⊢
    exact isUnit_C.mpr (Ne.isUnit (fun h => ha (by rw [h, C_0])))
  rw [irreducible_iff]
  refine ⟨fun h => ?_, fun a b hab => ?_⟩
  · have h0 := natDegree_eq_zero_of_isUnit h
    have h1 : 0 < L.natDegree := natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hL)
    omega
  · have hab' : J.comp (-polyX ^ 2) = a.comp (-polyX ^ 2) * b.comp (-polyX ^ 2) := by rw [hab,
    mul_comp]
    have ha0 : a ≠ 0 := fun h => hJ0 (by rw [hab, h, zero_mul])
    have hb0 : b ≠ 0 := fun h => hJ0 (by rw [hab, h, mul_zero])
    rcases hL'.isUnit_or_isUnit hab' with h | h
    · exact Or.inl (hunit a ha0 h)
    · exact Or.inr (hunit b hb0 h)

/-- **Theorem 1.2** (the Cullinan–Hajir conjecture), for every `m ≥ 1` and `δ ∈ {0, 1}` with
`(m, δ) ≠ (2, 1)`: `Gal(P_{2m+δ}(x)/x^δ / ℚ) = W_m`.

Conditional on [Deng, Theorem 1.1], [BMOR, Corollary 1.7], [MV, Theorem 2], [Jones,
Corollary 1.3], [CHL, Theorem 1.9(a)] and [CHL, Lemma 2.2]. -/
theorem galoisGroupIsWreath_reducedLegendre_of_ne (hDeng : DengLegendreIrreducibility)
    (hBMOR : BMORPrimeCountingBound) (hBT : BrunTitchmarshInequality)
    (hJones : JonesCycleTheorem) (hCHL : CullinanHajirLegendreGalois)
    (hCHL4 : PrimesModFourInDyadicInterval) {m δ : ℕ} (hm : 1 ≤ m) (hδ : δ ≤ 1)
    (hexc : (m, δ) ≠ (2, 1)) : GaloisGroupIsWreath (reducedLegendre m δ) := by
  have hL : Irreducible (reducedLegendre m δ) := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hδ with h | h <;> subst h
    · exact (hDeng m hm).1
    · exact (hDeng m hm).2
  have hk : ((-2 : ℚ) ^ m * m.factorial) ≠ 0 := by positivity
  have hJ := irreducible_of_comp_neg_X_sq hk (legendreJ_comp_neg_X_sq m δ hδ) hL
  exact galoisGroupIsWreath_reducedLegendre hBMOR hBT hJones hCHL hCHL4 hδ hm hexc hJ

/-- **Theorem 5.9, second assertion**, in every degree: for `n ≥ 1` and
`δ ∈ {0, 1}`, `ε = 2δ - 1`, if `J_n^ε` is irreducible over `ℚ` then
`Gal(L_{2n+δ}/ℚ) = W_n`. Conditional on the cited results of
`galoisGroupIsWreath_reducedLegendre` (the case `(n, δ) = (2, 1)` uses none). -/
theorem galoisGroupIsWreath_reducedLegendre_of_irreducible (hBMOR : BMORPrimeCountingBound)
    (hBT : BrunTitchmarshInequality) (hJones : JonesCycleTheorem)
    (hCHL : CullinanHajirLegendreGalois) (hCHL4 : PrimesModFourInDyadicInterval)
    {n δ : ℕ} (hδ : δ ≤ 1) (hn : 1 ≤ n)
    (hirr : Irreducible ((legendreJ (2 * (δ : ℤ) - 1) n).map (Int.castRingHom ℚ))) :
    GaloisGroupIsWreath (reducedLegendre n δ) := by
  by_cases hexc : (n, δ) = (2, 1)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hexc
    exact galoisGroupIsWreath_reducedLegendre_two_one
  · exact galoisGroupIsWreath_reducedLegendre hBMOR hBT hJones hCHL hCHL4 hδ hn hexc hirr

/-- **Theorem 1.2** (the Legendre Galois groups; the Cullinan–Hajir conjecture). For every
`m ≥ 1` and `δ ∈ {0, 1}`, `Gal(P_{2m+δ}(x)/x^δ / ℚ) = W_m`.

Conditional on [Deng, Theorem 1.1], [BMOR, Corollary 1.7], [MV, Theorem 2], [Jones,
Corollary 1.3], [CHL, Theorem 1.9(a)] and [CHL, Lemma 2.2]. -/
theorem legendreGaloisStatement (hDeng : DengLegendreIrreducibility)
    (hBMOR : BMORPrimeCountingBound) (hBT : BrunTitchmarshInequality)
    (hJones : JonesCycleTheorem) (hCHL : CullinanHajirLegendreGalois)
    (hCHL4 : PrimesModFourInDyadicInterval) : LegendreGaloisStatement := by
  intro m δ hm hδ
  by_cases hexc : (m, δ) = (2, 1)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hexc
    exact galoisGroupIsWreath_reducedLegendre_two_one
  · exact galoisGroupIsWreath_reducedLegendre_of_ne hDeng hBMOR hBT hJones hCHL hCHL4 hm hδ hexc

/-- **Theorem 5.9, irreducibility equivalence.** For `n ≥ 1` and `δ ∈ {0, 1}`, `ε = 2δ - 1`,
`J_n^ε` is irreducible over `ℚ` if and only if `L_{2n+δ}` is. The direction `L → J` is
elementary; for `J → L` the Galois group of `L_{2n+δ}` is `W_n`, which is transitive on the
roots. Conditional on the cited results of `galoisGroupIsWreath_reducedLegendre_of_irreducible`
(used for `J → L`). -/
theorem irreducible_legendreJ_iff_irreducible_reducedLegendre (hBMOR : BMORPrimeCountingBound)
    (hBT : BrunTitchmarshInequality) (hJones : JonesCycleTheorem)
    (hCHL : CullinanHajirLegendreGalois) (hCHL4 : PrimesModFourInDyadicInterval)
    {n δ : ℕ} (hδ : δ ≤ 1) (hn : 1 ≤ n) :
    Irreducible ((legendreJ (2 * (δ : ℤ) - 1) n).map (Int.castRingHom ℚ)) ↔
      Irreducible (reducedLegendre n δ) := by
  have hk : ((-2 : ℚ) ^ n * n.factorial) ≠ 0 := by positivity
  have hJL := legendreJ_comp_neg_X_sq n δ hδ
  refine ⟨fun hJ => ?_, irreducible_of_comp_neg_X_sq hk hJL⟩
  have hε : 2 * (δ : ℤ) - 1 = 1 ∨ 2 * (δ : ℤ) - 1 = -1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hδ with h | h <;> simp [h]
  have hJ0 := coeff_zero_legendreJ_map_ne_zero hε n
  have hsep := separable_of_comp_neg_X_sq hk hJL hJ.separable hJ0
  have hW := galoisGroupIsWreath_reducedLegendre_of_irreducible hBMOR hBT hJones hCHL hCHL4 hδ
    hn hJ
  rw [galoisGroupIsWreath_iff] at hW
  have htrans := isPretransitive_negCommPerm (s := (reducedLegendre n δ).rootSet
    (reducedLegendre n δ).SplittingField) two_ne_zero
    (zero_not_mem_rootSet_of_comp_neg_X_sq hk hJL hJ0)
    (fun x hx => neg_mem_rootSet_of_comp_neg_X_sq hk hJL hx)
  rw [← hW] at htrans
  refine irreducible_of_isPretransitive hsep ?_ htrans
  rw [natDegree_reducedLegendre]
  omega

end ArithmeticOfJacobiPolynomials
