/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.KanekoZagier.ExplicitCutoff

/-!
# Completion in every degree: the range covered by [CHK]

The manuscript completes the irreducibility in Theorem 1.1 by three ranges:
Proposition B.1 for `n ≥ 250 000`, the computation of Cullinan and Hajir [CHK, Remark 4.6] for
`1 ≤ n ≤ 8332`, and the Proposition B.2 for `8333 ≤ n ≤ 250 000` (a hand reduction to
integer-arithmetic comparisons that the manuscript verifies by computer).

This file records the conversion used for the cited range: Cullinan and Hajir
[CHK, Definition 2.3] index the four families by `ℓ = 12n + 6 + 2λ + 3μ` and work with
`K_ℓ(X) = 3^n n! P_n^{(λ/3, μ/2)}(4X + 1)`; irreducibility of `K_ℓ` and of `P_n^{(λ/3, μ/2)}`
over `ℚ` are equivalent (`irreducible_chkPoly_iff`), and `ℓ ≤ 10^5` for `n ≤ 8332`
(`chk_index_le_of_le`), since `12 · 8332 + 11 = 99 995`.

Proposition B.1 is `kanekoZagier_explicit_cutoff`
(`ArithmeticOfJacobiPolynomials.KanekoZagier.ExplicitLargeDegreeIrreducibility`).
The assembly of Theorem 1.1 from the three ranges is `mahlburgOno_of_finiteRange`
(`ArithmeticOfJacobiPolynomials.KanekoZagier.MahlburgOno`), which takes Proposition B.2
(`KanekoZagierFiniteRange`) as a hypothesis; it is proved from the computed comparisons
`KanekoZagierFastCriterion` in `ArithmeticOfJacobiPolynomials.KanekoZagier.FiniteRange`.
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial

/-- The polynomial `K_ℓ(X) = 3^n n! P_n^{(λ/3, μ/2)}(4X + 1)` of [CHK, Definition 2.3],
`ℓ = 12n + 6 + 2λ + 3μ` (the argument `l` is `λ`). -/
noncomputable def chkPoly (l μ : ℤ) (n : ℕ) : ℚ[X] :=
  C ((3 : ℚ) ^ n * n.factorial) * (jacobiP ((l : ℚ) / 3) ((μ : ℚ) / 2) n).comp (4 * polyX + 1)

theorem chkPoly_eq (l μ : ℤ) (n : ℕ) : chkPoly l μ n =
    C ((3 : ℚ) ^ n * n.factorial) * (jacobiP ((l : ℚ) / 3) ((μ : ℚ) / 2) n).comp (4 * polyX + 1) :=
  (rfl)

/-- `K_ℓ` and `P_n^{(λ/3, μ/2)}` are irreducible over `ℚ` together. -/
theorem irreducible_chkPoly_iff (l μ : ℤ) (n : ℕ) :
    Irreducible (chkPoly l μ n) ↔ Irreducible (kanekoZagierJacobi l μ n) := by
  have h41 : (4 * polyX + 1 : ℚ[X]) = C 4 * polyX + C 1 := by rw [C_1, C_ofNat]
  rw [chkPoly_eq, h41, kanekoZagierJacobi_eq]
  exact irreducible_C_mul_comp_affine_iff (f := jacobiP ((l : ℚ) / 3) ((μ : ℚ) / 2) n)
    (c := (1 : ℚ)) (by positivity) (by norm_num)

/-- For `λ, μ ∈ {-1, 1}` and `n ≤ 8332`, the index `ℓ = 12n + 6 + 2λ + 3μ` is at most `10^5`. -/
theorem chk_index_le_of_le {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) {n : ℕ}
    (hn : n ≤ 8332) : 12 * (n : ℤ) + 6 + 2 * l + 3 * μ ≤ 10 ^ 5 := by
  have : (n : ℤ) ≤ 8332 := by exact_mod_cast hn
  rcases hl with rfl | rfl <;> rcases hμ with rfl | rfl <;> omega

end ArithmeticOfJacobiPolynomials
