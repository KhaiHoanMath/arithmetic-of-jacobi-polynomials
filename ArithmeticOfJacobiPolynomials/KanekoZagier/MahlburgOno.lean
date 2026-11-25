/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.KanekoZagier.Completion
public import ArithmeticOfJacobiPolynomials.KanekoZagier.ExplicitLargeDegreeIrreducibility
public import ArithmeticOfJacobiPolynomials.Galois.KanekoZagierGalois

/-!
# Theorem 1.1 (the Mahlburg–Ono conjecture): assembly

Irreducibility of `P_n^{(λ/3, μ/2)}` in every degree `n ≥ 1` comes from three ranges:

* `1 ≤ n ≤ 8332`: the computation of Cullinan and Hajir [CHK, Remark 4.6]
  (`CullinanHajirKanekoZagierIrreducibility`), through `irreducible_chkPoly_iff`
  (`irreducible_kanekoZagierJacobi_of_le`);
* `8333 ≤ n ≤ 250000`: Proposition B.2 (`KanekoZagierFiniteRange`), proved in `FiniteRange` from
  the computed comparisons `KanekoZagierFastCriterion`;
* `n ≥ 250000`: Proposition B.1 (`kanekoZagier_explicit_cutoff`).

The Galois group is then `S_n` by Theorem 5.12 (`galoisGroupIsSymmetric_kanekoZagierJacobi`).

`mahlburgOno_of_finiteRange` derives `MahlburgOnoStatement` from the cited inputs and
`KanekoZagierFiniteRange`. That proposition is Proposition B.2 of the manuscript; it is not
cited literature and is discharged in `FiniteRange` (from the computed input
`KanekoZagierFastCriterion`). This file does not prove Theorem 1.1 on its own.
-/

public section

namespace ArithmeticOfJacobiPolynomials

/-- **Proposition B.2** (the finite range), as a statement: for `λ, μ ∈ {-1, 1}` and
`8333 ≤ n ≤ 250000`, `P_n^{(λ/3, μ/2)}` is irreducible over `ℚ`. -/
def KanekoZagierFiniteRange : Prop :=
  ∀ l μ : ℤ, (l = 1 ∨ l = -1) → (μ = 1 ∨ μ = -1) → ∀ n : ℕ, 8333 ≤ n → n ≤ 250000 →
    Irreducible (kanekoZagierJacobi l μ n)

theorem kanekoZagierFiniteRange_eq : KanekoZagierFiniteRange =
    ∀ l μ : ℤ, (l = 1 ∨ l = -1) → (μ = 1 ∨ μ = -1) → ∀ n : ℕ, 8333 ≤ n → n ≤ 250000 →
      Irreducible (kanekoZagierJacobi l μ n) := (rfl)

/-- **The range of [CHK, Remark 4.6]**: for `1 ≤ n ≤ 8332`, `P_n^{(λ/3, μ/2)}` is irreducible. -/
theorem irreducible_kanekoZagierJacobi_of_le (hCHK : CullinanHajirKanekoZagierIrreducibility)
    {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) {n : ℕ} (hn : 1 ≤ n)
    (hn' : n ≤ 8332) : Irreducible (kanekoZagierJacobi l μ n) := by
  have h := hCHK l μ hl hμ n hn (chk_index_le_of_le hl hμ hn')
  rw [← chkPoly_eq, irreducible_chkPoly_iff] at h
  exact h

/-- **Irreducibility in every degree**, from [CHK, Remark 4.6], Proposition B.2
(`KanekoZagierFiniteRange`) and Proposition B.1. -/
theorem irreducible_kanekoZagierJacobi_of_finiteRange (hCHK :
    CullinanHajirKanekoZagierIrreducibility) (hB2 : KanekoZagierFiniteRange)
     (hZ : JacobiSimpleRealZeros) (hNP : NewtonPolygonRootSlopes) (hH : HansonLcmBound)
    (hT : BMORThetaBound) (hS : BMORThetaSmallBound) {l μ : ℤ} (hl : l = 1 ∨ l = -1)
    (hμ : μ = 1 ∨ μ = -1) {n : ℕ} (hn : 1 ≤ n) : Irreducible (kanekoZagierJacobi l μ n) := by
  rcases le_or_gt n 8332 with h1 | h1
  · exact irreducible_kanekoZagierJacobi_of_le hCHK hl hμ hn h1
  rcases le_or_gt n 250000 with h2 | h2
  · exact hB2 l μ hl hμ n (by omega) h2
  · exact kanekoZagier_explicit_cutoff hZ hNP hH hT hS hl hμ h2.le

/-- **Theorem 1.1 (the Mahlburg–Ono conjecture)**, from the cited inputs and Proposition B.2
(`KanekoZagierFiniteRange`, proved in `FiniteRange`). -/
theorem mahlburgOno_of_finiteRange (hCHK : CullinanHajirKanekoZagierIrreducibility)
    (hB2 : KanekoZagierFiniteRange)
    (hZ : JacobiSimpleRealZeros)
    (hNP : NewtonPolygonRootSlopes) (hH : HansonLcmBound) (hT : BMORThetaBound)
    (hS : BMORThetaSmallBound) (hBMOR : BMORPrimeCountingBound)
    (hBT : BrunTitchmarshInequality) (hJones : JonesCycleTheorem)
    (hCHKG : CullinanHajirKanekoZagierGalois) : MahlburgOnoStatement := by
  intro l μ hl hμ n hn
  have hirr := irreducible_kanekoZagierJacobi_of_finiteRange hCHK hB2 hZ hNP hH hT hS hl hμ hn
  exact ⟨hirr, galoisGroupIsSymmetric_kanekoZagierJacobi hBMOR hBT hJones hCHKG hl hμ hn hirr⟩

end ArithmeticOfJacobiPolynomials
