/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.KanekoZagier.FiniteRangeReduction
public import ArithmeticOfJacobiPolynomials.KanekoZagier.MahlburgOno
public import ArithmeticOfJacobiPolynomials.External

/-!
# Proposition B.2 for `8333 ≤ n ≤ 250000`

For `λ, μ ∈ {-1, 1}` and `8333 ≤ n ≤ 250000` the polynomial `P_n^{(λ/3, μ/2)}` is irreducible
over `ℚ`. The manuscript (Proposition B.2) proves this from three ingredients:

* the **hand reduction** (proved here, in `FiniteRangeReduction`): the conditions
  `|D_{2,n} log 2 - D_{3,n} log 3| ≤ (9/10) n` and `Δ_n > 0` exclude every proper factorization
  (`irreducible_kanekoZagierJacobi_of_fast_criterion`; conditional on the cited
  [DLMF, §18.2(vi)] and [Berger, Theorem 2.4] and proved Lemma 2.5 through Proposition 4.7);
* the **computed comparisons** `KanekoZagierFastCriterion` (a `ComputerVerified` input, see
  `External.lean`): for the four parameter pairs and `8333 ≤ n ≤ 250000` the first
  inequality and `Δ_n > n/1000`;
* the cited computation of Cullinan–Hajir for `1 ≤ n ≤ 8332` and the proved Proposition B.1
  for `n ≥ 250000`, combined in `MahlburgOno`.

* `irreducible_kanekoZagierJacobi_finiteRange` — **Proposition B.2 for `8333 ≤ n ≤ 250000`**;
* `kanekoZagierFiniteRange_holds` — the statement `KanekoZagierFiniteRange` of `MahlburgOno`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

/-- **Proposition B.2 for `8333 ≤ n ≤ 250000`**: for `λ, μ ∈ {-1, 1}` the
polynomial `P_n^{(λ/3, μ/2)}` is irreducible over `ℚ`. Conditional on the computed comparisons
`KanekoZagierFastCriterion` and on the cited [DLMF, §18.2(vi)] and [Berger, Theorem 2.4] and
proved Lemma 2.5 (through Proposition 4.7); the range `1 ≤ n ≤ 8332` is the cited computation of
Cullinan–Hajir and is not covered here. -/
theorem irreducible_kanekoZagierJacobi_finiteRange (hC : KanekoZagierFastCriterion)
    (hZ : JacobiSimpleRealZeros) (hNP : NewtonPolygonRootSlopes) {l μ : ℤ}
    (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) {n : ℕ} (hn1 : 8333 ≤ n) (hn2 : n ≤ 250000) :
    Irreducible (kanekoZagierJacobi l μ n) := by
  obtain ⟨h1, h2⟩ := hC l μ hl hμ n hn1 hn2
  have hpos : (0 : ℝ) < (n : ℝ) / 1000 := by
    have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    positivity
  exact irreducible_kanekoZagierJacobi_of_fast_criterion hZ hNP hl hμ (by omega) h1
    (hpos.trans h2)

/-- **Proposition B.2 exactly as stated in the manuscript**: for every `1 ≤ n ≤ 250000` and
`λ, μ ∈ {-1, 1}`, `P_n^{(λ/3, μ/2)}` is irreducible over `ℚ`. The range `1 ≤ n ≤ 8332` is the
cited computation of Cullinan–Hajir (`CullinanHajirKanekoZagierIrreducibility`, used independently
of the Galois-group statement of [CHK, Theorem 1.8]); the range `8333 ≤ n ≤ 250000` is
`irreducible_kanekoZagierJacobi_finiteRange`. Uses neither Proposition B.1 nor any Galois-group
input. -/
theorem irreducible_kanekoZagierJacobi_le_250000
    (hCHK : CullinanHajirKanekoZagierIrreducibility) (hC : KanekoZagierFastCriterion)
    (hZ : JacobiSimpleRealZeros)
    (hNP : NewtonPolygonRootSlopes) {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    {n : ℕ} (hn1 : 1 ≤ n) (hn2 : n ≤ 250000) : Irreducible (kanekoZagierJacobi l μ n) := by
  rcases le_or_gt n 8332 with h | h
  · exact irreducible_kanekoZagierJacobi_of_le hCHK hl hμ hn1 h
  · exact irreducible_kanekoZagierJacobi_finiteRange hC hZ hNP hl hμ (by omega) hn2

/-- **Proposition B.2**, the range `8333 ≤ n ≤ 250000`, as the statement
`KanekoZagierFiniteRange`. Conditional on `KanekoZagierFastCriterion` and the cited
[DLMF, §18.2(vi)] and [Berger, Theorem 2.4] and proved Lemma 2.5. -/
theorem kanekoZagierFiniteRange_holds (hC : KanekoZagierFastCriterion)
    (hZ : JacobiSimpleRealZeros) (hNP : NewtonPolygonRootSlopes) : KanekoZagierFiniteRange := by
  rw [kanekoZagierFiniteRange_eq]
  intro l μ hl hμ n hn1 hn2
  exact irreducible_kanekoZagierJacobi_finiteRange hC hZ hNP hl hμ hn1 hn2

end ArithmeticOfJacobiPolynomials
