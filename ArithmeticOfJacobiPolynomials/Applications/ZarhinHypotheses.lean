/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.HyperellipticProjective
public import ArithmeticOfJacobiPolynomials.KanekoZagier.MahlburgOno
public import ArithmeticOfJacobiPolynomials.Galois.UnequalParametersGalois
public import ArithmeticOfJacobiPolynomials.Galois.FixedRationalParametersDerivatives
public import ArithmeticOfJacobiPolynomials.Applications.Jacobians

/-!
# The hypotheses of Corollary 6.6 for the families of the paper (§6.5)

This file proves that the polynomials satisfy its hypotheses: separable of degree
at least nine with symmetric Galois group. The smooth projective model
`y² = f(x)` is smooth and proper in each case. The finite Kaneko–Zagier range
is discharged by `zarhinHypotheses_kanekoZagierJacobi'` in `IrreducibilityAndGalois`.

* Kaneko–Zagier family `f = P_d^{(λ/3, μ/2)}`, `d ≥ 9` (from Theorem 1.1; Proposition B.2 enters
  as the hypothesis `KanekoZagierFiniteRange`, exactly as in `mahlburgOno_of_finiteRange`);
* `f = P_d^{(a,b)}` for unequal `a, b` and `d ≥ max {9, N(a,b)}` (Theorem 1.3);
* `f = Q_{m,r,δ}` for fixed `r` and large `m` (Corollary 1.7).
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial AlgebraicGeometry

/-- The hypotheses of Corollary 6.6 on `f`: separable of degree `d ≥ 9`, Galois group `S_d`. -/
def ZarhinHypotheses (f : ℚ[X]) : Prop :=
  f.Separable ∧ 9 ≤ f.natDegree ∧ GaloisGroupIsSymmetric f

theorem zarhinHypotheses_iff (f : ℚ[X]) : ZarhinHypotheses f ↔
    f.Separable ∧ 9 ≤ f.natDegree ∧ GaloisGroupIsSymmetric f := Iff.rfl

/-- Under the hypotheses of Corollary 6.6, the projective model of `y² = f(x)` is smooth and
proper over `ℚ`, and its genus parameter is `⌊(d-1)/2⌋`. -/
theorem ZarhinHypotheses.smooth_isProper {f : ℚ[X]} (h : ZarhinHypotheses f) :
    Smooth (Hyperelliptic.toSpecField f) ∧ IsProper (Hyperelliptic.toSpecField f) ∧
      Hyperelliptic.genus f = (f.natDegree - 1) / 2 :=
  ⟨Hyperelliptic.smooth_toSpecField (by norm_num) h.1 (by have := h.2.1; omega),
    Hyperelliptic.isProper_toSpecField f, rfl⟩

theorem zarhinHypotheses_of_irreducible {f : ℚ[X]} (hirr : Irreducible f)
    (hd : 9 ≤ f.natDegree) (hS : GaloisGroupIsSymmetric f) : ZarhinHypotheses f :=
  ⟨hirr.separable, hd, hS⟩

/-- **Kaneko–Zagier family.** For `λ, μ ∈ {±1}` and `d ≥ 9`, `P_d^{(λ/3, μ/2)}` satisfies the
hypotheses of Corollary 6.6 (from Theorem 1.1, with Proposition B.2 as the hypothesis `hB2`). -/
theorem zarhinHypotheses_kanekoZagierJacobi (hCHK : CullinanHajirKanekoZagierIrreducibility)
    (hB2 : KanekoZagierFiniteRange)
    (hZ : JacobiSimpleRealZeros)
    (hNP : NewtonPolygonRootSlopes) (hH : HansonLcmBound) (hT : BMORThetaBound)
    (hS : BMORThetaSmallBound) (hBMOR : BMORPrimeCountingBound)
    (hBT : BrunTitchmarshInequality) (hJones : JonesCycleTheorem)
    (hCHKG : CullinanHajirKanekoZagierGalois) {l μ : ℤ} (hl : l = 1 ∨ l = -1)
    (hμ : μ = 1 ∨ μ = -1) {d : ℕ} (hd : 9 ≤ d) :
    ZarhinHypotheses (kanekoZagierJacobi l μ d) := by
  obtain ⟨hirr, hgal⟩ := mahlburgOno_of_finiteRange hCHK hB2 hZ hNP hH hT hS hBMOR hBT hJones
    hCHKG l μ hl hμ d (by omega)
  exact zarhinHypotheses_of_irreducible hirr (by rw [natDegree_kanekoZagierJacobi hμ]; exact hd)
    hgal

/-- **Unequal integral parameters.** For distinct `a, b ∈ ℕ` there is `N(a,b)` such that
`P_d^{(a,b)}` satisfies the hypotheses of Corollary 6.6 for every `d ≥ max {9, N(a,b)}`
(from Theorem 1.3). -/
theorem exists_zarhinHypotheses_jacobiP (hH : HansonLcmBound)
    (hZ : JacobiSimpleRealZeros) (hJordan : JordanPrimeCycleTheorem)
    (hEis : EisensteinPrimeTotallyRamified)
    (hdisc : JacobiDiscriminantFormula) (hDusart : DusartThetaBound) {a b : ℕ} (hab : a ≠ b) :
    ∃ N : ℕ, ∀ d ≥ max 9 N, ZarhinHypotheses (jacobiP a b d) := by
  obtain ⟨N, hN⟩ := unequalIntegralParameters hH hZ hJordan hEis hdisc hDusart a b hab
  refine ⟨N, fun d hd => ?_⟩
  obtain ⟨hirr, hgal⟩ := hN d (le_trans (le_max_right _ _) hd)
  exact zarhinHypotheses_of_irreducible hirr
    (by rw [natDegree_jacobiP_nat]; exact le_trans (le_max_left _ _) hd) hgal

/-- **Derivative families.** For fixed `r` there is `N` such that `Q_{m,r,δ}` satisfies the
hypotheses of Corollary 6.6 for every `m ≥ max {9, N}` and `δ ∈ {0, 1}` (from Corollary 1.7 with
`E = ℚ`). -/
theorem exists_zarhinHypotheses_reducedGegenbauerSquare (hQ : GegenbauerQuadraticTransformation)
    (hH : HansonLcmBound) (hZ : JacobiSimpleRealZeros)
    (hBMOR : BMORPrimeCountingBound) (h619 : BMORLargeModulusPrimeCounting)
    (hBT : BrunTitchmarshInequality) (hJones : JonesCycleTheorem) (r : ℕ) :
    ∃ N : ℕ, ∀ m ≥ max 9 N, ∀ δ : ℕ, δ ≤ 1 →
      ZarhinHypotheses (reducedGegenbauerSquare m r δ) := by
  obtain ⟨N, hN⟩ := fixedDerivativesGaloisStatement hQ hH hZ hBMOR h619 hBT hJones r ℚ
  refine ⟨N, fun m hm δ hδ => ?_⟩
  obtain ⟨-, -, hirr, hgal, -, -⟩ := hN m (le_trans (le_max_right _ _) hm) δ hδ
  have e : (reducedGegenbauerSquare m r δ).map (algebraMap ℚ ℚ) = reducedGegenbauerSquare m r δ :=
    by rw [Algebra.algebraMap_self, Polynomial.map_id]
  rw [e] at hirr hgal
  exact zarhinHypotheses_of_irreducible hirr
    (by rw [natDegree_reducedGegenbauerSquare]; exact le_trans (le_max_left _ _) hm) hgal

open FixedRationalParameters Filter in
/-- **The dominant-factor application**, §6.5. For all sufficiently
large `n`, every dominant factor in Theorem 1.6 satisfies Corollary 6.6 with
its degree `h.natDegree` (which may be less than the Jacobi degree `n`). -/
theorem exists_zarhinHypotheses_dominant_jacobiP (hBMOR : BMORPrimeCountingBound)
    (h619 : BMORLargeModulusPrimeCounting) (hBT : BrunTitchmarshInequality)
    (hJones : JonesCycleTheorem) {α β : ℚ}
    (hcond : FixedRationalParameters.DenomCond α β) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ h : ℚ[X],
      FixedRationalParameters.IsDominant (jacobiP α β n) h → ZarhinHypotheses h := by
  classical
  obtain ⟨N₀, hN₀⟩ := galoisGroupIsSymmetric_isDominant_jacobiP hBMOR h619 hBT hJones hcond
  obtain ⟨C₀, N₁, hN₁⟩ := natDegree_isDominant_jacobiP h619 hcond 1 one_pos
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((eventually_le_log_natCast (10 * |C₀| + 1)).and
      (eventually_ge_atTop (N₀ + N₁ + 100)))
  refine ⟨N, fun n hn h hh => ?_⟩
  obtain ⟨hL, hn'⟩ := hN n hn
  have hhd := (isDominant_iff _ _).mp hh
  have hM := hN₁ n (by omega) h hh
  rw [Real.rpow_one] at hM
  have hn100 : (100 : ℝ) ≤ n := by exact_mod_cast (show 100 ≤ n by omega)
  have hlogpos : 0 < Real.log n := by linarith [abs_nonneg C₀]
  have hCn : C₀ * n / Real.log n ≤ 0.1 * n := by
    rw [div_le_iff₀ hlogpos]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ n)
      (by linarith [le_abs_self C₀] : (0 : ℝ) ≤ Real.log n - 10 * C₀)]
  have hdegree : 9 ≤ h.natDegree := by
    have : (9 : ℝ) ≤ h.natDegree := by linarith
    exact_mod_cast this
  have hf0 : jacobiP α β n ≠ 0 := by
    intro hz
    have hv := eval_one_ne_zero_of_dvd ((denomCond_iff _ _).mp hcond).2.2.1
      (dvd_refl (jacobiP α β n))
    simp [hz] at hv
  obtain ⟨g, κ, hg, hfac⟩ := exists_monic_cofactor hf0 hhd.2.2.1
  exact zarhinHypotheses_of_irreducible hhd.2.1 hdegree
    (hN₀ n (by omega) h g κ hh hg hfac).1

end ArithmeticOfJacobiPolynomials
