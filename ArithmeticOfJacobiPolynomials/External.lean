/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.EtaleCycleClassInterface
public import ArithmeticOfJacobiPolynomials.Analysis.IntervalVandermonde
public import ArithmeticOfJacobiPolynomials.KanekoZagier.FiniteRangeQuantities
public import ArithmeticOfJacobiPolynomials.Jacobi.LegendreDerivativeData
public import ArithmeticOfJacobiPolynomials.Padic.NewtonHullDef
public import ArithmeticOfJacobiPolynomials.Padic.ProjectiveDistance

public import ArithmeticOfJacobiPolynomials.Algebra.AbelianTateLie
public import ArithmeticOfJacobiPolynomials.Geometry.WeilPairingGeometry
public import ArithmeticOfJacobiPolynomials.Algebra.JacobiParameters
public import ArithmeticOfJacobiPolynomials.Algebra.HyperellipticModel
public import ArithmeticOfJacobiPolynomials.Geometry.JacobianPolarization
public import ArithmeticOfJacobiPolynomials.Geometry.AbelianBettiHodge
public import ArithmeticOfJacobiPolynomials.Geometry.AbelianBettiCohomology
public import ArithmeticOfJacobiPolynomials.Geometry.AbelianBettiPolarizationInterface
public import ArithmeticOfJacobiPolynomials.Geometry.AbelianArithmeticInterface
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import ArithmeticOfJacobiPolynomials.Algebra.ZarhinGroups
public import ArithmeticOfJacobiPolynomials.Algebra.GroupObjectEnd
public import ArithmeticOfJacobiPolynomials.Galois.Defs
public import ArithmeticOfJacobiPolynomials.Jacobi.Legendre
public import ArithmeticOfJacobiPolynomials.Jacobi.Endpoints
public import ArithmeticOfJacobiPolynomials.NumberTheory.PrimeCounting
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import ArithmeticOfJacobiPolynomials.Elliptic.Supersingular
public import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
public import Mathlib.FieldTheory.Finite.Basic
public import ArithmeticOfJacobiPolynomials.Modular.JInvariant
public import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# External inputs

General cited literature and background are explicit propositions. The manuscript's
reported computations appear separately in `section ComputerVerified`.

The inventory below gives the declaration names relative to
`ArithmeticOfJacobiPolynomials`, citation keys from `references.bib`, source locators and
one-line statements. The declaration docstrings specify the full hypotheses and source
qualifications.

## Cited literature

- `DengLegendreIrreducibility` — [Deng, Theorem 1.1] (arXiv preprint 2609.22336v2). Even Legendre
  polynomials and odd Legendre
  polynomials divided by x are irreducible over ℚ.
- `JacobiSimpleRealZeros` — [DLMF, §18.2(vi), Table 18.3.1; normalization 18.5.8]. For real
  parameters greater than −1, the degree-n Jacobi polynomial has n distinct roots in (−1,1).
- `GegenbauerQuadraticTransformation` — [DLMF, 18.7.15–18.7.16; normalizations 18.5.8, 18.5.10].
  Even and odd Gegenbauer polynomials are scalar multiples of quadratic transforms of Jacobi
  polynomials in characteristic zero.
- `DusartThetaBound` — [Dusart10, Theorem 5.2, column k = 2]. For x ≥ 3594641, the theta function
  differs from x by less than 0.2x/log²x.
- `JacobiDiscriminantFormula` — [DLMF, 18.16.19; root-product normalization 18.2.20]. The Jacobi
  discriminant is the stated product for arbitrary characteristic-zero parameters and a root
  factorization.
- `BMORLargeModulusPrimeCounting` — [BMOR, Proposition 6.19, (6.23), Definition 6.1; arXiv v3].
  Prime counts in reduced residue classes satisfy the explicit logarithmic estimate above the
  stated large-modulus threshold.
- `BMORThetaBound` — [BMOR, Corollary 1.7, second part; arXiv v3]. The theta function in each
  reduced residue class satisfies the explicit large-x estimate.
- `BMORThetaSmallBound` — [BMOR, Theorem 1.9, (1.18)]. The theta function in each reduced residue
  class satisfies the stated estimate for small moduli.
- `CullinanHajirKanekoZagierIrreducibility` — [CHK, Remark 4.6, Definition 2.3]. The cited Magma
  computation establishes irreducibility of all four Kaneko–Zagier families through degree 8332.
- `JacobiQuadraticTransformation` — [DLMF, 18.7.13–18.7.14]. Even and odd symmetric-parameter
  Jacobi polynomials satisfy the quadratic transformation identities.
- `JonesCycleTheorem` — [Jones, Corollary 1.3]. A primitive permutation group containing a single
  cycle (of any length) with at least three fixed points contains the alternating group.
- `JordanPrimeCycleTheorem` — [Jones, Theorem 1.1] (Jordan). A primitive permutation group
  containing a single cycle of prime length with at least three fixed points contains the
  alternating group.
- `EisensteinPrimeTotallyRamified` — [Milne, ANT v3.08, Proposition 3.53] (also Proposition 7.55,
  direction `⇐`, for complete discretely valued fields). For a Dedekind domain `A` and a monic
  polynomial Eisenstein at a nonzero prime `𝔭`, the field generated by a root is such that `𝔭` is
  totally ramified in it: every prime over `𝔭` has ramification index equal to the degree.
- `NewtonPolygonRootSlopes` — [Berger, Theorem 2.4, p. 4]. For every prime `p` and nonzero
  polynomial over `PadicAlgCl p`, the valuations of the nonzero roots, with multiplicity, are the
  negatives of the unit-step slopes of the lower convex hull of the points `(j, v_p(c_j))`.
- `BMORPrimeCountingBound` — [BMOR, Corollary 1.7, second part; arXiv v3]. Prime counts in reduced
  residue classes satisfy the stated explicit estimate.
- `BrunTitchmarshInequality` — [MV, Theorem 2, (1.10), p. 121]. For x > 0 and y > q, the number of
  primes in the reduced residue class a mod q in the interval (x, x + y] is less than
  2y/(φ(q)log(y/q)).
- `HansonLcmBound` — [Hanson, Theorem 1]. The least common multiple of 1,…,n is less than 3ⁿ for n
  ≥ 1.
- `PrimesModFourInDyadicInterval` — [CHL, Lemma 2.2]. For integer x ≥ 9 each odd residue class
  modulo 4 contains a prime in the stated interval.
- `CullinanHajirKanekoZagierGalois` — [CHK, Theorem 1.8, (3)]. Irreducible Kaneko–Zagier lifts have
  symmetric Galois group in the cited parameter ranges.
- `CullinanHajirLegendreGalois` — [CHL, Theorem 1.9(a), Lemma 1.2]. When irreducible, the
  Legendre quotient `J_n^ε` has full symmetric Galois group for `n ≤ 10^9`.
- `KanekoZagierSupersingularReduction` — [KZ, Theorem 1, (10)–(12), Theorem 5(ii)]. At a prime
  index the source hypergeometric polynomial is integral at that prime and reduces to the
  supersingular j-polynomial with the stated factors.
- `BSSResidueCriterion` — [BSS, §2, (2.2)–(2.4)]. Solutions of the stated pole equations make the
  reducible weight-two modular form have zero residues.
- `LegendreElliptic.HasseSupersingularCriterion` — [KZ, §2, Proposition 1 and Corollary]. Over a
  finite field of odd characteristic p, an elliptic monic cubic is supersingular exactly when its
  Hasse coefficient vanishes.
- `Zarhin.GeometricEndomorphisms` — [Zarhin02, Theorem 2.4, final assertion]. Hyperelliptic
  Jacobians of the stated degree and Galois type have geometric endomorphism ring ℤ.
- `Zarhin.TateLieAlgebra` — [Zarhin02, Theorem 2.6, §2]. Over characteristic-zero fields finitely
  generated over ℚ, the Tate Lie algebra of an admissible hyperelliptic Jacobian is scalar plus
  symplectic.
- `Zarhin.HodgeAndMumfordTateGroups` — [Zarhin02; Deligne82, Zarhin Theorem 9.1, proof and Remark
  9.2; Deligne Propositions 3.4, 3.6]. Derived from Zarhin's Lie-algebra equality and Deligne's
  connectedness results: the canonical Hodge and Mumford–Tate groups of admissible hyperelliptic
  Jacobians are the symplectic and similitude groups.
- `JacobianArithmeticInputs.HodgeClassDivisorProducts` — [Zarhin02, Theorem 9.1]. Hodge classes on
  all powers of admissible hyperelliptic Jacobians are generated by products of divisor classes.
- `JacobianArithmeticInputs.MumfordTateLieEquality` — [Zarhin02, Theorem 9.1, proof and Remark
  9.2]. The Betti–Tate comparison identifies the Tate Lie algebra with the ℚℓ-span of the
  Mumford–Tate Lie algebra.
- `Zarhin.TateClassesDivisorProducts` — [Zarhin02, Theorem 8.1, characteristic-zero alternative].
  Tate classes on every positive power over finite extensions are generated by products of divisor
  classes.

## Assumed background

- `Jacobian.JacobianExists` — [MilneJV, Theorem 1.1, Remark 1.7, Proposition 1.9]. Every smooth
  projective geometrically irreducible curve over a field (no rational point assumed) has an
  abelian variety representing its degree-zero Picard sheaf `Pic⁰_{X/k}`, the sections of the fppf
  Picard sheaf of degree zero on every geometric fibre.
- `Jacobian.CanonicalPrincipalPolarizationExists` — [MilneJV, Theorem 6.6, Summary 6.11], with
  Galois descent from `k̄` to `k`. Every Jacobian has its canonical principal polarization from the
  Poincaré sheaf and negative normalized diagonal correspondence.
- `AbelianBettiHodge.ComplexUniformization` — [MilneAVNotes, I, Proposition 2.1(a,b), Theorem 2.3
  and proof]. Every complex abelian variety has the canonical exponential and period identification
  with singular first homology.
- `TorusBettiCupProduct` — [MilneAVNotes, I, Theorem 2.3, p. 13]. Cup products identify the
  rational cohomology of every real torus with exterior powers of first cohomology.
- `AbelianVariety.WeilPairingsExist` — [MilneAV; MumfordAV, Milne Theorem 11.1, Lemmas 16.1–16.2,
  §16; Mumford §20]. Geometric torsion of every abelian variety admits compatible
  Galois-equivariant Weil pairings, perfect over algebraically closed fields.
- `AbelianVariety.PolarizedWeilAlternating` — [MilneAV; MilneAVNotes; MumfordAV, Milne Lemma
  16.2(e), with (c,d); course notes Proposition 13.2(d); Mumford §20, §23]. The Tate pairing
  induced by a line bundle polarization is alternating.
- `AbelianBettiHodge.PolarizationRiemannForm` — [MilneAVNotes, I, Example 13.3, §12; MumfordAV, §2;
  BirkenhakeLange, Chapter 2]. Every
  line-bundle polarization induces, on periods, the canonical polarization `-E_L`, minus the
  Riemann form `E_L` of the line bundle.
- `AbelianArithmetic.BettiFirstChernExists` — [MilneAVNotes, I, Example 13.3, Theorem 2.3;
  MumfordAV, §2; BirkenhakeLange, Chapter 2]. The
  rational first Chern map is additive and agrees with the logarithmic pairing on periods, up to
  the global sign convention stated for `PolarizationRiemannForm`.
- `AbelianArithmetic.BettiTateComparisonExists` — [MilneAVNotes, I, Proposition 2.1(b), Theorem
  2.3, Theorem 7.2, Corollary 3.7]. The period lattice and geometric torsion give an
  origin-preserving Betti–Tate comparison over every subfield of ℂ.
- `AbelianArithmetic.BettiCycleClassExists` — [Fulton; MilneAVNotes, Fulton Proposition 19.1.2,
  Corollary 19.2(b), §19.3.6; Milne I, Example 13.3, Theorem 2.3]. Complex abelian varieties admit
  Betti cycle class systems compatible with Chern classes, cup products and Hodge type.
- `EtaleCycleClassInterface.KummerChartsExist` — [EGAIV4; SGA4, EGA IV₄, 17.12.1–17.12.2; SGA 4,
  VIII 1.1]. Kummer charts cover every smooth closed pair at each coefficient level.
- `EtaleCycleClassInterface.CanonicalCycleSystemExists` — [SGA4Half; SGA5; SGA4; EGAIV4; MilneLEC,
  SGA 4½, Cycle 2.1.2–2.1.3, 2.2.2–2.2.10, 2.3.2, 2.3.7–2.3.10; SGA 5, VI 3.2–3.3, I 3.1.4; SGA 4,
  XVI 3.7/3.9, VIII 1.1; EGA IV₄ 17.12.1–2; Milne 23.3(b,c)]. Smooth proper schemes admit
  compatible ℓ-adic cycle systems with supports, cup, Chern, Chow and Galois properties and a
  common orientation sign.

## Computer-verified inputs

- `KanekoZagierFastCriterion` — [Manuscript, Proposition B.2]. For all four sign pairs and 8333 ≤ n
  ≤ 250000, the endpoint logarithmic comparison holds and Δₙ > n/1000. Exact integer arithmetic
  with rational logarithm bounds and outward rounding.
- `FirstDerivativeIntegerInequalities` — [Manuscript, Lemma C.2, Appendix C.2, (C.2)]. For the 318
  pairs with 1 ≤ m ≤ 199 outside the exceptional sets, m ≥ 4 and the stated strict integer
  irreducibility inequality holds. Trial division and successive prime multiplication in integer
  arithmetic.
- `FirstDerivativeFactorDegreeChecks` — [Manuscript, Lemma C.2, Appendix C.2, Lemma C.1]. For the
  80 exceptional pairs, primitive degree-2m polynomials have squarefree degree-preserving
  reductions excluding every proper factor degree, at primes ≤ 317. Integer arithmetic and
  Euclidean division over finite fields, with 254 retained reductions and largest prime 317.

The canonical étale cycle system has a common orientation sign. The divisor-span conclusions hold
for either sign. `CanonicalCycleSystemExists` includes the chart cover stated separately in
`KummerChartsExist`.
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial

/-- **Stieltjes' irreducibility conjecture** ([Deng, Theorem 1.1]; arXiv preprint 2609.22336v2,
not a refereed publication).
For every `j ≥ 1`, the Legendre polynomials `P_{2j}(x)` and `P_{2j+1}(x)/x` are irreducible
in `ℚ[x]`. Qualifications: `P_n` is the Legendre polynomial `P_n^{(0,0)}` with `P_n(1) = 1`,
as in the source. 
Source: [Deng, Theorem 1.1] (arXiv:2609.22336v2). -/
@[expose] def DengLegendreIrreducibility : Prop :=
  ∀ j : ℕ, 1 ≤ j → Irreducible (reducedLegendre j 0) ∧ Irreducible (reducedLegendre j 1)

/-- **Zeros of Jacobi polynomials** ([DLMF, §18.2(vi)], with the Jacobi weight,
interval and parameter range in [DLMF, Table 18.3.1]). For all real `α, β > -1`,
`P_n^{(α,β)}` has exactly `n` distinct roots, all in `(-1,1)`. The normalization
is [DLMF, 18.5.8]. 
Source: [DLMF, §18.2(vi), Table 18.3.1; normalization 18.5.8]. -/
@[expose] def JacobiSimpleRealZeros : Prop :=
  ∀ α β : ℝ, -1 < α → -1 < β → ∀ n : ℕ,
    (jacobiPolynomial α β n).roots.Nodup ∧
    (jacobiPolynomial α β n).roots.card = n ∧
    ∀ x ∈ (jacobiPolynomial α β n).roots, -1 < x ∧ x < 1

/-- The rational-parameter instance follows by coefficient transport. -/
theorem JacobiSimpleRealZeros.rat (h : JacobiSimpleRealZeros) (α β : ℚ)
    (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    ((jacobiP α β n).map (algebraMap ℚ ℝ)).roots.Nodup ∧
    ((jacobiP α β n).map (algebraMap ℚ ℝ)).roots.card = n ∧
    ∀ x ∈ ((jacobiP α β n).map (algebraMap ℚ ℝ)).roots, -1 < x ∧ x < 1 := by
  simpa only [map_jacobiP_real] using h (α : ℝ) (β : ℝ)
    (by exact_mod_cast hα) (by exact_mod_cast hβ) n

/-- **Quadratic transformations of Gegenbauer polynomials** ([DLMF, 18.7.15–18.7.16]).
These are algebraic polynomial identities, in the normalizations [DLMF, 18.5.8 and 18.5.10].
The rising factorials `(1/2)_n` in the denominators are nonzero in characteristic zero.
Both sides are polynomials in the parameter `ν`, so [DLMF]'s real-parameter statement
extends to every field of characteristic zero. 
Source: [DLMF, 18.7.15–18.7.16; normalizations 18.5.8, 18.5.10]. -/
@[expose] def GegenbauerQuadraticTransformation : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ν : K) (n : ℕ),
    gegenbauerPolynomial ν (2 * n) =
      C ((ascPochhammer K n).eval ν / (ascPochhammer K n).eval (1 / 2)) *
        (jacobiPolynomial (ν - 1 / 2) (-1 / 2) n).comp (2 * polyX ^ 2 - 1) ∧
    gegenbauerPolynomial ν (2 * n + 1) =
      C ((ascPochhammer K (n + 1)).eval ν / (ascPochhammer K (n + 1)).eval (1 / 2)) * polyX *
        (jacobiPolynomial (ν - 1 / 2) (1 / 2) n).comp (2 * polyX ^ 2 - 1)

/-- The rational Gegenbauer identity, used for the manuscript's derivative families. -/
theorem GegenbauerQuadraticTransformation.rat (h : GegenbauerQuadraticTransformation)
    (ν : ℚ) (n : ℕ) :
    gegenbauerC ν (2 * n) = C ((ascPochhammer ℚ n).eval ν / (ascPochhammer ℚ n).eval (1 / 2)) *
      (jacobiP (ν - 1 / 2) (-1 / 2) n).comp (2 * polyX ^ 2 - 1) ∧
    gegenbauerC ν (2 * n + 1) =
      C ((ascPochhammer ℚ (n + 1)).eval ν / (ascPochhammer ℚ (n + 1)).eval (1 / 2)) * polyX *
        (jacobiP (ν - 1 / 2) (1 / 2) n).comp (2 * polyX ^ 2 - 1) := by
  simpa only [gegenbauerPolynomial_rat, jacobiPolynomial_rat] using h ℚ ν n

/-- **Explicit prime number theorem for `ϑ`** ([Dusart10, Theorem 5.2], column `k = 2`:
`η_2 = 0.2`, `x_2 = 3 594 641`; arXiv:1002.0442v1). For real `x ≥ 3 594 641`,
`|ϑ(x) - x| < 0.2 x / log² x`, where `ϑ(x) = ∑_{p ≤ x} log p` (Mathlib's `Chebyshev.theta`).
Qualifications: none. 
Source: [Dusart10, Theorem 5.2, column k = 2]. -/
@[expose] def DusartThetaBound : Prop :=
  ∀ x : ℝ, 3594641 ≤ x → |Chebyshev.theta x - x| < 0.2 * x / Real.log x ^ 2

/-- The Jacobi discriminant value
`2^{-n(n-1)} ∏_{h=1}^n h^{h-2n+2} (h+a)^{h-1} (h+b)^{h-1} (n+h+a+b)^{n-h}`
of [DLMF, 18.16.19] (manuscript (5.31), §5.6). -/
noncomputable def jacobiDiscriminant (a b n : ℕ) : ℚ :=
  (2 : ℚ)⁻¹ ^ (n * (n - 1)) * ∏ h ∈ Finset.Icc 1 n,
    ((h : ℚ) ^ ((h : ℤ) - 2 * n + 2) * ((h : ℚ) + a) ^ (h - 1) * ((h : ℚ) + b) ^ (h - 1) *
      ((n : ℚ) + h + a + b) ^ (n - h))

theorem jacobiDiscriminant_eq (a b n : ℕ) : jacobiDiscriminant a b n =
    (2 : ℚ)⁻¹ ^ (n * (n - 1)) * ∏ h ∈ Finset.Icc 1 n,
      ((h : ℚ) ^ ((h : ℤ) - 2 * n + 2) * ((h : ℚ) + a) ^ (h - 1) * ((h : ℚ) + b) ^ (h - 1) *
        ((n : ℚ) + h + a + b) ^ (n - h)) := (rfl)

/-- **Discriminant of Jacobi polynomials** ([DLMF, 18.16.19], with the root-product
normalization of [DLMF, 18.2.20]). This is the algebraic formula for arbitrary parameters in
characteristic zero and for any list of roots giving the indicated factorization.
Both sides are polynomials in `α` and `β`, so [DLMF]'s real-parameter statement extends to every
field of characteristic zero. 
Source: [DLMF, 18.16.19; root-product normalization 18.2.20]. -/
@[expose] def JacobiDiscriminantFormula : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (α β : K) (n : ℕ) (x : Fin n → K),
    jacobiPolynomial α β n =
        C (jacobiPolynomial α β n).leadingCoeff * ∏ i, (polyX - C (x i)) →
      (jacobiPolynomial α β n).leadingCoeff ^ (2 * n - 2) *
          ∏ i, ∏ j ∈ Finset.Ioi i, (x i - x j) ^ 2 =
        (2 : K)⁻¹ ^ (n * (n - 1)) * ∏ h ∈ Finset.Icc 1 n,
          ((h : K) ^ ((h : ℤ) - 2 * n + 2) * ((h : K) + α) ^ (h - 1) *
            ((h : K) + β) ^ (h - 1) * ((n : K) + h + α + β) ^ (n - h))

/-- The integral-parameter rational instance of the discriminant identity. -/
theorem JacobiDiscriminantFormula.rat (h : JacobiDiscriminantFormula)
    (a b n : ℕ) (K : Type) [Field K] [Algebra ℚ K] (x : Fin n → K)
    (hfac : (jacobiP a b n).map (algebraMap ℚ K) =
      C (algebraMap ℚ K (jacobiP a b n).leadingCoeff) * ∏ i, (polyX - C (x i))) :
    algebraMap ℚ K ((jacobiP a b n).leadingCoeff ^ (2 * n - 2)) *
        ∏ i, ∏ j ∈ Finset.Ioi i, (x i - x j) ^ 2 =
      algebraMap ℚ K (jacobiDiscriminant a b n) := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  have hp : (jacobiP a b n).map (algebraMap ℚ K) =
      jacobiPolynomial (a : K) (b : K) n := by
    rw [← jacobiPolynomial_rat, map_jacobiPolynomial]
    simp only [map_natCast]
  have hlead : (jacobiPolynomial (a : K) (b : K) n).leadingCoeff =
      algebraMap ℚ K (jacobiP a b n).leadingCoeff := by
    rw [← hp, Polynomial.leadingCoeff_map_of_injective (algebraMap ℚ K).injective]
  have hfac' : jacobiPolynomial (a : K) (b : K) n =
      C (jacobiPolynomial (a : K) (b : K) n).leadingCoeff * ∏ i, (polyX - C (x i)) := by
    rw [hlead, ← hp]
    exact hfac
  have hd := h K (a : K) (b : K) n x hfac'
  simpa only [hlead, jacobiDiscriminant_eq, map_mul, map_pow, map_prod, map_inv₀,
    map_ofNat, map_natCast, map_add, map_zpow₀] using hd

/-- **Explicit prime number theorem for large moduli** ([BMOR, Proposition 6.19], with (6.23) and
`R₁ = 9.645908801` of [BMOR, Definition 6.1]; numbering of arXiv:1802.00085v3). Let `q ≥ 10^5`, let
`a` be an integer prime to `q`, and let `Z > 0`, `κ₁ ≥ 0.0132`, `κ₂ > 1`, `κ₃ > 1` satisfy (6.23):
`Z ≤ min{460.516 κ₁/(log κ₁ + 13.087), (√(κ₂/R₁) - 0.85317)/log κ₂ - 1/2, (κ₃ - 6.44)/(2 log κ₃)}`.
If `x/(log x)^{Z+1} ≥ 2000 exp(max{κ₁ √q log³ q, κ₂, κ₃, Z + 28})`, then
`|π(x; q, a) - Li(x)/φ(q)| ≤ x/(4 (log x)^{Z+1})`.
Qualifications: stated only for `x ≥ x₄ = exp(max{κ₁ √q log³ q, κ₂, κ₃, Z + 28})`, the range of the
source's proof (its `x₅ > x₄`); this excludes `x` near `1`, where the real power is degenerate. 
Source: [BMOR, Proposition 6.19, (6.23), Definition 6.1; numbering of arXiv v3]. -/
@[expose] def BMORLargeModulusPrimeCounting : Prop :=
  ∀ (q : ℕ) (a : ℤ) (Z κ₁ κ₂ κ₃ : ℝ), 10 ^ 5 ≤ q → Int.gcd a q = 1 → 0 < Z → 0.0132 ≤ κ₁ →
    1 < κ₂ → 1 < κ₃ → Z ≤ 460.516 * κ₁ / (Real.log κ₁ + 13.087) →
    Z ≤ (Real.sqrt (κ₂ / 9.645908801) - 0.85317) / Real.log κ₂ - 1 / 2 →
    Z ≤ (κ₃ - 6.44) / (2 * Real.log κ₃) → ∀ x : ℝ,
    Real.exp (max (max (κ₁ * Real.sqrt q * Real.log q ^ 3) κ₂) (max κ₃ (Z + 28))) ≤ x →
    2000 * Real.exp (max (max (κ₁ * Real.sqrt q * Real.log q ^ 3) κ₂) (max κ₃ (Z + 28))) ≤
      x / Real.log x ^ (Z + 1) →
    |(primeCountingAP x q a : ℝ) - logIntegral x / q.totient| ≤ x / (4 * Real.log x ^ (Z + 1))

/-- `θ(x; q, a) = ∑_{p ≤ x, p ≡ a (mod q)} log p`. -/
noncomputable def chebyshevThetaAP (x : ℝ) (q : ℕ) (a : ℤ) : ℝ :=
  ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ (p : ℤ) ≡ a [ZMOD q]),
    Real.log p

theorem chebyshevThetaAP_eq (x : ℝ) (q : ℕ) (a : ℤ) : chebyshevThetaAP x q a =
    ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ (p : ℤ) ≡ a [ZMOD q]),
      Real.log p := (rfl)

/-- **Explicit prime number theorem in progressions, `θ` form** ([BMOR, Corollary 1.7], second
part; arXiv:1802.00085v3). For `1 ≤ q ≤ 10^5`, `gcd(a, q) = 1` and `x ≥ 10^6`,
`|θ(x; q, a) - x/φ(q)| < 0.024 x / log x`. Qualifications: only the `θ` bound for `x ≥ 10^6` is
stated. 
Source: [BMOR, Corollary 1.7, second part; arXiv v3]. -/
@[expose] def BMORThetaBound : Prop :=
  ∀ (q : ℕ) (a : ℤ), 1 ≤ q → q ≤ 10 ^ 5 → Int.gcd a q = 1 → ∀ x : ℝ, 10 ^ 6 ≤ x →
    |chebyshevThetaAP x q a - x / q.totient| < 0.024 * x / Real.log x

/-- The small-`x` threshold `x₂(q)` in [BMOR, (1.18)]. A modulus congruent to
`2 (mod 4)` is reduced to its odd half, exactly as in the source. -/
@[expose] def bmorSmallThreshold (q : ℕ) : ℝ :=
  let q' := if q % 4 = 2 then q / 2 else q
  if q' = 1 then 10 ^ 12
  else if q' = 3 ∨ q' = 4 ∨ q' = 5 then 4 * 10 ^ 13
  else if q' ≤ 100 then 10 ^ 13
  else if q' ≤ 10 ^ 4 then 10 ^ 12
  else 10 ^ 11

/-- **Explicit small-`x` theta bound** ([BMOR, Theorem 1.9] and (1.18);
arXiv:1802.00085v3, published numerical verification). For every `1 ≤ q ≤ 10^5`, `gcd(a,q)=1`, and
`1 ≤ y ≤ x ≤ x₂(q)`, `|θ(y;q,a)-y/φ(q)| ≤ 2.072 √x`.
This states the theta component over the full modulus and real-argument ranges. 
Source: [BMOR, Theorem 1.9, (1.18)]. -/
@[expose] def BMORThetaSmallBound : Prop :=
  ∀ (q : ℕ) (a : ℤ), 1 ≤ q → q ≤ 10 ^ 5 → Int.gcd a q = 1 →
    ∀ x y : ℝ, 1 ≤ y → y ≤ x → x ≤ bmorSmallThreshold q →
      |chebyshevThetaAP y q a - y / q.totient| ≤ 2.072 * √x

/-- The modulus-six instance used in the appendix follows from the full cited bound. -/
theorem BMORThetaSmallBound.modSix (h : BMORThetaSmallBound)
    (a : ℤ) (ha : Int.gcd a 6 = 1) (x y : ℝ)
    (hy : 1 ≤ y) (hyx : y ≤ x) (hx : x ≤ 4 * 10 ^ 13) :
    |chebyshevThetaAP y 6 a - y / 2| ≤ 2.072 * √x := by
  have hd := h 6 a (by norm_num) (by norm_num) ha x y hy hyx
    (by simpa [bmorSmallThreshold] using hx)
  norm_num at hd ⊢
  exact hd

/-- **Irreducibility of the Kaneko–Zagier lifts through index `10^5`** ([CHK, Remark 4.6], with
[CHK, Definition 2.3]; published computer verification). For `λ, μ ∈
{-1, 1}`, `n ≥ 1` and
`ℓ = 12n + 6 + 2λ + 3μ ≤ 10^5`, the polynomial `K_ℓ(X) = 3^n n! P_n^{(λ/3,μ/2)}(4X + 1)` is
irreducible over `ℚ`. Qualifications: [CHK, Definition 2.3] defines `K_ℓ(x) = 3^n n! J_n(2x)`
with `J_n(x) = P_n^{(λ/3,μ/2)}(2x + 1)` (§2.2), i.e. `K_ℓ(X) = 3^n n! P_n(4X + 1)`; Remark 4.6
reports a published Magma computation; the argument `l` is `λ`. 
Source: [CHK, Remark 4.6, Definition 2.3]. -/
@[expose] def CullinanHajirKanekoZagierIrreducibility : Prop :=
  ∀ l μ : ℤ, (l = 1 ∨ l = -1) → (μ = 1 ∨ μ = -1) → ∀ n : ℕ, 1 ≤ n →
    12 * (n : ℤ) + 6 + 2 * l + 3 * μ ≤ 10 ^ 5 →
    Irreducible (C ((3 : ℚ) ^ n * n.factorial) *
      (jacobiP ((l : ℚ) / 3) ((μ : ℚ) / 2) n).comp (4 * polyX + 1))

/-- **Quadratic transformations of Jacobi polynomials** ([DLMF, 18.7.13–18.7.14]).
These are the algebraic identities obtained by multiplying the displayed quotients by their
nonzero denominators. Parameters range over characteristic-zero fields without a rational
or orthogonality-range restriction. The cross-multiplied identity is polynomial in `α`, so
[DLMF]'s real-parameter statement extends to every field of characteristic zero. 
Source: [DLMF, 18.7.13–18.7.14]. -/
@[expose] def JacobiQuadraticTransformation : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (α : K) (n : ℕ),
    ((jacobiPolynomial α α (2 * n)).eval 1 ≠ 0 →
      (jacobiPolynomial α (-1 / 2) n).eval 1 ≠ 0 →
      C ((jacobiPolynomial α (-1 / 2) n).eval 1) * jacobiPolynomial α α (2 * n) =
        C ((jacobiPolynomial α α (2 * n)).eval 1) *
          (jacobiPolynomial α (-1 / 2) n).comp (2 * polyX ^ 2 - 1)) ∧
    ((jacobiPolynomial α α (2 * n + 1)).eval 1 ≠ 0 →
      (jacobiPolynomial α (1 / 2) n).eval 1 ≠ 0 →
      C ((jacobiPolynomial α (1 / 2) n).eval 1) * jacobiPolynomial α α (2 * n + 1) =
        C ((jacobiPolynomial α α (2 * n + 1)).eval 1) *
          (polyX * (jacobiPolynomial α (1 / 2) n).comp (2 * polyX ^ 2 - 1)))

private theorem jacobi_endpoint_ne_zero {α : ℚ} (hα : -1 < α) (β : ℚ) (n : ℕ) :
    (jacobiP α β n).eval 1 ≠ 0 := by
  rw [jacobiP_eval_one]
  intro hz
  have he := Ring.descPochhammer_eq_factorial_smul_choose ((n : ℚ) + α) n
  rw [hz, smul_zero, descPochhammer_smeval_eq_ascPochhammer,
    ascPochhammer_smeval_eq_eval] at he
  have he' : (ascPochhammer ℚ n).eval (α + 1) = 0 := by
    convert he using 1
    congr 1
    ring
  exact (ascPochhammer_pos n (α + 1) (by linarith)).ne' he'

/-- The rational-parameter instance, with the denominators proved nonzero. -/
theorem JacobiQuadraticTransformation.rat (h : JacobiQuadraticTransformation)
    (α : ℚ) (hα : -1 < α) (n : ℕ) :
    C ((jacobiP α (-1 / 2) n).eval 1) * jacobiP α α (2 * n) =
      C ((jacobiP α α (2 * n)).eval 1) * (jacobiP α (-1 / 2) n).comp (2 * polyX ^ 2 - 1) ∧
    C ((jacobiP α (1 / 2) n).eval 1) * jacobiP α α (2 * n + 1) =
      C ((jacobiP α α (2 * n + 1)).eval 1) * (polyX * (jacobiP α (1 / 2) n).comp (2 * polyX ^ 2
        - 1)) := by
  have he := jacobi_endpoint_ne_zero hα
  have h0 := (h ℚ α n).1
    (by simpa only [jacobiPolynomial_rat] using he α (2 * n))
    (by simpa only [jacobiPolynomial_rat] using he (-1 / 2) n)
  have h1 := (h ℚ α n).2
    (by simpa only [jacobiPolynomial_rat] using he α (2 * n + 1))
    (by simpa only [jacobiPolynomial_rat] using he (1 / 2) n)
  simpa only [jacobiPolynomial_rat] using And.intro h0 h1

/-- **Jones's cycle theorem** ([Jones, Corollary 1.3]; arXiv:1209.5169).
A primitive permutation group of finite degree `n` containing a cycle with `k ≥ 3` fixed
points contains the alternating group `A_n`. Qualifications: only the case `k ≥ 3` of the
corollary is stated; a cycle is a nontrivial single cycle (`Equiv.Perm.IsCycle`), and its
number of fixed points is `n` minus the size of its support. The proof of Lemma 5.16 does not use
this hypothesis; it uses `JordanPrimeCycleTheorem`, as the manuscript does. This hypothesis is
used where the manuscript cites [Jones, Corollary 1.3] for cycles of arbitrary length, namely
for the even cycles of Proposition 5.7 and Theorem 1.6, and for the quoted Theorem 5.4; a result
that combines those with Lemma 5.16 carries both hypotheses.
Source: [Jones, Corollary 1.3]. -/
@[expose] def JonesCycleTheorem : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (G : Subgroup (Equiv.Perm α)),
    MulAction.IsPreprimitive G α → ∀ σ ∈ G, σ.IsCycle →
      3 ≤ Fintype.card α - σ.support.card → alternatingGroup α ≤ G

/-- **Jordan's prime-cycle theorem** ([Jones, Theorem 1.1]; arXiv:1209.5169, attributed there to
Jordan, with the references [Dixon--Mortimer, Theorem 3.3E] and [Wielandt, Theorem 13.9]).
A primitive permutation group of finite degree `n` containing a cycle of prime length fixing at
least three points contains the alternating group `A_n`. Qualifications: a cycle is a nontrivial
single cycle (`Equiv.Perm.IsCycle`), its length is the size of its support, and its number of
fixed points is `n` minus that size. This is the classical theorem that the manuscript cites at
the end of the proof of Lemma 5.16; it does not use the classification of finite simple groups.
Source: [Jones, Theorem 1.1]. -/
@[expose] def JordanPrimeCycleTheorem : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (G : Subgroup (Equiv.Perm α)),
    MulAction.IsPreprimitive G α → ∀ σ ∈ G, σ.IsCycle → σ.support.card.Prime →
      3 ≤ Fintype.card α - σ.support.card → alternatingGroup α ≤ G

/-- **Eisenstein polynomials over a Dedekind domain** ([Milne, ANT v3.08, Proposition 3.53]; for a
complete discretely valued base this is also [Milne, ANT v3.08, Proposition 7.55, direction `⇐`]).
Let `A` be a Dedekind domain with field of fractions `K`, let `𝔭` be a nonzero prime ideal of `A`,
and let `f ∈ A[X]` be monic and Eisenstein with respect to `𝔭` (`f` has `𝔭`-divisible lower
coefficients and constant term in `𝔭 ∖ 𝔭²`). Let `L` be a finite extension of `K` generated by a
root `α` of `f`, and `B` the integral closure of `A` in `L`. Then `f` is irreducible over `K` and
`𝔭` is totally ramified in `L`: every prime `P` of `B` over `𝔭` has ramification index
`deg f`, i.e. `𝔭 B = P ^ (deg f)`.
Qualifications: this is stated in the generality of Proposition 3.53, which needs no completeness
or discrete valuation hypothesis on `A` (Milne's `ord_𝔭(a_m) = 1` is `a_m ∈ 𝔭 ∖ 𝔭²`; his
`ord_𝔭(a_i) > 0` is `a_i ∈ 𝔭`); the three types live in the lowest universe, and `L = K[α]` is
stated as `K⟮α⟯ = ⊤`; the ramification index is Mathlib's `Ideal.ramificationIdx` of `P` over `A`,
which for a prime of the integral closure over `𝔭` is the exponent of `P` in `𝔭 B` (it is only
used for primes `P` over `𝔭`). Source: [Milne, ANT v3.08, Proposition 3.53]. -/
@[expose] def EisensteinPrimeTotallyRamified : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] [IsDedekindDomain A] (K : Type) [Field K] [Algebra A K]
    [IsFractionRing A K] (L : Type) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] (𝔭 : Ideal A) [𝔭.IsPrime], 𝔭 ≠ ⊥ → ∀ f : A[X], f.Monic →
      f.IsEisensteinAt 𝔭 → ∀ α : L, aeval α f = 0 → IntermediateField.adjoin K {α} = ⊤ →
        Irreducible (f.map (algebraMap A K)) ∧
          ∀ P : Ideal (integralClosure A L), P.IsPrime → P.LiesOver 𝔭 →
            P.ramificationIdx A = f.natDegree

/-- **The Newton polygon theorem** ([Berger, Theorem 2.4, p. 4]; L. Berger, *Galois representations
and (φ,Γ)-modules*, course notes, Institut Henri Poincaré 2010, Section 2). Let `p` be a prime and
let `P ≠ 0` be a polynomial over `PadicAlgCl p`, the algebraic closure of `ℚ_p` with the unique
extension of `v_p`, in which every polynomial splits. Let `a` be the order of vanishing of `P` at
`0`, `b = deg P`, and let `H` be the lower convex hull (`newtonHull`: the greatest convex function
on `[a,b]` below the points) of the points `(j, v_p(c_j))` over the support of `P`. Then the
multiset of valuations of the nonzero roots of `P`, with multiplicity, is the multiset of the
slopes `-(H(j+1) - H(j))`, `a ≤ j < b`.
Qualifications: Berger states the theorem for the number of roots of valuation `λ` being the length
of the segment of slope `-λ` and is informal about the field containing the roots and about
multiplicity. The statement here is the derived form for roots in `PadicAlgCl p` counted with
multiplicity (a polynomial over `PadicAlgCl p` splits there). Since the hull has integer
abscissae at its vertices, a segment of slope `-λ` and length `d` is `d` unit steps `[j, j+1]` on
which the hull has slope `-λ`, so the per-valuation count and the multiset of unit-step slopes are
equivalent forms. The roots `0` (corresponding to the slope `-∞` of a polynomial with `a > 0`) are
not counted; `padicVal p x = -log_p ‖x‖` is the real-valued valuation with `v_p(p) = 1`.
Source: [Berger, Theorem 2.4]. -/
@[expose] def NewtonPolygonRootSlopes : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : (PadicAlgCl p)[X]), P ≠ 0 →
    ((@Multiset.filter _ (· ≠ 0) (fun _ => Classical.propDecidable _) P.roots).map
        (padicVal p)) =
      (Finset.Ico P.natTrailingDegree P.natDegree).val.map fun j =>
        -(newtonHull P.natTrailingDegree P.natDegree P.support
            (fun i => padicVal p (P.coeff i)) ((j + 1 : ℕ) : ℝ) -
          newtonHull P.natTrailingDegree P.natDegree P.support
            (fun i => padicVal p (P.coeff i)) (j : ℝ))

/-- **Explicit prime number theorem in progressions** ([BMOR, Corollary 1.7], second part;
arXiv:1802.00085). Let `a` and `q` be integers with `1 ≤ q ≤ 10^5` and `gcd(a, q) = 1`.
If `x ≥ 10^6`, then `|π(x; q, a) - Li(x)/φ(q)| < 0.027 x / log² x`.
Qualifications: only the bound for `π(x; q, a)` is stated. 
Source: [BMOR, Corollary 1.7, second part; arXiv v3]. -/
@[expose] def BMORPrimeCountingBound : Prop :=
  ∀ (q : ℕ) (a : ℤ), 1 ≤ q → q ≤ 10 ^ 5 → Int.gcd a q = 1 → ∀ x : ℝ, 10 ^ 6 ≤ x →
    |(primeCountingAP x q a : ℝ) - logIntegral x / q.totient| < 0.027 * x / Real.log x ^ 2

/-- **Brun–Titchmarsh inequality** — Montgomery–Vaughan, *The large sieve*,
Mathematika 20 (1973), Theorem 2, Eq. (1.10), p. 121.
For positive reals `x, y` and coprime integers `a, q` with `q ≥ 1` and `y > q`,
`π(x + y; q, a) - π(x; q, a) < 2y / (φ(q) log(y/q))`.
The source's positive residue representative is equivalent to a residue class.
Qualifications: none; the second bound (1.11) is not used. 
Source: [MV, Theorem 2, (1.10), p. 121]. -/
@[expose] def BrunTitchmarshInequality : Prop :=
  ∀ (q : ℕ) (a : ℤ) (x y : ℝ), 1 ≤ q → Int.gcd a q = 1 → 0 < x → (q : ℝ) < y →
    (primeCountingAP (x + y) q a : ℝ) - primeCountingAP x q a <
      2 * y / (q.totient * Real.log (y / q))

/-- **Hanson's bound** ([Hanson, Theorem 1]).
For every integer `N ≥ 1`, `lcm(1, …, N) < 3^N`.
Qualifications: none. 
Source: [Hanson, Theorem 1]. -/
@[expose] def HansonLcmBound : Prop :=
  ∀ N : ℕ, 1 ≤ N → (Finset.Icc 1 N).lcm id < 3 ^ N

/-- **Primes in both odd classes modulo 4** ([CHL, Lemma 2.2]).
For every integer `x ≥ 9`, both odd residue classes modulo `4` contain a prime `p` with
`x ≤ p ≤ 2x - 5`. Qualifications: stated for natural numbers `x` only. The manuscript quotes
the lemma for every real `x ≥ 9`, which is false (for `x = 23/2` the interval `[11.5, 18]`
contains no prime `≡ 3 (mod 4)`); the integer form is the one used (Lemma 5.11 takes
`x = 2n + 2` and `x = 2n + 4`). 
Source: [CHL, Lemma 2.2]. -/
@[expose] def PrimesModFourInDyadicInterval : Prop :=
  ∀ x : ℕ, 9 ≤ x → ∀ a : ℕ, (a = 1 ∨ a = 3) →
    ∃ p : ℕ, p.Prime ∧ p % 4 = a ∧ x ≤ p ∧ p + 5 ≤ 2 * x

/-- **The source polynomial of [KZ, (12) / Theorem 5 ii)]**, `σ = (0 ∞)`:
`1728^m binom(m - ν₀, m) F(-m, -m + ν_∞; 1 - ν₀; Y/1728)`, the terminating hypergeometric series
`F(-m, b; c; z) = ∑_{i ≤ m} (-m)_i (b)_i / ((c)_i i!) z^i` with `b = -m + ν_∞`, `c = 1 - ν₀`
(`(x)_i` is `ascPochhammer`). It is meant for `1 - ν₀ ∉ {0, -1, -2, …}` (the source has
`1 - ν₀ ∈ {2/3, 4/3, 2}`); at a vanishing denominator the quotient is the junk value `0`. -/
@[expose] noncomputable def kzSourcePoly (ν₀ νinf : ℚ) (m : ℕ) : ℚ[X] :=
  ∑ i ∈ Finset.range (m + 1),
    C (1728 ^ m * Ring.choose ((m : ℚ) - ν₀) m *
        ((ascPochhammer ℚ i).eval (-(m : ℚ)) * (ascPochhammer ℚ i).eval (-(m : ℚ) + νinf) /
          ((ascPochhammer ℚ i).eval (1 - ν₀) * i.factorial)) / 1728 ^ i) * polyX ^ i

/-- The Kaneko–Zagier modular polynomial `F̃_{ℓ-1}(Y) = 1728^n P_n^{(λ/3,μ/2)}(1 - Y/864)`,
`ℓ = 12n + 6 + 2λ + 3μ` ((6.4), §6.4), in the normalization ((6.5),
§6.4) of the manuscript (the argument `l` is `λ`). -/
noncomputable def kanekoZagierModularPoly (l μ : ℤ) (n : ℕ) : ℚ[X] :=
  C ((1728 : ℚ) ^ n) * (jacobiP ((l : ℚ) / 3) ((μ : ℚ) / 2) n).comp (C (-1 / 864) * polyX + C 1)

theorem kanekoZagierModularPoly_eq (l μ : ℤ) (n : ℕ) : kanekoZagierModularPoly l μ n =
    C ((1728 : ℚ) ^ n) * (jacobiP ((l : ℚ) / 3) ((μ : ℚ) / 2) n).comp
      (C (-1 / 864) * polyX + C 1) := (rfl)

/-- **Galois groups of Kaneko–Zagier lifts through index `10^9`** ([CHK, Theorem 1.8]; published
  computer verification). For `λ, μ ∈ {-1, 1}`, `n ≥ 1` and modular
index `ℓ = 12n + 6 + 2λ + 3μ ≤ 10^9`
(such `ℓ` is prime to `6`), if `F̃_{ℓ-1}` is irreducible over `ℚ` then its Galois group is `S_n`.
Qualifications: `F̃_{ℓ-1}(Y) = 1728^n P_n^{(λ/3,μ/2)}(1 - Y/864)` as in [CHK, Eq. (3)] and the
manuscript ((6.5), §6.4). 
Source: [CHK, Theorem 1.8, (3)]. -/
@[expose] def CullinanHajirKanekoZagierGalois : Prop :=
  ∀ l μ : ℤ, (l = 1 ∨ l = -1) → (μ = 1 ∨ μ = -1) → ∀ n : ℕ, 1 ≤ n →
    12 * (n : ℤ) + 6 + 2 * l + 3 * μ ≤ 10 ^ 9 →
    Irreducible (kanekoZagierModularPoly l μ n) →
      GaloisGroupIsSymmetric (kanekoZagierModularPoly l μ n)

/-- **Galois groups of Legendre quotients through degree `10^9`** ([CHL, Theorem 1.9(a)]; published
  computer verification used in the proof of Theorem 5.9).
For `ε ∈ {-1, 1}` and `1 ≤ n ≤ 10^9`, if `J_n^ε` is irreducible over `ℚ` then
`Gal(J_n^ε/ℚ) = S_n`. Qualifications: `J_n^ε(T) = ∑_j binom(n,j) ∏_{k=1}^n (2j + 2k + ε) T^j`
is the manuscript's
normalization ((5.13), §5.3); it is exactly [CHL]'s `𝒥_n^ε` (Lemma 1.2), so Theorem 1.9(a)
applies verbatim. [CHL, Theorem 1.9(b)] states the corresponding result for the polynomial in `X²`
attached to `P_{2n+δ}(X)/X^δ` (`ε = 2δ - 1`), whose roots are the squares of the opposite
root pairs; it is `J_n^ε` up to the substitution `T = -X²` and a nonzero scalar
((5.14), §5.3; [CHL, Lemma 1.2]). 
Source: [CHL, Theorem 1.9(a), Lemma 1.2]. -/
@[expose] def CullinanHajirLegendreGalois : Prop :=
  ∀ ε : ℤ, (ε = 1 ∨ ε = -1) → ∀ n : ℕ, 1 ≤ n → n ≤ 10 ^ 9 →
    Irreducible ((legendreJ ε n).map (Int.castRingHom ℚ)) →
      GaloisGroupIsSymmetric ((legendreJ ε n).map (Int.castRingHom ℚ))

/-! ### [KZ, Theorem 1]: definitions and the cited statement

 -/

section KanekoZagierSupersingular

open Polynomial Finset WeierstrassCurve LegendreElliptic

open scoped Classical in
/-- **The supersingular `j`-invariants in `𝔽̄_ℓ`**: the `j ∈ 𝔽̄_ℓ` such that the elliptic curve
`WeierstrassCurve.ofJ j` (Mathlib's model with `j`-invariant `j`) is supersingular, i.e. has no
nonzero `ℓ`-torsion over an algebraic closure. By `mem_supersingularJ_iff_exists` this is the
set of `j(E)` for supersingular elliptic curves `E/𝔽̄_ℓ`, as in [KZ, §1]. -/
@[expose] def supersingularJ (ℓ : ℕ) [Fact ℓ.Prime] : Set (AlgebraicClosure (ZMod ℓ)) :=
  {j | IsSupersingular ℓ (WeierstrassCurve.ofJ j)}

/-- `Y^a (Y - 1728)^b F̃_{ℓ-1}(Y)` with `a = (λ+1)/2`, `b = (μ+1)/2` (§6.4). -/
@[expose] noncomputable def kanekoZagierSupersingularPoly (l μ : ℤ) (n : ℕ) : ℚ[X] :=
  polyX ^ ((l + 1) / 2).toNat * (polyX - C 1728) ^ ((μ + 1) / 2).toNat * kanekoZagierModularPoly
    l μ n

/-- The coefficientwise reduction of a rational polynomial to `𝔽_ℓ`: each coefficient
`q = q.num / q.den` is sent to `q.num / q.den ∈ 𝔽_ℓ` (`Rat.cast`). On polynomials with
`ℓ`-integral coefficients this is the reduction modulo `ℓ`. -/
@[expose] noncomputable def ratPolyReduction (ℓ : ℕ) [Fact ℓ.Prime] (f : ℚ[X]) : (ZMod ℓ)[X] :=
  ∑ i ∈ range (f.natDegree + 1), monomial i ((f.coeff i : ℚ) : ZMod ℓ)

/-- `λ = 1` iff `ℓ ≡ 5, 11 (mod 12)`. -/
@[expose] def kzLambda (ℓ : ℕ) : ℤ := if ℓ % 12 = 5 ∨ ℓ % 12 = 11 then 1 else -1

/-- `μ = 1` iff `ℓ ≡ 7, 11 (mod 12)`. -/
@[expose] def kzMu (ℓ : ℕ) : ℤ := if ℓ % 12 = 7 ∨ ℓ % 12 = 11 then 1 else -1

/-- **The Kaneko–Zagier reduction** `kzReduction ℓ ∈ 𝔽_ℓ[Y]`: the reduction modulo `ℓ` of
`Y^a (Y - 1728)^b F̃_{ℓ-1}(Y)`, with `(λ, μ, n)` determined by `ℓ = 12n + 6 + 2λ + 3μ`. -/
@[expose] noncomputable def kzReduction (ℓ : ℕ) [Fact ℓ.Prime] : (ZMod ℓ)[X] :=
  ratPolyReduction ℓ (kanekoZagierSupersingularPoly (kzLambda ℓ) (kzMu ℓ) (ℓ / 12))

/-- **Cited: [KZ, Theorem 1] with (10)–(11) and Theorem 5 ii), in the source's generality.**
For a prime `p ≥ 5`, write `k = p - 1 = 12m + 4δ + 6ε` ([KZ, (1)], `δ ∈ {0, 1, 2}`, `ε ∈ {0, 1}`;
`F_k` exists for `k ≢ 2 (mod 3)`, i.e. `δ ≠ 2`, which holds automatically since `p ≠ 3`, so the
case `δ = 2` is vacuous). Then the coefficients of `F̃_{p-1}` are `p`-integral and
`ss_p(j) ≡ j^δ (j - 1728)^ε F̃_{p-1}(j) (mod p)`, where `F̃_{p-1}` is [KZ, Theorem 5 ii)] with
`σ = (0 ∞)`, `ν₀ = (1 - 2δ)/3`, `ν_∞ = (k + 1)/6 = p/6`, normalized by [KZ, (12)]. The sign
`+` is that of (10)–(11): `F̃_{p-1} ≡ Ẽ_{p-1} ≡ (-1)^{δ+ε} H̃_{p-1}` and
`ss_p ≡ (-1)^{δ+ε} j^δ (j - 1728)^ε H̃_{p-1}` (the "±" of Theorem 1 is resolved there).
This is literature; it is **not proved** here and is used only as an explicit hypothesis. 
Source: [KZ, Theorem 1, (10)–(12), Theorem 5(ii)]. -/
@[expose] def KanekoZagierSupersingularReduction : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ m δ ε : ℕ, δ ≤ 2 → ε ≤ 1 → p - 1 = 12 * m + 4 * δ + 6 * ε →
    (∀ i, (kzSourcePoly ((1 - 2 * (δ : ℚ)) / 3) ((p : ℚ) / 6) m).coeff i ≠ 0 →
      0 ≤ padicValRat p ((kzSourcePoly ((1 - 2 * (δ : ℚ)) / 3) ((p : ℚ) / 6) m).coeff i)) ∧
    ∃ s : Finset (AlgebraicClosure (ZMod p)),
      (s : Set (AlgebraicClosure (ZMod p))) = supersingularJ p ∧
        (ratPolyReduction p (polyX ^ δ * (polyX - C 1728) ^ ε *
            kzSourcePoly ((1 - 2 * (δ : ℚ)) / 3) ((p : ℚ) / 6) m)).map
          (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) = ∏ j ∈ s, (polyX - C j)

end KanekoZagierSupersingular

section BSSResidue

open UpperHalfPlane

/-- **The residue calculation of the reducible construction** ([BSS, §2, (2.2)–(2.4)], cited, not
  proved here). Let `ε = 2a`, `δ = 2b ∈ {0, 2}` and let `w_1, …, w_k ∈ ℍ` have
pairwise distinct invariants `x_i = J(w_i) ∉ {0, 1}` (non-elliptic, pairwise inequivalent). If
the `x_i` solve (2.3), `(4+2ε)/x_i + (3+3δ)/(x_i - 1) + 12 ∑_{j≠i} 1/(x_i - x_j) = 0`, then the form
`F` of (2.2) has zero residue at every `w_i`: `∮_{|z - w_i| = r} F(z) dz = 0` for all small
`r > 0`. (Only the direction "(2.3) ⇒ residues vanish" of the cited equivalence is stated.) 
Source: [BSS, §2, (2.2)–(2.4)]. -/
@[expose] def BSSResidueCriterion : Prop :=
  ∀ a b : ℕ, a ≤ 1 → b ≤ 1 → ∀ (k : ℕ) (w : Fin k → ℍ),
    Function.Injective (fun i => jInvariant (w i)) →
    (∀ i, jInvariant (w i) ≠ 0 ∧ jInvariant (w i) ≠ 1728) →
    (∀ i, (4 + 4 * a : ℂ) / (jInvariant (w i) / 1728) +
        (3 + 6 * b : ℂ) / (jInvariant (w i) / 1728 - 1) +
        12 * ∑ j ∈ Finset.univ.erase i,
          1 / (jInvariant (w i) / 1728 - jInvariant (w j) / 1728) = 0) →
    ∀ i, ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      circleIntegral (fun z => bssWeightTwoForm a b
        (Finset.univ.val.map fun j => jInvariant (w j) / 1728) (ofComplex z)) (w i) r = 0

end BSSResidue

namespace LegendreElliptic

universe uHasse

/-- **Cited: the Hasse–Deuring supersingularity criterion** [KZ, §2, Proposition 1 and its
Corollary] (M. Kaneko and D. Zagier, *Supersingular j-invariants, hypergeometric series, and
Atkin's orthogonal polynomials*, §2 "Supersingular elliptic curves"; also [BM, §1]). The source
states it over a finite field `𝔽_q`, `q = p^r`, `p` odd, for the elliptic curve `y² = f(x)`,
`f ∈ 𝔽_q[x]` of degree `3`: `E` is supersingular iff the coefficient `a_p` of `x^{p-1}` in
`f(x)^{(p-1)/2}` vanishes. The cited hypothesis takes `f = x³ + a₂x² + a₄x + a₆` over a finite field
with the curve elliptic (`Δ ≠ 0`, i.e. `f` separable).
Source: [KZ, §2, Proposition 1 and Corollary]. -/
@[expose] def HasseSupersingularCriterion : Prop :=
  ∀ (K : Type uHasse) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p], p ≠ 2 →
    ∀ a₂ a₄ a₆ : K, (shortCubicCurve a₂ a₄ a₆).Δ ≠ 0 →
      (IsSupersingular p (shortCubicCurve a₂ a₄ a₆) ↔
        ((monicCubic a₂ a₄ a₆) ^ ((p - 1) / 2)).coeff (p - 1) = 0)

end LegendreElliptic

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
  ArithmeticOfJacobiPolynomials.GroupObject

universe uJacobian

/-- **[MilneJV, Theorem 1.1, Remark 1.7 and Proposition 1.9]: existence of the Jacobian of a smooth
projective geometrically irreducible curve over any field.** For every field `k` and every
such curve `f : X ⟶ Spec k` (no `k`-rational point is assumed) there is an abelian variety `G`
over `k` representing `Pic⁰_{X/k}` on every big fppf site containing `X` and `Spec k`, in the sense
of `Jacobian.IsJacobianOf`.

Here `Pic⁰_{X/k}(T)` is the group of sections `ξ` of the fppf Picard sheaf `Pic_{X/k}`
(`Stacks.PicardFunctor.picardFunctor`) whose pullback to every geometric point `Spec Ω ⟶ T` of the
site (`Ω` algebraically closed) is the class of a degree-zero invertible module on `X_Ω`
(`Jacobian.IsGeomFibrewiseDegreeZero`). Since `X_Ω` has a rational point, `Pic(X_Ω) = Pic_{X/k}(Ω)`,
so this is the classical `Pic⁰_{X/k}`: the sections of degree zero on all geometric fibres, i.e.
the morphisms to the Picard scheme landing in its identity component. [MilneJV, Theorem 1.1]
constructs the Jacobian over any field. It represents the étale sheaf associated with the functor
`P⁰_C` of families of degree-zero invertible sheaves ([MilneJV, Remark 1.7]). The étale cover
obtained by adjoining a rational point also gives the identification after fppf sheafification.

Over an algebraically closed field, `Jacobian.exists_isJacobianOf_of_isAlgClosed` proves existence
using Stacks.
Source: [MilneJV, Theorem 1.1, Remark 1.7, Proposition 1.9]. -/
@[expose]
def Jacobian.JacobianExists : Prop :=
  ∀ (k : Type uJacobian) [Field k] {X : Scheme.{uJacobian}} (f : X ⟶ Spec (.of k)) [IsCurve k f]
    [GeometricallyIrreducible f] [Smooth f] [IsProjectiveVariety k f],
    ∃ G : Grp (Over (Spec (.of k))),
      ∀ (B : BigFppfSite.{uJacobian}) (hX : B.Contains X) (hk : B.Contains (Spec (.of k)))
        (g : B.obj hX ⟶ B.obj hk) (hg : B.inclusion.map g = f),
        haveI : IsProper (B.inclusion.map g) := by rw [hg]; infer_instance
        Nonempty (Jacobian.IsJacobianOf B hX hk g
          (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le G)

/-- **The canonical principal polarization of a Jacobian**, Milne, *Jacobian
Varieties*, Theorem 6.6 and Summary 6.11. The Poincaré sheaf represents
normalized Picard families, and its pullback by the geometric Abel–Jacobi maps is
the negative normalized diagonal correspondence. [MilneJV, §6] assumes a `k`-rational point `P`
of the curve and then extends scalars to `k̄`. Here no rational point is assumed (the hyperelliptic
models to which this is applied need not have one), so the statement uses one further step, Galois
descent: `φ_{L(Θ)}` does not depend on the choice of `P` (another choice replaces `Θ` by a
translate, and `φ_L` is unchanged by translating `L`), so the geometric map is invariant under
`Gal(k̄/k)` and is defined over `k`, as are the dual, the Poincaré class and the correspondence
condition of [MilneJV, Summary 6.11]. The ample line bundle is allowed to exist only
geometrically. The statement applies to every smooth projective geometrically irreducible curve
and every degree-zero Picard representer.
Source: [MilneJV, Theorem 6.6, Summary 6.11, with Galois descent from `k̄` to `k`]. -/
@[expose] def Jacobian.CanonicalPrincipalPolarizationExists : Prop :=
  ∀ (k : Type uJacobian) [Field k] (B : BigFppfSite.{uJacobian})
    {X : Scheme.{uJacobian}} (hX : B.Contains X) (hk : B.Contains (Spec (.of k)))
    (f : B.obj hX ⟶ B.obj hk)
    [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
    [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
    [IsProjectiveVariety k (B.inclusion.map f)]
    (hdim : topologicalKrullDim X ≤ 1) (J : Grp (Over (Spec (.of k))))
    (_ : Jacobian.IsJacobianOf B hX hk f hdim J),
      ∃ (D : Grp (Over (Spec (.of k))))
        (P : Stacks.Picard.ofScheme (J.X ⊗ D.X).left) (φ : J.X ⟶ D.X)
        (_ : IsMonHom φ),
          Jacobian.IsCanonicalPrincipalPolarization (Over.mk (B.inclusion.map f)) J D.X P φ

/-- **Geometric endomorphisms of hyperelliptic Jacobians** (Zarhin, *Very simple
2-adic representations and hyperelliptic Jacobians*, 2002, Theorem 2.4, final assertion).
The field has arbitrary characteristic other than two. All Galois-group alternatives
of the source are included. The affine chart characterizes the smooth projective model, and the
relative degree-zero Picard universal property characterizes its Jacobian. No rational point is
assumed.
Source: [Zarhin02, Theorem 2.4, final assertion]. -/
@[expose] def Zarhin.GeometricEndomorphisms : Prop :=
  ∀ (k L : Type uJacobian) [Field k] [Field L] [Algebra k L] [IsAlgClosure k L]
    (f : k[X]) (_ : (2 : k) ≠ 0) (_ : f.Separable) (_ : 9 ≤ f.natDegree)
    (_ : Zarhin.AdmissibleGalois f)
    (C : Scheme.{uJacobian}) (π : C ⟶ Spec (CommRingCat.of L))
    (_ : Zarhin.HyperellipticModel (f.map (algebraMap k L)) (Over.mk π))
    (B : BigFppfSite.{uJacobian}) (hC : B.Contains C)
    (hL : B.Contains (Spec (CommRingCat.of L))) (g : B.obj hC ⟶ B.obj hL)
    (_ : B.inclusion.map g = π) [IsProper (B.inclusion.map g)]
    (hdim : topologicalKrullDim C ≤ 1) (J : Grp (Over (Spec (CommRingCat.of L))))
    (hJ : Jacobian.IsJacobianOf B hC hL g hdim J),
    letI := hJ.isAbelianVariety
    letI := isCommMonObj_of_isProper_of_geometricallyIntegral J.X
    Function.Bijective (Int.castRingHom (GrpObjEnd J.X))

/-- **Complex uniformization of every abelian variety**, Milne, *Abelian Varieties*
(v2.00, 2008), Chapter I, Proposition 2.1(a,b) and Theorem 2.3 (including the
identification of the period lattice with singular first homology in its proof).
The exponential has the identity differential on the canonical algebraic tangent
space; loops map to the displacement of their lifts. The per-object structure
records these geometric characterizations and their uniqueness.
Source: [MilneAVNotes, I, Proposition 2.1(a,b), Theorem 2.3 and proof]. -/
@[expose] def AbelianBettiHodge.ComplexUniformization : Prop :=
  ∀ (A : Over (Spec (CommRingCat.of ℂ))) [GrpObj A] [IsAbelianVariety ℂ A],
    Nonempty (AbelianBettiHodge.UniformizationData A)

/-- **Cohomology of every real torus**, Milne, *Abelian Varieties* (course notes
v2.00, 2008), Chapter I, Theorem 2.3, p. 13. The source identifies the integral
cohomology with exterior powers by the cup product. These groups are finite free, so the same
identification holds with rational coefficients. The statement applies to any space homeomorphic
to a finite product of circles. Alexander–Whitney cochain products characterize the equivalence.
Source: [MilneAVNotes, I, Theorem 2.3, p. 13]. -/
@[expose] def TorusBettiCupProduct : Prop :=
  ∀ (T : TopCat.{0}) (n : ℕ), Nonempty (T ≃ₜ (Fin n → Circle)) → ∀ r : ℕ,
    ∃ e : (⋀[ℚ]^r (AbelianBettiCohomology.singularCohomology T 1)) ≃ₗ[ℚ]
        AbelianBettiCohomology.singularCohomology T r,
      ∀ (ψ : Fin r → Module.Dual ℚ ((AbelianBettiCohomology.singularChain.obj T).X 1))
        (h : ∀ i, (AbelianBettiCohomology.dualMap
          ((AbelianBettiCohomology.singularChain.obj T).d (1 + 1) 1)).hom (ψ i) = 0),
        e (exteriorPower.ιMulti ℚ r fun i => AbelianBettiCohomology.cocycleClass
          (AbelianBettiCohomology.singularChain.obj T) 1 (ψ i) (h i)) =
          AbelianBettiCohomology.singularCupClass T r ψ h

/-- **The scalar plus symplectic Lie algebra of a hyperelliptic Jacobian**,
Zarhin (2002), Theorem 2.6, pp. 3–4 of arXiv:math/0109014v2, with the representation and
canonical polarization of Section 2. The base is any characteristic-zero field finitely
generated as a field over the rationals (`Algebra.EssFiniteType`). All Galois
alternatives are included, with the source's degree bound of five. The pairing on the rational
Tate module is the geometric Weil pairing of the normalized Poincaré class and the canonical
principal polarization. The statement concerns the absolute Galois image over the base field.
Restriction to finite extensions and diagonal powers are treated separately.
Source: [Zarhin02, Theorem 2.6, §2]. -/
@[expose] def Zarhin.TateLieAlgebra : Prop :=
  ∀ (k L : Type uJacobian) [Field k] [CharZero k] [Algebra ℚ k]
    [Algebra.EssFiniteType ℚ k] [Field L] [Algebra k L] [IsAlgClosure k L]
    (f : k[X]) (_ : f.Separable) (_ : 5 ≤ f.natDegree)
    (_ : Zarhin.AdmissibleGalois f)
    (C : Over (Spec (.of k))) (_ : Zarhin.HyperellipticModel f C)
    (B : BigFppfSite.{uJacobian}) (hC : B.Contains C.left)
    (hk : B.Contains (Spec (.of k))) (g : B.obj hC ⟶ B.obj hk)
    (_ : B.inclusion.map g = C.hom) [IsProper (B.inclusion.map g)]
    (hdim : topologicalKrullDim C.left ≤ 1)
    (J : Grp (Over (Spec (.of k)))) [IsCommMonObj J.X]
    (_ : Jacobian.IsJacobianOf B hC hk g hdim J)
    (D : Over (Spec (.of k))) [GrpObj D] [IsCommMonObj D]
    (P : Stacks.Picard.ofScheme (J.X ⊗ D).left) (φ : J.X ⟶ D) [IsMonHom φ]
    (_ : Jacobian.IsCanonicalPrincipalPolarization C J D P φ)
    (ℓ : ℕ) [Fact ℓ.Prime] (W : DualPairingData ℓ L J.X D)
    (_ : WeilPairingGeometry.IsWeilData L J.X D W P)
    (m : ℕ) (b : Module.Basis (Fin m) ℚ_[ℓ]
      (rationalTate ℓ (GroupScheme.GeomPoints k L J.X))),
      ellAdicLie ℓ (AbelianTateLie.tateGaloisUnits J.X b).range =
        AbelianTateLie.scalarPlusSymplectic ℓ
          (AbelianTateLie.transportForm b.equivFun (abelianWeilPairing W φ))

open WeilPairingGeometry AbelianDuality GroupScheme

/-- **Finite Weil pairings of an abelian variety** (Milne, *Abelian Varieties*, Theorem 11.1 and
Lemmas 16.1, 16.2, pp. 18, 29–30;
the geometric value is the rational-function construction in §16, p. 29, referring
to Mumford, *Abelian Varieties*, §20, p. 184. Theorem 11.1 gives Cartier duality `ker f^∨ = (ker
f)^∨`.) For every abelian variety `A` over every field `K`, every Poincaré pair
`(Â, P)`, and every extension field `L`, there is a family `e_m : A[m](L) × Â[m](L) → μ_m(L)` (`m`
invertible in `K`) that is the geometric Weil pairing of `P`, Galois equivariant, compatible
(`e_{mn}(a, b)^n = e_m(n a, n b)`), and, when `L` is algebraically closed, perfect. 
Source: [MilneAV; MumfordAV, Milne Theorem 11.1, Lemmas 16.1–16.2, §16; Mumford §20]. -/
@[expose] def AbelianVariety.WeilPairingsExist : Prop :=
  ∀ (K : Type uJacobian) [Field K] (A Â : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
    [GrpObj Â] [IsCommMonObj Â] [IsAbelianVariety K A]
    (P : Stacks.Picard.ofScheme (A ⊗ Â).left) (_ : IsPoincarePair A Â P)
    (L : Type uJacobian) [Field L] [Algebra K L],
    ∃ e : ∀ m : ℕ, (m : K) ≠ 0 →
        AddSubgroup.torsionBy (GeomPoints K L A) (m : ℤ) →+
          AddSubgroup.torsionBy (GeomPoints K L Â) (m : ℤ) →+
            AddSubgroup.torsionBy (Additive Lˣ) (m : ℤ),
      IsWeilFamily L A Â P e

/-- **Alternation of the polarized Weil pairing on the Tate module** (Milne, *Abelian Varieties*,
Lemma 16.2(e) (with (c,d)), p. 30: `L ↦ e_ℓ^L` is a homomorphism `Pic(A) → Hom(∧² T_ℓ A, ℤ_ℓ(1))`;
course notes (v2.00) Proposition 13.2(d); that the pairing is alternating, including for `ℓ = 2`,
is in Mumford, *Abelian Varieties*, §20 and §23). For an abelian variety `A` over a field `K`,
a Poincaré pair
`(Â, P)`, a polarization `φ = φ_L` of `A` by an ample line bundle (`IsPolarization`), an
algebraically closed extension `L`, a prime `ℓ` invertible in `L`, and any `ℓ`-adic duality datum
that is the geometric Weil pairing of `P`: the pairing `e_ℓ^φ(x, y) = e_ℓ(x, φ y)` on `T_ℓ A(L)`
is alternating. 
Source: [MilneAV; MilneAVNotes; MumfordAV, Milne Lemma 16.2(e), with (c,d); course notes
Proposition 13.2(d); Mumford §20, §23]. -/
@[expose] def AbelianVariety.PolarizedWeilAlternating : Prop :=
  ∀ (K : Type uJacobian) [Field K] (A Â : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
    [GrpObj Â] [IsCommMonObj Â] [IsAbelianVariety K A]
    (P : Stacks.Picard.ofScheme (A ⊗ Â).left) (_ : IsPoincarePair A Â P)
    (φ : A ⟶ Â) [IsMonHom φ] (_ : IsPolarization A Â P φ)
    (L : Type uJacobian) [Field L] [Algebra K L] [IsAlgClosed L]
    (ℓ : ℕ) [Fact ℓ.Prime] (_ : (ℓ : L) ≠ 0) (D : DualPairingData ℓ L A Â)
    (_ : IsWeilData L A Â D P) (x : Stacks.AbelianGroup.tateModule (GeomPoints K L A) ℓ),
    abelianTatePairing D φ x x = 0

/-- **The Riemann form of every polarization**, Milne, *Abelian Varieties*
(course notes v2.00), Chapter I, Example 13.3, together with the definition of
polarization in Chapter I, Section 12. The integral first Chern class `E_L` of an
ample line bundle is a nondegenerate Riemann form (`E_L(ix, x) > 0`). Its values on periods are
the logarithmic transition-function pairing `chernForm`; this formula and its sign convention are
the Appell–Humbert description of `L` by factors of automorphy (Mumford, *Abelian Varieties*, §2;
Birkenhake–Lange, *Complex Abelian Varieties*, Chapter 2), not part of [MilneAVNotes]. The
polarization of the canonical Hodge
structure that the line bundle induces (positivity `ψ(x, Jx) > 0`) takes on periods the values
`-E_L`, minus the logarithmic pairing, and the line bundle induces the
specified morphism to the Picard dual. The symplectic and similitude groups of `ψ` and `-ψ`
coincide, so the group equalities hold for either sign. This applies to every complex abelian
variety and every polarization.
Source: [MilneAVNotes, I, Example 13.3, §12; MumfordAV, §2; BirkenhakeLange, Chapter 2]. -/
@[expose] def AbelianBettiHodge.PolarizationRiemannForm : Prop :=
  ∀ (A : Over (Spec (.of ℂ))) [GrpObj A] [IsAbelianVariety ℂ A]
    (U : AbelianBettiHodge.UniformizationData A)
    (D : Over (Spec (.of ℂ))) [GrpObj D]
    (P : Stacks.Picard.ofScheme (A ⊗ D).left)
    (_ : AbelianDuality.IsPoincarePair A D P)
    (φ : A ⟶ D) [IsMonHom φ] (_ : AbelianDuality.IsPolarization A D P φ),
      Nonempty (AbelianBettiHodge.PolarizationForm A U D P φ)

/-- **Hodge and Mumford--Tate groups in the degree-at-least-nine case**,
Zarhin (2002), Theorem 9.1, proof on pp. 24--25 of arXiv:math/0109014v2, and Remark 9.2.
The group statement is derived from Zarhin's Lie-algebra equality together with Deligne's
Propositions 3.4 and 3.6; neither source states it in this form. The proof identifies the
Mumford--Tate Lie algebra with scalar plus symplectic
and the Hodge invariants with symplectic invariants. Deligne, *Hodge cycles on
abelian varieties* (1982), Proposition 3.4 and Proposition 3.6 with its proof
identify these as connected algebraic groups; their Lie equality therefore gives
the corresponding group statement on rational points. The source permits any subfield of the
complex numbers and all its Galois alternatives. The form is the Riemann form
of the canonical principal polarization, normalized on integral periods. The divisor-generation
statement uses the source's bound of five, and the group comparison uses nine.
Source: [Zarhin02; Deligne82, Zarhin Theorem 9.1, proof and Remark 9.2; Deligne Propositions 3.4,
3.6]. -/
@[expose] def Zarhin.HodgeAndMumfordTateGroups : Prop :=
  ∀ (K : Type) [Field K] [Algebra K ℂ] (f : K[X])
    (_ : f.Separable) (_ : 9 ≤ f.natDegree)
    (_ : Zarhin.AdmissibleGalois f)
    (C : Over (Spec (.of ℂ)))
    (_ : Zarhin.HyperellipticModel (f.map (algebraMap K ℂ)) C)
    (B : BigFppfSite.{0}) (hC : B.Contains C.left)
    (hℂ : B.Contains (Spec (.of ℂ))) (g : B.obj hC ⟶ B.obj hℂ)
    (_ : B.inclusion.map g = C.hom) [IsProper (B.inclusion.map g)]
    (hdim : topologicalKrullDim C.left ≤ 1)
    (J : Grp (Over (Spec (.of ℂ))))
    (_ : Jacobian.IsJacobianOf B hC hℂ g hdim J)
    (D : Over (Spec (.of ℂ))) [GrpObj D]
    (P : Stacks.Picard.ofScheme (J.X ⊗ D).left)
    (φ : J.X ⟶ D) [IsMonHom φ]
    (_ : Jacobian.IsCanonicalPrincipalPolarization C J D P φ)
    (U : AbelianBettiHodge.UniformizationData J.X)
    (F : AbelianBettiHodge.PolarizationForm J.X U D P φ),
      U.canonicalHodge.hodgeGroup = symplecticGroup F.riemann.form ∧
        U.canonicalHodge.mumfordTateGroup = similitudeGroup F.riemann.form

/-- **The rational first Chern map of every complex abelian variety**,
Milne, *Abelian Varieties*, course notes v2.00, Chapter I, Example 13.3,
with the cup comparison of Theorem 2.3. The exponential sequence defines an
additive map from the Picard group to integral degree-two cohomology. After
rationalization, its alternating form on integral periods is the logarithmic
transition-function pairing (Appell–Humbert: Mumford, *Abelian Varieties*, §2; Birkenhake–Lange,
*Complex Abelian Varieties*, Chapter 2), up to the global sign convention of
`AbelianBettiHodge.PolarizationRiemannForm` (the induced polarization is minus this pairing).
This input applies to every complex abelian variety,
every uniformization and every cup-normalized comparison.
Source: [MilneAVNotes, I, Example 13.3, Theorem 2.3; MumfordAV, §2; BirkenhakeLange, Chapter 2]. -/
@[expose] def AbelianArithmetic.BettiFirstChernExists : Prop :=
  ∀ (A : Over (Spec (.of ℂ))) [GrpObj A] [IsAbelianVariety ℂ A]
    (U : AbelianBettiHodge.UniformizationData A)
    (c₂ : AbelianHodgeClasses.CupComparison A 2),
    ∃ c1 : Stacks.Picard.ofScheme A.left →+ AbelianBettiCohomology.bettiCohomology A 2,
      AbelianArithmetic.IsBettiFirstChern (U := U) c₂ c1

namespace AbelianArithmetic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open AbelianBettiHodge AbelianBettiCohomology AbelianHodgeClasses ComplexRealization
open scoped CategoryTheory.MonObj

/-- **Existence of the Betti–Tate comparison**: Milne, *Abelian Varieties*,
course notes v2.00, Chapter I, Proposition 2.1(b), Theorem 2.3, Theorem 7.2 and Corollary 3.7.
The base-change morphism preserves the origin; Corollary 3.7 identifies an
origin-preserving isomorphism of abelian varieties as a group homomorphism.
Uniformization gives `A(ℂ)[N] = N⁻¹Λ/Λ`; multiplication by every positive integer
is finite étale in characteristic zero (Theorem 7.2). Its geometric points lie
in the algebraic closure of the base field. Passing to the inverse limit and
rationalizing gives the period/torsion comparison for every abelian variety
over every subfield of `ℂ`, every uniformization and every rational basis. 
Source: [MilneAVNotes, I, Proposition 2.1(b), Theorem 2.3, Theorem 7.2, Corollary 3.7]. -/
@[expose] def BettiTateComparisonExists : Prop :=
  ∀ (K : Type) [Field K] [Algebra K ℂ] (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]
    (σ : L →ₐ[K] ℂ) (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A] [IsAbelianVariety K A]
    (Aℂ : CSch) [GrpObj Aℂ] [IsAbelianVariety ℂ Aℂ] (emb : Aℂ.left ⟶ A.left)
    (_ : IsPullback emb Aℂ.hom A.hom (Spec.map (CommRingCat.ofHom (algebraMap K ℂ))))
    (_ : PreservesOrigin emb) (U : UniformizationData Aℂ) (ℓ : ℕ) [Fact ℓ.Prime] {n : ℕ}
    (bV : Module.Basis (Fin n) ℚ (bettiOne Aℂ)),
    ∃ bW : Module.Basis (Fin n) ℚ_[ℓ] (rationalTate ℓ (GroupScheme.GeomPoints K L A)),
      IsBettiTateComparison U emb σ ℓ bV bW

/-- **Existence of the Betti cycle class map for complex abelian varieties**:
Fulton, *Intersection Theory*, second edition, Proposition 19.1.2 (Chern-cap
compatibility), Corollary 19.2(b) (multiplicativity), and subsection 19.3.6 (Hodge type).
Milne AV I, Example 13.3 and Theorem 2.3 identify divisor classes with the
period-normalized first Chern map and the cup-normalized exterior presentation.
The properties are stated for every complex abelian variety and every degree.
Source: [Fulton; MilneAVNotes, Fulton Proposition 19.1.2, Corollary 19.2(b), §19.3.6; Milne I,
Example 13.3, Theorem 2.3]. -/
@[expose] def BettiCycleClassExists : Prop :=
  ∀ (A : CSch) [GrpObj A] [IsAbelianVariety ℂ A] [LocallyOfFiniteType A.hom]
    (U : UniformizationData A) (c₂ : CupComparison A 2)
    (c1 : Stacks.Picard.ofScheme A.left →+ bettiCohomology A 2)
    (_ : IsBettiFirstChern (U := U) c₂ c1)
    (c : ℕ) (cr : CupComparison A (2 * c)) (i : ℤ)
    (_ : i + c = (Stacks.Groupoids.abelianVarietyDimension A : ℤ)),
    Nonempty (BettiCycleClassSystem U c₂ c1 c cr i)

end AbelianArithmetic

namespace JacobianArithmeticInputs

open GroupScheme AbelianTateLie ComplexRealization

open AbelianBettiHodge AbelianBettiCohomology AbelianHodgeClasses AbelianArithmetic
  AbelianEtale AbelianCycleClass

/-- **Hodge classes on self-products of hyperelliptic Jacobians are
generated by divisor classes** — Zarhin (2002), Theorem 9.1 (degree bound `n ≥ 5`, all Galois
alternatives, any subfield `K` of `ℂ`). Every Hodge class on every self-product of the Jacobian of
the hyperelliptic curve is a `ℚ`-linear combination of products of divisor classes. 
Source: [Zarhin02, Theorem 9.1]. -/
@[expose] def HodgeClassDivisorProducts : Prop :=
  ∀ (K : Type) [Field K] [Algebra K ℂ] (f : K[X]) (_ : f.Separable) (_ : 5 ≤ f.natDegree)
    (_ : Zarhin.AdmissibleGalois f)
    (C : Over (Spec (.of ℂ))) (_ : Zarhin.HyperellipticModel (f.map (algebraMap K ℂ)) C)
    (B : BigFppfSite.{0}) (hC : B.Contains C.left) (hℂ : B.Contains (Spec (.of ℂ)))
    (g : B.obj hC ⟶ B.obj hℂ) (_ : B.inclusion.map g = C.hom) [IsProper (B.inclusion.map g)]
    (hdim : topologicalKrullDim C.left ≤ 1) (J : Grp (Over (Spec (.of ℂ))))
    (_ : Jacobian.IsJacobianOf B hC hℂ g hdim J)
    (h : ℕ) (U : UniformizationData (powObj ℂ J.X (h + 1))) (c : ℕ)
    (c₂ : CupComparison (powObj ℂ J.X (h + 1)) 2)
    (cr : CupComparison (powObj ℂ J.X (h + 1)) (2 * c))
    (c1 : Stacks.Picard.ofScheme (powObj ℂ J.X (h + 1)).left →+
      bettiCohomology (powObj ℂ J.X (h + 1)) 2),
    IsBettiFirstChern (U := U) c₂ c1 →
    ∀ x ∈ canonicalHodgeClasses U cr,
      ((cr.toEquiv.symm x : ⋀[ℚ]^(2 * c) (bettiCohomology (powObj ℂ J.X (h + 1)) 1)) :
        ExteriorAlgebra ℚ (bettiCohomology (powObj ℂ J.X (h + 1)) 1)) ∈
        divisorProductSpan c₂ c1 c

/-- **The canonical `ℓ`-adic Lie algebra equality for hyperelliptic Jacobians** — Zarhin
  (2002), Theorem 9.1 proof and Remark 9.2 (numbering of arXiv:math/0109014v2)
(`γ_ℓ 𝔤_ℓ γ_ℓ⁻¹ = 𝔪𝔱 ⊗ ℚ_ℓ`; degree `n ≥ 9`, all Galois alternatives, `K ⊂ ℂ` finitely generated
over `ℚ`). For `Jℂ` a base change of `J` along `K ⊂ ℂ`, a
uniformization `U`, an embedding `σ` of an algebraic closure `L` of `K` into `ℂ` and bases
`bV`, `bW` related by the Betti–Tate comparison (`IsBettiTateComparison`), the Lie algebra of the
image of `Gal(L/K)` on `V_ℓ(J)` is the `ℚ_ℓ`-span of the Lie algebra of the Mumford–Tate
group of the canonical Hodge structure. Passing to finite extensions is not part of the input: it
is the manuscript's own finite-index argument (`AbelianTateLie`). 
Source: [Zarhin02, Theorem 9.1, proof and Remark 9.2]. -/
@[expose] def MumfordTateLieEquality : Prop :=
  ∀ (K L : Type) [Field K] [CharZero K] [Algebra ℚ K] [Algebra.EssFiniteType ℚ K] [Algebra K ℂ]
    [Field L] [Algebra K L] [IsAlgClosure K L] (σ : L →ₐ[K] ℂ)
    (f : K[X]) (_ : f.Separable) (_ : 9 ≤ f.natDegree) (_ : Zarhin.AdmissibleGalois f)
    (C : Over (Spec (.of K))) (_ : Zarhin.HyperellipticModel f C)
    (B : BigFppfSite.{0}) (hC : B.Contains C.left) (hK : B.Contains (Spec (.of K)))
    (g : B.obj hC ⟶ B.obj hK) (_ : B.inclusion.map g = C.hom) [IsProper (B.inclusion.map g)]
    (hdim : topologicalKrullDim C.left ≤ 1) (J : Grp (Over (Spec (.of K)))) [IsCommMonObj J.X]
    (_ : Jacobian.IsJacobianOf B hC hK g hdim J) (Jℂ : Grp (Over (Spec (.of ℂ))))
    (emb : Jℂ.X.left ⟶ J.X.left)
    (_ : IsPullback emb Jℂ.X.hom J.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap K ℂ))))
    (_ : PreservesOrigin emb) (U : UniformizationData Jℂ.X) (ℓ : ℕ) [Fact ℓ.Prime] {n : ℕ}
    (bV : Module.Basis (Fin n) ℚ (bettiOne Jℂ.X))
    (bW : Module.Basis (Fin n) ℚ_[ℓ] (rationalTate ℓ (GeomPoints K L J.X)))
    (_ : IsBettiTateComparison U emb σ ℓ bV bW),
    ellAdicLie ℓ (tateGaloisUnits J.X bW).range =
      (Submodule.span ℚ_[ℓ]
        (liftEnd ℓ bV '' zariskiLie bV U.canonicalHodge.mumfordTateGroup) : Set _)

end JacobianArithmeticInputs

/-! ## General literature for canonical cycle classes -/

section CycleClassLiterature

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open GroupScheme AbelianEtale AbelianCycleClass EtaleCycleClassInterface

universe uCycle

namespace EtaleCycleClassInterface

/-- **Cited: Kummer charts cover the smooth locus**.
For every field `K`, every `K`-scheme `Y` smooth of relative dimension `r + c`, every closed
immersion `ι : Z ⟶ Y` and every open `O ⊆ Z` smooth of relative dimension `r` over `K`, every point
`z ∈ O` has a Kummer chart whose open `U ⊆ Y` contains `ι z`, at every level `N`. This is the
existence of local regular parameters of a smooth subscheme of a smooth scheme — *EGA IV₄ 17.12.1
and 17.12.2* (a closed `K`-immersion `Z ↪ Y` with `Z`, `Y` smooth over `K` is regular, locally cut
out by a regular sequence `φ₁, …, φ_c` whose differentials extend to a basis of `Ω_{Y/K}`, with
`ker = (φ₁, …, φ_c)`), together with the topological invariance of the étale site (*SGA 4 VIII
1.1*) which gives the isomorphism `θ` between the two extensions by zero of `Λ` supported on the
same closed subset, and the principal closed subschemes `V(φ_m)` (Stacks, ideal sheaves). It is
the chart cover included in `CanonicalCycleSystemExists`. 
Source: [EGAIV4; SGA4, EGA IV₄, 17.12.1–17.12.2; SGA 4, VIII 1.1]. -/
@[expose] def KummerChartsExist : Prop :=
  ∀ (K : Type uCycle) [Field K] (Y Z : Scheme.{uCycle}) (fY : Y ⟶ Spec (.of K)) (ι : Z ⟶ Y)
    [IsClosedImmersion ι] (N c r : ℕ) (O : Z.Opens), SmoothOfRelativeDimension (r + c) fY →
    SmoothOfRelativeDimension r (O.ι ≫ ι ≫ fY) → ∀ z ∈ O,
    ∃ T : KummerChart N fY ι c r, ι z ∈ T.U

/-- **Cited: existence of the canonical `ℓ`-adic cycle class system**.
SGA 4½, *Cycle*, 2.1.2–2.1.3 (Kummer normalization), 2.2.2–2.2.3 (regular-sequence
independence), 2.2.6–2.2.10 (determination and all cycles),
2.3.2 (trace characterization), 2.3.7–2.3.8 (base change and Galois action);
SGA 5 VI 3.2 (finite coefficient compatibility), 3.3(i)–(iii) (functoriality
and multiplicativity). General smooth-pair purity is SGA 4 XVI 3.7, 3.9 and SGA 5 I 3.1.4; the chart
cover uses EGA IV₄ 17.12.1–2 and SGA 4 VIII 1.1.

For every smooth proper nonempty scheme of relative dimension `d`, an
algebraically closed separable normal overfield, and invertible prime `ℓ`, the
system has all the stated supports, cycle, cup and Chern properties. The support
classes retain a single global sign `ε : ℤˣ` relating the source's support boundary
to raw library Yoneda flags, consistently across codimensions and levels. Its
expected value under the standard `Ext.δ` convention is `-1`; that comparison is
not assumed. The identification of raw library Yoneda flags with the source
cup products with supports, up to this global sign, is a convention comparison
without a Lean proof. `CanonicalCycleSystem.orientationSign` records it, and the manuscript
span conclusions do not require its value. The Galois action is pullback along
`id × Spec σ` (`fieldBaseChangeGlobalSectionsGaloisAction`), a left action;
`ρ(σ) cl(Z) = cl(Z^σ)` is Cycle 2.3.8(ii), with `σ` acting on roots as `ζ ↦ σζ`.
SGA 5 VI 3.3(iii) states multiplicativity for
all products; its reference to Cycle 2.3.8 supplies the non-excess case. On
quasi-projective schemes the Chern-cap statement also follows from Cycle
2.3.8(iii), 2.3.9, 2.1.1–2.1.2, Milne LEC 23.3(b)(c), and Stacks 02T9/tensor
additivity. Unit normalization is Cycle 2.2.2/2.2.4 in codimension zero; factoring through
Chow is SGA 5 VI 3.3(iv) and Cycle 2.3.10. The `divisorClass` uses the same
cycle normalization. 
Source: [SGA4Half; SGA5; SGA4; EGAIV4; MilneLEC, SGA 4½, Cycle 2.1.2–2.1.3, 2.2.2–2.2.10, 2.3.2,
2.3.7–2.3.10; SGA 5, VI 3.2–3.3, I 3.1.4; SGA 4, XVI 3.7/3.9, VIII 1.1; EGA IV₄ 17.12.1–2; Milne
23.3(b,c)]. -/
@[expose] def CanonicalCycleSystemExists : Prop :=
  ∀ (B : BigEtaleSite.{0}) (ℓ : ℕ) [Fact ℓ.Prime] [EllAdicSite B ℓ] (X : B.Scheme)
    [IsNoetherian X.1] {k : Type} [Field k] (f : X.1 ⟶ Spec (.of k)) [IsProper f] [Smooth f]
    (kbar : Type) [Field kbar] [Algebra k kbar] [Algebra.IsSeparable k kbar] [Normal k kbar]
    [IsAlgClosed kbar] (_ : (ℓ : k) ≠ 0) (ζ : RootSystem ℓ kbar) (d : ℕ)
    (_ : RelativeDimension f d) (_ : Nonempty X.1),
    Nonempty (CanonicalCycleSystem B ℓ X f kbar ζ d)

end EtaleCycleClassInterface

namespace Zarhin

/-- **Cited — the CHARACTERISTIC-ZERO ASSERTION of Zarhin's Theorem 8.1:
Tate classes on powers of hyperelliptic Jacobians are generated by products of divisor classes over
`K_a`** — Zarhin (2002), *Very simple 2-adic representations and hyperelliptic Jacobians*,
Theorem 8.1 (cited by the manuscript, §6.5, as "the Tate statement over every finite
extension and on every power"), alternative "`K` is a field of characteristic zero finitely
generated over `ℚ`".

`K` of characteristic `0` finitely generated over `ℚ` (`CharZero K`, `Algebra ℚ K`,
`Algebra.EssFiniteType ℚ K`; `char K ≠ 2` of the theorem is automatic), `f ∈ K[x]` separable of
degree `≥ 5` with any of the Galois alternatives of the source (`Zarhin.AdmissibleGalois`);
`C` any smooth projective geometrically irreducible model of `y² = f(x)` and `J` its Jacobian;
`K_a = L` an algebraic closure of `K` (`IsAlgClosure K L`; since `char K = 0` it is also the
separable closure `K_s`, so there is no `K_a`/`K_s` ambiguity); `K'` any finite extension of `K`
inside `L` (the separability and normality binders are automatic in characteristic `0`); `ℓ` any
prime (invertible in `K`); every positive power `J^{h+1}`; `X = (J^{h+1})_{K'}` of relative
dimension `d`; and `P` the canonical `ℓ`-adic cycle class system of `X` (the characterized object of
`CanonicalCycleSystem`): every `Gal(L/K')`-invariant class of `H^{2c}_{ét}(X_L, ℚ_ℓ(c))` is a
`ℚ_ℓ`-linear combination of products of `c` divisor classes `c₁(L₁) ∪ ⋯ ∪ c₁(L_c)`, `L_j` invertible
modules on `X_L`. 
Source: [Zarhin02, Theorem 8.1, characteristic-zero alternative]. -/
@[expose] def TateClassesDivisorProducts : Prop :=
  ∀ (K L : Type) [Field K] [CharZero K] [Algebra ℚ K] [Algebra.EssFiniteType ℚ K]
    [Field L] [Algebra K L] [IsAlgClosure K L]
    (f : K[X]) (_ : f.Separable) (_ : 5 ≤ f.natDegree)
    (_ : Zarhin.AdmissibleGalois f)
    (C : Over (Spec (.of K))) (_ : Zarhin.HyperellipticModel f C)
    (B : BigFppfSite.{0}) (hC : B.Contains C.left) (hK : B.Contains (Spec (.of K)))
    (g : B.obj hC ⟶ B.obj hK) (_ : B.inclusion.map g = C.hom) [IsProper (B.inclusion.map g)]
    (hdim : topologicalKrullDim C.left ≤ 1) (J : Grp (Over (Spec (.of K))))
    (_ : Jacobian.IsJacobianOf B hC hK g hdim J)
    (K' : IntermediateField K L) [FiniteDimensional K K'] [Algebra.IsSeparable K' L] [Normal K' L]
    (ℓ : ℕ) [Fact ℓ.Prime] (_ : (ℓ : K) ≠ 0) (h c d : ℕ)
    (B' : BigEtaleSite.{0}) [EllAdicSite B' ℓ] (X : B'.Scheme) [IsNoetherian X.1]
    (fX : X.1 ⟶ Spec (.of K')) [IsProper fX] (π : X.1 ⟶ (powObj K J.X (h + 1)).left)
    (_ : IsPullback π fX (powObj K J.X (h + 1)).hom
      (Spec.map (CommRingCat.ofHom (algebraMap K K'))))
    (_ : RelativeDimension fX d) (ζ : RootSystem ℓ L)
    (P : CanonicalCycleSystem B' ℓ X fX L ζ d),
    ∀ w ∈ (etaleCohomologyTwistRep B' ℓ X fX L c).invariants,
      w ∈ Submodule.span ℚ_[ℓ] {x | P.IsDivisorProduct c x}

end Zarhin

end CycleClassLiterature

/-! ## ComputerVerified: manuscript computational outputs

These are inputs, separate from literature. Main results take them as arguments,
including the Kaneko–Zagier family clause of Corollary 6.6.

-/

section ComputerVerified

open FirstDerivativeCriterion

/-- **Computed (Proposition B.2).** For `λ, μ ∈ {-1, 1}` and every
integer `8333 ≤ n ≤ 250000`, both
`|D_{2,n} log 2 - D_{3,n} log 3| ≤ (9/10) n` (the first condition of Appendix B.2) and
`Δ_n > n/1000`. Established in the manuscript by exact integer arithmetic with rational
logarithm bounds from the formulas, with outward rounding.
Source: [Manuscript, Proposition B.2]. -/
@[expose] def KanekoZagierFastCriterion : Prop :=
  ∀ l μ : ℤ, (l = 1 ∨ l = -1) → (μ = 1 ∨ μ = -1) → ∀ n : ℕ, 8333 ≤ n → n ≤ 250000 →
    |(kzEndpointTwo l n : ℝ) * Real.log 2 - (kzEndpointThree μ n : ℝ) * Real.log 3| ≤
        9 / 10 * (n : ℝ) ∧
      (n : ℝ) / 1000 < kzFastDelta l μ n

/-- **Computed (Lemma C.2, the `318` integer inequalities).** For `1 ≤ m ≤ 199` and `δ ∈ {0,1}`
with `m ∉ E_δ`, one has `m ≥ 4` and the strict integer inequality (C.2)
`16^m V² > 64 m (m+1)² Z² U²`. Established in the manuscript (Lemma C.2) by exact integer
arithmetic (trial division and successive multiplication by each prime).
Source: [Manuscript, Lemma C.2, Appendix C.2, (C.2)]. -/
@[expose] def FirstDerivativeIntegerInequalities : Prop :=
  ∀ m δ : ℕ, 1 ≤ m → m ≤ 199 → δ ≤ 1 → m ∉ exceptionalIndices δ →
    4 ≤ m ∧ 64 * m * (m + 1) ^ 2 * partZ m δ ^ 2 * partU m δ ^ 2 < 16 ^ m * partV m δ ^ 2

/-- **Computed (Lemma C.2, the `80` factor-degree checks).** For `1 ≤ m ≤ 199`, `δ ∈ {0,1}` with
`m ∈ E_δ`, the primitive integral polynomial `H_{2m+δ}` of positive leading coefficient
(proportional to `finiteDerivativeCoefficientPoly m δ`) has degree `2m`, and there is a finite set
`𝒫` of primes `p ≤ 317` at each of which its reduction has degree `2m` and is squarefree, such
that every `k ∈ {1, …, m}` fails to be a subset sum `Σ_p` of the factor-degree multiset `𝒟_p` for
some `p ∈ 𝒫` (that is, `{1,…,⌊D/2⌋} ∩ ⋂_{p ∈ 𝒫} Σ_p = ∅` of Lemma C.1). Established in the
manuscript (Lemma C.2) by integer arithmetic and Euclidean division over finite fields
(`254` retained reductions, largest prime `317`).
Source: [Manuscript, Lemma C.2, Appendix C.2, Lemma C.1]. -/
@[expose] def FirstDerivativeFactorDegreeChecks : Prop :=
  ∀ m δ : ℕ, 1 ≤ m → m ≤ 199 → δ ≤ 1 → m ∈ exceptionalIndices δ →
    ∃ H : ℤ[X], H.IsPrimitive ∧ 0 < H.leadingCoeff ∧ H.natDegree = 2 * m ∧
      (∃ c : ℚ, c ≠ 0 ∧
        H.map (Int.castRingHom ℚ) = C c * finiteDerivativeCoefficientPoly m δ) ∧
      ∃ P : Finset ℕ,
        (∀ p ∈ P, p.Prime ∧ p ≤ 317 ∧
          (H.map (Int.castRingHom (ZMod p))).natDegree = 2 * m ∧
          Squarefree (H.map (Int.castRingHom (ZMod p)))) ∧
        ∀ k : ℕ, 1 ≤ k → k ≤ m → ∃ p ∈ P, ∃ _ : Fact p.Prime,
          k ∉ subsetSums (factorDegrees p H)

end ComputerVerified

end ArithmeticOfJacobiPolynomials
