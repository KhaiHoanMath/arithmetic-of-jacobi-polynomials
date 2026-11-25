/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.Basic
public import ArithmeticOfJacobiPolynomials.Galois.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.FieldTheory.Minpoly.Field

/-!
# Statements of the manuscript's main results

Each main result of the manuscript is recorded here as a proposition, so that its exact
meaning is fixed in Lean. A proposition defined in this file is a *statement*, not an
assumption: no theorem of the library takes one of them as a hypothesis. Which of them are
proved (possibly conditionally on the cited literature in `ArithmeticOfJacobiPolynomials.External`)
is
recorded in the README.

Effectivity assertions of the manuscript ("effectively computable threshold") are not part of
these existential statements. They are formalized separately, as explicit computable threshold
functions with theorems valid beyond them, in `ArithmeticOfJacobiPolynomials.Effective`: Theorem 1.3
(irreducibility, Galois group, and the fixed-field addendum, with the threshold computed
from a monic defining polynomial `F` of `E` by
`fixedFieldPolyBound F = |Res(F, F')|`), Lemma 3.5, Proposition 3.6,
Theorem 1.4, Corollaries 6.1, 6.2, 6.4, 6.5 and Proposition 6.3 (`fixedFactorThresholdOfRat`,
computed from `F` and rational `c`).
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial TensorProduct

/-- The four Kaneko–Zagier Jacobi polynomials `P_n^{(λ/3, μ/2)}`, `λ, μ ∈ {-1, 1}`
(the argument `l` is `λ`). -/
noncomputable def kanekoZagierJacobi (l μ : ℤ) (n : ℕ) : ℚ[X] :=
  jacobiP ((l : ℚ) / 3) ((μ : ℚ) / 2) n

theorem kanekoZagierJacobi_eq (l μ : ℤ) (n : ℕ) :
    kanekoZagierJacobi l μ n = jacobiP ((l : ℚ) / 3) ((μ : ℚ) / 2) n := (rfl)

/-- **Theorem 1.1 (the Mahlburg–Ono conjecture).** For every `n ≥ 1` and `λ, μ ∈ {-1,1}`,
`P_n^{(λ/3,μ/2)}` is irreducible over `ℚ` and its Galois group is `S_n`. -/
@[expose] def MahlburgOnoStatement : Prop :=
  ∀ (l μ : ℤ), (l = 1 ∨ l = -1) → (μ = 1 ∨ μ = -1) → ∀ n : ℕ, 1 ≤ n →
    Irreducible (kanekoZagierJacobi l μ n) ∧ GaloisGroupIsSymmetric (kanekoZagierJacobi l μ n)

/-- **Theorem 1.2 (the Legendre Galois groups; the Cullinan–Hajir conjecture).** For every
`m ≥ 1` and `δ ∈ {0,1}`, `Gal(P_{2m+δ}(x)/x^δ / ℚ) = W_m`. -/
@[expose] def LegendreGaloisStatement : Prop :=
  ∀ m δ : ℕ, 1 ≤ m → δ ≤ 1 → GaloisGroupIsWreath (reducedLegendre m δ)

/-- **Theorem 1.3.** For distinct nonnegative integers `a, b` there is `N(a,b)` such that for
every `n ≥ N(a,b)`, `P_n^{(a,b)}` is irreducible over `ℚ` with Galois group `S_n`. -/
@[expose] def UnequalIntegralParametersStatement : Prop :=
  ∀ a b : ℕ, a ≠ b → ∃ N : ℕ, ∀ n ≥ N,
    Irreducible (jacobiP a b n) ∧ GaloisGroupIsSymmetric (jacobiP a b n)

/-- **Addendum to Theorem 1.3.** For distinct nonnegative integers `a, b` and a number field
`E`, for all sufficiently large `n` the splitting field of `P_n^{(a,b)}` is linearly disjoint
from `E` over `ℚ` (equivalently, as it is Galois, its tensor product with `E` is a field), and
`P_n^{(a,b)}` remains irreducible over `E` with Galois group `S_n`. -/
@[expose] def UnequalIntegralParametersFixedFieldStatement : Prop :=
  ∀ a b : ℕ, a ≠ b → ∀ (E : Type) [Field E] [NumberField E], ∃ N : ℕ, ∀ n ≥ N,
    IsField ((jacobiP a b n).SplittingField ⊗[ℚ] E) ∧
    Irreducible ((jacobiP a b n).map (algebraMap ℚ E)) ∧
    GaloisGroupIsSymmetric ((jacobiP a b n).map (algebraMap ℚ E))

/-- **Theorem 1.4.** `F_{m,r,δ} = C_{2m+δ}^{r+1/2}/x^δ` is irreducible over `ℚ` whenever
`m ≥ max{100r, 1000}`; and there is an absolute `M_0` such that the same holds whenever
`m ≥ max{8r, M_0}`. -/
@[expose] def SymmetricParametersStatement : Prop :=
  (∀ m r δ : ℕ, δ ≤ 1 → max (100 * r) 1000 ≤ m → Irreducible (reducedGegenbauer m r δ)) ∧
  ∃ M₀ : ℕ, ∀ m r δ : ℕ, δ ≤ 1 → 1 ≤ m → max (8 * r) M₀ ≤ m →
    Irreducible (reducedGegenbauer m r δ)

/-- **Theorem 1.5.** For every `m ≥ 1`, the polynomials `P_{2m}`, `P_{2m+1}/x`, `P'_{2m+1}`
and `P'_{2m+2}/x` are irreducible over `ℚ`. -/
@[expose] def LegendreAndDerivativesStatement : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    Irreducible (legendreP (2 * m)) ∧ Irreducible (legendreP (2 * m + 1) /ₘ X) ∧
    Irreducible (derivative (legendreP (2 * m + 1))) ∧
    Irreducible (derivative (legendreP (2 * m + 2)) /ₘ X)

/-- The denominator hypotheses of Theorem 1.6 on rational parameters `α = a/u`, `β = b/v` in
lowest terms: the reduced denominator `D` of `α + β` is even, `D ≥ max{u, v}`, and neither
parameter is a negative integer. -/
@[expose] def JacobiDenominatorCondition (α β : ℚ) : Prop :=
  Even (α + β).den ∧ max α.den β.den ≤ (α + β).den ∧
    (∀ k : ℕ, α ≠ -((k : ℚ) + 1)) ∧ ∀ k : ℕ, β ≠ -((k : ℚ) + 1)

/-- `h` is a dominant factor of `f`: a monic irreducible factor of degree greater than
`deg f / 2`. Such a factor is unique when it exists. -/
@[expose] def IsDominantFactor (f h : ℚ[X]) : Prop :=
  h.Monic ∧ Irreducible h ∧ h ∣ f ∧ f.natDegree < 2 * h.natDegree

/-- **Theorem 1.6 (fixed rational parameters).** Under the denominator condition, for all
sufficiently large `n`, `f_n = P_n^{(α,β)}` has a unique dominant factor `h_n` (monic,
irreducible, of degree `M_n > n/2`); writing `f_n = κ_n h_n g_n` with `g_n` monic:

* `Gal(h_n/ℚ) = S_{M_n}`, and restriction `Gal(h_n g_n/ℚ) → Gal(h_n/ℚ) × Gal(g_n/ℚ)` is an
  isomorphism (linear disjointness of the two splitting fields and
  `Gal(f_n/ℚ) = S_{M_n} × Gal(g_n/ℚ)`);
* `n - M_n = O_{α,β,A}(n / (log n)^A)` for every fixed `A > 0`;
* for each fixed `c ∈ ℚ^×`, for all large `n`, `h_n(1+cx^2)` is irreducible with group
  `W_{M_n}`, and restriction
  `Gal(h_n(1+cx^2) g_n(1+cx^2)/ℚ) → Gal(h_n(1+cx^2)/ℚ) × Gal(g_n(1+cx^2)/ℚ)` is an
  isomorphism;
* for each fixed number field `E` and `c ∈ ℚ^×`, for all large `n`, the splitting fields of
  `h_n` and `h_n(1+cx^2)` are linearly disjoint from `E`. -/
@[expose] def FixedRationalParametersStatement : Prop :=
  ∀ α β : ℚ, JacobiDenominatorCondition α β →
    (∃ N : ℕ, ∀ n ≥ N, ∃ h : ℚ[X], IsDominantFactor (jacobiP α β n) h ∧
        ∀ h' : ℚ[X], IsDominantFactor (jacobiP α β n) h' → h' = h) ∧
    (∃ N : ℕ, ∀ n ≥ N, ∀ h g : ℚ[X], ∀ κ : ℚ, IsDominantFactor (jacobiP α β n) h → g.Monic →
        jacobiP α β n = C κ * h * g →
        GaloisGroupIsSymmetric h ∧ Function.Bijective (Gal.restrictProd h g)) ∧
    (∀ A : ℝ, 0 < A → ∃ (Cst : ℝ) (N : ℕ), ∀ n ≥ N, ∀ h : ℚ[X],
        IsDominantFactor (jacobiP α β n) h →
        ((n : ℝ) - h.natDegree) ≤ Cst * n / Real.log n ^ A) ∧
    (∀ c : ℚ, c ≠ 0 → ∃ N : ℕ, ∀ n ≥ N, ∀ h g : ℚ[X], ∀ κ : ℚ,
        IsDominantFactor (jacobiP α β n) h → g.Monic → jacobiP α β n = C κ * h * g →
        Irreducible (h.comp (1 + C c * X ^ 2)) ∧
        GaloisGroupIsWreath (h.comp (1 + C c * X ^ 2)) ∧
        Function.Bijective (Gal.restrictProd (h.comp (1 + C c * X ^ 2))
          (g.comp (1 + C c * X ^ 2)))) ∧
    (∀ (E : Type) [Field E] [NumberField E], ∀ c : ℚ, c ≠ 0 → ∃ N : ℕ, ∀ n ≥ N,
        ∀ h : ℚ[X], IsDominantFactor (jacobiP α β n) h →
        IsField (h.SplittingField ⊗[ℚ] E) ∧
        IsField ((h.comp (1 + C c * X ^ 2)).SplittingField ⊗[ℚ] E))

/-- `Q_{m,r,δ}`, the polynomial with `F_{m,r,δ}(x) = Q_{m,r,δ}(x^2)` (`F_{m,r,δ}` is even). -/
noncomputable def reducedGegenbauerSquare (m r δ : ℕ) : ℚ[X] :=
  contract 2 (reducedGegenbauer m r δ)

theorem reducedGegenbauerSquare_eq (m r δ : ℕ) :
    reducedGegenbauerSquare m r δ = contract 2 (reducedGegenbauer m r δ) := (rfl)

/-- **Corollary 1.7.** Fix `r ≥ 0` and a number field `E`. For all sufficiently large `m` and
both `δ ∈ {0,1}`, `F_{m,r,δ}` and `Q_{m,r,δ}` are irreducible over `E` with
`Gal(F_{m,r,δ}/E) = W_m` and `Gal(Q_{m,r,δ}/E) = S_m`, and their splitting fields over `ℚ`
are linearly disjoint from `E`. -/
@[expose] def FixedDerivativesGaloisStatement : Prop :=
  ∀ (r : ℕ) (E : Type) [Field E] [NumberField E], ∃ N : ℕ, ∀ m ≥ N, ∀ δ : ℕ, δ ≤ 1 →
    Irreducible ((reducedGegenbauer m r δ).map (algebraMap ℚ E)) ∧
    GaloisGroupIsWreath ((reducedGegenbauer m r δ).map (algebraMap ℚ E)) ∧
    Irreducible ((reducedGegenbauerSquare m r δ).map (algebraMap ℚ E)) ∧
    GaloisGroupIsSymmetric ((reducedGegenbauerSquare m r δ).map (algebraMap ℚ E)) ∧
    IsField ((reducedGegenbauer m r δ).SplittingField ⊗[ℚ] E) ∧
    IsField ((reducedGegenbauerSquare m r δ).SplittingField ⊗[ℚ] E)

/-- **Corollary 6.1.** For integers `a, b` with `|a| ≠ |b|`, `a_- = max{-a,0}`,
`b_- = max{-b,0}`: for all sufficiently large `n`, `P_n^{(a,b)}(x)/((x-1)^{a_-}(x+1)^{b_-})`
is irreducible over `ℚ` with Galois group `S_{n - a_- - b_-}`. -/
@[expose] def IntegralParametersStatement : Prop :=
  ∀ a b : ℤ, |a| ≠ |b| → ∃ N : ℕ, ∀ n ≥ N,
    let g := jacobiP a b n /ₘ ((X - 1) ^ (-a).toNat * (X + 1) ^ (-b).toNat)
    g.natDegree = n - (-a).toNat - (-b).toNat ∧ Irreducible g ∧ GaloisGroupIsSymmetric g

/-- **Corollary 6.2.** (1) For distinct nonnegative integers `a, b`, only finitely many pairs
of different degrees give Jacobi polynomials `P_n^{(a,b)}` with a common complex root.
(2) No two distinct members of `{P_ℓ, P'_ℓ : ℓ ≥ 1}` have a common nonzero root; here the
member `(ℓ, false)` is `P_ℓ` and `(ℓ, true)` is `P'_ℓ`. -/
@[expose] def CommonRootsStatement : Prop :=
  (∀ a b : ℕ, a ≠ b →
    {nn : ℕ × ℕ | nn.1 ≠ nn.2 ∧ ∃ z : ℂ, aeval z (jacobiP a b nn.1) = 0 ∧
        aeval z (jacobiP a b nn.2) = 0}.Finite) ∧
  ∀ i j : ℕ × Bool, 1 ≤ i.1 → 1 ≤ j.1 → i ≠ j → ∀ z : ℂ, z ≠ 0 →
    let P : ℕ × Bool → ℚ[X] := fun k =>
      if k.2 then derivative (legendreP k.1) else legendreP k.1
    ¬ (aeval z (P i) = 0 ∧ aeval z (P j) = 0)

/-- **Corollary 6.4.** There is `M_1` such that for `m ≥ M_1` and `0 ≤ r ≤ m/2`, neither
`C_{2m}^{r+1/2}` nor `C_{2m+1}^{r+1/2}/x` has a rational root. -/
@[expose] def NoRationalRootsStatement : Prop :=
  ∃ M₁ : ℕ, ∀ m r δ : ℕ, M₁ ≤ m → 2 * r ≤ m → δ ≤ 1 → ∀ q : ℚ,
    (reducedGegenbauer m r δ).eval q ≠ 0

/-- **Corollary 6.5 (vanishing modes on a circular cone).** (1) For every `D ≥ 1` there is
`L_D` such that for every nonzero real algebraic `α ∈ (-1,1)` of degree at most `D`, if
`ℓ ≥ L_D`, `0 ≤ r ≤ ℓ` and `P_ℓ^{(r)}(α) = 0`, then `17r > ℓ - 1`. (2) For `α = 1/√3`,
`P_ℓ^{(r)}(α) = 0` with `r ≤ ℓ` implies `23r > 4(ℓ-1)` for all sufficiently large `ℓ`.
(3) There is an absolute `L` such that for nonzero rational `α ∈ (-1,1)`, `ℓ ≥ L`,
`r ≤ ℓ` and `P_ℓ^{(r)}(α) = 0` imply `5r > ℓ - 1`. -/
@[expose] def ConeModesStatement : Prop :=
  (∀ D : ℕ, 1 ≤ D → ∃ L : ℕ, ∀ α : ℝ, α ≠ 0 → -1 < α → α < 1 → IsAlgebraic ℚ α →
      (minpoly ℚ α).natDegree ≤ D → ∀ ℓ r : ℕ, L ≤ ℓ → r ≤ ℓ →
      aeval α (derivative^[r] (legendreP ℓ)) = 0 → ℓ - 1 < 17 * r) ∧
  (∃ L : ℕ, ∀ ℓ r : ℕ, L ≤ ℓ → r ≤ ℓ →
      aeval (1 / Real.sqrt 3) (derivative^[r] (legendreP ℓ)) = 0 → 4 * (ℓ - 1) < 23 * r) ∧
  (∃ L : ℕ, ∀ α : ℚ, α ≠ 0 → |α| < 1 → ∀ ℓ r : ℕ, L ≤ ℓ → r ≤ ℓ →
      (derivative^[r] (legendreP ℓ)).eval α = 0 → ℓ - 1 < 5 * r)

/-- **Theorem A.1 (local irreducibility).** For every `a ≥ 0` and `λ, μ ∈ {-1,1}`,
`P_{3^a}^{(λ/3,μ/2)}` is irreducible over `ℚ_3`; `P_{5·3^a}^{(λ/3,μ/2)}` is irreducible over
`ℚ_3` precisely when `μ = -1` or `a ≥ 2`; and for `μ = 1` the degrees of its irreducible
factors over `ℚ_3` are `1, 1, 3` when `a = 0` and `2, 13` when `a = 1`. -/
@[expose] def KanekoZagierLocalIrreducibilityStatement : Prop :=
  ∀ (l μ : ℤ), (l = 1 ∨ l = -1) → (μ = 1 ∨ μ = -1) →
    (∀ a : ℕ, Irreducible ((kanekoZagierJacobi l μ (3 ^ a)).map (algebraMap ℚ ℚ_[3]))) ∧
    (∀ a : ℕ, Irreducible ((kanekoZagierJacobi l μ (5 * 3 ^ a)).map (algebraMap ℚ ℚ_[3])) ↔
      (μ = -1 ∨ 2 ≤ a)) ∧
    (μ = 1 → (UniqueFactorizationMonoid.factors
        ((kanekoZagierJacobi l μ 5).map (algebraMap ℚ ℚ_[3]))).map natDegree = {1, 1, 3}) ∧
    (μ = 1 → (UniqueFactorizationMonoid.factors
        ((kanekoZagierJacobi l μ 15).map (algebraMap ℚ ℚ_[3]))).map natDegree = {2, 13})

end ArithmeticOfJacobiPolynomials
