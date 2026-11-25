/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Remarks.LegendreElliptic
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.FiniteType
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.Algebra.Algebra.ZMod
import all ArithmeticOfJacobiPolynomials.Elliptic.Supersingular

/-!
# Supersingular Legendre curves over `𝔽̄_p` (§6.4): descent to a finite field

`ArithmeticOfJacobiPolynomials.Remarks.LegendreElliptic` proves, conditional on the cited
Hasse–Deuring
criterion (stated over finite fields, as in [KZ, §2]), that for `z ≠ 0, 1` in a *finite* field of
characteristic `p = 2m + 1` the Legendre curve `y² = x(x-1)(x-z)` is supersingular iff
`∑_{j ≤ m} binom(m,j)² z^j = 0`. The manuscript states this for `z ∈ 𝔽̄_p`. This file supplies
the descent step, with no further hypothesis:

* `exists_nsmul_eq_zero_of_baseChange` (specialization): if an elliptic curve `W₀` over a field
  `F` has a nonzero point `P` with `n • P = 0` over some field extension `K` of `F`, then it has
  one over `AlgebraicClosure F`. The coordinates of the multiples `k • P` and the inverses used by
  the chord–tangent formulas generate a finitely generated `F`-subalgebra `R ⊆ K`; by Zariski's
  lemma (`finite_of_finite_type_of_isJacobsonRing`) a residue field of `R` is finite over `F`, so
  there is an `F`-algebra map `φ : R → F̄`, and `φ` transports the computation of `n • P`
  (`pointsCorrespond_nsmul`).
* `exists_nsmul_eq_zero_iff`: hence a nonzero `n`-torsion point exists over an algebraically
  closed extension `K` of `F` iff one exists over `AlgebraicClosure F` (the converse direction
  maps points along an embedding `F̄ → K`, `Affine.Point.map`).
* `legendreCurve_isSupersingular_iff_of_isAlgebraic`: for any field `Ω` of characteristic
  `p = 2m + 1` and `z ∈ Ω` algebraic over `𝔽_p`, `z ≠ 0, 1`, the Legendre curve is supersingular
  iff `∑_{j ≤ m} binom(m,j)² z^j = 0` (descending to the finite field `𝔽_p(z)`); in particular
  for every `z ∈ 𝔽̄_p = AlgebraicClosure (ZMod p)` (`legendreCurve_isSupersingular_iff_closure`).

Both are conditional only on the cited `HasseSupersingularCriterion` (finite fields).
-/

public section

namespace ArithmeticOfJacobiPolynomials

namespace LegendreElliptic

open Polynomial Finset WeierstrassCurve

universe u

open scoped Classical in
/-- Unfolding of `IsSupersingular`: no nonzero `p`-torsion point over the algebraic closure. -/
theorem isSupersingular_iff_not_exists {K : Type*} [Field K] (p : ℕ) (E : WeierstrassCurve K) :
    IsSupersingular p E ↔
      ¬ ∃ P : (E.baseChange (AlgebraicClosure K)).toAffine.Point, p • P = 0 ∧ P ≠ 0 := by
  unfold IsSupersingular
  exact ⟨fun h ⟨P, hP, hP0⟩ => hP0 (h P hP), fun h P hP => by_contra fun hP0 => h ⟨P, hP, hP0⟩⟩

section Specialization

variable {R K L : Type*} [CommRing R] [Field K] [Field L]

/-- The `X`-coordinate of an affine point (`0` for the point at infinity). -/
def pointX {W : Affine K} : W.Point → K
  | .zero => 0
  | .some x _ _ => x

/-- The `Y`-coordinate of an affine point (`0` for the point at infinity). -/
def pointY {W : Affine K} : W.Point → K
  | .zero => 0
  | .some _ y _ => y

/-- Points over `K` and over `L` *correspond* along `ι : R → K` and `φ : R → L` if both are
the point at infinity, or both are affine with coordinates the images of the same `x, y ∈ R`. -/
def PointsCorrespond (W : Affine R) (ι : R →+* K) (φ : R →+* L) (P : (W.map ι).Point)
    (Q : (W.map φ).Point) : Prop :=
  (P = 0 ∧ Q = 0) ∨
    ∃ x y : R, (∃ h, P = .some (ι x) (ι y) h) ∧ (∃ h', Q = .some (φ x) (φ y) h')

theorem exists_some_eq {W : Affine K} {a b a' b' : K} (h : W.Nonsingular a b) (ha : a = a')
    (hb : b = b') : ∃ h', (Affine.Point.some a b h : W.Point) = .some a' b' h' := by
  subst ha hb
  exact ⟨h, rfl⟩

theorem map_eq_inv_of_mul_eq_one (f : R →+* K) {a u : R} (h : a * u = 1) : f u = (f a)⁻¹ :=
  eq_inv_of_mul_eq_one_right (by rw [← map_mul, h, map_one])

theorem map_ne_of_mul_eq_one (f : R →+* K) {a b u : R} (h : (a - b) * u = 1) : f a ≠ f b := by
  intro e
  have := congrArg f h
  rw [map_mul, map_sub, e, sub_self, zero_mul, map_one] at this
  exact zero_ne_one this

/-- **The chord–tangent law commutes with a specialization**, provided the differences used by
the formulas are either `0` or invertible in `R`. -/
theorem pointsCorrespond_add [DecidableEq K] [DecidableEq L] (W : Affine R) {ι : R →+* K}
    (hι : Function.Injective ι) (φ : R →+* L) {x₁ y₁ x₂ y₂ : R}
    (h₁ : (W.map ι).Nonsingular (ι x₁) (ι y₁)) (h₂ : (W.map ι).Nonsingular (ι x₂) (ι y₂))
    (h₁' : (W.map φ).Nonsingular (φ x₁) (φ y₁)) (h₂' : (W.map φ).Nonsingular (φ x₂) (φ y₂))
    (hX : x₁ = x₂ ∨ ∃ u, (x₁ - x₂) * u = 1)
    (hY : y₁ = W.negY x₂ y₂ ∨ ∃ u, (y₁ - W.negY x₂ y₂) * u = 1)
    (hT : y₁ = W.negY x₁ y₁ ∨ ∃ u, (y₁ - W.negY x₁ y₁) * u = 1) :
    PointsCorrespond W ι φ (.some _ _ h₁ + .some _ _ h₂) (.some _ _ h₁' + .some _ _ h₂') := by
  have hnegK : ∀ a b : R, (W.map ι).negY (ι a) (ι b) = ι (W.negY a b) := fun a b => by
    rw [Affine.map_negY]
  have hnegL : ∀ a b : R, (W.map φ).negY (φ a) (φ b) = φ (W.negY a b) := fun a b => by
    rw [Affine.map_negY]
  by_cases hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂
  · left
    constructor
    · exact Affine.Point.add_of_Y_eq (congrArg ι hxy.1) (by rw [hnegK, hxy.2])
    · exact Affine.Point.add_of_Y_eq (congrArg φ hxy.1) (by rw [hnegL, hxy.2])
  have hK : ¬(ι x₁ = ι x₂ ∧ ι y₁ = (W.map ι).negY (ι x₂) (ι y₂)) := by
    rw [hnegK]
    exact fun h => hxy ⟨hι h.1, hι h.2⟩
  have hL : ¬(φ x₁ = φ x₂ ∧ φ y₁ = (W.map φ).negY (φ x₂) (φ y₂)) := by
    rw [hnegL]
    rintro ⟨e1, e2⟩
    rcases hX with hx | ⟨u, hu⟩
    · rcases hY with hy | ⟨v, hv⟩
      · exact hxy ⟨hx, hy⟩
      · exact map_ne_of_mul_eq_one φ hv e2
    · exact map_ne_of_mul_eq_one φ hu e1
  obtain ⟨ℓ, hℓK, hℓL⟩ : ∃ ℓ : R, (W.map ι).slope (ι x₁) (ι x₂) (ι y₁) (ι y₂) = ι ℓ ∧
      (W.map φ).slope (φ x₁) (φ x₂) (φ y₁) (φ y₂) = φ ℓ := by
    by_cases hx : x₁ = x₂
    · have hy : y₁ ≠ W.negY x₂ y₂ := fun hy => hxy ⟨hx, hy⟩
      obtain ⟨v, hv⟩ := hY.resolve_left hy
      have hyK : ι y₁ ≠ (W.map ι).negY (ι x₂) (ι y₂) := by
        rw [hnegK]
        exact fun e => hy (hι e)
      have hyL : φ y₁ ≠ (W.map φ).negY (φ x₂) (φ y₂) := by
        rw [hnegL]
        exact map_ne_of_mul_eq_one φ hv
      have hT' : y₁ ≠ W.negY x₁ y₁ := by
        intro e
        have hy12 : y₁ = y₂ := hι (Affine.Y_eq_of_Y_ne h₁.1 h₂.1 (congrArg ι hx) hyK)
        apply hy
        rw [← hx, ← hy12]
        exact e
      obtain ⟨w, hw⟩ := hT.resolve_left hT'
      have hwK : ι w = (ι y₁ - ι (W.negY x₁ y₁))⁻¹ := by
        rw [← map_sub]
        exact map_eq_inv_of_mul_eq_one ι hw
      have hwL : φ w = (φ y₁ - φ (W.negY x₁ y₁))⁻¹ := by
        rw [← map_sub]
        exact map_eq_inv_of_mul_eq_one φ hw
      refine ⟨(3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) * w, ?_, ?_⟩
      · rw [Affine.slope_of_Y_ne (congrArg ι hx) hyK, hnegK, div_eq_mul_inv, ← hwK]
        simp only [map_mul, map_sub, map_add, map_pow, map_ofNat, WeierstrassCurve.map_a₁,
          WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄]
      · rw [Affine.slope_of_Y_ne (congrArg φ hx) hyL, hnegL, div_eq_mul_inv, ← hwL]
        simp only [map_mul, map_sub, map_add, map_pow, map_ofNat, WeierstrassCurve.map_a₁,
          WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄]
    · obtain ⟨u, hu⟩ := hX.resolve_left hx
      have huK : ι u = (ι x₁ - ι x₂)⁻¹ := by
        rw [← map_sub]
        exact map_eq_inv_of_mul_eq_one ι hu
      have huL : φ u = (φ x₁ - φ x₂)⁻¹ := by
        rw [← map_sub]
        exact map_eq_inv_of_mul_eq_one φ hu
      refine ⟨(y₁ - y₂) * u, ?_, ?_⟩
      · rw [Affine.slope_of_X_ne (fun e => hx (hι e)), div_eq_mul_inv, ← huK, map_mul,
          map_sub]
      · rw [Affine.slope_of_X_ne (map_ne_of_mul_eq_one φ hu), div_eq_mul_inv, ← huL, map_mul,
          map_sub]
  rw [Affine.Point.add_some hK, Affine.Point.add_some hL]
  right
  refine ⟨W.addX x₁ x₂ ℓ, W.addY x₁ x₂ y₁ ℓ, ?_, ?_⟩
  · exact exists_some_eq _ (by rw [hℓK, Affine.map_addX]) (by rw [hℓK, Affine.map_addY])
  · exact exists_some_eq _ (by rw [hℓL, Affine.map_addX]) (by rw [hℓL, Affine.map_addY])

/-- **Specialization of multiples**: the multiples `n • P` and `n • Q` of corresponding affine
points correspond, provided the differences used along the way are `0` or invertible in `R`. -/
theorem pointsCorrespond_nsmul [DecidableEq K] [DecidableEq L] (W : Affine R) {ι : R →+* K}
    (hι : Function.Injective ι) (φ : R →+* L) {x₁ y₁ : R}
    (h₁ : (W.map ι).Nonsingular (ι x₁) (ι y₁)) (h₁' : (W.map φ).Nonsingular (φ x₁) (φ y₁))
    (n : ℕ)
    (H : ∀ k < n, ∀ x y : R,
      (∃ h, k • (Affine.Point.some _ _ h₁ : (W.map ι).Point) = .some (ι x) (ι y) h) →
        (x = x₁ ∨ ∃ u, (x - x₁) * u = 1) ∧
        (y = W.negY x₁ y₁ ∨ ∃ u, (y - W.negY x₁ y₁) * u = 1) ∧
        (y = W.negY x y ∨ ∃ u, (y - W.negY x y) * u = 1)) :
    PointsCorrespond W ι φ (n • Affine.Point.some _ _ h₁) (n • Affine.Point.some _ _ h₁') := by
  induction n with
  | zero => exact Or.inl ⟨zero_nsmul _, zero_nsmul _⟩
  | succ n ih =>
    rw [succ_nsmul, succ_nsmul]
    rcases ih (fun k hk => H k (by omega)) with ⟨hP, hQ⟩ | ⟨x, y, ⟨h, hP⟩, ⟨h', hQ⟩⟩
    · rw [hP, hQ, zero_add, zero_add]
      exact Or.inr ⟨x₁, y₁, ⟨h₁, rfl⟩, ⟨h₁', rfl⟩⟩
    · rw [hP, hQ]
      obtain ⟨hX, hY, hT⟩ := H n (by omega) x y ⟨h, hP⟩
      exact pointsCorrespond_add W hι φ h h₁ h' h₁' hX hY hT

/-- A nonzero `n`-torsion affine point specializes to a nonzero `n`-torsion point. -/
theorem exists_nsmul_eq_zero_of_correspond [DecidableEq K] [DecidableEq L] (W : Affine R)
    {ι : R →+* K} (hι : Function.Injective ι) (φ : R →+* L) (WK : Affine K) (WL : Affine L)
    (hWK : W.map ι = WK) (hWL : W.map φ = WL) {x₁ y₁ : R}
    (h₁ : WK.Nonsingular (ι x₁) (ι y₁)) (h₁' : WL.Nonsingular (φ x₁) (φ y₁)) (n : ℕ)
    (H : ∀ k < n, ∀ x y : R,
      (∃ h, k • (Affine.Point.some _ _ h₁ : WK.Point) = .some (ι x) (ι y) h) →
        (x = x₁ ∨ ∃ u, (x - x₁) * u = 1) ∧
        (y = W.negY x₁ y₁ ∨ ∃ u, (y - W.negY x₁ y₁) * u = 1) ∧
        (y = W.negY x y ∨ ∃ u, (y - W.negY x y) * u = 1))
    (hn : n • (Affine.Point.some _ _ h₁ : WK.Point) = 0) :
    ∃ Q : WL.Point, n • Q = 0 ∧ Q ≠ 0 := by
  subst hWK hWL
  refine ⟨Affine.Point.some _ _ h₁', ?_, Affine.Point.some_ne_zero h₁'⟩
  rcases pointsCorrespond_nsmul W hι φ h₁ h₁' n H with ⟨_, hQ⟩ | ⟨x, y, ⟨h, hP⟩, -⟩
  · exact hQ
  · exact absurd (hP.symm.trans hn) (Affine.Point.some_ne_zero h)

theorem eq_or_exists_mul_eq_one {F : Type*} [Field F] [Algebra F K] {S : Subalgebra F K}
    (a b : S) (h : ((a : K) - b)⁻¹ ∈ S) : a = b ∨ ∃ u : S, (a - b) * u = 1 := by
  by_cases hab : a = b
  · exact Or.inl hab
  · refine Or.inr ⟨⟨_, h⟩, Subtype.ext ?_⟩
    have : (a : K) - b ≠ 0 := sub_ne_zero.mpr fun e => hab (Subtype.ext e)
    push_cast
    exact mul_inv_cancel₀ this

/-- **Specialization to the algebraic closure.** If a Weierstrass curve `W₀` over a field `F`
with `Δ ≠ 0` has a nonzero point `P` with `n • P = 0` over a field extension `K` of `F`, then it
has such a point over `AlgebraicClosure F`. -/
theorem exists_nsmul_eq_zero_of_baseChange {F : Type*} [Field F] [Algebra F K] [DecidableEq K]
    [DecidableEq (AlgebraicClosure F)] (W₀ : WeierstrassCurve F) (hΔ : W₀.Δ ≠ 0) (n : ℕ)
    (P : (W₀.baseChange K).toAffine.Point) (hP : n • P = 0) (hP0 : P ≠ 0) :
    ∃ Q : (W₀.baseChange (AlgebraicClosure F)).toAffine.Point, n • Q = 0 ∧ Q ≠ 0 := by
  obtain _ | ⟨x₁, y₁, h₁⟩ := P
  · exact absurd rfl hP0
  let P₁ : (W₀.baseChange K).toAffine.Point := Affine.Point.some x₁ y₁ h₁
  let WK := (W₀.baseChange K).toAffine
  let A : ℕ → Set K := fun k =>
    {pointX (k • P₁), pointY (k • P₁), (pointX (k • P₁) - x₁)⁻¹,
      (pointY (k • P₁) - WK.negY x₁ y₁)⁻¹,
      (pointY (k • P₁) - WK.negY (pointX (k • P₁)) (pointY (k • P₁)))⁻¹}
  let S : Set K := {x₁, y₁} ∪ ⋃ k : Fin n, A k
  have hS : S.Finite := (Set.toFinite _).union (Set.finite_iUnion fun _ => Set.toFinite _)
  let R := Algebra.adjoin F S
  have : Algebra.FiniteType F R := Algebra.FiniteType.adjoin_of_finite hS
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal R
  let _ : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have : Module.Finite F (R ⧸ 𝔪) := finite_of_finite_type_of_isJacobsonRing F (R ⧸ 𝔪)
  have : Module.IsTorsionFree F (R ⧸ 𝔪) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (algebraMap F (R ⧸ 𝔪)).injective
  have : Algebra.IsAlgebraic F (R ⧸ 𝔪) := Algebra.IsAlgebraic.of_finite F (R ⧸ 𝔪)
  let φ : R →ₐ[F] AlgebraicClosure F :=
    (IsAlgClosed.lift : (R ⧸ 𝔪) →ₐ[F] AlgebraicClosure F).comp (Ideal.Quotient.mkₐ F 𝔪)
  let ι : R →+* K := (R.val : R →+* K)
  have hι : Function.Injective ι := Subtype.val_injective
  let W : Affine R := (W₀.baseChange R).toAffine
  have hWK : W.map ι = WK := W₀.map_baseChange R.val
  have hWL : W.map (φ : R →+* AlgebraicClosure F) =
      (W₀.baseChange (AlgebraicClosure F)).toAffine := W₀.map_baseChange φ
  have hmem : ∀ k < n, A k ⊆ R := fun k hk a ha =>
    Algebra.subset_adjoin (Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨⟨k, hk⟩, ha⟩))
  let x₁' : R := ⟨x₁, Algebra.subset_adjoin (Set.mem_union_left _ (Set.mem_insert _ _))⟩
  let y₁' : R := ⟨y₁, Algebra.subset_adjoin
    (Set.mem_union_left _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))⟩
  have hneg : ∀ a b : R, ((W.negY a b : R) : K) = WK.negY a b := fun a b => by
    rw [← hWK]
    exact (Affine.map_negY (f := ι) (x := a) (y := b)).symm
  have hΔL : (W₀.baseChange (AlgebraicClosure F)).toAffine.Δ ≠ 0 := by
    rw [show (W₀.baseChange (AlgebraicClosure F)).toAffine.Δ =
      algebraMap F (AlgebraicClosure F) W₀.Δ from WeierstrassCurve.map_Δ ..]
    exact (_root_.map_ne_zero _).mpr hΔ
  have h₁' : (W₀.baseChange (AlgebraicClosure F)).toAffine.Nonsingular (φ x₁') (φ y₁') := by
    rw [← Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔL, ← hWL]
    have hE : (W.map ι).Equation (ι x₁') (ι y₁') := by
      rw [hWK]
      exact h₁.1
    exact Affine.Equation.map (f := (φ : R →+* AlgebraicClosure F))
      ((Affine.map_equation (W := W) (f := ι) hι x₁' y₁').mp hE)
  refine exists_nsmul_eq_zero_of_correspond W hι (φ : R →+* AlgebraicClosure F) WK _ hWK hWL
    (x₁ := x₁') (y₁ := y₁') h₁ h₁' n ?_ hP
  intro k hk x y ⟨h, e⟩
  have e' : k • P₁ = _ := e
  have hx : pointX (k • P₁) = x := by rw [e']; rfl
  have hy : pointY (k • P₁) = y := by rw [e']; rfl
  refine ⟨eq_or_exists_mul_eq_one x x₁' ?_, eq_or_exists_mul_eq_one y _ ?_,
    eq_or_exists_mul_eq_one y _ ?_⟩
  · rw [← hx]
    exact hmem k hk (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  · rw [hneg, ← hy]
    exact hmem k hk (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
  · rw [hneg, ← hx, ← hy]
    exact hmem k hk (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))))

end Specialization

/-- **Torsion descends to the algebraic closure of the field of definition.** For a Weierstrass
curve `W₀` with `Δ ≠ 0` over a field `F` and any algebraically closed field extension `K` of
`F` (e.g. `AlgebraicClosure` of any extension of `F`), `W₀` has a nonzero `n`-torsion point
over `K` iff it has one over `AlgebraicClosure F`. -/
theorem exists_nsmul_eq_zero_iff {F K : Type*} [Field F] [Field K] [Algebra F K] [IsAlgClosed K]
    [DecidableEq K] [DecidableEq (AlgebraicClosure F)]
    (W₀ : WeierstrassCurve F) (hΔ : W₀.Δ ≠ 0) (n : ℕ) :
    (∃ P : (W₀.baseChange K).toAffine.Point, n • P = 0 ∧ P ≠ 0) ↔
      ∃ Q : (W₀.baseChange (AlgebraicClosure F)).toAffine.Point, n • Q = 0 ∧ Q ≠ 0 := by
  constructor
  · rintro ⟨P, hP, hP0⟩
    exact exists_nsmul_eq_zero_of_baseChange W₀ hΔ n P hP hP0
  · rintro ⟨Q, hQ, hQ0⟩
    let f : AlgebraicClosure F →ₐ[F] K := IsAlgClosed.lift
    refine ⟨Affine.Point.map (W' := W₀) f Q, by rw [← map_nsmul, hQ, map_zero], fun h => hQ0 ?_⟩
    exact Affine.Point.map_injective (W' := W₀) (f := f) (by rw [h, map_zero])

/-- **The Legendre family is a Hasse family over `𝔽̄_p` (§6.4)**, conditional on the
cited Hasse–Deuring criterion. Let `Ω` be a field of characteristic `p = 2m + 1` and `z ∈ Ω`
algebraic over `𝔽_p` (e.g. any `z ∈ 𝔽̄_p`), `z ≠ 0, 1`. Then the Legendre curve
`y² = x(x-1)(x-z)` is supersingular iff `∑_{j ≤ m} binom(m,j)² z^j = 0`. -/
theorem legendreCurve_isSupersingular_iff_of_isAlgebraic
    (hHasse : HasseSupersingularCriterion.{u}) {Ω : Type u} [Field Ω] (p : ℕ) [CharP Ω p]
    [Algebra (ZMod p) Ω] (m : ℕ) (hp : p = 2 * m + 1) {z : Ω} (hz : IsAlgebraic (ZMod p) z)
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    IsSupersingular p (legendreCurve z) ↔
      ∑ j ∈ range (m + 1), ((m.choose j : ℕ) : Ω) ^ 2 * z ^ j = 0 := by
  classical
  have : NeZero p := ⟨by omega⟩
  have : Fact p.Prime := CharP.char_is_prime_of_pos Ω p
  let F := IntermediateField.adjoin (ZMod p) {z}
  have : FiniteDimensional (ZMod p) F := IntermediateField.adjoin.finiteDimensional hz.isIntegral
  have : Finite F := Module.finite_of_finite (ZMod p)
  have : CharP F p := charP_of_injective_algebraMap (algebraMap (ZMod p) F).injective p
  let z' : F := ⟨z, IntermediateField.mem_adjoin_simple_self (F := ZMod p) (α := z)⟩
  have hz'0 : z' ≠ 0 := fun h => hz0 (by simpa [z'] using congrArg (fun w : F => (w : Ω)) h)
  have hz'1 : z' ≠ 1 := fun h => hz1 (by simpa [z'] using congrArg (fun w : F => (w : Ω)) h)
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).mp (by exact_mod_cast h)
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have := (Fact.out : p.Prime).two_le
    omega
  have hΔ : (legendreCurve z').Δ ≠ 0 := (legendreCurve_isElliptic h2 hz'0 hz'1).isUnit.ne_zero
  have h1 : (legendreCurve z').baseChange Ω = legendreCurve z := by
    ext <;> simp [WeierstrassCurve.baseChange, z']
  have hcurve : (legendreCurve z).baseChange (AlgebraicClosure Ω) =
      (legendreCurve z').baseChange (AlgebraicClosure Ω) := by
    rw [← h1]
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_map,
      ← IsScalarTower.algebraMap_eq]
  have hsum : ∑ j ∈ range (m + 1), ((m.choose j : ℕ) : Ω) ^ 2 * z ^ j =
      algebraMap F Ω (∑ j ∈ range (m + 1), ((m.choose j : ℕ) : F) ^ 2 * z' ^ j) := by
    simp [map_sum, z']
  rw [isSupersingular_iff_not_exists, hcurve]
  refine (not_congr
    (exists_nsmul_eq_zero_iff (K := AlgebraicClosure Ω) (legendreCurve z') hΔ p)).trans
    ((isSupersingular_iff_not_exists p (legendreCurve z')).symm.trans ?_)
  rw [legendreCurve_isSupersingular_iff hHasse p m hp hz'0 hz'1, hsum, _root_.map_eq_zero]

/-- **The Legendre family is a Hasse family over `𝔽̄_p` (§6.4)**: for `p = 2m + 1`
prime and `z ∈ 𝔽̄_p = AlgebraicClosure (ZMod p)`, `z ≠ 0, 1`, conditional on the cited
Hasse–Deuring criterion, `y² = x(x-1)(x-z)` is supersingular iff
`∑_{j ≤ m} binom(m,j)² z^j = 0`. -/
theorem legendreCurve_isSupersingular_iff_closure (hHasse : HasseSupersingularCriterion.{0})
    (p : ℕ) [Fact p.Prime] (m : ℕ) (hp : p = 2 * m + 1) {z : AlgebraicClosure (ZMod p)}
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    IsSupersingular p (legendreCurve z) ↔
      ∑ j ∈ range (m + 1), ((m.choose j : ℕ) : AlgebraicClosure (ZMod p)) ^ 2 * z ^ j = 0 := by
  have : CharP (AlgebraicClosure (ZMod p)) p :=
    charP_of_injective_algebraMap (algebraMap (ZMod p) _).injective p
  exact legendreCurve_isSupersingular_iff_of_isAlgebraic hHasse p m hp
    (Algebra.IsAlgebraic.isAlgebraic z) hz0 hz1

end LegendreElliptic

end ArithmeticOfJacobiPolynomials
