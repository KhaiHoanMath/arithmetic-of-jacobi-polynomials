/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.MainResults
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Section 6.5: hyperelliptic Jacobians and the degree-two map

## Corollary 6.6

Corollary 6.6 concerns the Jacobian `J_f` of the smooth projective curve
`y^2 = f(x)`, its endomorphism ring over `ℚ̄`, its Hodge and Mumford–Tate groups on
`H_1(J_f(ℂ), ℚ)`, the `ℓ`-adic Lie algebra of the Galois image on `V_ℓ(J_f)`, the Weil pairing,
Hodge classes, and the cycle class maps `CH^c((J_f^h)_K) ⊗ ℚ_ℓ → H^{2c}_ét(…, ℚ_ℓ(c))^{Gal}`.
The curve is constructed in this library: the smooth proper, geometrically integral
model `ArithmeticOfJacobiPolynomials.Hyperelliptic.projectiveModel f`, of genus `⌊(deg f - 1)/2⌋`
(`ArithmeticOfJacobiPolynomials.Geometry.Hyperelliptic*`); the Picard group of a scheme with
pullbacks and the
relative Picard sheaf and its Jacobian are supplied by Stacks through
`ArithmeticOfJacobiPolynomials.Geometry.Jacobian`. General-field existence is an explicit Milne
input in
`External.lean`, specialized in `Applications.JacobianExistence`. Geometric endomorphisms
follow from Zarhin Theorem 2.4 in `Applications.JacobianEndomorphisms`. Tate-module
freeness and rank are proved in `Algebra.JacobianTate`; `Algebra.AbelianWeilPairing` builds
pairings from finite duality data and a principal-polarization isomorphism.

`Applications.JacobianArithmetic` states the conclusion as
`JacobianSetting.ArithmeticConclusions`. `JacobianSetting.arithmeticConclusions` in
`Applications.JacobianArithmeticConsequences` proves it from the cited hypotheses, using
Zarhin's Theorem 8.1 for the cycle-class conjunct. `Applications.JacobianTateLie` proves the
Lie-algebra step. Rational averaging and finite-index transfer are proved in
`Algebra.RationalDescent`, `Algebra.CycleDescent` and `Algebra.FiniteIndexLie`.

## The degree-two map `{y^2 = F_{m,r,δ}(x)} → {y^2 = Q_{m,r,δ}(t)}`

The paragraph after Corollary 6.6 uses the substitution `t = x^2`: since
`F_{m,r,δ}(x) = Q_{m,r,δ}(x^2)`, the map `(x, y) ↦ (x^2, y)` sends the affine curve
`y^2 = F_{m,r,δ}(x)` to the affine curve `y^2 = Q_{m,r,δ}(t)`, and its fibre over `(t, y)` is
`{(x, y) : x^2 = t}`. This file proves:

* `coeff_reducedGegenbauer_eq_zero_of_odd`: `F_{m,r,δ}` is even;
* `expand_reducedGegenbauerSquare`: `F_{m,r,δ}(x) = Q_{m,r,δ}(x^2)` (as polynomials, the
  expansion of `Q_{m,r,δ}` by `2` is `F_{m,r,δ}`);
* `natDegree_reducedGegenbauer_eq_two_mul`, `natDegree_reducedGegenbauerSquare`: `deg F_{m,r,δ} =
  2m`
  and `deg Q_{m,r,δ} = m` (so `Q_{m,r,δ}` has the degree `d = m` used in the application of
  Corollary 6.6, and `F_{m,r,δ}` has degree `2m`);
* `sq_eq_aeval_reducedGegenbauer_iff`: the map of affine equations, over every `ℚ`-algebra;
* `squareMap_fiber_iff`, `eq_or_eq_neg_of_sq_eq`: the fibre of the map over a point `(t, y)`
  of `y^2 = Q_{m,r,δ}(t)` is `{x : x^2 = t}`, which over a domain consists of at most the two
  points `±x₀` (distinct when `x₀ ≠ 0` and `2 ≠ 0`);
* `squareMap`, `squareRootExtensionEquiv`, `free_and_finrank_squareMap`: on affine coordinate
  rings the map is `R[t, y]/(y^2 - q(t)) → R[x, y]/(y^2 - q(x^2))`, `t ↦ x^2`, `y ↦ y`; the
  target is the source with `√t` adjoined, hence a free module of rank two over it (the map
  of affine models is finite and flat of degree two);
  `free_and_finrank_squareMap_reducedGegenbauerSquare` is the case `q = Q_{m,r,δ}`.

The extension to the smooth projective models is
`ArithmeticOfJacobiPolynomials.Hyperelliptic.squareMorphism`
(`Geometry/HyperellipticSquareMap.lean`). It is
finite of degree two (`Geometry/HyperellipticSquareMapDegree.lean`).
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial

/-- The coefficients of `p /ₘ X^δ` are those of `p`, shifted by `δ`. -/
theorem coeff_divByMonic_X_pow_eq_coeff_add {R : Type*} [CommRing R] [Nontrivial R]
    (p : R[X]) (δ j : ℕ) : (p /ₘ X ^ δ).coeff j = p.coeff (j + δ) := by
  have h := modByMonic_add_div p (X ^ δ : R[X])
  have hlt : (p %ₘ X ^ δ).degree < ((j + δ : ℕ) : WithBot ℕ) := by
    refine (degree_modByMonic_lt p (monic_X_pow δ)).trans_le ?_
    rw [degree_X_pow]
    exact_mod_cast Nat.le_add_left δ j
  conv_rhs => rw [← h]
  rw [coeff_add, coeff_eq_zero_of_degree_lt hlt, zero_add, coeff_X_pow_mul]

/-- Every monomial of `C_n^{ν}` has degree `≡ n (mod 2)`. -/
theorem coeff_gegenbauerC_eq_zero_of_mod_two_ne (ν : ℚ) (n j : ℕ) (h : j % 2 ≠ n % 2) :
    (gegenbauerC ν n).coeff j = 0 := by
  rw [gegenbauerC_eq, finsetSum_coeff]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [coeff_C_mul_X_pow]
  split_ifs with h'
  · omega
  · rfl

/-- `C_n^{ν}` has no monomial of degree `> n`. -/
theorem coeff_gegenbauerC_eq_zero_of_lt (ν : ℚ) (n j : ℕ) (h : n < j) :
    (gegenbauerC ν n).coeff j = 0 := by
  rw [gegenbauerC_eq, finsetSum_coeff]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [coeff_C_mul_X_pow]
  split_ifs with h'
  · omega
  · rfl

/-- For `ν > 0`, the coefficient of `x^n` in `C_n^{ν}` is nonzero. -/
theorem coeff_gegenbauerC_self_ne_zero (ν : ℚ) (hν : 0 < ν) (n : ℕ) :
    (gegenbauerC ν n).coeff n ≠ 0 := by
  rw [gegenbauerC_eq, finsetSum_coeff, Finset.sum_eq_single 0]
  · rw [coeff_C_mul_X_pow]
    split_ifs with h'
    swap
    · omega
    have hpos := ascPochhammer_pos (n - 0) ν hν
    exact mul_ne_zero (div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) hpos.ne')
      (by positivity)) (by positivity)
  · intro k hk0 hk
    rw [Finset.mem_range] at hk0
    rw [coeff_C_mul_X_pow]
    split_ifs with h'
    · omega
    · rfl
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.succ_pos _)) h

/-- `F_{m,r,δ}` is even: its coefficients of odd degree vanish. -/
theorem coeff_reducedGegenbauer_eq_zero_of_odd (m r δ j : ℕ) (hj : j % 2 = 1) :
    (reducedGegenbauer m r δ).coeff j = 0 := by
  rw [reducedGegenbauer_eq, coeff_divByMonic_X_pow_eq_coeff_add]
  exact coeff_gegenbauerC_eq_zero_of_mod_two_ne _ _ _ (by omega)

/-- **The substitution `t = x^2`.** `F_{m,r,δ}(x) = Q_{m,r,δ}(x^2)`. -/
theorem expand_reducedGegenbauerSquare (m r δ : ℕ) :
    expand ℚ 2 (reducedGegenbauerSquare m r δ) = reducedGegenbauer m r δ := by
  ext n
  rw [reducedGegenbauerSquare_eq, coeff_expand two_pos, coeff_contract two_ne_zero]
  split_ifs with h
  · rw [Nat.div_mul_cancel h]
  · exact (coeff_reducedGegenbauer_eq_zero_of_odd m r δ n (by omega)).symm

/-- `deg F_{m,r,δ} = 2m`. -/
theorem natDegree_reducedGegenbauer_eq_two_mul (m r δ : ℕ) :
    (reducedGegenbauer m r δ).natDegree = 2 * m := by
  have hν : (0 : ℚ) < (r : ℚ) + 1 / 2 := by positivity
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [reducedGegenbauer_eq, coeff_divByMonic_X_pow_eq_coeff_add]
    exact coeff_gegenbauerC_eq_zero_of_lt _ _ _ (by omega)
  · rw [reducedGegenbauer_eq, coeff_divByMonic_X_pow_eq_coeff_add]
    exact coeff_gegenbauerC_self_ne_zero _ hν _

/-- `deg Q_{m,r,δ} = m`. -/
theorem natDegree_reducedGegenbauerSquare (m r δ : ℕ) :
    (reducedGegenbauerSquare m r δ).natDegree = m := by
  have h := congrArg natDegree (expand_reducedGegenbauerSquare m r δ)
  rw [natDegree_expand, natDegree_reducedGegenbauer_eq_two_mul] at h
  omega

/-- `F_{m,r,δ}(x) = Q_{m,r,δ}(x^2)` in every `ℚ`-algebra. -/
theorem aeval_reducedGegenbauer {A : Type*} [CommSemiring A] [Algebra ℚ A] (m r δ : ℕ)
    (x : A) :
    aeval x (reducedGegenbauer m r δ) = aeval (x ^ 2) (reducedGegenbauerSquare m r δ) := by
  rw [← expand_reducedGegenbauerSquare, expand_aeval]

/-- **The map of affine equations.** `(x, y)` lies on `y^2 = F_{m,r,δ}(x)` if and only if
`(x^2, y)` lies on `y^2 = Q_{m,r,δ}(t)` (over every `ℚ`-algebra). -/
theorem sq_eq_aeval_reducedGegenbauer_iff {A : Type*} [CommSemiring A] [Algebra ℚ A]
    (m r δ : ℕ) (x y : A) :
    y ^ 2 = aeval x (reducedGegenbauer m r δ) ↔
      y ^ 2 = aeval (x ^ 2) (reducedGegenbauerSquare m r δ) := by
  rw [aeval_reducedGegenbauer]

/-- **The fibre of `(x, y) ↦ (x^2, y)`.** Over a point `(t, y)` of `y^2 = Q_{m,r,δ}(t)`, the
points `(x, y)` of `y^2 = F_{m,r,δ}(x)` mapping to it are exactly those with `x^2 = t`. -/
theorem squareMap_fiber_iff {A : Type*} [CommSemiring A] [Algebra ℚ A] (m r δ : ℕ)
    {t y : A} (hty : y ^ 2 = aeval t (reducedGegenbauerSquare m r δ)) (x : A) :
    (y ^ 2 = aeval x (reducedGegenbauer m r δ) ∧ x ^ 2 = t) ↔ x ^ 2 = t := by
  refine ⟨And.right, fun hx => ⟨?_, hx⟩⟩
  rw [sq_eq_aeval_reducedGegenbauer_iff, hx]
  exact hty

/-- Over a domain, the fibre `{x : x^2 = t}` consists of at most the two points `±x₀`. -/
theorem eq_or_eq_neg_of_sq_eq {A : Type*} [CommRing A] [NoZeroDivisors A] {x x₀ : A}
    (h : x ^ 2 = x₀ ^ 2) : x = x₀ ∨ x = -x₀ :=
  sq_eq_sq_iff_eq_or_eq_neg.1 h

/-- If `2 ≠ 0` in a domain and `x₀ ≠ 0`, the two points `±x₀` of the fibre are distinct. -/
theorem neg_ne_self_of_ne_zero {A : Type*} [CommRing A] [NoZeroDivisors A]
    (h2 : (2 : A) ≠ 0) {x₀ : A} (hx₀ : x₀ ≠ 0) : -x₀ ≠ x₀ := by
  intro h
  have : (2 : A) * x₀ = 0 := by linear_combination -h
  exact (mul_ne_zero h2 hx₀) this

section CoordinateRing

/-! ### The map on affine coordinate rings is finite free of rank two

For `q ∈ R[t]` put `f(x) = q(x^2)` (`f = expand R 2 q`). The map `(x, y) ↦ (x^2, y)` from
`y^2 = f(x)` to `y^2 = q(t)` corresponds to the ring map
`squareMap q : R[t, y]/(y^2 - q(t)) → R[x, y]/(y^2 - f(x))`, `t ↦ x^2`, `y ↦ y`. Adjoining a
square root of `t` to the source gives the target (`squareRootExtensionEquiv`), so the
target is a free module of rank two over the source (`free_and_finrank_squareMap`): on the
affine models the map is finite and flat of degree two. -/

variable {R : Type*} [CommRing R]

/-- The coordinate ring `R[x, y]/(y^2 - f(x))` of the affine curve `y^2 = f(x)`; the
coordinate `x` is `AdjoinRoot.of _ X` and `y` is `AdjoinRoot.root _`. -/
abbrev HyperellipticCoordRing (f : R[X]) : Type _ := AdjoinRoot (X ^ 2 - C f : R[X][X])

/-- In `S[y]/(y^2 - a)`, `y^2 = a`. -/
theorem root_sq_eq_of {S : Type*} [CommRing S] (a : S) :
    AdjoinRoot.root (X ^ 2 - C a) ^ 2 = AdjoinRoot.of (X ^ 2 - C a) a := by
  have h := AdjoinRoot.eval₂_root (X ^ 2 - C a)
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h
  exact sub_eq_zero.1 h

/-- The ring map of `(x, y) ↦ (x^2, y)`: `R[t, y]/(y^2 - q(t)) → R[x, y]/(y^2 - q(x^2))`,
`t ↦ x^2`, `y ↦ y`. -/
noncomputable def squareMap (q : R[X]) :
    HyperellipticCoordRing q →+* HyperellipticCoordRing (expand R 2 q) :=
  AdjoinRoot.lift ((AdjoinRoot.of _).comp (expand R 2 : R[X] →ₐ[R] R[X]).toRingHom)
    (AdjoinRoot.root _) (by
      have h := root_sq_eq_of (expand R 2 q)
      simp only [eval₂_sub, eval₂_X_pow, eval₂_C]
      exact sub_eq_zero.2 h)

theorem squareMap_of (q p : R[X]) :
    squareMap q (AdjoinRoot.of _ p) = AdjoinRoot.of _ (expand R 2 p) := by
  rw [squareMap, AdjoinRoot.lift_of]
  try rfl

theorem squareMap_root (q : R[X]) :
    squareMap q (AdjoinRoot.root _) = AdjoinRoot.root _ := by
  rw [squareMap, AdjoinRoot.lift_root]

/-- `R[t, y]/(y^2 - q(t))` with a square root of `t` adjoined. -/
abbrev SquareRootExtension (q : R[X]) : Type _ :=
  AdjoinRoot (X ^ 2 - C (AdjoinRoot.of (X ^ 2 - C q) X) : (HyperellipticCoordRing q)[X])

/-- `R[x] → SquareRootExtension q`, `x ↦ √t`. -/
noncomputable def squareRootCoord (q : R[X]) : R[X] →+* SquareRootExtension q :=
  eval₂RingHom (((AdjoinRoot.of _).comp (AdjoinRoot.of _)).comp C) (AdjoinRoot.root _)

theorem squareRootCoord_expand (q p : R[X]) :
    squareRootCoord q (expand R 2 p) = AdjoinRoot.of _ (AdjoinRoot.of _ p) := by
  have h : (squareRootCoord q).comp (expand R 2 : R[X] →ₐ[R] R[X]).toRingHom =
      (AdjoinRoot.of _).comp (AdjoinRoot.of _) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp [squareRootCoord]
    · simp only [squareRootCoord, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, expand_X, coe_eval₂RingHom, eval₂_X_pow]
      exact root_sq_eq_of _
  exact congrArg (fun φ : R[X] →+* SquareRootExtension q => φ p) h

/-- `SquareRootExtension q → R[x, y]/(y^2 - q(x^2))`, `t ↦ x^2`, `y ↦ y`, `√t ↦ x`. -/
noncomputable def squareRootExtensionToCoordRing (q : R[X]) :
    SquareRootExtension q →+* HyperellipticCoordRing (expand R 2 q) :=
  AdjoinRoot.lift (squareMap q) (AdjoinRoot.of _ X) (by
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C, squareMap_of, expand_X, map_pow, sub_self])

/-- `R[x, y]/(y^2 - q(x^2)) → SquareRootExtension q`, `x ↦ √t`, `y ↦ y`. -/
noncomputable def coordRingToSquareRootExtension (q : R[X]) :
    HyperellipticCoordRing (expand R 2 q) →+* SquareRootExtension q :=
  AdjoinRoot.lift (squareRootCoord q) (AdjoinRoot.of _ (AdjoinRoot.root _)) (by
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C, squareRootCoord_expand, ← map_pow,
      root_sq_eq_of, sub_self])

/-- **Adjoining `√t` to `R[t, y]/(y^2 - q(t))` gives `R[x, y]/(y^2 - q(x^2))`**, compatibly
with `squareMap q`. -/
noncomputable def squareRootExtensionEquiv (q : R[X]) :
    SquareRootExtension q ≃+* HyperellipticCoordRing (expand R 2 q) :=
  RingEquiv.ofRingHom (squareRootExtensionToCoordRing q) (coordRingToSquareRootExtension q)
    (by
      refine AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext (fun a => ?_) ?_) ?_
      · simp [squareRootExtensionToCoordRing, coordRingToSquareRootExtension, squareRootCoord,
          squareMap_of]
      · simp [squareRootExtensionToCoordRing, coordRingToSquareRootExtension, squareRootCoord]
      · simp [squareRootExtensionToCoordRing, coordRingToSquareRootExtension, squareMap_root])
    (by
      refine AdjoinRoot.ringHom_ext
        (AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext (fun a => ?_) ?_) ?_) ?_
      · simp [squareRootExtensionToCoordRing, coordRingToSquareRootExtension, squareRootCoord,
          squareMap_of]
      · simp only [RingHom.comp_apply, squareRootExtensionToCoordRing, AdjoinRoot.lift_of,
          squareMap_of, coordRingToSquareRootExtension, squareRootCoord_expand, RingHom.id_apply]
      · simp [squareRootExtensionToCoordRing, coordRingToSquareRootExtension, squareMap_root]
      · simp [squareRootExtensionToCoordRing, coordRingToSquareRootExtension, squareRootCoord])

theorem squareRootExtensionEquiv_of (q : R[X]) (a : HyperellipticCoordRing q) :
    squareRootExtensionEquiv q (AdjoinRoot.of _ a) = squareMap q a := by
  rw [squareRootExtensionEquiv, RingEquiv.ofRingHom_apply, squareRootExtensionToCoordRing,
    AdjoinRoot.lift_of]

/-- **The map `(x, y) ↦ (x^2, y)` is finite free of degree two on affine models.** Over a
nontrivial commutative ring `R`, for the algebra structure given by `squareMap q`, the ring
`R[x, y]/(y^2 - q(x^2))` is a free module of rank `2` over `R[t, y]/(y^2 - q(t))`. -/
theorem free_and_finrank_squareMap [Nontrivial R] (q : R[X])
    [Algebra (HyperellipticCoordRing q) (HyperellipticCoordRing (expand R 2 q))]
    (hq : algebraMap (HyperellipticCoordRing q) (HyperellipticCoordRing (expand R 2 q)) =
      squareMap q) :
    Module.Free (HyperellipticCoordRing q) (HyperellipticCoordRing (expand R 2 q)) ∧
      Module.finrank (HyperellipticCoordRing q) (HyperellipticCoordRing (expand R 2 q)) = 2 := by
  have : Nontrivial (HyperellipticCoordRing q) :=
    (AdjoinRoot.nontrivial_iff_of_monic (monic_X_pow_sub_C q two_ne_zero)).2
      (natDegree_pos_iff_degree_pos.1 (by rw [natDegree_X_pow_sub_C]; exact two_pos))
  have hmon : (X ^ 2 - C (AdjoinRoot.of (X ^ 2 - C q) X) :
      (HyperellipticCoordRing q)[X]).Monic := monic_X_pow_sub_C _ two_ne_zero
  let pb := AdjoinRoot.powerBasis' hmon
  let e : SquareRootExtension q ≃ₐ[HyperellipticCoordRing q]
      HyperellipticCoordRing (expand R 2 q) :=
    AlgEquiv.ofRingEquiv (f := squareRootExtensionEquiv q) (fun a => by
      rw [AdjoinRoot.algebraMap_eq, hq, squareRootExtensionEquiv_of])
  have : Module.Free (HyperellipticCoordRing q) (SquareRootExtension q) :=
    Module.Free.of_basis pb.basis
  refine ⟨Module.Free.of_equiv e.toLinearEquiv, ?_⟩
  rw [← e.toLinearEquiv.finrank_eq, pb.finrank, AdjoinRoot.powerBasis'_dim,
    natDegree_X_pow_sub_C]

/-- For the derivative families: `ℚ[x, y]/(y^2 - F_{m,r,δ}(x))` is free of rank two over
`ℚ[t, y]/(y^2 - Q_{m,r,δ}(t))` via `t ↦ x^2`, `y ↦ y` (here `F_{m,r,δ} = expand ℚ 2 Q_{m,r,δ}`,
`expand_reducedGegenbauerSquare`). -/
theorem free_and_finrank_squareMap_reducedGegenbauerSquare (m r δ : ℕ)
    [Algebra (HyperellipticCoordRing (reducedGegenbauerSquare m r δ))
      (HyperellipticCoordRing (expand ℚ 2 (reducedGegenbauerSquare m r δ)))]
    (hq : algebraMap (HyperellipticCoordRing (reducedGegenbauerSquare m r δ))
      (HyperellipticCoordRing (expand ℚ 2 (reducedGegenbauerSquare m r δ))) =
        squareMap (reducedGegenbauerSquare m r δ)) :
    Module.Free (HyperellipticCoordRing (reducedGegenbauerSquare m r δ))
        (HyperellipticCoordRing (expand ℚ 2 (reducedGegenbauerSquare m r δ))) ∧
      Module.finrank (HyperellipticCoordRing (reducedGegenbauerSquare m r δ))
        (HyperellipticCoordRing (expand ℚ 2 (reducedGegenbauerSquare m r δ))) = 2 :=
  free_and_finrank_squareMap _ hq

end CoordinateRing

end ArithmeticOfJacobiPolynomials
