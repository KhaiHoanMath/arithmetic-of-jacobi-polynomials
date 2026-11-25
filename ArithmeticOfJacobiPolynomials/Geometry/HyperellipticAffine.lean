/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Applications.Jacobians
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Smoothness of the affine hyperelliptic curve `y^2 = f(x)` (Jacobian criterion)

For a field `k` with `2 ≠ 0` and a separable polynomial `f ∈ k[x]`, the coordinate ring
`k[x, y]/(y^2 - f(x))` (`HyperellipticCoordRing f`) is a smooth `k`-algebra
(`smooth_hyperellipticCoordRing`). This is the Jacobian criterion for the affine curve
`y^2 = f(x)`: from `a f + b f' = 1` one gets `a(x) y^2 + b(x) f'(x) = 1`, so the affine curve
is covered by the two basic opens `D(y)` and `D(f'(x))`. On `D(y)` the ring is standard étale
over `k[x]` (the partial derivative `2y` of `y^2 - f(x)` in `y` is a unit), on `D(f'(x))` it is
standard étale over `k[y]` (the partial derivative `-f'(x)` in `x` is a unit); both are
therefore smooth over `k`.

The second affine chart of the smooth projective model is `w^2 = x'^{2g+2} f(1/x')`, i.e. the
curve attached to the reflected polynomial `reflect (2g+2) f` (`2g + 2 ∈ {d, d+1}`). The
reflection of a separable polynomial of degree `d` at `N ∈ {d, d+1}` is separable
(`separable_reflect`), so this chart is smooth as well (`smooth_hyperellipticCoordRing_reflect`).
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial

namespace Hyperelliptic

variable {k : Type*} [Field k]

/-! ### The reflected polynomial `x^N f(1/x)` -/

theorem X_mul_C_mul_X_pow_sub_one (a : k) (m : ℕ) :
    X * (C (a * m) * X ^ (m - 1)) = C (a * m) * X ^ m := by
  cases m with
  | zero => simp
  | succ m => simp only [Nat.add_sub_cancel]; ring

/-- Euler's identity for the reflection: `x (f^*)' + (x f')^* = N f^*` with `f^* = reflect N f`,
for `deg f ≤ N`. -/
theorem X_mul_derivative_reflect (N : ℕ) (f : k[X]) (hf : f.natDegree ≤ N) :
    X * derivative (reflect N f) + reflect N (X * derivative f) = C (N : k) * reflect N f := by
  refine induction_with_natDegree_le
    (fun f => X * derivative (reflect N f) + reflect N (X * derivative f) =
      C (N : k) * reflect N f) N ?_ ?_ ?_ f hf
  · simp
  · intro n r _ hn
    rw [reflect_C_mul_X_pow, revAt_le hn, derivative_C_mul_X_pow, derivative_C_mul_X_pow,
      X_mul_C_mul_X_pow_sub_one, X_mul_C_mul_X_pow_sub_one, reflect_C_mul_X_pow, revAt_le hn,
      ← add_mul, ← C_add, ← mul_add, ← Nat.cast_add, Nat.sub_add_cancel hn, ← mul_assoc,
      ← C_mul, mul_comm r]
  · intro f g _ _ hf hg
    beta_reduce at hf hg ⊢
    simp only [reflect_add, derivative_add, mul_add]
    linear_combination hf + hg

theorem natDegree_X_mul_derivative_le (f : k[X]) :
    (X * derivative f).natDegree ≤ f.natDegree := by
  by_cases h0 : f.natDegree = 0
  · rw [derivative_of_natDegree_zero h0, mul_zero, natDegree_zero]
    exact Nat.zero_le _
  by_cases hd : derivative f = 0
  · rw [hd, mul_zero, natDegree_zero]
    exact Nat.zero_le _
  rw [natDegree_X_mul hd]
  have := natDegree_derivative_lt h0
  omega

/-- Evaluating the reflection: `f^*(a) = a^N f(1/a)` for `a ≠ 0`. -/
theorem aeval_reflect_mul_pow {K : Type*} [Field K] [Algebra k K] (N : ℕ) (f : k[X])
    (hf : f.natDegree ≤ N) {a : K} (ha : a ≠ 0) :
    aeval a (reflect N f) * a⁻¹ ^ N = aeval a⁻¹ f := by
  let : Invertible a⁻¹ := invertibleOfNonzero (inv_ne_zero ha)
  have h := eval₂_reflect_mul_pow (algebraMap k K) a⁻¹ N f hf
  rw [invOf_eq_inv, inv_inv] at h
  rw [aeval_def, aeval_def, h]

/-- The reflection `x^N f(1/x)` of a separable polynomial `f` of degree `d` at `N = d` or
`N = d + 1` is separable. -/
theorem separable_reflect {f : k[X]} (hf : f.Separable) {N : ℕ} (hN : f.natDegree ≤ N)
    (hN' : N ≤ f.natDegree + 1) : (reflect N f).Separable := by
  let K := AlgebraicClosure k
  have hf0 : f ≠ 0 := hf.ne_zero
  have hlead : f.coeff f.natDegree ≠ 0 := by
    rw [← leadingCoeff]
    exact leadingCoeff_ne_zero.mpr hf0
  have hfK := (isCoprime_iff_aeval_ne_zero_of_isAlgClosed k K f (derivative f)).mp hf
  refine (isCoprime_iff_aeval_ne_zero_of_isAlgClosed k K _ _).mpr fun a => ?_
  by_cases ha : a = 0
  · subst ha
    rw [aeval_def, aeval_def, eval₂_at_zero, eval₂_at_zero, coeff_derivative, coeff_reflect,
      coeff_reflect, revAt_le (Nat.zero_le N)]
    obtain h | h : N = f.natDegree ∨ N = f.natDegree + 1 := by omega
    · left
      have hN0 : N - 0 = f.natDegree := by omega
      rw [hN0]
      simpa using hlead
    · right
      have hN1 : N - (0 + 1) = f.natDegree := by omega
      rw [revAt_le (by omega : 0 + 1 ≤ N), hN1]
      simpa using hlead
  · by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hE := congrArg (aeval a) (X_mul_derivative_reflect N f hN)
    simp only [map_add, map_mul, aeval_X, aeval_C, h1, h2, mul_zero, zero_add] at hE
    have hb : aeval a⁻¹ (X * derivative f) = 0 := by
      rw [← aeval_reflect_mul_pow N _ ((natDegree_X_mul_derivative_le f).trans hN) ha, hE,
        zero_mul]
    have hb1 : aeval a⁻¹ f = 0 := by
      rw [← aeval_reflect_mul_pow N f hN ha, h1, zero_mul]
    rw [map_mul, aeval_X] at hb
    have hb2 : aeval a⁻¹ (derivative f) = 0 :=
      (mul_eq_zero.mp hb).resolve_left (inv_ne_zero ha)
    rcases hfK a⁻¹ with h | h
    · exact h hb1
    · exact h hb2

/-! ### The chart `D(y)`: standard étale over `k[x]` -/

/-- The standard étale pair `(Y^2 - f, Y)` over `k[x]` (its derivative `2Y` is a unit times `Y`). -/
noncomputable def yChartPair (f : k[X]) (h2 : (2 : k) ≠ 0) : StandardEtalePair k[X] where
  f := X ^ 2 - C f
  monic_f := monic_X_pow_sub_C f two_ne_zero
  g := X
  cond := ⟨C (C (2⁻¹ : k)), 0, 1, by
    have h : (C (C (2⁻¹ : k)) : k[X][X]) * C (C 2) = 1 := by
      rw [← C_mul, ← C_mul, inv_mul_cancel₀ h2, C_1, C_1]
    rw [derivative_sub, derivative_C, sub_zero, derivative_X_pow, mul_zero, add_zero, pow_one]
    have h2' : (C ((2 : ℕ) : k[X]) : k[X][X]) = C (C 2) := by
      rw [← map_natCast (C : k →+* k[X]) 2, Nat.cast_ofNat]
    rw [h2']
    linear_combination (X : k[X][X]) * h⟩

instance smooth_polynomial : Algebra.Smooth k k[X] :=
  Algebra.Smooth.mk (Algebra.FormallySmooth.polynomial k) inferInstance

theorem smooth_away_root (f : k[X]) (h2 : (2 : k) ≠ 0) :
    Algebra.Smooth k (Localization.Away (AdjoinRoot.root (X ^ 2 - C f : k[X][X]))) := by
  have : Algebra.Smooth k[X]
      (Localization.Away (AdjoinRoot.root (X ^ 2 - C f : k[X][X]))) :=
    Algebra.Smooth.of_equiv (yChartPair f h2).equivAwayAdjoinRoot
  exact Algebra.Smooth.comp (R := k) (A := k[X]) _

/-! ### The chart `D(f'(x))`: standard étale over `k[y]` -/

/-- `c⁻¹ (f(X) - y^2)` as a monic polynomial in `X` over `k[y]`. -/
noncomputable def swappedEquation (f : k[X]) : k[X][X] :=
  C (C f.leadingCoeff⁻¹) * (f.map C - C (X ^ 2))

theorem swappedEquation_eq (f : k[X]) :
    swappedEquation f =
      C (C (-f.leadingCoeff⁻¹)) * Bivariate.swap (X ^ 2 - C f : k[X][X]) := by
  rw [map_sub, map_pow, Bivariate.swap_Y, Bivariate.swap_C, swappedEquation]
  simp only [map_neg, map_pow]
  ring

theorem derivative_swappedEquation (f : k[X]) :
    derivative (swappedEquation f) = C (C f.leadingCoeff⁻¹) * (derivative f).map C := by
  rw [swappedEquation, derivative_C_mul, derivative_sub, derivative_C, sub_zero, derivative_map]

theorem monic_swappedEquation {f : k[X]} (hf : 0 < f.natDegree) :
    (swappedEquation f).Monic := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hf
  apply monic_C_mul_of_mul_leadingCoeff_eq_one
  have hdeg : (C (X ^ 2) : k[X][X]).degree < (f.map C).degree := by
    rw [degree_map_eq_of_injective C_injective]
    exact (degree_C_le).trans_lt (natDegree_pos_iff_degree_pos.mp hf)
  rw [leadingCoeff_sub_of_degree_lt hdeg, leadingCoeff_map_of_injective C_injective, ← C_mul,
    inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hf0), C_1]

/-- The standard étale pair `(c⁻¹ (f(X) - y^2), f'(X))` over `k[y]`. -/
noncomputable def derivChartPair (f : k[X]) (hf : 0 < f.natDegree) :
    StandardEtalePair k[X] where
  f := swappedEquation f
  monic_f := monic_swappedEquation hf
  g := (derivative f).map C
  cond := ⟨C (C f.leadingCoeff), 0, 1, by
    have hf0 : f ≠ 0 := by
      rintro rfl
      simp at hf
    have h : (C (C f.leadingCoeff⁻¹) : k[X][X]) * C (C f.leadingCoeff) = 1 := by
      rw [← C_mul, ← C_mul, inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hf0), C_1, C_1]
    rw [derivative_swappedEquation, mul_zero, add_zero, pow_one]
    linear_combination ((derivative f).map C) * h⟩

theorem smooth_away_derivChart (f : k[X]) (hf : 0 < f.natDegree) :
    Algebra.Smooth k (Localization.Away
      (AdjoinRoot.mk (swappedEquation f) ((derivative f).map C))) := by
  have : Algebra.Smooth k[X] (Localization.Away
      (AdjoinRoot.mk (swappedEquation f) ((derivative f).map C))) :=
    Algebra.Smooth.of_equiv (derivChartPair f hf).equivAwayAdjoinRoot
  exact Algebra.Smooth.comp (R := k) (A := k[X]) _

/-- Exchanging the roles of `x` and `y`: `k[x][y]/(y^2 - f(x)) ≃ k[y][x]/(c⁻¹ (f(x) - y^2))`. -/
noncomputable def swapEquiv (f : k[X]) (hf : f ≠ 0) :
    HyperellipticCoordRing f ≃ₐ[k] AdjoinRoot (swappedEquation f) :=
  Ideal.quotientEquivAlg (Ideal.span {(X ^ 2 - C f : k[X][X])})
    (Ideal.span {swappedEquation f}) (Bivariate.swap (R := k)) (by
    have hu : IsUnit (C (C (-f.leadingCoeff⁻¹)) : k[X][X]) :=
      isUnit_C.mpr (isUnit_C.mpr
        (neg_ne_zero.mpr (inv_ne_zero (leadingCoeff_ne_zero.mpr hf))).isUnit)
    rw [Ideal.map_span, Set.image_singleton, swappedEquation_eq,
      Ideal.span_singleton_mul_left_unit hu]
    try rfl)

theorem swapEquiv_of (f p : k[X]) (hf : f ≠ 0) :
    swapEquiv f hf (AdjoinRoot.of _ p) = AdjoinRoot.mk (swappedEquation f) (p.map C) := by
  change Ideal.quotientEquivAlg _ _ _ _ (Ideal.Quotient.mk _ (C p)) = _
  rw [Ideal.quotientEquivAlg_mk, Bivariate.swap_C]
  try rfl

theorem smooth_away_derivative (f : k[X]) (hf : 0 < f.natDegree) :
    Algebra.Smooth k (Localization.Away
      (AdjoinRoot.of (X ^ 2 - C f : k[X][X]) (derivative f))) := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hf
  have H : Submonoid.map (swapEquiv f hf0).toRingEquiv.toMonoidHom
      (Submonoid.powers (AdjoinRoot.of (X ^ 2 - C f : k[X][X]) (derivative f))) =
      Submonoid.powers (AdjoinRoot.mk (swappedEquation f) ((derivative f).map C)) := by
    rw [Submonoid.map_powers]
    congr 1
    exact swapEquiv_of f _ hf0
  let e := IsLocalization.ringEquivOfRingEquiv
    (Localization.Away (AdjoinRoot.of (X ^ 2 - C f : k[X][X]) (derivative f)))
    (Localization.Away (AdjoinRoot.mk (swappedEquation f) ((derivative f).map C)))
    (swapEquiv f hf0).toRingEquiv H
  have he : ∀ c : k, e (algebraMap k _ c) = algebraMap k _ c := by
    intro c
    simp only [e]
    rw [IsScalarTower.algebraMap_apply k (HyperellipticCoordRing f),
      IsLocalization.ringEquivOfRingEquiv_eq]
    change algebraMap _ _ ((swapEquiv f hf0) (algebraMap k _ c)) = _
    rw [AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  have := smooth_away_derivChart f hf
  exact Algebra.Smooth.of_equiv (AlgEquiv.ofRingEquiv (f := e) he).symm

/-! ### The Jacobian criterion -/

theorem finitePresentation_hyperellipticCoordRing (f : k[X]) :
    Algebra.FinitePresentation k (HyperellipticCoordRing f) := by
  have : Algebra.FinitePresentation k[X] (HyperellipticCoordRing f) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton _)
  exact Algebra.FinitePresentation.trans k k[X] _

/-- **Jacobian criterion** for `y^2 = f(x)`: if `2 ≠ 0` in `k` and `f` is separable, the affine
curve `y^2 = f(x)` is smooth over `k`. -/
theorem smooth_hyperellipticCoordRing {f : k[X]} (h2 : (2 : k) ≠ 0) (hf : f.Separable) :
    Algebra.Smooth k (HyperellipticCoordRing f) := by
  have := finitePresentation_hyperellipticCoordRing f
  refine Algebra.Smooth.mk ?_ inferInstance
  refine Algebra.smoothLocus_eq_univ_iff.mp (Set.eq_univ_of_forall fun p => ?_)
  obtain ⟨a, b, hab⟩ := hf
  by_cases hy : AdjoinRoot.root (X ^ 2 - C f : k[X][X]) ∈ p.asIdeal
  · have hu : AdjoinRoot.of (X ^ 2 - C f : k[X][X]) (derivative f) ∉ p.asIdeal := by
      intro hu
      apply p.isPrime.ne_top
      rw [Ideal.eq_top_iff_one]
      have h1 : AdjoinRoot.of (X ^ 2 - C f : k[X][X]) a *
          AdjoinRoot.root (X ^ 2 - C f : k[X][X]) ^ 2 +
          AdjoinRoot.of (X ^ 2 - C f : k[X][X]) b *
          AdjoinRoot.of (X ^ 2 - C f : k[X][X]) (derivative f) = 1 := by
        rw [root_sq_eq_of, ← map_mul, ← map_mul, ← map_add, hab, map_one]
      rw [← h1]
      exact p.asIdeal.add_mem (p.asIdeal.mul_mem_left _ (p.asIdeal.pow_mem_of_mem hy 2
        two_pos)) (p.asIdeal.mul_mem_left _ hu)
    by_cases hdeg : 0 < f.natDegree
    · exact (Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr
        (smooth_away_derivative f hdeg)) hu
    · exfalso
      apply hu
      rw [derivative_of_natDegree_zero (by omega), map_zero]
      exact p.asIdeal.zero_mem
  · exact (Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr (smooth_away_root f h2)) hy

/-- The second chart `w^2 = x'^N f(1/x')` (`N = deg f` or `deg f + 1`; for the smooth
projective model `N = 2g + 2`) is smooth over `k`. -/
theorem smooth_hyperellipticCoordRing_reflect {f : k[X]} (h2 : (2 : k) ≠ 0)
    (hf : f.Separable) {N : ℕ} (hN : f.natDegree ≤ N) (hN' : N ≤ f.natDegree + 1) :
    Algebra.Smooth k (HyperellipticCoordRing (reflect N f)) :=
  smooth_hyperellipticCoordRing h2 (separable_reflect hf hN hN')

end Hyperelliptic

end ArithmeticOfJacobiPolynomials
