/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.CartierLinearEquivalence
public import ArithmeticOfJacobiPolynomials.Geometry.HyperellipticDivisors
public import ArithmeticOfJacobiPolynomials.Geometry.HyperellipticBranchPoints

/-!
# Branch-point divisors of the hyperelliptic curve: `2 [P_c] ~ 2 [P_{c'}]`

Let `k` be a field with `2 ≠ 0` and `f ∈ k[x]` separable. For a root `c` of `f`, `P_c = (c, 0)`
is a point of the finite chart `y^2 = f(x)` of the projective model `X = projectiveModel f`
(`ArithmeticOfJacobiPolynomials.Hyperelliptic.branchPoint`); the roots of `f` are exactly the
finite branch
points of the double cover `X → ℙ¹`
(`ArithmeticOfJacobiPolynomials.Hyperelliptic.isFiniteBranchPoint_iff`).
This file proves the first step of the statement (§6.5) that the divisor classes
supported on the branch points are `2`-torsion: `2 [P_c] ~ 2 [P_{c'}]` for any two roots `c, c'`
of `f`. All divisor theory is Stacks': effective Cartier divisors are
`Stacks.Divisors.IsEffectiveCartierDivisor` ideal sheaves, linear equivalence is
`Stacks.Divisors.LinearlyEquivalent` (Tag 0CCT, `𝒪_X(D) ≅ 𝒪_X(D')`), and classes live in
`Stacks.Picard.ofScheme X` (`Stacks.Divisors.picardClass`).

## Main definitions and results

* `ArithmeticOfJacobiPolynomials.Divisors.pointIdeal P`: the ideal sheaf of a point (the vanishing
ideal sheaf
  of its closure); a section `s` over an affine open lies in it iff `P ∉ D(s)`
  (`ArithmeticOfJacobiPolynomials.Divisors.mem_pointIdeal_iff`).
* `ArithmeticOfJacobiPolynomials.Hyperelliptic.branchIdeal hc`: the ideal sheaf of `P_c`. On the
finite chart it
  is the maximal ideal `(x - c, y)` (`branchIdeal_ideal_chartOpen`), and its square is the
  principal ideal `(x - c)` (`branchIdeal_mul_self_ideal_chartOpen`, using that `f` is
  separable: `f/(x - c)` does not vanish at `c`).
* `ArithmeticOfJacobiPolynomials.Hyperelliptic.isEffectiveCartierDivisor_branchIdeal`: `P_c` is an
effective
  Cartier divisor, with local generator `y` on `D(f/(x - c))`.
* `ArithmeticOfJacobiPolynomials.Hyperelliptic.linearlyEquivalent_branchIdeal_sq`: for roots `c,
c'` of `f`,
  `2 P_c ~ 2 P_{c'}`, from
  `ArithmeticOfJacobiPolynomials.Divisors.linearlyEquivalent_of_two_local_ratios`. The
  rational function `(x - c)/(x - c')` realizes the linear equivalence: on the finite chart the
  generators are `x - c` and `x - c'`; near infinity they are the units `1 - c/x` and
  `1 - c'/x`.
* `ArithmeticOfJacobiPolynomials.Hyperelliptic.two_nsmul_picardClass_branchIdeal_eq`: the same in
the Picard
  group, `2 • picardClass P_c = 2 • picardClass P_{c'}`.

Nothing is claimed about the Jacobian.
-/

public section

namespace ArithmeticOfJacobiPolynomials

namespace Hyperelliptic

open _root_.Polynomial renaming X → polyX

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite _root_.Polynomial Divisors

universe u

variable {k : Type u} [Field k] {f : k[X]} {c : k}

/-- **The branch point `P_c` is an effective Cartier divisor** (`f` separable): `y` is a local
equation on `D(f/(x - c))`, and `1` away from `P_c`. -/
theorem isEffectiveCartierDivisor_branchIdeal (hf : f.Separable) (hc : f.eval c = 0) :
    Stacks.Divisors.IsEffectiveCartierDivisor (branchIdeal f hc) := by
  refine Stacks.Divisors.isEffectiveCartierDivisor_of_forall_exists_affineOpen _ fun x => ?_
  by_cases hx : x = branchPoint f c hc
  · subst hx
    exact ⟨_, (isAffineOpen_opensRange (affineChart f)).basicOpen
      (finiteFn f (f /ₘ (Polynomial.X - C c))), branchPoint_mem_basicOpen_divByMonic hf hc, _,
      isRegular_iff_mem_nonZeroDivisors.mpr (finiteY_res_mem_nonZeroDivisors hf hc),
      branchIdeal_ideal_basicOpen_divByMonic hf hc⟩
  · obtain ⟨V, hxV, hPV⟩ := exists_affineOpen_not_mem hc hx
    refine ⟨V.1, V.2, hxV, 1, isRegular_one, ?_⟩
    rw [Ideal.span_singleton_one]
    exact pointIdeal_ideal_eq_top _ V hPV

/-- **`2 P_c ~ 2 P_{c'}`**: for roots `c, c'` of a separable `f` (over a field with `2 ≠ 0`), the
effective Cartier divisors `2 P_c` and `2 P_{c'}` are linearly equivalent
(`𝒪_X(2 P_c) ≅ 𝒪_X(2 P_{c'})`, Tag 0CCT); the rational function `(x - c)/(x - c')` has
divisor `2 P_c - 2 P_{c'}`. -/
theorem linearlyEquivalent_branchIdeal_sq (h2 : (2 : k) ≠ 0) (hf : f.Separable) {c' : k}
    (hc : f.eval c = 0) (hc' : f.eval c' = 0) :
    Stacks.Divisors.LinearlyEquivalent (branchIdeal f hc ^ 2) (branchIdeal f hc' ^ 2) := by
  have hdeg : 0 < f.natDegree := natDegree_pos_of_eval_eq_zero hf hc
  have := isIntegral_projectiveModel hf hdeg
  have := isNormal_projectiveModel h2 hf hdeg
  have := isEffectiveCartierDivisor_branchIdeal hf hc
  have := isEffectiveCartierDivisor_branchIdeal hf hc'
  have hcov := mem_chartOpen_or_mem_basicOpen_mul (f := f) c c'
  have hUinf := isAffineOpen_opensRange (affineChartAtInfinity f)
  have hW₂ : (projectiveModel f).basicOpen
      (infiniteFn f (1 - C c * Polynomial.X) * infiniteFn f (1 - C c' * Polynomial.X)) ≤
        (projectiveModel f).basicOpen (infiniteFn f (1 - C c * Polynomial.X)) ⊓
          (projectiveModel f).basicOpen (infiniteFn f (1 - C c' * Polynomial.X)) := by
    rw [Scheme.basicOpen_mul]
  let W₂ : (projectiveModel f).affineOpens :=
    ⟨_, hUinf.basicOpen
      (infiniteFn f (1 - C c * Polynomial.X) * infiniteFn f (1 - C c' * Polynomial.X))⟩
  have hW₂a : W₂.1 ≤ (projectiveModel f).basicOpen (infiniteFn f (1 - C c * Polynomial.X)) :=
    hW₂.trans inf_le_left
  have hW₂b : W₂.1 ≤ (projectiveModel f).basicOpen (infiniteFn f (1 - C c' * Polynomial.X)) :=
    hW₂.trans inf_le_right
  have hW₂inf : W₂.1 ≤ chartOpenAtInfinity f :=
    hW₂a.trans ((projectiveModel f).basicOpen_le _)
  rw [sq, sq]
  refine Divisors.linearlyEquivalent_of_two_local_ratios _ _ inferInstance inferInstance
    (chartAffineOpen f) W₂ hcov (τ₁ := finiteFn f (Polynomial.X - C c))
    (σ₁ := finiteFn f (Polynomial.X - C c'))
    (τ₂ := (projectiveModel f).presheaf.map (homOfLE (hW₂a.trans
      ((projectiveModel f).basicOpen_le _))).op (infiniteFn f (1 - C c * Polynomial.X)))
    (σ₂ := (projectiveModel f).presheaf.map (homOfLE (hW₂b.trans
      ((projectiveModel f).basicOpen_le _))).op (infiniteFn f (1 - C c' * Polynomial.X)))
    (branchIdeal_mul_self_ideal_chartOpen hf hc)
    (branchIdeal_mul_self_ideal_eq_span_of_le hc W₂ hW₂a)
    (branchIdeal_mul_self_ideal_chartOpen hf hc')
    (branchIdeal_mul_self_ideal_eq_span_of_le hc' W₂ hW₂b)
    (finiteFn_mem_nonZeroDivisors hf hdeg (X_sub_C_ne_zero c))
    (isUnit_res_of_le_basicOpen _ hW₂a).mem_nonZeroDivisors
    (finiteFn_mem_nonZeroDivisors hf hdeg (X_sub_C_ne_zero c'))
    (isUnit_res_of_le_basicOpen _ hW₂b).mem_nonZeroDivisors
    (fun x h₁ h₂ => germ_branch_compat c c' x h₁ hW₂inf h₂)

/-- **`2 P_c ~ 2 P_{c'}` in the Picard group**: `2 • [𝒪_X(P_c)] = 2 • [𝒪_X(P_{c'})]` in
`Stacks.Picard.ofScheme X`. -/
theorem two_nsmul_picardClass_branchIdeal_eq (h2 : (2 : k) ≠ 0) (hf : f.Separable) {c' : k}
    (hc : f.eval c = 0) (hc' : f.eval c' = 0) :
    haveI := isEffectiveCartierDivisor_branchIdeal hf hc
    haveI := isEffectiveCartierDivisor_branchIdeal hf hc'
    2 • Stacks.Divisors.picardClass (branchIdeal f hc) =
      2 • Stacks.Divisors.picardClass (branchIdeal f hc') := by
  have := isEffectiveCartierDivisor_branchIdeal hf hc
  have := isEffectiveCartierDivisor_branchIdeal hf hc'
  have h := (Divisors.linearlyEquivalent_iff_picardClass_eq' _ _).mp
    (linearlyEquivalent_branchIdeal_sq h2 hf hc hc')
  rwa [Stacks.Divisors.picardClass_pow, Stacks.Divisors.picardClass_pow] at h

end Hyperelliptic

end ArithmeticOfJacobiPolynomials
