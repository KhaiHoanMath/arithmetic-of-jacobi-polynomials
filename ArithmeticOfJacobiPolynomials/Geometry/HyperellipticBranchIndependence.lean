/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.HyperellipticBranchAlgebra
public import ArithmeticOfJacobiPolynomials.Geometry.HyperellipticBranchTorsion
public import ArithmeticOfJacobiPolynomials.Geometry.HyperellipticDivisors
public import Mathlib.GroupTheory.Index

/-!
# Independence of the branch-point classes in `Pic(X)[2]`

Let `k` be a field with `2 ≠ 0`, `f ∈ k[x]` separable and split over `k`, and
`X = projectiveModel f` the smooth projective model of `y^2 = f(x)`. The file
`ArithmeticOfJacobiPolynomials.Geometry.HyperellipticBranchTorsion` constructs the homomorphisms
`branchTorsionHom h2 hf c₀ : (ℤ/2)^{roots} → Stacks.Picard.ofScheme X`, `δ_c ↦ [P_c - P_{c₀}]`
(even degree), and `branchTorsionHomInf : (ℤ/2)^{roots} → Stacks.Picard.ofScheme X`,
`δ_c ↦ [P_c - P_∞]` (odd degree), and the relations in their kernels. Here we determine the kernels
exactly (§6.5: the classes supported on the branch points describe the `2`-torsion), and
deduce the order `2^{2g}` of the image. All divisor theory is Stacks': effective Cartier divisors
`Stacks.Divisors.IsEffectiveCartierDivisor`, classes `Stacks.Divisors.picardClass`, linear
equivalence `Stacks.Divisors.LinearlyEquivalent`, Weil divisors
`AlgebraicGeometry.effectiveCartierWeilDivisor` and
`AlgebraicGeometry.rationalFunctionWeilDivisor`.

## Main results

* `ArithmeticOfJacobiPolynomials.Hyperelliptic.branchTorsionHom_eq_zero_iff` (even degree `2g +
2`): `v` is in the
  kernel of `branchTorsionHom h2 hf c₀` iff `v` is constant on the roots `c ≠ c₀`; the kernel is
  spanned by `δ_{c₀}` (`[P_{c₀} - P_{c₀}] = 0`) and the all-ones vector.
* `ArithmeticOfJacobiPolynomials.Hyperelliptic.branchTorsionHomInf_eq_zero_iff` (odd degree `2g +
1`): the kernel
  of `branchTorsionHomInf` is `{0, (1, …, 1)}`.
* `ArithmeticOfJacobiPolynomials.Hyperelliptic.card_range_branchTorsionHom`,
  `ArithmeticOfJacobiPolynomials.Hyperelliptic.card_range_branchTorsionHomInf`: the image has order
  `2^{2g}`.

## Method

If `∑_{c ∈ S} [P_c - P_B] = 0` in `Pic X` (`B` the base point), the divisors `∏_{c ∈ S} P_c` and
`B^{|S|}` are linearly equivalent
(`ArithmeticOfJacobiPolynomials.Divisors.linearlyEquivalent_iff_picardClass_eq'`),
so by
`ArithmeticOfJacobiPolynomials.Divisors.linearlyEquivalent_iff_exists_rationalFunctionWeilDivisor`
their Weil
divisors differ by `div φ`. Since `2 P_c - 2 P_B = div ρ_c` for the explicit rational functions
`ρ_c = (x - c₀)/(x - c)` resp. `1/(x - c)`
(`ArithmeticOfJacobiPolynomials.Divisors.effectiveCartierWeilDivisor_eq_add_of_two_local_ratios`),
the function
`φ^2 / ∏_{c ∈ S} ρ_c` has trivial divisor, so it is a non-zero constant `l`
(`rationalFunctionWeilDivisor_eq_zero_iff_projectiveModel`). Clearing denominators in
`k[x, y]/(y^2 - f)` gives `α^2 ∏_{c ∈ S} (x - c) = β^2 · l b(x)^{|S|}`; multiplying by the square
of the conjugate `β(x, -y)` and comparing the coefficients of `1, y`
(`exists_sq_mul_eq_of_sq_mul_eq`) yields a polynomial identity `g^2 P = N^2 Q` or
`g^2 f P = N^2 Q` in `k[x]`, and comparing multiplicities of roots (`count_roots_mod_two_eq`)
forces `S` to be trivial.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Hyperelliptic

open _root_.Polynomial renaming X → polyX

open _root_.Polynomial Divisors

variable {k : Type u} [Field k] {f : k[X]}

/-! ### The Weil divisors of `P_c` and `P_∞` -/

section WeilDivisors

variable [IsIntegral (projectiveModel f)]

/-- The Weil divisor `[P_c]` of the branch point `P_c`. -/
@[expose] noncomputable def branchWeil (hf : f.Separable) {c : k} (hc : f.eval c = 0) :
    WeilDivisor (projectiveModel f) :=
  effectiveCartierWeilDivisor (branchIdeal f hc) (isEffectiveCartierDivisor_branchIdeal hf hc)

local notation "𝐆" => Scheme.germToFunctionField (projectiveModel f) (chartOpen f)

/-- **`2 P_{c₀} = 2 P_c + div ((x - c₀)/(x - c))`**, coefficientwise. -/
theorem branchWeil_two_eq (hf : f.Separable) {c c₀ : k} (hc : f.eval c = 0)
    (hc₀ : f.eval c₀ = 0) (Z : PrimeDivisor (projectiveModel f)) :
    (branchWeil hf hc₀).1 Z + (branchWeil hf hc₀).1 Z =
      ((branchWeil hf hc).1 Z + (branchWeil hf hc).1 Z) +
        (projectiveModel f).ord
          (𝐆 (finiteCoord f (Polynomial.X - C c₀)) / 𝐆 (finiteCoord f (Polynomial.X - C c)))
          Z.genericPoint := by
  have hdeg : 0 < f.natDegree := natDegree_pos_of_eval_eq_zero hf hc
  have hPc := isEffectiveCartierDivisor_branchIdeal hf hc
  have hPc₀ := isEffectiveCartierDivisor_branchIdeal hf hc₀
  have hUinf := isAffineOpen_opensRange (affineChartAtInfinity f)
  let W₂ : (projectiveModel f).affineOpens :=
    ⟨(projectiveModel f).basicOpen (infiniteCoord f (1 - C c * Polynomial.X) *
      infiniteCoord f (1 - C c₀ * Polynomial.X)), hUinf.basicOpen _⟩
  have hW₂ : W₂.1 ≤ (projectiveModel f).basicOpen (infiniteCoord f (1 - C c * Polynomial.X)) ⊓
      (projectiveModel f).basicOpen (infiniteCoord f (1 - C c₀ * Polynomial.X)) := by
    change (projectiveModel f).basicOpen _ ≤ _
    rw [Scheme.basicOpen_mul]
  have hW₂a := hW₂.trans inf_le_left
  have hW₂b := hW₂.trans inf_le_right
  have hW₂inf : W₂.1 ≤ chartOpenAtInfinity f := hW₂a.trans ((projectiveModel f).basicOpen_le _)
  have hcov : ∀ x, x ∈ chartOpen f ∨ x ∈ W₂.1 := by
    intro x
    by_cases hx : x ∈ chartOpen f
    · exact Or.inl hx
    · refine Or.inr ?_
      change x ∈ (projectiveModel f).basicOpen _
      rw [Scheme.basicOpen_mul]
      exact ⟨mem_basicOpen_infiniteCoord_of_not_mem (by simp) hx,
        mem_basicOpen_infiniteCoord_of_not_mem (by simp) hx⟩
  have : Nonempty (chartAffineOpen f).1 := nonempty_chartOpen f
  have hne : ∀ d : k, 𝐆 (finiteCoord f (Polynomial.X - C d)) ≠ 0 := fun d =>
    germ_finiteCoord_ne_zero (X_sub_C_ne_zero d)
  exact effectiveCartierWeilDivisor_two_apply_of_two_local_ratios (branchIdeal f hc)
    (branchIdeal f hc₀) hPc hPc₀ (chartAffineOpen f) W₂ hcov
    (branchIdeal_mul_self_ideal_chartOpen_coord hf hc)
    (branchIdeal_mul_self_ideal_eq_span_of_le_coord hc W₂ hW₂a)
    (branchIdeal_mul_self_ideal_chartOpen_coord hf hc₀)
    (branchIdeal_mul_self_ideal_eq_span_of_le_coord hc₀ W₂ hW₂b)
    (finiteCoord_mem_nonZeroDivisors hf hc)
    (isUnit_res_of_le_basicOpen _ hW₂a).mem_nonZeroDivisors
    (fun x h₁ h₂ => by
      have hxinf : x ∈ chartOpenAtInfinity f := hW₂inf h₂
      have hO : x ∈ chartOpen f ⊓ chartOpenAtInfinity f := ⟨h₁, hxinf⟩
      have e1 := congrArg ((projectiveModel f).presheaf.germ _ x hO)
        (overlap_coord_identity (f := f) c)
      have e2 := congrArg ((projectiveModel f).presheaf.germ _ x hO)
        (overlap_coord_identity (f := f) c₀)
      simp only [map_mul, TopCat.Presheaf.germ_res_apply] at e1 e2
      simp only [TopCat.Presheaf.germ_res_apply]
      rw [← e1, ← e2]
      ring)
    (Units.mk0 (𝐆 (finiteCoord f (Polynomial.X - C c₀)) /
      𝐆 (finiteCoord f (Polynomial.X - C c))) (div_ne_zero (hne c₀) (hne c)))
    (by
      simp only [Units.val_mk0]
      exact div_mul_cancel₀ _ (hne c)) Z

variable (h0 : (reflect (2 * genus f + 2) f).eval 0 = 0)

/-- The Weil divisor `[P_∞]` of the branch point at infinity (odd degree). -/
@[expose] noncomputable def infinityWeil (hf : f.Separable) (hdeg : 0 < f.natDegree) :
    WeilDivisor (projectiveModel f) :=
  effectiveCartierWeilDivisor (infinityIdeal f h0)
    (isEffectiveCartierDivisor_infinityIdeal h0 hf hdeg)

/-- **`2 P_∞ = 2 P_c + div (1/(x - c))`** (odd degree), coefficientwise. -/
theorem infinityWeil_two_eq (hf : f.Separable) (hdeg : 0 < f.natDegree) {c : k}
    (hc : f.eval c = 0) (Z : PrimeDivisor (projectiveModel f)) :
    (infinityWeil h0 hf hdeg).1 Z + (infinityWeil h0 hf hdeg).1 Z =
      ((branchWeil hf hc).1 Z + (branchWeil hf hc).1 Z) +
        (projectiveModel f).ord
          (𝐆 (finiteCoord f 1) / 𝐆 (finiteCoord f (Polynomial.X - C c))) Z.genericPoint := by
  have hPc := isEffectiveCartierDivisor_branchIdeal hf hc
  have hP := isEffectiveCartierDivisor_infinityIdeal h0 hf hdeg
  have hUinf := isAffineOpen_opensRange (affineChartAtInfinity f)
  let W₂ : (projectiveModel f).affineOpens :=
    ⟨(projectiveModel f).basicOpen (infiniteCoord f (1 - C c * Polynomial.X)),
      hUinf.basicOpen _⟩
  have hV : W₂.1 ≤ (projectiveModel f).basicOpen (infiniteCoord f (1 - C c * Polynomial.X)) :=
    le_rfl
  have hWinf : W₂.1 ≤ chartOpenAtInfinity f := (projectiveModel f).basicOpen_le _
  have hcov : ∀ x, x ∈ chartOpen f ∨ x ∈ W₂.1 := by
    intro x
    by_cases hx : x ∈ chartOpen f
    · exact Or.inl hx
    · exact Or.inr (mem_basicOpen_infiniteCoord_of_not_mem (by simp) hx)
  have : Nonempty (chartAffineOpen f).1 := nonempty_chartOpen f
  have hσ₂ : (infinityIdeal f h0 * infinityIdeal f h0).ideal W₂ = Ideal.span
      {(projectiveModel f).presheaf.map (homOfLE (Scheme.basicOpen_le _ _)).op
        (infiniteCoord f Polynomial.X)} :=
    ideal_affineBasicOpen_eq_span _ (chartAffineOpenAtInfinity f)
      (infinityIdeal_mul_self_ideal_chartOpenAtInfinity h0 hf hdeg) _
  have hne := germ_finiteCoord_ne_zero (f := f) (X_sub_C_ne_zero c)
  exact effectiveCartierWeilDivisor_two_apply_of_two_local_ratios (branchIdeal f hc)
    (infinityIdeal f h0) hPc hP (chartAffineOpen f) W₂ hcov
    (branchIdeal_mul_self_ideal_chartOpen_coord hf hc)
    (branchIdeal_mul_self_ideal_eq_span_of_le_coord hc W₂ hV)
    (infinityIdeal_mul_self_ideal_chartOpen h0) hσ₂
    (finiteCoord_mem_nonZeroDivisors hf hc)
    (isUnit_res_of_le_basicOpen _ hV).mem_nonZeroDivisors
    (fun x h₁ h₂ => by
      have hxinf : x ∈ chartOpenAtInfinity f := hWinf h₂
      have hO : x ∈ chartOpen f ⊓ chartOpenAtInfinity f := ⟨h₁, hxinf⟩
      have e := congrArg ((projectiveModel f).presheaf.germ _ x hO)
        (overlap_coord_identity (f := f) c)
      simp only [map_mul, TopCat.Presheaf.germ_res_apply] at e
      simp only [map_one, mul_one, TopCat.Presheaf.germ_res_apply]
      exact e)
    (Units.mk0 (𝐆 (finiteCoord f 1) / 𝐆 (finiteCoord f (Polynomial.X - C c)))
      (div_ne_zero (by rw [finiteCoord_one, map_one]; exact one_ne_zero) hne))
    (by
      simp only [Units.val_mk0, finiteCoord_one, map_one]
      exact div_mul_cancel₀ _ hne) Z

end WeilDivisors

/-! ### The core argument -/

section Core

variable [IsIntegral (projectiveModel f)]

local notation "𝐆" => Scheme.germToFunctionField (projectiveModel f) (chartOpen f)

/-- **Principal sums of branch points give polynomial square relations.** Let `B` be an effective
Cartier divisor with `2 [B] = 2 [P_c] + div (b(x)/(x - c))` for every root `c`. If
`∑_{c ∈ S} [P_c] = |S| · [B]` in `Pic X`, then for some `g, N ∈ k[x]`, `N ≠ 0`, and `l ∈ kˣ`:
`g^2 ∏_{c ∈ S} (x - c) = N^2 l b^{|S|}` or `g^2 f ∏_{c ∈ S} (x - c) = N^2 l b^{|S|}`. -/
theorem exists_poly_relation (h2 : (2 : k) ≠ 0) (hf : f.Separable) (hdeg : 0 < f.natDegree)
    {B : (projectiveModel f).IdealSheafData}
    (hB : Stacks.Divisors.IsEffectiveCartierDivisor B) (b : k[X]) (hb : b ≠ 0)
    (hrel : ∀ (c : BranchRoot f) (Z : PrimeDivisor (projectiveModel f)),
      (effectiveCartierWeilDivisor B hB).1 Z + (effectiveCartierWeilDivisor B hB).1 Z =
        ((branchWeil hf (BranchRoot.eval_eq_zero c)).1 Z +
            (branchWeil hf (BranchRoot.eval_eq_zero c)).1 Z) +
          (projectiveModel f).ord
            (𝐆 (finiteCoord f b) / 𝐆 (finiteCoord f (Polynomial.X - C c.1))) Z.genericPoint)
    (S : Finset (BranchRoot f))
    (hS : ∑ c ∈ S, branchClass hf c = S.card • @Stacks.Divisors.picardClass _ _ hB) :
    ∃ g N : k[X], ∃ l : k, l ≠ 0 ∧ N ≠ 0 ∧
      (g ^ 2 * ∏ c ∈ S, (Polynomial.X - C c.1) = N ^ 2 * (C l * b ^ S.card) ∨
        g ^ 2 * (f * ∏ c ∈ S, (Polynomial.X - C c.1)) = N ^ 2 * (C l * b ^ S.card)) := by
  classical
  have := isNormal_projectiveModel h2 hf hdeg
  have hPi : ∀ c : BranchRoot f, Stacks.Divisors.IsEffectiveCartierDivisor
      (branchIdeal f (BranchRoot.eval_eq_zero c)) := fun c =>
    isEffectiveCartierDivisor_branchIdeal hf (BranchRoot.eval_eq_zero c)
  have hBi : ∀ _c : BranchRoot f, Stacks.Divisors.IsEffectiveCartierDivisor B := fun _ => hB
  have hD := isEffectiveCartierDivisor_prod S hPi
  have hD' := isEffectiveCartierDivisor_prod S hBi
  -- the classes of `∏_S P_c` and `∏_S B` agree
  have hclass : Stacks.Divisors.picardClass (∏ c ∈ S, branchIdeal f (BranchRoot.eval_eq_zero c)) =
      Stacks.Divisors.picardClass (∏ _c ∈ S, B) := by
    rw [picardClass_prod S (fun c => branchIdeal f (BranchRoot.eval_eq_zero c)),
      picardClass_prod S (fun _ => B), Finset.sum_const]
    exact hS
  obtain ⟨φ, hφ⟩ := (linearlyEquivalent_iff_exists_rationalFunctionWeilDivisor _ _ hD hD').mp
    ((linearlyEquivalent_iff_picardClass_eq' _ _).mpr hclass)
  have hφZ : ∀ Z : PrimeDivisor (projectiveModel f),
      S.card * (effectiveCartierWeilDivisor B hB).1 Z =
        ∑ c ∈ S, (branchWeil hf (BranchRoot.eval_eq_zero c)).1 Z +
          (projectiveModel f).ord (φ : (projectiveModel f).functionField) Z.genericPoint := by
    intro Z
    have h : (effectiveCartierWeilDivisor (∏ _c ∈ S, B) hD').1 Z =
        (effectiveCartierWeilDivisor (∏ c ∈ S, branchIdeal f (BranchRoot.eval_eq_zero c)) hD).1 Z +
          (projectiveModel f).ord (φ : (projectiveModel f).functionField) Z.genericPoint :=
      congrFun (congrArg Subtype.val hφ) Z
    rw [effectiveCartierWeilDivisor_prod_apply S (fun c => branchIdeal f _) Z] at h
    rw [effectiveCartierWeilDivisor_prod_apply S (fun _ => B) Z, Finset.sum_const,
      nsmul_eq_mul] at h
    exact h
  -- the rational functions `ρ_c`
  have hρ : ∀ c : BranchRoot f,
      𝐆 (finiteCoord f b) / 𝐆 (finiteCoord f (Polynomial.X - C c.1)) ≠ 0 :=
    fun c => div_ne_zero (germ_finiteCoord_ne_zero hb)
      (germ_finiteCoord_ne_zero (X_sub_C_ne_zero c.1))
  have hφ0 : (φ : (projectiveModel f).functionField) ≠ 0 := φ.ne_zero
  have hProd : ∏ c ∈ S, 𝐆 (finiteCoord f b) / 𝐆 (finiteCoord f (Polynomial.X - C c.1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun c _ => hρ c
  have hψ0 : (φ : (projectiveModel f).functionField) ^ 2 /
      ∏ c ∈ S, 𝐆 (finiteCoord f b) / 𝐆 (finiteCoord f (Polynomial.X - C c.1)) ≠ 0 :=
    div_ne_zero (pow_ne_zero 2 hφ0) hProd
  have hψ : rationalFunctionWeilDivisor (projectiveModel f) (Units.mk0 _ hψ0) = 0 := by
    refine Subtype.ext (funext fun Z => ?_)
    change (projectiveModel f).ord _ Z.genericPoint = 0
    rw [Units.val_mk0, ord_div_functionField (pow_ne_zero 2 hφ0) hProd, ord_pow_functionField hφ0,
      ord_prod_functionField S _ (fun c _ => hρ c)]
    have hsum : ∑ c ∈ S, (projectiveModel f).ord
        (𝐆 (finiteCoord f b) / 𝐆 (finiteCoord f (Polynomial.X - C c.1))) Z.genericPoint =
        ∑ c ∈ S, (2 * (effectiveCartierWeilDivisor B hB).1 Z -
          2 * (branchWeil hf (BranchRoot.eval_eq_zero c)).1 Z) :=
      Finset.sum_congr rfl fun c _ => by have := hrel c Z; omega
    rw [hsum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    have := hφZ Z
    push_cast
    linarith
  obtain ⟨l, hl⟩ := (rationalFunctionWeilDivisor_eq_zero_iff_projectiveModel h2 hf hdeg _).mp hψ
  rw [germ_top_globalStructureMap, Units.val_mk0] at hl
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [C_0, finiteCoord_zero, map_zero] at hl
    exact hψ0 hl.symm
  rw [Finset.prod_div_distrib, Finset.prod_const] at hl
  -- clear denominators
  have : IsFractionRing Γ(projectiveModel f, chartOpen f) (projectiveModel f).functionField :=
    functionField_isFractionRing_of_isAffineOpen (projectiveModel f) (chartOpen f)
      (isAffineOpen_opensRange (affineChart f))
  obtain ⟨⟨a, b'⟩, hab⟩ :=
    IsLocalization.surj (nonZeroDivisors Γ(projectiveModel f, chartOpen f))
      (φ : (projectiveModel f).functionField)
  have hab' : (φ : (projectiveModel f).functionField) *
      𝐆 (b' : Γ(projectiveModel f, chartOpen f)) = 𝐆 a := hab
  have hb'0 : (b' : Γ(projectiveModel f, chartOpen f)) ≠ 0 := nonZeroDivisors.coe_ne_zero b'
  have hbn : 𝐆 (finiteCoord f b) ^ S.card ≠ 0 := pow_ne_zero _ (germ_finiteCoord_ne_zero hb)
  have e3 : (φ : (projectiveModel f).functionField) ^ 2 *
      ∏ c ∈ S, 𝐆 (finiteCoord f (Polynomial.X - C c.1)) =
      𝐆 (finiteCoord f (C l)) * 𝐆 (finiteCoord f b) ^ S.card := by
    rw [hl, div_div_eq_mul_div, div_mul_cancel₀ _ hbn]
  have e4 : 𝐆 (a ^ 2 * ∏ c ∈ S, finiteCoord f (Polynomial.X - C c.1)) =
      𝐆 ((b' : Γ(projectiveModel f, chartOpen f)) ^ 2 *
        (finiteCoord f (C l) * finiteCoord f b ^ S.card)) := by
    simp only [map_mul, map_pow, map_prod]
    rw [← hab']
    linear_combination 𝐆 (b' : Γ(projectiveModel f, chartOpen f)) ^ 2 * e3
  have e5 := congrArg (sectionsEquivFinite f)
    ((projectiveModel f).germToFunctionField_injective _ e4)
  simp only [map_mul, map_pow, map_prod, sectionsEquivFinite_finiteCoord] at e5
  have e6 : sectionsEquivFinite f a ^ 2 *
        AdjoinRoot.of (Polynomial.X ^ 2 - C f) (∏ c ∈ S, (Polynomial.X - C c.1)) =
      sectionsEquivFinite f b' ^ 2 * AdjoinRoot.of (Polynomial.X ^ 2 - C f) (C l * b ^ S.card) := by
    simp only [map_mul, map_pow, map_prod]
    exact e5
  have hβ : sectionsEquivFinite f b' ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (sectionsEquivFinite f).injective]
    exact hb'0
  obtain ⟨g, N, hN, hgN⟩ :=
    exists_sq_mul_eq_of_sq_mul_eq f h2 hf hdeg hβ (prod_X_sub_C_branch_ne_zero S) e6
  exact ⟨g, N, l, hl0, hN, hgN⟩

end Core

/-! ### The kernels -/

section TorsionKernel

variable {A : Type*} [AddCommGroup A] {ι : Type*}

/-- `torsionHomOfSq e he v = ∑_{v_i = 1} e_i`. -/
theorem torsionHomOfSq_eq_sum_filter [Fintype ι] (e : ι → A) (he : ∀ i, 2 • e i = 0)
    (v : ι → ZMod 2) :
    torsionHomOfSq e he v = ∑ i ∈ Finset.univ.filter (fun i => v i = 1), e i := by
  rw [torsionHomOfSq_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have h01' : ¬ ((0 : ZMod 2) = 1) := by decide
  rcases h01 (v i) with h | h
  · rw [h, map_zero, ite_eq_right h01']
  · rw [h, zmodTwoHom_one, ite_eq_left rfl]

theorem sum_sub_eq_zero_iff (s : Finset ι) (n : ι → A) (b : A) :
    ∑ i ∈ s, (n i - b) = 0 ↔ ∑ i ∈ s, n i = s.card • b := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, sub_eq_zero]

end TorsionKernel

theorem zmod_two_eq_zero_of_ne_one : ∀ a : ZMod 2, a ≠ 1 → a = 0 := by decide

theorem zmod_two_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

theorem branchDiffClass_self (hf : f.Separable) (c₀ : BranchRoot f) :
    branchDiffClass hf c₀ c₀ = 0 :=
  sub_self _

/-- **The kernel of `δ_c ↦ [P_c - P_{c₀}]` in even degree** (`f` separable and split over `k`,
`2 ≠ 0` in `k`): `∑_c v_c [P_c - P_{c₀}] = 0` in `Pic X` iff `v` is constant on the roots
`c ≠ c₀`. Equivalently the kernel is spanned by `δ_{c₀}` and the all-ones vector. -/
theorem branchTorsionHom_eq_zero_iff (h2 : (2 : k) ≠ 0) (hf : f.Separable)
    (hsplit : f.roots.card = f.natDegree) (heven : Even f.natDegree) (c₀ : BranchRoot f)
    (v : BranchRoot f → ZMod 2) :
    branchTorsionHom h2 hf c₀ v = 0 ↔ ∀ c c' : BranchRoot f, c ≠ c₀ → c' ≠ c₀ → v c = v c' := by
  classical
  have hdeg : 0 < f.natDegree := natDegree_pos_of_eval_eq_zero hf (BranchRoot.eval_eq_zero c₀)
  have := isIntegral_projectiveModel hf hdeg
  rw [branchTorsionHom, torsionHomOfSq_eq_sum_filter]
  constructor
  · intro h
    have h' := (sum_sub_eq_zero_iff _ (fun c => branchClass hf c) (branchClass hf c₀)).mp h
    obtain ⟨g, N, l, hl, hN, hgN⟩ := exists_poly_relation h2 hf hdeg
      (isEffectiveCartierDivisor_branchIdeal hf (BranchRoot.eval_eq_zero c₀))
      (Polynomial.X - C c₀.1) (X_sub_C_ne_zero _)
      (fun c Z => branchWeil_two_eq hf (BranchRoot.eval_eq_zero c) (BranchRoot.eval_eq_zero c₀) Z)
      _ h'
    have hQ : C l * (Polynomial.X - C c₀.1) ^
        (Finset.univ.filter (fun c => v c = 1)).card ≠ 0 :=
      mul_ne_zero (C_ne_zero.mpr hl) (pow_ne_zero _ (X_sub_C_ne_zero _))
    have hQc : ∀ c : BranchRoot f, c ≠ c₀ →
        (C l * (Polynomial.X - C c₀.1) ^
          (Finset.univ.filter (fun c => v c = 1)).card).roots.count c.1 = 0 := by
      intro c hc
      have hne : c.1 ≠ c₀.1 := fun h => hc (Subtype.ext h)
      rw [roots_C_mul _ hl, roots_pow, roots_X_sub_C, Multiset.count_nsmul,
        Multiset.count_singleton, ite_eq_right hne, mul_zero]
    rcases hgN with hgN | hgN
    · have hS : ∀ c : BranchRoot f, c ≠ c₀ → v c = 0 := by
        intro c hc
        refine zmod_two_eq_zero_of_ne_one _ fun hv => ?_
        have hmem : c ∈ Finset.univ.filter (fun c => v c = 1) := by simp [hv]
        have hpar := count_roots_mod_two_eq hN hQ hgN c.1
        rw [count_roots_prod_branch, hQc c hc, ite_eq_left hmem] at hpar
        exact absurd hpar (by decide)
      intro c c' hc hc'
      rw [hS c hc, hS c' hc']
    · have hS : ∀ c : BranchRoot f, c ≠ c₀ → v c = 1 := by
        intro c hc
        by_contra hv
        have hmem : c ∉ Finset.univ.filter (fun c => v c = 1) := by simp [hv]
        have hpar := count_roots_mod_two_eq hN hQ hgN c.1
        rw [roots_mul (mul_ne_zero hf.ne_zero (prod_X_sub_C_branch_ne_zero _)),
          Multiset.count_add, count_roots_prod_branch, count_roots_branch_eq_one hf, hQc c hc,
          ite_eq_right hmem] at hpar
        exact absurd hpar (by decide)
      intro c c' hc hc'
      rw [hS c hc, hS c' hc']
  · intro hv
    have hall : ∑ c : BranchRoot f, branchDiffClass hf c₀ c = 0 := by
      have := branchTorsionHom_one_of_even h2 hf hsplit heven c₀
      rwa [branchTorsionHom, torsionHomOfSq_one] at this
    by_cases hex : ∃ c : BranchRoot f, c ≠ c₀ ∧ v c = 1
    · obtain ⟨c₁, hc₁, hv₁⟩ := hex
      refine (Finset.sum_subset (Finset.subset_univ _) ?_).trans hall
      intro c _ hc
      by_cases hcc : c = c₀
      · rw [hcc, branchDiffClass_self]
      · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ c, (hv c c₁ hcc hc₁).trans hv₁⟩) hc
    · refine Finset.sum_eq_zero fun c hc => ?_
      by_cases hcc : c = c₀
      · rw [hcc, branchDiffClass_self]
      · exact (hex ⟨c, hcc, (Finset.mem_filter.mp hc).2⟩).elim

variable (h0 : (reflect (2 * genus f + 2) f).eval 0 = 0)

/-- **The kernel of `δ_c ↦ [P_c - P_∞]` in odd degree** (`f` separable and split over `k`,
`2 ≠ 0` in `k`): `∑_c v_c [P_c - P_∞] = 0` in `Pic X` iff `v` is `0` or the all-ones vector. -/
theorem branchTorsionHomInf_eq_zero_iff (h2 : (2 : k) ≠ 0) (hf : f.Separable)
    (hdeg : 0 < f.natDegree) (hsplit : f.roots.card = f.natDegree) (hodd : Odd f.natDegree)
    (v : BranchRoot f → ZMod 2) :
    branchTorsionHomInf h0 h2 hf hdeg v = 0 ↔ ∀ c c' : BranchRoot f, v c = v c' := by
  classical
  have := isIntegral_projectiveModel hf hdeg
  rw [branchTorsionHomInf, torsionHomOfSq_eq_sum_filter]
  constructor
  · intro h
    have h' := (sum_sub_eq_zero_iff _ (fun c => branchClass hf c) (infinityClass h0 hf hdeg)).mp h
    obtain ⟨g, N, l, hl, hN, hgN⟩ := exists_poly_relation h2 hf hdeg
      (isEffectiveCartierDivisor_infinityIdeal h0 hf hdeg) 1 one_ne_zero
      (fun c Z => infinityWeil_two_eq h0 hf hdeg (BranchRoot.eval_eq_zero c) Z) _ h'
    have hQ : C l * (1 : k[X]) ^ (Finset.univ.filter (fun c => v c = 1)).card ≠ 0 := by
      rw [one_pow, mul_one]
      exact C_ne_zero.mpr hl
    have hQc : ∀ c : BranchRoot f,
        (C l * (1 : k[X]) ^ (Finset.univ.filter (fun c => v c = 1)).card).roots.count c.1 =
          0 := by
      intro c
      rw [one_pow, mul_one, roots_C, Multiset.count_zero]
    rcases hgN with hgN | hgN
    · have hS : ∀ c : BranchRoot f, v c = 0 := by
        intro c
        refine zmod_two_eq_zero_of_ne_one _ fun hv => ?_
        have hmem : c ∈ Finset.univ.filter (fun c => v c = 1) := by simp [hv]
        have hpar := count_roots_mod_two_eq hN hQ hgN c.1
        rw [count_roots_prod_branch, hQc c, ite_eq_left hmem] at hpar
        exact absurd hpar (by decide)
      intro c c'
      rw [hS c, hS c']
    · have hS : ∀ c : BranchRoot f, v c = 1 := by
        intro c
        by_contra hv
        have hmem : c ∉ Finset.univ.filter (fun c => v c = 1) := by simp [hv]
        have hpar := count_roots_mod_two_eq hN hQ hgN c.1
        rw [roots_mul (mul_ne_zero hf.ne_zero (prod_X_sub_C_branch_ne_zero _)),
          Multiset.count_add, count_roots_prod_branch, count_roots_branch_eq_one hf, hQc c,
          ite_eq_right hmem] at hpar
        exact absurd hpar (by decide)
      intro c c'
      rw [hS c, hS c']
  · intro hv
    have hall : ∑ c : BranchRoot f, branchDiffClassInf h0 hf hdeg c = 0 := by
      have := branchTorsionHomInf_one h0 h2 hf hdeg hsplit hodd
      rwa [branchTorsionHomInf, torsionHomOfSq_one] at this
    by_cases hex : ∃ c : BranchRoot f, v c = 1
    · obtain ⟨c₁, hv₁⟩ := hex
      refine (Finset.sum_subset (Finset.subset_univ _) ?_).trans hall
      intro c _ hc
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ c, (hv c c₁).trans hv₁⟩) hc
    · exact Finset.sum_eq_zero fun c hc => (hex ⟨c, (Finset.mem_filter.mp hc).2⟩).elim

/-- The odd-degree kernel in the form `{0, (1, …, 1)}`. -/
theorem branchTorsionHomInf_eq_zero_iff_eq_zero_or_eq_one (h2 : (2 : k) ≠ 0)
    (hf : f.Separable) (hdeg : 0 < f.natDegree) (hsplit : f.roots.card = f.natDegree)
    (hodd : Odd f.natDegree) (v : BranchRoot f → ZMod 2) :
    branchTorsionHomInf h0 h2 hf hdeg v = 0 ↔ v = 0 ∨ v = 1 := by
  rw [branchTorsionHomInf_eq_zero_iff h0 h2 hf hdeg hsplit hodd]
  constructor
  · intro hv
    obtain ⟨c₁⟩ : Nonempty (BranchRoot f) :=
      Fintype.card_pos_iff.mp (by rw [card_branchRoot hf hsplit]; exact hdeg)
    rcases zmod_two_cases (v c₁) with h | h
    · left
      funext c
      rw [Pi.zero_apply, hv c c₁, h]
    · right
      funext c
      rw [Pi.one_apply, hv c c₁, h]
  · rintro (rfl | rfl) <;> intro c c' <;> rfl

/-- **The image of `branchTorsionHom` has order `2^{2g}`** (even degree `2g + 2`, `f` separable
and split over `k`, `2 ≠ 0`): `(ℤ/2)^{2g+2}` modulo the kernel `⟨δ_{c₀}, (1, …, 1)⟩` of order
`4`. -/
theorem card_range_branchTorsionHom (h2 : (2 : k) ≠ 0) (hf : f.Separable)
    (hsplit : f.roots.card = f.natDegree) (heven : Even f.natDegree) (c₀ : BranchRoot f) :
    Nat.card (branchTorsionHom h2 hf c₀).range = 2 ^ (2 * genus f) := by
  have hpos : 0 < f.natDegree := by
    rw [← card_branchRoot hf hsplit]
    exact Fintype.card_pos_iff.mpr ⟨c₀⟩
  have hN : f.natDegree = 2 * genus f + 2 := by
    obtain ⟨m, hm⟩ := heven
    unfold genus
    omega
  have hcard : Nat.card (BranchRoot f) = 2 * genus f + 2 := by
    rw [Nat.card_eq_fintype_card, card_branchRoot hf hsplit, hN]
  obtain ⟨c₁, hc₁⟩ := Fintype.exists_ne_of_one_lt_card
    (by rw [card_branchRoot hf hsplit]; omega) c₀
  classical
  have hmem : ∀ v : BranchRoot f → ZMod 2, v ∈ (branchTorsionHom h2 hf c₀).ker ↔
      ∀ c c' : BranchRoot f, c ≠ c₀ → c' ≠ c₀ → v c = v c' := fun v =>
    AddMonoidHom.mem_ker.trans (branchTorsionHom_eq_zero_iff h2 hf hsplit heven c₀ v)
  let e : (branchTorsionHom h2 hf c₀).ker ≃ ZMod 2 × ZMod 2 :=
    { toFun := fun v => (v.1 c₀, v.1 c₁)
      invFun := fun a => ⟨fun c => if c = c₀ then a.1 else a.2,
        (hmem _).mpr fun c c' hc hc' => by rw [ite_eq_right hc, ite_eq_right hc']⟩
      left_inv := fun v => by
        refine Subtype.ext (funext fun c => ?_)
        change (if c = c₀ then v.1 c₀ else v.1 c₁) = v.1 c
        by_cases hc : c = c₀
        · rw [ite_eq_left hc, hc]
        · rw [ite_eq_right hc]
          exact (hmem v.1).mp v.2 c₁ c hc₁ hc
      right_inv := fun a => by
        change ((if c₀ = c₀ then a.1 else a.2), (if c₁ = c₀ then a.1 else a.2)) = a
        rw [ite_eq_left rfl, ite_eq_right hc₁] }
  have htot := (branchTorsionHom h2 hf c₀).ker.card_eq_card_quotient_mul_card_addSubgroup
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (branchTorsionHom h2 hf c₀)).toEquiv,
    mul_comm, Nat.card_congr e, Nat.card_prod, Nat.card_zmod, Nat.card_fun, Nat.card_zmod,
    hcard] at htot
  have h4 : (2 : ℕ) ^ (2 * genus f + 2) = 4 * 2 ^ (2 * genus f) := by ring
  rw [h4, show (2 : ℕ) * 2 = 4 from rfl] at htot
  exact (Nat.eq_of_mul_eq_mul_left (by norm_num) htot).symm

/-- **The image of `branchTorsionHomInf` has order `2^{2g}`** (odd degree `2g + 1`, `f`
separable and split over `k`, `2 ≠ 0`): `(ℤ/2)^{2g+1}` modulo the kernel `{0, (1, …, 1)}`. -/
theorem card_range_branchTorsionHomInf (h2 : (2 : k) ≠ 0) (hf : f.Separable)
    (hdeg : 0 < f.natDegree)
    (hsplit : f.roots.card = f.natDegree) (hodd : Odd f.natDegree) :
    Nat.card (branchTorsionHomInf h0 h2 hf hdeg).range = 2 ^ (2 * genus f) := by
  have hN : f.natDegree = 2 * genus f + 1 := by
    obtain ⟨m, hm⟩ := hodd
    unfold genus
    omega
  have hcard : Nat.card (BranchRoot f) = 2 * genus f + 1 := by
    rw [Nat.card_eq_fintype_card, card_branchRoot hf hsplit, hN]
  obtain ⟨c₁⟩ : Nonempty (BranchRoot f) :=
    Fintype.card_pos_iff.mp (by rw [card_branchRoot hf hsplit]; omega)
  classical
  have hmem : ∀ v : BranchRoot f → ZMod 2, v ∈ (branchTorsionHomInf h0 h2 hf hdeg).ker ↔
      ∀ c c' : BranchRoot f, v c = v c' := fun v =>
    AddMonoidHom.mem_ker.trans (branchTorsionHomInf_eq_zero_iff h0 h2 hf hdeg hsplit hodd v)
  let e : (branchTorsionHomInf h0 h2 hf hdeg).ker ≃ ZMod 2 :=
    { toFun := fun v => v.1 c₁
      invFun := fun t => ⟨fun _ => t, (hmem _).mpr fun _ _ => rfl⟩
      left_inv := fun v => Subtype.ext (funext fun c => (hmem v.1).mp v.2 c₁ c)
      right_inv := fun _ => rfl }
  have htot := (branchTorsionHomInf h0 h2 hf hdeg).ker.card_eq_card_quotient_mul_card_addSubgroup
  rw [Nat.card_congr
      (QuotientAddGroup.quotientKerEquivRange (branchTorsionHomInf h0 h2 hf hdeg)).toEquiv,
    mul_comm, Nat.card_congr e, Nat.card_zmod, Nat.card_fun, Nat.card_zmod,
    hcard] at htot
  have h4 : (2 : ℕ) ^ (2 * genus f + 1) = 2 * 2 ^ (2 * genus f) := by ring
  rw [h4] at htot
  exact (Nat.eq_of_mul_eq_mul_left (by norm_num) htot).symm

end Hyperelliptic

end ArithmeticOfJacobiPolynomials
