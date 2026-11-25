/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.Divisors.LinearEquivalence
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk

/-!
# Weil divisors, classes and linear equivalence of effective Cartier divisors from local data

Stacks defines linear equivalence of effective Cartier divisors `D ∼ D'` as `𝒪_X(D) ≅ 𝒪_X(D')`
(`Stacks.Divisors.LinearlyEquivalent`, Tag 0CCT) and proves, on a normal Noetherian integral
scheme, that it is the existence of a rational function `φ` with `[D'] = [D] + div φ`
(`ArithmeticOfJacobiPolynomials.Divisors.linearlyEquivalent_iff_exists_ord`). This file records the
additivity of
the Weil divisor `[D]` (`AlgebraicGeometry.effectiveCartierWeilDivisor`, Tag 02AR (5)) and of the
Picard class (`Stacks.Divisors.picardClass`) over finite products of effective Cartier divisors,
and packages the criterion above for divisors given by explicit local equations.

## Main results

* `ArithmeticOfJacobiPolynomials.Divisors.linearlyEquivalent_iff_picardClass_eq'`: `D ∼ D'` iff `D`
and `D'` have
  the same class in `Stacks.Picard.ofScheme X` (`Stacks.Divisors.picardClass`).
* `ArithmeticOfJacobiPolynomials.Divisors.effectiveCartierWeilDivisor_mul`, `_top`, `_prod_apply`:
  `[D D'] = [D] + [D']`, `[⊤] = 0`, and the coefficients of `[∏ D_i]` are the sums of those of
  the `[D_i]`;
  `ArithmeticOfJacobiPolynomials.Divisors.isEffectiveCartierDivisor_prod`, `picardClass_prod`: the
  same for the
  class.
* `ArithmeticOfJacobiPolynomials.Divisors.effectiveCartierWeilDivisor_eq_add_of_local_ratios`: if
affine opens
  `W i` cover `X`, `D = (τ i)` and `D' = (σ i)` on `W i` for non-zero-divisors `τ i`, `σ i` with
  `τ i σ j = τ j σ i` at every point of `W i ∩ W j`, and `φ σ`-ratio `σ i₀ / τ i₀`, then
  `[D'] = [D] + div φ`.
* `ArithmeticOfJacobiPolynomials.Divisors.linearlyEquivalent_of_local_ratios`: in that situation `D
∼ D'` (on a
  normal scheme), and the two-open versions `..._of_two_local_ratios`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

namespace Divisors

open AlgebraicGeometry CategoryTheory

universe u

variable {X : Scheme.{u}}

/-- **Linear equivalence is equality of Picard classes** (`Stacks.Divisors.picardClass`, in the
Picard group of `Stacks.Picard.ofScheme`). -/
theorem linearlyEquivalent_iff_picardClass_eq' (D D' : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] [Stacks.Divisors.IsEffectiveCartierDivisor D'] :
    Stacks.Divisors.LinearlyEquivalent D D' ↔
      Stacks.Divisors.picardClass D = Stacks.Divisors.picardClass D' := by
  rw [Stacks.Divisors.linearlyEquivalent_iff_picardClass_eq]
  exact Iff.rfl

/-! ### Finite products of effective Cartier divisors -/

section Products

/-- **A finite product of effective Cartier divisors is an effective Cartier divisor.** -/
theorem isEffectiveCartierDivisor_prod {ι : Type*} (s : Finset ι) {I : ι → X.IdealSheafData}
    (hI : ∀ i, Stacks.Divisors.IsEffectiveCartierDivisor (I i)) :
    Stacks.Divisors.IsEffectiveCartierDivisor (∏ i ∈ s, I i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Scheme.IdealSheafData.one_eq_top]
    infer_instance
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have := hI a
    have := ih
    infer_instance

/-- **Additivity of the Picard class over finite products.** -/
theorem picardClass_prod {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData)
    [hI : ∀ i, Stacks.Divisors.IsEffectiveCartierDivisor (I i)] :
    haveI := isEffectiveCartierDivisor_prod s hI
    Stacks.Divisors.picardClass (∏ i ∈ s, I i) = ∑ i ∈ s, Stacks.Divisors.picardClass (I i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h1 : (∏ i ∈ (∅ : Finset ι), I i) = ⊤ :=
      Finset.prod_empty.trans Scheme.IdealSheafData.one_eq_top
    have := isEffectiveCartierDivisor_prod (∅ : Finset ι) hI
    rw [Stacks.Divisors.picardClass_congr h1, Stacks.Divisors.picardClass_top, Finset.sum_empty]
  | insert a s ha ih =>
    have := isEffectiveCartierDivisor_prod s hI
    have := isEffectiveCartierDivisor_prod (insert a s) hI
    rw [Stacks.Divisors.picardClass_congr (Finset.prod_insert ha),
      Stacks.Divisors.picardClass_mul, ih, Finset.sum_insert ha]

variable [IsNoetherian X] [IsIntegral X]

/-- **Additivity of the Weil divisor**: `[D D'] = [D] + [D']` (Tag 02AR (5)). -/
theorem effectiveCartierWeilDivisor_mul (I J : X.IdealSheafData)
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)
    (hJ : Stacks.Divisors.IsEffectiveCartierDivisor J) :
    effectiveCartierWeilDivisor (I * J)
        (@Stacks.Divisors.IsEffectiveCartierDivisor.mul _ I J hI hJ) =
      effectiveCartierWeilDivisor I hI + effectiveCartierWeilDivisor J hJ := by
  refine Subtype.ext (funext fun Z => ?_)
  obtain ⟨a, ha, hareg⟩ := exists_stalk_eq_span_of_isEffectiveCartierDivisor hI Z.genericPoint
  obtain ⟨b, hb, hbreg⟩ := exists_stalk_eq_span_of_isEffectiveCartierDivisor hJ Z.genericPoint
  have hab : IdealSheafData.stalk (I * J) Z.genericPoint = Ideal.span {a * b} := by
    rw [IdealSheafData.stalk_mul, ha, hb, Ideal.span_singleton_mul_span_singleton]
  have hinj := IsFractionRing.injective (X.presheaf.stalk Z.genericPoint) X.functionField
  have ha0 : algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField a ≠ 0 := fun h =>
    nonZeroDivisors.ne_zero hareg (hinj (h.trans (map_zero _).symm))
  have hb0 : algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField b ≠ 0 := fun h =>
    nonZeroDivisors.ne_zero hbreg (hinj (h.trans (map_zero _).symm))
  change (effectiveCartierWeilDivisor (I * J) _).1 Z =
    (effectiveCartierWeilDivisor I hI).1 Z + (effectiveCartierWeilDivisor J hJ).1 Z
  rw [effectiveCartierWeilDivisor_apply_eq_ord _ _ Z hab,
    effectiveCartierWeilDivisor_apply_eq_ord I hI Z ha,
    effectiveCartierWeilDivisor_apply_eq_ord J hJ Z hb, map_mul, Scheme.ord_mul ha0 hb0]

/-- The empty divisor has Weil divisor `0`. -/
theorem effectiveCartierWeilDivisor_top :
    effectiveCartierWeilDivisor (⊤ : X.IdealSheafData) inferInstance = 0 := by
  have h := effectiveCartierWeilDivisor_mul (⊤ : X.IdealSheafData) ⊤ inferInstance inferInstance
  have htop : ((⊤ : X.IdealSheafData) * ⊤) = ⊤ := by
    rw [← Scheme.IdealSheafData.one_eq_top, one_mul]
  have h' : effectiveCartierWeilDivisor (⊤ : X.IdealSheafData) inferInstance =
      effectiveCartierWeilDivisor (⊤ : X.IdealSheafData) inferInstance +
        effectiveCartierWeilDivisor (⊤ : X.IdealSheafData) inferInstance := by
    convert h using 2
    exact htop.symm
  exact left_eq_add.mp h' |>.symm ▸ rfl

/-- Equal effective Cartier divisors have equal Weil divisors. -/
theorem effectiveCartierWeilDivisor_congr {I J : X.IdealSheafData} (h : I = J)
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)
    (hJ : Stacks.Divisors.IsEffectiveCartierDivisor J) :
    effectiveCartierWeilDivisor I hI = effectiveCartierWeilDivisor J hJ := by
  subst h
  rfl

/-- **Additivity of the Weil divisor over finite products**, coefficientwise:
`[∏ D_i] Z = ∑ [D_i] Z`. -/
theorem effectiveCartierWeilDivisor_prod_apply {ι : Type*} (s : Finset ι)
    (I : ι → X.IdealSheafData) [hI : ∀ i, Stacks.Divisors.IsEffectiveCartierDivisor (I i)]
    (Z : PrimeDivisor X) :
    (effectiveCartierWeilDivisor (∏ i ∈ s, I i) (isEffectiveCartierDivisor_prod s hI)).1 Z =
      ∑ i ∈ s, (effectiveCartierWeilDivisor (I i) (hI i)).1 Z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact congrArg (fun D : WeilDivisor X => D.1 Z)
      ((effectiveCartierWeilDivisor_congr
        (Finset.prod_empty.trans Scheme.IdealSheafData.one_eq_top) _ inferInstance).trans
        effectiveCartierWeilDivisor_top)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ← ih]
    exact congrArg (fun D : WeilDivisor X => D.1 Z)
      ((effectiveCartierWeilDivisor_congr (Finset.prod_insert ha) _
        (@Stacks.Divisors.IsEffectiveCartierDivisor.mul _ (I a) (∏ i ∈ s, I i) (hI a)
          (isEffectiveCartierDivisor_prod s hI))).trans
        (effectiveCartierWeilDivisor_mul _ _ _ _))

/-! ### Orders of vanishing of products, quotients and powers -/

/-- `ord 1 = 0`. -/
theorem ord_one_functionField (z : X) : X.ord (1 : X.functionField) z = 0 := by
  have h := Scheme.ord_mul (X := X) (x := z) (f := (1 : X.functionField)) (g := 1) one_ne_zero
    one_ne_zero
  rw [mul_one] at h
  omega

/-- The order of vanishing of a finite product of non-zero rational functions is the sum of the
orders. -/
theorem ord_prod_functionField {ι : Type*} (s : Finset ι) (g : ι → X.functionField)
    (hg : ∀ i ∈ s, g i ≠ 0) (z : X) : X.ord (∏ i ∈ s, g i) z = ∑ i ∈ s, X.ord (g i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty]; exact ord_one_functionField z
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      Scheme.ord_mul (hg a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hg i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hg i (Finset.mem_insert_of_mem hi)]

/-- `ord (a / b) = ord a - ord b` for non-zero `a, b`. -/
theorem ord_div_functionField {a b : X.functionField} (ha : a ≠ 0) (hb : b ≠ 0) (z : X) :
    X.ord (a / b) z = X.ord a z - X.ord b z := by
  have h := Scheme.ord_mul (X := X) (x := z) (div_ne_zero ha hb) hb
  rw [div_mul_cancel₀ _ hb] at h
  omega

/-- `ord (a ^ n) = n · ord a` for non-zero `a`. -/
theorem ord_pow_functionField {a : X.functionField} (ha : a ≠ 0) (n : ℕ) (z : X) :
    X.ord (a ^ n) z = n * X.ord a z := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul]; exact ord_one_functionField z
  | succ n ih =>
    rw [pow_succ, Scheme.ord_mul (pow_ne_zero n ha) ha, ih]
    push_cast
    ring

end Products

/-! ### Local ratios -/

section LocalRatios

variable [IsNoetherian X] [IsIntegral X]

/-- **The Weil divisors of two effective Cartier divisors with local ratios.** Suppose affine
opens `W i` cover `X`, with `I` cut out on `W i` by a non-zero-divisor `τ i` and `J` by a
non-zero-divisor `σ i`, and `τ i σ j = τ j σ i` at every point of `W i ∩ W j`. If the rational
function `φ` satisfies `φ τ i₀ = σ i₀` (so `φ = σ i / τ i` on every `W i`), then
`[J] = [I] + div φ`. -/
theorem effectiveCartierWeilDivisor_eq_add_of_local_ratios {ι : Type*} (I J : X.IdealSheafData)
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)
    (hJ : Stacks.Divisors.IsEffectiveCartierDivisor J) (W : ι → X.affineOpens)
    (τ σ : ∀ i, Γ(X, (W i).1)) (cover : ∀ x : X, ∃ i, x ∈ (W i).1)
    (hτ : ∀ i, I.ideal (W i) = Ideal.span {τ i}) (hσ : ∀ i, J.ideal (W i) = Ideal.span {σ i})
    (hτ0 : ∀ i, τ i ∈ nonZeroDivisors Γ(X, (W i).1))
    (compat : ∀ (i j : ι) (x : X) (hi : x ∈ (W i).1) (hj : x ∈ (W j).1),
      X.presheaf.germ (W i).1 x hi (τ i) * X.presheaf.germ (W j).1 x hj (σ j) =
        X.presheaf.germ (W j).1 x hj (τ j) * X.presheaf.germ (W i).1 x hi (σ i))
    (i0 : ι) [Nonempty (W i0).1] (φ : X.functionFieldˣ)
    (hφ : (φ : X.functionField) * X.germToFunctionField (W i0).1 (τ i0) =
      X.germToFunctionField (W i0).1 (σ i0)) :
    effectiveCartierWeilDivisor J hJ =
      effectiveCartierWeilDivisor I hI + rationalFunctionWeilDivisor X φ := by
  have hη : ∀ i (z : X), z ∈ (W i).1 → genericPoint X ∈ (W i).1 := fun i z hz =>
    ((genericPoint_spec X).mem_open_set_iff (W i).1.isOpen).mpr ⟨z, Set.mem_univ _, hz⟩
  have hne : ∀ (i : ι) [Nonempty (W i).1] (s : Γ(X, (W i).1)),
      s ∈ nonZeroDivisors Γ(X, (W i).1) → X.germToFunctionField (W i).1 s ≠ 0 := by
    intro i _ s hs
    have : IsDomain Γ(X, (W i).1) := IsIntegral.component_integral (W i).1
    intro h
    exact nonZeroDivisors.ne_zero hs (X.germToFunctionField_injective _ (h.trans (map_zero _).symm))
  have hi0 : genericPoint X ∈ (W i0).1 := ((genericPoint_spec X).mem_open_set_iff
    (W i0).1.isOpen).mpr (by simpa using ‹Nonempty (W i0).1›)
  have ht0 : X.germToFunctionField (W i0).1 (τ i0) ≠ 0 := hne i0 _ (hτ0 i0)
  refine Subtype.ext (funext fun Z => ?_)
  obtain ⟨i, hi⟩ := cover Z.genericPoint
  have : Nonempty (W i).1 := ⟨⟨_, hi⟩⟩
  have hηi := hη i _ hi
  have hcI := effectiveCartierWeilDivisor_apply_eq_ord_of_ideal_eq_span I hI Z hi (hτ i)
  have hcJ := effectiveCartierWeilDivisor_apply_eq_ord_of_ideal_eq_span J hJ Z hi (hσ i)
  rw [X.algebraMap_germ_eq_germToFunctionField hi] at hcI hcJ
  have ha : X.germToFunctionField (W i).1 (τ i) ≠ 0 := hne i _ (hτ0 i)
  have hc := compat i i0 (genericPoint X) hηi hi0
  have hrel : (φ : X.functionField) * X.germToFunctionField (W i).1 (τ i) =
      X.germToFunctionField (W i).1 (σ i) := by
    refine mul_right_cancel₀ ht0 ?_
    calc (φ : X.functionField) * X.germToFunctionField (W i).1 (τ i) *
          X.germToFunctionField (W i0).1 (τ i0)
        = X.germToFunctionField (W i).1 (τ i) *
            ((φ : X.functionField) * X.germToFunctionField (W i0).1 (τ i0)) := by ring
      _ = X.germToFunctionField (W i).1 (τ i) * X.germToFunctionField (W i0).1 (σ i0) := by
          rw [hφ]
      _ = X.germToFunctionField (W i0).1 (τ i0) * X.germToFunctionField (W i).1 (σ i) := hc
      _ = _ := mul_comm _ _
  change (effectiveCartierWeilDivisor J hJ).1 Z =
    (effectiveCartierWeilDivisor I hI).1 Z + (rationalFunctionWeilDivisor X φ).1 Z
  rw [hcI, hcJ, ← hrel, Scheme.ord_mul φ.ne_zero ha, rationalFunctionWeilDivisor_apply]
  exact add_comm _ _

/-- **Linear equivalence from local ratios.** Let `X` be a normal Noetherian integral scheme and
`I`, `J` effective Cartier divisors with local ratios as in
`effectiveCartierWeilDivisor_eq_add_of_local_ratios`. Then `I` and `J` are linearly equivalent
(the ratios `σ i / τ i` glue to the rational function `φ` with `[J] = [I] + div φ`). -/
theorem linearlyEquivalent_of_local_ratios [IsNormal X] {ι : Type*} (I J : X.IdealSheafData)
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)
    (hJ : Stacks.Divisors.IsEffectiveCartierDivisor J) (W : ι → X.affineOpens)
    (τ σ : ∀ i, Γ(X, (W i).1)) (cover : ∀ x : X, ∃ i, x ∈ (W i).1)
    (hτ : ∀ i, I.ideal (W i) = Ideal.span {τ i}) (hσ : ∀ i, J.ideal (W i) = Ideal.span {σ i})
    (hτ0 : ∀ i, τ i ∈ nonZeroDivisors Γ(X, (W i).1))
    (hσ0 : ∀ i, σ i ∈ nonZeroDivisors Γ(X, (W i).1))
    (compat : ∀ (i j : ι) (x : X) (hi : x ∈ (W i).1) (hj : x ∈ (W j).1),
      X.presheaf.germ (W i).1 x hi (τ i) * X.presheaf.germ (W j).1 x hj (σ j) =
        X.presheaf.germ (W j).1 x hj (τ j) * X.presheaf.germ (W i).1 x hi (σ i)) :
    Stacks.Divisors.LinearlyEquivalent I J := by
  rw [linearlyEquivalent_iff_exists_rationalFunctionWeilDivisor I J hI hJ]
  obtain ⟨i0, hi0⟩ := cover (genericPoint X)
  have : Nonempty (W i0).1 := ⟨⟨_, hi0⟩⟩
  have : IsDomain Γ(X, (W i0).1) := IsIntegral.component_integral (W i0).1
  have hne : ∀ s : Γ(X, (W i0).1), s ∈ nonZeroDivisors Γ(X, (W i0).1) →
      X.germToFunctionField (W i0).1 s ≠ 0 := fun s hs h =>
    nonZeroDivisors.ne_zero hs (X.germToFunctionField_injective _ (h.trans (map_zero _).symm))
  have hs0 := hne _ (hσ0 i0)
  have ht0 := hne _ (hτ0 i0)
  refine ⟨Units.mk0 (X.germToFunctionField (W i0).1 (σ i0) /
    X.germToFunctionField (W i0).1 (τ i0)) (div_ne_zero hs0 ht0), ?_⟩
  exact effectiveCartierWeilDivisor_eq_add_of_local_ratios I J hI hJ W τ σ cover hτ hσ hτ0
    compat i0 _ (by simp only [Units.val_mk0]; exact div_mul_cancel₀ _ ht0)

/-- Two affine opens, indexed by `Bool`. -/
private def twoAffineOpens (W₁ W₂ : X.affineOpens) : Bool → X.affineOpens
  | true => W₁
  | false => W₂

/-- Two sections over two affine opens, indexed by `Bool`. -/
private def twoSections {W₁ W₂ : X.affineOpens} (s₁ : Γ(X, W₁.1)) (s₂ : Γ(X, W₂.1)) :
    ∀ b, Γ(X, (twoAffineOpens W₁ W₂ b).1)
  | true => s₁
  | false => s₂

/-- **The Weil divisors of two effective Cartier divisors with local ratios on a cover by two
affine opens**: `I = (τ₁)`, `J = (σ₁)` on `W₁`, `I = (τ₂)`, `J = (σ₂)` on `W₂`, with
non-zero-divisor generators and `τ₁ σ₂ = τ₂ σ₁` at every point of `W₁ ∩ W₂`. If `φ τ₁ = σ₁` in
the function field then `[J] = [I] + div φ`. -/
theorem effectiveCartierWeilDivisor_eq_add_of_two_local_ratios
    (I J : X.IdealSheafData) (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)
    (hJ : Stacks.Divisors.IsEffectiveCartierDivisor J) (W₁ W₂ : X.affineOpens)
    [Nonempty W₁.1] (hcov : ∀ x : X, x ∈ W₁.1 ∨ x ∈ W₂.1) {τ₁ σ₁ : Γ(X, W₁.1)}
    {τ₂ σ₂ : Γ(X, W₂.1)}
    (hτ₁ : I.ideal W₁ = Ideal.span {τ₁}) (hτ₂ : I.ideal W₂ = Ideal.span {τ₂})
    (hσ₁ : J.ideal W₁ = Ideal.span {σ₁}) (hσ₂ : J.ideal W₂ = Ideal.span {σ₂})
    (hτ₁0 : τ₁ ∈ nonZeroDivisors Γ(X, W₁.1)) (hτ₂0 : τ₂ ∈ nonZeroDivisors Γ(X, W₂.1))
    (h12 : ∀ (x : X) (h₁ : x ∈ W₁.1) (h₂ : x ∈ W₂.1),
      X.presheaf.germ W₁.1 x h₁ τ₁ * X.presheaf.germ W₂.1 x h₂ σ₂ =
        X.presheaf.germ W₂.1 x h₂ τ₂ * X.presheaf.germ W₁.1 x h₁ σ₁)
    (φ : X.functionFieldˣ)
    (hφ : (φ : X.functionField) * X.germToFunctionField W₁.1 τ₁ = X.germToFunctionField W₁.1 σ₁) :
    effectiveCartierWeilDivisor J hJ =
      effectiveCartierWeilDivisor I hI + rationalFunctionWeilDivisor X φ := by
  have : Nonempty (twoAffineOpens W₁ W₂ true).1 := ‹Nonempty W₁.1›
  exact effectiveCartierWeilDivisor_eq_add_of_local_ratios I J hI hJ (twoAffineOpens W₁ W₂)
    (twoSections τ₁ τ₂) (twoSections σ₁ σ₂)
    (fun x => (hcov x).elim (fun h => ⟨true, h⟩) (fun h => ⟨false, h⟩))
    (fun b => by cases b; exacts [hτ₂, hτ₁]) (fun b => by cases b; exacts [hσ₂, hσ₁])
    (fun b => by cases b; exacts [hτ₂0, hτ₁0])
    (fun i j x hi hj => by
      cases i <;> cases j
      exacts [rfl, (h12 x hj hi).symm, h12 x hi hj, rfl])
    true φ hφ

/-- **Doubled Weil divisors of two effective Cartier divisors with local ratios on a cover by two
affine opens**, coefficientwise: if `I * I = (τ₁), (τ₂)` and `J * J = (σ₁), (σ₂)` as above, then
`2 [J] Z = 2 [I] Z + ord_Z φ` where `φ τ₁ = σ₁`. -/
theorem effectiveCartierWeilDivisor_two_apply_of_two_local_ratios
    (I J : X.IdealSheafData) (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)
    (hJ : Stacks.Divisors.IsEffectiveCartierDivisor J) (W₁ W₂ : X.affineOpens)
    [Nonempty W₁.1] (hcov : ∀ x : X, x ∈ W₁.1 ∨ x ∈ W₂.1) {τ₁ σ₁ : Γ(X, W₁.1)}
    {τ₂ σ₂ : Γ(X, W₂.1)}
    (hτ₁ : (I * I).ideal W₁ = Ideal.span {τ₁}) (hτ₂ : (I * I).ideal W₂ = Ideal.span {τ₂})
    (hσ₁ : (J * J).ideal W₁ = Ideal.span {σ₁}) (hσ₂ : (J * J).ideal W₂ = Ideal.span {σ₂})
    (hτ₁0 : τ₁ ∈ nonZeroDivisors Γ(X, W₁.1)) (hτ₂0 : τ₂ ∈ nonZeroDivisors Γ(X, W₂.1))
    (h12 : ∀ (x : X) (h₁ : x ∈ W₁.1) (h₂ : x ∈ W₂.1),
      X.presheaf.germ W₁.1 x h₁ τ₁ * X.presheaf.germ W₂.1 x h₂ σ₂ =
        X.presheaf.germ W₂.1 x h₂ τ₂ * X.presheaf.germ W₁.1 x h₁ σ₁)
    (φ : X.functionFieldˣ)
    (hφ : (φ : X.functionField) * X.germToFunctionField W₁.1 τ₁ = X.germToFunctionField W₁.1 σ₁)
    (Z : PrimeDivisor X) :
    (effectiveCartierWeilDivisor J hJ).1 Z + (effectiveCartierWeilDivisor J hJ).1 Z =
      ((effectiveCartierWeilDivisor I hI).1 Z + (effectiveCartierWeilDivisor I hI).1 Z) +
        X.ord (φ : X.functionField) Z.genericPoint := by
  have key := effectiveCartierWeilDivisor_eq_add_of_two_local_ratios (I * I) (J * J)
    (@Stacks.Divisors.IsEffectiveCartierDivisor.mul _ _ _ hI hI)
    (@Stacks.Divisors.IsEffectiveCartierDivisor.mul _ _ _ hJ hJ) W₁ W₂ hcov hτ₁ hτ₂ hσ₁ hσ₂
    hτ₁0 hτ₂0 h12 φ hφ
  rw [effectiveCartierWeilDivisor_mul, effectiveCartierWeilDivisor_mul] at key
  exact congrArg (fun D : WeilDivisor X => D.1 Z) key

/-- **Linear equivalence from local ratios on a cover by two affine opens.** -/
theorem linearlyEquivalent_of_two_local_ratios [IsNormal X]
    (I J : X.IdealSheafData) (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)
    (hJ : Stacks.Divisors.IsEffectiveCartierDivisor J) (W₁ W₂ : X.affineOpens)
    (hcov : ∀ x : X, x ∈ W₁.1 ∨ x ∈ W₂.1) {τ₁ σ₁ : Γ(X, W₁.1)} {τ₂ σ₂ : Γ(X, W₂.1)}
    (hτ₁ : I.ideal W₁ = Ideal.span {τ₁}) (hτ₂ : I.ideal W₂ = Ideal.span {τ₂})
    (hσ₁ : J.ideal W₁ = Ideal.span {σ₁}) (hσ₂ : J.ideal W₂ = Ideal.span {σ₂})
    (hτ₁0 : τ₁ ∈ nonZeroDivisors Γ(X, W₁.1)) (hτ₂0 : τ₂ ∈ nonZeroDivisors Γ(X, W₂.1))
    (hσ₁0 : σ₁ ∈ nonZeroDivisors Γ(X, W₁.1)) (hσ₂0 : σ₂ ∈ nonZeroDivisors Γ(X, W₂.1))
    (h12 : ∀ (x : X) (h₁ : x ∈ W₁.1) (h₂ : x ∈ W₂.1),
      X.presheaf.germ W₁.1 x h₁ τ₁ * X.presheaf.germ W₂.1 x h₂ σ₂ =
        X.presheaf.germ W₂.1 x h₂ τ₂ * X.presheaf.germ W₁.1 x h₁ σ₁) :
    Stacks.Divisors.LinearlyEquivalent I J :=
  linearlyEquivalent_of_local_ratios I J hI hJ (twoAffineOpens W₁ W₂) (twoSections τ₁ τ₂)
    (twoSections σ₁ σ₂) (fun x => (hcov x).elim (fun h => ⟨true, h⟩) (fun h => ⟨false, h⟩))
    (fun b => by cases b; exacts [hτ₂, hτ₁]) (fun b => by cases b; exacts [hσ₂, hσ₁])
    (fun b => by cases b; exacts [hτ₂0, hτ₁0]) (fun b => by cases b; exacts [hσ₂0, hσ₁0])
    (fun i j x hi hj => by
      cases i <;> cases j
      exacts [rfl, (h12 x hj hi).symm, h12 x hi hj, rfl])

end LocalRatios

end Divisors

end ArithmeticOfJacobiPolynomials
