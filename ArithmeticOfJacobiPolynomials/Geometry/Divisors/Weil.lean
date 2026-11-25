/- Assembled by AxiomProver. -/
module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Chow.Vocabulary.PrincipalCycle
public import StacksFrontier.AlgebraicGeometry.Divisors.RationalFunctionWeilDivisor
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.ClassGroup

/-!
# Bridges between points of coheight one, prime divisors and algebraic cycles

Weil divisors, principal divisors and class groups are the library's:

* `AlgebraicGeometry.PrimeDivisor X`, `AlgebraicGeometry.WeilDivisor X` (Stacks 0BE2),
  indexed by prime divisors (integral closed subschemes of codimension one);
* `AlgebraicGeometry.principalDivisor X : (Stacks.Chow.rationalFunctions X)ˣ → WeilDivisor X`
  (its docstring cites Stacks 0BE3; the `@[stacks 0BE3]` attribute itself sits on
  `Stacks.Chow.principalCycle`), `AlgebraicGeometry.rationalFunctionWeilDivisor X :
  X.functionFieldˣ → WeilDivisor X` (`@[stacks 02AR]`, part (3)) and
  `AlgebraicGeometry.weilDivisorClassGroup X` (`@[stacks 0BE4]`);
* Mathlib's `AlgebraicGeometry.AlgebraicCycle X ℤ` (`@[stacks 02QR]`), its subgroup
  `AlgebraicGeometry.AlgebraicCycle.weilDivisors X ℤ` of cycles supported in coheight one
  (`@[stacks 0BE2 "(2)"]`) and the degree `AlgebraicGeometry.AlgebraicCycle.degree`
  (`@[stacks 0AZ2]`).

This file proves the dictionary between the *prime-divisor* presentation
(used by `principalDivisor`, `weilDivisorClassGroup`, `effectiveCartierWeilDivisor`) and the
*point* presentation (used by `AlgebraicCycle` and `Scheme.ord`) for
`AlgebraicGeometry.PrimeDivisor`.
Stacks has the dictionary for its separate structure `Stacks.Divisors.PrimeDivisor`
(`Stacks.Divisors.PrimeDivisor.equivCoheightOne`, `Stacks.Chow.weilDivisorAlgebraicCycle`).

## Main definitions and results

* `ArithmeticOfJacobiPolynomials.Divisors.primeDivisorEquivCoheightOne`:
  `PrimeDivisor X ≃ {x : X // coheight x = 1}`, with inverse `PrimeDivisor.ofCoheightOne`.
* `ArithmeticOfJacobiPolynomials.Divisors.cycleOfWeilDivisor : WeilDivisor X →+ AlgebraicCycle X
ℤ`: the cycle
  with coefficient `D Z` at the generic point of `Z` and `0` elsewhere; it is injective with
  range `AlgebraicCycle.weilDivisors X ℤ`
  (`ArithmeticOfJacobiPolynomials.Divisors.range_cycleOfWeilDivisor`).
* `ArithmeticOfJacobiPolynomials.Divisors.cycleOfWeilDivisor_principalDivisor`,
  `ArithmeticOfJacobiPolynomials.Divisors.cycleOfWeilDivisor_rationalFunctionWeilDivisor`: the
  cycle of a
  principal divisor is `z ↦ Scheme.ord f z`, at every point.
* `ArithmeticOfJacobiPolynomials.Divisors.cycleOfWeilDivisor_principalDivisor_eq_principalCycle`:
the cycle of a
  principal divisor is the library's `Stacks.Chow.principalCycle` (Stacks 0BE3, 02RP).
* `ArithmeticOfJacobiPolynomials.Divisors.principalDivisor_apply_ofCoheightOne`: the coefficient of
a principal
  divisor at `PrimeDivisor.ofCoheightOne x hx`.
* `ArithmeticOfJacobiPolynomials.Divisors.rationalFunctionWeilDivisor_mul`, `_one`, `_inv`, `_div`:
the
  multiplicativity of `rationalFunctionWeilDivisor` (the library states it for `principalDivisor`
  only).
* `ArithmeticOfJacobiPolynomials.Divisors.rationalFunctionWeilDivisor_germ_unit`: the divisor of a
global unit is
  zero.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Divisors

variable {X : Scheme.{u}}

/-! ### Prime divisors are the points of coheight one -/

/-- **Prime divisors are the points of coheight one**, for the canonical
`AlgebraicGeometry.PrimeDivisor` (`@[stacks 0BE2 "part (1)"]`). The inverse is
`PrimeDivisor.ofCoheightOne`; the analogous equivalence for the separate structure
`Stacks.Divisors.PrimeDivisor` is `Stacks.Divisors.PrimeDivisor.equivCoheightOne`. -/
@[expose] noncomputable def primeDivisorEquivCoheightOne :
    PrimeDivisor X ≃ {x : X // Order.coheight x = 1} where
  toFun Z := ⟨Z.genericPoint, Z.coheight_genericPoint⟩
  invFun x := PrimeDivisor.ofCoheightOne x.1 x.2
  left_inv _ := PrimeDivisor.genericPoint_injective (PrimeDivisor.genericPoint_ofCoheightOne _ _)
  right_inv _ := Subtype.ext (PrimeDivisor.genericPoint_ofCoheightOne _ _)

/-- A prime divisor is `ofCoheightOne` of its generic point. -/
theorem ofCoheightOne_genericPoint (Z : PrimeDivisor X) :
    PrimeDivisor.ofCoheightOne Z.genericPoint Z.coheight_genericPoint = Z :=
  PrimeDivisor.genericPoint_injective (PrimeDivisor.genericPoint_ofCoheightOne _ _)

/-- The generic points of prime divisors are exactly the points of coheight one. -/
theorem mem_range_genericPoint_iff {x : X} :
    x ∈ Set.range (PrimeDivisor.genericPoint (X := X)) ↔ Order.coheight x = 1 :=
  ⟨fun ⟨Z, hZ⟩ => hZ ▸ Z.coheight_genericPoint,
    fun h => ⟨_, PrimeDivisor.genericPoint_ofCoheightOne x h⟩⟩

/-! ### The cycle of a Weil divisor -/

/-- The coefficient function on the points of `X` of a coefficient family on prime divisors: at a
point `x` of coheight one it is the coefficient of `PrimeDivisor.ofCoheightOne x`, elsewhere `0`.
(The analogue `Stacks.Chow.weilDivisorCoeff` is for the separate structure
`Stacks.Divisors.PrimeDivisor`.) -/
@[expose] noncomputable def pointCoeff (D : PrimeDivisor X → ℤ) (x : X) : ℤ :=
  open Classical in
  if hx : Order.coheight x = 1 then D (PrimeDivisor.ofCoheightOne x hx) else 0

@[simp]
theorem pointCoeff_genericPoint (D : PrimeDivisor X → ℤ) (Z : PrimeDivisor X) :
    pointCoeff D Z.genericPoint = D Z := by
  rw [pointCoeff, dite_eq_left Z.coheight_genericPoint, ofCoheightOne_genericPoint]

theorem pointCoeff_of_coheight_ne_one (D : PrimeDivisor X → ℤ) {x : X}
    (hx : Order.coheight x ≠ 1) : pointCoeff D x = 0 :=
  dite_eq_right hx

theorem pointCoeff_ofCoheightOne (D : PrimeDivisor X → ℤ) {x : X} (hx : Order.coheight x = 1) :
    pointCoeff D x = D (PrimeDivisor.ofCoheightOne x hx) :=
  dite_eq_left hx

theorem pointCoeff_add (D E : PrimeDivisor X → ℤ) :
    pointCoeff (D + E) = pointCoeff D + pointCoeff E := by
  funext x
  by_cases hx : Order.coheight x = 1
  · simp [pointCoeff_ofCoheightOne _ hx]
  · simp [pointCoeff_of_coheight_ne_one _ hx]

@[simp]
theorem pointCoeff_zero : pointCoeff (0 : PrimeDivisor X → ℤ) = 0 := by
  funext x
  by_cases hx : Order.coheight x = 1
  · simp [pointCoeff_ofCoheightOne _ hx]
  · simp [pointCoeff_of_coheight_ne_one _ hx]

/-- The coefficient function of a Weil divisor has locally finite support: a point with non-zero
coefficient is the generic point of a prime divisor in the support family. -/
theorem exists_mem_nhds_finite_inter_support_pointCoeff (D : WeilDivisor X) (x : X) :
    ∃ t ∈ nhds x, (t ∩ Function.support (pointCoeff D.1)).Finite := by
  obtain ⟨U, hU, hfin⟩ := D.property x
  refine ⟨U, hU, (hfin.image PrimeDivisor.genericPoint).subset fun y hy => ?_⟩
  have hy1 : Order.coheight y = 1 := by
    by_contra h
    exact hy.2 (pointCoeff_of_coheight_ne_one _ h)
  have hD : D.1 (PrimeDivisor.ofCoheightOne y hy1) ≠ 0 := by
    have h := hy.2
    rwa [Function.mem_support, pointCoeff_ofCoheightOne _ hy1] at h
  have hyS : y ∈ (PrimeDivisor.ofCoheightOne y hy1).support := by
    rw [PrimeDivisor.support_eq_closure, PrimeDivisor.genericPoint_ofCoheightOne]
    exact subset_closure rfl
  exact ⟨PrimeDivisor.ofCoheightOne y hy1, ⟨y, by simpa [hD] using hyS, hy.1⟩,
    PrimeDivisor.genericPoint_ofCoheightOne y hy1⟩

/-- **The cycle of a Weil divisor.** The algebraic cycle (Mathlib's generic-point-indexed form of
`∑ n_Z [Z]`) with coefficient `D Z` at the generic point of each prime divisor `Z` and `0` at
every other point. Its range is `AlgebraicCycle.weilDivisors X ℤ`
(`range_cycleOfWeilDivisor`). -/
@[expose] noncomputable def cycleOfWeilDivisor : WeilDivisor X →+ AlgebraicCycle X ℤ where
  toFun D :=
    { toFun := pointCoeff D.1
      supportWithinDomain' := by simp
      supportLocallyFiniteWithinDomain' := fun x _ =>
        exists_mem_nhds_finite_inter_support_pointCoeff D x }
  map_zero' := by
    ext x
    simp [pointCoeff_zero]
  map_add' D E := by
    ext x
    change pointCoeff (D.1 + E.1) x = pointCoeff D.1 x + pointCoeff E.1 x
    rw [pointCoeff_add]
    rfl

@[simp]
theorem cycleOfWeilDivisor_apply (D : WeilDivisor X) (x : X) :
    cycleOfWeilDivisor D x = pointCoeff D.1 x :=
  rfl

/-- The coefficient of the cycle at the generic point of a prime divisor `Z` is `D Z`. -/
theorem cycleOfWeilDivisor_genericPoint (D : WeilDivisor X) (Z : PrimeDivisor X) :
    cycleOfWeilDivisor D Z.genericPoint = D.1 Z :=
  pointCoeff_genericPoint D.1 Z

/-- The coefficient of the cycle at a point of coheight one `x` is the coefficient at
`PrimeDivisor.ofCoheightOne x hx`. -/
theorem cycleOfWeilDivisor_apply_of_coheight_eq_one (D : WeilDivisor X) {x : X}
    (hx : Order.coheight x = 1) :
    cycleOfWeilDivisor D x = D.1 (PrimeDivisor.ofCoheightOne x hx) :=
  pointCoeff_ofCoheightOne D.1 hx

theorem cycleOfWeilDivisor_apply_of_coheight_ne_one (D : WeilDivisor X) {x : X}
    (hx : Order.coheight x ≠ 1) : cycleOfWeilDivisor D x = 0 :=
  pointCoeff_of_coheight_ne_one D.1 hx

theorem cycleOfWeilDivisor_injective : Function.Injective (cycleOfWeilDivisor (X := X)) := by
  intro D E h
  refine Subtype.ext (funext fun Z => ?_)
  rw [← cycleOfWeilDivisor_genericPoint D Z, ← cycleOfWeilDivisor_genericPoint E Z, h]

/-- The cycles of Weil divisors are exactly the cycles supported in coheight one: the range of
`cycleOfWeilDivisor` is Mathlib's `AlgebraicCycle.weilDivisors X ℤ`. -/
theorem range_cycleOfWeilDivisor :
    (cycleOfWeilDivisor (X := X)).range = AlgebraicCycle.weilDivisors X ℤ := by
  ext c
  rw [AlgebraicCycle.mem_weilDivisors, AlgebraicCycle.isWeilDivisor_iff]
  constructor
  · rintro ⟨D, rfl⟩ x hx
    by_contra h
    exact hx (cycleOfWeilDivisor_apply_of_coheight_ne_one D h)
  · intro hc
    have hmem : (fun Z : PrimeDivisor X => c Z.genericPoint) ∈ WeilDivisor X := by
      refine mem_weilDivisor_of_forall_exists_open fun x => ?_
      obtain ⟨t, ht, hfin⟩ := c.locallyFiniteSupport x
      refine ⟨interior t, isOpen_interior, mem_interior_iff_mem_nhds.mpr ht, ?_⟩
      refine Set.Finite.of_finite_image (f := PrimeDivisor.genericPoint)
        (hfin.subset ?_) PrimeDivisor.genericPoint_injective.injOn
      rintro - ⟨Z, ⟨hZV, hZne⟩, rfl⟩
      exact ⟨interior_subset hZV, hZne⟩
    refine ⟨⟨_, hmem⟩, ?_⟩
    ext x
    by_cases hx : Order.coheight x = 1
    · rw [cycleOfWeilDivisor_apply_of_coheight_eq_one _ hx]
      simp [PrimeDivisor.genericPoint_ofCoheightOne]
    · rw [cycleOfWeilDivisor_apply_of_coheight_ne_one _ hx]
      by_contra h
      exact hx (hc (Function.mem_support.mpr (Ne.symm h)))

/-- The Weil divisors of `X` as a subgroup of the algebraic cycles: the library's
`weilDivisors X ℤ`. -/
@[expose] noncomputable def weilDivisorEquivWeilDivisors :
    WeilDivisor X ≃+ AlgebraicCycle.weilDivisors X ℤ :=
  (AddMonoidHom.ofInjective (f := cycleOfWeilDivisor (X := X))
    cycleOfWeilDivisor_injective).trans
    (AddEquiv.addSubgroupCongr range_cycleOfWeilDivisor)

@[simp]
theorem coe_weilDivisorEquivWeilDivisors (D : WeilDivisor X) :
    (weilDivisorEquivWeilDivisors D : AlgebraicCycle X ℤ) = cycleOfWeilDivisor D :=
  rfl

/-! ### Principal divisors in the point presentation -/

section Principal

variable [IsIntegral X] [IsLocallyNoetherian X]

/-- The coefficient of a principal divisor at `PrimeDivisor.ofCoheightOne x hx` is the order of
vanishing at `x` of the corresponding element of the function field. -/
theorem principalDivisor_apply_ofCoheightOne (f : (Stacks.Chow.rationalFunctions X)ˣ) {x : X}
    (hx : Order.coheight x = 1) :
    (principalDivisor X f).1 (PrimeDivisor.ofCoheightOne x hx) =
      X.ord ((Stacks.Chow.rationalFunctionsEquivFunctionField X).val f) x := by
  rw [principalDivisor_apply, PrimeDivisor.genericPoint_ofCoheightOne]

/-- The cycle of a principal divisor is `z ↦ ord_z f` at **every** point (both sides vanish off
coheight one). -/
theorem cycleOfWeilDivisor_principalDivisor (f : (Stacks.Chow.rationalFunctions X)ˣ) (x : X) :
    cycleOfWeilDivisor (principalDivisor X f) x =
      X.ord ((Stacks.Chow.rationalFunctionsEquivFunctionField X).val f) x := by
  by_cases hx : Order.coheight x = 1
  · rw [cycleOfWeilDivisor_apply_of_coheight_eq_one _ hx, principalDivisor_apply_ofCoheightOne _ hx]
  · rw [cycleOfWeilDivisor_apply_of_coheight_ne_one _ hx,
      Scheme.ord_eq_zero_of_coheight_neq_one hx]

/-- The cycle of `principalDivisor X f` is the library's `Stacks.Chow.principalCycle` (Stacks 0BE3)
of the corresponding element of the function field. -/
theorem cycleOfWeilDivisor_principalDivisor_eq_principalCycle
    (f : (Stacks.Chow.rationalFunctions X)ˣ) :
    cycleOfWeilDivisor (principalDivisor X f) =
      Stacks.Chow.principalCycle X ((Stacks.Chow.rationalFunctionsEquivFunctionField X).val f) :=
  Function.locallyFinsuppWithin.ext fun z => by
    rw [cycleOfWeilDivisor_principalDivisor, Stacks.Chow.principalCycle_apply]

end Principal

section RationalFunctions

variable [IsIntegral X] [IsNoetherian X]

/-- The coefficient of `rationalFunctionWeilDivisor X f` at `PrimeDivisor.ofCoheightOne x hx` is
`ord_x f`. -/
theorem rationalFunctionWeilDivisor_apply_ofCoheightOne (f : X.functionFieldˣ) {x : X}
    (hx : Order.coheight x = 1) :
    (rationalFunctionWeilDivisor X f).1 (PrimeDivisor.ofCoheightOne x hx) =
      X.ord (f : X.functionField) x := by
  rw [rationalFunctionWeilDivisor_apply, PrimeDivisor.genericPoint_ofCoheightOne]

/-- The cycle of `rationalFunctionWeilDivisor X f` is `z ↦ ord_z f` at every point. -/
theorem cycleOfWeilDivisor_rationalFunctionWeilDivisor (f : X.functionFieldˣ) (x : X) :
    cycleOfWeilDivisor (rationalFunctionWeilDivisor X f) x = X.ord (f : X.functionField) x := by
  by_cases hx : Order.coheight x = 1
  · rw [cycleOfWeilDivisor_apply_of_coheight_eq_one _ hx,
      rationalFunctionWeilDivisor_apply_ofCoheightOne _ hx]
  · rw [cycleOfWeilDivisor_apply_of_coheight_ne_one _ hx,
      Scheme.ord_eq_zero_of_coheight_neq_one hx]

/-- The cycle of `rationalFunctionWeilDivisor X f` is `Stacks.Chow.principalCycle X f`. -/
theorem cycleOfWeilDivisor_rationalFunctionWeilDivisor_eq_principalCycle (f : X.functionFieldˣ) :
    cycleOfWeilDivisor (rationalFunctionWeilDivisor X f) =
      Stacks.Chow.principalCycle X (f : X.functionField) :=
  Function.locallyFinsuppWithin.ext fun z => by
    rw [cycleOfWeilDivisor_rationalFunctionWeilDivisor, Stacks.Chow.principalCycle_apply]

/-- `div (f g) = div f + div g`. (Stacks states this for `principalDivisor` only.) -/
theorem rationalFunctionWeilDivisor_mul (f g : X.functionFieldˣ) :
    rationalFunctionWeilDivisor X (f * g) =
      rationalFunctionWeilDivisor X f + rationalFunctionWeilDivisor X g := by
  refine Subtype.ext (funext fun Z => ?_)
  simp only [rationalFunctionWeilDivisor_apply, Units.val_mul, AddSubgroup.coe_add, Pi.add_apply]
  exact X.ord_mul f.ne_zero g.ne_zero

@[simp]
theorem rationalFunctionWeilDivisor_one :
    rationalFunctionWeilDivisor X (1 : X.functionFieldˣ) = 0 := by
  simpa using rationalFunctionWeilDivisor_mul (X := X) 1 1

@[simp]
theorem rationalFunctionWeilDivisor_inv (f : X.functionFieldˣ) :
    rationalFunctionWeilDivisor X f⁻¹ = -rationalFunctionWeilDivisor X f := by
  rw [eq_neg_iff_add_eq_zero, add_comm, ← rationalFunctionWeilDivisor_mul, mul_inv_cancel,
    rationalFunctionWeilDivisor_one]

theorem rationalFunctionWeilDivisor_div (f g : X.functionFieldˣ) :
    rationalFunctionWeilDivisor X (f / g) =
      rationalFunctionWeilDivisor X f - rationalFunctionWeilDivisor X g := by
  rw [div_eq_mul_inv, rationalFunctionWeilDivisor_mul, rationalFunctionWeilDivisor_inv,
    sub_eq_add_neg]

theorem rationalFunctionWeilDivisor_prod {ι : Type*} (s : Finset ι) (g : ι → X.functionFieldˣ) :
    rationalFunctionWeilDivisor X (∏ i ∈ s, g i) =
      ∑ i ∈ s, rationalFunctionWeilDivisor X (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha,
      rationalFunctionWeilDivisor_mul, ih]

theorem rationalFunctionWeilDivisor_pow (f : X.functionFieldˣ) (n : ℕ) :
    rationalFunctionWeilDivisor X (f ^ n) = n • rationalFunctionWeilDivisor X f := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, rationalFunctionWeilDivisor_mul, ih, succ_nsmul]

/-- **The divisor of a global unit is zero.** `u ∈ Γ(X, ⊤)ˣ`, read in the function field through
the germ at the generic point. -/
theorem rationalFunctionWeilDivisor_germ_unit (u : Γ(X, ⊤)ˣ) :
    rationalFunctionWeilDivisor X
      (Units.map (X.presheaf.germ ⊤ (genericPoint X) trivial).hom.toMonoidHom u) = 0 := by
  have : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  refine Subtype.ext (funext fun Z => ?_)
  exact Scheme.ord_of_isUnit (U := ⊤) u.isUnit trivial

end RationalFunctions

end Divisors

end ArithmeticOfJacobiPolynomials
