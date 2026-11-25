/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.Divisors.Weil
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.MaximalDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.DeltaDimensionCoheight
public import StacksFrontier.AlgebraicGeometry.Chow.DimensionFunction
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalenceDefs

/-!
# Cycles and Chow groups of an integral scheme: dimension indexing

Cycles, rational equivalence and Chow groups are the library's: for a Chow situation `C`
(Stacks 02QL; over a field `k` it is `Stacks.Chow.fieldChowSituation k`) and `p : X ⟶ C.S` locally
of finite type,

* `Stacks.Chow.CycleGroup C p k` is `Z_k(X)` (Stacks 02QR), cycles graded by delta-dimension;
* `Stacks.Chow.rationalEquivalences C p k` is the subgroup of cycles rationally equivalent to
  zero (Stacks 02RW);
* `Stacks.Chow.chowGroup C p k = Z_k(X) ⧸ rationalEquivalences C p k` is `A_k(X)` (Stacks 02RW),
  and `Stacks.Chow.properChowPushforward` is the proper pushforward on it (Stacks 0GU8).

What the library does not provide, and this file proves, is the **dimension-indexing bridge**
between the two presentations used here. Divisors are indexed by *codimension*
(`AlgebraicGeometry.WeilDivisor X`, prime divisors, points of coheight one, the canonical objects
of `ArithmeticOfJacobiPolynomials.Geometry.Divisors.Weil`), cycles by *delta-dimension* (the
grading of
`CycleGroup C p`). On an integral scheme `X` of delta-dimension `n` the two are related by
`δ(x) = n - coheight x`, so that Weil divisors are exactly the cycles of delta-dimension `n - 1`.

## Main results

* `ArithmeticOfJacobiPolynomials.Chow.exists_coheight_eq_relativeDimension_eq`: for `X` integral of
  delta-dimension `n` and every point `x`, there is `c : ℕ` with `coheight x = c` and
  `δ(x) = n - c` (from Stacks 02JW through `Stacks.Chow.relativeDimension_sub_le_coheight` and
  `Stacks.Chow.exists_coheight_eq_and_relativeDimension_add_le`).
* `ArithmeticOfJacobiPolynomials.Chow.coheight_eq_one_iff_relativeDimension`: coheight one is
delta-dimension
  `n - 1`.
* `ArithmeticOfJacobiPolynomials.Chow.mem_cyclesOfDimension_sub_one_iff`: a cycle is an `(n -
1)`-cycle iff it is
  supported in coheight one.
* `ArithmeticOfJacobiPolynomials.Chow.weilDivisorEquivCycleGroup`:
  `WeilDivisor X ≃+ CycleGroup C p (n - 1)`, with the coefficient at the generic point of a
  prime divisor `Z` equal to `D Z`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open AlgebraicGeometry Stacks.Chow Order TopologicalSpace ArithmeticOfJacobiPolynomials.Divisors

universe u

namespace Chow

section Dimension

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  [IsIntegral X] {n : ℤ}

/-- On an integral scheme of delta-dimension `n` the generic point has relative dimension `n`. -/
theorem relativeDimension_genericPoint_eq (hn : schemeDeltaDimension C p = (n : EInt)) :
    relativeDimension C.dimensionFunction p (genericPoint X) = n := by
  rw [schemeDeltaDimension_eq_genericPoint] at hn
  exact WithBotTop.coe_injective hn

omit [IsIntegral X] in
/-- Every point of a scheme of delta-dimension `n` has relative dimension at most `n`. -/
theorem relativeDimension_le_of_schemeDeltaDimension_eq
    (hn : schemeDeltaDimension C p = (n : EInt)) (x : X) :
    relativeDimension C.dimensionFunction p x ≤ n :=
  relativeDimension_le_of_schemeDeltaDimension_le' C p hn.le x

/-- **The dimension bridge** (Stacks 02JW). On an integral scheme `X` of delta-dimension `n`, a
point of coheight `c` has delta-dimension `n - c`, and every coheight is finite. -/
theorem exists_coheight_eq_relativeDimension_eq (hn : schemeDeltaDimension C p = (n : EInt))
    (x : X) :
    ∃ c : ℕ, coheight x = c ∧ relativeDimension C.dimensionFunction p x = n - c := by
  obtain ⟨c, hc, hle⟩ := exists_coheight_eq_and_relativeDimension_add_le C p x n
    fun y _ => relativeDimension_le_of_schemeDeltaDimension_eq C p hn y
  have h2 := relativeDimension_sub_le_coheight C p (genericPoint_specializes x) hc
  rw [relativeDimension_genericPoint_eq C p hn] at h2
  exact ⟨c, hc, by omega⟩

/-- A point has coheight zero iff it has delta-dimension `n`, i.e. iff it is the generic point. -/
theorem coheight_eq_zero_iff_relativeDimension (hn : schemeDeltaDimension C p = (n : EInt))
    (x : X) : coheight x = 0 ↔ relativeDimension C.dimensionFunction p x = n := by
  obtain ⟨c, hc, hδ⟩ := exists_coheight_eq_relativeDimension_eq C p hn x
  rw [hc, hδ]
  constructor
  · intro h
    have : c = 0 := by exact_mod_cast h
    subst this
    simp
  · intro h
    have : c = 0 := by omega
    subst this
    simp

/-- A point has coheight one iff it has delta-dimension `n - 1`. -/
theorem coheight_eq_one_iff_relativeDimension (hn : schemeDeltaDimension C p = (n : EInt))
    (x : X) : coheight x = 1 ↔ relativeDimension C.dimensionFunction p x = n - 1 := by
  obtain ⟨c, hc, hδ⟩ := exists_coheight_eq_relativeDimension_eq C p hn x
  rw [hc, hδ]
  constructor
  · intro h
    have : c = 1 := by exact_mod_cast h
    subst this
    simp
  · intro h
    have : c = 1 := by omega
    subst this
    simp

/-- A cycle is an `(n - 1)`-cycle iff it is supported in coheight one. -/
theorem mem_cyclesOfDimension_sub_one_iff (hn : schemeDeltaDimension C p = (n : EInt))
    (c : AlgebraicCycle X ℤ) :
    c ∈ cyclesOfDimension C p (n - 1) ↔ ∀ x : X, c x ≠ 0 → coheight x = 1 := by
  rw [mem_cyclesOfDimension_iff_forall_point]
  exact forall_congr' fun x =>
    imp_congr_right fun _ => (coheight_eq_one_iff_relativeDimension C p hn x).symm

end Dimension

section WeilDivisors

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  [IsIntegral X] {n : ℤ}

/-- The cycle of a Weil divisor, as an element of `Z_{n-1}(X)`. -/
@[expose] noncomputable def weilDivisorToCycleGroup (hn : schemeDeltaDimension C p = (n : EInt)) :
    WeilDivisor X →+ CycleGroup C p (n - 1) :=
  (cycleOfWeilDivisor (X := X)).codRestrict (cyclesOfDimension C p (n - 1)) fun D => by
    rw [mem_cyclesOfDimension_sub_one_iff C p hn]
    intro x hx
    by_contra h
    exact hx (cycleOfWeilDivisor_apply_of_coheight_ne_one D h)

@[simp]
theorem coe_weilDivisorToCycleGroup (hn : schemeDeltaDimension C p = (n : EInt))
    (D : WeilDivisor X) :
    (weilDivisorToCycleGroup C p hn D : AlgebraicCycle X ℤ) = cycleOfWeilDivisor D :=
  rfl

theorem weilDivisorToCycleGroup_injective (hn : schemeDeltaDimension C p = (n : EInt)) :
    Function.Injective (weilDivisorToCycleGroup C p hn) := fun _ _ h =>
  cycleOfWeilDivisor_injective (congrArg Subtype.val h)

theorem weilDivisorToCycleGroup_surjective (hn : schemeDeltaDimension C p = (n : EInt)) :
    Function.Surjective (weilDivisorToCycleGroup C p hn) := by
  rintro ⟨c, hc⟩
  rw [mem_cyclesOfDimension_sub_one_iff C p hn] at hc
  have hmem : c ∈ (cycleOfWeilDivisor (X := X)).range := by
    rw [range_cycleOfWeilDivisor, AlgebraicCycle.mem_weilDivisors,
      AlgebraicCycle.isWeilDivisor_iff]
    intro x hx
    exact hc x hx
  obtain ⟨D, hD⟩ := hmem
  exact ⟨D, Subtype.ext hD⟩

/-- **Weil divisors are the `(n - 1)`-cycles.** On an integral scheme of delta-dimension `n`,
`Z_{n-1}(X) ≃ WeilDivisor X`: dimension `n - 1` is codimension one. -/
@[expose] noncomputable def weilDivisorEquivCycleGroup
    (hn : schemeDeltaDimension C p = (n : EInt)) :
    WeilDivisor X ≃+ CycleGroup C p (n - 1) :=
  AddEquiv.ofBijective (weilDivisorToCycleGroup C p hn)
    ⟨weilDivisorToCycleGroup_injective C p hn, weilDivisorToCycleGroup_surjective C p hn⟩

@[simp]
theorem coe_weilDivisorEquivCycleGroup (hn : schemeDeltaDimension C p = (n : EInt))
    (D : WeilDivisor X) :
    (weilDivisorEquivCycleGroup C p hn D : AlgebraicCycle X ℤ) = cycleOfWeilDivisor D :=
  rfl

/-- The coefficient of the cycle of `D` at the generic point of a prime divisor `Z` is `D Z`. -/
theorem weilDivisorEquivCycleGroup_genericPoint (hn : schemeDeltaDimension C p = (n : EInt))
    (D : WeilDivisor X) (Z : PrimeDivisor X) :
    (weilDivisorEquivCycleGroup C p hn D : AlgebraicCycle X ℤ) Z.genericPoint = D.1 Z :=
  cycleOfWeilDivisor_genericPoint D Z

end WeilDivisors

end Chow

end ArithmeticOfJacobiPolynomials
