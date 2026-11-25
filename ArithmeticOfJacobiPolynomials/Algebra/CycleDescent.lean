/- Assembled by AxiomProver. -/
module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.FiniteFieldExtensionDivisibility
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GenericFibre
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.LinearAlgebra.Span.Defs

/-!
# Descent of Galois-invariant cycle classes by averaging (proof of Corollary 6.6)

The last sentence of the proof of Corollary 6.6 (§6.5) reads: "A Galois-invariant
class represented by algebraic cycles over a finite extension descends with rational
coefficients by averaging over a finite Galois extension."

This file proves that argument for the **Chow groups of the Stacks project**
(`Stacks.Chow.chowGroup`, `Stacks.Chow.baseChangeChowPullbackOfIsPullback` = flat pullback `π^*`
along the projection `π : X_E ⟶ X` of a finite field extension `E/k`, and
`Stacks.Chow.properChowPushforward` = proper pushforward `π_*`); the cycle class map and the trace
formula are hypotheses of the final theorem (see "Hypotheses of `mem_span_range_cl_of_invariant`"
below).

## Contents

### 1. The averaging identity (generic linear algebra)

`span_range_descent`: let `R` be a field, `ρ` a representation of a group `G` on an `R`-vector
space `W`, `clE : B →+ W` and `clK : A →+ W` additive maps ("cycle class maps" on the integral
Chow groups over the big and the small field) and `P : B →+ A` an additive map ("transfer" /
proper pushforward). Assume the **trace formula** `clK (P δ) = ∑ j, ρ (g j) (clE δ)` for a finite
family `g : ι → G` whose cardinality is nonzero in `R`. Then every `G`-invariant vector of
`W` in the `R`-span of `range clE` lies in the `R`-span of `range clK`: it is
`(#ι)⁻¹ • ∑ j, ρ (g j) w` and each summand is, by the trace formula, the image of the transfer
of a cycle class.

`span_range_descent_quotient` is the same with `ι = G ⧸ H` for a finite-index subgroup `H`
(averaging over the cosets; characteristic zero).

### 2. The Stacks transfer for a finite field extension

Fix `E/k` finite, `X` locally of finite type over `k`, `π : X_E ⟶ X` the projection. Stacks
provides `π^*` on Chow groups and `π_*` on Chow groups of the scheme `X_E` regarded **over
`Spec k`** (`π ≫ f`). The Chow group of `X_E` over `Spec E` (the target of the base change map)
and over `Spec k` have the same cycles and the same rational equivalence
(`Stacks.Chow.isRationallyEquivalentToZero_congr`); we build the identification
`ArithmeticOfJacobiPolynomials.CycleDescent.chowLift` and the class-level transfer
`ArithmeticOfJacobiPolynomials.CycleDescent.pushforward : CH_i(X_E) →+ CH_i(X)`.

* `pushforward_baseChange` — the push-pull formula `π_* π^* α = [E : k] • α` on Chow *classes*
  (Stacks 02RH at the level of cycles, lifted to classes);
* `baseChange_pushforward_of_mem_range` and `exists_baseChange_eq_finrank_smul_of_norm_eq` —
  a class `δ` of `X_E` lies in the image of `π^*` **up to the denominator `[E:k]`** exactly when
  it is norm-invariant, `π^* π_* δ = [E:k] • δ`.  This is the Chow-level form of "descent with
  rational coefficients by averaging": in `CH ⊗ ℚ` the norm-invariant classes are exactly
  `π^* CH_i(X) ⊗ ℚ`.

### 3. The descent theorem

`mem_span_range_cl_of_invariant`: `span_range_descent` with `P` the Stacks transfer.

## Hypotheses of `mem_span_range_cl_of_invariant`

For the manuscript's use (`k = K` a number field, `E = L` finite over `K`, `ρ` the action of
`G = Gal(Q̄/K)` on `W = H^{2c}_{ét}(J_{Q̄}, ℚ_ℓ(c))`, `H = Gal(Q̄/L)`, `ι = G/H`) the theorem
takes two inputs as hypotheses:

1. **A cycle class map** `cl : CH^c(Y) → H^{2c}_{ét}(Y_{Q̄}, ℚ_ℓ(c))` for `Y` smooth projective
   over a field, additive, with values in a `ℚ_ℓ`-vector space (`clK`, `clE` above).
2. **The trace formula** `cl_K(π_* δ) = ∑_{g ∈ G/H} g · cl_L(δ)`. Geometrically: the base
   change of `π_* δ` from `K` to `Q̄` is the sum over the `K`-embeddings `τ : L ↪ Q̄` of the
   `τ`-conjugates of `δ_{Q̄}`, because `L ⊗_K Q̄ ≅ ∏_τ Q̄` and proper pushforward commutes with flat
   base change (Stacks 02R4 / Fulton, *Intersection theory*, Prop. 1.7); and the cycle class
   map is compatible with base change to `Q̄` and with the Galois action
   (`g · cl(δ) = cl(g^* δ)`). The Chow-level part of this is
   `ArithmeticOfJacobiPolynomials.ChowGaloisDescent.mackeyFormula` (`π^* π_* = ∑_σ σ`), for the
   action of `Aut(L/K)` on the Stacks Chow groups of `X_L` constructed in
   `ArithmeticOfJacobiPolynomials/Geometry/Chow/GaloisAction.lean`; the resulting trace formula
   is `trace_formula` in `ArithmeticOfJacobiPolynomials/Geometry/AbelianCycleClass.lean`.

The finite extension `E` itself is produced by `ArithmeticOfJacobiPolynomials.ChowFiniteExtension`:
every Chow class over `Q̄` is the base change of a class over a finite Galois subextension
(`exists_galoisStageChowPullback_eq`, from Stacks `0FVQ`/`0FH6`).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace ArithmeticOfJacobiPolynomials

namespace CycleDescent

/-! ### 1. The averaging identity -/

section Averaging

variable {R G W A B : Type*} [Field R] [Group G] [AddCommGroup W] [Module R W]
  [AddCommGroup A] [AddCommGroup B]

/-- **Averaging identity.** Let `ρ` be a representation of `G` on the `R`-vector space `W`,
`clK : A →+ W`, `clE : B →+ W`, `P : B →+ A`, and `g : ι → G` a finite family with `#ι ≠ 0` in
`R`, satisfying the trace formula `clK (P δ) = ∑ j, ρ (g j) (clE δ)` for all `δ : B`. Then every
`G`-invariant vector of `span R (range clE)` lies in `span R (range clK)`. -/
theorem span_range_descent (clK : A →+ W) (clE : B →+ W) (P : B →+ A)
    (ρ : Representation R G W) {ι : Type*} [Fintype ι] (g : ι → G)
    (hι : (Fintype.card ι : R) ≠ 0)
    (htrace : ∀ δ : B, clK (P δ) = ∑ j, ρ (g j) (clE δ))
    {w : W} (hw : w ∈ ρ.invariants) (hwE : w ∈ Submodule.span R (Set.range clE)) :
    w ∈ Submodule.span R (Set.range clK) := by
  have key : ∀ x ∈ Submodule.span R (Set.range clE),
      ∑ j, ρ (g j) x ∈ Submodule.span R (Set.range clK) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨δ, rfl⟩ := hx
      rw [← htrace δ]
      exact Submodule.subset_span ⟨P δ, rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      simpa only [map_add, Finset.sum_add_distrib] using add_mem hx hy
    | smul a x _ hx =>
      simpa only [map_smul, ← Finset.smul_sum] using
        Submodule.smul_mem _ a hx
  have hsum : ∑ j, ρ (g j) w = (Fintype.card ι : R) • w := by
    rw [Representation.mem_invariants] at hw
    simp only [hw, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul R]
  have h1 := key w hwE
  rw [hsum] at h1
  have h2 := Submodule.smul_mem _ ((Fintype.card ι : R)⁻¹) h1
  rwa [smul_smul, inv_mul_cancel₀ hι, one_smul] at h2

/-- **Averaging over the cosets of a finite-index subgroup.** The case of `span_range_descent`
with `ι = G ⧸ H` (in the application `G = Gal(Q̄/K)`, `H = Gal(Q̄/L)` of index `[L : K]`) in
characteristic zero. -/
theorem span_range_descent_quotient [CharZero R] (clK : A →+ W) (clE : B →+ W) (P : B →+ A)
    (ρ : Representation R G W) (H : Subgroup G) [H.FiniteIndex] [Fintype (G ⧸ H)]
    (htrace : ∀ δ : B, clK (P δ) = ∑ q : G ⧸ H, ρ (Quotient.out q) (clE δ))
    {w : W} (hw : w ∈ ρ.invariants) (hwE : w ∈ Submodule.span R (Set.range clE)) :
    w ∈ Submodule.span R (Set.range clK) := by
  refine span_range_descent clK clE P ρ (fun q : G ⧸ H => Quotient.out q) ?_ htrace hw hwE
  refine Nat.cast_ne_zero.mpr ?_
  rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
  exact Subgroup.FiniteIndex.index_ne_zero

end Averaging

/-! ### 2. The Stacks transfer along a finite field extension -/

section StacksTransfer

variable (k E : Type u) [Field k] [Field E] [Algebra k E] [FiniteDimensional k E]
  {X : Scheme.{u}} (f : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType f]

/-- The projection `π : X_E ⟶ X` is finite locally free of rank `[E : k]` (Stacks 02KA). -/
instance instIsFiniteLocallyFreeOfRankProj :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (pullback.fst f (fieldExtensionBaseChangeSituation k E).g) (Module.finrank k E) :=
  isFiniteLocallyFreeOfRank_pullbackFst_fieldExtension k E f

instance instLocallyOfFiniteTypeProj :
    LocallyOfFiniteType (pullback.fst f (fieldExtensionBaseChangeSituation k E).g) :=
  Stacks.Morphisms.locallyOfFiniteType_of_isFiniteLocallyFreeOfRank _ (Module.finrank k E)

instance instFlatProj : Flat (pullback.fst f (fieldExtensionBaseChangeSituation k E).g) :=
  Stacks.Morphisms.flat_of_isFiniteLocallyFreeOfRank _ (Module.finrank k E)

instance instIsProperProj : IsProper (pullback.fst f (fieldExtensionBaseChangeSituation k E).g) :=
  Stacks.Morphisms.isProper_of_isFiniteLocallyFreeOfRank _ (Module.finrank k E)

variable (i : ℤ)

/-- The identification of cycles of `X_E` over `Spec E` with cycles of `X_E` over `Spec k`
(through `π ≫ f`): the same coefficient functions. -/
def cycleLift :
    CycleGroup (fieldChowSituation E)
        (pullback.snd f (fieldExtensionBaseChangeSituation k E).g) i →+
      CycleGroup (fieldChowSituation k)
        (pullback.fst f (fieldExtensionBaseChangeSituation k E).g ≫ f) i where
  toFun c := ⟨c.1, mem_cyclesOfDimension_pullbackFst_comp_fieldExtension k E f i c⟩
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

theorem cycleLift_mem_rationalEquivalences
    {a : CycleGroup (fieldChowSituation E)
      (pullback.snd f (fieldExtensionBaseChangeSituation k E).g) i}
    (ha : a ∈ rationalEquivalences (fieldChowSituation E)
      (pullback.snd f (fieldExtensionBaseChangeSituation k E).g) i) :
    cycleLift k E f i a ∈ rationalEquivalences (fieldChowSituation k)
      (pullback.fst f (fieldExtensionBaseChangeSituation k E).g ≫ f) i :=
  (isRationallyEquivalentToZero_congr (fieldChowSituation E) (fieldChowSituation k)
    (pullback.snd f (fieldExtensionBaseChangeSituation k E).g)
    (pullback.fst f (fieldExtensionBaseChangeSituation k E).g ≫ f)
    (relativeDimension_comp_pullbackSnd_fieldExtension k E f) i a (cycleLift k E f i a) rfl).1 ha

/-- The identification `CH_i(X_E / E) ≃ CH_i(X_E / k)` (here only the homomorphism in the
direction needed): a class of `X_E` over `Spec E` is a class of `X_E` over `Spec k`. -/
def chowLift :
    chowGroup (fieldChowSituation E)
        (pullback.snd f (fieldExtensionBaseChangeSituation k E).g) i →+
      chowGroup (fieldChowSituation k)
        (pullback.fst f (fieldExtensionBaseChangeSituation k E).g ≫ f) i :=
  QuotientAddGroup.map _ _ (cycleLift k E f i)
    (fun _ ha => cycleLift_mem_rationalEquivalences k E f i ha)

/-- **The transfer** `π_* : CH_i(X_E) →+ CH_i(X)` for `π : X_E ⟶ X` the projection of the base
change along a finite field extension: the Stacks proper pushforward on Chow groups
(Stacks 02S2, 0GU8) composed with `chowLift`. -/
def pushforward :
    chowGroup (fieldChowSituation E)
        (pullback.snd f (fieldExtensionBaseChangeSituation k E).g) i →+
      chowGroup (fieldChowSituation k) f i :=
  (properChowPushforward (fieldChowSituation k)
    (pullback.fst f (fieldExtensionBaseChangeSituation k E).g ≫ f) f
    (pullback.fst f (fieldExtensionBaseChangeSituation k E).g) rfl i
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper (fieldChowSituation k)
      (pullback.fst f (fieldExtensionBaseChangeSituation k E).g ≫ f) f
      (pullback.fst f (fieldExtensionBaseChangeSituation k E).g) rfl i)).comp
    (chowLift k E f i)

/-- The flat pullback `π^* : CH_i(X) →+ CH_i(X_E)` along the projection of a field-extension
base change (Stacks 0FVJ, on classes). -/
abbrev baseChangeMap :
    chowGroup (fieldChowSituation k) f i →+
      chowGroup (fieldChowSituation E)
        (pullback.snd f (fieldExtensionBaseChangeSituation k E).g) i :=
  baseChangeChowPullbackOfIsPullback (fieldExtensionBaseChangeSituation k E) rfl f
    (IsPullback.of_hasPullback f (fieldExtensionBaseChangeSituation k E).g) i

/-- **Push-pull on Chow classes.** `π_* π^* α = [E : k] • α` for `α ∈ CH_i(X)` (Stacks 02RH,
`properPushforward_flatPullback_of_isFiniteLocallyFreeOfRank`, lifted to classes). -/
theorem pushforward_baseChange (α : chowGroup (fieldChowSituation k) f i) :
    pushforward k E f i (baseChangeMap k E f i α) = (Module.finrank k E : ℤ) • α := by
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective
    (rationalEquivalences (fieldChowSituation k) f i) α
  have hrd : AlgebraicGeometry.RelativeDimension
      (pullback.fst f (fieldExtensionBaseChangeSituation k E).g) 0 :=
    Stacks.Morphisms.relativeDimension_zero_of_isFiniteLocallyFreeOfRank _ (Module.finrank k E)
  have hcast : i + ((0 : ℕ) : ℤ) = i := by simp
  have hlift : cycleLift k E f i
      (baseChangeCyclePullbackOfIsPullback (fieldExtensionBaseChangeSituation k E) rfl f
        (IsPullback.of_hasPullback f (fieldExtensionBaseChangeSituation k E).g) i z) =
      hcast ▸ flatPullback (fieldChowSituation k)
        (pullback.fst f (fieldExtensionBaseChangeSituation k E).g ≫ f) f
        (pullback.fst f (fieldExtensionBaseChangeSituation k E).g) rfl 0 hrd i z := by
    apply Subtype.ext
    rw [val_cycleGroup_cast]
    exact val_baseChangeCyclePullbackOfIsPullback_eq_val_flatPullback k E f hrd i z
  have hπP : properPushforward (fieldChowSituation k)
      (pullback.fst f (fieldExtensionBaseChangeSituation k E).g ≫ f) f
      (pullback.fst f (fieldExtensionBaseChangeSituation k E).g) rfl i
      (hcast ▸ flatPullback (fieldChowSituation k)
        (pullback.fst f (fieldExtensionBaseChangeSituation k E).g ≫ f) f
        (pullback.fst f (fieldExtensionBaseChangeSituation k E).g) rfl 0 hrd i z) =
      (Module.finrank k E : ℤ) • z := by
    rw [← properPushforward_flatPullback_of_isFiniteLocallyFreeOfRank (fieldChowSituation k)
      (pullback.fst f (fieldExtensionBaseChangeSituation k E).g ≫ f) f
      (pullback.fst f (fieldExtensionBaseChangeSituation k E).g) (Module.finrank k E) rfl i
      hcast z]
    apply Subtype.ext
    rw [val_cycleGroup_cast]
    change AlgebraicCycle.map (pullback.fst f (fieldExtensionBaseChangeSituation k E).g) _ _
        (hcast ▸ flatPullback (fieldChowSituation k)
          (pullback.fst f (fieldExtensionBaseChangeSituation k E).g ≫ f) f
          (pullback.fst f (fieldExtensionBaseChangeSituation k E).g) rfl 0 hrd i z).1 =
      AlgebraicCycle.map (pullback.fst f (fieldExtensionBaseChangeSituation k E).g) _ _ _
    rw [val_cycleGroup_cast]
  have h1 : baseChangeMap k E f i
      (QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) f i) z) =
      QuotientAddGroup.mk'
        (rationalEquivalences (fieldChowSituation E)
          (pullback.snd f (fieldExtensionBaseChangeSituation k E).g) i)
        (baseChangeCyclePullbackOfIsPullback (fieldExtensionBaseChangeSituation k E) rfl f
          (IsPullback.of_hasPullback f (fieldExtensionBaseChangeSituation k E).g) i z) :=
    baseChangeChowPullbackOfIsPullback_mk (fieldExtensionBaseChangeSituation k E) rfl f _ i z
  rw [h1, ← map_zsmul (QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) f i)),
    ← hπP, ← hlift]
  rfl

/-- If `δ = π^* α` comes from `X`, it is norm-invariant: `π^* π_* δ = [E:k] • δ`. -/
theorem baseChange_pushforward_of_mem_range
    {δ : chowGroup (fieldChowSituation E)
      (pullback.snd f (fieldExtensionBaseChangeSituation k E).g) i}
    (hδ : δ ∈ (baseChangeMap k E f i).range) :
    baseChangeMap k E f i (pushforward k E f i δ) = (Module.finrank k E : ℤ) • δ := by
  obtain ⟨α, rfl⟩ := hδ
  rw [pushforward_baseChange, map_zsmul]

/-- **Descent with rational coefficients, at the level of Chow classes.** If a class `δ` of
`X_E` is norm-invariant, `π^* π_* δ = [E:k] • δ`, then `[E:k] • δ` comes from `X`, namely
`[E:k] • δ = π^*(π_* δ)`: in `CH ⊗ ℚ`, `δ = π^*((1/[E:k]) π_* δ)`. -/
theorem exists_baseChange_eq_finrank_smul_of_norm_eq
    {δ : chowGroup (fieldChowSituation E)
      (pullback.snd f (fieldExtensionBaseChangeSituation k E).g) i}
    (hδ : baseChangeMap k E f i (pushforward k E f i δ) = (Module.finrank k E : ℤ) • δ) :
    ∃ α : chowGroup (fieldChowSituation k) f i,
      baseChangeMap k E f i α = (Module.finrank k E : ℤ) • δ :=
  ⟨pushforward k E f i δ, hδ⟩

/-- **The descent theorem for cycle classes (manuscript, proof of Corollary 6.6, last
sentence), with the cycle class maps and the trace formula as hypotheses.**

`ρ` is a representation of `G` on an `R`-vector space `W` (in the application `G = Gal(Q̄/K)`,
`W = H^{2c}_{ét}(J_{Q̄}, ℚ_ℓ(c))`); `clK`, `clE` are cycle class maps on the Stacks Chow groups
of `X` and of `X_E` (hypotheses: see the module docstring, items 1 and 2) satisfying the trace
formula `clK (π_* δ) = ∑_j ρ (g j) (clE δ)`. Then every `G`-invariant vector of `W` in the span of
the classes of cycles over `E` lies in the span of the classes of cycles over `k`. -/
theorem mem_span_range_cl_of_invariant {R G W : Type*} [Field R] [Group G] [AddCommGroup W]
    [Module R W]
    (clK : chowGroup (fieldChowSituation k) f i →+ W)
    (clE : chowGroup (fieldChowSituation E)
      (pullback.snd f (fieldExtensionBaseChangeSituation k E).g) i →+ W)
    (ρ : Representation R G W) {ι : Type*} [Fintype ι] (g : ι → G)
    (hι : (Fintype.card ι : R) ≠ 0)
    (htrace : ∀ δ, clK (pushforward k E f i δ) = ∑ j, ρ (g j) (clE δ))
    {w : W} (hw : w ∈ ρ.invariants) (hwE : w ∈ Submodule.span R (Set.range clE)) :
    w ∈ Submodule.span R (Set.range clK) :=
  span_range_descent clK clE (pushforward k E f i) ρ g hι htrace hw hwE

end StacksTransfer

end CycleDescent

end ArithmeticOfJacobiPolynomials

end
