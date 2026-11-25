/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Algebra.EllAdicLie
public import ArithmeticOfJacobiPolynomials.Algebra.SymplecticSimilitude
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The `ℓ`-adic Lie algebras of the symplectic and similitude groups

Let `p` be a prime, `V` a finite-dimensional normed `ℚ_[p]`-space, `W` a `ℚ_[p]`-vector space and
`ψ : V × V → W` a `ℚ_[p]`-bilinear map (in the application, the Weil pairing on `V_ℓ` with values
in `ℚ_ℓ(1)`). We work in the complete normed `ℚ_[p]`-algebra `V →L[ℚ_[p]] V` and transport the
groups `Sp(V, ψ)` and `GSp(V, ψ)` of `ArithmeticOfJacobiPolynomials.SymplecticSimilitude` to its
unit group along
`ArithmeticOfJacobiPolynomials.unitsToLinearEquiv` (`ArithmeticOfJacobiPolynomials.symplecticUnits`,
`ArithmeticOfJacobiPolynomials.similitudeUnits`).

The `p`-adic Lie algebra (`ArithmeticOfJacobiPolynomials.ellAdicLie`, defined via `exp (t • X)` for
small `t`) is
computed:

* `ArithmeticOfJacobiPolynomials.ellAdicLie_symplecticUnits`: `Lie(Sp(V, ψ)) = 𝔰𝔭(V, ψ)`;
* `ArithmeticOfJacobiPolynomials.ellAdicLie_similitudeUnits`: `Lie(GSp(V, ψ)) = 𝔤𝔰𝔭(V, ψ)`, and
  `ArithmeticOfJacobiPolynomials.ellAdicLie_similitudeUnits_eq_span_id_sup`:
  `Lie(GSp(V, ψ)) = ℚ_[p] · id ⊕ 𝔰𝔭(V, ψ)`;
* `ArithmeticOfJacobiPolynomials.ellAdicLie_subset_of_le_similitudeUnits` and
  `ArithmeticOfJacobiPolynomials.ellAdicLie_eq_span_id_sup_iff`: for a subgroup `H ≤ GSp(V, ψ)`,
  `Lie(H) ⊆ 𝔤𝔰𝔭`,
  and `Lie(H) = ℚ_[p] · id ⊕ 𝔰𝔭` iff `Lie(H) = Lie(GSp(V, ψ))`.

No hypothesis on `ψ` (nondegeneracy, alternation) is needed. The inclusion `𝔤𝔰𝔭 ⊆ Lie` uses that
pairs `(B, C)` with `ψ (B x) z = ψ x (C z)` form a (closed, finite-dimensional) subspace stable
under powers, hence under `exp`; the reverse inclusion differentiates
`t ↦ χ (ψ (exp (t • X) x) (exp (t • X) y))` at `t = 0` for linear functionals `χ` on `W`.
This is the Lie-algebra statement "`ℚ_ℓ Id ⊕ 𝔰𝔭(V_ℓ, ψ_ℓ)`" of the manuscript (Corollary 6.6).
-/

public section

open NormedSpace Filter Topology

namespace ArithmeticOfJacobiPolynomials

variable {p : ℕ} [hp : Fact p.Prime]
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℚ_[p] V] [AddCommGroup W]
  [Module ℚ_[p] W]

section Transport

variable (p V) in
/-- A unit of `V →L[ℚ_[p]] V` as a linear automorphism of `V`. -/
@[expose]
noncomputable def unitsToLinearEquiv : (V →L[ℚ_[p]] V)ˣ →* (V ≃ₗ[ℚ_[p]] V) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv ℚ_[p] V).toMonoidHom.comp
    (Units.map (ContinuousLinearMap.toLinearMapRingHom : (V →L[ℚ_[p]] V) →+* _).toMonoidHom)

theorem unitsToLinearEquiv_apply (u : (V →L[ℚ_[p]] V)ˣ) (x : V) :
    unitsToLinearEquiv p V u x = (u : V →L[ℚ_[p]] V) x :=
  rfl

/-- The symplectic group `Sp(V, ψ)` inside the units of `V →L[ℚ_[p]] V`. -/
@[expose]
noncomputable def symplecticUnits (ψ : V →ₗ[ℚ_[p]] V →ₗ[ℚ_[p]] W) :
    Subgroup (V →L[ℚ_[p]] V)ˣ :=
  (symplecticGroup ψ).comap (unitsToLinearEquiv p V)

/-- The similitude group `GSp(V, ψ)` inside the units of `V →L[ℚ_[p]] V`. -/
@[expose]
noncomputable def similitudeUnits (ψ : V →ₗ[ℚ_[p]] V →ₗ[ℚ_[p]] W) :
    Subgroup (V →L[ℚ_[p]] V)ˣ :=
  (similitudeGroup ψ).comap (unitsToLinearEquiv p V)

theorem mem_symplecticUnits {ψ : V →ₗ[ℚ_[p]] V →ₗ[ℚ_[p]] W} {u : (V →L[ℚ_[p]] V)ˣ} :
    u ∈ symplecticUnits ψ ↔
      ∀ x y, ψ ((u : V →L[ℚ_[p]] V) x) ((u : V →L[ℚ_[p]] V) y) = ψ x y :=
  Iff.rfl

theorem mem_similitudeUnits {ψ : V →ₗ[ℚ_[p]] V →ₗ[ℚ_[p]] W} {u : (V →L[ℚ_[p]] V)ˣ} :
    u ∈ similitudeUnits ψ ↔
      ∃ c : ℚ_[p]ˣ, ∀ x y,
        ψ ((u : V →L[ℚ_[p]] V) x) ((u : V →L[ℚ_[p]] V) y) = (c : ℚ_[p]) • ψ x y :=
  Iff.rfl

theorem symplecticUnits_le_similitudeUnits (ψ : V →ₗ[ℚ_[p]] V →ₗ[ℚ_[p]] W) :
    symplecticUnits ψ ≤ similitudeUnits ψ :=
  Subgroup.comap_mono (symplecticGroup_le_similitudeGroup ψ)

end Transport

section Adjoint

variable (V) in
/-- The pairs `(B, C)` of operators with `ψ (B x) z = ψ x (C z)` (`C` is a right adjoint of `B`
for `ψ`), a subspace of `(V →L V) × (V →L V)`. -/
@[expose]
def adjointPairs (ψ : V →ₗ[ℚ_[p]] V →ₗ[ℚ_[p]] W) :
    Submodule ℚ_[p] ((V →L[ℚ_[p]] V) × (V →L[ℚ_[p]] V)) where
  carrier := {q | ∀ x z, ψ (q.1 x) z = ψ x (q.2 z)}
  add_mem' := by
    intro a b ha hb x z
    simp only [Prod.fst_add, Prod.snd_add, add_apply, map_add,
      LinearMap.add_apply]
    rw [ha x z, hb x z]
  zero_mem' := by
    intro x z
    simp only [Prod.fst_zero, Prod.snd_zero, zero_apply, map_zero,
      LinearMap.zero_apply]
  smul_mem' := by
    intro c a ha x z
    simp only [Prod.smul_fst, Prod.smul_snd, smul_apply, map_smul,
      LinearMap.smul_apply]
    rw [ha x z]

theorem mem_adjointPairs {ψ : V →ₗ[ℚ_[p]] V →ₗ[ℚ_[p]] W}
    {q : (V →L[ℚ_[p]] V) × (V →L[ℚ_[p]] V)} :
    q ∈ adjointPairs V ψ ↔ ∀ x z, ψ (q.1 x) z = ψ x (q.2 z) :=
  Iff.rfl

theorem pow_mem_adjointPairs {ψ : V →ₗ[ℚ_[p]] V →ₗ[ℚ_[p]] W} {B C : V →L[ℚ_[p]] V}
    (h : (B, C) ∈ adjointPairs V ψ) (n : ℕ) : (B ^ n, C ^ n) ∈ adjointPairs V ψ := by
  induction n with
  | zero =>
    refine mem_adjointPairs.2 fun x z => ?_
    simp only [pow_zero, one_apply_eq_self]
  | succ n ih =>
    refine mem_adjointPairs.2 fun x z => ?_
    change ψ ((B ^ (n + 1)) x) z = ψ x ((C ^ (n + 1)) z)
    rw [pow_succ, pow_succ', mul_apply_eq_comp, mul_apply_eq_comp]
    exact (mem_adjointPairs.1 ih (B x) z).trans (mem_adjointPairs.1 h x ((C ^ n) z))

end Adjoint

variable [FiniteDimensional ℚ_[p] V]

section AdjointExp

/-- **Adjoint pairs are stable under the exponential**: if `ψ (B x) z = ψ x (C z)` and `B`, `C`
lie in the disc of convergence, then `ψ (exp B x) z = ψ x (exp C z)`. -/
theorem exp_mem_adjointPairs {ψ : V →ₗ[ℚ_[p]] V →ₗ[ℚ_[p]] W} {B C : V →L[ℚ_[p]] V}
    (h : (B, C) ∈ adjointPairs V ψ)
    (hB : B ∈ Metric.eball (0 : V →L[ℚ_[p]] V) (expSeries ℚ_[p] (V →L[ℚ_[p]] V)).radius)
    (hC : C ∈ Metric.eball (0 : V →L[ℚ_[p]] V) (expSeries ℚ_[p] (V →L[ℚ_[p]] V)).radius) :
    (exp B, exp C) ∈ adjointPairs V ψ := by
  have := FiniteDimensional.complete ℚ_[p] V
  have hs := (expSeries_hasSum_exp_of_mem_ball' (𝕂 := ℚ_[p]) B hB).prodMk
    (expSeries_hasSum_exp_of_mem_ball' (𝕂 := ℚ_[p]) C hC)
  refine (Submodule.closed_of_finiteDimensional (adjointPairs V ψ)).mem_of_tendsto
    hs.tendsto_sum_nat (Eventually.of_forall fun n => ?_)
  refine Submodule.sum_mem _ fun i _ => ?_
  have hi := (adjointPairs V ψ).smul_mem ((i.factorial : ℚ_[p])⁻¹) (pow_mem_adjointPairs h i)
  exact hi

end AdjointExp

section Derivative

/-- **The derivative of `ψ` along a one-parameter subgroup.** For a linear functional `χ` on `W`,
`t ↦ χ (ψ (exp (t • X) x) (exp (t • X) y))` has derivative `χ (ψ (X x) y + ψ x (X y))` at `0`. -/
theorem hasDerivAt_dual_bilin_exp_smul (ψ : V →ₗ[ℚ_[p]] V →ₗ[ℚ_[p]] W)
    (χ : Module.Dual ℚ_[p] W) (X : V →L[ℚ_[p]] V) (x y : V) :
    HasDerivAt (fun t : ℚ_[p] => χ (ψ (exp (t • X) x) (exp (t • X) y)))
      (χ (ψ (X x) y + ψ x (X y))) 0 := by
  have := FiniteDimensional.complete ℚ_[p] V
  let B : V →L[ℚ_[p]] V →L[ℚ_[p]] ℚ_[p] :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap :
          (V →ₗ[ℚ_[p]] ℚ_[p]) ≃ₗ[ℚ_[p]] V →L[ℚ_[p]] ℚ_[p]).toLinearMap ∘ₗ ψ.compr₂ χ)
  have hB : ∀ v w, B v w = χ (ψ v w) := fun v w => rfl
  have h0 : (0 : ℚ_[p]) • X ∈
      Metric.eball (0 : V →L[ℚ_[p]] V) (expSeries ℚ_[p] (V →L[ℚ_[p]] V)).radius := by
    rw [zero_smul]
    exact Metric.mem_eball_self (padic_expSeries_radius_pos p _)
  have hE : HasDerivAt (fun t : ℚ_[p] => exp (t • X)) X 0 := by
    have := hasDerivAt_exp_smul_const_of_mem_ball (𝕂 := ℚ_[p]) X 0 h0
    rwa [zero_smul, exp_zero, one_mul] at this
  have hu : ∀ v : V, HasDerivAt (fun t : ℚ_[p] => exp (t • X) v) (X v) 0 := fun v =>
    HasFDerivAt.comp_hasDerivAt (0 : ℚ_[p]) (ContinuousLinearMap.apply ℚ_[p] V v).hasFDerivAt hE
  have hc : HasDerivAt (fun t : ℚ_[p] => B (exp (t • X) x)) (B (X x)) 0 :=
    HasFDerivAt.comp_hasDerivAt (0 : ℚ_[p]) B.hasFDerivAt (hu x)
  have h := hc.clm_apply (hu y)
  simp only [hB, zero_smul, exp_zero, one_apply_eq_self] at h
  rw [map_add]
  exact h

/-- In a vector space, a vector killed by every linear functional is zero. -/
theorem eq_of_forall_dual_eq {w w' : W} (h : ∀ χ : Module.Dual ℚ_[p] W, χ w = χ w') : w = w' := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℚ_[p]]
  intro χ
  rw [map_sub, h χ, sub_self]

end Derivative

section Symplectic

/-- **`𝔰𝔭 ⊆ Lie(Sp)`**: if `A ∈ 𝔰𝔭(V, ψ)`, then `exp (t • A)` is symplectic for all small `t`. -/
theorem mem_ellAdicLie_symplecticUnits_of_mem {ψ : V →ₗ[ℚ_[p]] V →ₗ[ℚ_[p]] W}
    {X : V →L[ℚ_[p]] V} (hX : (X : Module.End ℚ_[p] V) ∈ symplecticLie ψ) :
    X ∈ ellAdicLie p (symplecticUnits ψ) := by
  have := FiniteDimensional.complete ℚ_[p] V
  rw [mem_ellAdicLie_iff]
  have hadj : (X, -X) ∈ adjointPairs V ψ := mem_adjointPairs.2 fun x z => by
    have h := mem_symplecticLie.1 hX x z
    change ψ (X x) z = ψ x ((-X) z)
    rw [neg_apply, map_neg]
    exact eq_neg_of_add_eq_zero_left h
  filter_upwards [padic_eventually_smul_mem_eball (p := p) X,
    padic_eventually_smul_mem_eball (p := p) (-X),
    padic_eventually_exp_smul_mul_exp_neg_smul (p := p) X] with t h1 h2 h3
  refine ⟨⟨exp (t • X), exp ((-t) • X), h3.1, h3.2⟩, mem_symplecticUnits.2 fun x y => ?_, rfl⟩
  change ψ (exp (t • X) x) (exp (t • X) y) = ψ x y
  have hadj' : (t • X, t • -X) ∈ adjointPairs V ψ := (adjointPairs V ψ).smul_mem t hadj
  have hexp := exp_mem_adjointPairs hadj' h1 h2
  rw [mem_adjointPairs.1 hexp x (exp (t • X) y), ← mul_apply_eq_comp, smul_neg,
    ← neg_smul, h3.2, one_apply_eq_self]

/-- **`Lie(Sp) ⊆ 𝔰𝔭`**: if `exp (t • X)` is symplectic for all small `t`, then `X ∈ 𝔰𝔭(V, ψ)`. -/
theorem mem_symplecticLie_of_mem_ellAdicLie {ψ : V →ₗ[ℚ_[p]] V →ₗ[ℚ_[p]] W}
    {X : V →L[ℚ_[p]] V} (hX : X ∈ ellAdicLie p (symplecticUnits ψ)) :
    (X : Module.End ℚ_[p] V) ∈ symplecticLie ψ := by
  refine mem_symplecticLie.2 fun x y => eq_of_forall_dual_eq (p := p) fun χ => ?_
  have hconst : (fun t : ℚ_[p] => χ (ψ (exp (t • X) x) (exp (t • X) y))) =ᶠ[𝓝 0]
      fun _ => χ (ψ x y) := by
    filter_upwards [mem_ellAdicLie_iff.1 hX] with t ht
    obtain ⟨u, hu, he⟩ := ht
    have h := mem_symplecticUnits.1 hu x y
    rw [he] at h
    rw [h]
  have hd := (hasDerivAt_const (0 : ℚ_[p]) (χ (ψ x y))).congr_of_eventuallyEq hconst
  rw [map_zero]
  exact (hasDerivAt_dual_bilin_exp_smul ψ χ X x y).unique hd

/-- **`Lie(Sp(V, ψ)) = 𝔰𝔭(V, ψ)`.** -/
theorem ellAdicLie_symplecticUnits (ψ : V →ₗ[ℚ_[p]] V →ₗ[ℚ_[p]] W) :
    ellAdicLie p (symplecticUnits ψ) =
      {X : V →L[ℚ_[p]] V | (X : Module.End ℚ_[p] V) ∈ symplecticLie ψ} :=
  Set.ext fun _ => ⟨mem_symplecticLie_of_mem_ellAdicLie, mem_ellAdicLie_symplecticUnits_of_mem⟩

end Symplectic

section Similitude

/-- **`𝔤𝔰𝔭 ⊆ Lie(GSp)`**: if `ψ (A x) y + ψ x (A y) = c • ψ x y`, then for all small `t`,
`exp (t • A)` is a similitude with multiplier `exp (t c)`. -/
theorem mem_ellAdicLie_similitudeUnits_of_mem {ψ : V →ₗ[ℚ_[p]] V →ₗ[ℚ_[p]] W}
    {X : V →L[ℚ_[p]] V} (hX : (X : Module.End ℚ_[p] V) ∈ similitudeLie ψ) :
    X ∈ ellAdicLie p (similitudeUnits ψ) := by
  have := FiniteDimensional.complete ℚ_[p] V
  rw [mem_ellAdicLie_iff]
  obtain ⟨c, hc⟩ := mem_similitudeLie.1 hX
  have hadj : (X, c • 1 - X) ∈ adjointPairs V ψ := mem_adjointPairs.2 fun x z => by
    have h := hc x z
    change ψ (X x) z = ψ x ((c • 1 - X) z)
    rw [sub_apply, smul_apply,
      one_apply_eq_self, map_sub, map_smul]
    exact eq_sub_of_add_eq h
  have hcomm : ∀ t : ℚ_[p], Commute (t • (c • 1 - X)) (t • X) := fun t =>
    ((((Commute.one_left X).smul_left c).sub_left (Commute.refl X)).smul_left t).smul_right t
  have hsum : ∀ t : ℚ_[p],
      t • (c • 1 - X) + t • X = algebraMap ℚ_[p] (V →L[ℚ_[p]] V) (t • c) := fun t => by
    rw [← smul_add, sub_add_cancel, Algebra.algebraMap_eq_smul_one, smul_smul, smul_eq_mul]
  filter_upwards [padic_eventually_smul_mem_eball (p := p) X,
    padic_eventually_smul_mem_eball (p := p) (c • 1 - X),
    padic_eventually_smul_mem_eball (p := p) (A := ℚ_[p]) c,
    padic_eventually_exp_smul_mul_exp_neg_smul (p := p) X,
    padic_eventually_exp_smul_mul_exp_neg_smul (p := p) (A := ℚ_[p]) c] with t h1 h2 h3 h4 h5
  have he : exp (t • c) ≠ 0 := left_ne_zero_of_mul_eq_one h5.1
  refine ⟨⟨exp (t • X), exp ((-t) • X), h4.1, h4.2⟩,
    mem_similitudeUnits.2 ⟨Units.mk0 _ he, fun x y => ?_⟩, rfl⟩
  change ψ (exp (t • X) x) (exp (t • X) y) = exp (t • c) • ψ x y
  have hadj' : (t • X, t • (c • 1 - X)) ∈ adjointPairs V ψ := (adjointPairs V ψ).smul_mem t hadj
  have hexp := exp_mem_adjointPairs hadj' h1 h2
  rw [mem_adjointPairs.1 hexp x (exp (t • X) y), ← mul_apply_eq_comp,
    ← exp_add_of_commute_of_mem_ball (hcomm t) h2 h1, hsum t,
    ← algebraMap_exp_comm_of_mem_ball (t • c) h3, Algebra.algebraMap_eq_smul_one,
    smul_apply, one_apply_eq_self, map_smul]

/-- **`Lie(GSp) ⊆ 𝔤𝔰𝔭`**: if `exp (t • X)` is a similitude for all small `t`, then
`X ∈ 𝔤𝔰𝔭(V, ψ)` (the constant is the derivative at `0` of the multiplier). -/
theorem mem_similitudeLie_of_mem_ellAdicLie {ψ : V →ₗ[ℚ_[p]] V →ₗ[ℚ_[p]] W}
    {X : V →L[ℚ_[p]] V} (hX : X ∈ ellAdicLie p (similitudeUnits ψ)) :
    (X : Module.End ℚ_[p] V) ∈ similitudeLie ψ := by
  by_cases hψ : ∀ x y, ψ x y = 0
  · exact mem_similitudeLie.2 ⟨0, fun x y => by simp only [hψ, add_zero, smul_zero]⟩
  push Not at hψ
  obtain ⟨x0, y0, h0⟩ := hψ
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℚ_[p] W, φ (ψ x0 y0) = 1 := by
    have h : ¬ ∀ φ : Module.Dual ℚ_[p] W, φ (ψ x0 y0) = 0 := fun h =>
      h0 ((Module.forall_dual_apply_eq_zero_iff ℚ_[p] _).1 h)
    push Not at h
    obtain ⟨φ, hφ⟩ := h
    exact ⟨(φ (ψ x0 y0))⁻¹ • φ, by rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hφ]⟩
  refine mem_similitudeLie.2 ⟨φ (ψ (X x0) y0 + ψ x0 (X y0)), fun x y =>
    eq_of_forall_dual_eq (p := p) fun χ => ?_⟩
  have heq : (fun t : ℚ_[p] => χ (ψ (exp (t • X) x) (exp (t • X) y))) =ᶠ[𝓝 0]
      fun t => φ (ψ (exp (t • X) x0) (exp (t • X) y0)) * χ (ψ x y) := by
    filter_upwards [mem_ellAdicLie_iff.1 hX] with t ht
    obtain ⟨u, hu, he⟩ := ht
    obtain ⟨d, hd⟩ := mem_similitudeUnits.1 hu
    have h1 := hd x y
    have h2 := hd x0 y0
    rw [he] at h1 h2
    rw [h1, h2, map_smul, map_smul, hφ, smul_eq_mul, smul_eq_mul, mul_one]
  have hd := ((hasDerivAt_dual_bilin_exp_smul ψ φ X x0 y0).mul_const
    (χ (ψ x y))).congr_of_eventuallyEq heq
  rw [map_smul, smul_eq_mul]
  exact (hasDerivAt_dual_bilin_exp_smul ψ χ X x y).unique hd

/-- **`Lie(GSp(V, ψ)) = 𝔤𝔰𝔭(V, ψ)`.** -/
theorem ellAdicLie_similitudeUnits (ψ : V →ₗ[ℚ_[p]] V →ₗ[ℚ_[p]] W) :
    ellAdicLie p (similitudeUnits ψ) =
      {X : V →L[ℚ_[p]] V | (X : Module.End ℚ_[p] V) ∈ similitudeLie ψ} :=
  Set.ext fun _ => ⟨mem_similitudeLie_of_mem_ellAdicLie, mem_ellAdicLie_similitudeUnits_of_mem⟩

/-- **`Lie(GSp(V, ψ)) = ℚ_[p] · id ⊕ 𝔰𝔭(V, ψ)`** (the sum is direct when `ψ ≠ 0`, by
`disjoint_span_id_symplecticLie`). -/
theorem ellAdicLie_similitudeUnits_eq_span_id_sup (ψ : V →ₗ[ℚ_[p]] V →ₗ[ℚ_[p]] W) :
    ellAdicLie p (similitudeUnits ψ) =
      {X : V →L[ℚ_[p]] V | (X : Module.End ℚ_[p] V) ∈
        (ℚ_[p] ∙ (LinearMap.id : Module.End ℚ_[p] V)) ⊔ symplecticLie ψ} := by
  rw [ellAdicLie_similitudeUnits, similitudeLie_eq_span_id_sup_symplecticLie ψ two_ne_zero]

/-- The Lie algebra of any subgroup `H ≤ GSp(V, ψ)` lies in `𝔤𝔰𝔭(V, ψ)`. -/
theorem ellAdicLie_subset_of_le_similitudeUnits {ψ : V →ₗ[ℚ_[p]] V →ₗ[ℚ_[p]] W}
    {H : Subgroup (V →L[ℚ_[p]] V)ˣ} (hH : H ≤ similitudeUnits ψ) :
    ellAdicLie p H ⊆ {X : V →L[ℚ_[p]] V | (X : Module.End ℚ_[p] V) ∈ similitudeLie ψ} :=
  (ellAdicLie_mono hH).trans (ellAdicLie_similitudeUnits ψ).subset

/-- A subgroup `H` has Lie algebra `ℚ_[p] · id ⊕ 𝔰𝔭(V, ψ)` iff it has the Lie algebra of
`GSp(V, ψ)`. -/
theorem ellAdicLie_eq_span_id_sup_iff (ψ : V →ₗ[ℚ_[p]] V →ₗ[ℚ_[p]] W)
    (H : Subgroup (V →L[ℚ_[p]] V)ˣ) :
    ellAdicLie p H = {X : V →L[ℚ_[p]] V | (X : Module.End ℚ_[p] V) ∈
        (ℚ_[p] ∙ (LinearMap.id : Module.End ℚ_[p] V)) ⊔ symplecticLie ψ} ↔
      ellAdicLie p H = ellAdicLie p (similitudeUnits ψ) := by
  rw [ellAdicLie_similitudeUnits_eq_span_id_sup]

end Similitude

end ArithmeticOfJacobiPolynomials
