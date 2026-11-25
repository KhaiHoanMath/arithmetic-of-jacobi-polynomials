/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Algebra.EllAdicLie
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The `ℓ`-adic Lie algebra of a closed subgroup is a `ℚ_ℓ`-Lie subalgebra

Let `p` be a prime, `A` a finite-dimensional normed `ℚ_[p]`-algebra (e.g. `V →L[ℚ_[p]] V` for a
finite-dimensional normed space `V`, or a matrix algebra) and `G` a subgroup of `Aˣ` which is
closed for the topology of `Aˣ`. We show that
`Lie(G) = {X | exp (t • X) ∈ G for t near 0}` (`ArithmeticOfJacobiPolynomials.ellAdicLie`) is a
`ℚ_[p]`-Lie
subalgebra of `A` (bracket `⁅X, Y⁆ = X * Y - Y * X`).

The real-analytic proof (Trotter's product formula `(exp(X/n) exp(Y/n))ⁿ → exp(X + Y)`) is not
available `p`-adically: integer powers can only shrink `p`-adically. Instead:

* `ArithmeticOfJacobiPolynomials.mem_ellAdicLie_of_exp_mem`: if `c` lies in the disc of convergence
and
  `exp c ∈ G`, then `c ∈ Lie(G)`. Indeed `exp (n • c) = (exp c)ⁿ ∈ G` for `n : ℕ`, and
  `ℕ` is dense in `ℤ_[p]`, so `exp (μ • c) ∈ G` for every `μ ∈ ℤ_[p]` by closedness.
* `ArithmeticOfJacobiPolynomials.span_ellAdicLie_subset`: let `X₁, …, Xₘ ∈ Lie(G)` be a basis of
the span of
  `Lie(G)`. The map `t ↦ log (exp (t₁ X₁) ⋯ exp (tₘ Xₘ))` (`log` the local inverse of `exp`
  at `0`, from the inverse function theorem) takes values in `Lie(G)` (previous point), hence in
  the span `V`, and has derivative `t ↦ ∑ tᵢ Xᵢ` at `0`, an isomorphism onto `V`. By the inverse
  function theorem its image contains a neighbourhood of `0` in `V`; since `Lie(G)` is stable
  under `ℚ_[p]`-scalars, `Lie(G) = V`.
* `ArithmeticOfJacobiPolynomials.lie_mem_ellAdicLie`: `exp (s X) Y exp (-s X) ∈ Lie(G)`
(conjugation invariance,
  `ArithmeticOfJacobiPolynomials.conj_mem_ellAdicLie`), and its derivative at `s = 0` is `X Y - Y
  X`; the
  subspace `Lie(G)` is closed (finite dimension).

Main definitions: `ArithmeticOfJacobiPolynomials.ellAdicLieSubmodule` and
`ArithmeticOfJacobiPolynomials.ellAdicLieSubalgebra`,
with carrier `ArithmeticOfJacobiPolynomials.ellAdicLie p G`.
-/

public section

open NormedSpace Filter Topology

namespace ArithmeticOfJacobiPolynomials

variable {p : ℕ} [hp : Fact p.Prime] {A : Type*} [NormedRing A] [NormedAlgebra ℚ_[p] A]

section Preliminaries

/-- The disc `eball 0 r` is a union of norm balls. -/
theorem mem_eball_of_norm_le {r : ENNReal} {x y : A} (h : ‖x‖ ≤ ‖y‖)
    (hy : y ∈ Metric.eball (0 : A) r) : x ∈ Metric.eball (0 : A) r := by
  rw [Metric.mem_eball, edist_dist, dist_zero_right] at hy ⊢
  exact (ENNReal.ofReal_le_ofReal h).trans_lt hy

theorem smul_mem_eball_of_norm_le_one {r : ENNReal} {μ : ℚ_[p]} (hμ : ‖μ‖ ≤ 1) {c : A}
    (hc : c ∈ Metric.eball (0 : A) r) : μ • c ∈ Metric.eball (0 : A) r :=
  mem_eball_of_norm_le ((norm_smul_le μ c).trans
    (mul_le_of_le_one_left (norm_nonneg _) hμ)) hc

variable [CompleteSpace A]

/-- In the disc of convergence, `exp c` is invertible with inverse `exp (-c)`. -/
theorem exp_mul_exp_neg_of_mem_eball {c : A}
    (hc : c ∈ Metric.eball (0 : A) (expSeries ℚ_[p] A).radius) :
    exp c * exp (-c) = 1 ∧ exp (-c) * exp c = 1 := by
  have hc' : -c ∈ Metric.eball (0 : A) (expSeries ℚ_[p] A).radius :=
    mem_eball_of_norm_le (norm_neg c).le hc
  refine ⟨?_, ?_⟩
  · rw [← exp_add_of_commute_of_mem_ball (Commute.neg_right (Commute.refl c)) hc hc',
      add_neg_cancel, exp_zero]
  · rw [← exp_add_of_commute_of_mem_ball (Commute.neg_left (Commute.refl c)) hc' hc,
      neg_add_cancel, exp_zero]

/-- In the disc of convergence, `exp (n • c) = (exp c) ^ n` for `n : ℕ`. -/
theorem exp_natCast_smul_of_mem_eball {c : A}
    (hc : c ∈ Metric.eball (0 : A) (expSeries ℚ_[p] A).radius) :
    ∀ n : ℕ, exp ((n : ℚ_[p]) • c) = exp c ^ n
  | 0 => by simp
  | n + 1 => by
    have hn1 : ‖(n : ℚ_[p])‖ ≤ 1 := by
      have := PadicInt.norm_le_one (n : ℤ_[p])
      rwa [PadicInt.norm_def, PadicInt.coe_natCast] at this
    have hn : (n : ℚ_[p]) • c ∈ Metric.eball (0 : A) (expSeries ℚ_[p] A).radius :=
      smul_mem_eball_of_norm_le_one hn1 hc
    rw [Nat.cast_succ, add_smul, one_smul,
      exp_add_of_commute_of_mem_ball ((Commute.refl c).smul_left _) hn hc,
      exp_natCast_smul_of_mem_eball hc n, pow_succ]

/-- **Key lemma.** If `G` is closed, `c` is in the disc of convergence of `exp` and
`exp c ∈ G`, then `c ∈ Lie(G)`: in fact `exp (μ • c) ∈ G` for all `μ ∈ ℤ_[p]`, as a limit of
the powers `(exp c) ^ n`. -/
theorem mem_ellAdicLie_of_exp_mem {G : Subgroup Aˣ} (hG : IsClosed (G : Set Aˣ)) {c : A}
    (hc : c ∈ Metric.eball (0 : A) (expSeries ℚ_[p] A).radius) {u : Aˣ} (hu : u ∈ G)
    (huc : (u : A) = exp c) : c ∈ ellAdicLie p G := by
  have hmem : ∀ μ : ℤ_[p], ((μ : ℚ_[p]) • c) ∈ Metric.eball (0 : A) (expSeries ℚ_[p] A).radius :=
    fun μ => smul_mem_eball_of_norm_le_one μ.2 hc
  have hmem' : ∀ μ : ℤ_[p],
      (-((μ : ℚ_[p]) • c)) ∈ Metric.eball (0 : A) (expSeries ℚ_[p] A).radius :=
    fun μ => mem_eball_of_norm_le (norm_neg _).le (hmem μ)
  let F : ℤ_[p] → Aˣ := fun μ =>
    ⟨exp ((μ : ℚ_[p]) • c), exp (-((μ : ℚ_[p]) • c)), (exp_mul_exp_neg_of_mem_eball (hmem μ)).1,
      (exp_mul_exp_neg_of_mem_eball (hmem μ)).2⟩
  have hsmul : Continuous fun μ : ℤ_[p] => (μ : ℚ_[p]) • c :=
    continuous_subtype_val.smul continuous_const
  have hcont : Continuous F := by
    rw [Units.continuous_iff]
    refine ⟨continuous_iff_continuousAt.2 fun μ => ?_, continuous_iff_continuousAt.2 fun μ => ?_⟩
    · exact ContinuousAt.comp (g := exp)
        (analyticAt_exp_of_mem_ball _ (hmem μ)).continuousAt hsmul.continuousAt
    · exact ContinuousAt.comp (g := exp)
        (analyticAt_exp_of_mem_ball _ (hmem' μ)).continuousAt hsmul.neg.continuousAt
  have hT : ∀ μ : ℤ_[p], F μ ∈ G := fun μ =>
    PadicInt.denseRange_natCast.induction_on (p := fun μ => F μ ∈ G) μ (hG.preimage hcont)
      fun n => by
        have hFn : F n = u ^ n := by
          apply Units.ext
          change exp (((n : ℤ_[p]) : ℚ_[p]) • c) = ((u ^ n : Aˣ) : A)
          rw [PadicInt.coe_natCast, exp_natCast_smul_of_mem_eball hc n, Units.val_pow_eq_pow_val,
            huc]
        rw [hFn]
        exact G.pow_mem hu n
  rw [mem_ellAdicLie_iff]
  refine Filter.mem_of_superset (Metric.closedBall_mem_nhds (0 : ℚ_[p]) one_pos) fun t ht => ?_
  have ht' : ‖t‖ ≤ 1 := by simpa using ht
  exact ⟨F ⟨t, ht'⟩, hT _, rfl⟩

omit [CompleteSpace A] in
/-- A finite ordered product of elements of `G` is in `G`. -/
theorem exists_mem_val_eq_list_prod {ι : Type*} (G : Subgroup Aˣ) (g : ι → A) :
    ∀ l : List ι, (∀ i ∈ l, ∃ u ∈ G, (u : A) = g i) → ∃ u ∈ G, (u : A) = (l.map g).prod
  | [], _ => ⟨1, G.one_mem, by simp⟩
  | i :: l, h => by
    obtain ⟨u, hu, hu'⟩ := h i List.mem_cons_self
    obtain ⟨v, hv, hv'⟩ :=
      exists_mem_val_eq_list_prod G g l fun j hj => h j (List.mem_cons_of_mem _ hj)
    exact ⟨u * v, G.mul_mem hu hv, by rw [Units.val_mul, hu', hv', List.map_cons, List.prod_cons]⟩

omit [CompleteSpace A] in
/-- Strict derivative of an ordered product of factors equal to `1` at the base point. -/
theorem hasStrictFDerivAt_list_prod_of_eq_one {ι E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℚ_[p] E] (f : ι → E → A) (f' : ι → E →L[ℚ_[p]] A) (x : E) :
    ∀ l : List ι, (∀ i ∈ l, f i x = 1) → (∀ i ∈ l, HasStrictFDerivAt (f i) (f' i) x) →
      HasStrictFDerivAt (fun y => (l.map fun i => f i y).prod) (l.map f').sum x
  | [], _, _ => by simpa using hasStrictFDerivAt_const (1 : A) x
  | i :: l, h1, hd => by
    have hl := hasStrictFDerivAt_list_prod_of_eq_one f f' x l
      (fun j hj => h1 j (List.mem_cons_of_mem _ hj)) (fun j hj => hd j (List.mem_cons_of_mem _ hj))
    have hprod : (l.map fun j => f j x).prod = 1 :=
      List.prod_eq_one fun y hy => by
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
        exact h1 j (List.mem_cons_of_mem _ hj)
    have h := (hd i List.mem_cons_self).mul' hl
    beta_reduce at h
    rw [h1 i List.mem_cons_self, hprod, one_smul, MulOpposite.op_one, one_smul, add_comm] at h
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    exact h

/-- `exp ∘ g` has strict derivative `g` at `0` for a continuous linear map `g`. -/
theorem hasStrictFDerivAt_exp_comp_clm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ_[p] E]
    (g : E →L[ℚ_[p]] A) : HasStrictFDerivAt (fun x => exp (g x)) g 0 := by
  have h := hasStrictFDerivAt_exp_zero_of_radius_pos (padic_expSeries_radius_pos p A)
  have h' : HasStrictFDerivAt (exp : A → A) (1 : A →L[ℚ_[p]] A) (g 0) := by
    rw [map_zero]; exact h
  have := h'.comp (0 : E) g.hasStrictFDerivAt
  convert this using 1
  ext v
  simp

/-- `s ↦ exp (s • X)` has derivative `X` at `0`. -/
theorem hasDerivAt_exp_smul_zero (X : A) :
    HasDerivAt (fun s : ℚ_[p] => exp (s • X)) X 0 := by
  have hexp :=
    (hasStrictFDerivAt_exp_zero_of_radius_pos (padic_expSeries_radius_pos p A)).hasFDerivAt
  have hl : HasDerivAt (fun s : ℚ_[p] => s • X) X 0 := by
    simpa using (hasDerivAt_id (0 : ℚ_[p])).smul_const X
  have := hexp.comp_hasDerivAt_of_eq (0 : ℚ_[p]) hl (zero_smul ℚ_[p] X).symm
  rw [one_apply_eq_self] at this
  exact this

end Preliminaries

section Subspace

variable [FiniteDimensional ℚ_[p] A]

/-- **The Lie algebra of a closed subgroup is a subspace**: the span of `Lie(G)` is contained
in `Lie(G)` (inverse function theorem argument, see the module docstring). -/
theorem span_ellAdicLie_subset {G : Subgroup Aˣ} (hG : IsClosed (G : Set Aˣ)) :
    (Submodule.span ℚ_[p] (ellAdicLie p G) : Set A) ⊆ ellAdicLie p G := by
  have : CompleteSpace A := FiniteDimensional.complete ℚ_[p] A
  obtain ⟨b, hbL, hspan, hli⟩ := exists_linearIndependent ℚ_[p] (ellAdicLie p G)
  have : Finite b := hli.finite
  have : Fintype b := Fintype.ofFinite b
  -- the linear isomorphism `ℚ_[p]^b → span (Lie G)`, `t ↦ ∑ tᵢ Xᵢ`
  let lin : (b → ℚ_[p]) →ₗ[ℚ_[p]] A := Fintype.linearCombination ℚ_[p] ((↑) : b → A)
  have hinj : Function.Injective lin := hli.fintypeLinearCombination_injective
  have hrange : LinearMap.range lin = Submodule.span ℚ_[p] (ellAdicLie p G) := by
    rw [Fintype.range_linearCombination, Subtype.range_coe, hspan]
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective lin (LinearMap.ker_eq_bot.2 hinj)
  let linC : (b → ℚ_[p]) →L[ℚ_[p]] A := LinearMap.toContinuousLinearMap lin
  let πC : A →L[ℚ_[p]] (b → ℚ_[p]) := LinearMap.toContinuousLinearMap π
  -- the product map `Φ t = exp (t₁ X₁) ⋯ exp (tₘ Xₘ)`
  let f' : b → (b → ℚ_[p]) →L[ℚ_[p]] A := fun i =>
    (ContinuousLinearMap.proj (R := ℚ_[p]) (φ := fun _ : b => ℚ_[p]) i).smulRight (i : A)
  let f : b → (b → ℚ_[p]) → A := fun i t => exp (f' i t)
  let Φ : (b → ℚ_[p]) → A := fun t => ((Finset.univ : Finset b).toList.map fun i => f i t).prod
  have hf0 : ∀ i, f i 0 = 1 := fun i => by simp only [f, map_zero, exp_zero]
  have hΦ : HasStrictFDerivAt Φ linC 0 := by
    have h := hasStrictFDerivAt_list_prod_of_eq_one f f' 0 (Finset.univ : Finset b).toList
      (fun i _ => hf0 i)
      (fun i _ => hasStrictFDerivAt_exp_comp_clm (f' i))
    have hsum : ((Finset.univ : Finset b).toList.map f').sum = linC := by
      refine ContinuousLinearMap.ext fun t => ?_
      rw [Finset.sum_map_toList, sum_apply]
      simp [linC, lin, Fintype.linearCombination_apply]
    rwa [hsum] at h
  have hΦ0 : Φ 0 = exp 0 := by
    rw [exp_zero]
    refine List.prod_eq_one fun y hy => ?_
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hy
    exact hf0 j
  -- the local logarithm, inverse of `exp` near `0`
  have hexp : HasStrictFDerivAt (exp : A → A)
      ((ContinuousLinearEquiv.refl ℚ_[p] A : A ≃L[ℚ_[p]] A) : A →L[ℚ_[p]] A) 0 := by
    have := hasStrictFDerivAt_exp_zero_of_radius_pos (padic_expSeries_radius_pos p A)
    convert this using 1
    ext x
    simp
  let L : A → A := hexp.localInverse exp _ 0
  have hL : HasStrictFDerivAt L
      (((ContinuousLinearEquiv.refl ℚ_[p] A).symm : A ≃L[ℚ_[p]] A) : A →L[ℚ_[p]] A) (Φ 0) := by
    rw [hΦ0]; exact hexp.to_localInverse
  have hL0 : L (Φ 0) = 0 := by rw [hΦ0]; exact hexp.localInverse_apply_image
  have hψ : HasStrictFDerivAt (fun t => L (Φ t)) linC 0 := by
    have := hL.comp (0 : b → ℚ_[p]) hΦ
    convert this using 1
    ext t
    simp
  -- `Θ = π ∘ log ∘ Φ` has derivative the identity at `0`
  let Θ : (b → ℚ_[p]) → (b → ℚ_[p]) := fun t => πC (L (Φ t))
  have hπlin : πC.comp linC =
      ((ContinuousLinearEquiv.refl ℚ_[p] (b → ℚ_[p]) : (b → ℚ_[p]) ≃L[ℚ_[p]] (b → ℚ_[p])) :
        (b → ℚ_[p]) →L[ℚ_[p]] (b → ℚ_[p])) := by
    refine ContinuousLinearMap.ext fun t => ?_
    simpa [πC, linC] using LinearMap.congr_fun hπ t
  have hΘ : HasStrictFDerivAt Θ
      ((ContinuousLinearEquiv.refl ℚ_[p] (b → ℚ_[p]) : (b → ℚ_[p]) ≃L[ℚ_[p]] (b → ℚ_[p])) :
        (b → ℚ_[p]) →L[ℚ_[p]] (b → ℚ_[p])) 0 := by
    rw [← hπlin]; exact πC.hasStrictFDerivAt.comp (0 : b → ℚ_[p]) hψ
  have hmap := hΘ.map_nhds_eq_of_equiv
  have hΘ0 : Θ 0 = 0 := by simp only [Θ, hL0, map_zero]
  -- near `0`, `log (Φ t) ∈ Lie(G)`
  have hGt : ∀ᶠ t in 𝓝 (0 : b → ℚ_[p]), ∃ u ∈ G, (u : A) = Φ t := by
    have : ∀ᶠ t in 𝓝 (0 : b → ℚ_[p]), ∀ i : b, ∃ u ∈ G, (u : A) = f i t := by
      rw [Filter.eventually_all]
      intro i
      have hX : (i : A) ∈ ellAdicLie p G := hbL i.2
      have htend : Tendsto (fun t : b → ℚ_[p] => t i) (𝓝 0) (𝓝 0) :=
        (continuous_apply i).tendsto' 0 0 rfl
      exact (htend.eventually (mem_ellAdicLie_iff.1 hX)).mono fun t ht => by
        simpa [f, f', ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]
          using ht
    exact this.mono fun t ht => exists_mem_val_eq_list_prod G (fun i => f i t) _ fun i _ => ht i
  have hRt : ∀ᶠ t in 𝓝 (0 : b → ℚ_[p]), exp (L (Φ t)) = Φ t := by
    have htend : Tendsto Φ (𝓝 0) (𝓝 (exp 0)) := by
      rw [← hΦ0]; exact hΦ.continuousAt.tendsto
    exact htend.eventually hexp.eventually_right_inverse
  have hball : ∀ᶠ t in 𝓝 (0 : b → ℚ_[p]),
      L (Φ t) ∈ Metric.eball (0 : A) (expSeries ℚ_[p] A).radius := by
    have htend : Tendsto (fun t => L (Φ t)) (𝓝 0) (𝓝 0) := by
      rw [← hL0]; exact hψ.continuousAt.tendsto
    exact htend.eventually (Metric.eball_mem_nhds _ (padic_expSeries_radius_pos p A))
  have hLie : ∀ᶠ t in 𝓝 (0 : b → ℚ_[p]), L (Φ t) ∈ ellAdicLie p G := by
    filter_upwards [hGt, hRt, hball] with t ht hRt' hb
    obtain ⟨u, hu, hut⟩ := ht
    exact mem_ellAdicLie_of_exp_mem hG hb hu (hut.trans hRt'.symm)
  -- hence `lin s ∈ Lie(G)` for `s` near `0`
  have hlin : ∀ᶠ s in 𝓝 (0 : b → ℚ_[p]), lin s ∈ ellAdicLie p G := by
    have : ∀ᶠ s in map Θ (𝓝 0), lin s ∈ ellAdicLie p G := by
      rw [Filter.eventually_map]
      filter_upwards [hLie] with t ht
      have hmem : L (Φ t) ∈ LinearMap.range lin := by
        rw [hrange]; exact Submodule.subset_span ht
      obtain ⟨w, hw⟩ := LinearMap.mem_range.1 hmem
      have hΘw : Θ t = w := by
        change πC (L (Φ t)) = w
        rw [← hw]
        simpa [πC] using LinearMap.congr_fun hπ w
      rw [hΘw, hw]
      exact ht
    rwa [hmap, hΘ0] at this
  -- conclusion: `Lie(G)` is a cone containing a neighbourhood of `0` in its span
  intro Z hZ
  have hZ' : Z ∈ LinearMap.range lin := by rw [hrange]; exact hZ
  obtain ⟨w, rfl⟩ := LinearMap.mem_range.1 hZ'
  have htend : Tendsto (fun c : ℚ_[p] => c • w) (𝓝 0) (𝓝 0) := by
    have := (tendsto_id (x := 𝓝 (0 : ℚ_[p]))).smul_const w
    rwa [zero_smul] at this
  have hev : ∀ᶠ c in 𝓝[≠] (0 : ℚ_[p]), c ∈ ({0} : Set ℚ_[p])ᶜ ∧ lin (c • w) ∈ ellAdicLie p G := by
    have h0 : ∀ᶠ c in 𝓝[≠] (0 : ℚ_[p]), c ∈ ({0} : Set ℚ_[p])ᶜ := self_mem_nhdsWithin
    exact h0.and (nhdsWithin_le_nhds (htend.eventually hlin))
  obtain ⟨c, hc0, hc⟩ := hev.exists
  have hc0' : c ≠ 0 := hc0
  have := smul_mem_ellAdicLie c⁻¹ hc
  rwa [map_smul, smul_smul, inv_mul_cancel₀ hc0', one_smul] at this

/-- `Lie(G)` equals its `ℚ_[p]`-span. -/
theorem span_ellAdicLie_eq {G : Subgroup Aˣ} (hG : IsClosed (G : Set Aˣ)) :
    (Submodule.span ℚ_[p] (ellAdicLie p G) : Set A) = ellAdicLie p G :=
  (span_ellAdicLie_subset hG).antisymm Submodule.subset_span

/-- **Closure under addition.** -/
theorem add_mem_ellAdicLie {G : Subgroup Aˣ} (hG : IsClosed (G : Set Aˣ)) {X Y : A}
    (hX : X ∈ ellAdicLie p G) (hY : Y ∈ ellAdicLie p G) : X + Y ∈ ellAdicLie p G :=
  span_ellAdicLie_subset hG
    (Submodule.add_mem _ (Submodule.subset_span hX) (Submodule.subset_span hY))

variable (p) in
/-- The `p`-adic Lie algebra of a closed subgroup `G ≤ Aˣ`, as a `ℚ_[p]`-subspace of `A`. -/
@[expose]
def ellAdicLieSubmodule (G : Subgroup Aˣ) (hG : IsClosed (G : Set Aˣ)) :
    Submodule ℚ_[p] A where
  carrier := ellAdicLie p G
  add_mem' := add_mem_ellAdicLie hG
  zero_mem' := zero_mem_ellAdicLie G
  smul_mem' c _ h := smul_mem_ellAdicLie c h

theorem coe_ellAdicLieSubmodule (G : Subgroup Aˣ) (hG : IsClosed (G : Set Aˣ)) :
    (ellAdicLieSubmodule p G hG : Set A) = ellAdicLie p G :=
  rfl

theorem mem_ellAdicLieSubmodule {G : Subgroup Aˣ} {hG : IsClosed (G : Set Aˣ)} {X : A} :
    X ∈ ellAdicLieSubmodule p G hG ↔ X ∈ ellAdicLie p G :=
  Iff.rfl

end Subspace

section Bracket

/-- `Lie(G)` is stable under conjugation by elements of `G`. -/
theorem conj_mem_ellAdicLie [CompleteSpace A] {G : Subgroup Aˣ} {u : Aˣ} (hu : u ∈ G) {Y : A}
    (hY : Y ∈ ellAdicLie p G) : (u : A) * Y * ↑u⁻¹ ∈ ellAdicLie p G := by
  rw [mem_ellAdicLie_iff]
  filter_upwards [mem_ellAdicLie_iff.1 hY, padic_eventually_smul_mem_eball (p := p) Y]
    with t ht hball
  obtain ⟨v, hv, hve⟩ := ht
  refine ⟨u * v * u⁻¹, G.mul_mem (G.mul_mem hu hv) (G.inv_mem hu), ?_⟩
  have hmap : ConjAct.toConjAct u • exp (t • Y) = exp (ConjAct.toConjAct u • (t • Y)) :=
    map_exp_of_mem_ball (MulSemiringAction.toRingHom (ConjAct Aˣ) A (ConjAct.toConjAct u))
      (continuous_const_smul (ConjAct.toConjAct u) :
        Continuous fun x : A => ConjAct.toConjAct u • x) (t • Y) hball
  rw [ConjAct.units_smul_def, ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct] at hmap
  rw [← smul_mul_assoc, ← mul_smul_comm, ← hmap, ← hve, Units.val_mul, Units.val_mul]

variable [FiniteDimensional ℚ_[p] A]

/-- **Closure under the commutator bracket.** -/
theorem lie_mem_ellAdicLie {G : Subgroup Aˣ} (hG : IsClosed (G : Set Aˣ)) {X Y : A}
    (hX : X ∈ ellAdicLie p G) (hY : Y ∈ ellAdicLie p G) : X * Y - Y * X ∈ ellAdicLie p G := by
  have : CompleteSpace A := FiniteDimensional.complete ℚ_[p] A
  let V := ellAdicLieSubmodule p G hG
  have hVc : IsClosed (V : Set A) := Submodule.closed_of_finiteDimensional V
  let g : ℚ_[p] → A := fun s => exp (s • X) * Y * exp ((-s) • X)
  have ha := hasDerivAt_exp_smul_zero (p := p) X
  have hb : HasDerivAt (fun s : ℚ_[p] => exp ((-s) • X)) (-X) 0 :=
    (hasDerivAt_exp_smul_zero (p := p) (-X)).congr_of_eventuallyEq
      (Eventually.of_forall fun s => by simp only [neg_smul, smul_neg])
  have hd : HasDerivAt g (X * Y - Y * X) 0 := by
    have h := (ha.fun_mul (hasDerivAt_const (0 : ℚ_[p]) Y)).fun_mul hb
    convert h using 1
    simp only [zero_smul, neg_zero, exp_zero, mul_zero, add_zero, mul_one, one_mul, mul_neg,
      sub_eq_add_neg]
  have hg0 : g 0 = Y := by simp [g]
  have h1 : ∀ᶠ s in 𝓝 (0 : ℚ_[p]), g s ∈ ellAdicLie p G := by
    filter_upwards [mem_ellAdicLie_iff.1 hX,
      padic_eventually_exp_smul_mul_exp_neg_smul (p := p) X] with s hs hs'
    obtain ⟨u, hu, hus⟩ := hs
    have hinv : ((u⁻¹ : Aˣ) : A) = exp ((-s) • X) :=
      Units.inv_eq_of_mul_eq_one_right (by rw [hus]; exact hs'.1)
    have := conj_mem_ellAdicLie hu hY
    rw [hinv, hus] at this
    exact this
  have hev : ∀ᶠ s in 𝓝[≠] (0 : ℚ_[p]), slope g 0 s ∈ V := by
    filter_upwards [nhdsWithin_le_nhds h1] with s hs
    rw [slope_def_module]
    refine V.smul_mem _ (V.sub_mem (mem_ellAdicLieSubmodule.2 hs) ?_)
    rw [hg0]
    exact mem_ellAdicLieSubmodule.2 hY
  exact mem_ellAdicLieSubmodule.1 (hVc.mem_of_tendsto (hasDerivAt_iff_tendsto_slope.1 hd) hev)

/-- Closure under the Lie bracket `⁅X, Y⁆ = X * Y - Y * X`. -/
theorem lie_mem_ellAdicLie' {G : Subgroup Aˣ} (hG : IsClosed (G : Set Aˣ)) {X Y : A}
    (hX : X ∈ ellAdicLie p G) (hY : Y ∈ ellAdicLie p G) : ⁅X, Y⁆ ∈ ellAdicLie p G := by
  rw [Ring.lie_def]
  exact lie_mem_ellAdicLie hG hX hY

end Bracket

section LieSubalgebra

/-! The Lie ring structure of an associative ring (commutator bracket) is not a global instance;
we use it locally. -/

attribute [local instance] LieRing.ofAssociativeRing

variable [FiniteDimensional ℚ_[p] A]

variable (p) in
/-- **The `p`-adic Lie algebra of a closed subgroup `G ≤ Aˣ` is a `ℚ_[p]`-Lie subalgebra** of
`A` (with the commutator bracket), with carrier `ellAdicLie p G`. -/
@[expose]
def ellAdicLieSubalgebra (G : Subgroup Aˣ) (hG : IsClosed (G : Set Aˣ)) :
    LieSubalgebra ℚ_[p] A :=
  { ellAdicLieSubmodule p G hG with
    lie_mem' := fun {X Y} hX hY => by
      rw [LieRing.of_associative_ring_bracket]
      exact lie_mem_ellAdicLie hG hX hY }

theorem coe_ellAdicLieSubalgebra (G : Subgroup Aˣ) (hG : IsClosed (G : Set Aˣ)) :
    (ellAdicLieSubalgebra p G hG : Set A) = ellAdicLie p G :=
  rfl

theorem mem_ellAdicLieSubalgebra {G : Subgroup Aˣ} {hG : IsClosed (G : Set Aˣ)} {X : A} :
    X ∈ ellAdicLieSubalgebra p G hG ↔ X ∈ ellAdicLie p G :=
  Iff.rfl

end LieSubalgebra

end ArithmeticOfJacobiPolynomials
