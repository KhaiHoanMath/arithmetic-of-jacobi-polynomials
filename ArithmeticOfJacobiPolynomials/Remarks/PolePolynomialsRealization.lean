/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Remarks.PolePolynomials
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import all ArithmeticOfJacobiPolynomials.Modular.JInvariant

/-!
# Pole polynomials: realizations in `ℍ` and the double poles of the [BSS] weight-two form

`ArithmeticOfJacobiPolynomials.Remarks.PolePolynomials` proves (`bssWeightTwoForm_residue_eq_zero`)
that *if*
`w_1, …, w_k ∈ ℍ` have invariants `J(w_j) = j(w_j)/1728` equal to the roots of `Q_k^{α,β}`, then
the weight-two form `F` of [BSS, (2.2)] has zero residues. The points exist, and each `w_i` is a
double pole of `F` under the hypotheses below.

* `exists_jInvariant_div_eq_of_mem_Icc`: **for every `x ∈ [0, 1]` there is `w ∈ ℍ` with
  `J(w) = x`.** The `S`-transformation law and the `q`-expansion give `E₆(i) = 0` and
  `E₄(ρ) = 0` (`ρ = e^{πi/3}`). The identities `J(-1/z) = J(z)` and
  `J(-z̄) = \overline{J(z)}` make `J` real on `|z| = 1`. The intermediate value theorem applies
  on the arc from `ρ` (`J = 0`) to `i` (`J = 1`);
* `exists_realization_of_bssQ_roots`: for the roots of `Q_k^{α,β}` (`α = (2a-1)/3`,
  `β = (2b-1)/2`) such points `w : Fin k → ℍ` exist (conditional only on the cited
  `JacobiSimpleRealZeros`);
* `bssWeightTwoForm_meromorphicOrderAt`: for pairwise distinct `j(w_j) ∉ {0, 1728}`, the form
  `F` (as a function of `z ∈ ℂ` via `ofComplex`) is meromorphic at each `w_i` with
  `meromorphicOrderAt = -2`, using `D j = -E₄² E₆/Δ ≠ 0` at `w_i`, `η ≠ 0` and
  `E₄(w_i), E₆(w_i) ≠ 0`;
* `bssWeightTwoForm_realized`: the unconditional-in-`w` corollary: there exist `w : Fin k → ℍ`
  realizing the roots of `Q_k^{α,β}`, at each of which `F` has a double pole with zero residue
  (conditional on the cited `JacobiSimpleRealZeros` and `BSSResidueCriterion`).
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial ModularForm UpperHalfPlane

open scoped MatrixGroups Manifold

/-! ### The weight-two form, unfolded -/

private theorem bssWeightTwoForm_apply (a b : ℕ) (x : Multiset ℂ) (z : ℍ) :
    bssWeightTwoForm a b x z =
      eta z ^ (4 + 16 * a + 24 * b) / (E₄ z ^ (2 * a) * E₆ z ^ (2 * b)) /
        (x.map fun c => (jInvariant z / 1728 - c) ^ 2).prod := by
  unfold bssWeightTwoForm
  rfl

/-! ### Eisenstein series: `S`-transformation, periodicity and conjugation -/

/-- `E_k(-1/z) = z^k E_k(z)`. -/
theorem E_S_smul {k : ℕ} (hk : 3 ≤ k) (z : ℍ) :
    ModularForm.E hk (ModularGroup.S • z) = (z : ℂ) ^ k * ModularForm.E hk z := by
  have h1 := SlashInvariantForm.slash_action_eqn (ModularForm.E hk)
    (ModularGroup.S : GL (Fin 2) ℝ) (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have h2 : (⇑(ModularForm.E hk) ∣[(k : ℤ)] ModularGroup.S) z = ModularForm.E hk z := by
    rw [ModularForm.SL_slash]
    exact congrFun h1 z
  rw [ModularForm.SL_slash_apply, ModularGroup.denom_S, zpow_neg, zpow_natCast] at h2
  have hinv : (z : ℂ) ^ k * ((z : ℂ) ^ k)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ (ne_zero z))
  linear_combination ((z : ℂ) ^ k) * h2 - ModularForm.E hk (ModularGroup.S • z) * hinv

theorem E₄_S_smul (z : ℍ) : E₄ (ModularGroup.S • z) = (z : ℂ) ^ 4 * E₄ z :=
  E_S_smul (k := 4) (by norm_num) z

theorem E₆_S_smul (z : ℍ) : E₆ (ModularGroup.S • z) = (z : ℂ) ^ 6 * E₆ z :=
  E_S_smul (k := 6) (by norm_num) z

/-- `E_k(w) = E_k(z)` when `e^{2πiw} = e^{2πiz}` (the `q`-expansion). -/
theorem E_eq_of_cexp_eq {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) {z w : ℍ}
    (h : Complex.exp (2 * Real.pi * Complex.I * (w : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (z : ℂ))) :
    ModularForm.E hk w = ModularForm.E hk z := by
  rw [EisensteinSeries.q_expansion_bernoulli hk hk2 w,
    EisensteinSeries.q_expansion_bernoulli hk hk2 z, h]

/-- `E_k(w) = \overline{E_k(z)}` when `e^{2πiw} = \overline{e^{2πiz}}` (the `q`-expansion has
rational coefficients). -/
theorem E_eq_conj_of_cexp_eq_conj {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) {z w : ℍ}
    (h : Complex.exp (2 * Real.pi * Complex.I * (w : ℂ)) =
      starRingEnd ℂ (Complex.exp (2 * Real.pi * Complex.I * (z : ℂ)))) :
    ModularForm.E hk w = starRingEnd ℂ (ModularForm.E hk z) := by
  rw [EisensteinSeries.q_expansion_bernoulli hk hk2 w,
    EisensteinSeries.q_expansion_bernoulli hk hk2 z, h]
  simp [Complex.conj_tsum, Complex.conj_ofNat]

/-- `J = j/1728 = E₄³/(E₄³ - E₆²)`. -/
theorem jInvariant_div_eq (z : ℍ) :
    jInvariant z / 1728 = E₄ z ^ 3 / (E₄ z ^ 3 - E₆ z ^ 2) := by
  rw [jInvariant_apply, discriminant_eq_E₄_cube_sub_E₆_sq, div_div,
    div_mul_cancel₀ _ (by norm_num : (1728 : ℂ) ≠ 0)]

theorem E₄_ne_zero_of_jInvariant_ne_zero {z : ℍ} (h : jInvariant z ≠ 0) : E₄ z ≠ 0 := by
  intro h4
  apply h
  rw [jInvariant_apply, h4, zero_pow (by norm_num), zero_div]

theorem E₆_ne_zero_of_jInvariant_ne {z : ℍ} (h : jInvariant z ≠ 1728) : E₆ z ≠ 0 := by
  intro h6
  apply h
  rw [jInvariant_apply, div_eq_iff (discriminant_ne_zero z), discriminant_eq_E₄_cube_sub_E₆_sq,
    h6]
  ring

/-! ### `J` on the arc `|z| = 1` -/

/-- If `-1/z = -z̄` (i.e. `|z| = 1`), then `J(z)` is real: `J(z) = J(-1/z) = J(-z̄)`
`= \overline{J(z)}`. -/
theorem conj_jInvariant_div_of_inv (z : ℍ) (hz : (-(z : ℂ))⁻¹ = -starRingEnd ℂ (z : ℂ)) :
    starRingEnd ℂ (jInvariant z / 1728) = jInvariant z / 1728 := by
  have hS : ((ModularGroup.S • z : ℍ) : ℂ) = -starRingEnd ℂ (z : ℂ) := by
    rw [modular_S_smul, coe_mk, hz]
  have hq : Complex.exp (2 * Real.pi * Complex.I * ((ModularGroup.S • z : ℍ) : ℂ)) =
      starRingEnd ℂ (Complex.exp (2 * Real.pi * Complex.I * (z : ℂ))) := by
    rw [hS, ← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
    ring
  have h4c : E₄ (ModularGroup.S • z) = starRingEnd ℂ (E₄ z) :=
    E_eq_conj_of_cexp_eq_conj (k := 4) (by norm_num) ⟨2, rfl⟩ hq
  have h6c : E₆ (ModularGroup.S • z) = starRingEnd ℂ (E₆ z) :=
    E_eq_conj_of_cexp_eq_conj (k := 6) (by norm_num) ⟨3, rfl⟩ hq
  have hz0 : (z : ℂ) ^ 12 ≠ 0 := pow_ne_zero 12 (ne_zero z)
  rw [jInvariant_div_eq, map_div₀, map_sub, map_pow, map_pow, ← h4c, ← h6c, E₄_S_smul,
    E₆_S_smul, show ((z : ℂ) ^ 4 * E₄ z) ^ 3 = (z : ℂ) ^ 12 * E₄ z ^ 3 by ring,
    show ((z : ℂ) ^ 6 * E₆ z) ^ 2 = (z : ℂ) ^ 12 * E₆ z ^ 2 by ring, ← mul_sub,
    mul_div_mul_left _ _ hz0]

/-- **`E₆(i) = 0`**, from `E₆(-1/z) = z⁶ E₆(z)` at the fixed point `i` of `S`. -/
theorem E₆_eq_zero_of_coe_eq_I (z : ℍ) (hz : (z : ℂ) = Complex.I) : E₆ z = 0 := by
  have hS : ModularGroup.S • z = z :=
    UpperHalfPlane.ext (by rw [modular_S_smul, coe_mk, hz, inv_neg, Complex.inv_I, neg_neg])
  have h := E₆_S_smul z
  rw [hS, hz] at h
  have hI6 : Complex.I ^ 6 = -1 := by
    have h' : Complex.I ^ 6 = (Complex.I ^ 2) ^ 3 := by ring
    rw [h', Complex.I_sq]
    norm_num
  rw [hI6] at h
  linear_combination h / 2

/-- **`J(i) = 1`.** -/
theorem jInvariant_div_eq_one_of_coe_eq_I (z : ℍ) (hz : (z : ℂ) = Complex.I) :
    jInvariant z / 1728 = 1 := by
  have h6 := E₆_eq_zero_of_coe_eq_I z hz
  have hΔ := discriminant_ne_zero z
  rw [discriminant_eq_E₄_cube_sub_E₆_sq, h6, zero_pow two_ne_zero, sub_zero] at hΔ
  rw [jInvariant_div_eq, h6, zero_pow two_ne_zero, sub_zero]
  exact div_self fun h => hΔ (by rw [h, zero_div])

/-- **`E₄(ρ) = 0`** for `ρ = e^{πi/3} = 1/2 + (√3/2) i`, from `E₄(-1/ρ) = ρ⁴ E₄(ρ)`,
`-1/ρ = ρ - 1` and the periodicity `E₄(ρ - 1) = E₄(ρ)`. -/
theorem E₄_eq_zero_of_coe_eq_rho (z : ℍ)
    (hz : (z : ℂ) = 1 / 2 + ((Real.sqrt 3 : ℝ) : ℂ) / 2 * Complex.I) : E₄ z = 0 := by
  have hr : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hsq : (z : ℂ) ^ 2 = (z : ℂ) - 1 := by
    rw [hz]
    linear_combination (1 / 4 * Complex.I ^ 2) * hr + (3 / 4 : ℂ) * Complex.I_sq
  have hinv : (-(z : ℂ))⁻¹ = (z : ℂ) - 1 :=
    inv_eq_of_mul_eq_one_right (by linear_combination -hsq)
  have hS : ((ModularGroup.S • z : ℍ) : ℂ) = (z : ℂ) - 1 := by
    rw [modular_S_smul, coe_mk, hinv]
  have hq : Complex.exp (2 * Real.pi * Complex.I * ((ModularGroup.S • z : ℍ) : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (z : ℂ)) := by
    rw [hS, mul_sub, mul_one, Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]
  have h1 : E₄ (ModularGroup.S • z) = E₄ z := E_eq_of_cexp_eq (k := 4) (by norm_num) ⟨2, rfl⟩ hq
  have h2 : E₄ (ModularGroup.S • z) = (z : ℂ) ^ 4 * E₄ z := E₄_S_smul z
  have hne : 1 + (z : ℂ) ≠ 0 := by
    intro h
    have hz1 : (z : ℂ) = -1 := by linear_combination h
    rw [hz1] at hsq
    norm_num at hsq
  have hmul : (1 + (z : ℂ)) * E₄ z = 0 := by
    linear_combination h2 - h1 + E₄ z * (z : ℂ) * ((z : ℂ) + 1) * hsq
  exact (mul_eq_zero.mp hmul).resolve_left hne

/-- **`J(ρ) = 0`.** -/
theorem jInvariant_div_eq_zero_of_coe_eq_rho (z : ℍ)
    (hz : (z : ℂ) = 1 / 2 + ((Real.sqrt 3 : ℝ) : ℂ) / 2 * Complex.I) : jInvariant z / 1728 = 0 := by
  rw [jInvariant_div_eq, E₄_eq_zero_of_coe_eq_rho z hz, zero_pow three_ne_zero, zero_div]

theorem im_cos_add_sin_mul_I (θ : ℝ) :
    ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I).im = Real.sin θ := by
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  ring

/-- On the unit circle `-1/z = -z̄`. -/
theorem inv_neg_cos_add_sin_mul_I (θ : ℝ) :
    (-((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I))⁻¹ =
      -starRingEnd ℂ ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) := by
  apply inv_eq_of_mul_eq_one_right
  rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
  have hcs : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq θ
  linear_combination hcs - (Real.sin θ : ℂ) ^ 2 * Complex.I_sq

/-- **Realizations.** For every `x ∈ [0, 1]` there is `w ∈ ℍ` with `J(w) = j(w)/1728 = x`
(intermediate value theorem for the real-valued `J` on the arc from `ρ = e^{πi/3}` to `i`). -/
theorem exists_jInvariant_div_eq_of_mem_Icc {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ w : ℍ, jInvariant w / 1728 = x := by
  have hsin : ∀ θ ∈ Set.Icc (Real.pi / 3) (Real.pi / 2), 0 < Real.sin θ := fun θ hθ =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos])
      (by linarith [hθ.2, Real.pi_pos])
  have hpath : Continuous fun θ : ℝ => (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I :=
    (Complex.continuous_ofReal.comp Real.continuous_cos).add
      ((Complex.continuous_ofReal.comp Real.continuous_sin).mul continuous_const)
  have hmaps : Set.MapsTo (fun θ : ℝ => (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)
      (Set.Icc (Real.pi / 3) (Real.pi / 2)) {z : ℂ | 0 < z.im} := fun θ hθ => by
    simp only [Set.mem_ofPred_eq, im_cos_add_sin_mul_I]
    exact hsin θ hθ
  have hJ : ContinuousOn (fun z : ℂ => (jInvariant ∘ ofComplex) z / 1728) {z : ℂ | 0 < z.im} :=
    (UpperHalfPlane.mdifferentiable_iff.mp mdifferentiable_jInvariant).continuousOn.div_const
      1728
  obtain ⟨g, hgdef⟩ : ∃ g : ℝ → ℝ, g = fun θ =>
      (jInvariant (ofComplex ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)) / 1728).re :=
    ⟨_, rfl⟩
  have hg : ContinuousOn g (Set.Icc (Real.pi / 3) (Real.pi / 2)) := by
    rw [hgdef]
    exact Complex.continuous_re.comp_continuousOn (hJ.comp hpath.continuousOn hmaps)
  have hpos : ∀ θ, 0 < Real.sin θ →
      0 < ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I).im := fun θ h => by
    rw [im_cos_add_sin_mul_I]
    exact h
  have hle : Real.pi / 3 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hp3 := hpos _ (hsin _ ⟨le_refl _, hle⟩)
  have hp2 := hpos _ (hsin _ ⟨hle, le_refl _⟩)
  have hg3 : g (Real.pi / 3) = 0 := by
    simp only [hgdef]
    rw [ofComplex_apply_of_im_pos hp3, jInvariant_div_eq_zero_of_coe_eq_rho _ ?_,
      Complex.zero_re]
    rw [coe_mk, Real.cos_pi_div_three, Real.sin_pi_div_three]
    push_cast
    ring
  have hg2 : g (Real.pi / 2) = 1 := by
    simp only [hgdef]
    rw [ofComplex_apply_of_im_pos hp2, jInvariant_div_eq_one_of_coe_eq_I _ ?_, Complex.one_re]
    rw [coe_mk, Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp
  obtain ⟨θ, hθ, hgθ⟩ := intermediate_value_Icc hle hg (by rw [hg3, hg2]; exact hx)
  have hθpos := hpos θ (hsin θ hθ)
  refine ⟨⟨_, hθpos⟩, ?_⟩
  have hre := Complex.conj_eq_iff_re.mp
    (conj_jInvariant_div_of_inv ⟨_, hθpos⟩ (inv_neg_cos_add_sin_mul_I θ))
  rw [← hre]
  congr 1
  rw [← hgθ]
  simp only [hgdef]
  rw [ofComplex_apply_of_im_pos hθpos]

/-- For every `y ∈ [0, 1728]` there is `w ∈ ℍ` with `j(w) = y`. -/
theorem exists_jInvariant_eq_of_mem_Icc {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1728) :
    ∃ w : ℍ, jInvariant w = y := by
  obtain ⟨w, hw⟩ := exists_jInvariant_div_eq_of_mem_Icc (x := y / 1728)
    ⟨by linarith [hy.1], by linarith [hy.2]⟩
  rw [Complex.ofReal_div, Complex.ofReal_ofNat, div_left_inj' (by norm_num : (1728 : ℂ) ≠ 0)]
    at hw
  exact ⟨w, hw⟩

/-! ### Realizations of the roots of `Q_k^{α,β}` -/

theorem exists_fin_univ_map_eq {α : Type*} (s : Multiset α) {n : ℕ}
    (h : Multiset.card s = n) : ∃ v : Fin n → α, Finset.univ.val.map v = s := by
  obtain ⟨l, rfl⟩ := Quot.exists_rep s
  change ∃ v : Fin n → α, Finset.univ.val.map v = (l : Multiset α)
  have hl : l.length = n := h
  subst hl
  exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]⟩

/-- **Realizations of the pole invariants.** For `a, b ∈ ℕ`, `α = (2a-1)/3`, `β = (2b-1)/2`
there are `w_1, …, w_k ∈ ℍ` whose invariants `J(w_j)` are (as a multiset) the roots of
`Q_k^{α,β}`, as required in `bssWeightTwoForm_residue_eq_zero` (conditional on the cited
`JacobiSimpleRealZeros`, which places the roots in `(0, 1)`). -/
theorem exists_realization_of_bssQ_roots (hZ : JacobiSimpleRealZeros) (a b k : ℕ) :
    ∃ w : Fin k → ℍ, Finset.univ.val.map (fun j => jInvariant (w j) / 1728) =
      ((bssQ k ((2 * a - 1) / 3) ((2 * b - 1) / 2)).map (algebraMap ℚ ℝ)).roots.map
        fun t : ℝ => (t : ℂ) := by
  have ha0 : (0 : ℚ) ≤ a := a.cast_nonneg
  have hb0 : (0 : ℚ) ≤ b := b.cast_nonneg
  have hα : (-1 : ℚ) < (2 * a - 1) / 3 := by linarith
  have hβ : (-1 : ℚ) < (2 * b - 1) / 2 := by linarith
  obtain ⟨-, hcard, hmem⟩ := bssQ_roots_real hZ (k := k) hα hβ
  obtain ⟨v, hv⟩ := exists_fin_univ_map_eq _ hcard
  have hreal : ∀ j, ∃ w : ℍ, jInvariant w / 1728 = (v j : ℂ) := by
    intro j
    have hj : v j ∈
        ((bssQ k ((2 * a - 1) / 3) ((2 * b - 1) / 2)).map (algebraMap ℚ ℝ)).roots := by
      rw [← hv]
      exact Multiset.mem_map_of_mem v (Finset.mem_val.mpr (Finset.mem_univ j))
    obtain ⟨h0, h1⟩ := hmem _ hj
    exact exists_jInvariant_div_eq_of_mem_Icc ⟨h0.le, h1.le⟩
  choose w hw using hreal
  refine ⟨w, ?_⟩
  rw [← hv, Multiset.map_map]
  exact Multiset.map_congr rfl fun j _ => hw j

/-! ### The double poles of the weight-two form -/

theorem analyticAt_comp_ofComplex {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (z : ℍ) :
    AnalyticAt ℂ (f ∘ ofComplex) (z : ℂ) :=
  (UpperHalfPlane.mdifferentiable_iff.mp hf).analyticAt
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)

/-- **The poles of the weight-two form (2.2).** Let `w_1, …, w_k ∈ ℍ` have pairwise distinct
`j(w_j) ∉ {0, 1728}`. Then the weight-two form `F` of [BSS, (2.2)] with pole invariants
`x_j = J(w_j)`, as a function of `z ∈ ℂ` (via `ofComplex`), is meromorphic at each `w_i` and has
a pole of order exactly `2` there. -/
theorem bssWeightTwoForm_meromorphicOrderAt (a b : ℕ) {k : ℕ} (w : Fin k → ℍ)
    (hinj : Function.Injective fun j => jInvariant (w j))
    (hne : ∀ j, jInvariant (w j) ≠ 0 ∧ jInvariant (w j) ≠ 1728) (i : Fin k) :
    MeromorphicAt (fun z => bssWeightTwoForm a b
      (Finset.univ.val.map fun j => jInvariant (w j) / 1728) (ofComplex z)) ((w i : ℍ) : ℂ) ∧
    meromorphicOrderAt (fun z => bssWeightTwoForm a b
      (Finset.univ.val.map fun j => jInvariant (w j) / 1728) (ofComplex z))
      ((w i : ℍ) : ℂ) = -2 := by
  have h4 : E₄ (w i) ≠ 0 := E₄_ne_zero_of_jInvariant_ne_zero (hne i).1
  have h6 : E₆ (w i) ≠ 0 := E₆_ne_zero_of_jInvariant_ne (hne i).2
  have hjA : AnalyticAt ℂ (jInvariant ∘ ofComplex) ((w i : ℍ) : ℂ) :=
    analyticAt_comp_ofComplex mdifferentiable_jInvariant (w i)
  have hofc : ofComplex ((w i : ℍ) : ℂ) = w i := ofComplex_apply (w i)
  have hηfun : (etaUpper ∘ ofComplex) = fun x => eta (ofComplex x) := by
    funext x
    rw [Function.comp_apply, etaUpper_apply]
  have hηA : AnalyticAt ℂ (fun x => eta (ofComplex x)) ((w i : ℍ) : ℂ) := by
    rw [← hηfun]
    exact analyticAt_comp_ofComplex mdifferentiable_etaUpper (w i)
  have hE4A : AnalyticAt ℂ (⇑E₄ ∘ ofComplex) ((w i : ℍ) : ℂ) :=
    analyticAt_comp_ofComplex mdifferentiable_E₄ (w i)
  have hE6A : AnalyticAt ℂ (⇑E₆ ∘ ofComplex) ((w i : ℍ) : ℂ) :=
    analyticAt_comp_ofComplex mdifferentiable_E₆ (w i)
  obtain ⟨A, hA⟩ : ∃ A : ℂ → ℂ, A = fun x => eta (ofComplex x) ^ (4 + 16 * a + 24 * b) /
      (E₄ (ofComplex x) ^ (2 * a) * E₆ (ofComplex x) ^ (2 * b)) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℂ → ℂ,
      B = fun x => (jInvariant ∘ ofComplex) x / 1728 - jInvariant (w i) / 1728 := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℂ → ℂ, C = fun x => ∏ j ∈ Finset.univ.erase i,
      ((jInvariant ∘ ofComplex) x / 1728 - jInvariant (w j) / 1728) ^ 2 := ⟨_, rfl⟩
  have hF : (fun z => bssWeightTwoForm a b
      (Finset.univ.val.map fun j => jInvariant (w j) / 1728) (ofComplex z)) =
      A * (B ^ 2 * C)⁻¹ := by
    funext x
    rw [bssWeightTwoForm_apply, Multiset.map_map, ← Finset.prod_eq_multiset_prod,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [hA, hB, hC, Pi.mul_apply, Pi.inv_apply, Pi.pow_apply, Function.comp_apply]
    exact div_eq_mul_inv _ _
  have hAA : AnalyticAt ℂ A ((w i : ℍ) : ℂ) := by
    rw [hA]
    refine (hηA.fun_pow _).fun_div ((hE4A.fun_pow _).fun_mul (hE6A.fun_pow _)) ?_
    simp only [hofc]
    exact mul_ne_zero (pow_ne_zero _ h4) (pow_ne_zero _ h6)
  have hA0 : A ((w i : ℍ) : ℂ) ≠ 0 := by
    rw [hA]
    simp only [hofc]
    exact div_ne_zero (pow_ne_zero _ (eta_ne_zero (w i).im_pos))
      (mul_ne_zero (pow_ne_zero _ h4) (pow_ne_zero _ h6))
  have hderiv : deriv (jInvariant ∘ ofComplex) ((w i : ℍ) : ℂ) ≠ 0 := by
    have h := normalizedDerivOfComplex_jInvariant_apply (w i)
    rw [Derivative.normalizedDerivOfComplex] at h
    intro h0
    rw [h0, mul_zero] at h
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 h4) h6)
      (inv_ne_zero (discriminant_ne_zero (w i)))) h.symm
  have hBA : AnalyticAt ℂ B ((w i : ℍ) : ℂ) := by
    rw [hB]
    exact hjA.div_const.fun_sub analyticAt_const
  have hB0 : B ((w i : ℍ) : ℂ) = 0 := by
    rw [hB]
    simp only [Function.comp_apply, hofc, sub_self]
  have hBd : deriv B ((w i : ℍ) : ℂ) ≠ 0 := by
    rw [hB, deriv_sub_const, deriv_div_const]
    exact div_ne_zero hderiv (by norm_num)
  have hBord : analyticOrderAt B ((w i : ℍ) : ℂ) = 1 :=
    hBA.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hB0 hBd
  have hCA : AnalyticAt ℂ C ((w i : ℍ) : ℂ) := by
    rw [hC]
    exact Finset.analyticAt_fun_prod _ fun j _ =>
      (hjA.div_const.fun_sub analyticAt_const).fun_pow 2
  have hC0 : C ((w i : ℍ) : ℂ) ≠ 0 := by
    rw [hC]
    simp only [Function.comp_apply, hofc]
    rw [Finset.prod_ne_zero_iff]
    intro j hj
    refine pow_ne_zero 2 (sub_ne_zero.mpr fun h => Finset.ne_of_mem_erase hj (hinj ?_).symm)
    exact (div_left_inj' (by norm_num : (1728 : ℂ) ≠ 0)).mp h
  have hD : AnalyticAt ℂ (B ^ 2 * C) ((w i : ℍ) : ℂ) := (hBA.pow 2).mul hCA
  have hDord : analyticOrderAt (B ^ 2 * C) ((w i : ℍ) : ℂ) = 2 := by
    rw [analyticOrderAt_mul (hBA.pow 2) hCA, analyticOrderAt_pow hBA, hBord,
      hCA.analyticOrderAt_eq_zero.mpr hC0]
    simp
  refine ⟨?_, ?_⟩
  · rw [hF]
    exact hAA.meromorphicAt.mul hD.meromorphicAt.inv
  · rw [hF, meromorphicOrderAt_mul_of_ne_zero hAA hA0, meromorphicOrderAt_inv,
      hD.meromorphicOrderAt_eq, hDord]
    rfl

/-- **The roots of `Q_k^{α,β}` are double poles.** If `w_1, …, w_k ∈ ℍ` realize the roots of
`Q_k^{α,β}` (`α = (2a-1)/3`, `β = (2b-1)/2`), the weight-two form (2.2) has a pole of order
exactly `2` at each `w_i` (conditional on the cited `JacobiSimpleRealZeros`, which makes the roots
simple and places them in `(0, 1)`). -/
theorem bssWeightTwoForm_meromorphicOrderAt_of_bssQ (hZ : JacobiSimpleRealZeros) {a b k : ℕ}
    (w : Fin k → ℍ)
    (hw : Finset.univ.val.map (fun j => jInvariant (w j) / 1728) =
      ((bssQ k ((2 * a - 1) / 3) ((2 * b - 1) / 2)).map (algebraMap ℚ ℝ)).roots.map
        fun t : ℝ => (t : ℂ)) (i : Fin k) :
    MeromorphicAt (fun z => bssWeightTwoForm a b
      (Finset.univ.val.map fun j => jInvariant (w j) / 1728) (ofComplex z)) ((w i : ℍ) : ℂ) ∧
    meromorphicOrderAt (fun z => bssWeightTwoForm a b
      (Finset.univ.val.map fun j => jInvariant (w j) / 1728) (ofComplex z))
      ((w i : ℍ) : ℂ) = -2 := by
  have ha0 : (0 : ℚ) ≤ a := a.cast_nonneg
  have hb0 : (0 : ℚ) ≤ b := b.cast_nonneg
  have hα : (-1 : ℚ) < (2 * a - 1) / 3 := by linarith
  have hβ : (-1 : ℚ) < (2 * b - 1) / 2 := by linarith
  obtain ⟨hnd, -, hmem⟩ := bssQ_roots_real hZ (k := k) hα hβ
  have hnodup : (Finset.univ.val.map fun j => jInvariant (w j) / 1728).Nodup := by
    rw [hw]; exact hnd.map Complex.ofReal_injective
  have hxinj : Function.Injective fun j => jInvariant (w j) / 1728 := fun i j h =>
    Multiset.inj_on_of_nodup_map hnodup i (Finset.mem_val.mpr (Finset.mem_univ i)) j
      (Finset.mem_val.mpr (Finset.mem_univ j)) h
  have hinj : Function.Injective fun j => jInvariant (w j) := fun i j h => by
    apply hxinj
    have h' : jInvariant (w i) = jInvariant (w j) := h
    change jInvariant (w i) / 1728 = jInvariant (w j) / 1728
    rw [h']
  refine bssWeightTwoForm_meromorphicOrderAt a b w hinj (fun j => ?_) i
  have h1 : jInvariant (w j) / 1728 ∈ Finset.univ.val.map fun j => jInvariant (w j) / 1728 :=
    Multiset.mem_map_of_mem _ (Finset.mem_val.mpr (Finset.mem_univ j))
  rw [hw] at h1
  obtain ⟨r, hr, hrx⟩ := Multiset.mem_map.mp h1
  obtain ⟨hr0, hr1⟩ := hmem r hr
  have hJ : jInvariant (w j) = 1728 * (r : ℂ) := by
    have hrx' : (r : ℂ) = jInvariant (w j) / 1728 := hrx
    rw [hrx']
    ring
  refine ⟨?_, ?_⟩
  · rw [hJ]
    exact mul_ne_zero (by norm_num) (by exact_mod_cast hr0.ne')
  · rw [hJ]
    intro h
    have hr1' : (r : ℂ) = 1 := by linear_combination h / 1728
    have hr1'' : r = 1 := by exact_mod_cast hr1'
    linarith

/-- **The Jacobi polynomial `Q_k^{α,β}` is the pole polynomial** ([BSS, §2–§4]).
For `a, b ≤ 1`, `α = (2a-1)/3`, `β = (2b-1)/2`, there are `w_1, …, w_k ∈ ℍ` whose invariants
`J(w_j)` are exactly the roots of `Q_k^{α,β}`; at each `w_i` the weight-two form `F` of (2.2) has
a pole of order exactly `2` and zero residue. Conditional on the cited `JacobiSimpleRealZeros` and
`BSSResidueCriterion`. -/
theorem bssWeightTwoForm_realized (hZ : JacobiSimpleRealZeros) (hRes : BSSResidueCriterion)
    {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) (k : ℕ) :
    ∃ w : Fin k → ℍ, Finset.univ.val.map (fun j => jInvariant (w j) / 1728) =
        ((bssQ k ((2 * a - 1) / 3) ((2 * b - 1) / 2)).map (algebraMap ℚ ℝ)).roots.map
          (fun t : ℝ => (t : ℂ)) ∧
      ∀ i : Fin k,
        MeromorphicAt (fun z => bssWeightTwoForm a b
          (Finset.univ.val.map fun j => jInvariant (w j) / 1728) (ofComplex z)) ((w i : ℍ) : ℂ) ∧
        meromorphicOrderAt (fun z => bssWeightTwoForm a b
          (Finset.univ.val.map fun j => jInvariant (w j) / 1728) (ofComplex z))
          ((w i : ℍ) : ℂ) = -2 ∧
        ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          circleIntegral (fun z => bssWeightTwoForm a b
            (Finset.univ.val.map fun j => jInvariant (w j) / 1728) (ofComplex z)) (w i) r = 0 := by
  obtain ⟨w, hw⟩ := exists_realization_of_bssQ_roots hZ a b k
  refine ⟨w, hw, fun i => ?_⟩
  obtain ⟨hm, ho⟩ := bssWeightTwoForm_meromorphicOrderAt_of_bssQ hZ w hw i
  exact ⟨hm, ho, bssWeightTwoForm_residue_eq_zero hZ hRes ha hb w hw i⟩

end ArithmeticOfJacobiPolynomials
