/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.External
public import ArithmeticOfJacobiPolynomials.Padic.SourceNewtonHull

/-!
# Root valuations of a monic polynomial from its coefficient hull

With `NewtonPolygonRootSlopes` (cited, Berger Theorem 2.4) and the hull computation
`newtonHull_eq_affine`: if the monic `P ∈ (PadicAlgCl p)[X]` of degree `n` has coefficient
valuations `v_p(c_j) = ρ(n-j) + θ Φ(j)`, `θ > 0`, then its root valuations are
`ρ - θ (W(j+1) - W(j))`, `j < n`, for the hull `W` of `(j, Φ(j))`
(`rootValuations_of_hull`), and the total deficit satisfies
`∑_z (ρ - v(z))_+ = θ (W(n) - min W)` (`deficit_eq_hull`), hence `≤ θ D` when `Φ ≥ -D`,
`Φ(n) = 0` (`deficit_le_of_hull`): the middle identities of Proposition 4.6.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

local notation "K" => PadicAlgCl p

/-- The root valuations of a monic polynomial are the (negated) slopes of its coefficient hull. -/
theorem rootValuations_of_hull (hNP : NewtonPolygonRootSlopes) {P : K[X]} {n : ℕ}
    (hmon : P.Monic) (hdeg : P.natDegree = n) (Φ : ℕ → ℤ) {ρ θ : ℝ} (hθ : 0 < θ)
    (hcoef : ∀ j ≤ n, P.coeff j ≠ 0 ∧
      padicVal p (P.coeff j) = ρ * ((n : ℝ) - j) + θ * Φ j) :
    P.roots.map (padicVal p) = (Finset.range n).val.map fun j =>
      ρ - θ * (lowerHull n Φ ((j + 1 : ℕ) : ℝ) - lowerHull n Φ (j : ℝ)) := by
  have hP0 : P ≠ 0 := hmon.ne_zero
  have h := hNP p P hP0
  have htrail : P.natTrailingDegree = 0 :=
    natTrailingDegree_eq_zero.mpr (Or.inr (hcoef 0 (Nat.zero_le n)).1)
  have hsupp : P.support = Finset.range (n + 1) := by
    ext j
    rw [mem_support_iff, Finset.mem_range]
    constructor
    · intro hj
      by_contra hlt
      exact hj (coeff_eq_zero_of_natDegree_lt (by omega))
    · intro hj
      exact (hcoef j (by omega)).1
  have hroots : ∀ z ∈ P.roots, z ≠ 0 := by
    intro z hz hz0
    subst hz0
    have : P.eval 0 = 0 := (mem_roots'.mp hz).2
    rw [← coeff_zero_eq_eval_zero] at this
    exact (hcoef 0 (Nat.zero_le n)).1 this
  have hfilt := @Multiset.filter_eq_self (PadicAlgCl p) (· ≠ 0)
    (fun _ => Classical.propDecidable _) P.roots
  rw [hfilt.mpr hroots, htrail, hdeg, hsupp] at h
  rw [h, ← Finset.range_eq_Ico]
  refine Multiset.map_congr rfl fun j hj => ?_
  have hj' : j < n := Finset.mem_range.mp hj
  have hmem : ∀ i ∈ Finset.range (n + 1), padicVal p (P.coeff i) =
      ρ * ((n : ℝ) - i) + θ * Φ i := fun i hi =>
    (hcoef i (by have := Finset.mem_range.mp hi; omega)).2
  have hx1 : (((j + 1 : ℕ) : ℝ)) ∈ Set.Icc (0 : ℝ) n :=
    ⟨Nat.cast_nonneg _, by exact_mod_cast hj'⟩
  have hx0 : ((j : ℕ) : ℝ) ∈ Set.Icc (0 : ℝ) n :=
    ⟨Nat.cast_nonneg _, by exact_mod_cast hj'.le⟩
  rw [newtonHull_congr hmem, newtonHull_congr hmem,
    newtonHull_eq_affine Φ hθ hx1, newtonHull_eq_affine Φ hθ hx0]
  push_cast
  ring

/-- **The Proposition 4.6 identity.** `∑_z (ρ - v(z))_+ = ∫_0^n (θ W')_+ = θ (W(n) - min W)`:
the sum of the positive parts of the root deficits is the sum of the positive increments of the
convex hull `W`, which by convexity is `W(n) - min W`. -/
theorem deficit_eq_hull (hNP : NewtonPolygonRootSlopes) {P : K[X]} {n : ℕ}
    (hmon : P.Monic) (hdeg : P.natDegree = n) (Φ : ℕ → ℤ) {ρ θ : ℝ} (hθ : 0 < θ)
    (hcoef : ∀ j ≤ n, P.coeff j ≠ 0 ∧
      padicVal p (P.coeff j) = ρ * ((n : ℝ) - j) + θ * Φ j) :
    ∃ i ≤ n, (∀ k ≤ n, lowerHull n Φ (i : ℝ) ≤ lowerHull n Φ (k : ℝ)) ∧
      (P.roots.map fun z => max (ρ - padicVal p z) 0).sum =
        θ * (lowerHull n Φ (n : ℝ) - lowerHull n Φ (i : ℝ)) := by
  have hroots := rootValuations_of_hull hNP hmon hdeg Φ hθ hcoef
  obtain ⟨i, hi, hmin, hsum⟩ := sum_pos_increments (a := fun j : ℕ => lowerHull n Φ (j : ℝ)) n
    fun j hj => lowerHull_increment_mono Φ hj
  refine ⟨i, hi, hmin, ?_⟩
  have e1 : (P.roots.map fun z => max (ρ - padicVal p z) 0) =
      (P.roots.map (padicVal p)).map fun v => max (ρ - v) 0 := by
    rw [Multiset.map_map]; rfl
  rw [e1, hroots]
  have e2 : (((Finset.range n).val.map fun j => ρ - θ *
      (lowerHull n Φ ((j + 1 : ℕ) : ℝ) - lowerHull n Φ (j : ℝ))).map fun v => max (ρ - v) 0) =
      (Finset.range n).val.map fun j =>
        θ * max (lowerHull n Φ ((j + 1 : ℕ) : ℝ) - lowerHull n Φ (j : ℝ)) 0 := by
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun j _ => ?_
    simp only [Function.comp_apply]
    rw [show ρ - (ρ - θ * (lowerHull n Φ ((j + 1 : ℕ) : ℝ) - lowerHull n Φ (j : ℝ))) =
      θ * (lowerHull n Φ ((j + 1 : ℕ) : ℝ) - lowerHull n Φ (j : ℝ)) by ring]
    rw [← mul_zero θ, ← mul_max_of_nonneg _ _ hθ.le, mul_zero]
  rw [e2]
  change (∑ j ∈ Finset.range n, θ * max (lowerHull n Φ ((j + 1 : ℕ) : ℝ) -
    lowerHull n Φ (j : ℝ)) 0) = _
  rw [← Finset.mul_sum, hsum]

/-- **Total deficit bound** (the end of the Proposition 4.6 chain): if `Φ ≥ -D` and `Φ(n) = 0`
then `∑_z (ρ - v(z))_+ ≤ θ D`. -/
theorem deficit_le_of_hull (hNP : NewtonPolygonRootSlopes) {P : K[X]} {n : ℕ}
    (hmon : P.Monic) (hdeg : P.natDegree = n) (Φ : ℕ → ℤ) {ρ θ : ℝ} (hθ : 0 < θ)
    (hcoef : ∀ j ≤ n, P.coeff j ≠ 0 ∧
      padicVal p (P.coeff j) = ρ * ((n : ℝ) - j) + θ * Φ j)
    (hΦn : Φ n = 0) {D : ℝ} (hD : ∀ j ≤ n, -D ≤ Φ j) :
    (P.roots.map fun z => max (ρ - padicVal p z) 0).sum ≤ θ * D := by
  obtain ⟨i, hi, -, hsum⟩ := deficit_eq_hull hNP hmon hdeg Φ hθ hcoef
  rw [hsum]
  have h1 : lowerHull n Φ (n : ℝ) ≤ 0 := by
    have := lowerHull_le_point n Φ (le_refl n)
    rw [hΦn] at this
    simpa using this
  have h2 : -D ≤ lowerHull n Φ (i : ℝ) := by
    have := affine_le_lowerHull (n := n) (Φ := Φ) (b := -D) (τ := 0)
      (fun j hj => by simpa using hD j hj) hi
    simpa using this
  have : lowerHull n Φ (n : ℝ) - lowerHull n Φ (i : ℝ) ≤ D := by linarith
  exact mul_le_mul_of_nonneg_left this hθ.le |>.trans_eq rfl

end ArithmeticOfJacobiPolynomials
