/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Padic.NewtonHullDef
public import ArithmeticOfJacobiPolynomials.Combinatorics.DigitHull

/-!
# Lower convex hulls of the manuscript's finite point sets

Finite hull arguments used with `NewtonPolygonRootSlopes` (the cited Newton polygon theorem of
`External.lean`): the hull of `(j, ρ(n-j) + θ Φ(j))` is `ρ(n-x) + θ H(x)` for the hull
`H = lowerHull n Φ` of `(j, Φ(j))` (`newtonHull_eq_affine`); the hull on a side from a line
touching the points at its endpoints (`lowerHull_eq_line`); and the
convexity step of Proposition 4.6, `∑_j (W(j+1) - W(j))_+ = W(n) - min W` for convex `W`
(`sum_pos_increments`).
-/

public section

namespace ArithmeticOfJacobiPolynomials

theorem convexOn_affine_newton (s : Set ℝ) (hs : Convex ℝ s) (b τ : ℝ) :
    ConvexOn ℝ s (fun x => b - τ * x) := by
  refine ⟨hs, fun x _ y _ a c _ _ hac => le_of_eq ?_⟩
  simp only [smul_eq_mul]
  linear_combination (-b) * hac

/-- The chord inequality of a convex function on `[0,n]`. -/
theorem chord_le {φ : ℝ → ℝ} {n : ℕ} (hφ : ConvexOn ℝ (Set.Icc 0 (n : ℝ)) φ)
    {a c t : ℝ} (ha : 0 ≤ a) (hac : a < c) (hcn : c ≤ n) (hat : a ≤ t) (htc : t ≤ c) :
    (c - a) * φ t ≤ (c - t) * φ a + (t - a) * φ c := by
  have hca : 0 < c - a := by linarith
  have hne : c - a ≠ 0 := hca.ne'
  have hα : 0 ≤ (c - t) / (c - a) := div_nonneg (by linarith) hca.le
  have hβ : 0 ≤ (t - a) / (c - a) := div_nonneg (by linarith) hca.le
  have hsum : (c - t) / (c - a) + (t - a) / (c - a) = 1 := by
    rw [← add_div, show c - t + (t - a) = c - a by ring, div_self hne]
  have hxa : a ∈ Set.Icc (0 : ℝ) n := ⟨ha, by linarith⟩
  have hxc : c ∈ Set.Icc (0 : ℝ) n := ⟨by linarith, hcn⟩
  have h := hφ.2 hxa hxc hα hβ hsum
  have e : ((c - t) / (c - a)) • a + ((t - a) / (c - a)) • c = t := by
    simp only [smul_eq_mul]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hne]
    ring
  rw [e] at h
  simp only [smul_eq_mul] at h
  have h2 := mul_le_mul_of_nonneg_left h hca.le
  have e2 : (c - a) * ((c - t) / (c - a) * φ a + (t - a) / (c - a) * φ c) =
      (c - t) * φ a + (t - a) * φ c := by
    field_simp
  linarith

/-- An affine function below the points lies below the hull. -/
theorem affine_le_lowerHull {n : ℕ} {Φ : ℕ → ℤ} {b τ : ℝ} (h : ∀ j ≤ n, b - τ * j ≤ Φ j)
    {k : ℕ} (hk : k ≤ n) : b - τ * k ≤ lowerHull n Φ k := by
  have hmin : IsHullMinorant n Φ (fun x => b - τ * x) :=
    (isHullMinorant_iff _ _ _).mpr ⟨convexOn_affine_newton _ (convex_Icc _ _) b τ, h⟩
  exact hmin.le_lowerHull ⟨Nat.cast_nonneg k, by exact_mod_cast hk⟩

/-- **The hull on a side.** If the line `b - τ x` lies below the points and touches them at
`i ≤ k ≤ i'`, then the lower hull is that line at `k`. -/
theorem lowerHull_eq_line {n : ℕ} {Φ : ℕ → ℤ} {b τ : ℝ} (h : ∀ j ≤ n, b - τ * j ≤ Φ j)
    {i i' k : ℕ} (hik : i ≤ k) (hki : k ≤ i') (hi' : i' ≤ n) (hei : b - τ * i = Φ i)
    (hei' : b - τ * i' = Φ i') : lowerHull n Φ k = b - τ * k := by
  refine le_antisymm ?_ (affine_le_lowerHull h (hki.trans hi'))
  refine lowerHull_le fun φ hφ' => ?_
  obtain ⟨hφ, hφle⟩ := (isHullMinorant_iff _ _ _).mp hφ'
  rcases eq_or_lt_of_le (hik.trans hki) with hii | hii
  · have : k = i := by omega
    subst this
    have := hφle k (by omega)
    linarith
  · have hpos : (0 : ℝ) < (i' : ℝ) - i := by
      have : (i : ℝ) < i' := by exact_mod_cast hii
      linarith
    have hkle : (k : ℝ) ≤ i' := by exact_mod_cast hki
    have hikle : (i : ℝ) ≤ k := by exact_mod_cast hik
    have hiN : (i' : ℝ) ≤ n := by exact_mod_cast hi'
    have hch := chord_le hφ (a := (i : ℝ)) (c := (i' : ℝ)) (t := (k : ℝ)) (Nat.cast_nonneg i)
      (by exact_mod_cast hii) hiN hikle hkle
    have h1 := hφle i (by omega)
    have h2 := hφle i' hi'
    rw [← hei] at h1
    rw [← hei'] at h2
    have hA : ((i' : ℝ) - k) * φ i ≤ ((i' : ℝ) - k) * (b - τ * i) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    have hB : ((k : ℝ) - i) * φ i' ≤ ((k : ℝ) - i) * (b - τ * i') :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    have hfin : ((i' : ℝ) - i) * φ k ≤ ((i' : ℝ) - i) * (b - τ * k) := by nlinarith
    exact le_of_mul_le_mul_left hfin hpos

/-- The hull is convex: its increments at integers are nondecreasing. -/
theorem lowerHull_increment_mono {n : ℕ} (Φ : ℕ → ℤ) {j : ℕ} (hj : j + 2 ≤ n) :
    lowerHull n Φ ((j + 1 : ℕ) : ℝ) - lowerHull n Φ (j : ℝ) ≤
      lowerHull n Φ ((j + 2 : ℕ) : ℝ) - lowerHull n Φ ((j + 1 : ℕ) : ℝ) := by
  have hc := chord_le ((isHullMinorant_iff _ _ _).mp (lowerHull_isHullMinorant n Φ)).1
    (a := (j : ℝ)) (c := ((j + 2 : ℕ) : ℝ))
    (t := ((j + 1 : ℕ) : ℝ)) (Nat.cast_nonneg j) (by push_cast; linarith)
    (by exact_mod_cast hj) (by push_cast; linarith) (by push_cast; linarith)
  push_cast at hc ⊢
  nlinarith

/-- **The convexity step of Proposition 4.6.** For a convex sequence the sum of the positive parts
of the increments is the final value minus the minimum. -/
theorem sum_pos_increments {a : ℕ → ℝ} (n : ℕ)
    (hconv : ∀ j, j + 2 ≤ n → a (j + 1) - a j ≤ a (j + 2) - a (j + 1)) :
    ∃ i ≤ n, (∀ k ≤ n, a i ≤ a k) ∧
      ∑ j ∈ Finset.range n, max (a (j + 1) - a j) 0 = a n - a i := by
  induction n with
  | zero => exact ⟨0, le_rfl, fun k hk => by interval_cases k; exact le_rfl, by simp⟩
  | succ n ih =>
    obtain ⟨i, hi, hmin, hsum⟩ := ih fun j hj => hconv j (by omega)
    by_cases hd : 0 ≤ a (n + 1) - a n
    · refine ⟨i, by omega, fun k hk => ?_, ?_⟩
      · rcases Nat.lt_or_ge k (n + 1) with h | h
        · exact hmin k (by omega)
        · have : k = n + 1 := by omega
          subst this
          have := hmin n le_rfl
          linarith
      · rw [Finset.sum_range_succ, hsum, max_eq_left hd]
        ring
    · push Not at hd
      -- all increments up to the last are negative, so the sequence decreases
      have hneg : ∀ m j, j + m = n → a (j + 1) - a j < 0 := by
        intro m
        induction m with
        | zero => intro j hj; have : j = n := by omega
                  subst this; exact hd
        | succ m ihm =>
          intro j hj
          have h1 := hconv j (by omega)
          have h2 := ihm (j + 1) (by omega)
          linarith
      have hall : ∀ j ≤ n, a (j + 1) - a j < 0 := fun j hj => hneg (n - j) j (by omega)
      refine ⟨n + 1, le_rfl, fun k hk => ?_, ?_⟩
      · have hdec : ∀ m k, k + m = n + 1 → a (n + 1) ≤ a k := by
          intro m
          induction m with
          | zero => intro k hk; have : k = n + 1 := by omega
                    subst this; exact le_rfl
          | succ m ihm =>
            intro k hk
            have := ihm (k + 1) (by omega)
            have := hall k (by omega)
            linarith
        exact hdec (n + 1 - k) k (by omega)
      · rw [Finset.sum_range_succ, sub_self]
        have : ∑ j ∈ Finset.range n, max (a (j + 1) - a j) 0 = 0 :=
          Finset.sum_eq_zero fun j hj => max_eq_right (hall j (by
            have := Finset.mem_range.mp hj; omega)).le
        rw [this, max_eq_right hd.le]
        ring

/-- The hull only depends on the values at the points of the support. -/
theorem newtonHull_congr {a b : ℕ} {S : Finset ℕ} {v v' : ℕ → ℝ} (h : ∀ j ∈ S, v j = v' j)
    (x : ℝ) : newtonHull a b S v x = newtonHull a b S v' x := by
  have hset : {φ : ℝ → ℝ | ConvexOn ℝ (Set.Icc (a : ℝ) b) φ ∧ ∀ j ∈ S, φ j ≤ v j} =
      {φ : ℝ → ℝ | ConvexOn ℝ (Set.Icc (a : ℝ) b) φ ∧ ∀ j ∈ S, φ j ≤ v' j} :=
    Set.ext fun φ => and_congr Iff.rfl (forall₂_congr fun j hj => by rw [h j hj])
  unfold newtonHull
  rw [hset]

/-- **Hull of the coefficient valuations.** If `v(j) = ρ(n-j) + θ Φ(j)` with `θ > 0` for
`0 ≤ j ≤ n`, the lower hull of the points `(j, v(j))` is `ρ(n-x) + θ H(x)`, with `H = lowerHull n Φ`
the hull of `(j, Φ(j))`. -/
theorem newtonHull_eq_affine {n : ℕ} (Φ : ℕ → ℤ) {ρ θ : ℝ} (hθ : 0 < θ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) n) :
    newtonHull 0 n (Finset.range (n + 1)) (fun j => ρ * ((n : ℝ) - j) + θ * Φ j) x =
      ρ * ((n : ℝ) - x) + θ * lowerHull n Φ x := by
  have hW := (isHullMinorant_iff _ _ _).mp (lowerHull_isHullMinorant n Φ)
  set ψ : ℝ → ℝ := fun y => ρ * ((n : ℝ) - y) + θ * lowerHull n Φ y with hψ
  have hψconv : ConvexOn ℝ (Set.Icc (((0 : ℕ) : ℝ)) (n : ℝ)) ψ := by
    refine ⟨by simpa using convex_Icc (0 : ℝ) n, fun x hx y hy a c ha hc hac => ?_⟩
    have hx' : x ∈ Set.Icc (0 : ℝ) n := by simpa using hx
    have hy' : y ∈ Set.Icc (0 : ℝ) n := by simpa using hy
    have h := hW.1.2 hx' hy' ha hc hac
    have h2 := mul_le_mul_of_nonneg_left h hθ.le
    simp only [smul_eq_mul] at h h2 ⊢
    have e : ρ * ((n : ℝ) - (a * x + c * y)) =
        a * (ρ * ((n : ℝ) - x)) + c * (ρ * ((n : ℝ) - y)) := by
      linear_combination (-(ρ * n)) * hac
    nlinarith
  have hψle : ∀ j ∈ Finset.range (n + 1), ψ j ≤ ρ * ((n : ℝ) - j) + θ * Φ j := by
    intro j hj
    have := lowerHull_le_point n Φ (j := j) (by simpa [Nat.lt_succ_iff] using hj)
    simp only [ψ]
    nlinarith
  have hbdd : BddAbove ((fun φ : ℝ → ℝ => φ x) ''
      {φ | ConvexOn ℝ (Set.Icc (((0 : ℕ) : ℝ)) (n : ℝ)) φ ∧
        ∀ j ∈ Finset.range (n + 1), φ j ≤ ρ * ((n : ℝ) - j) + θ * Φ j}) := by
    refine ⟨max (ρ * ((n : ℝ) - 0) + θ * Φ 0) (ρ * ((n : ℝ) - n) + θ * Φ n), ?_⟩
    rintro _ ⟨φ, ⟨hφc, hφl⟩, rfl⟩
    have h0 : ((0 : ℕ) : ℝ) ∈ Set.Icc (((0 : ℕ) : ℝ)) (n : ℝ) := ⟨le_rfl, by simp⟩
    have hn : (n : ℝ) ∈ Set.Icc (((0 : ℕ) : ℝ)) (n : ℝ) := ⟨by simp, le_rfl⟩
    have hseg : x ∈ segment ℝ ((0 : ℕ) : ℝ) n := by
      rw [segment_eq_Icc (by simp)]; simpa using hx
    have := hφc.le_on_segment h0 hn hseg
    have e0 := hφl 0 (by simp)
    have en := hφl n (by simp)
    simp only [Nat.cast_zero] at this e0 ⊢
    exact this.trans (max_le_max e0 en)
  unfold newtonHull
  refine le_antisymm (csSup_le ⟨ψ x, ψ, ⟨hψconv, hψle⟩, rfl⟩ ?_)
    (le_csSup hbdd ⟨ψ, ⟨hψconv, hψle⟩, rfl⟩)
  rintro _ ⟨φ, ⟨hφc, hφl⟩, rfl⟩
  -- `(φ - ρ(n-y))/θ` is a convex minorant of `Φ`
  have h1 := convexOn_affine_newton (Set.Icc (0 : ℝ) n) (convex_Icc _ _) (-(ρ * n)) (-ρ)
  have hφc0 : ConvexOn ℝ (Set.Icc (0 : ℝ) n) φ := by simpa using hφc
  have h2 := (hφc0.add h1).smul (inv_nonneg.mpr hθ.le)
  have hmin : IsHullMinorant n Φ (fun y => θ⁻¹ * (φ y - ρ * ((n : ℝ) - y))) := by
    refine (isHullMinorant_iff _ _ _).mpr ⟨?_, fun j hj => ?_⟩
    · simpa [smul_eq_mul, sub_eq_add_neg, mul_add, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm] using h2
    · have := hφl j (by simpa [Nat.lt_succ_iff] using hj)
      rw [inv_mul_le_iff₀ hθ]
      linarith
  have := hmin.le_lowerHull hx
  rw [inv_mul_le_iff₀ hθ] at this
  linarith

end ArithmeticOfJacobiPolynomials
