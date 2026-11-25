/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.KanekoZagier.ExplicitCutoff
public import ArithmeticOfJacobiPolynomials.Remarks.Prose
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.Mul

/-!
# The elementary minimization of the finite criterion (Section 4.5)

After the exact finite criterion `ℋ_n(z)` of Proposition 4.8 the manuscript says:

> The minimization is elementary. Set `a_n = T_{2,n} + T_{3,n} + E - 2L_n + 2 log 2`. The part of
> `ℋ_n(z)` that depends on `z` is `a_n z + 2 log 2 / z - log z`, which is strictly convex for
> `z > 0`. If `a_n ≤ 0` it is decreasing. If `a_n > 0`, its minimum is at
> `q_n = (1 + √(1 + 8 a_n log 2)) / (2 a_n)`. Thus on an interval of integer degrees it suffices
> to check the integers adjacent to the clipped value of `q_n`.

This module proves each of these assertions.

* `endpointShape a c z = a z + c / z - log z`, with `c = 2 log 2` in the manuscript;
  `strictConvexOn_endpointShape` (strictly convex on `z > 0`, for `c ≥ 0`);
  `strictAntiOn_endpointShape` (strictly decreasing on `z > 0` when `a ≤ 0`, `c > 0`);
* `endpointMinimizer a = (1 + √(1 + 8 a log 2)) / (2 a)` (`q_n`), `0 < endpointMinimizer a` and
  the exact comparison `endpointShape_sub_of_root` with the value at the positive root `q` of
  `a q² = q + c` (`endpointMinimizer_root`), and the resulting global minimum on `z > 0`
  (`endpointShape_minimizer_le`, `endpointShape_minimizer_lt`);
* `endpointClip a lo hi` is the clipped value (`q_n` clipped to `[lo, hi]` when `a > 0`, and
  `hi` when `a ≤ 0`, where the minimum over the interval is at the right end);
  `endpointShape_adjacent_min`: for naturals `1 ≤ lo ≤ hi` the integers `⌊t⌋`, `⌈t⌉` of the
  clipped value `t` lie in `[lo, hi]` and the smaller of the two values of the `z`-dependent part
  is at most its value at every integer degree `k ∈ [lo, hi]`;
* the same statements for `ℋ_n` itself (`strictConvexOn_kzCriterionFn`,
  `kzCriterionFn_adjacent_min`), using the decomposition `kzCriterionFn_eq_add`.

`Remarks.Prose` proves the profile facts for `c = 2 log 2` (strict convexity, strict monotonicity
on `(0, q]` and `[q, ∞)`, and uniqueness of the minimizer). Its definitions `finiteCriterionProfile`
and `finiteCriterionMinimizer` agree with `endpointShape a (2 log 2)` and `endpointMinimizer` by
`endpointShape_two_log_two` and `endpointMinimizer_eq_finiteCriterionMinimizer`. The general-`c`
statements reduce minimization over integer degrees in `[lo, hi]` to the integers adjacent to the
clipped minimizer (`endpointShape_adjacent_min`, `kzCriterionFn_adjacent_min`).

The statements hold on the whole half line `z > 0`; the manuscript defines `ℋ_n(z)` for `z ≥ 1`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Set

/-- The part `a z + c / z - log z` of `ℋ_n(z)` that depends on `z`
(`c = 2 log 2` in the manuscript). -/
@[expose] noncomputable def endpointShape (a c z : ℝ) : ℝ := a * z + c / z - Real.log z

theorem endpointShape_eq (a c z : ℝ) : endpointShape a c z = a * z + c / z - Real.log z := (rfl)

/-- `q_n = (1 + √(1 + 8 a log 2)) / (2 a)` for the slope `a = a_n`. -/
@[expose] noncomputable def endpointMinimizer (a : ℝ) : ℝ :=
  (1 + √(1 + 8 * a * Real.log 2)) / (2 * a)

theorem endpointMinimizer_eq (a : ℝ) :
    endpointMinimizer a = (1 + √(1 + 8 * a * Real.log 2)) / (2 * a) := (rfl)

/-- The clipped value: `q_n` clipped to `[lo, hi]` if `a > 0`, and the right end `hi` if `a ≤ 0`. -/
@[expose] noncomputable def endpointClip (a : ℝ) (lo hi : ℕ) : ℝ :=
  if 0 < a then max (lo : ℝ) (min (hi : ℝ) (endpointMinimizer a)) else (hi : ℝ)

theorem endpointClip_eq (a : ℝ) (lo hi : ℕ) : endpointClip a lo hi =
    if 0 < a then max (lo : ℝ) (min (hi : ℝ) (endpointMinimizer a)) else (hi : ℝ) := (rfl)

/-! ### Convexity and monotonicity -/

/-- `a z + c / z - log z` is strictly convex on `z > 0` (for `c ≥ 0`). -/
theorem strictConvexOn_endpointShape (a : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    StrictConvexOn ℝ (Ioi 0) (endpointShape a c) := by
  have h1 : StrictConvexOn ℝ (Ioi (0 : ℝ)) (fun z : ℝ => -Real.log z) :=
    strictConcaveOn_log_Ioi.neg
  have h2 : ConvexOn ℝ (Ioi (0 : ℝ)) (fun z : ℝ => c * z⁻¹) := by
    have := (convexOn_zpow (-1)).smul hc
    simpa [smul_eq_mul, zpow_neg_one] using this
  have h3 : ConvexOn ℝ (Ioi (0 : ℝ)) (fun z : ℝ => a * z) :=
    ⟨convex_Ioi 0, fun x _ y _ s t _ _ _ => le_of_eq (by simp only [smul_eq_mul]; ring)⟩
  have h4 := h1.add_convexOn (h3.add h2)
  convert h4 using 1
  funext z
  simp only [endpointShape_eq, Pi.add_apply, div_eq_mul_inv]
  ring

/-- If `a ≤ 0` (and `c > 0`), `a z + c / z - log z` is strictly decreasing on `z > 0`. -/
theorem strictAntiOn_endpointShape {a c : ℝ} (ha : a ≤ 0) (hc : 0 < c) :
    StrictAntiOn (endpointShape a c) (Ioi 0) := by
  intro x hx y _ hxy
  have hx' : (0 : ℝ) < x := hx
  simp only [endpointShape_eq]
  have h1 : a * y ≤ a * x := mul_le_mul_of_nonpos_left hxy.le ha
  have h2 : c / y < c / x := div_lt_div_of_pos_left hc hx' hxy
  have h3 : Real.log x < Real.log y := Real.log_lt_log hx' hxy
  linarith

/-! ### The minimum for `a > 0` -/

/-- The exact difference from the value at a positive root `q` of `a q² = q + c`:
`F(z) - F(q) = c (z - q)² / (q² z) + ((z - q)/q - log (z/q))`. -/
theorem endpointShape_sub_of_root {a c q z : ℝ} (hq : 0 < q) (hz : 0 < z)
    (hroot : a * q ^ 2 = q + c) :
    endpointShape a c z - endpointShape a c q =
      c * (z - q) ^ 2 / (q ^ 2 * z) + ((z - q) / q - Real.log (z / q)) := by
  have ha : a = (q + c) / q ^ 2 := by
    field_simp
    linarith
  have e : Real.log (z / q) = Real.log z - Real.log q := Real.log_div hz.ne' hq.ne'
  simp only [endpointShape_eq]
  rw [e, ha]
  field_simp
  ring

theorem sub_div_sub_log_nonneg {q z : ℝ} (hq : 0 < q) (hz : 0 < z) :
    0 ≤ (z - q) / q - Real.log (z / q) := by
  have h := Real.log_le_sub_one_of_pos (div_pos hz hq)
  have e : (z - q) / q = z / q - 1 := by field_simp
  linarith

/-- The value at a positive root `q` of `a q² = q + c` is the global minimum on `z > 0`. -/
theorem endpointShape_root_le {a c q z : ℝ} (hc : 0 ≤ c) (hq : 0 < q) (hz : 0 < z)
    (hroot : a * q ^ 2 = q + c) : endpointShape a c q ≤ endpointShape a c z := by
  have h := endpointShape_sub_of_root hq hz hroot
  have h1 : 0 ≤ c * (z - q) ^ 2 / (q ^ 2 * z) := by positivity
  have h2 := sub_div_sub_log_nonneg hq hz
  linarith

/-- ... and the minimum is attained only at `q` (for `c > 0`). -/
theorem endpointShape_root_lt {a c q z : ℝ} (hc : 0 < c) (hq : 0 < q) (hz : 0 < z)
    (hzq : z ≠ q) (hroot : a * q ^ 2 = q + c) : endpointShape a c q < endpointShape a c z := by
  have h := endpointShape_sub_of_root hq hz hroot
  have h1 : 0 < c * (z - q) ^ 2 / (q ^ 2 * z) :=
    div_pos (mul_pos hc (sq_pos_of_ne_zero (sub_ne_zero.mpr hzq))) (by positivity)
  have h2 := sub_div_sub_log_nonneg hq hz
  linarith

theorem one_add_eight_mul_log_two_nonneg {a : ℝ} (ha : 0 < a) : 0 ≤ 1 + 8 * a * Real.log 2 := by
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  positivity

/-- `q_n > 0` for `a > 0`. -/
theorem endpointMinimizer_pos {a : ℝ} (ha : 0 < a) : 0 < endpointMinimizer a := by
  rw [endpointMinimizer_eq]
  have := Real.sqrt_nonneg (1 + 8 * a * Real.log 2)
  positivity

/-- `q_n` is the positive root of `a q² = q + 2 log 2`, i.e. of `a - 2 log 2 / q² - 1/q = 0`. -/
theorem endpointMinimizer_root {a : ℝ} (ha : 0 < a) :
    a * endpointMinimizer a ^ 2 = endpointMinimizer a + 2 * Real.log 2 := by
  have h0 := one_add_eight_mul_log_two_nonneg ha
  have hs := Real.sq_sqrt h0
  set s := √(1 + 8 * a * Real.log 2) with hsdef
  rw [endpointMinimizer_eq]
  rw [← hsdef]
  field_simp
  linear_combination hs

/-- For `a > 0` the global minimum of `a z + 2 log 2 / z - log z` over `z > 0` is at `q_n`. -/
theorem endpointShape_minimizer_le {a : ℝ} (ha : 0 < a) {z : ℝ} (hz : 0 < z) :
    endpointShape a (2 * Real.log 2) (endpointMinimizer a) ≤
      endpointShape a (2 * Real.log 2) z :=
  endpointShape_root_le (by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity)
    (endpointMinimizer_pos ha) hz (endpointMinimizer_root ha)

theorem endpointShape_minimizer_lt {a : ℝ} (ha : 0 < a) {z : ℝ} (hz : 0 < z)
    (hzq : z ≠ endpointMinimizer a) :
    endpointShape a (2 * Real.log 2) (endpointMinimizer a) <
      endpointShape a (2 * Real.log 2) z :=
  endpointShape_root_lt (by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity)
    (endpointMinimizer_pos ha) hz hzq (endpointMinimizer_root ha)

/-! ### Minimization over an interval of integers -/

/-- A convex function `f` on `z > 0` with global minimizer `q > 0` is minimized over `[lo, hi]` at
the clipped value `max lo (min hi q)`. -/
theorem clip_le_of_convex {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f) {q lo hi : ℝ} (hq : 0 < q)
    (hmin : ∀ z, 0 < z → f q ≤ f z) (hlo : 0 < lo) (hlh : lo ≤ hi) {x : ℝ}
    (hx : x ∈ Icc lo hi) : f (max lo (min hi q)) ≤ f x := by
  obtain ⟨hx1, hx2⟩ := hx
  have hx0 : 0 < x := lt_of_lt_of_le hlo hx1
  rcases le_total q lo with h | h
  · have e : max lo (min hi q) = lo := max_eq_left ((min_le_right _ _).trans h)
    rw [e]
    calc f lo ≤ max (f q) (f x) := hf.le_max_of_mem_Icc hq hx0 ⟨h, hx1⟩
      _ = f x := max_eq_right (hmin x hx0)
  · rcases le_total hi q with h' | h'
    · have e : max lo (min hi q) = hi := by
        rw [min_eq_left h']; exact max_eq_right hlh
      rw [e]
      calc f hi ≤ max (f x) (f q) := hf.le_max_of_mem_Icc hx0 hq ⟨hx2, h'⟩
        _ = f x := max_eq_left (hmin x hx0)
    · have e : max lo (min hi q) = q := by
        rw [min_eq_right h']; exact max_eq_right h
      rw [e]
      exact hmin x hx0

/-- A convex function on `z > 0` that is minimal at a real `t ∈ [lo, hi]` among the points of
`[lo, hi]` is minimal over the integers `k ∈ [lo, hi]` at `⌊t⌋` or `⌈t⌉`. -/
theorem adjacent_min_of_convex {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f) {lo hi : ℕ}
    (hlo : 1 ≤ lo) {t : ℝ} (ht1 : (lo : ℝ) ≤ t) (ht2 : t ≤ hi)
    (hmin : ∀ x ∈ Icc (lo : ℝ) hi, f t ≤ f x) :
    (lo ≤ ⌊t⌋₊ ∧ ⌊t⌋₊ ≤ hi ∧ lo ≤ ⌈t⌉₊ ∧ ⌈t⌉₊ ≤ hi) ∧
      ∀ k : ℕ, lo ≤ k → k ≤ hi → min (f ⌊t⌋₊) (f ⌈t⌉₊) ≤ f k := by
  have hfl1 : lo ≤ ⌊t⌋₊ := Nat.le_floor ht1
  have hfl2 : ⌊t⌋₊ ≤ hi := Nat.floor_le_of_le ht2 |>.trans le_rfl
  have hce1 : lo ≤ ⌈t⌉₊ := hfl1.trans (Nat.floor_le_ceil t)
  have hce2 : ⌈t⌉₊ ≤ hi := Nat.ceil_le.mpr ht2
  refine ⟨⟨hfl1, hfl2, hce1, hce2⟩, fun k hk1 hk2 => ?_⟩
  have hlo0 : (0 : ℝ) < lo := by exact_mod_cast hlo
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le hlo0 (by exact_mod_cast hk1)
  have ht0 : 0 < t := lt_of_lt_of_le hlo0 ht1
  have hkI : (k : ℝ) ∈ Icc (lo : ℝ) hi := ⟨by exact_mod_cast hk1, by exact_mod_cast hk2⟩
  have hfk := hmin k hkI
  rcases Nat.lt_or_ge ⌊t⌋₊ k with h | h
  · -- `⌈t⌉ ≤ ⌊t⌋ + 1 ≤ k`
    have hck : ⌈t⌉₊ ≤ k := (Nat.ceil_le_floor_add_one t).trans h
    have hc0 : (0 : ℝ) < ⌈t⌉₊ := lt_of_lt_of_le hlo0 (by exact_mod_cast hce1)
    have hle : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
    refine min_le_of_right_le ?_
    calc f ⌈t⌉₊ ≤ max (f t) (f k) := hf.le_max_of_mem_Icc ht0 hk0 ⟨hle, by exact_mod_cast hck⟩
      _ = f k := max_eq_right hfk
  · have hle : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht0.le
    have hf0 : (0 : ℝ) < ⌊t⌋₊ := lt_of_lt_of_le hlo0 (by exact_mod_cast hfl1)
    refine min_le_of_left_le ?_
    calc f ⌊t⌋₊ ≤ max (f k) (f t) :=
          hf.le_max_of_mem_Icc hk0 ht0 ⟨by exact_mod_cast h, hle⟩
      _ = f k := max_eq_left hfk

/-- **The elementary minimization of Section 4.5.** For naturals `1 ≤ lo ≤ hi` and the clipped
value `t = endpointClip a lo hi` (`q_n` clipped to `[lo, hi]` if `a > 0`; `hi` if `a ≤ 0`), the
integers `⌊t⌋` and `⌈t⌉` lie in `[lo, hi]` and, for every integer `k ∈ [lo, hi]`,
`min (F ⌊t⌋) (F ⌈t⌉) ≤ F k` where `F z = a z + 2 log 2 / z - log z`. -/
theorem endpointShape_adjacent_min (a : ℝ) {lo hi : ℕ} (hlo : 1 ≤ lo) (hlh : lo ≤ hi) :
    (lo ≤ ⌊endpointClip a lo hi⌋₊ ∧ ⌊endpointClip a lo hi⌋₊ ≤ hi ∧
        lo ≤ ⌈endpointClip a lo hi⌉₊ ∧ ⌈endpointClip a lo hi⌉₊ ≤ hi) ∧
      ∀ k : ℕ, lo ≤ k → k ≤ hi →
        min (endpointShape a (2 * Real.log 2) ⌊endpointClip a lo hi⌋₊)
            (endpointShape a (2 * Real.log 2) ⌈endpointClip a lo hi⌉₊) ≤
          endpointShape a (2 * Real.log 2) k := by
  have hlo0 : (0 : ℝ) < lo := by exact_mod_cast hlo
  have hlhR : (lo : ℝ) ≤ hi := by exact_mod_cast hlh
  have hlog2 : 0 < 2 * Real.log 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
  have hconv := (strictConvexOn_endpointShape a hlog2.le).convexOn
  by_cases ha : 0 < a
  · have hclip : endpointClip a lo hi = max (lo : ℝ) (min (hi : ℝ) (endpointMinimizer a)) := by
      simp [endpointClip_eq, ha]
    rw [hclip]
    refine adjacent_min_of_convex hconv hlo (le_max_left _ _)
      (max_le hlhR (min_le_left _ _)) ?_
    intro x hx
    exact clip_le_of_convex hconv (endpointMinimizer_pos ha)
      (fun z hz => endpointShape_minimizer_le ha hz) hlo0 hlhR hx
  · have hclip : endpointClip a lo hi = (hi : ℝ) := by simp [endpointClip_eq, ha]
    rw [hclip]
    have hanti := strictAntiOn_endpointShape (not_lt.mp ha) hlog2
    refine adjacent_min_of_convex hconv hlo hlhR le_rfl ?_
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hlo0 hx1
    rcases hx2.lt_or_eq with h | h
    · exact (hanti hx0 (show (0 : ℝ) < hi from lt_of_lt_of_le hlo0 hlhR) h).le
    · rw [h]

/-- For `a ≤ 0` the minimum over `[lo, hi]` is at `hi` (the manuscript: "if `a_n ≤ 0` it is
decreasing"). -/
theorem endpointShape_min_right_of_nonpos {a : ℝ} (ha : a ≤ 0) {lo hi : ℕ} (hlo : 1 ≤ lo)
    {k : ℕ} (hk1 : lo ≤ k) (hk2 : k ≤ hi) :
    endpointShape a (2 * Real.log 2) hi ≤ endpointShape a (2 * Real.log 2) k := by
  have hlog2 : 0 < 2 * Real.log 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
  have hanti := strictAntiOn_endpointShape ha hlog2
  have hk0 : (0 : ℝ) < k := by
    have : (0 : ℝ) < lo := by exact_mod_cast hlo
    exact lt_of_lt_of_le this (by exact_mod_cast hk1)
  rcases hk2.lt_or_eq with h | h
  · exact (hanti hk0 (show (0 : ℝ) < hi from lt_of_lt_of_le hk0 (by exact_mod_cast hk2))
      (by exact_mod_cast h)).le
  · rw [h]

/-! ### The finite criterion `ℋ_n` -/

/-- The `z`-independent part of `ℋ_n` (`Λ_n + log 2 + log √C_n`). -/
@[expose] noncomputable def kzConst (l μ : ℤ) (n : ℕ) : ℝ :=
  (Real.log (kzKappa n) - Real.log (kzContent l μ n) - kzJ μ n +
      n * (kzL l μ n - kzT2 l n - kzT3 μ n - kzE) - 4 * Real.log 2) +
    (Real.log 2 +
      Real.log √((jacobiWronskianConstant ((l : ℚ) / 3) ((μ : ℚ) / 2) n : ℚ) : ℝ))

theorem kzConst_eq (l μ : ℤ) (n : ℕ) : kzConst l μ n =
    (Real.log (kzKappa n) - Real.log (kzContent l μ n) - kzJ μ n +
        n * (kzL l μ n - kzT2 l n - kzT3 μ n - kzE) - 4 * Real.log 2) +
      (Real.log 2 +
        Real.log √((jacobiWronskianConstant ((l : ℚ) / 3) ((μ : ℚ) / 2) n : ℚ) : ℝ)) := (rfl)

/-- `ℋ_n` is strictly convex on `z > 0`. -/
theorem strictConvexOn_kzCriterionFn {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    (n : ℕ) : StrictConvexOn ℝ (Ioi 0) (kzCriterionFn l μ n) := by
  have hlog2 : 0 ≤ 2 * Real.log 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
  have h := (strictConvexOn_endpointShape (kzSlope l μ n) hlog2).add_convexOn
    (convexOn_const (kzConst l μ n) (convex_Ioi (0 : ℝ)))
  refine h.congr fun z hz => ?_
  have hz' : z ≠ 0 := (show (0 : ℝ) < z from hz).ne'
  simp only [Pi.add_apply, endpointShape_eq, kzConst_eq]
  rw [kzCriterionFn_eq_add hl hμ n hz']
  ring

theorem kzCriterionFn_eq_const_add {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    (n : ℕ) {z : ℝ} (hz : z ≠ 0) :
    kzCriterionFn l μ n z = kzConst l μ n + endpointShape (kzSlope l μ n) (2 * Real.log 2) z := by
  rw [kzCriterionFn_eq_add hl hμ n hz, endpointShape_eq, kzConst_eq]

/-- **The adjacent-integer reduction for `ℋ_n`.** For naturals `1 ≤ lo ≤ hi` and the clipped value
`t = endpointClip a_n lo hi`, the integers `⌊t⌋`, `⌈t⌉` lie in `[lo, hi]` and
`min (ℋ_n ⌊t⌋) (ℋ_n ⌈t⌉) ≤ ℋ_n k` for every integer degree `k ∈ [lo, hi]`. -/
theorem kzCriterionFn_adjacent_min {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    (n : ℕ) {lo hi : ℕ} (hlo : 1 ≤ lo) (hlh : lo ≤ hi) :
    (lo ≤ ⌊endpointClip (kzSlope l μ n) lo hi⌋₊ ∧ ⌊endpointClip (kzSlope l μ n) lo hi⌋₊ ≤ hi ∧
        lo ≤ ⌈endpointClip (kzSlope l μ n) lo hi⌉₊ ∧
        ⌈endpointClip (kzSlope l μ n) lo hi⌉₊ ≤ hi) ∧
      ∀ k : ℕ, lo ≤ k → k ≤ hi →
        min (kzCriterionFn l μ n ⌊endpointClip (kzSlope l μ n) lo hi⌋₊)
            (kzCriterionFn l μ n ⌈endpointClip (kzSlope l μ n) lo hi⌉₊) ≤
          kzCriterionFn l μ n k := by
  obtain ⟨hb, hk⟩ := endpointShape_adjacent_min (kzSlope l μ n) hlo hlh
  refine ⟨hb, fun k hk1 hk2 => ?_⟩
  have hpos : ∀ x : ℕ, lo ≤ x → (x : ℝ) ≠ 0 := fun x hx =>
    (Nat.cast_pos.mpr (lt_of_lt_of_le hlo hx)).ne'
  rw [kzCriterionFn_eq_const_add hl hμ n (hpos _ hb.1), kzCriterionFn_eq_const_add hl hμ n
    (hpos _ hb.2.2.1), kzCriterionFn_eq_const_add hl hμ n (hpos _ hk1), min_add_add_left]
  have := hk k hk1 hk2
  linarith

/-- The reduction used with the finite criterion: if `S < ℋ_n` at the two integers adjacent to the
clipped value, then `S < ℋ_n(k)` for every integer degree `k ∈ [lo, hi]`. -/
theorem lt_kzCriterionFn_of_adjacent {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    (n : ℕ) {lo hi : ℕ} (hlo : 1 ≤ lo) (hlh : lo ≤ hi) {S : ℝ}
    (h1 : S < kzCriterionFn l μ n ⌊endpointClip (kzSlope l μ n) lo hi⌋₊)
    (h2 : S < kzCriterionFn l μ n ⌈endpointClip (kzSlope l μ n) lo hi⌉₊) {k : ℕ} (hk1 : lo ≤ k)
    (hk2 : k ≤ hi) : S < kzCriterionFn l μ n k := by
  have h := (kzCriterionFn_adjacent_min hl hμ n hlo hlh).2 k hk1 hk2
  rcases lt_min_iff.mpr ⟨h1, h2⟩ with h3
  exact lt_of_lt_of_le h3 h

/-! ### Agreement with `Remarks/Prose.lean` -/

/-- With `c = 2 log 2`, `endpointShape` is the profile `finiteCriterionProfile` of
`Remarks/Prose.lean`. -/
theorem endpointShape_two_log_two (a z : ℝ) :
    endpointShape a (2 * Real.log 2) z = finiteCriterionProfile a z := by
  rw [endpointShape_eq, finiteCriterionProfile_eq]

/-- `endpointMinimizer` is the minimizer `finiteCriterionMinimizer` of `Remarks/Prose.lean`. -/
theorem endpointMinimizer_eq_finiteCriterionMinimizer (a : ℝ) :
    endpointMinimizer a = finiteCriterionMinimizer a := by
  rw [endpointMinimizer_eq, finiteCriterionMinimizer_eq]

end ArithmeticOfJacobiPolynomials
