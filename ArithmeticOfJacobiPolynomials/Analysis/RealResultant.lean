/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Polynomial.ResultantRoots
public import ArithmeticOfJacobiPolynomials.External
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.RingTheory.Polynomial.Content
public import Mathlib.Analysis.Normed.Ring.Basic

/-!
# The real lower bound for factor resultants (Lemma 2.6)

This file contains the archimedean part of Lemma 2.6 of the manuscript.

* `shiftedTwoAdicOrder F` is `c_F = min_j v_2([X^j] F(2X+1))`, the minimum over the nonzero
  coefficients.
* `two_pow_shiftedTwoAdicOrder_lt_leadingCoeff`: the endpoint bound `u > 2^{c_F}` for an
  integral polynomial with all roots real, nonzero and in `(-1,1)`, obtained from
  `u^2 ∏_i (1 - α_i^2) = |F(1) F(-1)|` and `2^{c_F} ∣ F(±1)`.
* `vandermondeSq_le_of_mem_Icc`, `neg_log_vandermondeSq_div_ge`: the interval Vandermonde
  bound (`intervalVandermondeBound`, proved Lemma 2.5) rescaled from `[0,1]` to `[-1,1]`:
  `V_F ≤ d^d 2^{-(d-1)(d-2)}` and `-log V_F / d ≥ (d-3) log 2 - log d`.
* `realResultant_lowerBound_of_twoAdic_bound`: the inequalities (2.11) and (2.12) of Lemma 2.6,
  with the 2-adic input of the proof, `v_2(R) ≤ e c_F + d c_G - de + d D_2`, taken as a
  hypothesis in place of the bound on the projective row sums of `h(2X+1)` at `2`.
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset

/-- `c_F = min_j v_2([X^j] F(2X+1))`, the minimum being over the nonzero coefficients of
`F(2X+1)` (zero coefficients have valuation `∞`). It is `0` for `F = 0`. -/
noncomputable def shiftedTwoAdicOrder (F : ℤ[X]) : ℕ :=
  sInf ((fun j => padicValInt 2 ((F.comp (2 * polyX + 1)).coeff j)) ''
    ((F.comp (2 * polyX + 1)).support : Set ℕ))

theorem shiftedTwoAdicOrder_eq (F : ℤ[X]) : shiftedTwoAdicOrder F =
    sInf ((fun j => padicValInt 2 ((F.comp (2 * polyX + 1)).coeff j)) ''
      ((F.comp (2 * polyX + 1)).support : Set ℕ)) := (rfl)

theorem shiftedTwoAdicOrder_le {F : ℤ[X]} {j : ℕ} (hj : (F.comp (2 * polyX + 1)).coeff j ≠ 0) :
    shiftedTwoAdicOrder F ≤ padicValInt 2 ((F.comp (2 * polyX + 1)).coeff j) :=
  Nat.sInf_le ⟨j, mem_support_iff.mpr hj, rfl⟩

/-- `2^{c_F}` divides every coefficient of `F(2X+1)`. -/
theorem two_pow_dvd_coeff_comp (F : ℤ[X]) (j : ℕ) :
    (2 : ℤ) ^ shiftedTwoAdicOrder F ∣ (F.comp (2 * polyX + 1)).coeff j := by
  by_cases hj : (F.comp (2 * polyX + 1)).coeff j = 0
  · simp [hj]
  · exact (pow_dvd_pow 2 (shiftedTwoAdicOrder_le hj)).trans (by exact_mod_cast padicValInt_dvd _)

private theorem dvd_eval_of_dvd_coeff {p : ℤ[X]} {m : ℤ} (h : ∀ j, m ∣ p.coeff j) (x : ℤ) :
    m ∣ p.eval x := by
  rw [eval_eq_sum_range]
  exact Finset.dvd_sum fun j _ => (h j).mul_right _

/-- `2^{c_F} ∣ F(1)`. -/
theorem two_pow_dvd_eval_one (F : ℤ[X]) : (2 : ℤ) ^ shiftedTwoAdicOrder F ∣ F.eval 1 := by
  have := dvd_eval_of_dvd_coeff (two_pow_dvd_coeff_comp F) 0
  simpa [eval_comp] using this

/-- `2^{c_F} ∣ F(-1)`. -/
theorem two_pow_dvd_eval_neg_one (F : ℤ[X]) : (2 : ℤ) ^ shiftedTwoAdicOrder F ∣ F.eval (-1) := by
  have := dvd_eval_of_dvd_coeff (two_pow_dvd_coeff_comp F) (-1)
  have h : (2 : ℤ) * -1 + 1 = -1 := by norm_num
  simpa [eval_comp, h] using this

/-- A nonzero multiple of `m` has absolute value at least `|m|`. -/
private theorem abs_le_abs_of_dvd {m n : ℤ} (h : m ∣ n) (hn : n ≠ 0) : |m| ≤ |n| := by
  have := Int.le_of_dvd (abs_pos.mpr hn) ((abs_dvd_abs _ _).mpr h)
  exact this

/-- `|F(x)| = u ∏ |x - α|` for a polynomial splitting over `ℝ`. -/
private theorem abs_eval_eq_of_splits {f : ℝ[X]} (hf : f.Splits) (x : ℝ) :
    |f.eval x| = |f.leadingCoeff| * (f.roots.map fun a => |x - a|).prod := by
  rw [hf.eval_eq_prod_roots, abs_mul]
  have := map_multiset_prod (absHom : ℝ →*₀ ℝ) (f.roots.map fun a => x - a)
  simp only [Multiset.map_map] at this
  exact congrArg _ this

/-- **The endpoint bound** `u > 2^{c_F}` of Lemma 2.6. Let `F ∈ ℤ[X]` have positive degree and
positive leading coefficient `u`, with all its roots real, nonzero and in `(-1,1)`. Then
`u > 2^{c_F}`, where `c_F = min_j v_2([X^j] F(2X+1))`. -/
theorem two_pow_shiftedTwoAdicOrder_lt_leadingCoeff {F : ℤ[X]} (hdeg : 0 < F.natDegree)
    (hlc : 0 < F.leadingCoeff)
    (hcard : (F.map (Int.castRingHom ℝ)).roots.card = F.natDegree)
    (hroots : ∀ x ∈ (F.map (Int.castRingHom ℝ)).roots, x ≠ 0 ∧ -1 < x ∧ x < 1) :
    (2 : ℤ) ^ shiftedTwoAdicOrder F < F.leadingCoeff := by
  set Fr := F.map (Int.castRingHom ℝ) with hFr
  have hinj : Function.Injective (Int.castRingHom ℝ) := Int.cast_injective
  have hdegr : Fr.natDegree = F.natDegree := natDegree_map_eq_of_injective hinj F
  have hlcr : Fr.leadingCoeff = (F.leadingCoeff : ℝ) := leadingCoeff_map_of_injective hinj F
  have hsplit : Fr.Splits := splits_iff_card_roots.mpr (by rw [hdegr]; exact hcard)
  have hFr0 : Fr ≠ 0 := by
    intro h0; rw [h0, natDegree_zero] at hdegr; omega
  set c := shiftedTwoAdicOrder F
  -- the integer values at `±1`
  have hev1 : Fr.eval 1 = ((F.eval 1 : ℤ) : ℝ) := by
    rw [hFr, eval_one_map]; rfl
  have hevm1 : Fr.eval (-1) = ((F.eval (-1) : ℤ) : ℝ) := by
    have := eval_intCast_map (Int.castRingHom ℝ) F (-1)
    push_cast at this
    rw [hFr, this]; rfl
  have hne1 : F.eval 1 ≠ 0 := by
    intro h0
    have : (1 : ℝ) ∈ Fr.roots := (mem_roots hFr0).mpr (by simp [IsRoot, hev1, h0])
    exact lt_irrefl _ (hroots 1 this).2.2
  have hnem1 : F.eval (-1) ≠ 0 := by
    intro h0
    have : (-1 : ℝ) ∈ Fr.roots := (mem_roots hFr0).mpr (by simp [IsRoot, hevm1, h0])
    exact lt_irrefl _ (hroots (-1) this).2.1
  have hb1 : ((2 : ℤ) ^ c : ℝ) ≤ |((F.eval 1 : ℤ) : ℝ)| := by
    have := abs_le_abs_of_dvd (two_pow_dvd_eval_one F) hne1
    rw [abs_of_pos (by positivity : (0 : ℤ) < 2 ^ c)] at this
    exact_mod_cast this
  have hbm1 : ((2 : ℤ) ^ c : ℝ) ≤ |((F.eval (-1) : ℤ) : ℝ)| := by
    have := abs_le_abs_of_dvd (two_pow_dvd_eval_neg_one F) hnem1
    rw [abs_of_pos (by positivity : (0 : ℤ) < 2 ^ c)] at this
    exact_mod_cast this
  -- `|F(1) F(-1)| = u^2 ∏ (1 - α^2)`
  have hu : (0 : ℝ) < F.leadingCoeff := by exact_mod_cast hlc
  have hprod : |Fr.eval 1| * |Fr.eval (-1)| =
      (F.leadingCoeff : ℝ) ^ 2 * (Fr.roots.map fun a => 1 - a ^ 2).prod := by
    rw [abs_eval_eq_of_splits hsplit, abs_eval_eq_of_splits hsplit, hlcr, abs_of_pos hu]
    have : (Fr.roots.map fun a => 1 - a ^ 2) =
        Fr.roots.map fun a => |1 - a| * |-1 - a| := by
      refine Multiset.map_congr rfl fun a ha => ?_
      obtain ⟨-, h1, h2⟩ := hroots a ha
      rw [abs_of_pos (by linarith : (0 : ℝ) < 1 - a), abs_of_neg (by linarith : -1 - a < 0)]
      ring
    rw [this, Multiset.prod_map_mul]
    ring
  have hP : (Fr.roots.map fun a => 1 - a ^ 2).prod < 1 := by
    have hne : Fr.roots ≠ 0 := by
      intro h0; rw [h0, Multiset.card_zero] at hcard; omega
    have := Multiset.prod_map_lt_prod_map hne (fun a => 1 - a ^ 2) (fun _ => (1 : ℝ))
      (fun a ha => by
        obtain ⟨-, h1, h2⟩ := hroots a ha
        nlinarith)
      (fun a ha => by
        obtain ⟨h0, -, -⟩ := hroots a ha
        have : 0 < a ^ 2 := by positivity
        linarith)
    simpa using this
  have hsq : ((2 : ℝ) ^ c) ^ 2 < (F.leadingCoeff : ℝ) ^ 2 := by
    have h1 : ((2 : ℝ) ^ c) * (2 ^ c) ≤ |Fr.eval 1| * |Fr.eval (-1)| := by
      rw [hev1, hevm1]
      push_cast at hb1 hbm1
      exact mul_le_mul hb1 hbm1 (by positivity) (abs_nonneg _)
    rw [hprod] at h1
    have hu2 : 0 < (F.leadingCoeff : ℝ) ^ 2 := by positivity
    nlinarith
  have : (2 : ℝ) ^ c < F.leadingCoeff :=
    lt_of_pow_lt_pow_left₀ 2 hu.le hsq
  exact_mod_cast this

/-- **Vandermonde bound on `[-1,1]`.** Rescaling the interval Vandermonde bound
(Lemma 2.5, `intervalVandermondeBound`) from `[0,1]` to `[-1,1]`: for `α_1, …, α_d ∈ [-1,1]`,
`∏_{i<j} (α_i - α_j)^2 ≤ d^d 2^{-(d-1)(d-2)}`. -/
theorem vandermondeSq_le_of_mem_Icc {d : ℕ} (α : Fin d → ℝ)
    (hα : ∀ i, α i ∈ Set.Icc (-1 : ℝ) 1) :
    ∏ i, ∏ j ∈ univ.filter (fun j => i < j), (α i - α j) ^ 2 ≤
      (d : ℝ) ^ d / 2 ^ ((d - 1) * (d - 2)) := by
  set t : Fin d → ℝ := fun i => (α i + 1) / 2
  have ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1 := by
    intro i
    obtain ⟨h1, h2⟩ := hα i
    constructor <;> simp only [t] <;> linarith
  have hW := intervalVandermondeBound d t ht
  have hsplit : ∏ i, ∏ j ∈ univ.filter (fun j => i < j), (α i - α j) ^ 2 =
      (∏ i : Fin d, ∏ j ∈ univ.filter (fun j => i < j), ((2 : ℝ) * 2)) *
        ∏ i, ∏ j ∈ univ.filter (fun j => i < j), (t i - t j) ^ 2 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [t]; ring
  have hcount : ∏ i : Fin d, ∏ j ∈ univ.filter (fun j => i < j), ((2 : ℝ) * 2) =
      2 ^ (d * (d - 1)) := by
    rw [← prod_prod_erase_eq_prod_prod_lt (fun (_ _ : Fin d) => (2 : ℝ))]
    simp [Finset.prod_const, Finset.card_erase_of_mem, ← pow_mul, mul_comm]
  have hexp : d * (d - 1) + (d - 1) * (d - 2) = 2 * (d - 1) ^ 2 := by
    rcases d with _ | _ | d
    · rfl
    · rfl
    · simp only [Nat.add_sub_cancel]
      rw [show d + 1 + 1 - 2 = d by omega]
      ring
  rw [hsplit, hcount]
  have h2pos : (0 : ℝ) < 2 ^ ((d - 1) * (d - 2)) := by positivity
  rw [le_div_iff₀ h2pos]
  calc 2 ^ (d * (d - 1)) * (∏ i, ∏ j ∈ univ.filter (fun j => i < j), (t i - t j) ^ 2) *
        2 ^ ((d - 1) * (d - 2))
      = 2 ^ (2 * (d - 1) ^ 2) *
          ∏ i, ∏ j ∈ univ.filter (fun j => i < j), (t i - t j) ^ 2 := by
        rw [← hexp, pow_add]; ring
    _ ≤ 2 ^ (2 * (d - 1) ^ 2) * ((d : ℝ) ^ d / 2 ^ (2 * (d - 1) ^ 2)) :=
        mul_le_mul_of_nonneg_left hW (by positivity)
    _ = (d : ℝ) ^ d := by field_simp

/-- **Logarithmic Vandermonde bound on `[-1,1]`.** For `d ≥ 1` distinct `α_i ∈ [-1,1]` and
`V = ∏_{i<j} (α_i - α_j)^2`, `-log V / d ≥ (d-3) log 2 - log d`. -/
theorem neg_log_vandermondeSq_div_ge {d : ℕ} (hd : 1 ≤ d)
    {α : Fin d → ℝ} (hinj : Function.Injective α) (hα : ∀ i, α i ∈ Set.Icc (-1 : ℝ) 1) :
    ((d : ℝ) - 3) * Real.log 2 - Real.log d ≤
      -Real.log (∏ i, ∏ j ∈ univ.filter (fun j => i < j), (α i - α j) ^ 2) / d := by
  set V := ∏ i, ∏ j ∈ univ.filter (fun j => i < j), (α i - α j) ^ 2
  have hVpos : 0 < V := by
    refine Finset.prod_pos fun i _ => Finset.prod_pos fun j hj => ?_
    have hij : i ≠ j := (mem_filter.mp hj).2.ne
    exact lt_of_le_of_ne (sq_nonneg _)
      (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr (hinj.ne hij))))
  have hle := vandermondeSq_le_of_mem_Icc α hα
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog : Real.log V ≤ d * Real.log d - ((d - 1) * (d - 2) : ℕ) * Real.log 2 := by
    have := Real.log_le_log hVpos hle
    rwa [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow] at this
  have hcast : (d : ℝ) * ((d : ℝ) - 3) ≤ ((d - 1) * (d - 2) : ℕ) := by
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
    rcases k with _ | k
    · norm_num
    · rw [show k + 1 + 1 - 1 = k + 1 by omega, show k + 1 + 1 - 2 = k by omega]
      push_cast
      nlinarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hdpos]
  nlinarith [mul_le_mul_of_nonneg_right hcast hl2.le]

/-- **Lemma 2.6, archimedean part, with the 2-adic input as a hypothesis.**

Let `h ∈ ℚ[x]` have only nonzero real roots in `(-1,1)` (as in Lemma 2.6), suppose `b_h = h(1)`
is a positive integer and `|h'(α)| > γ > 0` at every real root. Let `κ > 0` and `F, G ∈ ℤ[x]`
with `F G = κ h`, `lc F > 0`, `1 ≤ d = deg F ≤ e = deg G` and `d + e = N`. Put
`R = Res(F, G)`, `𝓡 = |R| / 2^{v_2(R)}`, `u = lc F`, `c_F = min_j v_2([X^j] F(2X+1))`
(`shiftedTwoAdicOrder`), likewise `c_G`, let `α_1, …, α_d` be distinct roots of `F` (hence all
of them) and `V_F = ∏_{i<j} (α_i - α_j)^2`.

In the manuscript the bound `v_2(R) ≤ e c_F + d c_G - de + d D_2` is derived from the
hypothesis that the projective row sums of `h(2X+1)` at `2` are at most `D_2`; here it is taken
as the hypothesis `h2`. Using the proved interval Vandermonde bound (Lemma 2.5), the
conclusions of Lemma 2.6 hold: `u > 2^{c_F}`, (2.11)
`log 𝓡 / d > e log 2 - log V_F / d + log (γ / b_h) - D_2 log 2 + ((e-d)/d) log (u / 2^{c_F})`,
and (2.12) `log 𝓡 / d > (N-3) log 2 - log d + log (γ / b_h) - D_2 log 2`.

The step `log κ - (c_F + c_G) log 2 ≥ -log b_h` of the manuscript's proof is the hypothesis
`hκb : 2^{c_F} 2^{c_G} ≤ κ b_h`; it is proved from `h ∈ ℤ[1/2][x]` and the primitivity of `H` in
`SourceRealResultantTwoPower` (`two_pow_shiftedTwoAdicOrder_mul_le`). The remaining hypotheses of
Lemma 2.6 (`deg h = N`, `lc h > 0`, distinct roots, primitivity of `F`, `G`, `lc G > 0`) are not
needed for this part. -/
theorem realResultant_lowerBound_of_twoAdic_bound {h : ℚ[X]}
    (hroots : ∀ x ∈ (h.map (algebraMap ℚ ℝ)).roots, x ≠ 0 ∧ -1 < x ∧ x < 1)
    {b : ℕ} (hb : 0 < b) (hb1 : h.eval 1 = b)
    {γ : ℝ} (hγ : 0 < γ)
    (hγ' : ∀ x ∈ (h.map (algebraMap ℚ ℝ)).roots,
      γ < |(derivative (h.map (algebraMap ℚ ℝ))).eval x|)
    {κ : ℚ} (hκ : 0 < κ) {F G : ℤ[X]}
    (hFG : (F * G).map (Int.castRingHom ℚ) = C κ * h) (hFlc : 0 < F.leadingCoeff)
    {d e N : ℕ} (hdF : F.natDegree = d) (heG : G.natDegree = e) (hd : 1 ≤ d) (hde : d ≤ e)
    (hdeN : d + e = N)
    (hκb : (2 : ℝ) ^ shiftedTwoAdicOrder F * 2 ^ shiftedTwoAdicOrder G ≤ κ * b)
    {D₂ : ℝ}
    (h2 : (padicValInt 2 (F.resultant G) : ℝ) ≤
      e * shiftedTwoAdicOrder F + d * shiftedTwoAdicOrder G - d * e + d * D₂)
    {α : Fin d → ℝ} (hα : Function.Injective α)
    (hαF : ∀ i, (F.map (Int.castRingHom ℝ)).eval (α i) = 0) :
    (2 : ℤ) ^ shiftedTwoAdicOrder F < F.leadingCoeff ∧
    (e : ℝ) * Real.log 2 -
          Real.log (∏ i, ∏ j ∈ univ.filter (fun j => i < j), (α i - α j) ^ 2) / d +
        Real.log (γ / b) - D₂ * Real.log 2 +
        ((e : ℝ) - d) / d * Real.log (F.leadingCoeff / 2 ^ shiftedTwoAdicOrder F) <
      Real.log (|(F.resultant G : ℝ)| / 2 ^ padicValInt 2 (F.resultant G)) / d ∧
    ((N : ℝ) - 3) * Real.log 2 - Real.log d + Real.log (γ / b) - D₂ * Real.log 2 <
      Real.log (|(F.resultant G : ℝ)| / 2 ^ padicValInt 2 (F.resultant G)) / d := by
  classical
  set hr := h.map (algebraMap ℚ ℝ) with hhr
  set Fr := F.map (Int.castRingHom ℝ) with hFr
  set Gr := G.map (Int.castRingHom ℝ) with hGr
  set cF := shiftedTwoAdicOrder F with hcF_def
  set cG := shiftedTwoAdicOrder G with hcG_def
  set R := F.resultant G with hR_def
  set V := ∏ i, ∏ j ∈ univ.filter (fun j => i < j), (α i - α j) ^ 2 with hV_def
  set u : ℝ := (F.leadingCoeff : ℝ) with hu_def
  have hinj : Function.Injective (Int.castRingHom ℝ) := Int.cast_injective
  have hh0 : h ≠ 0 := by
    rintro rfl
    simp only [eval_zero] at hb1
    exact absurd (by exact_mod_cast hb1.symm : b = 0) hb.ne'
  have hr0 : hr ≠ 0 := Polynomial.map_ne_zero hh0
  have hκr : (0 : ℝ) < κ := by exact_mod_cast hκ
  have hHr : Fr * Gr = C (κ : ℝ) * hr := by
    have := congrArg (Polynomial.map (algebraMap ℚ ℝ)) hFG
    simp only [Polynomial.map_map, Polynomial.map_mul, map_C] at this
    rw [show (algebraMap ℚ ℝ).comp (Int.castRingHom ℚ) = Int.castRingHom ℝ from
        RingHom.ext_int _ _] at this
    rw [hFr, hGr, this]
    rfl
  have hF0 : F ≠ 0 := by rintro rfl; simp at hFlc
  have hFr0 : Fr ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hF0
  have hFrdeg : Fr.natDegree = d := by rw [hFr, natDegree_map_eq_of_injective hinj, hdF]
  have hGrdeg : Gr.natDegree = e := by rw [hGr, natDegree_map_eq_of_injective hinj, heG]
  have hFrlc : Fr.leadingCoeff = u := leadingCoeff_map_of_injective hinj F
  have hu : 0 < u := by rw [hu_def]; exact_mod_cast hFlc
  have hHr0 : Fr * Gr ≠ 0 := by rw [hHr]; exact mul_ne_zero (C_ne_zero.mpr hκr.ne') hr0
  have hHroots : (Fr * Gr).roots = hr.roots := by rw [hHr, roots_C_mul _ hκr.ne']
  have hFroots_le : Fr.roots ≤ hr.roots :=
    hHroots ▸ roots.le_of_dvd hHr0 (dvd_mul_right Fr Gr)
  have hmem : ∀ i, α i ∈ Fr.roots := fun i => (mem_roots hFr0).mpr (hαF i)
  have hle : univ.val.map α ≤ Fr.roots := by
    refine (Multiset.le_iff_subset (Multiset.Nodup.map hα univ.nodup)).mpr fun x hx => ?_
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hx
    exact hmem i
  have hFroots : univ.val.map α = Fr.roots := by
    refine Multiset.eq_of_le_of_card_le hle ?_
    rw [Multiset.card_map, Finset.card_val, card_univ, Fintype.card_fin, ← hFrdeg]
    exact card_roots' Fr
  have hFrcard : Fr.roots.card = Fr.natDegree := by
    rw [← hFroots, hFrdeg]; simp
  have hFr_eq : Fr = C u * ∏ j, (polyX - C (α j)) := by
    rw [prod_X_sub_C_eq_multiset, hFroots, ← hFrlc]
    exact (C_leadingCoeff_mul_prod_multiset_X_sub_C hFrcard).symm
  have hαhr : ∀ i, α i ∈ hr.roots := fun i => Multiset.mem_of_le hFroots_le (hmem i)
  -- the endpoint bound `u > 2^{c_F}`
  have hcF : (2 : ℤ) ^ cF < F.leadingCoeff :=
    two_pow_shiftedTwoAdicOrder_lt_leadingCoeff (by omega) hFlc
      (hFrcard.trans (natDegree_map_eq_of_injective hinj F))
      (fun x hx => hroots x (Multiset.mem_of_le hFroots_le hx))
  have hcFr : (2 : ℝ) ^ cF < u := by
    have : (((2 : ℤ) ^ cF : ℤ) : ℝ) < (F.leadingCoeff : ℝ) := Int.cast_lt.mpr hcF
    rw [hu_def]
    push_cast at this
    exact this
  refine ⟨hcF, ?_⟩
  -- the resultant–derivative identity
  have hRr : resultant Fr Gr = (R : ℝ) := by
    have h1 : resultant Fr Gr = resultant Fr Gr F.natDegree G.natDegree := by
      rw [← natDegree_map_eq_of_injective hinj F, ← natDegree_map_eq_of_injective hinj G]
    rw [h1, resultant_map_map]
    rfl
  have hid := abs_resultant_eq_div hu.ne' hα Gr (by rw [hGrdeg]; exact hde)
  rw [← hFr_eq, hRr, hGrdeg, hHr, abs_of_pos hu] at hid
  simp only [derivative_C_mul, eval_mul, eval_C, abs_mul, abs_of_pos hκr] at hid
  have hVpos : 0 < V := by
    refine Finset.prod_pos fun i _ => Finset.prod_pos fun j hj => ?_
    have hij : i ≠ j := (mem_filter.mp hj).2.ne
    exact lt_of_le_of_ne (sq_nonneg _)
      (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr (hα.ne hij))))
  have hprod_lt : ((κ : ℝ) * γ) ^ d < ∏ i, ((κ : ℝ) * |(derivative hr).eval (α i)|) := by
    have hc : ∏ _i : Fin d, ((κ : ℝ) * γ) = ((κ : ℝ) * γ) ^ d := by simp
    rw [← hc]
    have hne : (univ : Finset (Fin d)).val ≠ 0 := by
      have : (univ : Finset (Fin d)).Nonempty := univ_nonempty_iff.mpr ⟨⟨0, by omega⟩⟩
      simpa [Finset.nonempty_iff_ne_empty, ← Finset.val_eq_zero] using this
    exact Multiset.prod_map_lt_prod_map hne _ _ (fun i _ => by positivity)
      (fun i _ => mul_lt_mul_of_pos_left (hγ' _ (hαhr i)) hκr)
  have hRgt : u ^ (e - d) * ((κ : ℝ) * γ) ^ d / V < |(R : ℝ)| := by
    rw [hid]
    gcongr
  have hRpos : 0 < |(R : ℝ)| := lt_of_le_of_lt (by positivity) hRgt
  have hlogR : ((e : ℝ) - d) * Real.log u + d * (Real.log κ + Real.log γ) - Real.log V <
      Real.log |(R : ℝ)| := by
    have := Real.log_lt_log (by positivity) hRgt
    rwa [Real.log_div (by positivity) hVpos.ne', Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_mul hκr.ne' hγ.ne', Nat.cast_sub hde] at this
  -- `κ b_h ≥ 2^{c_F + c_G}` is the hypothesis `hκb`
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
  have hlogκb : ((cF : ℝ) + cG) * Real.log 2 ≤ Real.log κ + Real.log b := by
    have := Real.log_le_log (by positivity) hκb
    rwa [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
      Real.log_mul hκr.ne' hbpos.ne', ← add_mul] at this
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog𝓡 : Real.log (|(R : ℝ)| / 2 ^ padicValInt 2 R) =
      Real.log |(R : ℝ)| - (padicValInt 2 R : ℝ) * Real.log 2 := by
    rw [Real.log_div hRpos.ne' (by positivity), Real.log_pow]
  have hγb : Real.log (γ / b) = Real.log γ - Real.log b := Real.log_div hγ.ne' hbpos.ne'
  have huc : Real.log (u / 2 ^ cF) = Real.log u - cF * Real.log 2 := by
    rw [Real.log_div hu.ne' (by positivity), Real.log_pow]
  have h2' := mul_le_mul_of_nonneg_right h2 hl2.le
  have hκb' := mul_le_mul_of_nonneg_left hlogκb hdpos.le
  have h211 : (e : ℝ) * Real.log 2 - Real.log V / d + Real.log (γ / b) - D₂ * Real.log 2 +
        ((e : ℝ) - d) / d * Real.log (u / 2 ^ cF) <
      Real.log (|(R : ℝ)| / 2 ^ padicValInt 2 R) / d := by
    rw [lt_div_iff₀ hdpos, hlog𝓡, hγb, huc]
    have hexp : ((e : ℝ) * Real.log 2 - Real.log V / d + (Real.log γ - Real.log b) -
          D₂ * Real.log 2 + ((e : ℝ) - d) / d * (Real.log u - cF * Real.log 2)) * d =
        e * d * Real.log 2 - Real.log V + d * (Real.log γ - Real.log b) - d * D₂ * Real.log 2 +
          ((e : ℝ) - d) * (Real.log u - cF * Real.log 2) := by
      field_simp
    rw [hexp]
    nlinarith
  refine ⟨h211, ?_⟩
  -- (2.12)
  have hVd := neg_log_vandermondeSq_div_ge hd hα (fun i => by
    obtain ⟨-, h1, h2⟩ := hroots _ (hαhr i)
    exact ⟨h1.le, h2.le⟩)
  rw [neg_div] at hVd
  have hlast : 0 ≤ ((e : ℝ) - d) / d * Real.log (u / 2 ^ cF) := by
    have hed : (0 : ℝ) ≤ (e : ℝ) - d := by
      have : (d : ℝ) ≤ e := by exact_mod_cast hde
      linarith
    refine mul_nonneg (div_nonneg hed hdpos.le) (Real.log_nonneg ?_)
    rw [le_div_iff₀ (by positivity), one_mul]
    exact hcFr.le
  have hNde : (N : ℝ) = d + e := by exact_mod_cast hdeN.symm
  rw [hNde]
  linarith

end ArithmeticOfJacobiPolynomials
