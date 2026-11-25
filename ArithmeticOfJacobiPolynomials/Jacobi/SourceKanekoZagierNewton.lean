/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.KanekoZagier.BadPrimes
public import ArithmeticOfJacobiPolynomials.Jacobi.KanekoZagierLocal
public import ArithmeticOfJacobiPolynomials.Padic.SourceNewtonRoots

/-!
# Theorem A.1, `n = 5` and `n = 15`: the Newton faces and the factor degrees

The manuscript factors `T_n^{λ,1}` over `ℚ_3` by the faces of its Newton polygon.

* `n = 5`: the polygon of `(j, v_3(b_j))` has the vertices `(0,8), (1,6), (4,1), (5,0)`, hence
  sides of slopes `-2, -5/3, -1` and horizontal lengths `1, 3, 1`; heights `2, 5, 1`.
* `n = 15`: the vertices are `(0,23), (13,3), (15,0)`: slopes `-20/13, -3/2`, lengths `13, 2`.

On each side the height and length are coprime, so every irreducible factor whose roots have the
side's slope has degree divisible by the length; the lengths add up to the degree of the side,
so each side carries exactly one irreducible factor.

Formalization. `NewtonPolygonRootSlopes` (Berger, Theorem 2.4) gives the root valuations of
`T_n` in `PadicAlgCl 3` as `3/2 - (1/2)(W(j+1) - W(j))` for the hull `W` of
`Φ_{n,1}` (`kanekoZagier_rootValuations`); the hull is computed on the finite table with
`lowerHull_eq_line`. All roots of one monic irreducible factor `g ∈ ℚ_3[X]` have the same
valuation `v_3(g(0)) / deg g` (`padicVal_root_of_factor`); `class_sum` gives, for each slope `s`,
`∑_{g : slope g = s} deg g = #{roots of valuation s}`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial

local notation "K" => PadicAlgCl 3

/-- The slope `v_3(g(0)) / deg g` of a polynomial over `ℚ_3`. -/
@[expose] noncomputable def factorSlope (g : ℚ_[3][X]) : ℝ :=
  ((g.coeff 0).valuation : ℝ) / g.natDegree

/-- Every root in `PadicAlgCl 3` of a monic irreducible `g ∈ ℚ_3[X]` has valuation
`v_3(g(0)) / deg g`. -/
theorem padicVal_root_of_factor {g : ℚ_[3][X]} (hg : g.Monic) (hirr : Irreducible g)
    (hg0 : g.coeff 0 ≠ 0) {z : K} (hz : aeval z g = 0) : padicVal 3 z = factorSlope g := by
  have hdpos : 0 < g.natDegree := hirr.natDegree_pos
  have hd : (0 : ℝ) < g.natDegree := by exact_mod_cast hdpos
  have hn := norm_pow_natDegree_eq_norm_coeff_zero hg hirr hz
  rw [PadicAlgCl.norm_extends, Padic.norm_eq_zpow_neg_valuation hg0] at hn
  have hz0 : ‖z‖ ≠ 0 := by
    intro h
    rw [h, zero_pow hdpos.ne'] at hn
    exact (zpow_pos (by positivity) _).ne hn
  have hzpos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz0)
  have hlog : (g.natDegree : ℝ) * Real.log ‖z‖ = -((g.coeff 0).valuation : ℝ) * Real.log 3 := by
    rw [← Real.log_pow, hn, Real.log_zpow]
    push_cast
    ring
  have h3 : Real.log 3 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [padicVal_def, factorSlope, eq_div_iff hd.ne', Real.logb]
  simp only [Nat.cast_ofNat]
  field_simp
  linarith

/-- The valuations of the roots of a monic irreducible factor are all `factorSlope g`. -/
theorem rootVals_of_factor {g : ℚ_[3][X]} (hg : g.Monic) (hirr : Irreducible g)
    (hg0 : g.coeff 0 ≠ 0) :
    (g.map (algebraMap ℚ_[3] K)).roots.map (padicVal 3) =
      Multiset.replicate g.natDegree (factorSlope g) := by
  rw [Multiset.eq_replicate]
  refine ⟨?_, fun b hb => ?_⟩
  · rw [Multiset.card_map, IsAlgClosed.card_roots_eq_natDegree, natDegree_map]
  · rw [Multiset.mem_map] at hb
    obtain ⟨z, hz, rfl⟩ := hb
    have hroot := (mem_roots ((hg.map (algebraMap ℚ_[3] K)).ne_zero)).mp hz
    refine padicVal_root_of_factor hg hirr hg0 ?_
    rw [aeval_def, eval₂_eq_eval_map]
    exact hroot

/-- The roots of the image in `K` of a product of factors. -/
theorem roots_map_eq_bind {T : ℚ[X]} {S : Multiset ℚ_[3][X]}
    (hS : ∀ g ∈ S, g.Monic ∧ Irreducible g)
    (hprod : S.prod = T.map (algebraMap ℚ ℚ_[3])) :
    (T.map (algebraMap ℚ K)).roots =
      (S.map (Polynomial.map (algebraMap ℚ_[3] K))).bind Polynomial.roots := by
  have h1 : T.map (algebraMap ℚ K) = (S.map (Polynomial.map (algebraMap ℚ_[3] K))).prod := by
    rw [← Polynomial.map_multiset_prod, hprod, Polynomial.map_map]
    congr 1
  rw [h1, roots_multiset_prod]
  intro h0
  rw [Multiset.mem_map] at h0
  obtain ⟨g, hg, h⟩ := h0
  exact ((hS g hg).1.map (algebraMap ℚ_[3] K)).ne_zero h

theorem sum_filter_map_ite {α : Type*} (S : Multiset α) (p : α → Prop) [DecidablePred p]
    (f : α → ℕ) : ((S.filter p).map f).sum = (S.map fun a => if p a then f a else 0).sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    by_cases h : p a
    · simp [Multiset.filter_cons_of_pos _ h, ih, h]
    · simp [Multiset.filter_cons_of_neg _ h, ih, h]

/-- For each slope `s`, the degrees of the factors of slope `s` add up to the number of roots of
valuation `s`. -/
theorem class_sum {T : ℚ[X]} {S : Multiset ℚ_[3][X]} (hS : ∀ g ∈ S, g.Monic ∧ Irreducible g)
    (hprod : S.prod = T.map (algebraMap ℚ ℚ_[3])) (hT0 : T.coeff 0 ≠ 0) (s : ℝ) :
    ((S.filter fun g => factorSlope g = s).map natDegree).sum =
      ((T.map (algebraMap ℚ K)).roots.map (padicVal 3)).count s := by
  classical
  have hg0 : ∀ g ∈ S, g.coeff 0 ≠ 0 := fun g hg => by
    have hdvd : g ∣ T.map (algebraMap ℚ ℚ_[3]) := hprod ▸ Multiset.dvd_prod hg
    exact (exists_ne_le_of_irreducible_factor hT0 (hS g hg).1 (hS g hg).2 hdvd).1
  rw [roots_map_eq_bind hS hprod, Multiset.map_bind, Multiset.count_bind, Multiset.map_map,
    sum_filter_map_ite]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun g hg => ?_)
  simp only [Function.comp_apply]
  rw [rootVals_of_factor (hS g hg).1 (hS g hg).2 (hg0 g hg), Multiset.count_replicate]

/-- Every factor has a slope occurring among the root valuations. -/
theorem slope_mem {T : ℚ[X]} {S : Multiset ℚ_[3][X]} (hS : ∀ g ∈ S, g.Monic ∧ Irreducible g)
    (hprod : S.prod = T.map (algebraMap ℚ ℚ_[3])) (hT0 : T.coeff 0 ≠ 0) {g : ℚ_[3][X]}
    (hg : g ∈ S) :
    factorSlope g ∈ (T.map (algebraMap ℚ K)).roots.map (padicVal 3) := by
  classical
  rw [← Multiset.count_pos, ← class_sum hS hprod hT0]
  have hmem : g.natDegree ∈ (S.filter fun g' => factorSlope g' = factorSlope g).map natDegree :=
    Multiset.mem_map_of_mem _ (Multiset.mem_filter.mpr ⟨hg, rfl⟩)
  exact lt_of_lt_of_le (Nat.pos_of_ne_zero (hS g hg).2.natDegree_pos.ne')
    (Multiset.le_sum_of_mem hmem)

/-- A single slope class of total degree `m`, all of whose degrees are multiples of `m`, is
one factor of degree `m`. -/
theorem class_eq_singleton {S : Multiset ℚ_[3][X]} {s : ℝ} {m : ℕ} (hm : 0 < m)
    (hpos : ∀ g ∈ S, 0 < g.natDegree)
    (hdiv : ∀ g ∈ S, factorSlope g = s → m ∣ g.natDegree)
    (hsum : ((S.filter fun g => factorSlope g = s).map natDegree).sum = m) :
    (S.filter fun g => factorSlope g = s).map natDegree = {m} := by
  refine multiset_eq_singleton_of_sum hm hsum fun x hx => ?_
  rw [Multiset.mem_map] at hx
  obtain ⟨g, hg, rfl⟩ := hx
  obtain ⟨hgS, hgs⟩ := Multiset.mem_filter.mp hg
  exact Nat.le_of_dvd (hpos g hgS) (hdiv g hgS hgs)

/-- A multiset is the sum of its slope classes when all slopes lie in a duplicate-free list. -/
theorem eq_sum_filters {α : Type*} (r : α → ℝ) :
    ∀ (L : List ℝ) (S : Multiset α), L.Nodup → (∀ a ∈ S, r a ∈ L) →
      S = (L.map fun s => S.filter fun a => r a = s).sum
  | [], S, _, h => by
    simp only [List.map_nil, List.sum_nil]
    exact Multiset.eq_zero_of_forall_notMem fun a ha => by simpa using h a ha
  | s :: L, S, hnd, h => by
    classical
    have hS : S = S.filter (fun a => r a = s) + S.filter (fun a => ¬ r a = s) :=
      (Multiset.filter_add_not _ _).symm
    set S' := S.filter (fun a => ¬ r a = s) with hS'
    have hnd' := List.nodup_cons.mp hnd
    have ih := eq_sum_filters r L S' hnd'.2 (fun a ha => by
      obtain ⟨haS, hne⟩ := Multiset.mem_filter.mp ha
      rcases List.mem_cons.mp (h a haS) with h1 | h1
      · exact absurd h1 hne
      · exact h1)
    have hf : ∀ s' ∈ L, S'.filter (fun a => r a = s') = S.filter (fun a => r a = s') := by
      intro s' hs'
      rw [hS', Multiset.filter_filter]
      refine Multiset.filter_congr fun a _ => ?_
      constructor
      · exact fun h => h.1
      · intro h'
        exact ⟨h', fun h'' => hnd'.1 ((h''.symm.trans h') ▸ hs')⟩
    rw [List.map_cons, List.sum_cons, ← List.map_congr_left hf, ← ih]
    exact hS

/-- **Root valuations of `T_n^{λ,μ}` from the Newton hull.** With the cited Newton polygon
theorem, the valuations of the roots of `T_n^{λ,μ}` in `PadicAlgCl 3` are
`3/2 - (1/2)(W(j+1) - W(j))`, `j < n`, for the hull `W` of `Φ_{n,δ}`. -/
theorem kanekoZagier_rootValuations (hNP : NewtonPolygonRootSlopes) {l μ : ℤ}
    (hl : l = 1 ∨ l = -1) {δ : ℕ} (hδ : δ ≤ 1) (hμ : μ = 2 * δ - 1) (n : ℕ) :
    ((monicEndpoint ((l : ℚ) / 3) ((μ : ℚ) / 2) n).map (algebraMap ℚ K)).roots.map
        (padicVal 3) =
      (Finset.range n).val.map fun j => (3 / 2 : ℝ) - (1 / 2) *
        (lowerHull n (digitPhi n δ) ((j + 1 : ℕ) : ℝ) - lowerHull n (digitPhi n δ) (j : ℝ)) := by
  obtain ⟨hmon, hdeg, hv⟩ := kanekoZagier_monicEndpoint_data hl δ hδ hμ n
  refine rootValuations_of_hull hNP (hmon.map _) (by rw [natDegree_map, hdeg]) (digitPhi n δ)
    (by norm_num) (fun j hj => ?_)
  obtain ⟨h1, h2⟩ := hv j hj
  rw [coeff_map, eq_ratCast]
  refine ⟨by exact_mod_cast h1, ?_⟩
  rw [padicVal_ratCast_padicAlgCl h1]
  have := congrArg (Int.cast : ℤ → ℝ) h2
  push_cast at this ⊢
  linarith

/-! ### The hull of `Φ_{5,1}` and `Φ_{15,1}` -/

/-- The vertices `(0,1), (1,0), (4,-1), (5,0)` of the hull of `Φ_{5,1}`. -/
theorem lowerHull_five (k : ℕ) (hk : k ≤ 5) :
    lowerHull 5 (digitPhi 5 1) k =
      if k ≤ 1 then 1 - (k : ℝ) else if k ≤ 4 then (1 - (k : ℝ)) / 3 else (k : ℝ) - 5 := by
  by_cases h1 : k ≤ 1
  · simp only [h1, ↓reduceIte]
    have := lowerHull_eq_line (n := 5) (Φ := digitPhi 5 1) (b := 1) (τ := 1) (i := 0) (i' := 1)
      (k := k) (fun j hj => by
        interval_cases j <;> norm_num [digitPhi_eq, digitSum3_eq])
      (Nat.zero_le _) h1 (by norm_num) (by norm_num [digitPhi_eq, digitSum3_eq])
      (by norm_num [digitPhi_eq, digitSum3_eq])
    rw [this]; ring
  · by_cases h2 : k ≤ 4
    · simp only [h1, h2, ↓reduceIte]
      have := lowerHull_eq_line (n := 5) (Φ := digitPhi 5 1) (b := 1 / 3) (τ := 1 / 3) (i := 1)
        (i' := 4) (k := k) (fun j hj => by
          interval_cases j <;> norm_num [digitPhi_eq, digitSum3_eq])
        (by omega) h2 (by norm_num) (by norm_num [digitPhi_eq, digitSum3_eq])
        (by norm_num [digitPhi_eq, digitSum3_eq])
      rw [this]; ring
    · simp only [h1, h2, ↓reduceIte]
      have := lowerHull_eq_line (n := 5) (Φ := digitPhi 5 1) (b := -5) (τ := -1) (i := 4)
        (i' := 5) (k := k) (fun j hj => by
          interval_cases j <;> norm_num [digitPhi_eq, digitSum3_eq])
        (by omega) hk le_rfl (by norm_num [digitPhi_eq, digitSum3_eq])
        (by norm_num [digitPhi_eq, digitSum3_eq])
      rw [this]; ring

/-- The vertices `(0,1), (13,0), (15,0)` of the hull of `Φ_{15,1}`. -/
theorem lowerHull_fifteen (k : ℕ) (hk : k ≤ 15) :
    lowerHull 15 (digitPhi 15 1) k = if k ≤ 13 then 1 - (k : ℝ) / 13 else 0 := by
  by_cases h1 : k ≤ 13
  · simp only [h1, ↓reduceIte]
    have := lowerHull_eq_line (n := 15) (Φ := digitPhi 15 1) (b := 1) (τ := 1 / 13) (i := 0)
      (i' := 13) (k := k) (fun j hj => by
        interval_cases j <;> norm_num [digitPhi_eq, digitSum3_eq])
      (Nat.zero_le _) h1 (by norm_num) (by norm_num [digitPhi_eq, digitSum3_eq])
      (by norm_num [digitPhi_eq, digitSum3_eq])
    rw [this]; ring
  · simp only [h1, ↓reduceIte]
    have := lowerHull_eq_line (n := 15) (Φ := digitPhi 15 1) (b := 0) (τ := 0) (i := 13)
      (i' := 15) (k := k) (fun j hj => by
        interval_cases j <;> norm_num [digitPhi_eq, digitSum3_eq])
      (by omega) hk le_rfl (by norm_num [digitPhi_eq, digitSum3_eq])
      (by norm_num [digitPhi_eq, digitSum3_eq])
    rw [this]; ring

/-- The root valuations of `T_5^{λ,1}`: `2, 5/3, 5/3, 5/3, 1`. -/
theorem rootValuations_five (hNP : NewtonPolygonRootSlopes) {l : ℤ} (hl : l = 1 ∨ l = -1) :
    ((monicEndpoint ((l : ℚ) / 3) (((1 : ℤ) : ℚ) / 2) 5).map (algebraMap ℚ K)).roots.map
        (padicVal 3) = {1, 5 / 3, 5 / 3, 5 / 3, 2} := by
  rw [kanekoZagier_rootValuations hNP hl (δ := 1) le_rfl (by norm_num) 5]
  have key : ∀ j ∈ (Finset.range 5).val, ((3 / 2 : ℝ) - (1 / 2) *
      (lowerHull 5 (digitPhi 5 1) ((j + 1 : ℕ) : ℝ) - lowerHull 5 (digitPhi 5 1) (j : ℝ))) =
      (if j = 0 then 2 else if j ≤ 3 then 5 / 3 else 1) := by
    intro j hj
    have hj5 : j < 5 := Finset.mem_range.mp hj
    rw [lowerHull_five (j + 1) (by omega), lowerHull_five j (by omega)]
    interval_cases j <;> norm_num
  rw [Multiset.map_congr rfl key]
  simp [Multiset.range_succ]

/-- The root valuations of `T_15^{λ,1}`: `20/13` (13 times) and `3/2` (twice). -/
theorem rootValuations_fifteen (hNP : NewtonPolygonRootSlopes) {l : ℤ} (hl : l = 1 ∨ l = -1) :
    ((monicEndpoint ((l : ℚ) / 3) (((1 : ℤ) : ℚ) / 2) 15).map (algebraMap ℚ K)).roots.map
        (padicVal 3) = 3 / 2 ::ₘ 3 / 2 ::ₘ Multiset.replicate 13 (20 / 13) := by
  rw [kanekoZagier_rootValuations hNP hl (δ := 1) le_rfl (by norm_num) 15]
  have key : ∀ j ∈ (Finset.range 15).val, ((3 / 2 : ℝ) - (1 / 2) *
      (lowerHull 15 (digitPhi 15 1) ((j + 1 : ℕ) : ℝ) - lowerHull 15 (digitPhi 15 1) (j : ℝ))) =
      (if j < 13 then 20 / 13 else 3 / 2) := by
    intro j hj
    have hj5 : j < 15 := Finset.mem_range.mp hj
    rw [lowerHull_fifteen (j + 1) (by omega), lowerHull_fifteen j (by omega)]
    interval_cases j <;> norm_num
  rw [Multiset.map_congr rfl key]
  simp [Multiset.range_succ, Multiset.replicate_succ]

/-- If the slope of `g` is `a/b` with `a, b` coprime, then `b` divides `deg g`: the height and
the length of a Newton side are coprime. -/
theorem dvd_natDegree_of_slope {g : ℚ_[3][X]} {a b : ℕ} (hb : 0 < b) (hcop : Nat.Coprime b a)
    (hd : 0 < g.natDegree) (h : factorSlope g = (a : ℝ) / b) : b ∣ g.natDegree := by
  have hdR : (g.natDegree : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have h1 : (g.coeff 0).valuation * (b : ℤ) = g.natDegree * a := by
    have h' : ((g.coeff 0).valuation : ℝ) / g.natDegree = a / b := h
    field_simp at h'
    exact_mod_cast h'
  have h2 : (b : ℤ) ∣ (a : ℤ) * g.natDegree := ⟨(g.coeff 0).valuation, by linarith⟩
  have h3 : IsCoprime (b : ℤ) (a : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  exact Int.natCast_dvd_natCast.mp (h3.dvd_of_dvd_mul_left h2)

/-- **`n = 5`, from the root valuations.** -/
theorem factorDegrees_five {T : ℚ[X]} {S : Multiset ℚ_[3][X]}
    (hS : ∀ g ∈ S, g.Monic ∧ Irreducible g) (hprod : S.prod = T.map (algebraMap ℚ ℚ_[3]))
    (hT0 : T.coeff 0 ≠ 0)
    (hV : (T.map (algebraMap ℚ K)).roots.map (padicVal 3) = {1, 5 / 3, 5 / 3, 5 / 3, 2}) :
    S.map natDegree = {1, 1, 3} := by
  classical
  have hpos : ∀ g ∈ S, 0 < g.natDegree := fun g hg => (hS g hg).2.natDegree_pos
  have hmemV : ∀ g ∈ S, factorSlope g ∈ ({1, 5 / 3, 5 / 3, 5 / 3, 2} : Multiset ℝ) := by
    intro g hg
    have := slope_mem hS hprod hT0 hg
    rwa [hV] at this
  have hcls : ∀ s, ((S.filter fun g => factorSlope g = s).map natDegree).sum =
      ({1, 5 / 3, 5 / 3, 5 / 3, 2} : Multiset ℝ).count s := fun s => by
    rw [← hV]; exact class_sum hS hprod hT0 s
  have hsplit := eq_sum_filters factorSlope [2, 5 / 3, 1] S (by norm_num) (fun g hg => by
    have := hmemV g hg
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at this
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    tauto)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hsplit
  have e2 := class_eq_singleton (S := S) (s := 2) (m := 1) one_pos hpos
    (fun g _ _ => one_dvd _) (by rw [hcls]; norm_num [Multiset.count_cons])
  have e1 := class_eq_singleton (S := S) (s := 1) (m := 1) one_pos hpos
    (fun g _ _ => one_dvd _) (by rw [hcls]; norm_num [Multiset.count_cons])
  have e3 := class_eq_singleton (S := S) (s := 5 / 3) (m := 3) (by norm_num) hpos
    (fun g hg h => dvd_natDegree_of_slope (a := 5) (by norm_num) (by norm_num) (hpos g hg)
      (by rw [h]; norm_num))
    (by rw [hcls]; norm_num [Multiset.count_cons])
  conv_lhs => rw [hsplit]
  rw [Multiset.map_add, Multiset.map_add, e2, e3, e1]
  decide

/-- **`n = 15`, from the root valuations.** -/
theorem factorDegrees_fifteen {T : ℚ[X]} {S : Multiset ℚ_[3][X]}
    (hS : ∀ g ∈ S, g.Monic ∧ Irreducible g) (hprod : S.prod = T.map (algebraMap ℚ ℚ_[3]))
    (hT0 : T.coeff 0 ≠ 0)
    (hV : (T.map (algebraMap ℚ K)).roots.map (padicVal 3) =
      3 / 2 ::ₘ 3 / 2 ::ₘ Multiset.replicate 13 (20 / 13)) :
    S.map natDegree = {2, 13} := by
  classical
  have hpos : ∀ g ∈ S, 0 < g.natDegree := fun g hg => (hS g hg).2.natDegree_pos
  have hmemV : ∀ g ∈ S, factorSlope g ∈
      (3 / 2 ::ₘ 3 / 2 ::ₘ Multiset.replicate 13 (20 / 13) : Multiset ℝ) := by
    intro g hg
    have := slope_mem hS hprod hT0 hg
    rwa [hV] at this
  have hcls : ∀ s, ((S.filter fun g => factorSlope g = s).map natDegree).sum =
      (3 / 2 ::ₘ 3 / 2 ::ₘ Multiset.replicate 13 (20 / 13) : Multiset ℝ).count s :=
    fun s => by rw [← hV]; exact class_sum hS hprod hT0 s
  have hsplit := eq_sum_filters factorSlope [20 / 13, 3 / 2] S (by norm_num) (fun g hg => by
    have := hmemV g hg
    simp only [Multiset.mem_cons, Multiset.mem_replicate] at this
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    tauto)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hsplit
  have ea := class_eq_singleton (S := S) (s := 20 / 13) (m := 13) (by norm_num) hpos
    (fun g hg h => dvd_natDegree_of_slope (a := 20) (by norm_num) (by norm_num) (hpos g hg)
      (by rw [h]; norm_num))
    (by rw [hcls]; norm_num [Multiset.count_cons, Multiset.count_replicate])
  have eb := class_eq_singleton (S := S) (s := 3 / 2) (m := 2) (by norm_num) hpos
    (fun g hg h => dvd_natDegree_of_slope (a := 3) (by norm_num) (by norm_num) (hpos g hg)
      (by rw [h]; norm_num))
    (by rw [hcls]; norm_num [Multiset.count_cons, Multiset.count_replicate])
  conv_lhs => rw [hsplit]
  rw [Multiset.map_add, ea, eb]
  decide

/-- **Theorem A.1, `n = 5`, `μ = 1`, from the Newton polygon theorem.** The factor degrees of
`P_5^{(λ/3,1/2)}` over `ℚ_3` are `1, 1, 3`. -/
theorem natDegree_factors_kanekoZagier_five_of_newton (hNP : NewtonPolygonRootSlopes) {l : ℤ}
    (hl : l = 1 ∨ l = -1) :
    (UniqueFactorizationMonoid.factors
      ((kanekoZagierJacobi l 1 5).map (algebraMap ℚ ℚ_[3]))).map natDegree = {1, 1, 3} := by
  refine natDegree_factors_kanekoZagier_eq hl (Or.inl rfl) 5 _ fun S hS hprod => ?_
  obtain ⟨-, -, hv⟩ := kanekoZagier_monicEndpoint_data (μ := 1) hl 1 le_rfl (by norm_num) 5
  exact factorDegrees_five hS hprod (hv 0 (by norm_num)).1 (rootValuations_five hNP hl)

/-- **Theorem A.1, `n = 15`, `μ = 1`, from the Newton polygon theorem.** The factor degrees of
`P_{15}^{(λ/3,1/2)}` over `ℚ_3` are `2, 13`. -/
theorem natDegree_factors_kanekoZagier_fifteen_of_newton (hNP : NewtonPolygonRootSlopes)
    {l : ℤ} (hl : l = 1 ∨ l = -1) :
    (UniqueFactorizationMonoid.factors
      ((kanekoZagierJacobi l 1 15).map (algebraMap ℚ ℚ_[3]))).map natDegree = {2, 13} := by
  refine natDegree_factors_kanekoZagier_eq hl (Or.inl rfl) 15 _ fun S hS hprod => ?_
  obtain ⟨-, -, hv⟩ := kanekoZagier_monicEndpoint_data (μ := 1) hl 1 le_rfl (by norm_num) 15
  exact factorDegrees_fifteen hS hprod (hv 0 (by norm_num)).1 (rootValuations_fifteen hNP hl)

/-- **Theorem A.1 (local irreducibility)**, with the `n = 5, 15` factorizations obtained from
the Newton polygon theorem (Berger, Theorem 2.4) and the finite hull computation. -/
theorem kanekoZagier_localIrreducibility_of_newton (hNP : NewtonPolygonRootSlopes) :
    KanekoZagierLocalIrreducibilityStatement := by
  unfold KanekoZagierLocalIrreducibilityStatement
  intro l μ hl hμ
  have h5 : μ = 1 → (UniqueFactorizationMonoid.factors
      ((kanekoZagierJacobi l μ 5).map (algebraMap ℚ ℚ_[3]))).map natDegree = {1, 1, 3} := by
    rintro rfl; exact natDegree_factors_kanekoZagier_five_of_newton hNP hl
  have h15 : μ = 1 → (UniqueFactorizationMonoid.factors
      ((kanekoZagierJacobi l μ 15).map (algebraMap ℚ ℚ_[3]))).map natDegree = {2, 13} := by
    rintro rfl; exact natDegree_factors_kanekoZagier_fifteen_of_newton hNP hl
  refine ⟨irreducible_kanekoZagier_three_pow hl hμ, fun a => ⟨fun hirr => ?_,
    irreducible_kanekoZagier_five_mul_three_pow hl hμ a⟩, h5, h15⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hμ1, ha⟩ := hcon
  have hμ1' : μ = 1 := by omega
  have hc := card_factors_of_irreducible hirr
  interval_cases a
  · rw [show 5 * 3 ^ 0 = 5 by norm_num, h5 hμ1'] at hc
    simp at hc
  · rw [show 5 * 3 ^ 1 = 15 by norm_num, h15 hμ1'] at hc
    simp at hc

end ArithmeticOfJacobiPolynomials
