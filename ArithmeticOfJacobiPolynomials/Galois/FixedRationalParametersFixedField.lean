/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Galois.FixedRationalParametersQuadratic
public import ArithmeticOfJacobiPolynomials.Galois.InertiaMembership
public import ArithmeticOfJacobiPolynomials.Galois.FixedFieldDisjointness

/-!
# Theorem 1.6: fixed number fields (Corollary 5.14)

For a fixed number field `E` and `c ∈ ℚ^×`, for all large `n` the splitting fields of the
dominant factor `h_n` of `P_n^{(α,β)}` and of `h_n(1 + cX²)` are linearly disjoint from `E`
(Corollary 5.14; `fixedField_isDominant_jacobiP`, unfolded form). Following the manuscript,
the cycles of Proposition 5.2 lie in inertia groups at the selected primes
(`exists_isCycle_galPerm_jacobiP_mem_inertia`), restriction to the splitting field of `h_n` (or
`h_n(1 + cX²)`) keeps them in inertia groups (`restrict_mem_inertia_comap`), and a normal
subgroup containing them is everything (Lemma 5.6); the fixed-field tool
`FixedFieldDisjointness.exists_bound_fixedField` turns this into linear disjointness.

`fixedRationalParameters_unfolded` packages all assertions of Theorem 1.6 with the dominant-factor
and denominator conditions unfolded.
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial Filter NumberField TensorProduct

namespace FixedRationalParameters

/-! ### Normal subgroups containing the cycles -/

open Classical in
/-- A normal subgroup of `Gal(h) = S_M` containing a single even-length cycle `2 ≤ d < M` is
everything (Lemma 5.6 (1)). -/
theorem eq_top_of_normal_of_symm {h : ℚ[X]} (hS : GaloisGroupIsSymmetric h)
    {N : Subgroup h.Gal} (hN : N.Normal) {τ : h.Gal} (hτN : τ ∈ N)
    (hτ : (galPerm h τ).IsCycle) {d : ℕ} (hd : (galPerm h τ).support.card = d) (heven : Even d)
    (hd2 : 2 ≤ d) (hdM : d < Fintype.card (h.rootSet h.SplittingField)) : N = ⊤ := by
  have htop := eq_top_of_normal_of_isCycle_of_even
    (hN.map (galPerm h) ((galoisGroupIsSymmetric_iff h).mp hS).2)
    (Subgroup.mem_map_of_mem _ hτN) hτ hd heven hd2 hdM
  rw [eq_top_iff]
  intro x _
  have hx : galPerm h x ∈ N.map (galPerm h) := by rw [htop]; trivial
  obtain ⟨x', hx', hxx'⟩ := Subgroup.mem_map.mp hx
  rwa [galPerm_injective h hxx'] at hx'

open Classical in
/-- A normal subgroup of `Gal(H) = W_M` containing single `2d₁`- and `2d₂`-cycles, `d₁` even,
`d₂` odd, `1 ≤ dᵢ < M`, is everything (Lemma 5.6 (2)). -/
theorem eq_top_of_normal_of_wreath {H : ℚ[X]}
    (h0 : (0 : H.SplittingField) ∉ H.rootSet H.SplittingField)
    (hneg : ∀ x ∈ H.rootSet H.SplittingField, -x ∈ H.rootSet H.SplittingField)
    (hW : GaloisGroupIsWreath H) {N : Subgroup H.Gal} (hN : N.Normal) {τ₁ τ₂ : H.Gal}
    (hτ₁N : τ₁ ∈ N) (hτ₂N : τ₂ ∈ N) (hc₁ : (galPerm H τ₁).IsCycle)
    {d₁ d₂ : ℕ} (hd₁ : (galPerm H τ₁).support.card = 2 * d₁) (hc₂ : (galPerm H τ₂).IsCycle)
    (hd₂ : (galPerm H τ₂).support.card = 2 * d₂) (heven : Even d₁) (hodd : Odd d₂)
    (hd₁pos : 1 ≤ d₁) (hd₁N : d₁ < Nat.card (squares (H.rootSet H.SplittingField)))
    (hd₂N : d₂ < Nat.card (squares (H.rootSet H.SplittingField))) : N = ⊤ := by
  have hWr := (galoisGroupIsWreath_iff H).mp hW
  have hle : N.map (galPerm H) ≤ negCommPerm (H.rootSet H.SplittingField) := by
    rw [← hWr]
    exact Subgroup.map_le_range _ _
  have hnorm : ((N.map (galPerm H)).subgroupOf
      (negCommPerm (H.rootSet H.SplittingField))).Normal := by
    refine ⟨fun a ha b => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp ha
    have hb : (b : Equiv.Perm (H.rootSet H.SplittingField)) ∈ (galPerm H).range := by
      rw [hWr]; exact b.2
    obtain ⟨w, hw⟩ := hb
    refine Subgroup.mem_map.mpr ⟨w * x * w⁻¹, hN.conj_mem x hx w, ?_⟩
    simp [map_mul, map_inv, hw, hxa]
  have htop := eq_negCommPerm_of_normal_of_isCycle two_ne_zero h0 hneg hle hnorm
    (Subgroup.mem_map_of_mem _ hτ₁N) (Subgroup.mem_map_of_mem _ hτ₂N) hc₁ hc₂ hd₁ hd₂
    heven hodd hd₁pos hd₁N hd₂N
  rw [eq_top_iff]
  intro x _
  have hx : galPerm H x ∈ N.map (galPerm H) := by
    rw [htop, ← hWr]
    exact ⟨x, rfl⟩
  obtain ⟨x', hx', hxx'⟩ := Subgroup.mem_map.mp hx
  rwa [galPerm_injective H hxx'] at hx'

/-! ### Restricting inertia cycles -/

open Classical in
/-- Restriction of an inertia cycle of `Gal(F)` whose support consists of roots of a factor `H`:
an element of an inertia group of `Gal(H)` above the same prime, a cycle of the same length. -/
theorem exists_inertia_restrict {F H : ℚ[X]} (hF : F ≠ 0) (hHF : H ∣ F) {p : ℕ}
    (P : Ideal (𝓞 F.SplittingField)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    {σ : F.Gal} (hσI : σ ∈ P.inertia Gal(F.SplittingField/ℚ)) (hσ : (galPerm F σ).IsCycle)
    (hsupp : ∀ z ∈ (galPerm F σ).support, aeval (z : F.SplittingField) H = 0) :
    ∃ Q : Ideal (𝓞 H.SplittingField), Q.IsPrime ∧ Q.LiesOver (Ideal.span {(p : ℤ)}) ∧
      ∃ τ : H.Gal, τ ∈ Q.inertia Gal(H.SplittingField/ℚ) ∧ (galPerm H τ).IsCycle ∧
        (galPerm H τ).support.card = (galPerm F σ).support.card := by
  have := fact_splits_of_dvd hF hHF
  obtain ⟨h1, h2, -⟩ := galPerm_restrict_isCycle hF hHF hσ hsupp
  have hI := restrict_mem_inertia_comap (g := H) hσI
  have hlies := liesOver_comap_int (RingOfIntegers.mapRingHom
    (algebraMap H.SplittingField F.SplittingField)) P (Ideal.span {(p : ℤ)})
  exact ⟨_, inferInstance, hlies, _, hI, h1, h2⟩

/-! ### Inertia cycles for the primes (5.20) -/

open Classical in
/-- **Proposition 5.2 (inertia form) for the primes (5.20).** -/
theorem exists_inertia_isCycle_of_eligible {α β : ℚ} (hcond : DenomCond α β) {n p : ℕ}
    (hp : p.Prime) (h1 : (α + β).den * n + cycleBound α β < p)
    (h2 : 2 * (p + cycleBound α β) ≤ 3 * ((α + β).den * n))
    (h3 : (p : ℤ) ≡ (α + β).num [ZMOD (α + β).den]) :
    ∃ P : Ideal (𝓞 (jacobiP α β n).SplittingField), P.IsPrime ∧
      P.LiesOver (Ideal.span {(p : ℤ)}) ∧ ∃ σ : (jacobiP α β n).Gal,
        σ ∈ P.inertia Gal((jacobiP α β n).SplittingField/ℚ) ∧ (galPerm _ σ).IsCycle ∧
        ((galPerm _ σ).support.card : ℤ) =
          2 * n + 1 - ((p : ℤ) - (α + β).num) / (α + β).den := by
  have H := jacobiCycleHypotheses_of_eligible hcond hp h1 h2 h3
  have hb := cycleLength_bounds (α + β).den_pos (cycleBound_bounds α β).1 h1 h2 h3
  have hidx := H.cast_index
  rw [jacobiCycleIndex_eq] at hidx
  have hd : 2 ≤ n + 1 - jacobiCycleIndexNat p n (α + β).den (α + β).num := by
    generalize ((p : ℤ) - (α + β).num) / ((α + β).den : ℤ) = k at hidx hb
    omega
  have eα : ((α.num : ℚ) / ((α.den : ℤ) : ℚ)) = α := by push_cast; exact Rat.num_div_den α
  have eβ : ((β.num : ℚ) / ((β.den : ℤ) : ℚ)) = β := by push_cast; exact Rat.num_div_den β
  obtain ⟨P₀, hP₀, hP₀l, σ₀, hσ₀I, hσ₀, hcard₀⟩ := exists_isCycle_galPerm_jacobiP_mem_inertia H hd
  have key : ∃ P : Ideal (𝓞 (jacobiP ((α.num : ℚ) / ((α.den : ℤ) : ℚ))
      ((β.num : ℚ) / ((β.den : ℤ) : ℚ)) n).SplittingField), P.IsPrime ∧
      P.LiesOver (Ideal.span {(p : ℤ)}) ∧ ∃ σ : (jacobiP ((α.num : ℚ) / ((α.den : ℤ) : ℚ))
      ((β.num : ℚ) / ((β.den : ℤ) : ℚ)) n).Gal,
        σ ∈ P.inertia Gal((jacobiP ((α.num : ℚ) / ((α.den : ℤ) : ℚ))
          ((β.num : ℚ) / ((β.den : ℤ) : ℚ)) n).SplittingField/ℚ) ∧ (galPerm _ σ).IsCycle ∧
        (galPerm _ σ).support.card = n + 1 - jacobiCycleIndexNat p n (α + β).den (α + β).num :=
    ⟨P₀, hP₀.isPrime, hP₀l, σ₀, hσ₀I, hσ₀, hcard₀⟩
  rw [eα, eβ] at key
  obtain ⟨P, hP, hPl, σ, hσI, hσ, hcard⟩ := key
  refine ⟨P, hP, hPl, σ, hσI, hσ, ?_⟩
  rw [hcard]
  generalize ((p : ℤ) - (α + β).num) / ((α + β).den : ℤ) = k at hidx hb ⊢
  omega

open Classical in
/-- **Proposition 5.2 (quadratic, inertia form) for the primes (5.20).** -/
theorem exists_inertia_isCycle_comp_of_eligible {α β : ℚ} (hcond : DenomCond α β) {n p : ℕ}
    (hp : p.Prime) (h1 : (α + β).den * n + cycleBound α β < p)
    (h2 : 2 * (p + cycleBound α β) ≤ 3 * ((α + β).den * n))
    (h3 : (p : ℤ) ≡ (α + β).num [ZMOD (α + β).den]) {c : ℚ} (hc : c ≠ 0)
    (hcp : padicValRat p c = 0) :
    ∃ P : Ideal (𝓞 ((jacobiP α β n).comp (1 + C c * polyX ^ 2)).SplittingField), P.IsPrime ∧
      P.LiesOver (Ideal.span {(p : ℤ)}) ∧ ∃ σ : ((jacobiP α β n).comp (1 + C c * polyX ^ 2)).Gal,
        σ ∈ P.inertia Gal(((jacobiP α β n).comp (1 + C c * polyX ^ 2)).SplittingField/ℚ) ∧
        (galPerm _ σ).IsCycle ∧
        ((galPerm _ σ).support.card : ℤ) =
          2 * (2 * n + 1 - ((p : ℤ) - (α + β).num) / (α + β).den) := by
  have H := jacobiCycleHypotheses_of_eligible hcond hp h1 h2 h3
  have hb := cycleLength_bounds (α + β).den_pos (cycleBound_bounds α β).1 h1 h2 h3
  have hidx := H.cast_index
  rw [jacobiCycleIndex_eq] at hidx
  have hD2 := (denomCond_facts hcond).1
  have h2n : 2 * n ≤ (α + β).den * n := Nat.mul_le_mul_right n hD2
  have h2d : 2 * (n + 1 - jacobiCycleIndexNat p n (α + β).den (α + β).num) < p := by
    have := H.one_le_index
    omega
  have eα : ((α.num : ℚ) / ((α.den : ℤ) : ℚ)) = α := by push_cast; exact Rat.num_div_den α
  have eβ : ((β.num : ℚ) / ((β.den : ℤ) : ℚ)) = β := by push_cast; exact Rat.num_div_den β
  obtain ⟨P₀, hP₀, hP₀l, σ₀, hσ₀I, hσ₀, hcard₀, -⟩ :=
    exists_isCycle_galPerm_jacobiP_comp_mem_inertia H hc hcp h2d
  have key : ∃ P : Ideal (𝓞 ((jacobiP ((α.num : ℚ) / ((α.den : ℤ) : ℚ))
      ((β.num : ℚ) / ((β.den : ℤ) : ℚ)) n).comp (1 + C c * polyX ^ 2)).SplittingField),
      P.IsPrime ∧ P.LiesOver (Ideal.span {(p : ℤ)}) ∧
      ∃ σ : ((jacobiP ((α.num : ℚ) / ((α.den : ℤ) : ℚ))
        ((β.num : ℚ) / ((β.den : ℤ) : ℚ)) n).comp (1 + C c * polyX ^ 2)).Gal,
        σ ∈ P.inertia Gal(((jacobiP ((α.num : ℚ) / ((α.den : ℤ) : ℚ))
          ((β.num : ℚ) / ((β.den : ℤ) : ℚ)) n).comp (1 + C c * polyX ^ 2)).SplittingField/ℚ) ∧
        (galPerm _ σ).IsCycle ∧ (galPerm _ σ).support.card =
          2 * (n + 1 - jacobiCycleIndexNat p n (α + β).den (α + β).num) :=
    ⟨P₀, hP₀.isPrime, hP₀l, σ₀, hσ₀I, hσ₀, hcard₀⟩
  rw [eα, eβ] at key
  obtain ⟨P, hP, hPl, σ, hσI, hσ, hcard⟩ := key
  refine ⟨P, hP, hPl, σ, hσI, hσ, ?_⟩
  rw [hcard]
  generalize ((p : ℤ) - (α + β).num) / ((α + β).den : ℤ) = k at hidx hb ⊢
  have := H.index_le_n
  omega

/-! ### Corollary 5.14 -/

/-- A nonzero multiple `f = h k` can be written `f = κ h g` with `g` monic. -/
theorem exists_monic_cofactor {f h : ℚ[X]} (hf : f ≠ 0) (hdvd : h ∣ f) :
    ∃ g : ℚ[X], ∃ κ : ℚ, g.Monic ∧ f = C κ * h * g := by
  obtain ⟨k, hk⟩ := hdvd
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hf (by rw [hk, mul_zero])
  have hlc : k.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hk0
  refine ⟨k * C k.leadingCoeff⁻¹, k.leadingCoeff, monic_mul_leadingCoeff_inv hk0, ?_⟩
  rw [hk]
  have e : C k.leadingCoeff * C k.leadingCoeff⁻¹ = (1 : ℚ[X]) := by
    rw [← C_mul, mul_inv_cancel₀ hlc, C_1]
  linear_combination (-(h * k)) * e

open Classical in
/-- **Corollary 5.14** (unfolded form). For a fixed number field `E` and
`c ∈ ℚ^×`, for all large `n` the splitting fields of the dominant factor `h` of `P_n^{(α,β)}`
and of `h(1 + cX²)` are linearly disjoint from `E` over `ℚ`. In particular (the second sentence
of the corollary) `h` and `h(1 + cX²)` remain irreducible over `E`, with groups `S_M` and `W_M`
respectively (`M = deg h`).

Conditional on [BMOR, Corollary 1.7], [BMOR, Proposition 6.19], Brun–Titchmarsh [MV, Theorem 2]
and [Jones, Corollary 1.3], taken as the hypotheses `hBMOR`, `h619`, `hBT`, `hJones`. -/
theorem fixedField_isDominant_jacobiP (hBMOR : BMORPrimeCountingBound)
    (h619 : BMORLargeModulusPrimeCounting) (hBT : BrunTitchmarshInequality)
    (hJones : JonesCycleTheorem) {α β : ℚ} (hcond : DenomCond α β) (E : Type) [Field E]
    [NumberField E] {c : ℚ} (hc : c ≠ 0) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ h : ℚ[X], IsDominant (jacobiP α β n) h →
      IsField (h.SplittingField ⊗[ℚ] E) ∧
      IsField ((h.comp (1 + C c * polyX ^ 2)).SplittingField ⊗[ℚ] E) ∧
      Irreducible (h.map (algebraMap ℚ E)) ∧ GaloisGroupIsSymmetric (h.map (algebraMap ℚ E)) ∧
      Irreducible ((h.comp (1 + C c * polyX ^ 2)).map (algebraMap ℚ E)) ∧
      GaloisGroupIsWreath ((h.comp (1 + C c * polyX ^ 2)).map (algebraMap ℚ E)) := by
  obtain ⟨R, hR⟩ := FixedFieldDisjointness.exists_bound_fixedField E
  obtain ⟨hD2, hr, hgc⟩ := denomCond_facts hcond
  have hgr := gcd_num_two_den hcond
  have hDpos := (α + β).den_pos
  obtain ⟨N₀, hN₀⟩ := galoisGroupIsSymmetric_isDominant_jacobiP hBMOR h619 hBT hJones hcond
  obtain ⟨Nq, hNq⟩ := quadratic_isDominant_jacobiP hBMOR h619 hBT hJones hcond hc
  obtain ⟨C₀, N₁, hN₁⟩ := natDegree_isDominant_jacobiP h619 hcond 1 one_pos
  have eve := eventually_exists_prime_upper hBMOR h619 (B := cycleBound α β) hD2 hgc
  have evo := eventually_exists_prime_upper hBMOR h619 (B := cycleBound α β) hD2 hgr
  have ev3 := eventually_le_log_natCast (10 * |C₀| + 1)
  have ev4 := eventually_ge_atTop
    (N₀ + Nq + N₁ + R + 100 * ((α + β).num.natAbs + 1) + c.num.natAbs + c.den + 1)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eve.and (evo.and (ev3.and ev4)))
  refine ⟨N, fun n hn h hh => ?_⟩
  obtain ⟨⟨pe, hpe, he1, he2, he3, he4⟩, ⟨po, hpo, ho1, ho2, ho3, ho4⟩, hL, hn'⟩ := hN n hn
  have hhd := (isDominant_iff _ _).mp hh
  have hdeg := natDegree_jacobiP_le α β n
  obtain ⟨he3', heven⟩ := modEq_and_even_of_modEq_add (n := n) hDpos he4
  obtain ⟨ho3', hodd⟩ := modEq_and_odd_of_modEq (n := n) hDpos ho4
  have hnDn : n ≤ (α + β).den * n := Nat.le_mul_of_pos_left n hDpos
  -- the linear inertia cycle at `pe`
  obtain ⟨P, hP, hPl, σ, hσI, hσ, hσc⟩ := exists_inertia_isCycle_of_eligible hcond hpe he1 he2 he3'
  have hf0 := ne_zero_of_isCycle hσ
  obtain ⟨g, κ, hg, hfac⟩ := exists_monic_cofactor hf0 hhd.2.2.1
  obtain ⟨hS, -⟩ := hN₀ n (by omega) h g κ hh hg hfac
  obtain ⟨hIrrC, hW, -⟩ := hNq n (by omega) h g κ hh hg hfac
  have hbe := cycleLength_bounds hDpos (cycleBound_bounds α β).1 he1 he2 he3'
  have hbo := cycleLength_bounds hDpos (cycleBound_bounds α β).1 ho1 ho2 ho3'
  have hnr : 100 * (|(α + β).num| + 1) ≤ (n : ℤ) := by
    have h0 : ((α + β).num.natAbs : ℤ) = |(α + β).num| := Int.natCast_natAbs _
    have h1 : 100 * ((α + β).num.natAbs + 1) ≤ n := by omega
    have h2 : (100 * (((α + β).num.natAbs : ℤ) + 1) : ℤ) ≤ n := by exact_mod_cast h1
    rw [← h0]
    exact h2
  have hue := cycleLength_le_of_upper hDpos he3 he3' hnr
  have huo := cycleLength_le_of_upper hDpos ho3 ho3' hnr
  -- `M ≥ 0.9 n`
  have hM := hN₁ n (by omega) h hh
  rw [Real.rpow_one] at hM
  have hn100 : (100 : ℝ) ≤ n := by
    have : 100 ≤ n := by omega
    exact_mod_cast this
  have hlogpos : 0 < Real.log n := by linarith [abs_nonneg C₀]
  have hCn : C₀ * n / Real.log n ≤ 0.1 * n := by
    rw [div_le_iff₀ hlogpos]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ n)
      (by linarith [le_abs_self C₀] : (0 : ℝ) ≤ Real.log n - 10 * C₀)]
  have hM9 : 0.9 * (n : ℝ) ≤ h.natDegree := by linarith
  have hcp : ∀ p : ℕ, p.Prime → (α + β).den * n + cycleBound α β < p →
      padicValRat p c = 0 := fun p hp hp1 =>
    padicValRat_eq_zero_of_lt hp hc (by omega) (by omega)
  -- the quadratic inertia cycles at `pe` and `po`
  obtain ⟨Pe, hPe, hPel, σe, hσeI, hσe, hσec⟩ :=
    exists_inertia_isCycle_comp_of_eligible hcond hpe he1 he2 he3' hc (hcp pe hpe he1)
  obtain ⟨Po, hPo, hPol, σo, hσoI, hσo, hσoc⟩ :=
    exists_inertia_isCycle_comp_of_eligible hcond hpo ho1 ho2 ho3' hc (hcp po hpo ho1)
  generalize hde : 2 * (n : ℤ) + 1 - ((pe : ℤ) - (α + β).num) / (α + β).den = de at *
  generalize hdo : 2 * (n : ℤ) + 1 - ((po : ℤ) - (α + β).num) / (α + β).den = do_ at *
  have hde0 : 0 ≤ de := by omega
  have hdo0 : 0 ≤ do_ := by omega
  lift de to ℕ using hde0
  lift do_ to ℕ using hdo0
  have hue' : (100 : ℝ) * de ≤ 61 * n := by exact_mod_cast hue
  have huo' : (100 : ℝ) * do_ ≤ 61 * n := by exact_mod_cast huo
  have hdeM : de < h.natDegree := by
    have : (de : ℝ) < h.natDegree := by linarith
    exact_mod_cast this
  have hdoM : do_ < h.natDegree := by
    have : (do_ : ℝ) < h.natDegree := by linarith
    exact_mod_cast this
  have heven' : Even de := (Int.even_coe_nat _).mp heven
  have hodd' : Odd do_ := (Int.odd_coe_nat _).mp hodd
  have hcardM : Fintype.card (h.rootSet h.SplittingField) = h.natDegree :=
    card_rootSet_of_irreducible hhd.2.1
  have hR₁ := hR h (fun Nh hNh hNI => by
    -- `h`: the even inertia cycle at `pe`
    have hσc' : (galPerm _ σ).support.card = de := by exact_mod_cast hσc
    obtain ⟨Q, hQ, hQl, τ, hτI, hτ, hτc⟩ := exists_inertia_restrict hf0 hhd.2.2.1 (p := pe) P hσI hσ
      (aeval_eq_zero_of_isDominant hdeg hh hσ (by omega))
    exact eq_top_of_normal_of_symm hS hNh (hNI pe hpe (by omega) Q hQl hτI) hτ
      (hτc.trans hσc') heven' (by omega) (by rw [hcardM]; exact hdeM))
  have hR₂ := hR (h.comp (1 + C c * polyX ^ 2)) (fun Nh hNh hNI => by
    -- `h(1 + cX²)`: the inertia `2d`-cycles at `pe` and `po`
    have hσec' : (galPerm _ σe).support.card = 2 * de := by exact_mod_cast hσec
    have hσoc' : (galPerm _ σo).support.card = 2 * do_ := by exact_mod_cast hσoc
    have hF0 := ne_zero_of_isCycle hσe
    have hHF : h.comp (1 + C c * polyX ^ 2) ∣ (jacobiP α β n).comp (1 + C c * polyX ^ 2) := by
      obtain ⟨k, hk⟩ := hhd.2.2.1
      exact ⟨k.comp (1 + C c * polyX ^ 2), by rw [hk, mul_comp]⟩
    obtain ⟨Qe, hQe, hQel, τe, hτeI, hτe, hτec⟩ :=
      exists_inertia_restrict hF0 hHF (p := pe) Pe hσeI hσe
      (aeval_eq_zero_of_isCycle_comp hc rfl hdeg hh hσe (by omega))
    obtain ⟨Qo, hQo, hQol, τo, hτoI, hτo, hτoc⟩ :=
      exists_inertia_restrict hF0 hHF (p := po) Po hσoI hσo
      (aeval_eq_zero_of_isCycle_comp hc rfl hdeg hh hσo (by omega))
    obtain ⟨-, -, h0, hneg, hNsq⟩ := galoisGroupIsWreath_comp hhd.2.1 hS hc rfl
      (eval_one_ne_zero_of_dvd ((denomCond_iff _ _).mp hcond).2.2.1 hhd.2.2.1) hτo
      (hτoc.trans hσoc') hodd' hdoM
    exact eq_top_of_normal_of_wreath h0 hneg hW hNh (hNI pe hpe (by omega) Qe hQel hτeI)
      (hNI po hpo (by omega) Qo hQol hτoI) hτe (hτec.trans hσec') hτo (hτoc.trans hσoc')
      heven' hodd' (by omega) (by rw [hNsq]; exact hdeM) (by rw [hNsq]; exact hdoM))
  obtain ⟨hF₁, hI₁, hS₁, -⟩ := hR₁
  obtain ⟨hF₂, hI₂, -, hW₂⟩ := hR₂
  exact ⟨hF₁, hF₂, hI₁ hhd.2.1, hS₁ hS, hI₂ hIrrC, hW₂ hW⟩

/-! ### Theorem 1.6 -/

/-- **Theorem 1.6**, with the dominant-factor and denominator conditions unfolded
(`IsDominant`, `DenomCond`; these are `ArithmeticOfJacobiPolynomials.IsDominantFactor` and
`ArithmeticOfJacobiPolynomials.JacobiDenominatorCondition` verbatim).

Conditional on [BMOR, Corollary 1.7], [BMOR, Proposition 6.19], Brun–Titchmarsh [MV, Theorem 2]
and [Jones, Corollary 1.3], taken as the hypotheses `hBMOR`, `h619`, `hBT`, `hJones`. -/
theorem fixedRationalParameters_unfolded (hBMOR : BMORPrimeCountingBound)
    (h619 : BMORLargeModulusPrimeCounting) (hBT : BrunTitchmarshInequality)
    (hJones : JonesCycleTheorem) :
    ∀ α β : ℚ, DenomCond α β →
    (∃ N : ℕ, ∀ n ≥ N, ∃ h : ℚ[X], IsDominant (jacobiP α β n) h ∧
        ∀ h' : ℚ[X], IsDominant (jacobiP α β n) h' → h' = h) ∧
    (∃ N : ℕ, ∀ n ≥ N, ∀ h g : ℚ[X], ∀ κ : ℚ, IsDominant (jacobiP α β n) h → g.Monic →
        jacobiP α β n = C κ * h * g →
        GaloisGroupIsSymmetric h ∧ Function.Bijective (Gal.restrictProd h g)) ∧
    (∀ A : ℝ, 0 < A → ∃ (Cst : ℝ) (N : ℕ), ∀ n ≥ N, ∀ h : ℚ[X],
        IsDominant (jacobiP α β n) h →
        ((n : ℝ) - h.natDegree) ≤ Cst * n / Real.log n ^ A) ∧
    (∀ c : ℚ, c ≠ 0 → ∃ N : ℕ, ∀ n ≥ N, ∀ h g : ℚ[X], ∀ κ : ℚ,
        IsDominant (jacobiP α β n) h → g.Monic → jacobiP α β n = C κ * h * g →
        Irreducible (h.comp (1 + C c * polyX ^ 2)) ∧
        GaloisGroupIsWreath (h.comp (1 + C c * polyX ^ 2)) ∧
        Function.Bijective (Gal.restrictProd (h.comp (1 + C c * polyX ^ 2))
          (g.comp (1 + C c * polyX ^ 2)))) ∧
    (∀ (E : Type) [Field E] [NumberField E], ∀ c : ℚ, c ≠ 0 → ∃ N : ℕ, ∀ n ≥ N,
        ∀ h : ℚ[X], IsDominant (jacobiP α β n) h →
        IsField (h.SplittingField ⊗[ℚ] E) ∧
        IsField ((h.comp (1 + C c * polyX ^ 2)).SplittingField ⊗[ℚ] E)) := by
  intro α β hcond
  exact ⟨exists_unique_isDominant_jacobiP h619 hcond,
    galoisGroupIsSymmetric_isDominant_jacobiP hBMOR h619 hBT hJones hcond,
    natDegree_isDominant_jacobiP h619 hcond,
    fun c hc => quadratic_isDominant_jacobiP hBMOR h619 hBT hJones hcond hc,
    fun E _ _ c hc => by
      obtain ⟨N, hN⟩ := fixedField_isDominant_jacobiP hBMOR h619 hBT hJones hcond E hc
      exact ⟨N, fun n hn h hh => ⟨(hN n hn h hh).1, (hN n hn h hh).2.1⟩⟩⟩

end FixedRationalParameters

end ArithmeticOfJacobiPolynomials
