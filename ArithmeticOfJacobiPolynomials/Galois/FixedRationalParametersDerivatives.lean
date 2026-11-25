/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Galois.FixedRationalParametersFixedField
public import ArithmeticOfJacobiPolynomials.Jacobi.QuadraticTransformation
public import ArithmeticOfJacobiPolynomials.Jacobi.SymmetricIrreducibility

/-!
# Corollary 1.7: Galois groups of the reduced Gegenbauer polynomials (Section 5.6)

Fix `r ≥ 0` and a number field `E`. For all large `m` and both `δ ∈ {0,1}`, `F_{m,r,δ}` and
`Q_{m,r,δ}` (with `F_{m,r,δ}(x) = Q_{m,r,δ}(x²)`) are irreducible over `E` with groups `W_m` and
`S_m`, and their splitting fields are linearly disjoint from `E`
(`fixedDerivativesGaloisStatement`).

Following the manuscript: by the bridge (5.33) (`reducedGegenbauer_eq_jacobiP_comp`),
`F_{m,r,δ} = s · J(1 - 2x²)` and `Q_{m,r,δ} = s · J(1 - 2T)` with `J = P_m^{(δ-1/2, r)}`, whose
parameters satisfy the denominator condition with `D = 2` (`denomCond_gegenbauer`). Theorem 1.4
makes `F_{m,r,δ}` irreducible, so `J` equals its dominant factor up to a scalar; Theorem 1.6 with
`c = -2`, the inertia cycles of Proposition 5.2 and the fixed-field step
(`FixedFieldDisjointness.exists_bound_fixedField`) give the rest (`derivativeGalois_core`).
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial Filter NumberField TensorProduct

namespace FixedRationalParameters

/-! ### Scalars and affine changes -/

/-- `a h(bX + c)` is irreducible with `h`, for `a, b ≠ 0`. -/
theorem irreducible_C_mul_comp_affine {h : ℚ[X]} (hirr : Irreducible h) {a b c : ℚ}
    (ha : a ≠ 0) (hb : b ≠ 0) : Irreducible (C a * h.comp (C b * polyX + C c)) := by
  have h1 := affine_comp_affine_inv (b := b) (c := c) hb
  have h2 := affine_inv_comp_affine (b := b) (c := c) hb
  have e : (algEquivOfCompEqX _ _ h1 h2) h = h.comp (C b * polyX + C c) := by
    rw [comp_eq_aeval]
    rfl
  rw [irreducible_isUnit_mul (isUnit_C.mpr (Ne.isUnit ha)), ← e]
  exact hirr.map _

open Classical in
/-- `Gal(a h(1+cX²)/ℚ) = W_M` (the scalar version of `galoisGroupIsWreath_comp`). -/
theorem galoisGroupIsWreath_C_mul_comp {h H : ℚ[X]} (hirr : Irreducible h)
    (hS : GaloisGroupIsSymmetric h) {c a : ℚ} (hc : c ≠ 0) (ha : a ≠ 0)
    (hHdef : H = C a * h.comp (1 + C c * polyX ^ 2)) (h1 : h.eval 1 ≠ 0) {τ : H.Gal}
    (hτ : (galPerm H τ).IsCycle) {d : ℕ} (hd : (galPerm H τ).support.card = 2 * d)
    (hodd : Odd d) (hdM : d < h.natDegree) :
    GaloisGroupIsWreath H ∧ (0 : H.SplittingField) ∉ H.rootSet H.SplittingField ∧
      (∀ x ∈ H.rootSet H.SplittingField, -x ∈ H.rootSet H.SplittingField) ∧
      Nat.card (squares (H.rootSet H.SplittingField)) = h.natDegree := by
  set J := C 1 * h.comp (C (-c) * polyX + C 1) with hJdef
  have hk : a⁻¹ ≠ 0 := inv_ne_zero ha
  have hJL : J.comp (-polyX ^ 2) = C a⁻¹ * H := by
    rw [hHdef, comp_neg_X_sq_eq h c, ← mul_assoc, ← C_mul, inv_mul_cancel₀ ha]
  have hJirr : Irreducible J := irreducible_comp_affine hirr hc
  have hJsep : J.Separable := hJirr.separable
  have hJ0 : J.coeff 0 ≠ 0 := by
    rw [coeff_zero_eq_eval_zero, hJdef, eval_mul, eval_C, one_mul, eval_comp]
    simpa using h1
  have hsym : GaloisGroupIsSymmetric J :=
    GaloisGroupIsSymmetric.affine h 1 one_ne_zero (neg_ne_zero.mpr hc) hS
  have hproj := map_pairPerm_range_galPerm_eq_top hk hJL hJsep hJ0 hsym
  have hΓ := range_galPerm_le_negCommPerm H
  have h0 := zero_not_mem_rootSet_of_comp_neg_X_sq hk hJL hJ0
  have hneg : ∀ x ∈ H.rootSet H.SplittingField, -x ∈ H.rootSet H.SplittingField :=
    fun x hx => neg_mem_rootSet_of_comp_neg_X_sq hk hJL hx
  have hJdeg : J.natDegree = h.natDegree := by
    rw [hJdef, natDegree_C_mul one_ne_zero, natDegree_comp,
      natDegree_linear (neg_ne_zero.mpr hc), mul_one]
  have hN : Nat.card (squares (H.rootSet H.SplittingField)) = h.natDegree := by
    rw [nat_card_squares_of_comp_neg_X_sq hk hJL hJsep hJ0, hJdeg]
  have hW := eq_negCommPerm_of_isCycle_of_odd two_ne_zero h0 hneg hΓ hproj
    (MonoidHom.mem_range.mpr ⟨τ, rfl⟩) hτ hd hodd (by rw [hN]; exact hdM)
  exact ⟨(galoisGroupIsWreath_iff H).mpr hW, h0, hneg, hN⟩

/-! ### The parameters `(δ - 1/2, r)` -/

/-- The parameters `α = δ - 1/2`, `β = r` satisfy the denominator condition of Theorem 1.6, with
`D = 2`. -/
theorem denomCond_gegenbauer (r δ : ℕ) : DenomCond ((δ : ℚ) - 1 / 2) r := by
  have hodd : ∀ k : ℕ, Nat.Coprime (2 * (k : ℤ) - 1).natAbs (2 : ℤ).natAbs := by
    intro k
    rw [show (2 : ℤ).natAbs = 2 from rfl, Nat.coprime_two_right, Int.natAbs_odd]
    exact ⟨k - 1, by ring⟩
  have e1 : ((δ : ℚ) - 1 / 2) = ((2 * (δ : ℤ) - 1 : ℤ) : ℚ) / ((2 : ℤ) : ℚ) := by
    push_cast; ring
  have e2 : ((δ : ℚ) - 1 / 2) + r = ((2 * ((δ + r : ℕ) : ℤ) - 1 : ℤ) : ℚ) / ((2 : ℤ) : ℚ) := by
    push_cast; ring
  have hd1 : (((δ : ℚ) - 1 / 2).den : ℤ) = 2 := by
    rw [e1]; exact Rat.den_div_eq_of_coprime (by norm_num) (hodd δ)
  have hd2 : ((((δ : ℚ) - 1 / 2) + r).den : ℤ) = 2 := by
    rw [e2]; exact Rat.den_div_eq_of_coprime (by norm_num) (hodd (δ + r))
  have hd1' : ((δ : ℚ) - 1 / 2).den = 2 := by exact_mod_cast hd1
  have hd2' : (((δ : ℚ) - 1 / 2) + r).den = 2 := by exact_mod_cast hd2
  refine (denomCond_iff _ _).mpr ⟨by rw [hd2']; exact even_two, ?_, fun k hk => ?_,
    fun k hk => ?_⟩
  · rw [hd1', hd2', Rat.den_natCast]
    norm_num
  · have h2 : ((2 * (δ : ℤ) - 1 : ℤ) : ℚ) = ((-(2 * (k : ℤ)) - 2 : ℤ) : ℚ) := by
      push_cast; linarith
    have h3 : 2 * (δ : ℤ) - 1 = -(2 * (k : ℤ)) - 2 := by exact_mod_cast h2
    omega
  · have : (0 : ℚ) ≤ r := Nat.cast_nonneg r
    have : (0 : ℚ) ≤ k := Nat.cast_nonneg k
    linarith

/-! ### The core argument -/

theorem natDegree_quad : (1 + C (-2 : ℚ) * polyX ^ 2).natDegree = 2 := by
  compute_degree!

open Classical in
/-- **Corollary 1.7, core.** Let `(α, β)` satisfy the denominator condition and fix a number
field `E`. For all large `m`, whenever `F = s · P_m^{(α,β)}(1 - 2X²)` is irreducible over `ℚ`
(`s ≠ 0`) and `Q = s · P_m^{(α,β)}(1 - 2T)`, the polynomials `F` and `Q` are irreducible over
`E` with groups `W_m` and `S_m`, and their splitting fields are linearly disjoint from `E`.

Conditional on [BMOR, Corollary 1.7], [BMOR, Proposition 6.19], Brun–Titchmarsh [MV, Theorem 2]
and [Jones, Corollary 1.3], taken as the hypotheses `hBMOR`, `h619`, `hBT`, `hJones`. -/
theorem derivativeGalois_core (hBMOR : BMORPrimeCountingBound)
    (h619 : BMORLargeModulusPrimeCounting) (hBT : BrunTitchmarshInequality)
    (hJones : JonesCycleTheorem) {α β : ℚ} (hcond : DenomCond α β) (E : Type) [Field E]
    [NumberField E] :
    ∃ N : ℕ, ∀ m ≥ N, ∀ F Q : ℚ[X], ∀ s : ℚ, s ≠ 0 →
      F = C s * (jacobiP α β m).comp (1 + C (-2) * polyX ^ 2) →
      Q = C s * (jacobiP α β m).comp (C (-2) * polyX + C 1) → Irreducible F →
      Irreducible (F.map (algebraMap ℚ E)) ∧ GaloisGroupIsWreath (F.map (algebraMap ℚ E)) ∧
      Irreducible (Q.map (algebraMap ℚ E)) ∧ GaloisGroupIsSymmetric (Q.map (algebraMap ℚ E)) ∧
      IsField (F.SplittingField ⊗[ℚ] E) ∧ IsField (Q.SplittingField ⊗[ℚ] E) := by
  obtain ⟨R, hR⟩ := FixedFieldDisjointness.exists_bound_fixedField E
  obtain ⟨hD2, hr, hgc⟩ := denomCond_facts hcond
  have hgr := gcd_num_two_den hcond
  have hDpos := (α + β).den_pos
  have hc : (-2 : ℚ) ≠ 0 := by norm_num
  obtain ⟨Nu, hNu⟩ := exists_unique_isDominant_jacobiP h619 hcond
  obtain ⟨N₀, hN₀⟩ := galoisGroupIsSymmetric_isDominant_jacobiP hBMOR h619 hBT hJones hcond
  obtain ⟨C₀, N₁, hN₁⟩ := natDegree_isDominant_jacobiP h619 hcond 1 one_pos
  have eve := eventually_exists_prime_upper hBMOR h619 (B := cycleBound α β) hD2 hgc
  have evo := eventually_exists_prime_upper hBMOR h619 (B := cycleBound α β) hD2 hgr
  have ev3 := eventually_le_log_natCast (10 * |C₀| + 1)
  have ev4 := eventually_ge_atTop
    (Nu + N₀ + N₁ + R + 100 * ((α + β).num.natAbs + 1) + (-2 : ℚ).num.natAbs +
      (-2 : ℚ).den + 1)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eve.and (evo.and (ev3.and ev4)))
  refine ⟨N, fun n hn F Q s hs hF hQ hFirr => ?_⟩
  obtain ⟨⟨pe, hpe, he1, he2, he3, he4⟩, ⟨po, hpo, ho1, ho2, ho3, ho4⟩, hL, hn'⟩ := hN n hn
  have hdeg := natDegree_jacobiP_le α β n
  obtain ⟨he3', heven⟩ := modEq_and_even_of_modEq_add (n := n) hDpos he4
  obtain ⟨ho3', hodd⟩ := modEq_and_odd_of_modEq (n := n) hDpos ho4
  have hnDn : n ≤ (α + β).den * n := Nat.le_mul_of_pos_left n hDpos
  have hcp : ∀ p : ℕ, p.Prime → (α + β).den * n + cycleBound α β < p →
      padicValRat p (-2) = 0 := fun p hp hp1 =>
    padicValRat_eq_zero_of_lt hp hc (by omega) (by omega)
  -- the dominant factor is everything
  obtain ⟨P, hP, hPl, σ, hσI, hσ, hσc⟩ := exists_inertia_isCycle_of_eligible hcond hpe he1 he2 he3'
  have hf0 := ne_zero_of_isCycle hσ
  obtain ⟨h, hh, -⟩ := hNu n (by omega)
  have hhd := (isDominant_iff _ _).mp hh
  obtain ⟨g, κ, hg, hfac⟩ := exists_monic_cofactor hf0 hhd.2.2.1
  obtain ⟨hS, -⟩ := hN₀ n (by omega) h g κ hh hg hfac
  have hκ : κ ≠ 0 := by
    rintro rfl
    exact hf0 (by rw [hfac, C_0, zero_mul, zero_mul])
  have hsκ : s * κ ≠ 0 := mul_ne_zero hs hκ
  have hFhg : F = C (s * κ) * h.comp (1 + C (-2) * polyX ^ 2) * g.comp (1 + C (-2) * polyX ^ 2)
    := by
    rw [hF, hfac, mul_comp, mul_comp, C_comp, C_mul]
    ring
  have hg1 : g = 1 := by
    rcases hFirr.isUnit_or_isUnit hFhg with hu | hu
    · exfalso
      have h0 := natDegree_eq_zero_of_isUnit hu
      rw [natDegree_C_mul hsκ, natDegree_comp, natDegree_quad] at h0
      have := hhd.2.1.natDegree_pos
      omega
    · have h0 := natDegree_eq_zero_of_isUnit hu
      rw [natDegree_comp, natDegree_quad] at h0
      exact hg.natDegree_eq_zero.mp (by omega)
  have hfac1 : jacobiP α β n = C κ * h := by rw [hfac, hg1, mul_one]
  have hFh : F = C (s * κ) * h.comp (1 + C (-2) * polyX ^ 2) := by
    rw [hFhg, hg1, one_comp, mul_one]
  have hQh : Q = C (s * κ) * h.comp (C (-2) * polyX + C 1) := by
    rw [hQ, hfac1, mul_comp, C_comp, C_mul]
    ring
  -- bounds
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
  -- the quadratic inertia cycles
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
  -- `Q`: irreducible with group `S_M`, and the inertia cycle
  have hQirr : Irreducible Q := by
    rw [hQh]; exact irreducible_C_mul_comp_affine hhd.2.1 hsκ hc
  have hQS : GaloisGroupIsSymmetric Q := by
    rw [hQh]; exact GaloisGroupIsSymmetric.affine h 1 hsκ hc hS
  have hQdeg : Q.natDegree = h.natDegree := by
    rw [hQh, natDegree_C_mul hsκ, natDegree_comp, natDegree_linear hc, mul_one]
  have hσc' : (galPerm _ σ).support.card = de := by exact_mod_cast hσc
  obtain ⟨Q₁, hQ₁, hQ₁l, τ, hτI, hτ, hτc⟩ := exists_inertia_restrict hf0 hhd.2.2.1 (p := pe) P hσI
    hσ (aeval_eq_zero_of_isDominant hdeg hh hσ (by omega))
  obtain ⟨Q₂, hQ₂, hQ₂l, τ', hτ'I, hτ', hτ'c, -⟩ := exists_mem_inertia_galPerm_affine_of_eq hsκ hc
    hQh (p := pe) (k := 0) τ hτ (hτc.trans hσc') (fun h => absurd h one_ne_zero) Q₁ hτI
  have hRQ := hR Q fun Nh hNh hNI => eq_top_of_normal_of_symm hQS hNh
    (hNI pe hpe (by omega) Q₂ hQ₂l hτ'I) hτ' hτ'c heven' (by omega)
    (by rw [card_rootSet_of_irreducible hQirr, hQdeg]; exact hdeM)
  -- `F`: the group `W_M` and the inertia cycles
  have hP0 := ne_zero_of_isCycle hσe
  have hFP : F ∣ (jacobiP α β n).comp (1 + C (-2) * polyX ^ 2) := by
    refine ⟨C s⁻¹, ?_⟩
    rw [hF, mul_comm (C s * _), ← mul_assoc, ← C_mul, inv_mul_cancel₀ hs, C_1, one_mul]
  have hsuppF : ∀ (σ' : ((jacobiP α β n).comp (1 + C (-2) * polyX ^ 2)).Gal),
      ∀ z ∈ (galPerm _ σ').support,
        aeval (z : ((jacobiP α β n).comp (1 + C (-2) * polyX ^ 2)).SplittingField) F = 0 := by
    intro σ' z _
    rw [hF, aeval_mul, (mem_rootSet.mp z.2).2, mul_zero]
  have hσec' : (galPerm _ σe).support.card = 2 * de := by exact_mod_cast hσec
  have hσoc' : (galPerm _ σo).support.card = 2 * do_ := by exact_mod_cast hσoc
  obtain ⟨Qe, hQe, hQel, τe, hτeI, hτe, hτec⟩ :=
    exists_inertia_restrict hP0 hFP (p := pe) Pe hσeI hσe (hsuppF σe)
  obtain ⟨Qo, hQo, hQol, τo, hτoI, hτo, hτoc⟩ :=
    exists_inertia_restrict hP0 hFP (p := po) Po hσoI hσo (hsuppF σo)
  obtain ⟨hW, h0, hneg, hNsq⟩ := galoisGroupIsWreath_C_mul_comp hhd.2.1 hS hc hsκ hFh
    (eval_one_ne_zero_of_dvd ((denomCond_iff _ _).mp hcond).2.2.1 hhd.2.2.1) hτo
    (hτoc.trans hσoc') hodd' hdoM
  have hRF := hR F fun Nh hNh hNI => eq_top_of_normal_of_wreath h0 hneg hW hNh
    (hNI pe hpe (by omega) Qe hQel hτeI) (hNI po hpo (by omega) Qo hQol hτoI) hτe
    (hτec.trans hσec') hτo (hτoc.trans hσoc') heven' hodd' (by omega)
    (by rw [hNsq]; exact hdeM) (by rw [hNsq]; exact hdoM)
  exact ⟨hRF.2.1 hFirr, hRF.2.2.2 hW, hRQ.2.1 hQirr, hRQ.2.2.1 hQS, hRF.1, hRQ.1⟩

end FixedRationalParameters

open FixedRationalParameters in
/-- **Corollary 1.7**. Fix `r ≥ 0` and a number field `E`. For all
large `m` and both `δ ∈ {0,1}`, `F_{m,r,δ}` and `Q_{m,r,δ}` are irreducible over `E` with
`Gal(F_{m,r,δ}/E) = W_m` and `Gal(Q_{m,r,δ}/E) = S_m`, and their splitting fields over `ℚ` are
linearly disjoint from `E`.

Conditional on [DLMF, 18.7.15–18.7.16] (`hQ`, through the bridge (5.33)), [Hanson, Theorem 1],
[DLMF, §18.2(vi)] (`hH`, `hZ`, through Theorem 1.4),
[BMOR, Corollary 1.7], [BMOR, Proposition 6.19], Brun–Titchmarsh [MV, Theorem 2] and
[Jones, Corollary 1.3] (`hBMOR`, `h619`, `hBT`, `hJones`, through Theorem 1.6). -/
theorem fixedDerivativesGaloisStatement (hQ : GegenbauerQuadraticTransformation)
    (hH : HansonLcmBound) (hZ : JacobiSimpleRealZeros)
    (hBMOR : BMORPrimeCountingBound) (h619 : BMORLargeModulusPrimeCounting)
    (hBT : BrunTitchmarshInequality) (hJones : JonesCycleTheorem) :
    FixedDerivativesGaloisStatement := by
  intro r E _ _
  obtain ⟨N₀, hN₀⟩ := derivativeGalois_core hBMOR h619 hBT hJones
    (denomCond_gegenbauer r 0) E
  obtain ⟨N₁, hN₁⟩ := derivativeGalois_core hBMOR h619 hBT hJones
    (denomCond_gegenbauer r 1) E
  refine ⟨N₀ + N₁ + 100 * r + 1000, fun m hm δ hδ => ?_⟩
  have hFirr := irreducible_reducedGegenbauer_of_explicit_range hH hZ hδ
    (m := m) (r := r) (by omega)
  have e1 : (1 - 2 * polyX ^ 2 : ℚ[X]) = 1 + C (-2) * polyX ^ 2 := by
    rw [map_neg, map_ofNat]; ring
  have e2 : (1 - 2 * polyX : ℚ[X]) = C (-2) * polyX + C 1 := by
    rw [map_neg, map_ofNat, C_1]; ring
  have hF := reducedGegenbauer_eq_jacobiP_comp hQ m r δ hδ
  have hQq := reducedGegenbauerSquare_eq_jacobiP_comp hQ m r δ hδ
  rw [e1] at hF
  rw [e2] at hQq
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hδ with rfl | rfl
  · exact hN₀ m (by omega) _ _ _ (gegenbauerBridgeScalar_ne_zero m r 0) hF hQq hFirr
  · exact hN₁ m (by omega) _ _ _ (gegenbauerBridgeScalar_ne_zero m r 1) hF hQq hFirr

end ArithmeticOfJacobiPolynomials
