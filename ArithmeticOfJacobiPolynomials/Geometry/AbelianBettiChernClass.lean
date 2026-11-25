/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Geometry.AbelianBettiHodge
public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
import all ArithmeticOfJacobiPolynomials.Algebra.ComplexRealization

/-!
# The first Chern class of an invertible module as a period form
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing

namespace ArithmeticOfJacobiPolynomials.AbelianBettiChern

open ArithmeticOfJacobiPolynomials.ComplexRealization
  ArithmeticOfJacobiPolynomials.AbelianBettiHodge

section LogChange

open unitInterval

instance contractibleSpace_unitInterval : ContractibleSpace unitInterval :=
  (convex_Icc (0:ℝ) 1).contractibleSpace ⟨0, by simp⟩
instance locallyPathConnectedSpace_unitInterval : LocallyPathConnectedSpace unitInterval :=
  (convex_Icc (0:ℝ) 1).locallyPathConnectedSpace

/-- `δ` is the total change of a logarithm of `P` along `I`. -/
def IsLogChange (P : I → ℂ) (δ : ℂ) : Prop :=
  ∃ ℓ : I → ℂ, Continuous ℓ ∧ (∀ t, Complex.exp (ℓ t) = P t) ∧ ℓ 1 - ℓ 0 = δ

theorem IsLogChange.unique {P : I → ℂ} {δ δ' : ℂ} (h : IsLogChange P δ) (h' : IsLogChange P δ') :
    δ = δ' := by
  obtain ⟨ℓ, hc, he, rfl⟩ := h
  obtain ⟨ℓ', hc', he', rfl⟩ := h'
  -- the two lifts differ at `0` by an element of `2πi ℤ`
  have h0 : Complex.exp (ℓ 0) = Complex.exp (ℓ' 0) := by rw [he, he']
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h0
  have hcov : IsCoveringMap fun z : ℂ ↦ (⟨_, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0}) :=
    Complex.isCoveringMap_exp
  have key : (fun t => ℓ t - n * (2 * Real.pi * Complex.I)) = ℓ' := by
    have := hcov.eq_of_comp_eq (A := I) (g₁ := fun t => ℓ t - n * (2 * Real.pi * Complex.I))
      (g₂ := ℓ') (hc.sub continuous_const) hc' ?_ 0 ?_
    · exact this
    · funext t
      apply Subtype.ext
      simp [Complex.exp_sub, he t, he' t, Complex.exp_int_mul_two_pi_mul_I]
    · simp only [hn]; ring
  have h1 : ℓ 1 - n * (2 * Real.pi * Complex.I) = ℓ' 1 := congrFun key 1
  have h2 : ℓ 0 - n * (2 * Real.pi * Complex.I) = ℓ' 0 := congrFun key 0
  linear_combination h1 - h2

theorem IsLogChange.mul {P Q : I → ℂ} {δ δ' : ℂ} (h : IsLogChange P δ) (h' : IsLogChange Q δ') :
    IsLogChange (fun t => P t * Q t) (δ + δ') := by
  obtain ⟨ℓ, hc, he, rfl⟩ := h
  obtain ⟨ℓ', hc', he', rfl⟩ := h'
  exact ⟨fun t => ℓ t + ℓ' t, hc.add hc', fun t => by simp [Complex.exp_add, he t, he' t], by ring⟩

theorem IsLogChange.div {P Q : I → ℂ} {δ δ' : ℂ} (h : IsLogChange P δ) (h' : IsLogChange Q δ') :
    IsLogChange (fun t => P t / Q t) (δ - δ') := by
  obtain ⟨ℓ, hc, he, rfl⟩ := h
  obtain ⟨ℓ', hc', he', rfl⟩ := h'
  exact ⟨fun t => ℓ t - ℓ' t, hc.sub hc', fun t => by simp [Complex.exp_sub, he t, he' t], by ring⟩

theorem IsLogChange.const (c : ℂ) (hc : c ≠ 0) : IsLogChange (fun _ => c) 0 :=
  ⟨fun _ => Complex.log c, continuous_const, fun _ => Complex.exp_log hc, by simp⟩

/-- Existence of logarithms on simply connected, locally path connected spaces. -/
theorem exists_log {A : Type*} [TopologicalSpace A] [SimplyConnectedSpace A]
    [LocallyPathConnectedSpace A] [Nonempty A] (G : A → ℂ) (hG : Continuous G)
    (h0 : ∀ z, G z ≠ 0) : ∃ F : A → ℂ, Continuous F ∧ ∀ z, Complex.exp (F z) = G z := by
  obtain ⟨a₀⟩ := ‹Nonempty A›
  let f : C(A, {z : ℂ // z ≠ 0}) := ⟨fun z => ⟨G z, h0 z⟩, hG.subtype_mk _⟩
  obtain ⟨F, ⟨-, hF⟩, -⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts f a₀
    (Complex.log (G a₀)) (by
      apply Subtype.ext
      simp [f, Complex.exp_log (h0 _)])
  refine ⟨F, F.continuous, fun z => ?_⟩
  have := congrFun hF z
  simpa [f] using congrArg Subtype.val this

/-- Existence of a log-change along an arbitrary continuous nonvanishing path. -/
theorem exists_logChange (P : I → ℂ) (hP : Continuous P) (h0 : ∀ t, P t ≠ 0) :
    ∃ δ, IsLogChange P δ := by
  obtain ⟨F, hF, he⟩ := exists_log P hP h0
  exact ⟨F 1 - F 0, F, hF, he, rfl⟩

/-- **The square lemma.** For a continuous nowhere vanishing function on the unit square, the
log-changes along the four edges and the diagonal are related by the usual identities. -/
theorem square_log (G : I × I → ℂ) (hG : Continuous G) (h0 : ∀ z, G z ≠ 0) :
    ∃ a b c d : ℂ, IsLogChange (fun t => G (t, 0)) a ∧ IsLogChange (fun t => G (1, t)) b ∧
      IsLogChange (fun t => G (0, t)) c ∧ IsLogChange (fun t => G (t, 1)) d ∧
      IsLogChange (fun t => G (t, t)) (a + b) ∧ a + b = c + d := by
  obtain ⟨F, hF, he⟩ := exists_log G hG h0
  refine ⟨F (1, 0) - F (0, 0), F (1, 1) - F (1, 0), F (0, 1) - F (0, 0), F (1, 1) - F (0, 1),
    ⟨fun t => F (t, 0), by fun_prop, fun t => he _, rfl⟩,
    ⟨fun t => F (1, t), by fun_prop, fun t => he _, rfl⟩,
    ⟨fun t => F (0, t), by fun_prop, fun t => he _, rfl⟩,
    ⟨fun t => F (t, 1), by fun_prop, fun t => he _, rfl⟩,
    ⟨fun t => F (t, t), by fun_prop, fun t => he _, by ring⟩, by ring⟩

open Classical in
/-- The total change of a logarithm of the path `P` (`0` if there is none). -/
def logChange (P : I → ℂ) : ℂ := if h : ∃ δ, IsLogChange P δ then h.choose else 0

theorem IsLogChange.logChange_eq {P : I → ℂ} {δ : ℂ} (h : IsLogChange P δ) : logChange P = δ := by
  have h' : ∃ δ, IsLogChange P δ := ⟨δ, h⟩
  unfold logChange
  simp only [h', ↓reduceDIte]
  exact h'.choose_spec.unique h

theorem isLogChange_logChange {P : I → ℂ} (hP : Continuous P) (h0 : ∀ t, P t ≠ 0) :
    IsLogChange P (logChange P) := by
  obtain ⟨δ, h⟩ := exists_logChange P hP h0
  rwa [h.logChange_eq]

theorem IsLogChange.exp_eq {P : I → ℂ} {δ : ℂ} (h : IsLogChange P δ) :
    Complex.exp δ = P 1 / P 0 := by
  obtain ⟨ℓ, -, he, rfl⟩ := h
  rw [Complex.exp_sub, he, he]

end LogChange

section Generators

variable {X : Scheme.{0}} (L : X.Modules)

/-- A **local generator** of the `𝒪_X`-module `L`: a section `e` of `L` over an open `U` which
freely generates `L` on `U`: for every open `V ⊆ U`, `r ↦ r • e|_V` is a bijection
`Γ(X, V) → Γ(L, V)`. -/
structure LocalGen where
  /-- The open on which the section lives. -/
  U : X.Opens
  /-- The generating section. -/
  e : Γ(L, U)
  /-- Over every open `V ⊆ U`, `r ↦ r • e|_V` is bijective. -/
  bijective : ∀ (V : X.Opens) (i : V ⟶ U),
    Function.Bijective (fun r : Γ(X, V) => r • L.presheaf.map i.op e)

variable {L}

/-- The transition function between two local generators over `V ⊆ U ∩ U'`:
`e'|_V = trans • e|_V`. -/
def LocalGen.trans (g g' : LocalGen L) (V : X.Opens) (h : V ≤ g.U) (h' : V ≤ g'.U) : Γ(X, V) :=
  ((g.bijective V (homOfLE h)).2 (L.presheaf.map (homOfLE h').op g'.e)).choose

theorem LocalGen.trans_spec (g g' : LocalGen L) (V : X.Opens) (h : V ≤ g.U) (h' : V ≤ g'.U) :
    g.trans g' V h h' • L.presheaf.map (homOfLE h).op g.e = L.presheaf.map (homOfLE h').op g'.e :=
  ((g.bijective V (homOfLE h)).2 (L.presheaf.map (homOfLE h').op g'.e)).choose_spec

theorem LocalGen.eq_trans (g g' : LocalGen L) (V : X.Opens) (h : V ≤ g.U) (h' : V ≤ g'.U)
    {r : Γ(X, V)}
    (hr : r • L.presheaf.map (homOfLE h).op g.e = L.presheaf.map (homOfLE h').op g'.e) :
    r = g.trans g' V h h' :=
  (g.bijective V (homOfLE h)).1 (hr.trans (g.trans_spec g' V h h').symm)

theorem LocalGen.trans_self (g : LocalGen L) (V : X.Opens) (h : V ≤ g.U) :
    g.trans g V h h = 1 :=
  (g.eq_trans g V h h (one_smul _ _)).symm

theorem LocalGen.trans_mul (g g' g'' : LocalGen L) (V : X.Opens) (h : V ≤ g.U) (h' : V ≤ g'.U)
    (h'' : V ≤ g''.U) :
    g'.trans g'' V h' h'' * g.trans g' V h h' = g.trans g'' V h h'' := by
  refine g.eq_trans g'' V h h'' ?_
  rw [mul_smul, g.trans_spec g' V h h', g'.trans_spec g'' V h' h'']

theorem LocalGen.trans_res (g g' : LocalGen L) {V W : X.Opens} (hWV : W ≤ V) (h : V ≤ g.U)
    (h' : V ≤ g'.U) :
    X.presheaf.map (homOfLE hWV).op (g.trans g' V h h') =
      g.trans g' W (hWV.trans h) (hWV.trans h') := by
  refine g.eq_trans g' W _ _ ?_
  have h1 : L.presheaf.map (homOfLE (hWV.trans h)).op g.e =
      L.presheaf.map (homOfLE hWV).op (L.presheaf.map (homOfLE h).op g.e) := by
    rw [← L.presheaf.map_comp_apply]; rfl
  have h2 : L.presheaf.map (homOfLE (hWV.trans h')).op g'.e =
      L.presheaf.map (homOfLE hWV).op (L.presheaf.map (homOfLE h').op g'.e) := by
    rw [← L.presheaf.map_comp_apply]; rfl
  rw [h1, h2, ← g.trans_spec g' V h h']
  exact (Scheme.Modules.map_smul L (homOfLE hWV) _ _).symm

end Generators

section PointEval

variable {A : CSch}

theorem ptEval_mul {U : A.left.Opens} (a b : Γ(A.left, U)) (p : Points A) (hp : secPt p ∈ U) :
    ptEval U (a * b) p = ptEval U a p * ptEval U b p := by
  simp [ptEval, hp]

theorem ptEval_one {U : A.left.Opens} (p : Points A) (hp : secPt p ∈ U) :
    ptEval U (1 : Γ(A.left, U)) p = 1 := by
  simp [ptEval, hp]

theorem ptEval_res {U V : A.left.Opens} (i : V ⟶ U) (r : Γ(A.left, U)) (p : Points A)
    (hp : secPt p ∈ V) :
    ptEval V (A.left.presheaf.map i.op r) p = ptEval U r p := by
  have hp' : secPt p ∈ U := i.le hp
  simp only [ptEval, hp, hp', ↓reduceDIte]
  rw [A.left.presheaf.germ_res_apply i (secPt p) hp r]

end PointEval

section Fibre

variable {A : CSch} {L : A.left.Modules}

/-- The transition function of two local generators evaluated at the complex point `p`
(`e'(p) = trPt • e(p)` in the fibre of `L` at `p`). -/
def LocalGen.trPt (g g' : LocalGen L) (p : Points A) : ℂ :=
  ptEval (g.U ⊓ g'.U) (g.trans g' (g.U ⊓ g'.U) inf_le_left inf_le_right) p

theorem LocalGen.trPt_eq (g g' : LocalGen L) (p : Points A) (V : A.left.Opens)
    (hp : secPt p ∈ V) (h : V ≤ g.U) (h' : V ≤ g'.U) :
    g.trPt g' p = ptEval V (g.trans g' V h h') p := by
  have hle : V ≤ g.U ⊓ g'.U := le_inf h h'
  unfold LocalGen.trPt
  rw [← g.trans_res g' hle inf_le_left inf_le_right]
  exact (ptEval_res (homOfLE hle) _ p hp).symm

theorem LocalGen.trPt_self (g : LocalGen L) (p : Points A) (hp : secPt p ∈ g.U) :
    g.trPt g p = 1 := by
  rw [g.trPt_eq g p g.U hp le_rfl le_rfl, g.trans_self, ptEval_one _ hp]

theorem LocalGen.trPt_mul (g g' g'' : LocalGen L) (p : Points A) (hp : secPt p ∈ g.U)
    (hp' : secPt p ∈ g'.U) (hp'' : secPt p ∈ g''.U) :
    g'.trPt g'' p * g.trPt g' p = g.trPt g'' p := by
  have hV : secPt p ∈ g.U ⊓ g'.U ⊓ g''.U := ⟨⟨hp, hp'⟩, hp''⟩
  have h1 : g.U ⊓ g'.U ⊓ g''.U ≤ g.U := inf_le_left.trans inf_le_left
  have h2 : g.U ⊓ g'.U ⊓ g''.U ≤ g'.U := inf_le_left.trans inf_le_right
  have h3 : g.U ⊓ g'.U ⊓ g''.U ≤ g''.U := inf_le_right
  rw [g'.trPt_eq g'' p _ hV h2 h3, g.trPt_eq g' p _ hV h1 h2, g.trPt_eq g'' p _ hV h1 h3,
    ← ptEval_mul _ _ p hV, g.trans_mul g' g'' _ h1 h2 h3]

variable (L) in
/-- **The fibre of the invertible module `L` at the complex point `p`**: the `ℂ`-vector space of
families `(c_g)`, indexed by the local generators `g` of `L` defined at `p`, with
`c_g = c_{g'} · (e_{g'}/e_g)(p)`. (A section `c_g(p) e_g` of `L` near `p` is independent of the
generator.) -/
def Fibre (p : Points A) : Submodule ℂ ({g : LocalGen L // secPt p ∈ g.U} → ℂ) where
  carrier := {f | ∀ g g' : {g : LocalGen L // secPt p ∈ g.U}, f g = f g' * g.1.trPt g'.1 p}
  add_mem' := by
    intro a b ha hb g g'
    simp only [Pi.add_apply, ha g g', hb g g', add_mul]
  zero_mem' := by
    intro g g'
    simp
  smul_mem' := by
    intro c f hf g g'
    simp only [Pi.smul_apply, smul_eq_mul, hf g g', mul_assoc]

open Classical in
variable (L) in
/-- The coordinate of an element of the fibre at `p` in the chart given by the local generator
`g` (zero when `g` is not defined at `p`). -/
def Fibre.coord (g : LocalGen L) (p : Points A) (σ : Fibre L p) : ℂ :=
  if h : secPt p ∈ g.U then σ.1 ⟨g, h⟩ else 0

theorem Fibre.coord_of_mem {p : Points A} (σ : Fibre L p) (g : LocalGen L) (h : secPt p ∈ g.U) :
    Fibre.coord L g p σ = σ.1 ⟨g, h⟩ := by
  simp [Fibre.coord, h]

theorem Fibre.coord_trans {p : Points A} (σ : Fibre L p) (g g' : LocalGen L) (h : secPt p ∈ g.U)
    (h' : secPt p ∈ g'.U) :
    Fibre.coord L g p σ = Fibre.coord L g' p σ * g.trPt g' p := by
  rw [coord_of_mem σ g h, coord_of_mem σ g' h']
  exact σ.2 ⟨g, h⟩ ⟨g', h'⟩

theorem Fibre.ext {p : Points A} {σ τ : Fibre L p}
    (h : ∀ (g : LocalGen L), secPt p ∈ g.U → Fibre.coord L g p σ = Fibre.coord L g p τ) :
    σ = τ := by
  refine Subtype.ext (funext fun g => ?_)
  have := h g.1 g.2
  rwa [coord_of_mem σ g.1 g.2, coord_of_mem τ g.1 g.2] at this

theorem Fibre.coord_ne_zero {p : Points A} {σ : Fibre L p} (hσ : σ ≠ 0) (g : LocalGen L)
    (hg : secPt p ∈ g.U) : Fibre.coord L g p σ ≠ 0 := by
  intro h0
  apply hσ
  refine Fibre.ext fun g' hg' => ?_
  have h1 := Fibre.coord_trans σ g' g hg' hg
  rw [h1, h0, zero_mul]
  simp [Fibre.coord, hg']

/-- Equal points have canonically isomorphic fibres. -/
def Fibre.cast {p q : Points A} (h : p = q) : Fibre L p ≃ₗ[ℂ] Fibre L q := by
  subst h
  exact LinearEquiv.refl ℂ _

theorem Fibre.coord_cast {p q : Points A} (h : p = q) (σ : Fibre L p) (g : LocalGen L) :
    Fibre.coord L g q (Fibre.cast h σ) = Fibre.coord L g p σ := by
  subst h
  rfl

end Fibre

section Exp

variable {A : CSch} [GrpObj A] (D : UniformizationData A) {L : A.left.Modules}

/-- `a ∈ Lie A` is a **period** of `exp`: translation by `a` preserves `exp`. -/
def IsPeriod (a : Lie A) : Prop := ∀ v : Lie A, D.exp (v + a) = D.exp v

theorem IsPeriod.zero : IsPeriod D 0 := fun v => by simp

theorem IsPeriod.add {a b : Lie A} (ha : IsPeriod D a) (hb : IsPeriod D b) : IsPeriod D (a + b) :=
  fun v => by rw [← add_assoc, hb, ha]

theorem IsPeriod.neg {a : Lie A} (ha : IsPeriod D a) : IsPeriod D (-a) := fun v => by
  have := ha (v + -a)
  simp only [neg_add_cancel_right] at this
  exact this.symm

/-- The group of periods of `exp`. -/
@[expose] def periodGroup : AddSubgroup (Lie A) where
  carrier := {a | IsPeriod D a}
  zero_mem' := IsPeriod.zero D
  add_mem' := fun ha hb => IsPeriod.add D ha hb
  neg_mem' := fun ha => IsPeriod.neg D ha

theorem continuous_add_right_lie (a : Lie A) : Continuous fun v : Lie A => v + a :=
  continuous_of_tangentEval fun U hU s => by
    simp only [tangentEval_add]
    exact (continuous_tangentEval U hU s).add continuous_const

theorem continuous_comb_lie (a b : Lie A) :
    Continuous fun p : ℝ × ℝ => ((p.1 : ℂ) • a + (p.2 : ℂ) • b) :=
  continuous_of_tangentEval fun U hU s => by
    simp only [tangentEval_add, tangentEval_smul]
    fun_prop

omit [GrpObj A] in
theorem isOpen_pointsIn (U : A.left.Opens) :
    @IsOpen (Points A) (analyticTopology A) {p | secPt p ∈ U} := by
  have : {p : Points A | secPt p ∈ U} = basicSet A U 1 Set.univ := by
    ext p
    constructor
    · intro hp
      have hr : Set.range p.left ⊆ Set.range U.ι := by
        rintro _ ⟨z, rfl⟩
        have hz : z = closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
        subst hz
        rw [Scheme.Opens.range_ι]
        exact hp
      exact ⟨IsOpenImmersion.lift U.ι p.left hr, IsOpenImmersion.lift_fac _ _ _, trivial⟩
    · rintro ⟨q, hq, -⟩
      have : secPt p = U.ι (q (closedPoint ℂ)) := by
        change p.left (closedPoint ℂ) = _
        rw [← hq]; rfl
      change secPt p ∈ U
      rw [this]
      have hm : U.ι (q (closedPoint ℂ)) ∈ Set.range U.ι := ⟨_, rfl⟩
      rwa [Scheme.Opens.range_ι] at hm
  rw [this]
  exact basicSet_isOpen A U 1 Set.univ isOpen_univ

theorem isOpen_exp_preimage (U : A.left.Opens) : IsOpen {v : Lie A | secPt (D.exp v) ∈ U} :=
  @IsOpen.preimage (Lie A) (Points A) _ (analyticTopology A) D.exp D.continuous_exp _
    (isOpen_pointsIn U)

variable {D}

/-- Every complex point of `A` lies in the domain of a local generator of `L`
(this is Stacks Tag 01CR/0B8M: an invertible module is locally free of rank one). -/
def CoversPoints (L : A.left.Modules) : Prop := ∀ p : Points A, ∃ g : LocalGen L, secPt p ∈ g.U

open Classical in
/-- The ratio of two elements of fibres at equal points (computed in any chart). -/
def Fibre.ratio (hL : CoversPoints L) {p q : Points A} (σ : Fibre L p) (τ : Fibre L q) : ℂ :=
  Fibre.coord L (hL q).choose p σ / Fibre.coord L (hL q).choose q τ

omit [GrpObj A] in
theorem Fibre.ratio_eq (hL : CoversPoints L) {p q : Points A} (h : p = q) (σ : Fibre L p)
    (τ : Fibre L q) (hτ : τ ≠ 0) (g : LocalGen L) (hg : secPt q ∈ g.U) :
    Fibre.ratio hL σ τ = Fibre.coord L g p σ / Fibre.coord L g q τ := by
  subst h
  have hg0 : secPt p ∈ (hL p).choose.U := (hL p).choose_spec
  unfold Fibre.ratio
  generalize (hL p).choose = g0 at hg0 ⊢
  have e1 := Fibre.coord_trans σ g0 g hg0 hg
  have e2 := Fibre.coord_trans τ g0 g hg0 hg
  have ht : g0.trPt g p ≠ 0 := by
    intro h0
    apply Fibre.coord_ne_zero hτ g0 hg0
    rw [e2, h0, mul_zero]
  rw [e1, e2, mul_div_mul_right _ _ ht]

omit [GrpObj A] in
theorem Fibre.ratio_ne_zero (hL : CoversPoints L) {p q : Points A} (h : p = q) {σ : Fibre L p}
    {τ : Fibre L q} (hσ : σ ≠ 0) (hτ : τ ≠ 0) : Fibre.ratio hL σ τ ≠ 0 := by
  obtain ⟨g, hg⟩ := hL q
  rw [Fibre.ratio_eq hL h σ τ hτ g hg]
  have hg' : secPt p ∈ g.U := h ▸ hg
  exact div_ne_zero (Fibre.coord_ne_zero hσ g hg') (Fibre.coord_ne_zero hτ g hg)

omit [GrpObj A] in
theorem Fibre.ratio_mul (hL : CoversPoints L) {p q r : Points A} (hpq : p = q) (hqr : q = r)
    (σ : Fibre L p) (τ : Fibre L q) (ρ : Fibre L r) (hτ : τ ≠ 0) (hρ : ρ ≠ 0) :
    Fibre.ratio hL σ τ * Fibre.ratio hL τ ρ = Fibre.ratio hL σ ρ := by
  subst hpq hqr
  obtain ⟨g, hg⟩ := hL p
  rw [Fibre.ratio_eq hL rfl σ τ hτ g hg, Fibre.ratio_eq hL rfl τ ρ hρ g hg,
    Fibre.ratio_eq hL rfl σ ρ hρ g hg]
  have := Fibre.coord_ne_zero hτ g hg
  field_simp

variable (D) (L) in
/-- **A continuous section of the pullback of `L` along `exp : Lie A → A(ℂ)`**: for every point
`v`, an element of the fibre of `L` at `exp v`, whose coordinate in every local chart `g` is
continuous on the open set of `v` with `exp v` in the chart's domain. -/
structure ExpSection where
  /-- The value of the section at `v`: an element of the fibre at `exp v`. -/
  val : (v : Lie A) → Fibre L (D.exp v)
  /-- Continuity in every algebraic chart. -/
  cont : ∀ g : LocalGen L, ContinuousOn (fun v : Lie A => Fibre.coord L g (D.exp v) (val v))
    {v | secPt (D.exp v) ∈ g.U}

/-- The section vanishes nowhere. -/
def ExpSection.NonVanishing (s : ExpSection D L) : Prop := ∀ v, s.val v ≠ 0

theorem continuous_of_local (hL : CoversPoints L) (F : Lie A → ℂ)
    (H : ∀ g : LocalGen L, ∃ f : Lie A → ℂ, ContinuousOn f {v | secPt (D.exp v) ∈ g.U} ∧
      ∀ v, secPt (D.exp v) ∈ g.U → F v = f v) : Continuous F := by
  rw [continuous_iff_continuousAt]
  intro v
  obtain ⟨g, hg⟩ := hL (D.exp v)
  obtain ⟨f, hf, hFf⟩ := H g
  have hopen : IsOpen {v : Lie A | secPt (D.exp v) ∈ g.U} := isOpen_exp_preimage D g.U
  have hnhds : {v : Lie A | secPt (D.exp v) ∈ g.U} ∈ nhds v := hopen.mem_nhds hg
  have h1 : ContinuousAt f v := hf.continuousAt hnhds
  exact h1.congr (Filter.eventually_of_mem hnhds fun w hw => (hFf w hw).symm)

/-- The ratio of two sections, a function `Lie A → ℂ`. -/
def ExpSection.ratio (hL : CoversPoints L) (s s' : ExpSection D L) (v : Lie A) : ℂ :=
  Fibre.ratio hL (s'.val v) (s.val v)

theorem ExpSection.continuous_ratio (hL : CoversPoints L) {s : ExpSection D L}
    (hs : s.NonVanishing) (s' : ExpSection D L) : Continuous (s.ratio hL s') :=
  continuous_of_local (D := D) hL _ fun g =>
    ⟨fun v => Fibre.coord L g (D.exp v) (s'.val v) / Fibre.coord L g (D.exp v) (s.val v),
      (s'.cont g).div (s.cont g) fun v hv => Fibre.coord_ne_zero (hs v) g hv,
      fun v hv => Fibre.ratio_eq hL rfl _ _ (hs v) g hv⟩

theorem ExpSection.ratio_ne_zero (hL : CoversPoints L) {s s' : ExpSection D L}
    (hs : s.NonVanishing) (hs' : s'.NonVanishing) (v : Lie A) : s.ratio hL s' v ≠ 0 :=
  Fibre.ratio_ne_zero hL rfl (hs' v) (hs v)

/-- The **automorphy factor** of the section `s` with respect to the period `a`:
`e_a(v) = s(v + a) / s(v)`. -/
def ExpSection.aut (hL : CoversPoints L) (s : ExpSection D L) (a : Lie A) (v : Lie A) : ℂ :=
  Fibre.ratio hL (s.val (v + a)) (s.val v)

theorem ExpSection.aut_ne_zero (hL : CoversPoints L) {s : ExpSection D L} (hs : s.NonVanishing)
    {a : Lie A} (ha : IsPeriod D a) (v : Lie A) : s.aut hL a v ≠ 0 :=
  Fibre.ratio_ne_zero hL (ha v) (hs _) (hs _)

theorem ExpSection.continuous_aut (hL : CoversPoints L) {s : ExpSection D L}
    (hs : s.NonVanishing) {a : Lie A} (ha : IsPeriod D a) : Continuous (s.aut hL a) := by
  refine continuous_of_local (D := D) hL _ fun g => ⟨fun v =>
    Fibre.coord L g (D.exp (v + a)) (s.val (v + a)) / Fibre.coord L g (D.exp v) (s.val v),
    ?_, fun v hv => Fibre.ratio_eq hL (ha v) _ _ (hs v) g hv⟩
  refine ContinuousOn.div ?_ (s.cont g) fun v hv => Fibre.coord_ne_zero (hs v) g hv
  exact (s.cont g).comp (continuous_add_right_lie a).continuousOn fun v hv => by
    change secPt (D.exp (v + a)) ∈ g.U
    rw [ha v]; exact hv

theorem ExpSection.aut_add (hL : CoversPoints L) {s : ExpSection D L} (hs : s.NonVanishing)
    {a b : Lie A} (ha : IsPeriod D a) (hb : IsPeriod D b) (v : Lie A) :
    s.aut hL (a + b) v = s.aut hL a (v + b) * s.aut hL b v := by
  unfold ExpSection.aut
  have e : v + (a + b) = v + b + a := by abel
  rw [e]
  exact (Fibre.ratio_mul hL (ha (v + b)) (hb v) _ _ _ (hs _) (hs _)).symm

/-- The cocycle identity in the commuted form `e_a(v + b) e_b(v) = e_b(v + a) e_a(v)`. -/
theorem ExpSection.aut_comm (hL : CoversPoints L) {s : ExpSection D L} (hs : s.NonVanishing)
    {a b : Lie A} (ha : IsPeriod D a) (hb : IsPeriod D b) (v : Lie A) :
    s.aut hL a (v + b) * s.aut hL b v = s.aut hL b (v + a) * s.aut hL a v := by
  rw [← s.aut_add hL hs ha hb, ← s.aut_add hL hs hb ha, add_comm]

/-- Changing the section by `u = s'/s` changes the automorphy factor accordingly. -/
theorem ExpSection.aut_ratio (hL : CoversPoints L) {s s' : ExpSection D L} (hs : s.NonVanishing)
    (hs' : s'.NonVanishing) {a : Lie A} (ha : IsPeriod D a) (v : Lie A) :
    s'.aut hL a v = s.aut hL a v * s.ratio hL s' (v + a) / s.ratio hL s' v := by
  obtain ⟨g, hg⟩ := hL (D.exp v)
  have hg' : secPt (D.exp (v + a)) ∈ g.U := by rw [ha v]; exact hg
  unfold ExpSection.aut ExpSection.ratio
  rw [Fibre.ratio_eq hL (ha v) _ _ (hs' v) g hg, Fibre.ratio_eq hL (ha v) _ _ (hs v) g hg,
    Fibre.ratio_eq hL rfl _ _ (hs (v + a)) g hg', Fibre.ratio_eq hL rfl _ _ (hs v) g hg]
  have h1 := Fibre.coord_ne_zero (hs v) g hg
  have h2 := Fibre.coord_ne_zero (hs (v + a)) g hg'
  have h3 := Fibre.coord_ne_zero (hs' v) g hg
  have h4 := Fibre.coord_ne_zero (hs' (v + a)) g hg'
  field_simp

end Exp

section Chern

open unitInterval

variable {A : CSch} [GrpObj A] {D : UniformizationData A} {L : A.left.Modules}

theorem continuous_line (x y : Lie A) : Continuous fun t : ℝ => x + (t : ℂ) • y :=
  continuous_of_tangentEval fun U hU s => by
    simp only [tangentEval_add, tangentEval_smul]
    fun_prop

/-- The straight path `t ↦ u (x + t y)`, `t ∈ [0,1]`, in `Lie A`, composed with `u`. -/
def lineFrom (u : Lie A → ℂ) (x y : Lie A) : I → ℂ := fun t => u (x + ((t : ℝ) : ℂ) • y)

theorem continuous_lineFrom {u : Lie A → ℂ} (hu : Continuous u) (x y : Lie A) :
    Continuous (lineFrom u x y) :=
  hu.comp ((continuous_line x y).comp continuous_subtype_val)

/-- The total change of a logarithm of `u` along the straight path from `x` to `x + y`. -/
def lineLog (u : Lie A → ℂ) (x y : Lie A) : ℂ := logChange (lineFrom u x y)

theorem isLogChange_lineLog {u : Lie A → ℂ} (hu : Continuous u) (h0 : ∀ v, u v ≠ 0)
    (x y : Lie A) : IsLogChange (lineFrom u x y) (lineLog u x y) :=
  isLogChange_logChange (continuous_lineFrom hu x y) fun _ => h0 _

theorem lineLog_mul {u w : Lie A → ℂ} (hu : Continuous u) (hu0 : ∀ v, u v ≠ 0)
    (hw : Continuous w) (hw0 : ∀ v, w v ≠ 0) (x y : Lie A) :
    lineLog (fun v => u v * w v) x y = lineLog u x y + lineLog w x y :=
  ((isLogChange_lineLog hu hu0 x y).mul (isLogChange_lineLog hw hw0 x y)).logChange_eq

theorem lineLog_div {u w : Lie A → ℂ} (hu : Continuous u) (hu0 : ∀ v, u v ≠ 0)
    (hw : Continuous w) (hw0 : ∀ v, w v ≠ 0) (x y : Lie A) :
    lineLog (fun v => u v / w v) x y = lineLog u x y - lineLog w x y :=
  ((isLogChange_lineLog hu hu0 x y).div (isLogChange_lineLog hw hw0 x y)).logChange_eq

theorem lineLog_shift (u : Lie A → ℂ) (c x y : Lie A) :
    lineLog (fun v => u (v + c)) x y = lineLog u (x + c) y := by
  have h : lineFrom (fun v => u (v + c)) x y = lineFrom u (x + c) y := by
    funext t
    simp only [lineFrom, add_right_comm]
  unfold lineLog
  rw [h]

theorem lineLog_congr {u w : Lie A → ℂ} (h : ∀ v, u v = w v) (x y : Lie A) :
    lineLog u x y = lineLog w x y := by
  have h' : lineFrom u x y = lineFrom w x y := funext fun t => h _
  unfold lineLog
  rw [h']

/-- The function `u` on the parallelogram spanned by `a` and `b`, parametrised by the unit
square. -/
def squareFun (u : Lie A → ℂ) (a b : Lie A) (p : I × I) : ℂ :=
  u (((p.1 : ℝ) : ℂ) • a + ((p.2 : ℝ) : ℂ) • b)

theorem continuous_square_map (a b : Lie A) :
    Continuous fun p : I × I => ((((p.1 : ℝ) : ℂ) • a + ((p.2 : ℝ) : ℂ) • b : Lie A)) :=
  continuous_of_tangentEval fun U hU s => by
    simp only [tangentEval_add, tangentEval_smul]
    fun_prop

theorem continuous_squareFun {u : Lie A → ℂ} (hu : Continuous u) (a b : Lie A) :
    Continuous (squareFun u a b) :=
  hu.comp (continuous_square_map a b)

/-- **The parallelogram lemma**: a continuous nowhere vanishing function on the real vector space
`Lie A` has a logarithm on every parallelogram (the square is simply connected), so its
total logarithmic changes along the two routes `0 → a → a + b` and `0 → b → a + b` agree, and
along the diagonal. -/
theorem lineLog_parallelogram {u : Lie A → ℂ} (hu : Continuous u) (h0 : ∀ v, u v ≠ 0)
    (a b : Lie A) :
    lineLog u 0 a + lineLog u a b = lineLog u 0 b + lineLog u b a ∧
      lineLog u 0 (a + b) = lineLog u 0 a + lineLog u a b := by
  obtain ⟨x, y, z, w, hx, hy, hz, hw, hd, hxy⟩ :=
    square_log (squareFun u a b) (continuous_squareFun hu a b) fun _ => h0 _
  have e1 : (fun t : I => squareFun u a b (t, 0)) = lineFrom u 0 a := by
    funext t; simp [squareFun, lineFrom]
  have e2 : (fun t : I => squareFun u a b (1, t)) = lineFrom u a b := by
    funext t; simp [squareFun, lineFrom]
  have e3 : (fun t : I => squareFun u a b (0, t)) = lineFrom u 0 b := by
    funext t; simp [squareFun, lineFrom]
  have e4 : (fun t : I => squareFun u a b (t, 1)) = lineFrom u b a := by
    funext t; simp [squareFun, lineFrom, add_comm]
  have e5 : (fun t : I => squareFun u a b (t, t)) = lineFrom u 0 (a + b) := by
    funext t; simp [squareFun, lineFrom, smul_add]
  rw [e1] at hx
  rw [e2] at hy
  rw [e3] at hz
  rw [e4] at hw
  rw [e5] at hd
  unfold lineLog
  rw [hx.logChange_eq, hy.logChange_eq, hz.logChange_eq, hw.logChange_eq, hd.logChange_eq]
  exact ⟨hxy, rfl⟩

section ChernForm

variable (hL : CoversPoints L)

/-- **The Chern pairing of two periods with respect to a trivialization `s` of the pullback of
`L` along `exp`**, as a complex number: the total change of the logarithm of the automorphy
factor `e_a` along the segment `[0, b]` minus that of `e_b` along `[0, a]`. By the cocycle
identity it lies in `2πi ℤ` (`chernC_int`); it is independent of `s` (`chernC_ratio`). -/
def chernC (s : ExpSection D L) (a b : Lie A) : ℂ :=
  lineLog (s.aut hL a) 0 b - lineLog (s.aut hL b) 0 a

variable {hL}

theorem chernC_int {s : ExpSection D L} (hs : s.NonVanishing) {a b : Lie A} (ha : IsPeriod D a)
    (hb : IsPeriod D b) : ∃ n : ℤ, chernC hL s a b = n * (2 * Real.pi * Complex.I) := by
  have h1 := (isLogChange_lineLog (s.continuous_aut hL hs ha) (s.aut_ne_zero hL hs ha) 0 b).exp_eq
  have h2 := (isLogChange_lineLog (s.continuous_aut hL hs hb) (s.aut_ne_zero hL hs hb) 0 a).exp_eq
  have hc := s.aut_comm hL hs ha hb 0
  have n1 := s.aut_ne_zero hL hs ha b
  have n2 := s.aut_ne_zero hL hs ha 0
  have n3 := s.aut_ne_zero hL hs hb a
  have n4 := s.aut_ne_zero hL hs hb 0
  simp only [lineFrom, Set.Icc.coe_one, Set.Icc.coe_zero, Complex.ofReal_one, one_smul,
    Complex.ofReal_zero, zero_smul, zero_add, add_zero] at h1 h2 hc
  rw [← Complex.exp_eq_one_iff]
  unfold chernC
  rw [Complex.exp_sub, h1, h2]
  field_simp
  linear_combination hc

open Classical in
/-- The Chern form: the integer `n` with `chernC = 2πi n` (`0` if there is none). -/
def chernForm (s : ExpSection D L) (a b : Lie A) : ℤ :=
  if h : ∃ n : ℤ, chernC hL s a b = n * (2 * Real.pi * Complex.I) then h.choose else 0

theorem chernC_eq {s : ExpSection D L} (hs : s.NonVanishing) {a b : Lie A} (ha : IsPeriod D a)
    (hb : IsPeriod D b) :
    chernC hL s a b = chernForm (hL := hL) s a b * (2 * Real.pi * Complex.I) := by
  have h := chernC_int (hL := hL) hs ha hb
  unfold chernForm
  simp only [h, ↓reduceDIte]
  exact h.choose_spec

theorem two_pi_I_ne_zero : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
  simp [Real.pi_ne_zero]

theorem chernForm_eq_of_chernC_eq {s s' : ExpSection D L} (hs : s.NonVanishing)
    (hs' : s'.NonVanishing) {a b : Lie A} (ha : IsPeriod D a) (hb : IsPeriod D b)
    (h : chernC hL s' a b = chernC hL s a b) :
    chernForm (hL := hL) s' a b = chernForm (hL := hL) s a b := by
  rw [chernC_eq hs' ha hb, chernC_eq hs ha hb] at h
  exact_mod_cast mul_right_cancel₀ two_pi_I_ne_zero h

theorem lineLog_aut_ratio {s s' : ExpSection D L} (hs : s.NonVanishing) (hs' : s'.NonVanishing)
    {a : Lie A} (ha : IsPeriod D a) (b : Lie A) :
    lineLog (s'.aut hL a) 0 b =
      lineLog (s.aut hL a) 0 b + lineLog (s.ratio hL s') a b - lineLog (s.ratio hL s') 0 b := by
  have cu := s.continuous_ratio hL hs s'
  have nu := s.ratio_ne_zero hL hs hs'
  have ca := s.continuous_aut hL hs ha
  have na := s.aut_ne_zero hL hs ha
  have cu' : Continuous fun v => s.ratio hL s' (v + a) := cu.comp (continuous_add_right_lie a)
  rw [lineLog_congr (u := s'.aut hL a)
    (w := fun v => s.aut hL a v * s.ratio hL s' (v + a) / s.ratio hL s' v)
    (fun v => s.aut_ratio hL hs hs' ha v),
    lineLog_div (u := fun v => s.aut hL a v * s.ratio hL s' (v + a)) (w := s.ratio hL s')
      (ca.mul cu') (fun v => mul_ne_zero (na v) (nu _)) cu nu,
    lineLog_mul (u := s.aut hL a) (w := fun v => s.ratio hL s' (v + a)) ca na cu'
      (fun v => nu _), lineLog_shift, zero_add]

theorem chernC_ratio {s s' : ExpSection D L} (hs : s.NonVanishing) (hs' : s'.NonVanishing)
    {a b : Lie A} (ha : IsPeriod D a) (hb : IsPeriod D b) :
    chernC hL s' a b = chernC hL s a b := by
  have cu := s.continuous_ratio hL hs s'
  have nu := s.ratio_ne_zero hL hs hs'
  have hp := (lineLog_parallelogram cu nu a b).1
  unfold chernC
  rw [lineLog_aut_ratio hs hs' ha, lineLog_aut_ratio hs hs' hb]
  linear_combination hp

/-- **Independence of the trivialization**: the Chern form does not depend on the nonvanishing
section `s` of the pullback of `L` along `exp`. -/
theorem chernForm_ratio {s s' : ExpSection D L} (hs : s.NonVanishing) (hs' : s'.NonVanishing)
    {a b : Lie A} (ha : IsPeriod D a) (hb : IsPeriod D b) :
    chernForm (hL := hL) s' a b = chernForm (hL := hL) s a b :=
  chernForm_eq_of_chernC_eq hs hs' ha hb (chernC_ratio hs hs' ha hb)

theorem lineLog_aut_add {s : ExpSection D L} (hs : s.NonVanishing) {a a' : Lie A}
    (ha : IsPeriod D a) (ha' : IsPeriod D a') (b : Lie A) :
    lineLog (s.aut hL (a + a')) 0 b =
      lineLog (s.aut hL a) a' b + lineLog (s.aut hL a') 0 b := by
  have ca := s.continuous_aut hL hs ha
  have na := s.aut_ne_zero hL hs ha
  have ca' := s.continuous_aut hL hs ha'
  have na' := s.aut_ne_zero hL hs ha'
  have cs : Continuous fun v => s.aut hL a (v + a') := ca.comp (continuous_add_right_lie a')
  rw [lineLog_congr (u := s.aut hL (a + a'))
    (w := fun v => s.aut hL a (v + a') * s.aut hL a' v) (fun v => s.aut_add hL hs ha ha' v),
    lineLog_mul (u := fun v => s.aut hL a (v + a')) (w := s.aut hL a') cs (fun v => na _) ca' na',
    lineLog_shift, zero_add]

theorem lineLog_aut_comm {s : ExpSection D L} (hs : s.NonVanishing) {a b : Lie A}
    (ha : IsPeriod D a) (hb : IsPeriod D b) (c : Lie A) :
    lineLog (s.aut hL a) b c =
      lineLog (s.aut hL b) a c + lineLog (s.aut hL a) 0 c - lineLog (s.aut hL b) 0 c := by
  have ca := s.continuous_aut hL hs ha
  have na := s.aut_ne_zero hL hs ha
  have cb := s.continuous_aut hL hs hb
  have nb := s.aut_ne_zero hL hs hb
  have cs : Continuous fun v => s.aut hL b (v + a) := cb.comp (continuous_add_right_lie a)
  have e : ∀ v, s.aut hL a (v + b) = s.aut hL b (v + a) * s.aut hL a v / s.aut hL b v := by
    intro v
    rw [eq_div_iff (nb v)]
    exact s.aut_comm hL hs ha hb v
  have h1 : lineLog (s.aut hL a) b c = lineLog (fun v => s.aut hL a (v + b)) 0 c := by
    rw [lineLog_shift, zero_add]
  rw [h1, lineLog_congr e,
    lineLog_div (u := fun v => s.aut hL b (v + a) * s.aut hL a v) (w := s.aut hL b)
      (cs.mul ca) (fun v => mul_ne_zero (nb _) (na v)) cb nb,
    lineLog_mul (u := fun v => s.aut hL b (v + a)) (w := s.aut hL a) cs (fun v => nb _) ca na,
    lineLog_shift, zero_add]

/-- Additivity of the Chern pairing in the first variable. -/
theorem chernC_add_left {s : ExpSection D L} (hs : s.NonVanishing) {a a' b : Lie A}
    (ha : IsPeriod D a) (ha' : IsPeriod D a') (hb : IsPeriod D b) :
    chernC hL s (a + a') b = chernC hL s a b + chernC hL s a' b := by
  have cb := s.continuous_aut hL hs hb
  have nb := s.aut_ne_zero hL hs hb
  have ca := s.continuous_aut hL hs ha
  have na := s.aut_ne_zero hL hs ha
  have h1 := lineLog_aut_add (hL := hL) hs ha ha' b
  have h2 := (lineLog_parallelogram cb nb a a').2
  have h3 := lineLog_aut_comm (hL := hL) hs ha hb a'
  have h4 := (lineLog_parallelogram ca na a' b).1
  unfold chernC
  rw [h1, h2]
  linear_combination h3 + h4

theorem chernC_neg_swap (s : ExpSection D L) (a b : Lie A) :
    chernC hL s b a = -chernC hL s a b := by
  unfold chernC; ring

theorem chernC_self (s : ExpSection D L) (a : Lie A) : chernC hL s a a = 0 := by
  unfold chernC; ring

theorem chernC_add_right {s : ExpSection D L} (hs : s.NonVanishing) {a b b' : Lie A}
    (ha : IsPeriod D a) (hb : IsPeriod D b) (hb' : IsPeriod D b') :
    chernC hL s a (b + b') = chernC hL s a b + chernC hL s a b' := by
  have h1 := chernC_neg_swap (hL := hL) s a (b + b')
  have h2 := chernC_add_left (hL := hL) hs hb hb' ha
  have h3 := chernC_neg_swap (hL := hL) s a b
  have h4 := chernC_neg_swap (hL := hL) s a b'
  linear_combination h1 - h2 - h3 - h4

theorem chernForm_add_left {s : ExpSection D L} (hs : s.NonVanishing) {a a' b : Lie A}
    (ha : IsPeriod D a) (ha' : IsPeriod D a') (hb : IsPeriod D b) :
    chernForm (hL := hL) s (a + a') b =
      chernForm (hL := hL) s a b + chernForm (hL := hL) s a' b := by
  have h := chernC_add_left (hL := hL) hs ha ha' hb
  rw [chernC_eq hs (ha.add D ha') hb, chernC_eq hs ha hb, chernC_eq hs ha' hb, ← add_mul] at h
  exact_mod_cast mul_right_cancel₀ two_pi_I_ne_zero h

theorem chernForm_add_right {s : ExpSection D L} (hs : s.NonVanishing) {a b b' : Lie A}
    (ha : IsPeriod D a) (hb : IsPeriod D b) (hb' : IsPeriod D b') :
    chernForm (hL := hL) s a (b + b') =
      chernForm (hL := hL) s a b + chernForm (hL := hL) s a b' := by
  have h := chernC_add_right (hL := hL) hs ha hb hb'
  rw [chernC_eq hs ha (hb.add D hb'), chernC_eq hs ha hb, chernC_eq hs ha hb', ← add_mul] at h
  exact_mod_cast mul_right_cancel₀ two_pi_I_ne_zero h

theorem chernForm_self {s : ExpSection D L} (hs : s.NonVanishing) {a : Lie A} (ha : IsPeriod D a) :
    chernForm (hL := hL) s a a = 0 := by
  have h := chernC_self (hL := hL) s a
  rw [chernC_eq hs ha ha] at h
  have := (mul_eq_zero.1 h).resolve_right two_pi_I_ne_zero
  exact_mod_cast this

variable (hL) in
/-- **The Chern form of the invertible module `L` on the period lattice**: the `ℤ`-bilinear form
`(a, b) ↦ chernForm s a b` on the group of periods of `exp`, for any trivialization `s` of the
pullback of `L` along `exp` (`chernHom_eq`: independent of `s`). -/
@[expose] def chernHom {s : ExpSection D L} (hs : s.NonVanishing) :
    periodGroup D →+ periodGroup D →+ ℤ :=
  AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun b => chernForm (hL := hL) s a b)
    (fun b b' => chernForm_add_right hs a.2 b.2 b'.2))
    (fun a a' => AddMonoidHom.ext fun b => chernForm_add_left hs a.2 a'.2 b.2)

theorem chernHom_apply {s : ExpSection D L} (hs : s.NonVanishing) (a b : periodGroup D) :
    chernHom hL hs a b = chernForm (hL := hL) s a b := rfl

/-- **Independence of the choices**: two trivializations give the same Chern form. -/
theorem chernHom_eq {s s' : ExpSection D L} (hs : s.NonVanishing) (hs' : s'.NonVanishing) :
    chernHom hL hs = chernHom hL hs' := by
  refine AddMonoidHom.ext fun a => AddMonoidHom.ext fun b => ?_
  exact (chernForm_ratio hs hs' a.2 b.2).symm

theorem chernHom_self {s : ExpSection D L} (hs : s.NonVanishing) (a : periodGroup D) :
    chernHom hL hs a a = 0 := chernForm_self hs a.2

theorem chernHom_swap {s : ExpSection D L} (hs : s.NonVanishing) (a b : periodGroup D) :
    chernHom hL hs b a = -chernHom hL hs a b := by
  have h := chernC_neg_swap (hL := hL) s a b
  rw [chernC_eq hs b.2 a.2, chernC_eq hs a.2 b.2] at h
  have h' : ((chernForm (hL := hL) s b a : ℤ) : ℂ) = -((chernForm (hL := hL) s a b : ℤ) : ℂ) :=
    mul_right_cancel₀ two_pi_I_ne_zero (by rw [h]; ring)
  exact_mod_cast h'

end ChernForm

end Chern

end ArithmeticOfJacobiPolynomials.AbelianBettiChern
