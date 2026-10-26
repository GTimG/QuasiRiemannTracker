import Candidate.Target836.Source836.GlobalNamed
import Candidate.Cycle63.Physical.InitialCoarse
import Candidate.Cycle63.Physical.ExternalHeight
import Candidate.Cycle63.Moment.InitialAffineContract
import Candidate.Cycle63.Physical.InitialMass.GeometryBudgetContraction
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineCaps
import Candidate.Cycle63.Physical.InitialMass.GeometryMeshChoice
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalZeroRadius

/- Original module: Candidate.Target836.Source836.InitialHeight. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
namespace OAI.SevenEighths.Target836SourceAssembly
noncomputable section
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource QuadraticInitialBound Cycle63Moment
local notation "O" => HeckeFamily.O
variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
variable (R : Ideal O) [NeZero R]
local instance : Finite (O ⧸ R) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne R)
variable (H : Subgroup (O ⧸ R)ˣ) (hH : RayOrthogonality.globalUnits R ≤ H)

/-- The analytic input is restricted to the bounded external-height range,
with the same literal initial energy and geometric gates as Target836Moment.InitialAffineAt. -/
def BoundedInitialAffineAt (W : ℝ → ℂ) (bslot a b bΦ mesh lo hi Mmin Mmax ε τ Z : ℝ)
    (η η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ) : Prop :=
  ∀ T : Finset α, ∀ (θ : T → RayQuotient.Characters R H) (w σ v : T → ℝ)
    (t height : ℝ), (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) →
    (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) → 0 ≤ height → (∀ i, |v i| ≤ height) →
    1+|t|+height ≤ Z^τ →
  ∀ width : ℝ, Mmin ≤ width → width ≤ Mmax →
  ∀ Φ : 𝓢(ℝ,ℂ), Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic bΦ →
    (∀ x, 0 ≤ (Φ x).re) →
  ∀ p : Profiles a b, ∀ X₁ X₂ : ℝ, 0 < X₁ → 0 < X₂ →
    (41/100)*width ≤ length Z X₁ → length Z X₁ ≤ (44/100)*width →
    (41/100)*width ≤ length Z X₂ → length Z X₂ ≤ (44/100)*width →
    (17/500)*width ≤ ∑ i, w i → (∑ i, w i) ≤ (1/25)*width →
    length Z X₁+length Z X₂+GlobalNamed.lambda*(∑ i, w i) ≤
      GlobalNamed.B*width →
    initialEnergy R H hH W bslot Z width η η₀ Q T θ w σ v t X₁ X₂
      (p.profile 0) (p.profile 1) Φ ≤
      C*diagonalControl Φ*(p.control S)^2*(1+|t|+height)^degree*Z^(width+ε)

lemma profile_control_mono {a b : ℝ} (p : Profiles a b)
    {S T : Finset (ℕ × ℕ)} (hST : S ⊆ T) : p.control S ≤ p.control T := by
  unfold Profiles.control
  exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono hST) (p.profile 0))
    (Seminorm.le_def.mp (Finset.sup_mono hST) (p.profile 1))
    (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

lemma initial_plain_length_cap (Z X width Mmax : ℝ) (hZ : 1 < Z) (_hX : 0 < X)
    (hMmax : 0 ≤ Mmax) (hw : width ≤ Mmax)
    (hL : length Z X ≤ (44/100)*width) : X ≤ Z^(Mmax+1) := by
  apply (le_max_right 1 X).trans
  apply (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le (le_max_left 1 X))).mp
  change length Z X ≤ Mmax+1
  linarith

/-- The degree is fixed after the two genuine estimates and before the base,
slot data, profiles, and all external frequencies and heights. -/
theorem initial_height_extend (W : ℝ → ℂ) (bslot a b bΦ mesh lo hi Mmin Mmax extra ε τ : ℝ)
    (hτ : 0 < τ) (hMmin : 0 < Mmin) (hMM : Mmin ≤ Mmax)
    (jSmall jCoarse : ℕ) (Ssmall Scoarse : Finset (ℕ × ℕ)) :
    ∃ degree : ℕ, ∀ (η : Label → Character) (η₀ : Character) (Q : Ideal O)
      (Csmall Ccoarse : ℝ), 0 ≤ Csmall → 0 ≤ Ccoarse →
    (∀ᶠ Z : ℝ in atTop, ∀ label : Label,
      BoundedInitialAffineAt (α := α) R H hH W bslot a b bΦ mesh lo hi Mmin Mmax
        ε τ Z (η label) η₀ Q jSmall Ssmall Csmall) →
    (∀ᶠ Z : ℝ in atTop, ∀ label : Label,
      InitialCoarseAt (α := α) R H hH W bslot a b bΦ mesh lo hi Mmin Mmax
        extra Z (η label) η₀ Q jCoarse Scoarse Ccoarse) →
    ∀ᶠ Z : ℝ in atTop, ∀ label : Label,
      Target836Moment.InitialAffineAt (α := α) R H hH W bslot a b bΦ mesh lo hi Mmin Mmax
        ε Z (η label) η₀ Q degree (Ssmall ∪ Scoarse) (Csmall+Ccoarse) := by
  obtain ⟨degree,hdegree⟩ := Cycle63.Physical.extend_bounded_height_bound hτ extra ε jSmall jCoarse
  refine ⟨degree,?_⟩
  intro η η₀ Q Csmall Ccoarse hCs hCc hsmall hcoarse
  filter_upwards [hsmall,hcoarse,eventually_gt_atTop (1 : ℝ)] with Z hzsmall hzcoarse hZ
  intro label T θ w σ v t height hw hwm hσlo hσhi hheight hv width hwidth hwidthmax
    Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂ hl₁ hu₁ hl₂ hu₂ hwl hwu hcap
  have hMmax : 0 ≤ Mmax := hMmin.le.trans hMM
  have hXcap₁ := initial_plain_length_cap Z X₁ width Mmax hZ hX₁ hMmax hwidthmax hu₁
  have hXcap₂ := initial_plain_length_cap Z X₂ width Mmax hZ hX₂ hMmax hwidthmax hu₂
  let control := diagonalControl Φ*(p.control (Ssmall ∪ Scoarse))^2
  have hd := diagonalControl_nonneg Φ
  have hcontrol : 0 ≤ control := mul_nonneg hd (sq_nonneg _)
  have hpcS := profile_control_mono p (Finset.subset_union_left (s₁ := Ssmall) (s₂ := Scoarse))
  have hpcC := profile_control_mono p (Finset.subset_union_right (s₁ := Ssmall) (s₂ := Scoarse))
  have hpS := p.control_nonneg Ssmall
  have hpC := p.control_nonneg Scoarse
  have hZp : 0 < Z := zero_lt_one.trans hZ
  have hSmall : 1+|t|+height ≤ Z^τ →
      initialEnergy R H hH W bslot Z width (η label) η₀ Q T θ w σ v t X₁ X₂
        (p.profile 0) (p.profile 1) Φ ≤ Csmall*control*(1+|t|+height)^jSmall*Z^(width+ε) := by
    intro hheightcap
    have hh := hzsmall label T θ w σ v t height hw hwm hσlo hσhi hheight hv hheightcap
      width hwidth hwidthmax Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂ hl₁ hu₁ hl₂ hu₂ hwl hwu hcap
    apply hh.trans
    dsimp only [control]
    rw [←mul_assoc Csmall]
    gcongr
  have hCoarse : initialEnergy R H hH W bslot Z width (η label) η₀ Q T θ w σ v t X₁ X₂
      (p.profile 0) (p.profile 1) Φ ≤ Ccoarse*control*(1+|t|+height)^jCoarse*Z^(width+extra) := by
    have hh := hzcoarse label T θ w σ v t height hw hwm hσlo hσhi hheight
      width hwidth hwidthmax Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂ hXcap₁ hXcap₂
    apply hh.trans
    dsimp only [control]
    rw [←mul_assoc Ccoarse]
    gcongr
  have hh := hdegree Z (1+|t|+height) width
    (initialEnergy R H hH W bslot Z width (η label) η₀ Q T θ w σ v t X₁ X₂
      (p.profile 0) (p.profile 1) Φ) control Csmall Ccoarse hZ.le
    (by linarith [abs_nonneg t]) hcontrol hCs hCc hSmall hCoarse
  change initialEnergy R H hH W bslot Z width (η label) η₀ Q T θ w σ v t X₁ X₂
    (p.profile 0) (p.profile 1) Φ ≤ _
  exact hh.trans_eq (by dsimp only [control]; ring)

/-- A bounded-height affine theorem is the sole new analytic input. The
all-height coarse side is obtained from the original incumbent, with a common
final degree before the fixed bases and the live initial configurations. -/
theorem original_initial_height (W : ℝ → ℂ) (aslot bslot a b bΦ mesh lo hi Mmin Mmax coarseError ε τ : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1/4) (hb : 1 ≤ b) (hbΦ : 0 < bΦ)
    (hmesh : 0 ≤ mesh) (hMmin : 0 < Mmin) (hMM : Mmin ≤ Mmax)
    (hcError : 0 < coarseError) (hcOne : coarseError ≤ 1)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) (hτ : 0 < τ)
    (η : Label → Character) (jSmall : ℕ) (Ssmall : Finset (ℕ × ℕ))
    (hsmall : ∀ η₀ : Character, ∀ Q : Ideal O,
      Q ≤ R → internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
      ∃ Csmall : ℝ, 0 < Csmall ∧ ∀ᶠ Z : ℝ in atTop, ∀ label : Label,
        BoundedInitialAffineAt (α := α) R H hH W bslot a b bΦ mesh lo hi Mmin Mmax
          ε τ Z (η label) η₀ Q jSmall Ssmall Csmall) :
    ∃ degree : ℕ, ∃ S : Finset (ℕ × ℕ), ∀ η₀ : Character, ∀ Q : Ideal O,
      Q ≤ R → internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, ∀ label : Label,
      Target836Moment.InitialAffineAt (α := α) R H hH W bslot a b bΦ mesh lo hi Mmin Mmax
        ε Z (η label) η₀ Q degree S C := by
  obtain ⟨jCoarse,Scoarse,hcoarse⟩ := original_initial_coarse (α := α) R H hH W
    aslot bslot a b bΦ mesh lo hi Mmin Mmax coarseError haslot hWs hW hbslot
    ha haUpper hb hbΦ hmesh hMmin hMM hcError hcOne hbeta η
  obtain ⟨degree,hextend⟩ := initial_height_extend (α := α) (Label := Label) R H hH W
    bslot a b bΦ mesh lo hi Mmin Mmax
    (coarseError+2*(Fintype.card α : ℝ)*mesh) ε τ hτ hMmin hMM
    jSmall jCoarse Ssmall Scoarse
  refine ⟨degree,Ssmall ∪ Scoarse,?_⟩
  intro η₀ Q hQR hQ0 hQt hQ72
  obtain ⟨Csmall,hCs,hsmall⟩ := hsmall η₀ Q hQR hQ0 hQt hQ72
  obtain ⟨Ccoarse,hCc,hcoarse⟩ := hcoarse η₀ Q hQR hQ0 hQt hQ72
  refine ⟨Csmall+Ccoarse,add_pos hCs hCc,?_⟩
  exact hextend η η₀ Q Csmall Ccoarse hCs.le hCc.le hsmall
    (hcoarse.mono (fun _ h => h.2))

#print axioms profile_control_mono
#print axioms initial_plain_length_cap
#print axioms initial_height_extend
#print axioms original_initial_height
end
end OAI.SevenEighths.Target836SourceAssembly
end

/- Original module: Candidate.Target836.Source836.GeometryAffineAssembly. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Target836SourceAssembly
noncomputable section
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentSecondHeightFamily CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentLogDyadic Cycle63InitialSource Cycle63Physical Cycle63Moment
open CenteredMomentFirstSourceReduction CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O

/-- Constants are collected over every subset of the fixed original slot type,
before any live source, geometry bin, or shifted Mellin height is chosen. -/
theorem uniform_geometry_mass {α : Type*} [Fintype α] [DecidableEq α]
    (Ψ : 𝓢(ℝ,ℂ)) (degree windowDegree : ℕ) (ξ εbin : ℝ)
    (hξ : 0≤ξ) (hεbin : 0<εbin)
    (hc : HasCompactSupport logAnnulus) (hsm : ContDiff ℝ ∞ logAnnulus) :
    ∃C : ℝ,0< C ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1< Z,
    ∀T : Finset α,∀s : Input T,∀N : ℕ,∀a b E : ℝ,
      0< a → Fintype.card T≤ N → a≤ s.lower → s.upper≤ b →
      s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤ Z^(3:ℝ) → volume s≤ Z^(2:ℝ) → 0≤ E →
    ∀H : ℤ×(Fin 5→ℤ)→ℝ,
      (∀key∈commonGeometryBins s 1 1 Z Z ξ,0< H key) →
      (∀key∈commonGeometryBins s 1 1 Z Z ξ,∀(reflected : Bool)(t u : ℝ),
        geometryLiveBudget reflected s 1 1 Z Z ξ 1 (Real.logb Z (volume s))
          (zero_lt_one.trans hZ) key
          (fun q=> normPhase (coordinateBlock s 1 1 Ψ Z Z ξ q)) N b
          (s.t+2*Real.pi*(u-(if reflected then -t else t)))≤
          ((if reflected then E/H key else E*H key)*(1+‖t‖)^degree)*
            (1+‖u‖)^(2*windowDegree)) →
      physicalMass s 1 1 fixedBadMask 1 Ψ Z Z ξ/volume s≤ C*E*Z^(1+εbin) := by
  have hm (T : Finset α) := actual_physical_mass_from_geometry_budgets (ι:=T)
    Ψ 0 degree windowDegree hc hsm
  choose Cm hCm hm using hm
  have hb (T : Finset α) := common_geometry_bins_subpower (ι:=T) 2 2 3 ξ εbin
    (by norm_num) (by norm_num) (by norm_num) hξ hεbin
  choose Cb hCb hb using hb
  let C := 1+∑T : Finset α,Cm T*Cb T
  have ht (T : Finset α) : 0≤ Cm T*Cb T := mul_nonneg (hCm T) (hCb T).le
  have hC : 0< C := by
    have hh := Finset.sum_nonneg (fun T (_ : T∈(Finset.univ:Finset (Finset α)))=> ht T)
    dsimp [C];linarith
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_all.mpr hb,eventually_gt_atTop (1:ℝ)] with Z hb hZ
  intro _hZ T s N a b E ha hn hlo hhi hz₁ hz₂ hr hV hE H hH hbudget
  have hCt : Cm T*Cb T≤ C := by
    have hh := Finset.single_le_sum (fun T (_ : T∈(Finset.univ:Finset (Finset α)))=> ht T)
      (Finset.mem_univ T)
    dsimp [C];linarith
  by_cases hsource : 0< sourceRadius s
  · have hKi : Z⁻¹≤ Z^(2:ℝ) := (inv_le_one_of_one_le₀ hZ.le).trans
      (Real.one_le_rpow hZ.le (by norm_num : (0:ℝ)≤2))
    have hcard := hb T s 1 1 Z (zero_lt_one.trans hZ) (by simp) hz₁ hz₂ hsource hr hV hKi
    have hh := hm T s 1 1 Z Z ξ 3 1 (Real.logb Z (volume s))
      (zero_lt_one.trans hZ) hZ N a b ha hn hlo hhi (by simp) hz₁ hz₂ hr
      (fun _=> E) H (fun _ _=> hE) hH hbudget
    have hs : (∑key∈commonGeometryBins s 1 1 Z Z ξ,
        E/(1+dyadicScale key.1)^(0:ℕ))=
        ((commonGeometryBins s 1 1 Z Z ξ).card:ℝ)*E := by simp
    rw [hs,CenteredMomentFirstPhysicalOriginalMask.original_physicalMass] at hh
    have hv := volume_pos s
    apply (div_le_iff₀ hv).mpr
    calc
      physicalMass s 1 1 fixedBadMask 1 Ψ Z Z ξ
          ≤ Cm T*Z^(1:ℝ)*volume s*((commonGeometryBins s 1 1 Z Z ξ).card:ℝ)*E := by
            exact hh.trans_eq (by ring)
      _ ≤ Cm T*Z^(1:ℝ)*volume s*(Cb T*Z^εbin)*E :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard
          (mul_nonneg (mul_nonneg (hCm T) (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)) hv.le)) hE
      _ = (Cm T*Cb T)*E*Z^(1+εbin)*volume s := by
        rw [Real.rpow_add (zero_lt_one.trans hZ)];ring
      _ ≤ C*E*Z^(1+εbin)*volume s :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCt hE)
            (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)) hv.le
  · rw [CenteredMomentFirstPhysicalZeroRadius.physicalMass_zero s 1 1 hz₁ hz₂
      (le_of_not_gt hsource) fixedBadMask 1 Ψ Z Z ξ]
    simp only [zero_div]
    exact mul_nonneg (mul_nonneg hC.le hE) (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)


variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance affineAssemblyFiniteQuotient : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (Hray : Subgroup (O⧸rayM)ˣ)(hHray : RayOrthogonality.globalUnits rayM≤ Hray)

/-- The pending input is the literal full live budget, including the actual
phase weight and both orientations at every first-Mellin shifted height.
There is no initial energy or physical-mass premise. -/
def LiteralAffineGeometryBudget
    (W : ℝ→ℂ)(hW : Continuous W)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (η η₀ : Character)(Q : Ideal O)(bΦ mesh εmass τ ξ : ℝ) : Prop :=
  ∀Ψ : 𝓢(ℝ,ℂ), Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) →
    (∀x,0≤(Ψ x).re) →
  ∃externalDegree outerDegree windowDegree : ℕ,∃S : Finset (ℕ×ℕ),
  ∃C : ℝ,0< C ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1< Z,
  ∀T : Finset α,∀θ : T→RayQuotient.Characters rayM Hray,
  ∀w σ freq : T→ℝ,∀t height : ℝ,
    (∀i,0≤ w i) → (∀i,w i≤ mesh) →
    ∀hσlo : (∀i,(33/50:ℝ)≤σ i),∀hσhi : (∀i,σ i≤(33/50:ℝ)),
    0≤ height → (∀i,|freq i|≤ height) → 1+|t|+height≤ Z^τ →
  ∀Φ : 𝓢(ℝ,ℂ),∀hsΦ : Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ,
  ∀hpΦ : ∀x,0≤(Φ x).re,∀p : Profiles (1/4) (9/4),∀X₁ X₂ : ℝ,
  ∀hX₁ : 0< X₁,∀hX₂ : 0< X₂,
    (41/100:ℝ)≤ length Z X₁ → length Z X₁≤(44/100:ℝ) →
    (41/100:ℝ)≤ length Z X₂ → length Z X₂≤(44/100:ℝ) →
    (17/500:ℝ)≤∑i,w i → (∑i,w i)≤(1/25:ℝ) →
    length Z X₁+length Z X₂+GlobalNamed.lambda*(∑i,w i)≤ GlobalNamed.B →
  let state:=fixedParentState η (internalQ Q η₀) Φ bΦ Z 1 hZ (by norm_num) hsΦ hpΦ;
  let inp:=affineInput rayM Hray hHray η₀ θ W hW 1 2 (33/50) (33/50)
    (by norm_num) hWs w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p (by norm_num)
    1 t X₁ X₂ hX₁ hX₂;
  let E:=C*(p.control S)^2*(1+|t|+height)^externalDegree*Z^εmass;
  ∃H : ℤ×(Fin 5→ℤ)→ℝ,
    (∀key∈commonGeometryBins inp 1 1 Z Z ξ,0< H key) ∧
    ∀key∈commonGeometryBins inp 1 1 Z Z ξ,∀(reflected : Bool)(t' u : ℝ),
      geometryLiveBudget reflected inp 1 1 Z Z ξ 1 (Real.logb Z (volume inp))
        (zero_lt_one.trans hZ) key
        (fun q=> normPhase (coordinateBlock inp 1 1 Ψ Z Z ξ q)) (Fintype.card α) (9/4)
        (inp.t+2*Real.pi*(u-(if reflected then -t' else t')))≤
        ((if reflected then E/H key else E*H key)*(1+‖t'‖)^outerDegree)*
          (1+‖u‖)^(2*windowDegree)

/-- End-to-end width-one assembly for one fixed chosen character and ideal.
Only the actual live-budget estimate is pending. -/
theorem literal_geometry_initial_affine
    (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (η η₀ : Character)(Q : Ideal O)(bΦ mesh ε τ ξ : ℝ)
    (hbΦ : 0< bΦ)(hmesh : 0< mesh)(hε : 0<ε)(hτ : 0<τ)(hξ : 0<ξ)
    (hmeshComparison : mesh≤ Cycle63FirstActual.comparisonMesh 1 1 (ε/2))
    (hbeta : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤(3/4:ℝ))
    (hQray : Q≤ rayM)(hQ0 : internalQ Q η₀≠0)(hQt : internalQ Q η₀≠⊤)
    (hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)})
    (hc : HasCompactSupport logAnnulus)(hsm : ContDiff ℝ ∞ logAnnulus)
    (hbudget : LiteralAffineGeometryBudget (α:=α) rayM Hray hHray W hW.continuous
      hWs η η₀ Q bΦ mesh (ε/4) τ ξ) :
    ∃degree : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0< C ∧ ∀ᶠ Z : ℝ in atTop,
      Target836Moment.InitialAffineAt (α:=α) rayM Hray hHray W 2 (1/4) (9/4) bΦ mesh
        (33/50) (33/50) 1 1 ε Z η η₀ Q degree S C := by
  let anchors : Fin 1→Character:=fun _=>η
  obtain ⟨Ψ,hΨ,hΨpos,_,jr,Sr,hred⟩ := actual_initial_source_reduction_fixed_mesh
    (α:=α) rayM Hray hHray anchors W 1 2 (33/50) (33/50) (1/4) (9/4) bΦ
    1 1 (ε/2) ξ (by norm_num) hWs hW (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hbΦ (by norm_num) (by norm_num) (by positivity) hξ hbeta hκbeta
  obtain ⟨Cr,hCr,hred⟩:=hred η₀ Q hQray hQ0 hQt hQ72
  obtain ⟨jb,jo,jw,Sb,Cb,hCb,hbud⟩:=hbudget Ψ hΨ hΨpos
  obtain ⟨Cm,hCm,hmass⟩:=uniform_geometry_mass (α:=α) Ψ jo jw ξ (ε/4) hξ.le
    (by positivity) hc hsm
  let Js:=max jr jb
  let Ss:=Sr∪Sb
  let Cs:=2*Cm*Cb+Cr
  have hCs : 0< Cs := by dsimp [Cs];positivity
  have hsmall : ∀ᶠ Z : ℝ in atTop,
      BoundedInitialAffineAt (α:=α) rayM Hray hHray W 2 (1/4) (9/4) bΦ mesh
        (33/50) (33/50) 1 1 ε τ Z η η₀ Q Js Ss Cs := by
    obtain hcaps := eventual_affine_polynomial_caps (α:=α) rayM Hray hHray W hW.continuous
      1 2 (33/50) (33/50) (1/4) (9/4) 1 (by norm_num) hWs
      (by norm_num) (by norm_num) (by norm_num)
    filter_upwards [hred,hbud,hmass,hcaps,eventually_gt_atTop (1:ℝ)] with Z hr hb hm hcaps hZ
    intro T θ w σ freq t height hw hwm hσlo hσhi hh hv hheight M hM₁ hM₂ Φ hsΦ hpΦ
      p X₁ X₂ hX₁ hX₂ hlo₁ hhi₁ hlo₂ hhi₂ hslotlo hslothi hcell
    have hM : M=1 := le_antisymm hM₂ hM₁
    subst M
    simp only [mul_one] at hlo₁ hhi₁ hlo₂ hhi₂ hslotlo hslothi hcell
    let state:=fixedParentState η (internalQ Q η₀) Φ bΦ Z 1 hZ (by norm_num) hsΦ hpΦ
    let inp:=affineInput rayM Hray hHray η₀ θ W hW.continuous 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p (by norm_num)
      1 t X₁ X₂ hX₁ hX₂
    have hN : Fintype.card T≤ Fintype.card α :=
      Fintype.card_le_of_injective (fun i:T=> i.val) Subtype.val_injective
    have hcap:=hcaps.2 T η₀ θ w σ freq (fun i=>⟨hσlo i,hσhi i⟩) bΦ state p
      1 t X₁ X₂ hX₁ hX₂ (by norm_num) (by norm_num) hw (by simpa only [mul_one] using hlo₁) (by simpa only [mul_one] using hlo₂)
      (by simpa only [mul_one] using hhi₁) (by simpa only [mul_one] using hhi₂) hslothi
    obtain ⟨H,hH,hbound⟩:=hb hZ T θ w σ freq t height hw hwm hσlo hσhi hh hv hheight
      Φ hsΦ hpΦ p X₁ X₂ hX₁ hX₂ hlo₁ hhi₁ hlo₂ hhi₂ hslotlo hslothi hcell
    have he : 0≤ Cb*(p.control Sb)^2*(1+|t|+height)^jb*Z^(ε/4) := by positivity
    have hz₁ : inp.W₁ 0=0 := CenteredMomentDetectorPlainSource.support_zero
      (p.profile 0) (1/4) (9/4) (by norm_num) (p.support 0)
    have hz₂ : inp.W₂ 0=0 := CenteredMomentDetectorPlainSource.support_zero
      (p.profile 1) (1/4) (9/4) (by norm_num) (p.support 1)
    have hm' := hm hZ T inp (Fintype.card α) (1/4) (9/4)
      (Cb*(p.control Sb)^2*(1+|t|+height)^jb*Z^(ε/4)) (by norm_num) hN
      (by change (1/4:ℝ)≤1;norm_num) (by change (2:ℝ)≤9/4;norm_num)
      hz₁ hz₂
      (by simpa only [show (1:ℝ)+2=3 by norm_num] using hcap.2.2.2.1)
      (by simpa only [show (1:ℝ)+1=2 by norm_num] using hcap.2.2.1) he H hH hbound
    have hr' := hr.2 (0:Fin 1) T θ w σ freq t height hw
      (fun i=>(hwm i).trans hmeshComparison) hσlo hσhi hh hv
      1 (by norm_num) (by norm_num) Φ hsΦ hpΦ p X₁ X₂ hX₁ hX₂ (by simpa only [mul_one] using hlo₁) (by simpa only [mul_one] using hhi₁)
      (by simpa only [mul_one] using hlo₂) (by simpa only [mul_one] using hhi₂)
      hslothi hZ (by norm_num)
    have hpcR := profile_control_mono p (Finset.subset_union_left (s₁ := Sr) (s₂ := Sb))
    have hpcB0 := p.control_nonneg Sb
    have hpcB := profile_control_mono p (Finset.subset_union_right (s₁ := Sr) (s₂ := Sb))
    have hbase : 1≤1+|t|+height := by linarith [abs_nonneg t]
    have hpowR : (1+|t|+height)^jr≤(1+|t|+height)^Js :=
      pow_le_pow_right₀ hbase (le_max_left jr jb)
    have hpowB : (1+|t|+height)^jb≤(1+|t|+height)^Js :=
      pow_le_pow_right₀ hbase (le_max_right jr jb)
    have hzpow : Z^(1+ε/2)≤ Z^(1+ε) :=
      Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
    have hm'' : physicalMass inp 1 1 fixedBadMask 1 Ψ Z Z ξ/volume inp≤
        Cm*Cb*(p.control Ss)^2*(1+|t|+height)^Js*Z^(1+ε) := by
      apply hm'.trans
      calc
        _ = Cm*Cb*(p.control Sb)^2*(1+|t|+height)^jb*Z^(1+ε/2) := by
          calc
            _ = Cm*Cb*(p.control Sb)^2*(1+|t|+height)^jb*
                (Z^(ε/4)*Z^(1+ε/4)) := by ring
            _ = _ := by
              rw [←Real.rpow_add (zero_lt_one.trans hZ)]
              have heq : ε/4+(1+ε/4)=(1:ℝ)+ε/2 := by ring
              rw [heq]
        _ ≤ _ := by dsimp [Ss];gcongr
    change initialEnergy rayM Hray hHray W 2 Z 1 η η₀ Q T θ w σ freq t X₁ X₂
      (p.profile 0) (p.profile 1) Φ≤ _
    change initialEnergy rayM Hray hHray W 2 Z 1 η η₀ Q T θ w σ freq t X₁ X₂
      (p.profile 0) (p.profile 1) Φ≤
      2*diagonalControl Φ*(physicalMass inp 1 1 fixedBadMask 1 Ψ (Z^(1:ℝ)) Z ξ/volume inp)+
      Cr*diagonalControl Φ*(p.control Sr)^2*(1+|t|+height)^jr*Z^(1+ε/2) at hr'
    apply hr'.trans
    have hd := diagonalControl_nonneg Φ
    have hpc0:=p.control_nonneg Sr
    calc
      _ ≤ 2*diagonalControl Φ*(Cm*Cb*(p.control Ss)^2*(1+|t|+height)^Js*Z^(1+ε))+
          Cr*diagonalControl Φ*(p.control Ss)^2*(1+|t|+height)^Js*Z^(1+ε) := by
        apply add_le_add
        · simpa only [Real.rpow_one] using mul_le_mul_of_nonneg_left hm'' (mul_nonneg (by norm_num) hd)
        · dsimp only [Ss]
          gcongr
      _ = _ := by dsimp [Cs];ring
  obtain ⟨jc,Sc,hcoarse⟩:=original_initial_coarse (α:=α) rayM Hray hHray W 1 2
    (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1 1 (by norm_num) hWs hW
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hbΦ hmesh.le
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hbeta anchors
  obtain ⟨Cc,hCc,hcoarse⟩:=hcoarse η₀ Q hQray hQ0 hQt hQ72
  obtain ⟨degree,hext⟩:=initial_height_extend (α := α) (Label := Fin 1) rayM Hray hHray W 2
    (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1
    (1+2*(Fintype.card α:ℝ)*mesh) ε τ hτ (by norm_num) (by norm_num) Js jc Ss Sc
  refine ⟨degree,Ss∪Sc,Cs+Cc,add_pos hCs hCc,?_⟩
  have hh:=hext anchors η₀ Q Cs Cc hCs.le hCc.le
    (hsmall.mono (fun _ h _=> h)) (hcoarse.mono (fun _ h=> h.2))
  exact hh.mono (fun _ h=> h (0:Fin 1))

end
end OAI.SevenEighths.Target836SourceAssembly
#print axioms OAI.SevenEighths.Target836SourceAssembly.uniform_geometry_mass
#print axioms OAI.SevenEighths.Target836SourceAssembly.literal_geometry_initial_affine
end
