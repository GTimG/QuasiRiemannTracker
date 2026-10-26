/-
Reserve-balanced affine local-capacity adaptation for Kari Roegnvaldsson, with AI assistance.
Based on nielstron local44-20261013 and Kari Roegnvaldsson affine-local-20261013 at c707738.
Retains the amplifier and final savings while reallocating intermediate reserves.
Status: candidate under verification; no admission is claimed here.
All inherited attribution and Apache-2.0 notices are retained below.
Section hashes identify original, pre-adaptation module snapshots.
-/
/- Deterministically bundled proof sources; original notices are retained below.
Affine-capacity adaptation: the source module hashes below identify the
pre-adaptation provenance, not the modified declarations in this file. -/
import Submissions.certb_local_20261013.Bundles.B119
import Submissions.certb_local_20261013.Bundles.B120
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.PositiveSummability
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.PrimeSlotShift
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SlotNormalization

/- BEGIN ORIGINAL MODULE Analytic.JointFirstAnnularFixed ; sha256 104271884a81898e87c95ddbb4cca14550fe0d40322d8bd530018f8db9f2f6e9 -/
section


/-! The genuine high and non-high source estimates are joined under one
fixed global bin classifier and one common height exponent. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Set Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceSecondZeroEnergy
open CenteredMomentExceptionalAmplitudePair EisensteinSchwartzPoisson
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentCanonicalFirst CenteredMomentRankinRadical CenteredMomentSectorLocalization
open CenteredMomentAllocatedRayDictionary CenteredMomentFiniteProfileExceptional
open CenteredMomentAllocatedNaturalSource CenteredMomentPrimePool CenteredMomentPrimeElements
open HeckeInverseAmplification RayFourExpansion CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentFirstAmplifiedFourCoefficients
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
open CenteredMomentSecondEnergySplit CenteredMomentSupportedTailAggregate CenteredMomentLogDyadic
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

variable (M : Ideal O) [NeZero M]
local instance firstAnnularFixedFiniteQuotient : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem actual_literal_first_annular_targets_fixed
    (Wslot : ℝ → ℂ) (aslot bslot a b σlo σhi Mslot lower upper bplain₁ bplain₂ BRmask : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support Wslot ⊆ Icc aslot bslot)
    (hW : ContDiff ℝ ∞ Wslot) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1/4) (hb : 1 ≤ b)
    (hbplain₁ : b ≤ bplain₁) (hbplain₂ : b ≤ bplain₂)
    (hMslot : 0 ≤ Mslot) (hlower : 0 < lower) (hupper : 1 ≤ upper) (hBRmask : 0 ≤ BRmask)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) (hbetaTop : HeckeZeroSupremum.beta ≤ 7/8)
    (lows highs : α → ℝ) (hlows : ∀ i,0 < lows i) (hhighs : ∀ i,0 ≤ highs i)
    (ηfirst : Character) (profile : Profiles a b)
    (η₀ : Character) (Q : Ideal O) (hQM : Q ≤ M)
    (hQ0 : internalQ Q η₀ ≠ 0) (hQt : internalQ Q η₀ ≠ ⊤)
    (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)})
    (hQη : internalQ Q η₀ ≤ ηfirst.modulus) :
    ∃ ν C : ℝ, 0 < ν ∧ 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (θ : α → RayQuotient.Characters M H) (w σ freq : α → ℝ) (height : ℝ),
      (∀ i,0 ≤ w i) → (∀ i,w i ≤ lowLocalMesh) →
      (∀ i,σlo ≤ σ i) → (∀ i,σ i ≤ σhi) →
      0 ≤ height → height ≤ Z^ν → (∀ i,|freq i| ≤ height) →
    ∀ (src : Input α), Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
      (∀ i,src.hi i ≤ bslot) → (∀ i,src.M i ≤ Mslot) →
      (∀ i,src.lo i = lows i) → (∀ i,src.hi i = highs i) →
      lower ≤ src.lower → src.upper ≤ upper →
      (∀ i,|src.hi i| ≤ upper) → |src.b₁| ≤ bplain₁ → |src.b₂| ≤ bplain₂ →
      0 ≤ src.b₁ → 0 ≤ src.b₂ → src.b₁ ≤ max 1 b → src.b₂ ≤ max 1 b →
      profile.profile 0 = src.W₁ → profile.profile 1 = src.W₂ → src.η = ηfirst →
      0 < sourceRadius src →
      Real.logb Z src.X₁ ≤ 423/1000 → Real.logb Z src.X₂ ≤ 423/1000 →
      Real.logb Z src.Y₁ ≤ 1 → Real.logb Z src.Y₂ ≤ 1 →
      (∑ i,w i) ≤ 37/1000 →
      localRegion (Real.logb Z src.X₁) (Real.logb Z src.X₂) (∑ i,w i) →
      Z^(1/4:ℝ) ≤ src.X₁ → Z^(1/4:ℝ) ≤ src.X₂ →
      Z^(1/4:ℝ) ≤ src.Y₁ → Z^(1/4:ℝ) ≤ src.Y₂ →
    ∀ (R : Ideal O), R ≠ 0 → (R.absNorm : ℝ) ≤ Z^BRmask →
    ∀ (hz₁ : src.W₁ 0=0) (hz₂ : src.W₂ 0=0),
    let radius := actualLowFirstRadius src R 1 Z Z nonHighCutoff
    let q := firstSourceOuterLabel src R 1 Z radius
    ∀ (labels : Finset (FirstSourceOuterIndex src R 1 Z radius))
      (refIndex : FirstSourceOuterIndex src R 1 Z radius), refIndex ∈ labels →
    ∀ eFirst : ℝ, 0 < eFirst → eFirst ≤ lowLocalTiny/8 →
      (∀ i ∈ labels,∀ j,|(q i).fullWidthCoordinates Z j-(q refIndex).fullWidthCoordinates Z j| < eFirst) →
    ∀ (t : Bool → ((i : FirstSourceOuterIndex src R 1 Z radius) × (q i).SourceIndex) → ℝ),
      (∀ left,∀ k ∈ firstSourceLabels labels q,|t left k| ≤ Z^ν) →
    ∀ left,
      firstLiteralAnnularEnergy src R Z labels left (t left) ≤
        (volume src.toData/(((q refIndex).sideCommon left).absNorm : ℝ))*
          (C*Z^((q refIndex).sideTargetWidth left Z
            (Real.logb Z (volume src.toData)))) := by
  have hcap := (high_local_product_parameters BRmask (Fintype.card α) hBRmask).2.2.1
  exact actual_literal_first_annular_targets M H hH
    Wslot aslot bslot a b σlo σhi Mslot lower upper bplain₁ bplain₂ BRmask
    haslot hWs hW hbslot ha haUpper hb hbplain₁ hbplain₂ hMslot hlower hupper hBRmask hbeta hbetaTop
    lows highs hlows hhighs ηfirst profile fixedBadPrimes (fun _ h => h)
    (highLocalBinCap BRmask (Fintype.card α)/2) (half_pos hcap) (half_le_self hcap.le)
    η₀ Q hQM hQ0 hQt hQ72 hQη ∅
    primeTest primeTest.contDiff primeTest.hasCompactSupport primeTest_tsupport
    (fun _ => primeTest.nonneg) primeTest_ne_zero (1/2) 1 1
    (by norm_num) (by norm_num) (by norm_num) primeTest_support (fun _ => primeTest.le_one)

#print axioms actual_literal_first_annular_targets_fixed
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstAnnularFixed -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstNaturalMoment ; sha256 12c7ffceb1fd6b7989011b9c8c915f361cf2db5929e73c46fc73936ddbb8b2a7 -/
section



/-! The literal natural fourth moment on the affine local capacity region. Both
annular branches are supplied by the actual analytic proof; no moment,
population, bin, or source-target bound remains as a premise. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceInputTailUniform CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstPhysicalSource CenteredMomentLogDyadic
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentEnergyNaturalInputMatches CenteredMomentFirstAnnularMajorant
open CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
local instance naturalMomentSumDecEq : DecidableEq (α ⊕ Fin 2) := Classical.decEq _

variable (M : Ideal O) [NeZero M]
local instance naturalMomentFinite : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- Genuine local natural energy estimate at bounded heights, for fixed
plain and radial profiles. The common anchor and compatible fixed modulus
are chosen before the height exponent, and the natural-state restrictions
are retained exactly. -/
theorem actual_local_natural_moment
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (Wslot : ℝ → ℂ) (aslot bslot lo hi a b bΦ Bmask ε : ℝ)
    (haslot : 0 < aslot) (hsSlot : Function.support Wslot ⊆ Set.Icc aslot bslot)
    (hcSlot : ContDiff ℝ ∞ Wslot) (hbslot : 0 < bslot)
    (ha : 0 < a) (hlo : a ≤ 1/4) (hhi : 1 ≤ b)
    (hbΦ : 0 < bΦ) (hBmask : 0 ≤ Bmask) (hε : 0 < ε)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) (hbetaTop : HeckeZeroSupremum.beta ≤ 7/8) :
    ∃ mesh : ℝ, 0 < mesh ∧ mesh ≤ lowLocalMesh ∧ ∃ J : ℕ,
    ∀ (ηfirst η₀ : Character) (Q : Ideal O), Q ≤ M →
      internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ → internalQ Q η₀ ≤ Ideal.span {(72:O)} →
      internalQ Q η₀ ≤ ηfirst.modulus →
    ∀ (p : Profiles a b) (Wradial : 𝓢(ℝ,ℂ)),
    ∃ ν C : ℝ, 0 < ν ∧ 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (θ : α → RayQuotient.Characters M H) (w σ freq : α → ℝ) (t height : ℝ),
      (∀ i,0 ≤ w i) → (∀ i,w i ≤ mesh) →
    ∀ (hσlo : ∀ i,lo ≤ σ i) (hσhi : ∀ i,σ i ≤ hi),
      0 ≤ height → height ≤ Z^ν → (∀ i,|freq i| ≤ height) → |t| ≤ Z^ν →
    ∀ (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂),
      410/1000 ≤ Real.logb Z X₁ → 410/1000 ≤ Real.logb Z X₂ →
      Real.logb Z X₁ ≤ 423/1000 → Real.logb Z X₂ ≤ 423/1000 →
      (∑ i,w i) ≤ 37/1000 →
      localRegion (Real.logb Z X₁) (Real.logb Z X₂) (∑ i,w i) →
    ∀ s : NaturalState Z Bmask bΦ,
      s.fixedModulus = internalQ Q η₀ → s.character = ηfirst → s.rowWidth = 1 →
      s.characterWidth = Real.logb Z (ηfirst.modulus.absNorm : ℝ) → s.radial.profile = Wradial →
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i => CenteredMomentPrimeSlot.primePool M H bslot (Z^(w i)))
        (fun i I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i => Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
        C*(1+|t|+height)^J*Z^(1+ε) := by
  let e := min ε (lowLocalTiny/8)
  have he : 0 < e := lt_min hε (by norm_num [lowLocalTiny])
  have heε : e ≤ ε := min_le_left _ _
  have hecap : e ≤ lowLocalTiny/8 := min_le_right _ _
  have hcut : 0 < nonHighCutoff := by norm_num [nonHighCutoff,lowLocalTiny]
  have hcutcap : nonHighCutoff ≤ 1 := by norm_num [nonHighCutoff,lowLocalTiny]
  obtain ⟨mesh,hmesh,hmeshcap,J,hnatural⟩ := actual_local_natural_from_annular (α := α) M H hH
    Wslot aslot bslot lo hi a b bΦ Bmask ε nonHighCutoff e
    haslot hsSlot hcSlot hbslot ha hlo hhi hbΦ hBmask hε hcut hcutcap he heε hbeta hbetaTop
  refine ⟨mesh,hmesh,hmeshcap,J,?_⟩
  intro ηfirst η₀ Q hQM hQzero hQtop hQ72 hQη p Wradial
  let F := profileBound Wslot hcSlot.continuous aslot bslot lo hi haslot hsSlot
  have hF : 0 ≤ F := zero_le_one.trans
    (profileBound_ge_one Wslot hcSlot.continuous aslot bslot lo hi haslot hsSlot)
  obtain ⟨ηheight,CAnn,hηheight,hCAnn,hannular⟩ := actual_literal_first_annular_targets_fixed
    (α := α) M H hH Wslot aslot bslot a b lo hi F aslot (max 1 bslot) b b Bmask
    haslot hsSlot hcSlot hbslot.le ha hlo hhi le_rfl le_rfl hF haslot (le_max_left _ _) hBmask hbeta hbetaTop
    (fun _ => aslot) (fun _ => bslot) (fun _ => haslot) (fun _ => hbslot.le)
    ηfirst p η₀ Q hQM hQzero hQtop hQ72 hQη
  let ν := ηheight/2
  have hν : 0 < ν := half_pos hηheight
  have hgap : ν < ηheight := half_lt_self hηheight
  obtain ⟨C,hC,hnatural⟩ := hnatural ηfirst η₀ Q hQM hQzero hQtop hQ72 p Wradial ν ηheight CAnn hν hgap hCAnn.le
  refine ⟨ν,C,hν,hC,?_⟩
  filter_upwards [hnatural,hannular,
    LocalFirstNaturalSource.eventually_join_geometry (α := α) M H hH Wslot hcSlot.continuous
      aslot bslot lo hi a b haslot hbslot hsSlot ha hhi] with Z hnatural hannular hgeometry
  refine ⟨hnatural.1,?_⟩
  intro θ w σ freq t height hw hwmesh hσlo hσhi hheight hheightCap hfreq ht
    X₁ X₂ hX₁ hX₂ hn₁lo hn₂lo hn₁hi hn₂hi hsum hcapacity s hQ hη hrow hwidth hradial
  let src := LocalFirstNaturalSource.input M H hH η₀ θ Wslot hcSlot.continuous
    aslot bslot lo hi haslot hsSlot w σ freq (fun i => ⟨hσlo i,hσhi i⟩)
    s p ha t X₁ X₂ hX₁ hX₂
  have hwlocal : ∀ i,w i ≤ lowLocalMesh := fun i => (hwmesh i).trans hmeshcap
  have hg := hgeometry.2 η₀ θ w σ freq (fun i => ⟨hσlo i,hσhi i⟩) Bmask bΦ s p
    t X₁ X₂ hX₁ hX₂ hw hwlocal hn₁lo hn₂lo hn₁hi hn₂hi hsum hcapacity
  have hp := LocalFirstNaturalSource.plain_join_gates M H hH η₀ θ Wslot hcSlot.continuous
    aslot bslot lo hi haslot hsSlot w σ freq (fun i => ⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂
  have hm := LocalFirstNaturalSource.input_matches M H hH η₀ θ Wslot hcSlot.continuous
    aslot bslot lo hi haslot hsSlot w σ freq (fun i => ⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂
  have hheightAnn : height ≤ Z^ηheight := hheightCap.trans
    (Real.rpow_le_rpow_of_exponent_le hnatural.1.le hgap.le)
  have hsourceAnn := hannular.2 θ w σ freq height hw hwlocal hσlo hσhi hheight hheightAnn hfreq
    src hm (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => rfl) (fun _ => rfl)
    le_rfl (le_max_right _ _)
    (fun _ => by change |bslot| ≤ max 1 bslot; rw [abs_of_pos hbslot]; exact le_max_right _ _)
    (by change |b| ≤ b; rw [abs_of_nonneg (zero_le_one.trans hhi)])
    (by change |b| ≤ b; rw [abs_of_nonneg (zero_le_one.trans hhi)])
    (zero_le_one.trans hhi) (zero_le_one.trans hhi) (le_max_right _ _) (le_max_right _ _)
    rfl rfl hη hg.source_positive hn₁hi hn₂hi hg.comparison_upper.1 hg.comparison_upper.2 hsum hcapacity
    hg.rectangle_lower.1 hg.rectangle_lower.2.1 hg.rectangle_lower.2.2.1 hg.rectangle_lower.2.2.2
    s.puncture s.puncture_ne_zero s.puncture_bound hp.1 hp.2.1
  apply hnatural.2 θ w σ freq t height hw hwmesh hσlo hσhi hheight hheightCap hfreq ht
    X₁ X₂ hX₁ hX₂ hn₁lo hn₂lo hn₁hi hn₂hi hsum hcapacity s hQ hη hrow hwidth hradial
  dsimp only [FirstNaturalAnnularTargets]
  intro labels hlabels ref href hclose hmin u hu left
  exact hsourceAnn labels ref href e he hecap hclose u hu left

#print axioms actual_local_natural_moment
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstNaturalMoment -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstNaturalMomentExplicitMesh ; sha256 4dcc9151511ffc4d62533e92284df4f45e0c7f72d8f6ff7485aab3816a77db2c -/
section



/-! The literal natural fourth moment on the affine local capacity region. Both
annular branches are supplied by the actual analytic proof; no moment,
population, bin, or source-target bound remains as a premise. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceInputTailUniform CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstPhysicalSource CenteredMomentLogDyadic
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentEnergyNaturalInputMatches CenteredMomentFirstAnnularMajorant
open CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
local instance naturalMomentExplicitSumDecEq : DecidableEq (α ⊕ Fin 2) := Classical.decEq _

variable (M : Ideal O) [NeZero M]
local instance naturalMomentExplicitFinite : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- Genuine local natural energy estimate at bounded heights, for fixed
plain and radial profiles. The common anchor and compatible fixed modulus
are chosen before the height exponent, and the natural-state restrictions
are retained exactly. -/
theorem actual_local_natural_moment_explicit_mesh
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (Wslot : ℝ → ℂ) (aslot bslot lo hi a b bΦ Bmask ε : ℝ)
    (haslot : 0 < aslot) (hsSlot : Function.support Wslot ⊆ Set.Icc aslot bslot)
    (hcSlot : ContDiff ℝ ∞ Wslot) (hbslot : 0 < bslot)
    (ha : 0 < a) (hlo : a ≤ 1/4) (hhi : 1 ≤ b)
    (hbΦ : 0 < bΦ) (hBmask : 0 ≤ Bmask) (hε : 0 < ε)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) (hbetaTop : HeckeZeroSupremum.beta ≤ 7/8) :
    ∃ J : ℕ,
    ∀ (ηfirst η₀ : Character) (Q : Ideal O), Q ≤ M →
      internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ → internalQ Q η₀ ≤ Ideal.span {(72:O)} →
      internalQ Q η₀ ≤ ηfirst.modulus →
    ∀ (p : Profiles a b) (Wradial : 𝓢(ℝ,ℂ)),
    ∃ ν C : ℝ, 0 < ν ∧ 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (θ : α → RayQuotient.Characters M H) (w σ freq : α → ℝ) (t height : ℝ),
      (∀ i,0 ≤ w i) → (∀ i,w i ≤ meshGuaranteed Bmask ε) →
    ∀ (hσlo : ∀ i,lo ≤ σ i) (hσhi : ∀ i,σ i ≤ hi),
      0 ≤ height → height ≤ Z^ν → (∀ i,|freq i| ≤ height) → |t| ≤ Z^ν →
    ∀ (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂),
      410/1000 ≤ Real.logb Z X₁ → 410/1000 ≤ Real.logb Z X₂ →
      Real.logb Z X₁ ≤ 423/1000 → Real.logb Z X₂ ≤ 423/1000 →
      (∑ i,w i) ≤ 37/1000 →
      localRegion (Real.logb Z X₁) (Real.logb Z X₂) (∑ i,w i) →
    ∀ s : NaturalState Z Bmask bΦ,
      s.fixedModulus = internalQ Q η₀ → s.character = ηfirst → s.rowWidth = 1 →
      s.characterWidth = Real.logb Z (ηfirst.modulus.absNorm : ℝ) → s.radial.profile = Wradial →
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i => CenteredMomentPrimeSlot.primePool M H bslot (Z^(w i)))
        (fun i I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i => Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
        C*(1+|t|+height)^J*Z^(1+ε) := by
  let e := min ε (lowLocalTiny/8)
  have he : 0 < e := lt_min hε (by norm_num [lowLocalTiny])
  have heε : e ≤ ε := min_le_left _ _
  have hecap : e ≤ lowLocalTiny/8 := min_le_right _ _
  have hcut : 0 < nonHighCutoff := by norm_num [nonHighCutoff,lowLocalTiny]
  have hcutcap : nonHighCutoff ≤ 1 := by norm_num [nonHighCutoff,lowLocalTiny]
  obtain ⟨J,hnatural⟩ := actual_local_natural_from_annular_explicit_mesh (α := α) M H hH
    Wslot aslot bslot lo hi a b bΦ Bmask ε nonHighCutoff e
    haslot hsSlot hcSlot hbslot ha hlo hhi hbΦ hBmask hε hcut hcutcap he heε hbeta hbetaTop
  refine ⟨J,?_⟩
  intro ηfirst η₀ Q hQM hQzero hQtop hQ72 hQη p Wradial
  let F := profileBound Wslot hcSlot.continuous aslot bslot lo hi haslot hsSlot
  have hF : 0 ≤ F := zero_le_one.trans
    (profileBound_ge_one Wslot hcSlot.continuous aslot bslot lo hi haslot hsSlot)
  obtain ⟨ηheight,CAnn,hηheight,hCAnn,hannular⟩ := actual_literal_first_annular_targets_fixed
    (α := α) M H hH Wslot aslot bslot a b lo hi F aslot (max 1 bslot) b b Bmask
    haslot hsSlot hcSlot hbslot.le ha hlo hhi le_rfl le_rfl hF haslot (le_max_left _ _) hBmask hbeta hbetaTop
    (fun _ => aslot) (fun _ => bslot) (fun _ => haslot) (fun _ => hbslot.le)
    ηfirst p η₀ Q hQM hQzero hQtop hQ72 hQη
  let ν := ηheight/2
  have hν : 0 < ν := half_pos hηheight
  have hgap : ν < ηheight := half_lt_self hηheight
  obtain ⟨C,hC,hnatural⟩ := hnatural ηfirst η₀ Q hQM hQzero hQtop hQ72 p Wradial ν ηheight CAnn hν hgap hCAnn.le
  refine ⟨ν,C,hν,hC,?_⟩
  filter_upwards [hnatural,hannular,
    LocalFirstNaturalSource.eventually_join_geometry (α := α) M H hH Wslot hcSlot.continuous
      aslot bslot lo hi a b haslot hbslot hsSlot ha hhi] with Z hnatural hannular hgeometry
  refine ⟨hnatural.1,?_⟩
  intro θ w σ freq t height hw hwmesh hσlo hσhi hheight hheightCap hfreq ht
    X₁ X₂ hX₁ hX₂ hn₁lo hn₂lo hn₁hi hn₂hi hsum hcapacity s hQ hη hrow hwidth hradial
  let src := LocalFirstNaturalSource.input M H hH η₀ θ Wslot hcSlot.continuous
    aslot bslot lo hi haslot hsSlot w σ freq (fun i => ⟨hσlo i,hσhi i⟩)
    s p ha t X₁ X₂ hX₁ hX₂
  have hwlocal : ∀ i,w i ≤ lowLocalMesh := fun i => (hwmesh i).trans (meshGuaranteed_le_lowLocalMesh Bmask ε)
  have hg := hgeometry.2 η₀ θ w σ freq (fun i => ⟨hσlo i,hσhi i⟩) Bmask bΦ s p
    t X₁ X₂ hX₁ hX₂ hw hwlocal hn₁lo hn₂lo hn₁hi hn₂hi hsum hcapacity
  have hp := LocalFirstNaturalSource.plain_join_gates M H hH η₀ θ Wslot hcSlot.continuous
    aslot bslot lo hi haslot hsSlot w σ freq (fun i => ⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂
  have hm := LocalFirstNaturalSource.input_matches M H hH η₀ θ Wslot hcSlot.continuous
    aslot bslot lo hi haslot hsSlot w σ freq (fun i => ⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂
  have hheightAnn : height ≤ Z^ηheight := hheightCap.trans
    (Real.rpow_le_rpow_of_exponent_le hnatural.1.le hgap.le)
  have hsourceAnn := hannular.2 θ w σ freq height hw hwlocal hσlo hσhi hheight hheightAnn hfreq
    src hm (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => rfl) (fun _ => rfl)
    le_rfl (le_max_right _ _)
    (fun _ => by change |bslot| ≤ max 1 bslot; rw [abs_of_pos hbslot]; exact le_max_right _ _)
    (by change |b| ≤ b; rw [abs_of_nonneg (zero_le_one.trans hhi)])
    (by change |b| ≤ b; rw [abs_of_nonneg (zero_le_one.trans hhi)])
    (zero_le_one.trans hhi) (zero_le_one.trans hhi) (le_max_right _ _) (le_max_right _ _)
    rfl rfl hη hg.source_positive hn₁hi hn₂hi hg.comparison_upper.1 hg.comparison_upper.2 hsum hcapacity
    hg.rectangle_lower.1 hg.rectangle_lower.2.1 hg.rectangle_lower.2.2.1 hg.rectangle_lower.2.2.2
    s.puncture s.puncture_ne_zero s.puncture_bound hp.1 hp.2.1
  apply hnatural.2 θ w σ freq t height hw hwmesh hσlo hσhi hheight hheightCap hfreq ht
    X₁ X₂ hX₁ hX₂ hn₁lo hn₂lo hn₁hi hn₂hi hsum hcapacity s hQ hη hrow hwidth hradial
  dsimp only [FirstNaturalAnnularTargets]
  intro labels hlabels ref href hclose hmin u hu left
  exact hsourceAnn labels ref href e he hecap hclose u hu left

#print axioms actual_local_natural_moment_explicit_mesh
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstNaturalMomentExplicitMesh -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstAnalyticalEstimate ; sha256 6dbc0cc0ff7da20b2be0448d3c91fe3e0deb019c966760d90aaf66574dac4703 -/
section



/-! The literal natural fourth moment on the affine local capacity region. Both
annular branches are supplied by the actual analytic proof; no moment,
population, bin, or source-target bound remains as a premise. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceInputTailUniform CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstPhysicalSource CenteredMomentLogDyadic
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentEnergyNaturalInputMatches CenteredMomentFirstAnnularMajorant
open CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
local instance analyticalEstimateSumDecEq : DecidableEq (α ⊕ Fin 2) := Classical.decEq _

variable (M : Ideal O) [NeZero M]
local instance analyticalEstimateFinite : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- The generalized local natural fourth moment with affine capacity and arbitrary
input heights. Profiles and the common fixed character family are fixed before
the height degree, constant and threshold; all masks and source rows remain live.
The proof has no improved-moment, bin-classification or source-target premise. -/
theorem actual_local_natural_moment_all_heights
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (Wslot : ℝ → ℂ) (aslot bslot lo hi a b bΦ Bmask ε : ℝ)
    (haslot : 0 < aslot) (hsSlot : Function.support Wslot ⊆ Set.Icc aslot bslot)
    (hcSlot : ContDiff ℝ ∞ Wslot) (hbslot : 0 < bslot)
    (ha : 0 < a) (hlo : a ≤ 1/4) (hhi : 1 ≤ b)
    (hbΦ : 0 < bΦ) (hBmask : 0 ≤ Bmask) (hε : 0 < ε)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) (hbetaTop : HeckeZeroSupremum.beta ≤ 7/8) :
    ∃ mesh : ℝ, 0 < mesh ∧ mesh ≤ lowLocalMesh ∧
    ∀ (ηfirst η₀ : Character) (Q : Ideal O), Q ≤ M →
      internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ → internalQ Q η₀ ≤ Ideal.span {(72:O)} →
      internalQ Q η₀ ≤ ηfirst.modulus →
    ∀ (p : Profiles a b) (Wradial : 𝓢(ℝ,ℂ)),
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (θ : α → RayQuotient.Characters M H) (w σ freq : α → ℝ) (t height : ℝ),
      (∀ i,0 ≤ w i) → (∀ i,w i ≤ mesh) →
    ∀ (hσlo : ∀ i,lo ≤ σ i) (hσhi : ∀ i,σ i ≤ hi),
      0 ≤ height → (∀ i,|freq i| ≤ height) →
    ∀ (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂),
      410/1000 ≤ Real.logb Z X₁ → 410/1000 ≤ Real.logb Z X₂ →
      Real.logb Z X₁ ≤ 423/1000 → Real.logb Z X₂ ≤ 423/1000 →
      (∑ i,w i) ≤ 37/1000 →
      localRegion (Real.logb Z X₁) (Real.logb Z X₂) (∑ i,w i) →
    ∀ s : NaturalState Z Bmask bΦ,
      s.fixedModulus = internalQ Q η₀ → s.character = ηfirst → s.rowWidth = 1 →
      s.characterWidth = Real.logb Z (ηfirst.modulus.absNorm : ℝ) → s.radial.profile = Wradial →
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i => CenteredMomentPrimeSlot.primePool M H bslot (Z^(w i)))
        (fun i I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i => Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
        C*(1+|t|+height)^J*Z^(1+ε) := by
  obtain ⟨mesh,hmesh,hmeshcap,J₀,hlocal⟩ := actual_local_natural_moment (α := α) M H hH
    Wslot aslot bslot lo hi a b bΦ Bmask ε haslot hsSlot hcSlot hbslot ha hlo hhi hbΦ hBmask hε
    hbeta hbetaTop
  refine ⟨mesh,hmesh,hmeshcap,?_⟩
  intro ηfirst η₀ Q hQM hQzero hQtop hQ72 hQη p Wradial
  obtain ⟨ν,C₁,hν,hC₁,hlocal⟩ := hlocal ηfirst η₀ Q hQM hQzero hQtop hQ72 hQη p Wradial
  obtain ⟨C₀,hC₀,hcoarse⟩ := LocalFirstNaturalSource.actual_natural_coarse_energy (α := α) M H hH
    Wslot hcSlot.continuous aslot bslot lo hi a b haslot hsSlot ha (zero_le_one.trans hhi) p Wradial
  obtain ⟨J,hheight⟩ := all_height_bound_of_local_and_coarse ν ε C₀ C₁ J₀ hν hC₀ hC₁.le
  refine ⟨J,C₀+C₁,by linarith only [hC₀,hC₁],?_⟩
  filter_upwards [hlocal] with Z hlocal
  refine ⟨hlocal.1,?_⟩
  intro θ w σ freq t height hw hwmesh hσlo hσhi hHgt hfreq
    X₁ X₂ hX₁ hX₂ hn₁lo hn₂lo hn₁hi hn₂hi hsum hcapacity s hQ hη hrow hwidth hradial
  apply hheight Z t height _ hlocal.1.le hHgt
  · exact hcoarse Z Bmask bΦ hlocal.1 s hrow hradial η₀ θ w σ freq
      (fun i => ⟨hσlo i,hσhi i⟩) t X₁ X₂ hX₁ hX₂ hn₁hi hn₂hi hsum
  · intro ht hheightCap
    exact hlocal.2 θ w σ freq t height hw hwmesh hσlo hσhi hHgt hheightCap hfreq ht
      X₁ X₂ hX₁ hX₂ hn₁lo hn₂lo hn₁hi hn₂hi hsum hcapacity s hQ hη hrow hwidth hradial

#print axioms actual_local_natural_moment_all_heights
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstAnalyticalEstimate -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstAnalyticalEstimateExplicitMesh ; sha256 95c67525c81ba00e314fe9e039261c44299a8e85a8e33de95f04dfe0841123b4 -/
section



/-! The literal natural fourth moment on the affine local capacity region. Both
annular branches are supplied by the actual analytic proof; no moment,
population, bin, or source-target bound remains as a premise. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceInputTailUniform CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstPhysicalSource CenteredMomentLogDyadic
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentEnergyNaturalInputMatches CenteredMomentFirstAnnularMajorant
open CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
local instance analyticalEstimateExplicitSumDecEq : DecidableEq (α ⊕ Fin 2) := Classical.decEq _

variable (M : Ideal O) [NeZero M]
local instance analyticalEstimateExplicitFinite : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- The generalized local natural fourth moment with affine capacity and arbitrary
input heights. Profiles and the common fixed character family are fixed before
the height degree, constant and threshold; all masks and source rows remain live.
The proof has no improved-moment, bin-classification or source-target premise. -/
theorem actual_local_natural_moment_all_heights_explicit_mesh
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (Wslot : ℝ → ℂ) (aslot bslot lo hi a b bΦ Bmask ε : ℝ)
    (haslot : 0 < aslot) (hsSlot : Function.support Wslot ⊆ Set.Icc aslot bslot)
    (hcSlot : ContDiff ℝ ∞ Wslot) (hbslot : 0 < bslot)
    (ha : 0 < a) (hlo : a ≤ 1/4) (hhi : 1 ≤ b)
    (hbΦ : 0 < bΦ) (hBmask : 0 ≤ Bmask) (hε : 0 < ε)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) (hbetaTop : HeckeZeroSupremum.beta ≤ 7/8) :
    ∀ (ηfirst η₀ : Character) (Q : Ideal O), Q ≤ M →
      internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ → internalQ Q η₀ ≤ Ideal.span {(72:O)} →
      internalQ Q η₀ ≤ ηfirst.modulus →
    ∀ (p : Profiles a b) (Wradial : 𝓢(ℝ,ℂ)),
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (θ : α → RayQuotient.Characters M H) (w σ freq : α → ℝ) (t height : ℝ),
      (∀ i,0 ≤ w i) → (∀ i,w i ≤ meshGuaranteed Bmask ε) →
    ∀ (hσlo : ∀ i,lo ≤ σ i) (hσhi : ∀ i,σ i ≤ hi),
      0 ≤ height → (∀ i,|freq i| ≤ height) →
    ∀ (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂),
      410/1000 ≤ Real.logb Z X₁ → 410/1000 ≤ Real.logb Z X₂ →
      Real.logb Z X₁ ≤ 423/1000 → Real.logb Z X₂ ≤ 423/1000 →
      (∑ i,w i) ≤ 37/1000 →
      localRegion (Real.logb Z X₁) (Real.logb Z X₂) (∑ i,w i) →
    ∀ s : NaturalState Z Bmask bΦ,
      s.fixedModulus = internalQ Q η₀ → s.character = ηfirst → s.rowWidth = 1 →
      s.characterWidth = Real.logb Z (ηfirst.modulus.absNorm : ℝ) → s.radial.profile = Wradial →
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i => CenteredMomentPrimeSlot.primePool M H bslot (Z^(w i)))
        (fun i I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i => Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
        C*(1+|t|+height)^J*Z^(1+ε) := by
  obtain ⟨J₀,hlocal⟩ := actual_local_natural_moment_explicit_mesh (α := α) M H hH
    Wslot aslot bslot lo hi a b bΦ Bmask ε haslot hsSlot hcSlot hbslot ha hlo hhi hbΦ hBmask hε
    hbeta hbetaTop
  intro ηfirst η₀ Q hQM hQzero hQtop hQ72 hQη p Wradial
  obtain ⟨ν,C₁,hν,hC₁,hlocal⟩ := hlocal ηfirst η₀ Q hQM hQzero hQtop hQ72 hQη p Wradial
  obtain ⟨C₀,hC₀,hcoarse⟩ := LocalFirstNaturalSource.actual_natural_coarse_energy (α := α) M H hH
    Wslot hcSlot.continuous aslot bslot lo hi a b haslot hsSlot ha (zero_le_one.trans hhi) p Wradial
  obtain ⟨J,hheight⟩ := all_height_bound_of_local_and_coarse ν ε C₀ C₁ J₀ hν hC₀ hC₁.le
  refine ⟨J,C₀+C₁,by linarith only [hC₀,hC₁],?_⟩
  filter_upwards [hlocal] with Z hlocal
  refine ⟨hlocal.1,?_⟩
  intro θ w σ freq t height hw hwmesh hσlo hσhi hHgt hfreq
    X₁ X₂ hX₁ hX₂ hn₁lo hn₂lo hn₁hi hn₂hi hsum hcapacity s hQ hη hrow hwidth hradial
  apply hheight Z t height _ hlocal.1.le hHgt
  · exact hcoarse Z Bmask bΦ hlocal.1 s hrow hradial η₀ θ w σ freq
      (fun i => ⟨hσlo i,hσhi i⟩) t X₁ X₂ hX₁ hX₂ hn₁hi hn₂hi hsum
  · intro ht hheightCap
    exact hlocal.2 θ w σ freq t height hw hwmesh hσlo hσhi hHgt hheightCap hfreq ht
      X₁ X₂ hX₁ hX₂ hn₁lo hn₂lo hn₁hi hn₂hi hsum hcapacity s hQ hη hrow hwidth hradial

/-- The mesh is explicitly chosen before the finite slot type. The polynomial
height degree, constant and scale threshold may depend on the slot family. -/
theorem actual_local_natural_moment_all_heights_uniform_mesh
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (Wslot : ℝ → ℂ) (aslot bslot lo hi a b bΦ Bmask ε : ℝ)
    (haslot : 0 < aslot) (hsSlot : Function.support Wslot ⊆ Set.Icc aslot bslot)
    (hcSlot : ContDiff ℝ ∞ Wslot) (hbslot : 0 < bslot)
    (ha : 0 < a) (hlo : a ≤ 1/4) (hhi : 1 ≤ b)
    (hbΦ : 0 < bΦ) (hBmask : 0 ≤ Bmask) (hε : 0 < ε)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) (hbetaTop : HeckeZeroSupremum.beta ≤ 7/8) :
    ∃ mesh : ℝ, mesh = meshGuaranteed Bmask ε ∧ 0 < mesh ∧ mesh ≤ lowLocalMesh ∧
    ∀ (α : Type*) [Fintype α] [DecidableEq α] [Nonempty α],
    ∀ (ηfirst η₀ : Character) (Q : Ideal O), Q ≤ M →
      internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ → internalQ Q η₀ ≤ Ideal.span {(72:O)} →
      internalQ Q η₀ ≤ ηfirst.modulus →
    ∀ (p : Profiles a b) (Wradial : 𝓢(ℝ,ℂ)),
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (θ : α → RayQuotient.Characters M H) (w σ freq : α → ℝ) (t height : ℝ),
      (∀ i,0 ≤ w i) → (∀ i,w i ≤ mesh) →
    ∀ (hσlo : ∀ i,lo ≤ σ i) (hσhi : ∀ i,σ i ≤ hi),
      0 ≤ height → (∀ i,|freq i| ≤ height) →
    ∀ (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂),
      410/1000 ≤ Real.logb Z X₁ → 410/1000 ≤ Real.logb Z X₂ →
      Real.logb Z X₁ ≤ 423/1000 → Real.logb Z X₂ ≤ 423/1000 →
      (∑ i,w i) ≤ 37/1000 →
      localRegion (Real.logb Z X₁) (Real.logb Z X₂) (∑ i,w i) →
    ∀ s : NaturalState Z Bmask bΦ,
      s.fixedModulus = internalQ Q η₀ → s.character = ηfirst → s.rowWidth = 1 →
      s.characterWidth = Real.logb Z (ηfirst.modulus.absNorm : ℝ) → s.radial.profile = Wradial →
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i => CenteredMomentPrimeSlot.primePool M H bslot (Z^(w i)))
        (fun i I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i => Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
        C*(1+|t|+height)^J*Z^(1+ε) := by
  refine ⟨meshGuaranteed Bmask ε,rfl,meshGuaranteed_pos Bmask ε hBmask hε,
    meshGuaranteed_le_lowLocalMesh Bmask ε,?_⟩
  intro α _ _ _
  exact actual_local_natural_moment_all_heights_explicit_mesh (α := α) M H hH
    Wslot aslot bslot lo hi a b bΦ Bmask ε haslot hsSlot hcSlot hbslot ha hlo hhi hbΦ hBmask hε
    hbeta hbetaTop

#print axioms actual_local_natural_moment_all_heights_uniform_mesh

#print axioms actual_local_natural_moment_all_heights_explicit_mesh
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstAnalyticalEstimateExplicitMesh -/

/- BEGIN ORIGINAL MODULE Analytic.JointIndependentHeights ; sha256 ba6b5d9771376c682368b646850212496b760604e36fe42c09abfdf60f2cc18b -/
section





/-! Independent plain heights from the actual equal-profile moments. The
analytic conclusion uses both diagonal capacities; it does not claim the
larger averaged-capacity region of the fixed-profile theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentOriginalCommonHarmonic
open CenteredMomentHeckeHeight CenteredMomentHeckeSlots CenteredMomentHeckeExpansion
open CenteredMomentRetainedEnergy CenteredMomentWholeSlotDeletion
open CenteredMomentSlotNormalization CenteredMomentPositiveSummability ConcreteTraceCRT
local notation "O" => HeckeFamily.O

/-- One fixed profile used on both plain legs. -/
def diagonalProfiles {a b : ℝ} (p : Profiles a b) (j : Fin 2) : Profiles a b where
  profile := fun _ => p.profile j
  support := fun _ => p.support j

/-- Two independent plain heights, with the slot frequency held fixed. -/
def independentPlainRow {α : Type*} [Fintype α]
    (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (S : α → Finset (Ideal O)) (β : α → Ideal O → ℂ) (P : α → ℝ)
    (t₁ t₂ X₁ X₂ : ℝ) : ℂ :=
  ((Real.sqrt X₁ : ℂ)⁻¹ * rowTwistedSum η m A z W₁ t₁ X₁) *
  ((Real.sqrt X₂ : ℂ)⁻¹ * rowTwistedSum η m A z W₂ t₂ X₂) *
    ∏ i, normalizedSlot η m A z (S i) (β i) 0 (P i)

def independentPlainEnergy {α : Type*} [Fintype α]
    (η : Character) (m A : O) (W₁ W₂ : ℝ → ℂ)
    (S : α → Finset (Ideal O)) (β : α → Ideal O → ℂ) (P : α → ℝ)
    (t₁ t₂ X₁ X₂ : ℝ) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  ∑' z : O, if keep z then
    ‖independentPlainRow η m A z W₁ W₂ S β P t₁ t₂ X₁ X₂‖^2 *
      (Φ (‖eisEmbedding z‖^2/K)).re else 0

lemma annular_slot_height_shift (η : Character) (m A z : O)
    (S : Finset (Ideal O)) (hS : ∀ I ∈ S, I ≠ 0)
    (c : Ideal O → ℂ) (W : ℝ → ℂ) (P σ freq t : ℝ) (hP : 0 < P) :
    normalizedSlot η m A z S
      (fun I => c I * HeckePrimeAnnular.annularWeight W P σ (freq-t) I) t P =
    (P : ℂ)^(Complex.I*t) * normalizedSlot η m A z S
      (fun I => c I * HeckePrimeAnnular.annularWeight W P σ freq I) 0 P := by
  unfold normalizedSlot
  rw [rowSlot_eq_weight,rowSlot_eq_weight,mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  have hN : 0 < (I.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hS I hI))
  have hh := CenteredMomentPrimeSlotShift.norm_height_split (I.absNorm : ℝ) P σ t (freq-t) hN hP
  rw [show t+(freq-t)=freq by ring] at hh
  simp only [Complex.ofReal_natCast] at hh
  simp only [HeckePrimeAnnular.annularWeight,rowWeight,MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one]
  calc
    _ = (c I * W ((I.absNorm : ℝ)/P) *
      (idealCoeff η I * CanonicalRowCompletion.idealRowHom (m^6*(A*z)) I)) *
      ((((I.absNorm : ℝ)/P : ℝ) : ℂ)^(-HeckeDyadic.shift σ (freq-t)) *
        (I.absNorm : ℂ)^(Complex.I*t)) := by ring
    _ = _ := by rw [hh]; ring

lemma annular_slot_height_shift_norm (η : Character) (m A z : O)
    (S : Finset (Ideal O)) (hS : ∀ I ∈ S, I ≠ 0)
    (c : Ideal O → ℂ) (W : ℝ → ℂ) (P σ freq t : ℝ) (hP : 0 < P) :
    ‖normalizedSlot η m A z S
      (fun I => c I * HeckePrimeAnnular.annularWeight W P σ (freq-t) I) t P‖ =
    ‖normalizedSlot η m A z S
      (fun I => c I * HeckePrimeAnnular.annularWeight W P σ freq I) 0 P‖ := by
  rw [annular_slot_height_shift η m A z S hS c W P σ freq t hP,norm_mul,
    CenteredMomentTwist.norm_real_imaginary_power P t hP,one_mul]

lemma independent_row_le_diagonal_rows {α : Type*} [Fintype α] [DecidableEq α]
    (η : Character) (m A z : O) (W₁ W₂ Wslot : ℝ → ℂ)
    (S : α → Finset (Ideal O)) (hS : ∀ i I, I ∈ S i → I ≠ 0)
    (c : α → Ideal O → ℂ) (P σ freq : α → ℝ) (hP : ∀ i, 0 < P i)
    (t₁ t₂ X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    ‖independentPlainRow η m A z W₁ W₂ S
      (fun i I => c i I * HeckePrimeAnnular.annularWeight Wslot (P i) (σ i) (freq i) I)
      P t₁ t₂ X₁ X₂‖^2 ≤
    ‖positiveSlotRow η m A z W₁ W₁ S
      (fun i I => c i I * HeckePrimeAnnular.annularWeight Wslot (P i) (σ i) (freq i-t₁) I)
      P t₁ X₁ X₁‖^2 +
    ‖positiveSlotRow η m A z W₂ W₂ S
      (fun i I => c i I * HeckePrimeAnnular.annularWeight Wslot (P i) (σ i) (freq i-t₂) I)
      P t₂ X₂ X₂‖^2 := by
  rw [← selectedProduct_univ _ _ _ _ _ _ _ _ _ _ _ _ (mul_pos hX₁ hX₁).le (fun i => (hP i).le),
    ← selectedProduct_univ _ _ _ _ _ _ _ _ _ _ _ _ (mul_pos hX₂ hX₂).le (fun i => (hP i).le)]
  simp only [independentPlainRow,selectedProduct,norm_mul,norm_prod]
  simp_rw [annular_slot_height_shift_norm η m A z _ (hS _) _ _ _ _ _ _ (hP _)]
  rw [Real.sqrt_mul hX₁.le,Real.sqrt_mul hX₂.le,
    Complex.ofReal_mul,Complex.ofReal_mul,mul_inv_rev,mul_inv_rev,norm_mul,norm_mul]
  nlinarith [sq_nonneg
    ((‖(Real.sqrt X₁ : ℂ)⁻¹‖*‖rowTwistedSum η m A z W₁ t₁ X₁‖)^2-
     (‖(Real.sqrt X₂ : ℂ)⁻¹‖*‖rowTwistedSum η m A z W₂ t₂ X₂‖)^2),
    sq_nonneg (∏ i, ‖normalizedSlot η m A z (S i)
      (fun I => c i I * HeckePrimeAnnular.annularWeight Wslot (P i) (σ i) (freq i) I) 0 (P i)‖)]

lemma independent_energy_le_diagonal_energies {α : Type*} [Fintype α] [DecidableEq α]
    (η : Character) (m A : O) (W₁ W₂ Wslot : ℝ → ℂ) (b₁ b₂ : ℝ)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (S : α → Finset (Ideal O)) (hS : ∀ i I, I ∈ S i → I ≠ 0)
    (c : α → Ideal O → ℂ) (P σ freq : α → ℝ) (hP : ∀ i, 0 < P i)
    (t₁ t₂ X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0 < K)
    (hΦ : ∀ x, 0 ≤ (Φ x).re) :
    independentPlainEnergy η m A W₁ W₂ S
      (fun i I => c i I * HeckePrimeAnnular.annularWeight Wslot (P i) (σ i) (freq i) I)
      P t₁ t₂ X₁ X₂ keep Φ K ≤
    energy η m A t₁ W₁ W₁ S
      (fun i I => c i I * HeckePrimeAnnular.annularWeight Wslot (P i) (σ i) (freq i-t₁) I)
      P X₁ X₁ keep Φ K +
    energy η m A t₂ W₂ W₂ S
      (fun i I => c i I * HeckePrimeAnnular.annularWeight Wslot (P i) (σ i) (freq i-t₂) I)
      P X₂ X₂ keep Φ K := by
  let f (W : ℝ → ℂ) (t X : ℝ) (z : O) : ℝ := if keep z then
    ‖positiveSlotRow η m A z W W S
      (fun i I => c i I * HeckePrimeAnnular.annularWeight Wslot (P i) (σ i) (freq i-t) I)
      P t X X‖^2 * (Φ (‖eisEmbedding z‖^2/K)).re else 0
  have hf (W : ℝ → ℂ) (b t X : ℝ) (hs : Function.support W ⊆ Set.Iic b) (hX : 0 < X) :
      Summable (f W t X) := by
    obtain ⟨B,hB⟩ := product_bounded η m A t (Real.sqrt (X*X*∏ i,P i) : ℂ)⁻¹
      W W b b X X hs hs hX hX S
      (fun i I => c i I * HeckePrimeAnnular.annularWeight Wslot (P i) (σ i) (freq i-t) I)
    exact bounded_radial_summable _ B hB keep Φ K hK
  have hf₁ := hf W₁ b₁ t₁ X₁ hs₁ hX₁
  have hf₂ := hf W₂ b₂ t₂ X₂ hs₂ hX₂
  let g (z : O) : ℝ := if keep z then
    ‖independentPlainRow η m A z W₁ W₂ S
      (fun i I => c i I * HeckePrimeAnnular.annularWeight Wslot (P i) (σ i) (freq i) I)
      P t₁ t₂ X₁ X₂‖^2 * (Φ (‖eisEmbedding z‖^2/K)).re else 0
  have hg₀ : ∀ z, 0 ≤ g z := by
    intro z
    dsimp [g]
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (hΦ _)
    · exact le_rfl
  have hg : ∀ z, g z ≤ f W₁ t₁ X₁ z+f W₂ t₂ X₂ z := by
    intro z
    dsimp [g,f]
    split_ifs
    · rw [←add_mul]
      exact mul_le_mul_of_nonneg_right
        (independent_row_le_diagonal_rows η m A z W₁ W₂ Wslot S hS c P σ freq hP
          t₁ t₂ X₁ X₂ hX₁ hX₂) (hΦ _)
    · simp
  have hgs : Summable g := Summable.of_nonneg_of_le hg₀ hg (hf₁.add hf₂)
  exact (hgs.tsum_le_tsum hg (hf₁.add hf₂)).trans_eq (Summable.tsum_add hf₁ hf₂)

#print axioms independent_energy_le_diagonal_energies
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointIndependentHeights -/
