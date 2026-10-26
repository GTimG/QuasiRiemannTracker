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
import Submissions.certb_local_20261013.Bundles.B088
import Submissions.certb_local_20261013.Bundles.B110
import Submissions.certb_local_20261013.Bundles.B111
import Submissions.certb_local_20261013.Bundles.B112
import Submissions.certb_local_20261013.Bundles.B113
import Submissions.certb_local_20261013.Bundles.B114
import Submissions.certb_local_20261013.Bundles.B115
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.NaturalInputMatches

/- BEGIN ORIGINAL MODULE Analytic.JointFirstLiteralAmplification ; sha256 b707235a032a76fb996c989ef5f9a033603ed453184912fef98a1706ed246ac7 -/
section


/-! The first annular amplifier specialized to the original physical
radius, retained dyadic row scale and actual prime family. The chosen
error characters precede every live source, label and height. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT RayFourExpansion
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentPrimePool CenteredMomentPrimeElements
open CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationGlobal CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSectorLocalization CenteredMomentSecondHeightFamily CenteredMomentChildRows
open CenteredMomentCommonAllocationSum CenteredMomentFirstScale
open CenteredMomentAmplificationActiveFactor CenteredMomentCommonProfile
open CenteredMomentCanonicalFirst CenteredMomentFirstNonexceptionalWeightSum ActualEisensteinCubic
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentLogDyadic
open ConcretePrimeRowBridge CenteredMomentExceptionalAmplitudePair
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma first_actual_nominal_puncture (src : Input ι) (R seed : Ideal O)
    (K : ℝ) (radius : (p : Labels src R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ)
    (i : FirstSourceOuterIndex src R seed K radius) (X : ℝ) :
    firstNominalScale i.1.val.1 i.1.val.2 (∏ P ∈ i.2.1.val,P.val) K X =
      firstNominalScale (firstSourceOuterLabel src R seed K radius i).C
        (firstSourceOuterLabel src R seed K radius i).D
        (Ideal.span {(firstSourceOuterLabel src R seed K radius i).puncture}) K X := by
  simp only [FirstJointLabel.puncture,firstSourceOuterLabel,primeSubsetGenerator,span_idealGenerator]

/-- No admissibility or target-energy premise is supplied by the caller:
the source support factor and retained first dyad give the amplifier gates. -/
theorem actual_first_literal_annular_amplification
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes ⊆ Sbad)
    (N : ℕ) (a b loss BR upper b₁ b₂ ξ reserve : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hloss : 0 < loss)
    (hξ : 0 < ξ) (hreserve : 0 < reserve) (hbudget : ξ+reserve ≤ lowLocalTiny) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^((9/500 : ℝ)/3))
      P.Nonempty ∧ Z^((3/500 : ℝ)-loss) ≤ actualHighPrimeCount M H Sbad Z ∧
      ∃ τ : (J : Finset ι) → Character → elementPool P → Fin 3 → RayCharacter → Character,
        (∀ J η (p : elementPool P) i χ, ((τ J η p i χ).modulus.absNorm : ℝ) ≤
          radicalBound (childCharacter η χ) fixedBadMask p.val (errorMovingExponent (errorIndex i))) ∧
      ∀ (src : Input ι) (R seed : Ideal O), Squarefree seed → R ≠ 0 →
        src.W₁ 0 = 0 → src.W₂ 0 = 0 → 0 ≤ sourceRadius src → sourceRadius src ≤ Z^(1:ℝ) →
        (R.absNorm : ℝ) ≤ Z^BR →
        Fintype.card ι ≤ N → a ≤ src.lower → src.upper ≤ b →
        (∀ i,|src.hi i| ≤ upper) → |src.b₁| ≤ b₁ → |src.b₂| ≤ b₂ →
      ∀ (w : ι → ℝ), (∀ i,w i ≤ lowLocalMesh) → (∀ i,src.P i = Z^(w i)) →
      let radius := actualLowFirstRadius src R seed Z Z ξ
      let q := firstSourceOuterLabel src R seed Z radius
      ∀ (labels : Finset (FirstSourceOuterIndex src R seed Z radius)) (left : Bool),
      let domain := firstSideSourceLabels labels q (fun _ => sourceRadius src) left
      let delta := frequencyLoss Z (32*(lowLiteralSupportConstant (Fintype.card ι) upper b₁ b₂)^2) ξ
      let omega := lowLiteralOmega (Fintype.card ι) upper b₁ b₂ ξ reserve Z
      ∀ t : ((i : FirstSourceOuterIndex src R seed Z radius) × (q i).SourceIndex) → ℝ,
      (∑ k ∈ firstSourceLabels labels q,
        ((q k.1).sourceChild k.2).sideEnergy left (t k)
          CenteredMomentFirstAnnularMajorant.profile (dyadicScale (k.1.2.2 1))/volume src.toData) ≤
        (56*((4+2*(9/500 : ℝ))/((9/500 : ℝ)/6)))*
          (∑ k ∈ domain,
            ((q k.1).sourceChild k.2).sideEnergy left (t k) ballProfile
              (firstLowMainScale (q k.1) left Z (Real.logb Z (volume src.toData)) 1 omega)/
                (volume src.toData*actualHighPrimeCount M H Sbad Z)) +
        ∑ k ∈ domain, allocatedExtractedErrors N src ((q k.1).sideCommon left) R k.2.1.val
          (((q k.1).sourceChild k.2).sideParent left) (t k) b Z ((q k.1).sideWidth (!left) Z)
          (nominalLog ((q k.1).sideCommon left) ((q k.1).sideCommon (!left))
            (Ideal.span {(q k.1).puncture}) Z (volume src.toData) Z)
          ((q k.1).sideWidth left Z) (9/500) delta reserve P
          (fun B => τ (liveIndices B.val) (((q k.1).sourceChild k.2).sideParent left)) := by
  let Cs := lowLiteralSupportConstant (Fintype.card ι) upper b₁ b₂
  have hCs : 1 ≤ Cs := by
    dsimp only [Cs,lowLiteralSupportConstant]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _)
  have hCsec : 1 ≤ Cs^2 := one_le_pow₀ hCs
  have hmesh : lowLocalMesh < (9/500 : ℝ)/6 := by
    have hh : lowLocalMesh ≤ lowLocalTiny/4 := min_le_right _ _
    norm_num [lowLocalTiny] at hh ⊢
    linarith only [hh]
  have hamp := actual_first_coherent_annular_amplification (ι := ι) M H hH Sbad hbad N
    a b (9/500) loss BR 1 4 lowLocalMesh (Cs^2) ξ reserve
    ha hb (by norm_num) hloss (by norm_num) hmesh hCsec hξ.le hreserve
  filter_upwards [hamp,eventually_ge_atTop (32:ℝ)] with Z hamp hZ32
  obtain ⟨hZ,hP,hcard,τ,hτ,hamp⟩ := hamp
  refine ⟨hZ,hP,?_,τ,hτ,?_⟩
  · simpa only [actualHighPrimeCount,show (9/500 : ℝ)/3=3/500 by norm_num] using hcard
  intro src R seed hs hR hz₁ hz₂ hsource₀ hsource hRcap hN hlo hhi hhiAbs hb₁ hb₂
    w hw hscale radius q labels left domain delta omega t
  have hz := zero_lt_one.trans hZ
  have hξcap : ξ ≤ 1 := by norm_num [lowLocalTiny] at hbudget; linarith only [hbudget,hreserve]
  have hsupport : sourceRadius src ≤ Cs*volume src.toData :=
    sourceRadius_le_fixed_volume src upper b₁ b₂ hhiAbs hb₁ hb₂
  let Tsec := fun k : (i : FirstSourceOuterIndex src R seed Z radius) × (q i).SourceIndex =>
    firstNominalScale (q k.1).C (q k.1).D (Ideal.span {(q k.1).puncture}) Z (sourceRadius src)
  let H₀ := fun k : (i : FirstSourceOuterIndex src R seed Z radius) × (q i).SourceIndex =>
    dyadicScale (k.1.2.2 1)
  have hnom (k) (_hk : k ∈ domain) : Tsec k ≤ Cs^2*
      firstNominalScale ((q k.1).sideCommon left) ((q k.1).sideCommon (!left))
        (Ideal.span {(q k.1).puncture}) Z (volume src.toData) :=
    (q k.1).side_nominal_source_factor left Z (sourceRadius src) (volume src.toData) Cs hz hsource₀ hsupport
  have hdyad (k) (_hk : k ∈ domain) :
      0 < H₀ k ∧ H₀ k ≤ 4*frequencyRadius (Tsec k) Z ξ ∧ 8*H₀ k ≤ Z^(4:ℝ) := by
    have hh := actual_first_annular_amplifier_scale src R seed Z Z ξ hZ.le hZ32 hξcap hsource₀ hsource k.1
    have heq : radius k.1.1 k.1.2.1.val = frequencyRadius (Tsec k) Z ξ := by
      dsimp only [radius,actualLowFirstRadius,Tsec]
      rw [first_actual_nominal_puncture src R seed Z radius k.1 (sourceRadius src)]
    change 0 < H₀ k ∧ H₀ k ≤ 4*radius k.1.1 k.1.2.1.val ∧ 8*H₀ k ≤ Z^(4:ℝ) at hh
    simpa only [heq,actual_amplifier_prime_card] using hh
  have hh := hamp src R seed hs hR hz₁ hz₂ hsource hRcap hN hlo hhi w hw hscale Z hz radius
    labels left t Tsec H₀ hnom hdyad
  have heq (k : (i : FirstSourceOuterIndex src R seed Z radius) × (q i).SourceIndex) :
      (q k.1).sideMainRadius left Z Z (volume src.toData) (9/500) delta reserve =
        firstLowMainScale (q k.1) left Z (Real.logb Z (volume src.toData)) 1 omega :=
    (q k.1).sideMainRadius_literal left src Z upper b₁ b₂ ξ reserve hZ
  have hvolume : CenteredMomentAmplificationChildInput.volume src = volume src.toData := rfl
  dsimp only [q,delta,omega,Cs] at heq
  simpa only [hvolume,Cs,heq,actual_amplifier_prime_card] using hh

#print axioms actual_first_literal_annular_amplification
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstLiteralAmplification -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstOriginalTarget ; sha256 15a0fdd8f0d5c19b2b653414b35e90d8d795127665910de3a44b8a80a77525bc -/
section




set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentInductionEnergy CenteredMomentEnergyReferenceState
open CenteredMomentCommonRadialData CenteredMomentSourceRow CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceInputTailUniform CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstPhysicalSource CenteredMomentLogDyadic CenteredMomentSourceMass CenteredMomentSourceProfileMass
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance firstOriginalTargetAlphaDecEq : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance firstOriginalTargetFinite : Finite (O⧸M):=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

lemma local_first_comparison_scales (Z X₁ X₂:ℝ)(hZ:1< Z)(hX₁:0< X₁)(hX₂:0< X₂)
    (hlo₁:410/1000≤ Real.logb Z X₁)(hlo₂:410/1000≤ Real.logb Z X₂)
    (hhi₁:Real.logb Z X₁≤423/1000)(hhi₂:Real.logb Z X₂≤423/1000):
    1≤ comparisonFirst Z 1 ∧ 1≤ comparisonSecond Z 1 X₁ X₂ ∧
      comparisonFirst Z 1≤ Z^(1/4:ℝ) ∧ comparisonSecond Z 1 X₁ X₂≤ Z^(3/5:ℝ):=by
  have hlog:Real.logb Z (X₁*X₂)=Real.logb Z X₁+Real.logb Z X₂:=
    Real.logb_mul hX₁.ne' hX₂.ne'
  refine ⟨Real.one_le_rpow hZ.le (by norm_num),?_,le_rfl,?_⟩
  · rw [comparison_second_power Z 1 X₁ X₂ hZ hX₁ hX₂,hlog]
    exact Real.one_le_rpow hZ.le (by linarith)
  · rw [comparison_second_power Z 1 X₁ X₂ hZ hX₁ hX₂,hlog]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)

/-- The complete original first-transform remainder in the new local window.
Its only unestimated term is the literal retained physical-block sum. -/
theorem actual_local_first_original_target
    (Wslot:ℝ→ℂ)(aslot bslot lo hi a b bΦ Bmask upper bplain₁ bplain₂ ε ξ:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)
    (hcSlot:ContDiff ℝ ∞ Wslot)(hbslot:0≤ bslot)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hBmask:0≤ Bmask)
    (hupper:0≤ upper)(hε:0<ε)(hξ:0<ξ)
    (hbeta:51/100≤ HeckeZeroSupremum.beta)(hbetaTop:HeckeZeroSupremum.beta≤7/8):
    ∃mesh:ℝ,0< mesh ∧ ∃J:ℕ,∃U Sd St:Finset (ℕ×ℕ),∃Cd Ct:ℝ,0< Cd ∧ 0< Ct ∧
    ∀ηfirst η₀:Character,∀Q:Ideal O,Q≤ M → internalQ Q η₀≠0 → internalQ Q η₀≠⊤ →
      internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃Cc:ℝ,0< Cc ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
      ∀(src:Input α)(profile:Profiles a b),
      profile.profile 0=src.W₁ → profile.profile 1=src.W₂ →
      (∀i,|src.hi i|≤ upper) → |src.b₁|≤ bplain₁ → |src.b₂|≤ bplain₂ → src.upper≤ upper →
      0< sourceRadius src →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(height:ℝ),
      CenteredMomentAllocatedRayDictionary.Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
      (∀i,0≤ w i) → (∀i,w i≤ mesh) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) →
      410/1000≤ Real.logb Z src.X₁ → 410/1000≤ Real.logb Z src.X₂ →
      Real.logb Z src.X₁≤423/1000 → Real.logb Z src.X₂≤423/1000 → (∑i,w i)≤37/1000 →
      src.Y₁=comparisonFirst Z 1 → src.Y₂=comparisonSecond Z 1 src.X₁ src.X₂ →
      ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=internalQ Q η₀ →
        s.character=ηfirst → src.η=s.character → s.rowWidth=1 →
        s.characterWidth=Real.logb Z (ηfirst.modulus.absNorm:ℝ) →
      energy src.η s.mask 1 src.t src.W₁ src.W₂ src.slots src.toData.coefficient src.P
        src.X₁ src.X₂ s.radial.keep s.radial.profile s.radial.scale ≤
      (2/volume src.toData)*
        (∑i:FirstSourceOuterIndex src s.puncture 1 Z (actualLowFirstRadius src s.puncture 1 Z Z ξ),
          ‖firstPhysicalValue src s.puncture 1 Z (actualLowFirstRadius src s.puncture 1 Z Z ξ)
            (fun _=> src.t) s.radial.profile (fun _=> logAnnulus) i‖)+
      2*Cd*(plainControl src (profile.profile 0) (profile.profile 1))^2*
        Sd.sup (schwartzSeminormFamily ℝ ℝ ℂ) s.radial.profile*Z^(1+ε)+
      2*Ct*(plainControl src (profile.profile 0) (profile.profile 1))^2*
        St.sup (schwartzSeminormFamily ℝ ℝ ℂ) s.radial.profile*Z^(1+ε)+
      2*Cc*diagonalControl s.radial.profile*
        (sourceControl U (profile.profile 0)*sourceControl U (profile.profile 1))^2*
        (1+|src.t|+height)^J*Z^(1+ε):=by
  obtain ⟨mesh,hmesh,J,U,hcomp⟩:=actual_local_comparison_energy (α:=α) M H hH
    Wslot aslot bslot lo hi a b bΦ Bmask ε haslot hsSlot hcSlot hbslot
    ha hlo hhi hbΦ hBmask hε hbeta hbetaTop
  obtain ⟨Sd,St,Cd,Ct,hCd,hCt,hrem⟩:=actual_local_first_original_remainder
    (ι:=α) a b upper bplain₁ bplain₂ ε ξ ha (by linarith) hupper hε hξ
  refine ⟨mesh,hmesh,J,U,Sd,St,Cd,Ct,hCd,hCt,?_⟩
  intro ηfirst η₀ Q hQM hQzero hQtop hQ72
  obtain ⟨Cc,hCc,hcomp⟩:=hcomp ηfirst η₀ Q hQM hQzero hQtop hQ72
  refine ⟨Cc,hCc,?_⟩
  filter_upwards [hrem,hcomp] with Z hr hc
  refine ⟨hr.1,?_⟩
  intro src profile hp₁ hp₂ hslotHi hb₁ hb₂ hupperSrc hsource θ w σ freq height hmatch
    hw hwmesh hσlo hσhi hheight hfreq hn₁lo hn₂lo hn₁hi hn₂hi hslots hy₁ hy₂
    s hQ hη hsrcη hrow hwidth
  have hscale:s.radial.scale=Z:=by rw [s.scale_eq,hrow,Real.rpow_one]
  have hrem:=hr.2 src profile hp₁ hp₂ hslotHi hb₁ hb₂ hupperSrc hsource
    w hmatch.scale hn₁hi hn₂hi hslots s.puncture s.radial hscale
  have hg:=local_first_comparison_scales Z src.X₁ src.X₂ hr.1 src.X₁_pos src.X₂_pos
    hn₁lo hn₂lo hn₁hi hn₂hi
  have hcomp:=hc.2 θ w σ freq src.t height hw hwmesh hσlo hσhi hheight hfreq
    s hQ hη hrow hwidth (profile.profile 0) (profile.profile 1) (profile.support 0) (profile.support 1)
    src.Y₁ src.Y₂ (hy₁ ▸ hg.1) (hy₂ ▸ hg.2.1) (hy₁ ▸ hg.2.2.1) (hy₂ ▸ hg.2.2.2) hslots
  have hcoeff:src.toData.coefficient=(fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I):=by
    funext i I
    change src.ν i I*src.W i ((I.absNorm:ℝ)/src.P i)=_
    rw [hmatch.character,hmatch.profile,hmatch.scale]
    rfl
  have hcomp':energy src.η s.mask 1 src.t src.W₁ src.W₂ src.slots src.toData.coefficient src.P
      src.Y₁ src.Y₂ s.radial.keep s.radial.profile s.radial.scale ≤
      Cc*diagonalControl s.radial.profile*
        (sourceControl U (profile.profile 0)*sourceControl U (profile.profile 1))^2*
        (1+|src.t|+height)^J*Z^(1+ε):=by
    rw [hsrcη,←hp₁,←hp₂,funext hmatch.pool,funext hmatch.scale,hcoeff]
    exact hcomp
  apply hrem.trans
  have hh:=mul_le_mul_of_nonneg_left hcomp' (by norm_num:(0:ℝ)≤2)
  apply add_le_add_right
  convert hh using 1 <;> (try rfl) <;> ring

#print axioms actual_local_first_original_target
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstOriginalTarget -/

/- BEGIN ORIGINAL MODULE Analytic.JointHighCumulativeSectors ; sha256 be5500594e03bfcc0630022de96c3b0863872828b17e9412d11947bc2dcc8d7e -/
section



/-! The first reference tolerance and the actual second lower-edge cell
give the cumulative common norms and second scalar gates in one step. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve

namespace CommonSecondKernelLabel
variable {Slot : Type*} [Fintype Slot]

theorem first_second_sector_gates (s : CommonSecondKernelLabel Slot)
    (q ref : FirstJointLabel Slot) (side : Bool) (Z eFirst eSecond : ℝ)
    (hZ : 1 < Z) (heSecond : 0 ≤ eSecond)
    (hfirst : s.firstCommon = q.sideCommon side)
    (hclose : ∀ j,|q.fullWidthCoordinates Z j-ref.fullWidthCoordinates Z j| < eFirst)
    (edge : Fin 4 → ℝ) (hedge : ∀ j,0 ≤ edge j)
    (hsector : ∀ j,edge j ≤ s.secondWidthCoordinates Z j ∧
      s.secondWidthCoordinates Z j ≤ edge j+eSecond) :
    let c₂ := edge 0
    let d₂ := edge 1
    let b₂ := (c₂+d₂)/2
    let g₂ := min (edge 2) b₂
    let t₂ := edge 3
    0 ≤ c₂ ∧ 0 ≤ d₂ ∧ 0 ≤ b₂ ∧ 0 ≤ g₂ ∧ g₂ ≤ b₂ ∧ 0 ≤ t₂ ∧
      2*b₂ = c₂+d₂ ∧
      Z^(ref.sideWidth side Z+c₂-eFirst) ≤ ((s.firstCommon*s.second.val.1).absNorm : ℝ) ∧
      Z^(ref.sideWidth side Z+d₂-eFirst) ≤ ((s.firstCommon*s.second.val.2).absNorm : ℝ) ∧
      s.secondLogCost Z ≤ g₂-t₂-b₂+eSecond := by
  dsimp only
  have hs := s.second_sector_gates Z eSecond hZ heSecond edge hedge hsector
  dsimp only at hs
  have hc : ref.sideWidth side Z-eFirst ≤ q.sideWidth side Z := by
    have hh := (q.literal_target_gates_of_full ref side Z eFirst hclose).2.1
    linarith
  have hqpos : (0:ℝ) < (q.sideCommon side).absNorm := by
    cases side
    · exact CenteredMomentFirstScale.norm_pos _ q.hD.1
    · exact CenteredMomentFirstScale.norm_pos _ q.hC.1
  have hnorm : Z^(ref.sideWidth side Z-eFirst) ≤ (s.firstCommon.absNorm : ℝ) := by
    rw [hfirst]
    calc
      _ ≤ Z^(q.sideWidth side Z) := Real.rpow_le_rpow_of_exponent_le hZ.le hc
      _ = _ := Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hqpos
  have hcum := s.cumulative_common_norm_lower Z (ref.sideWidth side Z-eFirst)
    (edge 0) (edge 1) (zero_lt_one.trans hZ) hnorm hs.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2.1
  refine ⟨hs.1,hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,by ring,?_,?_,hs.2.2.2.2.2.2.2.2⟩
  · convert hcum.1 using 1 <;> congr 1 <;> ring
  · convert hcum.2 using 1 <;> congr 1 <;> ring

end CommonSecondKernelLabel
#print axioms CommonSecondKernelLabel.first_second_sector_gates
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighCumulativeSectors -/

/- BEGIN ORIGINAL MODULE Analytic.JointHighLocalParameters ; sha256 056a44d715c9fe6c4e31a6029e5d4eee512a7068ed6aa1a3360fadb6a97bd02e -/
section




/-! Fixed high-branch loss parameters and scalar envelopes. These gates
use the actual local source lengths and retain the cancellation budget;
no moment or zero-density estimate is assumed here. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair

/-- A fixed conductor scale absorbs the original puncture and all moving
row/common masks; it is chosen before the source and sector labels. -/
def highLocalDmax (BR : ℝ) : ℝ := BR+10

def highLocalEpsilon (BR : ℝ) (N : ℕ) : ℝ :=
  lowLocalTiny/(100*highLocalDmax BR*(N+1))

def highLocalProductLoss (BR : ℝ) (N : ℕ) : ℝ :=
  (2+2*(N:ℝ))*highLocalEpsilon BR N

/-- One bin mesh can be used by the low bound, the high products and the
single global zero-bin classifier. -/
def highLocalBinCap (BR : ℝ) (N : ℕ) : ℝ :=
  min (lowLocalBinCap N) (min (highLocalEpsilon BR N/192) (1/2000))

theorem high_local_product_parameters (BR : ℝ) (N : ℕ) (hBR : 0 ≤ BR) :
    1 ≤ highLocalDmax BR ∧ 0 < highLocalEpsilon BR N ∧
    0 < highLocalBinCap BR N ∧
    ∀ e : ℝ,0 < e → e ≤ highLocalBinCap BR N →
      e ≤ lowLocalBinCap N ∧ e < 1/1000 ∧
      0 < highLocalEpsilon BR N/32 ∧ highLocalEpsilon BR N/32 ≤ 1 ∧
      0 < highLocalEpsilon BR N/16 ∧
      12*e*((2:ℝ)+2)+8*(highLocalEpsilon BR N/32)+2*(highLocalEpsilon BR N/16) ≤ highLocalEpsilon BR N ∧
      8*e*2+highLocalEpsilon BR N/32 ≤ highLocalEpsilon BR N ∧
      (2+2*(N:ℝ))*highLocalEpsilon BR N ≤ highLocalProductLoss BR N ∧
      lowLocalTiny/2+highLocalDmax BR*highLocalProductLoss BR N ≤ lowLocalTiny := by
  have ht : 0 < lowLocalTiny := by norm_num [lowLocalTiny]
  have hd : 10 ≤ highLocalDmax BR := by dsimp only [highLocalDmax]; linarith
  have hn : (0:ℝ) < N+1 := by positivity
  have hden : 0 < 100*highLocalDmax BR*(N+1) := by positivity
  have hε : 0 < highLocalEpsilon BR N := div_pos ht hden
  have hεcap : highLocalEpsilon BR N ≤ lowLocalTiny := by
    apply (div_le_iff₀ hden).mpr
    have hh : 1 ≤ 100*highLocalDmax BR*(N+1) := by nlinarith [show (0:ℝ) ≤ (N:ℝ) from Nat.cast_nonneg N]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hh ht.le
  have hlow := (low_local_parameter_choices N).2.2.2.2.1
  have hbin : 0 < highLocalBinCap BR N := lt_min hlow (lt_min (by positivity) (by norm_num))
  refine ⟨by linarith,hε,hbin,?_⟩
  intro e he hecap
  have helow := hecap.trans (min_le_left _ _)
  have heε := hecap.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hesmall := hecap.trans ((min_le_right _ _).trans (min_le_right _ _))
  change e ≤ highLocalEpsilon BR N/192 at heε
  change e ≤ (1/2000:ℝ) at hesmall
  have hid : highLocalDmax BR*highLocalProductLoss BR N = lowLocalTiny/50 := by
    unfold highLocalProductLoss highLocalEpsilon
    field_simp [ne_of_gt hn,ne_of_gt (by linarith : 0 < highLocalDmax BR)]
    <;> ring
  refine ⟨helow,by linarith,by positivity,?_,by positivity,?_,?_,le_rfl,?_⟩
  · norm_num [lowLocalTiny] at hεcap
    linarith only [hεcap]
  · linarith only [heε,hε]
  · linarith only [heε,hε]
  · rw [hid]
    norm_num [lowLocalTiny]

/-- All fixed high fees fit well inside the proven strict arithmetic reserve.
The sector mesh, source support, Fourier cutoff and row-absorption fees
are independently charged. -/
theorem high_local_total_budget (omega eFirst eSecond sourceLoss ξ rowAbsorb supportLoss clipLoss : ℝ)
    (homega : 0 ≤ omega) (homegaCap : omega ≤ lowLocalTiny)
    (he : 0 ≤ eFirst) (hecap : eFirst ≤ lowLocalTiny)
    (he₂ : 0 ≤ eSecond) (he₂cap : eSecond ≤ lowLocalTiny)
    (hs : 0 ≤ sourceLoss) (hscap : sourceLoss ≤ lowLocalTiny)
    (hξ : 0 ≤ ξ) (hξcap : ξ ≤ lowLocalTiny)
    (ha : 0 ≤ rowAbsorb) (hacap : rowAbsorb ≤ lowLocalTiny)
    (hsp : 0 ≤ supportLoss) (hspcap : supportLoss ≤ lowLocalTiny)
    (hcp : 0 ≤ clipLoss) (hcpcap : clipLoss ≤ 2*lowLocalTiny) :
    0 ≤ 10*eFirst+2*sourceLoss+ξ/2+rowAbsorb ∧
    0 ≤ supportLoss+clipLoss+eFirst ∧
    (omega+6*eFirst+eSecond)+lowLocalTiny+lowLocalTiny+lowLocalTiny+
      (10*eFirst+2*sourceLoss+ξ/2+rowAbsorb)+(supportLoss+clipLoss+eFirst)+4*eFirst ≤
        144011/109800000 ∧
    lowLocalTiny ≤ 144011/219600000 ∧
    -(144011/219600000 : ℝ)+lowLocalTiny+2*eFirst ≤ -1/10000 := by
  refine ⟨by positivity,by positivity,?_,?_,?_⟩
  all_goals norm_num [lowLocalTiny] at homegaCap hecap he₂cap hscap hξcap hacap hspcap hcpcap ⊢
  all_goals linarith

/-- The actual row and missing-radical upper widths are uniformly bounded,
using the exact cancellation saving rather than discarding canceled primes. -/
theorem high_local_row_missing_caps (c d p R R₀ E L geometryLoss missingLoss : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hp : p ≤ 1)
    (hR : 0 ≤ R) (hRp : R ≤ p) (hR₀ : 0 ≤ R₀) (hE : 0 ≤ E)
    (hL : 0 ≤ L) (hcancel : L ≤ 5*(R-R₀))
    (hg : geometryLoss ≤ 1/2) (hm : missingLoss ≤ 1) :
    1-R-max (c-d) 0+L-6*(3/500)+geometryLoss ≤ 6 ∧
    p-R-E+R₀+missingLoss ≤ 2 := by
  have hR₀R : R₀ ≤ R := by linarith
  constructor <;> linarith [le_max_right (c-d) 0]

theorem high_local_conductor_budget (BR W : ℝ) (hBR : 0 ≤ BR) (hW : W ≤ 6) :
    W+(BR+2)+lowLocalTiny ≤ highLocalDmax BR := by
  norm_num [highLocalDmax,lowLocalTiny]
  linarith only [hW]

/-- The original source scales satisfy the high product's fixed Rwidth=2
cap at any d≥1. This applies to all surviving subsets automatically. -/
theorem high_original_scale_caps {ι : Type*} [Fintype ι] [DecidableEq ι]
    (src : Input ι) (Z d : ℝ) (w : ι → ℝ) (hZ : 1 < Z) (hd : 1 ≤ d)
    (hP : ∀ i,src.P i=Z^(w i)) (hw : ∀ i,0 ≤ w i) (hwcap : ∀ i,w i ≤ lowLocalMesh)
    (hX₁ : Real.logb Z src.X₁ ≤ 423/1000) (hX₂ : Real.logb Z src.X₂ ≤ 423/1000)
    (hY₁ : Real.logb Z src.Y₁ ≤ 1) (hY₂ : Real.logb Z src.Y₂ ≤ 1) :
    src.X₁ ≤ (Z^d)^(2:ℝ) ∧ src.X₂ ≤ (Z^d)^(2:ℝ) ∧
    src.Y₁ ≤ (Z^d)^(2:ℝ) ∧ src.Y₂ ≤ (Z^d)^(2:ℝ) ∧
    ∀ i,1 ≤ src.P i ∧ src.P i ≤ (Z^d)^(2:ℝ) := by
  have hbase : Z^(1:ℝ) ≤ (Z^d)^(2:ℝ) := by
    rw [←Real.rpow_mul (zero_lt_one.trans hZ).le]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  refine ⟨(plain_scale_le_base src.X₁ Z src.X₁_pos hZ hX₁).trans hbase,
    (plain_scale_le_base src.X₂ Z src.X₂_pos hZ hX₂).trans hbase,
    (plain_scale_le_base_of_log_le_one src.Y₁ Z src.Y₁_pos hZ hY₁).trans hbase,
    (plain_scale_le_base_of_log_le_one src.Y₂ Z src.Y₂_pos hZ hY₂).trans hbase,?_⟩
  intro i
  rw [hP i]
  refine ⟨Real.one_le_rpow hZ.le (hw i),?_⟩
  have hm : lowLocalMesh ≤ lowLocalTiny/4 := min_le_right _ _
  have hi : w i ≤ 1 := by
    have hh := (hwcap i).trans hm
    norm_num [lowLocalTiny] at hh
    linarith only [hh]
  exact (Real.rpow_le_rpow_of_exponent_le hZ.le hi).trans hbase

/-- Generous fixed Fourier target bounds hold throughout the genuine local
source window and bounded first sectors. -/
theorem high_local_tail_target_caps (A c d p R E Bc b₂ g₂ t₂ omegaLoss : ℝ)
    (hA₀ : 0 ≤ A) (hA : A ≤ 883/1000)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (hd : 0 ≤ d)
    (hp : 0 ≤ p) (hR : 0 ≤ R) (hR1 : R ≤ 1)
    (hE : 0 ≤ E) (hE1 : E ≤ 1) (hBc : 0 ≤ Bc)
    (hgb : g₂ ≤ b₂) (ht : 0 ≤ t₂) (homega : omegaLoss ≤ 1) :
    A-min c d+R+E-1+5*(3/500)+g₂-t₂-b₂+omegaLoss ≤ 4 ∧
    -2 ≤ p+A-c+R+E+Bc-144011/109800000 := by
  have hm : 0 ≤ min c d := le_min hc hd
  constructor <;> linarith

#print axioms high_local_product_parameters
#print axioms high_local_total_budget
#print axioms high_original_scale_caps
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighLocalParameters -/

/- BEGIN ORIGINAL MODULE Analytic.JointNonHighLiteralTarget ; sha256 edc5789b8ce1fb2b5a6ff20d3781a845feb8408098d4f41c2a0706976a3aa523 -/
section







/-! The literal non-high contributions share one source, one first cell,
one prime family and one Fourier height exponent. All analytical bounds
are obtained from the genuine source endpoints inside this theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 4800000
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
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- The exact first amplifier coefficient at sigma=9/500 and Mmax=4. -/
def nonHighAmplifierFactor : ℝ := 56*((4+2*(9/500))/((9/500)/6))
def nonHighCutoff : ℝ := lowLocalTiny/4

/-- Literal normalized zero, exceptional, low-bin and discarded main
terms, followed by the selected amplifier errors with their original
normalization. -/
def firstNonHighContribution
    (src : Input α) (R seed : Ideal O) (Z : ℝ)
    (hs : Squarefree seed) (hz₁ : src.W₁ 0=0) (hz₂ : src.W₂ 0=0)
    (upper bplain₁ bplain₂ : ℝ) (W : 𝓢(ℝ,ℂ)) (Q : Ideal O) (χ : RayCharacter) (m : O)
    (P : Finset (Ideal O)) (primeCount : ℝ)
    (τ : (J : Finset α) → Character → elementPool P → Fin 3 → RayCharacter → Character)
    (I : ℕ) (e : ℝ) (bin : NonzeroElement → Option (Fin (I+1) × Fin (I+1)))
    (labels : Finset (FirstSourceOuterIndex src R seed Z
      (actualLowFirstRadius src R seed Z Z nonHighCutoff)))
    (left : Bool)
    (t : ((i : FirstSourceOuterIndex src R seed Z
      (actualLowFirstRadius src R seed Z Z nonHighCutoff)) ×
      (firstSourceOuterLabel src R seed Z (actualLowFirstRadius src R seed Z Z nonHighCutoff) i).SourceIndex) → ℝ) : ℝ :=
  let radius := actualLowFirstRadius src R seed Z Z nonHighCutoff
  let q := firstSourceOuterLabel src R seed Z radius
  let domain := firstSideSourceLabels labels q (fun _ => sourceRadius src) left
  let A := Real.logb Z (volume src.toData)
  let omega := lowLiteralOmega (Fintype.card α) upper bplain₁ bplain₂ nonHighCutoff nonHighCutoff Z
  let delta := frequencyLoss Z (32*(lowLiteralSupportConstant (Fintype.card α) upper bplain₁ bplain₂)^2) nonHighCutoff
  nonHighAmplifierFactor*((∑ k ∈ domain,
    ‖((firstLowMainScale (q k.1) left Z A 1 omega : ℂ)*paperRadialFourier W 0)*
      sourceSecondZero (commonSecondColumns (original src R seed) ((q k.1).sideCommon left)
        ((q k.1).sideCommon_supported left))
        (commonSecondBeta (original src R seed) ((q k.1).sideCommon left) k.2.1.val)
        (((q k.1).sourceChild k.2).sideParent left) (t k)‖/(volume src.toData*primeCount))+
    (∑ k ∈ domain,‖firstCoherentExceptionalPart src R seed Z radius k left Z A omega
      nonHighCutoff (t k) W χ Q m‖/(volume src.toData*primeCount))+
    (∑ bidx ∈ actualLowBins I e,∑ k ∈ domain,
      ‖firstLowBinBlock src R seed hs hz₁ hz₂ Z radius k left Z A 1 omega
        nonHighCutoff (t k) W bin bidx‖/(volume src.toData*primeCount))+
    (∑ k ∈ domain,‖firstCoherentTailPart src R seed Z radius k left Z A omega
      nonHighCutoff (t k) W‖/(volume src.toData*primeCount)))+
    ∑ k ∈ domain,firstCoherentErrorTerm src R seed Z radius k left upper delta nonHighCutoff (t k) P τ

variable (M : Ideal O) [NeZero M]
local instance nonHighLiteralFiniteQuotient : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem actual_literal_first_nonhigh_target
    (Wslot : ℝ → ℂ) (aslot bslot a b σlo σhi Mslot lower upper bplain₁ bplain₂ BRmask : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support Wslot ⊆ Icc aslot bslot)
    (hW : ContDiff ℝ ∞ Wslot) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1/4) (hb : 1 ≤ b)
    (hMslot : 0 ≤ Mslot) (hlower : 0 < lower) (hupper : 1 ≤ upper) (hBRmask : 0 ≤ BRmask)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) (hbetaTop : HeckeZeroSupremum.beta ≤ 7/8)
    (lows highs : α → ℝ) (hlows : ∀ i,0 < lows i) (hhighs : ∀ i,0 ≤ highs i)
    (ηfirst : Character) (profile : Profiles a b) (Wkernel : 𝓢(ℝ,ℂ))
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes ⊆ Sbad)
    (I : ℕ) (e τheight : ℝ) (he : 0 < e) (hecap : e ≤ lowLocalBinCap (Fintype.card α))
    (hτheight : 0 < τheight) (hτcap : τheight ≤ 1/8) :
    ∃ ν : ℝ, 0 < ν ∧ ν < τheight ∧
    ∀ (η₀ : Character) (Q : Ideal O) (hQM : Q ≤ M),
      internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      ∀ hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)},
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, ∀ hZ : 1 < Z,
    let P := primePool M H Sbad (1/2) 1 (Z^((9/500:ℝ)/3))
    ∀ (τ : (J : Finset α) → Character → elementPool P → Fin 3 → RayCharacter → Character),
      (∀ J η (p : elementPool P) i χ, ((τ J η p i χ).modulus.absNorm : ℝ) ≤
        CenteredMomentAmplificationRadicalFamily.radicalBound (CenteredMomentChildRows.childCharacter η χ)
          fixedBadMask p.val (CenteredMomentAmplificationActiveFactor.errorMovingExponent (errorIndex i))) →
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
    ∀ (R seed : Ideal O), R ≠ 0 → (R.absNorm : ℝ) ≤ Z^BRmask →
    ∀ hs : Squarefree seed, seed ≠ 0 →
    ∀ (hz₁ : src.W₁ 0=0) (hz₂ : src.W₂ 0=0),
    let radius := actualLowFirstRadius src R seed Z Z nonHighCutoff
    let q := firstSourceOuterLabel src R seed Z radius
    ∀ (labels : Finset (FirstSourceOuterIndex src R seed Z radius))
      (refIndex : FirstSourceOuterIndex src R seed Z radius), refIndex ∈ labels →
    ∀ eFirst : ℝ, 0 < eFirst → eFirst ≤ lowLocalTiny/8 →
      (∀ i ∈ labels,∀ j,|(q i).fullWidthCoordinates Z j-(q refIndex).fullWidthCoordinates Z j| < eFirst) →
    ∀ (t : ((i : FirstSourceOuterIndex src R seed Z radius) × (q i).SourceIndex) → ℝ),
      (∀ k ∈ firstSourceLabels labels q,|t k| ≤ Z^ν) →
    ∀ (bin : NonzeroElement → Option (Fin (I+1) × Fin (I+1))),
      (∀ w,bin w = none ↔ CenteredExceptionalProfile.FixedInducingRow ηfirst (internalQ Q η₀) fixedBadMask 1 w.val) →
      (∀ w bidx,bin w = some bidx →
        jointRelativeSourceZeroBin ηfirst (relativeSlotTranslate M H hH (fun _ : α => η₀))
          (internalQ Q η₀) hQ72
          (relativeSlotTranslate_fixedQ M H hH (fun _ : α => η₀) (internalQ Q η₀)
            (inf_le_left.trans hQM) (fun _ => inf_le_right))
          (fun _ => 1) (fun _ => one_ne_zero)
          (51/100+(e/2)*(bidx.2.val : ℝ)) (51/100+(e/2)*(bidx.2.val : ℝ)+e)
          (3*(bidx.1.val+1 : ℕ)*Z^τheight) w) →
    ∀ (χ : RayCharacter) (m : O), m ≠ 0 → goodLambda ∣ m → (2:O) ∣ m →
    ∀ left : Bool,
      firstNonHighContribution src R seed Z hs hz₁ hz₂ upper bplain₁ bplain₂ Wkernel
        (internalQ Q η₀) χ m P (actualHighPrimeCount M H Sbad Z) τ I e bin labels left t ≤
      (C/(seed.absNorm : ℝ))*(1/(((q refIndex).sideCommon left).absNorm : ℝ))*
        Z^((q refIndex).sideTargetWidth left Z (Real.logb Z (volume src.toData))-1/30000000) := by
  have hcut : 0 < nonHighCutoff := by norm_num [nonHighCutoff,lowLocalTiny]
  have hcutBudget : nonHighCutoff+nonHighCutoff ≤ lowLocalTiny := by norm_num [nonHighCutoff,lowLocalTiny]
  have hcutCap : nonHighCutoff ≤ lowLocalTiny := by norm_num [nonHighCutoff,lowLocalTiny]
  obtain ⟨νlow,hνlow,hνlowτ,hlow⟩ := actual_literal_first_low_target M H hH
    Wslot aslot bslot a b σlo σhi Mslot upper bplain₁ bplain₂ BRmask
    haslot hWs hW hbslot ha haUpper hb hMslot hBRmask hbeta hbetaTop lows highs hlows
    ηfirst profile Wkernel Sbad I e τheight he hecap hτheight hτcap
    nonHighCutoff nonHighCutoff nonHighCutoff hcut hcut.le hcutBudget hcut.le hcutCap
  obtain ⟨νex,hνex,hνexτ,hex⟩ := actual_literal_first_coherent_exceptional_target M H hH Sbad
    a b Mslot upper bplain₁ bplain₂ BRmask τheight nonHighCutoff nonHighCutoff
    ha (zero_le_one.trans hb) hMslot hBRmask hτheight hcut hcut.le hcutBudget
    lows highs hlows ηfirst profile Wkernel
  obtain ⟨νerr,hνerr,hνerrτ,herr⟩ := actual_literal_first_extracted_error_target M H hH
    Wslot aslot bslot a b σlo σhi Mslot lower upper bplain₁ bplain₂ BRmask
    haslot hWs hW hbslot ha haUpper hb hMslot hlower hupper hBRmask hbeta hbetaTop
    lows highs hhighs ηfirst profile Sbad hbad τheight nonHighCutoff nonHighCutoff
    hτheight hcut hcut.le hcutBudget
  let ν := min νlow (min νex νerr)/2
  have hν : 0 < ν := half_pos (lt_min hνlow (lt_min hνex hνerr))
  have hνlow' : ν ≤ νlow := (half_le_self (le_of_lt (lt_min hνlow (lt_min hνex hνerr)))).trans (min_le_left _ _)
  have hνex' : ν ≤ νex := (half_le_self (le_of_lt (lt_min hνlow (lt_min hνex hνerr)))).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hνerr' : ν ≤ νerr := (half_le_self (le_of_lt (lt_min hνlow (lt_min hνex hνerr)))).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ν,hν,hνlow'.trans_lt hνlowτ,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cl,hCl,hlow⟩ := hlow η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Ce,hCe,hex⟩ := hex (internalQ Q η₀) hQ0 hQt hQ72
  obtain ⟨Cr,hCr,herr⟩ := herr η₀ Q hQM hQ0 hQt hQ72
  let B₁ := SchwartzMap.seminorm ℝ 0 0 (profile.profile 0)
  let B₂ := SchwartzMap.seminorm ℝ 0 0 (profile.profile 1)
  have hB₁ : 0 ≤ B₁ := by positivity
  have hB₂ : 0 ≤ B₂ := by positivity
  obtain ⟨Cz,hCz,hzero⟩ := actual_literal_first_coherent_zero_target (ι := α) M H hH
    Mslot B₁ B₂ upper bplain₁ bplain₂ hB₁ hB₂ Wkernel Sbad
    nonHighCutoff nonHighCutoff hcut hcut.le hcutBudget
  obtain ⟨Ct,hCt,htail⟩ := actual_literal_first_coherent_tail_target (ι := α) M H hH Sbad
    Mslot B₁ B₂ upper bplain₁ bplain₂ hB₁ hB₂
    nonHighCutoff nonHighCutoff nonHighCutoff hcut hcut.le hcutBudget hcut Wkernel
  let C := nonHighAmplifierFactor*(Cz+Ce+Cl+Ct)+Cr
  have hF : 0 < nonHighAmplifierFactor := by norm_num [nonHighAmplifierFactor]
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  filter_upwards [hlow,hex,herr,hzero,htail,
    eventually_low_fixed_profile_gates (ι := α) upper bplain₁ bplain₂ b lowLocalTiny (by norm_num [lowLocalTiny])]
    with Z hlow hex herr hzero htail hfixed
  intro hZ P τ hτ θ w σ freq height hw hwmesh hσlo hσhi hheight hheightCap hfreq
    src hmatch hhi hMs hlo hhiInput hlowerSrc hupperSrc hhiAbs hb₁ hb₂ hb₁₀ hb₂₀ hb₁b hb₂b
    hp₁ hp₂ hη hsource₀ hn₁ hn₂ hm₁ hm₂ hwSum hcapacity hX₁ hX₂ hY₁ hY₂
    R seed hR hRcap hs hs0 hz₁ hz₂ radius q labels refIndex href eFirst heFirst heFirstCap hfull
    t ht bin hbinNone hbins χ m hm hmLam hm2 left
  let ref := q refIndex
  let A := Real.logb Z (volume src.toData)
  let domain := firstSideSourceLabels labels q (fun _ => sourceRadius src) left
  have hW₁ : ∀ x,‖src.W₁ x‖ ≤ B₁ := by rw [←hp₁]; exact SchwartzMap.norm_le_seminorm ℝ _
  have hW₂ : ∀ x,‖src.W₂ x‖ ≤ B₂ := by rw [←hp₂]; exact SchwartzMap.norm_le_seminorm ℝ _
  have hsector (i) (hi : i∈labels) (side : Bool) :=
    (q i).literal_target_gates_of_full ref side Z eFirst (hfull i hi)
  have hfirst (side : Bool) : ∀ i∈labels,
      (q i).radicalWidth Z ≤ ref.radicalWidth Z+lowLocalTiny ∧
      ref.sideWidth side Z ≤ (q i).sideWidth side Z+lowLocalTiny ∧
      (q i).activeWidth Z ≤ ref.activeWidth Z+lowLocalTiny ∧
      (q i).punctureWidth Z ≤ ref.punctureWidth Z+lowLocalTiny := by
    intro i hi
    have hh := hsector i hi side
    have heTiny : eFirst ≤ lowLocalTiny := by linarith [show (0:ℝ) < lowLocalTiny by norm_num [lowLocalTiny]]
    exact ⟨by linarith [hh.1],by linarith [hh.2.1],by linarith [hh.2.2.1],by linarith [hh.2.2.2.1]⟩
  have hcombined (side : Bool) (i) (hi : i∈labels) :
      -2*(q i).sideWidth side Z+(q i).activeWidth Z+(q i).punctureWidth Z+(q i).sideAllowance side Z ≤
        -2*ref.sideWidth side Z+ref.activeWidth Z+ref.punctureWidth Z+ref.sideAllowance side Z+lowLocalTiny := by
    have hh := (hsector i hi side).2.2.2.2
    linarith
  have hheightFor (ν' : ℝ) (hν' : ν ≤ ν') : height ≤ Z^ν' :=
    hheightCap.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hν')
  have htFor (ν' : ℝ) (hν' : ν ≤ ν') : ∀ k∈domain,|t k| ≤ Z^ν' := by
    intro k hk
    have hk' : k∈firstSourceLabels labels q := by
      cases left <;> exact (Finset.mem_filter.mp hk).1
    exact (ht k hk').trans (Real.rpow_le_rpow_of_exponent_le hZ.le hν')
  have hAeq := original_volume_log src Z w hZ hmatch.scale
  have hA := (local_capacity_of_volume Z (Real.logb Z src.X₁) (Real.logb Z src.X₂)
    (∑ i,w i) A hAeq hn₁ hn₂ hwSum hcapacity).1
  have hn₁lo : (1/4:ℝ) ≤ Real.logb Z src.X₁ := by
    have hh := Real.logb_le_logb_of_le hZ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hX₁
    simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh
  have hn₂lo : (1/4:ℝ) ≤ Real.logb Z src.X₂ := by
    have hh := Real.logb_le_logb_of_le hZ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hX₂
    simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh
  have hA0 : 0 ≤ A := by linarith [Finset.sum_nonneg (fun i (_ : i∈Finset.univ) => hw i)]
  have hsourceLog := (hfixed.2.1 src hsource₀ hhiAbs hb₁ hb₂ hupperSrc).1
  have hsource : sourceRadius src ≤ Z^(1:ℝ) := by
    calc
      _ = Z^(Real.logb Z (sourceRadius src)) := (Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hsource₀).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num [lowLocalTiny] at hsourceLog; linarith)
  have hrefCaps := first_actual_common_caps src R seed hs hz₁ hz₂ Z radius refIndex Z hsource
  have hzBound := hzero hZ src w hmatch.scale hMs hhiAbs hb₁ hb₂ hW₁ hW₂ hn₁ hn₂ hwSum hcapacity
    R seed hs hs0 hz₁ hz₂ hsource₀ Z hZ.le labels ref left (hfirst left) t
  have heBound := hex hZ src w hw hmatch.scale hlo hhiInput hMs hupperSrc hhiAbs hb₁ hb₂
    hp₁.symm hp₂.symm hη hsource₀ hn₁ hn₂ hwSum hcapacity hX₁ hX₂ hY₁ hY₂ R seed hR hRcap hs hs0
    labels ref left (by
      intro i hi
      have hh := (hfirst left i hi).1
      have hc := hcombined left i hi
      norm_num [lowLocalTiny] at hh hc
      exact ⟨by linarith,by linarith⟩) t (htFor νex hνex') χ m hm hmLam hm2
  have hlBound := hlow hZ θ w σ freq height hw hwmesh hσlo hσhi hheight (hheightFor νlow hνlow') hfreq
    src hmatch hhi hMs hp₁ hp₂ hlo hhiInput hhiAbs hupperSrc hb₁ hb₂ hη hn₁ hn₂ hm₁ hm₂ hwSum hcapacity
    R seed hR hRcap hs hs0 hz₁ hz₂ hsource₀ Z hZ.le labels ref left (hfirst left) t (htFor νlow hνlow')
    bin hbinNone hbins
  have htBound := htail hZ src hMs hupperSrc hhiAbs hb₁ hb₂ hW₁ hW₂ hz₁ hz₂ hsource₀ hA0 hA
    R seed hs hs0 Z hZ.le labels ref left hrefCaps.1 hrefCaps.2 (by
      intro i hi
      have hh := (hfirst left i hi).1
      norm_num [lowLocalTiny] at hh
      linarith) t
  have hrBound := herr hZ τ hτ θ w σ freq height hw hwmesh hσlo hσhi hheight (hheightFor νerr hνerr') hfreq
    src hmatch hhi hMs hlo hhiInput hlowerSrc hupperSrc hhiAbs hb₁ hb₂ hb₁₀ hb₂₀ hb₁b hb₂b
    hp₁ hp₂ hη hsource₀ hn₁ hn₂ hm₁ hm₂ hwSum hcapacity hX₁ hX₂ hY₁ hY₂
    R seed hR hRcap hs hs0 labels ref (by exact hη)
    (fun i hi => (hfirst true i hi).1)
    (by
      intro i hi
      have hh := hcombined true i hi
      simp only [FirstJointLabel.sideWidth,FirstJointLabel.sideCommon,FirstJointLabel.sideAllowance,
        FirstJointLabel.leftWidth,FirstJointLabel.rightWidth,ite_true,ite_false,Bool.false_eq_true] at hh ⊢
      linarith)
    (by
      intro i hi
      have hh := hcombined false i hi
      simp only [FirstJointLabel.sideWidth,FirstJointLabel.sideCommon,FirstJointLabel.sideAllowance,
        FirstJointLabel.leftWidth,FirstJointLabel.rightWidth,ite_true,ite_false,Bool.false_eq_true] at hh ⊢
      linarith)
    t (fun k hk => (ht k hk).trans (Real.rpow_le_rpow_of_exponent_le hZ.le hνerr')) left
  let factor := (1/(seed.absNorm : ℝ))*(1/((ref.sideCommon left).absNorm : ℝ))*
    Z^(ref.sideTargetWidth left Z A-1/30000000)
  have upgrade (c r x : ℝ) (hc : 0 ≤ c) (hr : (1/30000000:ℝ) ≤ r)
      (hx : x ≤ (c/(seed.absNorm : ℝ))*(1/((ref.sideCommon left).absNorm : ℝ))*
        Z^(ref.sideTargetWidth left Z A-r)) : x ≤ c*factor := by
    apply hx.trans
    have hp := Real.rpow_le_rpow_of_exponent_le hZ.le (show ref.sideTargetWidth left Z A-r ≤
      ref.sideTargetWidth left Z A-1/30000000 by linarith)
    have hh := mul_le_mul_of_nonneg_left hp
      (by positivity : 0 ≤ (c/(seed.absNorm : ℝ))*(1/((ref.sideCommon left).absNorm : ℝ)))
    convert hh using 1 <;> dsimp [factor] <;> ring
  have hz' := upgrade Cz (1/100) _ hCz.le (by norm_num) hzBound
  have he' := upgrade Ce (1/100) _ hCe.le (by norm_num) heBound
  have hl' := upgrade Cl (1/30000000) _ hCl.le (by norm_num) hlBound
  have ht' := upgrade Ct (1/100) _ hCt.le (by norm_num) htBound
  have hr' := upgrade Cr (1/10000) _ hCr.le (by norm_num) hrBound
  have hadd := add_le_add
    (mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add hz' he') hl') ht') hF.le) hr'
  change firstNonHighContribution src R seed Z hs hz₁ hz₂ upper bplain₁ bplain₂ Wkernel
      (internalQ Q η₀) χ m P (actualHighPrimeCount M H Sbad Z) τ I e bin labels left t ≤ _
  convert hadd using 1 <;> dsimp only [firstNonHighContribution,C,factor,domain,A,ref] <;> ring

#print axioms actual_literal_first_nonhigh_target
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointNonHighLiteralTarget -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstAnnularHighJoin ; sha256 763e04eb78ae1fcb802b86957c04e3149eb240cf32f853e8a5e92f2e7f6b6dbf -/
section




/-! The actual annular first amplifier and coherent five-part split are
joined to all genuine non-high estimates. Only the literal high-bin sum
remains as an analytic input. The chosen error characters precede sources. -/
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

def firstLiteralHighBinSum
    (src : Input α) (R : Ideal O) (Z : ℝ) (hz₁ : src.W₁ 0=0) (hz₂ : src.W₂ 0=0)
    (upper bplain₁ bplain₂ primeCount : ℝ) (I : ℕ) (e : ℝ)
    (bin : NonzeroElement → Option (Fin (I+1) × Fin (I+1)))
    (labels : Finset (FirstSourceOuterIndex src R 1 Z
      (actualLowFirstRadius src R 1 Z Z nonHighCutoff))) (left : Bool)
    (t : ((i : FirstSourceOuterIndex src R 1 Z
      (actualLowFirstRadius src R 1 Z Z nonHighCutoff)) ×
      (firstSourceOuterLabel src R 1 Z (actualLowFirstRadius src R 1 Z Z nonHighCutoff) i).SourceIndex) → ℝ) : ℝ :=
  let radius := actualLowFirstRadius src R 1 Z Z nonHighCutoff
  let q := firstSourceOuterLabel src R 1 Z radius
  let omega := lowLiteralOmega (Fintype.card α) upper bplain₁ bplain₂ nonHighCutoff nonHighCutoff Z
  ∑ bidx ∈ actualHighBins I e,∑ k ∈ firstSideSourceLabels labels q (fun _ => sourceRadius src) left,
    ‖firstLowBinBlock src R 1 squarefree_one hz₁ hz₂ Z radius k left Z
      (Real.logb Z (volume src.toData)) 1 omega nonHighCutoff (t k) ballProfile bin bidx‖/
      (volume src.toData*primeCount)

def firstLiteralAnnularEnergy
    (src : Input α) (R : Ideal O) (Z : ℝ)
    (labels : Finset (FirstSourceOuterIndex src R 1 Z
      (actualLowFirstRadius src R 1 Z Z nonHighCutoff))) (left : Bool)
    (t : ((i : FirstSourceOuterIndex src R 1 Z
      (actualLowFirstRadius src R 1 Z Z nonHighCutoff)) ×
      (firstSourceOuterLabel src R 1 Z (actualLowFirstRadius src R 1 Z Z nonHighCutoff) i).SourceIndex) → ℝ) : ℝ :=
  let q := firstSourceOuterLabel src R 1 Z (actualLowFirstRadius src R 1 Z Z nonHighCutoff)
  ∑ k ∈ firstSourceLabels labels q,((q k.1).sourceChild k.2).sideEnergy left (t k)
    CenteredMomentFirstAnnularMajorant.profile (dyadicScale (k.1.2.2 1))

variable (M : Ideal O) [NeZero M]
local instance annularJoinFiniteQuotient : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem actual_literal_first_annular_targets_of_high
    (Wslot : ℝ → ℂ) (aslot bslot a b σlo σhi Mslot lower upper bplain₁ bplain₂ BRmask : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support Wslot ⊆ Icc aslot bslot)
    (hW : ContDiff ℝ ∞ Wslot) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1/4) (hb : 1 ≤ b)
    (hMslot : 0 ≤ Mslot) (hlower : 0 < lower) (hupper : 1 ≤ upper) (hBRmask : 0 ≤ BRmask)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) (hbetaTop : HeckeZeroSupremum.beta ≤ 7/8)
    (lows highs : α → ℝ) (hlows : ∀ i,0 < lows i) (hhighs : ∀ i,0 ≤ highs i)
    (ηfirst : Character) (profile : Profiles a b)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes ⊆ Sbad)
    (I : ℕ) (e τheight : ℝ) (he : 0 < e) (hecap : e ≤ lowLocalBinCap (Fintype.card α))
    (hτheight : 0 < τheight) (hτcap : τheight ≤ 1/8) :
    ∃ ν : ℝ, 0 < ν ∧ ν < τheight ∧
    ∀ (η₀ : Character) (Q : Ideal O) (hQM : Q ≤ M),
      internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      ∀ hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)},
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    let P := primePool M H Sbad (1/2) 1 (Z^((9/500:ℝ)/3))
    ∃ τ : (J : Finset α) → Character → elementPool P → Fin 3 → RayCharacter → Character,
      (∀ J η (p : elementPool P) i χ, ((τ J η p i χ).modulus.absNorm : ℝ) ≤
        CenteredMomentAmplificationRadicalFamily.radicalBound (CenteredMomentChildRows.childCharacter η χ)
          fixedBadMask p.val (CenteredMomentAmplificationActiveFactor.errorMovingExponent (errorIndex i))) ∧
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
    ∀ (bin : NonzeroElement → Option (Fin (I+1) × Fin (I+1))),
      (∀ w,bin w = none ↔ CenteredExceptionalProfile.FixedInducingRow ηfirst (internalQ Q η₀) fixedBadMask 1 w.val) →
      (∀ w bidx,bin w = some bidx →
        jointRelativeSourceZeroBin ηfirst (relativeSlotTranslate M H hH (fun _ : α => η₀))
          (internalQ Q η₀) hQ72
          (relativeSlotTranslate_fixedQ M H hH (fun _ : α => η₀) (internalQ Q η₀)
            (inf_le_left.trans hQM) (fun _ => inf_le_right))
          (fun _ => 1) (fun _ => one_ne_zero)
          (51/100+(e/2)*(bidx.2.val : ℝ)) (51/100+(e/2)*(bidx.2.val : ℝ)+e)
          (3*(bidx.1.val+1 : ℕ)*Z^τheight) w) →
    ∀ Ch : ℝ, 0 ≤ Ch →
      (∀ left, firstLiteralHighBinSum src R Z hz₁ hz₂ upper bplain₁ bplain₂
        (actualHighPrimeCount M H Sbad Z) I e bin labels left (t left) ≤
        (Ch/(((q refIndex).sideCommon left).absNorm : ℝ))*
          Z^((q refIndex).sideTargetWidth left Z (Real.logb Z (volume src.toData)))) →
    ∀ left,
      firstLiteralAnnularEnergy src R Z labels left (t left) ≤
        (volume src.toData/(((q refIndex).sideCommon left).absNorm : ℝ))*
          ((C+nonHighAmplifierFactor*Ch)*Z^((q refIndex).sideTargetWidth left Z
            (Real.logb Z (volume src.toData)))) := by
  have hcut : 0 < nonHighCutoff := by norm_num [nonHighCutoff,lowLocalTiny]
  have hcutBudget : nonHighCutoff+nonHighCutoff ≤ lowLocalTiny := by norm_num [nonHighCutoff,lowLocalTiny]
  obtain ⟨ν,hν,hντ,hother⟩ := actual_literal_first_nonhigh_target M H hH
    Wslot aslot bslot a b σlo σhi Mslot lower upper bplain₁ bplain₂ BRmask
    haslot hWs hW hbslot ha haUpper hb hMslot hlower hupper hBRmask hbeta hbetaTop
    lows highs hlows hhighs ηfirst profile ballProfile Sbad hbad I e τheight he hecap hτheight hτcap
  refine ⟨ν,hν,hντ,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,hother⟩ := hother η₀ Q hQM hQ0 hQt hQ72
  have hamp := actual_first_literal_annular_amplification (ι := α) M H hH Sbad hbad
    (Fintype.card α) lower upper lowLocalTiny BRmask upper bplain₁ bplain₂ nonHighCutoff nonHighCutoff
    hlower (zero_le_one.trans hupper) (by norm_num [lowLocalTiny]) hcut hcut hcutBudget
  refine ⟨C,hC,?_⟩
  filter_upwards [hother,hamp,
    eventually_low_fixed_profile_gates (ι := α) upper bplain₁ bplain₂ b lowLocalTiny (by norm_num [lowLocalTiny])]
    with Z hother hamp hfixed
  obtain ⟨hZ,hP,hPcard,τ,hτ,hamp⟩ := hamp
  refine ⟨hZ,τ,hτ,?_⟩
  intro θ w σ freq height hw hwmesh hσlo hσhi hheight hheightCap hfreq
    src hmatch hhi hMs hlo hhiInput hlowerSrc hupperSrc hhiAbs hb₁ hb₂ hb₁₀ hb₂₀ hb₁b hb₂b
    hp₁ hp₂ hη hsource₀ hn₁ hn₂ hm₁ hm₂ hwSum hcapacity hX₁ hX₂ hY₁ hY₂
    R hR hRcap hz₁ hz₂ radius q labels refIndex href eFirst heFirst heFirstCap hfull t ht bin hbinNone hbins
    Ch hCh hhigh left
  let ref := q refIndex
  let A := Real.logb Z (volume src.toData)
  let omega := lowLiteralOmega (Fintype.card α) upper bplain₁ bplain₂ nonHighCutoff nonHighCutoff Z
  let P := primePool M H Sbad (1/2) 1 (Z^((9/500:ℝ)/3))
  have hprime : 0 < actualHighPrimeCount M H Sbad Z :=
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).trans_le hPcard
  have hAeq := original_volume_log src Z w hZ hmatch.scale
  have hA := (local_capacity_of_volume Z (Real.logb Z src.X₁) (Real.logb Z src.X₂)
    (∑ i,w i) A hAeq hn₁ hn₂ hwSum hcapacity).1
  have hsourceLog := (hfixed.2.1 src hsource₀ hhiAbs hb₁ hb₂ hupperSrc).1
  have hsource : sourceRadius src ≤ Z^(1:ℝ) := by
    calc
      _ = Z^(Real.logb Z (sourceRadius src)) := (Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hsource₀).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num [lowLocalTiny] at hsourceLog; linarith)
  have hampBound := hamp src R 1 squarefree_one hR hz₁ hz₂ hsource₀.le hsource hRcap le_rfl
    hlowerSrc hupperSrc hhiAbs hb₁ hb₂ w hwmesh hmatch.scale labels left (t left)
  have hnonhigh := hother hZ τ hτ θ w σ freq height hw hwmesh hσlo hσhi hheight hheightCap hfreq
    src hmatch hhi hMs hlo hhiInput hlowerSrc hupperSrc hhiAbs hb₁ hb₂ hb₁₀ hb₂₀ hb₁b hb₂b
    hp₁ hp₂ hη hsource₀ hn₁ hn₂ hm₁ hm₂ hwSum hcapacity hX₁ hX₂ hY₁ hY₂ R 1 hR hRcap
    squarefree_one one_ne_zero hz₁ hz₂ labels refIndex href eFirst heFirst heFirstCap hfull
    (t left) (ht left) bin hbinNone hbins 1 fixedBadMask fixedBadMask_ne_zero
    (dvd_mul_right _ _) (dvd_mul_left _ _) left
  have hbinSrc (v) : bin v=none ↔
      CenteredExceptionalProfile.FixedInducingRow src.η (internalQ Q η₀) fixedBadMask 1 v.val := by
    rw [hη]
    exact hbinNone v
  have hupperBin (v) (bidx) (hv : bin v=some bidx) :
      51/100+(e/2)*(bidx.2.val : ℝ) ≤ 7/8 := by
    obtain ⟨hnp,hloBin,hhiBin⟩ := hbins v bidx hv
    exact hloBin.trans (zeroMaximum_le_seven_eighths _ _ _ hbetaTop)
  have hsplit := actual_first_common_low_high_split src R 1 squarefree_one hz₁ hz₂ Z radius labels left
    Z A 1 omega nonHighCutoff (zero_lt_one.trans hZ) ballProfile (actualHighPrimeCount M H Sbad Z) hprime
    I e bin (internalQ Q η₀) hQ72 hbinSrc hupperBin 1 fixedBadMask fixedBadMask_ne_zero
    (dvd_mul_right _ _) (dvd_mul_left _ _) (t left)
  have hF : 0 ≤ nonHighAmplifierFactor := by norm_num [nonHighAmplifierFactor]
  have hnormalized : firstLiteralAnnularEnergy src R Z labels left (t left)/volume src.toData ≤
      firstNonHighContribution src R 1 Z squarefree_one hz₁ hz₂ upper bplain₁ bplain₂ ballProfile
        (internalQ Q η₀) 1 fixedBadMask P (actualHighPrimeCount M H Sbad Z) τ I e bin labels left (t left)+
      nonHighAmplifierFactor*firstLiteralHighBinSum src R Z hz₁ hz₂ upper bplain₁ bplain₂
        (actualHighPrimeCount M H Sbad Z) I e bin labels left (t left) := by
    rw [firstLiteralAnnularEnergy,Finset.sum_div]
    apply hampBound.trans
    have hh := mul_le_mul_of_nonneg_left hsplit hF
    dsimp only at hh
    have hh' := add_le_add_right hh
      (∑ k∈firstSideSourceLabels labels q (fun _ => sourceRadius src) left,
        firstCoherentErrorTerm src R 1 Z radius k left upper
          (frequencyLoss Z (32*(lowLiteralSupportConstant (Fintype.card α) upper bplain₁ bplain₂)^2) nonHighCutoff)
          nonHighCutoff (t left k) P τ)
    have hv : CenteredMomentAmplificationChildInput.volume src=volume src.toData := rfl
    convert hh' using 1 <;> first
      | rfl
      | (dsimp only [firstNonHighContribution,firstLiteralHighBinSum,firstCoherentExceptionalPart,
          firstCoherentTailPart,firstCoherentErrorTerm,nonHighAmplifierFactor,omega,A]
         rw [hv]
         ring)
  have hnonhigh' : firstNonHighContribution src R 1 Z squarefree_one hz₁ hz₂ upper bplain₁ bplain₂ ballProfile
      (internalQ Q η₀) 1 fixedBadMask P (actualHighPrimeCount M H Sbad Z) τ I e bin labels left (t left) ≤
      (C/((ref.sideCommon left).absNorm : ℝ))*Z^(ref.sideTargetWidth left Z A) := by
    apply hnonhigh.trans
    have hN1 : ((1 : Ideal O).absNorm : ℝ)=1 := by
      simp only [Ideal.one_eq_top,Ideal.absNorm_top,Nat.cast_one]
    rw [hN1,div_one]
    have hp := Real.rpow_le_rpow_of_exponent_le hZ.le
      (show ref.sideTargetWidth left Z A-1/30000000 ≤ ref.sideTargetWidth left Z A by linarith)
    convert mul_le_mul_of_nonneg_left hp
      (by positivity : 0 ≤ C/((ref.sideCommon left).absNorm : ℝ)) using 1 <;> ring
  have hbound := hnormalized.trans (add_le_add hnonhigh'
    (mul_le_mul_of_nonneg_left (hhigh left) hF))
  have hraw := (div_le_iff₀ (volume_pos src.toData)).mp hbound
  convert hraw using 1 <;> ring

#print axioms actual_literal_first_annular_targets_of_high
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstAnnularHighJoin -/
