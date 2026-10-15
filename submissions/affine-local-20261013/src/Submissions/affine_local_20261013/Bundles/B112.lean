/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.affine_local_20261013.Bundles.B016
import Submissions.affine_local_20261013.Bundles.B070
import Submissions.affine_local_20261013.Bundles.B088
import Submissions.affine_local_20261013.Bundles.B090
import Submissions.affine_local_20261013.Bundles.B096
import Submissions.affine_local_20261013.Bundles.B104
import Submissions.affine_local_20261013.Bundles.B108
import Submissions.affine_local_20261013.Bundles.B109
import Submissions.affine_local_20261013.Bundles.B110
import Submissions.affine_local_20261013.Bundles.B111
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceInputFirstTailScale

/- BEGIN ORIGINAL MODULE Analytic.JointFirstLiveRowSupport ; sha256 4ed1062f263c6189c62d12f88ce78dbb0223de17d32caeafac9a567ba49e2532 -/
section


/-! The actual joint row image inherits a retained-frequency witness at the
literal residual source radius. This supplies the support side of the high
row-norm geometry without an independent row-size hypothesis. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

namespace ActualFirstSecondSource
variable (src : Input ι) (R seed : Ideal O) (Kfirst : ℝ)
  (radius : (p : Labels src R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ)
  (side : Bool) (Z A M omega ξ : ℝ)
  (hs : Squarefree seed) (hz₁ : src.W₁ 0=0) (hz₂ : src.W₂ 0=0)
  (bin : NonzeroElement → Option κ) (b : κ)
  (t : First src R seed Kfirst radius → ℝ) (W : 𝓢(ℝ,ℂ))
  (labels : Finset (FirstSourceOuterIndex src R seed Kfirst radius))

theorem live_rayRows_frequency_witness
    (fallback : First src R seed Kfirst radius) (χ₁ ξ₁ : RayCharacter)
    (q : NonzeroJointSourceRow (original src R seed) side)
    (hq : q∈rayRows fallback
      (liveBinPackets src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b t W labels)
      (liveBinPackets_nonzero src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b t W labels) χ₁ ξ₁) :
    let K := mainScale src R seed Kfirst radius side Z A M omega
    let Radius := mainRadius src R seed Kfirst radius side Z A M omega ξ
    ∃ n : q.val.FirstDyadic Kfirst (radius q.val.first q.val.E) (sourceRadius src),
      secondScale fallback Radius χ₁ ξ₁ q.val n =
        frequencyRadius ((sourceRadius src/(q.label.C₁.absNorm : ℝ))^2 /
          secondScale fallback K χ₁ ξ₁ q.val n) Z ξ ∧
      q.val.z ∈ ActualJointSourceRow.liveFrequencyRows q.val.second.val.1 q.val.second.val.2 q.val.U
        (secondScale fallback Radius χ₁ ξ₁ q.val n) := by
  dsimp only
  obtain ⟨x,hx,hχ,hξ,hrow⟩ := mem_rayRows_witness fallback _ _ χ₁ ξ₁ q hq
  rcases q with ⟨q,hqzero⟩
  change row x=q at hrow
  subst q
  subst χ₁; subst ξ₁
  let n : (row x).FirstDyadic Kfirst (radius (row x).first (row x).E) (sourceRadius src) := x.1.1.2.2
  refine ⟨n,?_,?_⟩
  · change secondScale fallback (mainRadius src R seed Kfirst radius side Z A M omega ξ)
      x.1.2.2.1 x.1.2.2.2 (row x) n =
      frequencyRadius ((sourceRadius src/((row x).label.C₁.absNorm : ℝ))^2 /
        secondScale fallback (mainScale src R seed Kfirst radius side Z A M omega)
          x.1.2.2.1 x.1.2.2.2 (row x) n) Z ξ
    rw [secondScale_mainRadius,secondScale_mainScale,mainRadius_actual,mainHeight_row]
  · change (row x).z ∈ ActualJointSourceRow.liveFrequencyRows
      (row x).second.val.1 (row x).second.val.2 (row x).U
      (secondScale fallback (mainRadius src R seed Kfirst radius side Z A M omega ξ)
        x.1.2.2.1 x.1.2.2.2 (row x) n)
    rw [secondScale_mainRadius]
    exact live_packet_frequency src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b t W labels x hx

end ActualFirstSecondSource
#print axioms ActualFirstSecondSource.live_rayRows_frequency_witness
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstLiveRowSupport -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstSectorTolerances ; sha256 5b0dba9d8e33e77fdb75a62b4cd245ea0c30f81094d267953554dc8e0997ad19 -/
section




/-! Explicit mesh costs for transporting actual first-width sectors to a
single reference. Radius, common-volume and missing-radical tolerances are
kept separate and charged once in their respective high-source budgets. -/
set_option autoImplicit false
namespace OAI
noncomputable section
namespace SevenEighths.Local44.Analytic

def firstMainExponent (A c d R E M a omega : ℝ) : ℝ :=
  2*A-c-d+R+E-M+max (d-c) 0+6*a+omega

theorem first_main_exponent_upper (A c d R E c₀ d₀ R₀ E₀ M a omega e : ℝ)
    (he : 0≤ e) (hc : |c-c₀|≤ e) (hd : |d-d₀|≤ e)
    (hR : |R-R₀|≤ e) (hE : |E-E₀|≤ e) :
    firstMainExponent A c d R E M a omega ≤ firstMainExponent A c₀ d₀ R₀ E₀ M a omega+6*e := by
  have hmax : max (d-c) 0≤ max (d₀-c₀) 0+2*e := by
    apply max_le
    · linarith [(abs_le.mp hc).1,(abs_le.mp hd).2,le_max_left (d₀-c₀) 0]
    · linarith [le_max_right (d₀-c₀) 0]
  unfold firstMainExponent
  linarith [(abs_le.mp hc).1,(abs_le.mp hd).1,(abs_le.mp hR).2,(abs_le.mp hE).2]

theorem first_main_exponent_lower (A c d R E c₀ d₀ R₀ E₀ M a omega e : ℝ)
    (he : 0≤ e) (hc : |c-c₀|≤ e) (hd : |d-d₀|≤ e)
    (hR : |R-R₀|≤ e) (hE : |E-E₀|≤ e) :
    firstMainExponent A c₀ d₀ R₀ E₀ M a omega-6*e≤ firstMainExponent A c d R E M a omega := by
  have hh := first_main_exponent_upper A c₀ d₀ R₀ E₀ c d R E M a omega e he
    (by simpa only [abs_sub_comm] using hc) (by simpa only [abs_sub_comm] using hd)
    (by simpa only [abs_sub_comm] using hR) (by simpa only [abs_sub_comm] using hE)
  linarith

/-- The lower radius parameters required by the source-row geometry.
Both first common lower edges cost two meshes before the six-mesh scale gap. -/
theorem first_row_scale_sector_lower (A c d R E c₀ d₀ R₀ E₀ M a omega e : ℝ)
    (he : 0≤ e) (hc : |c-c₀|≤ e) (hd : |d-d₀|≤ e)
    (hR : |R-R₀|≤ e) (hE : |E-E₀|≤ e) :
    firstMainExponent A (c₀-e) (d₀-e) R₀ E₀ M a (omega-8*e)≤
      firstMainExponent A c d R E M a omega := by
  have hh := first_main_exponent_lower A c d R E c₀ d₀ R₀ E₀ M a omega e he hc hd hR hE
  have hm : (d₀-e)-(c₀-e)=d₀-c₀ := by ring
  unfold firstMainExponent at *
  rw [hm]
  linarith

/-- Four one-sided first-sector substitutions account for the entire
missing-radical tolerance. -/
theorem first_missing_sector_loss (p R E R₀ e : ℝ) :
    (p+e)-(R-e)-(E-e)+(R₀+e)=p-R-E+R₀+4*e := by ring

/-- With the actual common lower edges and lower ball scale, ten mesh
widths pay the row reconstruction tolerance. -/
theorem first_row_sector_loss (c d R L a omega e sourceLoss ξ absorb : ℝ) :
    1-R-max ((c-e)-(d-e)) 0+(L+e)-6*a-(omega-8*e)+
      2*sourceLoss+e+ξ/2+absorb =
      1-R-max (c-d) 0+L-6*a-omega+10*e+2*sourceLoss+ξ/2+absorb := by
  rw [show (c-e)-(d-e)=c-d by ring]
  ring

#print axioms first_row_scale_sector_lower
#print axioms first_missing_sector_loss
#print axioms first_row_sector_loss
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstSectorTolerances -/

/- BEGIN ORIGINAL MODULE Analytic.JointHighPacketBins ; sha256 019a74b66bf55952bc9694f8f308a93f32dbe11a2a13dbf5660af5a75593ab3a -/
section




/-! The single global classifier supplies the complete relative zero bin
on every canonical source row in every actual packet cell. Punctures may
depend on the reconstruction label; the classifier remains unchanged. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentCanonicalFirst CenteredMomentExceptionalAmplitudePair
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily NonzeroJointSourceRow
local notation "O" => HeckeFamily.O
variable {Slot κ : Type*} [Fintype Slot] [DecidableEq Slot] [DecidableEq κ]

namespace ActualFirstSecondSource
variable (src : Input Slot) (R seed : Ideal O) (Kfirst : ℝ)
  (radius : (p : Labels src R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ)
  (side : Bool) (Z A M omega ξ : ℝ)
  (hs : Squarefree seed) (hz₁ : src.W₁ 0=0) (hz₂ : src.W₂ 0=0)
  (bin : NonzeroElement → Option κ) (b : κ)
  (t : First src R seed Kfirst radius → ℝ) (W : 𝓢(ℝ,ℂ))
  (labels : Finset (FirstSourceOuterIndex src R seed Kfirst radius))

theorem subset_rayRows_bin
    (X : Finset (LivePacket src R seed Kfirst radius side Z A M omega ξ))
    (hX : X ⊆ liveBinPackets src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b t W labels)
    (hzero : ∀ x ∈ X,(row x).z ≠ 0)
    (fallback : First src R seed Kfirst radius) (χ₁ ξ₁ : RayCharacter)
    (q : NonzeroJointSourceRow (original src R seed) side)
    (hq : q ∈ rayRows fallback X hzero χ₁ ξ₁) :
    bin (q.val.reconstructed src.η χ₁ ξ₁⁻¹ q.property) = some b := by
  obtain ⟨x,hx,hχ,hξ,hrow⟩ := mem_rayRows_witness fallback X hzero χ₁ ξ₁ q hq
  have hb := live_packet_bin src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b t W labels x (hX hx)
  subst χ₁
  subst ξ₁
  simpa only [hrow] using hb

theorem packet_cell_canonical_bin
    (X : Finset (LivePacket src R seed Kfirst radius side Z A M omega ξ))
    (hX : X ⊆ liveBinPackets src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b t W labels)
    (hzero : ∀ x ∈ X,(row x).z ≠ 0)
    (fallbackFirst : First src R seed Kfirst radius)
    (fallback : NonzeroJointSourceRow (original src R seed) side) (χ₁ ξ₁ : RayCharacter) :
    ∀ v ∈ (rayRows fallbackFirst X hzero χ₁ ξ₁).image NonzeroJointSourceRow.label,
      bin (sourceRow fallback src.η χ₁ ξ₁⁻¹ v) = some b := by
  intro v hv
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hv
  simpa only [sourceRow,recover_label] using subset_rayRows_bin src R seed Kfirst radius side
    Z A M omega ξ hs hz₁ hz₂ bin b t W labels X hX hzero fallbackFirst χ₁ ξ₁ q hq

end ActualFirstSecondSource

open ActualFirstSecondSource
variable (modulus : Ideal O) [NeZero modulus]
local instance highPacketBinsFiniteQuotient : Finite (O ⧸ modulus) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne modulus)
variable (H : Subgroup (O ⧸ modulus)ˣ) (hH : RayOrthogonality.globalUnits modulus ≤ H)

theorem actual_packet_cell_relative_source_bin
    (src : Input Slot) (R seed : Ideal O) (Kfirst : ℝ)
    (radius : (p : Labels src R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ)
    (side : Bool) (Z A M omega ξ : ℝ)
    (hs : Squarefree seed) (hz₁ : src.W₁ 0=0) (hz₂ : src.W₂ 0=0)
    (I : ℕ) (bin : NonzeroElement → Option (Fin (I+1) × Fin (I+1)))
    (b : Fin (I+1) × Fin (I+1))
    (t : First src R seed Kfirst radius → ℝ) (W : 𝓢(ℝ,ℂ))
    (labels : Finset (FirstSourceOuterIndex src R seed Kfirst radius))
    (η₀ : Character) (Q : Ideal O) (hQ72 : Q ≤ Ideal.span {(72:O)})
    (hQM : Q ≤ modulus) (hQη₀ : Q ≤ η₀.modulus) (e T : ℝ)
    (hclass : ∀ w b,bin w = some b →
      ∀ (P : JointRelativeLabel src.η (Option (Slot × RayQuotient.Characters modulus H)) → Ideal O)
        (hP : ∀ label,P label ≠ 0),
        jointRelativeSourceZeroBin src.η (relativeSlotTranslate modulus H hH (fun _ : Slot => η₀))
          Q hQ72 (relativeSlotTranslate_fixedQ modulus H hH (fun _ : Slot => η₀) Q hQM
            (fun _ => hQη₀)) P hP
          (51/100+(e/2)*(b.2.val : ℝ)) (51/100+(e/2)*(b.2.val : ℝ)+e)
          ((3*(b.1.val+1):ℕ)*T) w)
    (X : Finset (LivePacket src R seed Kfirst radius side Z A M omega ξ))
    (hX : X ⊆ liveBinPackets src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b t W labels)
    (hzero : ∀ x ∈ X,(row x).z ≠ 0)
    (fallbackFirst : First src R seed Kfirst radius)
    (fallback : NonzeroJointSourceRow (original src R seed) side) (χ₁ ξ₁ : RayCharacter)
    (P : JointReconstructionLabel →
      JointRelativeLabel src.η (Option (Slot × RayQuotient.Characters modulus H)) → Ideal O)
    (hP : ∀ v label,P v label ≠ 0) :
    ∀ v ∈ (rayRows fallbackFirst X hzero χ₁ ξ₁).image NonzeroJointSourceRow.label,
      jointRelativeSourceZeroBin src.η (relativeSlotTranslate modulus H hH (fun _ : Slot => η₀))
        Q hQ72 (relativeSlotTranslate_fixedQ modulus H hH (fun _ : Slot => η₀) Q hQM
          (fun _ => hQη₀)) (P v) (hP v)
        (51/100+(e/2)*(b.2.val : ℝ)) (51/100+(e/2)*(b.2.val : ℝ)+e)
        ((3*(b.1.val+1):ℕ)*T) (sourceRow fallback src.η χ₁ ξ₁⁻¹ v) := by
  intro v hv
  exact hclass _ b
    (packet_cell_canonical_bin src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b
      t W labels X hX hzero fallbackFirst fallback χ₁ ξ₁ v hv) (P v) (hP v)

#print axioms ActualFirstSecondSource.packet_cell_canonical_bin
#print axioms actual_packet_cell_relative_source_bin
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighPacketBins -/

/- BEGIN ORIGINAL MODULE Analytic.JointHighPacketGeometry ; sha256 75f9954d7fe7e9a0fbec62e85e75af7ad0b9e34b3ce9523fcad68c6b2faff925 -/
section





/-! The genuine high-source estimate summed over both actual dyadic block
families. Maximization pays their subpower mass without recounting arithmetic rows. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Set Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification HeckeDetectorZeros CanonicalQuadraticSieve
open IdealMobiusDivisorSum LocalMoment ProbeHighRowFamily ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentSectorLocalization HeckeDetectorDyadicGeometry
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput RayFourExpansion
open NonzeroJointSourceRow CenteredMomentOriginalCommonHarmonic
open CenteredMomentCanonicalFirst CenteredMomentActive CenteredMomentCompleteCommon
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondPhysicalBlock
open CenteredMomentSourceRow CenteredMomentSecondLiveBlock
open CanonicalRowCompletion CenteredMomentRankinRadical ActualEisensteinCubic
open ActualFirstSecondSource CenteredMomentFirstNonexceptionalWeightSum
open CenteredMomentSecondBlockHarmonicMass
open CenteredMomentFirstPhysicalDyadicAssembly
local notation "O" => HeckeFamily.O

section FixedData
variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
variable (η : Character) (η₀ : Slot → Character) (Q : Ideal O) [NeZero Q]
  (hQtop : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hQη : Q ≤ η.modulus)
  (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
  (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
  (hH : RayOrthogonality.globalUnits M ≤ H) (hQM : Q ≤ M)
  (hQη₀ : ∀ j, Q ≤ (η₀ j).modulus)
  (S₀ : Finset (Ideal O))
  (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
  (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
  (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
  (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
  (hβupper : HeckeZeroSupremum.beta ≤ 7/8)
include hQtop hQ72 hQη hβ hH hQM hQη₀ S₀ hφ hφc hφp hφ0 hφne ha₀ hab₀ hB₀ hφs hφB hβupper

theorem actual_joint_high_packet_geometry
    (V : Slot → ℝ → ℂ) (Aprofile Bprofile : Slot → ℝ) (hA : ∀ j, 0 < Aprofile j)
    (hVs : ∀ j, Function.support (V j) ⊆ Icc (Aprofile j) (Bprofile j))
    (hV : ∀ j, ContDiff ℝ ∞ (V j))
    (ηcommon : Character) (hanchor : ∀ j, η₀ j = ηcommon)
    (Wslot : ℝ → ℂ) (hVslot : ∀ j, V j = Wslot)
    (bslot : ℝ) (hBslot : ∀ j, Bprofile j = bslot)
    (Rwidth dmax ε e κ ηaux σmin σmax productLoss populationLoss loss B : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hκone : κ ≤ 1) (hη : 0 < ηaux)
    (hbudget : 12*e*(Rwidth+2)+8*κ+2*ηaux ≤ ε)
    (hprimebudget : 8*e*Rwidth+κ ≤ ε)
    (hproductLoss : (2+2*(Fintype.card Slot : ℝ))*ε ≤ productLoss)
    (hpopulationLoss : 0 < populationLoss) (hB : 0 ≤ B)
    (hloss : populationLoss+dmax*productLoss ≤ loss)
    (τdetector dmin heightLoss : ℝ) (I : ℕ)
    (hτdetector : 0 < τdetector) (hdmin : 0 < dmin) (hheightLoss : 0 < heightLoss)
    (W₁ W₂ : ℝ → ℂ) (a₁ b₁ a₂ b₂plain : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hs₁ : Function.support W₁ ⊆ Icc a₁ b₁) (hW₁ : ContDiff ℝ ∞ W₁)
    (hs₂ : Function.support W₂ ⊆ Icc a₂ b₂plain) (hW₂ : ContDiff ℝ ∞ W₂)
    (lo hi : Slot → ℝ) (fiberLoss : ℝ) (hfiberLoss : 0 < fiberLoss)
    (aSource Mslot upper : ℝ) (haSource : 0 < aSource) (hMslot : 0 ≤ Mslot)
    (conductorReserve : ℝ) (hconductorReserve : 0 < conductorReserve)
    (Sbad : Finset (Ideal O)) (primeLoss : ℝ) (hprimeLoss : 0 < primeLoss)
    (hprimeReserve : primeLoss ≤ 144011/219600000)
    (Wkernel : 𝓢(ℝ,ℂ))
    (tailA targetLower plainBound₁ plainBound₂ : ℝ)
    (hplainBound₁ : 0 ≤ plainBound₁) (hplainBound₂ : 0 ≤ plainBound₂)
    (hplainNorm₁ : ∀ x, ‖W₁ x‖ ≤ plainBound₁) (hplainNorm₂ : ∀ x, ‖W₂ x‖ ≤ plainBound₂)
    (Bdyad₁ Ldyad₁ Crdyad₁ Bdyad₂ Ldyad₂ Crdyad₂ dyadicLoss : ℝ)
    (hBdyad₁ : 0 ≤ Bdyad₁) (hLdyad₁ : 0 ≤ Ldyad₁) (hCrdyad₁ : 0 < Crdyad₁)
    (hBdyad₂ : 0 ≤ Bdyad₂) (hLdyad₂ : 0 ≤ Ldyad₂) (hCrdyad₂ : 0 < Crdyad₂)
    (hdyadicLoss : 0 < dyadicLoss)
    (rowAbsorb : ℝ) (hrowAbsorb : 0 < rowAbsorb)
    (haSource_eq : aSource = (∏ j, lo j)*a₁*a₂) :
    ∃ profileBound : ℕ → ℝ, (∀ k, 0 < profileBound k) ∧
    ∃ (τ ν : ℝ) (orders : Finset Slot → ℕ) (N Nkernel : ℕ) (C : ℝ),
      0 < ν ∧ ν < τ ∧ τ < τdetector ∧ 4*τ < dmin*ηaux ∧
      (∀ J, orders J ≤ N) ∧ 0 < C ∧
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (d P W : ℝ), dmin ≤ d → d ≤ dmax → 2 ≤ Z^d → 2 < Z^τ → P ≤ B → W ≤ B →
      ∀ (p : DensityWindow), p.upper < p.lower+2*e →
      ∀ i : ℕ, i ≤ I → p.height = (3*(i+1 : ℕ))*Z^τ →
      ∀ (input : Input Slot) (puncture seed : Ideal O)
        (hpuncture : puncture ≠ 0) (hseed : Squarefree seed)
        (hz₁ : input.W₁ 0 = 0) (hz₂ : input.W₂ 0 = 0)
        (hinputη : input.η=η) (side : Bool) (ξ₁ ξ₂ : RayCharacter)
        (fallback : NonzeroJointSourceRow (original input puncture seed) side)
        (K₁ : ℝ)
        (radius : (p : Labels input puncture seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ)
        (fallbackFirst : First input puncture seed K₁ radius)
        (K Radius Height : First input puncture seed K₁ radius → ℝ)
        (X : Finset (Packet input puncture seed K₁ radius side K Radius Height))
        (hzero : ∀ x∈X,(row x).z≠0),
      let qs := rayRows fallbackFirst X hzero ξ₁ ξ₂;
      let Kfirst := fun _ : NonzeroJointSourceRow (original input puncture seed) side => K₁;
      let Rfirst := fun q : NonzeroJointSourceRow (original input puncture seed) side => radius q.val.first q.val.E;
      let Hfirst := fun _ : NonzeroJointSourceRow (original input puncture seed) side => sourceRadius input;
      let Ksecond := fun q : NonzeroJointSourceRow (original input puncture seed) side => secondScale fallbackFirst K ξ₁ ξ₂ q.val;
      let Rsecond := fun q : NonzeroJointSourceRow (original input puncture seed) side => secondScale fallbackFirst Radius ξ₁ ξ₂ q.val;
      let Hsecond := fun q : NonzeroJointSourceRow (original input puncture seed) side => secondScale fallbackFirst Height ξ₁ ξ₂ q.val;
      let good := fun (q : NonzeroJointSourceRow (original input puncture seed) side)
        (b : q.val.DyadicFiber (Kfirst q) (Rfirst q) (Hfirst q) (Ksecond q) (Rsecond q) (Hsecond q)) =>
        (⟨q,b⟩ : FiberTarget fallbackFirst ξ₁ ξ₂ K Radius Height side)∈rayTarget fallbackFirst X hzero ξ₁ ξ₂;
      let S := qs.image NonzeroJointSourceRow.label
      let unit := sourceUnit fallback η ξ₁ ξ₂⁻¹
      let w := sourceRow fallback η ξ₁ ξ₂⁻¹
      let s := sourceKernel input puncture seed side hseed hz₁ hz₂ fallback η ξ₁ ξ₂⁻¹ 1 1
      let first := sourceFirst fallback η ξ₁ ξ₂⁻¹
      let z := sourceFrequency fallback
      let Ds := fun v => (s v).physicalProjectors
      ∀ (R : JointReconstructionLabel →
        JointRelativeLabel η (Option (Slot × RayQuotient.Characters M H)) → Ideal O)
        (hR : ∀ v label, R v label ≠ 0),
      (∀ v ∈ S, jointRelativeSourceZeroBin η (relativeSlotTranslate M H hH η₀) Q hQ72
        (relativeSlotTranslate_fixedQ M H hH η₀ Q hQM hQη₀) (R v) (hR v)
        p.lower p.upper p.height (w v)) →
      sourceRadius input ≤ Z^B →
      (∀ q ∈ qs, 0 < Kfirst q ∧ 0 < Hfirst q ∧
        Rfirst q ≤ Crdyad₁*Z^Ldyad₁ ∧ Hfirst q ≤ Z^Bdyad₁) →
      (∀ q ∈ qs, ∀ n₁, 0 < Ksecond q n₁ ∧
        Rsecond q n₁ ≤ Crdyad₂*Z^Ldyad₂ ∧ Hsecond q n₁ ≤ Z^Bdyad₂) →
      ∀ (height : First input puncture seed K₁ radius → ℝ),
      let t := fun (q : NonzeroJointSourceRow (original input puncture seed) side)
        (n : q.val.FirstDyadic (Kfirst q) (Rfirst q) (Hfirst q)) => height (firstAt fallbackFirst q.val ξ₁ ξ₂ n);
      ∀ (tbase firstU firstTheta : (q : NonzeroJointSourceRow (original input puncture seed) side) → q.val.FirstDyadic (Kfirst q) (Rfirst q) (Hfirst q) → ℝ)
        (σ freq : JointReconstructionLabel → Slot → ℝ)
        (θ : JointReconstructionLabel → Slot → RayQuotient.Characters M H)
        (slotWidth : JointReconstructionLabel → Slot → ℝ),
      (∀ v ∈ S, (∀ j, (s v).input.M j ≤ Mslot) ∧ (s v).input.upper ≤ upper ∧
        (s v).input.b₁ ≤ b₁ ∧ (s v).input.b₂ ≤ b₂plain) →
      (∀ v ∈ S, (∀ j, (s v).input.lo j = lo j) ∧ (∀ j, (s v).input.hi j = hi j)) →
      (∀ x∈X, ∃ rows : Finset O,
        activePhysicalRows
          (parent input puncture seed K₁ radius side x.1) (height x.1)
          (columns input puncture seed K₁ radius side x.1) (beta input puncture seed K₁ radius side x.1)
          Wkernel (K x.1) (Radius x.1) (Height x.1) x.2.1 rows ≠ 0) →
      ∀ Bmask : ℝ, W+Bmask+conductorReserve ≤ d →
      (∀ v ∈ S, (((first v).leftPuncture (s v)).radical.absNorm : ℝ) ≤ Z^Bmask ∧
        (((first v).rightPuncture (s v)).radical.absNorm : ℝ) ≤ Z^Bmask) →
      (∀ v ∈ S, (s v).input.W₁ = W₁ ∧ (s v).input.W₂ = W₂) →
      (∀ v ∈ S, CenteredMomentAllocatedRayDictionary.Matches M H hH (s v).input
        ηcommon (θ v) (slotWidth v) (σ v) (freq v) Wslot bslot Z) →
      (∀ v ∈ S, (s v).input.X₁ ≤ (Z^d)^Rwidth ∧ (s v).input.X₂ ≤ (Z^d)^Rwidth ∧
        (s v).input.Y₁ ≤ (Z^d)^Rwidth ∧ (s v).input.Y₂ ≤ (Z^d)^Rwidth) →
      (∀ v ∈ S, ∀ j, 1 ≤ (s v).input.P j ∧ (s v).input.P j ≤ (Z^d)^Rwidth) →
      (∀ q ∈ qs, ∀ b : q.val.DyadicFiber (Kfirst q) (Rfirst q) (Hfirst q) (Ksecond q) (Rsecond q) (Hsecond q), good q b →
        t q b.1 = tbase q b.1+2*Real.pi*(firstU q b.1-firstTheta q b.1)) →
      (∀ q ∈ qs, ∀ b : q.val.DyadicFiber (Kfirst q) (Rfirst q) (Hfirst q) (Ksecond q) (Rsecond q) (Hsecond q), good q b →
        |tbase q b.1| ≤ Z^ν ∧ |firstU q b.1| ≤ Z^ν ∧ |firstTheta q b.1| ≤ Z^ν) →
      (∀ v ∈ S, ∀ j, σmin ≤ σ v j ∧ σ v j ≤ σmax) →
      (∀ v ∈ S, ∀ j, |freq v j| ≤ Z^ν) →
      ∀ (A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ : ℝ),
      2*b₂ = c₂+d₂ →
      ∀ supportLoss clipLoss commonLoss : ℝ, supportLoss+clipLoss+commonLoss ≤ lengthLoss →
      (∀ v ∈ S, CenteredMomentExceptionalAmplitudePair.volume (s v).input.toData ≤ Z^A) →
      (∀ v ∈ S, Z^(c+c₂-commonLoss) ≤ (((s v).firstCommon*(s v).second.val.1).absNorm : ℝ) ∧
        Z^(c+d₂-commonLoss) ≤ (((s v).firstCommon*(s v).second.val.2).absNorm : ℝ)) →
      (∀ v ∈ S, (max 1 (s v).input.upper)^Fintype.card Slot ≤ Z^supportLoss) →
      Real.logb Z (max 1 b₁*max 1 b₂plain) ≤ clipLoss →
      67/100 ≤ 2*p.lower-1 → 2*p.lower-1 ≤ 3/4 → A ≤ 883/1000 →
      0 ≤ π → π ≤ c → π ≤ d₁ → R₁ ≤ π →
      0 ≤ R₀ → 0 ≤ E → 0 ≤ Bc → L ≤ 5*(R₁-R₀) →
      0 ≤ b₂ → g₂ ≤ b₂ → 0 ≤ t₂cost → 0 ≤ geometryLoss → 0 ≤ lengthLoss →
      W ≤ 1-R₁-max (c-d₁) 0+L-6*(3/500)+geometryLoss → P ≤ π-R₁-E+R₀+missingLoss →
      omegaLoss+fiberLoss+loss+heightLoss+geometryLoss+lengthLoss+missingLoss ≤ 144011/109800000 →
      A-min c d₁+R₁+E-1+5*(3/500)+g₂-t₂cost-b₂+omegaLoss ≤ tailA →

      targetLower ≤ π+A-c+R₁+E+Bc-144011/109800000 →
      ∀ scalarLoss : ℝ,
      (∀ q ∈ qs, ∀ b : q.val.DyadicFiber (Kfirst q) (Rfirst q) (Hfirst q) (Ksecond q) (Rsecond q) (Hsecond q), good q b →
        Ksecond q b.1 ≤ Z^(2*A-c-d₁+R₁+E-1+max (d₁-c) 0+6*(3/500)+(omegaLoss-scalarLoss))) →
      (∀ v ∈ S, (s v).secondLogCost Z ≤ g₂-t₂cost-b₂+scalarLoss) →
      ∀ (rowc rowd rowR rowe rowomega rowL sourceLoss subsetLoss ξ
        pMissing rMissing eMissing cancelMissing : ℝ),
      sourceRadius input ≤ Z^(A+sourceLoss) →
      1-rowR-max (rowc-rowd) 0+rowL-6*(3/500)-rowomega+
        2*sourceLoss+subsetLoss+ξ/2+rowAbsorb ≤ W →
      pMissing-rMissing-eMissing+cancelMissing ≤ P →
      (∀ q ∈ qs, Z^rowc ≤ (q.label.C₁.absNorm : ℝ) ∧
        normValue (primeSubsetGenerator (fun P : CommonIndex q.label.C₁ q.label.D₁ => P.val) q.label.E) ≤ Z^(rowe+subsetLoss) ∧
        normValue (leftEffectiveFactor q.label.C₁ q.label.D₁) ≤ Z^rowL ∧
        Z^rMissing ≤ normValue (activeConductor q.label.C₁ q.label.D₁) ∧
        Z^eMissing ≤ normValue (primeSubsetGenerator (fun P : CommonIndex q.label.C₁ q.label.D₁ => P.val) q.label.E) ∧
        ((commonRadical q.label.C₁ q.label.D₁).absNorm : ℝ) ≤ Z^pMissing ∧
        ((canceledIdeal q.label.C₁ q.label.D₁ 5).absNorm : ℝ) ≤ Z^cancelMissing) →
      (∀ q ∈ qs, ∃ n₁ : q.val.FirstDyadic (Kfirst q) (Rfirst q) (Hfirst q),
        Z^(2*A-rowc-rowd+rowR+rowe-1+max (rowd-rowc) 0+6*(3/500)+rowomega) ≤ Ksecond q n₁ ∧
        Rsecond q n₁ = frequencyRadius
          ((sourceRadius input/(q.label.C₁.absNorm : ℝ))^2/Ksecond q n₁) Z ξ ∧
        q.val.z ∈ ActualJointSourceRow.liveFrequencyRows q.val.second.val.1 q.val.second.val.2
          q.val.U (Rsecond q n₁)) →
      ∀ volumeLoss : ℝ,
      Z^(A-volumeLoss) ≤ CenteredMomentExceptionalAmplitudePair.volume input.toData →
      (∑ x∈rayPackets X ξ₁ ξ₂,
        packetValue hseed hz₁ hz₂ (CenteredMomentExceptionalAmplitudePair.volume input.toData)
          (actualHighPrimeCount M H Sbad Z) height Wkernel x) ≤
        C*Z^(π+A-2*c+R₁+E+Bc+volumeLoss-144011/219600000+dyadicLoss) := by
  obtain ⟨profileBound,hprofile,τ,ν,orders,N,Nkernel,C,hν,hντ,hτdet,hheight,horders,hC,hhigh⟩ :=
    actual_joint_high_source_geometry η η₀ Q hQtop hQ72 hQη hβ M H hH hQM hQη₀ S₀
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB hβupper
      V Aprofile Bprofile hA hVs hV ηcommon hanchor Wslot hVslot bslot hBslot
      Rwidth dmax ε e κ ηaux σmin σmax productLoss populationLoss loss B
      hRw hdmax hε he he' hκ hκone hη hbudget hprimebudget hproductLoss hpopulationLoss hB hloss
      τdetector dmin heightLoss I hτdetector hdmin hheightLoss
      W₁ W₂ a₁ b₁ a₂ b₂plain ha₁ ha₂ hs₁ hW₁ hs₂ hW₂ lo hi fiberLoss hfiberLoss
      aSource Mslot upper haSource hMslot conductorReserve hconductorReserve
      Sbad primeLoss hprimeLoss hprimeReserve Wkernel tailA targetLower plainBound₁ plainBound₂
      hplainBound₁ hplainBound₂ hplainNorm₁ hplainNorm₂
      Bdyad₁ Ldyad₁ Crdyad₁ Bdyad₂ Ldyad₂ Crdyad₂ dyadicLoss
      hBdyad₁ hLdyad₁ hCrdyad₁ hBdyad₂ hLdyad₂ hCrdyad₂ hdyadicLoss
      rowAbsorb hrowAbsorb haSource_eq
  refine ⟨profileBound,hprofile,τ,ν,orders,N,Nkernel,C,hν,hντ,hτdet,hheight,horders,hC,?_⟩
  filter_upwards [hhigh] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro d P W hd hdmax' hbase hT hPB hWB p hp i hi hheightBin
    input puncture seed hpuncture hseed hz₁ hz₂ hinputη side ξ₁ ξ₂ fallback
    K₁ radius fallbackFirst K Radius Height X hzero
    qs Kfirst Rfirst Hfirst Ksecond Rsecond Hsecond good S w s first
    R hR hbin hsourceRadius hfirstDyadic hsecondDyadic
    height t tbase firstU firstTheta σ freq θ slotWidth
    hprofileCaps hsourceIntervals hphysicalX
    Bmask hconductorBalance hmaskNorm hplain hmatch
    hscale hprimeScale hteq hinputfreq hσrange hslotfreq
    A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ hb₂
    supportLoss clipLoss commonLoss hlengthLossSplit hvolume hcommonDyads hsupport hclip
    hδ hδtop hAtop hp₀ hpc hpd hRp hR₀ hE hBc hL hb₂₀ hg₂ ht₂
    hgeometryLoss hlengthLoss hW hP htotal htailA htarget scalarLoss hKactual hcost
    rowc rowd rowR rowe rowomega rowL sourceLoss subsetLoss ξ
    pMissing rMissing eMissing cancelMissing hsourceRow hrowBudget hmissingBudget
    hfirstGeometry hrowSupport volumeLoss hVolumeLower
  have hprojSource : ∀ q∈qs, Squarefree q.val.L := fun q hq =>
    (rayRows_first_gates fallbackFirst X hzero ξ₁ ξ₂ q hq).1
  have hprincipal : ∀ q∈qs, q.val.E ∈ (principalSupport Finset.univ
      (leftExponent q.val.first.val.1 q.val.first.val.2)
      (rightExponent q.val.first.val.1 q.val.first.val.2)).powerset := fun q hq =>
    (rayRows_first_gates fallbackFirst X hzero ξ₁ ξ₂ q hq).2
  have hphysicalSource : ∀ q∈qs, ∀ b : q.val.DyadicFiber
      (Kfirst q) (Rfirst q) (Hfirst q) (Ksecond q) (Rsecond q) (Hsecond q), good q b →
      ∃ rows : Finset O, physicalBlock (s q.label).parent (t q b.1)
        (s q.label).toKernelLabel.columns (s q.label).toKernelLabel.beta
        (s q.label).second.val.1 (s q.label).second.val.2
        (s q.label).toKernelLabel.hC (s q.label).toKernelLabel.hD (s q.label).partition
        (Rsecond q b.1) rows Wkernel (Ksecond q b.1) (fun j => b.2 j) ≠ 0 := by
    intro q hq b hg
    have hh := rayTarget_physical hseed hz₁ hz₂ fallbackFirst fallback X hzero ξ₁ ξ₂
      height Wkernel hphysicalX ⟨q,b⟩ hg
    have he : sourceKernel input puncture seed side hseed hz₁ hz₂ fallback input.η ξ₁ ξ₂⁻¹ 1 1 q.label = s q.label := by rw [hinputη]
    dsimp only at hh
    rw [he] at hh
    exact hh
  have hb := hZ.2 d P W hd hdmax' hbase hT hPB hWB p hp i hi hheightBin
    input puncture seed hpuncture hseed hz₁ hz₂ side ξ₁ ξ₂⁻¹ fallback qs
    R hR hprojSource hbin hsourceRadius
    Kfirst Rfirst Hfirst hfirstDyadic Ksecond Rsecond Hsecond hsecondDyadic
    t tbase firstU firstTheta good σ freq θ slotWidth
    hprofileCaps hsourceIntervals hphysicalSource
    Bmask hconductorBalance hmaskNorm hplain hmatch hscale hprimeScale
    hteq hinputfreq hσrange hslotfreq
    A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ hb₂
    supportLoss clipLoss commonLoss hlengthLossSplit hvolume hcommonDyads hsupport hclip
    hδ hδtop hAtop hp₀ hpc hpd hRp hR₀ hE hBc hL hb₂₀ hg₂ ht₂
    hgeometryLoss hlengthLoss hW hP htotal htailA htarget scalarLoss hKactual hcost
    rowc rowd rowR rowe rowomega rowL sourceLoss subsetLoss ξ
    pMissing rMissing eMissing cancelMissing hsourceRow hrowBudget hmissingBudget
    hprincipal hfirstGeometry hrowSupport volumeLoss hVolumeLower
  rw [sum_ray_fibers hseed hz₁ hz₂ fallbackFirst X hzero ξ₁ ξ₂]
  convert hb using 1
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro n₁ hn₁
  apply Finset.sum_congr rfl
  intro n₂ hn₂
  split_ifs with hg
  · exact (fiberValue_eq_high hseed hz₁ hz₂ fallbackFirst fallback ξ₁ ξ₂
      (CenteredMomentExceptionalAmplitudePair.volume input.toData) (actualHighPrimeCount M H Sbad Z)
      height Wkernel q ⟨n₁,n₂⟩).trans (by rw [hinputη])
  · rfl

end FixedData
#print axioms actual_joint_high_packet_geometry
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighPacketGeometry -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowLiteralRadius ; sha256 f824f67664766ab8574e6a77a54dbcea6c8184f3e1374d6966445260fdb619ce -/
section



/-! The original physical first radius and the coherent amplifier loss
satisfy the low endpoint's fixed scalar caps. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstScale
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentSourceInputFirstTailUniform CenteredMomentFirstAmplificationChoice
open CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def actualLowFirstRadius (src : Input ι) (R seed : Ideal O) (K Z ξ : ℝ)
    (p : Labels src R seed) (E : Finset (CommonIndex p.val.1 p.val.2)) : ℝ :=
  frequencyRadius (firstNominalScale p.val.1 p.val.2 (∏ P ∈ E,P.val) K (sourceRadius src)) Z ξ

lemma actualLowFirstRadius_le (src : Input ι) (R seed : Ideal O) (K Z ξ : ℝ)
    (hK : 1 ≤ K) (hZ : 1 < Z) (hξ : ξ ≤ 1)
    (hsource₀ : 0 ≤ sourceRadius src) (hsource : sourceRadius src ≤ Z^(1:ℝ)) :
    ∀ p E,actualLowFirstRadius src R seed K Z ξ p E ≤ 1*Z^(3:ℝ) := by
  intro p E
  have hz := zero_lt_one.trans hZ
  have hk : 0 < K := zero_lt_one.trans_le hK
  have hnom := first_nominal_scale_le p.val.1 p.val.2 E K (sourceRadius src) hk
  change firstNominalScale _ _ _ _ _*Z^(ξ/2) ≤ _
  calc
    _ ≤ ((sourceRadius src)^2/K)*Z^(ξ/2) :=
      mul_le_mul_of_nonneg_right hnom (Real.rpow_nonneg hz.le _)
    _ ≤ (sourceRadius src)^2*Z^(ξ/2) :=
      mul_le_mul_of_nonneg_right (div_le_self (sq_nonneg _) hK) (Real.rpow_nonneg hz.le _)
    _ ≤ (Z^(1:ℝ))^2*Z^(ξ/2) := by gcongr
    _ = Z^(2+ξ/2) := by
      rw [←Real.rpow_natCast (Z^(1:ℝ)) 2,←Real.rpow_mul hz.le,←Real.rpow_add hz]
      norm_num
    _ ≤ _ := by rw [one_mul]; exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)

def lowLiteralSupportConstant (N : ℕ) (upper b₁ b₂ : ℝ) : ℝ :=
  (max 1 upper)^N*max 1 b₁*max 1 b₂

def lowLiteralOmega (N : ℕ) (upper b₁ b₂ ξ reserve Z : ℝ) : ℝ :=
  frequencyLoss Z (32*(lowLiteralSupportConstant N upper b₁ b₂)^2) ξ+reserve

lemma eventually_low_literal_omega (N : ℕ) (upper b₁ b₂ ξ reserve : ℝ)
    (hξ : 0 < ξ) (hr : 0 ≤ reserve) (hbudget : ξ+reserve ≤ lowLocalTiny) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      0 ≤ lowLiteralOmega N upper b₁ b₂ ξ reserve Z ∧
      lowLiteralOmega N upper b₁ b₂ ξ reserve Z ≤ lowLocalTiny := by
  have hc : 1 ≤ lowLiteralSupportConstant N upper b₁ b₂ := by
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _)
  have hC : (1:ℝ) ≤ 32*(lowLiteralSupportConstant N upper b₁ b₂)^2 := by nlinarith
  filter_upwards [eventually_frequency_loss (32*(lowLiteralSupportConstant N upper b₁ b₂)^2) ξ hC hξ]
    with Z hZ
  refine ⟨hZ.1,?_,?_⟩ <;> dsimp only [lowLiteralOmega]
  · exact add_nonneg hZ.2.1 hr
  · linarith [hZ.2.2]

#print axioms actualLowFirstRadius_le
#print axioms eventually_low_literal_omega
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowLiteralRadius -/

/- BEGIN ORIGINAL MODULE Analytic.JointOriginalComparisonExplicitMesh ; sha256 f08081d822b02ee8192ced3ee2d79da047a9f08446670b8c834289a660efd568 -/
section




set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceLowBands CenteredMomentNaturalFixedRaySource
open CenteredMomentPrimeSlot QuadraticInitialBound CenteredMomentFiniteProfileExceptional
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance originalComparisonExplicitFinite : Finite (O⧸M):=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

/-- The comparison term for a fixed parent is supplied by the incumbent proof.
The new local window enters only through the direct/reflected comparison geometry. -/
theorem actual_local_comparison_energy_explicit_mesh
    (Wslot:ℝ→ℂ)(aslot bslot lo hi a b bΦ Bmask ε:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)
    (hcSlot:ContDiff ℝ ∞ Wslot)(hbslot:0≤ bslot)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hBmask:0≤ Bmask)(hε:0<ε)
    (hbeta:51/100≤ HeckeZeroSupremum.beta)(hbetaTop:HeckeZeroSupremum.beta≤7/8):
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),
    ∀ηfirst η₀:Character,∀Q:Ideal O,Q≤ M → internalQ Q η₀≠0 → internalQ Q η₀≠⊤ →
      internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤ w i) → (∀i,w i≤ meshGuaranteed Bmask ε) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) →
      ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=internalQ Q η₀ →
        s.character=ηfirst → s.rowWidth=1 →
        s.characterWidth=Real.logb Z (ηfirst.modulus.absNorm:ℝ) →
      ∀W₁ W₂:𝓢(ℝ,ℂ),Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
        Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀X₁ X₂:ℝ,1≤ X₁ → 1≤ X₂ → X₁≤ Z^(1/4:ℝ) → X₂≤ Z^(3/5:ℝ) →
      (∑i,w i)≤37/1000 →
      energy s.character s.mask 1 t W₁ W₂
        (fun i=> primePool M H bslot (Z^(w i)))
        (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=> Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
      C*diagonalControl s.radial.profile*(sourceControl U W₁*sourceControl U W₂)^2*
        (1+|t|+height)^J*Z^(1+ε):=by
  obtain ⟨d,xi,L,hd,hxi,hxicap,hL,hLcap,hpower⟩:=
    local_comparison_power_from_low (α:=α) M H hH Wslot aslot bslot lo hi
      haslot hsSlot hcSlot.continuous a b bΦ (1/10) (ε/2) 2 Bmask
      ha hlo hhi hbΦ (by norm_num) (by positivity) (by norm_num) hBmask (by norm_num)
  obtain ⟨degree,S,hinc⟩:=actual_incumbent_pair (α:=α) M H hH Wslot
    aslot bslot a b bΦ Bmask L lo hi 2 (ε/2) haslot hsSlot hcSlot hbslot
    ha hlo hhi hbΦ hBmask (by norm_num) (by positivity) hbeta hbetaTop
  obtain ⟨J,U,Cpower,hCp,hpower⟩:=hpower degree S
  let mesh:=Cycle25.Energy.commonMesh 2 Bmask L (ε/2)
  have hmesh:0< mesh:=Cycle25.Energy.commonMesh_pos 2 Bmask L (ε/2)
    (by norm_num) hBmask (by positivity)
  have hguarantee : meshGuaranteed Bmask ε ≤ mesh :=
    meshGuaranteed_le_comparison Bmask ε L hBmask hε (by linarith only [hLcap])
  refine ⟨J,U,?_⟩
  intro ηfirst η₀ Q hQM hQzero hQtop hQ72
  obtain ⟨Czero,K,hCzero,hK,hinc⟩:=hinc η₀ Q hQM hQzero hQtop hQ72
  have hη:0<(ηfirst.modulus.absNorm:ℝ):=
    CenteredMomentFirstScale.norm_pos _ ηfirst.modulus_ne_bot
  refine ⟨Cpower*(K+1)*(ηfirst.modulus.absNorm:ℝ),by positivity,?_⟩
  filter_upwards [hpower,hinc,eventually_fixed_logb_le (ηfirst.modulus.absNorm:ℝ) (1/100) hη (by norm_num)]
    with Z hp hiZ hfixed
  refine ⟨hp.1,?_⟩
  intro θ w σ freq t height hw hwmesh hσlo hσhi hh hf s hQ hchar hrow hwidth
    W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hslots
  have hslo:1≤ s.width:=by
    unfold NaturalState.width
    rw [hrow]
    linarith [s.character_nonneg]
  have hshi:s.width≤101/100:=by
    unfold NaturalState.width
    rw [hrow,hwidth]
    linarith [hfixed.2]
  have hlow:PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L mesh lo hi
      2 (ε/2) (3/4) Z η₀ Q degree S K:=by
    intro T θ w σ v t height hw hwL hσlo hσhi hh hv s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcapacity _
    exact hiZ.2.2 T θ w σ v t height hw hwL hσlo hσhi hh hv s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcapacity
  have hbound:=hp.2 (ε/2) mesh (3/4) η₀ Q K (by positivity) hK.le hlow
    θ w σ freq t height hw (fun i => (hwmesh i).trans hguarantee) hσlo hσhi hh hf rfl
    s hQ hslo hshi (by linarith) W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hslots
  have hz:0< Z:=zero_lt_one.trans hp.1
  have hpow:Z^(s.width+ε/2+ε/2)=(ηfirst.modulus.absNorm:ℝ)*Z^(1+ε):=by
    have he:s.width+ε/2+ε/2=Real.logb Z (ηfirst.modulus.absNorm:ℝ)+(1+ε):=by
      unfold NaturalState.width
      rw [hrow,hwidth]
      ring
    rw [he,Real.rpow_add hz,Real.rpow_logb hz hp.1.ne' hη]
  apply hbound.trans_eq
  rw [hpow]
  ring

#print axioms actual_local_comparison_energy_explicit_mesh
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointOriginalComparisonExplicitMesh -/
