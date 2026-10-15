/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B104
import Submissions.local44_20261013.Bundles.B108
import Submissions.local44_20261013.Bundles.B109
import Submissions.local44_20261013.Bundles.B111
import Submissions.local44_20261013.Bundles.B112
import Submissions.local44_20261013.Bundles.B113
import Submissions.local44_20261013.Bundles.B114
import Submissions.local44_20261013.Bundles.B116
import Submissions.local44_20261013.Bundles.B117
import Submissions.local44_20261013.Bundles.B118
import Submissions.local44_20261013.Bundles.B119

/- BEGIN ORIGINAL MODULE Analytic.JointHighPacketRecoveryGates ; sha256 6662acac3a4bbd2c444a312142f9ca41c36ebc51413ec3e4a423bd13a3afb598 -/
section




/-! Exact recovery of the first supported source label on good packet fibers,
and the actual first/second dyadic and Fourier-height gates. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
local notation "O"=> HeckeFamily.O
variable {ι κ:Type*}[Fintype ι][DecidableEq ι][DecidableEq κ]
namespace ActualFirstSecondSource
variable {src:Input ι}{R seed:Ideal O}{Kfirst:ℝ}
  {radius:(p:Labels src R seed)→Finset (CommonIndex p.val.1 p.val.2)→ℝ}
  {side:Bool}{K Radius H:First src R seed Kfirst radius→ℝ}

lemma packet_first_mem
    (labels:Finset (FirstSourceOuterIndex src R seed Kfirst radius))
    (rows:(k:First src R seed Kfirst radius)→Blocks src R seed Kfirst radius side K Radius H k→Finset O)
    (x:Packet src R seed Kfirst radius side K Radius H)
    (hx:x∈packets src R seed Kfirst radius side K Radius H labels rows):
    x.1∈firstSideSourceLabels labels (firstSourceOuterLabel src R seed Kfirst radius)
      (fun _=> sourceRadius src) side:=
  (Finset.mem_sigma.mp hx).1

lemma packet_outer_mem
    (labels:Finset (FirstSourceOuterIndex src R seed Kfirst radius))
    (rows:(k:First src R seed Kfirst radius)→Blocks src R seed Kfirst radius side K Radius H k→Finset O)
    (x:Packet src R seed Kfirst radius side K Radius H)
    (hx:x∈packets src R seed Kfirst radius side K Radius H labels rows):x.1.1∈labels:=by
  have hk:=packet_first_mem labels rows x hx
  cases side <;> exact (Finset.mem_sigma.mp (Finset.mem_filter.mp hk).1).1

lemma rayTarget_first_mem (fallback:First src R seed Kfirst radius)
    (labels:Finset (FirstSourceOuterIndex src R seed Kfirst radius))
    (rows:(k:First src R seed Kfirst radius)→Blocks src R seed Kfirst radius side K Radius H k→Finset O)
    (X:Finset (Packet src R seed Kfirst radius side K Radius H))
    (hX:X⊆packets src R seed Kfirst radius side K Radius H labels rows)
    (hzero:∀x∈X,(row x).z≠0)(χ ξ:RayCharacter)
    (y:FiberTarget fallback χ ξ K Radius H side)(hy:y∈rayTarget fallback X hzero χ ξ):
    firstAt fallback y.1.val χ ξ y.2.1∈firstSideSourceLabels labels
      (firstSourceOuterLabel src R seed Kfirst radius) (fun _=> sourceRadius src) side:=by
  obtain ⟨x,hx,hχ,hξ,hz,rfl⟩:=mem_rayTarget_witness fallback X hzero χ ξ y hy
  subst χ;subst ξ
  simpa only [liftPacket,firstAt_packet] using packet_first_mem labels rows x (hX hx)

/-- All first dyadic representatives of an actual ray row have the literal
second scale/radius caps; the good predicate is not needed for these caps. -/
theorem rayRows_main_dyadic_caps (fallback:First src R seed Kfirst radius)
    (X:Finset (Packet src R seed Kfirst radius side K Radius H))
    (hzero:∀x∈X,(row x).z≠0)(χ ξ:RayCharacter)
    (Z A omega ξamp:ℝ)(hZ:1< Z)(hA:0≤ A)(homega:0≤ omega)(hξ:ξamp≤1)
    (hsource₀:0< sourceRadius src)(hsource:sourceRadius src≤ Z^(1:ℝ))
    (hs:Squarefree seed)(hz₁:src.W₁ 0=0)(hz₂:src.W₂ 0=0)
    (q:NonzeroJointSourceRow (original src R seed) side)(hq:q∈rayRows fallback X hzero χ ξ)
    (n:q.val.FirstDyadic Kfirst (radius q.val.first q.val.E) (sourceRadius src)):
    0< secondScale fallback (mainScale src R seed Kfirst radius side Z A 1 omega) χ ξ q.val n ∧
    secondScale fallback (mainRadius src R seed Kfirst radius side Z A 1 omega ξamp) χ ξ q.val n≤1*Z^(6:ℝ) ∧
    0< secondScale fallback (mainHeight src R seed Kfirst radius side) χ ξ q.val n ∧
    secondScale fallback (mainHeight src R seed Kfirst radius side) χ ξ q.val n≤ Z^(1:ℝ):=by
  obtain ⟨x,hx,hχ,hξ,hrow⟩:=mem_rayRows_witness fallback X hzero χ ξ q hq
  rcases q with ⟨q,hqzero⟩
  change row x=q at hrow
  subst q;subst χ;subst ξ
  exact recovered_main_dyadic_caps fallback x Z A omega ξamp hZ hA homega hξ
    hsource₀ hsource hs hz₁ hz₂ n

lemma literal_first_dyadic_caps (src:Input ι)(R seed:Ideal O)(Z ξamp:ℝ)
    (hZ:1< Z)(hξ:ξamp≤1)(hsource₀:0< sourceRadius src)(hsource:sourceRadius src≤ Z^(1:ℝ))
    (side:Bool)(q:NonzeroJointSourceRow (original src R seed) side):
    0< Z ∧ 0< sourceRadius src ∧
    actualLowFirstRadius src R seed Z Z ξamp q.val.first q.val.E≤1*Z^(3:ℝ) ∧
    sourceRadius src≤ Z^(1:ℝ):=by
  exact ⟨zero_lt_one.trans hZ,hsource₀,
    actualLowFirstRadius_le src R seed Z Z ξamp hZ.le hZ hξ hsource₀.le hsource _ _,hsource⟩

variable (src R seed Kfirst radius side)(Z A M omega ξamp:ℝ)
  (hs:Squarefree seed)(hz₁:src.W₁ 0=0)(hz₂:src.W₂ 0=0)
  (bin:NonzeroElement→Option κ)(b:κ)
  (height:First src R seed Kfirst radius→ℝ)(W:𝓢(ℝ,ℂ))
  (labels:Finset (FirstSourceOuterIndex src R seed Kfirst radius))

lemma live_rayTarget_first_mem (fallback:First src R seed Kfirst radius)
    (X:Finset (LivePacket src R seed Kfirst radius side Z A M omega ξamp))
    (hX:X⊆liveBinPackets src R seed Kfirst radius side Z A M omega ξamp hs hz₁ hz₂ bin b height W labels)
    (hzero:∀x∈X,(row x).z≠0)(χ ξ:RayCharacter)
    (y:FiberTarget fallback χ ξ (mainScale src R seed Kfirst radius side Z A M omega)
      (mainRadius src R seed Kfirst radius side Z A M omega ξamp)
      (mainHeight src R seed Kfirst radius side) side)
    (hy:y∈rayTarget fallback X hzero χ ξ):
    firstAt fallback y.1.val χ ξ y.2.1∈firstSideSourceLabels labels
      (firstSourceOuterLabel src R seed Kfirst radius) (fun _=> sourceRadius src) side:=
  rayTarget_first_mem fallback labels
    (liveBinRows src R seed Kfirst radius side Z A M omega ξamp hs hz₁ hz₂ bin b height W)
    X hX hzero χ ξ y hy

/-- The Fourier constructor may take its base to be the already shifted first
source height, with the two extra coordinates zero. Its cube bound is inherited
from the original supported first-source domain only on actual good fibers. -/
theorem live_rayTarget_fourier_gates (fallback:First src R seed Kfirst radius)
    (X:Finset (LivePacket src R seed Kfirst radius side Z A M omega ξamp))
    (hX:X⊆liveBinPackets src R seed Kfirst radius side Z A M omega ξamp hs hz₁ hz₂ bin b height W labels)
    (hzero:∀x∈X,(row x).z≠0)(χ ξ:RayCharacter)(ν:ℝ)(hZ:0≤ Z)
    (hheight:∀k∈firstSideSourceLabels labels (firstSourceOuterLabel src R seed Kfirst radius)
      (fun _=> sourceRadius src) side,|height k|≤ Z^ν)
    (y:FiberTarget fallback χ ξ (mainScale src R seed Kfirst radius side Z A M omega)
      (mainRadius src R seed Kfirst radius side Z A M omega ξamp)
      (mainHeight src R seed Kfirst radius side) side)
    (hy:y∈rayTarget fallback X hzero χ ξ):
    height (firstAt fallback y.1.val χ ξ y.2.1)=
      height (firstAt fallback y.1.val χ ξ y.2.1)+2*Real.pi*(0-0) ∧
    |height (firstAt fallback y.1.val χ ξ y.2.1)|≤ Z^ν ∧ |(0:ℝ)|≤ Z^ν ∧ |(0:ℝ)|≤ Z^ν:=by
  have hm:=live_rayTarget_first_mem src R seed Kfirst radius side Z A M omega ξamp
    hs hz₁ hz₂ bin b height W labels fallback X hX hzero χ ξ y hy
  exact ⟨by ring,hheight _ hm,by simpa using Real.rpow_nonneg hZ ν,by simpa using Real.rpow_nonneg hZ ν⟩

#print axioms rayTarget_first_mem
#print axioms rayRows_main_dyadic_caps
#print axioms live_rayTarget_fourier_gates
end ActualFirstSecondSource
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighPacketRecoveryGates -/

/- BEGIN ORIGINAL MODULE Analytic.JointHighPacketCanonicalGates ; sha256 dc8b4c4d80176b7c87df48b0821f3f90f13bbd5c67f9a4379bc06242bd5b4492 -/
section





/-! Canonical source-image geometry inherited from literal packet cells.
The source mask bounds also hold at the harmless extension fallback. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentCanonicalFirst CenteredMomentExceptionalAmplitudePair
open CenteredMomentSectorLocalization
open CenteredMomentFirstSourceConductorCaps CenteredMomentCompleteCommon
open CenteredMomentRankinRadical CanonicalRowCompletion ConcretePrimeRowBridge
open NonzeroJointSourceRow ActualEisensteinCubic
local notation "O" => HeckeFamily.O
variable {Slot κ : Type*} [Fintype Slot] [DecidableEq Slot] [DecidableEq κ]

theorem canonical_source_mask_caps
    (src : Input Slot) (R seed : Ideal O) (side : Bool)
    (hs : Squarefree seed) (hz₁ : src.W₁ 0=0) (hz₂ : src.W₂ 0=0)
    (fallback : NonzeroJointSourceRow (original src R seed) side)
    (η : Character) (χ ξ : RayCharacter) (Z BR : ℝ) (hZ : 1 < Z)
    (hR : R ≠ 0) (hRN : (R.absNorm : ℝ) ≤ Z^BR)
    (hsource : sourceRadius src ≤ Z^(1:ℝ)) :
    ∀ v : JointReconstructionLabel,
      (((sourceFirst fallback η χ ξ v).leftPuncture
        (sourceKernel src R seed side hs hz₁ hz₂ fallback η χ ξ 1 1 v)).radical.absNorm : ℝ) ≤ Z^(BR+2) ∧
      (((sourceFirst fallback η χ ξ v).rightPuncture
        (sourceKernel src R seed side hs hz₁ hz₂ fallback η χ ξ 1 1 v)).radical.absNorm : ℝ) ≤ Z^(BR+2) := by
  intro v
  have hcap := actual_common_gates src R seed hs hz₁ hz₂
    (recover fallback v).val.first.val.1 (recover fallback v).val.first.val.2
    (recover fallback v).val.first.property
  exact (sourceFirst fallback η χ ξ v).high_puncture_caps
    (sourceKernel src R seed side hs hz₁ hz₂ fallback η χ ξ 1 1 v)
    hz₁ hz₂ Z BR hZ hR hRN (hcap.2.2.2.2.2.1.trans hsource) hsource

namespace ActualFirstSecondSource
variable (src : Input Slot) (R seed : Ideal O) (Kfirst : ℝ)
  (radius : (p : Labels src R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ)
  (side : Bool) (Z A M omega ξ : ℝ)
  (hs : Squarefree seed) (hz₁ : src.W₁ 0=0) (hz₂ : src.W₂ 0=0)
  (bin : NonzeroElement → Option κ) (b : κ)
  (t : First src R seed Kfirst radius → ℝ) (W : 𝓢(ℝ,ℂ))
  (labels : Finset (FirstSourceOuterIndex src R seed Kfirst radius))

theorem live_packet_outer_mem
    (x : LivePacket src R seed Kfirst radius side Z A M omega ξ)
    (hx : x∈liveBinPackets src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b t W labels) :
    x.1.1 ∈ labels := by
  have hh := (Finset.mem_sigma.mp hx).1
  cases side <;>
    simp only [firstSideSourceLabels,firstLeftSourceLabels,firstRightSourceLabels,
      firstSourceLabels,Finset.mem_filter,Finset.mem_sigma,Finset.mem_univ,
      and_true,Bool.false_eq_true,ite_false,ite_true] at hh
  all_goals exact hh.1

theorem packet_cell_first_norm_gates
    (X : Finset (LivePacket src R seed Kfirst radius side Z A M omega ξ))
    (hX : X⊆liveBinPackets src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b t W labels)
    (hzero : ∀ x∈X,(row x).z≠0)
    (fallback : First src R seed Kfirst radius) (χ₁ ξ₁ : RayCharacter)
    (ref : FirstJointLabel Slot) (e : ℝ) (hZ : 1 < Z)
    (hfull : ∀ i∈labels,∀ j,
      |(firstSourceOuterLabel src R seed Kfirst radius i).fullWidthCoordinates Z j-ref.fullWidthCoordinates Z j| < e) :
    ∀ q∈rayRows fallback X hzero χ₁ ξ₁,
      Z^(ref.sideWidth side Z-e) ≤ (q.label.C₁.absNorm : ℝ) ∧
      normValue (primeSubsetGenerator (fun P : CommonIndex q.label.C₁ q.label.D₁ => P.val) q.label.E) ≤ Z^(ref.punctureWidth Z+e) ∧
      normValue (leftEffectiveFactor q.label.C₁ q.label.D₁) ≤
        Z^(Real.logb Z (normValue (leftEffectiveFactor (ref.sideCommon side) (ref.sideCommon (!side))))+e) ∧
      Z^(ref.activeWidth Z-e) ≤ normValue (activeConductor q.label.C₁ q.label.D₁) ∧
      Z^(ref.punctureWidth Z-e) ≤ normValue (primeSubsetGenerator
        (fun P : CommonIndex q.label.C₁ q.label.D₁ => P.val) q.label.E) ∧
      ((commonRadical q.label.C₁ q.label.D₁).absNorm : ℝ) ≤ Z^(ref.radicalWidth Z+e) ∧
      ((canceledIdeal q.label.C₁ q.label.D₁ 5).absNorm : ℝ) ≤
        Z^(Real.logb Z ((canceledIdeal (ref.sideCommon side) (ref.sideCommon (!side)) 5).absNorm : ℝ)+e) := by
  intro q hq
  obtain ⟨x,hx,hχ,hξ,hrow⟩ := mem_rayRows_witness fallback X hzero χ₁ ξ₁ q hq
  have hi := live_packet_outer_mem src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b t W labels x (hX hx)
  have hh := packet_first_norm_gates x ref Z e hZ (hfull _ hi)
  rw [hrow] at hh
  exact hh

theorem packet_cell_second_sector_gates
    (X : Finset (LivePacket src R seed Kfirst radius side Z A M omega ξ))
    (hX : X⊆liveBinPackets src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b t W labels)
    (hzero : ∀ x∈X,(row x).z≠0)
    (fallbackFirst : First src R seed Kfirst radius)
    (fallback : NonzeroJointSourceRow (original src R seed) side) (χ₁ ξ₁ : RayCharacter)
    (ref : FirstJointLabel Slot) (eFirst eSecond : ℝ) (hZ : 1 < Z) (heSecond : 0 ≤ eSecond)
    (hfull : ∀ i∈labels,∀ j,
      |(firstSourceOuterLabel src R seed Kfirst radius i).fullWidthCoordinates Z j-ref.fullWidthCoordinates Z j| < eFirst)
    (edge : Fin 4 → ℝ) (hedge : ∀ j,0 ≤ edge j)
    (hsector : ∀ v∈(rayRows fallbackFirst X hzero χ₁ ξ₁).image NonzeroJointSourceRow.label,∀ j,
      edge j ≤ (sourceKernel src R seed side hs hz₁ hz₂ fallback src.η χ₁ ξ₁⁻¹ 1 1 v).secondWidthCoordinates Z j ∧
      (sourceKernel src R seed side hs hz₁ hz₂ fallback src.η χ₁ ξ₁⁻¹ 1 1 v).secondWidthCoordinates Z j ≤ edge j+eSecond) :
    ∀ v∈(rayRows fallbackFirst X hzero χ₁ ξ₁).image NonzeroJointSourceRow.label,
      let s := sourceKernel src R seed side hs hz₁ hz₂ fallback src.η χ₁ ξ₁⁻¹ 1 1 v
      Z^(ref.sideWidth side Z+edge 0-eFirst) ≤ ((s.firstCommon*s.second.val.1).absNorm : ℝ) ∧
      Z^(ref.sideWidth side Z+edge 1-eFirst) ≤ ((s.firstCommon*s.second.val.2).absNorm : ℝ) ∧
      s.secondLogCost Z ≤ min (edge 2) ((edge 0+edge 1)/2)-edge 3-(edge 0+edge 1)/2+eSecond := by
  intro v hv
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨x,hx,hχ,hξ,hrow⟩ := mem_rayRows_witness fallbackFirst X hzero χ₁ ξ₁ q hq
  let s := sourceKernel src R seed side hs hz₁ hz₂ fallback src.η χ₁ ξ₁⁻¹ 1 1 q.label
  have hfirst : s.firstCommon = (firstSourceOuterLabel src R seed Kfirst radius x.1.1).sideCommon side := by
    dsimp only [s,sourceKernel,ActualJointSourceRow.kernelLabel]
    rw [recover_label,←hrow]
    cases side <;> rfl
  have hi := live_packet_outer_mem src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b t W labels x (hX hx)
  have hh := s.first_second_sector_gates (firstSourceOuterLabel src R seed Kfirst radius x.1.1)
    ref side Z eFirst eSecond hZ heSecond hfirst (hfull _ hi) edge hedge
    (hsector _ (Finset.mem_image.mpr ⟨q,hq,rfl⟩))
  exact hh.2.2.2.2.2.2.2

end ActualFirstSecondSource
#print axioms canonical_source_mask_caps
#print axioms ActualFirstSecondSource.packet_cell_first_norm_gates
#print axioms ActualFirstSecondSource.packet_cell_second_sector_gates
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighPacketCanonicalGates -/

/- BEGIN ORIGINAL MODULE Analytic.JointHighPacketScaleGates ; sha256 11b10e52b38874152f6c2eebe960a0055c1d4711854bbe726d1773105a7535d7 -/
section



/-! Main-scale sector gates on the exact transformed live packet image.
The retained-frequency witness and lower scale come from one actual packet. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
local notation "O"=> HeckeFamily.O
variable {ι κ:Type*}[Fintype ι][DecidableEq ι][DecidableEq κ]

lemma FirstJointLabel.main_widths_close_of_full (q ref:FirstJointLabel ι)(side:Bool)(Z e:ℝ)
    (h:∀j,|q.fullWidthCoordinates Z j-ref.fullWidthCoordinates Z j|< e):
    |q.sideWidth side Z-ref.sideWidth side Z|≤ e ∧
    |q.sideWidth (!side) Z-ref.sideWidth (!side) Z|≤ e ∧
    |q.activeWidth Z-ref.activeWidth Z|≤ e ∧
    |q.punctureWidth Z-ref.punctureWidth Z|≤ e:=by
  cases side
  · exact ⟨(h 1).le,(h 0).le,(h 3).le,(h 4).le⟩
  · exact ⟨(h 0).le,(h 1).le,(h 3).le,(h 4).le⟩

namespace ActualFirstSecondSource
variable (src:Input ι)(R seed:Ideal O)(Kfirst:ℝ)
  (radius:(p:Labels src R seed)→Finset (CommonIndex p.val.1 p.val.2)→ℝ)
  (side:Bool)(Z A M omega ξamp:ℝ)
  (hs:Squarefree seed)(hz₁:src.W₁ 0=0)(hz₂:src.W₂ 0=0)
  (bin:NonzeroElement→Option κ)(b:κ)
  (t:First src R seed Kfirst radius→ℝ)(W:𝓢(ℝ,ℂ))
  (labels:Finset (FirstSourceOuterIndex src R seed Kfirst radius))

theorem packet_cell_main_scale_upper
    (X:Finset (LivePacket src R seed Kfirst radius side Z A M omega ξamp))
    (hX:X⊆liveBinPackets src R seed Kfirst radius side Z A M omega ξamp hs hz₁ hz₂ bin b t W labels)
    (hzero:∀x∈X,(row x).z≠0)
    (fallback:First src R seed Kfirst radius)(χ ξ:RayCharacter)
    (ref:FirstJointLabel ι)(eFirst:ℝ)(hZ:1< Z)(heFirst:0≤ eFirst)
    (hfull:∀i∈labels,∀j,
      |(firstSourceOuterLabel src R seed Kfirst radius i).fullWidthCoordinates Z j-
        ref.fullWidthCoordinates Z j|< eFirst):
    ∀q∈rayRows fallback X hzero χ ξ,
    ∀n:q.val.FirstDyadic Kfirst (radius q.val.first q.val.E) (sourceRadius src),
      secondScale fallback (mainScale src R seed Kfirst radius side Z A M omega) χ ξ q.val n≤
      Z^(firstMainExponent A (ref.sideWidth side Z) (ref.sideWidth (!side) Z)
        (ref.activeWidth Z) (ref.punctureWidth Z) M (3/500) (omega+6*eFirst)):=by
  intro q hq n
  obtain ⟨x,hx,hχ,hξ,hrow⟩:=mem_rayRows_witness fallback X hzero χ ξ q hq
  have hi:=packet_outer_mem labels
    (liveBinRows src R seed Kfirst radius side Z A M omega ξamp hs hz₁ hz₂ bin b t W) x (hX hx)
  have hg:=(firstSourceOuterLabel src R seed Kfirst radius x.1.1).main_widths_close_of_full
    ref side Z eFirst (hfull _ hi)
  rcases q with ⟨q,hqzero⟩
  change row x=q at hrow
  subst q;subst χ;subst ξ
  exact (recovered_main_sector_bounds fallback x ref Z A M omega eFirst hZ heFirst
    hg.1 hg.2.1 hg.2.2.1 hg.2.2.2 n).1

/-- One genuine first dyadic representative supplies both the reference-sector
lower main scale and the retained row support at its actual residual radius. -/
theorem packet_cell_main_scale_frequency_witness
    (X:Finset (LivePacket src R seed Kfirst radius side Z A M omega ξamp))
    (hX:X⊆liveBinPackets src R seed Kfirst radius side Z A M omega ξamp hs hz₁ hz₂ bin b t W labels)
    (hzero:∀x∈X,(row x).z≠0)
    (fallback:First src R seed Kfirst radius)(χ ξ:RayCharacter)
    (ref:FirstJointLabel ι)(eFirst:ℝ)(hZ:1< Z)(heFirst:0≤ eFirst)
    (hfull:∀i∈labels,∀j,
      |(firstSourceOuterLabel src R seed Kfirst radius i).fullWidthCoordinates Z j-
        ref.fullWidthCoordinates Z j|< eFirst):
    ∀q∈rayRows fallback X hzero χ ξ,
    ∃n:q.val.FirstDyadic Kfirst (radius q.val.first q.val.E) (sourceRadius src),
      Z^(firstMainExponent A (ref.sideWidth side Z-eFirst) (ref.sideWidth (!side) Z-eFirst)
        (ref.activeWidth Z) (ref.punctureWidth Z) M (3/500) (omega-8*eFirst))≤
        secondScale fallback (mainScale src R seed Kfirst radius side Z A M omega) χ ξ q.val n ∧
      secondScale fallback (mainRadius src R seed Kfirst radius side Z A M omega ξamp) χ ξ q.val n=
        frequencyRadius ((sourceRadius src/(q.label.C₁.absNorm:ℝ))^2/
          secondScale fallback (mainScale src R seed Kfirst radius side Z A M omega) χ ξ q.val n) Z ξamp ∧
      q.val.z∈ActualJointSourceRow.liveFrequencyRows q.val.second.val.1 q.val.second.val.2 q.val.U
        (secondScale fallback (mainRadius src R seed Kfirst radius side Z A M omega ξamp) χ ξ q.val n):=by
  intro q hq
  obtain ⟨x,hx,hχ,hξ,hrow⟩:=mem_rayRows_witness fallback X hzero χ ξ q hq
  have hi:=packet_outer_mem labels
    (liveBinRows src R seed Kfirst radius side Z A M omega ξamp hs hz₁ hz₂ bin b t W) x (hX hx)
  have hg:=(firstSourceOuterLabel src R seed Kfirst radius x.1.1).main_widths_close_of_full
    ref side Z eFirst (hfull _ hi)
  rcases q with ⟨q,hqzero⟩
  change row x=q at hrow
  subst q;subst χ;subst ξ
  let n:(row x).FirstDyadic Kfirst (radius (row x).first (row x).E) (sourceRadius src):=x.1.1.2.2
  refine ⟨n,(recovered_main_sector_bounds fallback x ref Z A M omega eFirst hZ heFirst
    hg.1 hg.2.1 hg.2.2.1 hg.2.2.2 n).2,?_,?_⟩
  · rw [secondScale_mainRadius,secondScale_mainScale,mainRadius_actual,mainHeight_row]
    rfl
  · rw [secondScale_mainRadius]
    exact live_packet_frequency src R seed Kfirst radius side Z A M omega ξamp
      hs hz₁ hz₂ bin b t W labels x (hX hx)

#print axioms packet_cell_main_scale_upper
#print axioms packet_cell_main_scale_frequency_witness
end ActualFirstSecondSource
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighPacketScaleGates -/

/- BEGIN ORIGINAL MODULE Analytic.JointHighLiteralConstructor ; sha256 5ae16b520a8bbc838484a6dcb7f274c8c24e931092dc301502c49908364de082 -/
section





/-! The literal high packet is assembled from the original source and its
first and second sector coordinates. Every analytical field is supplied by
the genuine global bin classifier; no target estimate is assumed. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentCanonicalFirst CenteredMomentExceptionalAmplitudePair
open CenteredMomentSectorLocalization ConcretePrimeRowBridge
open CenteredMomentSecondHeightFamily CenteredMomentNaturalRowSource
open NonzeroJointSourceRow ActualFirstSecondSource
local notation "O" => HeckeFamily.O
variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
variable (modulus : Ideal O) [NeZero modulus]
local instance highLiteralConstructorFiniteQuotient : Finite (O ⧸ modulus) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne modulus)

 theorem actual_literal_high_packet_data
    (H : Subgroup (O ⧸ modulus)ˣ) (hH : RayOrthogonality.globalUnits modulus ≤ H)
    (η₀ : Character) (Q : Ideal O) (hQ72 : Q ≤ Ideal.span {(72:O)})
    (hQM : Q ≤ modulus) (hQη₀ : Q ≤ η₀.modulus)
    (Wslot : ℝ → ℂ) (bslot BR e σmin σmax : ℝ) (I : ℕ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂plain : ℝ) (lo hi : Slot → ℝ) (Mslot upper : ℝ)
    (Sbad : Finset (Ideal O)) (Wkernel : 𝓢(ℝ,ℂ))
    (src : Input Slot) (R seed : Ideal O) (hs : Squarefree seed)
    (hz₁ : src.W₁ 0=0) (hz₂ : src.W₂ 0=0)
    (Z τ ν A omega ξamp ξsecond eFirst eSecond : ℝ) (side : Bool)
    (hZ : 2 ≤ Z) (hτ : 2 < Z^τ) (hBR : 0 ≤ BR)
    (he : 0 < e) (heFirst : 0 ≤ eFirst) (heFirstCap : eFirst ≤ lowLocalTiny)
    (heSecond : 0 ≤ eSecond) (heSecondCap : eSecond ≤ lowLocalTiny)
    (hA₀ : 0 ≤ A) (hA : A ≤ 883/1000)
    (homega : 0 ≤ omega) (homegaCap : omega ≤ lowLocalTiny)
    (hξamp : ξamp ≤ 1) (hξsecond : 0 ≤ ξsecond) (hξsecondCap : ξsecond ≤ lowLocalTiny)
    (hR : R ≠ 0) (hRN : (R.absNorm : ℝ) ≤ Z^BR)
    (hsource₀ : 0 < sourceRadius src) (hsource : sourceRadius src ≤ Z^(1:ℝ))
    (hsourceA : sourceRadius src ≤ Z^(A+lowLocalTiny))
    (hvolume : volume src.toData = Z^A)
    (hprofile : src.W₁ = W₁ ∧ src.W₂ = W₂)
    (hbplain : src.b₁ ≤ b₁ ∧ src.b₂ ≤ b₂plain)
    (hM : ∀ j,src.M j ≤ Mslot) (hupper : src.upper ≤ upper)
    (hlo : ∀ j,src.lo j = lo j) (hhi : ∀ j,src.hi j = hi j)
    (hsupport : (max 1 src.upper)^Fintype.card Slot ≤ Z^lowLocalTiny)
    (hclip : Real.logb Z (max 1 b₁*max 1 b₂plain) ≤ 2*lowLocalTiny)
    (θ : Slot → RayQuotient.Characters modulus H) (w σ freq : Slot → ℝ)
    (hmatch : CenteredMomentAllocatedRayDictionary.Matches modulus H hH src
      η₀ θ w σ freq Wslot bslot Z)
    (hP : ∀ j,src.P j = Z^(w j)) (hw : ∀ j,0 ≤ w j)
    (hwcap : ∀ j,w j ≤ lowLocalMesh)
    (hX₁ : Real.logb Z src.X₁ ≤ 423/1000) (hX₂ : Real.logb Z src.X₂ ≤ 423/1000)
    (hY₁ : Real.logb Z src.Y₁ ≤ 1) (hY₂ : Real.logb Z src.Y₂ ≤ 1)
    (hσ : ∀ j,σmin ≤ σ j ∧ σ j ≤ σmax) (hfreq : ∀ j,|freq j| ≤ Z^ν)
    (bin : NonzeroElement → Option (Fin (I+1) × Fin (I+1)))
    (b : Fin (I+1) × Fin (I+1))
    (hbinLower : 167/200 ≤ 51/100+(e/2)*(b.2.val : ℝ))
    (hbinUpper : 51/100+(e/2)*(b.2.val : ℝ) ≤ 7/8)
    (hclass : ∀ w b,bin w = some b →
      ∀ (P : JointRelativeLabel src.η (Option (Slot × RayQuotient.Characters modulus H)) → Ideal O)
        (hP : ∀ label,P label ≠ 0),
        jointRelativeSourceZeroBin src.η (relativeSlotTranslate modulus H hH (fun _ : Slot => η₀))
          Q hQ72 (relativeSlotTranslate_fixedQ modulus H hH (fun _ : Slot => η₀) Q hQM
            (fun _ => hQη₀)) P hP
          (51/100+(e/2)*(b.2.val : ℝ)) (51/100+(e/2)*(b.2.val : ℝ)+e)
          ((3*(b.1.val+1):ℕ)*Z^τ) w)
    (height : First src R seed Z (actualLowFirstRadius src R seed Z Z ξamp) → ℝ)
    (labels : Finset (FirstSourceOuterIndex src R seed Z (actualLowFirstRadius src R seed Z Z ξamp)))
    (hheight : ∀ k∈firstSideSourceLabels labels
      (firstSourceOuterLabel src R seed Z (actualLowFirstRadius src R seed Z Z ξamp))
      (fun _=> sourceRadius src) side,|height k| ≤ Z^ν)
    (ref : FirstJointLabel Slot)
    (hCref : (ref.C.absNorm : ℝ) ≤ Z^(1:ℝ)) (hDref : (ref.D.absNorm : ℝ) ≤ Z^(1:ℝ))
    (hfull : ∀ i∈labels,∀ j,
      |(firstSourceOuterLabel src R seed Z (actualLowFirstRadius src R seed Z Z ξamp) i).fullWidthCoordinates Z j-
        ref.fullWidthCoordinates Z j| < eFirst)
    (X : Finset (LivePacket src R seed Z (actualLowFirstRadius src R seed Z Z ξamp)
      side Z A 1 omega ξsecond))
    (hX : X ⊆ liveBinPackets src R seed Z (actualLowFirstRadius src R seed Z Z ξamp)
      side Z A 1 omega ξsecond hs hz₁ hz₂ bin b height Wkernel labels)
    (hzero : ∀ x∈X,(row x).z≠0)
    (fallbackFirst : First src R seed Z (actualLowFirstRadius src R seed Z Z ξamp))
    (fallback : NonzeroJointSourceRow (original src R seed) side) (χ₁ ξ₁ : RayCharacter)
    (edge : Fin 4 → ℝ) (hedge : ∀ j,0 ≤ edge j)
    (hsector : ∀ v∈(rayRows fallbackFirst X hzero χ₁ ξ₁).image NonzeroJointSourceRow.label,∀ j,
      edge j ≤ (sourceKernel src R seed side hs hz₁ hz₂ fallback src.η χ₁ ξ₁⁻¹ 1 1 v).secondWidthCoordinates Z j ∧
      (sourceKernel src R seed side hs hz₁ hz₂ fallback src.η χ₁ ξ₁⁻¹ 1 1 v).secondWidthCoordinates Z j ≤ edge j+eSecond) :
    ∃ exponent : ℝ, LocalHighPacketData modulus H hH src.η η₀ Q hQ72 hQM hQη₀
      Wslot bslot BR e σmin σmax I W₁ W₂ b₁ b₂plain lo hi Mslot upper Sbad Wkernel Z τ ν
      (∑ x∈rayPackets X χ₁ ξ₁,packetValue hs hz₁ hz₂ (volume src.toData)
        (actualHighPrimeCount modulus H Sbad Z) height Wkernel x) exponent ∧
      exponent ≤ ref.radicalWidth Z+A-2*ref.sideWidth side Z+ref.activeWidth Z+
        ref.punctureWidth Z+ref.sideAllowance side Z-1/10000 := by
  have hZ₁ : 1 < Z := by linarith only [hZ]
  have hd : 1 ≤ highLocalDmax BR := by dsimp only [highLocalDmax];linarith
  have hξ₂ : ξsecond ≤ 1 := by norm_num [lowLocalTiny] at hξsecondCap;linarith
  let c := ref.sideWidth side Z
  let d₁ := ref.sideWidth (!side) Z
  let π := ref.radicalWidth Z
  let R₁ := ref.activeWidth Z
  let R₀ := Real.logb Z ((canceledIdeal (ref.sideCommon side) (ref.sideCommon (!side)) 5).absNorm : ℝ)
  let E := ref.punctureWidth Z
  let Bc := ref.sideAllowance side Z
  let L := Real.logb Z (normValue (leftEffectiveFactor (ref.sideCommon side) (ref.sideCommon (!side))))
  let b₂ := (edge 0+edge 1)/2
  let g₂ := min (edge 2) b₂
  have hb₂ : 0 ≤ b₂ := by dsimp only [b₂];linarith [hedge 0,hedge 1]
  have gates := actual_high_reference_packet_gates ref side Z A BR eFirst eSecond omega ξsecond
    b₂ g₂ (edge 3) hZ₁ hCref hDref hA₀ hA hBR heFirst heFirstCap heSecond heSecondCap
    homega homegaCap hξsecond hξsecondCap hb₂ (min_le_right _ _) (hedge 3)
  let p : DensityWindow := ⟨51/100+(e/2)*(b.2.val:ℝ),51/100+(e/2)*(b.2.val:ℝ)+e,
    ((3*(b.1.val+1):ℕ):ℝ)*Z^τ,hbinLower,hbinUpper⟩
  have hscales := high_original_scale_caps src Z (highLocalDmax BR) w hZ₁ hd hP hw hwcap hX₁ hX₂ hY₁ hY₂
  have hbins := actual_packet_cell_relative_source_bin modulus H hH src R seed Z
    (actualLowFirstRadius src R seed Z Z ξamp) side Z A 1 omega ξsecond hs hz₁ hz₂ I bin b
    height Wkernel labels η₀ Q hQ72 hQM hQη₀ e (Z^τ) hclass X hX hzero fallbackFirst fallback
    χ₁ ξ₁ (fun _ _=>1) (fun _ _=> one_ne_zero)
  have hsecond := packet_cell_second_sector_gates src R seed Z
    (actualLowFirstRadius src R seed Z Z ξamp) side Z A 1 omega ξsecond hs hz₁ hz₂ bin b
    height Wkernel labels X hX hzero fallbackFirst fallback χ₁ ξ₁ ref eFirst eSecond hZ₁ heSecond
    hfull edge hedge hsector
  have hfirst := packet_cell_first_norm_gates src R seed Z
    (actualLowFirstRadius src R seed Z Z ξamp) side Z A 1 omega ξsecond hs hz₁ hz₂ bin b
    height Wkernel labels X hX hzero fallbackFirst χ₁ ξ₁ ref eFirst hZ₁ hfull
  have hupperK := packet_cell_main_scale_upper src R seed Z
    (actualLowFirstRadius src R seed Z Z ξamp) side Z A 1 omega ξsecond hs hz₁ hz₂ bin b
    height Wkernel labels X hX hzero fallbackFirst χ₁ ξ₁ ref eFirst hZ₁ heFirst hfull
  have hlowerK := packet_cell_main_scale_frequency_witness src R seed Z
    (actualLowFirstRadius src R seed Z Z ξamp) side Z A 1 omega ξsecond hs hz₁ hz₂ bin b
    height Wkernel labels X hX hzero fallbackFirst χ₁ ξ₁ ref eFirst hZ₁ heFirst hfull
  refine ⟨π+A-2*c+R₁+E+Bc+0-144011/219600000+lowLocalTiny,?_,?_⟩
  · unfold LocalHighPacketData HighPacketSourceData
    refine ⟨highLocalDmax BR,highPacketMissingWidth π R₁ E R₀ eFirst,
      highPacketRowWidth c d₁ R₁ L eFirst ξsecond,p,b.1.val,src,R,seed,hR,hs,hz₁,hz₂,rfl,side,
      χ₁,ξ₁,fallback,Z,actualLowFirstRadius src R seed Z Z ξamp,fallbackFirst,
      mainScale src R seed Z (actualLowFirstRadius src R seed Z Z ξamp) side Z A 1 omega,
      mainRadius src R seed Z (actualLowFirstRadius src R seed Z Z ξamp) side Z A 1 omega ξsecond,
      mainHeight src R seed Z (actualLowFirstRadius src R seed Z Z ξamp) side,
      X,hzero,(fun _ _=>1),(fun _ _=> one_ne_zero),height,
      (fun q n=> height (firstAt fallbackFirst q.val χ₁ ξ₁ n)),(fun _ _=>0),(fun _ _=>0),
      (fun _=>σ),(fun _=> freq),(fun _=>θ),(fun _=> w),BR+2,A,c,d₁,π,R₁,R₀,E,Bc,L,b₂,g₂,edge 3,
      highPacketOmegaLoss eFirst eSecond omega,highPacketGeometryLoss eFirst ξsecond,
      highPacketLengthLoss eFirst,4*eFirst,edge 0,edge 1,lowLocalTiny,2*lowLocalTiny,eFirst,eSecond,
      c-eFirst,d₁-eFirst,R₁,E,omega-8*eFirst,L+eFirst,lowLocalTiny,eFirst,ξsecond,
      π+eFirst,R₁-eFirst,E-eFirst,R₀+eFirst,0,?_,rfl,rfl⟩
    dsimp only
    refine ⟨hd,le_rfl,?_,hτ,?_,gates.row_cap,?_,Nat.le_of_lt_succ b.1.isLt,(by simp only [p,Nat.cast_mul,Nat.cast_ofNat]),
      hbins,?_,?_,?_,?_,?_,?_,gates.conductor,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,
      gates.length_split,?_,?_,?_,hclip,?_,?_,gates.A_cap,gates.p_nonneg,gates.p_le_c,
      gates.p_le_d,gates.R_le_p,gates.R₀_nonneg,gates.E_nonneg,gates.Bc_nonneg,
      gates.cancellation,gates.b_nonneg,gates.g_le_b,gates.t_nonneg,gates.geometry_nonneg,
      gates.length_nonneg,le_rfl,le_rfl,gates.total_budget,gates.tail_cap,gates.target_lower,
      ?_,?_,hsourceA,gates.row_budget,gates.missing_budget,hfirst,?_,?_⟩
    · exact hZ.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hZ₁.le hd)
    · exact gates.missing_cap.trans (by norm_num)
    · dsimp only [p];linarith
    · exact hsource.trans (Real.rpow_le_rpow_of_exponent_le hZ₁.le (by norm_num))
    · intro q hq
      exact literal_first_dyadic_caps src R seed Z ξamp hZ₁ hξamp hsource₀ hsource side q
    · intro q hq n
      have hh := rayRows_main_dyadic_caps fallbackFirst X hzero χ₁ ξ₁ Z A omega ξsecond hZ₁ hA₀ homega hξ₂
        hsource₀ hsource hs hz₁ hz₂ q hq n
      exact ⟨hh.1,hh.2.1,hh.2.2.2⟩
    · intro v hv;exact ⟨hM,hupper,hbplain.1,hbplain.2⟩
    · intro v hv;exact ⟨hlo,hhi⟩
    · exact live_subset_physical src R seed Z (actualLowFirstRadius src R seed Z Z ξamp)
        side Z A 1 omega ξsecond hs hz₁ hz₂ bin b height Wkernel labels X hX
    · intro v hv
      exact canonical_source_mask_caps src R seed side hs hz₁ hz₂ fallback src.η χ₁ ξ₁⁻¹ Z BR hZ₁ hR hRN hsource v
    · intro v hv;exact hprofile
    · intro v hv;exact hmatch
    · intro v hv;exact ⟨hscales.1,hscales.2.1,hscales.2.2.1,hscales.2.2.2.1⟩
    · intro v hv;exact hscales.2.2.2.2
    · intro q hq b hb;ring
    · intro q hq b hb
      exact (live_rayTarget_fourier_gates src R seed Z (actualLowFirstRadius src R seed Z Z ξamp)
        side Z A 1 omega ξsecond hs hz₁ hz₂ bin _ height Wkernel labels fallbackFirst X hX hzero
        χ₁ ξ₁ ν (by linarith only [hZ]) hheight ⟨q,b⟩ hb).2
    · intro v hv;exact hσ
    · intro v hv;exact hfreq
    · dsimp only [b₂];ring
    · intro v hv;exact hvolume.le
    · intro v hv;exact ⟨(hsecond v hv).1,(hsecond v hv).2.1⟩
    · intro v hv;exact hsupport
    · dsimp only [p];linarith
    · dsimp only [p];linarith
    · intro q hq b hb
      simpa only [firstMainExponent,highPacketOmegaLoss,add_sub_cancel_right] using hupperK q hq b.1
    · intro v hv;exact (hsecond v hv).2.2
    · exact hlowerK
    · simpa only [sub_zero] using hvolume.ge
  · have hh := gates.final_saving
    dsimp only [c,π,R₁,E,Bc]
    linarith

#print axioms actual_literal_high_packet_data
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighLiteralConstructor -/

/- BEGIN ORIGINAL MODULE Analytic.JointHighLiteralTarget ; sha256 80bcc7db2421a69860a6d0bd39040251586d529ade516c68e041ef2fad728e8f -/
section










/-! The fixed local high estimate: all numerical losses and Mellin budgets
are chosen before the live source. Only the literal source-data constructor
is used for each nonempty packet cell and first-ray pair. -/
set_option autoImplicit false
set_option maxRecDepth 8192
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
open CenteredMomentSupportedTailAggregate CenteredMomentSecondEnergySplit CenteredMomentFirstAmplificationChoice
open CenteredMomentExceptionalAmplitudePair EisensteinSchwartzPoisson
open CenteredMomentCanonicalFirst CenteredMomentActive CenteredMomentCompleteCommon
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondPhysicalBlock
open CenteredMomentSourceRow CenteredMomentSecondLiveBlock
open CanonicalRowCompletion CenteredMomentRankinRadical ActualEisensteinCubic
open ActualFirstSecondSource CenteredMomentFirstNonexceptionalWeightSum
open CenteredMomentSecondBlockHarmonicMass
open CenteredMomentFirstPhysicalDyadicAssembly
local notation "O" => HeckeFamily.O

section FixedData
variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot] [Nonempty Slot]
variable (η : Character) (η₀ : Character) (Q : Ideal O) [NeZero Q]
  (hQtop : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hQη : Q ≤ η.modulus)
  (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
  (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
  (hH : RayOrthogonality.globalUnits M ≤ H) (hQM : Q ≤ M)
  (hQη₀ : Q ≤ η₀.modulus)
  (S₀ : Finset (Ideal O))
  (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
  (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
  (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
  (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
  (hβupper : HeckeZeroSupremum.beta ≤ 7/8)
include hQtop hQ72 hQη hβ hH hQM hQη₀ S₀ hφ hφc hφp hφ0 hφne ha₀ hab₀ hB₀ hφs hφB hβupper

theorem actual_literal_high_bins_target
    (Wslot : ℝ → ℂ) (aslot bslot : ℝ) (haslot : 0 < aslot)
    (hWslot : ContDiff ℝ ∞ Wslot)
    (hslotSupport : Function.support Wslot ⊆ Icc aslot bslot)
    (BR e σmin σmax τdetector : ℝ) (I : ℕ)
    (hBR : 0 ≤ BR) (he : 0 < e) (hecap : e ≤ highLocalBinCap BR (Fintype.card Slot))
    (hτdetector : 0 < τdetector)
    (W₁ W₂ : ℝ → ℂ) (a₁ b₁ a₂ b₂plain : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hs₁ : Function.support W₁ ⊆ Icc a₁ b₁) (hW₁ : ContDiff ℝ ∞ W₁)
    (hs₂ : Function.support W₂ ⊆ Icc a₂ b₂plain) (hW₂ : ContDiff ℝ ∞ W₂)
    (lo hi : Slot → ℝ) (hlo : ∀ j,0 < lo j)
    (Mslot upper : ℝ) (hMslot : 0 ≤ Mslot)
    (Sbad : Finset (Ideal O)) :
    ∃ τ ν C : ℝ, 0 < ν ∧ ν < τ ∧ τ < τdetector ∧
      4*τ < highLocalEpsilon BR (Fintype.card Slot)/16 ∧ 0 < C ∧
      ∀ᶠ Z : ℝ in atTop, 2 ≤ Z ∧ 2 < Z^τ ∧
      ∀ (θ : Slot → RayQuotient.Characters M H) (w σ freq : Slot → ℝ),
      (∀ i,0 ≤ w i) → (∀ i,w i ≤ lowLocalMesh) →
      (∀ i,σmin ≤ σ i ∧ σ i ≤ σmax) → (∀ i,|freq i| ≤ Z^ν) →
      ∀ (src : Input Slot),
      CenteredMomentAllocatedRayDictionary.Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
      src.η = η → src.W₁ = W₁ → src.W₂ = W₂ →
      (∀ i,src.M i ≤ Mslot) → src.upper ≤ upper →
      (∀ i,src.lo i = lo i) → (∀ i,src.hi i = hi i) →
      (∀ i,|src.hi i| ≤ upper) → |src.b₁| ≤ b₁ → |src.b₂| ≤ b₂plain →
      Real.logb Z src.X₁ ≤ 423/1000 → Real.logb Z src.X₂ ≤ 423/1000 →
      Real.logb Z src.Y₁ ≤ 1 → Real.logb Z src.Y₂ ≤ 1 →
      0 < sourceRadius src →
      0 ≤ Real.logb Z (CenteredMomentExceptionalAmplitudePair.volume src.toData) →
      Real.logb Z (CenteredMomentExceptionalAmplitudePair.volume src.toData) ≤ 883/1000 →
      ∀ (R : Ideal O),R ≠ 0 → (R.absNorm : ℝ) ≤ Z^BR →
      ∀ (hz₁ : src.W₁ 0=0) (hz₂ : src.W₂ 0=0),
      let radius := actualLowFirstRadius src R 1 Z Z nonHighCutoff;
      let q := firstSourceOuterLabel src R 1 Z radius;
      ∀ (labels : Finset (FirstSourceOuterIndex src R 1 Z radius)) (refIndex : FirstSourceOuterIndex src R 1 Z radius),
      refIndex ∈ labels →
      ∀ eFirst : ℝ,0 ≤ eFirst → eFirst ≤ lowLocalTiny →
      (∀ i∈labels,∀ j,|(q i).fullWidthCoordinates Z j-(q refIndex).fullWidthCoordinates Z j| < eFirst) →
      ∀ (side : Bool) (height : First src R 1 Z radius → ℝ),
      (∀ k∈firstSourceLabels labels q,|height k| ≤ Z^ν) →
      ∀ (bin : NonzeroElement → Option (Fin (I+1) × Fin (I+1))),
      (∀ w b,bin w = some b →
        ∀ (P : JointRelativeLabel src.η (Option (Slot × RayQuotient.Characters M H)) → Ideal O)
          (hP : ∀ label,P label ≠ 0),
          jointRelativeSourceZeroBin src.η (relativeSlotTranslate M H hH (fun _ : Slot => η₀))
            Q hQ72 (relativeSlotTranslate_fixedQ M H hH (fun _ : Slot => η₀) Q hQM
              (fun _ => hQη₀)) P hP
            (51/100+(e/2)*(b.2.val : ℝ)) (51/100+(e/2)*(b.2.val : ℝ)+e)
            ((3*(b.1.val+1):ℕ)*Z^τ) w) →
      0 < actualHighPrimeCount M H Sbad Z →
      firstLiteralHighBinSum src R Z hz₁ hz₂ upper b₁ b₂plain (actualHighPrimeCount M H Sbad Z)
        I e bin labels side height ≤
      (C/(((q refIndex).sideCommon side).absNorm : ℝ))*
        Z^((q refIndex).sideTargetWidth side Z
          (Real.logb Z (CenteredMomentExceptionalAmplitudePair.volume src.toData))-1/10000) := by
  have htiny : 0 < lowLocalTiny := by norm_num [lowLocalTiny]
  have hcut : 0 < nonHighCutoff := by norm_num [nonHighCutoff,lowLocalTiny]
  have hcutcap : nonHighCutoff ≤ lowLocalTiny := by norm_num [nonHighCutoff,lowLocalTiny]
  have hcutone : nonHighCutoff ≤ 1 := by norm_num [nonHighCutoff,lowLocalTiny]
  obtain ⟨N,hsectors⟩ := uniform_actual_packet_second_sectors (lowLocalTiny/8) (by positivity)
  obtain ⟨τ,ν,C,hν,hντ,hτdet,hτsmall,hC,hhigh⟩ := actual_local_high_reference_bound
    (Cell := Fin 4 → Fin (N+1)) (κbin := Fin (I+1) × Fin (I+1))
    η η₀ Q hQtop hQ72 hQη hβ M H hH hQM hQη₀ S₀
    φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB hβupper
    Wslot aslot bslot haslot hWslot hslotSupport BR e σmin σmax τdetector I hBR he hecap hτdetector
    W₁ W₂ a₁ b₁ a₂ b₂plain ha₁ ha₂ hs₁ hW₁ hs₂ hW₂ lo hi hlo Mslot upper hMslot Sbad ballProfile
  let C' := (1+((actualHighBins I e).card : ℝ))*C
  refine ⟨τ,ν,C',hν,hντ,hτdet,hτsmall,by dsimp only [C'];positivity,?_⟩
  filter_upwards [hhigh,eventually_ge_atTop (2:ℝ),
    (tendsto_rpow_atTop (hν.trans hντ)).eventually (eventually_gt_atTop (2:ℝ)),
    eventually_low_literal_omega (Fintype.card Slot) upper b₁ b₂plain nonHighCutoff nonHighCutoff
      hcut hcut.le (by norm_num [nonHighCutoff,lowLocalTiny]),
    eventually_low_fixed_profile_gates (ι := Slot) upper b₁ b₂plain 1 lowLocalTiny htiny,
    eventually_fixed_logb_le (max 1 b₁*max 1 b₂plain) (2*lowLocalTiny) (by positivity) (by positivity)]
    with Z hhigh hZ₂ hT homega hfixed hclip
  have hZ := hhigh.1
  have hz := zero_lt_one.trans hZ
  refine ⟨hZ₂,hT,?_⟩
  intro θ w σ freq hw hwcap hσ hfreq src hmatch hη hp₁ hp₂ hMs hupper hloSrc hhiSrc hhiAbs hb₁ hb₂
    hX₁ hX₂ hY₁ hY₂ hsource₀ hA₀ hAcap R hR hRN hz₁ hz₂ radius q labels refIndex href
    eFirst heFirst heFirstCap hfull side height hheight bin hclass hprime
  let A := Real.logb Z (CenteredMomentExceptionalAmplitudePair.volume src.toData)
  let omega := lowLiteralOmega (Fintype.card Slot) upper b₁ b₂plain nonHighCutoff nonHighCutoff Z
  let ref := q refIndex
  have hvolume : CenteredMomentExceptionalAmplitudePair.volume src.toData = Z^A :=
    (Real.rpow_logb hz hZ.ne' (CenteredMomentExceptionalAmplitudePair.volume_pos src.toData)).symm
  have hfixedSrc := hfixed.2.1 src hsource₀ hhiAbs hb₁ hb₂ hupper
  have hsourceA : sourceRadius src ≤ Z^(A+lowLocalTiny) := by
    calc
      _ = Z^(Real.logb Z (sourceRadius src)) := (Real.rpow_logb hz hZ.ne' hsource₀).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le hfixedSrc.1
  have hsource : sourceRadius src ≤ Z^(1:ℝ) := hsourceA.trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num [lowLocalTiny];linarith only [hAcap]))
  have hsupp : (max 1 src.upper)^Fintype.card Slot ≤ Z^lowLocalTiny := by
    have hp : 0 < (max 1 src.upper)^Fintype.card Slot := by positivity
    have hh : Real.logb Z ((max 1 src.upper)^Fintype.card Slot) ≤ lowLocalTiny := by
      simpa only [Real.logb_pow] using hfixedSrc.2
    calc
      _ = Z^(Real.logb Z ((max 1 src.upper)^Fintype.card Slot)) := (Real.rpow_logb hz hZ.ne' hp).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le hh
  have hrefcaps := first_actual_common_caps src R 1 squarefree_one hz₁ hz₂ Z radius refIndex Z hsource
  have hheightSide (k) (hk : k ∈ firstSideSourceLabels labels q (fun _ => sourceRadius src) side) :
      |height k| ≤ Z^ν := by
    apply hheight k
    cases side <;> exact (Finset.mem_filter.mp hk).1
  have hbin (bidx) (hbidx : bidx ∈ actualHighBins I e) :
      (∑ k∈firstSideSourceLabels labels q (fun _ => sourceRadius src) side,
        ‖firstLowBinBlock src R 1 squarefree_one hz₁ hz₂ Z radius k side Z A 1 omega nonHighCutoff
          (height k) ballProfile bin bidx‖ /
          (CenteredMomentExceptionalAmplitudePair.volume src.toData*actualHighPrimeCount M H Sbad Z)) ≤
        (C/((ref.sideCommon side).absNorm : ℝ))*Z^(ref.sideTargetWidth side Z A-1/10000) := by
    obtain ⟨code,hcode⟩ := hsectors src R 1 Z radius side
      (mainScale src R 1 Z radius side Z A 1 omega)
      (mainRadius src R 1 Z radius side Z A 1 omega nonHighCutoff)
      (mainHeight src R 1 Z radius side) squarefree_one hz₁ hz₂ Z hZ
      (by simpa only [Real.rpow_one] using hsource)
    apply hhigh.2 src R 1 squarefree_one hz₁ hz₂ Z radius side A 1 omega nonHighCutoff
      bin bidx height labels code ref hprime
    intro cell χ ξ hnonempty
    let X := liveBinPackets src R 1 Z radius side Z A 1 omega nonHighCutoff squarefree_one hz₁ hz₂
      bin bidx height ballProfile labels
    let Y := X.filter (fun x => code x=cell)
    have hY : Y ⊆ X := Finset.filter_subset _ _
    have hzero : ∀ x∈Y,(row x).z≠0 := fun x hx =>
      liveBinPackets_nonzero src R 1 Z radius side Z A 1 omega nonHighCutoff squarefree_one hz₁ hz₂
        bin bidx height ballProfile labels x (hY hx)
    obtain ⟨x,hx⟩ := hnonempty
    have hxY : x ∈ Y := (Finset.mem_filter.mp hx).1
    let fallback := (⟨row x,hzero x hxY⟩ : NonzeroJointSourceRow (original src R 1) side)
    have hedge (j) : 0 ≤ secondWidthEdge (lowLocalTiny/8) cell j := by
      dsimp only [secondWidthEdge]
      positivity
    have hsec := packet_cell_second_sector squarefree_one hz₁ hz₂ x.1 fallback src.η χ ξ 1 1 X
      code cell Z (lowLocalTiny/8) (fun x _ => hcode x) hzero
    have hdata := actual_literal_high_packet_data M H hH η₀ Q hQ72 hQM hQη₀
      Wslot bslot BR e σmin σmax I W₁ W₂ b₁ b₂plain lo hi Mslot upper Sbad ballProfile
      src R 1 squarefree_one hz₁ hz₂ Z τ ν A omega nonHighCutoff nonHighCutoff eFirst (lowLocalTiny/8) side
      hZ₂ hT hBR he heFirst heFirstCap (by positivity) (by linarith) hA₀ hAcap homega.2.1 homega.2.2
      hcutone hcut.le hcutcap hR hRN hsource₀ hsource hsourceA hvolume ⟨hp₁,hp₂⟩
      ⟨(le_abs_self _).trans hb₁,(le_abs_self _).trans hb₂⟩ hMs hupper hloSrc hhiSrc hsupp hclip.2
      θ w σ freq hmatch hmatch.scale hw hwcap hX₁ hX₂ hY₁ hY₂ hσ hfreq bin bidx
      (Finset.mem_filter.mp hbidx).2.1.le (Finset.mem_filter.mp hbidx).2.2 hclass height labels hheightSide
      ref hrefcaps.1 hrefcaps.2 hfull Y hY hzero x.1 fallback χ ξ
      (secondWidthEdge (lowLocalTiny/8) cell) hedge (fun v hv j => (hsec v hv j).2)
    rw [hη] at hdata
    exact hdata
  have hsum := Finset.sum_le_sum hbin
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  change (∑ bidx∈actualHighBins I e,_) ≤ _
  apply hsum.trans
  have hcoef : 0 ≤ C/((ref.sideCommon side).absNorm : ℝ) := by positivity
  have hp := Real.rpow_nonneg hz.le (ref.sideTargetWidth side Z A-1/10000)
  have hle := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (show ((actualHighBins I e).card : ℝ) ≤ 1+(actualHighBins I e).card by linarith) hcoef) hp
  convert hle using 1 <;> dsimp only [C',ref,A] <;> ring

end FixedData
#print axioms actual_literal_high_bins_target
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighLiteralTarget -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstAnalyticalJoin ; sha256 e9d2586d9974bd6e22cdcc1e23924f5c4de40f110ca0b7541b56baa1a41a033d -/
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
local instance firstAnalyticalJoinFiniteQuotient : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem actual_literal_first_annular_targets
    (Wslot : ℝ → ℂ) (aslot bslot a b σlo σhi Mslot lower upper bplain₁ bplain₂ BRmask : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support Wslot ⊆ Icc aslot bslot)
    (hW : ContDiff ℝ ∞ Wslot) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1/4) (hb : 1 ≤ b)
    (hbplain₁ : b ≤ bplain₁) (hbplain₂ : b ≤ bplain₂)
    (hMslot : 0 ≤ Mslot) (hlower : 0 < lower) (hupper : 1 ≤ upper) (hBRmask : 0 ≤ BRmask)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) (hbetaTop : HeckeZeroSupremum.beta ≤ 7/8)
    (lows highs : α → ℝ) (hlows : ∀ i,0 < lows i) (hhighs : ∀ i,0 ≤ highs i)
    (ηfirst : Character) (profile : Profiles a b)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes ⊆ Sbad)
    (e : ℝ) (he : 0 < e) (hecap : e ≤ highLocalBinCap BRmask (Fintype.card α))
    (η₀ : Character) (Q : Ideal O) (hQM : Q ≤ M)
    (hQ0 : internalQ Q η₀ ≠ 0) (hQt : internalQ Q η₀ ≠ ⊤)
    (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)})
    (hQη : internalQ Q η₀ ≤ ηfirst.modulus)
    (S₀ : Finset (Ideal O))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y,0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y,φ y ≤ B₀) :
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
      Real.logb Z src.X₁+Real.logb Z src.X₂+(22/5)*(∑ i,w i) ≤ 1 →
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
  letI : NeZero (internalQ Q η₀) := ⟨hQ0⟩
  obtain ⟨I,hI,hclassifier⟩ := exists_global_original_source_bins (Slot := α) M H hH e he hbetaTop
  have hs₁ : Function.support (profile.profile 0 : ℝ → ℂ) ⊆ Icc a bplain₁ := by
    intro x hx
    exact ⟨(profile.support 0 hx).1,((profile.support 0 hx).2.trans hbplain₁)⟩
  have hs₂ : Function.support (profile.profile 1 : ℝ → ℂ) ⊆ Icc a bplain₂ := by
    intro x hx
    exact ⟨(profile.support 1 hx).1,((profile.support 1 hx).2.trans hbplain₂)⟩
  obtain ⟨τheight,νhigh,Ch,hνhigh,hνhighτ,hτcap,hτsmall,hCh,hhigh⟩ :=
    actual_literal_high_bins_target ηfirst η₀ (internalQ Q η₀) hQt hQ72 hQη hbeta M H hH
      (inf_le_left.trans hQM) inf_le_right S₀
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB hbetaTop
      Wslot aslot bslot haslot hW hWs BRmask e σlo σhi (1/8) I hBRmask he hecap (by norm_num)
      (profile.profile 0) (profile.profile 1) a bplain₁ a bplain₂ ha ha hs₁ ((profile.profile 0).smooth ⊤)
      hs₂ ((profile.profile 1).smooth ⊤) lows highs hlows Mslot upper hMslot Sbad
  have helow : e ≤ lowLocalBinCap (Fintype.card α) :=
    hecap.trans (min_le_left _ _)
  obtain ⟨νother,hνother,hνotherτ,hother⟩ := actual_literal_first_annular_targets_of_high M H hH
    Wslot aslot bslot a b σlo σhi Mslot lower upper bplain₁ bplain₂ BRmask
    haslot hWs hW hbslot ha haUpper hb hMslot hlower hupper hBRmask hbeta hbetaTop
    lows highs hlows hhighs ηfirst profile Sbad hbad I e τheight he helow (hνhigh.trans hνhighτ) hτcap.le
  obtain ⟨Co,hCo,hother⟩ := hother η₀ Q hQM hQ0 hQt hQ72
  let ν := min νhigh νother/2
  have hν : 0 < ν := half_pos (lt_min hνhigh hνother)
  have hνhigh' : ν ≤ νhigh := (half_le_self (lt_min hνhigh hνother).le).trans (min_le_left _ _)
  have hνother' : ν ≤ νother := (half_le_self (lt_min hνhigh hνother).le).trans (min_le_right _ _)
  have hF : 0 ≤ nonHighAmplifierFactor := by norm_num [nonHighAmplifierFactor]
  refine ⟨ν,Co+nonHighAmplifierFactor*Ch,hν,by positivity,?_⟩
  filter_upwards [hhigh,hother,eventually_actual_high_prime_ratio M H hH Sbad lowLocalTiny
    (by norm_num [lowLocalTiny])] with Z hhigh hother hprime
  obtain ⟨hZ,τ,hτ,hother⟩ := hother
  obtain ⟨bin,hbinNone,hbins⟩ := hclassifier ηfirst η₀ (internalQ Q η₀) hQ72
    (inf_le_left.trans hQM) inf_le_right (Z^τheight) hhigh.2.1
  refine ⟨hZ,?_⟩
  intro θ w σ freq height hw hwmesh hσlo hσhi hheight hheightCap hfreq
    src hmatch hhi hMs hlo hhiInput hlowerSrc hupperSrc hhiAbs hb₁ hb₂ hb₁₀ hb₂₀ hb₁b hb₂b
    hp₁ hp₂ hη hsource₀ hn₁ hn₂ hm₁ hm₂ hwSum hcapacity hX₁ hX₂ hY₁ hY₂
    R hR hRcap hz₁ hz₂ radius q labels refIndex href eFirst heFirst heFirstCap hfull t ht left
  have hheightOther : height ≤ Z^νother := hheightCap.trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le hνother')
  have hheightHigh : height ≤ Z^νhigh := hheightCap.trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le hνhigh')
  have htOther : ∀ side,∀ k∈firstSourceLabels labels q,|t side k| ≤ Z^νother :=
    fun side k hk => (ht side k hk).trans (Real.rpow_le_rpow_of_exponent_le hZ.le hνother')
  have htHigh : ∀ side,∀ k∈firstSourceLabels labels q,|t side k| ≤ Z^νhigh :=
    fun side k hk => (ht side k hk).trans (Real.rpow_le_rpow_of_exponent_le hZ.le hνhigh')
  have hAeq := original_volume_log src Z w hZ hmatch.scale
  have hAcap := (local_capacity_of_volume Z (Real.logb Z src.X₁) (Real.logb Z src.X₂)
    (∑ i,w i) (Real.logb Z (volume src.toData)) hAeq hn₁ hn₂ hwSum hcapacity).1
  have hA₀ : 0 ≤ Real.logb Z (volume src.toData) := by
    rw [hAeq]
    have hn₁₀ := Real.logb_nonneg hZ ((Real.one_le_rpow hZ.le (by norm_num : (0:ℝ) ≤ 1/4)).trans hX₁)
    have hn₂₀ := Real.logb_nonneg hZ ((Real.one_le_rpow hZ.le (by norm_num : (0:ℝ) ≤ 1/4)).trans hX₂)
    exact add_nonneg (add_nonneg hn₁₀ hn₂₀) (Finset.sum_nonneg (fun i _=> hw i))
  have hclassSrc : ∀ w bidx,bin w = some bidx →
      ∀ (P : JointRelativeLabel src.η (Option (α × RayQuotient.Characters M H)) → Ideal O)
        (hP : ∀ label,P label ≠ 0),
        jointRelativeSourceZeroBin src.η (relativeSlotTranslate M H hH (fun _ : α => η₀))
          (internalQ Q η₀) hQ72 (relativeSlotTranslate_fixedQ M H hH (fun _ : α => η₀)
            (internalQ Q η₀) (inf_le_left.trans hQM) (fun _=> inf_le_right)) P hP
          (51/100+(e/2)*(bidx.2.val : ℝ)) (51/100+(e/2)*(bidx.2.val : ℝ)+e)
          ((3*(bidx.1.val+1):ℕ)*Z^τheight) w := by
    rw [hη]
    exact fun w bidx hb=> (hbins w bidx hb).2.2.2
  have hh (side : Bool) := hhigh.2.2 θ w σ freq hw hwmesh (fun j=>⟨hσlo j,hσhi j⟩)
    (fun j=>(hfreq j).trans hheightHigh) src hmatch hη hp₁.symm hp₂.symm hMs hupperSrc hlo hhiInput
    hhiAbs hb₁ hb₂ hn₁ hn₂ hm₁ hm₂ hsource₀ hA₀ (by linarith only [hAcap])
    R hR hRcap hz₁ hz₂ labels refIndex href eFirst heFirst.le
    (heFirstCap.trans (by norm_num [lowLocalTiny])) hfull side (t side) (htHigh side) bin hclassSrc hprime.2.1
  apply hother θ w σ freq height hw hwmesh hσlo hσhi hheight hheightOther hfreq
    src hmatch hhi hMs hlo hhiInput hlowerSrc hupperSrc hhiAbs hb₁ hb₂ hb₁₀ hb₂₀ hb₁b hb₂b
    hp₁ hp₂ hη hsource₀ hn₁ hn₂ hm₁ hm₂ hwSum hcapacity hX₁ hX₂ hY₁ hY₂ R hR hRcap hz₁ hz₂
    labels refIndex href eFirst heFirst heFirstCap hfull t htOther bin hbinNone
    (fun w bidx hb=> by
      simpa only [Nat.cast_mul,Nat.cast_ofNat] using
        (hbins w bidx hb).2.2.2 (fun _=>1) (fun _=> one_ne_zero)) Ch hCh.le ?_ left
  intro side
  apply (hh side).trans
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))
    (by positivity)

#print axioms actual_literal_first_annular_targets
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstAnalyticalJoin -/
