/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B087
import Submissions.local44_20261013.Bundles.B094
import Submissions.local44_20261013.Bundles.B104
import Submissions.local44_20261013.Bundles.B108
import Submissions.local44_20261013.Bundles.B109
import Submissions.local44_20261013.Bundles.B111
import Submissions.local44_20261013.Bundles.B112
import Submissions.local44_20261013.Bundles.B113
import Submissions.local44_20261013.Bundles.B114
import Submissions.local44_20261013.Bundles.B115
import Submissions.local44_20261013.Bundles.B116
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.NaturalInputMatches

/- BEGIN ORIGINAL MODULE Analytic.JointFirstHighReferenceTarget ; sha256 1c701c7b70990c506c1821d7c71ba51950845d6d695096f975557fbb2f1ea48e -/
section






/-! The genuine high-source estimate summed over both actual dyadic block
families. Maximization pays their subpower mass without recounting arithmetic rows. -/
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
open CenteredMomentCanonicalFirst CenteredMomentActive CenteredMomentCompleteCommon
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondPhysicalBlock
open CenteredMomentSourceRow CenteredMomentSecondLiveBlock
open CanonicalRowCompletion CenteredMomentRankinRadical ActualEisensteinCubic
open ActualFirstSecondSource CenteredMomentFirstNonexceptionalWeightSum
open CenteredMomentSecondBlockHarmonicMass
open CenteredMomentFirstPhysicalDyadicAssembly
local notation "O" => HeckeFamily.O

variable {Cell κbin : Type*} [Fintype Cell] [DecidableEq Cell] [DecidableEq κbin]
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

theorem actual_first_high_reference_target
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
      ∀ (src : Input Slot) (Rmask seed : Ideal O) (hs : Squarefree seed)
        (hz₁ : src.W₁ 0=0) (hz₂ : src.W₂ 0=0) (Kfirst : ℝ)
        (radius : (p : Labels src Rmask seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ)
        (side : Bool) (A Mparent omega ξ : ℝ)
        (bin : NonzeroElement → Option κbin) (bidx : κbin)
        (height : First src Rmask seed Kfirst radius → ℝ)
        (labels : Finset (FirstSourceOuterIndex src Rmask seed Kfirst radius))
        (cell : LivePacket src Rmask seed Kfirst radius side Z A Mparent omega ξ → Cell)
        (ref : FirstJointLabel Slot),
      0 < actualHighPrimeCount M H Sbad Z →
      let X := liveBinPackets src Rmask seed Kfirst radius side Z A Mparent omega ξ hs hz₁ hz₂
        bin bidx height Wkernel labels;
      (∀ c : Cell, ∀ χ₁ ξ₁ : RayCharacter,
        (rayPackets (X.filter (fun x => cell x=c)) χ₁ ξ₁).Nonempty →
        ∃ actualExponent : ℝ, HighPacketSourceData η η₀ Q hQ72 M H hH hQM hQη₀ ηcommon Wslot bslot Rwidth dmax e σmin σmax loss B dmin heightLoss I W₁ W₂ b₁ b₂plain lo hi fiberLoss Mslot upper conductorReserve Sbad Wkernel tailA targetLower Bdyad₁ Ldyad₁ Crdyad₁ Bdyad₂ Ldyad₂ Crdyad₂ dyadicLoss rowAbsorb Z τ ν
          (∑ x∈rayPackets (X.filter (fun x => cell x=c)) χ₁ ξ₁,
            packetValue hs hz₁ hz₂ (CenteredMomentExceptionalAmplitudePair.volume src.toData)
              (actualHighPrimeCount M H Sbad Z) height Wkernel x) actualExponent ∧ actualExponent ≤ ref.radicalWidth Z+A-2*ref.sideWidth side Z+ref.activeWidth Z+ref.punctureWidth Z+ref.sideAllowance side Z-1/10000) →
      (∑ k∈firstSideSourceLabels labels (firstSourceOuterLabel src Rmask seed Kfirst radius)
        (fun _ => sourceRadius src) side,
        ‖firstLowBinBlock src Rmask seed hs hz₁ hz₂ Kfirst radius k side Z A Mparent omega ξ
          (height k) Wkernel bin bidx‖ /
          (CenteredMomentExceptionalAmplitudePair.volume src.toData*actualHighPrimeCount M H Sbad Z)) ≤
        ((Fintype.card Cell : ℝ)*(Fintype.card RayCharacter : ℝ)^2*C /
          ((ref.sideCommon side).absNorm : ℝ))*Z^(ref.sideTargetWidth side Z A-1/10000) := by
  obtain ⟨profileBound,hprofile,τ,ν,orders,N,Nkernel,C,hν,hντ,hτdet,hheight,horders,hC,hhigh⟩ :=
    actual_first_high_cell_bound (Cell := Cell) (κbin := κbin) η η₀ Q hQtop hQ72 hQη hβ M H hH hQM hQη₀ S₀
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
  intro src Rmask seed hs hz₁ hz₂ Kfirst radius side A Mparent omega ξ bin bidx height labels cell ref hP X hdata
  have hh := hZ.2 src Rmask seed hs hz₁ hz₂ Kfirst radius side A Mparent omega ξ
    bin bidx height labels cell
    (ref.radicalWidth Z+A-2*ref.sideWidth side Z+ref.activeWidth Z+ref.punctureWidth Z+
      ref.sideAllowance side Z-1/10000) hP hdata
  have he := ref.side_target_power side Z A
    ((Fintype.card Cell : ℝ)*(Fintype.card RayCharacter : ℝ)^2*C) (-(1/10000)) hZ.1
  convert hh.trans_eq he using 1 <;> ring

end FixedData
#print axioms actual_first_high_reference_target
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstHighReferenceTarget -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstNaturalSource ; sha256 643ee8866c4a5010688ab6259fc9849dfff0bcdf9de37c20f08ce4464ebd12ef -/
section


set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
namespace LocalFirstNaturalSource
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentInductionEnergy CenteredMomentEnergyReferenceState
open CenteredMomentCommonRadialData CenteredMomentSourceRow CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceInputTailUniform
open CenteredMomentEnergyNaturalInputMatches
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance firstNaturalSourceFinite : Finite (O⧸M):=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)
variable (η₀:Character)(θ:α→RayQuotient.Characters M H)
variable (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0< aslot)
variable (hWs:Function.support W⊆Set.Icc aslot bslot)
variable (w σ freq:α→ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0< a)
variable (t X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂)

/-- A literal natural source with the comparison rectangle chosen at row width one. -/
def input:Input α:=
  CenteredMomentEnergyNaturalInputMatches.input M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ s p ha t X₁ X₂ (comparisonFirst Z 1) (comparisonSecond Z 1 X₁ X₂)
    hX₁ hX₂
    (comparison_positive Z 1 X₁ X₂ (zero_lt_one.trans_le s.base_ge_one) hX₁ hX₂).1
    (comparison_positive Z 1 X₁ X₂ (zero_lt_one.trans_le s.base_ge_one) hX₁ hX₂).2
    (comparison_same_product Z 1 X₁ X₂ (zero_lt_one.trans_le s.base_ge_one))

local notation "src"=> input M H hH η₀ θ W hW aslot bslot lo hi haslot hWs w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂

lemma input_matches:CenteredMomentAllocatedRayDictionary.Matches M H hH src η₀ θ w σ freq W bslot Z:=by
  constructor <;> intros <;> rfl

lemma metadata:
    (∀i,(src).lo i=aslot ∧ (src).hi i=bslot ∧
      (src).M i=profileBound W hW aslot bslot lo hi haslot hWs) ∧
    (src).lower=aslot ∧ (src).upper=bslot ∧ (src).b₁=b ∧ (src).b₂=b ∧
    (src).η=s.character ∧ (src).m=s.mask ∧ (src).t=t ∧
    (src).W₁=p.profile 0 ∧ (src).W₂=p.profile 1 ∧
    (src).X₁=X₁ ∧ (src).X₂=X₂ ∧ (src).Y₁=comparisonFirst Z 1 ∧ (src).Y₂=comparisonSecond Z 1 X₁ X₂:=by
  exact ⟨fun _=>⟨rfl,rfl,rfl⟩,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

lemma source_radius_positive (hbslot:0< bslot)(hb:0< b):0< sourceRadius src:=by
  change 0<(∏_i:α,bslot)*b*b*(X₁*X₂)*(∏i,Z^(w i))
  have hz:0< Z:=zero_lt_one.trans_le s.base_ge_one
  positivity

lemma plain_control:
    plainControl src (p.profile 0) (p.profile 1)=
      (profileBound W hW aslot bslot lo hi haslot hWs)^Fintype.card α*
      SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*SchwartzMap.seminorm ℝ 0 0 (p.profile 1):=by
  change (∏_i:α,profileBound W hW aslot bslot lo hi haslot hWs)*_ * _ = _
  simp

lemma comparison_source_gates (hZ:1< Z)
    (hn₁lo:410/1000≤ Real.logb Z X₁)(hn₂lo:410/1000≤ Real.logb Z X₂)
    (hn₁hi:Real.logb Z X₁≤423/1000)(hn₂hi:Real.logb Z X₂≤423/1000):
    Real.logb Z (src).Y₁≤1 ∧ Real.logb Z (src).Y₂≤1 ∧
    Z^(1/4:ℝ)≤(src).X₁ ∧ Z^(1/4:ℝ)≤(src).X₂ ∧ Z^(1/4:ℝ)≤(src).Y₁ ∧ Z^(1/4:ℝ)≤(src).Y₂:=by
  have hz:=zero_lt_one.trans hZ
  change Real.logb Z (comparisonFirst Z 1)≤1 ∧ Real.logb Z (comparisonSecond Z 1 X₁ X₂)≤1 ∧
    Z^(1/4:ℝ)≤ X₁ ∧ Z^(1/4:ℝ)≤ X₂ ∧ Z^(1/4:ℝ)≤ comparisonFirst Z 1 ∧
    Z^(1/4:ℝ)≤ comparisonSecond Z 1 X₁ X₂
  have hlog:Real.logb Z (X₁*X₂)=Real.logb Z X₁+Real.logb Z X₂:=Real.logb_mul hX₁.ne' hX₂.ne'
  have hy:comparisonSecond Z 1 X₁ X₂=Z^(Real.logb Z X₁+Real.logb Z X₂-1/4):=by
    rw [comparison_second_power Z 1 X₁ X₂ hZ hX₁ hX₂,hlog]
  refine ⟨?_,?_,?_,?_,le_rfl,?_⟩
  · change Real.logb Z (Z^(1/4:ℝ))≤1
    rw [Real.logb_rpow hz hZ.ne'];norm_num
  · rw [hy,Real.logb_rpow hz hZ.ne'];linarith
  · calc
      _≤ Z^(Real.logb Z X₁):=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
      _=X₁:=Real.rpow_logb hz hZ.ne' hX₁
  · calc
      _≤ Z^(Real.logb Z X₂):=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
      _=X₂:=Real.rpow_logb hz hZ.ne' hX₂
  · rw [hy]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)

lemma original_energy:
    energy (src).η s.mask 1 (src).t (src).W₁ (src).W₂ (src).slots (src).toData.coefficient (src).P
      (src).X₁ (src).X₂ s.radial.keep s.radial.profile s.radial.scale=
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i=> CenteredMomentPrimeSlot.primePool M H bslot (Z^(w i)))
      (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I)
      (fun i=> Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale:=rfl

#print axioms comparison_source_gates
#print axioms original_energy
end LocalFirstNaturalSource
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstNaturalSource -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstOriginalExplicitMesh ; sha256 69604522312a7ffab2b6bc30b7119b79472e264ee244a0ad74fea1a7b089e970 -/
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
local instance firstOriginalExplicitAlphaDecEq : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance firstOriginalExplicitFinite : Finite (O⧸M):=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

/-- The complete original first-transform remainder in the new local window.
Its only unestimated term is the literal retained physical-block sum. -/
theorem actual_local_first_original_target_explicit_mesh
    (Wslot:ℝ→ℂ)(aslot bslot lo hi a b bΦ Bmask upper bplain₁ bplain₂ ε ξ:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)
    (hcSlot:ContDiff ℝ ∞ Wslot)(hbslot:0≤ bslot)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hBmask:0≤ Bmask)
    (hupper:0≤ upper)(hε:0<ε)(hξ:0<ξ)
    (hbeta:51/100≤ HeckeZeroSupremum.beta)(hbetaTop:HeckeZeroSupremum.beta≤7/8):
    ∃J:ℕ,∃U Sd St:Finset (ℕ×ℕ),∃Cd Ct:ℝ,0< Cd ∧ 0< Ct ∧
    ∀ηfirst η₀:Character,∀Q:Ideal O,Q≤ M → internalQ Q η₀≠0 → internalQ Q η₀≠⊤ →
      internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃Cc:ℝ,0< Cc ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
      ∀(src:Input α)(profile:Profiles a b),
      profile.profile 0=src.W₁ → profile.profile 1=src.W₂ →
      (∀i,|src.hi i|≤ upper) → |src.b₁|≤ bplain₁ → |src.b₂|≤ bplain₂ → src.upper≤ upper →
      0< sourceRadius src →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(height:ℝ),
      CenteredMomentAllocatedRayDictionary.Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
      (∀i,0≤ w i) → (∀i,w i≤ meshGuaranteed Bmask ε) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
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
  obtain ⟨J,U,hcomp⟩:=actual_local_comparison_energy_explicit_mesh (α:=α) M H hH
    Wslot aslot bslot lo hi a b bΦ Bmask ε haslot hsSlot hcSlot hbslot
    ha hlo hhi hbΦ hBmask hε hbeta hbetaTop
  obtain ⟨Sd,St,Cd,Ct,hCd,hCt,hrem⟩:=actual_local_first_original_remainder
    (ι:=α) a b upper bplain₁ bplain₂ ε ξ ha (by linarith) hupper hε hξ
  refine ⟨J,U,Sd,St,Cd,Ct,hCd,hCt,?_⟩
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

#print axioms actual_local_first_original_target_explicit_mesh
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstOriginalExplicitMesh -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstRetainedFromTargets ; sha256 e1f8c6a151185d0b04f1fca9ad11305e58124d37ff772f14a41e0833227bec95 -/
section




/-! Exact final first-transform assembly. The only analytic hypotheses
are the two joint targets on the actual finite Fourier cube; all lower
dyads, label counts, source radii and original block identifications are
derived here. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT RayFourExpansion
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentCanonicalFirst
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentSourceMass CenteredMomentSourceRow CenteredMomentActiveSource
open CenteredMomentSecondRetainedAggregate CenteredMomentFirstSectors
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentSectorLocalization
open CenteredMomentFirstAnnularMajorant CenteredMomentSecondRetainedRows CenteredMomentLogDyadic
open ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
local instance firstRetainedTargetsDecidableSum {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem FirstJointLabel.common_norms_of_full_close {ι : Type*} [Fintype ι]
    (q ref : FirstJointLabel ι) (Z e : ℝ) (hZ : 1 < Z)
    (h : ∀ j,|q.fullWidthCoordinates Z j-ref.fullWidthCoordinates Z j| < e) :
    (q.C.absNorm : ℝ) ≤ Z^e*(ref.C.absNorm : ℝ) ∧
    (q.D.absNorm : ℝ) ≤ Z^e*(ref.D.absNorm : ℝ) := by
  have hz := zero_lt_one.trans hZ
  have hc : q.leftWidth Z ≤ e+ref.leftWidth Z := by
    have hh := (abs_lt.mp (h 0)).2
    change q.leftWidth Z-ref.leftWidth Z < e at hh
    linarith
  have hd : q.rightWidth Z ≤ e+ref.rightWidth Z := by
    have hh := (abs_lt.mp (h 1)).2
    change q.rightWidth Z-ref.rightWidth Z < e at hh
    linarith
  constructor
  · calc
      _ = Z^(q.leftWidth Z) := (Real.rpow_logb hz hZ.ne' (CenteredMomentFirstScale.norm_pos _ q.hC.1)).symm
      _ ≤ Z^(e+ref.leftWidth Z) := Real.rpow_le_rpow_of_exponent_le hZ.le hc
      _ = _ := by rw [Real.rpow_add hz,FirstJointLabel.leftWidth,Real.rpow_logb hz hZ.ne' (CenteredMomentFirstScale.norm_pos _ ref.hC.1)]
  · calc
      _ = Z^(q.rightWidth Z) := (Real.rpow_logb hz hZ.ne' (CenteredMomentFirstScale.norm_pos _ q.hD.1)).symm
      _ ≤ Z^(e+ref.rightWidth Z) := Real.rpow_le_rpow_of_exponent_le hZ.le hd
      _ = _ := by rw [Real.rpow_add hz,FirstJointLabel.rightWidth,Real.rpow_logb hz hZ.ne' (CenteredMomentFirstScale.norm_pos _ ref.hD.1)]

theorem eventually_original_first_absolute_from_joint_targets
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Wkernel : 𝓢(ℝ,ℂ)) (Ncap : ℕ)
    (ν F U b₁ b₂ B₁ B₂ a₁ a₂ aSource e Amin Amax : ℝ)
    (hν : 0 < ν) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (haSource : 0 < aSource) (he : 0 < e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ Z : ℝ in atTop,
    ∀ (s : Input ι) (R : Ideal O),
    Fintype.card ι ≤ Ncap → (∀ i,s.M i ≤ F) → s.upper ≤ U → s.b₁ ≤ b₁ → s.b₂ ≤ b₂ →
    s.W₁ 0 = 0 → s.W₂ 0 = 0 →
    (∀ x,‖s.W₁ x‖ ≤ B₁) → (∀ x,‖s.W₂ x‖ ≤ B₂) →
    (∀ x,s.W₁ x ≠ 0 → a₁ ≤ x) → (∀ x,s.W₂ x ≠ 0 → a₂ ≤ x) →
    aSource ≤ originalLowerProfile s a₁ a₂ →
    0 < sourceRadius s → sourceRadius s ≤ Z^(1:ℝ) →
    ∀ A : ℝ,Amin ≤ A → A ≤ Amax → volume s.toData = Z^A →
    ∀ ξ : ℝ,ξ ≤ 1 →
    let radius := actualLowFirstRadius s R 1 Z Z ξ
    let q := firstSourceOuterLabel s R 1 Z radius
    ∀ t Ch : ℝ,0 ≤ Ch →
    let live := firstLiveSourceLabels s R 1 Z radius Finset.univ (fun _ => t) Wkernel (fun _ => logAnnulus)
    (∀ (labels : Finset (FirstSourceOuterIndex s R 1 Z radius)),labels ⊆ live →
      ∀ ref ∈ labels,
      (∀ i ∈ labels,∀ j,|(q i).fullWidthCoordinates Z j-(q ref).fullWidthCoordinates Z j| < e) →
      (∀ i ∈ labels,(q ref).activeWidth Z/2+(q ref).punctureWidth Z ≤
        (q i).activeWidth Z/2+(q i).punctureWidth Z) →
      ∀ θ w : ℝ,‖θ‖ ≤ Z^ν → ‖w‖ ≤ Z^ν →
      (∑ k ∈ firstSourceLabels labels q,
        ((q k.1).sourceChild k.2).leftEnergy (t+2*Real.pi*(w-θ)) profile (dyadicScale (k.1.2.2 1))) ≤
        (Z^A/((q ref).C.absNorm : ℝ))*(Ch*Z^((q ref).leftTargetWidth Z A)) ∧
      (∑ k ∈ firstSourceLabels labels q,
        ((q k.1).sourceChild k.2).rightEnergy (t+2*Real.pi*(w-(-θ))) profile (dyadicScale (k.1.2.2 1))) ≤
        (Z^A/((q ref).D.absNorm : ℝ))*(Ch*Z^((q ref).rightTargetWidth Z A))) →
    (∑ i : FirstSourceOuterIndex s R 1 Z radius,
      ‖firstPhysicalValue s R 1 Z radius (fun _ => t) Wkernel (fun _ => logAnnulus) i‖)/
      volume s.toData ≤
      C*(Ch+firstSourceCoarseConstant Ncap F U b₁ b₂ B₁ B₂
        (QuadraticInitialBound.diagonalControl profile))*Z^(1+e) := by
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hwin (i : Fin 4) (y : ℝ) (hy : logAnnulus y ≠ 0) : |y| ≤ Real.log 4 := by
    have hh := logAnnulus_support hy
    exact abs_le.mpr ⟨hh.1,hh.2.trans hlog⟩
  obtain ⟨degree,Cs,hCs,hsector⟩ := eventually_actual_first_absolute_annular_sector_from_local_targets
    (ι := ι) Wkernel (fun _ => logAnnulus) rfl (fun _ => Real.log 4) (fun _ => hlog)
    hwin logAnnulus_compact logAnnulus_smooth logAnnulus_compact logAnnulus_smooth Ncap ν
    F U b₁ b₂ B₁ B₂ 1 3 1 Amin Amax hν hB₁ hB₂ (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨Cc,hCc,hcells⟩ := uniform_first_full_sector_sum 1 e (by norm_num) he
  refine ⟨Cc*Cs*(Real.exp (Real.log 4)/aSource),by positivity,?_⟩
  filter_upwards [hsector,eventually_gt_atTop (1:ℝ)] with Z hsector hZ
  have hz := zero_lt_one.trans hZ
  intro s R hN hF hU hb₁ hb₂ hz₁ hz₂ hbound₁ hbound₂ hs₁ hs₂ haProfile hsourcepos hsource
    A hAmin hAmax hvolume ξ hξ
  dsimp only
  intro t Ch hCh htargets
  let radius := actualLowFirstRadius s R 1 Z Z ξ
  let q := firstSourceOuterLabel s R 1 Z radius
  let live := firstLiveSourceLabels s R 1 Z radius Finset.univ (fun _ => t) Wkernel (fun _ => logAnnulus)
  let coarse := firstSourceCoarseConstant Ncap F U b₁ b₂ B₁ B₂ (QuadraticInitialBound.diagonalControl profile)
  let bound := Cs*(Ch+coarse)*(Real.exp (Real.log 4)/aSource)*Z^(1+e)
  have hcoarse : 0 ≤ coarse := by
    have hd := QuadraticInitialBound.diagonalControl_nonneg profile
    dsimp only [coarse,firstSourceCoarseConstant]
    positivity
  have hbound : 0 ≤ bound := by dsimp only [bound]; positivity
  have hZA := Real.rpow_pos_of_pos hz A
  have hr := actualLowFirstRadius_le s R 1 Z Z ξ hZ.le hZ hξ hsourcepos.le hsource
  have hcap (i) : ((q i).C.absNorm : ℝ) ≤ Z^(1:ℝ) ∧ ((q i).D.absNorm : ℝ) ≤ Z^(1:ℝ) :=
    first_actual_common_caps s R 1 squarefree_one hz₁ hz₂ Z radius i Z hsource
  have hfull := hcells live q Z hZ (fun i _ => hcap i)
    (fun i => ‖firstPhysicalValue s R 1 Z radius (fun _ => t) Wkernel (fun _ => logAnnulus) i‖/Z^A)
    bound hbound (by
      intro labels hlabels ref href hclose hmin
      have hlo (i) (hi : i ∈ labels) := first_live_source_lower_dyads s R 1 Z radius Finset.univ
        (fun _ => t) Wkernel (fun _ => logAnnulus) a₁ a₂ (Real.log 4) ha₁ ha₂ hs₁ hs₂ hwin i (hlabels hi)
      have hlower (i) (hi : i ∈ labels) :
          aSource*Z^A ≤ ((q i).C.absNorm : ℝ)*Real.exp (Real.log 4)*dyadicScale (i.2.2 2) ∧
          aSource*Z^A ≤ ((q i).D.absNorm : ℝ)*Real.exp (Real.log 4)*dyadicScale (i.2.2 3) := by
        have hh := hlo i hi
        rw [hvolume] at hh
        exact ⟨(mul_le_mul_of_nonneg_right haProfile hZA.le).trans hh.1,
          (mul_le_mul_of_nonneg_right haProfile hZA.le).trans hh.2⟩
      have hn (i) (hi : i ∈ labels) := (q i).common_norms_of_full_close (q ref) Z e hZ (hclose i hi)
      have hh := hsector s R 1 hN hF hU hb₁ hb₂ hz₁ hz₂ hbound₁ hbound₂ hsourcepos hsource
        1 A e aSource (Real.log 4) Ch hAmin hAmax haSource hCh hvolume radius hr
      dsimp only at hh
      rw [Real.rpow_one] at hh
      have hh' := hh labels ref (fun _ => t)
        (fun i hi => (hlower i hi).1) (fun i hi => (hlower i hi).2)
        (fun i hi => (hn i hi).1) (fun i hi => (hn i hi).2) hmin (fun i _ => logAnnulus_norm _)
        (fun θ w hθ hw => (htargets labels hlabels ref href hclose hmin θ w hθ hw).1)
        (fun θ w hθ hw => (htargets labels hlabels ref href hclose hmin θ w hθ hw).2)
      simpa only [Finset.sum_div] using hh')
  have heq :
      (∑ i : FirstSourceOuterIndex s R 1 Z radius,
        ‖firstPhysicalValue s R 1 Z radius (fun _ => t) Wkernel (fun _ => logAnnulus) i‖) =
      ∑ i ∈ live,‖firstPhysicalValue s R 1 Z radius (fun _ => t) Wkernel (fun _ => logAnnulus) i‖ := by
    dsimp only [live,firstLiveSourceLabels]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs with hn
    · rfl
    · simp only [not_not] at hn
      simp only [hn,norm_zero]
  rw [hvolume]
  calc
    _ = ∑ i ∈ live,‖firstPhysicalValue s R 1 Z radius (fun _ => t) Wkernel (fun _ => logAnnulus) i‖/Z^A := by
      rw [heq,Finset.sum_div]
    _ ≤ Cc*bound := hfull
    _ = _ := by dsimp only [bound,coarse]; ring

theorem eventually_original_retained_from_joint_targets
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Wkernel : 𝓢(ℝ,ℂ)) (Ncap : ℕ)
    (ν F U b₁ b₂ B₁ B₂ a₁ a₂ aSource e Amin Amax : ℝ)
    (hν : 0 < ν) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (haSource : 0 < aSource) (he : 0 < e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ Z : ℝ in atTop,
    ∀ (s : Input ι) (R : Ideal O),
    Fintype.card ι ≤ Ncap → (∀ i,s.M i ≤ F) → s.upper ≤ U → s.b₁ ≤ b₁ → s.b₂ ≤ b₂ →
    s.W₁ 0 = 0 → s.W₂ 0 = 0 →
    (∀ x,‖s.W₁ x‖ ≤ B₁) → (∀ x,‖s.W₂ x‖ ≤ B₂) →
    (∀ x,s.W₁ x ≠ 0 → a₁ ≤ x) → (∀ x,s.W₂ x ≠ 0 → a₂ ≤ x) →
    aSource ≤ originalLowerProfile s a₁ a₂ →
    0 < sourceRadius s → sourceRadius s ≤ Z^(1:ℝ) →
    ∀ A : ℝ,Amin ≤ A → A ≤ Amax → volume s.toData = Z^A →
    ∀ ξ : ℝ,ξ ≤ 1 →
    let radius := actualLowFirstRadius s R 1 Z Z ξ
    let q := firstSourceOuterLabel s R 1 Z radius
    ∀ t Ch : ℝ,0 ≤ Ch →
    let live := firstLiveSourceLabels s R 1 Z radius Finset.univ (fun _ => t) Wkernel (fun _ => logAnnulus)
    (∀ (labels : Finset (FirstSourceOuterIndex s R 1 Z radius)),labels ⊆ live →
      ∀ ref ∈ labels,
      (∀ i ∈ labels,∀ j,|(q i).fullWidthCoordinates Z j-(q ref).fullWidthCoordinates Z j| < e) →
      (∀ i ∈ labels,(q ref).activeWidth Z/2+(q ref).punctureWidth Z ≤
        (q i).activeWidth Z/2+(q i).punctureWidth Z) →
      ∀ θ w : ℝ,‖θ‖ ≤ Z^ν → ‖w‖ ≤ Z^ν →
      (∑ k ∈ firstSourceLabels labels q,
        ((q k.1).sourceChild k.2).leftEnergy (t+2*Real.pi*(w-θ)) profile (dyadicScale (k.1.2.2 1))) ≤
        (Z^A/((q ref).C.absNorm : ℝ))*(Ch*Z^((q ref).leftTargetWidth Z A)) ∧
      (∑ k ∈ firstSourceLabels labels q,
        ((q k.1).sourceChild k.2).rightEnergy (t+2*Real.pi*(w-(-θ))) profile (dyadicScale (k.1.2.2 1))) ≤
        (Z^A/((q ref).D.absNorm : ℝ))*(Ch*Z^((q ref).rightTargetWidth Z A))) →
    ‖CenteredMomentFirstSectorLocalization.retainedEnergy s.η
      (CenteredMomentSecondHeightFamily.fixedBadMask*idealGenerator R) 1 t
      (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R 1) Wkernel Z (sourceRadius s) Z ξ‖/
      volume s.toData ≤
      C*(Ch+firstSourceCoarseConstant Ncap F U b₁ b₂ B₁ B₂
        (QuadraticInitialBound.diagonalControl profile))*Z^(1+e) := by
  obtain ⟨C,hC,habs⟩ := eventually_original_first_absolute_from_joint_targets
    (ι := ι) Wkernel Ncap ν F U b₁ b₂ B₁ B₂ a₁ a₂ aSource e Amin Amax
    hν hB₁ hB₂ ha₁ ha₂ haSource he
  refine ⟨C,hC,?_⟩
  filter_upwards [habs,eventually_gt_atTop (0:ℝ)] with Z habs hZ
  intro s R hN hF hU hb₁ hb₂ hz₁ hz₂ hbound₁ hbound₂ hs₁ hs₂ haProfile hsourcepos hsource
    A hAmin hAmax hvolume ξ hξ
  dsimp only
  intro t Ch hCh htargets
  have hh := habs s R hN hF hU hb₁ hb₂ hz₁ hz₂ hbound₁ hbound₂ hs₁ hs₂ haProfile
    hsourcepos hsource A hAmin hAmax hvolume ξ hξ t Ch hCh htargets
  have hret := original_retained_norm_actual_first_blocks s R 1 hz₁ hz₂ t Wkernel Z Z ξ hZ
  exact (div_le_div_of_nonneg_right hret (volume_pos s.toData).le).trans hh

#print axioms eventually_original_first_absolute_from_joint_targets
#print axioms eventually_original_retained_from_joint_targets
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstRetainedFromTargets -/

/- BEGIN ORIGINAL MODULE Analytic.JointHighLiteralData ; sha256 751ceac8a5d702468900d9dbda621d3c5860501d524c42f6f406bef7ac46481d -/
section



/-! The fixed local choices used by the literal high-packet constructor.
This abbreviation only names the existing concrete source predicate. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily
local notation "O" => HeckeFamily.O
variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M]
local instance highLiteralDataFiniteQuotient : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

abbrev LocalHighPacketData
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (η η₀ : Character) (Q : Ideal O) (hQ72 : Q ≤ Ideal.span {(72:O)})
    (hQM : Q ≤ M) (hQη₀ : Q ≤ η₀.modulus)
    (Wslot : ℝ → ℂ) (bslot BR e σmin σmax : ℝ) (I : ℕ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ : ℝ) (lo hi : Slot → ℝ) (Mslot upper : ℝ)
    (Sbad : Finset (Ideal O)) (Wkernel : 𝓢(ℝ,ℂ))
    (Z τ ν value exponent : ℝ) : Prop :=
  HighPacketSourceData η (fun _ : Slot => η₀) Q hQ72 M H hH hQM (fun _ => hQη₀)
    η₀ Wslot bslot 2 (highLocalDmax BR) e σmin σmax lowLocalTiny 6 1 lowLocalTiny I
    W₁ W₂ b₁ b₂ lo hi lowLocalTiny Mslot upper lowLocalTiny Sbad Wkernel 4 (-2)
    1 3 1 1 6 1 lowLocalTiny lowLocalTiny Z τ ν value exponent

end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighLiteralData -/

/- BEGIN ORIGINAL MODULE Analytic.JointHighLocalMasks ; sha256 21f3a1f85ebe1feaa3598e16ac792fd2de1eda44ca3780e71682bce97a5ff32d -/
section




/-! The high source's complete moving masks have a fixed polynomial cap.
The source common norms and the literal canceled-prime product supply it. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentActive CenteredMomentSectorLocalization
open CenteredMomentSupportedCorrelation CenteredMomentFirstSourceConductorCaps
open CenteredMomentOriginalCommonHarmonic
local notation "O" => HeckeFamily.O

lemma canceled_ideal_norm_le_active (C D : Ideal O) (hC : Supported C) (k : ℕ) :
    ((canceledIdeal C D k).absNorm : ℝ) ≤ normValue (activeConductor C D) := by
  rw [canceled_ideal_norm_product,active_conductor_norm_product C D hC]
  apply Finset.prod_le_prod₀
  · intro i _
    split_ifs
    · exact Nat.cast_nonneg _
    · exact zero_le_one
  · intro i _
    split_ifs
    · exact le_rfl
    · exact normValue_ge_one _ (supported_element_ne_zero _ (activePrimary_supported C D hC i))

lemma first_side_canceled_norm_cap (C D : Ideal O) (hC : Supported C) (left : Bool)
    (Z : ℝ) (hcap : (C.absNorm : ℝ) ≤ Z^(1:ℝ)) :
    ((firstSideCanceled C D left).absNorm : ℝ) ≤ Z^(1:ℝ) := by
  have hh := canceled_ideal_norm_le_active C D hC (if left then 5 else 1)
  apply hh.trans
  rw [normValue_eq_embedding]
  exact ((original_factor_caps C D hC ∅).2).trans hcap

lemma high_mask_radical_norm_cap (R T C : Ideal O) (hR : R ≠ 0) (hT : T ≠ 0) (hC : C ≠ 0)
    (Z BR : ℝ) (hZ : 1 < Z) (hRN : (R.absNorm : ℝ) ≤ Z^BR)
    (hTN : (T.absNorm : ℝ) ≤ Z^(1:ℝ)) (hCN : (C.absNorm : ℝ) ≤ Z^(1:ℝ)) :
    (((R*T)*C).radical.absNorm : ℝ) ≤ Z^(BR+2) := by
  have hnorm : (((R*T)*C).radical.absNorm : ℝ) ≤ ((R*T)*C).absNorm :=
    divisor_norm_le _ _ (mul_ne_zero (mul_ne_zero hR hT) hC)
      (Ideal.dvd_iff_le.mpr Ideal.le_radical)
  apply hnorm.trans
  simp only [map_mul,Nat.cast_mul]
  calc
    _ ≤ Z^BR*Z^(1:ℝ)*Z^(1:ℝ) := by gcongr
    _ = Z^(BR+2) := by
      rw [←Real.rpow_add (zero_lt_one.trans hZ),←Real.rpow_add (zero_lt_one.trans hZ)]
      congr 1
      ring

namespace FirstSidePresentation
variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot] {η : Character}

/-- The actual cumulative source common bounds leave just BR+2 for either
complete mask, including every canceled first prime. -/
theorem high_puncture_caps (F : FirstSidePresentation η) (s : CommonSecondKernelLabel Slot)
    (hz₁ : s.input.W₁ 0 = 0) (hz₂ : s.input.W₂ 0 = 0)
    (Z BR : ℝ) (hZ : 1 < Z) (hpuncture : s.puncture ≠ 0)
    (hR : (s.puncture.absNorm : ℝ) ≤ Z^BR)
    (hfirst : (F.C.absNorm : ℝ) ≤ Z^(1:ℝ))
    (hsource : sourceRadius s.input ≤ Z^(1:ℝ)) :
    ((F.leftPuncture s).radical.absNorm : ℝ) ≤ Z^(BR+2) ∧
      ((F.rightPuncture s).radical.absNorm : ℝ) ≤ Z^(BR+2) := by
  have hcancel₀ : firstSideCanceled F.C F.D F.side ≠ 0 :=
    canceledIdeal_ne_zero F.C F.D F.supported _
  have hcancel := first_side_canceled_norm_cap F.C F.D F.supported F.side Z hfirst
  have hc := s.actual_cumulative_norm hz₁ hz₂
  exact ⟨high_mask_radical_norm_cap _ _ _ hpuncture
      (mul_ne_zero s.hfirst.1 s.toKernelLabel.hC.1) hcancel₀ Z BR hZ hR (hc.1.trans hsource) hcancel,
    high_mask_radical_norm_cap _ _ _ hpuncture
      (mul_ne_zero s.hfirst.1 s.toKernelLabel.hD.1) hcancel₀ Z BR hZ hR (hc.2.trans hsource) hcancel⟩

end FirstSidePresentation
#print axioms canceled_ideal_norm_le_active
#print axioms FirstSidePresentation.high_puncture_caps
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighLocalMasks -/
