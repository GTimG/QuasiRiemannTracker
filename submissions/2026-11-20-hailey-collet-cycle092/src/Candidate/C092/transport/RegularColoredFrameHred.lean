/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
The genuine colored physical label is bounded by one native packed
two-anchor child on a surviving original slot subset, at positive lengths
below one original/reference pair. The exact native label mass is retained.
-/
import Candidate.C092.transport.RegularColoredFrameLeaf
import Submissions.sil_density_split_20261026.CubeFree.Packet.Reduce.Label
import Submissions.sil_density_split_20261026.CubeFree.FP.MixedHeightEnergy
import Submissions.sil_density_split_20261026.CubeFree.Packet.Dictionary
import Submissions.sil_density_split_20261026.CubeFree.Packet.Sublattice
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ChildState

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace QRH.Cycle092.RegularColoredForward
open Candidate.FourthPower.KernelAssignmentReindex Candidate.FourthPower.NativeFiniteHoles Candidate.FourthPower.KernelNaturalSlots
open QRH.SilDensitySplit.CubeFree.FP
open QRH.SilDensitySplit.CubeFree.Packet.Reduce

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open ReferencePrimeEnclosure MixedCompletedRows
open NativeInjectiveEnergy
open MixedCenteredEnergy MixedLiveRows MixedLiveNormalization MixedCanonicalSource
open MixedCommonCoefficient MixedCommonRestriction MixedLiteralAllocation
open MixedCommonSource MixedOriginalSource MixedRestrictedDictionary MixedHeightEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentWholeSlotDeletion
open CenteredMomentEnergyCapacityRemoval CenteredMomentNaturalFixedRaySource
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentInductionEnergy CenteredMomentCommonMaskEnergy
open CenteredMomentNaturalRowSource CenteredMomentFiniteProfileExceptional
open CenteredMomentRayMaskedFloor HeckeDyadic CenteredMomentCommonProfile
open CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass
open CenteredMomentFirstSectors CenteredMomentSourceRectangle CenteredMomentSourceMass
open CenteredMomentRestrictedSource CenteredMomentHeckeColumnWindow
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState CenteredMomentEnergyChildState
open CenteredMomentEnergyReferenceChild CenteredMomentEnergySlotHeight
open CenteredMomentEnergyAllocatedChildren CenteredMomentLattice CenteredMomentTwist
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondExceptionalFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentSectorLocalization CenteredMomentCanonicalFirst
open CenteredMomentRetainedEnergy CenteredMomentHeckeSlots CenteredMomentHeckeExpansion
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

local instance c092LocalInst_Candidate_C092_transport_RegularColoredFrameHred_44ab2feddf1f3370_001 {β : Type*} : DecidableEq (β⊕Fin 2) := Classical.decEq _
variable (M : Ideal O) [NeZero M]
local instance c092LocalInst_Candidate_C092_transport_RegularColoredFrameHred_44ab2feddf1f3370_002 : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

theorem frame_label_reduction_single {α : Type} [Fintype α] (Holes : ℕ)
    (W : ℝ→ℂ) (a b L Lslot Lcap Cap Bmask ε δ lo hi : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (hb : 1≤b) (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hBmask : 0≤Bmask) (hCapb : b≤Cap) (hLordinary : L≤Lcap) (hε : 0<ε) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z →
    ∀(η₀ : Character)(θ : α→RayQuotient.Characters M Hray)(w σ freq : α→ℝ)(t : ℝ)
      (R₀ : α→Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → (∀i,(R₀ i).card≤Holes) →
    ∀(τ σA ω₁ ω₂ : Character)(Q : Id)(n : Fin 4→ℤ)(V wm : O),V≠0 → wm≠0 →
      (∀I : Id,Supported I → IsCoprime I (Ideal.span {wm}) →
        idealCoeff τ I=idealCoeff σA I*CanonicalRowCompletion.idealRowHom V I) →
    ∀R G seed D : Id,R≠0 → ∀hG : G≠0,seed∣G → Squarefree D →
      (∀I : Id,IsCoprime G I → IsCoprime I (Ideal.span {wm})) →
    ∀H : Finset PrimeIdeal,H⊆enclosure (Cap*Z^Lcap) →
      (Ideal.absNorm (∏I∈primeSupport ((R*G)*D)∪holes H,I):ℝ)≤Z^Bmask →
      (∀i,∀P∈H,P.val∈R₀ i) →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),∀_hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀_hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ),0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ →
      X₁≤Z^L → X₂≤Z^L → Y₁≤Z^L → Y₂≤Z^L → X₁*X₂=Y₁*Y₂ →
    ∀d : Id×Id,∀hd : d.1≠0 ∧ d.2≠0,∀v : ℝ,
    frameLabelEnergy M Hray hHray W η₀ θ Z w σ freq t R₀ τ ω₁ ω₂ Q n Cap Lcap R G hG seed D H
      W₁ W₂ t₁ t₂ b X₁ X₂ Y₁ Y₂ d hd v ≤ 0 ∨
    ∃ (A : Finset α) (X₁' X₂' : ℝ), 0<X₁' ∧ 0<X₂' ∧
      ((X₁'≤X₁ ∧ X₂'≤X₂) ∨ (X₁'≤Y₁ ∧ X₂'≤Y₂)) ∧
      frameLabelEnergy M Hray hHray W η₀ θ Z w σ freq t R₀ τ ω₁ ω₂ Q n Cap Lcap R G hG seed D H
        W₁ W₂ t₁ t₂ b X₁ X₂ Y₁ Y₂ d hd v ≤
      labelMass C Z ε δ w X₁ X₂ G D d *
        GroupedPair.pairEnergy (σA.product ω₁) (σA.product ω₂)
          (fixedBadMask*OAI.ConcretePrimeRowBridge.idealGenerator 1) 1 1
          (fun y=>∏i∈A,normalizedSlot σA (fixedBadMask*OAI.ConcretePrimeRowBridge.idealGenerator 1)
            1 y (primePool M Hray 2 (Z^(w i)))
            (slotBeta M Hray hHray W η₀ θ Z w σ freq i) (t+v) (Z^(w i)))
          (2*Real.pi*(t₁+v/(2*Real.pi))) (2*Real.pi*(t₂+v/(2*Real.pi)))
          W₁ W₂ X₁' X₂' (packedKeep σA Q V) ballProfile
          (((Ideal.span {V}).absNorm:ℝ)*dyadicScale (n 1)) := by
  obtain ⟨C,hC,hred⟩ := frame_label_reduction M Hray hHray (α:=α) Holes W a b L Lslot Lcap Cap
    Bmask ε δ lo hi hWs hW ha hb hLslot hLcap hCap hBmask hCapb hLordinary hε hδ
  refine ⟨C,hC,?_⟩
  intro Z hZ η₀ θ w σ freq t R₀ hw hwL hσ hσhi hR₀ τ σA ω₁ ω₂ Q n V wm hV hwm hcoef
    R G seed D hR hG hseed hD hGw H hH hcap hHR W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂
    hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd v
  obtain ⟨Lf,hLf,hdom⟩ := hred Z hZ η₀ θ w σ freq t R₀ hw hwL hσ hσhi hR₀
    τ σA ω₁ ω₂ Q n V wm hV hwm hcoef R G seed D hR hG hseed hD hGw H hH hcap hHR
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd v
  rcases hdom.exists_leaf (coloredNativeLeaf_nonneg M Hray hHray W η₀ θ Z w σ freq (t+v)
    σA ω₁ ω₂ (packedKeep σA Q V) ballProfile _ (fun _=>ballProfile_nonneg _) W₁ W₂ _ _) with
    hn | ⟨A,p,hp,he⟩
  · exact Or.inl hn
  · have hl := hLf p hp
    refine Or.inr ⟨A,p.1,p.2,hl.1,hl.2.1,hl.2.2,?_⟩
    unfold framePackedLeaf at he
    rw [frameNativeLeaf_pairEnergy M Hray hHray W η₀ θ Z w σ freq (t+v) σA ω₁ ω₂
      (packedKeep σA Q V) (packedKeep_ne_zero σA Q V) ballProfile _ W₁ W₂ a b ha hs₁ hs₂
      _ _ A p.1 p.2 hl.1 hl.2.1] at he
    exact he

end
end QRH.Cycle092.RegularColoredForward

#print axioms QRH.Cycle092.RegularColoredForward.frame_label_reduction_single
