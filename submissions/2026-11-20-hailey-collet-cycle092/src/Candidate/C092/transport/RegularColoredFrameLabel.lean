/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
Actual physical-label packing for two independently colored ordinary
coordinates. Adapted from Sil Label. It uses the native V-row map, exact
keep/character transfer and original label mass, including G and D savings.
-/
import Candidate.C092.transport.RegularColoredFrameHeight
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

local instance c092LocalInst_Candidate_C092_transport_RegularColoredFrameLabel_2d8b2a39a51f9a7a_001 {β : Type*} : DecidableEq (β⊕Fin 2) := Classical.decEq _
variable (M : Ideal O) [NeZero M]
local instance c092LocalInst_Candidate_C092_transport_RegularColoredFrameLabel_2d8b2a39a51f9a7a_002 : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

theorem frame_originalMaskedRow_congr_char {α : Type*} [Fintype α] (ω₁ ω₂ : Id →*₀ ℂ) (χ χ' : Character)
    (S H : Finset PrimeIdeal) (pool : α→Finset Id) (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0)
    (G R seed D : Id) (hG : G≠0) (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ)
    (h : ∀I : Id,IsCoprime G I → idealCoeff χ I=idealCoeff χ' I) :
    frameOriginalMaskedRow ω₁ ω₂ χ S H pool d hd G R seed D hG ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂=
      frameOriginalMaskedRow ω₁ ω₂ χ' S H pool d hd G R seed D hG ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ := by
  unfold frameOriginalMaskedRow
  congr 1
  apply Finset.sum_congr rfl
  intro I _
  by_cases hI : IsCoprime G I ∧ D∣I
  · simp [hI,h I hI.1]
  · simp [hI]

def framePackedLeaf {α : Type*} (W : ℝ→ℂ) (η₀ : Character) (θ : α→RayQuotient.Characters M Hray)
    (Z : ℝ) (w σ freq : α→ℝ) (t : ℝ) (σA ω₁ ω₂ : Character) (Q : Id) (V : O) (K : ℝ)
    (W₁ W₂ : ℝ→ℂ) (t₁ t₂ : ℝ) : Finset α → ℝ → ℝ → ℝ :=
  coloredNativeLeaf M Hray hHray W η₀ θ Z w σ freq t σA ω₁ ω₂ (packedKeep σA Q V) ballProfile
    (((Ideal.span {V}).absNorm:ℝ)*K) W₁ W₂ t₁ t₂

def frameLabelEnergy {α : Type*} [Fintype α] (W : ℝ→ℂ) (η₀ : Character)
    (θ : α→RayQuotient.Characters M Hray) (Z : ℝ) (w σ freq : α→ℝ) (t : ℝ) (R₀ : α→Finset Id)
    (τ ω₁ ω₂ : Character) (Q : Id) (n : Fin 4→ℤ) (Cap Lcap : ℝ) (R G : Id) (hG : G≠0) (seed D : Id)
    (H : Finset PrimeIdeal) (W₁ W₂ : ℝ→ℂ) (t₁ t₂ b X₁ X₂ Y₁ Y₂ : ℝ) (d : Id×Id)
    (hd : d.1≠0 ∧ d.2≠0) (v : ℝ) : ℝ :=
  sourceRestrictedEnergy (canonicalRadial τ Q n).keep
    (residualPool G hG (finiteColumns (Fintype.piFinset
      (sourcePools (fun i=>supportedPool (primePool M Hray 2 (Z^(w i)))) d hd b X₁ X₂ Y₁ Y₂))))
    (fun I=>if IsCoprime G I ∧ D∣I then
      frameOriginalColumn (idealCoeff ω₁) (idealCoeff ω₂) (enclosure (Cap*Z^Lcap)) H
        (fun i=>supportedPool (primePool M Hray 2 (Z^(w i)))) d hd R seed
        (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
        (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
        (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂ (G*I) else 0)
    (heightCoeff τ v) ballProfile (dyadicScale (n 1))

/-- **Label reduction.**  One second-step label's literal one-sided energy (the left side of
FP's `MixedCanonicalEnvelope.uniform_canonical_source_envelope`) is dominated by the packed
canonical leaves, with the label mass.  The constant precedes every label datum. -/
theorem frame_label_reduction {α : Type*} [Fintype α] (Holes : ℕ)
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
    ∃Lf : Finset (ℝ×ℝ),LengthsBelow₂ Lf X₁ X₂ Y₁ Y₂ ∧
      LeafDom (framePackedLeaf M Hray hHray W η₀ θ Z w σ freq (t+v) σA ω₁ ω₂ Q V (dyadicScale (n 1)) W₁ W₂
          (2*Real.pi*(t₁+v/(2*Real.pi))) (2*Real.pi*(t₂+v/(2*Real.pi)))) Lf
        (labelMass C Z ε δ w X₁ X₂ G D d)
        (frameLabelEnergy M Hray hHray W η₀ θ Z w σ freq t R₀ τ ω₁ ω₂ Q n Cap Lcap R G hG seed D H
          W₁ W₂ t₁ t₂ b X₁ X₂ Y₁ Y₂ d hd v) := by
  obtain ⟨C,hC,hbase⟩ := frame_original_source_dom M Hray hHray (α:=α) Holes W a b L Lslot Lcap Cap
    Bmask ε δ lo hi hWs hW ha hb hLslot hLcap hCap hBmask hCapb hLordinary hε hδ
  refine ⟨C,hC,?_⟩
  intro Z hZ η₀ θ w σ freq t R₀ hw hwL hσ hσhi hR₀ τ σA ω₁ ω₂ Q n V wm hV hwm hcoef R G seed D hR hG
    hseed hD hGw H hH hcap hHR W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄
    hXY d hd v
  have hZ0 : 0<Z := zero_lt_one.trans_le hZ
  let pool := fun i=>supportedPool (primePool M Hray 2 (Z^(w i)))
  have hp (i : α) (I : Id) (hI : I∈pool i) : Prime I :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2.1
  have hP (i : α) : 0<Z^(w i) := Real.rpow_pos_of_pos hZ0 _
  let K := dyadicScale (n 1)
  have hK : 0<K := dyadicScale_pos _
  have hNV : 0<((Ideal.span {V}).absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hV))
  -- the exact height dictionary
  have hh := frame_canonical_source_height_energy (idealCoeff ω₁) (idealCoeff ω₂) τ v (enclosure (Cap*Z^Lcap)) H pool hp d hd
    G R seed D hG (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t
    (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i)) hP W₁ W₂ t₁ t₂ b X₁ X₂ Y₁ Y₂
    hX₁ hX₂ hY₁ hY₂ hXY (canonicalRadial τ Q n).keep (fun z hz=>hz.1) ballProfile K
  -- packing at the physical row
  have hpack := radialEnergy_pack
    (fun z=>frameOriginalMaskedRow (idealCoeff ω₁) (idealCoeff ω₂) (naturalCharacter τ z) (enclosure (Cap*Z^Lcap)) H pool d hd
      G R seed D hG (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ (t+v))
      (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
      (phaseProfile W₁ (t₁+v/(2*Real.pi))) (phaseProfile W₂ (t₂+v/(2*Real.pi))) b X₁ X₂ Y₁ Y₂)
    (fun y=>frameOriginalMaskedRow (idealCoeff ω₁) (idealCoeff ω₂) (naturalCharacter σA y) (enclosure (Cap*Z^Lcap)) H pool d hd
      G R seed D hG (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ (t+v))
      (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
      (phaseProfile W₁ (t₁+v/(2*Real.pi))) (phaseProfile W₂ (t₂+v/(2*Real.pi))) b X₁ X₂ Y₁ Y₂)
    (canonicalRadial τ Q n).keep (packedKeep σA Q V) ballProfile K V hV
    (by
      intro z
      rw [QRH.SilDensitySplit.CubeFree.Packet.keep_transfer τ σA Q n V wm z hwm hV hcoef]
      exact ⟨fun h=>⟨dvd_mul_right V z,h⟩,fun h=>h.2⟩)
    (fun y hy=>hy.1)
    (by
      intro z hz
      have hz0 : z≠0 := hz.1
      apply frame_originalMaskedRow_congr_char
      intro I hI
      by_cases hs : Supported I
      · exact QRH.SilDensitySplit.CubeFree.Packet.naturalCharacter_transfer τ σA V wm z hV hz0 hcoef I hs (hGw I hI)
      · rw [natural_character_off_supported τ z hz0 I hs,
          natural_character_off_supported σA (V*z) (mul_ne_zero hV hz0) I hs])
  -- the source chain on the packed state
  obtain ⟨Lf,hLf,he⟩ := hbase Z hZ η₀ θ w σ freq (t+v) R₀ hw hwL hσ hσhi hR₀ σA ω₁ ω₂
    (packedKeep σA Q V) ballProfile (((Ideal.span {V}).absNorm:ℝ)*K) 2 (mul_pos hNV hK)
    ball_support (fun _=>ballProfile_nonneg _) (packedKeep_ne_zero σA Q V)
    R G seed D hR hG hseed hD H hH hcap hHR W₁ W₂ hs₁ hs₂
    (t₁+v/(2*Real.pi)) (t₂+v/(2*Real.pi)) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd
  refine ⟨Lf,hLf,?_⟩
  have hT : 0<X₁*X₂*∏i,Z^(w i) :=
    mul_pos (mul_pos hX₁ hX₂) (Finset.prod_pos (fun i _=>hP i))
  have hlabel := (div_eq_iff hT.ne').mp hh
  unfold frameLabelEnergy
  rw [hlabel,hpack]
  have hs := he.smul hT.le
  refine (hs.of_eq (by ring)).mass_le (le_of_eq ?_)
  unfold labelMass
  ring


end
end QRH.Cycle092.RegularColoredForward

#print axioms QRH.Cycle092.RegularColoredForward.frame_label_reduction
