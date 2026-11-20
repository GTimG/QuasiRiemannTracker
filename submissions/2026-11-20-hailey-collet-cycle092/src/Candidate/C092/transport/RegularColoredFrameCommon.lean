/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
Full common and primary allocation domination with independent ordinary
characters. Adapted from Sil MixedDom3. The actual frozen coefficients,
selected divisor norms, full puncture and native subpower counts remain.
-/
import Candidate.C092.transport.RegularColoredFrameDictionary

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
open MixedUniformSource MixedFrozenSource MixedSourceAssembly MixedAllocationCost
open MixedAllocationSource MixedCommonCoefficient MixedCommonRestriction MixedLiteralAllocation
open MixedAllocatedEnergy MixedUniformAllocated MixedCommonAllocated MixedDivisorMask
open MixedCommonMasked MixedCommonSource MixedOriginalSource MixedRestrictedDictionary
open MixedFixedSupport
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentEnergyCapacityRemoval CenteredMomentNaturalFixedRaySource
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentInductionEnergy CenteredMomentCommonMaskEnergy
open CenteredMomentNaturalRowSource CenteredMomentFiniteProfileExceptional
open CenteredMomentRayMaskedFloor HeckeDyadic CenteredMomentCommonProfile
open CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass
open CenteredMomentFirstSectors CenteredMomentSourceRectangle CenteredMomentSourceMass
open CenteredMomentCommonAllocationBox CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

local instance c092LocalInst_Candidate_C092_transport_RegularColoredFrameCommon_21cecf42fea70075_001 {β : Type*} : DecidableEq (β⊕Fin 2) := Classical.decEq _
variable (M : Ideal O) [NeZero M]
local instance c092LocalInst_Candidate_C092_transport_RegularColoredFrameCommon_21cecf42fea70075_002 : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

/-- **Frozen common factor, one divisor allocation** (reduction form of
`MixedCommonAllocated.uniform_common_allocated_source`). -/
theorem frame_common_allocated_dom {α : Type*} [Fintype α] (Holes : ℕ)
    (W : ℝ→ℂ) (a b L Lslot Lcap Cap Bmask ε δ lo hi : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (hb : 1≤b) (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hBmask : 0≤Bmask) (hCapb : b≤Cap) (hLordinary : L≤Lcap) (hε : 0<ε) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z →
    ∀(η₀ : Character)(θ : α→RayQuotient.Characters M Hray)(w σ freq : α→ℝ)(t : ℝ)
      (R₀ : α→Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → (∀i,(R₀ i).card≤Holes) →
    ∀(η ω₁ ω₂ : Character)(keep : O→Prop)(Φ : 𝓢(ℝ,ℂ))(K radial : ℝ),0<K →
      Function.support (Φ:ℝ→ℂ)⊆Set.Iic radial → (∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re) →
      (∀z,keep z → z≠0) →
    ∀R G F : Id,R≠0 → G≠0 → F≠0 → ∀H : Finset PrimeIdeal,H⊆enclosure (Cap*Z^Lcap) →
      (Ideal.absNorm (∏I∈primeSupport ((R*G)*F)∪holes H,I):ℝ)≤Z^Bmask →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),∀_hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀_hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ),0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ →
      X₁≤Z^L → X₂≤Z^L → Y₁≤Z^L → Y₂≤Z^L → X₁*X₂=Y₁*Y₂ →
    ∀d : Id×Id,∀hd : d.1≠0 ∧ d.2≠0,∀B : Tuple α,∀hB : ∀j,B j≠0,
      finiteTupleProduct B=G → (∀i : liveIndices B,∀P∈H,P.val∈R₀ i.val) →
    ∀D : Id,D∣F → ∀allocation : Allocation D (Finset.univ : Finset (liveIndices B⊕Fin 2)),
    ∃Lf : Finset (ℝ×ℝ),LengthsBelow₂ Lf X₁ X₂ Y₁ Y₂ ∧
      LeafDom (coloredNativeLeaf M Hray hHray W η₀ θ Z w σ freq t η ω₁ ω₂ keep Φ K W₁ W₂
          (2*Real.pi*t₁) (2*Real.pi*t₂)) Lf
        (C*Z^ε*(F.absNorm:ℝ)^δ/(G.absNorm:ℝ)/pairNorm d/
          ((∏j,selectedDivisor D Finset.univ allocation j).absNorm:ℝ))
        (radialEnergy (fun z=>normalization (X₁*X₂) (fun i=>Z^(w i))*
          (frozenCoefficient B G R
            (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
            (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))*
          frameAllocatedLiveSum (idealCoeff ω₁) (idealCoeff ω₂) (naturalCharacter η z) (enclosure (Cap*Z^Lcap)) H
            (fun i=>supportedPool (primePool M Hray 2 (Z^(w i)))) d hd B hB G R D allocation
            (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
            (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
            (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂)) keep Φ K) := by
  obtain ⟨K₀,hK₀,hslot⟩ := slot_profile_bound W hW.continuous hWs lo hi
  let A : ℝ := (∏_i : α,K₀)^2*2^Fintype.card α
  have hA : 0<A := by
    have hKpos : 0<K₀ := zero_lt_one.trans_le hK₀
    dsimp [A]
    positivity
  obtain ⟨C,hC,hbase⟩ := frame_allocated_subsets_dom M Hray hHray (α:=α) Holes W a b L Lslot Lcap Cap
    Bmask ε δ lo hi hWs hW ha hb hLslot hLcap hCap hBmask hCapb hLordinary hε hδ
  refine ⟨C*A,mul_pos hC hA,?_⟩
  intro Z hZ η₀ θ w σ freq t R₀ hw hwL hσ hσhi hR₀ η ω₁ ω₂ keep Φ K radial hK hs hΦ hkeep R G F hR hG hF
    H hH hcap W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY
    d hd B hB hprod hHR D hDF allocation
  have hZ0 : 0<Z := zero_lt_one.trans_le hZ
  let ν := slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t
  let Wslot := fun i=>slotProfile W (σ i) (freq i)
  let P := fun i=>Z^(w i)
  obtain ⟨Lf,hLf,he⟩ := hbase Z hZ η₀ θ w σ freq t R₀ hw hwL hσ hσhi hR₀ η ω₁ ω₂ keep Φ K radial hK hs
    hΦ hkeep (R*G) F (mul_ne_zero hR hG) hF H hH hcap W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂
    hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY (d.1*B (Sum.inr 0),d.2*B (Sum.inr 1))
    ⟨mul_ne_zero hd.1 (hB _),mul_ne_zero hd.2 (hB _)⟩ (liveIndices B) hHR D hDF allocation
  refine ⟨Lf,hLf,?_⟩
  intro E hE hl
  let E' := C*Z^ε*(F.absNorm:ℝ)^δ/((∏j,selectedDivisor D Finset.univ allocation j).absNorm:ℝ)*E
  have hE' : 0≤E' := by dsimp only [E']; positivity
  have hchild : radialEnergy (fun z=>normalization (X₁*X₂) (fun i : liveIndices B=>P i.val)*
      frameAllocatedLiveSum (idealCoeff ω₁) (idealCoeff ω₂) (naturalCharacter η z) (enclosure (Cap*Z^Lcap)) H
        (fun i=>supportedPool (primePool M Hray 2 (P i))) d hd B hB G R D allocation ν Wslot P
        (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂) keep Φ K≤
        E'/pairNorm (d.1*B (Sum.inr 0),d.2*B (Sum.inr 1)) := by
    simp_rw [frame_allocated_live_row]
    apply (he E hE hl).trans_eq
    dsimp only [E']
    ring
  have hh := frozen_source_energy B hB G R hG hprod d hd (X₁*X₂) (mul_pos hX₁ hX₂)
    ν Wslot P (fun _=>K₀) (fun _=>Real.rpow_pos_of_pos hZ0 _)
    (fun i I=>slot_coefficient_norm _ R₀ t i I)
    (fun i x=>hslot (σ i) (freq i) (hσ i) (hσhi i) x) (fun _=>hK₀) 1 2 (by norm_num)
    (fun i=>(slot_profile_support W (σ i) (freq i)).trans hWs) _
    keep Φ K E' hE' hchild
  apply hh.trans_eq
  dsimp only [A,E']
  norm_num only [max_eq_right (show (1:ℝ)≤2 by norm_num)]
  ring

/-- **The squarefree divisor mask** (reduction form of
`MixedCommonMasked.uniform_common_masked_source`). -/
theorem frame_common_masked_dom {α : Type*} [Fintype α] (Holes : ℕ)
    (W : ℝ→ℂ) (a b L Lslot Lcap Cap Bmask ε δ lo hi : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (hb : 1≤b) (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hBmask : 0≤Bmask) (hCapb : b≤Cap) (hLordinary : L≤Lcap) (hε : 0<ε) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z →
    ∀(η₀ : Character)(θ : α→RayQuotient.Characters M Hray)(w σ freq : α→ℝ)(t : ℝ)
      (R₀ : α→Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → (∀i,(R₀ i).card≤Holes) →
    ∀(η ω₁ ω₂ : Character)(keep : O→Prop)(Φ : 𝓢(ℝ,ℂ))(K radial : ℝ),0<K →
      Function.support (Φ:ℝ→ℂ)⊆Set.Iic radial → (∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re) →
      (∀z,keep z → z≠0) →
    ∀R G D : Id,R≠0 → G≠0 → Squarefree D → ∀H : Finset PrimeIdeal,H⊆enclosure (Cap*Z^Lcap) →
      (Ideal.absNorm (∏I∈primeSupport ((R*G)*D)∪holes H,I):ℝ)≤Z^Bmask →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),∀_hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀_hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ),0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ →
      X₁≤Z^L → X₂≤Z^L → Y₁≤Z^L → Y₂≤Z^L → X₁*X₂=Y₁*Y₂ →
    ∀d : Id×Id,∀hd : d.1≠0 ∧ d.2≠0,∀B : Tuple α,∀hB : ∀j,B j≠0,
      finiteTupleProduct B=G → (∀i : liveIndices B,∀P∈H,P.val∈R₀ i.val) →
    ∃Lf : Finset (ℝ×ℝ),LengthsBelow₂ Lf X₁ X₂ Y₁ Y₂ ∧
      LeafDom (coloredNativeLeaf M Hray hHray W η₀ θ Z w σ freq t η ω₁ ω₂ keep Φ K W₁ W₂
          (2*Real.pi*t₁) (2*Real.pi*t₂)) Lf
        (C*Z^ε*(D.absNorm:ℝ)^δ/(G.absNorm:ℝ)/pairNorm d/(D.absNorm:ℝ))
        (radialEnergy (fun z=>normalization (X₁*X₂) (fun i=>Z^(w i))*
          (frozenCoefficient B G R
            (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
            (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))*
          TwistedRawSource.maskedLiveSum (idealCoeff ω₁) (idealCoeff ω₂) (naturalCharacter η z) (enclosure (Cap*Z^Lcap)) H
            (fun i=>supportedPool (primePool M Hray 2 (Z^(w i)))) d hd B hB G R D
            (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
            (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
            (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂)) keep Φ K) := by
  obtain ⟨C,hC,hbase⟩ := frame_common_allocated_dom M Hray hHray (α:=α) Holes W a b L Lslot Lcap Cap
    Bmask ε (δ/2) lo hi hWs hW ha hb hLslot hLcap hCap hBmask hCapb hLordinary hε (half_pos hδ)
  obtain ⟨Ccount,hCcount,hcount⟩ :=
    allocation_count_squared (Fintype.card α+2) (by omega) (δ/2) (half_pos hδ)
  refine ⟨C*Ccount,mul_pos hC hCcount,?_⟩
  intro Z hZ η₀ θ w σ freq t R₀ hw hwL hσ hσhi hR₀ η ω₁ ω₂ keep Φ K radial hK hs hΦ hkeep R G D hR hG hD
    H hH hcap W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd B hB hprod hHR
  classical
  have hZ0 : 0<Z := zero_lt_one.trans_le hZ
  let ν := slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t
  let Wslot := fun i=>slotProfile W (σ i) (freq i)
  let P := fun i=>Z^(w i)
  have hDpos : 0<(D.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.ne_zero)
  have hGpos : 0<(G.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hG)
  have hchild (al : Allocation D (Finset.univ : Finset (liveIndices B⊕Fin 2))) :=
    hbase Z hZ η₀ θ w σ freq t R₀ hw hwL hσ hσhi hR₀ η ω₁ ω₂ keep Φ K radial hK hs hΦ hkeep
      R G D hR hG hD.ne_zero H hH hcap W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂
      hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd B hB hprod hHR D (dvd_refl D) al
  choose La hLa hdoma using hchild
  refine ⟨Finset.univ.biUnion La,LengthsBelow₂.biUnion _ _ (fun al _=>hLa al),?_⟩
  intro E hE hl
  let m : ℝ := C*Z^ε*(D.absNorm:ℝ)^(δ/2)/(G.absNorm:ℝ)/pairNorm d/(D.absNorm:ℝ)
  have hd' := pairNorm_pos hd.1 hd.2
  have hm : 0≤ m := by dsimp only [m]; positivity
  let f := fun (al : Allocation D (Finset.univ : Finset (liveIndices B⊕Fin 2)))(z : O)=>
    normalization (X₁*X₂) P*(frozenCoefficient B G R ν Wslot P*
      frameAllocatedLiveSum (idealCoeff ω₁) (idealCoeff ω₂) (naturalCharacter η z) (enclosure (Cap*Z^Lcap)) H
        (fun i=>supportedPool (primePool M Hray 2 (P i))) d hd B hB G R D al ν Wslot P
        (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂)
  have hf (al : Allocation D (Finset.univ : Finset (liveIndices B⊕Fin 2))) :
      radialEnergy (f al) keep Φ K≤ m*E := by
    have h1 := hdoma al E hE (fun A p hp=>hl A p
      (Finset.mem_biUnion.mpr ⟨al,Finset.mem_univ _,hp⟩))
    apply h1.trans
    apply mul_le_mul_of_nonneg_right _ hE
    have hsel := squarefree_norm_le_selected_product D hD al
    have hnum : 0≤C*Z^ε*(D.absNorm:ℝ)^(δ/2)/(G.absNorm:ℝ)/pairNorm d := by positivity
    exact div_le_div_of_nonneg_left hnum hDpos hsel
  have hsum := radial_phase_sum
    (fun (_ : Allocation D (Finset.univ : Finset (liveIndices B⊕Fin 2))) (_ : O)=>(1:ℂ))
    f (m*E) keep Φ K radial hK hs hΦ (by intros; simp) hf
  simp only [one_mul] at hsum
  have hrow (z : O) := frame_masked_live_sum (idealCoeff ω₁) (idealCoeff ω₂) (naturalCharacter η z) (enclosure (Cap*Z^Lcap)) H
    (fun i=>supportedPool (primePool M Hray 2 (P i))) d hd B hB G R D hD ν Wslot P
    (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂
  change radialEnergy (fun z=>normalization (X₁*X₂) P*(frozenCoefficient B G R ν Wslot P*
    TwistedRawSource.maskedLiveSum (idealCoeff ω₁) (idealCoeff ω₂) (naturalCharacter η z) (enclosure (Cap*Z^Lcap)) H
      (fun i=>supportedPool (primePool M Hray 2 (P i))) d hd B hB G R D ν Wslot P
      (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂)) keep Φ K≤_
  conv_lhs =>
    arg 1
    ext z
    rw [hrow z,Finset.mul_sum,Finset.mul_sum]
  apply hsum.trans
  have hdim : Fintype.card (liveIndices B⊕Fin 2)≤Fintype.card α+2 := by
    simp only [Fintype.card_sum,Fintype.card_fin,Fintype.card_coe]
    exact Nat.add_le_add_right (Finset.card_le_univ _) 2
  apply (mul_le_mul_of_nonneg_right (hcount hdim D hD.ne_zero)
    (mul_nonneg hm hE)).trans_eq
  have hpow : (D.absNorm:ℝ)^(δ/2)*(D.absNorm:ℝ)^(δ/2)=(D.absNorm:ℝ)^δ := by
    rw [←Real.rpow_add hDpos]
    congr 1
    ring
  dsimp only [m]
  rw [←hpow]
  ring

/-- **Genuine common allocations** (reduction form of
`MixedCommonSource.uniform_common_source`). -/
theorem frame_common_source_dom {α : Type*} [Fintype α] (Holes : ℕ)
    (W : ℝ→ℂ) (a b L Lslot Lcap Cap Bmask ε δ lo hi : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (hb : 1≤b) (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hBmask : 0≤Bmask) (hCapb : b≤Cap) (hLordinary : L≤Lcap) (hε : 0<ε) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z →
    ∀(η₀ : Character)(θ : α→RayQuotient.Characters M Hray)(w σ freq : α→ℝ)(t : ℝ)
      (R₀ : α→Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → (∀i,(R₀ i).card≤Holes) →
    ∀(η ω₁ ω₂ : Character)(keep : O→Prop)(Φ : 𝓢(ℝ,ℂ))(K radial : ℝ),0<K →
      Function.support (Φ:ℝ→ℂ)⊆Set.Iic radial → (∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re) →
      (∀z,keep z → z≠0) →
    ∀R G D : Id,R≠0 → G≠0 → Squarefree D → ∀H : Finset PrimeIdeal,H⊆enclosure (Cap*Z^Lcap) →
      (Ideal.absNorm (∏I∈primeSupport ((R*G)*D)∪holes H,I):ℝ)≤Z^Bmask →
      (∀i,∀P∈H,P.val∈R₀ i) →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),∀_hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀_hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ),0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ →
      X₁≤Z^L → X₂≤Z^L → Y₁≤Z^L → Y₂≤Z^L → X₁*X₂=Y₁*Y₂ →
    ∀d : Id×Id,∀hd : d.1≠0 ∧ d.2≠0,
    ∃Lf : Finset (ℝ×ℝ),LengthsBelow₂ Lf X₁ X₂ Y₁ Y₂ ∧
      LeafDom (coloredNativeLeaf M Hray hHray W η₀ θ Z w σ freq t η ω₁ ω₂ keep Φ K W₁ W₂
          (2*Real.pi*t₁) (2*Real.pi*t₂)) Lf
        (C*Z^ε*(G.absNorm:ℝ)^δ*(D.absNorm:ℝ)^δ/(G.absNorm:ℝ)/pairNorm d/(D.absNorm:ℝ))
        (radialEnergy (fun z=>frameCommonMaskedRow (idealCoeff ω₁) (idealCoeff ω₂) (naturalCharacter η z)
          (enclosure (Cap*Z^Lcap)) H (fun i=>supportedPool (primePool M Hray 2 (Z^(w i))))
          d hd G R D
          (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
          (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
          (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂) keep Φ K) := by
  obtain ⟨C,hC,hbase⟩ := frame_common_masked_dom M Hray hHray (α:=α) Holes W a b L Lslot Lcap Cap
    Bmask ε δ lo hi hWs hW ha hb hLslot hLcap hCap hBmask hCapb hLordinary hε hδ
  obtain ⟨Ccount,hCcount,hcount⟩ := genuine_count_squared (Fintype.card α+2) δ hδ
  refine ⟨C*Ccount,mul_pos hC hCcount,?_⟩
  intro Z hZ η₀ θ w σ freq t R₀ hw hwL hσ hσhi hR₀ η ω₁ ω₂ keep Φ K radial hK hs hΦ hkeep R G D hR hG hD
    H hH hcap hHR W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd
  classical
  let ν := slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t
  let Wslot := fun i=>slotProfile W (σ i) (freq i)
  let P := fun i=>Z^(w i)
  let T := sourcePools (fun i=>supportedPool (primePool M Hray 2 (P i))) d hd b X₁ X₂ Y₁ Y₂
  have hchild (B : actualAllocations T G) :=
    hbase Z hZ η₀ θ w σ freq t R₀ hw hwL hσ hσhi hR₀ η ω₁ ω₂ keep Φ K radial hK hs hΦ hkeep
      R G D hR hG hD H hH hcap W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂
      hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd B.val
      (allocation_data T G B.val (Finset.mem_filter.mp B.property).1).1
      (Finset.mem_filter.mp B.property).2 (fun i=>hHR i.val)
  choose LB hLB hdomB using hchild
  refine ⟨Finset.univ.biUnion LB,LengthsBelow₂.biUnion _ _ (fun B _=>hLB B),?_⟩
  intro E hE hl
  let m : ℝ := C*Z^ε*(D.absNorm:ℝ)^δ/(G.absNorm:ℝ)/pairNorm d/(D.absNorm:ℝ)
  have hd' := pairNorm_pos hd.1 hd.2
  have hm : 0≤ m := by dsimp only [m]; positivity
  let f := fun (B : actualAllocations T G)(z : O)=>
    normalization (X₁*X₂) P*(frozenCoefficient B.val G R ν Wslot P*
      TwistedRawSource.maskedLiveSum (idealCoeff ω₁) (idealCoeff ω₂) (naturalCharacter η z) (enclosure (Cap*Z^Lcap)) H
        (fun i=>supportedPool (primePool M Hray 2 (P i))) d hd B.val
        (allocation_data T G B.val (Finset.mem_filter.mp B.property).1).1 G R D ν Wslot P
        (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂)
  let phase := fun (B : actualAllocations T G)(_ : O)=>
    frozenWeight (punctureProduct (enclosure (Cap*Z^Lcap)) H) B.val *
      TwistedRawSource.ordinaryColor (idealCoeff ω₁) (idealCoeff ω₂) B.val
  have hf (B : actualAllocations T G) : radialEnergy (f B) keep Φ K≤ m*E :=
    hdomB B E hE (fun A p hp=>hl A p (Finset.mem_biUnion.mpr ⟨B,Finset.mem_univ _,hp⟩))
  have hphase : ∀B z,keep z→‖phase B z‖≤1 := by
    intro B z _
    dsimp only [phase]
    have hc : ‖TwistedRawSource.ordinaryColor (idealCoeff ω₁) (idealCoeff ω₂) B.val‖ ≤ 1 := by
      unfold TwistedRawSource.ordinaryColor
      rw [norm_mul]
      exact (mul_le_mul (idealCoeff_norm_le_one ω₁ _) (idealCoeff_norm_le_one ω₂ _)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    rw [norm_mul]
    unfold frozenWeight
    split_ifs <;> simpa using hc
  have hsum := radial_phase_sum phase f (m*E) keep Φ K radial hK hs hΦ hphase hf
  change radialEnergy (fun z=>∑B : actualAllocations T G,phase B z*f B z) keep Φ K≤_
  apply hsum.trans
  rw [Fintype.card_coe]
  have hdim : Fintype.card (α⊕Fin 2)≤Fintype.card α+2 := by
    simp only [Fintype.card_sum,Fintype.card_fin,le_refl]
  apply (mul_le_mul_of_nonneg_right (hcount hdim T G hG) (mul_nonneg hm hE)).trans_eq
  dsimp only [m]
  ring

/-- **The original residual-column source** (reduction form of
`MixedOriginalSource.uniform_original_source`): the seed is removed because it divides the
genuine common ideal. -/
theorem frame_original_source_dom {α : Type*} [Fintype α] (Holes : ℕ)
    (W : ℝ→ℂ) (a b L Lslot Lcap Cap Bmask ε δ lo hi : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (hb : 1≤b) (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hBmask : 0≤Bmask) (hCapb : b≤Cap) (hLordinary : L≤Lcap) (hε : 0<ε) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z →
    ∀(η₀ : Character)(θ : α→RayQuotient.Characters M Hray)(w σ freq : α→ℝ)(t : ℝ)
      (R₀ : α→Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → (∀i,(R₀ i).card≤Holes) →
    ∀(η ω₁ ω₂ : Character)(keep : O→Prop)(Φ : 𝓢(ℝ,ℂ))(K radial : ℝ),0<K →
      Function.support (Φ:ℝ→ℂ)⊆Set.Iic radial → (∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re) →
      (∀z,keep z → z≠0) →
    ∀R G seed D : Id,R≠0 → ∀hG : G≠0,seed∣G → Squarefree D →
    ∀H : Finset PrimeIdeal,H⊆enclosure (Cap*Z^Lcap) →
      (Ideal.absNorm (∏I∈primeSupport ((R*G)*D)∪holes H,I):ℝ)≤Z^Bmask →
      (∀i,∀P∈H,P.val∈R₀ i) →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),∀_hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀_hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ),0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ →
      X₁≤Z^L → X₂≤Z^L → Y₁≤Z^L → Y₂≤Z^L → X₁*X₂=Y₁*Y₂ →
    ∀d : Id×Id,∀hd : d.1≠0 ∧ d.2≠0,
    ∃Lf : Finset (ℝ×ℝ),LengthsBelow₂ Lf X₁ X₂ Y₁ Y₂ ∧
      LeafDom (coloredNativeLeaf M Hray hHray W η₀ θ Z w σ freq t η ω₁ ω₂ keep Φ K W₁ W₂
          (2*Real.pi*t₁) (2*Real.pi*t₂)) Lf
        (C*Z^ε*(G.absNorm:ℝ)^δ*(D.absNorm:ℝ)^δ/(G.absNorm:ℝ)/pairNorm d/(D.absNorm:ℝ))
        (radialEnergy (fun z=>frameOriginalMaskedRow (idealCoeff ω₁) (idealCoeff ω₂) (naturalCharacter η z)
          (enclosure (Cap*Z^Lcap)) H (fun i=>supportedPool (primePool M Hray 2 (Z^(w i))))
          d hd G R seed D hG
          (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
          (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
          (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂) keep Φ K) := by
  obtain ⟨C,hC,hbase⟩ := frame_common_source_dom M Hray hHray (α:=α) Holes W a b L Lslot Lcap Cap
    Bmask ε δ lo hi hWs hW ha hb hLslot hLcap hCap hBmask hCapb hLordinary hε hδ
  refine ⟨C,hC,?_⟩
  intro Z hZ η₀ θ w σ freq t R₀ hw hwL hσ hσhi hR₀ η ω₁ ω₂ keep Φ K radial hK hs hΦ hkeep R G seed D
    hR hG hseed hD H hH hcap hHR W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄
    hXY d hd
  obtain ⟨Lf,hLf,he⟩ := hbase Z hZ η₀ θ w σ freq t R₀ hw hwL hσ hσhi hR₀ η ω₁ ω₂ keep Φ K radial hK hs
    hΦ hkeep R G D hR hG hD H hH hcap hHR W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂
    hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd
  have hp (i : α) (I : Id) (hI : I∈supportedPool (primePool M Hray 2 (Z^(w i)))) : Prime I :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2.1
  refine ⟨Lf,hLf,he.of_eq ?_⟩
  congr 1
  funext z
  exact frame_original_masked_row_eq (idealCoeff ω₁) (idealCoeff ω₂) (naturalCharacter η z) (enclosure (Cap*Z^Lcap)) H
    (fun i=>supportedPool (primePool M Hray 2 (Z^(w i)))) hp d hd G R seed D hG hseed
    (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
    (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
    (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂

end

end QRH.Cycle092.RegularColoredForward

#print axioms QRH.Cycle092.RegularColoredForward.frame_common_allocated_dom
#print axioms QRH.Cycle092.RegularColoredForward.frame_common_masked_dom
#print axioms QRH.Cycle092.RegularColoredForward.frame_common_source_dom
#print axioms QRH.Cycle092.RegularColoredForward.frame_original_source_dom
