/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
Uniform surviving-slot, frozen-source and complete frozen-family
domination with two independent ordinary characters. Adapted from Sil
MixedDom, using the actual shared TwistedRawSource frozen/canonical rows.
-/
import Candidate.C092.transport.RegularColoredForwardDomSource
import Candidate.C092.transport.TwistedRawSourceFrozen
import Submissions.sil_density_split_20261026.CubeFree.Packet.Reduce.MixedDom3
import Candidate.C092.transport.RegularColoredForwardCanonical
import Submissions.sil_density_split_20261026.CubeFree.FP.MixedAllocationSource

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
open KernelMarkedRows KernelRowPools KernelRowProfiles
open KernelRowExpansion KernelLabelledSlots KernelPunctureRows
open MixedTupleRows MixedCompletedRows RestorationFamily ReferencePrimeEnclosure
open NativeInjectiveEnergy NativeForwardEnergy NativePuncturedForward
open NativePuncturedInjective
open MixedCenteredEnergy MixedLiveRows MixedLiveNormalization MixedCanonicalSource
open MixedUniformSource MixedFrozenSource MixedSourceAssembly MixedAllocationCost
open MixedAllocationSource MixedCommonCoefficient MixedCommonRestriction
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentEnergyCapacityRemoval CenteredMomentNaturalFixedRaySource
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentInductionEnergy CenteredMomentCommonMaskEnergy
open IdealMobiusDivisorSum (support_prime)
open CenteredMomentNaturalRowSource CenteredMomentFiniteProfileExceptional
open CenteredMomentRayMaskedFloor HeckeDyadic CenteredMomentCommonProfile
open CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass
open CenteredMomentFirstSectors CenteredMomentSourceRectangle CenteredMomentSourceMass
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

variable (M : Ideal O) [NeZero M]
local instance c092LocalInst_Candidate_C092_transport_RegularColoredFrameSources_c1dedfb4e6914910_001 : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

/-- Leaves on a subtype of the slots, restated for a `Finset` of slots. -/
theorem coloredNativeLeaf_finset {α : Type*} (T : Finset α) (W : ℝ→ℂ) (η₀ : Character)
    (θ : α→RayQuotient.Characters M Hray) (Z : ℝ) (w σ freq : α→ℝ) (t : ℝ) (η ω₁ ω₂ : Character)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (W₁ W₂ : ℝ→ℂ) (t₁ t₂ : ℝ)
    (A : Finset T) (X₁ X₂ : ℝ) :
    coloredNativeLeaf M Hray hHray W η₀ (fun i : T=>θ i.val) Z (fun i=>w i.val) (fun i=>σ i.val)
        (fun i=>freq i.val) t η ω₁ ω₂ keep Φ K W₁ W₂ t₁ t₂ A X₁ X₂ =
      coloredNativeLeaf M Hray hHray W η₀ θ Z w σ freq t η ω₁ ω₂ keep Φ K W₁ W₂ t₁ t₂
        (A.map (Function.Embedding.subtype (fun i=>i∈T))) X₁ X₂ :=
  coloredNativeLeaf_subtype M Hray hHray (fun i=>i∈T) W η₀ θ Z w σ freq t η ω₁ ω₂ keep Φ K W₁ W₂ t₁ t₂ A X₁ X₂

/-- **The source on every remaining marked subset** (reduction form of
`MixedUniformSource.uniform_source`); the constant precedes the subset. -/
theorem frame_uniform_source_dom {α : Type*} [Fintype α] (Holes : ℕ)
    (W : ℝ→ℂ) (a b L Lslot Lcap Cap Bmask ε lo hi : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (hb : 1≤b) (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hBmask : 0≤Bmask) (hCapb : b≤Cap) (hLordinary : L≤Lcap) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z →
    ∀(η₀ : Character)(θ : α→RayQuotient.Characters M Hray)(w σ freq : α→ℝ)(t : ℝ)
      (R₀ : α→Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → (∀i,(R₀ i).card≤Holes) →
    ∀(η ω₁ ω₂ : Character)(keep : O→Prop)(Φ : 𝓢(ℝ,ℂ))(K radial : ℝ),0<K →
      Function.support (Φ:ℝ→ℂ)⊆Set.Iic radial → (∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re) →
      (∀z,keep z → z≠0) →
    ∀R : Id,R≠0 → ∀H : Finset PrimeIdeal,H⊆enclosure (Cap*Z^Lcap) →
      (Ideal.absNorm (∏I∈primeSupport R∪holes H,I):ℝ)≤Z^Bmask →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),∀_hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀_hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ),0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ →
      X₁≤Z^L → X₂≤Z^L → Y₁≤Z^L → Y₂≤Z^L → X₁*X₂=Y₁*Y₂ →
    ∀d : Id×Id,d.1≠0 → d.2≠0 → ∀T : Finset α,
      (∀i : T,∀P∈H,P.val∈R₀ i.val) →
    ∃Lf : Finset (ℝ×ℝ),LengthsBelow₂ Lf X₁ X₂ Y₁ Y₂ ∧
      LeafDom (coloredNativeLeaf M Hray hHray W η₀ θ Z w σ freq t η ω₁ ω₂ keep Φ K W₁ W₂
          (2*Real.pi*t₁) (2*Real.pi*t₂)) Lf (C*Z^ε/pairNorm d)
        (radialEnergy (fun z=>normalization (X₁*X₂) (fun i : T=>Z^(w i.val))*
          coloredCanonicalSource (naturalCharacter η z) (idealCoeff ω₁) (idealCoeff ω₂) (enclosure (Cap*Z^Lcap)) H R
            (fun i : T=>supportedPool (primePool M Hray 2 (Z^(w i.val))))
            (slotCoefficient (fun i : T=>relativeCharacter M Hray hHray η₀ (θ i.val))
              (fun i=>R₀ i.val) t)
            (fun i : T=>slotProfile W (σ i.val) (freq i.val)) (fun i : T=>Z^(w i.val))
            (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂ d) keep Φ K) := by
  choose CT hCT hbase using fun T : Finset α=>
    colored_source_dom M Hray hHray (α:=T) Holes W a b L Lslot Lcap Cap Bmask ε lo hi
      hWs hW ha hb hLslot hLcap hCap hBmask hCapb hLordinary hε
  let C := 1+∑T : Finset α,CT T
  have hC : 0<C := by
    have hh := Finset.sum_nonneg (fun T (_ : T∈(Finset.univ : Finset (Finset α)))=>(hCT T).le)
    dsimp [C]
    linarith
  have hCTC (T : Finset α) : CT T≤C := by
    have hh := Finset.single_le_sum (s:=Finset.univ) (f:=CT)
      (fun T _=>(hCT T).le) (Finset.mem_univ T)
    dsimp [C]
    linarith
  refine ⟨C,hC,?_⟩
  intro Z hZ η₀ θ w σ freq t R₀ hw hwL hσ hσhi hR₀ η ω₁ ω₂ keep Φ K radial hK hs hΦ hkeep R hR H hH
    hcap W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd₁ hd₂ T hHR
  obtain ⟨Lf,hLf,he⟩ := hbase T Z hZ η₀ (fun i=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val)
    (fun i=>freq i.val) t (fun i=>R₀ i.val) (fun i=>hw i.val) (fun i=>hwL i.val)
    (fun i=>hσ i.val) (fun i=>hσhi i.val) (fun i=>hR₀ i.val) η ω₁ ω₂ keep Φ K radial hK hs hΦ hkeep
    R hR H hH hHR hcap W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY
    d hd₁ hd₂
  refine ⟨Lf,hLf,((he.reindex (fun A=>A.map (Function.Embedding.subtype (fun i=>i∈T)))
    (fun A X₁ X₂=>coloredNativeLeaf_finset M Hray hHray T W η₀ θ Z w σ freq t η ω₁ ω₂ keep Φ K W₁ W₂
      (2*Real.pi*t₁) (2*Real.pi*t₂) A X₁ X₂))).mass_le ?_⟩
  have hZε : 0≤Z^ε := Real.rpow_nonneg (zero_le_one.trans hZ) _
  have hd := pairNorm_pos hd₁ hd₂
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hCTC T) hZε) hd.le

/-! ### Frozen coefficients and live sums -/

/-- **The live sum with its frozen coefficient** (reduction form of
`MixedFrozenSource.uniform_live_source`).  The frozen coefficient contributes the scalar
`1/N(∏B)`. -/
theorem frame_live_source_dom {α : Type*} [Fintype α] (Holes : ℕ)
    (W : ℝ→ℂ) (a b L Lslot Lcap Cap Bmask ε lo hi : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (hb : 1≤b) (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hBmask : 0≤Bmask) (hCapb : b≤Cap) (hLordinary : L≤Lcap) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z →
    ∀(η₀ : Character)(θ : α→RayQuotient.Characters M Hray)(w σ freq : α→ℝ)(t : ℝ)
      (R₀ : α→Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → (∀i,(R₀ i).card≤Holes) →
    ∀(η ω₁ ω₂ : Character)(keep : O→Prop)(Φ : 𝓢(ℝ,ℂ))(K radial : ℝ),0<K →
      Function.support (Φ:ℝ→ℂ)⊆Set.Iic radial → (∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re) →
      (∀z,keep z → z≠0) →
    ∀R F : Id,R≠0 → F≠0 → ∀H : Finset PrimeIdeal,H⊆enclosure (Cap*Z^Lcap) →
      (Ideal.absNorm (∏I∈primeSupport (R*F)∪holes H,I):ℝ)≤Z^Bmask →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),∀_hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀_hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ),0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ →
      X₁≤Z^L → X₂≤Z^L → Y₁≤Z^L → Y₂≤Z^L → X₁*X₂=Y₁*Y₂ →
    ∀d : Id×Id,∀hd : d.1≠0 ∧ d.2≠0,∀B : Tuple α,∀hB : ∀j,B j≠0,
      (∀i : liveIndices B,∀P∈H,P.val∈R₀ i.val) →
    ∃Lf : Finset (ℝ×ℝ),LengthsBelow₂ Lf X₁ X₂ Y₁ Y₂ ∧
      LeafDom (coloredNativeLeaf M Hray hHray W η₀ θ Z w σ freq t η ω₁ ω₂ keep Φ K W₁ W₂
          (2*Real.pi*t₁) (2*Real.pi*t₂)) Lf
        (C*Z^ε/((finiteTupleProduct B).absNorm:ℝ)/pairNorm d)
        (radialEnergy (fun z=>normalization (X₁*X₂) (fun i=>Z^(w i))*
          (frozenCoefficient B (finiteTupleProduct B) R
            (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
            (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))*
          TwistedRawSource.frozenLiveSum (idealCoeff ω₁) (idealCoeff ω₂) (naturalCharacter η z) (enclosure (Cap*Z^Lcap)) H
            (fun i=>supportedPool (primePool M Hray 2 (Z^(w i)))) d hd B hB F R
            (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
            (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
            (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂)) keep Φ K) := by
  obtain ⟨K₀,hK₀,hslot⟩ := slot_profile_bound W hW.continuous hWs lo hi
  let A : ℝ := (∏_i : α,K₀)^2*2^Fintype.card α
  have hA : 0<A := by
    have hKpos : 0<K₀ := zero_lt_one.trans_le hK₀
    dsimp [A]
    positivity
  obtain ⟨C,hC,hbase⟩ := frame_uniform_source_dom M Hray hHray (α:=α) Holes W a b L Lslot Lcap Cap
    Bmask ε lo hi hWs hW ha hb hLslot hLcap hCap hBmask hCapb hLordinary hε
  refine ⟨C*A,mul_pos hC hA,?_⟩
  intro Z hZ η₀ θ w σ freq t R₀ hw hwL hσ hσhi hR₀ η ω₁ ω₂ keep Φ K radial hK hs hΦ hkeep R F hR hF H hH
    hcap W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd B hB hHR
  have hZ0 : 0<Z := zero_lt_one.trans_le hZ
  let ν := slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t
  let Wslot := fun i=>slotProfile W (σ i) (freq i)
  let P := fun i=>Z^(w i)
  have hPB : finiteTupleProduct B≠0 := Finset.prod_ne_zero_iff.mpr (fun j _=>hB j)
  obtain ⟨Lf,hLf,he⟩ := hbase Z hZ η₀ θ w σ freq t R₀ hw hwL hσ hσhi hR₀ η ω₁ ω₂ keep Φ K radial hK hs
    hΦ hkeep (R*F) (mul_ne_zero hR hF) H hH hcap W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂
    hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY (d.1*B (Sum.inr 0),d.2*B (Sum.inr 1))
    (mul_ne_zero hd.1 (hB _)) (mul_ne_zero hd.2 (hB _)) (liveIndices B) hHR
  refine ⟨Lf,hLf,?_⟩
  intro E hE hl
  have hchild : radialEnergy (fun z=>normalization (X₁*X₂) (fun i : liveIndices B=>P i.val)*
      TwistedRawSource.frozenLiveSum (idealCoeff ω₁) (idealCoeff ω₂) (naturalCharacter η z) (enclosure (Cap*Z^Lcap)) H
        (fun i=>supportedPool (primePool M Hray 2 (P i))) d hd B hB F R ν Wslot P
        (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂) keep Φ K≤
        (C*Z^ε*E)/pairNorm (d.1*B (Sum.inr 0),d.2*B (Sum.inr 1)) := by
    simp_rw [TwistedRawSource.frozen_live_eq_canonical]
    apply (he E hE hl).trans_eq
    ring
  have hCE : 0≤C*Z^ε*E := by positivity
  have hh := frozen_source_energy B hB (finiteTupleProduct B) R hPB rfl d hd (X₁*X₂)
    (mul_pos hX₁ hX₂) ν Wslot P (fun _=>K₀) (fun _=>Real.rpow_pos_of_pos hZ0 _)
    (fun i I=>slot_coefficient_norm _ R₀ t i I)
    (fun i x=>hslot (σ i) (freq i) (hσ i) (hσhi i) x) (fun _=>hK₀) 1 2 (by norm_num)
    (fun i=>(slot_profile_support W (σ i) (freq i)).trans hWs) _
    keep Φ K (C*Z^ε*E) hCE hchild
  apply hh.trans_eq
  dsimp only [A]
  norm_num only [max_eq_right (show (1:ℝ)≤2 by norm_num)]
  ring

/-- **Sums over frozen labels** (reduction form of `MixedAllocationSource.uniform_frozen_sum`). -/
theorem frame_frozen_sum_dom {α : Type*} [Fintype α] (Holes : ℕ)
    (W : ℝ→ℂ) (a b L Lslot Lcap Cap Bmask ε lo hi : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (hb : 1≤b) (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hBmask : 0≤Bmask) (hCapb : b≤Cap) (hLordinary : L≤Lcap) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z →
    ∀(η₀ : Character)(θ : α→RayQuotient.Characters M Hray)(w σ freq : α→ℝ)(t : ℝ)
      (R₀ : α→Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → (∀i,(R₀ i).card≤Holes) →
    ∀(η ω₁ ω₂ : Character)(keep : O→Prop)(Φ : 𝓢(ℝ,ℂ))(K radial : ℝ),0<K →
      Function.support (Φ:ℝ→ℂ)⊆Set.Iic radial → (∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re) →
      (∀z,keep z → z≠0) →
    ∀R F : Id,R≠0 → F≠0 → ∀H : Finset PrimeIdeal,H⊆enclosure (Cap*Z^Lcap) →
      (Ideal.absNorm (∏I∈primeSupport (R*F)∪holes H,I):ℝ)≤Z^Bmask →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),∀_hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀_hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ),0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ →
      X₁≤Z^L → X₂≤Z^L → Y₁≤Z^L → Y₂≤Z^L → X₁*X₂=Y₁*Y₂ →
    ∀d : Id×Id,∀hd : d.1≠0 ∧ d.2≠0,∀labels : Finset (Tuple α),
    ∀hlabels : ∀B : labels,∀j,B.val j≠0,
    ∀active : labels→Prop,∀phase : labels→O→ℂ,
      (∀B z,keep z→‖phase B z‖≤1) →
      (∀B,¬active B→∀z,phase B z=0) →
      (∀B : labels,active B→∀i : liveIndices B.val,∀P∈H,P.val∈R₀ i.val) →
    ∃Lf : Finset (ℝ×ℝ),LengthsBelow₂ Lf X₁ X₂ Y₁ Y₂ ∧
      LeafDom (coloredNativeLeaf M Hray hHray W η₀ θ Z w σ freq t η ω₁ ω₂ keep Φ K W₁ W₂
          (2*Real.pi*t₁) (2*Real.pi*t₂)) Lf
        (C*Z^ε/pairNorm d*scalarBudget labels active)
        (radialEnergy (fun z=>∑B : labels,phase B z*
          TwistedRawSource.frozenRow (idealCoeff ω₁) (idealCoeff ω₂) (naturalCharacter η z) (enclosure (Cap*Z^Lcap)) H
            (fun i=>supportedPool (primePool M Hray 2 (Z^(w i)))) d hd B.val (hlabels B) F R
            (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
            (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
            (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂) keep Φ K) := by
  obtain ⟨C,hC,hbase⟩ := frame_live_source_dom M Hray hHray (α:=α) Holes W a b L Lslot Lcap Cap
    Bmask ε lo hi hWs hW ha hb hLslot hLcap hCap hBmask hCapb hLordinary hε
  refine ⟨C,hC,?_⟩
  intro Z hZ η₀ θ w σ freq t R₀ hw hwL hσ hσhi hR₀ η ω₁ ω₂ keep Φ K radial hK hs hΦ hkeep R F hR hF H hH
    hcap W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY
    d hd labels hlabels active phase hphase hzero hHR
  classical
  have hchild (B : labels) (hBa : active B) := hbase Z hZ η₀ θ w σ freq t R₀ hw hwL hσ hσhi hR₀
    η ω₁ ω₂ keep Φ K radial hK hs hΦ hkeep R F hR hF H hH hcap W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂
    hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd B.val (hlabels B) (hHR B hBa)
  choose! LB hLB hdomB using hchild
  refine ⟨(Finset.univ.filter active).biUnion LB,
    LengthsBelow₂.biUnion _ _ (fun B hB=>hLB B (Finset.mem_filter.mp hB).2),?_⟩
  intro E hE hl
  have hf (B : labels) (hBa : active B) := hdomB B hBa E hE (fun A p hp=>hl A p
    (Finset.mem_biUnion.mpr ⟨B,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hBa⟩,hp⟩))
  have he := radial_active_family active phase
    (fun B z=>TwistedRawSource.frozenRow (idealCoeff ω₁) (idealCoeff ω₂) (naturalCharacter η z) (enclosure (Cap*Z^Lcap)) H
      (fun i=>supportedPool (primePool M Hray 2 (Z^(w i)))) d hd B.val (hlabels B) F R
      (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
      (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
      (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂)
    (fun B=>C*Z^ε/((finiteTupleProduct B.val).absNorm:ℝ)/pairNorm d*E)
    keep Φ K radial hK hs hΦ hphase hzero hf
  apply he.trans_eq
  rw [Fintype.card_coe]
  have hsum : (∑B : labels,if active B then
      C*Z^ε/((finiteTupleProduct B.val).absNorm:ℝ)/pairNorm d*E else 0)=
      C*Z^ε/pairNorm d*E*∑B : labels,if active B then
        1/((finiteTupleProduct B.val).absNorm:ℝ) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro B _
    split_ifs <;> ring
  rw [hsum]
  unfold scalarBudget
  ring

end

end QRH.Cycle092.RegularColoredForward

#print axioms QRH.Cycle092.RegularColoredForward.frame_uniform_source_dom
#print axioms QRH.Cycle092.RegularColoredForward.frame_live_source_dom
#print axioms QRH.Cycle092.RegularColoredForward.frame_frozen_sum_dom
