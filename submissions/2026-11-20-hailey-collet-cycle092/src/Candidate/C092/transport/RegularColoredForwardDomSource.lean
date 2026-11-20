/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
The actual independently colored canonical source through its signed
original/reference rectangles to two-character native physical leaves.
Adapted from Sil MixedDom. The complete puncture, original inherited masks,
paired-divisor normalization and original mark coefficients are retained.
The source is the shared TwistedRawSource.canonicalSource.
-/
import Candidate.C092.transport.RegularColoredForwardDomForward
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
local instance c092LocalInst_Candidate_C092_transport_RegularColoredForwardDomSource_e2588b0a769e0770_001 : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

/-- Equality of every literal ideal coefficient transports the genuine
colored forward family, retaining both ordinary colors. -/
theorem coloredForwardRow_character_congr {α : Type*} [Fintype α]
    (χ ψ ω₁ ω₂ : Character) (h : ∀ I, idealCoeff χ I = idealCoeff ψ I)
    (S : Finset PrimeIdeal) (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ : ℝ) :
    coloredForwardRow S χ ω₁ ω₂ pool β P W₁ W₂ b X₁ X₂ =
      coloredForwardRow S ψ ω₁ ω₂ pool β P W₁ W₂ b X₁ X₂ := by
  unfold coloredForwardRow weightedSum naturalCoefficients slotTerm row normalizedRow pairCharacter
  simp_rw [h]

/-! ### Centered punctured rows -/

/-- **Centered punctured rows** (reduction form of `MixedCenteredEnergy.canonical_centered`). -/
theorem colored_centered_dom {α : Type*} [Fintype α] (Holes : ℕ)
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
    ∀R : Finset Id,∀hR : ∀I∈R,Prime I,∀H : Finset PrimeIdeal,
      H⊆enclosure (Cap*Z^Lcap) → (∀i,∀P∈H,P.val∈R₀ i) →
      (Ideal.absNorm (∏I∈R∪holes H,I):ℝ)≤Z^Bmask →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),∀hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ),0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ →
      X₁≤Z^L → X₂≤Z^L → Y₁≤Z^L → Y₂≤Z^L →
    ∀d : Id×Id,d.1≠0 → d.2≠0 →
    ∃Lf : Finset (ℝ×ℝ),LengthsBelow₂ Lf X₁ X₂ Y₁ Y₂ ∧
      LeafDom (coloredNativeLeaf M Hray hHray W η₀ θ Z w σ freq t η ω₁ ω₂ keep Φ K W₁ W₂
          (2*Real.pi*t₁) (2*Real.pi*t₂)) Lf (C*Z^ε/pairNorm d)
        (radialEnergy (fun z=>coloredCenteredRow ((naturalCharacter η z).excludePrimes R hR) (idealCoeff ω₁) (idealCoeff ω₂)
          (enclosure (Cap*Z^Lcap)) H
          (fun i=>supportedPool (primePool M Hray 2 (Z^(w i))))
          (fun i=>heightCoefficient
            (holeCoefficient (slotBeta M Hray hHray W η₀ θ Z w σ freq) R₀ i) t)
          (fun i=>Z^(w i)) (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂ d) keep Φ K) := by
  obtain ⟨Cf,hCf,hfwd⟩ := colored_forward_dom M Hray hHray (α:=α) Holes W a b L Lslot Lcap Cap Bmask ε
    lo hi hWs hW ha hb hLslot hLcap hCap hBmask hCapb hLordinary hε
  refine ⟨4*Cf,by positivity,?_⟩
  intro Z hZ η₀ θ w σ freq t R₀ hw hwL hσ hσhi hR₀ η ω₁ ω₂ keep Φ K radial hK hs hΦ hkeep R hR H hH hHR
    hcap W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ d hd1 hd2
  let primes := enclosure (Cap*Z^Lcap)
  let pool := fun i=>supportedPool (primePool M Hray 2 (Z^(w i)))
  let β₀ := slotBeta M Hray hHray W η₀ θ Z w σ freq
  let βc := fun i=>heightCoefficient (holeCoefficient β₀ R₀ i) t
  let T := R∪holes H
  have hT : ∀I∈T,Prime I := fun I hI=>(Finset.mem_union.mp hI).elim (hR I) (holes_prime H I)
  have hβH (i : α) (P : PrimeIdeal) (hP : P∈H) : βc i P.val=0 := by
    simp only [βc,heightCoefficient,holeCoefficient,ite_eq_left (hHR i P hP),zero_mul]
  have hid (A B : ℝ) (z : O) :
      coloredPuncturedRow ((naturalCharacter η z).excludePrimes R hR) (idealCoeff ω₁) (idealCoeff ω₂) primes H pool βc
        (fun i=>Z^(w i)) (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b A B=
      coloredForwardRow primes ((naturalCharacter η z).excludePrimes T hT) ω₁ ω₂ pool βc
        (fun i=>Z^(w i)) (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b A B := by
    rw [coloredPuncturedRow,colored_family_hole_absorption _ (idealCoeff ω₁) (idealCoeff ω₂) primes H hH pool βc _ hβH]
    exact coloredForwardRow_character_congr _ _ ω₁ ω₂ (character_union _ R (holes H) hR (holes_prime H)) _ _ _ _ _ _ _ _ _
  have hlen (x : ℝ) (hx : 0<x) (hc : x≤Z^L) (e : Id) (he : e≠0) : x/(e.absNorm:ℝ)≤Z^L :=
    (shortened_positive_le hx he).2.trans hc
  have hXd := hfwd Z hZ η₀ θ w σ freq t R₀ hw hwL hσ hσhi hR₀ η ω₁ ω₂ keep Φ K radial hK hs hΦ hkeep
    T hT hcap W₁ W₂ hs₁ hs₂ t₁ t₂ (X₁/(d.1.absNorm:ℝ)) (X₂/(d.2.absNorm:ℝ))
    (shortened_positive_le hX₁ hd1).1 (shortened_positive_le hX₂ hd2).1
    (hlen X₁ hX₁ hc₁ _ hd1) (hlen X₂ hX₂ hc₂ _ hd2)
  have hYd := hfwd Z hZ η₀ θ w σ freq t R₀ hw hwL hσ hσhi hR₀ η ω₁ ω₂ keep Φ K radial hK hs hΦ hkeep
    T hT hcap W₁ W₂ hs₁ hs₂ t₁ t₂ (Y₁/(d.1.absNorm:ℝ)) (Y₂/(d.2.absNorm:ℝ))
    (shortened_positive_le hY₁ hd1).1 (shortened_positive_le hY₂ hd2).1
    (hlen Y₁ hY₁ hc₃ _ hd1) (hlen Y₂ hY₂ hc₄ _ hd2)
  let LX := forwardLengths primes b (X₁/(d.1.absNorm:ℝ)) (X₂/(d.2.absNorm:ℝ)) T
  let LY := forwardLengths primes b (Y₁/(d.1.absNorm:ℝ)) (Y₂/(d.2.absNorm:ℝ)) T
  refine ⟨LX∪LY,?_,?_⟩
  · apply LengthsBelow₂.union
    · exact LengthsBelow₂.left Y₁ Y₂ ((forwardLengths_below hT (shortened_positive_le hX₁ hd1).1
        (shortened_positive_le hX₂ hd2).1).mono (shortened_positive_le hX₁ hd1).2
        (shortened_positive_le hX₂ hd2).2)
    · exact LengthsBelow₂.right X₁ X₂ ((forwardLengths_below hT (shortened_positive_le hY₁ hd1).1
        (shortened_positive_le hY₂ hd2).1).mono (shortened_positive_le hY₁ hd1).2
        (shortened_positive_le hY₂ hd2).2)
  · intro E hE hl
    have hfX : radialEnergy (fun z=>coloredPuncturedRow ((naturalCharacter η z).excludePrimes R hR) (idealCoeff ω₁) (idealCoeff ω₂)
        primes H pool βc (fun i=>Z^(w i)) (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b
        (X₁/(d.1.absNorm:ℝ)) (X₂/(d.2.absNorm:ℝ))) keep Φ K≤Cf*Z^ε*E := by
      simp_rw [hid]
      exact hXd E hE (fun A p hp=>hl A p (Finset.mem_union_left _ hp))
    have hfY : radialEnergy (fun z=>coloredPuncturedRow ((naturalCharacter η z).excludePrimes R hR) (idealCoeff ω₁) (idealCoeff ω₂)
        primes H pool βc (fun i=>Z^(w i)) (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b
        (Y₁/(d.1.absNorm:ℝ)) (Y₂/(d.2.absNorm:ℝ))) keep Φ K≤Cf*Z^ε*E := by
      simp_rw [hid]
      exact hYd E hE (fun A p hp=>hl A p (Finset.mem_union_right _ hp))
    have he := radial_extracted_centered _ _ d ⟨hd1,hd2⟩ keep Φ K radial (Cf*Z^ε*E) hK hs hΦ
      hfX hfY
    apply he.trans_eq
    ring

/-! ### The canonical source -/

/-- **The original finite source** (reduction form of `MixedCanonicalSource.canonical_source`). -/
theorem colored_source_dom {α : Type*} [Fintype α] (Holes : ℕ)
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
    ∀R : Id,R≠0 → ∀H : Finset PrimeIdeal,
      H⊆enclosure (Cap*Z^Lcap) → (∀i,∀P∈H,P.val∈R₀ i) →
      (Ideal.absNorm (∏I∈primeSupport R∪holes H,I):ℝ)≤Z^Bmask →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),∀_hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀_hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ),0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ →
      X₁≤Z^L → X₂≤Z^L → Y₁≤Z^L → Y₂≤Z^L → X₁*X₂=Y₁*Y₂ →
    ∀d : Id×Id,d.1≠0 → d.2≠0 →
    ∃Lf : Finset (ℝ×ℝ),LengthsBelow₂ Lf X₁ X₂ Y₁ Y₂ ∧
      LeafDom (coloredNativeLeaf M Hray hHray W η₀ θ Z w σ freq t η ω₁ ω₂ keep Φ K W₁ W₂
          (2*Real.pi*t₁) (2*Real.pi*t₂)) Lf (C*Z^ε/pairNorm d)
        (radialEnergy (fun z=>normalization (X₁*X₂) (fun i=>Z^(w i))*
          coloredCanonicalSource (naturalCharacter η z) (idealCoeff ω₁) (idealCoeff ω₂) (enclosure (Cap*Z^Lcap)) H R
            (fun i=>supportedPool (primePool M Hray 2 (Z^(w i))))
            (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
            (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
            (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂ d) keep Φ K) := by
  obtain ⟨C,hC,hbase⟩ := colored_centered_dom M Hray hHray (α:=α) Holes W a b L Lslot Lcap Cap Bmask ε
    lo hi hWs hW ha hb hLslot hLcap hCap hBmask hCapb hLordinary hε
  refine ⟨C,hC,?_⟩
  intro Z hZ η₀ θ w σ freq t R₀ hw hwL hσ hσhi hR₀ η ω₁ ω₂ keep Φ K radial hK hs hΦ hkeep R hR H hH hHR
    hcap W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd₁ hd₂
  obtain ⟨Lf,hLf,he⟩ := hbase Z hZ η₀ θ w σ freq t R₀ hw hwL hσ hσhi hR₀ η ω₁ ω₂ keep Φ K radial hK hs
    hΦ hkeep (primeSupport R) (fun _ h=>support_prime h) H hH hHR hcap W₁ W₂ hs₁ hs₂
    t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ d hd₁ hd₂
  refine ⟨Lf,hLf,he.of_eq ?_⟩
  have hp (i : α) :
      supportedPool (primePool M Hray 2 (Z^(w i)))⊆primeValues (enclosure (Cap*Z^Lcap)) := by
    rw [enclosure_values]
    exact canonical_pool_enclosed M Hray Z (w i) Lcap Cap hZ ((hwL i).trans hLcap) hCap
  have hbound (x : ℝ) (hx : 0<x) (hc : x≤Z^L) (D : Id) (hD : D≠0) :
      b*(x/D.absNorm)≤Cap*Z^Lcap :=
    mul_le_mul hCapb (((shortened_positive_le hx hD).2.trans hc).trans
      (Real.rpow_le_rpow_of_exponent_le hZ hLordinary))
      (shortened_positive_le hx hD).1.le (by linarith)
  have hcover (I : Id) (hI : Supported I)
      (hh : (((I.absNorm:ℝ)≤b*(X₁/d.1.absNorm) ∨ (I.absNorm:ℝ)≤b*(X₂/d.2.absNorm)) ∨
       ((I.absNorm:ℝ)≤b*(Y₁/d.1.absNorm) ∨ (I.absNorm:ℝ)≤b*(Y₂/d.2.absNorm)))) :
      primeSupport I⊆primeValues (enclosure (Cap*Z^Lcap)) := by
    apply support_enclosed _ I hI
    rcases hh with (hh|hh)|(hh|hh)
    · exact hh.trans (hbound X₁ hX₁ hc₁ _ hd₁)
    · exact hh.trans (hbound X₂ hX₂ hc₂ _ hd₂)
    · exact hh.trans (hbound Y₁ hY₁ hc₃ _ hd₁)
    · exact hh.trans (hbound Y₂ hY₂ hc₄ _ hd₂)
  have hid (z : O) (hz : keep z) :=
    colored_source_centered (naturalCharacter η z) (idealCoeff ω₁) (idealCoeff ω₂) (enclosure (Cap*Z^Lcap)) H R hR _ hp
      (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
      (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
      (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂ d
      hX₁ hX₂ hY₁ hY₂ hXY ⟨hd₁,hd₂⟩
      ((phaseProfile_support W₁ t₁).trans (fun x hx=>(hs₁ hx).2))
      ((phaseProfile_support W₂ t₂).trans (fun x hx=>(hs₂ hx).2))
      (natural_character_off_supported η z (hkeep z hz)) hcover
  unfold radialEnergy
  apply tsum_congr
  intro z
  by_cases hz : keep z
  · simp only [hz,ite_true,hid z hz,
      slot_coefficient_identity (fun i=>relativeCharacter M Hray hHray η₀ (θ i))
        R₀ W (fun i=>Z^(w i)) σ freq t]
    rfl
  · simp only [hz,ite_false]


end
end QRH.Cycle092.RegularColoredForward

#print axioms QRH.Cycle092.RegularColoredForward.colored_centered_dom
#print axioms QRH.Cycle092.RegularColoredForward.colored_source_dom
