/- Copyright (c) 2026 Sil. Apache-2.0.
All-height envelope for the actual restricted physical source in a
NaturalState. The exact height dictionary and effective-row equality
identify the source before applying the established estimate.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedHeightEnergy
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedHeightEnvelope

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedStateEnvelope
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelAssignmentReindex KernelNaturalSlots ReferencePrimeEnclosure MixedCompletedRows
open MixedCanonicalSource MixedOriginalSource MixedHeightEnergy MixedHeightEnvelope
open MixedLiveNormalization MixedSourceAssembly MixedLiteralAllocation
open NativeInjectiveEnergy NativeFiniteHoles
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentEnergyCapacityRemoval CenteredMomentEnergyState CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceChild
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentInductionEnergy QuadraticInitialBound CenteredMomentNaturalRowSource
open CenteredMomentFiniteProfileExceptional CenteredMomentRayMaskedFloor HeckeDyadic
open CenteredMomentSourceProfileMass CenteredMomentSourceMass CenteredMomentAddedZeroUniform
open CenteredMomentFirstSectors CenteredMomentRestrictedSource CenteredMomentHeckeColumnWindow
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]
local instance {β : Type*} : DecidableEq (β⊕Fin 2) := Classical.decEq _
variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

/-- The original restricted-column energy has a proved polynomial
height envelope on the state's original kept rows. This includes every
independent height v and has no auxiliary source-energy premise.
The even height exponent is suitable for the baseline window theorems. -/
theorem uniform_source_height_envelope
    (Holes : ℕ) (W : ℝ→ℂ) (a b radial Mcap L Lslot Lcap Cap Bmask ε δ lo hi κ : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b) (hrad : 0<radial) (hM : 0<Mcap)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap) (hBmask : 0≤Bmask)
    (hCapb : b≤Cap) (hLordinary : L≤Lcap) (hε : 0<ε) (hδ : 0<δ)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus →
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : α→RayQuotient.Characters M Hray)(w σ freq : α→ℝ)(t V : ℝ)(R₀ : α→Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤V → (∀i,|freq i|≤V) → (∀i,(R₀ i).card≤Holes) →
    ∀Bstate : ℝ,∀s : NaturalState Z Bstate radial,s.fixedModulus=Q → s.width≤Mcap →
    ∀R G seed D : Id,R≠0 → ∀hG : G≠0,seed∣G → Squarefree D →
    ∀H : Finset PrimeIdeal,H⊆enclosure (Cap*Z^Lcap) →
      (Ideal.absNorm (∏I∈primeSupport ((R*G)*D)∪holes H,I):ℝ)≤Z^Bmask →
      (∀i,∀P∈H,P.val∈R₀ i) →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),∀hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ),0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ →
      X₁≤Z^L → X₂≤Z^L → Y₁≤Z^L → Y₂≤Z^L → X₁*X₂=Y₁*Y₂ →
    ∀d : Id×Id,∀hd : d.1≠0 ∧ d.2≠0,∀v : ℝ,
      sourceRestrictedEnergy s.radial.keep
        (residualPool G hG (finiteColumns (Fintype.piFinset
          (sourcePools (fun i=>supportedPool (primePool M Hray 2 (Z^(w i)))) d hd b X₁ X₂ Y₁ Y₂))))
        (fun I=>if IsCoprime G I ∧ D∣I then
          originalColumn (enclosure (Cap*Z^Lcap)) H
            (fun i=>supportedPool (primePool M Hray 2 (Z^(w i)))) d hd R seed
            (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
            (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
            (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂ (G*I) else 0)
        (heightCoeff s.character v) s.radial.profile s.radial.scale/(X₁*X₂*∏i,Z^(w i)) ≤
      (C*(G.absNorm:ℝ)^δ*(D.absNorm:ℝ)^δ/(G.absNorm:ℝ)/pairNorm d/(D.absNorm:ℝ))*
        diagonalControl s.radial.profile*
        (sourceControl control W₁*sourceControl control W₂)^2*
        (sourceHeight t V t₁ t₂)^degree*(1+‖v‖)^(2*degree)*
        Z^(s.width+κ*(∑i,w i)+ε) := by
  obtain ⟨degree,U,hbase⟩ := uniform_shifted_original_source (α:=α) M Hray hHray Holes W
    a b radial Mcap L Lslot Lcap Cap Bmask ε δ lo hi κ
    hWs hW ha haUpper hb hrad hM hLslot hLcap hCap hBmask hCapb hLordinary hε hδ hβ hκ Q hQt hQ72 hQM
  refine ⟨degree,U,?_⟩
  intro η₀ hQη
  obtain ⟨C,hC,hbase⟩ := hbase η₀ hQη
  refine ⟨C,hC,hbase.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bstate s hQ hwidth
    R G seed D hR hG hseed hD H hH hcap hHR
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd v
  have he := hZ.2 θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bstate s hQ hwidth
    R G seed D hR hG hseed hD H hH hcap hHR W₁ W₂ hs₁ hs₂
    t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd v
  have hp (i : α) (I : Id) (hI : I∈supportedPool (primePool M Hray 2 (Z^(w i)))) : Prime I :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2.1
  have hP (i : α) : 0<Z^(w i) := Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _
  rw [canonical_source_height_energy s.character v (enclosure (Cap*Z^Lcap)) H
    (fun i=>supportedPool (primePool M Hray 2 (Z^(w i)))) hp d hd G R seed D hG
    (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t
    (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i)) hP
    W₁ W₂ t₁ t₂ b X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hXY
    s.radial.keep s.row_ne_zero s.radial.profile s.radial.scale]
  apply (le_of_eq (radialEnergy_effective s.radial _).symm).trans
  apply he.trans
  have hv : (1+|v|)^degree≤(1+‖v‖)^(2*degree) := by
    rw [Real.norm_eq_abs]
    exact pow_le_pow_right₀ (by linarith [abs_nonneg v]) (by omega)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)
  apply mul_le_mul_of_nonneg_left hv
  have := diagonalControl_nonneg s.radial.profile
  have := pairNorm_pos hd.1 hd.2
  have := sourceHeight_one_le t V t₁ t₂ hV
  positivity

end
end Candidate.FourthPower.MixedStateEnvelope
