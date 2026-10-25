/- Copyright (c) 2026 Sil. Apache-2.0.
Raw physical-source envelope. Absorption of divisor subpowers uses
explicit bounds on the full norms, separately from the radical cap.
-/
import Candidate.Feedback.FourthPower.MixedStateEnvelope

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.Feedback.FourthPower.MixedRawEnvelope
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelAssignmentReindex KernelNaturalSlots ReferencePrimeEnclosure MixedCompletedRows
open MixedCanonicalSource MixedOriginalSource MixedHeightEnergy MixedHeightEnvelope MixedStateEnvelope
open MixedLiveNormalization MixedSourceAssembly MixedLiteralAllocation
open NativeInjectiveEnergy NativeFiniteHoles
open CenteredMomentEnergyState CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceChild
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentInductionEnergy QuadraticInitialBound CenteredMomentNaturalRowSource
open CenteredMomentFiniteProfileExceptional CenteredMomentRayMaskedFloor HeckeDyadic
open CenteredMomentSourceProfileMass CenteredMomentSourceMass CenteredMomentAddedZeroUniform
open CenteredMomentFirstSectors CenteredMomentRestrictedSource CenteredMomentHeckeColumnWindow
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

def divisorSlack (B ε : ℝ) : ℝ := ε/(4*(B+1))

theorem divisorSlack_pos (B ε : ℝ) (hB : 0≤B) (hε : 0<ε) :
    0<divisorSlack B ε := by
  unfold divisorSlack
  exact div_pos hε (by positivity)

/-- Two full divisor norm caps absorb their subpowers. The B+1 in the
slack makes the proof valid at B=0 without a separate limiting argument. -/
theorem capped_divisor_subpowers (Z B ε : ℝ) (hZ : 1≤Z) (hB : 0≤B) (hε : 0<ε)
    (G D : Id) (hG : (G.absNorm:ℝ)≤Z^B) (hD : (D.absNorm:ℝ)≤Z^B) :
    (G.absNorm:ℝ)^(divisorSlack B ε)*(D.absNorm:ℝ)^(divisorSlack B ε)≤Z^(ε/2) := by
  have hZ0 : 0<Z := zero_lt_one.trans_le hZ
  have hδ := divisorSlack_pos B ε hB hε
  have hb : B*divisorSlack B ε+B*divisorSlack B ε≤ε/2 := by
    have he : divisorSlack B ε*(4*(B+1))=ε := by
      unfold divisorSlack
      exact div_mul_cancel₀ ε (by positivity)
    nlinarith
  calc
    _ ≤ (Z^B)^(divisorSlack B ε)*(Z^B)^(divisorSlack B ε) :=
      mul_le_mul (Real.rpow_le_rpow (Nat.cast_nonneg _) hG hδ.le)
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hD hδ.le)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg (Real.rpow_nonneg hZ0.le _) _)
    _ = Z^(B*divisorSlack B ε+B*divisorSlack B ε) := by
      simp only [←Real.rpow_mul hZ0.le,←Real.rpow_add hZ0]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ hb

/-- Raw budget before the squarefree divisor denominator. A is the
proved profile and base-height factor, not an analytic hypothesis. -/
def rawBudget (volume A Z exponent : ℝ) (G : Id) (d : Id×Id) : ℝ :=
  volume*A*Z^exponent/(G.absNorm:ℝ)/pairNorm d

variable {α : Type*} [Fintype α]
local instance {β : Type*} : DecidableEq (β⊕Fin 2) := Classical.decEq _
variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

/-- The actual raw restricted source has budget E_G/N(D) at every
height, with full norm caps supplied explicitly. No child-source bound
or physical-source estimate occurs among the hypotheses. -/
theorem uniform_raw_source_envelope
    (Holes : ℕ) (W : ℝ→ℂ) (a b radial Mcap L Lslot Lcap Cap Bmask Bnorm ε lo hi κ : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b) (hrad : 0<radial) (hM : 0<Mcap)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap) (hBmask : 0≤Bmask)
    (hBnorm : 0≤Bnorm) (hCapb : b≤Cap) (hLordinary : L≤Lcap) (hε : 0<ε)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus →
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : α→RayQuotient.Characters M Hray)(w σ freq : α→ℝ)(t V : ℝ)(R₀ : α→Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤V → (∀i,|freq i|≤V) → (∀i,(R₀ i).card≤Holes) →
    ∀Bstate : ℝ,∀s : NaturalState Z Bstate radial,s.fixedModulus=Q → s.width≤Mcap →
    ∀R G seed D : Id,R≠0 → ∀hG : G≠0,seed∣G → Squarefree D →
      (G.absNorm:ℝ)≤Z^Bnorm → (D.absNorm:ℝ)≤Z^Bnorm →
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
        (heightCoeff s.character v) s.radial.profile s.radial.scale ≤
      (rawBudget (X₁*X₂*∏i,Z^(w i))
        (C*diagonalControl s.radial.profile*(sourceControl control W₁*sourceControl control W₂)^2*
          (sourceHeight t V t₁ t₂)^degree)
        Z (s.width+κ*(∑i,w i)+ε) G d/(D.absNorm:ℝ))*(1+‖v‖)^(2*degree) := by
  obtain ⟨degree,U,hbase⟩ := uniform_source_height_envelope (α:=α) M Hray hHray Holes W
    a b radial Mcap L Lslot Lcap Cap Bmask (ε/2) (divisorSlack Bnorm ε) lo hi κ
    hWs hW ha haUpper hb hrad hM hLslot hLcap hCap hBmask hCapb hLordinary
    (half_pos hε) (divisorSlack_pos Bnorm ε hBnorm hε) hβ hκ Q hQt hQ72 hQM
  refine ⟨degree,U,?_⟩
  intro η₀ hQη
  obtain ⟨C,hC,hbase⟩ := hbase η₀ hQη
  refine ⟨C,hC,hbase.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bstate s hQ hwidth
    R G seed D hR hG hseed hD hNG hND H hH hcap hHR
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd v
  have he := hZ.2 θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bstate s hQ hwidth
    R G seed D hR hG hseed hD H hH hcap hHR W₁ W₂ hs₁ hs₂
    t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd v
  have hZ0 : 0<Z := zero_lt_one.trans hZ.1
  have hvolume : 0<X₁*X₂*∏i,Z^(w i) :=
    mul_pos (mul_pos hX₁ hX₂) (Finset.prod_pos (fun i _=>Real.rpow_pos_of_pos hZ0 _))
  have hraw := (div_le_iff₀ hvolume).mp he
  have hsub := capped_divisor_subpowers Z Bnorm ε hZ.1.le hBnorm hε G D hNG hND
  have hscale : (G.absNorm:ℝ)^(divisorSlack Bnorm ε)*(D.absNorm:ℝ)^(divisorSlack Bnorm ε)*
      Z^(s.width+κ*(∑i,w i)+ε/2)≤Z^(s.width+κ*(∑i,w i)+ε) := by
    apply (mul_le_mul_of_nonneg_right hsub (Real.rpow_nonneg hZ0.le _)).trans_eq
    rw [←Real.rpow_add hZ0]
    congr 1
    ring
  let F := ((X₁*X₂*∏i,Z^(w i))*C*diagonalControl s.radial.profile*
    (sourceControl U W₁*sourceControl U W₂)^2*(sourceHeight t V t₁ t₂)^degree)/
    (G.absNorm:ℝ)/pairNorm d/(D.absNorm:ℝ)*(1+‖v‖)^(2*degree)
  have hF : 0≤F := by
    have := diagonalControl_nonneg s.radial.profile
    have := pairNorm_pos hd.1 hd.2
    have := sourceHeight_one_le t V t₁ t₂ hV
    dsimp only [F]
    positivity
  apply hraw.trans
  calc
    _ = F*((G.absNorm:ℝ)^(divisorSlack Bnorm ε)*(D.absNorm:ℝ)^(divisorSlack Bnorm ε)*
        Z^(s.width+κ*(∑i,w i)+ε/2)) := by dsimp only [F];ring
    _ ≤ F*Z^(s.width+κ*(∑i,w i)+ε) := mul_le_mul_of_nonneg_left hscale hF
    _ = _ := by dsimp only [F,rawBudget];ring

end
end Candidate.Feedback.FourthPower.MixedRawEnvelope
