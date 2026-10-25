/- Copyright (c) 2026 Sil. Apache-2.0.
the literal mixed source in the baseline canonical child state.
The analytic estimate is MixedRawEnvelope; the remaining width condition
is explicitly geometric. No new state constructor or energy premise.
-/
import Candidate.SilPrior.FourthPower.MixedRawEnvelope
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ChildState

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.MixedCanonicalEnvelope
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CompletedGauss RayFourExpansion
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelAssignmentReindex KernelNaturalSlots ReferencePrimeEnclosure MixedCompletedRows
open MixedCanonicalSource MixedOriginalSource MixedHeightEnergy MixedHeightEnvelope
open MixedRawEnvelope MixedLiveNormalization MixedSourceAssembly MixedLiteralAllocation
open NativeInjectiveEnergy NativeFiniteHoles
open CenteredMomentEnergyState CenteredMomentEnergyChildState
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentInductionEnergy QuadraticInitialBound CenteredMomentNaturalRowSource
open CenteredMomentFiniteProfileExceptional CenteredMomentRayMaskedFloor HeckeDyadic
open CenteredMomentSourceProfileMass CenteredMomentSourceMass CenteredMomentAddedZeroUniform
open CenteredMomentFirstSectors CenteredMomentRestrictedSource CenteredMomentHeckeColumnWindow
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondHeightFamily
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondExceptionalFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentSectorLocalization CenteredMomentCanonicalFirst
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-- Exact conductor-times-row-scale cost, without a numerical relaxation. -/
theorem canonical_budget (Z Bstate : ℝ) (hZ : 1<Z) (τ : Character) (Q R : Id)
    (hR : R≠0) (hRN : (R.absNorm:ℝ)≤Z^Bstate) (n : Fin 4→ℤ)
    (hn : 1≤dyadicScale (n 1)) (volume A exponent : ℝ) (G : Id) (d : Id×Id) :
    rawBudget volume A Z
      ((canonicalState Z Bstate hZ τ Q R hR hRN n hn).width+exponent) G d =
    rawBudget volume (A*(τ.modulus.absNorm:ℝ)*dyadicScale (n 1)) Z exponent G d := by
  unfold rawBudget
  rw [Real.rpow_add (zero_lt_one.trans hZ),canonicalState_power]
  ring

variable {α : Type*} [Fintype α]
local instance {β : Type*} : DecidableEq (β⊕Fin 2) := Classical.decEq _
variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

/-- Uniform canonical-row envelope for the actual tuple-weighted source.
All original norm, radical, hole, seed and rectangle hypotheses are retained.
The log-width cap is geometry, not a source-energy assumption. -/
theorem uniform_canonical_source_envelope
    (Holes : ℕ) (W : ℝ→ℂ) (a b Mcap L Lslot Lcap Cap Bmask Bnorm ε lo hi κ : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b) (hM : 0<Mcap)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap) (hBmask : 0≤Bmask)
    (hBnorm : 0≤Bnorm) (hCapb : b≤Cap) (hLordinary : L≤Lcap) (hε : 0<ε)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus →
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : α→RayQuotient.Characters M Hray)(w σ freq : α→ℝ)(t V : ℝ)(R₀ : α→Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤V → (∀i,|freq i|≤V) → (∀i,(R₀ i).card≤Holes) →
    ∀(Bstate : ℝ)(τ : Character)(n : Fin 4→ℤ),1≤dyadicScale (n 1) →
      Real.logb Z (dyadicScale (n 1))+Real.logb Z (τ.modulus.absNorm:ℝ)≤Mcap →
    ∀R G seed D : Id,∀hR : R≠0,(R.absNorm:ℝ)≤Z^Bstate →
    ∀hG : G≠0,seed∣G → Squarefree D →
      (G.absNorm:ℝ)≤Z^Bnorm → (D.absNorm:ℝ)≤Z^Bnorm →
    ∀H : Finset PrimeIdeal,H⊆enclosure (Cap*Z^Lcap) →
      (Ideal.absNorm (∏I∈QRH.Record1252270103KernelMass.primeSupport ((R*G)*D)∪holes H,I):ℝ)≤Z^Bmask →
      (∀i,∀P∈H,P.val∈R₀ i) →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),∀hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ),0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ →
      X₁≤Z^L → X₂≤Z^L → Y₁≤Z^L → Y₂≤Z^L → X₁*X₂=Y₁*Y₂ →
    ∀d : Id×Id,∀hd : d.1≠0 ∧ d.2≠0,∀v : ℝ,
      sourceRestrictedEnergy (canonicalRadial τ Q n).keep
        (residualPool G hG (finiteColumns (Fintype.piFinset
          (sourcePools (fun i=>supportedPool (primePool M Hray 2 (Z^(w i)))) d hd b X₁ X₂ Y₁ Y₂))))
        (fun I=>if IsCoprime G I ∧ D∣I then
          originalColumn (enclosure (Cap*Z^Lcap)) H
            (fun i=>supportedPool (primePool M Hray 2 (Z^(w i)))) d hd R seed
            (slotCoefficient
              (fun i=>CenteredMomentNaturalFixedRaySource.relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
            (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
            (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂ (G*I) else 0)
        (heightCoeff τ v) ballProfile (dyadicScale (n 1)) ≤
      (rawBudget (X₁*X₂*∏i,Z^(w i))
        ((C*diagonalControl ballProfile*(sourceControl control W₁*sourceControl control W₂)^2*
          (sourceHeight t V t₁ t₂)^degree)*(τ.modulus.absNorm:ℝ)*dyadicScale (n 1))
        Z (κ*(∑i,w i)+ε) G d/(D.absNorm:ℝ))*(1+‖v‖)^(2*degree) := by
  obtain ⟨degree,U,hbase⟩ := uniform_raw_source_envelope (α:=α) M Hray hHray Holes W
    a b 2 Mcap L Lslot Lcap Cap Bmask Bnorm ε lo hi κ
    hWs hW ha haUpper hb (by norm_num) hM hLslot hLcap hCap hBmask hBnorm
    hCapb hLordinary hε hβ hκ Q hQt hQ72 hQM
  refine ⟨degree,U,?_⟩
  intro η₀ hQη
  obtain ⟨C,hC,hbase⟩ := hbase η₀ hQη
  refine ⟨C,hC,hbase.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ Bstate τ n hn hwidth
    R G seed D hR hRN hG hseed hD hNG hND H hH hcap hHR
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd v
  let s := canonicalState Z Bstate hZ.1 τ Q R hR hRN n hn
  have hswidth : s.width≤Mcap := hwidth
  have he := hZ.2 θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀
    Bstate s rfl hswidth R G seed D hR hG hseed hD hNG hND H hH hcap hHR
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd v
  rw [add_assoc s.width (κ*(∑i,w i)) ε] at he
  dsimp only [s] at he
  rw [canonical_budget] at he
  exact he

section Actual
variable {η : Character} {C D : Id} {hC : Supported C} {hD : Supported D}
  {U : Finset (CommonIndex C D)} {τ : RayCharacter→Character}

/-- The two purely geometric inputs above come from the actual nonzero
physical block. The displayed ledger cap is the remaining numerical
geometry obligation; this theorem has no analytic source premise. -/
theorem actual_canonical_geometry
    (h : Family η C D hC hD U τ)
    (t : ℝ) (S : Finset Id) (β : Id→ℂ) (radius : ℝ) (rows : Finset O)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) (n : Fin 4→ℤ)
    (hne : physicalBlock η t S β C D hC hD U radius rows W K n≠0)
    (Z Bstate Mcap : ℝ) (hZ : 1<Z) (χ : RayCharacter) (Q R : Id)
    (hR : R≠0) (hRN : (R.absNorm:ℝ)≤Z^Bstate)
    (hledger : Real.logb Z radius+Real.logb Z (η.modulus.absNorm:ℝ)-
      Real.logb Z (normValue (commonFrequencyGenerator C D))+
      Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+
      Real.logb Z (16*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ))≤Mcap) :
    1≤dyadicScale (n 1) ∧
      Real.logb Z (dyadicScale (n 1))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤Mcap := by
  refine ⟨actual_dyad_ge_one t S β radius rows W K n hne,?_⟩
  have hh := actualState_width h t S β radius rows W K hK n hne
    Z Bstate hZ χ Q R hR hRN
  exact hh.trans hledger

end Actual
end
end Candidate.SilPrior.FourthPower.MixedCanonicalEnvelope
