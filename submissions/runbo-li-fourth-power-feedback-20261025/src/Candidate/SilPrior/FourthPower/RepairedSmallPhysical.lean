/- Copyright (c) 2026 Sil. Apache-2.0.
Actual second physical block on ORIGINAL avoided coefficients. Both
ordinary envelopes are proved internally; only explicit arithmetic geometry
is supplied.
-/
import Candidate.SilPrior.FourthPower.RepairedSmallAvoidedNative
import Candidate.SilPrior.FourthPower.MixedPhysicalEnvelopes
import Candidate.SilPrior.FourthPower.MixedActualFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.RepairedSmallPhysical
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentFirstSectors
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentAllocatedNaturalRadial
open CenteredMomentOriginalRadialComparison CenteredMomentSecondNonexceptionalChosenBlock
open CenteredMomentSecondHeightFamily CenteredMomentUncenteredTerminal HeckeDyadic
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedFirstLiveSource
open MixedNativeFloor MixedInnerExceptionalBlock MixedFirstActualNonexceptional
open MixedFirstProfileEnvelope MixedCanonicalSource MixedFirstAvoidance OuterFreshSelectedWindow
open RepairedSmallRowAllocation RepairedSmallRawBudget RepairedSmallNativeRaw RepairedSmallNativeFamily
open QuadraticInitialBound
open CenteredMomentCanonicalFirst
open CenteredMomentSecondExceptionalFamily
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq (α ⊕ Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι]
variable (M : Id) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O ⧸ M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)


open RayFourExpansion
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentSourceRow
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondEnergySplit CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondWindowBudget CenteredMomentSecondHeightFamily
open MixedActualFamily MixedPhysicalEnvelopes MixedRawEnvelope
open RepairedSmallAvoidedNative

theorem uniform_avoided_physical
    (Holes decay : ℕ) (Wslot : ℝ → ℂ) (Ψ : 𝓢(ℝ,ℂ))
    (a b L Lslot Lcap Cap BR BH Bnorm Brow Bchar rho ε δCount δPhys lo hi : ℝ)
    (hWs : Function.support Wslot⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ Wslot)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hCapb : b≤Cap) (hLordinary : L≤Lcap)
    (hBR : 0≤BR) (hBH : 0≤BH) (hBnorm : 0≤Bnorm)
    (hBrow : 0≤Brow) (hBchar : 0≤Bchar) (hε : 0<ε) (hδCount : 0<δCount) (hδPhys : 0<δPhys)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M)
 :
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus →
    ∃Cs Cp : ℝ,0<Cs ∧ 0<Cp ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : ι → RayQuotient.Characters M Hray)(w σ freq : ι → ℝ)(t₀ V : ℝ)
      (R₀ : ι → Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤V → (∀i,|freq i|≤V) → (∀i,(R₀ i).card≤Holes) → (∑i,w i)≤rho →
    ∀s : Source ι a b,Canonical M Hray hHray Wslot Cap Lcap Z η₀ θ w σ freq t₀ R₀ s →
      (∀i,1≤s.M i) → (s.R.absNorm:ℝ)≤Z^BR →
      s.H⊆ReferencePrimeEnclosure.enclosure (Cap*Z^Lcap) →
      ((∏I∈MixedCompletedRows.holes s.H,I).absNorm:ℝ)≤Z^BH →
      (∀i,∀P∈s.H,P.val∈R₀ i) →
      s.X₁≤Z^L → s.X₂≤Z^L → s.Y₁≤Z^L → s.Y₂≤Z^L →
    ∀cover : OriginalEnclosure s,∀u seed : Id,u∣s.R*seed →
    ∀(η : Character)(τ : RayCharacter → Character)(C D : Id)(hC : Supported C)(hD : Supported D),
      primeSupport C=primeSupport D → seed∣C → seed∣D →
      (C.absNorm:ℝ)≤Z^Bnorm → (D.absNorm:ℝ)≤Z^Bnorm →
    ∀U : Finset (CommonIndex C D),Family η C D hC hD U τ →
    ∀(n : Fin 4 → ℤ)(tp radius Kphys Hsource cost : ℝ),
      0<Kphys → 0≤cost → 1≤dyadicScale (n 1) → dyadicScale (n 1)≤Z^Brow →
      (∀χ,((τ χ).modulus.absNorm:ℝ)≤Z^Bchar) →
      (∀χ,((τ χ).modulus.absNorm:ℝ)*dyadicScale (n 1)≤cost) →
      (∀I,sourceCoefficient (avoidSource s u) ha seed I≠0 → (I.absNorm:ℝ)≤Hsource) →
      Hsource/(D.absNorm:ℝ)≤Z^Bnorm →
    ∀(m : O)(χ₀ : RayCharacter),m≠0 → ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
    let A:=Cs*slotCost s*diagonalControl ballProfile*
      (sourceControl control s.W₁*sourceControl control s.W₂)^2*
      (height t₀ V s.t₁ s.t₂)^degree;
    let base:=(3/4:ℝ)*rho+ε+Bnorm*δCount;
    let Eleft:=rawBudget (sourceVolume s) (A*cost) Z base C s.d;
    let Eright:=rawBudget (sourceVolume s) (A*cost) Z base D s.d;
    ‖physicalBlock η tp (sourceColumns s) (sourceCoefficient (avoidSource s u) ha seed)
      C D hC hD U radius (partRows false η χ₀ Q m C D U radius) Ψ Kphys n‖≤
      Cp*Z^δPhys*(outerScalar C D Kphys n*normalizer C D U)*
        (windowBudget degree tp Eleft*windowBudget degree tp Eright)/
        (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))^decay := by
  obtain ⟨degree,control,hsource⟩ := uniform_avoided_native (ι:=ι) M Hray hHray
    Holes Wslot a b L Lslot Lcap Cap BR BH Bnorm Brow Bchar rho ε δCount lo hi
    hWs hW ha haUpper hb hLslot hLcap hCap hCapb hLordinary hBR hBH hBnorm
    hBrow hBchar hε hδCount hβ Q hQt hQ72 hQM
  obtain ⟨Cp,hCp,hphysical⟩ := actual_canonical_source_envelopes
    Ψ decay degree degree Bnorm δPhys hBnorm hδPhys
  refine ⟨degree,control,?_⟩
  intro η₀ hQη₀
  obtain ⟨Cs,hCs,hsource⟩ := hsource η₀ hQη₀
  refine ⟨Cs,Cp,hCs,hCp,?_⟩
  filter_upwards [hsource,hphysical] with Z hZ hpZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq t₀ V R₀ hw hwL hσ hσhi hV hfreq hholes hsmall
    s hcan hM hR hH hHnorm hHR hX₁ hX₂ hY₁ hY₂ cover u seed hu
    η τ C D hC hD hCD hseedC hseedD hCcap hDcap U hfamily
    n tp radius Kphys Hsource cost hKphys hcost0 hn hncap hτcap hcost hcolumns hdivision
    m χ₀ hm hml hm2 A base Eleft Eright
  have hz : 0<Z := zero_lt_one.trans hZ.1
  have hA : 0≤A := by
    have hs := slot_cost_nonneg s
    have hd := diagonalControl_nonneg ballProfile
    have hh : 0≤height t₀ V s.t₁ s.t₂ := by unfold height;positivity
    dsimp only [A]
    positivity
  have hraw (G : Id) (hG : Supported G) (hseedG : seed∣G) (hGcap : (G.absNorm:ℝ)≤Z^Bnorm)
      (L2 : Id) (hL2 : Squarefree L2) (hL2cap : (L2.absNorm:ℝ)≤Z^Bnorm)
      (χ : RayCharacter) (v : ℝ) :
      sourceRestrictedEnergy (canonicalRadial (τ χ) Q n).keep
        (residualPool G hG.1 (sourceColumns s))
        (fun I => if IsCoprime G I ∧ L2∣I then
          sourceCoefficient (avoidSource s u) ha seed (G*I) else 0)
        (heightCoeff (τ χ) v) ballProfile (dyadicScale (n 1))≤
        (rawBudget (sourceVolume s) (A*cost) Z base G s.d/(L2.absNorm:ℝ))*
          (1+‖v‖)^(2*degree) := by
    have huG : u∣s.R*G := hu.trans (mul_dvd_mul_left s.R hseedG)
    have he := hZ.2 θ w σ freq t₀ V R₀ hw hwL hσ hσhi hV hfreq hholes hsmall
      s hcan hM hR hH hHnorm hHR hX₁ hX₂ hY₁ hY₂ cover (τ χ) n hn hncap
      (hτcap χ) u G seed L2 hG hseedG huG hL2 hGcap hL2cap v
    rw [height_energy_exact] at he
    have hr := (div_le_iff₀ (sourceVolume_pos s)).mp he
    have hpow : (G.absNorm:ℝ)^δCount≤Z^(Bnorm*δCount) := by
      have hh := Real.rpow_le_rpow (Nat.cast_nonneg _) hGcap hδCount.le
      simpa only [←Real.rpow_mul hz.le] using hh
    have hc := mul_le_mul (hcost χ) hpow
      (Real.rpow_nonneg (Nat.cast_nonneg _) _) hcost0
    let rest := A*sourceVolume s*Z^((3/4:ℝ)*rho+ε)/
      (G.absNorm:ℝ)/pairNorm s.d/(L2.absNorm:ℝ)*(1+‖v‖)^(2*degree)
    have hrest : 0≤rest := by
      have hv := (sourceVolume_pos s).le
      have hp := (pairNorm_pos s.hd.1 s.hd.2).le
      dsimp only [rest]
      positivity
    have hfinal := mul_le_mul_of_nonneg_left hc hrest
    have hpower : Z^base=Z^((3/4:ℝ)*rho+ε)*Z^(Bnorm*δCount) :=
      Real.rpow_add hz _ _
    apply hr.trans
    convert hfinal using 1 <;> dsimp only [rest,A,rawBudget] <;> (try simp only [hpower]) <;> ring
  have hbudget (G : Id) : 0≤rawBudget (sourceVolume s) (A*cost) Z base G s.d := by
    have hv := (sourceVolume_pos s).le
    have hp := (pairNorm_pos s.hd.1 s.hd.2).le
    unfold rawBudget
    positivity
  apply hpZ.2 Kphys hKphys n η τ tp (sourceColumns s)
    (sourceCoefficient (avoidSource s u) ha seed) C D hC hD hCD U hfamily
    Hsource hcolumns hdivision radius Q m χ₀ hQ72 hm hml hm2
    Eleft Eright (hbudget C) (hbudget D)
  · intro L2 hmem hLN hsf χ v
    exact hraw C hC hseedC hCcap L2 hsf (hLN.trans hdivision) χ v
  · intro L2 hmem hLN hsf χ v
    exact hraw D hD hseedD hDcap L2 hsf (hLN.trans hdivision) χ v

end
end Candidate.SilPrior.FourthPower.RepairedSmallPhysical
