/- Copyright (c) 2026 Sil. Apache-2.0.
Actual avoided active labels supply the seed, common norms, canonical
families and dyadic admissibility for the native physical block.

-/
import Candidate.Feedback.FourthPower.RepairedSmallPhysical
import Candidate.Feedback.FourthPower.MixedActualEnvelopePhysical
import Candidate.Feedback.FourthPower.MixedActualGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.Feedback.FourthPower.RepairedSmallActivePhysical
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
open CenteredMomentSecondNonexceptionalScalar
open MixedOriginalTail
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


open CenteredMomentActiveSource CenteredMomentSecondBlockAggregate
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondRadicalBudget CenteredMomentCompleteCommon
open MixedCanonicalEnvelope MixedOriginalCoprimality MixedOriginalNormCap
open MixedInnerExceptionalLedger MixedActualGeometry
open RepairedSmallPhysical

theorem factor_caps (Z x y B : ℝ) (hZ : 1<Z) (hx : 1≤x) (hy : 1≤y)
    (hlog : Real.logb Z x+Real.logb Z y≤B) : x≤Z^B ∧ y≤Z^B := by
  have hx0 := zero_lt_one.trans_le hx
  have hy0 := zero_lt_one.trans_le hy
  have hlx := Real.logb_nonneg hZ hx
  have hly := Real.logb_nonneg hZ hy
  constructor
  · calc
      x=Z^(Real.logb Z x) := (Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hx0).symm
      _≤Z^B := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  · calc
      y=Z^(Real.logb Z y) := (Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hy0).symm
      _≤Z^B := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)

theorem uniform_active_avoided_physical
    (Holes decay : ℕ) (Wslot : ℝ → ℂ) (Ψ : 𝓢(ℝ,ℂ))
    (a b Mcap L Lslot Lcap Cap BR BH Bnorm rho ε δCount δPhys lo hi : ℝ)
    (hWs : Function.support Wslot⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ Wslot)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hCapb : b≤Cap) (hLordinary : L≤Lcap)
    (hBR : 0≤BR) (hBH : 0≤BH) (hBnorm : 0≤Bnorm)
    (hMcap : 0≤Mcap) (hε : 0<ε) (hδCount : 0<δCount) (hδPhys : 0<δPhys)
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
      sourceNormCap s.P b s.T s.d≤Z^Bnorm →
    ∀cover : OriginalEnclosure s,∀u seed : Id,Squarefree seed → u∣s.R*seed →
    let Sco:=sourceColumns s;
    let beta:=sourceCoefficient (avoidSource s u) ha seed;
    let A:=Cs*slotCost s*diagonalControl ballProfile*
      (sourceControl control s.W₁*sourceControl control s.W₂)^2*
      (height t₀ V s.t₁ s.t₂)^degree;
    let base:=(3/4:ℝ)*rho+ε+Bnorm*δCount;
    ∀(η : Character)(p : ActiveLabel Sco beta)(U : Finset (CommonIndex p.val.1 p.val.2)),
    ∃τ : RayCharacter → Character,
      Family η p.val.1 p.val.2
        (commonLabels_supported (activeSource Sco beta) _ _ p.property).1
        (commonLabels_supported (activeSource Sco beta) _ _ p.property).2 U τ ∧
    ∀(tp radius Kphys Rdecl : ℝ)(m : O)(χ₀ : RayCharacter)(n : Fin 4 → ℤ),
      0<Kphys → m≠0 → ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      physicalBlock η tp Sco beta p.val.1 p.val.2
        (commonLabels_supported (activeSource Sco beta) _ _ p.property).1
        (commonLabels_supported (activeSource Sco beta) _ _ p.property).2 U radius
        (partRows false η χ₀ Q m p.val.1 p.val.2 U radius) Ψ Kphys n≠0 →
      Real.logb Z radius+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator p.val.1 p.val.2))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+
        Real.logb Z (16*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ))≤Rdecl → Rdecl≤Mcap →
      ‖physicalBlock η tp Sco beta p.val.1 p.val.2
        (commonLabels_supported (activeSource Sco beta) _ _ p.property).1
        (commonLabels_supported (activeSource Sco beta) _ _ p.property).2 U radius
        (partRows false η χ₀ Q m p.val.1 p.val.2 U radius) Ψ Kphys n‖≤
      Cp*Z^δPhys*(outerScalar p.val.1 p.val.2 Kphys n*normalizer p.val.1 p.val.2 U)*
        (windowBudget degree tp
          (rawBudget (sourceVolume s) (A*childEnvelope η p.val.1 p.val.2 U n) Z base p.val.1 s.d)*
        windowBudget degree tp
          (rawBudget (sourceVolume s) (A*childEnvelope η p.val.1 p.val.2 U n) Z base p.val.2 s.d))/
        (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))^decay := by
  obtain ⟨degree,control,hbase⟩ := uniform_avoided_physical (ι:=ι) M Hray hHray
    Holes decay Wslot Ψ a b L Lslot Lcap Cap BR BH Bnorm Mcap Mcap rho ε δCount δPhys lo hi
    hWs hW ha haUpper hb hLslot hLcap hCap hCapb hLordinary hBR hBH hBnorm hMcap hMcap
    hε hδCount hδPhys hβ Q hQt hQ72 hQM
  refine ⟨degree,control,?_⟩
  intro η₀ hQη₀
  obtain ⟨Cs,Cp,hCs,hCp,hbase⟩ := hbase η₀ hQη₀
  refine ⟨Cs,Cp,hCs,hCp,hbase.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq t₀ V R₀ hw hwL hσ hσhi hV hfreq hholes hsmall
    s hcan hM hR hH hHnorm hHR hX₁ hX₂ hY₁ hY₂ hsourcecap cover u seed hseed hu
    Sco beta A base η p U
  have hcols (I : Id) (hi : beta I≠0) :
      (I.absNorm:ℝ)≤sourceNormCap s.P b s.T s.d :=
    (original_coefficient_cap (avoidSource s u) ha seed I hi).2
  have hnorms := commonLabel_norm_bounds Sco beta (sourceNormCap s.P b s.T s.d)
    (fun I _ hi=>hcols I hi) p.val.1 p.val.2 p.property
  have hsupp := commonLabels_supported (activeSource Sco beta) _ _ p.property
  have hseeds := active_common_seed Sco beta seed hseed
    (fun I hi=>source_coefficient_seed (avoidSource s u) ha seed I hi) p
  have hsource0 : 0≤sourceNormCap s.P b s.T s.d := by
    have ht := s.total_pos
    have hp := pairNorm_pos s.hd.1 s.hd.2
    have hP (i : ι) : 0<s.P i := zero_lt_one.trans_le (s.hP i)
    unfold sourceNormCap
    exact mul_nonneg (mul_nonneg (sq_nonneg b) (div_nonneg ht.le hp.le))
      (Finset.prod_nonneg (fun i _ => mul_nonneg (by norm_num) (hP i).le))
  have hdivision : sourceNormCap s.P b s.T s.d/(p.val.2.absNorm:ℝ)≤Z^Bnorm :=
    (div_le_self hsource0 (ideal_norm_one_le hsupp.2.1)).trans hsourcecap
  obtain ⟨τall,hτall⟩ := exists_actual_families η Sco beta
  let τ:=τall p U
  have hf := hτall p U
  refine ⟨τ,hf,?_⟩
  intro tp radius Kphys Rdecl m χ₀ n hKphys hm hml hm2 hne hledger hRdecl
  let rows:=partRows false η χ₀ Q m p.val.1 p.val.2 U radius
  have hg (χ : RayCharacter) := actual_canonical_geometry hf tp Sco beta radius rows Ψ Kphys
    hKphys n hne Z BR Rdecl hZ.1 χ Q s.R s.hR hR hledger
  have hcaps (χ : RayCharacter) :
      dyadicScale (n 1)≤Z^Mcap ∧ ((τ χ).modulus.absNorm:ℝ)≤Z^Mcap :=
    factor_caps Z _ _ Mcap hZ.1 (hg χ).1 (ideal_norm_one_le (τ χ).modulus_ne_bot)
      ((hg χ).2.trans hRdecl)
  have hcost (χ : RayCharacter) :
      ((τ χ).modulus.absNorm:ℝ)*dyadicScale (n 1)≤childEnvelope η p.val.1 p.val.2 U n :=
    family_child_envelope hf tp Sco beta radius rows Ψ Kphys hKphys n hne χ
  have hcost0 : 0≤childEnvelope η p.val.1 p.val.2 U n := by
    have hh := (dyadicScale_pos (n 1)).le
    unfold childEnvelope
    positivity
  exact hZ.2 θ w σ freq t₀ V R₀ hw hwL hσ hσhi hV hfreq hholes hsmall
    s hcan hM hR hH hHnorm hHR hX₁ hX₂ hY₁ hY₂ cover u seed hu
    η τ p.val.1 p.val.2 hsupp.1 hsupp.2 (active_equal_support Sco beta p)
    hseeds.1 hseeds.2 (hnorms.1.trans hsourcecap) (hnorms.2.trans hsourcecap) U hf
    n tp radius Kphys (sourceNormCap s.P b s.T s.d) (childEnvelope η p.val.1 p.val.2 U n)
    hKphys hcost0 (hg 1).1 (hcaps 1).1 (fun χ=>(hcaps χ).2) hcost hcols hdivision
    m χ₀ hm hml hm2

end
end Candidate.Feedback.FourthPower.RepairedSmallActivePhysical
