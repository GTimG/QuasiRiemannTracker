/- Copyright (c) 2026 Sil. Apache-2.0.
Uniform actual nonexceptional suppliers for all remaining subsets of a
fixed original grid. Constants precede every allocation and original
profile. There is no source-energy premise.
-/
import Candidate.Feedback.FourthPower.MixedActualNonexceptionalBound
import Candidate.Feedback.FourthPower.MixedPrincipalPositivePart
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondUniformSubsetSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.Feedback.FourthPower.MixedFirstUniformNonexceptional
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open RayFourExpansion
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open ReferencePrimeEnclosure MixedCompletedRows MixedCanonicalSource MixedHeightEnergy
open MixedHeightEnvelope MixedRawEnvelope MixedActualEnvelopePhysical MixedLocalizedDictionary
open MixedActualGeometry MixedActualRetained MixedOriginalCoprimality
open CenteredMomentSecondBlockHarmonicMass CenteredMomentSecondRadicalBudget
open MixedOriginalNormCap MixedLiteralAllocation NativeInjectiveEnergy MixedPoissonLocalization
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentNaturalFixedRaySource CenteredMomentFiniteProfileExceptional
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization CenteredMomentCanonicalFirst
open CenteredMomentActiveSource CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit CenteredMomentSecondWindowBudget CenteredMomentSecondLiveBlock
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondWholeKernel
open CenteredMomentSecondActivePhysicalDictionary
open QuadraticInitialBound
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

open MixedActualNonexceptionalBound

/-- Only monotonicity of the displayed, already established budget. -/
theorem budget_mono (slots j k : ℕ) (hjk : j≤k)
    (Cp Cp' Cg Cg' Z exponent exponent' A A' b volume tp Wblock : ℝ)
    (η : Character) (seed : Id) (d : Id×Id)
    (hCp : 0≤Cp) (hCp' : Cp≤Cp') (hCg : 0≤Cg) (hCg' : Cg≤Cg')
    (hZ : 1≤Z) (hexp : exponent≤exponent') (hA : 0≤A) (hA' : A≤A') (hW : 0≤Wblock) :
    closedBudget slots j Cp Cg Z exponent A b volume tp Wblock η seed d≤
      closedBudget slots k Cp' Cg' Z exponent' A' b volume tp Wblock η seed d := by
  have hheight : 1≤heightEnvelope tp := by
    unfold heightEnvelope
    have h₁ : (1:ℝ)≤1+‖tp‖+2*Real.pi := by linarith [norm_nonneg tp,Real.pi_pos]
    have h₂ : (1:ℝ)≤1+2*Real.pi := by linarith [Real.pi_pos]
    simpa only [one_mul] using mul_le_mul h₁ h₂ zero_le_one (zero_le_one.trans h₁)
  have hh := pow_le_pow_right₀ hheight (Nat.mul_le_mul_left 2 hjk)
  have hm := pow_le_pow_left₀ (profileMoment_nonneg j)
    (CenteredMomentSecondUniformSubsetSource.moment_mono hjk) 2
  have hCpn := hCp.trans hCp'
  have hCgn := hCg.trans hCg'
  have hAn := hA.trans hA'
  have hz := Real.rpow_nonneg (zero_le_one.trans hZ) exponent
  have hpower := Real.rpow_le_rpow_of_exponent_le hZ hexp
  have hd : 0≤pairNorm d^2*(seed.absNorm:ℝ)*Wblock := by positivity
  unfold closedBudget
  apply div_le_div_of_nonneg_right _ hd
  gcongr
variable {α : Type*} [Fintype α]
local instance {β : Type*} : DecidableEq (β⊕Fin 2) := Classical.decEq _
variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

theorem uniform_nonexceptional_subsets
    (Holes : ℕ) (W : ℝ→ℂ)
    (a b Mcap L Lslot Lcap Cap BR BH B ε δ lo hi κ Lradius Cr εg : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b) (hM : 0<Mcap)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hBR : 0≤BR) (hBH : 0≤BH) (hB : 0≤B)
    (hCapb : b≤Cap) (hLordinary : L≤Lcap) (hε : 0<ε) (hδ : 0<δ)
    (hLradius : 0≤Lradius) (hCr : 0<Cr) (hεg : 0<εg)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus →
    ∃Cs Cp Cg : ℝ,0<Cs ∧ 0<Cp ∧ 0<Cg ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀T : Finset α,∀(θ : α→RayQuotient.Characters M Hray)(w σ freq : α→ℝ)(t V : ℝ)(R₀ : α→Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤V → (∀i,|freq i|≤V) → (∀i,(R₀ i).card≤Holes) →
    ∀R seed : Id,R≠0 → (R.absNorm:ℝ)≤Z^BR → Squarefree seed →
    ∀H : Finset PrimeIdeal,H⊆enclosure (Cap*Z^Lcap) →
      ((∏I∈holes H,I).absNorm:ℝ)≤Z^BH → (∀i : T,∀P∈H,P.val∈R₀ i.val) →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
    ∀(t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ),0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ →
      X₁≤Z^L → X₂≤Z^L → Y₁≤Z^L → Y₂≤Z^L → X₁*X₂=Y₁*Y₂ →
    ∀d : Id×Id,∀hd : d.1≠0 ∧ d.2≠0,
    let pool := fun i : T=>supportedPool (primePool M Hray 2 (Z^(w i.val)))
    let S := finiteColumns (Fintype.piFinset (sourcePools pool d hd b X₁ X₂ Y₁ Y₂))
    let β := originalColumn (enclosure (Cap*Z^Lcap)) H pool d hd R seed
      (slotCoefficient (fun i : T=>relativeCharacter M Hray hHray η₀ (θ i.val)) (fun i=>R₀ i.val) t)
      (fun i : T=>slotProfile W (σ i.val) (freq i.val)) (fun i : T=>Z^(w i.val))
      (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂
    let Hsource := sourceNormCap (fun i : T=>Z^(w i.val)) b (X₁*X₂) d
    let volume := X₁*X₂*∏i : T,Z^(w i.val)
    let A := Cs*diagonalControl ballProfile*(sourceControl control W₁*sourceControl control W₂)^2*
      (sourceHeight t V t₁ t₂)^degree
    Hsource≤Z^B →
    ∀(η : Character)(tp K Wblock Tsec ξ : ℝ)(m : O)(χ₀ : RayCharacter),
      0<K → 0<Wblock → m≠0 → ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      frequencyRadius Tsec Z ξ≤Cr*Z^Lradius →
    ∀ρ : (p : ActiveLabel S β)→(U : Finset (CommonIndex p.val.1 p.val.2))→
      SourceBlocks p.val.1 p.val.2 U (16*K*Wblock^4) (frequencyRadius Tsec Z ξ) Hsource→ℝ,
    (∀p∈liveLabels η S β,∀U,∀n : SourceBlocks p.val.1 p.val.2 U
        (16*K*Wblock^4) (frequencyRadius Tsec Z ξ) Hsource,
      physicalBlock η tp S β p.val.1 p.val.2
        (commonLabels_supported (activeSource S β) _ _ p.property).1
        (commonLabels_supported (activeSource S β) _ _ p.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false η χ₀ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
        ballProfile (16*K*Wblock^4) (fun i=>(n i:ℤ))≠0 →
      Real.logb Z (frequencyRadius Tsec Z ξ)+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator p.val.1 p.val.2))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+
        Real.logb Z (16*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ))≤ρ p U n ∧
        ρ p U n≤Mcap) →
      ‖localizedDensity Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
          (fun I : supportedColumns S=>β I*heightCoeff η tp I) K Wblock
          (retainedWeight (frequencyRadius Tsec Z ξ))-
        partEnergy true η χ₀ Q m tp S β ballProfile (16*K*Wblock^4) Tsec Z ξ Hsource/(Wblock:ℂ)‖ ≤
      closedBudget (Fintype.card T) degree Cp Cg Z (κ*(∑i,w i)+ε+δ+εg)
        A b volume tp Wblock η seed d := by
  choose degreeT controlT hbase using fun T : Finset α=>
    uniform_actual_nonexceptional_bound (α:=T) M Hray hHray Holes W
      a b Mcap L Lslot Lcap Cap BR BH B ε δ lo hi κ Lradius Cr εg
      hWs hW ha haUpper hb hM hLslot hLcap hCap hBR hBH hB hCapb hLordinary hε hδ
      hLradius hCr hεg hβ hκ Q hQt hQ72 hQM
  let degree := ∑T : Finset α,degreeT T
  let control := (Finset.univ : Finset (Finset α)).biUnion controlT
  have hn (T : Finset α) : degreeT T≤degree :=
    Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ T)
  have hcontrol (T : Finset α) : controlT T⊆control :=
    Finset.subset_biUnion_of_mem controlT (Finset.mem_univ T)
  refine ⟨degree,control,?_⟩
  intro η₀ hQη
  choose CsT CpT CgT hCsT hCpT hCgT hbase using fun T=>hbase T η₀ hQη
  have hconstant (f : Finset α→ℝ) (hf : ∀T,0<f T) :
      0<1+∑T : Finset α,f T ∧ ∀T,f T≤1+∑U : Finset α,f U := by
    constructor
    · have hh := Finset.sum_nonneg (fun T (_ : T∈(Finset.univ : Finset (Finset α)))=>(hf T).le)
      linarith
    · intro T
      have hh := Finset.single_le_sum (s:=Finset.univ) (f:=f)
        (fun U _=>(hf U).le) (Finset.mem_univ T)
      linarith
  let Cs := 1+∑T : Finset α,CsT T
  let Cp := 1+∑T : Finset α,CpT T
  let Cg := 1+∑T : Finset α,CgT T
  have hCs : 0<Cs := (hconstant CsT hCsT).1
  have hCp : 0<Cp := (hconstant CpT hCpT).1
  have hCg : 0<Cg := (hconstant CgT hCgT).1
  refine ⟨Cs,Cp,Cg,hCs,hCp,hCg,(Filter.eventually_all.mpr hbase).mono ?_⟩
  intro Z hZ
  refine ⟨(hZ ∅).1,?_⟩
  intro T θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ R seed hR hRN hseed
    H hH hholes hHR W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂
    hc₁ hc₂ hc₃ hc₄ hXY d hd pool S β Hsource volume A hsourcecap
    η tp K Wblock Tsec ξ m χ₀ hK hWblock hm hml hm2 hradius ρ hgeometry
  have he := (hZ T).2 (fun i=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val)
    (fun i=>freq i.val) t V (fun i=>R₀ i.val)
    (fun i=>hw i.val) (fun i=>hwL i.val) (fun i=>hσ i.val) (fun i=>hσhi i.val)
    hV (fun i=>hfreq i.val) (fun i=>hR₀ i.val) R seed hR hRN hseed H hH hholes hHR
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd
    hsourcecap η tp K Wblock Tsec ξ m χ₀ hK hWblock hm hml hm2 hradius ρ hgeometry
  let AT := CsT T*diagonalControl ballProfile*
    (sourceControl (controlT T) W₁*sourceControl (controlT T) W₂)^2*
    (sourceHeight t V t₁ t₂)^(degreeT T)
  have hheight := sourceHeight_one_le t V t₁ t₂ hV
  have hdiag := diagonalControl_nonneg ballProfile
  have hAT : 0≤AT := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (hCsT T).le hdiag) (sq_nonneg _))
      (pow_nonneg (zero_le_one.trans hheight) _)
  have hprofile : sourceControl (controlT T) W₁*sourceControl (controlT T) W₂≤
      sourceControl control W₁*sourceControl control W₂ :=
    mul_le_mul (MixedPrincipalPositivePart.control_mono (hcontrol T) W₁)
      (MixedPrincipalPositivePart.control_mono (hcontrol T) W₂)
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hATle : AT≤A := by
    have hpow := pow_le_pow_right₀ hheight (hn T)
    have hc := mul_le_mul
      (mul_le_mul_of_nonneg_right ((hconstant CsT hCsT).2 T) hdiag)
      (pow_le_pow_left₀ (mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)) hprofile 2)
      (sq_nonneg _) (mul_nonneg hCs.le hdiag)
    have ht := mul_le_mul hc hpow
      (pow_nonneg (zero_le_one.trans hheight) _)
      (mul_nonneg (mul_nonneg hCs.le hdiag) (sq_nonneg _))
    exact ht
  have hκ0 : 0≤κ := by linarith
  have hsum : (∑i : T,w i.val)≤∑i,w i := by
    rw [Finset.sum_coe_sort T w]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _=>hw i)
  have hexp : κ*(∑i : T,w i.val)+ε+δ+εg≤κ*(∑i,w i)+ε+δ+εg := by
    linarith [mul_le_mul_of_nonneg_left hsum hκ0]
  apply he.trans
  exact budget_mono (Fintype.card T) (degreeT T) degree (hn T)
    (CpT T) Cp (CgT T) Cg Z _ _ AT A b volume tp Wblock η seed d
    (hCpT T).le ((hconstant CpT hCpT).2 T) (hCgT T).le ((hconstant CgT hCgT).2 T)
    (hZ T).1.le hexp hAT hATle hWblock.le

end
end Candidate.Feedback.FourthPower.MixedFirstUniformNonexceptional
