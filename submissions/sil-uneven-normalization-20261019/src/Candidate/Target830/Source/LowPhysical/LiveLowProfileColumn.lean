import Candidate.Target830.Parameters
import Candidate.Target830.Source.Low.PaidMain
import Candidate.Cycle63.Physical.InitialMass.SecondLowProfiles
import Candidate.Target830.Source.LowPhysical.LiveLowUniform
import Candidate.Cycle63.Physical.FinalProfiles
import Candidate.Cycle63.Physical.InitialMass.SecondLowProfileCommon
import Candidate.Cycle63.Physical.InitialMass.SecondLowCommon
import Candidate.Cycle63.Physical.InitialMass.SecondLowProfileColumn
import Candidate.Cycle63.Physical.InitialMass.SecondExtraction

/- Original module: Candidate.Target830.Source.LowPhysical.LiveLowProfiles. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Target830.Source.LowPhysical
noncomputable section
open OAI OAI.SevenEighths
open OAI.SevenEighths.Target830.Source.LowBranch
open OAI.SevenEighths.Cycle63InitialMass
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentCanonicalFirst
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentRetainedProfile CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentEligibleEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale
open Cycle63FinalLow
open Cycle63Moment.LowBranch Cycle63FinalNatural Cycle63FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle63FinalProfiles
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Literal retained plain quotients, before clipping. -/
def profileScales (P : SourcePlane) {ι : Type*} [Fintype ι] [DecidableEq ι] (src : Data ι)
    (second : Bool) (L₂ : Ideal O) (alloc : Allocation L₂ (Finset.univ : Finset (ι⊕Fin 2)))
    (j : Fin 2) : ℝ :=
  Cycle63.Physical.sourcePlainScales src.toSource second j/(selectedPlain L₂ alloc j).absNorm

theorem profile_scales_pos (P : SourcePlane) {ι : Type*} [Fintype ι] [DecidableEq ι] (src : Data ι)
    (second : Bool) (L₂ : Ideal O) (alloc : Allocation L₂ (Finset.univ : Finset (ι⊕Fin 2)))
    (j : Fin 2) : 0 < profileScales (P := P) src second L₂ alloc j := by
  apply div_pos (source_plain_positive src second j)
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (selectedDivisor_ne_zero L₂ Finset.univ alloc (Sum.inr j)))

/-- An actual surviving row forces both retained support tests. -/
theorem profile_scales_survive (P : SourcePlane) {ι : Type*} [Fintype ι] [DecidableEq ι] (src : Data ι)
    (second : Bool) (L₂ : Ideal O) (alloc : Allocation L₂ (Finset.univ : Finset (ι⊕Fin 2)))
    (z : O) (hne : Cycle63.Physical.sourcePositiveRow src.toSource second L₂ alloc z≠0) :
    1 ≤ profileScales (P := P) src second L₂ alloc 0*src.b₁ ∧
      1 ≤ profileScales (P := P) src second L₂ alloc 1*src.b₂ := by
  exact allocated_survives src L₂ alloc z _ _ (source_plain_positive src second 0)
    (source_plain_positive src second 1) hne

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Actual low bound controlled by the original plain profiles. The uniform
control and all constants precede the moving retained scales. -/
theorem actual_live_main_low_profiles (P : SourcePlane)
    (W : ℝ→ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0 < A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0 ≤ B) (ha : 0 < a) (ha' : a ≤ 1/4) (hb : 1 ≤ b)
    (hBmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hεold : 0 < εold)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ η)
    (hbudget : 8*e*Rwidth+κ ≤ ε) (hmargin : 0 < margin)
    (hd : 0 < d) (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1 ≤ bs) (hew : 0 < εwidth) (hep : 0 < εpad) (hmin : 0 < Mmin) :
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∀η₀ : Character, ∀Q : Ideal O,
    ∀hQM : Q ≤ M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀ ≤ Ideal.span {(72:O)} →
    ∃Cg : ℝ, 0 < Cg ∧ ∀ᶠZ : ℝ in atTop,1 < Z ∧
    ∀(hZ : 1 < Z)(s : Input α)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh aLow : ℝ)(i : ℕ),
      Matches M H hH s η₀ θ w σ freq W B Z → s.η=ηseed → s.upper ≤ bs → s.b₁=b → s.b₂=b →
      (∀j,0 ≤ w j) → (∀j,w j ≤ Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      (∀j,w j/d ≤ Rwidth) → 0 ≤ mesh → (∀j,w j ≤ mesh) → (∀j,lo ≤ σ j) → (∀j,σ j ≤ hi) →
      0 ≤ height → (∀j,|freq j| ≤ height) → 51/100 ≤ aLow → aLow ≤ ((1+P.q)/2) →
      |v|+height+Z^τ/2 ≤ (3*i+2:ℕ)*Z^τ → (3+(3*i+2:ℕ)*Z^τ)^2 ≤ (Z^d)^η →
    ∀(Mrow omega ξ : ℝ),Mmin ≤ Mrow → 0 ≤ omega → 0 ≤ ξ → Mrow+εwidth*Mrow+ξ/2 ≤ Mcap →
      ((17/500)*Mrow ≤ ∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j)) ≤ (1/25)*Mrow) →
      length Z s.X₁+length Z s.X₂+P.lambda*(∑j,Real.logb Z (s.P j)) ≤ P.B*Mrow →
    ∀q : Chain s,
    let cell := widthCellUpper ((∑j,Real.logb Z (s.P j))/Mrow)
    let amp := Mrow*P.amp cell
    ∀g : LiveMainGeometry s q Z Mrow amp omega ξ bs (Fintype.card α),
    ∀(χ : RayFourExpansion.RayCharacter)(hP : q.R₂*q.E₂≠0)(hPN : ((q.R₂*q.E₂).absNorm:ℝ) ≤ Z^Bmask)
      (second : Bool)(L₂ : Ideal O)
      (alloc : Allocation L₂ (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices q.B₂.val⊕Fin 2))),
    let st := retainedState Z Bmask hZ (g.datum.τ χ) (internalQ Q η₀) (q.R₂*q.E₂) hP hPN g.datum.radius g.datum.C g.datum.D g.datum.inactive
    let src := q.final (g.datum.τ χ) v
    let nominal := secondNominal Mrow Z amp omega q.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive
    let δwidth := εwidth*Mrow+ξ/2
    let padding := omega+εpad*Mrow
    ∀p₀ : Profiles a b,
      s.W₁=(p₀.profile 0 : ℝ→ℂ) → s.W₂=(p₀.profile 1 : ℝ→ℂ) →
      finalPlain src second L₂ alloc 0 ≤ Z^L → finalPlain src second L₂ alloc 1 ≤ Z^L →
    let hQM' : st.fixedModulus ≤ M := inf_le_left.trans hQM
    let hQη : st.fixedModulus ≤ η₀.modulus := inf_le_right
    let low := ActualLow M H hH st η₀ hQM' hQη aLow e (3*(i+1:ℕ)*Z^τ)
    finalPositiveEnergy src second L₂ alloc (fun z=> st.radial.keep z ∧ low z) st.radial.profile st.radial.scale ≤ 
      Cg*QuadraticInitialBound.diagonalControl st.radial.profile*(p₀.control Sp)^2*(1+|v|+height)^degree*
        Z^(nominal+δwidth+amp-Mrow*lowReserve+εold+2*ε*d*(Fintype.card α:ℝ)+
          (P.q/(6*incumbentKappa))*padding+P.q*mesh) := by
  have haClip : 0 < a/max 1 b := div_pos ha (by positivity)
  have haClip' : a/max 1 b ≤ 1/4 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ) < max 1 b)).mpr
    exact ha'.trans (by nlinarith [le_max_left (1:ℝ) b])
  obtain ⟨degree,S,hmain⟩ := actual_live_main_low_uniform (P := P) (α:=α) M H hH W A B (a/max 1 b) b Bmask L lo hi Mcap εold
    hA hWs hW hB haClip haClip' hb hBmask hMcap hεold hbeta
    Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
    ηseed bs b b εwidth εpad Mmin hbs hew hep hmin
  obtain ⟨Sp,Cp,hCp,hcontrol⟩ := clipped_pair_control a b ha S
  refine ⟨degree,Sp,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,hbound⟩ := hmain η₀ Q hQM hQ0 hQt hQ72
  refine ⟨C*Cp^2,by positivity,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro hZone s θ w σ freq v height mesh aLow i hm hsη hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm
    hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh Mrow omega ξ hMmin hω hξ hMcap' hz haff q
    cell amp g χ hP hPN second L₂ alloc st src nominal δwidth padding p₀ hp₁ hp₂ hXcap₁ hXcap₂
  dsimp only
  let U := profileScales (P := P) src second L₂ alloc
  have hU : ∀j,0 < U j := profile_scales_pos (P := P) src second L₂ alloc
  by_cases hret : ∀j,1 ≤ U j*b
  · let p := retainedPair a b ha p₀ U hU 0
    have hp (j : Fin 2) : (p.profile j : ℝ→ℂ)=dilated (p₀.profile j) (clipDilation (U j)) :=
      actual_clipped_pair a b ha p₀ U hU hret j
    have henergy := hZ.2 hZone s θ w σ freq v height mesh aLow i hm hsη hsupper hsb₁ hsb₂
      hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh
      Mrow omega ξ hMmin hω hξ hMcap' hz haff q g χ hP hPN second L₂ alloc p
      (by rw [hp 0,←hp₁]; rfl) (by rw [hp 1,←hp₂]; rfl) hXcap₁ hXcap₂
    have hc := hcontrol p₀ U hU
    have hc2 : (p.control S)^2 ≤ Cp^2*(p₀.control Sp)^2 := by
      calc (p.control S)^2 ≤ (Cp*p₀.control Sp)^2 := pow_le_pow_left₀ (Profiles.control_nonneg p S) hc 2
           _=Cp^2*(p₀.control Sp)^2 := by ring
    have hdiag := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
    let exponent : ℝ := nominal+δwidth+amp-Mrow*lowReserve+εold+2*ε*d*(Fintype.card α:ℝ)+
      (P.q/(6*incumbentKappa))*padding+P.q*mesh
    apply henergy.trans
    change C*QuadraticInitialBound.diagonalControl st.radial.profile*(p.control S)^2*
      (1+|v|+height)^degree*Z^exponent ≤ _
    calc C*QuadraticInitialBound.diagonalControl st.radial.profile*(p.control S)^2*
          (1+|v|+height)^degree*Z^exponent ≤ 
        C*QuadraticInitialBound.diagonalControl st.radial.profile*(Cp^2*(p₀.control Sp)^2)*
          (1+|v|+height)^degree*Z^exponent := by gcongr
         _=_ := by ring
  · have hzrow : ∀z,Cycle63.Physical.sourcePositiveRow src.toSource second L₂ alloc z=0 := by
      intro z
      by_contra hne
      have hh := profile_scales_survive (P := P) src second L₂ alloc z hne
      have hb₁ : src.b₁=b := hsb₁
      have hb₂ : src.b₂=b := hsb₂
      rw [hb₁,hb₂] at hh
      apply hret
      intro j; fin_cases j
      · exact hh.1
      · exact hh.2
    rw [zero_low_energy src second L₂ alloc _ _ _ hzrow]
    have hdiag := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
    positivity

#print axioms OAI.SevenEighths.Target830.Source.LowPhysical.actual_live_main_low_profiles
end
end OAI.SevenEighths.Target830.Source.LowPhysical
end

/- Original module: Candidate.Target830.Source.LowPhysical.LiveLowProfileCommon. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Target830.Source.LowPhysical
noncomputable section
open OAI OAI.SevenEighths
open OAI.SevenEighths.Target830.Source.LowBranch
open OAI.SevenEighths.Cycle63InitialMass
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentCanonicalFirst
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentRetainedProfile CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentEligibleEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale
open CenteredMomentCommonLinearNormalization CenteredMomentSourceLiveColumn
open Cycle63Moment
open Cycle63FinalLow
open Cycle63Moment.LowBranch Cycle63FinalNatural Cycle63FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle63FinalProfiles
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The genuine low analytic bound through both allocation layers.
Each common allocation stays fixed across the complete frequency sum. -/
theorem actual_live_main_low_profile_common (P : SourcePlane)
    (W : ℝ→ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0 < A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0 ≤ B) (ha : 0 < a) (ha' : a ≤ 1/4) (hb : 1 ≤ b)
    (hBmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hεold : 0 < εold)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ η)
    (hbudget : 8*e*Rwidth+κ ≤ ε) (hmargin : 0 < margin)
    (hd : 0 < d) (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1 ≤ bs) (hew : 0 < εwidth) (hep : 0 < εpad) (hmin : 0 < Mmin)
    (εshell : ℝ) (heshell : 0 < εshell) :
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∀η₀ : Character, ∀Q : Ideal O,
    ∀hQM : Q ≤ M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀ ≤ Ideal.span {(72:O)} →
    ∃Cg : ℝ, 0 < Cg ∧ ∀ᶠZ : ℝ in atTop,1 < Z ∧
    ∀(hZ : 1 < Z)(s : Input α)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh aLow : ℝ)(i : ℕ),
      Matches M H hH s η₀ θ w σ freq W B Z → s.η=ηseed → s.upper ≤ bs → s.b₁=b → s.b₂=b →
      (∀j,0 ≤ w j) → (∀j,w j ≤ Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      (∀j,w j/d ≤ Rwidth) → 0 ≤ mesh → (∀j,w j ≤ mesh) → (∀j,lo ≤ σ j) → (∀j,σ j ≤ hi) →
      0 ≤ height → (∀j,|freq j| ≤ height) → 51/100 ≤ aLow → aLow ≤ ((1+P.q)/2) →
      |v|+height+Z^τ/2 ≤ (3*i+2:ℕ)*Z^τ → (3+(3*i+2:ℕ)*Z^τ)^2 ≤ (Z^d)^η →
    ∀(Mrow omega ξ : ℝ),Mmin ≤ Mrow → 0 ≤ omega → 0 ≤ ξ → Mrow+εwidth*Mrow+ξ/2 ≤ Mcap →
      ((17/500)*Mrow ≤ ∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j)) ≤ (1/25)*Mrow) →
      length Z s.X₁+length Z s.X₂+P.lambda*(∑j,Real.logb Z (s.P j)) ≤ P.B*Mrow →
    ∀q : Chain s,
    let cell := widthCellUpper ((∑j,Real.logb Z (s.P j))/Mrow)
    let amp := Mrow*P.amp cell
    ∀g : LiveMainGeometry s q Z Mrow amp omega ξ bs (Fintype.card α),
    ∀(χ : RayFourExpansion.RayCharacter)(hP : q.R₂*q.E₂≠0)(hPN : ((q.R₂*q.E₂).absNorm:ℝ) ≤ Z^Bmask),
    let st := retainedState Z Bmask hZ (g.datum.τ χ) (internalQ Q η₀) (q.R₂*q.E₂) hP hPN g.datum.radius g.datum.C g.datum.D g.datum.inactive
    let src := withHeight q.first (g.datum.τ χ) v
    let nominal := secondNominal Mrow Z amp omega q.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive
    let δwidth := εwidth*Mrow+ξ/2
    let padding := omega+εpad*Mrow
    ∀(Ds : Finset (Ideal O))(T pad : ℝ), 1 ≤ T →
      (∀D∈Ds,Squarefree D ∧ T ≤ (D.absNorm:ℝ) ∧ (D.absNorm:ℝ) < 2*T) →
    ∀p₀ : Profiles a b,
      s.W₁=(p₀.profile 0 : ℝ→ℂ) → s.W₂=(p₀.profile 1 : ℝ→ℂ) →
      (∀B₂ : actualAllocations src.pools q.E₂,commonScalar src q.E₂ q.R₂ B₂≠0 →
        (commonData src q.E₂ q.R₂ B₂).toSource.allowance Z ≤ pad) →
      (∀B₂ : actualAllocations src.pools q.E₂,commonScalar src q.E₂ q.R₂ B₂≠0 →
        ∀D∈Ds,∀alloc∈(commonData src q.E₂ q.R₂ B₂).toSource.active D,∀second : Bool,
        finalPlain (commonData src q.E₂ q.R₂ B₂) second D alloc 0 ≤ Z^L ∧
        finalPlain (commonData src q.E₂ q.R₂ B₂) second D alloc 1 ≤ Z^L) →
    let hQM' : st.fixedModulus ≤ M := inf_le_left.trans hQM
    let hQη : st.fixedModulus ≤ η₀.modulus := inf_le_right
    let low := ActualLow M H hH st η₀ hQM' hQη aLow e (3*(i+1:ℕ)*Z^τ)
    ∀(zs : Finset O)(weight : O→ℝ),
      (∀z∈zs,st.radial.keep z ∧ low z) →
      (∀z∈zs,weight z ≤ (st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)).re) →
      (∑D∈Ds,∑z∈zs,weight z*commonRetainedCost src q.E₂ q.R₂ D z) ≤ 
      Cg*src.toData.profileFactor*(∏j,src.M j)^2*
        QuadraticInitialBound.diagonalControl st.radial.profile*(p₀.control Sp)^2*
        (1+|v|+height)^degree*(q.E₂.absNorm:ℝ)^(εshell-1)*(2*T)^(2*εshell)*
        Z^(nominal+δwidth+amp-Mrow*lowReserve+εold+2*ε*d*(Fintype.card α:ℝ)+
          (P.q/(6*incumbentKappa))*padding+P.q*mesh)*Z^pad := by
  obtain ⟨degree,Sp,hprofiles⟩ := actual_live_main_low_profiles (P := P) (α:=α) M H hH W A B a b Bmask L lo hi Mcap εold
    hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
    Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
    ηseed bs εwidth εpad Mmin hbs hew hep hmin
  choose Ks hKs hcommon using fun J : Finset α=> actual_common_low_energy (ι:=↥J) bs εshell heshell
  let Kall := 1+∑J : Finset α,Ks J
  have hKall : 0 < Kall := by
    dsimp [Kall]
    have hh : 0 ≤ ∑J : Finset α,Ks J := Finset.sum_nonneg (fun J _=>(hKs J).le)
    linarith
  have hKle (J : Finset α) : Ks J ≤ Kall := by
    have hh := Finset.single_le_sum (fun J (_ : J∈Finset.univ)=>(hKs J).le) (Finset.mem_univ J)
    dsimp [Kall]; linarith
  refine ⟨degree,Sp,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,hbound⟩ := hprofiles η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Kall*C,by positivity,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro hZone s θ w σ freq v height mesh aLow i hm hsη hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm
    hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh Mrow omega ξ hMmin hω hξ hMcap' hz haff q
    cell amp g χ hP hPN st src nominal δwidth padding Ds T pad hT hDs p₀ hp₁ hp₂ hallow hcaps
    hQM' hQη low zs weight hkeep hweight
  let exponent : ℝ := nominal+δwidth+amp-Mrow*lowReserve+εold+2*ε*d*(Fintype.card α:ℝ)+
    (P.q/(6*incumbentKappa))*padding+P.q*mesh
  let E := C*QuadraticInitialBound.diagonalControl st.radial.profile*(p₀.control Sp)^2*
    (1+|v|+height)^degree*Z^exponent
  have hdiag := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have henergy (B₂ : actualAllocations src.pools q.E₂)(hn : commonScalar src q.E₂ q.R₂ B₂≠0)
      (D : Ideal O)(hD : D∈Ds)
      (alloc : Allocation D (Finset.univ : Finset (liveIndices B₂.val⊕Fin 2)))
      (halloc : alloc∈(commonData src q.E₂ q.R₂ B₂).toSource.active D)(second : Bool) :
      finalPositiveEnergy (commonData src q.E₂ q.R₂ B₂) second D alloc
        (fun z=> st.radial.keep z ∧ low z) st.radial.profile st.radial.scale ≤ E := by
    let q' : Chain s := { q with B₂:=B₂ }
    have hB₂ : frozenCoefficient B₂.val q.E₂ q.R₂ q.first.ν q.first.W q.first.P≠0 :=
      right_ne_zero_of_mul hn
    let g' : LiveMainGeometry s q' Z Mrow amp omega ξ bs (Fintype.card α) :=
      { reflected:=g.reflected, C₀:=g.C₀, D₀:=g.D₀, hC₀:=g.hC₀, hD₀:=g.hD₀,
        heq₀:=g.heq₀, selected:=g.selected, E₀:=g.E₀, hmod:=g.hmod,
        δ:=g.δ, reserve:=g.reserve, homega:=g.homega, datum:=g.datum,
        parent:=g.parent, row:=g.row, radius_eq:=g.radius_eq, label:=g.label,
        first_nonzero:=g.first_nonzero, second_nonzero:=hB₂ }
    exact hZ.2 hZone s θ w σ freq v height mesh aLow i hm hsη hsupper hsb₁ hsb₂
      hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh
      Mrow omega ξ hMmin hω hξ hMcap' hz haff q' g' χ hP hPN second D alloc p₀ hp₁ hp₂
      (hcaps B₂ hn D hD alloc halloc second).1 (hcaps B₂ hn D hD alloc halloc second).2
  have hC₂ : q.E₂≠0 := CenteredMomentAllocatedNaturalRadial.common_nonzero q.first q.E₂ q.B₂
  have hh := hcommon (liveIndices q.B₁.val) src hsupper q.E₂ q.R₂ hC₂ Ds zs weight
    T Z pad E hT hZone hE hDs (fun z=> st.radial.keep z ∧ low z)
    st.radial.profile st.radial.scale st.radial.scale_pos (fun z _=> st.radial.nonneg z)
    hkeep hweight hallow henergy
  apply hh.trans
  have hp:=src.toData.profile_nonneg
  have hn:=CenteredMomentFirstScale.norm_pos q.E₂ hC₂
  calc
    _ ≤ Kall*src.toData.profileFactor*(∏j,src.M j)^2*E*(q.E₂.absNorm:ℝ)^(εshell-1)*
        (2*T)^(2*εshell)*Z^pad := by
      gcongr
      exact hKle _
    _=_ := by dsimp [E,exponent]; ring

end
end OAI.SevenEighths.Target830.Source.LowPhysical
#print axioms OAI.SevenEighths.Target830.Source.LowPhysical.actual_live_main_low_profile_common
end

/- Original module: Candidate.Target830.Source.LowPhysical.LiveLowProfileColumn. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Target830.Source.LowPhysical
noncomputable section
open OAI OAI.SevenEighths
open OAI.SevenEighths.Target830.Source.LowBranch
open OAI.SevenEighths.Cycle63InitialMass
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentCanonicalFirst
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentRetainedProfile CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentEligibleEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale
open CenteredMomentCommonLinearNormalization CenteredMomentSourceLiveColumn
open Cycle63Moment
open Cycle63FinalLow
open Cycle63Moment.LowBranch Cycle63FinalNatural Cycle63FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle63FinalProfiles
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)


open CenteredMomentCommonPairedSource
/-- The actual low analytic estimate for normalized columns, after both
common and residual allocations, with the original radial row majorant. -/
theorem actual_live_main_low_profile_column (P : SourcePlane)
    (W : ℝ→ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0 < A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0 ≤ B) (ha : 0 < a) (ha' : a ≤ 1/4) (hb : 1 ≤ b)
    (hBmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hεold : 0 < εold)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ η)
    (hbudget : 8*e*Rwidth+κ ≤ ε) (hmargin : 0 < margin)
    (hd : 0 < d) (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1 ≤ bs) (hew : 0 < εwidth) (hep : 0 < εpad) (hmin : 0 < Mmin)
    (εshell : ℝ) (heshell : 0 < εshell) :
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∀η₀ : Character, ∀Q : Ideal O,
    ∀hQM : Q ≤ M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀ ≤ Ideal.span {(72:O)} →
    ∃Cg : ℝ, 0 < Cg ∧ ∀ᶠZ : ℝ in atTop,1 < Z ∧
    ∀(hZ : 1 < Z)(s : Input α)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh aLow : ℝ)(i : ℕ),
      Matches M H hH s η₀ θ w σ freq W B Z → s.η=ηseed → s.upper ≤ bs → s.b₁=b → s.b₂=b →
      (∀j,0 ≤ w j) → (∀j,w j ≤ Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      (∀j,w j/d ≤ Rwidth) → 0 ≤ mesh → (∀j,w j ≤ mesh) → (∀j,lo ≤ σ j) → (∀j,σ j ≤ hi) →
      0 ≤ height → (∀j,|freq j| ≤ height) → 51/100 ≤ aLow → aLow ≤ ((1+P.q)/2) →
      |v|+height+Z^τ/2 ≤ (3*i+2:ℕ)*Z^τ → (3+(3*i+2:ℕ)*Z^τ)^2 ≤ (Z^d)^η →
    ∀(Mrow omega ξ : ℝ),Mmin ≤ Mrow → 0 ≤ omega → 0 ≤ ξ → Mrow+εwidth*Mrow+ξ/2 ≤ Mcap →
      ((17/500)*Mrow ≤ ∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j)) ≤ (1/25)*Mrow) →
      length Z s.X₁+length Z s.X₂+P.lambda*(∑j,Real.logb Z (s.P j)) ≤ P.B*Mrow →
    ∀q : Chain s,
    let cell := widthCellUpper ((∑j,Real.logb Z (s.P j))/Mrow)
    let amp := Mrow*P.amp cell
    ∀g : LiveMainGeometry s q Z Mrow amp omega ξ bs (Fintype.card α),
    ∀(χ : RayFourExpansion.RayCharacter)(hP : q.R₂*q.E₂≠0)(hPN : ((q.R₂*q.E₂).absNorm:ℝ) ≤ Z^Bmask),
    let st := retainedState Z Bmask hZ (g.datum.τ χ) (internalQ Q η₀) (q.R₂*q.E₂) hP hPN g.datum.radius g.datum.C g.datum.D g.datum.inactive
    let src := withHeight q.first (g.datum.τ χ) v
    let nominal := secondNominal Mrow Z amp omega q.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive
    let δwidth := εwidth*Mrow+ξ/2
    let padding := omega+εpad*Mrow
    ∀(seed : Ideal O)(hE₂ : Supported q.E₂),seed∣q.E₂ →
    ∀(Ds : Finset (Ideal O))(T pad : ℝ), 1 ≤ T →
      (∀D∈Ds,Squarefree D ∧ T ≤ (D.absNorm:ℝ) ∧ (D.absNorm:ℝ) < 2*T) →
    ∀p₀ : Profiles a b,
      s.W₁=(p₀.profile 0 : ℝ→ℂ) → s.W₂=(p₀.profile 1 : ℝ→ℂ) →
      (∀B₂ : actualAllocations src.pools q.E₂,commonScalar src q.E₂ q.R₂ B₂≠0 →
        (commonData src q.E₂ q.R₂ B₂).toSource.allowance Z ≤ pad) →
      (∀B₂ : actualAllocations src.pools q.E₂,commonScalar src q.E₂ q.R₂ B₂≠0 →
        ∀D∈Ds,∀alloc∈(commonData src q.E₂ q.R₂ B₂).toSource.active D,∀second : Bool,
        finalPlain (commonData src q.E₂ q.R₂ B₂) second D alloc 0 ≤ Z^L ∧
        finalPlain (commonData src q.E₂ q.R₂ B₂) second D alloc 1 ≤ Z^L) →
    let hQM' : st.fixedModulus ≤ M := inf_le_left.trans hQM
    let hQη : st.fixedModulus ≤ η₀.modulus := inf_le_right
    let low := ActualLow M H hH st η₀ hQM' hQη aLow e (3*(i+1:ℕ)*Z^τ)
    ∀(zs : Finset O)(weight : O→ℝ),(∀z∈zs,0 ≤ weight z) →
      (∀z∈zs,st.radial.keep z ∧ low z) →
      (∀z∈zs,weight z ≤ (st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)).re) →
      (∑D∈Ds,∑z∈zs,weight z*‖normalizedColumn src q.E₂ hE₂ q.R₂ seed D z‖^2) ≤ 
      Cg*src.toData.profileFactor*(∏j,src.M j)^2*
        QuadraticInitialBound.diagonalControl st.radial.profile*(p₀.control Sp)^2*
        (1+|v|+height)^degree*(q.E₂.absNorm:ℝ)^(εshell-1)*(2*T)^(3*εshell)*
        Z^(nominal+δwidth+amp-Mrow*lowReserve+εold+2*ε*d*(Fintype.card α:ℝ)+
          (P.q/(6*incumbentKappa))*padding+P.q*mesh)*Z^pad := by
  obtain ⟨degree,Sp,hcommon⟩ := actual_live_main_low_profile_common (P := P) (α:=α) M H hH W A B a b Bmask L lo hi Mcap εold
    hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
    Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
    ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell
  obtain ⟨K,hK,hpoint⟩ := actual_uniform_second_column_extraction (α:=α) εshell heshell
  refine ⟨degree,Sp,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,hbound⟩ := hcommon η₀ Q hQM hQ0 hQt hQ72
  refine ⟨K*C,by positivity,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro hZone s θ w σ freq v height mesh aLow i hm hsη hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm
    hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh Mrow omega ξ hMmin hω hξ hMcap' hz haff q
    cell amp g χ hP hPN st src nominal δwidth padding seed hE₂ hseed Ds T pad hT hDs p₀ hp₁ hp₂ hallow hcaps
    hQM' hQη low zs weight hnonneg hkeep hweight
  have hh := hZ.2 hZone s θ w σ freq v height mesh aLow i hm hsη hsupper hsb₁ hsb₂
    hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh
    Mrow omega ξ hMmin hω hξ hMcap' hz haff q g χ hP hPN Ds T pad hT hDs p₀ hp₁ hp₂
    hallow hcaps zs weight hkeep hweight
  have hT0 : 0 < 2*T := by linarith
  have hmajor : (∑D∈Ds,∑z∈zs,weight z*‖normalizedColumn src q.E₂ hE₂ q.R₂ seed D z‖^2) ≤ 
      K*(2*T)^εshell*(∑D∈Ds,∑z∈zs,weight z*commonRetainedCost src q.E₂ q.R₂ D z) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro D hD
    apply Finset.sum_le_sum
    intro z hz
    have hp:=mul_le_mul_of_nonneg_left
      (hpoint (liveIndices q.B₁.val) src q.E₂ hE₂ q.R₂ seed D hseed (hDs D hD).1 z) (hnonneg z hz)
    apply hp.trans
    have hd:=Real.rpow_le_rpow (Nat.cast_nonneg D.absNorm) (hDs D hD).2.2.le heshell.le
    have hc:=common_retained_cost_nonneg src q.E₂ q.R₂ D z
    have hbnd:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd hK.le)
      (mul_nonneg (hnonneg z hz) hc)
    convert hbnd using 1 <;> ring
  apply hmajor.trans
  apply (mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ K*(2*T)^εshell)).trans_eq
  rw [show 3*εshell=εshell+2*εshell by ring,Real.rpow_add hT0 εshell (2*εshell)]
  ring

end
end OAI.SevenEighths.Target830.Source.LowPhysical
#print axioms OAI.SevenEighths.Target830.Source.LowPhysical.actual_live_main_low_profile_column
end
