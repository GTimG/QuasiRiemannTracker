import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondLowUniform
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.FinalLow.Profiles
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle25.Energy.Endpoint
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
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

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

variable [Cycle63.AffineLedger] in
/-- Actual low bound controlled by the original plain profiles. The uniform
control and all constants precede the moving retained scales. -/
theorem actual_live_main_low_profiles [Cycle63.AffineLedger.DeletesIntoOldRegion]
    (W : ℝ→ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0<A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤B) (ha : 0<a) (ha' : a≤1/4) (hb : 1≤b)
    (hBmask : 0≤Bmask) (hMcap : 0<Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤Rwidth) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0< margin)
    (hd : 0<d) (hdsupply : Mcap+Bmask+margin≤d) (hdm : d≤dmax)
    (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0<Mmin) :
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∀η₀ : Character, ∀Q : Ideal O,
    ∀hQM : Q≤M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Cg : ℝ, 0<Cg ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(hZ : 1<Z)(s : Input α)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh aLow : ℝ)(i : ℕ),
      Matches M H hH s η₀ θ w σ freq W B Z → s.upper≤bs → s.b₁=b → s.b₂=b →
      (∀j,0≤w j) → (∀j,w j≤Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      (∀j,w j/d≤Rwidth) → 0≤ mesh → (∀j,w j≤ mesh) → (∀j,lo≤σ j) → (∀j,σ j≤hi) →
      0≤height → (∀j,|freq j|≤height) → 51/100≤aLow → aLow≤((1+Cycle63.AffineLedger.q)/2) →
      |v|+height+Z^τ/2≤(3*i+2:ℕ)*Z^τ → (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^η →
    ∀(unit Mrow omega ξ : ℝ),Mmin≤unit → 0≤omega → 0≤ξ → unit+εwidth*unit+ξ/2≤Mcap →
      Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)≤unit+(εwidth/2)*unit →
      (Cycle63.AffineLedger.slotFloor*unit≤∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.slotTop*unit) →
      length Z s.X₁+length Z s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.B*unit →
    ∀q : Chain s,
    let cell := Cycle63.AffineLedger.cellUpper (Cycle63.AffineLedger.originalCell ((∑j,Real.logb Z (s.P j))/unit))
    let amp := unit*Cycle63.AffineLedger.amp cell
    ∀g : LiveMainGeometry s q Z Mrow amp omega ξ bs (Fintype.card α),
    ∀(χ : RayFourExpansion.RayCharacter)(hP : q.R₂*q.E₂≠0)(hPN : ((q.R₂*q.E₂).absNorm:ℝ)≤Z^Bmask)
      (second : Bool)(L₂ : Ideal O)
      (alloc : Allocation L₂ (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices q.B₂.val⊕Fin 2))),
    let st := retainedState Z Bmask hZ (g.datum.τ χ) (internalQ Q η₀) (q.R₂*q.E₂) hP hPN g.datum.radius g.datum.C g.datum.D g.datum.inactive
    let src := q.final (g.datum.τ χ) v
    let nominal := secondNominal unit Z amp omega q.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive
    let δwidth := εwidth*unit+ξ/2
    let padding := omega+εpad*unit
    ∀p₀ : Profiles a b,
      s.W₁=(p₀.profile 0 : ℝ→ℂ) → s.W₂=(p₀.profile 1 : ℝ→ℂ) →
      finalPlain src second L₂ alloc 0≤Z^L → finalPlain src second L₂ alloc 1≤Z^L →
    let hQM' : st.fixedModulus≤M := inf_le_left.trans hQM
    let hQη : st.fixedModulus≤η₀.modulus := inf_le_right
    let low := ActualLow M H hH st η₀ hQM' hQη aLow e (3*(i+1:ℕ)*Z^τ)
    finalPositiveEnergy src second L₂ alloc (fun z=>st.radial.keep z ∧ low z) st.radial.profile st.radial.scale≤
      Cg*QuadraticInitialBound.diagonalControl st.radial.profile*(p₀.control Sp)^2*(1+|v|+height)^degree*
        Z^(nominal+δwidth+amp-unit*(Cycle63.AffineLedger.lowReserve)+εold+2*ε*d*(Fintype.card α:ℝ)+
          Cycle63.AffineLedger.lowRate*padding+Cycle63.AffineLedger.q*mesh) := by
  have haClip : 0<a/max 1 b := div_pos ha (by positivity)
  have haClip' : a/max 1 b≤1/4 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)< max 1 b)).mpr
    exact ha'.trans (by nlinarith [le_max_left (1:ℝ) b])
  obtain ⟨degree,S,hmain⟩ := actual_live_main_low_uniform (α:=α) M H hH W A B (a/max 1 b) b Bmask L lo hi Mcap εold
    hA hWs hW hB haClip haClip' hb hBmask hMcap hεold hbeta
    Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
    bs b b εwidth εpad Mmin hbs hew hep hmin
  obtain ⟨Sp,Cp,hCp,hcontrol⟩ := clipped_pair_control a b ha S
  refine ⟨degree,Sp,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,hbound⟩ := hmain η₀ Q hQM hQ0 hQt hQ72
  refine ⟨C*Cp^2,by positivity,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro hZone s θ w σ freq v height mesh aLow i hm hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm
    hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh unit Mrow omega ξ hMmin hω hξ hMcap' hfit hz haff q
    cell amp g χ hP hPN second L₂ alloc st src nominal δwidth padding p₀ hp₁ hp₂ hXcap₁ hXcap₂
  dsimp only
  let U := profileScales src second L₂ alloc
  have hU : ∀j,0<U j := profile_scales_pos src second L₂ alloc
  by_cases hret : ∀j,1≤U j*b
  · let p := retainedPair a b ha p₀ U hU 0
    have hp (j : Fin 2) : (p.profile j : ℝ→ℂ)=dilated (p₀.profile j) (clipDilation (U j)) :=
      actual_clipped_pair a b ha p₀ U hU hret j
    have henergy := hZ.2 hZone s θ w σ freq v height mesh aLow i hm hsupper hsb₁ hsb₂
      hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh
      unit Mrow omega ξ hMmin hω hξ hMcap' hfit hz haff q g χ hP hPN second L₂ alloc p
      (by rw [hp 0,←hp₁]; rfl) (by rw [hp 1,←hp₂]; rfl) hXcap₁ hXcap₂
    have hc := hcontrol p₀ U hU
    have hc2 : (p.control S)^2≤Cp^2*(p₀.control Sp)^2 := by
      calc (p.control S)^2≤(Cp*p₀.control Sp)^2 := pow_le_pow_left₀ (Profiles.control_nonneg p S) hc 2
           _=Cp^2*(p₀.control Sp)^2 := by ring
    have hdiag := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
    let exponent : ℝ := nominal+δwidth+amp-unit*(Cycle63.AffineLedger.lowReserve)+εold+2*ε*d*(Fintype.card α:ℝ)+
      Cycle63.AffineLedger.lowRate*padding+Cycle63.AffineLedger.q*mesh
    apply henergy.trans
    change C*QuadraticInitialBound.diagonalControl st.radial.profile*(p.control S)^2*
      (1+|v|+height)^degree*Z^exponent≤_
    calc C*QuadraticInitialBound.diagonalControl st.radial.profile*(p.control S)^2*
          (1+|v|+height)^degree*Z^exponent≤
        C*QuadraticInitialBound.diagonalControl st.radial.profile*(Cp^2*(p₀.control Sp)^2)*
          (1+|v|+height)^degree*Z^exponent := by gcongr
         _=_ := by ring
  · have hzrow : ∀z,Cycle63.Physical.sourcePositiveRow src.toSource second L₂ alloc z=0 := by
      intro z
      by_contra hne
      have hh := profile_scales_survive src second L₂ alloc z hne
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

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
