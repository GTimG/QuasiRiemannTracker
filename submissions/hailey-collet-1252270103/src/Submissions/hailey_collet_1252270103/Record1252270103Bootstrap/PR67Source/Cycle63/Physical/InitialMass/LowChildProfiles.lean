import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.LowChildDaughter
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondLowProfiles
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The bound for one final daughter of a LOW child controlled by the original plain profiles. Released under
Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
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
variable {α : Type*} [Fintype α] [DecidableEq α]

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The bound for one final daughter of a LOW child controlled by the original plain profiles `p₀`, of the form of
`LowDaughterStmt`. -/
def LowProfilesStmt [Led : Cycle63.AffineLedger] {Base : Type}
    (W : ℝ→ℂ) (B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d : ℝ)
    (bs εwidth εpad Mmin : ℝ)
    (Adm : ℝ → ℝ → ℝ → Prop) (AllowRet : Prop) (rate εX : ℝ)
    (Xf : ℝ → Ideal O → Ideal O → Ideal O → Ideal O → Ideal O → ℝ)
    (base : Character → Base → Character) (Bnorm lossFloor gridSlack ampSlack : ℝ)
    (Presented : Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop) : Prop :=
  ∀η₀ : Character, ∀Q : Ideal O,
    ∀hQM : Q≤M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∃Kcls : ℝ, ∃Cg : ℝ, 0<Cg ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(hZ : 1<Z)(s : Input α)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh aLow : ℝ)(i : ℕ),
      Matches M H hH s η₀ θ w σ freq W B Z → s.upper≤bs → s.b₁=b → s.b₂=b →
      (∀j,0≤w j) → (∀j,w j≤Lslot) →
      (∀j,w j/d≤Rwidth) → 0≤ mesh → (∀j,w j≤ mesh) → (∀j,lo≤σ j) → (∀j,σ j≤hi) →
      0≤height → (∀j,|freq j|≤height) → 51/100≤aLow → aLow≤((1+Cycle63.AffineLedger.q)/2) →
      |v|+height+Z^τ/2≤(3*i+2:ℕ)*Z^τ → (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^η →
    ∀(unit Mrow omega ξ : ℝ),Mmin≤unit → Adm unit omega ξ → 0≤omega → 0≤ξ → unit+εwidth*unit+ξ/2≤Mcap →
      Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)≤unit+(εwidth/2)*unit →
      (Cycle63.AffineLedger.slotFloor*unit≤∑j,Real.logb Z (s.P j) ∧
        (∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.slotTop*unit) →
      length Z s.X₁+length Z s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j))≤
        Cycle63.AffineLedger.B*unit →
    ∀q : Chain s,
    let cell := Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell ((∑j,Real.logb Z (s.P j))/unit))
    let amp := unit*Cycle63.AffineLedger.amp cell
    ∀g : LiveMainGeometry s q Z Mrow amp omega ξ bs (Fintype.card α),
    ∀(χ : RayFourExpansion.RayCharacter)(hP : q.R₂*q.E₂≠0)(hPN : ((q.R₂*q.E₂).absNorm:ℝ)≤Z^Bmask)
      (second : Bool)(L₂ : Ideal O)
      (alloc : Allocation L₂ (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices q.B₂.val⊕Fin 2))),
    let st := retainedState Z Bmask hZ (g.datum.τ χ) (internalQ Q η₀) (q.R₂*q.E₂) hP hPN g.datum.radius g.datum.C
      g.datum.D g.datum.inactive
    let src := q.final (g.datum.τ χ) v
    let nominal := secondNominal unit Z amp omega q.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive
    let δwidth := εwidth*unit+ξ/2
    let padding := omega+εpad*unit
    ∀p₀ : Profiles a b,
      s.W₁=(p₀.profile 0 : ℝ→ℂ) → s.W₂=(p₀.profile 1 : ℝ→ℂ) →
      finalPlain src second L₂ alloc 0≤Z^L → finalPlain src second L₂ alloc 1≤Z^L →
    ∀(v₁ : O)(Tz : ℝ),
      (∀(W' : ℝ)(hW' : st.width≤W'),Presented η₀ Z (widenState st W' hW') v₁ Tz) →
    let hQM' : st.fixedModulus≤M := inf_le_left.trans hQM
    let hQη : st.fixedModulus≤η₀.modulus := inf_le_right
    let low := ActualLow M H hH st η₀ hQM' hQη aLow e (3*(i+1:ℕ)*Z^τ)
    ∃Ret : ℝ,0≤Ret ∧
      ReturnedClause M H hH AllowRet base η₀ Z Bnorm Tz v₁ st.rowWidth lossFloor
        (Real.logb Z (volume s)-Real.logb Z (q.C₁.absNorm:ℝ)-Real.logb Z (q.E₂.absNorm:ℝ)+
          supportPadding (Fintype.card α) bs s.b₁ s.b₂ Z-unit*Cycle63.Optimization.fixedDeletion cell+gridSlack)
        (unit*Cycle63.Optimization.secondAmp cell+ampSlack) Kcls
        (Z^(2*ε*d*(Fintype.card α:ℝ)+Cycle63.AffineLedger.q*(unit*Cycle63.Optimization.fixedDeletion cell+mesh)))
        Ret ∧
      finalPositiveEnergy src second L₂ alloc (fun z=>st.radial.keep z ∧ low z) st.radial.profile st.radial.scale≤
        Cg*QuadraticInitialBound.diagonalControl st.radial.profile*(p₀.control Sp)^2*(1+|v|+height)^degree*
          (Z^(nominal+δwidth+amp-unit*(Cycle63.AffineLedger.lowReserve)+εold+εX+2*ε*d*(Fintype.card α:ℝ)+
            rate*padding+Cycle63.AffineLedger.q*mesh+Xf Z q.C₁ g.D₁ g.datum.C g.datum.D q.E₂)+Ret)

/-- The bound for one final daughter of a LOW child with the plain profiles clipped at the scale of the child gives
the bound with the original plain profiles. -/
theorem lowProfiles_of_daughter [Led : Cycle63.AffineLedger] {Base : Type}
    (W : ℝ→ℂ) (B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d : ℝ)
    (bs εwidth εpad Mmin : ℝ)
    (Adm : ℝ → ℝ → ℝ → Prop) (AllowRet : Prop) (rate εX : ℝ)
    (Xf : ℝ → Ideal O → Ideal O → Ideal O → Ideal O → Ideal O → ℝ)
    (base : Character → Base → Character) (Bnorm lossFloor gridSlack ampSlack : ℝ)
    (Presented : Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop)
    (ha : 0<a)
    (hdaughter : LowDaughterStmt (α:=α) M H hH W B (a/max 1 b) b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d bs b b
      εwidth εpad Mmin Adm AllowRet rate εX Xf base Bnorm lossFloor gridSlack ampSlack Presented) :
    LowProfilesStmt (α:=α) M H hH W B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d bs εwidth εpad Mmin Adm
      AllowRet rate εX Xf base Bnorm lossFloor gridSlack ampSlack Presented := by
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨degree,S,Kcls,C,hC,hbound⟩ := hdaughter η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Sp,Cp,hCp,hcontrol⟩ := clipped_pair_control a b ha S
  refine ⟨degree,Sp,Kcls,C*Cp^2,by positivity,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro hZone s θ w σ freq v height mesh aLow i hm hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm
    hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh unit Mrow omega ξ hMmin hunit hω hξ hMcap' hfit hz haff q
    cell amp g χ hP hPN second L₂ alloc st src nominal δwidth padding p₀ hp₁ hp₂ hXcap₁ hXcap₂ v₁ Tz hpres
    hQM' hQη low
  let U := profileScales src second L₂ alloc
  have hU : ∀j,0<U j := profile_scales_pos src second L₂ alloc
  by_cases hret : ∀j,1≤U j*b
  · let p := retainedPair a b ha p₀ U hU 0
    have hp (j : Fin 2) : (p.profile j : ℝ→ℂ)=dilated (p₀.profile j) (clipDilation (U j)) :=
      actual_clipped_pair a b ha p₀ U hU hret j
    obtain ⟨Ret,hRet0,hRet,henergy⟩ := hZ.2 hZone s θ w σ freq v height mesh aLow i hm hsupper hsb₁ hsb₂
      hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh
      unit Mrow omega ξ hMmin hunit hω hξ hMcap' hfit hz haff q g χ hP hPN second L₂ alloc p
      (by rw [hp 0,←hp₁]; rfl) (by rw [hp 1,←hp₂]; rfl) hXcap₁ hXcap₂ v₁ Tz hpres
    refine ⟨Ret,hRet0,hRet,?_⟩
    have hc := hcontrol p₀ U hU
    have hc2 : (p.control S)^2≤Cp^2*(p₀.control Sp)^2 := by
      calc (p.control S)^2≤(Cp*p₀.control Sp)^2 := pow_le_pow_left₀ (Profiles.control_nonneg p S) hc 2
           _=Cp^2*(p₀.control Sp)^2 := by ring
    have hdiag := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
    let exponent : ℝ := nominal+δwidth+amp-unit*(Cycle63.AffineLedger.lowReserve)+εold+εX+
      2*ε*d*(Fintype.card α:ℝ)+rate*padding+Cycle63.AffineLedger.q*mesh+
      Xf Z q.C₁ g.D₁ g.datum.C g.datum.D q.E₂
    apply henergy.trans
    change C*QuadraticInitialBound.diagonalControl st.radial.profile*(p.control S)^2*
      (1+|v|+height)^degree*(Z^exponent+Ret)≤_
    have hZE : 0≤Z^exponent := Real.rpow_nonneg (zero_le_one.trans hZone.le) _
    calc C*QuadraticInitialBound.diagonalControl st.radial.profile*(p.control S)^2*
          (1+|v|+height)^degree*(Z^exponent+Ret)≤
        C*QuadraticInitialBound.diagonalControl st.radial.profile*(Cp^2*(p₀.control Sp)^2)*
          (1+|v|+height)^degree*(Z^exponent+Ret) := by gcongr
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
    refine ⟨0,le_rfl,Or.inl rfl,?_⟩
    rw [zero_low_energy src second L₂ alloc _ _ _ hzrow]
    have hdiag := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
    have hZE : 0≤Z^(nominal+δwidth+amp-unit*(Cycle63.AffineLedger.lowReserve)+εold+εX+
      2*ε*d*(Fintype.card α:ℝ)+rate*padding+Cycle63.AffineLedger.q*mesh+
      Xf Z q.C₁ g.D₁ g.datum.C g.datum.D q.E₂) := Real.rpow_nonneg (zero_le_one.trans hZone.le) _
    positivity

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
