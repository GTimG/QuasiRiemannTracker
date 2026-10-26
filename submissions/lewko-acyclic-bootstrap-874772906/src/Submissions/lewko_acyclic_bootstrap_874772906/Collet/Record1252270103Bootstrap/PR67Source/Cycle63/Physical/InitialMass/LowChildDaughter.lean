import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondLowUniform
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.LowChildReturned
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.WidenedState
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The bound for one final daughter of a LOW child of a step, controlled by the plain profiles clipped at the scale of
the child: the old moment at the width of the child, the allowance of the labels and the returned part of the second
step. The statement is the form of the old bound of the daughter (`actual_live_main_low_uniform`); it gives the bound
for the original plain profiles by `lowProfiles_of_daughter`. The bound with the second step is stated directly for the
original plain profiles (`two_level_low_profiles`). Released under Apache 2.0. -/
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
variable {α : Type*} [Fintype α] [DecidableEq α]

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The bound for one final daughter of a LOW child. The data of the step are those of `actual_live_main_low_uniform`.
The bound holds for the units `unit` and the frequency losses `omega`, `ξ` with `Adm unit omega ξ` and has the
exponent of the old bound with the loss `εX`, the rate `rate` of the padding and the allowance
`Xf Z q.C₁ g.D₁ g.datum.C g.datum.D q.E₂` of the labels, and a returned part `Ret` that is zero, or, when
`AllowRet`, the slot factor times the count form of the HIGH part of the second step of a child presented by `v₁`
with heights of the zeros at most `T` (`Presented` is stated for every widening of the state). The returned part has
the energy scale `st.rowWidth` of the state of the child (the logarithm of its radial scale), the loss `lossFloor`,
at most `Kcls` classes in each record (a constant chosen with `degree` and `Sp`), a total length that leaves the
planned deletion of the cell out of the capacity of the child, and an amplifier at most that of the second step in
the cell of the child, up to `gridSlack` and `ampSlack`. The lengths `w j` of the slots are at most the slot bound
`Lslot`; the bound of the old moment holds for the slot bound `commonMesh Mcap Bmask L εold`, so a statement proved from
it needs `Lslot ≤ commonMesh Mcap Bmask L εold` (`hLslot`). -/
def LowDaughterStmt [Led : Cycle63.AffineLedger] {Base : Type}
    (W : ℝ→ℂ) (B ap bp Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d : ℝ)
    (bs bp₁ bp₂ εwidth εpad Mmin : ℝ)
    (Adm : ℝ → ℝ → ℝ → Prop) (AllowRet : Prop) (rate εX : ℝ)
    (Xf : ℝ → Ideal O → Ideal O → Ideal O → Ideal O → Ideal O → ℝ)
    (base : Character → Base → Character) (Bnorm lossFloor gridSlack ampSlack : ℝ)
    (Presented : Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop) : Prop :=
  ∀η₀ : Character, ∀Q : Ideal O,
    ∀hQM : Q≤M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∃Kcls : ℝ, ∃Cg : ℝ, 0<Cg ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(hZ : 1<Z)(s : Input α)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh aLow : ℝ)(i : ℕ),
      Matches M H hH s η₀ θ w σ freq W B Z → s.upper≤bs → s.b₁=bp₁ → s.b₂=bp₂ →
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
    ∀p : Profiles ap bp,
      dilated s.W₁ (clipDilation (Cycle63.Physical.sourcePlainScales src.toSource second 0/
        (Ideal.absNorm (selectedPlain L₂ alloc 0):ℝ)))=p.profile 0 →
      dilated s.W₂ (clipDilation (Cycle63.Physical.sourcePlainScales src.toSource second 1/
        (Ideal.absNorm (selectedPlain L₂ alloc 1):ℝ)))=p.profile 1 →
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
        Cg*QuadraticInitialBound.diagonalControl st.radial.profile*(p.control Sp)^2*(1+|v|+height)^degree*
          (Z^(nominal+δwidth+amp-unit*(Cycle63.AffineLedger.lowReserve)+εold+εX+2*ε*d*(Fintype.card α:ℝ)+
            rate*padding+Cycle63.AffineLedger.q*mesh+Xf Z q.C₁ g.D₁ g.datum.C g.datum.D q.E₂)+Ret)

/-- The old bound of the final daughters of a LOW child (`actual_live_main_low_uniform`) is the bound of
`LowDaughterStmt` for all units, without allowance, without the loss `εX` and without a returned part, at the rate
`lowRate` of the padding. -/
theorem lowDaughterStmt_of_row0 [Cycle63.AffineLedger.DeletesIntoOldRegion] {Base : Type}
    (W : ℝ→ℂ) (A B ap bp Bmask L Lslot lo hi Mcap εold : ℝ)
    (hA : 0<A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤B) (hap : 0<ap) (hap' : ap≤1/4) (hbp : 1≤bp)
    (hBmask : 0≤Bmask) (hMcap : 0<Mcap) (hεold : 0<εold)
    (hLslot : Lslot≤Cycle25.Energy.commonMesh Mcap Bmask L εold)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤Rwidth) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0< margin)
    (hd : 0<d) (hdsupply : Mcap+Bmask+margin≤d) (hdm : d≤dmax)
    (bs bp₁ bp₂ εwidth εpad Mmin : ℝ)
    (hbs : 1≤bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0<Mmin)
    (base : Character → Base → Character) (Bnorm lossFloor gridSlack ampSlack : ℝ)
    (Presented : Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop) :
    LowDaughterStmt (α:=α) M H hH W B ap bp Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d bs bp₁ bp₂ εwidth εpad Mmin
      (fun _ _ _ => True) False Cycle63.AffineLedger.lowRate 0 (fun _ _ _ _ _ _ => 0) base Bnorm lossFloor gridSlack
      ampSlack Presented := by
  obtain ⟨degree,Sp,hmain⟩ := actual_live_main_low_uniform (α:=α) M H hH W A B ap bp Bmask L lo hi Mcap εold
    hA hWs hW hB hap hap' hbp hBmask hMcap hεold hbeta
    Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
    bs bp₁ bp₂ εwidth εpad Mmin hbs hew hep hmin
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cg,hCg,hbound⟩ := hmain η₀ Q hQM hQ0 hQt hQ72
  refine ⟨degree,Sp,0,Cg,hCg,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro hZone s θ w σ freq v height mesh aLow i hm hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm
    hσlo hσhi hheight hfreq ha ha' hfreqbin hhigh unit Mrow omega ξ hMmin _ hω hξ hMcap' hfit hz haff q
    cell amp g χ hP hPN second L₂ alloc st src nominal δwidth padding p hp₁ hp₂ hXcap₁ hXcap₂ v₁ Tz _
    hQM' hQη low
  have h := hZ.2 hZone s θ w σ freq v height mesh aLow i hm hsupper hsb₁ hsb₂ hw (fun j => (hwL j).trans hLslot) hwr
    hmesh hwm
    hσlo hσhi hheight hfreq ha ha' hfreqbin hhigh unit Mrow omega ξ hMmin hω hξ hMcap' hfit hz haff q g χ hP hPN
    second L₂ alloc p hp₁ hp₂ hXcap₁ hXcap₂
  refine ⟨0,le_rfl,Or.inl rfl,?_⟩
  refine h.trans_eq ?_
  dsimp only
  rw [add_zero, add_zero, add_zero]

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
