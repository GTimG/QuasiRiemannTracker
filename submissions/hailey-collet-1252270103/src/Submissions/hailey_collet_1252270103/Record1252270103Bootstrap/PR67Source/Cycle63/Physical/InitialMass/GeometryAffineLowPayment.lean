import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineScheduleData
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryMainLowCompletePayment
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryMainAbsoluteBox
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineExceptionalGates
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxRecDepth 2500
set_option maxHeartbeats 100000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentSourceLiveColumn
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceMass CenteredMomentRankinRadical CenteredMomentFirstDiscardedEnergy
open CenteredMomentLogDyadic CenteredMomentWholeDivisorShell CenteredMomentSlotRatios
open CenteredMomentCommonPairedSource
open CenteredMomentFirstChildProfileControl
open Cycle63FinalNatural Cycle63Moment.LowBranch
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
open Cycle63Moment LocalMoment
open CenteredMomentSecondInputCapacitySource
open CenteredMomentChildRows CenteredMomentSecondCanonical CenteredMomentSecondEnergySplit
open CenteredMomentNaturalRowSource
open Cycle63InitialSource
open Cycle63FinalLow
open Cycle63Moment.LowBranch Cycle63FinalNatural Cycle63FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle63FinalProfiles

variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal HeckeFamily.O) [NeZero M]
variable (H : Subgroup (HeckeFamily.O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

local instance geometryAffineLowDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := geometryMainCoarseFamilySumDecidable

variable [Cycle63.AffineLedger] in
/-- Actual affine endpoint and source-scale receipts. -/
structure GeometryAffineLowSourceGates (s : Input α) (p : Profiles (1/4) (9/4))
    (Cs Z : ℝ) : Prop extends GeometryAffineExceptionalSourceGates s p (Fintype.card α) Cs Z where
  b₁ : s.b₁=9/4
  b₂ : s.b₂=9/4
  plainScales : ∀side j,Cycle63.Physical.sourcePlainScales s.toData.toSource side j≤Z^(1:ℝ)
  primeScales : ∀j,s.P j≤Z^(1:ℝ)
  windows : ∀j,logWindow (s.lo j) (s.hi j)≤Real.log 2

omit [DecidableEq α] in
variable [Cycle63.AffineLedger] in
/-- All added source gates come from the actual affine constructor. -/
theorem actual_affine_low_source_gates
    (η₀ : Character)(θ : α→RayQuotient.Characters M H)
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (w σ freq : α→ℝ)(hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
    {Z Bmask bΦ : ℝ}(state : NaturalState Z Bmask bΦ)(p : Profiles (1/4) (9/4))
    (t X₁ X₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂)(Cs : ℝ)(hZ : 1<Z)
    (hw : ∀i,0≤w i)(hwin : Cycle63.AffineLedger.PlainWindow (length Z X₁) (length Z X₂) (∑i,w i)) :
    let inp:=affineInput M H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) t X₁ X₂ hX₁ hX₂
    GeometryAffineExceptionalSourceGates inp p (Fintype.card α) Cs Z →
    GeometryAffineLowSourceGates inp p Cs Z ∧ Matches M H hH inp η₀ θ w σ freq W 2 Z := by
  intro inp caps
  have hvol:=hwin.volume_le (Finset.sum_nonneg (fun i _=>hw i))
  have hplain:=affine_plain_caps M H hH η₀ θ W hW 1 2 (33/50) (33/50)
    (by norm_num) hWs w σ freq hσ state p (by norm_num) (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) 1 t X₁ X₂ hX₁ hX₂
    1 hZ (by norm_num) le_rfl (Cycle63.AffineLedger.comparisonLength_nonneg _ _ _ hwin)
    (Cycle63.AffineLedger.comparisonLength_le _ _ _ hwin)
    (by linarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hw i)])
  refine ⟨⟨caps,rfl,rfl,hplain,?_,?_⟩,?_⟩
  · intro i
    have hi : w i≤1 := (Finset.single_le_sum (fun j _=>hw j) (Finset.mem_univ i)).trans
      (hwin.slots_le.trans Cycle63.AffineLedger.slotTop_le_one)
    exact Real.rpow_le_rpow_of_exponent_le hZ.le hi
  · intro i
    change max |Real.log (1:ℝ)| |Real.log (2:ℝ)|≤Real.log 2
    simp only [Real.log_one,abs_zero,abs_of_nonneg (Real.log_nonneg (by norm_num : (1:ℝ)≤2)),
      max_eq_right (Real.log_nonneg (by norm_num : (1:ℝ)≤2))]
    exact le_rfl
  · constructor <;> intros <;> rfl

set_option linter.defProp false in
/-- The actual absolute box is common to every selected first allocation. -/
def geometryAffineLowBoxReceipt (N : ℕ)(g : GeometryAffineLowSchedule) :=
  eventual_actual_geometry_main_absolute_box N 4 (g.μ/8) (9/4) (9/4)
    (g.μ/64) g.δ (by norm_num) (by linarith [g.μ_pos]) (by norm_num) (by norm_num)
    (by linarith [g.μ_pos]) (by linarith [g.μ_pos]) g.δ_pos

def geometryAffineLowBoxConstant (N : ℕ)(g : GeometryAffineLowSchedule) : ℝ :=
  Classical.choose (geometryAffineLowBoxReceipt N g)

/- Fixed mesh-facing caps are installed on the proved complete consumer.
Actual cardinality is retained in every first Fourier scale and second datum. -/
attribute [local irreducible] mainLowPhysicalCompleteCost mainLowFixedRayPhysicalCost
variable [Cycle63.AffineLedger] in
set_option maxHeartbeats 140000 in
theorem affine_low_complete_physical_spec_mono {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ ℂ) (A B a b Bmask L Lslot lo hi Mcap εold : ℝ)
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
    (hbs : 1≤bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0<Mmin)
    (εshell : ℝ) (heshell : 0<εshell) (N : ℕ)(Cs : ℝ)(hCs : 1≤Cs)
    (supply εv Bnorm εlabels : ℝ)(hsupply : 0<supply)(hev : 0<εv)
    (hBnorm : 0≤Bnorm)(hel : 0<εlabels)
    (Adm : ℝ→ℝ→ℝ→Prop)
    (Presented : Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop)
    (ap εmass Bmass : ℝ)(hap : 0<ap)(hemass : 0≤εmass)
    (U εunion : ℝ)(hUcap : 0≤U)(heunion : 0<εunion)
    (window pad : ℝ)(hwindow : 0≤window)(hpad : 0<pad)(hL0 : 0≤L)
    (εfirst Cfirst εbox Cbox : ℝ)(degree : ℕ)(Sp Sp₁ : Finset (ℕ×ℕ))(Cg Cu : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤M) (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)}) (Z : ℝ)
    (hsub : Sp⊆Sp₁)(hCg : 0≤Cg)(hCu : 0≤Cu)(hfirst : 0≤Cfirst)(hbox : 0≤Cbox)
    (hspec : MainLowCompletePhysicalSpec (α:=α) M H hH
      W A B a b Bmask L Lslot lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel Adm Presented
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      εfirst Cfirst εbox Cbox degree Sp Cg Cu η₀ Q hQM hQ72 Z) :
    MainLowCompletePhysicalSpec (α:=α) M H hH
      W A B a b Bmask L Lslot lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel Adm Presented
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      εfirst Cfirst εbox Cbox degree Sp₁ Cg Cu η₀ Q hQM hQ72 Z := by
  unfold MainLowCompletePhysicalSpec at hspec ⊢
  intro hZ s θ w σ freq heightV height mesh hcard hmass hsupply' hm hsupper hsb₁ hsb₂
    hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq hT hfreqbin hβhi
    unit Mrow reserve ξ hMmin hAdm hω hξ hMcap' hfit hzslot haff Label _ reflected second R seed₀ bin t firstIndex
    first cell amp childSrc Rchild seed K Tsec p c exponent sideLower hf₁ hw₁ hw₂ hsource
    hs₀ hs₀0 hinj hfirstproj rows hOriginal hU box hboxCard hbox datum B₂ rwitness hf₂ q g χ₀ m hm₀ hml hm₂
    hP hPN divisorSeed hE₂ hdivisor p₀ hp₁ hp₂ Ψ hsourceOriginal hplain₁ hplain₂ hpool
    hwindowSource hplainScale st leftR uR unitR Tz hleft hu₀ hdict _ hpres canonical firstMass physical error
    exponentFull t₀ u hshift
    hseed
  have hbound := hspec hZ s θ w σ freq heightV height mesh hcard hmass hsupply' hm hsupper hsb₁ hsb₂ hw hwL hwr hmesh
    hwm hσlo hσhi hheight hfreq hT hfreqbin hβhi unit Mrow reserve ξ hMmin hAdm hω hξ hMcap' hfit hzslot haff
    reflected second R seed₀ bin t firstIndex hf₁ hw₁ hw₂ hsource hs₀ hs₀0 hinj hfirstproj rows hOriginal hU box
    hboxCard hbox B₂ rwitness hf₂ χ₀ m hm₀ hml hm₂ hP hPN divisorSeed hE₂ hdivisor p₀ hp₁ hp₂ Ψ hsourceOriginal
    hplain₁ hplain₂ hpool hwindowSource hplainScale leftR uR unitR Tz hleft hu₀ hdict hpres t₀ u hshift hseed
  apply hbound.trans
  have hctrl := CenteredMomentEnergyBandMonotonicity.profile_control_mono p₀ hsub
  have hphy : 0≤physical := (geometry_high_factor_pos reflected _ bin
    (geometrySupportConstant_pos N supply ap ap hsupply hap hap)).le
  have hlow := (lowerFactor_pos N supply ap hsupply hap).le
  have hdiag := QuadraticInitialBound.diagonalControl_nonneg ballProfile
  have hb0 := zero_le_one.trans hb
  have hCs0 := zero_le_one.trans hCs
  gcongr
  exact Profiles.control_nonneg p₀ Sp

variable [Cycle63.AffineLedger] in
set_option maxHeartbeats 160000 in
def actual_affine_low_complete_enlarged {Adm : ℝ→ℝ→ℝ→Prop} {labelExp : Bool → ℝ → ℝ → FirstSourceLabel → ℝ}
    {Presented : (Bmask : ℝ) → Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop}
    (hgate : LowBinGate labelExp 6)
    {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ ℂ) (A B a b Bmask L Lslot lo hi Mcap εold : ℝ)
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
    (hbs : 1≤bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0<Mmin)
    (εshell : ℝ) (heshell : 0<εshell) (N : ℕ)(Cs : ℝ)(hCs : 1≤Cs)
    (supply εv Bnorm εlabels : ℝ)(hsupply : 0<supply)(hev : 0<εv)
    (hBnorm : 0≤Bnorm)(hel : 0<εlabels)
    (hrow5 : LowSelectedStmt (α:=α) M H hH W B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d bs εwidth εpad Mmin
      εshell N Cs supply εv Bnorm εlabels Adm labelExp (Presented Bmask))
    (ap εmass Bmass : ℝ)(hap : 0<ap)(hemass : 0≤εmass)
    (U εunion : ℝ)(hUcap : 0≤U)(heunion : 0<εunion)
    (window pad : ℝ)(hwindow : 0≤window)(hpad : 0<pad)(hL0 : 0≤L) (hτgap : 2*τ<d*η) (hBstrong : Bmass+1≤Bnorm) (εfirst : ℝ)(hefirst : 0<εfirst) (εbox Cbox : ℝ)
    (ηcoarse : Character)(u₀ : O)(F₀ : NaturalRow ηcoarse u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (ξ₀ Bcoarse plainCap targetMin coarseLoss coarseShell coarsePad coarseVolume : ℝ)
    (hN : N=Fintype.card α)(hbsb : bs=b)(hboxC : 0≤Cbox)
    (hξ₀ : 0≤ξ₀)(hξloss : ξ₀≤ coarseLoss)(hBc : 0≤Bcoarse)(hpc : 0≤plainCap)
    (hcloss : 0<coarseLoss)(hcshell : 0<coarseShell)(hcpad : 0<coarsePad)(hcvolume : 0<coarseVolume) :
    ∀(η₀ : Character)(Q : Ideal O)(hQM : Q≤M),
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → ∀hQ72 : internalQ Q η₀≤Ideal.span {(72:O)},
      Σdegree : ℕ,ΣSp : Finset (ℕ×ℕ),ΣCu : ℝ,ΣCfirst : ℝ,
        PLift (0<Cu ∧ 0<Cfirst ∧ (0,0)∈Sp) ×
        (let coarse:=Bcoarse+(39*(Bcoarse+coarseLoss)+(Bcoarse+coarseLoss)*εmass+
          (Bcoarse+coarseLoss)*coarseShell+coarseVolume)+8*(Bcoarse+coarseLoss)+3*coarseLoss+
          ((N:ℝ)+2)*plainCap+2*coarsePad+3*(((N:ℝ)+2)*U)*coarseShell+Bcoarse
         let degreeAll:=mainLowCompleteHeightDegree coarse targetMin τ hτ degree
         ΣCg : ℝ,ΣKall : ℝ,PLift (0<Cg ∧ 0<Kall ∧ ∀ᶠZ : ℝ in atTop,2≤Z ∧
          MainLowCompleteAllHeightSpec (α:=α) M H hH
      W A B a b Bmask L Lslot lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel Adm (Presented Bmask)
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      εfirst Cfirst εbox Cbox ξ₀ Bcoarse plainCap targetMin Kall degreeAll degree Sp Cg Cu η₀ Q hQM hQ72 Z)) := by
  intro η₀ Q hQM hQ0 hQt hQ72
  let coarse:=Bcoarse+(39*(Bcoarse+coarseLoss)+(Bcoarse+coarseLoss)*εmass+
        (Bcoarse+coarseLoss)*coarseShell+coarseVolume)+8*(Bcoarse+coarseLoss)+3*coarseLoss+
        ((N:ℝ)+2)*plainCap+2*coarsePad+3*(((N:ℝ)+2)*U)*coarseShell+Bcoarse
  have hα : Fintype.card α≤N := by rw [hN]
  let cr:=actual_main_low_complete_coarse_payment (α:=α) ηcoarse u₀ F₀ R₀ hu₀
    N hα Bcoarse coarseLoss coarseShell coarsePad Cs b bs window plainCap supply ap
    coarseVolume εmass ξ₀ U hBc hcloss hcshell hcpad hCs hb hbs hwindow hpc hsupply hap
    hcvolume hemass hξ₀ hξloss hUcap
  let Kcoarse:=Classical.choose cr
  have hKcoarse:=(Classical.choose_spec cr).1
  have hcoarse:=(Classical.choose_spec cr).2
  let k:=actual_main_low_complete_physical_bins (α:=α) M H hH hgate
      W A B a b Bmask L Lslot lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel hrow5
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      hτgap hBstrong εfirst hefirst εbox Cbox η₀ Q hQM hQ0 hQt hQ72
  let Sp:=k.2.1∪{(0,0)}
  refine ⟨k.1,Sp,k.2.2.1,k.2.2.2.1,PLift.up ⟨k.2.2.2.2.1.down.1,k.2.2.2.2.1.down.2,
    Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩,?_⟩
  dsimp only
  let hc:=k.2.2.2.2.2
  let degreeAll:=mainLowCompleteHeightDegree coarse targetMin τ hτ k.1
  let Kall:=mainLowCompleteHeightConstant N degreeAll e supply ap hc.1 k.2.2.1 k.2.2.2.1 Cbox b Cs Kcoarse
  have hKall : 0<Kall := by
    dsimp only [Kall,mainLowCompleteHeightConstant,mainLowCompleteFee]
    have hCu:=k.2.2.2.2.1.down.1
    have hfirst:=k.2.2.2.2.1.down.2
    have hCg:=hc.2.down.1
    have hdiag:=QuadraticInitialBound.diagonalControl_nonneg ballProfile
    have hlower:=(lowerFactor_pos N supply ap hsupply hap).le
    have hCs0:=zero_le_one.trans hCs
    positivity
  refine ⟨hc.1,Kall,PLift.up ⟨hc.2.down.1,hKall,?_⟩⟩
  filter_upwards [hc.2.down.2,hcoarse] with Z hz hcz
  refine ⟨hz.1,?_⟩
  have hmono:=affine_low_complete_physical_spec_mono (α:=α) M H hH
      W A B a b Bmask L Lslot lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel Adm (Presented Bmask)
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      εfirst k.2.2.2.1 εbox Cbox k.1 k.2.1 Sp hc.1 k.2.2.1 η₀ Q hQM hQ72 Z
      Finset.subset_union_left hc.2.down.1.le k.2.2.2.2.1.down.1.le
      k.2.2.2.2.1.down.2.le hboxC hz.2
  exact (main_low_complete_all_height_spec_of_receipts (α:=α) M H hH
      W A B a b Bmask L Lslot lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel Adm (Presented Bmask)
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      εfirst k.2.2.2.1 εbox Cbox ξ₀ Bcoarse plainCap targetMin coarse Kcoarse
      k.1 Sp hc.1 k.2.2.1 η₀ Q hQM hQ72 Z
      hc.2.down.1.le k.2.2.2.2.1.down.1.le k.2.2.2.2.1.down.2.le hboxC hKcoarse
      hN hbsb hmono hcz).2

variable [Cycle63.AffineLedger] in
set_option linter.defProp false in
set_option linter.unusedVariables false in
/-- Row 5 at the parameters of the first step of the affine moment, for the modulus `M`, the schedule `g` and the cap
`Mcap` of the width of the states: for every slot type `α`, every smooth slot profile `W` supported in `[1, 2]` and every profile cap
`Cs` at least one, the selected low frequency columns are paid at the unit one, the mask `28`, the degree `31` of the
dictionary, the plain scales `1/4` and `9/4` and the losses of the schedule. -/
def LowSelectedPaidAt (g : GeometryAffineLowSchedule) (Mcap Lslot : ℝ) (Adm : ℝ→ℝ→ℝ→Prop)
    (labelExp : Bool → ℝ → ℝ → FirstSourceLabel → ℝ)
    (Presented : (Bmask : ℝ) → Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop) : Prop :=
  ∀⦃α : Type⦄[Fintype α][DecidableEq α]
    (W : ℝ→ℂ)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)(hW : ContDiff ℝ ∞ W)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)(Cs : ℝ)(hCs : 1≤Cs),
    LowSelectedStmt (α:=α) M H hH W 2 (1/4) (9/4) 28 1 Lslot (33/50) (33/50) Mcap (g.μ/8) 1 g.τ g.δ g.e g.vslot 31
      (9/4) (g.μ/8) (g.μ/8) 1 g.δ (Fintype.card α) Cs 1 g.δ 4 g.δ Adm labelExp (Presented 28)

variable [Cycle63.AffineLedger] in
/-- Row 5 at every parameter is row 5 at the parameters of the first step, for a cap `Mcap` of the width of the states
at most two. -/
theorem lowSelectedPaidAt_of_columns {Adm : ℝ→ℝ→ℝ→Prop} {labelExp : Bool → ℝ → ℝ → FirstSourceLabel → ℝ}
    {Presented : (Bmask : ℝ) → Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop}
    (h : LowSelectedPaidColumns Adm labelExp Presented) (g : GeometryAffineLowSchedule) (Mcap Lslot : ℝ)
    (hMcap0 : 0<Mcap) (hMcap2 : Mcap≤2) (hLslot : Lslot≤Cycle25.Energy.commonMesh Mcap 28 1 (g.μ/8)) :
    LowSelectedPaidAt M H hH g Mcap Lslot Adm labelExp Presented := by
  intro α _ _ W hWs hW hbeta Cs hCs
  exact h M H hH W 1 2 (1/4) (9/4) 28 1 Lslot (33/50) (33/50) Mcap (g.μ/8)
    (by norm_num) hWs hW (by norm_num) (by norm_num) le_rfl (by norm_num)
    (by norm_num) hMcap0 (by linarith [g.μ_pos]) hLslot hbeta
    1 31 g.τ g.δ g.e g.κ g.vslot 1 31
    (by norm_num) (by norm_num) g.τ_pos g.δ_pos g.e_pos g.e_cap g.κ_pos g.vslot_nonneg
    (by simpa only [mul_one] using g.budget) (by norm_num) (by norm_num) (by linarith) le_rfl
    (9/4) (g.μ/8) (g.μ/8) 1 (by norm_num) (by linarith [g.μ_pos]) (by linarith [g.μ_pos]) (by norm_num)
    g.δ g.δ_pos (Fintype.card α) Cs hCs
    1 g.δ 4 g.δ (by norm_num) g.δ_pos (by norm_num) g.δ_pos

variable [Cycle63.AffineLedger] in
set_option maxHeartbeats 140000 in
def actual_affine_low_complete_data {Adm : ℝ→ℝ→ℝ→Prop} {labelExp : Bool → ℝ → ℝ → FirstSourceLabel → ℝ}
    {Presented : (Bmask : ℝ) → Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop}
    (hgate : LowBinGate labelExp 6)
    (W : ℝ→ℂ)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)(hW : ContDiff ℝ ∞ W)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)(g : GeometryAffineLowSchedule)(Mcap Lslot : ℝ)(hMcap2 : Mcap≤2)
    (hMcap0 : 0<Mcap)(hrow5 : LowSelectedPaidAt M H hH g Mcap Lslot Adm labelExp Presented)(Cs : ℝ)(hCs : 1≤Cs)
    (ηcoarse : Character)(u₀ : O)(F₀ : NaturalRow ηcoarse u₀)(R₀ : Ideal O)(hu₀ : u₀≠0) :=
  actual_affine_low_complete_enlarged (α:=α) M H hH hgate
    W 1 2 (1/4) (9/4) 28 1 Lslot (33/50) (33/50) Mcap (g.μ/8)
    (by norm_num) hWs hW (by norm_num) (by norm_num) le_rfl (by norm_num)
    (by norm_num) hMcap0 (by linarith [g.μ_pos]) hbeta
    1 31 g.τ g.δ g.e g.κ g.vslot 1 31
    (by norm_num) (by norm_num) g.τ_pos g.δ_pos g.e_pos g.e_cap g.κ_pos g.vslot_nonneg
    (by simpa only [mul_one] using g.budget) (by norm_num) (by norm_num) (by linarith) le_rfl
    (9/4) (g.μ/8) (g.μ/8) 1 (by norm_num) (by linarith [g.μ_pos]) (by linarith [g.μ_pos]) (by norm_num)
    g.δ g.δ_pos (Fintype.card α) Cs hCs
    1 g.δ 4 g.δ (by norm_num) g.δ_pos (by norm_num) g.δ_pos (hrow5 (α:=α) W hWs hW hbeta Cs hCs)
    (1/4) g.δ 3 (by norm_num) g.δ_pos.le 3 g.δ (by norm_num) g.δ_pos
    (Real.log 2) (g.μ/8) (Real.log_nonneg (by norm_num)) (by linarith [g.μ_pos]) (by norm_num)
    g.cutoff (by norm_num) g.δ g.δ_pos g.δ (geometryAffineLowBoxConstant (Fintype.card α) g)
    ηcoarse u₀ F₀ R₀ hu₀
    (g.μ/64) 4 1 (-1) (g.μ/8) g.δ g.δ g.δ
    rfl rfl (Classical.choose_spec (geometryAffineLowBoxReceipt (Fintype.card α) g)).1.le
    (by linarith [g.μ_pos]) (by linarith [g.μ_pos]) (by norm_num) (by norm_num)
    (by linarith [g.μ_pos]) g.δ_pos g.δ_pos g.δ_pos

/-- Actual profiles provide the coarse pointwise norm receipt after adjoining
(0,0), uniformly in all physical source coordinates. -/
theorem affine_low_profile_norm_receipt (p : Profiles (1/4) (9/4))
    (Sp : Finset (ℕ×ℕ)) (hzero : (0,0)∈Sp) :
    let B₁:=sourceControl Sp (p.profile 0)
    let B₂:=sourceControl Sp (p.profile 1)
    0≤B₁ ∧ 0≤B₂ ∧ (∀x,‖p.profile 0 x‖≤B₁) ∧ (∀x,‖p.profile 1 x‖≤B₂) ∧
      (B₁*B₂)^2≤(p.control Sp)^2 := by
  intro B₁ B₂
  have hn (j : Fin 2)(x : ℝ) : ‖p.profile j x‖≤ sourceControl Sp (p.profile j) := by
    apply (SchwartzMap.norm_le_seminorm ℝ (p.profile j) x).trans
    change (schwartzSeminormFamily ℝ ℝ ℂ) (0,0) (p.profile j)≤
      Sp.sup (schwartzSeminormFamily ℝ ℝ ℂ) (p.profile j)
    exact Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ) hzero
  exact ⟨sourceControl_nonneg _ _,sourceControl_nonneg _ _,hn 0,hn 1,le_rfl⟩

variable [Cycle63.AffineLedger] in
/- Complete selected low physical cost. All source, profile, child-radius,
projector-mask and box estimates are provided by actual receipts. The remaining
premises concern the fixed source, its valid schedule and supported first selection. -/
set_option linter.unusedVariables false in
set_option linter.defProp false in
set_option maxHeartbeats 140000 in
def GeometryAffineLowSelectedSpec
    (W : ℝ→ℂ)(hbeta : 51/100≤HeckeZeroSupremum.beta)
    (g : GeometryAffineLowSchedule)(Mcap Lslot Cs : ℝ)
    (Adm : ℝ→ℝ→ℝ→Prop)
    (Presented : Character → (Z : ℝ) → NaturalState Z 28 2 → O → ℝ → Prop)
    (Sp : Finset (ℕ×ℕ))(degreeAll : ℕ)(Kall : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤M)
    (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)})(Z : ℝ) : Prop :=
  ∀(hZ : 1<Z)(s : Input α)(p : Profiles (1/4) (9/4))
    (caps : GeometryAffineLowSourceGates s p Cs Z)
    (θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
    (hm : Matches M H hH s η₀ θ w σ freq W 2 Z)
    (R seed : Ideal O)(Rc Mrow : ℝ)(hR : R≠0)(hseed : Squarefree seed)
    (hRc : Rc≤20)(hRcap : (R.absNorm:ℝ)≤Z^Rc)(hMrow : 0≤Mrow)(hMrow1 : Mrow≤1)
    (hfit : Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)≤1+g.μ/16)
    (hAdm : Adm 1 (frequencyLoss Z 32 (g.μ/64)+g.μ/8) (g.μ/64))
    (height mesh : ℝ)(hw : ∀j,0≤w j)
    (hwL : ∀j,w j≤Lslot)
    (hwr : ∀j,w j/31≤1)(hmesh : 0≤ mesh)(hwm : ∀j,w j≤ mesh)
    (hσ : ∀j,σ j∈Set.Icc (33/50:ℝ) (33/50))
    (hheight : 0≤height)(hfreq : ∀j,|freq j|≤height)(hT : 2<Z^g.τ)
    (hβhi : HeckeZeroSupremum.beta≤7/8)
    (hzslot : Cycle63.AffineLedger.slotFloor≤∑j,Real.logb Z (s.P j) ∧
      (∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.slotTop)
    (haff : length Z s.X₁+length Z s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j))≤
      Cycle63.AffineLedger.B)
    {Label : Type}[Fintype Label]
    (reflected second : Bool)(bin : ℤ×(Fin 5→ℤ))(t : ℝ)
    (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z (g.μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin),
    let first:=fun l=>geometryFirstLabel s R seed (Z^Mrow) Z (g.μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
    let amp:=(1:ℝ)*Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell ((∑j,Real.logb Z (s.P j))/(1:ℝ))))
    let omega:=frequencyLoss Z 32 (g.μ/64)+g.μ/8
    ∀(hamp0 : 0≤amp)(hamp : |amp|≤4)(homega : |omega|≤4)
      (htarget : -1≤geometryAffineLowTarget g (Fintype.card α) amp omega mesh)
      (hf₁ : ∀l,frozenCoefficient (firstIndex l).2.val
        (geometryColumnIdeal reflected s R seed (Z^Mrow) Z (g.μ/64)
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
        R s.ν s.W s.P≠0)
      (hinj : Function.Injective (fun l=>(first l,(firstIndex l).1.val.2.1.val)))
      (hfirstproj : ∀l,seed∣firstProjectorRadical (first l).1.1 (first l).1.2 (first l).2.val),
    let rows:=mainLowSelectedNonzeroRows reflected s R seed Z Mrow amp (g.μ/64) (g.μ/8)
      (9/4) t (Fintype.card α) hZ bin caps.zero₁ caps.zero₂ firstIndex
    let datum : rows→SecondInputDatum α:=fun r=>geometryLowSecondDatum reflected s R seed Z Mrow amp
      (g.μ/64) (g.μ/8) (9/4) t (Fintype.card α) hZ bin (firstIndex r.val.1)
      caps.zero₁ caps.zero₂ r.val.2
    ∀(χ₀ : rows→RayFourExpansion.RayCharacter)(m : O)(hm₀ : m≠0)
      (hml : goodLambda∣m)(hm₂ : (2:O)∣m)(Ψ : 𝓢(ℝ,ℂ))(t₀ u : ℝ),
    ∃hP : ∀r,(datum r).R*(if second then (datum r).D else (datum r).C)≠0,
    ∃hPN : ∀r,((((datum r).R*(if second then (datum r).D else (datum r).C)).absNorm:ℝ))≤Z^(28:ℝ),
    ∃hPNc : ∀r,((((datum r).R*(if second then (datum r).D else (datum r).C)).absNorm:ℝ))≤Z^(Rc+8),
    let st:=fun (r : rows)(ray : RayFourExpansion.RayCharacter)=>retainedState Z 28 hZ ((datum r).τ ray)
      (internalQ Q η₀) ((datum r).R*(if second then (datum r).D else (datum r).C)) (hP r) (hPN r)
      (datum r).radius (datum r).C (datum r).D (datum r).inactive
    ∀(left₁ : Bool)(u₀ : O)(unit₁ : FirstSourceLabel→O)(Tz : ℝ),
    left₁=!reflected → u₀≠0 →
    ((∀l,IsUnit (unit₁ l)) ∧ Real.logb Z (normValue u₀)≤g.δ) →
    let mult:=fun r : rows=>firstRowMultiplier first left₁ u₀ unit₁ r.val
    (∀r,∀ray,∀(W' : ℝ)(hW' : (st r ray).width≤W'),Presented η₀ Z (widenState (st r ray) W' hW') (mult r) Tz) →
    let canonical:=fun (r : rows) (χ ψ : RayFourExpansion.RayCharacter)=>
      mainLowCanonicalSelector M H hH (datum r) (χ₀ r) χ ψ (internalQ Q η₀) hQ72
        m hm₀ hml hm₂ Z 28 hZ second (hP r) (hPN r) η₀
        (inf_le_left.trans hQM) inf_le_right g.e (Z^g.τ) g.e_pos hT hbeta hβhi
    let firstMass:=fun l=>geometryFirstHighMass reflected s R seed Ψ Mrow Z (g.μ/64) g.δ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
    let childSrc:=fun l=>geometryLowFirstChild reflected s R seed (Z^Mrow) Z (g.μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t (firstIndex l)
    mainLowPhysicalCompleteCost (Fintype.card α) 1 (1/4) second
      (fun r=>ordinarySecondDatum (datum r) (χ₀ r) (internalQ Q η₀) m)
      (fun r=>firstMass r.val.1/volume (childSrc r.val.1)) t₀ u canonical≤
      Kall*(p.control Sp)^2*geometryHighFactor reflected (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) bin*
        Z^(geometryAffineLowTarget g (Fintype.card α) amp omega mesh+(1-Mrow))*
        (1+|t|+height)^degreeAll*(1+|t₀|)^degreeAll*(1+|u|)^degreeAll

attribute [local irreducible] Finset.univ

set_option maxHeartbeats 100000 in
theorem affine_low_selected_original_mem {Label : Type*} [Fintype Label]
    (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z)
    (key : ℤ×(Fin 5→ℤ)) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)
    (r : (l : Label)×GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key (firstIndex l))
    (hr : r∈mainLowSelectedNonzeroRows reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ firstIndex) :
    (⟨firstIndex r.1,r.2⟩ : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key)∈
      geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ := by
  exact (Finset.mem_filter.mp hr).2

private theorem affine_low_mask_cap (Z Rc : ℝ)(hZ : 1<Z)(R E : Ideal O)
    (hR : (R.absNorm:ℝ)≤Z^(Rc+4))(hE : (E.absNorm:ℝ)≤Z^(4:ℝ)) :
    ((R*E).absNorm:ℝ)≤Z^(Rc+8) := by
  rw [map_mul,Nat.cast_mul]
  calc
    _≤Z^(Rc+4)*Z^(4:ℝ) := mul_le_mul hR hE (Nat.cast_nonneg _) (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
    _=Z^(Rc+8) := by rw [←Real.rpow_add (zero_lt_one.trans hZ)]; congr 1; ring

def geometryAffineLowCoarseExponent (g : GeometryAffineLowSchedule)(N : ℕ) : ℝ :=
  4+(39*(4+g.μ/8)+(4+g.μ/8)*g.δ+(4+g.μ/8)*g.δ+g.δ)+
    8*(4+g.μ/8)+3*(g.μ/8)+((N:ℝ)+2)*1+2*g.δ+3*(((N:ℝ)+2)*3)*g.δ+4

attribute [local irreducible] GeometryAffineLowSelectedSpec MainLowCompleteAllHeightSpec
attribute [local irreducible] actual_affine_low_complete_data actual_affine_low_complete_enlarged
variable [Cycle63.AffineLedger] in
set_option maxHeartbeats 260000 in
def actual_affine_low_selected_payment {Adm : ℝ→ℝ→ℝ→Prop} {labelExp : Bool → ℝ → ℝ → FirstSourceLabel → ℝ}
    {Presented : (Bmask : ℝ) → Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop}
    (hgate : LowBinGate labelExp 6)
    (W : ℝ→ℂ)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)(hW : ContDiff ℝ ∞ W)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)(g : GeometryAffineLowSchedule)(Mcap Lslot : ℝ)
    (hMcap1 : 101/100≤Mcap)(hMcap2 : Mcap≤2)(hrow5 : LowSelectedPaidAt M H hH g Mcap Lslot Adm labelExp Presented)
    (Cs : ℝ)(hCs : 1≤Cs)
    (ηcoarse : Character)(u₀ : O)(F₀ : NaturalRow ηcoarse u₀)(R₀ : Ideal O)(hu₀ : u₀≠0) :
    ∀(η₀ : Character)(Q : Ideal O)(hQM : Q≤M),
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → ∀hQ72 : internalQ Q η₀≤Ideal.span {(72:O)},
      ΣdegreeAll : ℕ,ΣSp : Finset (ℕ×ℕ),PLift ((0,0)∈Sp) ×
        ΣKall : ℝ,PLift (0<Kall ∧ ∀ᶠZ : ℝ in atTop,2≤Z ∧
          GeometryAffineLowSelectedSpec (α:=α) M H hH W hbeta g Mcap Lslot Cs Adm (Presented 28) Sp degreeAll Kall η₀ Q hQM hQ72
            Z) := by
  have hMcap0 : 0<Mcap := by linarith
  intro η₀ Q hQM hQ0 hQt hQ72
  let k:=actual_affine_low_complete_data (α:=α) M H hH hgate W hWs hW hbeta g Mcap Lslot hMcap2 hMcap0 hrow5 Cs hCs
    ηcoarse u₀ F₀ R₀ hu₀ η₀ Q hQM hQ0 hQt hQ72
  let degreeAll:=mainLowCompleteHeightDegree (geometryAffineLowCoarseExponent g (Fintype.card α)) (-1) g.τ g.τ_pos k.1
  have hzero : (0,0)∈k.2.1 := k.2.2.2.2.1.down.2.2
  refine ⟨degreeAll,k.2.1,PLift.up hzero,?_⟩
  let hc:=k.2.2.2.2.2
  refine ⟨hc.2.1,PLift.up ⟨hc.2.2.down.2.1,?_⟩⟩
  filter_upwards [hc.2.2.down.2.2,
      (Classical.choose_spec (geometryAffineLowBoxReceipt (Fintype.card α) g)).2,
      eventual_geometry_child_source_cap (Fintype.card α) (9/4) (9/4) (g.μ/8)
        (by norm_num) (by norm_num) (by linarith [g.μ_pos]),
      eventual_actual_geometry_main_high_source_caps (Fintype.card α) (9/4) (9/4) (g.μ/8)
        (by norm_num) (by norm_num) (by linarith [g.μ_pos]) (by linarith [g.μ_cap])]
    with Z hz hb hchild hnorm
  refine ⟨hz.1,?_⟩
  unfold GeometryAffineLowSelectedSpec
  intro hZ s p caps θ w σ freq hm R seed Rc Mrow hR hseed hRc hRcap hMrow hMrow1 hfit hAdm height mesh hw hwL hwr
    hmesh hwm hσ hheight hfreq hT hβhi hzslot haff Label _ reflected second bin t firstIndex first amp omega
    hamp0 hamp homega htarget hf₁ hinj hfirstproj rows datum χ₀ m hm₀ hml hm₂ Ψ t₀ u
  let hK:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow
  have hMrow4 : |Mrow|≤4 := by rw [abs_of_nonneg hMrow]; linarith
  have hsource4 : CenteredMomentOriginalCommonHarmonic.sourceRadius s≤Z^(4:ℝ) := caps.sourceCap.trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le (show (3:ℝ)≤4 by norm_num))
  have hvolume4 : |Real.logb Z (volume s)|≤4 := caps.volumeLog.trans (by norm_num)
  have hvolume3 : volume s≤Z^(3:ℝ) := caps.volume.trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le (show (2:ℝ)≤3 by norm_num))
  have hsourceChild (l : Label) : CenteredMomentOriginalCommonHarmonic.sourceRadius (geometryLowFirstChild reflected s R seed (Z^Mrow) Z (g.μ/64)
      hK bin t (firstIndex l))≤Z^(4:ℝ) := by
    have hh:=hchild.2 s 2 (le_refl _) caps.endpoints caps.volume
      (geometryColumnIdeal reflected s R seed (Z^Mrow) Z (g.μ/64) hK bin (firstIndex l).1.val)
      R (firstIndex l).2 (geometryColumnCharacter reflected s R seed (Z^Mrow) Z (g.μ/64) hK bin (firstIndex l).1.val)
      t (hf₁ l)
    exact hh.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith [g.μ_cap]))
  let original : rows→ geometryMainNonzeroBlocks reflected s R seed Z Mrow amp (g.μ/64) (g.μ/8) (9/4) t
      (Fintype.card α) hZ bin caps.zero₁ caps.zero₂ :=
    mainLowSelectedOriginal reflected s R seed Z Mrow amp (g.μ/64) (g.μ/8) (9/4) t (Fintype.card α)
      hZ bin caps.zero₁ caps.zero₂ firstIndex
  have hnorms (r : rows) := hnorm.2 reflected s R seed Mrow amp (g.μ/64) (g.μ/8) t hZ
    (le_refl _) caps.endpoints hseed caps.zero₁ caps.zero₂ caps.sourceCap hvolume3 bin (χ₀ r)
    (internalQ Q η₀) m (original r).val (hf₁ r.val.1)
  have hP (r : rows) : (datum r).R*(if second then (datum r).D else (datum r).C)≠0 :=
    actual_geometry_low_second_puncture reflected s R seed Z Mrow amp (g.μ/64) (g.μ/8) (9/4) t
      (Fintype.card α) hZ bin (firstIndex r.val.1) caps.zero₁ caps.zero₂ r.val.2 hR second
  have hPNc (r : rows) : ((((datum r).R*(if second then (datum r).D else (datum r).C)).absNorm:ℝ))≤Z^(Rc+8) := by
    have hcolumn : ((geometryColumnIdeal reflected s R seed (Z^Mrow) Z (g.μ/64) hK bin
        (firstIndex r.val.1).1.val).absNorm:ℝ)≤Z^(4:ℝ) := by
      cases reflected
      · exact (hnorms r).1
      · exact (hnorms r).2.1
    have hr : ((datum r).R.absNorm:ℝ)≤Z^(Rc+4) := by
      change ((R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z (g.μ/64) hK bin
        (firstIndex r.val.1).1.val).absNorm:ℝ)≤_
      rw [map_mul,Nat.cast_mul]
      calc
        _≤Z^Rc*Z^(4:ℝ) := mul_le_mul hRcap hcolumn (Nat.cast_nonneg _)
          (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
        _=Z^(Rc+4) := by rw [←Real.rpow_add (zero_lt_one.trans hZ)]
    apply affine_low_mask_cap Z Rc hZ (datum r).R _ hr
    cases second
    · exact (hnorms r).2.2.1
    · exact (hnorms r).2.2.2
  have hPN (r : rows) : ((((datum r).R*(if second then (datum r).D else (datum r).C)).absNorm:ℝ))≤Z^(28:ℝ) :=
    (hPNc r).trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith only [hRc]))
  refine ⟨hP,hPN,hPNc,?_⟩
  intro st leftR uR unitR Tz hleft hu₀ hdict _ hpres canonical firstMass childSrc
  obtain ⟨B₂,rwitness,hgood⟩:=actual_main_low_family_choices reflected s R seed Z Mrow amp (g.μ/64)
    (g.μ/8) (9/4) t (Fintype.card α) hZ bin caps.zero₁ caps.zero₂ original second
  have hOriginal:=affine_low_selected_original_mem reflected s R seed Z Mrow amp (g.μ/64) (g.μ/8) (9/4) t
    (Fintype.card α) hZ bin caps.zero₁ caps.zero₂ firstIndex
  have hU : ∀r∈rows,ActualSecondBlockIndex.IsInactive r.2 :=
    fun r hr=>actual_main_low_selected_inactive reflected s R seed Z Mrow amp (g.μ/64) (g.μ/8) (9/4) t
      (Fintype.card α) hZ bin caps.zero₁ caps.zero₂ firstIndex ⟨r,hr⟩
  have hbox : ∀r∈rows,actualSecondDyad (childSrc r.1)
      (R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z (g.μ/64) hK bin (firstIndex r.1).1.val)
      (firstIndex r.1).1.val.2.1.val
      (firstMainRadius reflected (Z^Mrow) (volume s) Z (g.μ/64) (3*amp) (g.μ/8) (first r.1))
      (firstMainFourierScale reflected (Z^Mrow) (volume s) Z (g.μ/64) (3*amp) (g.μ/8) (9/4)
        (Fintype.card α) (first r.1)) Z (g.μ/64) r.2∈geometryMainAbsoluteBox Z (Fintype.card α) 4 (g.μ/8) (9/4) := by
    intro r hr
    exact hb.2.2 reflected s R seed Mrow amp (g.μ/8) t hK (le_refl _) caps.endpoints hseed
      caps.zero₁ caps.zero₂ hsource4 hvolume4 hMrow4 hamp homega hamp0
      (by linarith [g.μ_pos]) bin (firstIndex r.1).1.val (firstIndex r.1).1.property
      (firstIndex r.1).2 (hf₁ r.1) r.2
  have hseedGates (r : rows) := actual_main_high_seed_gates reflected s R seed Z Mrow amp (g.μ/64) (g.μ/8)
    (9/4) t (Fintype.card α) hZ bin caps.zero₁ caps.zero₂ (χ₀ r) (internalQ Q η₀) m (original r).val
  have he₂ (r : rows) : Supported (if second then (datum r).D else (datum r).C) := by
    cases second
    · exact (datum r).hC
    · exact (datum r).hD
  have hdiv (r : rows) : (datum r).seed∣(if second then (datum r).D else (datum r).C) := by
    cases second
    · exact (hseedGates r).1
    · exact (hseedGates r).2
  have hn:=affine_low_profile_norm_receipt p k.2.1 hzero
  have hn₁ : ∀x,‖s.W₁ x‖≤ sourceControl k.2.1 (p.profile 0) := by
    simpa only [caps.profile₁] using hn.2.2.1
  have hn₂ : ∀x,‖s.W₂ x‖≤ sourceControl k.2.1 (p.profile 1) := by
    simpa only [caps.profile₂] using hn.2.2.2.1
  have hω0 : 0≤frequencyLoss Z 32 (g.μ/64)+g.μ/8 := add_nonneg
    (frequencyLoss_nonneg Z 32 (g.μ/64) hZ (by norm_num) (by linarith [g.μ_pos])) (by linarith [g.μ_pos])
  have hspec:=hz.2
  rw [MainLowCompleteAllHeightSpec] at hspec
  have hk₀:=hspec (Label:=Label) hZ s θ w σ freq (t+2*Real.pi*(u-(if second then -t₀ else t₀))) height mesh
    (le_refl _) caps.controls (by rw [caps.lower]) hm caps.endpoints.1 caps.b₁ caps.b₂
    hw hwL hwr hmesh hwm (fun j=>(hσ j).1) (fun j=>(hσ j).2) hheight hfreq hT hβhi
    1 Mrow (g.μ/8) (g.μ/64) le_rfl hAdm hω0 (by linarith [g.μ_pos]) (by linarith [g.μ_cap, hMcap1])
    (by linarith only [hfit]) (by simpa only [mul_one] using hzslot) (by simpa only [mul_one] using haff)
  have hk₁:=hk₀ reflected second R seed bin t firstIndex hf₁ caps.zero₁ caps.zero₂ hsourceChild hseed
    hseed.ne_zero hinj hfirstproj
  have hk₂a:=hk₁ rows hOriginal hU
  have hk₂:=hk₂a (geometryMainAbsoluteBox Z (Fintype.card α) 4 (g.μ/8) (9/4)) hb.2.1 hbox
  have hk₃:=hk₂ B₂ rwitness (fun r=>(hgood r).1) χ₀ m hm₀ hml hm₂ hP hPN (fun r=>(datum r).seed) he₂ hdiv
  have hk:=hk₃ p caps.profile₁ caps.profile₂ Ψ caps.sourceCap caps.support₁ caps.support₂ caps.poolCap caps.windows caps.plainScales
    caps.endpoints hsource4 hvolume4 hMrow4 hamp homega caps.plainScales caps.primeScales hamp0
    (by linarith [g.μ_pos]) rfl (sourceControl k.2.1 (p.profile 0)) (sourceControl k.2.1 (p.profile 1))
    hn.1 hn.2.1 hn₁ hn₂ hn.2.2.2.2 leftR uR unitR Tz hleft hu₀ hdict hpres
  have hout:=hk (by
    simp only [geometryAffineLowTarget,omega,mul_one,one_mul,mul_assoc] at htarget ⊢
    linarith only [htarget,hMrow1]) t₀ u rfl (fun _=>rfl)
  convert hout using 1
  simp only [geometryAffineLowTarget,omega,amp,div_one,mul_one,one_mul,mul_assoc,degreeAll,
    geometryAffineLowCoarseExponent]
  ring_nf

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
