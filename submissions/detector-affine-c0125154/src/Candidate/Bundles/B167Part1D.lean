/- Packaging rehearsal. Original notices retained; separate replay required. -/
/- B167Part1D (4 of 4): consecutive declarations of one original source section, unchanged, split for the 600-second per-module replay limit. -/
import Candidate.Bundles.B167Part1C

section
                                                            
                                                         
                                                       
                                                                   

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentSourceLiveColumn
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceMass CenteredMomentRankinRadical CenteredMomentFirstDiscardedEnergy
open CenteredMomentLogDyadic
open CenteredMomentCommonPairedSource
open CenteredMomentFirstChildProfileControl
open Cycle61FinalNatural Cycle61Moment.LowBranch
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
open Cycle61Moment
open Cycle61FinalLow
open Cycle61Moment.LowBranch Cycle61FinalNatural Cycle61FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle61FinalProfiles

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal HeckeFamily.O) [NeZero M]
variable (H : Subgroup (HeckeFamily.O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

local notation "O" => HeckeFamily.O
attribute [local instance] geometryMainLowSelectedDecidable

attribute [local irreducible] geometryLowActualChain geometryLowActualGeometry geometryLowSecondDatum
set_option maxHeartbeats 400000 in
set_option linter.defProp false in
def actual_geometry_selected_low_paid_columns {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0< A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤ B) (ha : 0< a) (ha' : a≤1/4) (hb : 1≤ b)
    (hBmask : 0≤ Bmask) (hMcap : 0< Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤ Rwidth) (hdmax : 0≤ dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0< margin)
    (hd : 0< d) (hdsupply : Mcap+Bmask+margin≤ d) (hdm : d≤ dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤ bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0< Mmin)
    (εshell : ℝ) (heshell : 0<εshell) (N : ℕ)(Cs : ℝ)(hCs : 1≤ Cs)
    (supply εv Bnorm εlabels : ℝ)(hsupply : 0< supply)(hev : 0<εv)
    (hBnorm : 0≤ Bnorm)(hel : 0<εlabels)
    (ap εmass Bmass : ℝ)(hap : 0< ap)(hemass : 0≤εmass) :=
  let hbase := actual_selected_low_paid_columns (α:=α) M H hH
    W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
    Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
    ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
    supply εv Bnorm εlabels hsupply hev hBnorm hel
  let degree:=Classical.choose hbase
  let hd:=Classical.choose_spec hbase
  let Sp:=Classical.choose hd
  let hcolumn:=Classical.choose_spec hd
  (degree,Sp,fun η₀ Q hQM hQ0 hQt hQ72=>
    let hc:=hcolumn η₀ Q hQM hQ0 hQt hQ72
    let Cg:=Classical.choose hc
    let hg:=Classical.choose_spec hc
    (Cg,PLift.up (And.intro hg.1 (Filter.Eventually.mono hg.2 (fun Z hz=>
      And.intro hz.1
      (fun (hZ : 1< Z)(s : Input α)(θ : α→ RayQuotient.Characters M H)(w σ freq : α→ℝ)
        (heightV height mesh aLow : ℝ)(i : ℕ) hcard hmass hsupply' hm hsη hsupper hsb₁ hsb₂
        hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh
        (Mrow reserve ξ : ℝ) hMmin hω hξ hMcap' hzslot haff
        {Label : Type}[Fintype Label]
        (reflected second : Bool)(R seed₀ : Ideal O)(bin : ℤ×(Fin 5→ℤ))(t : ℝ)
        (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)=>
        let first:=fun l=>geometryFirstLabel s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let cell:=Cycle61.Arithmetic.cellUpper
          (Cycle61.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
        let amp:=Mrow*Cycle61.Arithmetic.amp cell
        let childSrc:=fun l=>geometryLowFirstChild reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t (firstIndex l)
        let Rchild:=fun l=>R*geometryColumnIdeal reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let seed:=fun l=>(firstIndex l).1.val.2.1.val
        let K:=fun l=>firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve (first l)
        let Tsec:=fun l=>firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve bs
          (Fintype.card α) (first l)
        fun hf heq
          (hf₁ : ∀l,frozenCoefficient (firstIndex l).2.val
            (geometryColumnIdeal reflected s R seed₀ (Z^Mrow) Z ξ
              (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
            R s.ν s.W s.P≠0)
          (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)
          hsource (Tfirst p exponent : ℝ) hTfirst hp hs₀ hs₀0 hinj hfirstseed hfirstnorm hrad hgeom hfirstshell
          (rows : Finset ((l : Label)×ActualSecondBlockIndex (childSrc l) (Rchild l) (seed l)
            (K l) (Tsec l) Z ξ))
          (hU : ∀r∈rows,r.2.2.1∈inactiveSubsets r.2.1.val.val.1 r.2.1.val.val.2)
          (box : Finset (Fin 4→ℤ)) hbox=>
        let datum:=fun r : rows=>geometryLowSecondDatum reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2
        fun (B₂ : (r : rows)→ actualAllocations (childSrc r.val.1).pools
            (if second then (datum r).D else (datum r).C))
          (rwitness : (r : rows)→ secondLiveRows (fun _:Unit=>(datum r).block))
          (hf₂ : ∀r,frozenCoefficient (B₂ r).val
            (if second then (datum r).D else (datum r).C) (datum r).R
            (childSrc r.val.1).ν (childSrc r.val.1).W (childSrc r.val.1).P≠0)=>
        let q:=fun r : rows=>geometryLowActualChain reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2 second (B₂ r)
        let g:=fun r : rows=>geometryLowActualGeometry reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2 second (B₂ r)
          (rwitness r) (hf₁ r.val.1) (hf₂ r)
        let fields:=fun r : rows=>actual_geometry_low_paid_fields reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2 (hU r.val r.property)
          second (B₂ r) (rwitness r) (hf₁ r.val.1) (hf₂ r)
        let hrow:=hz.2 hZ s θ w σ freq heightV height mesh aLow i hcard hmass hsupply' hm hsη hsupper hsb₁ hsb₂
          hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh
          Mrow (frequencyLoss Z 32 ξ+reserve) ξ hMmin hω hξ hMcap' hzslot haff
          reflected second first hf heq R (fun l=>(firstIndex l).2)
          (fun l=>geometryColumnCharacter reflected s R seed₀ (Z^Mrow) Z ξ
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
          (fun _=>t) hf₁ Rchild seed K Tsec reserve
          (fun l=>actual_first_live_squarefree
            (geometryFirstSource s R seed₀ (Z^Mrow) Z ξ
              (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
            (fun _=>logAnnulus) (firstIndex l).1.val (firstIndex l).1.property)
          (fun _=>hw₁) (fun _=>hw₂) hsource Tfirst p exponent hTfirst hp seed₀ hs₀ hs₀0 hinj hfirstseed
          hfirstnorm hrad hgeom hfirstshell rows hU box hbox q g
          (fun r=>(fields r).1) (fun r=>(fields r).2.1) (fun r=>(fields r).2.2.1)
          (fun r=>(fields r).2.2.2.1) (fun r=>(fields r).2.2.2.2.1)
          (fun r=>(fields r).2.2.2.2.2.1) (fun r=>(fields r).2.2.2.2.2.2) rfl
        fun χ hP hPN divisorSeed hE₂ hdivisor Ds T pad hT hDs p₀ hp₁ hp₂ hallow hcaps
          zs weight hnonneg hkeep hweight (Ψ : 𝓢(ℝ,ℂ)) hsourceOriginal hplain₁ hplain₂
          (sideLower : ℝ)
          (hside : ∀l,sideLower≤ geometryHighSide reflected (Real.logb Z (volume s))
            (geometryExponents s R seed₀ (Z^Mrow) Z ξ (firstIndex l).1.val.1.val))=>
        let firstMass:=fun l=>geometryFirstHighMass reflected s R seed₀ Ψ Mrow Z ξ εmass
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let physical:=geometryHighFactor reflected (geometrySupportConstant N supply ap ap) bin
        let hphysical : 0≤ physical := by
          cases reflected <;> simp only [physical,geometryHighFactor,ite_true,ite_false]
          · exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (geometryDCompensator_pos bin).le
          · exact (inv_pos.mpr (geometryDCompensator_pos bin)).le
        hrow χ hP hPN divisorSeed hE₂ hdivisor Ds T pad hT hDs p₀ hp₁ hp₂ hallow hcaps
          zs weight hnonneg hkeep hweight firstMass physical (Bmass*εmass-sideLower) hphysical
          (fun l=>geometry_first_high_mass_nonneg reflected s R seed₀ Ψ Mrow Z ξ εmass
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
          (fun l=>actual_geometry_low_uniform_mass reflected N supply ap hsupply hap s R seed₀ Ψ
            Mrow Z ξ Bmass εmass sideLower hZ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hemass
            hcard hsupply' hs₀ hw₁ hw₂ hsourceOriginal hplain₁ hplain₂ bin (firstIndex l).1.val (hside l))))))))

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_child_low_profile_factor

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_low_fixed_profile_columns

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_selected_low_paid_columns

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_low_paid_fields

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_selected_low_paid_columns

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_low_uniform_mass

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainLowSelected -/
