/- The native root raw domain with its actual amplifier exposed as one argument.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootRawLow
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondCanonicalScalar
open CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondInputCapacitySource Cycle63Moment LocalMoment
open Cycle63Moment.LowBranch CenteredMomentEnergyBandMonotonicity CenteredMomentSecondEnergySplit
open CenteredMomentExceptionalAmplitudePair CenteredMomentFirstAmplificationChoice
open CenteredMomentEnergyFirstAnnularAdmission CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CompletedGauss Cycle63FinalNatural CenteredMomentDivisorExtraction
open CenteredMomentCommonRawScale Cycle63InitialSource CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentAllocatedRayDictionary Cycle63InitialMass
open Cycle153Reachable
variable {alpha : Type}[Fintype alpha][DecidableEq alpha]
variable (M : Ideal O)[NeZero M](H : Subgroup (O⧸M)ˣ)(hH : RayOrthogonality.globalUnits M≤H)
noncomputable local instance rootRawAtAmpLedger : Cycle63.AffineLedger:=Cycle153.Root.rootLedger

/-- This is the literal native selected RAW body. Exposing amp before
introducing the physical rows lets the actual prime-scale identity be
transported once, rather than casting already selected rows/characters. -/
def RootRawAtAmp (hbeta : 51/100≤HeckeZeroSupremum.beta)(g : GeometryAffineLowSchedule)
    (Sp : Finset (ℕ×ℕ))(degreeAll : ℕ)(Kall : ℝ)(eta0 : Character)(Q : Ideal O)
    (hQM : Q≤M)(hQ72 : internalQ Q eta0≤Ideal.span {(72:O)})
    (Z outer Kreturn : ℝ)(Receipt : Type*)(returnedValue : Receipt→ℝ)
    (hZ : 1<Z)(s : Input alpha)(p : Profiles (1/4) (9/4))
    (hz1 : s.W₁ 0=0)(hz2 : s.W₂ 0=0)(height mesh : ℝ)
    (hT : 2<Z^g.τ)(hBetaHigh : HeckeZeroSupremum.beta≤7/8)
    {Label : Type}[Fintype Label](reflected second : Bool)(bin : ℤ×(Fin 5→ℤ))(t : ℝ)
    (firstIndex : Label→GeometryLowFirstIndex reflected s 1 1 (Z^(1:ℝ)) Z (g.μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)(amp : ℝ) : Prop :=
    let first:=fun l=>geometryFirstLabel s 1 1 (Z^(1:ℝ)) Z (g.μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
    let omega:=frequencyLoss Z 32 (g.μ/64)+g.μ/8
    ∀(hamp0 : 0≤amp)(hamp : |amp|≤4)(homega : |omega|≤4)
      (htarget : -1≤geometryAffineLowTarget g (Fintype.card alpha) amp omega mesh)
      (hf1 : ∀l,frozenCoefficient (firstIndex l).2.val
        (geometryColumnIdeal reflected s 1 1 (Z^(1:ℝ)) Z (g.μ/64)
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
        1 s.ν s.W s.P≠0)
      (hinj : Function.Injective (fun l=>(first l,(firstIndex l).1.val.2.1.val)))
      (hfirstproj : ∀l,(1:Ideal O)∣firstProjectorRadical (first l).1.1 (first l).1.2 (first l).2.val),
    let rows:=mainLowSelectedNonzeroRows reflected s 1 1 Z 1 amp (g.μ/64) (g.μ/8)
      (9/4) t (Fintype.card alpha) hZ bin hz1 hz2 firstIndex
    let datum : rows→SecondInputDatum alpha:=fun r=>geometryLowSecondDatum reflected s 1 1 Z 1 amp
      (g.μ/64) (g.μ/8) (9/4) t (Fintype.card alpha) hZ bin (firstIndex r.val.1) hz1 hz2 r.val.2
    ∀(chi0 : rows→RayFourExpansion.RayCharacter)(m : O)(hm0 : m≠0)
      (hml : goodLambda∣m)(hm2 : (2:O)∣m)(Psi : 𝓢(ℝ,ℂ))(t0 u : ℝ),
    ∃hP : ∀r,(datum r).R*(if second then (datum r).D else (datum r).C)≠0,
    ∃hPN : ∀r,(((datum r).R*(if second then (datum r).D else (datum r).C)).absNorm:ℝ)≤Z^(28:ℝ),
    ∃hPNc : ∀r,(((datum r).R*(if second then (datum r).D else (datum r).C)).absNorm:ℝ)≤Z^((0:ℝ)+8),
    let st:=fun (r : rows)(ray : RayFourExpansion.RayCharacter)=>retainedState Z 28 hZ ((datum r).τ ray)
      (internalQ Q eta0) ((datum r).R*(if second then (datum r).D else (datum r).C)) (hP r) (hPN r)
      (datum r).radius (datum r).C (datum r).D (datum r).inactive
    ∀(left : Bool)(u0 : O)(units : FirstSourceLabel→O)(Tz : ℝ),
      left=!reflected→u0≠0→((∀l,IsUnit (units l))∧Real.logb Z (normValue u0)≤g.δ)→
      (∀r ray W' (hW' : (st r ray).width≤W'),True)→
    let canonical:=fun (r : rows)(chi psi : RayFourExpansion.RayCharacter)=>
      mainLowCanonicalSelector M H hH (datum r) (chi0 r) chi psi (internalQ Q eta0) hQ72
        m hm0 hml hm2 Z 28 hZ second (hP r) (hPN r) eta0
        (inf_le_left.trans hQM) inf_le_right g.e (Z^g.τ) g.e_pos hT hbeta hBetaHigh
    let firstMass:=fun l=>geometryFirstHighMass reflected s 1 1 Psi 1 Z (g.μ/64) g.δ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
    let childSrc:=fun l=>geometryLowFirstChild reflected s 1 1 (Z^(1:ℝ)) Z (g.μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t (firstIndex l)
    ∃receipt : Receipt,∃rawOldExponent : ℝ,
      rawOldExponent≤outer+geometryAffineLowTarget g (Fintype.card alpha) amp omega mesh+(1-(1:ℝ))∧
      Z^outer*mainLowPhysicalCompleteCost (Fintype.card alpha) 1 (1/4) second
        (fun r=>ordinarySecondDatum (datum r) (chi0 r) (internalQ Q eta0) m)
        (fun r=>firstMass r.val.1/volume (childSrc r.val.1)) t0 u canonical≤
      Kall*((p.control Sp)^2*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card alpha) 1 (1/4) (1/4)) bin*
        (1+|t|+height)^degreeAll*(1+|t0|)^degreeAll*(1+|u|)^degreeAll)*Z^rawOldExponent+
      Kreturn*((p.control Sp)^2*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card alpha) 1 (1/4) (1/4)) bin*
        (1+|t|+height)^degreeAll*(1+|t0|)^degreeAll*(1+|u|)^degreeAll)*returnedValue receipt
end
end OAI.SevenEighths.Cycle153RegionalLow
