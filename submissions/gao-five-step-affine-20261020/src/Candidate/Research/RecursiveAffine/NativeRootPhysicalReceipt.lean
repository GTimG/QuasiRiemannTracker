/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.NativeUniformPhysicalForest
import Candidate.Research.RecursiveAffine.NativeForestReceiptShift

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 500000
set_option maxRecDepth 4000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondEnergySplit
open CenteredMomentSectorLocalization CenteredMomentCommonAllocationSum
open CenteredMomentSecondCanonicalScalar CenteredMomentCommonPairedSource
open CenteredMomentSourceLiveColumn CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional LocalMoment CenteredMomentSecondHeightFamily
open CenteredMomentSourceMass CenteredMomentEligibleEnergy CenteredMomentChildRows
open CenteredMomentCommonHeightEnvelope CenteredMomentSecondInputCapacitySource
open CenteredMomentCommonLinearNormalization CenteredMomentWholeDivisorShell
open CenteredMomentLogDyadic Cycle153SourceReturn Cycle153LowPhysical Cycle153Reachable Cycle153JointCount

variable {alpha Current : Type} [Fintype alpha] [DecidableEq alpha] [Fintype Current] [DecidableEq Current]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M ≤ H}

variable [Cycle63.AffineLedger] in
/-- The actual residual, ray and buffer LOW operator consumes literal
one-shell root receipts and retains ONE whole actual root forest. The
native shell power shifts terminal records and their loss on both sides
of every root/child binding. All native reciprocal/Cauchy factors and raw
edge coefficients remain in their original locations. The only energy
input is the corresponding actual one-shell source estimate. -/
theorem eventual_actual_root_physical_receipt
    (N : ℕ)(U eps epsUnion : ℝ)(hU : 0 ≤ U)(heps : 0 ≤ eps)(hUnion : 0<epsUnion) :
    ∃Cu : ℝ,0<Cu ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
    ∀(C : SourceContext (α:=alpha) M H)(hbase : C.globalBase=Z)
      (Bsrc : ℝ)(boxes : ℕ→Finset (Fin 4→ℤ)),
    ∀{Label : Type}[Fintype Label](supply ap : ℝ)(second : Bool)
      (datum : Label→SecondInputDatum Current)(coefficient : Label→ℝ)(t u e : ℝ)
      (select : (r : Label)→(chi psi : RayFourExpansion.RayCharacter)→
        mainLowSourceRows second (datum r) (fun _=>True)→BufferIndex e),
    (∀r,Fintype.card (datum r).slots ≤ N) →
    (∀r i I,I∈(datum r).input.pools i→(I.absNorm:ℝ) ≤ Z^U) →
    (∀r,0 ≤ coefficient r*(datum r).K*normalizer (datum r).C (datum r).D (datum r).inactive) →
    ∀(oldBound sourceConstant : ℝ),0 ≤ oldBound → 0 ≤ sourceConstant →
    0<lowerFactor N supply ap →
    (∀r chi psi p z,z∈mainLowPaymentRows (mainLowSourceRows second (datum r) (fun _=>True))
      (select r chi psi) p→1 ≤ p.1.val) →
    (∀(chi psi : RayFourExpansion.RayCharacter)(p : BufferIndex e),1 ≤ p.1.val →
      ∀n∈selectedShells (sharedProjectors (fun r=>(datum r).block.divisors.filter Squarefree)),
      ∃receipt : NativeRootForestReceipt (hH:=hH) (C:=C) Bsrc boxes,
        (∀d z,(receipt.family.part d z).loss+
          (epsUnion+3*(((N:ℝ)+2)*U)*eps) ≤ 6/1000000000000) ∧
        (∑r,∑D∈shell (sharedProjectors (fun r=>(datum r).block.divisors.filter Squarefree)) n,
          nativeResidualCost second datum
            (fun r=>coefficient r*(datum r).K*normalizer (datum r).C (datum r).D (datum r).inactive)
            (fun _=>if second then psi⁻¹ else chi)
            (fun r=>(datum r).input.t+2*Real.pi*(u-(if second then -t else t)))
            (fun r=>mainLowPaymentRows (mainLowSourceRows second (datum r) (fun _=>True))
              (select r chi psi) p) (fun _ _=>1) r D) ≤
          (oldBound+sourceConstant*receipt.family.value)*(2*dyadicScale n)^(3*eps)) →
    ∃receipt : NativeRootForestReceipt (hH:=hH) (C:=C) Bsrc boxes,
      mainLowPhysicalCompleteCost N supply ap second datum coefficient t u select ≤
        (1/lowerFactor N supply ap)*
          ((Fintype.card RayFourExpansion.RayCharacter:ℝ)^2*
            (Fintype.card (BufferIndex e):ℝ)*
              (oldBound*(Cu*Z^(epsUnion+3*(((N:ℝ)+2)*U)*eps))+
                2*(Cu*sourceConstant)*receipt.family.value)) := by
  obtain ⟨Cu,hCu,hoperator⟩ := eventual_complete_low_shells_forest_uniform_metadata (alpha:=Current) (M:=M) (H:=H) (hH:=hH) (Depth:=SuffixDepth 4) (junction:=suffixJunction 0 4) (Base:=suffixBase 0 4) (base:=suffixDictionary 0 4) N U eps epsUnion hU heps hUnion
  refine ⟨Cu,hCu,?_⟩
  filter_upwards [hoperator] with Z hz
  refine ⟨hz.1,?_⟩
  intro C hbase Bsrc boxes Label _ supply ap second datum coefficient t u e select hN hpool hcoefficient
    oldBound sourceConstant hold hconstant hlower hpositive hlocal
  subst Z
  let shellFee:=epsUnion+3*(((N:ℝ)+2)*U)*eps
  let Trace:=fun (_chi _psi : RayFourExpansion.RayCharacter)(_p : BufferIndex e)(_n : ℤ)
      (F : RootLowFamily (hH:=hH) C)=>
    ∃receipt : NativeRootForestReceipt (hH:=hH) (C:=C) Bsrc boxes,
      receipt.family=F ∧ ∀d z,(receipt.family.part d z).loss+shellFee ≤ 6/1000000000000
  have hlocal' : ∀(chi psi : RayFourExpansion.RayCharacter)(p : BufferIndex e),1 ≤ p.1.val →
      ∀n∈selectedShells (sharedProjectors (fun r=>(datum r).block.divisors.filter Squarefree)),
      ∃F : RootLowFamily (hH:=hH) C,Trace chi psi p n F ∧
        (∑r,∑D∈shell (sharedProjectors (fun r=>(datum r).block.divisors.filter Squarefree)) n,
          nativeResidualCost second datum
            (fun r=>coefficient r*(datum r).K*normalizer (datum r).C (datum r).D (datum r).inactive)
            (fun _=>if second then psi⁻¹ else chi)
            (fun r=>(datum r).input.t+2*Real.pi*(u-(if second then -t else t)))
            (fun r=>mainLowPaymentRows (mainLowSourceRows second (datum r) (fun _=>True))
              (select r chi psi) p) (fun _ _=>1) r D) ≤
          (oldBound+sourceConstant*F.value)*(2*dyadicScale n)^(3*eps) := by
    intro chi psi p hp n hn
    obtain ⟨receipt,hloss,hbound⟩:=hlocal chi psi p hp n hn
    exact ⟨receipt.family,⟨receipt,rfl,hloss⟩,hbound⟩
  obtain ⟨F,hselected,hbound⟩:=hz.2 C.etaSeed C.Bnorm C.Tz (1:O) C.globalBase_gt_one supply ap second datum coefficient t u e select
    hN hpool hcoefficient oldBound sourceConstant hold hconstant hlower hpositive Trace hlocal'
  cases hselected with
  | inl hempty=>
    refine ⟨native_empty_root_forest_receipt Bsrc boxes,?_⟩
    simpa only [hempty,native_empty_root_forest_receipt] using hbound
  | inr htrace=>
    obtain ⟨chi,psi,p,n,Fraw,hp,hn,hraw,hshift⟩:=htrace
    obtain ⟨receipt,hfamily,hloss⟩:=hraw
    let selected:=NativeRootForestReceipt.shiftShell receipt shellFee hloss
    refine ⟨selected,?_⟩
    have hselected : selected.family=F := by
      change shiftedReturnedForest receipt.family shellFee=F
      rw [hfamily]
      exact hshift.symm
    simpa only [hselected] using hbound

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.eventual_actual_root_physical_receipt
