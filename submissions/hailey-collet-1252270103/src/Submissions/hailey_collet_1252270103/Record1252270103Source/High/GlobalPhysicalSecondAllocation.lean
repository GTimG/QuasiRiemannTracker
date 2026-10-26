/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact common-allocation expansion of the modified second plain column.
The full allocation count and frozen coefficient are paid only after
the finite coefficient identity has been established. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalSecondWindow
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.CoupledFirstAllocationSupport
import Submissions.hailey_collet_1252270103.Record1252270103Source.Second.CoupledAllocation
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceRow
open CenteredMomentFirstSectors CenteredMomentRowNorm CenteredMomentRestrictedDomain
open CenteredMomentRestrictedSource CenteredMomentCommonWindowColumn CenteredMomentHeckeColumnWindow
open CenteredMomentAmplificationChildInput CenteredMomentExceptionalWholeWindow
open Record1252270103Source Record1252270103Second
local notation "O"=>HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance secondAllocationSumDecidable : DecidableEq (ι⊕Fin 2):=Classical.decEq _

theorem modified_live_rowPolynomial (modifier : Tuple ι→ℂ)
    (S : (ι⊕Fin 2)→Finset (Ideal O))
    (hS : ∀i,∀I∈S i,I≠0) (hp : ∀i,∀I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀i,B i≠0) (C R : Ideal O) (hC : Supported C)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (f : Ideal O→ℂ) (z : O) :
    let c:=finiteColumnCoefficient (liveBox S B hB)
      (modifiedLiveProfile modifier B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
    let Q:=residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
    let T:=finiteColumns (liveBox S B hB)
    rowPolynomial Finset.univ (sourceGenerator Q) (fun I:supportedColumns Q=>c I*f I) z=
      rowPolynomial Finset.univ (sourceGenerator T) (fun I:supportedColumns T=>c I*f I) z := by
  let c:=finiteColumnCoefficient (liveBox S B hB)
    (modifiedLiveProfile modifier B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
  let Q:=residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
  let T:=finiteColumns (liveBox S B hB)
  change rowPolynomial Finset.univ (sourceGenerator Q)
    (fun I:supportedColumns Q=>c I*f I) z=_
  refine (source_rowPolynomial Q (fun I=>c I*f I) z).trans ?_
  refine Eq.trans ?_ (source_rowPolynomial T (fun I=>c I*f I) z).symm
  simpa only [mul_assoc] using CoupledFirst.modified_live_column_sum modifier S hS hp B hB C R hC
    hlabel hprod ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ (fun I=>f I*CanonicalRowCompletion.idealRowHom z I)

def modifiedChildPlain (s : Input ι) (modifier : Tuple ι→ℂ) (C R L : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t T : ℝ) (z : O) : ℂ :=
  let s':=child s C R B τ t
  let Q:=finiteColumns (Fintype.piFinset s'.pools)
  (Real.sqrt T:ℂ)⁻¹*rowPolynomial Finset.univ (sourceGenerator Q)
    (fun I:supportedColumns Q=>CoupledFirst.coefficient s' (pulledModifier B.val modifier)
      (R*C) L I*heightCoeff τ t I) z

theorem modified_plain_allocation (s : Input ι) (modifier : Tuple ι→ℂ)
    (C : Ideal O) (hC : Supported C) (R seed L : Ideal O) (hseed : seed∣C)
    (τ : Character) (t : ℝ) (z : O) :
    modifiedPlainColumn s modifier C hC R seed L τ t z=
      ∑B:actualAllocations s.pools C,frozenCoefficient B.val C R s.ν s.W s.P*
        modifiedChildPlain s modifier C R L B τ t (volume s) z := by
  let Q:=columns s C hC
  let b:=fun B:actualAllocations s.pools C=>frozenCoefficient B.val C R s.ν s.W s.P
  let d:=fun (B:actualAllocations s.pools C)(I:supportedColumns Q)=>
    finiteColumnCoefficient (liveBox s.pools B.val (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1)
      (modifiedLiveProfile modifier B.val C R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1) I*
        ((if L∣(I:Ideal O) then 1 else 0)*heightCoeff τ t I)
  have he (I:supportedColumns Q) :
      (if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then CoupledFirst.coefficient s modifier R seed (C*I)
        else 0)*heightCoeff τ t I=∑B,b B*d B I := by
    have hc:=original_modified_punctured_column modifier s.pools s.pools_ne s.prime C R seed I hC.1
      (Finset.mem_filter.mp I.property).2.1 hseed s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1
    change (if IsCoprime C (I:Ideal O) then CoupledFirst.coefficient s modifier R seed (C*I) else 0)=_ at hc
    by_cases hl:L∣(I:Ideal O)
    · simp only [hl,and_true]
      rw [hc,Finset.sum_mul]
      simp only [b,d,hl,ite_true,one_mul,mul_assoc]
    · simp only [hl,and_false,ite_false,zero_mul,b,d,mul_zero,Finset.sum_const_zero]
  unfold modifiedPlainColumn
  simp only [modifiedWindowCoefficient,mul_assoc,rowPolynomial_factor]
  change (Real.sqrt (volume s):ℂ)⁻¹*rowPolynomial Finset.univ (sourceGenerator Q) _ z=_
  rw [funext he,rowPolynomial_allocation,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  have hh:=modified_live_rowPolynomial modifier s.pools s.pools_ne s.prime B.val
    (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1 C R hC
    (Finset.mem_filter.mp B.property).1 (Finset.mem_filter.mp B.property).2
    s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1
    (fun I=>(if L∣I then 1 else 0)*heightCoeff τ t I) z
  change rowPolynomial Finset.univ (sourceGenerator Q) (d B) z=_ at hh
  rw [hh]
  have hp (I : Ideal O) := modified_live_column_mask modifier B.val
    (liveBox s.pools B.val (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1)
    C R L I s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1
  simp_rw [←mul_assoc,←hp]
  rw [modified_child_column s modifier C R L B τ t,modified_child_columns s C R B τ t]
  dsimp only [modifiedChildPlain,b]
  ring

theorem modified_plain_allocation_bound (s : Input ι) (modifier : Tuple ι→ℂ)
    (C : Ideal O) (hC : Supported C) (R seed L : Ideal O) (hseed : seed∣C)
    (τ : Character) (t : ℝ) (z : O) :
    ‖modifiedPlainColumn s modifier C hC R seed L τ t z‖^2≤
      ((actualAllocations s.pools C).card:ℝ)*∑B:actualAllocations s.pools C,
        ‖frozenCoefficient B.val C R s.ν s.W s.P‖^2*
          ‖modifiedChildPlain s modifier C R L B τ t (volume s) z‖^2 := by
  rw [modified_plain_allocation s modifier C hC R seed L hseed τ t z]
  simpa only [Finset.card_univ,Fintype.card_coe,norm_mul,mul_pow] using
    CubicEisenstein.norm_sum_sq_le_card Finset.univ
      (fun B:actualAllocations s.pools C=>frozenCoefficient B.val C R s.ν s.W s.P*
        modifiedChildPlain s modifier C R L B τ t (volume s) z)

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.modified_live_rowPolynomial
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.modified_plain_allocation
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.modified_plain_allocation_bound
