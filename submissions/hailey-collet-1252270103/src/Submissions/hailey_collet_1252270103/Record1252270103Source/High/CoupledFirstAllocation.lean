/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Modifier-preserving common allocation. Adapted from pinned OpenAI/Hailey Collet
LiveDomain and AmplificationLiveMask; support uses the actual modified tuple sum. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.CoupledFirstAllocationSupport
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceOriginalData
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.CoupledFirst
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentAmplificationLiveMask CenteredMomentLiveDomain CenteredMomentRemainingBox
open CenteredMomentGaussEnergy CenteredMomentSourceAllocationEnergy CenteredMomentHeckeColumnWindow
open CenteredMomentSecondHeightFamily CenteredMomentCommonPuncture CenteredMomentOriginalChildEnergy
open Record1252270103Source CenteredMomentFirstPhysicalSource
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]
local instance coupledFirstAllocationDecidable : DecidableEq (ι⊕Fin 2):=Classical.decEq _

def modifiedBeta (D:OriginalData ι) (modifier:Tuple ι→ℂ) : Ideal O→ℂ :=
  finiteColumnCoefficient (Fintype.piFinset D.S) (fun v=>modifier v*D.profile v)

def modifiedRowCoefficient (D:OriginalData ι) (modifier:Tuple ι→ℂ)
    (τ:Character) (m:O) (t T:ℝ) : supportedColumns D.columns→ℂ :=
  fun I=>(Real.sqrt T:ℂ)⁻¹*(modifiedBeta D modifier I*CenteredMomentHeckeExpansion.rowWeight τ m 1 1 t I)

def commonGauss (D:OriginalData ι)(modifier:Tuple ι→ℂ)(C:Ideal O)(hC:Supported C)(τ:Character)(t:ℝ)(L:Ideal O)(z:O):ℂ:=
  let Q:=residualPool C hC.1 D.columns
  gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    (fun I:supportedColumns Q=>(if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O)
      then modifiedBeta D modifier (C*I) else 0)*heightCoeff τ t I) z

theorem common_gauss_allocation (D:OriginalData ι)(modifier:Tuple ι→ℂ)
    (hS:∀i,∀I∈D.S i,I≠0)(hp:∀i,∀I∈D.S (Sum.inl i),Prime I)
    (C:Ideal O)(hC:Supported C)(hseed:D.s∣C)(τ:Character)(t:ℝ)(L:Ideal O)(z:O):
    commonGauss D modifier C hC τ t L z=
      ∑B:actualAllocations D.S C,frozenCoefficient B.val C D.R D.nu D.slot D.lengths*
        gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
          (sourceGenerator_supported (allocatedData D C L B).columns)
          (fun I=>(modifiedBeta (allocatedData D C L B) (pulledModifier B.val modifier) I)*heightCoeff τ t I) z:=by
  let Q:=residualPool C hC.1 D.columns
  let b:=fun B:actualAllocations D.S C=>frozenCoefficient B.val C D.R D.nu D.slot D.lengths
  let d:=fun (B:actualAllocations D.S C)(I:supportedColumns Q)=>
    finiteColumnCoefficient (liveBox D.S B.val (allocation_data D.S C B (Finset.mem_filter.mp B.property).1).1)
      (modifiedLiveProfile modifier B.val C D.R D.nu D.slot D.lengths D.W₁ D.W₂ D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂) I*
        ((if L∣(I:Ideal O) then 1 else 0)*heightCoeff τ t I)
  have he (I:supportedColumns Q):
      (if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then modifiedBeta D modifier (C*I) else 0)*heightCoeff τ t I=
        ∑B,b B*d B I:=by
    have hc:=original_modified_punctured_column modifier D.S hS hp C D.R D.s I hC.1
      (Finset.mem_filter.mp I.property).2.1 hseed D.nu D.slot D.lengths D.W₁ D.W₂
      D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂
    change (if IsCoprime C (I:Ideal O) then modifiedBeta D modifier (C*I) else 0)=_ at hc
    by_cases hl:L∣(I:Ideal O)
    · simp only [hl,and_true]
      change (if IsCoprime C (I:Ideal O) then _ else 0)*heightCoeff τ t I=_
      rw [hc,Finset.sum_mul]
      simp only [b,d,hl,ite_true,one_mul,mul_assoc]
    · simp only [hl,and_false,ite_false,zero_mul,b,d,mul_zero,Finset.sum_const_zero]
  unfold commonGauss
  change gaussPolynomial Finset.univ (sourceGenerator Q) _ _ z=_
  rw [funext he,gaussPolynomial_allocation]
  apply Finset.sum_congr rfl
  intro B hB
  apply congrArg (fun w:ℂ=>b B*w)
  have hh:=modified_live_gaussPolynomial modifier D.S hS hp B.val
    (allocation_data D.S C B (Finset.mem_filter.mp B.property).1).1 C D.R hC
    (Finset.mem_filter.mp B.property).1 (Finset.mem_filter.mp B.property).2
    D.nu D.slot D.lengths D.W₁ D.W₂ D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂
    (fun I=>(if L∣I then 1 else 0)*heightCoeff τ t I) z
  change gaussPolynomial Finset.univ (sourceGenerator Q) _ (d B) z=_ at hh
  rw [hh]
  congr 1
  funext I
  change _=finiteColumnCoefficient _ (fun v=>pulledModifier B.val modifier v*(allocatedData D C L B).profile v) I*heightCoeff τ t I
  simp only [allocated_profile,maskedLiveProfile]
  rw [modified_column_mask]
  rw [allocated_pools]
  exact (mul_assoc _ _ _).symm

theorem normalized_common_gauss_allocation (D:OriginalData ι)(modifier:Tuple ι→ℂ)
    (hS:∀i,∀I∈D.S i,I≠0)(hp:∀i,∀I∈D.S (Sum.inl i),Prime I)
    (C:Ideal O)(hC:Supported C)(hseed:D.s∣C)(τ:Character)(t T:ℝ)(L:Ideal O)(z:O):
    (Real.sqrt T:ℂ)⁻¹*commonGauss D modifier C hC τ t L z=
      ∑B:actualAllocations D.S C,frozenCoefficient B.val C D.R D.nu D.slot D.lengths*
        gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
          (sourceGenerator_supported (allocatedData D C L B).columns)
          (modifiedRowCoefficient (allocatedData D C L B) (pulledModifier B.val modifier) τ fixedBadMask t T) z:=by
  rw [common_gauss_allocation D modifier hS hp C hC hseed τ t L z,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  simp only [modifiedRowCoefficient,gaussPolynomial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [heightCoeff_eq_fixed_rowWeight τ t I (Finset.mem_filter.mp I.property).2]
  ring

end
end QRH.Record1252270103Source.High.CoupledFirst
#print axioms QRH.Record1252270103Source.High.CoupledFirst.common_gauss_allocation
#print axioms QRH.Record1252270103Source.High.CoupledFirst.normalized_common_gauss_allocation
