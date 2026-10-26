/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Complete forced-prime extraction at each literal row, with no analytic premise. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Second.RestoredChild
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.CoupledFirstAllocationSupport
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.JointForced
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentSourceRow CenteredMomentActiveSource CenteredMomentSecondHeightFamily
open CenteredMomentHeckeExpansion CenteredMomentSourceRectangle CenteredMomentLiveDomain
open CenteredMomentFirstSectors CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale
open CenteredMomentAbsoluteEnergy CenteredMomentAmplificationLiveMask Record1252270103Source Record1252270103Second
local notation "O"=>ActualEisensteinCubic.O
local notation "coefficient"=>QRH.Record1252270103Source.High.CoupledFirst.coefficient
variable {ι:Type*} [Fintype ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

lemma supported_row (S:Finset (Ideal O)) (β:Ideal O→ℂ) (τ:Character) (t:ℝ) (z:O) :
    (∑I∈supportedColumns S,β I*rowWeight τ fixedBadMask 1 z t I)=
      ∑I∈S,β I*rowWeight τ fixedBadMask 1 z t I := by
  rw [supportedColumns,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hs:Supported I
  · simp only [hs,ite_true]
  · rw [rowWeight_zero_of_not_supported τ fixedBadMask 1 z t
      (dvd_mul_right _ _) (dvd_mul_left _ _) I hs]
    simp only [mul_zero,ite_self]

lemma active_row (S:Finset (Ideal O)) (β:Ideal O→ℂ) (τ:Character) (t:ℝ) (z:O) :
    (∑I∈supportedColumns (activeSource S β),β I*rowWeight τ fixedBadMask 1 z t I)=
      ∑I∈S,β I*rowWeight τ fixedBadMask 1 z t I := by
  rw [supported_row,activeSource,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hb:β I=0 <;> simp [hb]

lemma residual_active_row (S:Finset (Ideal O)) (β:Ideal O→ℂ)
    (C:Ideal O) (hC:Supported C) (τ:Character) (t:ℝ) (z:O) :
    (∑J∈residualPool C hC.1 (supportedColumns (activeSource S β)),
      (if IsCoprime C J then β (C*J) else 0)*rowWeight τ fixedBadMask 1 z t J)=
      ∑J∈residualPool C hC.1 S,
        (if IsCoprime C J then β (C*J) else 0)*rowWeight τ fixedBadMask 1 z t J := by
  have hset:residualPool C hC.1 (supportedColumns (activeSource S β))=
      (residualPool C hC.1 S).filter (fun J=>β (C*J)≠0 ∧ Supported J) := by
    ext J
    simp only [mem_residualPool,supportedColumns,activeSource,Finset.mem_filter,
      supported_mul_iff,hC,true_and,and_assoc]
  rw [hset,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro J hJ
  by_cases hb:β (C*J)=0
  · simp only [hb,ite_self,zero_mul]
  by_cases hs:Supported J
  · rw [ite_eq_left ⟨hb,hs⟩]
  · rw [rowWeight_zero_of_not_supported τ fixedBadMask 1 z t
      (dvd_mul_right _ _) (dvd_mul_left _ _) J hs]
    simp only [mul_zero,ite_self]

lemma modified_row_columns (s:Input ι) (modifier:Tuple ι→ℂ) (R seed:Ideal O)
    (τ:Character) (t:ℝ) (z:O) :
    modifiedSourceRow s modifier R seed τ t z=
      ∑I∈finiteColumns (Fintype.piFinset s.pools),
        coefficient s modifier R seed I*rowWeight τ fixedBadMask 1 z t I := by
  unfold QRH.Record1252270103Source.High.CoupledFirst.coefficient
    QRH.Record1252270103Source.High.CoupledFirst.tupleCoefficient
  rw [finite_column_regroup]
  rfl

/-- Exact common extraction, retaining the whole pulled modifier and seed 1. -/
theorem punctured_row_children (s:Input ι) (modifier:Tuple ι→ℂ) (C R L:Ideal O)
    (hC:Supported C) (hLC:L∣C) (τ:Character) (t:ℝ) (z:O) :
    (∑J∈residualPool C hC.1 (finiteColumns (Fintype.piFinset s.pools)),
      (if IsCoprime C J then coefficient s modifier R L (C*J) else 0)*
        rowWeight τ fixedBadMask 1 z t J)=
      ∑B:actualAllocations s.pools C,frozenCoefficient B C R s.ν s.W s.P*
        modifiedSourceRow (child s C R B τ t) (pulledModifier B modifier) (R*C) 1 τ t z := by
  rw [←supported_row]
  have hc (I:Ideal O) (hI:I∈supportedColumns (residualPool C hC.1
      (finiteColumns (Fintype.piFinset s.pools)))) :
      (if IsCoprime C I then coefficient s modifier R L (C*I) else 0)=
        ∑B:actualAllocations s.pools C,frozenCoefficient B C R s.ν s.W s.P*
          finiteColumnCoefficient
            (liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1)
            (modifiedLiveProfile modifier B C R s.ν s.W s.P s.W₁ s.W₂
              s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1) I :=
    original_modified_punctured_column modifier s.pools s.pools_ne s.prime C R L I hC.1
      (Finset.mem_filter.mp hI).2.1 hLC s.ν s.W s.P s.W₁ s.W₂
      s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1
  simp_rw [Finset.sum_congr rfl (fun I hI=>congrArg (fun x:ℂ=>x*rowWeight τ fixedBadMask 1 z t I) (hc I hI))]
  simp only [Finset.sum_mul,mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro B hB
  rw [←Finset.mul_sum]
  apply congrArg (fun x:ℂ=>frozenCoefficient B C R s.ν s.W s.P*x)
  rw [High.CoupledFirst.modified_live_column_sum modifier s.pools s.pools_ne s.prime B.val
    (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1 C R hC
    (Finset.mem_filter.mp B.property).1 (Finset.mem_filter.mp B.property).2]
  have hcol := modified_child_column s modifier C R 1 B τ t
  change finiteColumnCoefficient _ (modifiedLiveProfile modifier B C R s.ν s.W s.P
    s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1)=_ at hcol
  rw [hcol,modified_child_columns,supported_row,←modified_row_columns]

/-- Exact full L-prime decomposition of the actual row. Unsupported ideals
and natural character zeros are retained through exact equalities. -/
theorem actual_forced_row (s:Input ι) (modifier:Tuple ι→ℂ) (R L:Ideal O)
    (hL:L≠0) (τ:Character) (t:ℝ) (z:O) :
    modifiedSourceRow s modifier R L τ t z=
      ∑C:forcedLabels L (forcedSource s modifier R L),rowWeight τ fixedBadMask 1 z t C*
        ∑B:actualAllocations s.pools (C:Ideal O),frozenCoefficient B C R s.ν s.W s.P*
          modifiedSourceRow (child s C R B τ t) (pulledModifier B modifier) (R*C) 1 τ t z := by
  rw [modified_row_columns,←active_row]
  have h:=forced_source_sum L (forcedSource s modifier R L) hL
    (fun I hI=>(Finset.mem_filter.mp hI).2.1) (forcedSource_seed s modifier R L)
    (coefficient s modifier R L) (rowWeight τ fixedBadMask 1 z t).toMonoidHom
  change (∑I∈forcedSource s modifier R L,coefficient s modifier R L I*
    rowWeight τ fixedBadMask 1 z t I)=_ at h
  change (∑I∈forcedSource s modifier R L,coefficient s modifier R L I*
    rowWeight τ fixedBadMask 1 z t I)=_
  rw [h]
  apply Finset.sum_congr rfl
  intro C hC
  apply congrArg (fun x:ℂ=>rowWeight τ fixedBadMask 1 z t C*x)
  have hc:=forcedSource_label_supported s modifier R L C
  have he : (∑J∈residualPool C hc.1 (forcedSource s modifier R L),
      if IsCoprime (C:Ideal O) J then coefficient s modifier R L (C*J)*
        rowWeight τ fixedBadMask 1 z t J else 0)=
      ∑J∈residualPool C hc.1 (forcedSource s modifier R L),
        (if IsCoprime (C:Ideal O) J then coefficient s modifier R L (C*J) else 0)*
          rowWeight τ fixedBadMask 1 z t J := by
    apply Finset.sum_congr rfl
    intro J hJ
    split_ifs <;> simp
  change (∑J∈residualPool C hc.1 (forcedSource s modifier R L),
    if IsCoprime (C:Ideal O) J then coefficient s modifier R L (C*J)*
      rowWeight τ fixedBadMask 1 z t J else 0)=_
  rw [he]
  change (∑J∈residualPool C hc.1 (supportedColumns (activeSource
    (finiteColumns (Fintype.piFinset s.pools)) (coefficient s modifier R L))),
    (if IsCoprime (C:Ideal O) J then coefficient s modifier R L (C*J) else 0)*
      rowWeight τ fixedBadMask 1 z t J)=_
  rw [residual_active_row _ _ C hc]
  exact punctured_row_children s modifier C R L hc (forcedSource_label_seed s modifier R L hL C) τ t z

/-- The literal double Cauchy estimate uses complete original allocation
cardinalities, before any row selection or analytic estimate. -/
theorem actual_forced_row_sq (s:Input ι) (modifier:Tuple ι→ℂ) (R L:Ideal O)
    (hL:L≠0) (τ:Character) (t:ℝ) (z:O) :
    ‖modifiedSourceRow s modifier R L τ t z‖^2≤
      ((forcedLabels L (forcedSource s modifier R L)).card:ℝ)*
        ∑C:forcedLabels L (forcedSource s modifier R L),
          ((actualAllocations s.pools (C:Ideal O)).card:ℝ)*
            ∑B:actualAllocations s.pools (C:Ideal O),‖frozenCoefficient B C R s.ν s.W s.P‖^2*
              ‖modifiedSourceRow (child s C R B τ t) (pulledModifier B modifier) (R*C) 1 τ t z‖^2 := by
  rw [actual_forced_row s modifier R L hL]
  apply (CubicEisenstein.norm_sum_sq_le_card Finset.univ _).trans
  simp only [Finset.card_univ,Fintype.card_coe]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro C hC
  rw [norm_mul,mul_pow]
  have hc:=pow_le_pow_left₀ (norm_nonneg _) (rowWeight_norm_le_one_all τ fixedBadMask 1 z t C) 2
  calc
    _≤1*‖∑B:actualAllocations s.pools (C:Ideal O),frozenCoefficient B C R s.ν s.W s.P*
        modifiedSourceRow (child s C R B τ t) (pulledModifier B modifier) (R*C) 1 τ t z‖^2 :=
      mul_le_mul_of_nonneg_right (by simpa using hc) (sq_nonneg _)
    _≤_ := by
      simpa only [one_mul,Finset.card_univ,Fintype.card_coe,norm_mul,mul_pow] using
        CubicEisenstein.norm_sum_sq_le_card Finset.univ
          (fun B:actualAllocations s.pools (C:Ideal O)=>frozenCoefficient B C R s.ν s.W s.P*
            modifiedSourceRow (child s C R B τ t) (pulledModifier B modifier) (R*C) 1 τ t z)

end
end QRH.Record1252270103Source.Admission.JointForced
#print axioms QRH.Record1252270103Source.Admission.JointForced.actual_forced_row
#print axioms QRH.Record1252270103Source.Admission.JointForced.actual_forced_row_sq
