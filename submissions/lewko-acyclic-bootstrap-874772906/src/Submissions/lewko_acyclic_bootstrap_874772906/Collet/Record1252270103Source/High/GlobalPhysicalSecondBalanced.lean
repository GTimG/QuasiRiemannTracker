/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact balanced second-row energies, with the modified coefficient retained.
Adapted from pinned Cycle61 SecondBalanced and SecondBalancedScalar. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalSecondFamily
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.SecondBalancedScalar
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentExceptionalAmplitudePair CenteredMomentCauchy CenteredMomentHeckeColumnWindow
open CenteredMomentLogDyadic CenteredMomentSectorLocalization
open Cycle61InitialMass Cycle61Moment RayFourExpansion
local notation "O"=>HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

def modifiedRowLeftWindow {Label : Type*} (d : Label→SecondInputDatum α)
    (modifier : ∀l,Tuple (d l).slots→ℂ) (w : Label→ℂ)
    (t : ℝ) (r : SecondRow (fun l=>(d l).block)) (L : Ideal O) : ℂ :=
  secondRowLeftScalar d w r*modifiedWindowColumn (d r.1).input (modifier r.1)
    (d r.1).C (d r.1).hC (d r.1).R (d r.1).seed L ((d r.1).τ r.2.1)
    (d r.1).input.t t (dyadicScale ((d r.1).dyad 2)) logAnnulus r.2.2.2.val

def modifiedRowRightWindow {Label : Type*} (d : Label→SecondInputDatum α)
    (modifier : ∀l,Tuple (d l).slots→ℂ)
    (t : ℝ) (r : SecondRow (fun l=>(d l).block)) (L : Ideal O) : ℂ :=
  secondRowRightScalar d r*modifiedWindowColumn (d r.1).input (modifier r.1)
    (d r.1).D (d r.1).hD (d r.1).R (d r.1).seed L ((d r.1).τ r.2.2.1⁻¹)
    (d r.1).input.t (-t) (dyadicScale ((d r.1).dyad 3))
    (fun x=>star (logAnnulus x)) (-r.2.2.2.val)

theorem modified_second_balanced_row_energy {α Label : Type*}
    [Fintype α] [DecidableEq α] [Fintype Label]
    (d : Label→SecondInputDatum α) (modifier : ∀l,Tuple (d l).slots→ℂ) (w : Label→ℂ)
    (balance : SecondRow (fun l=>modifiedDatumBlock (d l) (modifier l))→ℝ) (t : ℝ) :
    secondBalancedEnergyPair (fun l=>modifiedDatumBlock (d l) (modifier l)) w balance t=
      Real.sqrt (∑r∈secondLiveRows (fun l=>modifiedDatumBlock (d l) (modifier l)),
        ∑L∈secondResidualIdeals (fun l=>modifiedDatumBlock (d l) (modifier l)) r,
          ‖(balance r:ℂ)⁻¹*modifiedRowLeftWindow d modifier w t r L‖^2)*
      Real.sqrt (∑r∈secondLiveRows (fun l=>modifiedDatumBlock (d l) (modifier l)),
        ∑L∈secondResidualIdeals (fun l=>modifiedDatumBlock (d l) (modifier l)) r,
          ‖(balance r:ℂ)*modifiedRowRightWindow d modifier t r L‖^2) := by
  have hl (q : SecondSector (fun l=>modifiedDatumBlock (d l) (modifier l))) :
      leftColumn Finset.univ (secondBalancedLeft (fun l=>modifiedDatumBlock (d l) (modifier l)) w balance q)
        logAnnulus (secondLeftLog (modifiedDatumBlock (d q.1) (modifier q.1))) t=
      (balance ⟨q.1,q.2.2⟩:ℂ)⁻¹ * leftColumn Finset.univ
        (secondJointLeft (fun l=>modifiedDatumBlock (d l) (modifier l)) w q) logAnnulus (secondLeftLog (modifiedDatumBlock (d q.1) (modifier q.1))) t := by
    simp only [leftColumn,secondBalancedLeft,Finset.mul_sum,mul_assoc]
  have hr (q : SecondSector (fun l=>modifiedDatumBlock (d l) (modifier l))) :
      rightColumn Finset.univ (secondBalancedRight (fun l=>modifiedDatumBlock (d l) (modifier l)) balance q)
        logAnnulus (secondRightLog (modifiedDatumBlock (d q.1) (modifier q.1))) t=
      (balance ⟨q.1,q.2.2⟩:ℂ) * rightColumn Finset.univ
        (secondJointRight (fun l=>modifiedDatumBlock (d l) (modifier l)) q) logAnnulus (secondRightLog (modifiedDatumBlock (d q.1) (modifier q.1))) t := by
    simp only [rightColumn,secondBalancedRight,star_mul,Complex.star_def,
      Complex.conj_ofReal,Finset.mul_sum,mul_assoc,mul_left_comm]
  unfold secondBalancedEnergyPair
  simp_rw [hl,hr,modified_second_family_left_column,modified_second_family_right_column]
  congr 1 <;> congr 1
  · rw [actual_second_rows_regroup]
    apply Finset.sum_congr rfl
    intro r hr
    exact actual_second_residual_sum (fun l=>modifiedDatumBlock (d l) (modifier l)) r
      (fun L=>‖(balance r:ℂ)⁻¹*modifiedRowLeftWindow d modifier w t r L‖^2)
  · rw [actual_second_rows_regroup]
    apply Finset.sum_congr rfl
    intro r hr
    rw [←actual_second_residual_sum]
    apply Finset.sum_congr rfl
    intro L hL
    simp only [secondRowSector,secondFamilyRightScalar,modifiedRowRightWindow,
      secondRowRightScalar,norm_mul,norm_star]
    rfl

theorem modified_second_geometric_row_energy {α Label : Type*}
    [Fintype α] [DecidableEq α] [Fintype Label]
    (d : Label→SecondInputDatum α) (modifier : ∀l,Tuple (d l).slots→ℂ) (w : Label→ℂ) (t : ℝ) :
    secondBalancedEnergyPair (fun l=>modifiedDatumBlock (d l) (modifier l)) w
      (secondGeometricBalance (fun l=>modifiedDatumBlock (d l) (modifier l)) w) t=
    Real.sqrt (∑r∈secondLiveRows (fun l=>modifiedDatumBlock (d l) (modifier l)),
      ∑L∈secondResidualIdeals (fun l=>modifiedDatumBlock (d l) (modifier l)) r,
        (‖w r.1‖*(d r.1).block.outside*volume (d r.1).input.toData)*
        ‖modifiedWindowColumn (d r.1).input (modifier r.1) (d r.1).C (d r.1).hC (d r.1).R (d r.1).seed L
          ((d r.1).τ r.2.1) (d r.1).input.t t (dyadicScale ((d r.1).dyad 2))
          logAnnulus r.2.2.2.val‖^2)*
    Real.sqrt (∑r∈secondLiveRows (fun l=>modifiedDatumBlock (d l) (modifier l)),
      ∑L∈secondResidualIdeals (fun l=>modifiedDatumBlock (d l) (modifier l)) r,
        (‖w r.1‖*(d r.1).block.outside*volume (d r.1).input.toData)*
        ‖modifiedWindowColumn (d r.1).input (modifier r.1) (d r.1).D (d r.1).hD (d r.1).R (d r.1).seed L
          ((d r.1).τ r.2.2.1⁻¹) (d r.1).input.t (-t) (dyadicScale ((d r.1).dyad 3))
          (fun x=>star (logAnnulus x)) (-r.2.2.2.val)‖^2) := by
  rw [modified_second_balanced_row_energy]
  congr 1 <;> congr 1
  · apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro L hL
    dsimp only [modifiedRowLeftWindow]
    rw [←mul_assoc,norm_mul,mul_pow]
    exact congrArg (fun x : ℝ=>x*_) (actual_second_balanced_scalar_norms d w r).1
  · apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro L hL
    dsimp only [modifiedRowRightWindow]
    rw [←mul_assoc,norm_mul,mul_pow]
    exact congrArg (fun x : ℝ=>x*_) (actual_second_balanced_scalar_norms d w r).2

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.modified_second_balanced_row_energy
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.modified_second_geometric_row_energy
