import Candidate.Cycle62.Physical.InitialMass.SecondRows
import Candidate.Cycle62.Physical.InitialMass.SecondShellWindows

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentCommonWindowColumn CenteredMomentSectorLocalization CenteredMomentLogDyadic
local notation "O" => HeckeFamily.O
local instance secondPhysicalWindowsDecidableSum {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- Actual residual projectors at a physical row, with the subtype removed
so the allocation and shell estimates apply directly. -/
def secondResidualIdeals {Label : Type*} (s : Label→SecondBlockSource)
    (r : SecondRow s) : Finset (Ideal O) :=
  (secondSquarefreeProjectors s r).image Subtype.val

theorem mem_second_residual_ideals {Label : Type*} (s : Label→SecondBlockSource)
    (r : SecondRow s) (L : Ideal O) :
    L∈secondResidualIdeals s r ↔ L∈(s r.1).divisors ∧ Squarefree L := by
  simp only [secondResidualIdeals,secondSquarefreeProjectors,Finset.mem_image,
    Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨L',hs,rfl⟩
    exact ⟨L'.property,hs⟩
  · rintro ⟨hL,hs⟩
    exact ⟨⟨L,hL⟩,hs,rfl⟩

theorem actual_second_residual_sum {Label : Type*} (s : Label→SecondBlockSource)
    (r : SecondRow s) (f : Ideal O→ℝ) :
    (∑L∈secondSquarefreeProjectors s r,f L.val)=∑L∈secondResidualIdeals s r,f L := by
  rw [secondResidualIdeals,Finset.sum_image]
  intro a ha b hb hab
  exact Subtype.ext hab

variable {α : Type*} [Fintype α] [DecidableEq α]

def secondRowLeftScalar {Label : Type*} (d : Label→SecondInputDatum α) (w : Label→ℂ)
    (r : SecondRow (fun l=>(d l).block)) : ℂ :=
  w r.1*(d r.1).block.outside*(Real.sqrt (volume (d r.1).input.toData):ℂ)
def secondRowRightScalar {Label : Type*} (d : Label→SecondInputDatum α)
    (r : SecondRow (fun l=>(d l).block)) : ℂ :=
  Real.sqrt (volume (d r.1).input.toData)

def secondRowLeftWindow {Label : Type*} (d : Label→SecondInputDatum α) (w : Label→ℂ)
    (t : ℝ) (r : SecondRow (fun l=>(d l).block)) (L : Ideal O) : ℂ :=
  secondRowLeftScalar d w r*windowColumn (d r.1).input (d r.1).C (d r.1).hC
    (d r.1).R (d r.1).seed L ((d r.1).τ r.2.1) (d r.1).input.t t
    (dyadicScale ((d r.1).dyad 2)) logAnnulus r.2.2.2.val

def secondRowRightWindow {Label : Type*} (d : Label→SecondInputDatum α)
    (t : ℝ) (r : SecondRow (fun l=>(d l).block)) (L : Ideal O) : ℂ :=
  secondRowRightScalar d r*windowColumn (d r.1).input (d r.1).D (d r.1).hD
    (d r.1).R (d r.1).seed L ((d r.1).τ r.2.2.1⁻¹) (d r.1).input.t (-t)
    (dyadicScale ((d r.1).dyad 3)) (fun x=>star (logAnnulus x)) (-r.2.2.2.val)

/-- The literal physical energy is the product of the two joint shell
energies. This equality retains every live row and every actual projector. -/
theorem actual_second_family_row_energy {Label : Type*} [Fintype Label]
    (d : Label→SecondInputDatum α) (w : Label→ℂ) (t : ℝ) :
    secondActiveEnergyPair (fun l=>(d l).block) w t=
      Real.sqrt (∑r∈secondLiveRows (fun l=>(d l).block),
        ∑L∈secondResidualIdeals (fun l=>(d l).block) r,‖secondRowLeftWindow d w t r L‖^2)*
      Real.sqrt (∑r∈secondLiveRows (fun l=>(d l).block),
        ∑L∈secondResidualIdeals (fun l=>(d l).block) r,‖secondRowRightWindow d t r L‖^2) := by
  rw [actual_second_family_energy]
  congr 1 <;> congr 1
  · rw [actual_second_rows_regroup]
    apply Finset.sum_congr rfl
    intro r hr
    exact actual_second_residual_sum (fun l=>(d l).block) r
      (fun L=>‖secondRowLeftWindow d w t r L‖^2)
  · rw [actual_second_rows_regroup]
    apply Finset.sum_congr rfl
    intro r hr
    exact actual_second_residual_sum (fun l=>(d l).block) r
      (fun L=>‖secondRowRightWindow d t r L‖^2)

end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.mem_second_residual_ideals
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_second_residual_sum
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_second_family_row_energy
