import Candidate.Cycle62.Physical.InitialMass.SecondCommonSelection

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion CenteredMomentLogDyadic
local notation "O" => HeckeFamily.O

/-- Row labels before choosing the residual second projector. -/
abbrev SecondRow {Label : Type*} (s : Label→SecondBlockSource) :=
  (l : Label) × RayCharacter × RayCharacter × ↥(s l).rows

def secondRowSector {Label : Type*} (s : Label→SecondBlockSource)
    (r : SecondRow s) (L : (s r.1).divisors) : SecondSector s :=
  ⟨r.1,⟨L,r.2⟩⟩

def secondLiveRows {Label : Type*} [Fintype Label]
    (s : Label→SecondBlockSource) : Finset (SecondRow s) :=
  Finset.univ.filter (fun r=>logAnnulus (s r.1).rho≠0 ∧
    logAnnulus ((s r.1).x r.2.2.2.val)≠0 ∧ (s r.1).rowWeight r.2.2.2.val≠0)

def secondSquarefreeProjectors {Label : Type*} (s : Label→SecondBlockSource)
    (r : SecondRow s) : Finset (s r.1).divisors :=
  Finset.univ.filter (fun L=>Squarefree L.val)

/-- The full active sum is regrouped by its physical row before summing
the second projectors. This is the order required by the residual-shell bound. -/
theorem actual_second_rows_regroup {Label : Type*} [Fintype Label]
    (s : Label→SecondBlockSource) (f : SecondSector s→ℝ) :
    (∑q∈secondActiveSectors s,f q)=
      ∑r∈secondLiveRows s,∑L∈secondSquarefreeProjectors s r,f (secondRowSector s r L) := by
  simp only [secondActiveSectors,secondLiveRows,secondSquarefreeProjectors,
    Finset.sum_filter,Fintype.sum_sigma,Fintype.sum_prod_type,secondRowSector]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ψ hψ
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  split_ifs with hrow
  · apply Finset.sum_congr rfl
    intro L hL
    simp only [hrow.1,hrow.2.1,hrow.2.2,ne_eq,not_false_eq_true,and_true,true_and]
  · apply Finset.sum_eq_zero
    intro L hL
    have hn : ¬(logAnnulus (s l).rho≠0 ∧ logAnnulus ((s l).x z.val)≠0 ∧
        Squarefree L.val ∧ (s l).rowWeight z.val≠0) := by
      intro h
      exact hrow ⟨h.1,h.2.1,h.2.2.2⟩
    simp only [hn,ite_false]

end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_second_rows_regroup
