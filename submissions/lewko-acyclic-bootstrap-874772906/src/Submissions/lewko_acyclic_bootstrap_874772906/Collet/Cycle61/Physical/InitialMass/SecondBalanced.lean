import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.SecondPhysicalWindows

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondSectorColumns CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondCanonicalScalar CenteredMomentSmooth CenteredMomentCauchy
open CenteredMomentLogDyadic CenteredMomentHeckeColumnWindow CenteredMomentSourceRow
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair
open CenteredMomentCommonWindowColumn CenteredMomentSectorLocalization
open Cycle61Moment RayFourExpansion
local notation "O" => HeckeFamily.O

/-- Reciprocal reweighting changes the two Cauchy energies without changing
any summand of the physical kernel. The balance may depend on the live row. -/
def secondBalancedLeft {Label : Type*} (s : Label→SecondBlockSource) (w : Label→ℂ)
    (balance : SecondRow s→ℝ) (q : SecondSector s) (i : (s q.1).LeftIndex) : ℂ :=
  (balance ⟨q.1,q.2.2⟩:ℂ)⁻¹*secondJointLeft s w q i

def secondBalancedRight {Label : Type*} (s : Label→SecondBlockSource)
    (balance : SecondRow s→ℝ) (q : SecondSector s) (i : (s q.1).RightIndex) : ℂ :=
  (balance ⟨q.1,q.2.2⟩:ℂ)*secondJointRight s q i

def secondBalancedEnergyPair {Label : Type*} [Fintype Label]
    (s : Label→SecondBlockSource) (w : Label→ℂ) (balance : SecondRow s→ℝ) (t : ℝ) : ℝ :=
  Real.sqrt (∑q∈secondActiveSectors s,
    ‖leftColumn Finset.univ (secondBalancedLeft s w balance q) logAnnulus (secondLeftLog (s q.1)) t‖^2)*
  Real.sqrt (∑q∈secondActiveSectors s,
    ‖rightColumn Finset.univ (secondBalancedRight s balance q) logAnnulus (secondRightLog (s q.1)) t‖^2)

theorem actual_second_balanced_expression {Label : Type*} [Fintype Label]
    (s : Label→SecondBlockSource) (w : Label→ℂ) (balance : SecondRow s→ℝ)
    (hne : ∀r,w r.1≠0 → balance r≠0) (W : 𝓢(ℝ,ℂ)) :
    (∑l,w l*(s l).value W)=
      ∑q∈secondActiveSectors s,secondJointWeight s q*
        ∑i : (s q.1).LeftIndex,∑j : (s q.1).RightIndex,
          (secondBalancedLeft s w balance q i*star (secondBalancedRight s balance q j))*
            wholeKernel W (fun _=>logAnnulus) (s q.1).ratio (s q.1).rho
              ((s q.1).x q.2.2.2.2.val) (secondLeftLog (s q.1) i) (secondRightLog (s q.1) j) := by
  rw [actual_second_batch_active_expression]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hw : w q.1=0
  · simp only [secondBalancedLeft,secondJointLeft,hw,zero_mul,mul_zero,Finset.sum_const_zero]
  have hb : (balance ⟨q.1,q.2.2⟩:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (hne _ hw)
  simp only [secondBalancedLeft,secondBalancedRight,star_mul,Complex.star_def,Complex.conj_ofReal]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  field_simp

theorem actual_second_balanced_contraction (W : 𝓢(ℝ,ℂ)) (A J : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀{Label : Type*}[Fintype Label][DecidableEq Label]
      (s : Label→SecondBlockSource) (w : Label→ℂ) (balance : SecondRow s→ℝ),
      (∀r,w r.1≠0 → balance r≠0) → ∀r : ℝ,0<r → (∀l,(s l).ratio=r) → ∀E : ℝ,0≤E →
      (∀t : ℝ,secondBalancedEnergyPair s w balance t≤E*(1+‖t‖)^J) →
        (1+r)^A*‖∑l,w l*(s l).value W‖≤C*E := by
  obtain ⟨C,hC,hbound⟩ := whole_kernel_dependent_row_estimate W (fun _=>logAnnulus)
    (fun _=>Real.log 4) (fun _=>Real.log_nonneg (by norm_num))
    (fun _ _ hn=>CenteredMomentSecondIdealBlockBound.logAnnulus_enclosure _ hn) A J
  refine ⟨C,hC,?_⟩
  intro Label _ _ s w balance hne r hr heq E hE he
  rw [actual_second_balanced_expression s w balance hne]
  simp_rw [heq]
  exact hbound r hr (Label:=Label) (κ:=SecondSector s)
    (α:=fun l=>(s l).LeftIndex) (β:=fun l=>(s l).RightIndex)
    (secondActiveSectors s) (fun q=>q.1) (secondBalancedLeft s w balance) (secondBalancedRight s balance)
    (fun l=>secondLeftLog (s l)) (fun l=>secondRightLog (s l))
    (fun q=>(s q.1).rho) (fun q=>(s q.1).x q.2.2.2.2.val) (secondJointWeight s)
    (fun q _=>canonical_sector_signed_weight_norm _ _ (actual_second_row_weight_norm _ _))
    (fun _ _=>logAnnulus_norm _) (fun _ _=>logAnnulus_norm _) E hE he

/-- The reweighted Cauchy pair is still the pair of full joint physical
window sums, with reciprocal factors on the two sides of each row. -/
theorem actual_second_balanced_row_energy {α Label : Type*}
    [Fintype α] [DecidableEq α] [Fintype Label]
    (d : Label→SecondInputDatum α) (w : Label→ℂ)
    (balance : SecondRow (fun l=>(d l).block)→ℝ) (t : ℝ) :
    secondBalancedEnergyPair (fun l=>(d l).block) w balance t=
      Real.sqrt (∑r∈secondLiveRows (fun l=>(d l).block),
        ∑L∈secondResidualIdeals (fun l=>(d l).block) r,
          ‖(balance r:ℂ)⁻¹*secondRowLeftWindow d w t r L‖^2)*
      Real.sqrt (∑r∈secondLiveRows (fun l=>(d l).block),
        ∑L∈secondResidualIdeals (fun l=>(d l).block) r,
          ‖(balance r:ℂ)*secondRowRightWindow d t r L‖^2) := by
  have hl (q : SecondSector (fun l=>(d l).block)) :
      leftColumn Finset.univ (secondBalancedLeft (fun l=>(d l).block) w balance q)
        logAnnulus (secondLeftLog (d q.1).block) t=
      (balance ⟨q.1,q.2.2⟩:ℂ)⁻¹ * leftColumn Finset.univ
        (secondJointLeft (fun l=>(d l).block) w q) logAnnulus (secondLeftLog (d q.1).block) t := by
    simp only [leftColumn,secondBalancedLeft,Finset.mul_sum,mul_assoc]
  have hr (q : SecondSector (fun l=>(d l).block)) :
      rightColumn Finset.univ (secondBalancedRight (fun l=>(d l).block) balance q)
        logAnnulus (secondRightLog (d q.1).block) t=
      (balance ⟨q.1,q.2.2⟩:ℂ) * rightColumn Finset.univ
        (secondJointRight (fun l=>(d l).block) q) logAnnulus (secondRightLog (d q.1).block) t := by
    simp only [rightColumn,secondBalancedRight,star_mul,Complex.star_def,
      Complex.conj_ofReal,Finset.mul_sum,mul_assoc,mul_left_comm]
  unfold secondBalancedEnergyPair
  simp_rw [hl,hr,actual_second_family_left_column,actual_second_family_right_column]
  congr 1 <;> congr 1
  · rw [actual_second_rows_regroup]
    apply Finset.sum_congr rfl
    intro r hr
    exact actual_second_residual_sum (fun l=>(d l).block) r
      (fun L=>‖(balance r:ℂ)⁻¹*secondRowLeftWindow d w t r L‖^2)
  · rw [actual_second_rows_regroup]
    apply Finset.sum_congr rfl
    intro r hr
    rw [←actual_second_residual_sum]
    apply Finset.sum_congr rfl
    intro L hL
    simp only [secondRowSector,secondFamilyRightScalar,secondRowRightWindow,
      secondRowRightScalar,norm_mul,norm_star]
    rfl

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_balanced_expression
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_balanced_contraction

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_balanced_row_energy
