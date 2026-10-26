import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.SecondBalanced

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondPhysicalBlock
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair
open CenteredMomentSectorLocalization CenteredMomentFirstScale
open CenteredMomentCommonWindowColumn CenteredMomentLogDyadic

lemma second_outside_pos (s : SecondBlockSource) : 0<s.outside := by
  have hC := norm_pos s.C s.hC.1
  have hD := norm_pos s.D s.hD.1
  have hK := s.K_pos
  have hX := dyadicScale_pos (s.dyad 2)
  have hY := dyadicScale_pos (s.dyad 3)
  have hN := normalizer_pos s.C s.D s.hC s.inactive
  unfold SecondBlockSource.outside outerScalar
  positivity

def secondGeometricBalance {Label : Type*} (s : Label→SecondBlockSource)
    (w : Label→ℂ) (r : SecondRow s) : ℝ := Real.sqrt (‖w r.1‖*(s r.1).outside)

theorem second_geometric_balance_nonzero {Label : Type*}
    (s : Label→SecondBlockSource) (w : Label→ℂ) (r : SecondRow s)
    (hw : w r.1≠0) : secondGeometricBalance s w r≠0 :=
  (Real.sqrt_pos.mpr (mul_pos (norm_pos_iff.mpr hw) (second_outside_pos _))).ne'

/-- Both balanced column scalars have the same squared norm, including
zero-weight rows. The full outside factor is therefore paid once. -/
theorem actual_second_balanced_scalar_norms {α Label : Type*}
    [Fintype α] [DecidableEq α]
    (d : Label→SecondInputDatum α) (w : Label→ℂ)
    (r : SecondRow (fun l=>(d l).block)) :
    ‖(secondGeometricBalance (fun l=>(d l).block) w r:ℂ)⁻¹*secondRowLeftScalar d w r‖^2=
      ‖w r.1‖*(d r.1).block.outside*volume (d r.1).input.toData ∧
    ‖(secondGeometricBalance (fun l=>(d l).block) w r:ℂ)*secondRowRightScalar d r‖^2=
      ‖w r.1‖*(d r.1).block.outside*volume (d r.1).input.toData := by
  have ho := second_outside_pos (d r.1).block
  have hv := volume_pos (d r.1).input.toData
  have hx : 0≤‖w r.1‖*(d r.1).block.outside := mul_nonneg (norm_nonneg _) ho.le
  have hs := Real.sq_sqrt hx
  have ht := Real.sq_sqrt hv.le
  simp only [secondGeometricBalance,secondRowLeftScalar,secondRowRightScalar,
    norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos ho,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,inv_pow,hs,ht]
  constructor
  · by_cases hw : w r.1=0
    · simp [hw]
    · have hn : 0<‖w r.1‖ := norm_pos_iff.mpr hw
      field_simp
  · trivial

/-- After balancing, the two full window sums have the same literal scalar
weight. In particular, neither side squares the original outside factor. -/
theorem actual_second_geometric_row_energy {α Label : Type*}
    [Fintype α] [DecidableEq α] [Fintype Label]
    (d : Label→SecondInputDatum α) (w : Label→ℂ) (t : ℝ) :
    secondBalancedEnergyPair (fun l=>(d l).block) w
      (secondGeometricBalance (fun l=>(d l).block) w) t=
    Real.sqrt (∑r∈secondLiveRows (fun l=>(d l).block),
      ∑L∈secondResidualIdeals (fun l=>(d l).block) r,
        (‖w r.1‖*(d r.1).block.outside*volume (d r.1).input.toData)*
        ‖windowColumn (d r.1).input (d r.1).C (d r.1).hC (d r.1).R (d r.1).seed L
          ((d r.1).τ r.2.1) (d r.1).input.t t (dyadicScale ((d r.1).dyad 2))
          logAnnulus r.2.2.2.val‖^2)*
    Real.sqrt (∑r∈secondLiveRows (fun l=>(d l).block),
      ∑L∈secondResidualIdeals (fun l=>(d l).block) r,
        (‖w r.1‖*(d r.1).block.outside*volume (d r.1).input.toData)*
        ‖windowColumn (d r.1).input (d r.1).D (d r.1).hD (d r.1).R (d r.1).seed L
          ((d r.1).τ r.2.2.1⁻¹) (d r.1).input.t (-t) (dyadicScale ((d r.1).dyad 3))
          (fun x=>star (logAnnulus x)) (-r.2.2.2.val)‖^2) := by
  rw [actual_second_balanced_row_energy]
  congr 1 <;> congr 1
  · apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro L hL
    rw [secondRowLeftWindow,←mul_assoc,norm_mul,mul_pow,
      (actual_second_balanced_scalar_norms d w r).1]
  · apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro L hL
    rw [secondRowRightWindow,←mul_assoc,norm_mul,mul_pow,
      (actual_second_balanced_scalar_norms d w r).2]

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.second_outside_pos
#print axioms OAI.SevenEighths.Cycle61InitialMass.second_geometric_balance_nonzero
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_balanced_scalar_norms

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_geometric_row_energy
