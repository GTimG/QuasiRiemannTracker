/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual four-type first-source geometry from both retained squarefree
projectors. Marked pools may overlap. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalMain
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103CommonGeometry.SourceLabel
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment
open CenteredMomentCommonRadialData CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentSecondCanonical Record1252270103CommonGeometry
open Record1252270103Source.Collision
local notation "O"=>HeckeFamily.O
variable {ι:Type*} [Fintype ι]

theorem marked_common_valuations (s:Input ι) (A₁ A₂ D K R seed I J:Ideal O)
    (correction:Ideal O→ℂ) (hI:Supported I) (hJ:Supported J)
    (hneI:CoupledFirst.coefficient s (markedSourceModifier A₁ A₂ D K correction) R seed I≠0)
    (hneJ:CoupledFirst.coefficient s (markedSourceModifier A₁ A₂ D K correction) R seed J≠0) :
    ValuationAtMostTwo (commonPart I J) ∧ ValuationAtMostTwo (commonPart J I) := by
  exact ⟨valuation_bound_of_dvd I _ hI.1 (commonPart_dvd I J hI.1)
      (marked_input_column_valuation s A₁ A₂ D K R seed I correction hneI),
    valuation_bound_of_dvd J _ hJ.1 (commonPart_dvd J I hJ.1)
      (marked_input_column_valuation s A₁ A₂ D K R seed J correction hneJ)⟩

/-- Exact signed numerator and common deficit for either orientation. The
inactive projector stays in l; no ordinary-column nonzero test is used. -/
theorem actual_marked_first_geometry (s:Input ι) (A₁ A₂ D K R seed I J:Ideal O)
    (correction:Ideal O→ℂ) (hI:Supported I) (hJ:Supported J)
    (hneI:CoupledFirst.coefficient s (markedSourceModifier A₁ A₂ D K correction) R seed I≠0)
    (hneJ:CoupledFirst.coefficient s (markedSourceModifier A₁ A₂ D K correction) R seed J≠0)
    (left:Bool) (l:FirstSourceLabel)
    (hlC:l.1.1=commonPart I J) (hlD:l.1.2=commonPart J I)
    (Z F T:ℝ) (hZ:1<Z) (hTI:normLog Z I≤T) (hTJ:normLog Z J≤T) :
    let c:=normLog Z (if left then l.1.1 else l.1.2)
    let d:=normLog Z (if left then l.1.2 else l.1.1)
    let delta:=max (d-c) 0
    F-normLog Z (Ideal.span {activeConductor l.1.1 l.1.2})-max (c-d) 0+
      normLog Z (Ideal.span {firstSourceNumerator left l})=F-delta ∧
      delta≤c ∧ 2*delta≤d ∧ d≤T ∧ F-T/2≤F-delta := by
  have hC:Supported l.1.1:=hlC.symm ▸ commonPart_supported I J hI
  have hD:Supported l.1.2:=hlD.symm ▸ commonPart_supported J I hJ
  obtain ⟨hbC,hbD⟩:=marked_common_valuations s A₁ A₂ D K R seed I J correction hI hJ hneI hneJ
  rw [←hlC] at hbC
  rw [←hlD] at hbD
  have heq:CompletedGauss.primeSupport l.1.1=CompletedGauss.primeSupport l.1.2:=by
    rw [hlC,hlD]
    exact commonParts_equal_support I J
  have hr:=first_source_raw_exponent left l hC hD heq hbC hbD Z F
  have hd:=first_source_deficit_bounds left l hC hD heq hbC hbD Z hZ
  have hother:normLog Z (if left then l.1.2 else l.1.1)≤T:=by
    cases left
    · simpa only [Bool.false_eq_true,ite_false,hlC] using
        (common_right_width_le_column Z hZ J I hI.1).trans hTI
    · simpa only [ite_true,hlD] using
        (common_right_width_le_column Z hZ I J hJ.1).trans hTJ
  exact ⟨hr,hd.1,hd.2,hother,by dsimp only at hd ⊢;linarith [hd.2]⟩

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.marked_common_valuations
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_marked_first_geometry
