/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Direct geometry for two surviving actual coupled columns. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103CommonGeometry.LogGeometry

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI.SevenEighths.Record1252270103CommonGeometry
noncomputable section
open scoped Classical BigOperators
open Record1252270103Source CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentSecondCanonical
open CanonicalQuadraticSieve Cycle61Moment
local notation "O" => ActualEisensteinCubic.O

theorem actual_pair_raw_geometry (Z F T : ℝ) (hZ : 1<Z)
    (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hbI : ValuationAtMostTwo I) (hbJ : ValuationAtMostTwo J)
    (hT : normLog Z J≤T) :
    let C := commonPart I J
    let D := commonPart J I
    let c := normLog Z C
    let d := normLog Z D
    let R := normLog Z (Ideal.span {activeConductor C D})
    let Lc := normLog Z (Ideal.span {firstLeftUncancelled C D})
    let δ := max (d-c) 0
    F-R-max (c-d) 0+Lc=F-δ ∧
      δ≤stratumWidth Z C D 1 2 ∧ δ≤c ∧ 2*δ≤d ∧ d≤T ∧ F-T/2≤F-δ := by
  dsimp only
  let C := commonPart I J
  let D := commonPart J I
  have hC : Supported C := commonPart_supported I J hI
  have hD : Supported D := commonPart_supported J I hJ
  have hbC := valuation_bound_of_dvd I C hI.1 (commonPart_dvd I J hI.1) hbI
  have hbD := valuation_bound_of_dvd J D hJ.1 (commonPart_dvd J I hJ.1) hbJ
  have heq : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D :=
    commonParts_equal_support I J
  have hc : commonPart C D=C := commonPart_eq_left C D hC.1 heq
  have hd : commonPart D C=D := commonPart_eq_left D C hD.1 heq.symm
  have hraw := restored_raw_exponent Z F C D hC hbC hbD
  have hdef := deficit_bounds Z hZ C D hbC hbD
  rw [hc,hd] at hraw hdef
  have hdt : normLog Z D≤T := (common_right_width_le_column Z hZ I J hJ.1).trans hT
  exact ⟨hraw,hdef.1,hdef.2.1,hdef.2.2,hdt,by linarith [hdef.2.2]⟩

/-- The public consumer has no valuation or scalar-geometry premise:
both bounds are obtained from the original coupled coefficients, their
fixed disjoint marked pools, and the squarefree ordinary projector. -/
theorem actual_coupled_pair_raw_geometry {ι : Type*} [Fintype ι]
    (A₁ A₂ D : Ideal O) (G : Ideal O→ℂ)
    (S : (ι⊕Fin 2)→Finset (Ideal O))
    (hp : ∀i,∀I∈S (Sum.inl i),Prime I)
    (hd : Pairwise (Function.onFun Disjoint (fun i=>S (Sum.inl i))))
    (R : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s I J : Ideal O)
    (hI : Supported I) (hJ : Supported J)
    (hneI : finiteColumnCoefficient (Fintype.piFinset S)
      (coupledProfile A₁ A₂ D G R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I≠0)
    (hneJ : finiteColumnCoefficient (Fintype.piFinset S)
      (coupledProfile A₁ A₂ D G R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) J≠0)
    (Z F T : ℝ) (hZ : 1<Z) (hT : normLog Z J≤T) :
    let C := commonPart I J
    let D := commonPart J I
    let c := normLog Z C
    let d := normLog Z D
    let R := normLog Z (Ideal.span {activeConductor C D})
    let Lc := normLog Z (Ideal.span {firstLeftUncancelled C D})
    let δ := max (d-c) 0
    F-R-max (c-d) 0+Lc=F-δ ∧
      δ≤stratumWidth Z C D 1 2 ∧ δ≤c ∧ 2*δ≤d ∧ d≤T ∧ F-T/2≤F-δ := by
  exact actual_pair_raw_geometry Z F T hZ I J hI hJ
    (coupled_column_valuation_bound A₁ A₂ D G S hp hd R ν Wslot P W₁ W₂
      X₁ X₂ Y₁ Y₂ B₁ B₂ s I hneI)
    (coupled_column_valuation_bound A₁ A₂ D G S hp hd R ν Wslot P W₁ W₂
      X₁ X₂ Y₁ Y₂ B₁ B₂ s J hneJ) hT

end
end OAI.SevenEighths.Record1252270103CommonGeometry

#print axioms OAI.SevenEighths.Record1252270103CommonGeometry.actual_pair_raw_geometry
#print axioms OAI.SevenEighths.Record1252270103CommonGeometry.actual_coupled_pair_raw_geometry
