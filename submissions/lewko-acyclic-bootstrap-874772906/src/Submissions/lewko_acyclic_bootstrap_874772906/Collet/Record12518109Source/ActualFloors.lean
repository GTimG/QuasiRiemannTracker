/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Source.ActualFirstCone
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Source.GlobalFloor
set_option autoImplicit false
namespace QRH.Record12518109Source
noncomputable section
open scoped BigOperators
open Record12518109Admission
open OAI OAI.SevenEighths
open HeckeFamily CanonicalQuadraticSieve CenteredMomentActive CenteredMomentCanonicalFirst
open CenteredMomentCompleteCommon CompletedGauss Record12518109Natural
local notation "O" => HeckeFamily.O

/-- The natural and complementary floor cones on the complete supported
ideal pair. The positive and zero natural-defect branches are both retained. -/
theorem actual_first_floors (k : Fin 15) (reflected : Bool) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (heq : primeSupport C=primeSupport D)
    (Z : ℝ) (hZ : 1 < Z) {ν : ℝ} (hν : ν ∈ Set.Icc (rawCells k).q (3/4)) :
    (∀p : Bool,0 ≤ globalFloor (rawCells k) p ν (actualFirstVector reflected C D Z)) ∧
      0 ≤ globalComplement (rawCells k) ν (actualFirstVector reflected C D Z) := by
  rw [actualFirstVector_eq_weighted reflected C D hC hD heq Z]
  have hw : ∀P∈(Finset.univ:Finset (CommonIndex C D)),0 ≤ Valuation.primeWeight C D Z P := by
    intro P hP
    exact Valuation.primeWeight_nonnegative C D hC Z hZ P
  have hi : ∀P∈(Finset.univ:Finset (CommonIndex C D)),
      0 < (if reflected then rightExponent C D else leftExponent C D) P := by
    intro P hP
    cases reflected
    · exact leftExponent_pos C D P
    · exact rightExponent_pos C D P
  have hj : ∀P∈(Finset.univ:Finset (CommonIndex C D)),
      0 < (if reflected then leftExponent C D else rightExponent C D) P := by
    intro P hP
    cases reflected
    · exact rightExponent_pos C D P
    · exact leftExponent_pos C D P
  exact ⟨fun p => globalFloor_weighted k p hν Finset.univ _ _ _ hw hi hj,
    globalComplement_weighted k hν Finset.univ _ _ _ hw hi hj⟩

end
end QRH.Record12518109Source
#print axioms QRH.Record12518109Source.actual_first_floors
