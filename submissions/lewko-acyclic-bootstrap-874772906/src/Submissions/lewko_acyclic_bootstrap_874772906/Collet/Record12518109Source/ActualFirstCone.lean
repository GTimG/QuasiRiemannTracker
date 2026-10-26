/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Uses the literal supported-ideal valuation factorization adapted from Gao,
accepted PR63, Apache-2.0; the two original orientations are retained. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Source.ActualFirstPoint
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Source.GlobalSurplus
set_option autoImplicit false
namespace QRH.Record12518109Source
noncomputable section
open scoped BigOperators
open Record12518109Admission
open OAI OAI.SevenEighths
open HeckeFamily CanonicalQuadraticSieve CenteredMomentActive CenteredMomentCanonicalFirst
open CenteredMomentCompleteCommon CompletedGauss
open Record12518109Natural
local notation "O" => HeckeFamily.O

def actualFirstVector (reflected : Bool) (C D : Ideal O) (Z : ℝ) : Fin 8→ℝ :=
  firstJoin (Valuation.actualVector reflected C D Z) (Valuation.actualVector (!reflected) C D Z)

theorem actualFirstVector_eq_weighted (reflected : Bool) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (heq : primeSupport C=primeSupport D) (Z : ℝ) :
    actualFirstVector reflected C D Z =
      firstWeighted Finset.univ
        (if reflected then rightExponent C D else leftExponent C D)
        (if reflected then leftExponent C D else rightExponent C D)
        (Valuation.primeWeight C D Z) := by
  unfold actualFirstVector
  rw [Valuation.actualVector_eq_weighted reflected C D hC hD heq Z,
    Valuation.actualVector_eq_weighted (!reflected) C D hC hD heq Z]
  cases reflected <;> exact firstJoin_weighted Finset.univ _ _ _

/-- The common cone is evaluated on the original supported ideal pair,
including both numerator and cancelled-radical orientations. -/
theorem actual_first_cones (k : Fin 15) (reflected : Bool) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (heq : primeSupport C=primeSupport D)
    (Z : ℝ) (hZ : 1 < Z) :
    let v:=actualFirstVector reflected C D Z
    globalOrdered (rawCells k) v ≤ 0 ∧ 0 ≤ globalSigma v ∧
      0 ≤ globalLocalization v ∧
      (∀ν : ℝ,ν ∈ Set.Icc (rawCells k).q (3/4) → 0 ≤ globalMixed (rawCells k) ν v) ∧
      (∀l r : ℝ,l ∈ Set.Icc (rawCells k).q (3/4) → r ∈ Set.Icc (rawCells k).q (3/4) →
        0 ≤ globalPaired (rawCells k) l r v) := by
  dsimp only
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
  refine ⟨globalOrdered_weighted k Finset.univ _ _ _ hw hi hj,
    globalSigma_nonnegative Finset.univ _ _ _ hw hi hj,
    globalLocalization_weighted Finset.univ _ _ _ hw hi hj,?_,?_⟩
  · intro ν hν
    exact globalMixed_weighted k hν Finset.univ _ _ _ hw hi hj
  · intro l r hl hr
    exact globalPaired_weighted k hl hr Finset.univ _ _ _ hw hi hj

end
end QRH.Record12518109Source
#print axioms QRH.Record12518109Source.actualFirstVector_eq_weighted
#print axioms QRH.Record12518109Source.actual_first_cones
