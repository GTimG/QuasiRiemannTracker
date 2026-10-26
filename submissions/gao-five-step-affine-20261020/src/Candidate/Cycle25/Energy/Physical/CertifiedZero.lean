import Candidate.Cycle25.Energy.Physical.CertifiedFourier

namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter
namespace SevenEighths.Cycle25WeightedNumeratorPhysical
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CenteredMomentDetectorDictionary CenteredMomentNaturalFixedRaySource
open CenteredMomentHeckeSlots CenteredMomentInductionEnergy CenteredMomentEnergyBands
open CenteredMomentDetectorEnergyInitialState CenteredMomentEnergyState
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentRowNorm CenteredMomentRetainedEnergy QuadraticInitialBound
open CenteredMomentDetectorPlainFiberSource CenteredMomentScaleSupremum CenteredMomentSectorLocalization
set_option maxHeartbeats 800000

/-- The empty-slot terminal estimate has no capacity condition on the two
plain lengths. Here each is permitted up to U². -/
theorem finite_pair_zeroAt {D : WeightedQRH.MomentData}
    (F : OAI.SevenEighths.ProbeFinalAssembly.WeightedSourceData D) (rows : Finset FreeRow)
    (η : Character) (Φ : 𝓢(ℝ,ℂ)) (U bΦ δ ε : ℝ)
    (hU : 1 ≤ U) (hδ : 0 ≤ δ) (hδtop : δ ≤ 1)
    (hs : Function.support (Φ:ℝ→ℂ) ⊆ Set.Iic bΦ) (hp : ∀x, 0 ≤ (Φ x).re)
    (hη : (η.modulus.absNorm:ℝ) ≤ U^δ)
    (hrows : ∀u∈rows, rowNorm u ≤ U)
    (hkeep : ∀u∈rows, initialKeep η (internalQ (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal F) η) u.val)
    (hone : ∀x∈Set.Icc (0:ℝ) 1, Φ x = 1)
    (degree : ℕ) (control : Finset (ℕ×ℕ)) (C : ℝ)
    (hzero : ZeroAt (internalQ (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal F) η) (1/4) (9/4) bΦ 0 2 2
      ε U degree control C)
    (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hX₁max : X₁ ≤ U^(2:ℝ)) (hX₂max : X₂ ≤ U^(2:ℝ)) :
    (∑u∈rows, ‖polynomial ((momentData η).character (momentElement u)) false
        (p.profile 0) X₁ 0 0 *
      polynomial ((momentData η).character (momentElement u)) false (p.profile 1) X₂ 0 0‖^2)
      ≤ C*diagonalControl Φ*(p.control control)^2*U^(1+δ+ε) := by
  let state := initialState η (internalQ (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal F) η)
    Φ bΦ U δ hU hδ hs hp hη
  have hwidth : state.width ≤ 2 := by change 1+δ ≤ 2; linarith
  have hz := hzero state rfl hwidth p 0 X₁ X₂ hX₁ hX₂ hX₁max hX₂max
  have he := finite_actual_pair_le_energy rows η (internalQ (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal F) η)
    Φ U bΦ δ hU hδ hs hp hη hrows hkeep hone (p.profile 0) (p.profile 1)
    (9/4) (9/4) X₁ X₂
    (fun _ hx=>(p.support 0 hx).2) (fun _ hx=>(p.support 1 hx).2) hX₁ hX₂
    (fun _:Fin 0=>∅) (fun _:Fin 0=>0) (fun _:Fin 0=>1) (by intro i; exact zero_lt_one)
  simp only [Finset.univ_eq_empty,Finset.prod_empty,mul_one] at he
  exact he.trans (by simpa [state,initialState,NaturalState.width,NaturalState.mask,
    NaturalState.plainEnergy] using hz)

end SevenEighths.Cycle25WeightedNumeratorPhysical
end
end OAI

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 keeps the original physical family and explicit variable-kappa capacity. -/
