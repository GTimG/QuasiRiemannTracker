/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.FixedCubeGaussMask

set_option autoImplicit false
namespace QRH.Cycle092.FixedCubeGauss
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSupport
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondPhysicalBlock
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentFirstSectorTransform
open CenteredMomentActiveSource CenteredMomentSourceRow CenteredMomentSecondEnergySplit
open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate CenteredMomentSectorLocalization
open QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalPair MixedPrincipalWindow MixedFirstCommonSum
open QRH.SilDensitySplit.CubeFree.Second.Concrete
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}

/-- The original fixed part after the complete seed sum and actual Gauss
expansion. The full common phase, rhoC, dyadic scales and physical
normalizers are retained; only provably zero off-diagonal blocks are removed. -/
def completedFixedGauss (r : Source ι a b) (ha : 0<a)
    (η : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ H : ℝ) : ℂ :=
  ∑ p : Labels r ha 1,rhoC p.val.1*
    (heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)*
      ∑ U : Finset (CommonIndex p.val.1 p.val.2),
      ∑ n : SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
        if p.val.1=p.val.2 then
          (outerScalar p.val.1 p.val.2 K (fun i=>(n i:ℤ)):ℂ)*
            (normalizer p.val.1 p.val.2 U:ℂ)*
            nativeGaussJoin η t (Second.Concrete.S0 r ha) (sourceCoefficient r ha 1)
              p.val.1 p.val.2
              (commonLabels_supported (Second.Concrete.S0 r ha) _ _ p.property).1
              (commonLabels_supported (Second.Concrete.S0 r ha) _ _ p.property).2
              U (frequencyRadius Tsec Z ξ)
              (partRows true η χ₀ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
              W K (fun i=>(n i:ℤ)) else 0)

/-- The exact original second fixed energy, before any norm, is this native
Gauss interface. This uses the full signed seed reconstruction. -/
theorem completed_fixed_part_eq_nativeGauss (r : Source ι a b) (ha : 0<a)
    (V : Finset Id) (hV : RawSides.CompleteSeeds r ha V)
    (η : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ H : ℝ) (hK : 0<K) :
    (∑ seed∈V,partEnergy true η χ₀ Q m t (sourceColumns r)
      (sourceCoefficient r ha seed) W K Tsec Z ξ H)=
      completedFixedGauss r ha η χ₀ Q m t W K Tsec Z ξ H := by
  rw [RawSides.completed_part_eq true r ha V hV η χ₀ Q m t W K Tsec Z ξ H]
  unfold completedFixedGauss
  apply Finset.sum_congr rfl
  intro p _
  congr 2
  apply Finset.sum_congr rfl
  intro U _
  apply Finset.sum_congr rfl
  intro n _
  have hr : ∀ z∈partRows true η χ₀ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ),z≠0 := by
    intro z hz
    exact sourceRows_nonzero _ _ U _ z (Finset.mem_filter.mp hz).1
  by_cases hd : p.val.1=p.val.2
  · rw [ite_eq_left hd]
    exact physicalBlock_eq_nativeGaussJoin η t _ _ _ _ _ _
      (commonLabels_data _ _ p.val.1 p.val.2 p.property).2.2 U _ _ hr W K hK _
  · rw [ite_eq_right hd]
    exact source_offDiagonal_physicalBlock_zero r ha p hd η t U _ _ hr W K hK _

#print axioms completed_fixed_part_eq_nativeGauss
end
end QRH.Cycle092.FixedCubeGauss
