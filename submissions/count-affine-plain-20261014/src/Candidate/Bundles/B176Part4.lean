/- Cycle61 successor parameter adaptation by Zhongpai Gao, with AI assistance. Nominal θ=4374299/5000000, q=67/100; exact reserves and actual source consumers are changed by scoped ownership maps. Original notices/provenance remain intact. Full source replay and independent verification are pending. -/
/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B117
import Candidate.Bundles.B133
import Candidate.Bundles.B135
import Candidate.Bundles.B150
import Candidate.Bundles.B155
import Candidate.Bundles.B161
import Candidate.Bundles.B172
import Candidate.Bundles.B173
import Candidate.Bundles.B174
import Candidate.Bundles.B175


import Candidate.Bundles.B176Part1
import Candidate.Bundles.B176Part2
import Candidate.Bundles.B176Part3

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryHighCostNormalization; sha256 a31ae78fd5d91d262e241fc74ef9463f53d07f15589048e60e23d39469225f6f -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                             

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceLiveColumn CenteredMomentCommonPairedSource
open CenteredMomentCommonLinearNormalization
open CenteredMomentSecondInputCapacitySource
local notation "O" => HeckeFamily.O

private theorem high_cost_scalar (Z amp mass K V lower norm energy : ℝ) (hZ : 0< Z) :
    (mass/V)*(K/lower)*norm*energy=
      (Z^amp/lower)*(mass*(Z^(-amp)*(K/V)*norm)*energy) := by
  have hne : Z^amp≠0 := (Real.rpow_pos_of_pos hZ amp).ne'
  rw [Real.rpow_neg hZ.le]
  simp only [div_eq_mul_inv]
  calc
    _=(Z^amp*(Z^amp)⁻¹)*(mass*V⁻¹*(K*lower⁻¹)*norm*energy) := by
      rw [mul_inv_cancel₀ hne,one_mul]
    _=_ := by ring

/-- The high estimate includes the amplification factor Z^(-amp). This exact
conversion restores Z^amp and the first-source lower factor before using it
as a selected physical cost. Both rays and the right-side sign are retained. -/
theorem actual_main_high_cost_normalization
    {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
    (N : ℕ) (a ap Z amp : ℝ) (hZ : 0< Z) (second : Bool)
    (d : Label → SecondInputDatum α) (mass : Label → ℝ) (t u : ℝ)
    (r : SecondRow (fun l=>(d l).block)) (D : Ideal O) :
    let columnEnergy : ℝ := if second then
      ‖normalizedColumn (withHeight (d r.1).input ((d r.1).τ r.2.2.1⁻¹)
        ((d r.1).input.t+2*Real.pi*(u-(-t))))
        (d r.1).D (d r.1).hD (d r.1).R (d r.1).seed D (-r.2.2.2.val)‖^2
    else
      ‖normalizedColumn (withHeight (d r.1).input ((d r.1).τ r.2.1)
        ((d r.1).input.t+2*Real.pi*(u-t)))
        (d r.1).C (d r.1).hC (d r.1).R (d r.1).seed D r.2.2.2.val‖^2
    mainNormalizedPhysicalCost N a ap second d
      (fun l=>mass l/volume (d l).input.toData) t u r D=
      (Z^amp/lowerFactor N a ap)*
        (mass r.1*(Z^(-amp)*((d r.1).K/volume (d r.1).input.toData)*
          normalizer (d r.1).C (d r.1).D (d r.1).inactive)*columnEnergy) := by
  intro columnEnergy
  exact high_cost_scalar Z amp (mass r.1) (d r.1).K (volume (d r.1).input.toData)
    (lowerFactor N a ap) (normalizer (d r.1).C (d r.1).D (d r.1).inactive) columnEnergy hZ


/-- The actual amplification factor cancels the restored high power before
summing complete physical rows. The first-source lower factor remains. -/
theorem actual_main_amplified_high_cost_rows
    {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
    (N : ℕ) (a ap Z amp : ℝ) (hZ : 0< Z) (second : Bool)
    (d : Label → SecondInputDatum α) (mass : Label → ℝ) (t u : ℝ) :
    let energy := fun (r : SecondRow (fun l=>(d l).block)) (D : Ideal O) =>
      if second then
        ‖normalizedColumn (withHeight (d r.1).input ((d r.1).τ r.2.2.1⁻¹)
          ((d r.1).input.t+2*Real.pi*(u-(-t))))
          (d r.1).D (d r.1).hD (d r.1).R (d r.1).seed D (-r.2.2.2.val)‖^2
      else
        ‖normalizedColumn (withHeight (d r.1).input ((d r.1).τ r.2.1)
          ((d r.1).input.t+2*Real.pi*(u-t)))
          (d r.1).C (d r.1).hC (d r.1).R (d r.1).seed D r.2.2.2.val‖^2
    Z^(-amp)*(∑l,mass l/volume (d l).input.toData *
      mainNormalizedBlockCost N a ap second (d l) t u)=
    (1/lowerFactor N a ap)*
      ∑r∈secondLiveRows (fun l=>(d l).block),
        ∑D∈secondResidualIdeals (fun l=>(d l).block) r,
          mass r.1*(Z^(-amp)*((d r.1).K/volume (d r.1).input.toData)*
            normalizer (d r.1).C (d r.1).D (d r.1).inactive)*energy r D := by
  intro energy
  rw [actual_main_block_cost_rows]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro D hD
  rw [actual_main_high_cost_normalization N a ap Z amp hZ]
  change Z^(-amp)*((Z^amp/lowerFactor N a ap)*_)=_
  have hne : Z^amp≠0 := (Real.rpow_pos_of_pos hZ amp).ne'
  rw [Real.rpow_neg hZ.le]
  simp only [div_eq_mul_inv,one_mul]
  dsimp only [energy]
  simp only [←mul_assoc,inv_mul_cancel₀ hne,one_mul]


end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_high_cost_normalization

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_amplified_high_cost_rows

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryHighCostNormalization -/
