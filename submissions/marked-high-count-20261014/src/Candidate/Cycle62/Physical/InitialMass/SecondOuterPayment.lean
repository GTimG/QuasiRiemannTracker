import Candidate.Cycle62.Physical.InitialMass.SecondBalancedScalar
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondInputCapacitySource

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondPhysicalBlock
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair
open CenteredMomentSectorLocalization CenteredMomentFirstScale
open CenteredMomentSourceBlockWindows CenteredMomentSecondInputCapacitySource
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceLiveColumn
local notation "O" => HeckeFamily.O

/-- The two witnessed second dyads jointly absorb their square-root
normalizations into the actual input volume. -/
theorem actual_second_outside_volume (s : SecondBlockSource) (W : 𝓢(ℝ,ℂ))
    (a V : ℝ)(ha : 0<a)(hV : 0<V)
    (hlower : ∀I : Ideal O,s.beta I≠0 → a*V≤(I.absNorm:ℝ))
    (hne : s.value W≠0) :
    s.outside≤s.K/(a*V)*normalizer s.C s.D s.inactive := by
  obtain ⟨hc,hd⟩ := physicalBlock_scale_lower s.character s.height s.pool s.beta
    s.C s.D s.hC s.hD s.inactive s.radius s.rows W s.K s.dyad a V ha hlower hne
  have hC := norm_pos s.C s.hC.1
  have hD := norm_pos s.D s.hD.1
  have hX := dyadicScale_pos (s.dyad 2)
  have hY := dyadicScale_pos (s.dyad 3)
  have hcl : a*V≤(s.C.absNorm:ℝ)*dyadicScale (s.dyad 2) := by
    have hh := (div_le_div_iff₀ hC ha).mp hc
    nlinarith
  have hdl : a*V≤(s.D.absNorm:ℝ)*dyadicScale (s.dyad 3) := by
    have hh := (div_le_div_iff₀ hD ha).mp hd
    nlinarith
  have hs : a*V≤Real.sqrt (s.C.absNorm:ℝ)*Real.sqrt (s.D.absNorm:ℝ)*
      Real.sqrt (dyadicScale (s.dyad 2))*Real.sqrt (dyadicScale (s.dyad 3)) := by
    have hh := mul_le_mul hcl hdl (mul_pos ha hV).le (mul_pos hC hX).le
    have hsq : (a*V)^2≤(Real.sqrt (s.C.absNorm:ℝ)*Real.sqrt (s.D.absNorm:ℝ)*
        Real.sqrt (dyadicScale (s.dyad 2))*Real.sqrt (dyadicScale (s.dyad 3)))^2 := by
      simp only [mul_pow,Real.sq_sqrt hC.le,Real.sq_sqrt hD.le,
        Real.sq_sqrt hX.le,Real.sq_sqrt hY.le]
      nlinarith
    nlinarith [show 0≤Real.sqrt (s.C.absNorm:ℝ)*Real.sqrt (s.D.absNorm:ℝ)*
      Real.sqrt (dyadicScale (s.dyad 2))*Real.sqrt (dyadicScale (s.dyad 3)) by positivity]
  unfold SecondBlockSource.outside outerScalar
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left s.K_pos.le (mul_pos ha hV) hs)
    (normalizer_pos s.C s.D s.hC s.inactive).le

/-- The lower-support constant is fixed before the actual block data. -/
theorem actual_input_second_outside {α : Type*}[Fintype α][DecidableEq α]
    (N : ℕ)(a ap : ℝ)(ha : 0<a)(hap : 0<ap)
    (d : SecondInputDatum α)(W : 𝓢(ℝ,ℂ))
    (hcard : Fintype.card α≤N)(hlower : a≤d.input.lower)
    (hW₁ : ∀x,d.input.W₁ x≠0 → ap≤x)(hW₂ : ∀x,d.input.W₂ x≠0 → ap≤x)
    (hne : d.block.value W≠0) :
    d.block.outside≤d.K/(lowerFactor N a ap*volume d.input.toData)*
      normalizer d.C d.D d.inactive := by
  apply actual_second_outside_volume d.block W (lowerFactor N a ap) (volume d.input.toData)
    (lowerFactor_pos N a ap ha hap) (volume_pos _) _ hne
  intro I hi
  have hc : Fintype.card d.slots≤Fintype.card α := by simpa using Finset.card_le_univ d.slots
  exact actual_lower_support N a ap ha hap d.input
    (hc.trans hcard) hlower hW₁ hW₂ d.R d.seed I hi

end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_second_outside_volume
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_input_second_outside
