/- Final actual physical probe consumer; new A/C analytic estimates remain explicit.
Original OpenAI/Hailey Collet/DaysSky attribution retained; Apache-2.0. -/
import Candidate.Target830.Physical.Finite.Bridge
import Candidate.Cycle25.Assembly.Continuation

set_option autoImplicit false
namespace OAI.SevenEighths.Target830.Physical.FinalAssembly
noncomputable section
open scoped Classical
open Filter HeckeFamily
open OAI.SevenEighths.Target830.Physical OAI.SevenEighths.Target830.Physical.Assembly

/-- Genuine source moments for one fixed fresh geometry. This contract is
proved by the source assembly, not by the numerical row certificate. -/
def ChosenSourceInput : Prop :=
  theta<HeckeZeroSupremum.beta → ∃A : ChosenData,
    (∀P : Count.Plane,InitialTransport.weighted_AffineFineInputAt P A.F) ∧
    Source.ActualAffineInput A

/-- All finite numerator cells, original masks, profiles, dyadic bands,
principal replacement and infinite tails feed the SAME common probe. -/
theorem common_probe_of_chosen_source (hinput : ChosenSourceInput) :
    Cycle25.UniformCommonProbe theta Assembly.signalShift := by
  intro hβ
  obtain ⟨A,hfields,hAffine⟩ := hinput hβ
  obtain ⟨J,hJ,hfinite⟩ := FiniteNumerator.fixed_numerator_of_affine hβ A hAffine
  have hβ51 := (moment_parameter_gates hβ).2.2
  have hjoint := actual_joint_height A.D A.F A.P A.counts hβ51 A.kappa_exact.ge A.fine
    hfields J hJ
  let loss := (HeckeZeroSupremum.beta-theta)/2
  have hloss : 0<loss := by dsimp [loss]; linarith
  have hgap : loss<HeckeZeroSupremum.beta-theta := by dsimp [loss]; linarith
  refine ⟨loss,A.P.sigma,hloss,hgap,A.P.sigma_pos,?_⟩
  apply fixed_source_contract A.D A.F loss A.P.sigma hloss
  intro η
  obtain ⟨τ,hheight,hcount⟩ := hjoint η
  exact sourceProbe_high_of_finite_numerator_at A.D A.F A.P J τ hheight hβ.le η
    (hfinite τ hheight η hcount)

theorem beta_le_theta_of_chosen_source (hinput : ChosenSourceInput) :
    HeckeZeroSupremum.beta≤theta := by
  exact Cycle25.beta_le_of_common_probe
    (show (1/2:ℝ)≤theta by norm_num [theta])
    (show theta≤(7/8:ℝ) by norm_num [theta])
    (common_probe_of_chosen_source hinput)
end
end OAI.SevenEighths.Target830.Physical.FinalAssembly
#print axioms OAI.SevenEighths.Target830.Physical.FinalAssembly.common_probe_of_chosen_source
#print axioms OAI.SevenEighths.Target830.Physical.FinalAssembly.beta_le_theta_of_chosen_source
