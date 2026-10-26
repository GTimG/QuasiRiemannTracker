import Candidate.Cycle63.Physical.InitialMass.GeometryMainRadius
import Candidate.Cycle63.Physical.InitialMass.SecondPhysicalWindows
import Candidate.Cycle63.Physical.HighLedgerGeometry
import Candidate.Cycle63.Physical.NonexceptionalLedger
import Candidate.Cycle63.Physical.FinalCapacity.Geometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonHarmonicMass
import Candidate.Cycle63.Arithmetic.Constants

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonRawScale CenteredMomentCommonProfile
open CenteredMomentSourceLiveColumn CenteredMomentFirstCanonicalFamily
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonical CenteredMomentSectorLocalization

/-- Supported frozen coefficients also give the lower child-volume bound
needed when the genuine common child's volume appears in a denominator. -/
theorem actual_common_inverse_volume {ι : Type*}[Fintype ι]
    (N : ℕ)(a : ℝ)(ha : 0<a)(s : Input ι)(hcard : Fintype.card ι≤N)
    (hlower : a≤ s.lower)(C R : Ideal O)(B : actualAllocations s.pools C)
    (χ : Character)(t : ℝ)(hne : frozenCoefficient B.val C R s.ν s.W s.P≠0) :
    (volume (child s C R B χ t))⁻¹≤((min 1 a)^N)⁻¹*((C.absNorm:ℝ)/volume s) := by
  have hr := rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  have hv := CenteredMomentAmplificationChildInput.volume_pos s
  have ha0 : 0< min 1 a := lt_min (by norm_num) ha
  have hp : (min 1 a)^N≤(min 1 a)^(Fintype.card ι) :=
    pow_le_pow_of_le_one ha0.le (min_le_left _ _) hcard
  have hn := (actual_reduction_norm B.val (alloc_ne s C B) C R (allocation_product s C B)
    s.ν s.W s.P s.P_pos a s.upper ha
    (fun j x hx=>⟨hlower.trans (s.slot_support j hx).1,(s.slot_support j hx).2⟩) hne).1
  have hraw : rawReduction B.val s.P≤(C.absNorm:ℝ)/(min 1 a)^N := by
    apply (le_div_iff₀ (pow_pos ha0 N)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hp hr.le]
  rw [common_volume,inv_div]
  calc
    _≤((C.absNorm:ℝ)/(min 1 a)^N)/volume s := div_le_div_of_nonneg_right hraw hv.le
    _=_ := by ring

/-- Its fixed support constant has uniformly vanishing logarithmic cost. -/
theorem eventual_common_inverse_volume (N : ℕ)(a ε : ℝ)(ha : 0<a)(hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀{ι : Type}[Fintype ι]
      (s : Input ι),Fintype.card ι≤N → a≤ s.lower →
      ∀(C R : Ideal O)(B : actualAllocations s.pools C)(χ : Character)(t : ℝ),
      frozenCoefficient B.val C R s.ν s.W s.P≠0 →
      (volume (child s C R B χ t))⁻¹≤Z^ε*((C.absNorm:ℝ)/volume s) := by
  filter_upwards [(tendsto_rpow_atTop hε).eventually (eventually_ge_atTop (((min 1 a)^N)⁻¹)),
    eventually_gt_atTop (1:ℝ)] with Z hc hZ
  refine ⟨hZ,?_⟩
  intro ι _ s hcard hlower C R B χ t hne
  exact (actual_common_inverse_volume N a ha s hcard hlower C R B χ t hne).trans
    (mul_le_mul_of_nonneg_right hc (div_nonneg (Nat.cast_nonneg _) (volume_pos s).le))

/-- The literal canonical scalar is exactly the common-generator norm
minus the inactive partition norm in the exponent ledger. -/
theorem actual_second_normalizer_power (C D : Ideal O)(hC : Supported C)
    (U : Finset (CommonIndex C D))(Z : ℝ)(hZ : 1<Z) :
    normalizer C D U=Z^(Real.logb Z (normValue (commonFrequencyGenerator C D))-
      Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)) := by
  have hg := normValue_pos _ (commonFrequencyGenerator_ne_zero C D hC)
  have hn : (0:ℝ)<(∏P∈U,P.val).absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Finset.prod_ne_zero_iff.mpr (fun P _=>(commonPrime_supported_ideal C D hC P).1)))
  rw [Real.rpow_sub (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hg,
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hn]
  exact actual_partitionNormalizer C D hC U

end
end OAI.SevenEighths.Cycle63InitialMass
