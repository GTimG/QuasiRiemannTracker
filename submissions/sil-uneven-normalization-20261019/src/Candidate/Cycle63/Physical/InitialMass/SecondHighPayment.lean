import Candidate.Cycle63.Physical.HighLedgerGeometry
import Candidate.Cycle63.Physical.NonexceptionalLedger
import Candidate.Cycle63.Physical.FinalCapacity.Geometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonHarmonicMass
import Candidate.Cycle63.Physical.InitialMass.GeometryMainRadius
import Candidate.Cycle63.Physical.InitialMass.SecondPhysicalWindows
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstExceptionalPrefactorActual

/- Original module: Candidate.Cycle63.Physical.InitialMass.SecondOrientedHigh. -/
section

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalAllowance CenteredMomentFirstCanonicalFamily
open CenteredMomentRankinRadical CenteredMomentCommonHarmonicMass
open Cycle63Moment Cycle63FinalCapacity CenteredMomentSectorLocalization
open CenteredMomentFirstPhysicalSource CenteredMomentFirstScale
open CenteredMomentAmplificationChildSourceCaps
local notation "O" => HeckeFamily.O

open Cycle63HighGeometry

/-- Literal common ideals on both sides of the second canonical transform
supply all of the final common-part inequalities in the high-bin ledger. -/
theorem actual_high_joint_excess_oriented (reflected left second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (heq₂ : primeSupport C₂=primeSupport D₂)
    (U : Finset (CommonIndex C₂ D₂)) (Z b δ M A a : ℝ)
    (hZ : 1<Z) (hb : 3401/100000≤b ∧ b≤1/25)
    (hδ : Cycle63.Arithmetic.q0≤δ ∧ δ≤3/4) (hM : 0≤M)
    (hA : A≤M*Cycle63.Arithmetic.totalA b)
    (ha : a≤M*Cycle63.Arithmetic.amp b) :
    let ρ := LocalMoment.unmarkedDensity δ
    let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    let R₀ := Real.logb Z ((cancelledRadical left l.1.1 l.1.2).absNorm:ℝ)
    let Lc := Real.logb Z ((Ideal.span {firstSourceNumerator left l}).absNorm:ℝ)
    let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
    let g₂ := Real.logb Z (normValue (CenteredMomentSecondCanonical.commonFrequencyGenerator C₂ D₂))
    let t₂ := Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)
    M*(ρ-1)+δ*A+a*(5-6*ρ)+(1-ρ)*max (c-d) 0-δ*c-(1+ρ)*R-E-
      max (3*c-5*d-R) 0/6+ρ*Lc+R₀+g₂-t₂-(1+δ)*b₂ ≤
        -M*((-3140426139/871234000000)) := by
  dsimp only
  obtain ⟨hp,hE,hR₀,hpc,hpd,hRp,hLc⟩ := actual_first_gates left l hC hD Z hZ
  have hb₂ : 0≤Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ) := by
    apply Real.logb_nonneg hZ
    cases second
    · exact norm_ge_one C₂ hC₂.1
    · exact norm_ge_one D₂ hD₂.1
  have hg₂ : Real.logb Z (normValue (CenteredMomentSecondCanonical.commonFrequencyGenerator C₂ D₂))≤
      Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ) := by
    apply Real.logb_le_logb_of_le hZ
      (normValue_pos _ (CenteredMomentSecondCanonicalFrequency.commonFrequencyGenerator_ne_zero C₂ D₂ hC₂))
    cases second
    · exact actual_common_norm_le C₂ D₂ hC₂ hD₂ heq₂
    · exact actual_common_norm_le_right C₂ D₂ hC₂ hD₂ heq₂
  cases reflected
  · exact Cycle63.Physical.high_joint_excess_bound hb hδ hM hA ha hp hE
      (div_nonneg (le_max_right _ _) (by norm_num)) hpc hpd hRp hR₀ hLc
      hb₂ (actual_unit_log_nonneg C₂ D₂ hC₂ U Z hZ) hg₂
  · exact Cycle63.Physical.high_joint_excess_bound hb hδ hM hA ha hp hE
      (div_nonneg (le_max_right _ _) (by norm_num)) hpd hpc hRp hR₀ hLc
      hb₂ (actual_unit_log_nonneg C₂ D₂ hC₂ U Z hZ) hg₂

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_high_joint_excess_oriented
end

/- Original module: Candidate.Cycle63.Physical.InitialMass.SecondScalarNormalization. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonRawScale CenteredMomentCommonProfile
open CenteredMomentSourceLiveColumn CenteredMomentFirstCanonicalFamily
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonical CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O

/-- Supported frozen coefficients also give the lower child-volume bound
needed when the genuine common child's volume appears in a denominator. -/
theorem actual_common_inverse_volume {ι : Type*}[Fintype ι]
    (N : ℕ)(a : ℝ)(ha : 0<a)(s : Input ι)(hcard : Fintype.card ι≤N)
    (hlower : a≤s.lower)(C R : Ideal O)(B : actualAllocations s.pools C)
    (χ : Character)(t : ℝ)(hne : frozenCoefficient B.val C R s.ν s.W s.P≠0) :
    (volume (child s C R B χ t))⁻¹≤((min 1 a)^N)⁻¹*((C.absNorm:ℝ)/volume s) := by
  have hr := rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  have hv := CenteredMomentAmplificationChildInput.volume_pos s
  have ha0 : 0<min 1 a := lt_min (by norm_num) ha
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
      (s : Input ι),Fintype.card ι≤N → a≤s.lower →
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
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_common_inverse_volume
#print axioms OAI.SevenEighths.Cycle63InitialMass.eventual_common_inverse_volume
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_second_normalizer_power
end

/- Original module: Candidate.Cycle63.Physical.InitialMass.SecondHighPayment. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstExceptionalPrefactor
open CenteredMomentAmplifiedRetainedRadius CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization Cycle63Moment Cycle63HighGeometry
local notation "O" => HeckeFamily.O

/-- The main radius uses the literal nominal scale, so its exponent includes
both common ideals and the inactive first projector exactly once. -/
theorem actual_main_radius_power (reflected : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : primeSupport l.1.1=primeSupport l.1.2)
    (Z M A a ξ reserve : ℝ) (hZ : 1<Z) :
    let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    firstMainRadius reflected (Z^M) (Z^A) Z ξ (3*a) reserve l=
      Z^(2*A-c-d+R+E-M+max (d-c) 0+6*a+frequencyLoss Z 32 ξ+reserve) := by
  have hz := zero_lt_one.trans hZ
  have hc : (0:ℝ)<l.1.1.absNorm := norm_pos _ hC.1
  have hd : (0:ℝ)<l.1.2.absNorm := norm_pos _ hD.1
  have hr := active_norm_pos l.1.1 l.1.2
  have he : (0:ℝ)<(firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm := by
    exact_mod_cast firstCommonSubsetNorm_pos _ _ hC l.2.val
  have hnom : nominalLog l.1.1 l.1.2
      (Ideal.span {primeSubsetGenerator (fun P : CommonIndex l.1.1 l.1.2=>P.val) l.2.val})
      (Z^M) (Z^A) Z=
      2*A-Real.logb Z (l.1.1.absNorm:ℝ)-Real.logb Z (l.1.2.absNorm:ℝ)+
        Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)+
        Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)-M := by
    rw [nominalLog,nominal_equal_support _ _ _ hC.1 hD.1 heq,
      primeSubsetGenerator,span_idealGenerator]
    change Real.logb Z (((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)*
      (Ideal.span {activeConductor l.1.1 l.1.2}).absNorm*(Z^A)^2 /
      (Z^M*(l.1.1.absNorm:ℝ)*l.1.2.absNorm))=_
    simp (disch := positivity) only [Real.logb_div,Real.logb_mul,Real.logb_pow,
      Real.logb_rpow hz hZ.ne']
    ring
  dsimp only
  unfold firstMainRadius mainCommonRadius
  rw [hnom]
  congr 1
  cases reflected <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> ring

/-- Paying the actual main radius, second canonical normalizer, and missing
radical leaves the strict high-branch reserve. Only the explicit Fourier
and frequency slack survives. -/
theorem actual_high_scalar_payment (reflected left second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : primeSupport l.1.1=primeSupport l.1.2)
    (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (heq₂ : primeSupport C₂=primeSupport D₂)
    (U : Finset (CommonIndex C₂ D₂)) (Z b δ M A a ξ reserve ε : ℝ)
    (hZ : 1<Z) (hb : 3401/100000≤b ∧ b≤1/25)
    (hδ : Cycle63.Arithmetic.q0≤δ ∧ δ≤3/4) (hM : 0≤M)
    (hA : A≤M*Cycle63.Arithmetic.totalA b)
    (ha : a≤M*Cycle63.Arithmetic.amp b) :
    let ρ := LocalMoment.unmarkedDensity δ
    let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical l.1.1 l.1.2).absNorm:ℝ)
    let Lc := Real.logb Z ((Ideal.span {firstSourceNumerator left l}).absNorm:ℝ)
    let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
    let ω := frequencyLoss Z 32 ξ+reserve
    let q := M-R-max (c-d) 0+Lc-6*a-ω+ε
    let m := Real.logb Z ((firstSourceMissing left l).absNorm:ℝ)
    let S := p+A-c+R+E+max (3*c-5*d-R) 0/6
    Z^(-a)*(firstMainRadius reflected (Z^M) (Z^A) Z ξ (3*a) reserve l/Z^(A-c))*
      (normalizer C₂ D₂ U/Z^b₂)*Z^(m+ρ*q+δ*(A-c-b₂)) ≤
      Z^(S-M*((-3140426139/871234000000))+(1-ρ)*ω+ρ*ε) := by
  dsimp only
  rw [actual_main_radius_power reflected l hC hD heq Z M A a ξ reserve hZ,
    actual_second_normalizer_power C₂ D₂ hC₂ U Z hZ,
    actual_missing_log left l hC Z]
  have hz := zero_lt_one.trans hZ
  simp only [←Real.rpow_sub hz,←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  have hh := actual_high_joint_excess_oriented reflected left second l hC hD
    C₂ D₂ hC₂ hD₂ heq₂ U Z b δ M A a hZ hb hδ hM hA ha
  dsimp only at hh
  have hm (c d : ℝ) : c-d+max (d-c) 0=max (c-d) 0 := by
    by_cases h : c≤d
    · rw [max_eq_left (sub_nonneg.mpr h),max_eq_right (sub_nonpos.mpr h)]
      ring
    · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge h)),
        max_eq_left (sub_nonneg.mpr (le_of_not_ge h))]
      ring
  have hm' := hm (Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ))
    (Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ))
  nlinarith

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_main_radius_power

#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_high_scalar_payment
end
