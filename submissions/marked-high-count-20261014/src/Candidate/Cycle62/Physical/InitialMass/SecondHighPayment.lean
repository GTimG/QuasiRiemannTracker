import Candidate.Cycle62.Physical.InitialMass.SecondScalarNormalization
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstExceptionalPrefactorActual

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstExceptionalPrefactor
open CenteredMomentAmplifiedRetainedRadius CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization Cycle62Moment Cycle62HighGeometry
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
    (hδ : Cycle62.Arithmetic.q0≤δ ∧ δ≤3/4) (hM : 0≤M)
    (hA : A≤M*Cycle62.Arithmetic.totalA b)
    (ha : a≤M*Cycle62.Arithmetic.amp b) :
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
      Z^(S-M*((-9517022237/6098638000000))+(1-ρ)*ω+ρ*ε) := by
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
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_main_radius_power

#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_high_scalar_payment
