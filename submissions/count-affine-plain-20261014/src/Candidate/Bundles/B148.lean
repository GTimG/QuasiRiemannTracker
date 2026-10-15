/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B141
import Candidate.Bundles.B146
import Candidate.Bundles.B147
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationAllocationCost
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalFixedQSaved
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalFixedQUniform
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalBudget
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalSaved
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondDivisorSupport
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondDyadicRowSupport
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalCommonSaving
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFamily
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalKernel
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalPhysicalSaving
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalSourceFamily
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondPhysicalBlock
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceLowerSupport

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorScalarPayment; sha256 39ec2d4e8310f1c920b2b870685d1b4015ffd265ea1ed8a1f7316a07a1d7562c -/
section
                                                         
                                                     
                                           

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open ConcretePrimeRowBridge
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentRankinRadical
open CenteredMomentAmplifiedRetainedRadius CenteredMomentFirstExceptionalPrefactor
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization Cycle61Moment Cycle61FinalErrorCapacity
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationErrorEnergy
local notation "O" => HeckeFamily.O

theorem actual_error_radius_power (reflected : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : primeSupport l.1.1=primeSupport l.1.2)
    (Z M A a δ reserve : ℝ) (p : O) (k : ℕ) (hZ : 1< Z) :
    let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    firstErrorTailRadius reflected l Z M (Z^A) a δ reserve p k=
      Z^(2*A-c-d+R+E-M+max (d-c-2*errorRemoval p Z k+errorMoving p Z k) 0+
        3*a+δ+reserve) := by
  have hz := zero_lt_one.trans hZ
  have hc : (0:ℝ)< l.1.1.absNorm := norm_pos _ hC.1
  have hd : (0:ℝ)< l.1.2.absNorm := norm_pos _ hD.1
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
  unfold firstErrorTailRadius errorCommonRadius
  rw [hnom]
  congr 1
  cases reflected
  · rfl
  · simp only [ite_true]
    ring


/-- Restoring the original physical error coefficient cancels only the
paid power. The actual local error cost remains on both sides. -/
theorem actual_error_paid_weight_restore (p : O) (k : ℕ) (Z energy : ℝ) (hZ : 1< Z) :
    localErrorCost p (k-1)*energy =
      Z^(errorRemoval p Z k-errorMoving p Z k)*
        (localErrorCost p (k-1)*Z^(-errorRemoval p Z k+errorMoving p Z k)*energy) := by
  have hz := zero_lt_one.trans hZ
  calc
    _ = localErrorCost p (k-1)*energy*Z^((errorRemoval p Z k-errorMoving p Z k)+
      (-errorRemoval p Z k+errorMoving p Z k)) := by
      rw [show (errorRemoval p Z k-errorMoving p Z k)+
        (-errorRemoval p Z k+errorMoving p Z k)=0 by ring,Real.rpow_zero,mul_one]
    _ = _ := by rw [Real.rpow_add hz]; ring


/-- The literal first-error coefficient is restored from the paid columns
without dividing by a possibly vanishing local error cost. -/
theorem actual_error_coefficient_paid_restore (p : O)(k n : ℕ)
    (Z wq V energy : ℝ)(hZ : 1< Z) :
    (wq*16*((n:ℝ)+2)*localErrorCost p (k-1)/V)*energy =
      (wq*16*((n:ℝ)+2)/V)*Z^(errorRemoval p Z k-errorMoving p Z k)*
        (localErrorCost p (k-1)*Z^(-errorRemoval p Z k+errorMoving p Z k)*energy) := by
  calc
    _ = (wq*16*((n:ℝ)+2)/V)*(localErrorCost p (k-1)*energy) := by ring
    _ = _ := by rw [actual_error_paid_weight_restore p k Z energy hZ]; ring

/-- The extracted prime volume and restored paid weight cancel the two
prime-power shifts in the genuine error radius and error nominal. -/
theorem actual_error_scalar_reciprocal (reflected second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : primeSupport l.1.1=primeSupport l.1.2)
    (C₂ D₂ : Ideal O)(hC₂ : Supported C₂)(hD₂ : Supported D₂)
    (U : Finset (CommonIndex C₂ D₂))
    (Z M A a δ reserve error : ℝ)(p : O)(k : ℕ)(hZ : 1< Z) :
    let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
    let w := errorRemoval p Z k
    let wo := errorMoving p Z k
    let nominal := errorNominal M Z a (δ+reserve) w wo
      (if reflected then l.1.2 else l.1.1) (if reflected then l.1.1 else l.1.2) C₂ D₂ U
    Z^(-a)*(firstErrorTailRadius reflected l Z M (Z^A) a δ reserve p k/Z^(A-c-w))*
      (normalizer C₂ D₂ U/Z^b₂)*Z^(nominal+a+error+w-wo)=
        Z^(lowGeometryExponent reflected Z A l+error)/((if second then D₂ else C₂).absNorm:ℝ) := by
  dsimp only
  rw [actual_error_radius_power reflected l hC hD heq Z M A a δ reserve p k hZ,
    actual_second_normalizer_power C₂ D₂ hC₂ U Z hZ]
  unfold errorNominal
  have hz := zero_lt_one.trans hZ
  simp only [←Real.rpow_sub hz,←Real.rpow_add hz]
  have hm (x : ℝ) : max (-x) 0-max x 0 = -x := by
    by_cases h : 0≤ x
    · rw [max_eq_left h,max_eq_right (neg_nonpos.mpr h)]; ring
    · rw [max_eq_right (le_of_not_ge h),max_eq_left (neg_nonneg.mpr (le_of_not_ge h))]; ring
  have hh := hm (Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)-
    Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)+
      2*errorRemoval p Z k-errorMoving p Z k)
  have hn : (0:ℝ)<(if second then D₂ else C₂).absNorm := by
    cases second
    · exact norm_pos C₂ hC₂.1
    · exact norm_pos D₂ hD₂.1
  conv_rhs => rw [←Real.rpow_logb hz hZ.ne' hn,←Real.rpow_sub hz]
  congr 1
  unfold lowGeometryExponent
  rw [show -(Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)-
    Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)+
      2*errorRemoval p Z k-errorMoving p Z k)=
      Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)-
      Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)-
      2*errorRemoval p Z k+errorMoving p Z k by ring] at hh
  linarith


/-- The extraction uses its exact prime power even when the stored first
child has extra zero-coefficient entries in its coprime pools. -/
theorem eventual_actual_twice_inverse_volume (N : ℕ)(lo εv : ℝ)
    (hlo : 0< lo)(hev : 0<εv) :
    ∀ᶠZ : ℝ in atTop,1< Z ∧ ∀{ι : Type}[Fintype ι]
    (s : Input ι),Fintype.card ι≤ N → lo≤ s.lower →
    ∀(C R : Ideal O)(B : actualAllocations s.pools C)(χ : Character)(t : ℝ),
    frozenCoefficient B.val C R s.ν s.W s.P≠0 →
    ∀(p : O),p≠0 → ∀(k : ℕ),
    (∀i,∀I∈(child s C R B χ t).slots i,IsCoprime (Ideal.span {p}) I) →
    ∀(Bp : actualAllocations (child s C R B χ t).pools ((Ideal.span {p})^k))
      (υ : Character)(v : ℝ),
    (volume (twiceChild s C R B χ t (Ideal.span {p}) k Bp υ v))⁻¹ ≤
      Z^εv*((C.absNorm:ℝ)*(normValue p)^k/volume s) := by
  filter_upwards [eventual_common_inverse_volume N lo εv hlo hev] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι _ s hcard hlow C R B χ t hB p hp k hslot Bp υ v
  have hi := hz.2 s hcard hlow C R B χ t hB
  have hv := child_volume (child s C R B χ t) (Ideal.span {p})
    (Ideal.span_singleton_eq_bot.not.mpr hp) k hslot (R*C) Bp υ v
  change volume (twiceChild s C R B χ t (Ideal.span {p}) k Bp υ v)=_ at hv
  rw [hv,inv_div]
  have hh := mul_le_mul_of_nonneg_left hi (pow_nonneg (normValue_pos p hp).le k)
  simpa only [normValue,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh

theorem eventual_actual_twice_error_payment (N : ℕ) (lo εv : ℝ)
    (hlo : 0< lo) (hev : 0<εv) :
    ∀ᶠZ : ℝ in atTop,1< Z ∧ ∀{ι : Type}[Fintype ι]
    (s : Input ι),Fintype.card ι≤ N → lo≤ s.lower →
    ∀(reflected second : Bool) (l : FirstSourceLabel)
    (_hC : Supported l.1.1) (_hD : Supported l.1.2),
    primeSupport l.1.1=primeSupport l.1.2 →
    ∀(Rfirst : Ideal O)(B : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
    (χ : Character)(t : ℝ),
    frozenCoefficient B.val (if reflected then l.1.2 else l.1.1) Rfirst s.ν s.W s.P≠0 →
    ∀(p : O),p≠0 → ∀(k : ℕ),
    (∀i,∀I∈(child s (if reflected then l.1.2 else l.1.1) Rfirst B χ t).slots i,
      IsCoprime (Ideal.span {p}) I) →
    ∀(Bp : actualAllocations (child s (if reflected then l.1.2 else l.1.1)
      Rfirst B χ t).pools ((Ideal.span {p})^k))(υ : Character)(v : ℝ),
    ∀(C₂ D₂ : Ideal O)(_hC₂ : Supported C₂)(_hD₂ : Supported D₂)
      (U : Finset (CommonIndex C₂ D₂))(M a δ reserve error : ℝ),
    let A := Real.logb Z (volume s)
    let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
    let nominal := errorNominal M Z a (δ+reserve) (errorRemoval p Z k) (errorMoving p Z k)
      (if reflected then l.1.2 else l.1.1) (if reflected then l.1.1 else l.1.2) C₂ D₂ U
    Z^(-a)*(firstErrorTailRadius reflected l Z M (volume s) a δ reserve p k/volume (twiceChild s
      (if reflected then l.1.2 else l.1.1) Rfirst B χ t (Ideal.span {p}) k Bp υ v))*
      (normalizer C₂ D₂ U/Z^b₂)*Z^(nominal+a+error+errorRemoval p Z k-errorMoving p Z k) ≤
      Z^(lowGeometryExponent reflected Z A l+error+εv)/((if second then D₂ else C₂).absNorm:ℝ) := by
  filter_upwards [eventual_actual_twice_inverse_volume N lo εv hlo hev] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι _ s hcard hlow reflected second l hC hD heq Rfirst B χ t hB p hp k hslot Bp υ v C₂ D₂ hC₂ hD₂ U M a δ reserve error
  let A := Real.logb Z (volume s)
  let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
  have hZ := zero_lt_one.trans hz.1
  have hc : (0:ℝ)<(if reflected then l.1.2 else l.1.1).absNorm := by
    cases reflected
    · exact norm_pos _ hC.1
    · exact norm_pos _ hD.1
  have hV : Z^A=volume s := Real.rpow_logb hZ hz.1.ne' (volume_pos s)
  have hratio : ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)*(normValue p)^k/volume s=
      (Z^(A-c-errorRemoval p Z k))⁻¹ := by
    rw [Real.rpow_sub hZ,Real.rpow_sub hZ,hV,Real.rpow_logb hZ hz.1.ne' hc,
      errorRemoval_power p hp Z hz.1 k,inv_div]
    rw [div_div_eq_mul_div]
    ring
  have hi := hz.2 s hcard hlow _ Rfirst B χ t hB p hp k hslot Bp υ v
  rw [hratio] at hi
  have hmain : firstErrorTailRadius reflected l Z M (volume s) a δ reserve p k /
      volume (twiceChild s (if reflected then l.1.2 else l.1.1) Rfirst B χ t (Ideal.span {p}) k Bp υ v) ≤
      Z^εv*(firstErrorTailRadius reflected l Z M (volume s) a δ reserve p k/Z^(A-c-errorRemoval p Z k)) := by
    have hh := mul_le_mul_of_nonneg_left hi
      (show 0≤ firstErrorTailRadius reflected l Z M (volume s) a δ reserve p k by
        unfold firstErrorTailRadius errorCommonRadius; positivity)
    simpa only [div_eq_mul_inv,mul_left_comm] using hh
  have hp := actual_error_scalar_reciprocal reflected second l hC hD heq C₂ D₂ hC₂ hD₂ U
    Z M A a δ reserve error p k hz.1
  dsimp only at hp ⊢
  rw [hV] at hp
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmain (Real.rpow_pos_of_pos hZ (-a)).le)
      (div_nonneg (normalizer_pos C₂ D₂ hC₂ U).le (Real.rpow_nonneg hZ.le (Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)))))
    (Real.rpow_nonneg hZ.le (errorNominal M Z a (δ+reserve) (errorRemoval p Z k) (errorMoving p Z k)
      (if reflected then l.1.2 else l.1.1) (if reflected then l.1.1 else l.1.2) C₂ D₂ U+a+error+errorRemoval p Z k-errorMoving p Z k))
  apply hh.trans_eq
  rw [show Z^εv*(firstErrorTailRadius reflected l Z M (volume s) a δ reserve p k/Z^(A-c-errorRemoval p Z k))=
    (firstErrorTailRadius reflected l Z M (volume s) a δ reserve p k/Z^(A-c-errorRemoval p Z k))*Z^εv by ring]
  calc
    _=Z^εv*(Z^(-a)*(firstErrorTailRadius reflected l Z M (volume s) a δ reserve p k/Z^(A-c-errorRemoval p Z k))*
      (normalizer C₂ D₂ U/Z^(Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)))*
      Z^(errorNominal M Z a (δ+reserve) (errorRemoval p Z k) (errorMoving p Z k)
        (if reflected then l.1.2 else l.1.1) (if reflected then l.1.1 else l.1.2) C₂ D₂ U+a+error+errorRemoval p Z k-errorMoving p Z k)) := by ring
    _=_ := by
      rw [hp,←mul_div_assoc,←Real.rpow_add hZ]
      congr 2
      ring


/-- Pay the common-allocation small power without discarding the
reciprocal second-label norm. -/
theorem eventual_actual_twice_error_mass_payment (N : ℕ) (lo εv : ℝ)
    (hlo : 0< lo) (hev : 0<εv) :
    ∀ᶠZ : ℝ in atTop,1< Z ∧ ∀{ι : Type}[Fintype ι]
    (s : Input ι),Fintype.card ι≤ N → lo≤ s.lower →
    ∀(reflected second : Bool) (l : FirstSourceLabel)
    (_hC : Supported l.1.1) (_hD : Supported l.1.2),
    primeSupport l.1.1=primeSupport l.1.2 →
    ∀(Rfirst : Ideal O)(B : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
    (χ : Character)(t : ℝ),
    frozenCoefficient B.val (if reflected then l.1.2 else l.1.1) Rfirst s.ν s.W s.P≠0 →
    ∀(p : O),p≠0 → ∀(k : ℕ),
    (∀i,∀I∈(child s (if reflected then l.1.2 else l.1.1) Rfirst B χ t).slots i,
      IsCoprime (Ideal.span {p}) I) →
    ∀(Bp : actualAllocations (child s (if reflected then l.1.2 else l.1.1)
      Rfirst B χ t).pools ((Ideal.span {p})^k))(υ : Character)(v : ℝ),
    ∀(C₂ D₂ : Ideal O)(_hC₂ : Supported C₂)(_hD₂ : Supported D₂)
      (U : Finset (CommonIndex C₂ D₂))(M a δ reserve error εcommon Bnorm : ℝ),0≤εcommon →
    ((if second then D₂ else C₂).absNorm:ℝ)≤ Z^Bnorm →
    let A := Real.logb Z (volume s)
    let nominal := errorNominal M Z a (δ+reserve) (errorRemoval p Z k) (errorMoving p Z k)
      (if reflected then l.1.2 else l.1.1) (if reflected then l.1.1 else l.1.2) C₂ D₂ U
    (firstErrorTailRadius reflected l Z M (volume s) a δ reserve p k/volume (twiceChild s
      (if reflected then l.1.2 else l.1.1) Rfirst B χ t (Ideal.span {p}) k Bp υ v))*
      (normalizer C₂ D₂ U*((if second then D₂ else C₂).absNorm:ℝ)^(εcommon-1))*Z^(nominal+error+errorRemoval p Z k-errorMoving p Z k) ≤
      Z^(lowGeometryExponent reflected Z A l+error+εv+Bnorm*εcommon)/((if second then D₂ else C₂).absNorm:ℝ) := by
  filter_upwards [eventual_actual_twice_error_payment N lo εv hlo hev] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι _ s hcard hlow reflected second l hC hD heq Rfirst B χ t hB p hp k hslot Bp υ v
    C₂ D₂ hC₂ hD₂ U M a δ reserve error εcommon Bnorm hecommon hnorm
  have hh := hz.2 s hcard hlow reflected second l hC hD heq Rfirst B χ t hB p hp k hslot Bp υ v
    C₂ D₂ hC₂ hD₂ U M a δ reserve error
  have hzpos : 0< Z := zero_lt_one.trans hz.1
  let n : ℝ := (if second then D₂ else C₂).absNorm
  have hn : 0< n := by
    cases second
    · exact norm_pos C₂ hC₂.1
    · exact norm_pos D₂ hD₂.1
  have hncap : n^εcommon≤ Z^(Bnorm*εcommon) :=
    (Real.rpow_le_rpow hn.le hnorm hecommon).trans_eq (Real.rpow_mul hzpos.le _ _).symm
  have hp := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hn.le εcommon)
  dsimp only at hp ⊢
  have heqpow : Z^(Real.logb Z n)=n := Real.rpow_logb hzpos hz.1.ne' hn
  have heqleft : normalizer C₂ D₂ U*n^(εcommon-1)=
      (normalizer C₂ D₂ U/Z^(Real.logb Z n))*n^εcommon := by
    rw [Real.rpow_sub hn,Real.rpow_one,heqpow]
    ring
  have hcancel (x y nominal : ℝ) :
      x*y*Z^(nominal+error+errorRemoval p Z k-errorMoving p Z k)=
      Z^(-a)*x*y*Z^(nominal+a+error+errorRemoval p Z k-errorMoving p Z k) := by
    calc
      _ = x*y*Z^(-a+(nominal+a+error+errorRemoval p Z k-errorMoving p Z k)) := by
        congr 1; ring
      _ = _ := by rw [Real.rpow_add hzpos]; ring
  rw [hcancel]
  change Z^(-a)*(firstErrorTailRadius reflected l Z M (volume s) a δ reserve p k/
      volume (twiceChild s (if reflected then l.1.2 else l.1.1) Rfirst B χ t (Ideal.span {p}) k Bp υ v))*
      (normalizer C₂ D₂ U*n^(εcommon-1))*
      Z^(errorNominal M Z a (δ+reserve) (errorRemoval p Z k) (errorMoving p Z k)
        (if reflected then l.1.2 else l.1.1) (if reflected then l.1.1 else l.1.2) C₂ D₂ U+a+error+errorRemoval p Z k-errorMoving p Z k)≤ _
  rw [heqleft]
  have hupper := mul_le_mul_of_nonneg_left hncap
    (div_nonneg (Real.rpow_nonneg hzpos.le
      (lowGeometryExponent reflected Z (Real.logb Z (volume s)) l+error+εv)) hn.le)
  apply le_trans _ (hupper.trans_eq ?_)
  · convert hp using 1
    dsimp only [n]
    ring
  · rw [div_mul_eq_mul_div,←Real.rpow_add hzpos]

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_error_radius_power
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_error_paid_weight_restore
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_error_scalar_reciprocal

#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_twice_inverse_volume
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_twice_error_payment

#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_twice_error_mass_payment

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_error_coefficient_paid_restore

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorScalarPayment -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorBudget; sha256 d5ee1806d04212330d45b7bc755a1cc3f79a2f130ad2f6f3b7862506c41fe9d8 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
                                                             
                                                              
                                                        
                                                                      

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Cycle61Moment Cycle61FinalError
open CenteredMomentFirstChildProfileControl CenteredMomentCommonHeightEnvelope CenteredMomentEligibleEnergy
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentRankinRadical
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationErrorEnergy CenteredMomentAmplificationChildSourceCaps
open CenteredMomentAmplificationAllocationCost CenteredMomentAmplificationActiveFactor
open CenteredMomentAmplifiedRetainedRadius CenteredMomentPrimeElements
open CenteredMomentFirstScale Cycle61FinalErrorCapacity RayFourExpansion
open CenteredMomentFirstAnnularInput
local notation "O" => HeckeFamily.O
local instance errorBudgetDecidableEq {ι : Type*} : DecidableEq ι := Classical.decEq _

/-- Actual supported second labels, including all inactive subsets, over
one squarefree residual projector shell. These are finite geometry gates. -/
structure ErrorResidualLabelShell (Z T B : ℝ) where
  projectors : Finset (Ideal O)
  labels : Ideal O→ Finset FirstSourceLabel
  squarefree : ∀D∈projectors,Squarefree D
  dyad : ∀D∈projectors,T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T
  supported : ∀D∈projectors,∀v∈labels D,Supported v.1.1 ∧ Supported v.1.2
  equalSupport : ∀D∈projectors,∀v∈labels D,primeSupport v.1.1=primeSupport v.1.2
  divides : ∀D∈projectors,∀v∈labels D,D∣v.1.1 ∧ D∣v.1.2
  norm : ∀D∈projectors,∀v∈labels D,(v.1.1.absNorm:ℝ)≤ Z^B ∧ (v.1.2.absNorm:ℝ)≤ Z^B

/-- Exact image of the active extraction menu in the unpruned source. -/
def errorLiftedActiveAllocations {ι : Type*}[Fintype ι]
    (s : Input ι)(Q : Ideal O)(k : ℕ) : Finset (actualAllocations s.pools (Q^k)) :=
  Finset.univ.image (errorActiveAllocation s (Q^k))

theorem error_lifted_active_allocations_card {ι : Type*}[Fintype ι]
    (s : Input ι)(Q : Ideal O)(k : ℕ) :
    (errorLiftedActiveAllocations s Q k).card=
      (actualAllocations (activeInput s).pools (Q^k)).card := by
  unfold errorLiftedActiveAllocations
  rw [Finset.card_image_of_injective _ (errorActiveAllocation_injective s (Q^k)),
    Finset.card_univ,Fintype.card_coe]

/-- Reindex the literal active menu without adding unpruned allocations. -/
theorem error_lifted_active_allocations_sum {ι : Type*}[Fintype ι]
    (s : Input ι)(Q : Ideal O)(k : ℕ)
    (f : actualAllocations s.pools (Q^k)→ℝ) :
    (∑B : errorLiftedActiveAllocations s Q k,f B.val)=
      ∑B : actualAllocations (activeInput s).pools (Q^k),f (errorActiveAllocation s (Q^k) B) := by
  rw [Finset.sum_coe_sort (errorLiftedActiveAllocations s Q k) f]
  unfold errorLiftedActiveAllocations
  rw [Finset.sum_image]
  intro B _ D _ h
  exact errorActiveAllocation_injective s (Q^k) h

/-- The shell loss is paid by a genuine second-label divisor, not by the
frequency ideal. -/
theorem actual_error_projector_height_cap (Z T B εshell : ℝ)
    (hZ : 0< Z)(hT : 0≤ T)(he : 0≤εshell)(D C : Ideal O)
    (hC : Supported C)(hDC : D∣C)(hdyad : T≤(D.absNorm:ℝ))
    (hcap : (C.absNorm:ℝ)≤ Z^B) :
    (2*T)^(3*εshell)≤2^(3*εshell)*Z^(B*(3*εshell)) := by
  have hn : (D.absNorm:ℝ)≤ C.absNorm := by
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)) (map_dvd Ideal.absNorm hDC)
  have hp := Real.rpow_le_rpow (by positivity : 0≤2*T)
    (mul_le_mul_of_nonneg_left (hdyad.trans (hn.trans hcap)) (by norm_num : (0:ℝ)≤2))
    (by positivity : 0≤3*εshell)
  apply hp.trans_eq
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (Real.rpow_nonneg hZ.le _),
    ←Real.rpow_mul hZ.le]

/-- The scalar remaining after the genuine paid column estimate. Its
prime shifts and extracted source volume have not been canceled by definition. -/
def extractedErrorLabelScalar (reflected second : Bool) (l v : FirstSourceLabel)
    (Z M a δ reserve error εcommon V Vextract : ℝ) (p : O) (k : ℕ) : ℝ :=
  (firstErrorTailRadius reflected l Z M V a δ reserve p k/Vextract)*
    (normalizer v.1.1 v.1.2 v.2.val*((if second then v.1.2 else v.1.1).absNorm:ℝ)^(εcommon-1))*
    Z^(errorNominal M Z a (δ+reserve) (errorRemoval p Z k) (errorMoving p Z k)
      (if reflected then l.1.2 else l.1.1) (if reflected then l.1.1 else l.1.2)
      v.1.1 v.1.2 v.2.val+(error-M*branchReserve k)+errorRemoval p Z k-errorMoving p Z k)

/-- Both child restrictions preserve the original fixed profile envelope.
The four mass powers remain visible until this pointwise payment. -/
theorem actual_error_fixed_source_factor {α : Type*}[Fintype α][DecidableEq α]
    (N : ℕ)(Cs bp : ℝ)(hCs : 1≤ Cs)(hbp : 1≤ bp)
    (s : Input α)(hcard : Fintype.card α≤ N)(hM : ∀j,s.M j≤ Cs)
    (hb₁ : s.b₁=bp)(hb₂ : s.b₂=bp)(q : Chain s)(η : Character)(v : ℝ) :
    let src := withHeight q.extracted η v
    src.toData.profileFactor*(∏j,src.M j)^2≤2*bp^2*Cs^(4*N) := by
  intro src
  have hfirst := child_mass s q.C₁ q.R₁ q.B₁ q.η₁ q.t₁
  have hextract := child_mass q.first ((Ideal.span {q.p})^q.k) (q.R₁*q.C₁) q.Bp q.υ q.t₂
  have hm : mass src≤ mass s := hextract.trans hfirst
  have hprod : mass s≤ Cs^N := by
    apply (Finset.prod_le_prod₀ (fun j _=>zero_le_one.trans (s.M_ge_one j)) (fun j _=>hM j)).trans
    simpa only [Finset.prod_const,Finset.card_univ] using pow_le_pow_right₀ hCs hcard
  have hbound := pow_le_pow_left₀ (mass_nonneg src) (hm.trans hprod) 4
  have hfactor : src.toData.profileFactor*(∏j,src.M j)^2=2*bp^2*(mass src)^4 := by
    change (2*(max 1 s.b₁*max 1 s.b₂))*(∏j,src.M j)^2*(∏j,src.M j)^2=_
    rw [hb₁,hb₂,max_eq_right hbp]
    dsimp only [mass]
    ring
  rw [hfactor]
  apply (mul_le_mul_of_nonneg_left hbound (by positivity)).trans_eq
  rw [←pow_mul]
  congr 2
  omega

set_option backward.isDefEq.respectTransparency false in
/-- Full extracted scalar payment: original first labels, residual
projectors, all second labels, all ray characters and actual active prime
allocations. The original prime denominator cancels only after counting. -/
theorem eventual_actual_error_full_label_payment (N : ℕ) (lo εv B ε : ℝ)
    (hlo : 0< lo) (hev : 0<εv) (hB : 0≤ B) (hε : 0<ε) :
    ∃K : ℝ,0< K ∧ ∀ᶠZ : ℝ in atTop,2≤ Z ∧
    ∀{ι : Type}[Fintype ι](s : Input ι),Fintype.card ι≤ N → lo≤ s.lower →
    ∀(reflected second : Bool)(T p exponent error εcommon M a δ reserve : ℝ),
    0≤εcommon → 1≤ T → p≤ B → ∀seed : Ideal O,Squarefree seed → seed≠0 →
    ∀labels : Finset FirstSourceLabel,
    (∀l∈labels,Supported l.1.1 ∧ Supported l.1.2) →
    (∀l∈labels,primeSupport l.1.1=primeSupport l.1.2) →
    (∀l∈labels,seed∣l.1.1 ∧ seed∣l.1.2) →
    (∀l∈labels,(l.1.1.absNorm:ℝ)≤ Z^B ∧ (l.1.2.absNorm:ℝ)≤ Z^B) →
    (∀l∈labels,((commonRadical l.1.1 l.1.2).absNorm:ℝ)≤ Z^p) →
    (∀l∈labels,lowGeometryExponent reflected Z (Real.logb Z (volume s)) l≤ exponent) →
    ∀Rfirst : Ideal O,
    ∀alloc : (l : labels)→ actualAllocations s.pools (if reflected then l.val.1.2 else l.val.1.1),
    ∀(χ : labels→ Character)(t : ℝ),
    (∀l : labels,frozenCoefficient (alloc l).val (if reflected then l.val.1.2 else l.val.1.1)
      Rfirst s.ν s.W s.P≠0) →
    let u : (l : labels)→ Input (CenteredMomentCommonProfile.liveIndices (alloc l).val) := fun l=>child s (if reflected then l.val.1.2 else l.val.1.1) Rfirst (alloc l) (χ l) t
    ∀P : Finset (Ideal O),P.Nonempty → (∀Q∈P,Prime Q) → (∀Q∈P,Q∉fixedBadPrimes) →
    (∀l : labels,∀q : elementPool P,∀j I,I∈(u l).slots j→ IsCoprime (Ideal.span {q.val}) I) →
    let Bps := fun (l : labels) (q : elementPool P)(i : Fin 3)=>
      errorLiftedActiveAllocations (u l) (Ideal.span {q.val}) (errorIndex i+1)
    ∀(υ : (l : labels)→(q : elementPool P)→(i : Fin 3)→ RayCharacter→ Bps l q i→ Character)
      (vheight : ℝ)
      (shell : (l : labels)→(q : elementPool P)→(i : Fin 3)→ RayCharacter→ Bps l q i→
        ErrorResidualLabelShell Z T B),
    (56/(P.card:ℝ))*(∑q : elementPool P,∑i : Fin 3,16*(errorIndex i+2:ℝ)*
      ∑l : labels,∑ψ : RayCharacter,∑Bp : Bps l q i,
        ∑D∈(shell l q i ψ Bp).projectors,∑v∈(shell l q i ψ Bp).labels D,
          extractedErrorLabelScalar reflected second l.val v Z M a δ reserve error εcommon
            (volume s) (volume (child (u l) ((Ideal.span {q.val})^(errorIndex i+1))
              (Rfirst*(if reflected then l.val.1.2 else l.val.1.1))
              (Bp.val) (υ l q i ψ Bp) vheight)) q.val (errorIndex i+1))≤
      K*Z^(p+exponent+error+εv+B*εcommon+ε)/(seed.absNorm:ℝ)*
        ∑i : Fin 3,16*(errorIndex i+2:ℝ)^2*Z^(-M*branchReserve (errorIndex i+1)) := by
  obtain ⟨Kf,hKf,hfirst⟩ := actual_first_low_label_count B (ε/2) hB (half_pos hε)
  obtain ⟨Ks,hKs,hsecond⟩ := actual_low_reciprocal_projector_shell B (ε/2) hB (half_pos hε)
  let Kray : ℝ := Fintype.card RayCharacter
  have hKray : 0< Kray := by dsimp [Kray]; exact_mod_cast Fintype.card_pos
  refine ⟨56*Kray*Kf*Ks,by positivity,?_⟩
  filter_upwards [eventual_actual_twice_error_mass_payment N lo εv hlo hev,
    eventually_ge_atTop (2:ℝ)] with Z hz hZ2
  refine ⟨hZ2,?_⟩
  intro ι _ s hcard hlow reflected second T p exponent error εcommon M a δ reserve
    hecommon hT hp seed hs hs0 labels hsup heq hseed hnorm hrad hgeom Rfirst alloc χ t halloc
    u P hne hprime hbad hslot Bps υ vheight shell
  have hZ : 0< Z := by linarith
  have hcount := hfirst Z (by linarith) p hp seed hs hs0 labels hsup heq hseed hnorm hrad
  have hpair (l : labels)(q : elementPool P)(i : Fin 3)
      (ψ : RayCharacter)(Bp : Bps l q i) :
      (∑D∈(shell l q i ψ Bp).projectors,∑v∈(shell l q i ψ Bp).labels D,
        extractedErrorLabelScalar reflected second l.val v Z M a δ reserve error εcommon
          (volume s) (volume (child (u l) ((Ideal.span {q.val})^(errorIndex i+1))
            (Rfirst*(if reflected then l.val.1.2 else l.val.1.1))
            (Bp.val) (υ l q i ψ Bp) vheight)) q.val (errorIndex i+1))≤
      Z^(exponent+error+εv+B*εcommon-M*branchReserve (errorIndex i+1))*(Ks*Z^(ε/2)) := by
    let sh := shell l q i ψ Bp
    have hc := hsecond second Z T hZ2 hT sh.projectors sh.squarefree sh.dyad sh.labels
      sh.supported sh.equalSupport sh.divides sh.norm
    calc
      _ ≤ ∑D∈sh.projectors,∑v∈sh.labels D,
          Z^(exponent+error+εv+B*εcommon-M*branchReserve (errorIndex i+1))/
            ((if second then v.1.2 else v.1.1).absNorm:ℝ) := by
        apply Finset.sum_le_sum
        intro D hD
        apply Finset.sum_le_sum
        intro v hv
        have hq := elementPool_data P hprime hbad q.val q.property
        have hq0 : q.val≠0 := hq.1.ne_zero
        have hm := hz.2 s hcard hlow reflected second l.val (hsup l.val l.property).1 (hsup l.val l.property).2
          (heq l.val l.property) Rfirst (alloc l) (χ l) t (halloc l) q.val hq0 (errorIndex i+1)
          (hslot l q) (Bp.val) (υ l q i ψ Bp) vheight
          v.1.1 v.1.2 (sh.supported D hD v hv).1 (sh.supported D hD v hv).2 v.2.val
          M a δ reserve (error-M*branchReserve (errorIndex i+1)) εcommon B hecommon (by
            cases second
            · exact (sh.norm D hD v hv).1
            · exact (sh.norm D hD v hv).2)
        apply hm.trans
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        apply Real.rpow_le_rpow_of_exponent_le (by linarith)
        linarith [hgeom l.val l.property]
      _ = Z^(exponent+error+εv+B*εcommon-M*branchReserve (errorIndex i+1))*
          (∑D∈sh.projectors,∑v∈sh.labels D,1/((if second then v.1.2 else v.1.1).absNorm:ℝ)) := by
        simp only [Finset.mul_sum,mul_one_div]
      _ ≤ _ := mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg hZ.le _)
  have hprimeIdeal (q : elementPool P) : Prime (Ideal.span {q.val}) := by
    have h := (elementPool_data P hprime hbad q.val q.property).2.1
    exact hprime _ h
  have halloccount (l : labels)(q : elementPool P)(i : Fin 3) :
      (Fintype.card (Bps l q i):ℝ)≤ errorIndex i+2 := by
    have hh := actual_amplification_allocations_card (u l).pools
      (Ideal.span {q.val}) (hprimeIdeal q) (errorIndex i+1) (by
        intro j I hI
        exact ⟨(u l).pools_ne _ _ hI,hslot l q j I hI⟩)
    have hsubset : (errorLiftedActiveAllocations (u l) (Ideal.span {q.val})
        (errorIndex i+1)).card≤(actualAllocations (u l).pools
          ((Ideal.span {q.val})^(errorIndex i+1))).card := by
      exact (Finset.card_le_univ _).trans_eq (Fintype.card_coe _)
    dsimp only [Bps]
    rw [Fintype.card_coe]
    exact_mod_cast hsubset.trans hh
  have htotal (q : elementPool P)(i : Fin 3) :
      (∑l : labels,∑ψ : RayCharacter,∑Bp : Bps l q i,
        ∑D∈(shell l q i ψ Bp).projectors,∑v∈(shell l q i ψ Bp).labels D,
          extractedErrorLabelScalar reflected second l.val v Z M a δ reserve error εcommon
            (volume s) (volume (child (u l) ((Ideal.span {q.val})^(errorIndex i+1))
              (Rfirst*(if reflected then l.val.1.2 else l.val.1.1))
              (Bp.val) (υ l q i ψ Bp) vheight)) q.val (errorIndex i+1))≤
      Kray*(errorIndex i+2:ℝ)*
        (Kf*Ks*Z^(p+exponent+error+εv+B*εcommon+ε)/(seed.absNorm:ℝ))*
          Z^(-M*branchReserve (errorIndex i+1)) := by
    let E := Z^(exponent+error+εv+B*εcommon-M*branchReserve (errorIndex i+1))*(Ks*Z^(ε/2))
    have hE : 0≤ E := by dsimp [E]; positivity
    calc
      _ ≤ ∑l : labels,∑ψ : RayCharacter,∑_Bp : Bps l q i,E := by
        apply Finset.sum_le_sum
        intro l _
        exact Finset.sum_le_sum (fun ψ _=>Finset.sum_le_sum (fun Bp _=>hpair l q i ψ Bp))
      _ ≤ ∑_l : labels,Kray*(errorIndex i+2:ℝ)*E := by
        apply Finset.sum_le_sum
        intro l _
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
        dsimp only [Kray]
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (halloccount l q i) hE)
          (Nat.cast_nonneg (Fintype.card RayCharacter))
      _ = (labels.card:ℝ)*(Kray*(errorIndex i+2:ℝ)*E) := by simp
      _ ≤ (Kf*Z^(p+ε/2)/(seed.absNorm:ℝ))*(Kray*(errorIndex i+2:ℝ)*E) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
      _ = _ := by
        dsimp only [E]
        simp only [Real.rpow_add hZ,Real.rpow_sub hZ]
        have he : Z^ε=Z^(ε/2)*Z^(ε/2) := by rw [←Real.rpow_add hZ,add_halves]
        rw [he,neg_mul,Real.rpow_neg hZ.le]
        ring
  have hpcount : Fintype.card (elementPool P)=P.card := by
    rw [Fintype.card_coe,elementPool_card P hprime hbad]
  have hpc : (0:ℝ)< P.card := by exact_mod_cast hne.card_pos
  calc
    _ ≤ (56/(P.card:ℝ))*(∑q : elementPool P,∑i : Fin 3,16*(errorIndex i+2:ℝ)*
        (Kray*(errorIndex i+2:ℝ)*(Kf*Ks*Z^(p+exponent+error+εv+B*εcommon+ε)/(seed.absNorm:ℝ))*
          Z^(-M*branchReserve (errorIndex i+1)))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun q _=>Finset.sum_le_sum
        (fun i _=>mul_le_mul_of_nonneg_left (htotal q i) (by positivity)))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hpcount,Finset.mul_sum]
      field_simp
      apply Finset.sum_congr rfl
      intro i hi
      ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_error_full_label_payment

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_error_fixed_source_factor

#print axioms OAI.SevenEighths.Cycle61InitialMass.error_lifted_active_allocations_card
#print axioms OAI.SevenEighths.Cycle61InitialMass.error_lifted_active_allocations_sum
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_error_projector_height_cap

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorBudget -/

/- BEGIN ORIGINAL Cycle61.Physical.FixedInducing; sha256 b4772638b96d51302d9b5d959387010eec2bc31cbbad3d56c5e34ea71fc00eb9 -/
section
                                                                              

namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory
namespace SevenEighths.Cycle61FixedInducing
open CenteredMomentFiniteProfileExceptionalPhysical CenteredMomentFirstCanonicalAllowance
open CenteredMomentSecondPhysicalLedger
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicRowSupport

open CenteredMomentSecondExceptionalPhysicalSaving CenteredMomentRankinRadical
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

/-- The literal physical block keeps both the positive radius factor and
its centered lattice cancellation before any common-part aggregation. -/
theorem physical_power_identity (Z : ℝ) (hZ : 1< Z)
    (Ck P a e δ θ r c d V K R : ℝ)
    (hc : 0< c) (hd : 0< d) (hV : 0< V) (hK : 0< K) (hR : 0< R) :
    Ck*(P*Z^(2*e+δ-max (r-min (Real.logb Z c) (Real.logb Z d)) 0)*
      (c*d)^θ*V^(1/3:ℝ)*K^(5/6:ℝ)*a^(-2/3:ℝ)*
      Z^(-(Real.logb Z c+Real.logb Z d)/3)/R) =
    Ck*P*a^(-2/3:ℝ)*Z^(2*e+δ+θ*(Real.logb Z c+Real.logb Z d)+
      Real.logb Z V/3+5*Real.logb Z K/6-(Real.logb Z c+Real.logb Z d)/3-
      Real.logb Z R-max (r-min (Real.logb Z c) (Real.logb Z d)) 0) := by
  have hz : 0< Z := zero_lt_one.trans hZ
  have power (x t : ℝ) (hx : 0< x) : x^t=Z^(Real.logb Z x*t) := by
    rw [Real.rpow_mul hz.le,Real.rpow_logb hz hZ.ne' hx]
  rw [power (c*d) θ (mul_pos hc hd), Real.logb_mul hc.ne' hd.ne',
    power V (1/3) hV, power K (5/6) hK]
  have hRi : R⁻¹=Z^(-Real.logb Z R) := by
    rw [Real.rpow_neg hz.le,Real.rpow_logb hz hZ.ne' hR]
  rw [div_eq_mul_inv,hRi]
  calc
    _ = Ck*P*a^(-2/3:ℝ)*(Z^(2*e+δ-max (r-min (Real.logb Z c) (Real.logb Z d)) 0)*
      Z^((Real.logb Z c+Real.logb Z d)*θ)*Z^(Real.logb Z V*(1/3))*
      Z^(Real.logb Z K*(5/6))*Z^(-(Real.logb Z c+Real.logb Z d)/3)*
      Z^(-Real.logb Z R)) := by ring
    _ = _ := by
      repeat rw [←Real.rpow_add hz]
      congr 2
      ring

theorem actual_exceptional_log_block (wlo whi:ℝ)(hwlo:0< wlo)(hwhi:0≤ whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤ B)(hL:0≤ Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤ Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤ Ideal.span {(72:O)} →
      ∃K:ℝ,0< K ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
      ∀τ:RayCharacter→ Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤ Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤ Z^B) →
      ∀χ₀:RayCharacter,idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤ H) → H/(D.absNorm:ℝ)≤ Z^Lbound →
      ∀a:ℝ,0< a → (∀I:Ideal O,β I≠0→ a*volume s.toData≤(I.absNorm:ℝ)) →
      ∀(R Kphys:ℝ),0< Kphys → ∀n:Fin 4→ℤ,
      ‖physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n‖/volume s.toData≤
        Ck*profileFactor Sprofile s p J Q K*a^(-2/3:ℝ)*
          Z^(2*ε+δ + θ*(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ)) +
            Real.logb Z (volume s.toData)/3 + 5*Real.logb Z Kphys/6 -
            (Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3 -
            Real.logb Z (Ideal.absNorm (commonRadical C D):ℝ) -
            max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0) := by
  obtain ⟨J,Sprofile,hSp,Ck,hCk,hbound⟩ :=
    CenteredMomentFiniteProfileExceptionalFixedQ.actual_saved_exceptional_block
      wlo whi hwlo hwhi lo hi W ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSp,Ck,hCk,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨K,hK,hbound⟩ := hbound Q hQ hQt hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW1 hW2 C D hC hD R0 seed hR0 hsC hsD hCD U A S β
    r hX1 hX2 hY1 hY2 τ hτ rows hn hex1 hex2 hcond1 hcond2 χ0 hη
    m hm hml hm2 hex H hβ hHD a ha hlower R Kphys hKphys n
  have hb := hZ.2 s p hlo hhi hP hW1 hW2 C D hC hD R0 seed hR0 hsC hsD hCD U
    r hX1 hX2 hY1 hY2 τ hτ rows hn hex1 hex2 hcond1 hcond2 χ0 hη
    m hm hml hm2 hex H hβ hHD a ha hlower R Kphys hKphys n
  have hc : 0<(C.absNorm:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd : 0<(D.absNorm:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hp : 0<(Ideal.absNorm (commonRadical C D):ℝ) := by
    rw [← common_ideal_product]
    exact common_product_pos C D hC Finset.univ
  apply hb.trans_eq
  exact physical_power_identity Z hZ.1 _ _ _ _ _ _ _ _ _ _ _ _ hc hd
    (volume_pos s.toData) hKphys hp

end SevenEighths.Cycle61FixedInducing
end
end OAI

#print axioms OAI.SevenEighths.Cycle61FixedInducing.actual_exceptional_log_block

end
/- END ORIGINAL Cycle61.Physical.FixedInducing -/

/- BEGIN ORIGINAL Cycle61.Physical.FixedInducingChosen; sha256 718069b685f1f754a2e5fd5ad142a8cd539d324c68f823ec7b42257d082a3bbe -/
section
                                     
                                                                        
                                                                                
                                                                  
                                                                 
                                                             
                                                                                
                                                                                 
                                                                        
                                                                          
                                                                 
                                                              
                                                                  
                                                               

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.Cycle61FixedInducingChosen
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicRowSupport

open CenteredMomentSecondExceptionalPhysicalSaving CenteredMomentRankinRadical
open CenteredMomentSecondExceptionalCommonSaving
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

open CenteredMomentSecondExceptionalFamily CenteredMomentSecondExceptionalSourceFamily
open CenteredMomentSecondEnergySplit CenteredMomentSecondLiveBlock
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceLowerSupport
open CenteredMomentFiniteProfileExceptionalPhysical

theorem chosen_exceptional_log_block (wlo whi:ℝ)(hwlo:0< wlo)(hwhi:0≤ whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤ B)(hL:0≤ Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤ Ck ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤ Ideal.span {(72:O)} →
      ∃K:ℝ,0< K ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),
      R0≠0 → seed∣C → seed∣D → (C.absNorm:ℝ)≤ Z^B → (D.absNorm:ℝ)≤ Z^B →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
      ∀χ₀:RayCharacter,idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      sourceRadius s≤ Z^Lbound → ∀(R Kphys:ℝ),0< Kphys →
      (expandedFactor s.η:ℝ)*R0.absNorm*C.absNorm*D.absNorm*(4*R)≤ Z^B →
      ∀n:Fin 4→ℤ,
      ‖physicalBlock s.η s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R0 seed) C D hC hD U R
        (partRows true s.η χ₀ Q m C D U R) W Kphys n‖/volume s.toData≤
        Ck*profileFactor Sprofile s p J Q K*((∏i,s.lo i)*wlo*wlo)^(-2/3:ℝ)*
          Z^(2*ε+δ + θ*(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ)) +
            Real.logb Z (volume s.toData)/3 + 5*Real.logb Z Kphys/6 -
            (Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3 -
            Real.logb Z (Ideal.absNorm (commonRadical C D):ℝ) -
            max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0):=by
  obtain ⟨J,Sprofile,hSp,Ck,hCk,hbound⟩:=
    Cycle61FixedInducing.actual_exceptional_log_block
      wlo whi hwlo hwhi lo hi W ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSp,Ck,hCk,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨K,hK,hbound⟩:=hbound Q hQ hQt hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW1 hW2 C D hC hD R0 seed hR0 hsC hsD hNC hND hCD U
    r hX1 hX2 hY1 hY2 χ₀ hη m hm hml hm2 hsource R Kphys hKphys hcond n
  let S:=finiteColumns (Fintype.piFinset s.pools)
  let β:=coefficient s R0 seed
  let rows:=partRows true s.η χ₀ Q m C D U R
  have hn:∀z∈rows,z≠0:=exceptional_part_nonzero s.η χ₀ Q m C D U R
  have hex:=exceptional_part_inducing s.η χ₀ Q m C D U R
  have hprofile0 (i:Fin 2):p.profile i 0=0:=by
    by_contra hh
    have hp:=(p.support i hh).1
    linarith
  have hz1:s.W₁ 0=0:=by rw [hW1];exact hprofile0 0
  have hz2:s.W₂ 0=0:=by rw [hW2];exact hprofile0 1
  have hβ:∀I:Ideal O,β I≠0→(I.absNorm:ℝ)≤ sourceRadius s:=
    fun I hI=>(original_column_norm s R0 seed I hz1 hz2 hI).2
  have hD1:1≤(D.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hHD:sourceRadius s/(D.absNorm:ℝ)≤ Z^Lbound:=by
    by_cases hh:0≤ sourceRadius s
    · exact (div_le_self hh hD1).trans hsource
    · exact (div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hh) (Nat.cast_nonneg _)).trans
        (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)
  have ha:0<(∏i,s.lo i)*wlo*wlo:=
    mul_pos (mul_pos (Finset.prod_pos (fun i _=>s.lo_pos i)) hwlo) hwlo
  have hlower (I:Ideal O)(hI:β I≠0):
      ((∏i,s.lo i)*wlo*wlo)*volume s.toData≤(I.absNorm:ℝ):=by
    have hh:=profile_column_lower R0 s.ν s.W s.P s.lo s.W₁ s.W₂ wlo wlo
      s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) 1 1 seed s.P_pos (fun i=>(s.lo_pos i).le)
      hwlo.le hwlo.le s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos one_ne_zero one_ne_zero rfl s.same_product
      (fun i x hx=>(s.support i hx).1)
      (fun x hx=>(p.support 0 (by rwa [hW1] at hx)).1)
      (fun x hx=>(p.support 1 (by rwa [hW2] at hx)).1)
      (Fintype.piFinset s.pools) I hI
    simpa only [CenteredMomentExceptionalAmplitudePair.volume,map_one,Nat.cast_one,mul_one,div_one,mul_assoc] using hh
  by_cases hzero:physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n=0
  · rw [hzero,norm_zero,zero_div]
    have hp:=profileFactor_nonneg Sprofile s p J Q K hK.le
    have hv:=volume_pos s.toData
    have hZpos:0< Z:=zero_lt_one.trans hZ.1
    positivity
  obtain ⟨τ,hτ⟩:=exists_exceptional_family s.η C D hC hD hCD U
  have he:=actual_family_both_rows s.η χ₀ Q hQ72 m hm hml hm2 C D hC hD U τ hτ R
  have hc (χ ξ:RayCharacter)(z:O)(hz:z∈rows):
      (expandedConductor (τ χ) R0 C z:ℝ)≤ Z^B ∧
      (expandedConductor (reflected (τ ξ)) R0 D z:ℝ)≤ Z^B:=by
    have hg:=expanded_conductor_bounds hτ hCD s.t S β R rows W Kphys hKphys n hzero χ ξ R0 z
    have hzlive:z∈liveRows C D U R rows:=by
      rw [show liveRows C D U R rows=rows from exceptional_part_live s.η χ₀ Q m C D U R]
      exact hz
    have hzN:=live_norm_le_four_radius C D U R rows z hzlive
    have hb:(expandedFactor s.η:ℝ)*R0.absNorm*C.absNorm*D.absNorm*(Ideal.span {z}).absNorm≤ Z^B:=by
      apply le_trans _ hcond
      exact mul_le_mul_of_nonneg_left hzN (by positivity)
    constructor
    · exact (show (expandedConductor (τ χ) R0 C z:ℝ)≤
        (expandedFactor s.η:ℝ)*R0.absNorm*C.absNorm*D.absNorm*(Ideal.span {z}).absNorm by
        exact_mod_cast hg.1).trans hb
    · exact (show (expandedConductor (reflected (τ ξ)) R0 D z:ℝ)≤
        (expandedFactor s.η:ℝ)*R0.absNorm*C.absNorm*D.absNorm*(Ideal.span {z}).absNorm by
        exact_mod_cast hg.2).trans hb
  exact hZ.2 s p hlo hhi hP hW1 hW2 C D hC hD R0 seed hR0 hsC hsD hCD U
    r hX1 hX2 hY1 hY2 τ hτ.height_eq rows hn he.1 he.2
    (fun χ z hz=>by simpa only [expandedConductor,Nat.cast_mul] using (hc χ χ z hz).1)
    (fun χ z hz=>by simpa only [expandedConductor,Nat.cast_mul] using (hc χ χ z hz).2)
    χ₀ hη m hm hml hm2 hex (sourceRadius s) hβ hHD
    ((∏i,s.lo i)*wlo*wlo) ha hlower R Kphys hKphys n

end SevenEighths.Cycle61FixedInducingChosen

end

end OAI

#print axioms OAI.SevenEighths.Cycle61FixedInducingChosen.chosen_exceptional_log_block

end
/- END ORIGINAL Cycle61.Physical.FixedInducingChosen -/
