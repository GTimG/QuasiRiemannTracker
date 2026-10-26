import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryErrorTail
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.FinalErrorCapacity.Capacity
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondLowLabelBudget
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open ConcretePrimeRowBridge
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentRankinRadical
open CenteredMomentAmplifiedRetainedRadius CenteredMomentFirstExceptionalPrefactor
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization Cycle63Moment Cycle63FinalErrorCapacity
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationErrorEnergy

theorem actual_error_radius_power (reflected : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : primeSupport l.1.1=primeSupport l.1.2)
    (Z M A a δ reserve : ℝ) (p : O) (k : ℕ) (hZ : 1<Z) :
    let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    firstErrorTailRadius reflected l Z M (Z^A) a δ reserve p k=
      Z^(2*A-c-d+R+E-M+max (d-c-2*errorRemoval p Z k+errorMoving p Z k) 0+
        3*a+δ+reserve) := by
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
  unfold firstErrorTailRadius errorCommonRadius
  rw [hnom]
  congr 1
  cases reflected
  · rfl
  · simp only [ite_true]
    ring

/-- The extracted prime volume and restored paid weight cancel the two
prime-power shifts in the genuine error radius and error nominal. -/
theorem actual_error_scalar_reciprocal (reflected second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : primeSupport l.1.1=primeSupport l.1.2)
    (C₂ D₂ : Ideal O)(hC₂ : Supported C₂)(hD₂ : Supported D₂)
    (U : Finset (CommonIndex C₂ D₂))
    (Z M A a δ reserve error : ℝ)(p : O)(k : ℕ)(hZ : 1<Z) :
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
    by_cases h : 0≤x
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
    (hlo : 0<lo)(hev : 0<εv) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀{ι : Type}[Fintype ι]
    (s : Input ι),Fintype.card ι≤N → lo≤ s.lower →
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
    (hlo : 0<lo) (hev : 0<εv) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀{ι : Type}[Fintype ι]
    (s : Input ι),Fintype.card ι≤N → lo≤ s.lower →
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
      (show 0≤firstErrorTailRadius reflected l Z M (volume s) a δ reserve p k by
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
    (hlo : 0<lo) (hev : 0<εv) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀{ι : Type}[Fintype ι]
    (s : Input ι),Fintype.card ι≤N → lo≤ s.lower →
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
    ((if second then D₂ else C₂).absNorm:ℝ)≤Z^Bnorm →
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
  have hzpos : 0<Z := zero_lt_one.trans hz.1
  let n : ℝ := (if second then D₂ else C₂).absNorm
  have hn : 0<n := by
    cases second
    · exact norm_pos C₂ hC₂.1
    · exact norm_pos D₂ hD₂.1
  have hncap : n^εcommon≤Z^(Bnorm*εcommon) :=
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
        congr 1; ring_nf
      _ = _ := by rw [Real.rpow_add hzpos]; ring
  rw [hcancel]
  change Z^(-a)*(firstErrorTailRadius reflected l Z M (volume s) a δ reserve p k/
      volume (twiceChild s (if reflected then l.1.2 else l.1.1) Rfirst B χ t (Ideal.span {p}) k Bp υ v))*
      (normalizer C₂ D₂ U*n^(εcommon-1))*
      Z^(errorNominal M Z a (δ+reserve) (errorRemoval p Z k) (errorMoving p Z k)
        (if reflected then l.1.2 else l.1.1) (if reflected then l.1.1 else l.1.2) C₂ D₂ U+a+error+errorRemoval p Z k-errorMoving p Z k)≤_
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
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
