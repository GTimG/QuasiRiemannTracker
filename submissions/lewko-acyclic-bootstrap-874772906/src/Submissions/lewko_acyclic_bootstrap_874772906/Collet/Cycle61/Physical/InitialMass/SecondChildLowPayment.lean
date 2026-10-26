import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.SecondLowLabelBudget

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization Cycle61Moment Cycle61HighGeometry
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
local notation "O" => HeckeFamily.O

/-- Low scalar payment for the literal first common child. The remaining
weight is the one-sided reciprocal norm used by the low label budget. -/
theorem eventual_actual_child_low_payment (N : ℕ) (lo εv : ℝ)
    (hlo : 0<lo) (hev : 0<εv) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀{ι : Type}[Fintype ι]
    (s : Input ι),Fintype.card ι≤N → lo≤s.lower →
    ∀(reflected second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2),
    primeSupport l.1.1=primeSupport l.1.2 →
    ∀(Rfirst : Ideal O)(B : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
    (χ : Character)(t : ℝ),
    frozenCoefficient B.val (if reflected then l.1.2 else l.1.1) Rfirst s.ν s.W s.P≠0 →
    ∀(C₂ D₂ : Ideal O)(hC₂ : Supported C₂)(hD₂ : Supported D₂)
      (U : Finset (CommonIndex C₂ D₂))(M a ξ reserve error : ℝ),
    let A := Real.logb Z (volume s)
    let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
    let nominal := Cycle61FinalCapacity.secondNominal M Z a (frequencyLoss Z 32 ξ+reserve)
      (if reflected then l.1.2 else l.1.1) (if reflected then l.1.1 else l.1.2) C₂ D₂ U
    Z^(-a)*(firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l/volume (child s
      (if reflected then l.1.2 else l.1.1) Rfirst B χ t))*
      (normalizer C₂ D₂ U/Z^b₂)*Z^(nominal+a+error) ≤
      Z^(lowGeometryExponent reflected Z A l+error+εv)/((if second then D₂ else C₂).absNorm:ℝ) := by
  filter_upwards [eventual_common_inverse_volume N lo εv hlo hev] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι _ s hcard hlow reflected second l hC hD heq Rfirst B χ t hB C₂ D₂ hC₂ hD₂ U M a ξ reserve error
  let A := Real.logb Z (volume s)
  let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
  have hZ := zero_lt_one.trans hz.1
  have hc : (0:ℝ)<(if reflected then l.1.2 else l.1.1).absNorm := by
    cases reflected
    · exact norm_pos _ hC.1
    · exact norm_pos _ hD.1
  have hV : Z^A=volume s := Real.rpow_logb hZ hz.1.ne' (volume_pos s)
  have hratio : ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)/volume s=
      (Z^(A-c))⁻¹ := by
    rw [Real.rpow_sub hZ,hV,Real.rpow_logb hZ hz.1.ne' hc,inv_div]
  have hi := hz.2 s hcard hlow _ Rfirst B χ t hB
  rw [hratio] at hi
  have hmain : firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l /
      volume (child s (if reflected then l.1.2 else l.1.1) Rfirst B χ t) ≤
      Z^εv*(firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l/Z^(A-c)) := by
    have hh := mul_le_mul_of_nonneg_left hi
      (first_main_radius_pos reflected (Z^M) (volume s) Z ξ (3*a) reserve hZ l).le
    simpa only [div_eq_mul_inv,mul_left_comm] using hh
  have hp := actual_low_scalar_reciprocal reflected second l hC hD heq C₂ D₂ hC₂ hD₂ U
    Z M A a ξ reserve error hz.1
  dsimp only at hp ⊢
  rw [hV] at hp
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmain (Real.rpow_pos_of_pos hZ (-a)).le)
      (div_nonneg (normalizer_pos C₂ D₂ hC₂ U).le (Real.rpow_nonneg hZ.le (Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)))))
    (Real.rpow_nonneg hZ.le (Cycle61FinalCapacity.secondNominal M Z a (frequencyLoss Z 32 ξ+reserve)
      (if reflected then l.1.2 else l.1.1) (if reflected then l.1.1 else l.1.2) C₂ D₂ U+a+error))
  apply hh.trans_eq
  rw [show Z^εv*(firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l/Z^(A-c))=
    (firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l/Z^(A-c))*Z^εv by ring]
  calc
    _=Z^εv*(Z^(-a)*(firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l/Z^(A-c))*
      (normalizer C₂ D₂ U/Z^(Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)))*
      Z^(Cycle61FinalCapacity.secondNominal M Z a (frequencyLoss Z 32 ξ+reserve)
        (if reflected then l.1.2 else l.1.1) (if reflected then l.1.1 else l.1.2) C₂ D₂ U+a+error)) := by ring
    _=_ := by rw [hp,←mul_div_assoc,←Real.rpow_add hZ]; congr 2 <;> ring

/-- Include the common-allocation small-power cost while retaining the
reciprocal norm required by the one-sided Rankin estimate. -/
theorem eventual_actual_child_low_mass_payment (N : ℕ) (lo εv : ℝ)
    (hlo : 0<lo) (hev : 0<εv) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀{ι : Type}[Fintype ι]
    (s : Input ι),Fintype.card ι≤N → lo≤s.lower →
    ∀(reflected second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2),
    primeSupport l.1.1=primeSupport l.1.2 →
    ∀(Rfirst : Ideal O)(B : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
    (χ : Character)(t : ℝ),
    frozenCoefficient B.val (if reflected then l.1.2 else l.1.1) Rfirst s.ν s.W s.P≠0 →
    ∀(C₂ D₂ : Ideal O)(hC₂ : Supported C₂)(hD₂ : Supported D₂)
      (U : Finset (CommonIndex C₂ D₂))(M a ξ reserve error εcommon Bnorm : ℝ),0≤εcommon →
    ((if second then D₂ else C₂).absNorm:ℝ)≤Z^Bnorm →
    let A := Real.logb Z (volume s)
    let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
    let nominal := Cycle61FinalCapacity.secondNominal M Z a (frequencyLoss Z 32 ξ+reserve)
      (if reflected then l.1.2 else l.1.1) (if reflected then l.1.1 else l.1.2) C₂ D₂ U
    Z^(-a)*(firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l/volume (child s
      (if reflected then l.1.2 else l.1.1) Rfirst B χ t))*
      (normalizer C₂ D₂ U*((if second then D₂ else C₂).absNorm:ℝ)^(εcommon-1))*Z^(nominal+a+error) ≤
      Z^(lowGeometryExponent reflected Z A l+error+εv+Bnorm*εcommon)/((if second then D₂ else C₂).absNorm:ℝ) := by
  filter_upwards [eventual_actual_child_low_payment N lo εv hlo hev] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι _ s hcard hlow reflected second l hC hD heq Rfirst B χ t hB
    C₂ D₂ hC₂ hD₂ U M a ξ reserve error εcommon Bnorm hecommon hnorm
  have hh := hz.2 s hcard hlow reflected second l hC hD heq Rfirst B χ t hB
    C₂ D₂ hC₂ hD₂ U M a ξ reserve error
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
  change Z^(-a)*(firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l/
      volume (child s (if reflected then l.1.2 else l.1.1) Rfirst B χ t))*
      (normalizer C₂ D₂ U*n^(εcommon-1))*
      Z^(Cycle61FinalCapacity.secondNominal M Z a (frequencyLoss Z 32 ξ+reserve)
        (if reflected then l.1.2 else l.1.1) (if reflected then l.1.1 else l.1.2) C₂ D₂ U+a+error)≤_
  rw [heqleft]
  have hupper := mul_le_mul_of_nonneg_left hncap
    (div_nonneg (Real.rpow_nonneg hzpos.le
      (lowGeometryExponent reflected Z (Real.logb Z (volume s)) l+error+εv)) hn.le)
  apply le_trans _ (hupper.trans_eq ?_)
  · convert hp using 1 <;> dsimp only [n] <;> ring
  · rw [div_mul_eq_mul_div,←Real.rpow_add hzpos]

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_child_low_payment

#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_child_low_mass_payment
