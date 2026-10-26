import Candidate.Cycle63.Physical.InitialMass.SecondHighPayment

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization Cycle63Moment Cycle63HighGeometry
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
local notation "O" => HeckeFamily.O

/-- High scalar payment for the genuine first common child. The eventual
threshold pays the fixed lower-volume constant before any moving source. -/
theorem eventual_actual_child_high_payment (N : ℕ) (lo εv : ℝ)
    (hlo : 0<lo) (hev : 0<εv) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀{ι : Type}[Fintype ι]
    (s : Input ι),Fintype.card ι≤N → lo≤s.lower →
    ∀(reflected left second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2),
    primeSupport l.1.1=primeSupport l.1.2 →
    ∀(Rfirst : Ideal O)(B : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
    (χ : Character)(t : ℝ),
    frozenCoefficient B.val (if reflected then l.1.2 else l.1.1) Rfirst s.ν s.W s.P≠0 →
    ∀(C₂ D₂ : Ideal O)(hC₂ : Supported C₂)(hD₂ : Supported D₂),
    primeSupport C₂=primeSupport D₂ →
    ∀(U : Finset (CommonIndex C₂ D₂))(b δ M a ξ reserve ε : ℝ),
    3401/100000≤b ∧ b≤1/25 →
    Cycle63.Arithmetic.q0≤δ ∧ δ≤3/4 → 0≤M →
    Real.logb Z (volume s)≤M*Cycle63.Arithmetic.totalA b →
    a≤M*Cycle63.Arithmetic.amp b →
    let A := Real.logb Z (volume s)
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
    Z^(-a)*(firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l/volume (child s
      (if reflected then l.1.2 else l.1.1) Rfirst B χ t))*
      (normalizer C₂ D₂ U/Z^b₂)*Z^(m+ρ*q+δ*(A-c-b₂)) ≤
      Z^(S-M*((-3140426139/871234000000))+(1-ρ)*ω+ρ*ε+εv) := by
  filter_upwards [eventual_common_inverse_volume N lo εv hlo hev] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι _ s hcard hlow reflected left second l hC hD heq Rfirst B χ t hB
    C₂ D₂ hC₂ hD₂ heq₂ U b δ M a ξ reserve ε hb hδ hM hA ha
  let A := Real.logb Z (volume s)
  let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
  have hZ := zero_lt_one.trans hz.1
  have hv := volume_pos s
  have hc : (0:ℝ)<(if reflected then l.1.2 else l.1.1).absNorm := by
    cases reflected <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · exact norm_pos _ hC.1
    · exact norm_pos _ hD.1
  have hV : Z^A=volume s := Real.rpow_logb hZ hz.1.ne' hv
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
  have hp := actual_high_scalar_payment reflected left second l hC hD heq
    C₂ D₂ hC₂ hD₂ heq₂ U Z b δ M A a ξ reserve ε hz.1 hb hδ hM hA ha
  dsimp only at hp ⊢
  rw [hV] at hp
  have hp' := mul_le_mul_of_nonneg_left hp (Real.rpow_pos_of_pos hZ εv).le
  rw [←Real.rpow_add hZ] at hp'
  rw [add_comm εv] at hp'
  apply le_trans _ hp'
  have hn := (normalizer_pos C₂ D₂ hC₂ U).le
  have hh := mul_le_mul_of_nonneg_left hmain (Real.rpow_pos_of_pos hZ (-a)).le
  have hh' := mul_le_mul_of_nonneg_right hh
    (div_nonneg hn (Real.rpow_pos_of_pos hZ (Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ))).le)
  have hh'' := mul_le_mul_of_nonneg_right hh' (Real.rpow_pos_of_pos hZ
    (Real.logb Z ((firstSourceMissing left l).absNorm:ℝ)+LocalMoment.unmarkedDensity δ*
      (M-Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)-
        max (c-Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)) 0+
        Real.logb Z ((Ideal.span {firstSourceNumerator left l}).absNorm:ℝ)-6*a-
        (frequencyLoss Z 32 ξ+reserve)+ε)+
      δ*(A-c-Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)))).le
  convert hh'' using 1 <;> ring

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.eventual_actual_child_high_payment
