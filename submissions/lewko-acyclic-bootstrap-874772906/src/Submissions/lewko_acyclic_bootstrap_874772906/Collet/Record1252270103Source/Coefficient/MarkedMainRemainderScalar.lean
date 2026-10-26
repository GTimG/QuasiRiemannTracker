/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The literal MAIN radius and balanced first-label normalization pay the
zero and discarded-tail exponents. No earlier numerical beta range is used. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.MarkedMainRemainderSum
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.MarkedMainPrefactor
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalBalancedPayment
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.MarkedMainRemainder
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open Filter HeckeFamily Cycle61InitialMass Cycle61Moment Cycle61SecondZero CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstExceptionalPrefactor CenteredMomentRankinRadical
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentAmplificationChildInput CenteredMomentFirstAnnularMajorant
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open QRH.Record1252270103Source.High.CoupledFirst
open QRH.Record1252270103Source.Admission
open Record12518109Natural (balancedGeometrySide)
open QRH.Record1252270103Source.Pool
local notation "O" => HeckeFamily.O

def mainBaseExponent (reflected : Bool) (M A : ℝ) (v : Fin 5→ℝ) : ℝ :=
  2*A-v 0-v 1+v 3+v 4-M+
    max ((if reflected then v 0 else v 1)-(if reflected then v 1 else v 0)) 0

/-- Both common ideals are nonzero, and the genuine balanced surplus is
nonnegative. The radical term is retained for the later label count. -/
theorem main_base_payment (reflected : Bool) (M A : ℝ) (v : Fin 5→ℝ)
    (hc : 0≤v 0) (hd : 0≤v 1) (hs : 0≤QRH.Record12518109Assembly.surplus v) :
    mainBaseExponent reflected M A v-balancedGeometrySide reflected A v+v 2≤A-M := by
  have hm₁ : max (v 1-v 0) 0≤v 1:=max_le (by linarith) hd
  have hm₀ : max (v 0-v 1) 0≤v 0:=max_le (by linarith) hc
  cases reflected
  · simp only [mainBaseExponent,balancedGeometrySide,Bool.false_eq_true,ite_false]
    rw [QRH.Record12518109Assembly.left_eq_old]
    dsimp only [Cycle61InitialMass.leftExponent]
    linarith [le_max_right (3*v 0-5*v 1-v 3) 0]
  · simp only [mainBaseExponent,balancedGeometrySide,ite_true]
    rw [QRH.Record12518109Assembly.right_eq_old]
    dsimp only [Cycle61InitialMass.rightExponent]
    linarith [le_max_right (3*v 1-5*v 0-v 3) 0]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem actual_main_base_payment (reflected : Bool) (s : Input ι) (modifier : Tuple ι→ℂ)
    (R seed : Ideal O) (K Z ξ M A : ℝ) (hZ : 1<Z)
    (q : SourceCoordinate s modifier R seed K Z ξ) :
    let v:=geometryExponents s modifier R seed K Z ξ q
    mainBaseExponent reflected M A v-balancedGeometrySide reflected A v+v 2≤A-M := by
  have hg:=CenteredMomentFirstSectors.commonLabels_data _ _ _ _ q.1.property
  apply main_base_payment
  · exact ideal_log_nonneg _ hg.1 Z hZ
  · exact ideal_log_nonneg _ hg.2.1 Z hZ
  · exact QRH.Record1252270103Source.High.CoupledFirst.actual_surplus_nonneg
      s modifier R seed K Z ξ hZ q

/-- This is the actual source label and original volume. In particular the
six amplification powers in the enlarged radius are not silently discarded. -/
theorem actual_main_radius_exponent (reflected : Bool) (s : Input ι) (modifier : Tuple ι→ℂ)
    (R seed : Ideal O) (Z M ξ a reserve : ℝ) (hZ : 1<Z) (hK : 0<Z^M)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s modifier R seed (Z^M) Z ξ hK bin)) :
    firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve
      (FirstFamily.firstLabel s modifier R seed (Z^M) Z ξ hK bin j)=
    Z^(mainBaseExponent reflected M (Real.logb Z (volume s))
      (geometryExponents s modifier R seed (Z^M) Z ξ j.1.val)+
        6*a+frequencyLoss Z 32 ξ+reserve) := by
  let l:=FirstFamily.firstLabel s modifier R seed (Z^M) Z ξ hK bin j
  let A:=Real.logb Z (volume s)
  let v:=geometryExponents s modifier R seed (Z^M) Z ξ j.1.val
  have hs:=FirstFamily.label_supported s modifier R seed (Z^M) Z ξ hK bin j
  have hV:volume s=Z^A:=(Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (volume_pos s)).symm
  have he:Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)=v 4 := by
    change Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)=
      Real.logb Z ((Ideal.span {ActualEisensteinCubic.primeSubsetGenerator
        (fun P : CommonIndex l.1.1 l.1.2=>P.val) l.2.val}).absNorm:ℝ)
    rw [first_projector_span]
  change firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l=_
  conv_lhs => rw [hV]
  rw [actual_main_radius_power reflected l hs.1 hs.2.1 hs.2.2 Z M A a ξ reserve hZ]
  change Z^(_)=Z^(mainBaseExponent reflected M A v+6*a+frequencyLoss Z 32 ξ+reserve)
  rw [he]
  congr 1
  have hc:Real.logb Z (l.1.1.absNorm:ℝ)=v 0:=rfl
  have hd:Real.logb Z (l.1.2.absNorm:ℝ)=v 1:=rfl
  have hr:Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)=v 3:=rfl
  cases reflected <;> simp only [Bool.false_eq_true,ite_false,ite_true,hc,hd,hr,mainBaseExponent] <;> ring

/-- One fixed threshold pays the annular prefactor. It precedes the moving
pool, scale exponent and every selected source label. -/
theorem eventual_main_weight (ell radiusMax ε : ℝ) (hell : 0<ell)
    (hmax : 0≤radiusMax) (hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀(P : Finset (Ideal O))(a mesh loss BD Bsource : ℝ)(depth : ℕ),
      FixedCellPoolData P Z a ell mesh loss BD Bsource depth →
    ∀ H0 radius : ℝ, 0<H0 → 0≤radius+6*a → radius+6*a≤radiusMax →
      0≤((bands H0).card:ℝ)*(P.card:ℝ)⁻¹*((radius+6*a)/ell) ∧
      ((bands H0).card:ℝ)*(P.card:ℝ)⁻¹*((radius+6*a)/ell)≤Z^(-a+loss+ε) := by
  have he:∀ᶠZ : ℝ in atTop,7*(radiusMax/ell)≤Z^ε:=
    (tendsto_rpow_atTop hε).eventually (eventually_ge_atTop _)
  filter_upwards [he,eventually_gt_atTop (1:ℝ)] with Z he hZ
  refine ⟨hZ,?_⟩
  intro P a mesh loss BD Bsource depth hpool H0 radius hH hr0 hr
  have hh:=mul_le_mul (bands_card H0 hH) hpool.reciprocal
    (inv_nonneg.mpr (Nat.cast_nonneg _)) (by norm_num : (0:ℝ)≤7)
  have hh':=((mul_le_mul hh (div_le_div_of_nonneg_right hr hell.le)
    (div_nonneg hr0 hell.le) (by positivity : (0:ℝ)≤7*Z^(-a+loss))))
  refine ⟨by positivity,?_⟩
  calc
    _≤7*Z^(-a+loss)*(radiusMax/ell):=hh'
    _=(7*(radiusMax/ell))*Z^(-a+loss):=by ring
    _≤Z^ε*Z^(-a+loss):=mul_le_mul_of_nonneg_right he (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
    _=Z^(-a+loss+ε):=by rw [←Real.rpow_add (zero_lt_one.trans hZ)];congr 1;ring


/-- The source-width gap pays all six enlargement powers. The actual pool
then leaves one full amplification power, in both orientations. -/
theorem main_remainder_power_payment (reflected : Bool)
    (Z M A Amax a omega B epsilonMass epsilonZero loss gap saving weight : ℝ)
    (v : Fin 5→ℝ) (hZ : 1<Z) (hA : A≤Amax) (hAmax : 0≤Amax)
    (hzero : 0≤epsilonZero)
    (hbase : mainBaseExponent reflected M A v-balancedGeometrySide reflected A v+v 2≤A-M)
    (hweight : weight≤Z^(-a+loss))
    (hgap : A+6*a+gap≤M)
    (herr : omega+B*epsilonMass+loss+epsilonZero*Amax≤gap) :
    weight*Z^(B*epsilonMass+(mainBaseExponent reflected M A v+6*a+omega+epsilonZero*A)-
      balancedGeometrySide reflected A v)≤Z^(-a-v 2) ∧
    weight*Z^(B*epsilonMass+(mainBaseExponent reflected M A v+6*a+omega-saving)-
      balancedGeometrySide reflected A v)≤Z^(-a-saving-v 2) := by
  have pay (power target : ℝ) (he : (-a+loss)+power≤target) :
      weight*Z^power≤Z^target := by
    calc
      _≤Z^(-a+loss)*Z^power:=mul_le_mul_of_nonneg_right hweight
        (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
      _=Z^((-a+loss)+power):=(Real.rpow_add (zero_lt_one.trans hZ) _ _).symm
      _≤Z^target:=Real.rpow_le_rpow_of_exponent_le hZ.le he
  constructor
  · apply pay
    have he:=mul_le_mul_of_nonneg_left hA hzero
    linarith only [hbase,hgap,herr,he]
  · apply pay
    have he:=mul_nonneg hzero hAmax
    linarith only [hbase,hgap,herr,he]

end
end QRH.Record1252270103Source.MarkedMainRemainder
#print axioms QRH.Record1252270103Source.MarkedMainRemainder.main_base_payment
#print axioms QRH.Record1252270103Source.MarkedMainRemainder.actual_main_base_payment
#print axioms QRH.Record1252270103Source.MarkedMainRemainder.actual_main_radius_exponent
#print axioms QRH.Record1252270103Source.MarkedMainRemainder.eventual_main_weight
#print axioms QRH.Record1252270103Source.MarkedMainRemainder.main_remainder_power_payment
