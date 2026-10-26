/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual first MAIN scalar admissions, with the counted common radical distinct
from the active conductor. No source estimate is assumed. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.MarkedMainRemainderScalar

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Low.InitialRemainder
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily Cycle61InitialMass ActualEisensteinCubic
open CenteredMomentFirstExceptionalPrefactor CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstAnnularMajorant
open QRH.Record1252270103Source.Admission
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open QRH.Record1252270103Source.High.CoupledFirst
open QRH.Record1252270103Source.MarkedMainRemainder
open QRH.Record1252270103Source.Pool
open Record12518109Natural (balancedGeometrySide)
local notation "O" => HeckeFamily.O

def weightConstant (ell : ℝ) : ℝ := 224/ell
def mainWeight (P : Finset (Ideal O)) (ell H0 radius a : ℝ) : ℝ :=
  ((bands H0).card:ℝ)*(P.card:ℝ)⁻¹*((radius+6*a)/ell)

theorem weightConstant_pos (ell : ℝ) (hell : 0<ell) : 0<weightConstant ell := by
  unfold weightConstant
  positivity

/-- This is a fixed multiplicative constant, not an extra exponent loss.
All pool/cardinality parameters remain moving. -/
theorem fixed_pool_weight (P : Finset (Ideal O))
    (Z a ell mesh loss BD Bsource : ℝ) (depth : ℕ)
    (hpool : FixedCellPoolData P Z a ell mesh loss BD Bsource depth)
    (hell : 0<ell) (H0 radius : ℝ) (hH : 0<H0)
    (hr0 : 0≤radius+6*a) (hr : radius+6*a≤32) :
    0≤mainWeight P ell H0 radius a ∧
    mainWeight P ell H0 radius a≤weightConstant ell*Z^(-a+loss) := by
  have hZ : 0<Z:=zero_lt_one.trans hpool.scale_gt_one
  have hh:=mul_le_mul (bands_card H0 hH) hpool.reciprocal
    (inv_nonneg.mpr (Nat.cast_nonneg _)) (by norm_num : (0:ℝ)≤7)
  have hh':=mul_le_mul hh (div_le_div_of_nonneg_right hr hell.le)
    (div_nonneg hr0 hell.le) (by positivity : (0:ℝ)≤7*Z^(-a+loss))
  refine ⟨by unfold mainWeight; positivity,?_⟩
  calc
    _≤7*Z^(-a+loss)*(32/ell):=hh'
    _=weightConstant ell*Z^(-a+loss):=by unfold weightConstant; ring

theorem normalized_pool_weight (P : Finset (Ideal O))
    (Z a ell mesh loss BD Bsource : ℝ) (depth : ℕ)
    (hpool : FixedCellPoolData P Z a ell mesh loss BD Bsource depth)
    (hell : 0<ell) (H0 radius : ℝ) (hH : 0<H0)
    (hr0 : 0≤radius+6*a) (hr : radius+6*a≤32) :
    0≤mainWeight P ell H0 radius a/weightConstant ell ∧
    mainWeight P ell H0 radius a/weightConstant ell≤Z^(-a+loss) := by
  have hh:=fixed_pool_weight P Z a ell mesh loss BD Bsource depth hpool hell H0 radius hH hr0 hr
  have hc:=weightConstant_pos ell hell
  exact ⟨div_nonneg hh.1 hc.le,(div_le_iff₀ hc).mpr (by simpa only [mul_comm] using hh.2)⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The radical on the left is exactly geometryExponents(...,2), hence
log of commonRadical. It is not the active-conductor exponent (...,3). -/
theorem actual_log_radius_payment (reflected : Bool) (s : Input ι)
    (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O)
    (Z M ξ a reserve : ℝ) (hZ : 1<Z) (hK : 0<Z^M)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s modifier R seed (Z^M) Z ξ hK bin)) :
    let v:=geometryExponents s modifier R seed (Z^M) Z ξ j.1.val
    let A:=Real.logb Z (volume s)
    Real.logb Z (firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve
      (FirstFamily.firstLabel s modifier R seed (Z^M) Z ξ hK bin j))
      -balancedGeometrySide reflected A v+v 2≤A-M+6*a+frequencyLoss Z 32 ξ+reserve := by
  dsimp only
  rw [actual_main_radius_exponent reflected s modifier R seed Z M ξ a reserve hZ hK bin j,
    Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  have hb:=actual_main_base_payment reflected s modifier R seed (Z^M) Z ξ M
    (Real.logb Z (volume s)) hZ j.1.val
  dsimp only at hb
  linarith only [hb]

/-- Three allowances in the true volume gap leave one allowance after
paying the visible mass, zero, pool, frequency and reserve errors. -/
theorem remainder_power_payment
    (Z A a allowance omega B epsMass epsZero loss saving weight Hlog side radical : ℝ)
    (hZ : 1<Z) (ha : 0≤a) (he : 0≤allowance) (hz : 0≤epsZero)
    (hlog : Hlog-side+radical≤A-1+6*a+omega)
    (hgap : A+6*a+3*allowance≤1)
    (herr : omega+B*epsMass+loss+epsZero≤2*allowance)
    (hweight : weight≤Z^(-a+loss)) :
    weight*Z^(B*epsMass+(Hlog+epsZero*A)-side)≤Z^((-a-allowance)-radical) ∧
    weight*Z^(B*epsMass+(Hlog-saving)-side)≤Z^((-a-allowance-saving)-radical) := by
  have hA : A≤1:=by linarith only [hgap,ha,he]
  have hzA : epsZero*A≤epsZero:=by simpa using mul_le_mul_of_nonneg_left hA hz
  have pay (power target : ℝ) (hh : (-a+loss)+power≤target) : weight*Z^power≤Z^target := by
    calc
      _≤Z^(-a+loss)*Z^power:=mul_le_mul_of_nonneg_right hweight
        (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
      _=Z^((-a+loss)+power):=(Real.rpow_add (zero_lt_one.trans hZ) _ _).symm
      _≤Z^target:=Real.rpow_le_rpow_of_exponent_le hZ.le hh
  constructor
  · apply pay
    linarith only [hlog,hgap,herr,hzA]
  · apply pay
    linarith only [hlog,hgap,herr,hz]

/-- Literal hpzero/hptail for selected_remainder_sums. No chosen first
Schwartz profile enters this scalar statement, so it stays independent of
the two plain profiles used by the actual allocation estimates. -/
theorem actual_remainder_admissions (reflected : Bool) (s : Input ι)
    (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ) (R seed : Ideal O)
    (Z ξ a reserve allowance B epsMass epsZero loss saving weight : ℝ)
    (hZ : 1<Z) (hK : 0<Z^(1:ℝ))
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s modifier R seed (Z^(1:ℝ)) Z ξ hK bin))
    (ha : 0≤a) (he : 0≤allowance) (hz : 0≤epsZero)
    (hgap : Real.logb Z (volume s)+6*a+3*allowance≤1)
    (herr : frequencyLoss Z 32 ξ+reserve+B*epsMass+loss+epsZero≤2*allowance)
    (hweight : weight≤Z^(-a+loss)) :
    let v:=geometryExponents s modifier R seed (Z^(1:ℝ)) Z ξ j.1.val
    let A:=Real.logb Z (volume s)
    let Hlog:=Real.logb Z (firstMainRadius reflected (Z^(1:ℝ)) (volume s) Z ξ (3*a) reserve
      (FirstFamily.firstLabel s modifier R seed (Z^(1:ℝ)) Z ξ hK bin j))
    weight*Z^(B*epsMass+(Hlog+epsZero*A)-balancedGeometrySide reflected A v)
      ≤Z^((-a-allowance)-v 2) ∧
    weight*Z^(B*epsMass+(Hlog-saving)-balancedGeometrySide reflected A v)
      ≤Z^((-a-allowance-saving)-v 2) := by
  dsimp only
  apply remainder_power_payment Z (Real.logb Z (volume s)) a allowance
    (frequencyLoss Z 32 ξ+reserve) B epsMass epsZero loss saving weight _ _ _ hZ ha he hz
  · have hh:=actual_log_radius_payment reflected s modifier R seed Z 1 ξ a reserve hZ hK bin j
    dsimp only at hh
    linarith only [hh]
  · exact hgap
  · exact herr
  · exact hweight

end
end QRH.Record1252270103Source.Low.InitialRemainder
#print axioms QRH.Record1252270103Source.Low.InitialRemainder.weightConstant_pos
#print axioms QRH.Record1252270103Source.Low.InitialRemainder.fixed_pool_weight
#print axioms QRH.Record1252270103Source.Low.InitialRemainder.normalized_pool_weight
#print axioms QRH.Record1252270103Source.Low.InitialRemainder.actual_log_radius_payment
#print axioms QRH.Record1252270103Source.Low.InitialRemainder.remainder_power_payment
#print axioms QRH.Record1252270103Source.Low.InitialRemainder.actual_remainder_admissions
