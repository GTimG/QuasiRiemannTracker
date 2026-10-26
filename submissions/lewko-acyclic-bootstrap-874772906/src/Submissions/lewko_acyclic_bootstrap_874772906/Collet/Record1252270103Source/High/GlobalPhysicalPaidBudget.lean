/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The literal HIGH source budget pays restoration, the buffered height and
three annular allocation losses with fixed constants. No row bound is assumed. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalPaidSome
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open Record12518109Natural QRH.Record1252270103Restoration QRH.Record1252270103KernelMass

def cofactorFixedRestoration (δ B : ℝ) : ℝ :=
  4*(holeDeletionMass*(eulerBound 5 (1/2+δ/(B+1))+eulerBound 432 (1/2+δ/(B+1))))^2

def bufferedHeightConstant (I J : ℕ) : ℝ := (1+2*Real.pi+6*(I+1:ℕ))^J

theorem cofactor_restoration_power (δ B Z : ℝ)(hZ:0≤Z) :
    cofactorRestorationCost δ B Z=cofactorFixedRestoration δ B*Z^(2*δ) := by
  let k:=eulerBound 5 (1/2+δ/(B+1))+eulerBound 432 (1/2+δ/(B+1))
  have hh:(holeDeletionMass*(k*Z^δ))^2=(holeDeletionMass*k)^2*Z^(2*δ) := by
    rw [←mul_assoc,mul_pow,←Real.rpow_mul_natCast hZ]
    congr 2
    norm_num
    ring
  change 4*(holeDeletionMass*(k*Z^δ))^2=(4*(holeDeletionMass*k)^2)*Z^(2*δ)
  rw [hh]
  ring

theorem annular_loss_constant (N:ℕ)(Z upper ν:ℝ)(hZ:1<Z)(hu:1≤upper)(hν:ν≤1) :
    Z^(ν*(3*(N:ℝ)*Real.logb Z upper))≤upper^(3*N) := by
  have hlog:0≤Real.logb Z upper:=Real.logb_nonneg hZ hu
  have hn:0≤3*(N:ℝ)*Real.logb Z upper:=by positivity
  calc
    _≤Z^(3*(N:ℝ)*Real.logb Z upper):=
      Real.rpow_le_rpow_of_exponent_le hZ.le (by nlinarith only [hν,hn])
    _=(Z^Real.logb Z upper)^(3*N):=by
      rw [←Real.rpow_mul_natCast (zero_lt_one.trans hZ).le]
      push_cast
      congr 1
      ring
    _=upper^(3*N):=by rw [Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (zero_lt_one.trans_le hu)]

/-- All constants are fixed before the moving density and source exponent. -/
theorem restoration_height_annular (N I J:ℕ)(δ B τ upper Z ν E:ℝ)
    (hZ:1<Z)(hτ:0≤τ)(hu:1≤upper)(hν:ν≤1) :
    cofactorRestorationCost δ B Z*(1+rawGeometryHeight Z τ I)^J*
        Z^(ν*(3*(N:ℝ)*Real.logb Z upper)+E)≤
      cofactorFixedRestoration δ B*bufferedHeightConstant I J*upper^(3*N)*
        Z^(2*δ+τ*(J:ℝ)+E) := by
  have hz:=zero_lt_one.trans hZ
  have hh:=raw_geometry_height_power hZ.le hτ I J
  change (1+rawGeometryHeight Z τ I)^J≤bufferedHeightConstant I J*Z^(τ*(J:ℝ)) at hh
  have ha:=annular_loss_constant N Z upper ν hZ hu hν
  rw [cofactor_restoration_power δ B Z hz.le,Real.rpow_add hz]
  have hrest:0≤cofactorFixedRestoration δ B:=by unfold cofactorFixedRestoration;positivity
  have hh0:0≤bufferedHeightConstant I J:=by unfold bufferedHeightConstant;positivity
  calc
    _≤(cofactorFixedRestoration δ B*Z^(2*δ))*(bufferedHeightConstant I J*Z^(τ*(J:ℝ)))*
        (upper^(3*N)*Z^E) := by gcongr
    _=_:=by
      rw [show 2*δ+τ*(J:ℝ)+E=(2*δ+τ*(J:ℝ))+E by ring,
        Real.rpow_add hz,Real.rpow_add hz]
      ring

/-- This is the exact paid-Some/paid-Natural budget, with every finite box and
original profile factor left in the fixed multiplicative constant. -/
theorem paid_high_reserve (N I J:ℕ)(δ B τ upper Z ν exponent pref saving:ℝ)
    (C profileCost geometry profileControl box:ℝ)
    (hZ:1<Z)(hτ:0≤τ)(hu:1≤upper)(hν:ν≤1)
    (hC:0≤C)(hp:0≤profileCost)(hg:0≤geometry)(hcontrol:0≤profileControl)(hbox:0≤box)
    (hpaid:pref+2*δ+τ*(J:ℝ)+exponent≤-saving) :
    (C*Z^pref*profileCost)*((max 1 profileCost)^2*(geometry*
      cofactorRestorationCost δ B Z*profileControl*box*
      (1+rawGeometryHeight Z τ I)^J*
      Z^(exponent+ν*(3*(N:ℝ)*Real.logb Z upper))))≤
    (C*profileCost*(max 1 profileCost)^2*cofactorFixedRestoration δ B*
      bufferedHeightConstant I J*upper^(3*N)*box)*geometry*profileControl*Z^(-saving) := by
  have hz:=zero_lt_one.trans hZ
  have h:=restoration_height_annular N I J δ B τ upper Z ν exponent hZ hτ hu hν
  have hfac:0≤C*profileCost*(max 1 profileCost)^2*geometry*profileControl*box:=by positivity
  have hh:=mul_le_mul_of_nonneg_left h (mul_nonneg hfac (Real.rpow_nonneg hz.le pref))
  calc
    _=(C*profileCost*(max 1 profileCost)^2*geometry*profileControl*box*Z^pref)*
        (cofactorRestorationCost δ B Z*(1+rawGeometryHeight Z τ I)^J*
          Z^(ν*(3*(N:ℝ)*Real.logb Z upper)+exponent)) := by rw [add_comm exponent];ring
    _≤_:=hh
    _=(C*profileCost*(max 1 profileCost)^2*cofactorFixedRestoration δ B*
        bufferedHeightConstant I J*upper^(3*N)*box)*geometry*profileControl*
          Z^(pref+2*δ+τ*(J:ℝ)+exponent) := by
      conv_rhs => rw [show pref+2*δ+τ*(J:ℝ)+exponent=pref+(2*δ+τ*(J:ℝ)+exponent) by ring,Real.rpow_add hz]
      ring
    _≤_:=by
      have hr:0≤cofactorFixedRestoration δ B:=by unfold cofactorFixedRestoration;positivity
      have hh:0≤bufferedHeightConstant I J:=by unfold bufferedHeightConstant;positivity
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le hpaid) (by positivity)

/-- The density interpolation has no additional loss beyond the two displayed
nonnegative errors. This applies uniformly to every buffered HIGH density. -/
theorem high_error_ledger (ρ omega err errv fee reserve other pref δ τ:ℝ)(J:ℕ)(saving:ℝ)
    (hρ0:0≤ρ)(hρ1:ρ≤1)(homega:0≤omega)(herr:0≤err)
    (hbudget:pref+2*δ+τ*(J:ℝ)+omega+err+errv+other+saving≤fee+reserve) :
    pref+2*δ+τ*(J:ℝ)+((1-ρ)*omega+ρ*err+errv-(fee+reserve)+other)≤-saving := by
  have h₁:=mul_nonneg hρ0 homega
  have h₂:=mul_nonneg (sub_nonneg.mpr hρ1) herr
  nlinarith only [h₁,h₂,hbudget]
end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.cofactor_restoration_power
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.annular_loss_constant
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.restoration_height_annular
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.paid_high_reserve
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.high_error_ledger
