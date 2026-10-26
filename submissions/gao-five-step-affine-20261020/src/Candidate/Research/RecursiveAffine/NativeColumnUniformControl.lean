/- Fixed source constants and dynamic physical bin controls remain distinct.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativePaidColumnsNativeForm
import Candidate.Cycle63.Physical.InitialHeight

set_option autoImplicit false
set_option maxHeartbeats 150000
namespace OAI.SevenEighths.Cycle153ActualColumn
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CenteredMomentEnergyBands CenteredMomentFirstAmplificationChoice
open CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy CenteredMomentAllocatedRayDictionary

/-- This coefficient depends only on the fixed finite source schedule.
The moving bin's geometryHighFactor is not part of it. -/
def nativeColumnSourceConstant
    (Nbudget : ℕ)(Cs Cpay Kterminal Kchild Kcol Cdirect C₀ C₁ Kdirect : ℝ) : ℝ :=
  (2*(9/4:ℝ)^2*Cs^(4*Nbudget))*QuadraticInitialBound.diagonalControl ballProfile*
    (Kcol*Cpay^Nbudget*(Kterminal+Kchild)+Kdirect*Cdirect^Nbudget*(C₀+C₁))

/-- The original finite profile/height family controls BOTH branches.
The physical first-bin factor is multiplied only after this bound, and
stays an explicit part of the dynamic source control. -/
theorem native_shared_column_uniform_control
    (Nbudget currentCard : ℕ)(Cs Cpay Kterminal Kchild Kcol Cdirect C₀ C₁ Kdirect : ℝ)
    (controlsWide controlsDirect : Finset (ℕ×ℕ))(degreeWide degreeDirect : ℕ)
    (p : Profiles (1/4) (9/4))(t height epsShell T physical : ℝ)
    (hcard : currentCard≤Nbudget)(hCs : 1≤Cs)(hCpay : 1≤Cpay)(hCdirect : 1≤Cdirect)
    (hKt : 0≤Kterminal)(hKchild : 0≤Kchild)(hKcol : 0≤Kcol)
    (hC₀ : 0≤C₀)(hC₁ : 0≤C₁)(hKdirect : 0≤Kdirect)
    (hheight : 0≤height)(hT : 0≤T)(hphysical : 0≤physical) :
    nativeSharedColumnFixed Nbudget currentCard Cs Cpay Kterminal Kchild Kcol Cdirect C₀ C₁ Kdirect
      controlsWide controlsDirect degreeWide degreeDirect p t height epsShell T*physical≤
    nativeColumnSourceConstant Nbudget Cs Cpay Kterminal Kchild Kcol Cdirect C₀ C₁ Kdirect*
      (p.control (controlsWide∪controlsDirect))^2*(1+|t|+height)^(max degreeWide degreeDirect)*
      (2*T)^(3*epsShell)*physical := by
  have hZC:=zero_le_one.trans hCs
  have hpay0:=zero_le_one.trans hCpay
  have hdir0:=zero_le_one.trans hCdirect
  have hH : 1≤1+|t|+height := by linarith only [abs_nonneg t,hheight]
  have hwideC : (p.control controlsWide)^2≤(p.control (controlsWide∪controlsDirect))^2 :=
    pow_le_pow_left₀ (p.control_nonneg _) (Cycle63Physical.profile_control_mono p Finset.subset_union_left) 2
  have hdirC : (p.control controlsDirect)^2≤(p.control (controlsWide∪controlsDirect))^2 :=
    pow_le_pow_left₀ (p.control_nonneg _) (Cycle63Physical.profile_control_mono p Finset.subset_union_right) 2
  have hwideH:=pow_le_pow_right₀ hH (le_max_left degreeWide degreeDirect)
  have hdirH:=pow_le_pow_right₀ hH (le_max_right degreeWide degreeDirect)
  have hwideA : Kcol*Cpay^currentCard*(Kterminal+Kchild)≤Kcol*Cpay^Nbudget*(Kterminal+Kchild) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hCpay hcard) hKcol)
      (add_nonneg hKt hKchild)
  have hdirA : Kdirect*Cdirect^currentCard*(C₀+C₁)≤Kdirect*Cdirect^Nbudget*(C₀+C₁) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hCdirect hcard) hKdirect)
      (add_nonneg hC₀ hC₁)
  have hwide : Kcol*Cpay^currentCard*(Kterminal+Kchild)*(p.control controlsWide)^2*(1+|t|+height)^degreeWide≤
      Kcol*Cpay^Nbudget*(Kterminal+Kchild)*(p.control (controlsWide∪controlsDirect))^2*
        (1+|t|+height)^(max degreeWide degreeDirect) := by
    exact mul_le_mul (mul_le_mul hwideA hwideC (sq_nonneg _) (by positivity)) hwideH
      (by positivity) (by positivity)
  have hdir : Kdirect*Cdirect^currentCard*(C₀+C₁)*(p.control controlsDirect)^2*(1+|t|+height)^degreeDirect≤
      Kdirect*Cdirect^Nbudget*(C₀+C₁)*(p.control (controlsWide∪controlsDirect))^2*
        (1+|t|+height)^(max degreeWide degreeDirect) := by
    exact mul_le_mul (mul_le_mul hdirA hdirC (sq_nonneg _) (by positivity)) hdirH
      (by positivity) (by positivity)
  have hsum:=add_le_add hwide hdir
  have hd:=QuadraticInitialBound.diagonalControl_nonneg ballProfile
  have hfront : 0≤(2*(9/4:ℝ)^2*Cs^(4*Nbudget))*QuadraticInitialBound.diagonalControl ballProfile := by positivity
  have hpaid:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hfront)
      (Real.rpow_nonneg (by positivity : 0≤2*T) (3*epsShell))) hphysical
  unfold nativeSharedColumnFixed nativeColumnSourceConstant
  convert hpaid using 1 <;> ring

end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.native_shared_column_uniform_control
