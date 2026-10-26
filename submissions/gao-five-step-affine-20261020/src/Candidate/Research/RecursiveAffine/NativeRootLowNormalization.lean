/- Exact raw root LOW source normalization with native whole-forest count.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootCoefficientAbsorption

set_option autoImplicit false
set_option maxHeartbeats 350000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Filter Cycle153SourceReturn Cycle153JointCount Cycle153Reachable Cycle153SourceSchedule

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M ≤ H}{C : SourceContext (α:=alpha) M H}

/-- Normalize the literal root AtState scale exactly once. The true
native forest count pays the returned term; the OLD exponent is compared
explicitly to the native target. No raw source factor is dropped and no
second outer factor is applied to the already raw-priced forest. -/
theorem actual_root_low_raw_normalization
    {Bsrc : ℝ}{boxes : ℕ→Finset (Fin 4→ℤ)}
    (receipt : NativeRootForestReceipt (hH:=hH) (C:=C) Bsrc boxes)
    (amp driverDelta driverError target rawOldExponent oldConstant Kreturn control cost : ℝ)
    (hdriver : 0 ≤ driverError)(hold : 0 ≤ oldConstant)(hcontrol : 0 ≤ control)
    (hcount : Kreturn*receipt.family.value ≤ C.globalBase)
    (hOldExponent : rawOldExponent ≤ 1+3*driverDelta-amp+driverError+target)
    (hsource : C.globalBase^(1+3*driverDelta-amp+driverError)*cost ≤
      oldConstant*control*C.globalBase^rawOldExponent+
        Kreturn*control*receipt.family.value) :
    cost ≤ (oldConstant*C.globalBase^target+C.globalBase^(amp-3*driverDelta))*control := by
  have hZ : 0<C.globalBase:=zero_lt_one.trans C.globalBase_gt_one
  let outer:=1+3*driverDelta-amp+driverError
  have houter : 0<C.globalBase^outer:=Real.rpow_pos_of_pos hZ _
  apply le_of_mul_le_mul_left ?_ houter
  have hOld:=Real.rpow_le_rpow_of_exponent_le C.globalBase_gt_one.le hOldExponent
  have hreturn:=mul_le_mul_of_nonneg_left hcount hcontrol
  have hreturnPower : C.globalBase ≤ C.globalBase^outer*C.globalBase^(amp-3*driverDelta) := by
    rw [←Real.rpow_add hZ]
    calc
      _=C.globalBase^(1:ℝ):=(Real.rpow_one _).symm
      _ ≤ _:=Real.rpow_le_rpow_of_exponent_le C.globalBase_gt_one.le (by dsimp only [outer];linarith only [hdriver])
  calc
    _ ≤ oldConstant*control*C.globalBase^rawOldExponent+Kreturn*control*receipt.family.value:=hsource
    _ ≤ oldConstant*control*C.globalBase^(outer+target)+control*C.globalBase:=by
      exact add_le_add (mul_le_mul_of_nonneg_left hOld (mul_nonneg hold hcontrol)) (by nlinarith only [hreturn])
    _ ≤ oldConstant*control*C.globalBase^(outer+target)+control*(C.globalBase^outer*C.globalBase^(amp-3*driverDelta)):=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hreturnPower hcontrol)
    _ = _:=by rw [Real.rpow_add hZ];ring

/-- One fixed zero-height exponent precedes both native class licences
and the actual LOW source coefficient. Only the cutoff depends on those
constants. At that cutoff, EACH actual physical source receipt is paid
and normalized, so no global root forest maximum is needed. -/
theorem eventual_actual_root_low_raw_normalization
    (M : Ideal O)[NeZero M](H : Subgroup (O⧸M)ˣ)(hH : RayOrthogonality.globalUnits M ≤ H)
    (eta : Character)(Bsrc Bnorm cap : ℝ)(N : ℕ)
    (hBsrc : 0 ≤ Bsrc)(hBnorm : 0 ≤ Bnorm)(hcap : 0<cap)
    (hbudget : ∀d : SuffixDepth 4,(rootHistoryDepth d:ℝ)*Bsrc ≤ Bnorm) :
    ∃tau : ℝ,0<tau ∧ tau ≤ cap ∧
    ∀Kclass : ℝ,0 ≤ Kclass → ∀Kreturn : ℝ,0 ≤ Kreturn →
    ∀ᶠ Z : ℝ in atTop,1<Z ∧
    ∀{alpha : Type}[Fintype alpha][DecidableEq alpha](C : SourceContext (α:=alpha) M H),
    C.globalBase=Z → C.etaSeed=eta → C.Bnorm=Bnorm → C.highClassCap=Kclass →
    0 ≤ C.Tz → C.Tz ≤ Z^tau →
    ∀receipt : NativeRootForestReceipt (hH:=hH) (C:=C) Bsrc (fun _=>rootNativeDyadBox Z N),
    ∀(amp driverDelta driverError target rawOldExponent oldConstant control cost : ℝ),
    0 ≤ driverError → 0 ≤ oldConstant → 0 ≤ control →
    rawOldExponent ≤ 1+3*driverDelta-amp+driverError+target →
    Z^(1+3*driverDelta-amp+driverError)*cost ≤
      oldConstant*control*Z^rawOldExponent+Kreturn*control*receipt.family.value →
    cost ≤ (oldConstant*Z^target+Z^(amp-3*driverDelta))*control := by
  obtain ⟨tau,htau,hcapTau,hpaid⟩:=actual_root_forest_absorption_with_coefficient M H hH
    eta Bsrc Bnorm cap N hBsrc hBnorm hcap hbudget
  refine ⟨tau,htau,hcapTau,?_⟩
  intro Kclass hKclass Kreturn hKreturn
  filter_upwards [hpaid Kclass hKclass Kreturn hKreturn] with Z hz
  refine ⟨hz.1,?_⟩
  intro alpha _ _ C hbase heta hnorm hclass hT0 hT receipt amp driverDelta driverError
    target rawOldExponent oldConstant control cost hdriver hold hcontrol hOld hsource
  have hcount:=hz.2 C hbase heta hnorm hclass hT0 hT receipt
  subst Z
  exact actual_root_low_raw_normalization receipt amp driverDelta driverError target rawOldExponent
    oldConstant Kreturn control cost hdriver hold hcontrol hcount hOld hsource

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_root_low_raw_normalization

#print axioms OAI.SevenEighths.Cycle153RegionalLow.eventual_actual_root_low_raw_normalization
