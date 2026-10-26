/- Copyright (c) 2026 Hailey Collet; source-preserving continuation
modifications (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.PhysicalStepCoordinates
import Candidate.Research.RecursiveAffine.PhysicalChildGeometry
import Candidate.Research.RecursiveAffine.PhysicalMaskBridge

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CenteredMomentEnergyBands Cycle153Geometry Cycle153ReachableGeometry

variable {α : Type} [Fintype α] [DecidableEq α]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {C : SourceContext (α:=α) M H} {j : Fin 4}

/-- The next source's parent unit is the actual current unit. Appending
this source's reduction triple leaves that earlier quantity unchanged. -/
theorem physical_next_parent_unit (j : Fin 4) (hj : j.val<3)
    (x : Fin 14→ℝ) (V Red ell : ℝ) :
    sourceParentUnit (nextInner j hj) (extendCoordinates x (nextInner j hj) V Red ell)=
      modelUnit j x := by
  fin_cases j <;> norm_num at hj
  all_goals simp [sourceParentUnit,nextInner,extendCoordinates,modelUnit,
    Coordinates.U0,Coordinates.U1,Coordinates.U2,Coordinates.U3,
    Coordinates.b,Coordinates.V0,Coordinates.V1,Coordinates.V2,Coordinates.V3,
    Coordinates.Red0,Coordinates.Red1,Coordinates.Red2,Coordinates.Red3,
    Coordinates.ell0,Coordinates.ell1,Coordinates.ell2,Coordinates.ell3,
    Coordinates.a0,Coordinates.a1,Coordinates.a2,
    Coordinates.gap0,Coordinates.gap1,Coordinates.gap2,
    Coordinates.capA1,Coordinates.capA2,Coordinates.A0,Coordinates.A1,Coordinates.A2,
    Coordinates.z0,Coordinates.z1,Coordinates.z2,Coordinates.rootSlack,
    Coordinates.d0,Coordinates.d1]

/-- Failure of the full genuine reflection test gives the next balanced
window. This uses the native balance theorem with its actual capacity
gate and half-width margin; no short-side bound is assumed. -/
theorem actual_continuation_balance {n1 n2 z u : ℝ}
    (hz : 0≤z) (hwide : (397/1000:ℝ)≤u)
    (hover : n1+n2+6*Cycle63.Optimization.slotPrice*z≤u+19/5000)
    (hnot : ¬(n1+n2+6*Cycle63.Optimization.slotPrice*z≤u+19/5000 ∧
      (max 0 (u-n2+1/10000)+n1+6*Cycle63.Optimization.slotPrice*z+19/5000≤u ∨
       max 0 (u-n1+1/10000)+n2+6*Cycle63.Optimization.slotPrice*z+19/5000≤u))) :
    |n1-n2|≤6*Cycle63.Optimization.slotPrice*z+u/100 := by
  have hp := not_or.mp (fun h=>hnot ⟨hover,h⟩)
  have hk : 0≤Cycle63.Optimization.slotPrice := by
    linarith [Cycle63.Optimization.slotPrice_mem.1]
  have hkz : 0≤6*Cycle63.Optimization.slotPrice*z := by positivity
  have hw : (2:ℝ)*(19/5000)≤u := by linarith only [hwide]
  have hp1 := not_le.mp hp.1
  have hp2 := not_le.mp hp.2
  have hb : |n1-n2|≤6*Cycle63.Optimization.slotPrice*z+((1/10000:ℝ)+19/5000) := by
    rw [abs_le]
    constructor
    · rcases le_total 0 (u-n2+(1/10000:ℝ)) with hh | hh
      · rw [max_eq_right hh] at hp1
        linarith only [hp1]
      · rw [max_eq_left hh] at hp1
        exfalso
        linarith only [hover,hp1,hw,hh,hkz]
    · rcases le_total 0 (u-n1+(1/10000:ℝ)) with hh | hh
      · rw [max_eq_right hh] at hp2
        linarith only [hp2]
      · rw [max_eq_left hh] at hp2
        exfalso
        linarith only [hover,hp2,hw,hh,hkz]
  have hs : (1/10000:ℝ)+19/5000≤u/100 := by linarith only [hwide]
  linarith only [hb,hs]

/-- The native increment is recorded at the literal next coordinate
triple. The same actual puncture is retained and every finite pad is paid
in the historical error allowance. -/
theorem actual_continuation_puncture_history (N : ReachableNode C j)
    (hj : j.val<3) (V Red ell pad : ℝ) (P : Ideal O)
    (hinc : Real.logb C.globalBase (P.absNorm:ℝ)≤
      Real.logb C.globalBase (N.state.puncture.absNorm:ℝ)+V+Red+pad)
    (hpad : pad≤1/1000000000000000) :
    Real.logb C.globalBase (P.absNorm:ℝ)≤
      modelMissing (nextInner j hj) (extendCoordinates N.coordinates (nextInner j hj) V Red ell)+
      modelReduction (nextInner j hj) (extendCoordinates N.coordinates (nextInner j hj) V Red ell)+
      (((nextInner j hj).val:ℝ)+1)/1000000000000000 := by
  exact puncture_history_step N (extendCoordinates N.coordinates (nextInner j hj) V Red ell)
    (by rfl) P V Red pad hinc (physical_next_history j hj N.coordinates V Red ell) hpad

/-- Arithmetic construction of the actual next regional geometry from
the native measured recurrences and the literal continuation tests. The
inherited regional plane, amplifier positivity, unit floor, reflection
capacity, balance and all rounded facts are derived here. No recursive
energy, returned-count estimate or desired next-source fact is supplied. -/
def childGeometryOfActualContinuation (N : ReachableNode C j) (hj : j.val<3)
    (u V Red ell : ℝ) (slots : Finset α) (X1 X2 : ℝ)
    (hV : 0≤V) (hRed : 0≤Red) (hell : 0≤ell)
    (hu1 : u≤1)
    (hunit : N.unit*u=N.unit-6*modelAmplification j N.coordinates-V)
    (hlen : N.unit*(length N.localBase X1+length N.localBase X2)+
      (∑i : slots,C.originalWeight i)=
        modelLength j N.coordinates-pathDeletion j.val N.coordinates-V-Red)
    (hslots : (∑i : slots,C.originalWeight i)=
      modelSlots j N.coordinates-pathDeletion j.val N.coordinates-ell)
    (hpaid : -(1/1000000000000000:ℝ)≤V+Red-ell)
    (hwide : (397/1000:ℝ)≤u)
    (hnotOld : u<length N.localBase X1+length N.localBase X2+
      6*Cycle63.Optimization.slotPrice*((∑i : slots,C.originalWeight i)/N.unit))
    (hnotReflect : ¬(length N.localBase X1+length N.localBase X2+
      6*Cycle63.Optimization.slotPrice*((∑i : slots,C.originalWeight i)/N.unit)≤u+19/5000 ∧
      (max 0 (u-length N.localBase X2+1/10000)+length N.localBase X1+
        6*Cycle63.Optimization.slotPrice*((∑i : slots,C.originalWeight i)/N.unit)+19/5000≤u ∨
       max 0 (u-length N.localBase X1+1/10000)+length N.localBase X2+
        6*Cycle63.Optimization.slotPrice*((∑i : slots,C.originalWeight i)/N.unit)+19/5000≤u)))
    (hgrid : 500*(1/C.gridDenominator:ℝ)≤positionMargin) :
    NativeChildGeometry C (nextInner j hj) N.localBase N.unit u slots X1 X2 := by
  let k := nextInner j hj
  let y := extendCoordinates N.coordinates k V Red ell
  let z := (∑i : slots,C.originalWeight i)/N.unit
  have hu : 0<u := lt_of_lt_of_le (by norm_num) hwide
  have hup := N.unit_pos
  have hsum : 0≤∑i : slots,C.originalWeight i :=
    Finset.sum_nonneg (fun i _=>C.originalWeight_nonneg i)
  have hz : 0≤z := div_nonneg hsum hup.le
  have hmodels := physical_next_models j hj N.coordinates V Red ell
  have hU : N.unit*u=modelUnit k y := by
    dsimp only at hmodels
    rw [hmodels.1,←N.unit_eq]
    exact hunit
  have hA : N.unit*(length N.localBase X1+length N.localBase X2+z)=modelLength k y := by
    dsimp only [z]
    rw [hmodels.2.1]
    calc
      _ = N.unit*(length N.localBase X1+length N.localBase X2)+∑i : slots,C.originalWeight i := by
        field_simp [ne_of_gt hup]
        <;> ring
      _ = _ := hlen
  have hS : N.unit*z=modelSlots k y := by
    dsimp only [z]
    rw [hmodels.2.2,←hslots]
    field_simp [ne_of_gt hup]
  have hn := physical_next_nonnegative N.coordinates k V Red ell N.physical_nonnegative hV hRed hell
  have hroot : ∀i : Fin 48,i.val<3 → -(1/1000000000000000:ℝ)≤Coordinates.rows i y := by
    intro i hi
    rw [earlier_rows_extend N.coordinates k V Red ell i (by dsimp [k,nextInner];omega)]
    exact N.prefixRows i (Or.inl (by omega))
  have hparent : N.unit=sourceParentUnit k y := by
    rw [physical_next_parent_unit j hj N.coordinates V Red ell]
    exact N.unit_eq
  have hover := actual_reflection_capacity_of_physical k y N.unit u
    (length N.localBase X1) (length N.localBase X2) z hup hparent hU hA hS hroot hn
  have hkappa : Coordinates.kappa=Cycle63.Optimization.slotPrice := by
    norm_num [Coordinates.kappa,Cycle63.Optimization.slotPrice,Cycle63.Optimization.betaBound]
  rw [hkappa] at hover
  have hbalance := actual_continuation_balance hz hwide hover hnotReflect
  have hactive : 0 < modelLength k y+(6*Coordinates.kappa-1)*modelSlots k y-modelUnit k y := by
    rw [←hA,←hS,←hU,hkappa]
    nlinarith only [hnotOld,hup]
  have hwideGlobal : Coordinates.mu*modelUnit j N.coordinates≤ modelUnit k y := by
    rw [←N.unit_eq,←hU]
    have h := mul_le_mul_of_nonneg_left hwide hup.le
    simpa only [Coordinates.mu,mul_comm] using h
  have hplain : 0≤ modelLength k y-modelSlots k y := by
    rw [←hA,←hS]
    have h1 := Real.logb_nonneg N.localBase_gt_one (le_max_left 1 X1)
    have h2 := Real.logb_nonneg N.localBase_gt_one (le_max_left 1 X2)
    change 0≤length N.localBase X1 at h1
    change 0≤length N.localBase X2 at h2
    nlinarith only [h1,h2,hup]
  have hr := raw_prefix_of_physical_step j hj N.coordinates V Red ell
    N.prefixRows N.physical_nonnegative hV hRed hell hpaid hwideGlobal hactive hplain
    (by rw [←hS];exact mul_nonneg hup.le hz)
  have hlenRebase : (N.unit*u)*(length (N.localBase^u) X1+length (N.localBase^u) X2+
      ∑i : slots,C.originalWeight i/(N.unit*u))=modelLength k y := by
    have h1 : u*length (N.localBase^u) X1=length N.localBase X1 :=
      unit_mul_logb_rebase N.localBase_gt_one hu
    have h2 : u*length (N.localBase^u) X2=length N.localBase X2 :=
      unit_mul_logb_rebase N.localBase_gt_one hu
    rw [←Finset.sum_div]
    calc
      _ = N.unit*(u*length (N.localBase^u) X1+u*length (N.localBase^u) X2)+
          ∑i : slots,C.originalWeight i := by
        field_simp [ne_of_gt hup,ne_of_gt hu]
        <;> ring
      _ = _ := by rw [h1,h2];exact hlen.trans hmodels.2.1.symm
  have hbalGlobal : |(N.unit*u)*length (N.localBase^u) X1-(N.unit*u)*length (N.localBase^u) X2|≤
      6*Cycle63.Optimization.slotPrice*modelSlots k y+modelUnit k y/100 := by
    have h1 : u*length (N.localBase^u) X1=length N.localBase X1 :=
      unit_mul_logb_rebase N.localBase_gt_one hu
    have h2 : u*length (N.localBase^u) X2=length N.localBase X2 :=
      unit_mul_logb_rebase N.localBase_gt_one hu
    rw [mul_assoc,mul_assoc,h1,h2,←mul_sub,abs_mul,abs_of_pos hup,←hS,←hU]
    nlinarith only [mul_le_mul_of_nonneg_left hbalance hup.le]
  exact childGeometryOfRawPhysical C k y N.localBase N.unit u slots X1 X2 hr hn hU
    (by nlinarith only [mul_le_mul_of_nonneg_left hu1 hup.le,N.unit_le_one])
    hgrid hlenRebase (by rw [←hS];dsimp only [z];field_simp [ne_of_gt hup])
    hbalGlobal (by simpa only [hkappa] using hactive)

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.actual_continuation_balance
#print axioms OAI.SevenEighths.Cycle153Reachable.childGeometryOfActualContinuation
