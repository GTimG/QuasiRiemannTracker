/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.NativeNodeStep
import Candidate.Research.RecursiveAffine.PhysicalChildGeometry

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CenteredMomentEnergyBands Cycle153Geometry Cycle153ReachableGeometry Cycle63.Optimization

def directNodeRate (j : Fin 4) : ℝ := (innerStage j.val).q/(6*slotPrice)

def modelOldGap (j : Fin 4) (x : Fin 14→ℝ) : ℝ :=
  modelCap j x+(6*slotPrice-1)*modelSlots j x-modelUnit j x

def modelDirectRoom (j : Fin 4) (x : Fin 14→ℝ) : ℝ :=
  directNodeRate j*((1-2*Coordinates.mu)*modelUnit j x-modelOldGap j x)+
    modelAmplification j x*(1-12*directNodeRate j)-
      lowReserveAt (innerStage j.val).price (innerStage j.val).intercept (innerStage j.val).q*modelUnit j x

theorem modelDirectRoom_identity (j : Fin 4) (hj : j.val<3) (x : Fin 14→ℝ) :
    modelDirectRoom j x=
      ![Coordinates.gate1_direct_width_floor x,Coordinates.gate2_direct_width_floor x,
        Coordinates.gate3_direct_width_floor x,0] j := by
  fin_cases j <;> norm_num at hj
  all_goals norm_num [modelDirectRoom,directNodeRate,modelOldGap,modelCap,modelSlots,modelUnit,
    modelAmplification,innerStage,Cycle153.FixedStages.stage1,Cycle153.FixedStages.stage2,
    Cycle153.FixedStages.stage3,Coordinates.gate1_direct_width_floor,
    Coordinates.gate2_direct_width_floor,Coordinates.gate3_direct_width_floor,
    Coordinates.oldcap1,Coordinates.oldcap2,Coordinates.oldcap3,
    Coordinates.lowres1,Coordinates.lowres2,Coordinates.lowres3,
    Coordinates.q1,Coordinates.q2,Coordinates.q3,Coordinates.k1,Coordinates.k2,Coordinates.k3,
    Coordinates.inner1,Coordinates.inner2,Coordinates.inner3,Coordinates.alpha,
    Coordinates.kappa,slotPrice,betaBound,lowReserveAt,lowReserveWeight,allowanceUnit]

/-- The direct branch uses only the already constructed parent prefix.
There is no assumption about the narrow child's later amplifier or rows. -/
theorem physical_direct_room_margin (j : Fin 4) (hj : j.val<3) (x : Fin 14→ℝ)
    (hp : PrefixRows (j.val+1) x) :
    (1568511/1000000000000000:ℝ) < modelDirectRoom j x := by
  rw [modelDirectRoom_identity j hj x]
  fin_cases j <;> norm_num at hj
  · exact prefix_gate hp 10 (by decide)
  · exact prefix_gate hp 26 (by decide)
  · exact prefix_gate hp 42 (by decide)

/-- The literal rounded old-gap displacement is small, with its correct
nonnegative slope. It is independent of the residual source being selected. -/
theorem rounded_oldgap_bounds (S : Cycle153.RegionalStage) {g B n1 n2 z : ℝ}
    (hg : 0<g) :
    let P := Cycle153.roundedPosition g B n1 n2 z
    planeGap slotPrice 1 S.lam B z≤S.oldGap P ∧
      S.oldGap P≤planeGap slotPrice 1 S.lam B z+6*g := by
  intro P
  have hB := Cycle153.roundUp_bounds hg B
  have hz := Cycle153.roundUp_bounds hg z
  have hk := slotPrice_mem
  have hc : 0≤6*slotPrice-S.lam := by linarith only [S.lam_le_six_old]
  have hc5 : 6*slotPrice-S.lam≤5 := by linarith only [S.one_le_lam,hk.2]
  have hlo := mul_le_mul_of_nonneg_left hz.1 hc
  have hhi := mul_le_mul_of_nonneg_left hz.2 hc
  have hcg := mul_le_mul_of_nonneg_right hc5 hg.le
  dsimp only [P,Cycle153.roundedPosition,Cycle153.RegionalStage.oldGap,planeGap]
  constructor <;> nlinarith only [hB,hlo,hhi,hcg]

variable {α : Type} [Fintype α] [DecidableEq α]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {C : SourceContext (α:=α) M H} {j : Fin 4} (N : ReachableNode C j)

theorem node_model_oldgap_identity :
    modelOldGap j N.coordinates/N.unit=
      planeGap slotPrice 1 (innerStage j.val).lam N.plane
        (∑i : N.slots,C.originalWeight i/N.unit) := by
  have hz : (∑i : N.slots,C.originalWeight i/N.unit)=modelSlots j N.coordinates/N.unit := by
    rw [←Finset.sum_div,N.slots_eq]
  rw [hz,N.plane_eq]
  unfold modelOldGap
  rw [modelCap_identity,rawPlane_eq_modelPlane,←N.unit_eq]
  unfold planeGap
  field_simp [ne_of_gt N.unit_pos]
  <;> ring

theorem node_oldgap_bounds :
    modelOldGap j N.coordinates/N.unit≤(innerStage j.val).oldGap N.position ∧
      (innerStage j.val).oldGap N.position≤ modelOldGap j N.coordinates/N.unit+6*(1/C.gridDenominator) := by
  have hg : (0:ℝ)<1/C.gridDenominator := by
    have hn : (0:ℝ)<C.gridDenominator := by exact_mod_cast C.grid_positive
    positivity
  have h := rounded_oldgap_bounds (innerStage j.val) (B:=N.plane)
    (n1:=length N.localBase N.X1) (n2:=length N.localBase N.X2)
    (z:=∑i : N.slots,C.originalWeight i/N.unit) hg
  rw [←N.rounded,←node_model_oldgap_identity N] at h
  exact h

def nativeNodeDirectRoom : ℝ :=
  directNodeRate j*((1-2*Coordinates.mu)-(innerStage j.val).oldGap N.position)+
    nodeSourceAmp N*(1-12*directNodeRate j)-
      lowReserveAt (innerStage j.val).price (innerStage j.val).intercept (innerStage j.val).q

/-- Actual rounded source parameters retain the direct-branch margin.
Both the old-gap and amplifier rounding errors are explicitly charged. -/
theorem native_node_direct_room (hj : j.val<3)
    (hgrid : 500*(1/C.gridDenominator:ℝ)≤positionMargin) :
    (1/1000000000:ℝ)≤nativeNodeDirectRoom N := by
  have hm := physical_direct_room_margin j hj N.coordinates N.prefixRows
  have hg := node_oldgap_bounds N
  have ha := nodeSourceAmp_bounds N
  have hu := N.unit_pos
  have hκ : 0≤directNodeRate j ∧ directNodeRate j≤1/2 := by
    fin_cases j <;> norm_num [directNodeRate,innerStage,Cycle153.FixedStages.stage1,
      Cycle153.FixedStages.stage2,Cycle153.FixedStages.stage3,Cycle153.FixedStages.stage4,
      slotPrice,betaBound,Coordinates.q1,Coordinates.q2,Coordinates.q3,Coordinates.q4]
  have hq : (1:ℝ)/12≤directNodeRate j := by
    fin_cases j <;> norm_num [directNodeRate,innerStage,Cycle153.FixedStages.stage1,
      Cycle153.FixedStages.stage2,Cycle153.FixedStages.stage3,Cycle153.FixedStages.stage4,
      slotPrice,betaBound,Coordinates.q1,Coordinates.q2,Coordinates.q3,Coordinates.q4]
  have hrate : 0≤12*directNodeRate j-1 ∧ 12*directNodeRate j-1≤5 := by
    constructor <;> linarith only [hκ.2,hq]
  have hgap := mul_le_mul_of_nonneg_left hg.2 hκ.1
  have hamp := mul_le_mul_of_nonneg_left ha.2 hrate.1
  have hnorm : (1568511/1000000000000000:ℝ) < modelDirectRoom j N.coordinates/N.unit := by
    apply (lt_div_iff₀ hu).mpr
    nlinarith only [hm,N.unit_le_one,hu]
  have hRoom : modelDirectRoom j N.coordinates/N.unit=
      directNodeRate j*((1-2*Coordinates.mu)-modelOldGap j N.coordinates/N.unit)+
        (modelAmplification j N.coordinates/N.unit)*(1-12*directNodeRate j)-
          lowReserveAt (innerStage j.val).price (innerStage j.val).intercept (innerStage j.val).q := by
    unfold modelDirectRoom
    rw [←N.unit_eq]
    field_simp [ne_of_gt hu]
    <;> ring
  have hgpos : (0:ℝ)≤1/C.gridDenominator := by positivity
  have hround1 := mul_le_mul_of_nonneg_right hκ.2 hgpos
  have hround2 := mul_le_mul_of_nonneg_right hrate.2 hgpos
  rw [hRoom] at hnorm
  dsimp only [nativeNodeDirectRoom]
  norm_num only [positionMargin] at hgrid
  nlinarith only [hnorm,hgap,hamp,hround1,hround2,hgrid]

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.native_node_direct_room
