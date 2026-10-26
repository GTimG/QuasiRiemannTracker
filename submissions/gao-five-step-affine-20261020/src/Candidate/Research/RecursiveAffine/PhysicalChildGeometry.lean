/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.ActualReachableChild
import Candidate.Research.RecursiveAffine.FixedReachablePosition
import Candidate.Research.RecursiveAffine.PhysicalPrefixClosure
import Candidate.Research.RecursiveAffine.Geometry.SourceDomainAudit

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentEnergyBands Cycle153Geometry Cycle153ReachableGeometry
open Cycle63.Optimization

variable {α : Type} [Fintype α] [DecidableEq α]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}

theorem rawPlane_eq_modelPlane (j : Fin 4) (x : Fin 14 → ℝ) :
    rawPlane j x=modelPlane j x := by
  fin_cases j <;> rfl

/-- The actual .009 comparison overshoot is paid at every reachable prefix. -/
theorem source_comparison_overshoot (j : Fin 4) (x : Fin 14 → ℝ)
    (hp : PrefixRows (j.val+1) x) :
    modelLength j x+(6*Coordinates.kappa-1)*modelSlots j x-modelUnit j x ≤
      (9/1000)*modelUnit j x := by
  fin_cases j
  · have hc : ∀k,-(1/1000000000000000:ℝ) ≤ eval (Model.constraint (SourceComparison1.selected k)) x := by
      intro k
      rw [constraint_meaning]
      apply hp (SourceComparison1.selected k)
      exact SourceComparison1.prefix_admissible k
    have h := SourceComparison1.robust_lower x (1/1000000000000000) le_rfl hc
    change (1568511/1000000000000000:ℝ)<
      (9/1000)*Coordinates.U1 x-(Coordinates.A1 x+(6*Coordinates.kappa-1)*Coordinates.z1 x-Coordinates.U1 x) at h
    change Coordinates.A1 x+(6*Coordinates.kappa-1)*Coordinates.z1 x-Coordinates.U1 x ≤ (9/1000)*Coordinates.U1 x
    linarith only [h]

  · have hc : ∀k,-(1/1000000000000000:ℝ) ≤ eval (Model.constraint (SourceComparison2.selected k)) x := by
      intro k
      rw [constraint_meaning]
      apply hp (SourceComparison2.selected k)
      exact SourceComparison2.prefix_admissible k
    have h := SourceComparison2.robust_lower x (1/1000000000000000) le_rfl hc
    change (1568511/1000000000000000:ℝ)<
      (9/1000)*Coordinates.U2 x-(Coordinates.A2 x+(6*Coordinates.kappa-1)*Coordinates.z2 x-Coordinates.U2 x) at h
    change Coordinates.A2 x+(6*Coordinates.kappa-1)*Coordinates.z2 x-Coordinates.U2 x ≤ (9/1000)*Coordinates.U2 x
    linarith only [h]

  · have hc : ∀k,-(1/1000000000000000:ℝ) ≤ eval (Model.constraint (SourceComparison3.selected k)) x := by
      intro k
      rw [constraint_meaning]
      apply hp (SourceComparison3.selected k)
      exact SourceComparison3.prefix_admissible k
    have h := SourceComparison3.robust_lower x (1/1000000000000000) le_rfl hc
    change (1568511/1000000000000000:ℝ)<
      (9/1000)*Coordinates.U3 x-(Coordinates.A3 x+(6*Coordinates.kappa-1)*Coordinates.z3 x-Coordinates.U3 x) at h
    change Coordinates.A3 x+(6*Coordinates.kappa-1)*Coordinates.z3 x-Coordinates.U3 x ≤ (9/1000)*Coordinates.U3 x
    linarith only [h]

  · have hc : ∀k,-(1/1000000000000000:ℝ) ≤ eval (Model.constraint (SourceComparison4.selected k)) x := by
      intro k
      rw [constraint_meaning]
      apply hp (SourceComparison4.selected k)
      exact SourceComparison4.prefix_admissible k
    have h := SourceComparison4.robust_lower x (1/1000000000000000) le_rfl hc
    change (1568511/1000000000000000:ℝ)<
      (9/1000)*Coordinates.U4 x-(Coordinates.A4 x+(6*Coordinates.kappa-1)*Coordinates.z4 x-Coordinates.U4 x) at h
    change Coordinates.A4 x+(6*Coordinates.kappa-1)*Coordinates.z4 x-Coordinates.U4 x ≤ (9/1000)*Coordinates.U4 x
    linarith only [h]

/-- Build the actual next source geometry from the scalar physical
history. Full ledger facts and the plain window are derived here, not
supplied as recursive hypotheses. -/
def childGeometryOfPhysical
    (C : SourceContext (α:=α) M H) (j : Fin 4) (x : Fin 14 → ℝ)
    (Zparent parentUnit u : ℝ) (slots : Finset α) (X1 X2 : ℝ)
    (hp : PrefixRows (j.val+1) x)
    (hphysical : ∀i : Fin 48,35 ≤ i.val → 0 ≤ Coordinates.rows i x)
    (hunit : parentUnit*u=modelUnit j x)
    (hfloor : (1/50:ℝ) ≤ parentUnit*u) (hU1 : parentUnit*u ≤ 1)
    (hgrid : 500*(1/C.gridDenominator:ℝ) ≤ positionMargin)
    (hlen : (parentUnit*u)*(length (Zparent^u) X1+length (Zparent^u) X2+
      ∑i : slots,C.originalWeight i/(parentUnit*u))=modelLength j x)
    (hslots : (∑i : slots,C.originalWeight i)=modelSlots j x)
    (hregion : modelLength j x ≤ modelCap j x)
    (hterminal : j.val=3 → modelLength j x+(6*Coordinates.k3-1)*modelSlots j x ≤
      Coordinates.inner3*modelUnit j x)
    (hbalanced : |(parentUnit*u)*length (Zparent^u) X1-(parentUnit*u)*length (Zparent^u) X2| ≤
      6*slotPrice*modelSlots j x+modelUnit j x/100)
    (hactive : 0 < modelLength j x+(6*slotPrice-1)*modelSlots j x-modelUnit j x) :
    NativeChildGeometry C j Zparent parentUnit u slots X1 X2 := by
  have hU : 0<parentUnit*u := lt_of_lt_of_le (by norm_num) hfloor
  have hUne : parentUnit*u≠0 := ne_of_gt hU
  have hpne : parentUnit≠0 := (mul_ne_zero_iff.mp hUne).1
  have hune : u≠0 := (mul_ne_zero_iff.mp hUne).2
  have hg : (0:ℝ)<1/C.gridDenominator := by
    have : (0:ℝ)<C.gridDenominator := by exact_mod_cast C.grid_positive
    positivity
  have hz : 0 ≤ modelSlots j x := by
    rw [←hslots]
    exact Finset.sum_nonneg (fun i _=>C.originalWeight_nonneg i)
  have hzlocal : (∑i : slots,C.originalWeight i/(parentUnit*u))=modelSlots j x/(parentUnit*u) := by
    rw [←Finset.sum_div,hslots]
  have hA : modelLength j x=(parentUnit*u)*length (Zparent^u) X1+
      (parentUnit*u)*length (Zparent^u) X2+modelSlots j x := by
    rw [hzlocal] at hlen
    calc
      modelLength j x = (parentUnit*u)*(length (Zparent^u) X1+
        length (Zparent^u) X2+modelSlots j x/(parentUnit*u)) := hlen.symm
      _ = _ := by field_simp [hpne,hune]
  have hraw := fixed_stage_rounded_facts j x hp hg hgrid
    (by rw [←hunit];exact hU1) hz hA hregion hterminal hbalanced hactive
  let B := modelPlane j x/(parentUnit*u)
  let pos := Cycle153.roundedPosition (1/C.gridDenominator) B
    (length (Zparent^u) X1) (length (Zparent^u) X2)
    (∑i : slots,C.originalWeight i/(parentUnit*u))
  have hn1 : ((parentUnit*u)*length (Zparent^u) X1)/(parentUnit*u)=length (Zparent^u) X1 := by
    field_simp [hpne,hune]
  have hn2 : ((parentUnit*u)*length (Zparent^u) X2)/(parentUnit*u)=length (Zparent^u) X2 := by
    field_simp [hpne,hune]
  have hfacts : pos.Facts (innerStage j.val) := by
    rw [←hunit,rawPlane_eq_modelPlane,hn1,hn2,←hzlocal] at hraw
    exact hraw
  have hplaneGlobal : (parentUnit*u)*length (Zparent^u) X1+
      (parentUnit*u)*length (Zparent^u) X2+(innerStage j.val).lam*modelSlots j x ≤ modelPlane j x := by
    have hc := modelCap_identity j x
    rw [rawPlane_eq_modelPlane] at hc
    nlinarith only [hA,hregion,hc]
  have hplane : length (Zparent^u) X1+length (Zparent^u) X2+
      (innerStage j.val).lam*(∑i : slots,C.originalWeight i/(parentUnit*u)) ≤ B := by
    dsimp only [B]
    rw [hzlocal]
    apply (le_div_iff₀ hU).mpr
    calc
      _ = (parentUnit*u)*length (Zparent^u) X1+
        (parentUnit*u)*length (Zparent^u) X2+(innerStage j.val).lam*modelSlots j x := by
          field_simp [hpne,hune]
      _ ≤ modelPlane j x := hplaneGlobal
  refine ⟨x,hp,hphysical,hunit,hfloor,hU1,hlen,hslots,B,rfl,pos,rfl,hfacts,?_,?_⟩
  · exact Cycle153.roundedPosition_window hg
      (Finset.sum_nonneg (fun i _=>div_nonneg (C.originalWeight_nonneg i) hU.le)) hplane
  · rw [hzlocal]
    have hov := source_comparison_overshoot j x hp
    have hk : Coordinates.kappa=slotPrice := by
      norm_num [Coordinates.kappa,slotPrice,betaBound]
    rw [hk] at hov
    apply le_of_mul_le_mul_left ?_ hU
    calc
      _ = modelLength j x+(6*slotPrice-1)*modelSlots j x := by
        rw [hA]
        field_simp [hpne,hune]
        ring
      _ ≤ (parentUnit*u)*(1+9/1000) := by
        nlinarith only [hov,hunit]

/-- Actual raw source inequalities determine the full child geometry.
The amplifier, unit floor and inherited regional plane are all derived
from the same retained physical prefix. -/
def childGeometryOfRawPhysical
    (C : SourceContext (α:=α) M H) (j : Fin 4) (x : Fin 14 → ℝ)
    (Zparent parentUnit u : ℝ) (slots : Finset α) (X1 X2 : ℝ)
    (hr : RawPrefixRows j x)
    (hphysical : ∀i : Fin 48,35 ≤ i.val → 0 ≤ Coordinates.rows i x)
    (hunit : parentUnit*u=modelUnit j x) (hU1 : parentUnit*u ≤ 1)
    (hgrid : 500*(1/C.gridDenominator:ℝ) ≤ positionMargin)
    (hlen : (parentUnit*u)*(length (Zparent^u) X1+length (Zparent^u) X2+
      ∑i : slots,C.originalWeight i/(parentUnit*u))=modelLength j x)
    (hslots : (∑i : slots,C.originalWeight i)=modelSlots j x)
    (hbalanced : |(parentUnit*u)*length (Zparent^u) X1-(parentUnit*u)*length (Zparent^u) X2| ≤
      6*slotPrice*modelSlots j x+modelUnit j x/100)
    (hactive : 0 < modelLength j x+(6*slotPrice-1)*modelSlots j x-modelUnit j x) :
    NativeChildGeometry C j Zparent parentUnit u slots X1 X2 := by
  have hp := prefixRows_of_raw_physical j x hr
  have hfloor : (1/50:ℝ) ≤ parentUnit*u := by
    rw [hunit]
    exact raw_prefix_unit_floor j x hr
  have hrgn := physical_previous_regions x hphysical
  have hregion : modelLength j x ≤ modelCap j x := by
    fin_cases j
    · change Coordinates.A1 x ≤ Coordinates.capA1 x
      dsimp only [Coordinates.capA1]
      linarith only [hrgn.1]
    · change Coordinates.A2 x ≤ Coordinates.capA2 x
      dsimp only [Coordinates.capA2]
      linarith only [hrgn.2.1]
    · change Coordinates.A3 x ≤ Coordinates.capA3 x
      dsimp only [Coordinates.capA3]
      linarith only [hrgn.2.2.1]
    · exact le_rfl
  have hterminal : j.val=3 → modelLength j x+(6*Coordinates.k3-1)*modelSlots j x ≤
      Coordinates.inner3*modelUnit j x := by
    intro hj
    have heq : j=(3:Fin 4) := Fin.ext hj
    subst j
    exact hrgn.2.2.2
  exact childGeometryOfPhysical C j x Zparent parentUnit u slots X1 X2 hp hphysical hunit
    hfloor hU1 hgrid hlen hslots hregion hterminal hbalanced hactive

end
end OAI.SevenEighths.Cycle153Reachable

#print axioms OAI.SevenEighths.Cycle153Reachable.childGeometryOfPhysical

#print axioms OAI.SevenEighths.Cycle153Reachable.childGeometryOfRawPhysical
