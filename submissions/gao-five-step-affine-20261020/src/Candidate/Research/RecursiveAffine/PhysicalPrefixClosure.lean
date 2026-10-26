/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.ReachableNode
import Candidate.Research.RecursiveAffine.Geometry.SourceDomainAudit

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open Cycle153Geometry Cycle153ReachableGeometry

/-- Raw physical prefix conditions. The next amplifier and unit floor
are conclusions, rather than assumptions about the next source. -/
def RawPrefixRows (j : Fin 4) (x : Fin 14 → ℝ) : Prop :=
  ∀ i : Fin 48, (i.val < 7*(j.val+2) ∨ 35 ≤ i.val) →
    i.val ≠ 10+7*j.val → i.val ≠ 11+7*j.val →
    -(1/1000000000000000 : ℝ) ≤ Coordinates.rows i x

/-- Four genuine .397 width tests imply the fixed lower unit bound.
Only the tests already available at the indicated prefix are used. -/
theorem raw_prefix_unit_floor (j : Fin 4) (x : Fin 14 → ℝ)
    (hr : RawPrefixRows j x) : (1/50:ℝ) ≤ modelUnit j x := by
  fin_cases j
  · have hw0 := hr 8 (Or.inl (by norm_num)) (by norm_num) (by norm_num)
    change -(1/1000000000000000:ℝ) ≤ Coordinates.U1 x-(397/1000)*1 at hw0
    change (1/50:ℝ) ≤ Coordinates.U1 x
    linarith only [hw0]
  · have hw0 := hr 8 (Or.inl (by norm_num)) (by norm_num) (by norm_num)
    change -(1/1000000000000000:ℝ) ≤ Coordinates.U1 x-(397/1000)*1 at hw0
    have hw1 := hr 15 (Or.inl (by norm_num)) (by norm_num) (by norm_num)
    change -(1/1000000000000000:ℝ) ≤ Coordinates.U2 x-(397/1000)*Coordinates.U1 x at hw1
    change (1/50:ℝ) ≤ Coordinates.U2 x
    linarith only [hw0,hw1]
  · have hw0 := hr 8 (Or.inl (by norm_num)) (by norm_num) (by norm_num)
    change -(1/1000000000000000:ℝ) ≤ Coordinates.U1 x-(397/1000)*1 at hw0
    have hw1 := hr 15 (Or.inl (by norm_num)) (by norm_num) (by norm_num)
    change -(1/1000000000000000:ℝ) ≤ Coordinates.U2 x-(397/1000)*Coordinates.U1 x at hw1
    have hw2 := hr 22 (Or.inl (by norm_num)) (by norm_num) (by norm_num)
    change -(1/1000000000000000:ℝ) ≤ Coordinates.U3 x-(397/1000)*Coordinates.U2 x at hw2
    change (1/50:ℝ) ≤ Coordinates.U3 x
    linarith only [hw0,hw1,hw2]
  · have hw0 := hr 8 (Or.inl (by norm_num)) (by norm_num) (by norm_num)
    change -(1/1000000000000000:ℝ) ≤ Coordinates.U1 x-(397/1000)*1 at hw0
    have hw1 := hr 15 (Or.inl (by norm_num)) (by norm_num) (by norm_num)
    change -(1/1000000000000000:ℝ) ≤ Coordinates.U2 x-(397/1000)*Coordinates.U1 x at hw1
    have hw2 := hr 22 (Or.inl (by norm_num)) (by norm_num) (by norm_num)
    change -(1/1000000000000000:ℝ) ≤ Coordinates.U3 x-(397/1000)*Coordinates.U2 x at hw2
    have hw3 := hr 29 (Or.inl (by norm_num)) (by norm_num) (by norm_num)
    change -(1/1000000000000000:ℝ) ≤ Coordinates.U4 x-(397/1000)*Coordinates.U3 x at hw3
    change (1/50:ℝ) ≤ Coordinates.U4 x
    linarith only [hw0,hw1,hw2,hw3]

/-- The omitted amplifier condition follows from the same native
prefix constraints. Middle-stage certificates explicitly omit that
condition, avoiding a circular assumption about amplifier positivity. -/
theorem raw_prefix_amplifier_nonneg (j : Fin 4) (x : Fin 14 → ℝ)
    (hr : RawPrefixRows j x) :
    0 ≤ Coordinates.rows ⟨10+7*j.val,by omega⟩ x := by
  have hU := raw_prefix_unit_floor j x hr
  fin_cases j
  · have hc : ∀ i,-(1/1000000000000000:ℝ) ≤ eval
        (Model.constraint (Certificate12.selected i)) x := by
      intro i
      rw [constraint_meaning]
      apply hr (Certificate12.selected i)
      · exact Certificate12.prefix_admissible i
      · exact Certificate12.exclusions_admissible i
      · fin_cases i <;> norm_num [Certificate12.selected]
    have hg := Certificate12.positive x (1/1000000000000000) le_rfl hc
    rw [objective12_meaning] at hg
    change 0 < Coordinates.gap1 x at hg
    have ha : (0:ℝ) ≤ Coordinates.q1/(6*(Coordinates.k1-Coordinates.q1*Coordinates.inner1)) := by
      norm_num [Coordinates.q1,Coordinates.k1,Coordinates.inner1]
    change (1/50:ℝ) ≤ Coordinates.U1 x at hU
    change 0 ≤ Coordinates.a1 x
    unfold Coordinates.a1
    exact add_nonneg (mul_nonneg ha hg.le)
      (mul_nonneg (by norm_num [Coordinates.alpha]) (by linarith only [hU]))
  · have hc : ∀ i,-(1/1000000000000000:ℝ) ≤ eval
        (Model.constraint (Certificate28.selected i)) x := by
      intro i
      rw [constraint_meaning]
      apply hr (Certificate28.selected i)
      · exact Certificate28.prefix_admissible i
      · exact Certificate28.exclusions_admissible i
      · fin_cases i <;> norm_num [Certificate28.selected]
    have hg := Certificate28.positive x (1/1000000000000000) le_rfl hc
    rw [objective28_meaning] at hg
    change 0 < Coordinates.gap2 x at hg
    have ha : (0:ℝ) ≤ Coordinates.q2/(6*(Coordinates.k2-Coordinates.q2*Coordinates.inner2)) := by
      norm_num [Coordinates.q2,Coordinates.k2,Coordinates.inner2]
    change (1/50:ℝ) ≤ Coordinates.U2 x at hU
    change 0 ≤ Coordinates.a2 x
    unfold Coordinates.a2
    exact add_nonneg (mul_nonneg ha hg.le)
      (mul_nonneg (by norm_num [Coordinates.alpha]) (by linarith only [hU]))
  · have hc : ∀ i,-(1/1000000000000000:ℝ) ≤ eval
        (Model.constraint (Certificate44.selected i)) x := by
      intro i
      rw [constraint_meaning]
      apply hr (Certificate44.selected i)
      · exact Certificate44.prefix_admissible i
      · exact Certificate44.exclusions_admissible i
      · fin_cases i <;> norm_num [Certificate44.selected]
    have hg := Certificate44.positive x (1/1000000000000000) le_rfl hc
    rw [objective44_meaning] at hg
    change 0 < Coordinates.gap3 x at hg
    have ha : (0:ℝ) ≤ Coordinates.q3/(6*(Coordinates.k3-Coordinates.q3*Coordinates.inner3)) := by
      norm_num [Coordinates.q3,Coordinates.k3,Coordinates.inner3]
    change (1/50:ℝ) ≤ Coordinates.U3 x at hU
    change 0 ≤ Coordinates.a3 x
    unfold Coordinates.a3
    exact add_nonneg (mul_nonneg ha hg.le)
      (mul_nonneg (by norm_num [Coordinates.alpha]) (by linarith only [hU]))
  · have hg := hr 30 (Or.inl (by norm_num)) (by norm_num) (by norm_num)
    change -(1/1000000000000000:ℝ) ≤
      Coordinates.A4 x+(6*Coordinates.kappa-1)*Coordinates.z4 x-Coordinates.U4 x at hg
    have hgap : -(1/1000000000000000:ℝ) ≤ Coordinates.gap4 x := by
      simpa only [Coordinates.gap4,Coordinates.capA4,Coordinates.inner4,
        Coordinates.k4,Coordinates.kappa,one_mul] using hg
    have ha : (0:ℝ) ≤ Coordinates.q4/(6*(Coordinates.k4-Coordinates.q4*Coordinates.inner4)) ∧
        Coordinates.q4/(6*(Coordinates.k4-Coordinates.q4*Coordinates.inner4)) ≤ 10 := by
      norm_num [Coordinates.q4,Coordinates.k4,Coordinates.inner4]
    have hm := mul_le_mul_of_nonneg_left hgap ha.1
    change (1/50:ℝ) ≤ Coordinates.U4 x at hU
    change 0 ≤ Coordinates.a4 x
    unfold Coordinates.a4
    norm_num only [Coordinates.alpha]
    nlinarith only [hm,ha.2,hU]

/-- All model constraints at this depth follow from raw physical
conditions; the two extra next-source premises have been discharged. -/
theorem prefixRows_of_raw_physical (j : Fin 4) (x : Fin 14 → ℝ)
    (hr : RawPrefixRows j x) : PrefixRows (j.val+1) x := by
  have hU := raw_prefix_unit_floor j x hr
  have ha := raw_prefix_amplifier_nonneg j x hr
  intro i hi
  by_cases hamp : i.val=10+7*j.val
  · have heq : i=⟨10+7*j.val,by omega⟩ := Fin.ext hamp
    rw [heq]
    exact le_trans (by norm_num) ha
  by_cases hunit : i.val=11+7*j.val
  · have heq : i=⟨11+7*j.val,by omega⟩ := Fin.ext hunit
    have hrow : Coordinates.rows ⟨11+7*j.val,by omega⟩ x = modelUnit j x-1/1000000 := by
      fin_cases j <;> rfl
    rw [heq,hrow]
    linarith only [hU]
  · exact hr i (by simpa only [Nat.add_assoc] using hi) hamp hunit

/-- Whole-slot deletion at the actual target puts the daughter in the
preceding regional plane. Positive physical reductions only help; every
finite error was paid by the explicit extra deletion before this step. -/
theorem deleted_region_from_actual_coordinates
    {A cap z U D a V Red ell k I gap Uchild Achild zchild extra : ℝ}
    (hcap : A ≤ cap) (hk : 1/6 ≤ k) (hI : I ≤ 1)
    (hV : 0 ≤ V) (hRed : 0 ≤ Red) (hell : 0 ≤ ell) (hextra : 0 ≤ extra)
    (hgap : gap=cap+(6*k-1)*z-I*U+extra)
    (hD : 6*k*D=gap+6*I*a)
    (hU : Uchild=U-6*a-V) (hA : Achild=A-D-V-Red)
    (hz : zchild=z-D-ell) :
    Achild+(6*k-1)*zchild ≤ I*Uchild := by
  have hmv : 0 ≤ (1-I)*V := mul_nonneg (by linarith only [hI]) hV
  have hme : 0 ≤ (6*k-1)*ell := mul_nonneg (by linarith only [hk]) hell
  rw [hU,hA,hz]
  nlinarith only [hcap,hRed,hextra,hgap,hD,hmv,hme]

/-- Exact nonnegative source coordinates imply every inherited regional
plane, including the last old-region plane. This uses the literal fixed
deletion recurrences, not another assumed next-ledger feasibility bound. -/
theorem physical_previous_regions (x : Fin 14 → ℝ)
    (hn : ∀i : Fin 48,35 ≤ i.val → 0 ≤ Coordinates.rows i x) :
    (Coordinates.A1 x+(6*Coordinates.k0-1)*Coordinates.z1 x ≤ Coordinates.inner0*Coordinates.U1 x) ∧
    (Coordinates.A2 x+(6*Coordinates.k1-1)*Coordinates.z2 x ≤ Coordinates.inner1*Coordinates.U2 x) ∧
    (Coordinates.A3 x+(6*Coordinates.k2-1)*Coordinates.z3 x ≤ Coordinates.inner2*Coordinates.U3 x) ∧
    (Coordinates.A4 x+(6*Coordinates.k3-1)*Coordinates.z4 x ≤ Coordinates.inner3*Coordinates.U4 x) := by
  have hv0 : 0 ≤ Coordinates.V0 x := hn 35 (by norm_num)
  have hr0 : 0 ≤ Coordinates.Red0 x := hn 39 (by norm_num)
  have he0 : 0 ≤ Coordinates.ell0 x := hn 43 (by norm_num)
  have hk0 : (1/6:ℝ) ≤ Coordinates.k0 := by norm_num [Coordinates.k0]
  have hi0 : Coordinates.inner0 ≤ 1 := by norm_num [Coordinates.inner0]
  have hkne0 : Coordinates.k0≠0 := by norm_num [Coordinates.k0]
  have hd0 : 6*Coordinates.k0*Coordinates.d0 x =
      Coordinates.gap0 x+6*Coordinates.inner0*Coordinates.a0 x := by
    dsimp only [Coordinates.d0]
    field_simp [hkne0]
  have hslack : 0 ≤ Coordinates.rootSlack x := hn 47 (by norm_num)
  have hco : 0 ≤ 6*Coordinates.k0-Coordinates.outerLambda := by
    norm_num [Coordinates.k0,Coordinates.outerLambda]
  have hg0 : Coordinates.gap0 x = Coordinates.capA0 x+(6*Coordinates.k0-1)*Coordinates.z0 x-
      Coordinates.inner0*Coordinates.U0 x+(6*Coordinates.k0-Coordinates.outerLambda)*Coordinates.rootSlack x := by
    dsimp only [Coordinates.gap0,Coordinates.capA0,Coordinates.A0,Coordinates.z0,Coordinates.U0]
    ring
  have hp0 := deleted_region_from_actual_coordinates
    (A:=Coordinates.A0 x) (cap:=Coordinates.capA0 x)
    le_rfl hk0 hi0 hv0 hr0 he0 (mul_nonneg hco hslack) hg0 hd0
    (show Coordinates.U1 x=Coordinates.U0 x-6*Coordinates.a0 x-Coordinates.V0 x from rfl)
    (show Coordinates.A1 x=Coordinates.A0 x-Coordinates.d0 x-Coordinates.V0 x-Coordinates.Red0 x from rfl)
    (show Coordinates.z1 x=Coordinates.z0 x-Coordinates.d0 x-Coordinates.ell0 x from rfl)
  have hv1 : 0 ≤ Coordinates.V1 x := hn 36 (by norm_num)
  have hr1 : 0 ≤ Coordinates.Red1 x := hn 40 (by norm_num)
  have he1 : 0 ≤ Coordinates.ell1 x := hn 44 (by norm_num)
  have hk1 : (1/6:ℝ) ≤ Coordinates.k1 := by norm_num [Coordinates.k1]
  have hi1 : Coordinates.inner1 ≤ 1 := by norm_num [Coordinates.inner1]
  have hkne1 : Coordinates.k1≠0 := by norm_num [Coordinates.k1]
  have hd1 : 6*Coordinates.k1*Coordinates.d1 x =
      Coordinates.gap1 x+6*Coordinates.inner1*Coordinates.a1 x := by
    dsimp only [Coordinates.d1]
    field_simp [hkne1]
  have hcap1 : Coordinates.A1 x ≤ Coordinates.capA1 x := by
    dsimp only [Coordinates.capA1]
    linarith only [hp0]
  have hg1 : Coordinates.gap1 x = Coordinates.capA1 x+(6*Coordinates.k1-1)*Coordinates.z1 x-
      Coordinates.inner1*Coordinates.U1 x+0 := by
    dsimp only [Coordinates.gap1]
    ring
  have hp1 := deleted_region_from_actual_coordinates hcap1 hk1 hi1 hv1 hr1 he1
    (le_rfl : (0:ℝ) ≤ 0) hg1 hd1
    (show Coordinates.U2 x=Coordinates.U1 x-6*Coordinates.a1 x-Coordinates.V1 x from rfl)
    (show Coordinates.A2 x=Coordinates.A1 x-Coordinates.d1 x-Coordinates.V1 x-Coordinates.Red1 x from rfl)
    (show Coordinates.z2 x=Coordinates.z1 x-Coordinates.d1 x-Coordinates.ell1 x from rfl)
  have hv2 : 0 ≤ Coordinates.V2 x := hn 37 (by norm_num)
  have hr2 : 0 ≤ Coordinates.Red2 x := hn 41 (by norm_num)
  have he2 : 0 ≤ Coordinates.ell2 x := hn 45 (by norm_num)
  have hk2 : (1/6:ℝ) ≤ Coordinates.k2 := by norm_num [Coordinates.k2]
  have hi2 : Coordinates.inner2 ≤ 1 := by norm_num [Coordinates.inner2]
  have hkne2 : Coordinates.k2≠0 := by norm_num [Coordinates.k2]
  have hd2 : 6*Coordinates.k2*Coordinates.d2 x =
      Coordinates.gap2 x+6*Coordinates.inner2*Coordinates.a2 x := by
    dsimp only [Coordinates.d2]
    field_simp [hkne2]
  have hcap2 : Coordinates.A2 x ≤ Coordinates.capA2 x := by
    dsimp only [Coordinates.capA2]
    linarith only [hp1]
  have hg2 : Coordinates.gap2 x = Coordinates.capA2 x+(6*Coordinates.k2-1)*Coordinates.z2 x-
      Coordinates.inner2*Coordinates.U2 x+0 := by
    dsimp only [Coordinates.gap2]
    ring
  have hp2 := deleted_region_from_actual_coordinates hcap2 hk2 hi2 hv2 hr2 he2
    (le_rfl : (0:ℝ) ≤ 0) hg2 hd2
    (show Coordinates.U3 x=Coordinates.U2 x-6*Coordinates.a2 x-Coordinates.V2 x from rfl)
    (show Coordinates.A3 x=Coordinates.A2 x-Coordinates.d2 x-Coordinates.V2 x-Coordinates.Red2 x from rfl)
    (show Coordinates.z3 x=Coordinates.z2 x-Coordinates.d2 x-Coordinates.ell2 x from rfl)
  have hv3 : 0 ≤ Coordinates.V3 x := hn 38 (by norm_num)
  have hr3 : 0 ≤ Coordinates.Red3 x := hn 42 (by norm_num)
  have he3 : 0 ≤ Coordinates.ell3 x := hn 46 (by norm_num)
  have hk3 : (1/6:ℝ) ≤ Coordinates.k3 := by norm_num [Coordinates.k3]
  have hi3 : Coordinates.inner3 ≤ 1 := by norm_num [Coordinates.inner3]
  have hkne3 : Coordinates.k3≠0 := by norm_num [Coordinates.k3]
  have hd3 : 6*Coordinates.k3*Coordinates.d3 x =
      Coordinates.gap3 x+6*Coordinates.inner3*Coordinates.a3 x := by
    dsimp only [Coordinates.d3]
    field_simp [hkne3]
  have hcap3 : Coordinates.A3 x ≤ Coordinates.capA3 x := by
    dsimp only [Coordinates.capA3]
    linarith only [hp2]
  have hg3 : Coordinates.gap3 x = Coordinates.capA3 x+(6*Coordinates.k3-1)*Coordinates.z3 x-
      Coordinates.inner3*Coordinates.U3 x+0 := by
    dsimp only [Coordinates.gap3]
    ring
  have hp3 := deleted_region_from_actual_coordinates hcap3 hk3 hi3 hv3 hr3 he3
    (le_rfl : (0:ℝ) ≤ 0) hg3 hd3
    (show Coordinates.U4 x=Coordinates.U3 x-6*Coordinates.a3 x-Coordinates.V3 x from rfl)
    (show Coordinates.A4 x=Coordinates.A3 x-Coordinates.d3 x-Coordinates.V3 x-Coordinates.Red3 x from rfl)
    (show Coordinates.z4 x=Coordinates.z3 x-Coordinates.d3 x-Coordinates.ell3 x from rfl)
  exact ⟨hp0,hp1,hp2,hp3⟩

def sourceParentUnit (j : Fin 4) (x : Fin 14 → ℝ) : ℝ :=
  ![Coordinates.U0 x,Coordinates.U1 x,Coordinates.U2 x,Coordinates.U3 x] j

/-- The actual reflected OLD branch's .0038 overshoot is licensed by
root cell bounds and nonnegative physical history alone. No assumption
about this daughter's amplifier, width or reflection test is used. -/
theorem physical_reflection_overshoot (j : Fin 4) (x : Fin 14 → ℝ)
    (hroot : ∀i : Fin 48,i.val<3 → -(1/1000000000000000:ℝ) ≤ Coordinates.rows i x)
    (hphysical : ∀i : Fin 48,35 ≤ i.val → 0 ≤ Coordinates.rows i x) :
    modelLength j x+(6*Coordinates.kappa-1)*modelSlots j x-modelUnit j x ≤
      (19/5000)*sourceParentUnit j x := by
  fin_cases j
  · have hc : ∀r,-(1/1000000000000000:ℝ) ≤ eval
        (Model.constraint (SourceReflection1.selected r)) x := by
      intro r
      rw [constraint_meaning]
      have hi : (SourceReflection1.selected r).val<3 ∨ 35 ≤ (SourceReflection1.selected r).val := by
        fin_cases r <;> norm_num [SourceReflection1.selected]
      rcases hi with hi | hi
      · exact hroot _ hi
      · exact le_trans (by norm_num) (hphysical _ hi)
    have hg := SourceReflection1.robust_lower x (1/1000000000000000) le_rfl hc
    change (1568511/1000000000000000:ℝ) < (19/5000)*Coordinates.U0 x-
      (Coordinates.A1 x+(6*Coordinates.kappa-1)*Coordinates.z1 x-Coordinates.U1 x) at hg
    change Coordinates.A1 x+(6*Coordinates.kappa-1)*Coordinates.z1 x-Coordinates.U1 x ≤
      (19/5000)*Coordinates.U0 x
    linarith only [hg]
  · have hc : ∀r,-(1/1000000000000000:ℝ) ≤ eval
        (Model.constraint (SourceReflection2.selected r)) x := by
      intro r
      rw [constraint_meaning]
      have hi : (SourceReflection2.selected r).val<3 ∨ 35 ≤ (SourceReflection2.selected r).val := by
        fin_cases r <;> norm_num [SourceReflection2.selected]
      rcases hi with hi | hi
      · exact hroot _ hi
      · exact le_trans (by norm_num) (hphysical _ hi)
    have hg := SourceReflection2.robust_lower x (1/1000000000000000) le_rfl hc
    change (1568511/1000000000000000:ℝ) < (19/5000)*Coordinates.U1 x-
      (Coordinates.A2 x+(6*Coordinates.kappa-1)*Coordinates.z2 x-Coordinates.U2 x) at hg
    change Coordinates.A2 x+(6*Coordinates.kappa-1)*Coordinates.z2 x-Coordinates.U2 x ≤
      (19/5000)*Coordinates.U1 x
    linarith only [hg]
  · have hc : ∀r,-(1/1000000000000000:ℝ) ≤ eval
        (Model.constraint (SourceReflection3.selected r)) x := by
      intro r
      rw [constraint_meaning]
      have hi : (SourceReflection3.selected r).val<3 ∨ 35 ≤ (SourceReflection3.selected r).val := by
        fin_cases r <;> norm_num [SourceReflection3.selected]
      rcases hi with hi | hi
      · exact hroot _ hi
      · exact le_trans (by norm_num) (hphysical _ hi)
    have hg := SourceReflection3.robust_lower x (1/1000000000000000) le_rfl hc
    change (1568511/1000000000000000:ℝ) < (19/5000)*Coordinates.U2 x-
      (Coordinates.A3 x+(6*Coordinates.kappa-1)*Coordinates.z3 x-Coordinates.U3 x) at hg
    change Coordinates.A3 x+(6*Coordinates.kappa-1)*Coordinates.z3 x-Coordinates.U3 x ≤
      (19/5000)*Coordinates.U2 x
    linarith only [hg]
  · have hc : ∀r,-(1/1000000000000000:ℝ) ≤ eval
        (Model.constraint (SourceReflection4.selected r)) x := by
      intro r
      rw [constraint_meaning]
      have hi : (SourceReflection4.selected r).val<3 ∨ 35 ≤ (SourceReflection4.selected r).val := by
        fin_cases r <;> norm_num [SourceReflection4.selected]
      rcases hi with hi | hi
      · exact hroot _ hi
      · exact le_trans (by norm_num) (hphysical _ hi)
    have hg := SourceReflection4.robust_lower x (1/1000000000000000) le_rfl hc
    change (1568511/1000000000000000:ℝ) < (19/5000)*Coordinates.U3 x-
      (Coordinates.A4 x+(6*Coordinates.kappa-1)*Coordinates.z4 x-Coordinates.U4 x) at hg
    change Coordinates.A4 x+(6*Coordinates.kappa-1)*Coordinates.z4 x-Coordinates.U4 x ≤
      (19/5000)*Coordinates.U3 x
    linarith only [hg]

/-- Convert the paid global gate to the SAME widened local unit used
by the native reflected-energy theorem. -/
theorem actual_reflection_capacity_of_physical
    (j : Fin 4) (x : Fin 14 → ℝ) (parentUnit u n1 n2 z : ℝ)
    (hparent : 0<parentUnit) (hparentEq : parentUnit=sourceParentUnit j x)
    (hunit : parentUnit*u=modelUnit j x)
    (hA : parentUnit*(n1+n2+z)=modelLength j x)
    (hz : parentUnit*z=modelSlots j x)
    (hroot : ∀i : Fin 48,i.val<3 → -(1/1000000000000000:ℝ) ≤ Coordinates.rows i x)
    (hphysical : ∀i : Fin 48,35 ≤ i.val → 0 ≤ Coordinates.rows i x) :
    n1+n2+6*Coordinates.kappa*z ≤ u+19/5000 := by
  have hg := physical_reflection_overshoot j x hroot hphysical
  rw [←hparentEq,←hunit,←hA,←hz] at hg
  apply le_of_mul_le_mul_left ?_ hparent
  nlinarith only [hg]

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.prefixRows_of_raw_physical

#print axioms OAI.SevenEighths.Cycle153Reachable.physical_previous_regions

#print axioms OAI.SevenEighths.Cycle153Reachable.actual_reflection_capacity_of_physical
