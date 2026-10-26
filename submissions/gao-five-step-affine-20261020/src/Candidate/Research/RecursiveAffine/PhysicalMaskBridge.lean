/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.ReachableNode
import Candidate.Research.RecursiveAffine.Geometry.SourceDomainAudit
import Candidate.Research.RecursiveAffine.NativePunctureSource

set_option autoImplicit false
set_option maxHeartbeats 0
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle153Geometry Cycle153ReachableGeometry

/-- The fixed mask gate uses the already constructed prefix only. -/
theorem physical_mask_budget (j : Fin 4) (x : Fin 14 → ℝ)
    (hp : PrefixRows (j.val+1) x) :
    modelMissing j x+modelReduction j x+((j.val:ℝ)+1)/1000000000000000 ≤
      20*modelUnit j x := by
  fin_cases j
  · have hc : ∀r,-(1/1000000000000000:ℝ) ≤ eval
        (Model.constraint (SourceMask1.selected r)) x := by
      intro r
      rw [constraint_meaning]
      exact hp (SourceMask1.selected r) (SourceMask1.prefix_admissible r)
    have hg := SourceMask1.robust_lower x (1/1000000000000000) le_rfl hc
    change (1568511/1000000000000000:ℝ) <
      (20*Coordinates.U1 x-Coordinates.historicalMissing1 x-Coordinates.historicalReduction1 x)/1000 at hg
    norm_num only
    change Coordinates.historicalMissing1 x+Coordinates.historicalReduction1 x+
      (1:ℝ)/1000000000000000 ≤ 20*Coordinates.U1 x
    linarith only [hg]
  · have hc : ∀r,-(1/1000000000000000:ℝ) ≤ eval
        (Model.constraint (SourceMask2.selected r)) x := by
      intro r
      rw [constraint_meaning]
      exact hp (SourceMask2.selected r) (SourceMask2.prefix_admissible r)
    have hg := SourceMask2.robust_lower x (1/1000000000000000) le_rfl hc
    change (1568511/1000000000000000:ℝ) <
      (20*Coordinates.U2 x-Coordinates.historicalMissing2 x-Coordinates.historicalReduction2 x)/1000 at hg
    norm_num only
    change Coordinates.historicalMissing2 x+Coordinates.historicalReduction2 x+
      (1:ℝ)/500000000000000 ≤ 20*Coordinates.U2 x
    linarith only [hg]
  · have hc : ∀r,-(1/1000000000000000:ℝ) ≤ eval
        (Model.constraint (SourceMask3.selected r)) x := by
      intro r
      rw [constraint_meaning]
      exact hp (SourceMask3.selected r) (SourceMask3.prefix_admissible r)
    have hg := SourceMask3.robust_lower x (1/1000000000000000) le_rfl hc
    change (1568511/1000000000000000:ℝ) <
      (20*Coordinates.U3 x-Coordinates.historicalMissing3 x-Coordinates.historicalReduction3 x)/1000 at hg
    norm_num only
    change Coordinates.historicalMissing3 x+Coordinates.historicalReduction3 x+
      (3:ℝ)/1000000000000000 ≤ 20*Coordinates.U3 x
    linarith only [hg]
  · have hc : ∀r,-(1/1000000000000000:ℝ) ≤ eval
        (Model.constraint (SourceMask4.selected r)) x := by
      intro r
      rw [constraint_meaning]
      exact hp (SourceMask4.selected r) (SourceMask4.prefix_admissible r)
    have hg := SourceMask4.robust_lower x (1/1000000000000000) le_rfl hc
    change (1568511/1000000000000000:ℝ) <
      (20*Coordinates.U4 x-Coordinates.historicalMissing4 x-Coordinates.historicalReduction4 x)/1000 at hg
    norm_num only
    change Coordinates.historicalMissing4 x+Coordinates.historicalReduction4 x+
      (1:ℝ)/250000000000000 ≤ 20*Coordinates.U4 x
    linarith only [hg]

/-- Convert the genuine global puncture-history invariant into the
native rebased mask20 cap. The coarse cap of the parent is not reused. -/
theorem actual_child_mask_of_history
    {α : Type} [Fintype α] [DecidableEq α]
    {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
    (C : SourceContext (α:=α) M H) (j : Fin 4) (x : Fin 14 → ℝ)
    (unit : ℝ) (hunit : unit=modelUnit j x)
    (P : Ideal O) (hP : P≠0) (hp : PrefixRows (j.val+1) x)
    (hlog : Real.logb C.globalBase (P.absNorm:ℝ) ≤
      modelMissing j x+modelReduction j x+((j.val:ℝ)+1)/1000000000000000) :
    (P.absNorm:ℝ) ≤ (C.globalBase^unit)^(20:ℝ) := by
  apply Cycle153RegionalLow.actual_puncture_mask20_of_log_budget P hP C.globalBase unit
    (modelMissing j x+modelReduction j x+((j.val:ℝ)+1)/1000000000000000)
    C.globalBase_gt_one hlog
  rw [hunit]
  exact physical_mask_budget j x hp

/-- Exact change of logarithmic base, retaining the actual physical
unit. It globalizes the native puncture-capacity receipt. -/
theorem unit_mul_logb_rebase {Z unit a : ℝ} (hZ : 1<Z) (hu : 0<unit) :
    unit*Real.logb (Z^unit) a=Real.logb Z a := by
  have hlog : Real.log Z≠0 := ne_of_gt (Real.log_pos hZ)
  rw [Real.logb,Real.logb,Real.log_rpow (zero_lt_one.trans hZ)]
  field_simp [hlog,ne_of_gt hu]

/-- A native local increment gives exactly the global increment used
by the inherited source mask. No new norm estimate is assumed. -/
theorem global_puncture_increment {Z unit child parent v red pad : ℝ}
    (hZ : 1<Z) (hu : 0<unit)
    (h : Real.logb (Z^unit) child ≤ Real.logb (Z^unit) parent+v+red+pad) :
    Real.logb Z child ≤ Real.logb Z parent+unit*v+unit*red+unit*pad := by
  have hm := mul_le_mul_of_nonneg_left h hu.le
  rw [mul_add,mul_add,mul_add,unit_mul_logb_rebase hZ hu,
    unit_mul_logb_rebase hZ hu] at hm
  exact hm

/-- Propagate the genuine inherited puncture budget at one physical
edge. The increment is the preceding native capacity receipt, and the
finite pad is explicitly scheduled. -/
theorem puncture_history_step
    {α : Type} [Fintype α] [DecidableEq α]
    {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
    {C : SourceContext (α:=α) M H} {j k : Fin 4} (N : ReachableNode C j)
    (x : Fin 14 → ℝ) (hk : k.val=j.val+1)
    (P : Ideal O) (V Red pad : ℝ)
    (hinc : Real.logb C.globalBase (P.absNorm:ℝ) ≤
      Real.logb C.globalBase (N.state.puncture.absNorm:ℝ)+V+Red+pad)
    (hcoords : modelMissing k x+modelReduction k x=
      modelMissing j N.coordinates+modelReduction j N.coordinates+V+Red)
    (hpad : pad ≤ 1/1000000000000000) :
    Real.logb C.globalBase (P.absNorm:ℝ) ≤
      modelMissing k x+modelReduction k x+((k.val:ℝ)+1)/1000000000000000 := by
  have hn := N.puncture_global_log
  have hindex : (k.val:ℝ)=(j.val:ℝ)+1 := by exact_mod_cast hk
  rw [hcoords,hindex]
  linarith only [hn,hinc,hpad]

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.actual_child_mask_of_history
#print axioms OAI.SevenEighths.Cycle153Reachable.puncture_history_step
