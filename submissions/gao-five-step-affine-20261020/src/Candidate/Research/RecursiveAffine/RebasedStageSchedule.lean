/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.RegionalStageSchedule

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Cycle153.RegionalSchedule
noncomputable section
open Filter
open OAI.SevenEighths OAI.SevenEighths.Cycle63InitialMass

/-- The last of the five local cutoffs is the smallest. -/
theorem depthHeight_last_le {τ : ℝ} (hτ : 0≤τ) (j : Fin 5) :
    depthHeight τ ⟨4,by decide⟩≤depthHeight τ j := by
  have hpow : (8:ℝ)^j.val≤(8:ℝ)^4 :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  exact div_le_div_of_nonneg_left hτ (by positivity) hpow

/-- Shared original-base exponent for the actual real zero-height Tz.
The positive lower bound Umin is paid before a base Z^U is selected. -/
def rootHeight (Umin τ : ℝ) : ℝ := Umin*depthHeight τ ⟨4,by decide⟩/16

theorem rootHeight_pos {Umin τ : ℝ} (hUmin : 0<Umin) (hτ : 0<τ) :
    0<rootHeight Umin τ := by
  unfold rootHeight
  exact div_pos (mul_pos hUmin (depthHeight_pos hτ _)) (by norm_num)

theorem rootHeight_exponent {Umin τ U : ℝ}
    (hUmin : 0<Umin) (hτ : 0<τ) (hU : Umin≤U) (j : Fin 5) :
    3*rootHeight Umin τ≤U*depthHeight τ j := by
  have hl := depthHeight_last_le hτ.le j
  have hp := depthHeight_pos hτ (⟨4,by decide⟩ : Fin 5)
  have hj := depthHeight_pos hτ j
  calc
    3*rootHeight Umin τ≤Umin*depthHeight τ ⟨4,by decide⟩ := by
      unfold rootHeight
      nlinarith [mul_pos hUmin hp]
    _ ≤ Umin*depthHeight τ j := mul_le_mul_of_nonneg_left hl hUmin.le
    _ ≤ U*depthHeight τ j := mul_le_mul_of_nonneg_right hU hj.le

/-- This is the actual unchanged-height rebase gate. One threshold,
chosen before U and j move, transports the same bound
Tz=3 Z^τT Z^τT into every actual child base Z^U, U≥Umin.
The exponent τT is not incorrectly reused as a local exponent. -/
theorem eventually_root_height_rebased (Umin τ : ℝ)
    (hUmin : 0<Umin) (hτ : 0<τ) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧ ∀U : ℝ,Umin≤U → ∀j : Fin 5,
      3*Z^(rootHeight Umin τ)*Z^(rootHeight Umin τ)≤
        (Z^U)^(depthHeight τ j) := by
  have hr := rootHeight_pos hUmin hτ
  filter_upwards [(tendsto_rpow_atTop hr).eventually (eventually_ge_atTop (3:ℝ)),
    eventually_gt_atTop (1:ℝ)] with Z hthree hZ
  refine ⟨hZ,?_⟩
  intro U hU j
  have hz : 0<Z := zero_lt_one.trans hZ
  have hp : 0≤Z^(rootHeight Umin τ) := Real.rpow_nonneg hz.le _
  calc
    3*Z^(rootHeight Umin τ)*Z^(rootHeight Umin τ)≤
        Z^(rootHeight Umin τ)*Z^(rootHeight Umin τ)*Z^(rootHeight Umin τ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hthree hp) hp
    _ = Z^(3*rootHeight Umin τ) := by
      rw [←Real.rpow_add hz,←Real.rpow_add hz]
      congr 1
      ring
    _ ≤ (Z^U)^(depthHeight τ j) := by
      rw [←Real.rpow_mul hz.le]
      exact Real.rpow_le_rpow_of_exponent_le hZ.le (rootHeight_exponent hUmin hτ hU j)

/-- Actual source slot mesh, distinct from the regional coordinate grid.
It pays the normalized slot weights w/U at every rebased stage. -/
def rootPrimeMesh (Umin μ : ℝ) : ℝ :=
  Umin*min (μ/8) (Cycle25.Energy.commonMesh 2 28 1 (μ/8))

theorem rootPrimeMesh_pos {Umin μ : ℝ} (hU : 0<Umin) (hμ : 0<μ) :
    0<rootPrimeMesh Umin μ := by
  unfold rootPrimeMesh
  apply mul_pos hU
  exact lt_min (by positivity) (Cycle25.Energy.commonMesh_pos 2 28 1 (μ/8)
    (by norm_num) (by norm_num) (by positivity))

theorem rebased_weight_gates {Umin μ U w : ℝ}
    (hUmin : 0<Umin) (hμ : 0<μ) (hU : Umin≤U)
    (hw : w≤rootPrimeMesh Umin μ) :
    w/U≤μ/8 ∧ w/U≤Cycle25.Energy.commonMesh 2 28 1 (μ/8) := by
  have hUp : 0<U := hUmin.trans_le hU
  have hlocal : w/U≤ min (μ/8) (Cycle25.Energy.commonMesh 2 28 1 (μ/8)) := by
    rw [div_le_iff₀ hUp]
    exact hw.trans (by
      unfold rootPrimeMesh
      have hm : 0≤ min (μ/8) (Cycle25.Energy.commonMesh 2 28 1 (μ/8)) := by
        exact le_min (by positivity) ((Cycle25.Energy.commonMesh_pos 2 28 1 (μ/8)
          (by norm_num) (by norm_num) (by positivity)).le)
      nlinarith [mul_le_mul_of_nonneg_right hU hm])
  exact ⟨hlocal.trans (min_le_left _ _),hlocal.trans (min_le_right _ _)⟩

end
end Cycle153.RegionalSchedule

#print axioms Cycle153.RegionalSchedule.eventually_root_height_rebased
#print axioms Cycle153.RegionalSchedule.rootPrimeMesh_pos
#print axioms Cycle153.RegionalSchedule.rebased_weight_gates
