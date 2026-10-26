/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.FixedStages
import Candidate.Research.RecursiveAffine.RegionalFiniteFamily
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineFinalSchedule
import Candidate.Cycle63.Physical.InitialMass.GeometryZeroPartition

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Cycle153.RegionalSchedule
noncomputable section
open scoped Classical ContDiff
open Filter Set
open OAI.SevenEighths OAI.SevenEighths.Cycle63InitialMass
open OAI.SevenEighths.Cycle63Moment
open Cycle63.Optimization

/-- The five fixed priced stages, in physical traversal order. -/
def stage (j : Fin 5) : RegionalStage :=
  ![FixedStages.stage0, FixedStages.stage1, FixedStages.stage2,
    FixedStages.stage3, FixedStages.stage4] j

/-- The exact native loss unit depends only on the regional stage, not
on the moving rounded plane position. -/
def stageMu (S : RegionalStage) (ε : ℝ) : ℝ :=
  min (ε/128) (min (lowReserveAt S.price S.intercept S.q*1/128)
    (min ((1:ℝ)/128) (1/128)))

theorem stageMu_pos (S : RegionalStage) {ε : ℝ} (hε : 0<ε) :
    0<stageMu S ε := by
  have hr : 0<lowReserveAt S.price S.intercept S.q := by
    have h : S.q*S.intercept/S.price<1 :=
      (div_lt_one S.price_pos).mpr S.q_intercept_lt_price
    unfold lowReserveAt
    exact mul_pos lowReserveWeight_pos (by linarith)
  unfold stageMu
  positivity

theorem stageMu_cap (S : RegionalStage) (ε : ℝ) : stageMu S ε≤1/128 :=
  (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))

theorem stageMu_eq_native (S : RegionalStage) (N : ℕ)
    (i : RegionalIndex S N) (ε : ℝ) :
    @geometryLossUnit (regionalFamily S N i) 1 ε=stageMu S ε := rfl

/-- Literal native HIGH parameters, before the final density degrees and
height cutoff are known. Every subset keeps its own fixed profile bound;
the ambient cardinality budget N is fixed before the source moves. -/
def preliminary (S : RegionalStage) (W : ℝ→ℂ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ε B L : ℝ) (N : ℕ) (bound : ℕ→ℝ) (hε : 0<ε)
    (hB : 0≤B) (hL : 0≤L) (hbound : ∀k,0≤bound k) : HighSourceParameters :=
  geometryAffineFinalHighSchedule W hWs hW (stageMu S ε) B L 2 1 N bound
    (stageMu_pos S hε) hB hL (by norm_num) (by norm_num) hbound

theorem preliminary_positive_slot (S : RegionalStage) (W : ℝ→ℂ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ε B L : ℝ) (N : ℕ) (bound : ℕ→ℝ) (hε : 0<ε)
    (hB : 0≤B) (hL : 0≤L) (hbound : ∀k,0≤bound k) :
    0<(preliminary S W hWs hW ε B L N bound hε hB hL hbound).vslot :=
  (preliminary S W hWs hW ε B L N bound hε hB hL hbound).hεs

theorem preliminary_positive_plain (S : RegionalStage) (W : ℝ→ℂ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ε B L : ℝ) (N : ℕ) (bound : ℕ→ℝ) (hε : 0<ε)
    (hB : 0≤B) (hL : 0≤L) (hbound : ∀k,0≤bound k) :
    0<(preliminary S W hWs hW ε B L N bound hε hB hL hbound).vplain :=
  div_pos (preliminary S W hWs hW ε B L N bound hε hB hL hbound).hεp (by norm_num)

/-- One backward choice after all finite actual density degrees are
known. The input P contains actual native source parameters, rather
than an assumed source estimate. The cutoff is chosen before every
moving height bin, parent row or child state. -/
def commonHeight {κ : Type*} [Fintype κ] [Nonempty κ]
    (P : κ→HighSourceParameters) (J : κ→ℕ) (μ : κ→ℝ) (cap : ℝ) : ℝ :=
  (Finset.univ.inf' Finset.univ_nonempty (fun i=>
    min cap (geometryFinalHeight (μ i) (P i).d (P i).vslot (P i).vplain (J i))))/2

theorem commonHeight_gates {κ : Type*} [Fintype κ] [Nonempty κ]
    (P : κ→HighSourceParameters) (J : κ→ℕ) (μ : κ→ℝ) (cap : ℝ)
    (hμ : ∀i,0<μ i) (hcap : 0<cap) (hs : ∀i,0<(P i).vslot)
    (hp : ∀i,0<(P i).vplain) :
    0<commonHeight P J μ cap ∧ commonHeight P J μ cap≤cap ∧
      ∀i, commonHeight P J μ cap≤μ i/16 ∧
        2*commonHeight P J μ cap<(P i).d*(P i).vslot ∧
        8*commonHeight P J μ cap≤(P i).d*(P i).vslot ∧
        16*commonHeight P J μ cap≤(P i).d*(P i).vplain ∧
        2*commonHeight P J μ cap*((J i:ℝ)+1)≤μ i/8 := by
  have hg (i : κ) := geometry_final_height_gates (μ i) (P i).d
    (P i).vslot (P i).vplain (J i) (hμ i) (P i).hd (hs i) (hp i)
  have hp : 0<commonHeight P J μ cap := by
    unfold commonHeight
    apply div_pos _ (by norm_num)
    exact (Finset.lt_inf'_iff _).mpr (fun i _=>lt_min hcap (hg i).1)
  have hle (i : κ) : 2*commonHeight P J μ cap≤
      min cap (geometryFinalHeight (μ i) (P i).d (P i).vslot (P i).vplain (J i)) := by
    have h := Finset.inf'_le (fun i=>min cap
      (geometryFinalHeight (μ i) (P i).d (P i).vslot (P i).vplain (J i))) (Finset.mem_univ i)
    change 2*((Finset.univ.inf' Finset.univ_nonempty _)/2)≤_
    linarith
  let i₀ : κ := Classical.choice inferInstance
  refine ⟨hp,by linarith [(hle i₀).trans (min_le_left _ _)],?_⟩
  intro i
  have hb := (hle i).trans (min_le_right _ _)
  have ht : commonHeight P J μ cap≤
      geometryFinalHeight (μ i) (P i).d (P i).vslot (P i).vplain (J i) := by linarith
  have hh := hg i
  have hJ : 0≤(J i:ℝ)+1 := by positivity
  refine ⟨ht.trans hh.2.1,?_,?_,?_,?_⟩
  · nlinarith [hh.2.2.1]
  · linarith [hh.2.2.1]
  · linarith [hh.2.2.2.1]
  · nlinarith [mul_le_mul_of_nonneg_right ht hJ,hh.2.2.2.2]

/-- Child cutoffs decrease by eight at each actual affine edge. The
fixed five-stage schedule is finite; no infinite iteration is assumed. -/
def depthHeight (τ : ℝ) (j : Fin 5) : ℝ := τ/(8:ℝ)^j.val

theorem depthHeight_pos {τ : ℝ} (hτ : 0<τ) (j : Fin 5) : 0<depthHeight τ j := by
  unfold depthHeight
  positivity

theorem depthHeight_le {τ : ℝ} (hτ : 0≤τ) (j : Fin 5) : depthHeight τ j≤τ := by
  unfold depthHeight
  exact div_le_self hτ (one_le_pow₀ (by norm_num))

theorem depthHeight_next (τ : ℝ) (j : Fin 4) :
    depthHeight τ j.succ=depthHeight τ j.castSucc/8 := by
  simp only [depthHeight, Fin.val_succ, Fin.val_castSucc, pow_succ, div_div]

/-- Replace only the height exponent. All native e/κ, source errors,
profiles, scales and supply bounds remain the same parameters. -/
def withHeight (P : HighSourceParameters) (τ : ℝ) (hτ : 0<τ) : HighSourceParameters :=
  { P with τ:=τ, hτ:=hτ }

/-- The exact native LOW schedule uses the same selector buffer, κ,
cutoff and dictionary rate as its HIGH schedule at this stage. -/
def lowSchedule (S : RegionalStage) (W : ℝ→ℂ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ε B L : ℝ) (N : ℕ) (bound : ℕ→ℝ) (hε : 0<ε)
    (hB : 0≤B) (hL : 0≤L) (hbound : ∀k,0≤bound k)
    (τ : ℝ) (hτ : 0<τ)
    (hcutoff : 2*τ<31*(preliminary S W hWs hW ε B L N bound hε hB hL hbound).vslot) :
    GeometryAffineLowSchedule :=
  let P := withHeight (preliminary S W hWs hW ε B L N bound hε hB hL hbound) τ hτ
  geometryAffineLowScheduleOfHigh P (stageMu S ε) (stageMu_pos S hε) (stageMu_cap S ε)
    (geometry_final_dictionary_budgets (stageMu S ε) 31 3 4 3 B L N
      (stageMu_pos S hε) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hB hL).2.2.1
    rfl rfl hcutoff

end
end Cycle153.RegionalSchedule

#print axioms Cycle153.RegionalSchedule.stageMu_eq_native
#print axioms Cycle153.RegionalSchedule.commonHeight_gates
#print axioms Cycle153.RegionalSchedule.depthHeight_next
#print axioms Cycle153.RegionalSchedule.lowSchedule
