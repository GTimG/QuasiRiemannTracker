/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonRadialData
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.PrimeSlot
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceChildProfiles

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckePrimeAnnular CenteredMomentSourceMass
open CenteredMomentLattice CenteredMomentTwist
local notation "O" => HeckeFamily.O

def initialSlotProfile (W : ℝ→ℂ) (v : ℝ) (x : ℝ) : ℂ :=
  W x*(x:ℂ)^(-HeckeDyadic.shift (33/50) v)

def initialSlotBound (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : Function.support W⊆Set.Icc (1:ℝ) 2) : ℝ :=
  max 1 (SchwartzMap.seminorm ℝ 0 0 (normPowerProfile W 1 2 (by norm_num) hs hW 0))

theorem initialSlotBound_ge_one (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : Function.support W⊆Set.Icc (1:ℝ) 2) : 1≤ initialSlotBound W hW hs :=
  le_max_left _ _

theorem initialSlotProfile_support (W : ℝ→ℂ)
    (hs : Function.support W⊆Set.Icc (1:ℝ) 2) (v : ℝ) :
    Function.support (initialSlotProfile W v)⊆Set.Icc (1:ℝ) 2 := by
  intro x hx
  exact hs (mul_ne_zero_iff.mp hx).1

/-- The bound is independent of the marked-slot height. -/
theorem initialSlotProfile_norm (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : Function.support W⊆Set.Icc (1:ℝ) 2) (v x : ℝ) :
    ‖initialSlotProfile W v x‖≤ initialSlotBound W hW hs := by
  have hb : ‖W x‖≤ initialSlotBound W hW hs := by
    rw [←normPowerProfile_norm W 1 2 (by norm_num) hs hW 0 x]
    exact (SchwartzMap.norm_le_seminorm ℝ _ _).trans (le_max_right _ _)
  by_cases hw : W x=0
  · simp only [initialSlotProfile,hw,zero_mul,norm_zero]
    exact zero_le_one.trans (initialSlotBound_ge_one W hW hs)
  · have hx : 1≤x := (hs hw).1
    have hp : ‖(x:ℂ)^(-HeckeDyadic.shift (33/50) v)‖≤1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hx)]
      have he : (-HeckeDyadic.shift (33/50) v).re=-(33/50:ℝ) := by norm_num [HeckeDyadic.shift]
      rw [he]
      exact Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
    rw [initialSlotProfile,norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hp).trans hb

theorem initialSlotProfile_annular (W : ℝ→ℂ) (P v : ℝ) (I : Ideal O) :
    initialSlotProfile W v ((I.absNorm:ℝ)/P)=annularWeight W P (33/50) v I := rfl

theorem initial_sigma_fixed {ι : Type*} (σ : ι→ℝ)
    (hlo : ∀i,(33/50:ℝ)≤σ i) (hhi : ∀i,σ i≤(33/50:ℝ)) :
    σ=fun _=>33/50 := funext (fun i=>le_antisymm (hhi i) (hlo i))

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.initialSlotProfile_norm
#print axioms QRH.Record1252270103Low.initialSlotProfile_annular
