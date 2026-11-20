/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
One early finite frame bank pays all actual selected slot counts and both
physical parts. Profile/height data and positive source fees may follow it. -/
import Candidate.C092.transport.ActualStageFrameBudgetData
import Candidate.C092.transport.ActualStageFrameBudgetSelect
import Candidate.C092.transport.ActualStageFrameBudgetHorizon
import Candidate.C092.transport.OrderedPairActualRestoredModulus
import Candidate.C092.transport.PairedRetainedBudgetLambda
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ActualStageFrameBudget
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentCommonProfile
open QRH.SilDensitySplit.CubeFree.FP
open QRH.Cycle092.PairedRetainedBudget

abbrev FrameBank (N:ℕ) := Fin (N+1) × Bool

def commonJ {N:ℕ} (j:FrameBank N→ℕ) : ℕ := Finset.univ.sup j

def commonDegree {N:ℕ} (j degree:FrameBank N→ℕ) : ℕ :=
  max (Finset.univ.sup degree) (2*commonJ j)

def commonControls {N:ℕ} (S:FrameBank N→Finset (ℕ×ℕ)) : Finset (ℕ×ℕ) :=
  {(0,0)} ∪ Finset.univ.biUnion S

/-- This bank is finite before all scales, RootShape hits and positive
Cz/Ct values. It includes the empty surviving mark set. -/
theorem finite_bank_parameters (N:ℕ) (j degree:FrameBank N→ℕ)
    (S:FrameBank N→Finset (ℕ×ℕ)) :
    (0,0)∈commonControls S ∧ ∀k:FrameBank N,
      j k ≤ commonJ j ∧ degree k ≤ commonDegree j degree ∧
      2*j k ≤ commonDegree j degree ∧ S k⊆commonControls S := by
  refine ⟨Finset.mem_union_left _ (by simp),?_⟩
  intro k
  have hj:j k ≤ commonJ j:=Finset.le_sup (Finset.mem_univ k)
  refine ⟨hj,(Finset.le_sup (Finset.mem_univ k)).trans (le_max_left _ _),
    (Nat.mul_le_mul_left 2 hj).trans (le_max_right _ _),?_⟩
  intro a ha
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k,Finset.mem_univ _,ha⟩)

/-- The exact original independent pitches are retained. No height ceiling
or late source constant is used in the choice of the degree or controls. -/
theorem bank_profile_height (N:ℕ) (j degree:FrameBank N→ℕ)
    (S:FrameBank N→Finset (ℕ×ℕ)) (k:FrameBank N)
    (W₁ W₂:𝓢(ℝ,ℂ)) (t₁ t₂ height:ℝ) (hh:0 ≤ height) :
    (sourceControl (S k) W₁*sourceControl (S k) W₂)^2*(2+‖t₁‖+‖t₂‖)^(2*j k) ≤
      (2:ℝ)^(2*commonJ j)*(sourceControl (commonControls S) W₁*
        sourceControl (commonControls S) W₂)^2*
          (1+|t₁|+|t₂|+height)^(commonDegree j degree) := by
  have hk:=(finite_bank_parameters N j degree S).2 k
  have hc₁:sourceControl (S k) W₁ ≤ sourceControl (commonControls S) W₁:=
    Seminorm.le_def.mp (Finset.sup_mono hk.2.2.2) W₁
  have hc₂:sourceControl (S k) W₂ ≤ sourceControl (commonControls S) W₂:=
    Seminorm.le_def.mp (Finset.sup_mono hk.2.2.2) W₂
  have hc:=mul_le_mul hc₁ hc₂ (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hH:1 ≤ 1+|t₁|+|t₂|+height:=by linarith [abs_nonneg t₁,abs_nonneg t₂]
  have hbase:2+‖t₁‖+‖t₂‖ ≤ 2*(1+|t₁|+|t₂|+height):=by
    simp only [Real.norm_eq_abs];linarith [abs_nonneg t₁,abs_nonneg t₂]
  have hpow:(2+‖t₁‖+‖t₂‖)^(2*j k) ≤
      (2:ℝ)^(2*commonJ j)*(1+|t₁|+|t₂|+height)^(commonDegree j degree):=by
    calc
      _ ≤ (2*(1+|t₁|+|t₂|+height))^(2*j k):=pow_le_pow_left₀ (by positivity) hbase _
      _ = (2:ℝ)^(2*j k)*(1+|t₁|+|t₂|+height)^(2*j k):=mul_pow _ _ _
      _ ≤ _:=mul_le_mul (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left 2 hk.1))
        (pow_le_pow_right₀ hH hk.2.2.1) (by positivity) (by positivity)
  have hctl0:0 ≤ sourceControl (S k) W₁*sourceControl (S k) W₂:=mul_nonneg
    (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  exact (mul_le_mul (pow_le_pow_left₀ hctl0 hc 2) hpow (by positivity) (by positivity)).trans_eq
    (by ring)

#print axioms finite_bank_parameters
#print axioms bank_profile_height
end
end QRH.Cycle092.ActualStageFrameBudget
