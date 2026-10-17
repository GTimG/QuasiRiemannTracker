/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineFinalSchedule

set_option autoImplicit false
set_option maxHeartbeats 60000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical ContDiff
open Cycle63Moment

/-- Fix the common low selector after all subset density degrees are known.
The high profiles remain subset-specific; only the scalar dictionary rate
uses the ambient count. No physical source or Fourier datum is changed. -/
theorem geometry_affine_uniform_schedule {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (μ B L bΦ : ℝ) (N : ℕ) (bound : Finset α→ℕ→ℝ) (J : Finset α→ℕ)
    (hμ : 0<μ) (hμcap : μ≤1/128) (hB : 0≤B) (hL : 0≤L) (hbΦ : 0≤bΦ)
    (hbound : ∀T k,0≤bound T k) :
    ∃τ : ℝ, ∃hτ : 0<τ, τ≤μ/16 ∧ ∃g : GeometryAffineLowSchedule,
      g.μ=μ ∧ g.δ=geometryFinalDictionaryRate μ 31 3 4 3 B L N ∧ g.τ=τ ∧
      ∀T : Finset α,
        let P:=geometryAffineFinalHighSchedule W hWs hW μ B L bΦ τ N (bound T)
          hμ hB hL hbΦ hτ (hbound T)
        P.profileBound=bound T ∧ g.e=P.e ∧ g.κ=P.κ ∧ g.vslot=P.vslot ∧
          8*P.τ≤P.d*P.vslot ∧ 16*P.τ≤P.d*P.vplain ∧
          2*P.τ*((J T:ℝ)+1)≤μ/8 := by
  let P₀ := fun T : Finset α=>
    geometryAffineFinalHighSchedule W hWs hW μ B L bΦ 1 N (bound T)
      hμ hB hL hbΦ (by norm_num) (hbound T)
  have rates := geometry_final_dictionary_budgets μ 31 3 4 3 B L N
    hμ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hB hL
  have hs (T : Finset α) : 0<(P₀ T).vslot := rates.1
  have hp (T : Finset α) : 0<(P₀ T).vplain := by
    change 0<geometryFinalPlainRate μ 31/8
    exact div_pos rates.2.2.2.1 (by norm_num)
  obtain ⟨τ,hτ,hτcap,hgates⟩ := geometry_uniform_high_height P₀ J μ hμ hs hp
  let P := fun T : Finset α=>
    geometryAffineFinalHighSchedule W hWs hW μ B L bΦ τ N (bound T)
      hμ hB hL hbΦ hτ (hbound T)
  have hcutoff : 2*(P ∅).τ<(P ∅).d*(P ∅).vslot := (hgates ∅).1
  let g := geometryAffineLowScheduleOfHigh (P ∅) μ hμ hμcap rates.2.2.1 rfl rfl hcutoff
  refine ⟨τ,hτ,hτcap,g,rfl,rfl,rfl,?_⟩
  intro T
  exact ⟨rfl,rfl,rfl,rfl,(hgates T).2.1,(hgates T).2.2.1,(hgates T).2.2.2⟩

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_affine_uniform_schedule
