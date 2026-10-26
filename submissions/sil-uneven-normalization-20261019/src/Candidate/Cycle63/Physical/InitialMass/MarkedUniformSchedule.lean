import Candidate.Cycle63.Physical.InitialMass.MarkedSchedule
import Candidate.Cycle63.Physical.InitialMass.MarkedParameterSchedule

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open scoped Classical ContDiff
open Cycle63Moment Cycle63InitialMass

/-- A common cutoff, chosen after the finite family of density degrees,
preserves the existing physical selector and also meets every marked
witness gate.  Its mesh was fixed independently in `markedGeometryMesh`. -/
theorem geometry_affine_marked_uniform_schedule {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (μ B L bΦ : ℝ) (N : ℕ) (bound : Finset α→ℕ→ℝ) (J : Finset α→ℕ)
    (hμ : 0<μ) (hμcap : μ≤1/100000000) (hB : 0≤B) (hL : 0≤L) (hbΦ : 0≤bΦ)
    (hbound : ∀T k,0≤bound T k) :
    ∃τ : ℝ, ∃hτ : 0<τ, τ≤μ/16 ∧ τ< markedCoreMin/2 ∧
      4*τ< markedCoreMin*markedWitnessRate ∧ ∃g : GeometryAffineLowSchedule,
      g.μ=μ ∧ g.δ=geometryFinalDictionaryRate μ 31 3 4 3 B L N ∧ g.τ=τ ∧
      ∀T : Finset α,
        let P:=geometryAffineFinalHighSchedule W hWs hW μ B L bΦ τ N (bound T)
          hμ hB hL hbΦ hτ (hbound T)
        P.profileBound=bound T ∧ g.e=P.e ∧ g.κ=P.κ ∧ g.vslot=P.vslot ∧
          8*P.τ≤P.d*P.vslot ∧ 16*P.τ≤P.d*P.vplain ∧
          2*P.τ*((J T:ℝ)+1)≤μ/8 ∧
          12*P.e*((22:ℝ)+2)+8*markedWitnessRate+2*markedWitnessRate≤ markedRate/2 ∧
          2*P.εslot*P.d≤ markedBinWidth*markedTinyWidth N ∧
          (2*P.εslot*P.d)*(N:ℝ)≤μ/32 := by
  let P₀ := fun T : Finset α=>
    geometryAffineFinalHighSchedule W hWs hW μ B L bΦ 1 N (bound T)
      hμ hB hL hbΦ (by norm_num) (hbound T)
  have rates := geometry_final_dictionary_budgets μ 31 3 4 3 B L N
    hμ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hB hL
  have hs (T : Finset α) : 0<(P₀ T).vslot := rates.1
  have hp (T : Finset α) : 0<(P₀ T).vplain := by
    change 0<geometryFinalPlainRate μ 31/8
    exact div_pos rates.2.2.2.1 (by norm_num)
  obtain ⟨τ₀,hτ₀,hτcap,hgates⟩ := geometry_uniform_high_height P₀ J μ hμ hs hp
  let τ := markedHeight τ₀
  have hnew := marked_height_gates τ₀ hτ₀
  have hτ : 0<τ := hnew.1
  have hle : τ≤τ₀ := hnew.2.1
  let P := fun T : Finset α=>
    geometryAffineFinalHighSchedule W hWs hW μ B L bΦ τ N (bound T)
      hμ hB hL hbΦ hτ (hbound T)
  have hcutoff : 2*(P ∅).τ<(P ∅).d*(P ∅).vslot := by
    change 2*τ<(P₀ ∅).d*(P₀ ∅).vslot
    linarith [(hgates ∅).1]
  let g := geometryAffineLowScheduleOfHigh (P ∅) μ hμ
    (hμcap.trans (by norm_num)) rates.2.2.1 rfl rfl hcutoff
  refine ⟨τ,hτ,hle.trans hτcap,hnew.2.2.1,hnew.2.2.2,g,rfl,rfl,rfl,?_⟩
  intro T
  have hg := hgates T
  have hslot : 8*(P T).τ≤(P T).d*(P T).vslot := by
    change 8*τ≤(P₀ T).d*(P₀ T).vslot
    linarith [hg.2.1]
  have hplain : 16*(P T).τ≤(P T).d*(P T).vplain := by
    change 16*τ≤(P₀ T).d*(P₀ T).vplain
    linarith [hg.2.2.1]
  have hheight : 2*(P T).τ*((J T:ℝ)+1)≤μ/8 :=
    marked_height_preserves_budget τ₀ μ (J T) hg.2.2.2
  have hm := existing_schedule_marked_gates W hWs hW μ B L bΦ τ N (bound T)
    hμ hμcap hB hL hbΦ hτ (hbound T)
  exact ⟨rfl,rfl,rfl,rfl,hslot,hplain,hheight,hm.2.1,hm.2.2.1,hm.2.2.2⟩

theorem geometry_final_marked_schedule
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (μ B L bΦ τ : ℝ) (N : ℕ) (bound : ℕ→ℝ)
    (hμ : 0<μ) (hμcap : μ≤1/100000000) (hB : 0≤B) (hL : 0≤L)
    (hbΦ : 0≤bΦ) (hτ : 0<τ) (hbound : ∀k,0≤bound k)
    (hτzero : τ< markedCoreMin/2) (hτw : 4*τ< markedCoreMin*markedWitnessRate) :
    MarkedSchedule
      (geometryAffineFinalHighSchedule W hWs hW μ B L bΦ τ N bound hμ hB hL hbΦ hτ hbound)
      N W (33/50) (33/50) := by
  have hh := existing_schedule_marked_gates W hWs hW μ B L bΦ τ N bound
    hμ hμcap hB hL hbΦ hτ hbound
  exact ⟨rfl,rfl,le_rfl,le_rfl,rfl,by norm_num [geometryAffineFinalHighSchedule,highParameters],
    hτzero,hτw,hh.2.1,hh.2.2.1⟩

end
end OAI.SevenEighths.Cycle63MarkedPlain
#print axioms OAI.SevenEighths.Cycle63MarkedPlain.geometry_affine_marked_uniform_schedule
