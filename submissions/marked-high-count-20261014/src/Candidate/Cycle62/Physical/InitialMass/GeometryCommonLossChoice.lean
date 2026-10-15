/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle62.Physical.InitialMass.GeometryLowLossChoice
import Candidate.Cycle62.Physical.InitialMass.GeometryHighLossChoice

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section

/-- One post-dictionary rate can pay both projector ledgers. The original
mesh and loss unit have already been chosen before the dictionary. -/
def geometryCommonDictionaryRate (μ d Bmass Bnorm U B L : ℝ) (N : ℕ) : ℝ :=
  min (geometryLowDictionaryRate μ d Bmass Bnorm U N)
    (min (geometryHighShellRate μ B L) (μ/128))

theorem geometry_common_dictionary_rate_budget
    (μ d Bmass Bnorm U B L : ℝ) (N : ℕ)
    (hμ : 0<μ) (hd : 0≤d) (hm : 0≤Bmass) (hn : 0≤Bnorm)
    (hU : 0≤U) (hB : 0≤B) (hL : 0≤L) :
    let δ:=geometryCommonDictionaryRate μ d Bmass Bnorm U B L N
    0<δ ∧ δ≤μ/128 ∧
      2*δ*d*N+Bmass*δ+Bnorm*δ+3*((N:ℝ)+2)*U*δ+8*δ≤μ ∧
      B*δ+3*L*δ+δ+8*δ≤μ := by
  intro δ
  have hlo:=geometry_low_dictionary_rate_budget μ d Bmass Bnorm U N hμ hd hm hn hU
  have hhi:=geometry_high_shell_rate_budget μ B L hμ hB hL
  have hδ : 0<δ := by
    exact lt_min hlo.1 (lt_min hhi.1 (by positivity))
  have hδlo : δ≤geometryLowDictionaryRate μ d Bmass Bnorm U N := min_le_left _ _
  have hδhi : δ≤geometryHighShellRate μ B L :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hδcap : δ≤μ/128 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨hδ,hδcap,?_,?_⟩
  · have hcoef : 0≤2*d*N+Bmass+Bnorm+3*((N:ℝ)+2)*U+8 := by positivity
    have hh:=mul_le_mul_of_nonneg_left hδlo hcoef
    nlinarith [hlo.2.2]
  · have hcoef : 0≤B+3*L+9 := by positivity
    have hh:=mul_le_mul_of_nonneg_left hδhi hcoef
    nlinarith [hhi.2.2]

end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.geometry_common_dictionary_rate_budget
