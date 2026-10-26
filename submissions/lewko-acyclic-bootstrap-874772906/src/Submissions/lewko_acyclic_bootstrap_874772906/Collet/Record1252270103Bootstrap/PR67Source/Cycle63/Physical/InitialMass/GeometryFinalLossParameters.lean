import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryCommonLossChoice
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryFinalParameters
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section

/-- The post-dictionary rate also pays the ambient slot count. -/
def geometryFinalDictionaryRate (μ d Bmass Bnorm U B Lproj : ℝ) (N : ℕ) : ℝ :=
  min (geometryCommonDictionaryRate μ d Bmass Bnorm U B Lproj N)
    (μ/(64*(d+1)*((N:ℝ)+1)))

def geometryFinalPlainRate (μ d : ℝ) : ℝ := μ/(64*(d+1))

/-- This rate pays dictionary multiplicity; the coarse source loss is μ/8. -/
def geometryFinalErrorDictionaryRate (μ : ℝ) (N : ℕ) : ℝ := μ/(8*((N:ℝ)+1))

def geometryFinalMassRate (μ δ Bmass : ℝ) : ℝ := min δ (μ/(8*(Bmass+1)))

theorem geometry_final_dictionary_budgets
    (μ d Bmass Bnorm U B Lproj : ℝ) (N : ℕ)
    (hμ : 0<μ) (hd : 0≤d) (hm : 0≤Bmass) (hn : 0≤Bnorm)
    (hU : 0≤U) (hB : 0≤B) (hL : 0≤Lproj) :
    let δ := geometryFinalDictionaryRate μ d Bmass Bnorm U B Lproj N
    let εplain := geometryFinalPlainRate μ d
    0<δ ∧ δ≤geometryCommonDictionaryRate μ d Bmass Bnorm U B Lproj N ∧
      δ≤μ/128 ∧ 0<εplain ∧
      2*δ*d*N+Bmass*δ+Bnorm*δ+3*((N:ℝ)+2)*U*δ+8*δ≤μ ∧
      B*δ+3*Lproj*δ+δ+8*δ≤μ ∧
      2*δ*d*N≤μ/32 ∧ 2*d*εplain≤μ/32 ∧
      μ/16+2*d*εplain+2*d*N*δ≤μ/4 := by
  intro δ εplain
  have common := geometry_common_dictionary_rate_budget μ d Bmass Bnorm U B Lproj N
    hμ hd hm hn hU hB hL
  have small := geometry_dictionary_loss_budgets μ d Bmass N hμ hd hm
  rcases small with ⟨hp,hs,he,hma,hplain,hslot,herror,hmass,hjoined⟩
  have hδc : δ≤geometryCommonDictionaryRate μ d Bmass Bnorm U B Lproj N :=
    min_le_left _ _
  have hδs : δ≤μ/(64*(d+1)*((N:ℝ)+1)) := min_le_right _ _
  have hδ : 0<δ := lt_min common.1 hs
  have hlowcoef : 0≤2*d*N+Bmass+Bnorm+3*((N:ℝ)+2)*U+8 := by positivity
  have hhighcoef : 0≤B+3*Lproj+9 := by positivity
  have hlo := mul_le_mul_of_nonneg_left hδc hlowcoef
  have hhi := mul_le_mul_of_nonneg_left hδc hhighcoef
  have hslot' := mul_le_mul_of_nonneg_left hδs (show 0≤2*d*N by positivity)
  refine ⟨hδ,hδc,hδc.trans common.2.1,hp,?_,?_,?_,hplain,?_⟩
  · nlinarith only [hlo,common.2.2.1]
  · nlinarith only [hhi,common.2.2.2]
  · nlinarith only [hslot',hslot]
  · change μ/16+2*d*(μ/(64*(d+1)))+2*d*N*δ≤μ/4
    nlinarith only [hslot',hjoined]

theorem geometry_final_error_dictionary_budget (μ : ℝ) (N : ℕ) (hμ : 0<μ) :
    0<geometryFinalErrorDictionaryRate μ N ∧
      ∀n : ℕ,n≤N → geometryFinalErrorDictionaryRate μ N*n≤μ/8 := by
  have ratepos : 0<geometryFinalErrorDictionaryRate μ N := by
    unfold geometryFinalErrorDictionaryRate
    positivity
  refine ⟨ratepos,?_⟩
  intro n hn
  have small := geometry_dictionary_loss_budgets μ 0 0 N hμ le_rfl le_rfl
  have hbudget := small.2.2.2.2.2.2.1
  have hcast : (n:ℝ)≤N := by exact_mod_cast hn
  have hle := mul_le_mul_of_nonneg_left hcast ratepos.le
  change (N:ℝ)*geometryFinalErrorDictionaryRate μ N≤μ/8 at hbudget
  nlinarith only [hle,hbudget]

theorem geometry_final_mass_dictionary_budget
    (μ δ Bmass : ℝ) (hμ : 0<μ) (hδ : 0<δ) (hm : 0≤Bmass) :
    0<geometryFinalMassRate μ δ Bmass ∧ geometryFinalMassRate μ δ Bmass≤δ ∧
      Bmass*geometryFinalMassRate μ δ Bmass≤μ/8 := by
  have hbase : 0<μ/(8*(Bmass+1)) := by positivity
  have hc := div_mul_cancel₀ μ (by positivity : (8*(Bmass+1))≠0)
  have hle := mul_le_mul_of_nonneg_left
    (min_le_right δ (μ/(8*(Bmass+1)))) hm
  refine ⟨lt_min hδ hbase,min_le_left _ _,?_⟩
  change Bmass*min δ (μ/(8*(Bmass+1)))≤μ/8
  nlinarith only [hc,hbase,hle]

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
