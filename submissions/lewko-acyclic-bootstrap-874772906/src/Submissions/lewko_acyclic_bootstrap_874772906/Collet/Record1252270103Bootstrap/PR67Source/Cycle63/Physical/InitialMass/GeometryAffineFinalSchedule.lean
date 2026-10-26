import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineScheduleData
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryFinalLowLoss
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryFinalLossParameters
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryUniformHighParameters
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.Constants
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 60000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped ContDiff
open Cycle63Moment

/-- Fixed mesh-facing caps, with the common cutoff supplied only after the
density degrees are known. The profile bound and actual subset count remain
local to the subset. -/
def geometryAffineFinalHighSchedule
    (W : ℝ → ℂ) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2)
    (hW : ContDiff ℝ ∞ W) (μ B L bΦ τ : ℝ) (N : ℕ) (bound : ℕ → ℝ)
    (hμ : 0<μ) (hB : 0≤B) (hL : 0≤L) (hbΦ : 0≤bΦ) (hτ : 0<τ)
    (hbound : ∀k,0≤bound k) : HighSourceParameters :=
  let δ := geometryFinalDictionaryRate μ 31 3 4 3 B L N
  let εplain := geometryFinalPlainRate μ 31
  let rates := geometry_final_dictionary_budgets μ 31 3 4 3 B L N
    hμ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hB hL
  let P := highParameters W 1 2 1 1 δ εplain (33/50) (33/50) bΦ 2 28 1 31
    (μ/8) 0 bound (by norm_num) hWs hW (by norm_num) (by norm_num)
    rates.1 rates.2.2.2.1 hbΦ (by norm_num) (by norm_num) (by norm_num)
    (by positivity) hbound
  { P with τ := τ, hτ := hτ }

/-- The low consumer uses the literal same selector buffer and cutoff as
the high consumer. The high slot budget supplies the low budget directly. -/
def geometryAffineLowScheduleOfHigh (P : HighSourceParameters) (μ : ℝ)
    (hμ : 0<μ) (hμcap : μ≤1/128) (hδcap : P.εslot≤μ/128)
    (hwidth : P.Rwidth=1) (hd : P.d=31) (hcutoff : 2*P.τ<P.d*P.vslot) :
    GeometryAffineLowSchedule where
  μ := μ
  δ := P.εslot
  τ := P.τ
  e := P.e
  κ := P.κ
  vslot := P.vslot
  μ_pos := hμ
  μ_cap := hμcap
  δ_pos := P.hεs
  δ_cap := hδcap
  τ_pos := P.hτ
  e_pos := P.he
  e_cap := P.he'
  κ_pos := P.hκ
  vslot_nonneg := P.hvs
  budget := by simpa only [hwidth,mul_one] using P.hslotBudget
  cutoff := by simpa only [hd] using hcutoff

/-- The degree-thirty-one schedule has a stronger cardinality cap. It
aligns the first mass even at the high coordinate ceiling B=130. -/
theorem geometry_affine_final_dictionary_mass_rate_eq (μ B L : ℝ) (N : ℕ)
    (hμ : 0<μ) (hB : 0≤B) (hBcap : B≤255) :
    let δ := geometryFinalDictionaryRate μ 31 3 4 3 B L N
    geometryFinalMassRate μ δ B=δ := by
  intro δ
  unfold geometryFinalMassRate
  apply min_eq_left
  have hsmall : δ≤μ/(64*(31+1)*((N:ℝ)+1)) := min_le_right _ _
  apply hsmall.trans
  apply div_le_div_of_nonneg_left hμ.le (by positivity)
  nlinarith only [hBcap, Nat.cast_nonneg (α:=ℝ) N]

variable [Cycle63.AffineLedger] in
/-- The exported low target pays selection, the ratio sum, and the prime
average with three copies of the same dictionary rate. -/
theorem geometry_affine_final_low_target_ledger
    (g : GeometryAffineLowSchedule) (B L : ℝ) (N : ℕ) (amp omega mesh : ℝ)
    (hB : 0≤B) (hL : 0≤L)
    (hδ : g.δ=geometryFinalDictionaryRate g.μ 31 3 4 3 B L N)
    (hω : omega≤33*g.μ/128) (hmesh : mesh≤g.μ/8) :
    geometryAffineLowTarget g N amp omega mesh+3*g.δ-amp≤
      -(Cycle63.AffineLedger.lowReserve:ℝ)+2*g.μ := by
  have hh := geometry_final_main_low_consumer_ledger g.μ 31 3 4 3 B L omega mesh amp N
    g.μ_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num) hB hL hω hmesh
  dsimp only at hh
  rw [←hδ] at hh
  dsimp only [geometryAffineLowTarget]
  nlinarith only [hh]

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
