/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.MainLowPaidMain
import Candidate.Uneven.MainHighParameters
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineScheduleData

set_option autoImplicit false
namespace OAI.SevenEighths.MainPhysical
noncomputable section
open MainLow Cycle63InitialMass
open Sil.Uneven.MainSource

def lowTarget (P : Plane) (g : GeometryAffineLowSchedule) (N : ℕ)
    (amp omega mesh : ℝ) : ℝ :=
  3*g.δ+amp+(g.μ/8+g.μ/64/2-lowReserve+g.μ/8+2*g.δ*31*N+
    (P.q/(6*incumbentKappa P))*(omega+g.μ/8)+P.q*mesh+g.μ/8)+
    g.δ+4*g.δ+g.δ+g.δ+(g.δ+3*((N:ℝ)+2)*3*g.δ)+g.δ

theorem low_target_lower (P : Plane) (g : GeometryAffineLowSchedule) (N : ℕ)
    (amp omega mesh : ℝ) (ha : 0 ≤ amp) (ho : 0 ≤ omega) (hm : 0 ≤ mesh) :
    -1 ≤ lowTarget P g N amp omega mesh := by
  have hq : 0 ≤ P.q := by have h := (parameter_gates P).1; linarith
  have hk : 0 < incumbentKappa P := (incumbent_bounds P).1
  have hp : 0 ≤ P.q/(6*incumbentKappa P)*(omega+g.μ/8) := by
    have hg := g.μ_pos.le
    positivity
  have hqm := mul_nonneg hq hm
  have hN : 0 ≤ 2*g.δ*31*(N:ℝ) := by have hd := g.δ_pos.le; positivity
  have hother : 0 ≤ 3*((N:ℝ)+2)*3*g.δ := by have hd := g.δ_pos.le; positivity
  unfold lowTarget
  norm_num [lowReserve]
  linarith [g.μ_pos,g.δ_pos]

/-- Retain the new, smaller LOW reserve explicitly instead of comparing
with the old source's larger fixed saving. -/
theorem low_target_ledger (P : Plane) (g : GeometryAffineLowSchedule)
    (n N : ℕ) (hn : n ≤ N) (amp omega mesh : ℝ)
    (hbudget : g.δ*((N:ℝ)+1) ≤ g.μ/2048)
    (hω : omega ≤ 33*g.μ/128) (hmesh : mesh ≤ g.μ/8) :
    lowTarget P g n amp omega mesh+3*g.δ-amp ≤ g.μ-lowReserve := by
  have hprice : 0 ≤ P.q/(6*incumbentKappa P) ∧ P.q/(6*incumbentKappa P) ≤ 1 := by
    cases P <;> norm_num [Plane.q,incumbentKappa,Plane.incumbent]
  have hq : 0 ≤ P.q ∧ P.q ≤ 1 := by
    have h := parameter_gates P
    constructor <;> linarith [h.1,h.2.1]
  have hωpaid : P.q/(6*incumbentKappa P)*(omega+g.μ/8) ≤ 49*g.μ/128 := by
    calc
      _ ≤ P.q/(6*incumbentKappa P)*(33*g.μ/128+g.μ/8) :=
        mul_le_mul_of_nonneg_left (by linarith : omega+g.μ/8 ≤ 33*g.μ/128+g.μ/8) hprice.1
      _ ≤ 1*(33*g.μ/128+g.μ/8) :=
        mul_le_mul_of_nonneg_right hprice.2 (by have h := g.μ_pos; positivity)
      _ = _ := by ring
  have hmeshpaid : P.q*mesh ≤ g.μ/8 := by
    calc
      _ ≤ P.q*(g.μ/8) := mul_le_mul_of_nonneg_left hmesh hq.1
      _ ≤ 1*(g.μ/8) := mul_le_mul_of_nonneg_right hq.2 (by have h := g.μ_pos; positivity)
      _ = _ := by ring
  have hn' : (n:ℝ) ≤ N := by exact_mod_cast hn
  have hδn := mul_le_mul_of_nonneg_left hn' g.δ_pos.le
  have hδpaid : (33+71*(n:ℝ))*g.δ ≤ 71*g.μ/2048 := by
    nlinarith [g.δ_pos]
  unfold lowTarget
  nlinarith [g.μ_pos]

theorem final_branch_exponents (P : Plane) (g : GeometryAffineLowSchedule)
    (n N : ℕ) (hn : n ≤ N) (amp omega mesh : ℝ)
    (hbudget : g.δ*((N:ℝ)+1) ≤ g.μ/2048)
    (hω : omega ≤ 33*g.μ/128) (hmesh : mesh ≤ g.μ/8)
    (hμ : g.μ ≤ 1/1000000000000) :
    lowTarget P g n amp omega mesh+3*g.δ-amp ≤ -(1/2000000000:ℝ) ∧
      (amp+(-MainHigh.mainHighReserve+4*g.μ-3*g.δ))+3*g.δ-amp ≤
        -(1/2000000000:ℝ) := by
  have hl := low_target_ledger P g n N hn amp omega mesh hbudget hω hmesh
  norm_num [lowReserve] at hl
  norm_num [MainHigh.mainHighReserve,highReserve,SaturatedPlain.fineHighRawFee]
  constructor <;> linarith

end
end OAI.SevenEighths.MainPhysical
