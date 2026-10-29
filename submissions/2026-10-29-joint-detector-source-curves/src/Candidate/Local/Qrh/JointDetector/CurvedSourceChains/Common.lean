/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.CurvedStageHigh
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.ActualProvider

namespace Qrh.JointDetector.CurvedSourceChains
noncomputable section
set_option autoImplicit false
open Set OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks RepeatedMarks.CurvedSourceStep

/-- One finite curved transition. The analytic provider and selected norm
are proved here; only the literal scalar certificate is supplied by data. -/
theorem certified_step (p : Params) (phi ray : ℝ) (combined : Bool)
    {n : ℕ} (cells : Fin n → HighCell)
    (g : StageHighCertificate p phi (RestartSourceChains.countFloor combined) ray combined cells)
    (hBmin : (9/10:ℝ) ≤ p.B0) (hcap : (1/10:ℝ) ≤ p.c0)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hp : GlobalSource p.B0 p.L0 p.c0) : GlobalSource p.B p.L p.c := by
  have hf : (2/5:ℝ) ≤ RestartSourceChains.countFloor combined := by
    cases combined <;> norm_num [RestartSourceChains.countFloor]
  have hfhi : RestartSourceChains.countFloor combined ≤ (3/4:ℝ) := by
    cases combined <;> norm_num [RestartSourceChains.countFloor]
  have hselected : combined = true →
      (50001/100000:ℝ) ≤ RestartSourceChains.countFloor combined := by
    cases combined <;> norm_num [RestartSourceChains.countFloor]
  have hpCount : GlobalSource p.B0 p.L0 (1/10) :=
    RestartSourceChains.globalSource_cap_mono (by norm_num) hcap hp
  have hcore := RestartSourceChains.actualParentCores
    (RestartSourceChains.countFloor combined) p.B0 p.L0 (1/10)
    hf hfhi hBmin g.geometry.face.B₀_lt.le g.parent_slope
    (by norm_num) (by norm_num) hpCount hβ
  have hnorm := FineCanonicalFromNorm.actual_norm NaturalSelectedNorm.natural_selected_cell_norm
  exact g.source_step hf hselected hnorm hcore hβ hp

/-- One literal transition in the finite acyclic source chain. -/
def SourceStep (p : Params) : Prop :=
  (51/100:ℝ)≤HeckeZeroSupremum.beta →
  GlobalSource p.B0 p.L0 p.c0 → GlobalSource p.B p.L p.c

/-- Infer all scalar cell parameters from the already proved certificate. -/
theorem certified_step_of_stage {p : Params} {phi ray : ℝ} {combined : Bool}
    {n : ℕ} {cells : Fin n→HighCell}
    (g : StageHighCertificate p phi (RestartSourceChains.countFloor combined) ray combined cells)
    (hBmin : (9/10:ℝ)≤p.B0) (hcap : (1/10:ℝ)≤p.c0) : SourceStep p :=
  fun hβ hp=>certified_step p phi ray combined cells g hBmin hcap hβ hp

#print axioms certified_step
end
end Qrh.JointDetector.CurvedSourceChains
