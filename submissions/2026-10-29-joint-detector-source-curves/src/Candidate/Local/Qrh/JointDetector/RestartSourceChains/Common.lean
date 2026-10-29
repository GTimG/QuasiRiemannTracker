/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceHighReserve
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceFromCores
import Candidate.Local.Qrh.JointDetector.RestartSourceDomain
import Candidate.Local.Qrh.JointDetector.NaturalUniformNear
import Candidate.Local.Qrh.JointDetector.FineCanonicalFromNorm
namespace Qrh.JointDetector.RestartSourceChains
noncomputable section
set_option autoImplicit false
open Set OAI.SevenEighths QRH.Record1252270103Source
open RepeatedMarks RepeatedMarks.SourceStep

/-- This explicit interface is discharged by the actual core-count theorem.
It is not included among the finite HIGH signs. -/
def ParentCoreProvider : Prop := ∀ floor B L c : ℝ,
 (2/5:ℝ) ≤ floor → floor ≤ 3/4 → (9/10:ℝ) ≤ B → B ≤ 1 →
 (3/2:ℝ) ≤ L → 0 ≤ c → c ≤ 1/6 →
 GlobalSource B L c → (51/100:ℝ) ≤ HeckeZeroSupremum.beta →
 PhysicalCoreCount floor B L c

def countFloor (combined : Bool) : ℝ := if combined then 50001/100000 else 2/5

theorem globalSource_cap_mono {B L c cap : ℝ} (hcap0 : 0 ≤ cap)
 (hcap : cap ≤ c) (hp : GlobalSource B L c) : GlobalSource B L cap := by
 apply RestartSourceDomain.uniform_source_of_contains (hsource:=hp)
 apply RestartSourceDomain.global_contains_global hcap0 hcap
 simp

theorem certified_step (hcores : ParentCoreProvider)
 (p : Params) (r : ℝ) (combined : Bool)
 (hgeom : GeometryCertificate p) (hsigns : SourceHighSigns p r combined)
 (hBmin : (9/10:ℝ) ≤ p.B0) (hB : p.B0 ≤ 1) (hL : (3/2:ℝ) ≤ p.L0)
 (hcap : (1/10:ℝ) ≤ p.c0)
 (hq : countFloor combined ≤ p.q)
 (hselectedCap : combined=true → p.c0 ≤ 1/10)
 (hpure : combined=false → r=1)
 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource p.B0 p.L0 p.c0) : GlobalSource p.B p.L p.c := by
 have hfloor : (2/5:ℝ) ≤ countFloor combined := by cases combined <;> norm_num [countFloor]
 have hfloorHi : countFloor combined ≤ (3/4:ℝ) := by cases combined <;> norm_num [countFloor]
 have hqI : p.q ∈ Ioc (0:ℝ) (3/4) :=
   ⟨hsigns.2.2.1,hsigns.2.2.2.1.le⟩
 have hB0 : 0 ≤ p.B0 := by linarith
 have hn := FineCanonicalFromNorm.actual_norm NaturalSelectedNorm.natural_selected_cell_norm
 have hg := hsigns.gates hgeom hB0 hB hL hqI hselectedCap hpure
 have hpSmall := globalSource_cap_mono (by norm_num : (0:ℝ) ≤ 1/10) hcap hp
 have hcore := hcores (countFloor combined) p.B0 p.L0 (1/10)
   hfloor hfloorHi hBmin hB hL (by norm_num) (by norm_num) hpSmall hβ
 apply SourceStep.source_step_of_physicalCoreCount p (1/10) (countFloor combined)
   hB hL (by norm_num) (by norm_num) hfloor ⟨hq,hgeom.q_mem.2⟩ combined
   (by cases combined <;> simp [countFloor]) hn hB0 hg hcore hβ hp


/-- The literal source map supplied by each scalar-certified stage. -/
def SourceStep (p : Params) : Prop :=
 ParentCoreProvider → (51/100:ℝ) ≤ HeckeZeroSupremum.beta →
 GlobalSource p.B0 p.L0 p.c0 → GlobalSource p.B p.L p.c

def SourceRanges (p : Params) (r : ℝ) (combined : Bool) : Prop :=
 (9/10:ℝ) ≤ p.B0 ∧ p.B0 ≤ 1 ∧ (3/2:ℝ) ≤ p.L0 ∧ (1/10:ℝ) ≤ p.c0 ∧
 countFloor combined ≤ p.q ∧ (combined=true → p.c0 ≤ 1/10) ∧
 (combined=false → r=1)

theorem certified_step_of_signs {p : Params} {r : ℝ} {combined : Bool}
 (hg : GeometryCertificate p) (hs : SourceHighSigns p r combined)
 (hn : SourceRanges p r combined) : SourceStep p := by
 rcases hn with ⟨hBmin,hB,hL,hcap,hq,hselected,hpure⟩
 intro hcores hβ hp
 exact certified_step hcores p r combined hg hs hBmin hB hL hcap hq hselected hpure hβ hp

#print axioms certified_step
end
end Qrh.JointDetector.RestartSourceChains
