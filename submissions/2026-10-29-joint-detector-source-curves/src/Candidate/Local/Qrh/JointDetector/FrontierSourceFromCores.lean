/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Fixed selected cutoff .500000001, same original-row event and full amplitude supremum.
Inherited notices follow unchanged. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.FrontierPackedFromCores
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceStep
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.CurvedSourceStep

namespace Qrh.JointDetector.FrontierRepeatedMarks
noncomputable section
open Set RepeatedMarks
open OAI.SevenEighths
open QRH.SilDensitySplit.CubeFree

/-- An all-real extension in the density argument. Only its admitted cuts
are used by the supplier; no ordering of prices on nonphysical inputs is
needed. -/
def familyHigh (B L c : ℝ) (hB0 : 0 ≤ B) (hB : B ≤ 1) (hL : (3/2:ℝ) ≤ L)
    (hc0 : 0 ≤ c) (hc : c ≤ 1/6) (combined : Bool) (q P s M : ℝ) : ℝ :=
  if hq : q ∈ Ioc (0:ℝ) (3/4) then
    (repeatedFamily B L c q hB0 hB hL hc0 hc hq combined).high P s M else 0

@[simp] theorem familyHigh_eq (B L c : ℝ) (hB0 : 0 ≤ B) (hB : B ≤ 1)
    (hL : (3/2:ℝ) ≤ L) (hc0 : 0 ≤ c) (hc : c ≤ 1/6) (combined : Bool)
    (q P s M : ℝ) (hq : q ∈ Ioc (0:ℝ) (3/4)) :
    familyHigh B L c hB0 hB hL hc0 hc combined q P s M =
      (repeatedFamily B L c q hB0 hB hL hc0 hc hq combined).high P s M := by
  simp only [familyHigh, dif_pos hq]

namespace SourceStep
open RepeatedMarks.SourceStep
/-- Close a scalar source step with the actual natural-row supplier. The
parent cap for LOW and the moment cap for HIGH remain distinct. -/
theorem source_step_of_physicalCoreCount
    (p : Params) (momentCap floor : ℝ)
    (hB : p.B0 ≤ 1) (hL : (3/2:ℝ) ≤ p.L0)
    (hc0 : 0 ≤ momentCap) (hc : momentCap ≤ 1/6)
    (hf : (2/5:ℝ) ≤ floor) (hq : p.q ∈ Icc floor (3/4))
    (combined : Bool) (hselectedFloor : combined = true → (50001/100000:ℝ) ≤ floor)
    (hnorm : FrontierNaturalCount.ActualSelectedSlotNorm)
    (hB0 : 0 ≤ p.B0)
    (g : Gates p (repeatedFamily p.B0 p.L0 momentCap p.q hB0 hB hL hc0 hc
      ⟨by linarith [hq.1],hq.2⟩ combined))
    (hcore : PhysicalCoreCount floor p.B0 p.L0 momentCap)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hp : QRH.Record1252270103Source.GlobalSource p.B0 p.L0 p.c0) :
    QRH.Record1252270103Source.GlobalSource p.B p.L p.c := by
  apply g.source_step hβ hp
  apply priced_source_of_physicalCoreCount p.B0 p.L0 momentCap floor hB0 hB hL hc0 hc hf
    combined hselectedFloor hnorm (familyHigh p.B0 p.L0 momentCap hB0 hB hL hc0 hc combined)
    (by intro q hq _ P s M; exact familyHigh_eq _ _ _ _ _ _ _ _ _ _ _ _ _ hq)
    hcore p.B0 p.L0 p.c0 (9/10) 4 4 g.L0_pos hβ
    ⟨g.B0_pos,hB,(lt_of_le_of_lt g.crossing_nonneg g.crossing_cap)⟩ (by norm_num) (by norm_num) hp
    (fun _ => p.q) (fun _ => hq)
  intro w P s M
  simp only [data, weightedPrice, familyHigh_eq _ _ _ _ _ _ _ _ _ _ _ _ _
    (show p.q ∈ Ioc (0:ℝ) (3/4) from ⟨by linarith [hq.1],hq.2⟩)]

end SourceStep

namespace CurvedSourceStep
open RepeatedMarks.CurvedSourceStep
/-- Curved selectors use the same supplier with a live bounded density cut.
The early mesh is uniform in that cut and the entire finite slot type. -/
theorem source_step_of_physicalCoreCount
    (p : Params) (momentCap floor : ℝ)
    (hB : p.B0 ≤ 1) (hL : (3/2:ℝ) ≤ p.L0)
    (hc0 : 0 ≤ momentCap) (hc : momentCap ≤ 1/6)
    (hf : (2/5:ℝ) ≤ floor)
    (q : ℝ → ℝ) (hq : ∀ w, q w ∈ Icc floor (3/4))
    (combined : Bool) (hselectedFloor : combined = true → (50001/100000:ℝ) ≤ floor)
    (hnorm : FrontierNaturalCount.ActualSelectedSlotNorm) (hB0 : 0 ≤ p.B0)
    (g : Gates p q (fun w => repeatedFamily p.B0 p.L0 momentCap (q w) hB0 hB hL hc0 hc
      ⟨by linarith [(hq w).1],(hq w).2⟩ combined))
    (hcore : PhysicalCoreCount floor p.B0 p.L0 momentCap)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hp : QRH.Record1252270103Source.GlobalSource p.B0 p.L0 p.c0) :
    QRH.Record1252270103Source.GlobalSource p.B p.L p.c := by
  apply g.source_step hβ hp
  apply priced_source_of_physicalCoreCount p.B0 p.L0 momentCap floor hB0 hB hL hc0 hc hf
    combined hselectedFloor hnorm (familyHigh p.B0 p.L0 momentCap hB0 hB hL hc0 hc combined)
    (by intro q hq _ P s M; exact familyHigh_eq _ _ _ _ _ _ _ _ _ _ _ _ _ hq)
    hcore p.B0 p.L0 p.c0 (9/10) 4 4 g.L0_pos hβ
    ⟨g.B0_pos,hB,(lt_of_le_of_lt g.crossing_nonneg g.crossing_cap)⟩
    (by norm_num) (by norm_num) hp
    (fun w => q (max (crossing p) w)) (fun w => hq _)
  intro w P s M
  simp only [data, weightedPrice, familyHigh_eq _ _ _ _ _ _ _ _ _ _ _ _ _
    (show q (max (crossing p) w) ∈ Ioc (0:ℝ) (3/4) from
      ⟨by linarith [(hq (max (crossing p) w)).1],(hq _).2⟩)]

end CurvedSourceStep
#print axioms SourceStep.source_step_of_physicalCoreCount
#print axioms CurvedSourceStep.source_step_of_physicalCoreCount
end
end Qrh.JointDetector.FrontierRepeatedMarks
