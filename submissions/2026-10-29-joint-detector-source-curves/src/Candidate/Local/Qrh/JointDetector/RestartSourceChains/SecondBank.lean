/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.Second
import Candidate.Local.Qrh.JointDetector.RestartReturn.BankSuppliers
import Candidate.Local.Qrh.JointDetector.RestartReturn.Endpoint
namespace Qrh.JointDetector.RestartSourceChains.Second
noncomputable section
set_option autoImplicit false
open OAI.SevenEighths QRH.Record1252270103Source

theorem bankSuppliers (hcores : ParentCoreProvider)
 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (999999999/1000000000:ℝ) (513373181897/200000000000:ℝ) (1/10:ℝ)) : RestartReturn.BankSuppliers := by
 intro b hb
 cases b
 · exact (hb rfl).elim
 · change GlobalSource (94429431246019/100000000000000:ℝ) (342923181897/200000000000:ℝ) (101/1000:ℝ)
   exact source17045 hcores hβ hp
 · change GlobalSource (49136538916807/50000000000000:ℝ) (436853181897/200000000000:ℝ) (1/10:ℝ)
   exact source07652 hcores hβ hp
 · change GlobalSource (49136538916807/50000000000000:ℝ) (436853181897/200000000000:ℝ) (1/10:ℝ)
   exact source07652 hcores hβ hp
 · change GlobalSource (3086039422459/3125000000000:ℝ) (452893181897/200000000000:ℝ) (1/10:ℝ)
   exact source06048 hcores hβ hp
 · change GlobalSource (49629406483459/50000000000000:ℝ) (472493181897/200000000000:ℝ) (1/10:ℝ)
   exact source04088 hcores hβ hp
 · change GlobalSource (49629406483459/50000000000000:ℝ) (472493181897/200000000000:ℝ) (1/10:ℝ)
   exact source04088 hcores hβ hp
 · change GlobalSource (49136538916807/50000000000000:ℝ) (436853181897/200000000000:ℝ) (1/10:ℝ)
   exact source07652 hcores hβ hp
 · change GlobalSource (94429431246019/100000000000000:ℝ) (342923181897/200000000000:ℝ) (101/1000:ℝ)
   exact source17045 hcores hβ hp
 · change GlobalSource (94429431246019/100000000000000:ℝ) (342923181897/200000000000:ℝ) (101/1000:ℝ)
   exact source17045 hcores hβ hp
 · change GlobalSource (24592977418591/25000000000000:ℝ) (440003181897/200000000000:ℝ) (1/10:ℝ)
   exact source07337 hcores hβ hp
 · change GlobalSource (48854077528557/50000000000000:ℝ) (420003181897/200000000000:ℝ) (1/10:ℝ)
   exact source09337 hcores hβ hp
 · change GlobalSource (96961445541543/100000000000000:ℝ) (400003181897/200000000000:ℝ) (1/10:ℝ)
   exact source11337 hcores hβ hp
 · change GlobalSource (19227283965471/20000000000000:ℝ) (380003181897/200000000000:ℝ) (1/10:ℝ)
   exact source13337 hcores hβ hp
 · change GlobalSource (47621575591377/50000000000000:ℝ) (360003181897/200000000000:ℝ) (1/10:ℝ)
   exact source15337 hcores hβ hp
 · change GlobalSource (47848933494537/50000000000000:ℝ) (370003181897/200000000000:ℝ) (1/10:ℝ)
   exact source14337 hcores hβ hp
 · change GlobalSource (94772395367213/100000000000000:ℝ) (350003181897/200000000000:ℝ) (1/10:ℝ)
   exact source16337 hcores hβ hp

theorem physicalSource (hcores : ParentCoreProvider)
 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (999999999/1000000000:ℝ) (513373181897/200000000000:ℝ) (1/10:ℝ)) :
 QRH.Record12518109Existence.UniformUnitFaceSource RestartReturn.physicalSourceFace := by
 change GlobalSource (49136538916807/50000000000000:ℝ) (436853181897/200000000000:ℝ) (1/10:ℝ)
 exact source07652 hcores hβ hp

#print axioms bankSuppliers
#print axioms physicalSource
end
end Qrh.JointDetector.RestartSourceChains.Second
