/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.First
import Candidate.Local.Qrh.JointDetector.FirstRestartReturn.BankSuppliers
import Candidate.Local.Qrh.JointDetector.FirstRestartReturn.Endpoint
namespace Qrh.JointDetector.RestartSourceChains.First
noncomputable section
set_option autoImplicit false
open OAI.SevenEighths QRH.Record1252270103Source

theorem bankSuppliers (hcores : ParentCoreProvider)
 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (99999/100000:ℝ) (1283620970349/500000000000:ℝ) (1/10:ℝ)) : FirstRestartReturn.BankSuppliers := by
 intro b hb
 cases b
 · exact (hb rfl).elim
 · change GlobalSource (2360868829489/2500000000000:ℝ) (857870970349/500000000000:ℝ) (101/1000:ℝ)
   exact source01703 hcores hβ hp
 · change GlobalSource (98274226585809/100000000000000:ℝ) (1092620970349/500000000000:ℝ) (1/10:ℝ)
   exact source00764 hcores hβ hp
 · change GlobalSource (98274226585809/100000000000000:ℝ) (1092620970349/500000000000:ℝ) (1/10:ℝ)
   exact source00764 hcores hβ hp
 · change GlobalSource (24685443232821/25000000000000:ℝ) (1131620970349/500000000000:ℝ) (1/10:ℝ)
   exact source00608 hcores hβ hp
 · change GlobalSource (99251525155089/100000000000000:ℝ) (1180870970349/500000000000:ℝ) (1/10:ℝ)
   exact source00411 hcores hβ hp
 · change GlobalSource (99251525155089/100000000000000:ℝ) (1180870970349/500000000000:ℝ) (1/10:ℝ)
   exact source00411 hcores hβ hp
 · change GlobalSource (98274226585809/100000000000000:ℝ) (1092620970349/500000000000:ℝ) (1/10:ℝ)
   exact source00764 hcores hβ hp
 · change GlobalSource (2360868829489/2500000000000:ℝ) (857870970349/500000000000:ℝ) (101/1000:ℝ)
   exact source01703 hcores hβ hp
 · change GlobalSource (2360868829489/2500000000000:ℝ) (857870970349/500000000000:ℝ) (101/1000:ℝ)
   exact source01703 hcores hβ hp
 · change GlobalSource (98368350440523/100000000000000:ℝ) (1100120970349/500000000000:ℝ) (1/10:ℝ)
   exact source00734 hcores hβ hp
 · change GlobalSource (48852168020443/50000000000000:ℝ) (1050120970349/500000000000:ℝ) (1/10:ℝ)
   exact source00934 hcores hβ hp
 · change GlobalSource (48478748967367/50000000000000:ℝ) (1000120970349/500000000000:ℝ) (1/10:ℝ)
   exact source01134 hcores hβ hp
 · change GlobalSource (96132504200737/100000000000000:ℝ) (950120970349/500000000000:ℝ) (1/10:ℝ)
   exact source01334 hcores hβ hp
 · change GlobalSource (95239424367701/100000000000000:ℝ) (900120970349/500000000000:ℝ) (1/10:ℝ)
   exact source01534 hcores hβ hp
 · change GlobalSource (95694034153033/100000000000000:ℝ) (925120970349/500000000000:ℝ) (1/10:ℝ)
   exact source01434 hcores hβ hp
 · change GlobalSource (94768797030979/100000000000000:ℝ) (875120970349/500000000000:ℝ) (1/10:ℝ)
   exact source01634 hcores hβ hp

theorem physicalSource (hcores : ParentCoreProvider)
 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hp : GlobalSource (99999/100000:ℝ) (1283620970349/500000000000:ℝ) (1/10:ℝ)) :
 QRH.Record12518109Existence.UniformUnitFaceSource FirstRestartReturn.physicalSourceFace := by
 change GlobalSource (98274226585809/100000000000000:ℝ) (1092620970349/500000000000:ℝ) (1/10:ℝ)
 exact source00764 hcores hβ hp

#print axioms bankSuppliers
#print axioms physicalSource
end
end Qrh.JointDetector.RestartSourceChains.First
