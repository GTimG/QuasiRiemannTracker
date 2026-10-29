/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/restart_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
A finite count-source bank and physical source remain explicit; no missing estimate is asserted. -/
import Candidate.Local.Qrh.JointDetector.FirstRestartReturn.SourceInlet
import Candidate.Local.Qrh.JointDetector.RestartSourceDomain
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unnecessarySeqFocus false
namespace Qrh.JointDetector.FirstRestartReturn
open QRH.Record1252270103Return
noncomputable section
open QRH.Record12518109Source QRH.Record12518109Existence

/-- Exact finite stages used by each ordinary/capped count face. -/
def supplierStage : CountBranch → ℕ
 | .old => 0
 | .Cnew => 1703
 | .Pnew => 764
 | .Cphys => 764
 | .Cold => 608
 | .Pold => 411
 | .Cphysold => 411
 | .Pwide => 764
 | .Pcount => 1703
 | .Pcountmid => 1703
 | .Cbridge0 => 734
 | .Cbridge1 => 934
 | .Cbridge2 => 1134
 | .Cbridge3 => 1334
 | .Cbridge4 => 1534
 | .Cbridge5 => 1434
 | .Cbridge6 => 1634
def bankSupplier : CountBranch → SourceFace
 | .old => countingSource .old
 | .Cnew => globalFace (2360868829489/2500000000000:ℝ) (857870970349/500000000000:ℝ) (101/1000:ℝ)
 | .Pnew => globalFace (98274226585809/100000000000000:ℝ) (1092620970349/500000000000:ℝ) (1/10:ℝ)
 | .Cphys => globalFace (98274226585809/100000000000000:ℝ) (1092620970349/500000000000:ℝ) (1/10:ℝ)
 | .Cold => globalFace (24685443232821/25000000000000:ℝ) (1131620970349/500000000000:ℝ) (1/10:ℝ)
 | .Pold => globalFace (99251525155089/100000000000000:ℝ) (1180870970349/500000000000:ℝ) (1/10:ℝ)
 | .Cphysold => globalFace (99251525155089/100000000000000:ℝ) (1180870970349/500000000000:ℝ) (1/10:ℝ)
 | .Pwide => globalFace (98274226585809/100000000000000:ℝ) (1092620970349/500000000000:ℝ) (1/10:ℝ)
 | .Pcount => globalFace (2360868829489/2500000000000:ℝ) (857870970349/500000000000:ℝ) (101/1000:ℝ)
 | .Pcountmid => globalFace (2360868829489/2500000000000:ℝ) (857870970349/500000000000:ℝ) (101/1000:ℝ)
 | .Cbridge0 => globalFace (98368350440523/100000000000000:ℝ) (1100120970349/500000000000:ℝ) (1/10:ℝ)
 | .Cbridge1 => globalFace (48852168020443/50000000000000:ℝ) (1050120970349/500000000000:ℝ) (1/10:ℝ)
 | .Cbridge2 => globalFace (48478748967367/50000000000000:ℝ) (1000120970349/500000000000:ℝ) (1/10:ℝ)
 | .Cbridge3 => globalFace (96132504200737/100000000000000:ℝ) (950120970349/500000000000:ℝ) (1/10:ℝ)
 | .Cbridge4 => globalFace (95239424367701/100000000000000:ℝ) (900120970349/500000000000:ℝ) (1/10:ℝ)
 | .Cbridge5 => globalFace (95694034153033/100000000000000:ℝ) (925120970349/500000000000:ℝ) (1/10:ℝ)
 | .Cbridge6 => globalFace (94768797030979/100000000000000:ℝ) (875120970349/500000000000:ℝ) (1/10:ℝ)


theorem bankSupplier_restricts (b : CountBranch) (hb : b ≠ .old) :
 RestartSourceDomain.Contains (bankSupplier b) (countingSource b) := by
 cases b <;> first | exact (hb rfl).elim | (apply RestartSourceDomain.contains_of_affine <;>
   norm_num [bankSupplier, countingSource, broadFace, globalFace,
     QRH.Record1252270103Return.globalFace, branchB, branchL, branchCap])

/-- Closed by the finite source chain, rather than an unproved face comparison. -/
def BankSuppliers : Prop := ∀ b : CountBranch, b ≠ .old →
 UniformUnitFaceSource (bankSupplier b)

theorem sourceBank_of_suppliers (hs : BankSuppliers) : SourceBank := by
 intro b hb ε hε
 obtain ⟨mesh, hm, hs⟩ := hs b hb ε hε
 exact ⟨mesh, hm, RestartSourceDomain.unit_source_of_contains (bankSupplier_restricts b hb) hs⟩

end
end Qrh.JointDetector.FirstRestartReturn
