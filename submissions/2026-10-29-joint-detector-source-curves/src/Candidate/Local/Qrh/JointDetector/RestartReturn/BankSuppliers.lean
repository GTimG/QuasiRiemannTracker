/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/restart_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
A finite count-source bank and physical source remain explicit; no missing estimate is asserted. -/
import Candidate.Local.Qrh.JointDetector.RestartReturn.SourceInlet
import Candidate.Local.Qrh.JointDetector.RestartSourceDomain
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unnecessarySeqFocus false
namespace Qrh.JointDetector.RestartReturn
open QRH.Record1252270103Return
noncomputable section
open QRH.Record12518109Source QRH.Record12518109Existence

/-- Exact finite stages used by each ordinary/capped count face. -/
def supplierStage : CountBranch → ℕ
 | .old => 0
 | .Cnew => 17045
 | .Pnew => 7652
 | .Cphys => 7652
 | .Cold => 6048
 | .Pold => 4088
 | .Cphysold => 4088
 | .Pwide => 7652
 | .Pcount => 17045
 | .Pcountmid => 17045
 | .Cbridge0 => 7337
 | .Cbridge1 => 9337
 | .Cbridge2 => 11337
 | .Cbridge3 => 13337
 | .Cbridge4 => 15337
 | .Cbridge5 => 14337
 | .Cbridge6 => 16337
def bankSupplier : CountBranch → SourceFace
 | .old => countingSource .old
 | .Cnew => globalFace (94429431246019/100000000000000:ℝ) (342923181897/200000000000:ℝ) (101/1000:ℝ)
 | .Pnew => globalFace (49136538916807/50000000000000:ℝ) (436853181897/200000000000:ℝ) (1/10:ℝ)
 | .Cphys => globalFace (49136538916807/50000000000000:ℝ) (436853181897/200000000000:ℝ) (1/10:ℝ)
 | .Cold => globalFace (3086039422459/3125000000000:ℝ) (452893181897/200000000000:ℝ) (1/10:ℝ)
 | .Pold => globalFace (49629406483459/50000000000000:ℝ) (472493181897/200000000000:ℝ) (1/10:ℝ)
 | .Cphysold => globalFace (49629406483459/50000000000000:ℝ) (472493181897/200000000000:ℝ) (1/10:ℝ)
 | .Pwide => globalFace (49136538916807/50000000000000:ℝ) (436853181897/200000000000:ℝ) (1/10:ℝ)
 | .Pcount => globalFace (94429431246019/100000000000000:ℝ) (342923181897/200000000000:ℝ) (101/1000:ℝ)
 | .Pcountmid => globalFace (94429431246019/100000000000000:ℝ) (342923181897/200000000000:ℝ) (101/1000:ℝ)
 | .Cbridge0 => globalFace (24592977418591/25000000000000:ℝ) (440003181897/200000000000:ℝ) (1/10:ℝ)
 | .Cbridge1 => globalFace (48854077528557/50000000000000:ℝ) (420003181897/200000000000:ℝ) (1/10:ℝ)
 | .Cbridge2 => globalFace (96961445541543/100000000000000:ℝ) (400003181897/200000000000:ℝ) (1/10:ℝ)
 | .Cbridge3 => globalFace (19227283965471/20000000000000:ℝ) (380003181897/200000000000:ℝ) (1/10:ℝ)
 | .Cbridge4 => globalFace (47621575591377/50000000000000:ℝ) (360003181897/200000000000:ℝ) (1/10:ℝ)
 | .Cbridge5 => globalFace (47848933494537/50000000000000:ℝ) (370003181897/200000000000:ℝ) (1/10:ℝ)
 | .Cbridge6 => globalFace (94772395367213/100000000000000:ℝ) (350003181897/200000000000:ℝ) (1/10:ℝ)


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
end Qrh.JointDetector.RestartReturn
