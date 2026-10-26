/- Repeated marks: fork of Collet's final-stage module CountWindows (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FinalReturn.CountMonotonicity
import Submissions.hailey_collet_1252270103.Record1252270103Return.CountingBridge
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FinalReturn.Rows.Admission01
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FinalReturn.Rows.Admission02
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FinalReturn.Rows.Admission03
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FinalReturn.Rows.Admission04
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FinalReturn.Rows.Admission05
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FinalReturn.Rows.Admission06
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FinalReturn.Rows.Admission07
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FinalReturn.Rows.Admission08
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FinalReturn.Rows.Admission09
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FinalReturn.Rows.Admission10
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FinalReturn.Rows.Admission11
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FinalReturn.Rows.Admission12
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FinalReturn.Rows.Admission13
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FinalReturn.Rows.Admission14
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FinalReturn.Rows.Admission15
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FinalReturn.Rows.Admission16
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FinalReturn.Rows.Admission17
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.RepeatedMarks.Return
open QRH.Record1252270103Return
noncomputable section

structure ReturnCountWindow where
 branch : CountBranch
 nonold : branch≠.old
 deltaLo : ℝ
 deltaHi : ℝ
 pLo : ℝ
 deltaBounds : 0≤deltaLo ∧ deltaHi≤3/4
 pBounds : 0≤pLo ∧ pLo≤1/2
 certificate : ∀{δ p:ℝ},δ∈Set.Icc deltaLo deltaHi → p∈Set.Icc pLo (1/2) →
  ∀j:Fin 15,0<admissionGuard branch δ p j

def ReturnCountWindow.Available (w : ReturnCountWindow) (δ p : ℝ) : Prop :=
 δ∈Set.Icc w.deltaLo w.deltaHi ∧ p∈Set.Icc w.pLo (1/2)
theorem ReturnCountWindow.upward (w : ReturnCountWindow) {δ p q:ℝ}
 (hp:w.Available δ p) (hpq:p≤q) (hq:q≤1/2) : w.Available δ q :=
 ⟨hp.1,⟨hp.2.1.trans hpq,hq⟩⟩
theorem ReturnCountWindow.antitone (w : ReturnCountWindow) {δ:ℝ}
 (hδ:δ∈Set.Icc w.deltaLo w.deltaHi) :
 AntitoneOn (branchCount w.branch δ) (Set.Icc w.pLo (1/2)) :=
 branchCount_antitoneOn w.branch w.nonold (w.deltaBounds.1.trans hδ.1)
  (by linarith [hδ.2,w.deltaBounds.2]) (fun _ hp=>w.certificate hδ hp)
def ReturnCountWindow.toBranch (w : ReturnCountWindow) : Branch where
 available := w.Available
 value := branchCount w.branch
 upward := w.upward
 antitone := by
  intro δ p q hp hq hpq
  exact w.antitone hp.1 hp.2 hq.2 hpq
def returnWindow01 : ReturnCountWindow where
 branch := .capC
 nonold := by decide
 deltaLo := (3/8:ℝ)
 deltaHi := (27/64:ℝ)
 pLo := (7/16:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission01_all
def returnWindow02 : ReturnCountWindow where
 branch := .capP
 nonold := by decide
 deltaLo := (27/64:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (15/32:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission02_all
def returnWindow03 : ReturnCountWindow where
 branch := .capC
 nonold := by decide
 deltaLo := (27/64:ℝ)
 deltaHi := (111/256:ℝ)
 pLo := (31/64:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission03_all
def returnWindow04 : ReturnCountWindow where
 branch := .weakC7
 nonold := by decide
 deltaLo := (111/256:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (31/64:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission04_all
def returnWindow05 : ReturnCountWindow where
 branch := .weakC7
 nonold := by decide
 deltaLo := (111/256:ℝ)
 deltaHi := (225/512:ℝ)
 pLo := (63/128:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission05_all
def returnWindow06 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (225/512:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (63/128:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission06_all
def returnWindow07 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (57/128:ℝ)
 deltaHi := (15/32:ℝ)
 pLo := (15/32:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission07_all
def returnWindow08 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (57/128:ℝ)
 deltaHi := (117/256:ℝ)
 pLo := (31/64:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission08_all
def returnWindow09 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (57/128:ℝ)
 deltaHi := (231/512:ℝ)
 pLo := (63/128:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission09_all
def returnWindow10 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (231/512:ℝ)
 deltaHi := (117/256:ℝ)
 pLo := (63/128:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission10_all
def returnWindow11 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (231/512:ℝ)
 deltaHi := (465/1024:ℝ)
 pLo := (127/256:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission11_all
def returnWindow12 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (465/1024:ℝ)
 deltaHi := (117/256:ℝ)
 pLo := (127/256:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission12_all
def returnWindow13 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (117/256:ℝ)
 deltaHi := (15/32:ℝ)
 pLo := (31/64:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission13_all
def returnWindow14 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (15/32:ℝ)
 deltaHi := (63/128:ℝ)
 pLo := (15/32:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission14_all
def returnWindow15 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (63/128:ℝ)
 deltaHi := (255/512:ℝ)
 pLo := (63/128:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission15_all
def returnWindow16 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (255/512:ℝ)
 deltaHi := (513/1024:ℝ)
 pLo := (127/256:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission16_all
def returnWindow17 : ReturnCountWindow where
 branch := .capP
 nonold := by decide
 deltaLo := (3/8:ℝ)
 deltaHi := (15/32:ℝ)
 pLo := (3/8:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission17_all
def returnWindows : List ReturnCountWindow := [returnWindow01,returnWindow02,returnWindow03,returnWindow04,returnWindow05,returnWindow06,returnWindow07,returnWindow08,returnWindow09,returnWindow10,returnWindow11,returnWindow12,returnWindow13,returnWindow14,returnWindow15,returnWindow16,returnWindow17]
def returnBranches : List Branch := returnWindows.map ReturnCountWindow.toBranch
end
end QRH.RepeatedMarks.Return
