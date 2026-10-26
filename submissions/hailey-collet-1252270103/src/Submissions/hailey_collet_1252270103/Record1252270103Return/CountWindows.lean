/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.CountMonotonicity
import Submissions.hailey_collet_1252270103.Record1252270103Return.CountingBridge
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Admission04
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Admission06
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Admission07
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Admission08
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Admission09
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Admission11
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Admission12
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Admission13
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Admission14
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Admission15
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Admission16
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Admission17
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Admission18
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Admission19
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Admission20
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Admission21
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Admission22
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Admission23
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Admission24
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Admission27
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Admission28
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Admission29
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Admission30
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Admission31
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Admission35
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Admission36
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Admission37
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Admission38
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Admission39
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Admission40
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Admission41
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Admission42
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Admission43
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Admission44
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Admission45
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Admission46
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Admission47
import Submissions.hailey_collet_1252270103.Record1252270103Finite.Admission48
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Return
noncomputable section
open Record1252270103Finite
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
def returnWindow04 : ReturnCountWindow where
 branch := .capC
 nonold := by decide
 deltaLo := (3/8:ℝ)
 deltaHi := (27/64:ℝ)
 pLo := (7/16:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission04_all
def returnWindow06 : ReturnCountWindow where
 branch := .capP
 nonold := by decide
 deltaLo := (27/64:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (15/32:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission06_all
def returnWindow07 : ReturnCountWindow where
 branch := .capC
 nonold := by decide
 deltaLo := (27/64:ℝ)
 deltaHi := (111/256:ℝ)
 pLo := (31/64:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission07_all
def returnWindow08 : ReturnCountWindow where
 branch := .capP
 nonold := by decide
 deltaLo := (111/256:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (31/64:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission08_all
def returnWindow09 : ReturnCountWindow where
 branch := .weakC7
 nonold := by decide
 deltaLo := (111/256:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (63/128:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission09_all
def returnWindow11 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (57/128:ℝ)
 deltaHi := (117/256:ℝ)
 pLo := (31/64:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission11_all
def returnWindow12 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (57/128:ℝ)
 deltaHi := (231/512:ℝ)
 pLo := (63/128:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission12_all
def returnWindow13 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (57/128:ℝ)
 deltaHi := (459/1024:ℝ)
 pLo := (127/256:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission13_all
def returnWindow14 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (57/128:ℝ)
 deltaHi := (459/1024:ℝ)
 pLo := (255/512:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission14_all
def returnWindow15 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (459/1024:ℝ)
 deltaHi := (231/512:ℝ)
 pLo := (127/256:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission15_all
def returnWindow16 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (231/512:ℝ)
 deltaHi := (117/256:ℝ)
 pLo := (63/128:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission16_all
def returnWindow17 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (231/512:ℝ)
 deltaHi := (465/1024:ℝ)
 pLo := (127/256:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission17_all
def returnWindow18 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (465/1024:ℝ)
 deltaHi := (117/256:ℝ)
 pLo := (127/256:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission18_all
def returnWindow19 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (117/256:ℝ)
 deltaHi := (15/32:ℝ)
 pLo := (31/64:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission19_all
def returnWindow20 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (117/256:ℝ)
 deltaHi := (237/512:ℝ)
 pLo := (63/128:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission20_all
def returnWindow21 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (237/512:ℝ)
 deltaHi := (477/1024:ℝ)
 pLo := (63/128:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission21_all
def returnWindow22 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (237/512:ℝ)
 deltaHi := (951/2048:ℝ)
 pLo := (127/256:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission22_all
def returnWindow23 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (951/2048:ℝ)
 deltaHi := (477/1024:ℝ)
 pLo := (127/256:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission23_all
def returnWindow24 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (477/1024:ℝ)
 deltaHi := (15/32:ℝ)
 pLo := (63/128:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission24_all
def returnWindow27 : ReturnCountWindow where
 branch := .P
 nonold := by decide
 deltaLo := (15/32:ℝ)
 deltaHi := (63/128:ℝ)
 pLo := (15/32:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission27_all
def returnWindow28 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (15/32:ℝ)
 deltaHi := (123/256:ℝ)
 pLo := (31/64:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission28_all
def returnWindow29 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (15/32:ℝ)
 deltaHi := (123/256:ℝ)
 pLo := (63/128:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission29_all
def returnWindow30 : ReturnCountWindow where
 branch := .P
 nonold := by decide
 deltaLo := (123/256:ℝ)
 deltaHi := (63/128:ℝ)
 pLo := (31/64:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission30_all
def returnWindow31 : ReturnCountWindow where
 branch := .P
 nonold := by decide
 deltaLo := (123/256:ℝ)
 deltaHi := (63/128:ℝ)
 pLo := (63/128:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission31_all
def returnWindow35 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (117/256:ℝ)
 deltaHi := (471/1024:ℝ)
 pLo := (127/256:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission35_all
def returnWindow36 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (117/256:ℝ)
 deltaHi := (939/2048:ℝ)
 pLo := (255/512:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission36_all
def returnWindow37 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (117/256:ℝ)
 deltaHi := (1875/4096:ℝ)
 pLo := (511/1024:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission37_all
def returnWindow38 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (1875/4096:ℝ)
 deltaHi := (939/2048:ℝ)
 pLo := (511/1024:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission38_all
def returnWindow39 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (1875/4096:ℝ)
 deltaHi := (3753/8192:ℝ)
 pLo := (1023/2048:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission39_all
def returnWindow40 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (3753/8192:ℝ)
 deltaHi := (939/2048:ℝ)
 pLo := (1023/2048:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission40_all
def returnWindow41 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (3753/8192:ℝ)
 deltaHi := (7509/16384:ℝ)
 pLo := (2047/4096:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission41_all
def returnWindow42 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (3753/8192:ℝ)
 deltaHi := (15015/32768:ℝ)
 pLo := (4095/8192:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission42_all
def returnWindow43 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (15015/32768:ℝ)
 deltaHi := (7509/16384:ℝ)
 pLo := (4095/8192:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission43_all
def returnWindow44 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (15015/32768:ℝ)
 deltaHi := (30033/65536:ℝ)
 pLo := (8191/16384:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission44_all
def returnWindow45 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (30033/65536:ℝ)
 deltaHi := (7509/16384:ℝ)
 pLo := (8191/16384:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission45_all
def returnWindow46 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (7509/16384:ℝ)
 deltaHi := (939/2048:ℝ)
 pLo := (2047/4096:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission46_all
def returnWindow47 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (939/2048:ℝ)
 deltaHi := (471/1024:ℝ)
 pLo := (255/512:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission47_all
def returnWindow48 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (471/1024:ℝ)
 deltaHi := (237/512:ℝ)
 pLo := (127/256:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := admission48_all
def returnWindows : List ReturnCountWindow := [returnWindow04,returnWindow06,returnWindow07,returnWindow08,returnWindow09,returnWindow11,returnWindow12,returnWindow13,returnWindow14,returnWindow15,returnWindow16,returnWindow17,returnWindow18,returnWindow19,returnWindow20,returnWindow21,returnWindow22,returnWindow23,returnWindow24,returnWindow27,returnWindow28,returnWindow29,returnWindow30,returnWindow31,returnWindow35,returnWindow36,returnWindow37,returnWindow38,returnWindow39,returnWindow40,returnWindow41,returnWindow42,returnWindow43,returnWindow44,returnWindow45,returnWindow46,returnWindow47,returnWindow48]
def returnBranches : List Branch := returnWindows.map ReturnCountWindow.toBranch
end
end QRH.Record1252270103Return
#print axioms QRH.Record1252270103Return.ReturnCountWindow.antitone
