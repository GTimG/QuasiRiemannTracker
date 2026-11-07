import Candidate.ReturnA.Finite.Admission000
import Candidate.ReturnA.Finite.Admission001
import Candidate.ReturnA.Finite.Admission002
import Candidate.ReturnA.Finite.Admission003
import Candidate.ReturnA.Finite.Admission004
import Candidate.ReturnA.Finite.Admission005
import Candidate.ReturnA.Finite.Admission006
import Candidate.ReturnA.Finite.Admission007
import Candidate.ReturnA.Finite.Admission008
import Candidate.ReturnA.Finite.Admission009
import Candidate.ReturnA.Finite.Admission010
import Candidate.ReturnA.Finite.Admission011
import Candidate.ReturnA.Finite.Admission012
import Candidate.ReturnA.Finite.Admission013
import Candidate.ReturnA.Finite.Admission014
import Candidate.ReturnA.Finite.Admission015
import Candidate.ReturnA.Finite.Admission016
import Candidate.ReturnA.Finite.Admission017
import Candidate.ReturnA.Finite.Admission018
import Candidate.ReturnA.Finite.Admission019
import Candidate.ReturnA.Finite.Admission020
import Candidate.ReturnA.Finite.Admission021
import Candidate.ReturnA.Finite.Admission022
import Candidate.ReturnA.Finite.Admission023
import Candidate.ReturnA.Finite.Admission024
import Candidate.ReturnA.Finite.Admission025
import Candidate.ReturnA.Finite.Admission026
import Candidate.ReturnA.Finite.Admission027
import Candidate.ReturnA.Finite.Admission028
import Candidate.ReturnA.Finite.Admission029
import Candidate.ReturnA.Finite.Admission030
import Candidate.ReturnA.Finite.Admission031
import Candidate.ReturnA.Finite.Admission032
import Candidate.ReturnA.Finite.Admission033
import Candidate.ReturnA.Finite.Admission034
import Candidate.ReturnA.Finite.Admission035
import Candidate.ReturnA.Finite.Admission036
import Candidate.ReturnA.Finite.Admission037
/- Adapted 2026-10-24 for Subhanjan Das, AI-assisted with OpenAI Codex.
Original Hailey Collet/Mark Lewko notices and Apache-2.0 license retained. -/
/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.ReturnA.CountMonotonicity
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.CountingBridge
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace Das.QRH.ReturnA
open QRH.LewkoStage2Return
noncomputable section
open DasStageAFinite
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
def returnWindow000 : ReturnCountWindow where
 branch := .capC
 nonold := by decide
 deltaLo := (3/8:ℝ)
 deltaHi := (27/64:ℝ)
 pLo := (7/16:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := DasStageAFinite.admission000_all
def returnWindow001 : ReturnCountWindow where
 branch := .capP
 nonold := by decide
 deltaLo := (27/64:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (15/32:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := DasStageAFinite.admission001_all
def returnWindow002 : ReturnCountWindow where
 branch := .capC
 nonold := by decide
 deltaLo := (27/64:ℝ)
 deltaHi := (111/256:ℝ)
 pLo := (31/64:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := DasStageAFinite.admission002_all
def returnWindow003 : ReturnCountWindow where
 branch := .capP
 nonold := by decide
 deltaLo := (111/256:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (31/64:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := DasStageAFinite.admission003_all
def returnWindow004 : ReturnCountWindow where
 branch := .capP
 nonold := by decide
 deltaLo := (111/256:ℝ)
 deltaHi := (57/128:ℝ)
 pLo := (63/128:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := DasStageAFinite.admission004_all
def returnWindow005 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (57/128:ℝ)
 deltaHi := (117/256:ℝ)
 pLo := (31/64:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := DasStageAFinite.admission005_all
def returnWindow006 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (57/128:ℝ)
 deltaHi := (231/512:ℝ)
 pLo := (63/128:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := DasStageAFinite.admission006_all
def returnWindow007 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (57/128:ℝ)
 deltaHi := (459/1024:ℝ)
 pLo := (127/256:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := DasStageAFinite.admission007_all
def returnWindow008 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (57/128:ℝ)
 deltaHi := (459/1024:ℝ)
 pLo := (255/512:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := DasStageAFinite.admission008_all
def returnWindow009 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (459/1024:ℝ)
 deltaHi := (231/512:ℝ)
 pLo := (127/256:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := DasStageAFinite.admission009_all
def returnWindow010 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (231/512:ℝ)
 deltaHi := (117/256:ℝ)
 pLo := (63/128:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := DasStageAFinite.admission010_all
def returnWindow011 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (231/512:ℝ)
 deltaHi := (465/1024:ℝ)
 pLo := (127/256:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := DasStageAFinite.admission011_all
def returnWindow012 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (465/1024:ℝ)
 deltaHi := (117/256:ℝ)
 pLo := (127/256:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := DasStageAFinite.admission012_all
def returnWindow013 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (117/256:ℝ)
 deltaHi := (15/32:ℝ)
 pLo := (31/64:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := DasStageAFinite.admission013_all
def returnWindow014 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (117/256:ℝ)
 deltaHi := (237/512:ℝ)
 pLo := (63/128:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := DasStageAFinite.admission014_all
def returnWindow015 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (237/512:ℝ)
 deltaHi := (477/1024:ℝ)
 pLo := (63/128:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := DasStageAFinite.admission015_all
def returnWindow016 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (237/512:ℝ)
 deltaHi := (951/2048:ℝ)
 pLo := (127/256:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := DasStageAFinite.admission016_all
def returnWindow017 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (951/2048:ℝ)
 deltaHi := (477/1024:ℝ)
 pLo := (127/256:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := DasStageAFinite.admission017_all
def returnWindow018 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (477/1024:ℝ)
 deltaHi := (15/32:ℝ)
 pLo := (63/128:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := DasStageAFinite.admission018_all
def returnWindow019 : ReturnCountWindow where
 branch := .P
 nonold := by decide
 deltaLo := (15/32:ℝ)
 deltaHi := (63/128:ℝ)
 pLo := (15/32:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := DasStageAFinite.admission019_all
def returnWindow020 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (15/32:ℝ)
 deltaHi := (123/256:ℝ)
 pLo := (31/64:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := DasStageAFinite.admission020_all
def returnWindow021 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (15/32:ℝ)
 deltaHi := (123/256:ℝ)
 pLo := (63/128:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := DasStageAFinite.admission021_all
def returnWindow022 : ReturnCountWindow where
 branch := .P
 nonold := by decide
 deltaLo := (123/256:ℝ)
 deltaHi := (63/128:ℝ)
 pLo := (31/64:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := DasStageAFinite.admission022_all
def returnWindow023 : ReturnCountWindow where
 branch := .P
 nonold := by decide
 deltaLo := (123/256:ℝ)
 deltaHi := (63/128:ℝ)
 pLo := (63/128:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := DasStageAFinite.admission023_all
def returnWindow024 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (117/256:ℝ)
 deltaHi := (471/1024:ℝ)
 pLo := (127/256:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := DasStageAFinite.admission024_all
def returnWindow025 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (117/256:ℝ)
 deltaHi := (939/2048:ℝ)
 pLo := (255/512:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := DasStageAFinite.admission025_all
def returnWindow026 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (117/256:ℝ)
 deltaHi := (1875/4096:ℝ)
 pLo := (511/1024:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := DasStageAFinite.admission026_all
def returnWindow027 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (1875/4096:ℝ)
 deltaHi := (939/2048:ℝ)
 pLo := (511/1024:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := DasStageAFinite.admission027_all
def returnWindow028 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (1875/4096:ℝ)
 deltaHi := (3753/8192:ℝ)
 pLo := (1023/2048:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := DasStageAFinite.admission028_all
def returnWindow029 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (3753/8192:ℝ)
 deltaHi := (939/2048:ℝ)
 pLo := (1023/2048:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := DasStageAFinite.admission029_all
def returnWindow030 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (3753/8192:ℝ)
 deltaHi := (7509/16384:ℝ)
 pLo := (2047/4096:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := DasStageAFinite.admission030_all
def returnWindow031 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (3753/8192:ℝ)
 deltaHi := (15015/32768:ℝ)
 pLo := (4095/8192:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := DasStageAFinite.admission031_all
def returnWindow032 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (15015/32768:ℝ)
 deltaHi := (7509/16384:ℝ)
 pLo := (4095/8192:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := DasStageAFinite.admission032_all
def returnWindow033 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (15015/32768:ℝ)
 deltaHi := (30033/65536:ℝ)
 pLo := (8191/16384:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := DasStageAFinite.admission033_all
def returnWindow034 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (30033/65536:ℝ)
 deltaHi := (7509/16384:ℝ)
 pLo := (8191/16384:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := DasStageAFinite.admission034_all
def returnWindow035 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (7509/16384:ℝ)
 deltaHi := (939/2048:ℝ)
 pLo := (2047/4096:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := DasStageAFinite.admission035_all
def returnWindow036 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (939/2048:ℝ)
 deltaHi := (471/1024:ℝ)
 pLo := (255/512:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := DasStageAFinite.admission036_all
def returnWindow037 : ReturnCountWindow where
 branch := .C
 nonold := by decide
 deltaLo := (471/1024:ℝ)
 deltaHi := (237/512:ℝ)
 pLo := (127/256:ℝ)
 deltaBounds := by norm_num
 pBounds := by norm_num
 certificate := DasStageAFinite.admission037_all
def returnWindows : List ReturnCountWindow := [returnWindow000,returnWindow001,returnWindow002,returnWindow003,returnWindow004,returnWindow005,returnWindow006,returnWindow007,returnWindow008,returnWindow009,returnWindow010,returnWindow011,returnWindow012,returnWindow013,returnWindow014,returnWindow015,returnWindow016,returnWindow017,returnWindow018,returnWindow019,returnWindow020,returnWindow021,returnWindow022,returnWindow023,returnWindow024,returnWindow025,returnWindow026,returnWindow027,returnWindow028,returnWindow029,returnWindow030,returnWindow031,returnWindow032,returnWindow033,returnWindow034,returnWindow035,returnWindow036,returnWindow037]
end
end Das.QRH.ReturnA
