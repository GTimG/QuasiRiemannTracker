/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/restart_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
A finite count-source bank and physical source remain explicit; no missing estimate is asserted. -/
import Candidate.Local.Qrh.JointDetector.RestartReturn.PowerAdmissions
import Candidate.Local.Qrh.JointDetector.AdmissionBlockCommands
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unnecessarySeqFocus false
namespace Qrh.JointDetector.RestartReturn
open QRH.Record1252270103Return
noncomputable section

admission_block admission255 using Pcount box((49/128:ℝ),(25/64:ℝ),(3/8:ℝ),(1/2:ℝ)) where
| (0,1) (5/2:ℝ) coefficients ![![1,0]]
| (0,0) (2:ℝ) coefficients ![![0]]
| (0,1) (8990101/10000000:ℝ) coefficients (fun i j => (![![1009899,0]] i j)/(5000000:ℝ))
| (1,1) (575/384:ℝ) coefficients (fun i j => (![![503,36],
![470,0]] i j)/(3:ℝ))
| (1,2) (440514949/2560000000:ℝ) coefficients (fun i j => (![![2009485051,1960000000,0],
![2194336566,2287683232,143841616]] i j)/(5000000:ℝ))
| (1,2) (30602657/163840000:ℝ) coefficients (fun i j => (![![294807515,1092541132,748248566],
![0,534949900,484454950]] i j)/(5000000:ℝ))
| (1,2) (23584363499/56832000000:ℝ) coefficients (fun i j => (![![645075820517,618850184016,0],
![682743596810,685627958400,29432096880]] i j)/(555000000:ℝ))
| (1,2) (152831717/153600000:ℝ) coefficients (fun i j => (![![12047737199,14030648912,2157624240],
![9718608110,9546925280,0]] i j)/(15000000:ℝ))
| (1,3) (31344317/1536000000:ℝ) coefficients (fun i j => (![![9062681665,14624011616,5709785104,0],
![12525737170,23660052800,13512906400,2227105920]] i j)/(15000000:ℝ))
| (1,3) (13004061336078887753/3276800000000000000000:ℝ) coefficients (fun i j => (![![370054692686926646721,1855601023454176328893,2252061393837752723422,781360578370503041250],
![0,879721377100022940820,1398548445029563232230,533975552929540291410]] i j)/(1500000000000000000:ℝ))
| (2,2) (32081717/1966080000:ℝ) coefficients (fun i j => (![![185121056655,192027885664,8602842832],
![359361252700,365010335360,8883167680],
![173834141500,172300000000,0]] i j)/(15000000:ℝ))
| (1,2) (727465253/768000000:ℝ) coefficients (fun i j => (![![3902310403,4368944408,623841616],
![3255241110,3097023600,0]] i j)/(5000000:ℝ))
| (0,0) (74999/10000000:ℝ) coefficients ![![0]]
| (0,0) (55710927428098103/2000000000000000000:ℝ) coefficients ![![0]]
| (1,2) (8163827/30720000:ℝ) coefficients (fun i j => (![![5382091687,5471893784,255563280],
![5136112030,4969286000,0]] i j)/(15000000:ℝ))
end_admission
end
end Qrh.JointDetector.RestartReturn
