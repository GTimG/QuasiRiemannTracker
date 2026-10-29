/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/restart_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
A finite count-source bank and physical source remain explicit; no missing estimate is asserted. -/
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.PowerAdmissions
import Candidate.Local.Qrh.JointDetector.AdmissionBlockCommands
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unnecessarySeqFocus false
namespace Qrh.JointDetector.RayCurveReturn
open QRH.Record1252270103Return
noncomputable section

admission_block admission250 using Pcount box((11/32:ℝ),(45/128:ℝ),(3/8:ℝ),(1/2:ℝ)) where
| (0,1) (5/2:ℝ) coefficients ![![1,0]]
| (0,0) (2:ℝ) coefficients ![![0]]
| (0,1) (8990101/10000000:ℝ) coefficients (fun i j => (![![1009899,0]] i j)/(5000000:ℝ))
| (1,1) (1195/768:ℝ) coefficients (fun i j => (![![488,36],
![455,0]] i j)/(3:ℝ))
| (1,2) (98891111/640000000:ℝ) coefficients (fun i j => (![![1804435556,1760000000,0],
![1989287071,2087683232,143841616]] i j)/(5000000:ℝ))
| (1,2) (364988073/1638400000:ℝ) coefficients (fun i j => (![![294807515,932422142,593179071],
![0,374830910,329385455]] i j)/(5000000:ℝ))
| (1,2) (5436214361/14208000000:ℝ) coefficients (fun i j => (![![603897423452,579282280896,0],
![641565199745,646060055280,29432096880]] i j)/(555000000:ℝ))
| (1,2) (332633737/307200000:ℝ) coefficients (fun i j => (![![12905261444,14873024672,2157624240],
![10576132355,10389301040,0]] i j)/(15000000:ℝ))
| (1,3) (3486263/384000000:ℝ) coefficients (fun i j => (![![2882933740,2850394496,100767424,0],
![6345989245,11886435680,7903888720,2227105920]] i j)/(15000000:ℝ))
| (1,3) (6301859270458208658657575746459/286581521117271257088000000000000:ℝ) coefficients (fun i j => (![![524199612281470622406835582166468,1658789073698794725134365209939844,1407526784192085122136648822239696,288482255917060445082366534466320],
![92672082531259196867704007742635,520795748109661165859902769398915,412225438501050283644559436656280,0]] i j)/(1749154791975532575000000000000:ℝ))
| (2,2) (245051211/13107200000:ℝ) coefficients (fun i j => (![![191966278880,195378388704,5799594352],
![377112242600,378535838400,6079919200],
![184739909175,182475000000,0]] i j)/(15000000:ℝ))
| (1,2) (1571900809/1536000000:ℝ) coefficients (fun i j => (![![4018448788,4490132288,623841616],
![3371379495,3218211480,0]] i j)/(5000000:ℝ))
| (0,0) (74999/10000000:ℝ) coefficients ![![0]]
| (0,0) (64972424551037892165253918981/2332206389300710100000000000000:ℝ) coefficients ![![0]]
| (1,2) (84832811/307200000:ℝ) coefficients (fun i j => (![![5334173572,5429299904,255563280],
![5088193915,4926692120,0]] i j)/(15000000:ℝ))
end_admission
end
end Qrh.JointDetector.RayCurveReturn
