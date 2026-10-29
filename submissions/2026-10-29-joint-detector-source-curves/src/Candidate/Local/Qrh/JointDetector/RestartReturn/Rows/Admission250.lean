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

admission_block admission250 branch Pcount box((11/32:ℝ),(45/128:ℝ),(3/8:ℝ),(1/2:ℝ)) where
guard(0,1) margin (5/2:ℝ) coeffs ![![1,0]]
guard(0,0) margin (2:ℝ) coeffs ![![0]]
guard(0,1) margin (8990101/10000000:ℝ) coeffs (fun i j => (![![1009899,0]] i j)/(5000000:ℝ))
guard(1,1) margin (1195/768:ℝ) coeffs (fun i j => (![![488,36],
![455,0]] i j)/(3:ℝ))
guard(1,2) margin (98891111/640000000:ℝ) coeffs (fun i j => (![![1804435556,1760000000,0],
![1989287071,2087683232,143841616]] i j)/(5000000:ℝ))
guard(1,2) margin (364988073/1638400000:ℝ) coeffs (fun i j => (![![294807515,932422142,593179071],
![0,374830910,329385455]] i j)/(5000000:ℝ))
guard(1,2) margin (5436214361/14208000000:ℝ) coeffs (fun i j => (![![603897423452,579282280896,0],
![641565199745,646060055280,29432096880]] i j)/(555000000:ℝ))
guard(1,2) margin (332633737/307200000:ℝ) coeffs (fun i j => (![![12905261444,14873024672,2157624240],
![10576132355,10389301040,0]] i j)/(15000000:ℝ))
guard(1,3) margin (3486263/384000000:ℝ) coeffs (fun i j => (![![2882933740,2850394496,100767424,0],
![6345989245,11886435680,7903888720,2227105920]] i j)/(15000000:ℝ))
guard(1,3) margin (1800852100180600561/81920000000000000000:ℝ) coeffs (fun i j => (![![449427475987205839716,1422297214821881147428,1206924097475638057552,247385025440962749840],
![79372783300279192995,446417568467727759355,353411148667448566360,0]] i j)/(1500000000000000000:ℝ))
guard(2,2) margin (245051211/13107200000:ℝ) coeffs (fun i j => (![![191966278880,195378388704,5799594352],
![377112242600,378535838400,6079919200],
![184739909175,182475000000,0]] i j)/(15000000:ℝ))
guard(1,2) margin (1571900809/1536000000:ℝ) coeffs (fun i j => (![![4018448788,4490132288,623841616],
![3371379495,3218211480,0]] i j)/(5000000:ℝ))
guard(0,0) margin (74999/10000000:ℝ) coeffs ![![0]]
guard(0,0) margin (55710927428098103/2000000000000000000:ℝ) coeffs ![![0]]
guard(1,2) margin (84832811/307200000:ℝ) coeffs (fun i j => (![![5334173572,5429299904,255563280],
![5088193915,4926692120,0]] i j)/(15000000:ℝ))
end_admission
end
end Qrh.JointDetector.RestartReturn
