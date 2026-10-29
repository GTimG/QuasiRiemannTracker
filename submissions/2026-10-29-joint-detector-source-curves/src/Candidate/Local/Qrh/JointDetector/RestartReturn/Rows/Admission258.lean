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

admission_block admission258 using Pcount box((13/32:ℝ),(53/128:ℝ),(15/32:ℝ),(1/2:ℝ)) where
| (0,1) (5/2:ℝ) coefficients ![![1,0]]
| (0,0) (2:ℝ) coefficients ![![0]]
| (0,1) (8990101/10000000:ℝ) coefficients (fun i j => (![![1009899,0]] i j)/(5000000:ℝ))
| (1,1) (1123/768:ℝ) coefficients (fun i j => (![![620,144],
![479,0]] i j)/(3:ℝ))
| (1,2) (116871313/640000000:ℝ) coefficients (fun i j => (![![8372514748,8320000000,0],
![10834990503,13082931712,2301465856]] i j)/(5000000:ℝ))
| (1,2) (23070080197/131072000000:ℝ) coefficients (fun i j => (![![4341723755,10764349006,6370110503],
![0,2202937294,2149412647]] i j)/(5000000:ℝ))
| (1,2) (6172016783/14208000000:ℝ) coefficients (fun i j => (![![2597555636420,2570363703552,0],
![3100445607785,3543845126208,470913550080]] i j)/(555000000:ℝ))
| (1,2) (1447406261/1536000000:ℝ) coefficients (fun i j => (![![71527511180,105883875584,34521987840],
![36328593035,36165999296,0]] i j)/(15000000:ℝ))
| (1,3) (10445969/384000000:ℝ) coefficients (fun i j => (![![159511837492,304557424640,145203131392,0],
![320442968053,768503939840,590756324608,142534778880]] i j)/(15000000:ℝ))
| (1,3) (136260021428994236193/524288000000000000000000:ℝ) coefficients (fun i j => (![![4414676464482271619337,15635154055249071279043,17676996394459519740247,6460457409792720080541],
![0,2858801029139786698138,5357083683352102781239,2502297002737316083101]] i j)/(375000000000000000:ℝ))
| (2,2) (14217581833/983040000000:ℝ) coefficients (fun i j => (![![831842689392,995212541440,164556670720],
![1490907584824,1657757336576,169041868288],
![654088568167,653087200000,0]] i j)/(15000000:ℝ))
| (1,2) (6923741621/7680000000:ℝ) coefficients (fun i j => (![![22335896956,32157125504,9981465856],
![12258490695,12097243488,0]] i j)/(5000000:ℝ))
| (0,0) (74999/10000000:ℝ) coefficients ![![0]]
| (0,0) (55710927428098103/2000000000000000000:ℝ) coefficients ![![0]]
| (1,2) (398607727/1536000000:ℝ) coefficients (fun i j => (![![24203262412,28123319168,4089012480],
![20149389883,19979369312,0]] i j)/(15000000:ℝ))
end_admission
end
end Qrh.JointDetector.RestartReturn
