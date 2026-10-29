/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/restart_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
A finite count-source bank and physical source remain explicit; no missing estimate is asserted. -/
import Candidate.Local.Qrh.JointDetector.FirstRestartReturn.PowerAdmissions
import Candidate.Local.Qrh.JointDetector.AdmissionBlockCommands
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unnecessarySeqFocus false
namespace Qrh.JointDetector.FirstRestartReturn
open QRH.Record1252270103Return
noncomputable section

admission_block admission243 using Pcount box((41/128:ℝ),(21/64:ℝ),(3/8:ℝ),(1/2:ℝ)) where
| (0,1) (5/2:ℝ) coefficients ![![1,0]]
| (0,0) (2:ℝ) coefficients ![![0]]
| (0,1) (8990101/10000000:ℝ) coefficients (fun i j => (![![1009899,0]] i j)/(5000000:ℝ))
| (1,1) (611/384:ℝ) coefficients (fun i j => (![![479,36],
![446,0]] i j)/(3:ℝ))
| (1,2) (368594141/2560000000:ℝ) coefficients (fun i j => (![![1681405859,1640000000,0],
![1866257374,1967683232,143841616]] i j)/(5000000:ℝ))
| (1,2) (1000912437/4096000000:ℝ) coefficients (fun i j => (![![294807515,836350748,500137374],
![0,278759516,236343758]] i j)/(5000000:ℝ))
| (1,2) (20641153811/56832000000:ℝ) coefficients (fun i j => (![![579190385213,555541539024,0],
![616858161506,622319313408,29432096880]] i j)/(555000000:ℝ))
| (1,2) (872039797/768000000:ℝ) coefficients (fun i j => (![![13419775991,15378450128,2157624240],
![11090646902,10894726496,0]] i j)/(15000000:ℝ))
| (1,3) (78649087/92160000000:ℝ) coefficients (fun i j => (![![1739030731,0,2847397776,4213775776],
![12128197246,27108123552,26256761664,10895093536]] i j)/(45000000:ℝ))
| (1,3) (15059109066312605713/512000000000000000000:ℝ) coefficients (fun i j => (![![2039069843086372426803,5299550819491248577579,3847671351358207130056,618244769203330979280],
![1114142738478166359246,2860489659699824917438,1714535102721658558192,0]] i j)/(3750000000000000000:ℝ))
| (2,2) (1613428579/81920000000:ℝ) coefficients (fun i j => (![![193055899487,194465490528,4117645264],
![381727811084,380804740224,4397970112],
![188265857052,185656800000,0]] i j)/(15000000:ℝ))
| (1,2) (4105207477/3840000000:ℝ) coefficients (fun i j => (![![4088131819,4562845016,623841616],
![3441062526,3290924208,0]] i j)/(5000000:ℝ))
| (0,0) (74999/10000000:ℝ) coefficients ![![0]]
| (0,0) (139374510002329651/5000000000000000000:ℝ) coefficients ![![0]]
| (1,2) (216873839/768000000:ℝ) coefficients (fun i j => (![![5305422703,5403743576,255563280],
![5059443046,4901135792,0]] i j)/(15000000:ℝ))
end_admission
end
end Qrh.JointDetector.FirstRestartReturn
