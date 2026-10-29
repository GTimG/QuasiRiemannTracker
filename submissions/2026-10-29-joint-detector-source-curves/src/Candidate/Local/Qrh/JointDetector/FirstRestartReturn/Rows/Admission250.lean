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

admission_block admission250 using Pcount box((3/8:ℝ),(49/128:ℝ),(3/8:ℝ),(1/2:ℝ)) where
| (0,1) (5/2:ℝ) coefficients ![![1,0]]
| (0,0) (2:ℝ) coefficients ![![0]]
| (0,1) (8990101/10000000:ℝ) coefficients (fun i j => (![![1009899,0]] i j)/(5000000:ℝ))
| (1,1) (1159/768:ℝ) coefficients (fun i j => (![![500,36],
![467,0]] i j)/(3:ℝ))
| (1,2) (26970303/160000000:ℝ) coefficients (fun i j => (![![1968475152,1920000000,0],
![2153326667,2247683232,143841616]] i j)/(5000000:ℝ))
| (1,2) (1589094353/8192000000:ℝ) coefficients (fun i j => (![![294807515,1060517334,717234667],
![0,502926102,453441051]] i j)/(5000000:ℝ))
| (1,2) (1451028893/3552000000:ℝ) coefficients (fun i j => (![![636840141104,610936603392,0],
![674507917397,677714377776,29432096880]] i j)/(555000000:ℝ))
| (1,2) (1555287473/1536000000:ℝ) coefficients (fun i j => (![![12219242048,14199124064,2157624240],
![9890112959,9715400432,0]] i j)/(15000000:ℝ))
| (1,3) (1741529/96000000:ℝ) coefficients (fun i j => (![![7826732080,12269288192,4587981568,0],
![11289787585,21305329376,12391102864,2227105920]] i j)/(15000000:ℝ))
| (1,3) (622675119350258209529/81920000000000000000000:ℝ) coefficients (fun i j => (![![924927104608206067557,4307163682289111297551,4996758592240195467967,1650878378559290237973],
![0,1868102522497687637410,2863622343603646896103,1032633609355959258693]] i j)/(3750000000000000000:ℝ))
| (2,2) (16578536177/983040000000:ℝ) coefficients (fun i j => (![![186993019888,193185186272,8042193136],
![363917288256,368689835968,8322517984],
![176518213823,174822200000,0]] i j)/(15000000:ℝ))
| (1,2) (7391622833/7680000000:ℝ) coefficients (fun i j => (![![3925538080,4393181984,623841616],
![3278468787,3121261176,0]] i j)/(5000000:ℝ))
| (0,0) (74999/10000000:ℝ) coefficients ![![0]]
| (0,0) (139374510002329651/5000000000000000000:ℝ) coefficients ![![0]]
| (1,2) (411385891/1536000000:ℝ) coefficients (fun i j => (![![5372508064,5463375008,255563280],
![5126528407,4960767224,0]] i j)/(15000000:ℝ))
end_admission
end
end Qrh.JointDetector.FirstRestartReturn
