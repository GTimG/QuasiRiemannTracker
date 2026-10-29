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

admission_block admission252 using Pcount box((23/64:ℝ),(47/128:ℝ),(3/8:ℝ),(1/2:ℝ)) where
| (0,1) (5/2:ℝ) coefficients ![![1,0]]
| (0,0) (2:ℝ) coefficients ![![0]]
| (0,1) (8990101/10000000:ℝ) coefficients (fun i j => (![![1009899,0]] i j)/(5000000:ℝ))
| (1,1) (1177/768:ℝ) coefficients (fun i j => (![![494,36],
![461,0]] i j)/(3:ℝ))
| (1,2) (206772323/1280000000:ℝ) coefficients (fun i j => (![![1886455354,1840000000,0],
![2071306869,2167683232,143841616]] i j)/(5000000:ℝ))
| (1,2) (1707017359/8192000000:ℝ) coefficients (fun i j => (![![294807515,996469738,655206869],
![0,438878506,391413253]] i j)/(5000000:ℝ))
| (1,2) (11240329933/28416000000:ℝ) coefficients (fun i j => (![![620368782278,595109442144,0],
![658036558571,661887216528,29432096880]] i j)/(555000000:ℝ))
| (1,2) (1609228079/1536000000:ℝ) coefficients (fun i j => (![![12562251746,14536074368,2157624240],
![10233122657,10052350736,0]] i j)/(15000000:ℝ))
| (1,3) (10452379/768000000:ℝ) coefficients (fun i j => (![![5354832910,7559841344,2344374496,0],
![8817888415,16595882528,10147495792,2227105920]] i j)/(15000000:ℝ))
| (1,3) (500095306047715524251/32768000000000000000000:ℝ) coefficients (fun i j => (![![370054692686926646721,1452747728334296672623,1482108006079981376509,413351576632611350607],
![0,476868081980143284550,628595057271791885317,165966551191648600767]] i j)/(1500000000000000000:ℝ))
| (2,2) (17548769713/983040000000:ℝ) coefficients (fun i j => (![![189982568172,194768987488,6920893744],
![371520603004,374587237184,7201218592],
![181131980287,179135800000,0]] i j)/(15000000:ℝ))
| (1,2) (7625563439/7680000000:ℝ) coefficients (fun i j => (![![3971993434,4441657136,623841616],
![3324924141,3169736328,0]] i j)/(5000000:ℝ))
| (0,0) (74999/10000000:ℝ) coefficients ![![0]]
| (0,0) (55710927428098103/2000000000000000000:ℝ) coefficients ![![0]]
| (1,2) (417774973/1536000000:ℝ) coefficients (fun i j => (![![5353340818,5446337456,255563280],
![5107361161,4943729672,0]] i j)/(15000000:ℝ))
end_admission
end
end Qrh.JointDetector.RestartReturn
