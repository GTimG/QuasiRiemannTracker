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

admission_block admission264 using Pcountmid box((5/16:ℝ),(41/128:ℝ),(31/64:ℝ),(1/2:ℝ)) where
| (0,1) (5/2:ℝ) coefficients ![![1,0]]
| (0,0) (2:ℝ) coefficients ![![0]]
| (0,1) (8995101/10000000:ℝ) coefficients (fun i j => (![![1004899,0]] i j)/(5000000:ℝ))
| (1,1) (1231/768:ℝ) coefficients (fun i j => (![![728,288],
![443,0]] i j)/(3:ℝ))
| (1,2) (8995101/64000000:ℝ) coefficients (fun i j => (![![12840195960,12800000000,0],
![22372184283,31541966848,9210983424]] i j)/(5000000:ℝ))
| (1,2) (671030238757/2621440000000:ℝ) coefficients (fun i j => (![![17128948323,35409648566,18240504283],
![0,1393793718,1352592859]] i j)/(5000000:ℝ))
| (1,2) (101181263/284160000:ℝ) coefficients (fun i j => (![![4409123414600,4385759667200,0],
![6359178363701,8221988872832,1886495800320]] i j)/(555000000:ℝ))
| (1,2) (590678299/512000000:ℝ) coefficients (fun i j => (![![228091145560,366054917120,138164751360],
![88577498287,88379533184,0]] i j)/(15000000:ℝ))
| (1,3) (4091781673/12582912000000:ℝ) coefficients (fun i j => (![![0,252998118600,523833154760,270714448280],
![1210644802857,3811214835144,4009228714184,1408535079320]] i j)/(15000000:ℝ))
| (1,3) (40458724959333180907/1228800000000000000000:ℝ) coefficients (fun i j => (![![23241886616334749090200,62570325231563865667480,55207862396059801367040,15880931129330684789760],
![6457670348450841286855,13132022615103299471239,6672807234439958184384,0]] i j)/(187500000000000000:ℝ))
| (2,2) (6552960259/327680000000:ℝ) coefficients (fun i j => (![![1722492668352,1946986952704,227253476352],
![3233936402544,3473715253248,245209626624],
![1492509269223,1489841600000,0]] i j)/(15000000:ℝ))
| (1,2) (8325170257/7680000000:ℝ) coefficients (fun i j => (![![199983890472,319334685184,119792950272],
![79615133073,79169962816,0]] i j)/(15000000:ℝ))
| (0,0) (74999/10000000:ℝ) coefficients ![![0]]
| (0,0) (55710927428098103/2000000000000000000:ℝ) coefficients ![![0]]
| (1,2) (144621573/512000000:ℝ) coefficients (fun i j => (![![18397837800,23759761920,5413616640],
![13007130345,12955085376,0]] i j)/(5000000:ℝ))
end_admission
end
end Qrh.JointDetector.RestartReturn
