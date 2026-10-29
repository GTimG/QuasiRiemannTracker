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

admission_block admission23 using Pold box((9/32:ℝ),(3/8:ℝ),(3/8:ℝ),(1/2:ℝ)) where
| (0,1) (5/2:ℝ) coefficients ![![1,0]]
| (0,0) (2:ℝ) coefficients ![![0]]
| (0,1) (9380001/10000000:ℝ) coefficients (fun i j => (![![619999,0]] i j)/(5000000:ℝ))
| (1,1) (73/48:ℝ) coefficients (fun i j => (![![215,108],
![116,0]] i j)/(9:ℝ))
| (1,2) (84420009/640000000:ℝ) coefficients (fun i j => (![![121859997,120000000,0],
![312560012,460160032,150080016]] i j)/(5000000:ℝ))
| (1,2) (99494391/512000000:ℝ) coefficients (fun i j => (![![901968045,1818572072,911024036],
![0,108367976,100927988]] i j)/(15000000:ℝ))
| (1,2) (3935818039/14208000000:ℝ) coefficients (fun i j => (![![147501093337,141226911376,0],
![268684134316,360256719328,98683226640]] i j)/(1665000000:ℝ))
| (1,2) (34393337/32000000:ℝ) coefficients (fun i j => (![![9432219819,16152960592,6753600720],
![2223759252,2196479296,0]] i j)/(45000000:ℝ))
| (1,3) (650462603/16384000000:ℝ) coefficients (fun i j => (![![0,4516602881,9147544289,4614201435],
![9725946615,29224502033,29693482577,10172607195]] i j)/(45000000:ℝ))
| (1,3) (34413874079959/384000000000000:ℝ) coefficients (fun i j => (![![10189621255368589,25050832764095477,19571718190894168,4718876668667280],
![3459711926276332,7015255382124236,3544383473847904,0]] i j)/(22500000000000:ℝ))
| (2,2) (26530011/1280000000:ℝ) coefficients (fun i j => (![![4859119569,5850279456,993439728],
![9789439528,11699519744,1890559872],
![3659519824,3689600000,0]] i j)/(45000000:ℝ))
| (1,2) (457979971/480000000:ℝ) coefficients (fun i j => (![![7319297485,12923677736,5670720144],
![1520237548,1448317664,0]] i j)/(45000000:ℝ))
| (0,0) (74999/10000000:ℝ) coefficients ![![0]]
| (0,0) (262253340591/5000000000000:ℝ) coefficients ![![0]]
| (1,2) (3893309/32000000:ℝ) coefficients (fun i j => (![![303091439,412584088,115199280],
![192212132,186025504,0]] i j)/(15000000:ℝ))
end_admission
end
end Qrh.JointDetector.RestartReturn
