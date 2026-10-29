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

admission_block admission80 using Pwide box((41/128:ℝ),(21/64:ℝ),(3/8:ℝ),(1/2:ℝ)) where
| (0,1) (5/2:ℝ) coefficients ![![1,0]]
| (0,0) (2:ℝ) coefficients ![![0]]
| (0,1) (9100001/10000000:ℝ) coefficients (fun i j => (![![899999,0]] i j)/(5000000:ℝ))
| (1,1) (611/384:ℝ) coefficients (fun i j => (![![479,36],
![446,0]] i j)/(3:ℝ))
| (1,2) (373100041/2560000000:ℝ) coefficients (fun i j => (![![1676899959,1640000000,0],
![1863399974,1971200032,145600016]] i j)/(5000000:ℝ))
| (1,2) (993988737/4096000000:ℝ) coefficients (fun i j => (![![296456015,830635948,497279974],
![0,269527916,231727958]] i j)/(5000000:ℝ))
| (1,2) (6613364237/18944000000:ℝ) coefficients (fun i j => (![![592808423913,568358516624,0],
![631244730906,636892932608,30408008880]] i j)/(555000000:ℝ))
| (1,2) (882700097/768000000:ℝ) coefficients (fun i j => (![![13078096891,15084797328,2184000240],
![10728196702,10553596896,0]] i j)/(15000000:ℝ))
| (1,3) (1105895147/65536000000:ℝ) coefficients (fun i j => (![![0,1743590369,5691234561,3836944315],
![3400742205,10554116753,13225320657,5958546235]] i j)/(15000000:ℝ))
| (1,3) (62745150192962733239/1536000000000000000000:ℝ) coefficients (fun i j => (![![3886411155634147256503,8870978656729752249679,5602746126835675644456,645853594990070651280],
![2925101981206204254646,6330165644738003633638,3376713695031799378992,0]] i j)/(3750000000000000000:ℝ))
| (2,2) (1688050679/81920000000:ℝ) coefficients (fun i j => (![![192043390787,194215797728,3992798864],
![379824782684,380565597824,4278398912],
![187370391852,185656800000,0]] i j)/(15000000:ℝ))
| (1,2) (1360233259/1280000000:ℝ) coefficients (fun i j => (![![11138689757,12616790248,1876800048],
![9199789778,8798390224,0]] i j)/(15000000:ℝ))
| (0,0) (74999/10000000:ℝ) coefficients ![![0]]
| (0,0) (260922945564779651/5000000000000000000:ℝ) coefficients ![![0]]
| (1,2) (183299389/768000000:ℝ) coefficients (fun i j => (![![4484085053,4567184776,215999280],
![4276185746,4142386192,0]] i j)/(15000000:ℝ))
end_admission
end
end Qrh.JointDetector.FirstRestartReturn
