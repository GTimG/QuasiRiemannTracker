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

admission_block admission95 using Pwide box((7/16:ℝ),(57/128:ℝ),(15/32:ℝ),(1/2:ℝ)) where
| (0,1) (5/2:ℝ) coefficients ![![1,0]]
| (0,0) (2:ℝ) coefficients ![![0]]
| (0,1) (9100001/10000000:ℝ) coefficients (fun i j => (![![899999,0]] i j)/(5000000:ℝ))
| (1,1) (1087/768:ℝ) coefficients (fun i j => (![![632,144],
![491,0]] i j)/(3:ℝ))
| (1,2) (63700007/320000000:ℝ) coefficients (fun i j => (![![9010399944,8960000000,0],
![11500900199,13779200512,2329600256]] i j)/(5000000:ℝ))
| (1,2) (19277221893/131072000000:ℝ) coefficients (fun i j => (![![4369748255,11296232398,6876084199],
![0,2678551886,2627251943]] i j)/(5000000:ℝ))
| (1,2) (1064233099/2368000000:ℝ) coefficients (fun i j => (![![2765636365560,2736537959936,0],
![3283348000425,3740467836992,486528142080]] i j)/(555000000:ℝ))
| (1,2) (1355900149/1536000000:ℝ) coefficients (fun i j => (![![68155993960,102963197952,34944003840],
![32556490315,32422390464,0]] i j)/(15000000:ℝ))
| (1,3) (10204961/192000000:ℝ) coefficients (fun i j => (![![201582320216,388944826880,187513706496,0],
![356504668277,834138006080,613569760512,135782522880]] i j)/(15000000:ℝ))
| (1,3) (331254393841254631509/1310720000000000000000000:ℝ) coefficients (fun i j => (![![11514021790342495705929,38801146406654506392139,42240290661497017996803,14962616034685007310593],
![0,5466091739107592598754,10085431514638969488867,4628958514843876890113]] i j)/(937500000000000000:ℝ))
| (2,2) (4076452831/327680000000:ℝ) coefficients (fun i j => (![![808639996352,1010150409728,200972804864],
![1404243188624,1611072011264,205542405632],
![590542791507,591295200000,0]] i j)/(15000000:ℝ))
| (1,2) (2133966503/2560000000:ℝ) coefficients (fun i j => (![![62032765208,91622366464,30028800768],
![31747464725,31305565216,0]] i j)/(15000000:ℝ))
| (0,0) (74999/10000000:ℝ) coefficients ![![0]]
| (0,0) (260922945564779651/5000000000000000000:ℝ) coefficients ![![0]]
| (1,2) (326098913/1536000000:ℝ) coefficients (fun i j => (![![20575131416,23884720384,3455988480],
![17148842837,17001543328,0]] i j)/(15000000:ℝ))
end_admission
end
end Qrh.JointDetector.FirstRestartReturn
