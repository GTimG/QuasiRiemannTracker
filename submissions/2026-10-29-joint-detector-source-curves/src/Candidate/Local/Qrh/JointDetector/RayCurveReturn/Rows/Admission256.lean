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

admission_block admission256 using Pcount box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ)) where
| (0,1) (5/2:ℝ) coefficients ![![1,0]]
| (0,0) (2:ℝ) coefficients ![![0]]
| (0,1) (8990101/10000000:ℝ) coefficients (fun i j => (![![1009899,0]] i j)/(5000000:ℝ))
| (1,1) (1141/768:ℝ) coefficients (fun i j => (![![506,36],
![473,0]] i j)/(3:ℝ))
| (1,2) (8990101/51200000:ℝ) coefficients (fun i j => (![![2050494950,2000000000,0],
![2235346465,2327683232,143841616]] i j)/(5000000:ℝ))
| (1,2) (1471171347/8192000000:ℝ) coefficients (fun i j => (![![294807515,1124564930,779262465],
![0,566973698,515468849]] i j)/(5000000:ℝ))
| (1,2) (2395226471/5683200000:ℝ) coefficients (fun i j => (![![653311499930,626763764640,0],
![690979276223,693541539024,29432096880]] i j)/(555000000:ℝ))
| (1,2) (1501346867/1536000000:ℝ) coefficients (fun i j => (![![11876232350,13862173760,2157624240],
![9547103261,9378450128,0]] i j)/(15000000:ℝ))
| (1,3) (3482417/153600000:ℝ) coefficients (fun i j => (![![10298631250,16978735040,6831588640,0],
![13761686755,26014776224,14634709936,2227105920]] i j)/(15000000:ℝ))
| (1,3) (8083537404424702365314953261079/38210869482302834278400000000000000:ℝ) coefficients (fun i j => (![![431527529750211425539131574423833,2320308408074021438588846883095359,2925197997955904160285368825140289,1054081816384707130955252766468763],
![0,1182315082484887879314384442554430,1929896652264869321793279439556873,765599560467646685872886232002443]] i j)/(1749154791975532575000000000000:ℝ))
| (2,2) (5156046739/327680000000:ℝ) coefficients (fun i j => (![![182997634028,190626985056,9163492528],
![354302298356,360843634752,9443817376],
![170898609783,169534200000,0]] i j)/(15000000:ℝ))
| (1,2) (7157682227/7680000000:ℝ) coefficients (fun i j => (![![3879082726,4344706832,623841616],
![3232013433,3072786024,0]] i j)/(5000000:ℝ))
| (0,0) (74999/10000000:ℝ) coefficients ![![0]]
| (0,0) (64972424551037892165253918981/2332206389300710100000000000000:ℝ) coefficients ![![0]]
| (1,2) (404996809/1536000000:ℝ) coefficients (fun i j => (![![5391675310,5480412560,255563280],
![5145695653,4977804776,0]] i j)/(15000000:ℝ))
end_admission
end
end Qrh.JointDetector.RayCurveReturn
