/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/restart_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
A finite count-source bank and physical source remain explicit; no missing estimate is asserted. -/
import Candidate.Local.Qrh.JointDetector.DirectRoundedReturn.PowerAdmissions
import Candidate.Local.Qrh.JointDetector.AdmissionBlockCommands
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unnecessarySeqFocus false
namespace Qrh.JointDetector.DirectRoundedReturn
open QRH.Record1252270103Return
noncomputable section

admission_block admission256 branch Pcount box((25/64:ℝ),(51/128:ℝ),(3/8:ℝ),(1/2:ℝ)) where
guard(0,1) margin (5/2:ℝ) coeffs ![![1,0]]
guard(0,0) margin (2:ℝ) coeffs ![![0]]
guard(0,1) margin (8990101/10000000:ℝ) coeffs (fun i j => (![![1009899,0]] i j)/(5000000:ℝ))
guard(1,1) margin (1141/768:ℝ) coeffs (fun i j => (![![506,36],
![473,0]] i j)/(3:ℝ))
guard(1,2) margin (8990101/51200000:ℝ) coeffs (fun i j => (![![2050494950,2000000000,0],
![2235346465,2327683232,143841616]] i j)/(5000000:ℝ))
guard(1,2) margin (1471171347/8192000000:ℝ) coeffs (fun i j => (![![294807515,1124564930,779262465],
![0,566973698,515468849]] i j)/(5000000:ℝ))
guard(1,2) margin (2395226471/5683200000:ℝ) coeffs (fun i j => (![![653311499930,626763764640,0],
![690979276223,693541539024,29432096880]] i j)/(555000000:ℝ))
guard(1,2) margin (1501346867/1536000000:ℝ) coeffs (fun i j => (![![11876232350,13862173760,2157624240],
![9547103261,9378450128,0]] i j)/(15000000:ℝ))
guard(1,3) margin (3482417/153600000:ℝ) coeffs (fun i j => (![![10298631250,16978735040,6831588640,0],
![13761686755,26014776224,14634709936,2227105920]] i j)/(15000000:ℝ))
guard(1,3) margin (506513353677882113265623765498986673220061/2388965131036316824426126797881344000000000000:ℝ) coeffs (fun i j => (![![26979366899848737459380536624398934659568947,145066580816569097746877200850117220472590581,182884157337393587558803489216416946557929451,65901350233814910616950953878815224812407817],
![0,73918528321661404226529661411082222702149370,120657287116676198048552740177190129162882307,47865253744419310834580090231986801809582937]] i j)/(109358145036452491352514349268250000000000:ℝ))
guard(2,2) margin (5156046739/327680000000:ℝ) coeffs (fun i j => (![![182997634028,190626985056,9163492528],
![354302298356,360843634752,9443817376],
![170898609783,169534200000,0]] i j)/(15000000:ℝ))
guard(1,2) margin (7157682227/7680000000:ℝ) coeffs (fun i j => (![![3879082726,4344706832,623841616],
![3232013433,3072786024,0]] i j)/(5000000:ℝ))
guard(0,0) margin (74999/10000000:ℝ) coeffs ![![0]]
guard(0,0) margin (5076837877722120292230623038460741935659/182263575060754152254190582113750000000000:ℝ) coeffs ![![0]]
guard(1,2) margin (404996809/1536000000:ℝ) coeffs (fun i j => (![![5391675310,5480412560,255563280],
![5145695653,4977804776,0]] i j)/(15000000:ℝ))
end_admission
end
end Qrh.JointDetector.DirectRoundedReturn
