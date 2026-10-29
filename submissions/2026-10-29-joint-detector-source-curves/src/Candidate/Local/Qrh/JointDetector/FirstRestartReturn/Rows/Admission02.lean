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

admission_block admission02 branch Pnew box((9/32:ℝ),(21/64:ℝ),(7/16:ℝ),(1/2:ℝ)) where
guard(0,1) margin (5/2:ℝ) coeffs ![![1,0]]
guard(0,0) margin (2:ℝ) coeffs ![![0]]
guard(0,1) margin (9380001/10000000:ℝ) coeffs (fun i j => (![![619999,0]] i j)/(5000000:ℝ))
guard(1,1) margin (611/384:ℝ) coeffs (fun i j => (![![430,216],
![223,0]] i j)/(9:ℝ))
guard(1,2) margin (84420009/640000000:ℝ) coeffs (fun i j => (![![483719994,480000000,0],
![1164660057,1760640128,600320064]] i j)/(5000000:ℝ))
guard(1,2) margin (19759962677/81920000000:ℝ) coeffs (fun i j => (![![3422268189,6880760342,3447332171],
![0,219967958,206947979]] i j)/(15000000:ℝ))
guard(1,2) margin (3935818039/14208000000:ℝ) coeffs (fun i j => (![![577456009426,564907645504,0],
![1016352084997,1397700167968,394732906560]] i j)/(1665000000:ℝ))
guard(1,2) margin (303286699/256000000:ℝ) coeffs (fun i j => (![![37663159382,64611842368,27014402880],
![9744616799,9684476896,0]] i j)/(45000000:ℝ))
guard(1,3) margin (19266772193/393216000000:ℝ) coeffs (fun i j => (![![0,36947091426,74251097122,37270525750],
![60538189815,201897077442,223135719394,81737771830]] i j)/(45000000:ℝ))
guard(1,3) margin (177710745800269653239/1536000000000000000000:ℝ) coeffs (fun i j => (![![20717036572953718578782,50961829147813447138238,39827719372958877174816,9587111791349148615360],
![9192398484034711136819,18395449571593628275811,9198168595433917138992,0]] i j)/(5625000000000000000:ℝ))
guard(2,2) margin (1878170679/81920000000:ℝ) coeffs (fun i j => (![![35275356612,39625274496,4359037248],
![70498396500,78475835648,7947517824],
![30895479321,30942800000,0]] i j)/(45000000:ℝ))
guard(1,2) margin (4018259777/3840000000:ℝ) coeffs (fun i j => (![![29144510154,51694710944,22682880576],
![6199370001,6061110224,0]] i j)/(45000000:ℝ))
guard(0,0) margin (74999/10000000:ℝ) coeffs ![![0]]
guard(0,0) margin (260922945564779651/5000000000000000000:ℝ) coeffs ![![0]]
guard(1,2) margin (32586463/256000000:ℝ) coeffs (fun i j => (![![1200952494,1650336352,460797120],
![748315323,736422064,0]] i j)/(15000000:ℝ))
end_admission
end
end Qrh.JointDetector.FirstRestartReturn
