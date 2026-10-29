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

admission_block admission10 using Pnew box((33/64:ℝ),(69/128:ℝ),(15/32:ℝ),(1/2:ℝ)) where
| (0,1) (5/2:ℝ) coefficients ![![1,0]]
| (0,0) (2:ℝ) coefficients ![![0]]
| (0,1) (9380001/10000000:ℝ) coefficients (fun i j => (![![619999,0]] i j)/(5000000:ℝ))
| (1,1) (979/768:ℝ) coefficients (fun i j => (![![950,432],
![527,0]] i j)/(9:ℝ))
| (1,2) (309540033/1280000000:ℝ) coefficients (fun i j => (![![3533639978,3520000000,0],
![6095540233,8482560512,2401280256]] i j)/(5000000:ℝ))
| (1,2) (7804506081/131072000000:ℝ) coefficients (fun i j => (![![13323444765,30384825398,17020460699],
![0,4101703862,4058923931]] i j)/(15000000:ℝ))
| (1,2) (14039337743/28416000000:ℝ) coefficients (fun i j => (![![3159626093410,3126164768896,0],
![4826047598005,6370681440064,1578931626240]] i j)/(1665000000:ℝ))
| (1,2) (353313371/512000000:ℝ) coefficients (fun i j => (![![132494203590,240476175232,108057611520],
![22633892655,22563832768,0]] i j)/(45000000:ℝ))
| (1,3) (29444953/256000000:ℝ) coefficients (fun i j => (![![331629772026,650338532480,318831520256,0],
![750469816209,1842580470080,1447976962304,355737968640]] i j)/(45000000:ℝ))
| (1,3) (43458332855315723268345694553/1551658065012987758284032000000:ℝ) coefficients (fun i j => (![![1445482637121718288473271823164634,4149210047784948395410335294523200,3943431013976697078143975373480448,1239951625757259546082739208929280],
![82519587504143506854103407611201,185572805329894377316493625545760,102793921634513178546752578999552,0]] i j)/(90917464746854751461955000000:ℝ))
| (2,2) (735772599/327680000000:ℝ) coefficients (fun i j => (![![437595699076,746947243520,307596821760],
![555520178772,881242288128,321950744064],
![102100677401,104125600000,0]] i j)/(45000000:ℝ))
| (1,2) (4846739473/7680000000:ℝ) coefficients (fun i j => (![![111011689594,201422052416,90731522304],
![19750068145,19423328672,0]] i j)/(45000000:ℝ))
| (0,0) (74999/10000000:ℝ) coefficients ![![0]]
| (0,0) (527367216886410068273181401/10101940527428305717995000000:ℝ) coefficients ![![0]]
| (1,2) (52213007/512000000:ℝ) coefficients (fun i j => (![![4939382462,6754944448,1843188480],
![3112033883,3083927392,0]] i j)/(15000000:ℝ))
end_admission
end
end Qrh.JointDetector.RayCurveReturn
