/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/restart_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
A finite count-source bank and physical source remain explicit; no missing estimate is asserted. -/
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Formulas
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unnecessarySeqFocus false
namespace Qrh.JointDetector.RayCurveReturn
open QRH.Record1252270103Return
noncomputable section

def admission_power_Cnew_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-266553189080163800899/79976677936106992899:ℝ)*δ^0*p^1
theorem admission_power_Cnew_00_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 0 = admission_power_Cnew_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_00] <;> ring

def admission_power_Cnew_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-186576511144056808000/79976677936106992899:ℝ)*δ^0*p^1
theorem admission_power_Cnew_01_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 1 = admission_power_Cnew_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_01] <;> ring

def admission_power_Cnew_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-2202296834524980158690738413981/1999416948402674822475000000000:ℝ)*δ^0*p^1
theorem admission_power_Cnew_02_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 2 = admission_power_Cnew_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_02] <;> ring

def admission_power_Cnew_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-1332765945400819004495/479860067616641957394:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (186576511144056808000/79976677936106992899:ℝ)*δ^1*p^2
theorem admission_power_Cnew_03_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 3 = admission_power_Cnew_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_03] <;> ring

def admission_power_Cnew_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-4201713782927654981165738413981/1999416948402674822475000000000:ℝ)*δ^1*p^1 + (2202296834524980158690738413981/1999416948402674822475000000000:ℝ)*δ^1*p^2
theorem admission_power_Cnew_04_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 4 = admission_power_Cnew_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_04] <;> ring

def admission_power_Cnew_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-222038806503776446148867/319906711744427971596000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (3702059487521826543029235913981/1999416948402674822475000000000:ℝ)*δ^1*p^1 + (-1036660081152485250710738413981/1999416948402674822475000000000:ℝ)*δ^1*p^2
theorem admission_power_Cnew_05_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 5 = admission_power_Cnew_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_05] <;> ring

def admission_power_Cnew_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-68745048536919668441653036048109/88774112509078762117890000000000:ℝ)*δ^0*p^1 + (3147628864961963974950112714099121599591784887149997/7099858605202319233613544294453364430863110000000000:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-481698544186279325675546963951891/73978427090898968431575000000000:ℝ)*δ^1*p^1 + (44849253562008496234366184180356959720548915112850003/5916548837668599361344620245377803692385925000000000:ℝ)*δ^1*p^2 + (-696255896740586880058801113291204585488000/236661953506743974453784809815112147695437:ℝ)*δ^1*p^3
theorem admission_power_Cnew_06_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 6 = admission_power_Cnew_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_06] <;> ring

def admission_power_Cnew_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-13270720230579035498547215241943/2399300338083209786970000000000:ℝ)*δ^0*p^1 + (587029244543783246424100847694647514142663921968919/191888070410873492800366062012253092726030000000000:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (13270720230579035498547215241943/1999416948402674822475000000000:ℝ)*δ^1*p^1 + (-587029244543783246424100847694647514142663921968919/159906725342394577333638385010210910605025000000000:ℝ)*δ^1*p^2
theorem admission_power_Cnew_07_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 7 = admission_power_Cnew_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_07] <;> ring

def admission_power_Cnew_08 (δ p : ℝ) : ℝ := (-730953618232406116172667226943/1865765111440568080000000000000:ℝ)*δ^0*p^0 + (200149778836864210589726183651882557555312951449757/223826543133160628935751950987629095880000000000000:ℝ)*δ^0*p^1 + (-18255476210270670955159177028783053247099229508070697586336184674701181/35801806707425895665745603237687537414797393707569900312240000000000000:ℝ)*δ^0*p^2 + (5395366396833826316172667226943/4664412778601420200000000000000:ℝ)*δ^1*p^0 + (-583506637388133254903994402361239186245163055498081/186522119277633857446459959156357579900000000000000:ℝ)*δ^1*p^1 + (989972002547817198952207183687357682312489086526081/373044238555267714892919918312715159800000000000000:ℝ)*δ^1*p^2 + (-21529040953289383600760929487232456794303377699/31981345068478915466727677002042182121005000000:ℝ)*δ^1*p^3
theorem admission_power_Cnew_08_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 8 = admission_power_Cnew_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_08] <;> ring

def admission_power_Cnew_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-4021913912698754882318396273057/2399300338083209786970000000000:ℝ)*δ^0*p^1 + (60401739512473430046089915051714139494908790009527/63962690136957830933455354004084364242010000000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (1257222729005387360575413899/399883389680534964495000000:ℝ)*δ^1*p^1 + (-1445513453040409324220779996481/666472316134224940825000000000:ℝ)*δ^1*p^2 + (5477335561469140164831944264021419408093322440991/17767413926932730814848709445578990067225000000000:ℝ)*δ^1*p^3
theorem admission_power_Cnew_09_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 9 = admission_power_Cnew_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_09] <;> ring

def admission_power_Cnew_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-2942201719069620685086113413981/2399300338083209786970000000000:ℝ)*δ^1*p^1 + (1802467050904734457342238413981/2399300338083209786970000000000:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (4351670054057855592851363413981/1999416948402674822475000000000:ℝ)*δ^2*p^1 + (-2951957576540332375039238413981/1999416948402674822475000000000:ℝ)*δ^2*p^2 + (3731530222881136160/26658892645368997633:ℝ)*δ^2*p^3
theorem admission_power_Cnew_10_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 10 = admission_power_Cnew_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_10] <;> ring

def admission_power_Cnew_11 (δ p : ℝ) : ℝ := (5941311621778869921022215241943/2399300338083209786970000000000:ℝ)*δ^0*p^0 + (-2202296834524980158690738413981/399883389680534964495000000000:ℝ)*δ^0*p^1 + (587029244543783246424100847694647514142663921968919/191888070410873492800366062012253092726030000000000:ℝ)*δ^0*p^2 + (-6201130731330329803640738413981/1999416948402674822475000000000:ℝ)*δ^1*p^0 + (6866709613126400358690738413981/999708474201337411237500000000:ℝ)*δ^1*p^1 + (-607808713790026453674653349055207316401506943327081/159906725342394577333638385010210910605025000000000:ℝ)*δ^1*p^2
theorem admission_power_Cnew_11_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 11 = admission_power_Cnew_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_11] <;> ring

def admission_power_Cnew_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cnew_12_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 12 = admission_power_Cnew_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_12] <;> ring

def admission_power_Cnew_13 (δ p : ℝ) : ℝ := (64972424551037892165253918981/2332206389300710100000000000000:ℝ)*δ^0*p^0
theorem admission_power_Cnew_13_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 13 = admission_power_Cnew_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_13] <;> ring

def admission_power_Cnew_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cnew_14_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 14 = admission_power_Cnew_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_14] <;> ring

def admission_power_Pnew_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-1:ℝ)*δ^0*p^1
theorem admission_power_Pnew_00_expanded (δ p : ℝ) : admissionGuard .Pnew δ p 0 = admission_power_Pnew_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pnew_00] <;> ring

def admission_power_Pnew_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0
theorem admission_power_Pnew_01_expanded (δ p : ℝ) : admissionGuard .Pnew δ p 1 = admission_power_Pnew_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pnew_01] <;> ring

def admission_power_Pnew_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-619999/5000000:ℝ)*δ^0*p^1
theorem admission_power_Pnew_02_expanded (δ p : ℝ) : admissionGuard .Pnew δ p 2 = admission_power_Pnew_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pnew_02] <;> ring

def admission_power_Pnew_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-5/6:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1
theorem admission_power_Pnew_03_expanded (δ p : ℝ) : admissionGuard .Pnew δ p 3 = admission_power_Pnew_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pnew_03] <;> ring

def admission_power_Pnew_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-5619999/5000000:ℝ)*δ^1*p^1 + (619999/5000000:ℝ)*δ^1*p^2
theorem admission_power_Pnew_04_expanded (δ p : ℝ) : admissionGuard .Pnew δ p 4 = admission_power_Pnew_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pnew_04] <;> ring

def admission_power_Pnew_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-833/4000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (4370499/5000000:ℝ)*δ^1*p^1 + (-619999/5000000:ℝ)*δ^1*p^2
theorem admission_power_Pnew_05_expanded (δ p : ℝ) : admissionGuard .Pnew δ p 5 = admission_power_Pnew_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pnew_05] <;> ring

def admission_power_Pnew_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-166180111/222000000:ℝ)*δ^0*p^1 + (15686679/74000000:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-393819889/185000000:ℝ)*δ^1*p^1 + (92939963/185000000:ℝ)*δ^1*p^2
theorem admission_power_Pnew_06_expanded (δ p : ℝ) : admissionGuard .Pnew δ p 6 = admission_power_Pnew_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pnew_06] <;> ring

def admission_power_Pnew_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-6859997/6000000:ℝ)*δ^0*p^1 + (619999/6000000:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (6859997/5000000:ℝ)*δ^1*p^1 + (-619999/5000000:ℝ)*δ^1*p^2
theorem admission_power_Pnew_07_expanded (δ p : ℝ) : admissionGuard .Pnew δ p 7 = admission_power_Pnew_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pnew_07] <;> ring

def admission_power_Pnew_08 (δ p : ℝ) : ℝ := (-1310003/4000000:ℝ)*δ^0*p^0 + (2225003/3000000:ℝ)*δ^0*p^1 + (-2530003/12000000:ℝ)*δ^0*p^2 + (11310003/10000000:ℝ)*δ^1*p^0 + (-11229999/5000000:ℝ)*δ^1*p^1 + (9949993/10000000:ℝ)*δ^1*p^2 + (-619999/5000000:ℝ)*δ^1*p^3
theorem admission_power_Pnew_08_expanded (δ p : ℝ) : admissionGuard .Pnew δ p 8 = admission_power_Pnew_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pnew_08] <;> ring

def admission_power_Pnew_09 (δ p : ℝ) : ℝ := (1824843167826357369008856401/2693850807314214858132000000:ℝ)*δ^0*p^0 + (-196975903597806075915181/202038810548566114359900:ℝ)*δ^0*p^1 + (6054192976085885667598383599/24244657265827933723188000000:ℝ)*δ^0*p^2 + (-8559470186111894514338856401/6734627018285537145330000000:ℝ)*δ^1*p^0 + (21746351396173022639646143599/10101940527428305717995000000:ℝ)*δ^1*p^1 + (-3832048499764548692374512401/4040776210971322287198000000:ℝ)*δ^1*p^2 + (619999/5000000:ℝ)*δ^1*p^3
theorem admission_power_Pnew_09_expanded (δ p : ℝ) : admissionGuard .Pnew δ p 9 = admission_power_Pnew_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pnew_09] <;> ring

def admission_power_Pnew_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-1348333/2000000:ℝ)*δ^1*p^1 + (319999/6000000:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (5994999/5000000:ℝ)*δ^2*p^1 + (-919999/5000000:ℝ)*δ^2*p^2
theorem admission_power_Pnew_10_expanded (δ p : ℝ) : admissionGuard .Pnew δ p 10 = admission_power_Pnew_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pnew_10] <;> ring

def admission_power_Pnew_11 (δ p : ℝ) : ℝ := (11859997/6000000:ℝ)*δ^0*p^0 + (-619999/1000000:ℝ)*δ^0*p^1 + (619999/6000000:ℝ)*δ^0*p^2 + (-10619999/5000000:ℝ)*δ^1*p^0 + (619999/2500000:ℝ)*δ^1*p^1 + (619999/5000000:ℝ)*δ^1*p^2
theorem admission_power_Pnew_11_expanded (δ p : ℝ) : admissionGuard .Pnew δ p 11 = admission_power_Pnew_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pnew_11] <;> ring

def admission_power_Pnew_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Pnew_12_expanded (δ p : ℝ) : admissionGuard .Pnew δ p 12 = admission_power_Pnew_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pnew_12] <;> ring

def admission_power_Pnew_13 (δ p : ℝ) : ℝ := (527367216886410068273181401/10101940527428305717995000000:ℝ)*δ^0*p^0
theorem admission_power_Pnew_13_expanded (δ p : ℝ) : admissionGuard .Pnew δ p 13 = admission_power_Pnew_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pnew_13] <;> ring

def admission_power_Pnew_14 (δ p : ℝ) : ℝ := (479997/2000000:ℝ)*δ^0*p^0 + (-159999/1000000:ℝ)*δ^0*p^1 + (53333/2000000:ℝ)*δ^0*p^2 + (-479997/5000000:ℝ)*δ^1*p^0 + (-159999/2500000:ℝ)*δ^1*p^1 + (159999/5000000:ℝ)*δ^1*p^2
theorem admission_power_Pnew_14_expanded (δ p : ℝ) : admissionGuard .Pnew δ p 14 = admission_power_Pnew_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pnew_14] <;> ring

def admission_power_Cphys_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-707826445838581723/250000000000000000:ℝ)*δ^0*p^1
theorem admission_power_Cphys_00_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 0 = admission_power_Cphys_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_00] <;> ring

def admission_power_Cphys_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-457826445838581723/250000000000000000:ℝ)*δ^0*p^1
theorem admission_power_Cphys_01_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 1 = admission_power_Cphys_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_01] <;> ring

def admission_power_Cphys_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-3971/4413:ℝ)*δ^0*p^1
theorem admission_power_Cphys_02_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 2 = admission_power_Cphys_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_02] <;> ring

def admission_power_Cphys_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-707826445838581723/300000000000000000:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (457826445838581723/250000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cphys_03_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 3 = admission_power_Cphys_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_03] <;> ring

def admission_power_Cphys_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-8384/4413:ℝ)*δ^1*p^1 + (3971/4413:ℝ)*δ^1*p^2
theorem admission_power_Cphys_04_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 4 = admission_power_Cphys_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_04] <;> ring

def admission_power_Cphys_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-589619429383538575259/1000000000000000000000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (72811913/44130000:ℝ)*δ^1*p^1 + (-4878550124391332802146099/11032500000000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cphys_05_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 5 = admission_power_Cphys_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_05] <;> ring

def admission_power_Cphys_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-4068415661980674861017/5442700000000000000000:ℝ)*δ^0*p^1 + (2477103582077472350021928044038798887539/6123037500000000000000000000000000000000:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-76125142142056735434259/13606750000000000000000:ℝ)*δ^1*p^1 + (46517210022984464171353/8164050000000000000000:ℝ)*δ^1*p^2 + (-2268431661781832642335441433047541103/1156250000000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cphys_06_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 6 = admission_power_Cphys_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_06] <;> ring

def admission_power_Cphys_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-677987567276184571511/147100000000000000000:ℝ)*δ^0*p^1 + (2810778816425008022033/1323900000000000000000:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (2033962701828553714533/367750000000000000000:ℝ)*δ^1*p^1 + (-2810778816425008022033/1103250000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cphys_07_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 7 = admission_power_Cphys_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_07] <;> ring

def admission_power_Cphys_08 (δ p : ℝ) : ℝ := (-986597858602568340331143599/2693850807314214858132000000:ℝ)*δ^0*p^0 + (809277588396119961465255876105482746604841077/1010194052742830571799500000000000000000000000:ℝ)*δ^0*p^1 + (-651352598550803925802239148125028556762630735198002688276835671/1515291079114245857699250000000000000000000000000000000000000000:ℝ)*δ^0*p^2 + (7721224876888105485661143599/6734627018285537145330000000:ℝ)*δ^1*p^0 + (-14827279295604527892378458425436149148399841077/5050970263714152858997500000000000000000000000:ℝ)*δ^1*p^1 + (2966456862886414051179488672997350454292658923/1262742565928538214749375000000000000000000000:ℝ)*δ^1*p^2 + (-353877153622110044289753880651223850351271/625000000000000000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cphys_08_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 8 = admission_power_Cphys_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_08] <;> ring

def admission_power_Cphys_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-1113306057814870129246510467/735500000000000000000000000:ℝ)*δ^0*p^1 + (2535598320056186867980248570130680164258183923/3309750000000000000000000000000000000000000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (7317599420425420113393277/2500000000000000000000000:ℝ)*δ^1*p^1 + (-1774551647063091299530989533/919375000000000000000000000:ℝ)*δ^1*p^2 + (841834600590657872120884280119319835741816077/2758125000000000000000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cphys_09_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 9 = admission_power_Cphys_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_09] <;> ring

def admission_power_Cphys_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-295144771151887149122827/264780000000000000000000:ℝ)*δ^1*p^1 + (40266585683543016569203/66195000000000000000000:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (348599/176520:ℝ)*δ^2*p^1 + (-266339478848112850877173/220650000000000000000000:ℝ)*δ^2*p^2 + (1373479337515745169/12500000000000000000:ℝ)*δ^2*p^3
theorem admission_power_Cphys_10_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 10 = admission_power_Cphys_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_10] <;> ring

def admission_power_Cphys_11 (δ p : ℝ) : ℝ := (1054787298171446285467/441300000000000000000:ℝ)*δ^0*p^0 + (-19855/4413:ℝ)*δ^0*p^1 + (2810778816425008022033/1323900000000000000000:ℝ)*δ^0*p^2 + (-12797/4413:ℝ)*δ^1*p^0 + (3013138105485661143599/551625000000000000000:ℝ)*δ^1*p^1 + (-44463545654854205713/17238281250000000000:ℝ)*δ^1*p^2
theorem admission_power_Cphys_11_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 11 = admission_power_Cphys_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_11] <;> ring

def admission_power_Cphys_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cphys_12_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 12 = admission_power_Cphys_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_12] <;> ring

def admission_power_Cphys_13 (δ p : ℝ) : ℝ := (527367216886410068273181401/10101940527428305717995000000:ℝ)*δ^0*p^0
theorem admission_power_Cphys_13_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 13 = admission_power_Cphys_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_13] <;> ring

def admission_power_Cphys_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cphys_14_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 14 = admission_power_Cphys_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_14] <;> ring

def admission_power_Cold_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-12230401/4230401:ℝ)*δ^0*p^1
theorem admission_power_Cold_00_expanded (δ p : ℝ) : admissionGuard .Cold δ p 0 = admission_power_Cold_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cold_00] <;> ring

def admission_power_Cold_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-8000000/4230401:ℝ)*δ^0*p^1
theorem admission_power_Cold_01_expanded (δ p : ℝ) : admissionGuard .Cold δ p 1 = admission_power_Cold_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cold_01] <;> ring

def admission_power_Cold_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-19452098647453/21152005000000:ℝ)*δ^0*p^1
theorem admission_power_Cold_02_expanded (δ p : ℝ) : admissionGuard .Cold δ p 2 = admission_power_Cold_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cold_02] <;> ring

def admission_power_Cold_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-61152005/25382406:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (8000000/4230401:ℝ)*δ^1*p^2
theorem admission_power_Cold_03_expanded (δ p : ℝ) : admissionGuard .Cold δ p 3 = admission_power_Cold_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cold_03] <;> ring

def admission_power_Cold_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-40604103647453/21152005000000:ℝ)*δ^1*p^1 + (19452098647453/21152005000000:ℝ)*δ^1*p^2
theorem admission_power_Cold_04_expanded (δ p : ℝ) : admissionGuard .Cold δ p 4 = admission_power_Cold_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cold_04] <;> ring

def admission_power_Cold_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-1455417719/2417372000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (35318217597953/21152005000000:ℝ)*δ^1*p^1 + (-9456098647453/21152005000000:ℝ)*δ^1*p^2
theorem admission_power_Cold_05_expanded (δ p : ℝ) : admissionGuard .Cold δ p 5 = admission_power_Cold_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cold_05] <;> ring

def admission_power_Cold_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-102137326447531/134164146000000:ℝ)*δ^0*p^1 + (556077277903160236613/1324325653939274000000:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-636294753552469/111803455000000:ℝ)*δ^1*p^1 + (19531396493202659290161/3310814134848185000000:ℝ)*δ^1*p^2 + (-195686416000000/94594689567091:ℝ)*δ^1*p^3
theorem admission_power_Cold_06_expanded (δ p : ℝ) : admissionGuard .Cold δ p 6 = admission_power_Cold_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cold_06] <;> ring

def admission_power_Cold_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-17072614420337/3626058000000:ℝ)*δ^0*p^1 + (237906966749907818653/107377755724806000000:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (17072614420337/3021715000000:ℝ)*δ^1*p^1 + (-237906966749907818653/89481463104005000000:ℝ)*δ^1*p^2
theorem admission_power_Cold_07_expanded (δ p : ℝ) : admissionGuard .Cold δ p 7 = admission_power_Cold_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cold_07] <;> ring

def admission_power_Cold_08 (δ p : ℝ) : ℝ := (-2833193376931/8000000000000:ℝ)*δ^0*p^0 + (5748929889384611333/7252116000000000000:ℝ)*δ^0*p^1 + (-186855770261659722301380577/429511022899224000000000000:ℝ)*δ^0*p^2 + (22833193376931/20000000000000:ℝ)*δ^1*p^0 + (-17879776162512462889/6043430000000000000:ℝ)*δ^1*p^1 + (28897326626264462889/12086860000000000000:ℝ)*δ^1*p^2 + (-51734226009634299099/89481463104005000000:ℝ)*δ^1*p^3
theorem admission_power_Cold_08_expanded (δ p : ℝ) : admissionGuard .Cold δ p 8 = admission_power_Cold_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cold_08] <;> ring

def admission_power_Cold_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-2798651095817/1813029000000:ℝ)*δ^0*p^1 + (171131131702440066893/214755511449612000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (8922790129343/3021715000000:ℝ)*δ^1*p^1 + (-11760021970017/6043430000000:ℝ)*δ^1*p^2 + (26321078371511818653/89481463104005000000:ℝ)*δ^1*p^3
theorem admission_power_Cold_09_expanded (δ p : ℝ) : admissionGuard .Cold δ p 9 = admission_power_Cold_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cold_09] <;> ring

def admission_power_Cold_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-28541222072453/25382406000000:ℝ)*δ^1*p^1 + (15782978347453/25382406000000:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (42190504022453/21152005000000:ℝ)*δ^2*p^1 + (-3731602706779/3021715000000:ℝ)*δ^2*p^2 + (480000/4230401:ℝ)*δ^2*p^3
theorem admission_power_Cold_10_expanded (δ p : ℝ) : admissionGuard .Cold δ p 10 = admission_power_Cold_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cold_10] <;> ring

def admission_power_Cold_11 (δ p : ℝ) : ℝ := (60660305942359/25382406000000:ℝ)*δ^0*p^0 + (-19452098647453/4230401000000:ℝ)*δ^0*p^1 + (237906966749907818653/107377755724806000000:ℝ)*δ^0*p^2 + (-61756108647453/21152005000000:ℝ)*δ^1*p^0 + (59452098647453/10576002500000:ℝ)*δ^1*p^1 + (-242542651609340181347/89481463104005000000:ℝ)*δ^1*p^2
theorem admission_power_Cold_11_expanded (δ p : ℝ) : admissionGuard .Cold δ p 11 = admission_power_Cold_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cold_11] <;> ring

def admission_power_Cold_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cold_12_expanded (δ p : ℝ) : admissionGuard .Cold δ p 12 = admission_power_Cold_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cold_12] <;> ring

def admission_power_Cold_13 (δ p : ℝ) : ℝ := (220742529263/5000000000000:ℝ)*δ^0*p^0
theorem admission_power_Cold_13_expanded (δ p : ℝ) : admissionGuard .Cold δ p 13 = admission_power_Cold_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cold_13] <;> ring

def admission_power_Cold_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cold_14_expanded (δ p : ℝ) : admissionGuard .Cold δ p 14 = admission_power_Cold_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cold_14] <;> ring

def admission_power_Pold_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-1:ℝ)*δ^0*p^1
theorem admission_power_Pold_00_expanded (δ p : ℝ) : admissionGuard .Pold δ p 0 = admission_power_Pold_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pold_00] <;> ring

def admission_power_Pold_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0
theorem admission_power_Pold_01_expanded (δ p : ℝ) : admissionGuard .Pold δ p 1 = admission_power_Pold_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pold_01] <;> ring

def admission_power_Pold_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-619999/5000000:ℝ)*δ^0*p^1
theorem admission_power_Pold_02_expanded (δ p : ℝ) : admissionGuard .Pold δ p 2 = admission_power_Pold_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pold_02] <;> ring

def admission_power_Pold_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-5/6:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1
theorem admission_power_Pold_03_expanded (δ p : ℝ) : admissionGuard .Pold δ p 3 = admission_power_Pold_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pold_03] <;> ring

def admission_power_Pold_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-5619999/5000000:ℝ)*δ^1*p^1 + (619999/5000000:ℝ)*δ^1*p^2
theorem admission_power_Pold_04_expanded (δ p : ℝ) : admissionGuard .Pold δ p 4 = admission_power_Pold_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pold_04] <;> ring

def admission_power_Pold_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-833/4000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (4370499/5000000:ℝ)*δ^1*p^1 + (-619999/5000000:ℝ)*δ^1*p^2
theorem admission_power_Pold_05_expanded (δ p : ℝ) : admissionGuard .Pold δ p 5 = admission_power_Pold_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pold_05] <;> ring

def admission_power_Pold_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-166180111/222000000:ℝ)*δ^0*p^1 + (15686679/74000000:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-393819889/185000000:ℝ)*δ^1*p^1 + (92939963/185000000:ℝ)*δ^1*p^2
theorem admission_power_Pold_06_expanded (δ p : ℝ) : admissionGuard .Pold δ p 6 = admission_power_Pold_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pold_06] <;> ring

def admission_power_Pold_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-6859997/6000000:ℝ)*δ^0*p^1 + (619999/6000000:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (6859997/5000000:ℝ)*δ^1*p^1 + (-619999/5000000:ℝ)*δ^1*p^2
theorem admission_power_Pold_07_expanded (δ p : ℝ) : admissionGuard .Pold δ p 7 = admission_power_Pold_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pold_07] <;> ring

def admission_power_Pold_08 (δ p : ℝ) : ℝ := (-1310003/4000000:ℝ)*δ^0*p^0 + (2225003/3000000:ℝ)*δ^0*p^1 + (-2530003/12000000:ℝ)*δ^0*p^2 + (11310003/10000000:ℝ)*δ^1*p^0 + (-11229999/5000000:ℝ)*δ^1*p^1 + (9949993/10000000:ℝ)*δ^1*p^2 + (-619999/5000000:ℝ)*δ^1*p^3
theorem admission_power_Pold_08_expanded (δ p : ℝ) : admissionGuard .Pold δ p 8 = admission_power_Pold_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pold_08] <;> ring

def admission_power_Pold_09 (δ p : ℝ) : ℝ := (5313997373149/8000000000000:ℝ)*δ^0*p^0 + (-11594003373149/12000000000000:ℝ)*δ^0*p^1 + (1986001041461/8000000000000:ℝ)*δ^0*p^2 + (-25313997373149/20000000000000:ℝ)*δ^1*p^0 + (21562000875617/10000000000000:ℝ)*δ^1*p^1 + (-19001988875617/20000000000000:ℝ)*δ^1*p^2 + (619999/5000000:ℝ)*δ^1*p^3
theorem admission_power_Pold_09_expanded (δ p : ℝ) : admissionGuard .Pold δ p 9 = admission_power_Pold_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pold_09] <;> ring

def admission_power_Pold_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-1348333/2000000:ℝ)*δ^1*p^1 + (319999/6000000:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (5994999/5000000:ℝ)*δ^2*p^1 + (-919999/5000000:ℝ)*δ^2*p^2
theorem admission_power_Pold_10_expanded (δ p : ℝ) : admissionGuard .Pold δ p 10 = admission_power_Pold_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pold_10] <;> ring

def admission_power_Pold_11 (δ p : ℝ) : ℝ := (11859997/6000000:ℝ)*δ^0*p^0 + (-619999/1000000:ℝ)*δ^0*p^1 + (619999/6000000:ℝ)*δ^0*p^2 + (-10619999/5000000:ℝ)*δ^1*p^0 + (619999/2500000:ℝ)*δ^1*p^1 + (619999/5000000:ℝ)*δ^1*p^2
theorem admission_power_Pold_11_expanded (δ p : ℝ) : admissionGuard .Pold δ p 11 = admission_power_Pold_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pold_11] <;> ring

def admission_power_Pold_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Pold_12_expanded (δ p : ℝ) : admissionGuard .Pold δ p 12 = admission_power_Pold_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pold_12] <;> ring

def admission_power_Pold_13 (δ p : ℝ) : ℝ := (262253340591/5000000000000:ℝ)*δ^0*p^0
theorem admission_power_Pold_13_expanded (δ p : ℝ) : admissionGuard .Pold δ p 13 = admission_power_Pold_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pold_13] <;> ring

def admission_power_Pold_14 (δ p : ℝ) : ℝ := (479997/2000000:ℝ)*δ^0*p^0 + (-159999/1000000:ℝ)*δ^0*p^1 + (53333/2000000:ℝ)*δ^0*p^2 + (-479997/5000000:ℝ)*δ^1*p^0 + (-159999/2500000:ℝ)*δ^1*p^1 + (159999/5000000:ℝ)*δ^1*p^2
theorem admission_power_Pold_14_expanded (δ p : ℝ) : admissionGuard .Pold δ p 14 = admission_power_Pold_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pold_14] <;> ring

def admission_power_Cphysold_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-12603201/4603201:ℝ)*δ^0*p^1
theorem admission_power_Cphysold_00_expanded (δ p : ℝ) : admissionGuard .Cphysold δ p 0 = admission_power_Cphysold_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphysold_00] <;> ring

def admission_power_Cphysold_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-8000000/4603201:ℝ)*δ^0*p^1
theorem admission_power_Cphysold_01_expanded (δ p : ℝ) : admissionGuard .Cphysold δ p 1 = admission_power_Cphysold_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphysold_01] <;> ring

def admission_power_Cphysold_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-3945996453113/4603201000000:ℝ)*δ^0*p^1
theorem admission_power_Cphysold_02_expanded (δ p : ℝ) : admissionGuard .Cphysold δ p 2 = admission_power_Cphysold_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphysold_02] <;> ring

def admission_power_Cphysold_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-21005335/9206402:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (8000000/4603201:ℝ)*δ^1*p^2
theorem admission_power_Cphysold_03_expanded (δ p : ℝ) : admissionGuard .Cphysold δ p 3 = admission_power_Cphysold_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphysold_03] <;> ring

def admission_power_Cphysold_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-8549197453113/4603201000000:ℝ)*δ^1*p^1 + (3945996453113/4603201000000:ℝ)*δ^1*p^2
theorem admission_power_Cphysold_04_expanded (δ p : ℝ) : admissionGuard .Cphysold δ p 4 = admission_power_Cphysold_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphysold_04] <;> ring

def admission_power_Cphysold_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-10498466433/18412804000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (7398857523213/4603201000000:ℝ)*δ^1*p^1 + (-1946796453113/4603201000000:ℝ)*δ^1*p^2
theorem admission_power_Cphysold_05_expanded (δ p : ℝ) : admissionGuard .Cphysold δ p 5 = admission_power_Cphysold_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphysold_05] <;> ring

def admission_power_Cphysold_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-51448280234819/68127374800000:ℝ)*δ^0*p^1 + (127892852608805351873/313603999806734800000:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-921213671295543/170318437000000:ℝ)*δ^1*p^1 + (4198977378672811944381/784009999516837000000:ℝ)*δ^1*p^2 + (-1411558512000000/784009999516837:ℝ)*δ^1*p^3
theorem admission_power_Cphysold_06_expanded (δ p : ℝ) : admissionGuard .Cphysold δ p 6 = admission_power_Cphysold_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphysold_06] <;> ring

def admission_power_Cphysold_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-8147063453113/1841280400000:ℝ)*δ^0*p^1 + (16577395481290071571/8475783778560400000:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (24441190359339/4603201000000:ℝ)*δ^1*p^1 + (-49732186443870214713/21189459446401000000:ℝ)*δ^1*p^2
theorem admission_power_Cphysold_07_expanded (δ p : ℝ) : admissionGuard .Cphysold δ p 7 = admission_power_Cphysold_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphysold_07] <;> ring

def admission_power_Cphysold_08 (δ p : ℝ) : ℝ := (-2690875283299/8000000000000:ℝ)*δ^0*p^0 + (13855252822653080033/18412804000000000000:ℝ)*δ^0*p^1 + (-68922529981893991264995211/169515675571208000000000000:ℝ)*δ^0*p^2 + (22690875283299/20000000000000:ℝ)*δ^1*p^0 + (-133533643779412919967/46032010000000000000:ℝ)*δ^1*p^1 + (211970917566604919967/92064020000000000000:ℝ)*δ^1*p^2 + (-58009157511784913499/105947297232005000000:ℝ)*δ^1*p^3
theorem admission_power_Cphysold_08_expanded (δ p : ℝ) : admissionGuard .Cphysold δ p 8 = admission_power_Cphysold_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphysold_08] <;> ring

def admission_power_Cphysold_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-6886757228117/4603201000000:ℝ)*δ^0*p^1 + (63221299342102243823/84757837785604000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (66439171278201/23016005000000:ℝ)*δ^1*p^1 + (-86103095871591/46032010000000:ℝ)*δ^1*p^2 + (6125121066431014713/21189459446401000000:ℝ)*δ^1*p^3
theorem admission_power_Cphysold_09_expanded (δ p : ℝ) : admissionGuard .Cphysold δ p 9 = admission_power_Cphysold_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphysold_09] <;> ring

def admission_power_Cphysold_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-2006396379371/1841280400000:ℝ)*δ^1*p^1 + (3189804393113/5523841200000:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (8894437528113/4603201000000:ℝ)*δ^2*p^1 + (-5302188513113/4603201000000:ℝ)*δ^2*p^2 + (480000/4603201:ℝ)*δ^2*p^3
theorem admission_power_Cphysold_10_expanded (δ p : ℝ) : admissionGuard .Cphysold δ p 10 = admission_power_Cphysold_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphysold_10] <;> ring

def admission_power_Cphysold_11 (δ p : ℝ) : ℝ := (4348130453113/1841280400000:ℝ)*δ^0*p^0 + (-3945996453113/920640200000:ℝ)*δ^0*p^1 + (16577395481290071571/8475783778560400000:ℝ)*δ^0*p^2 + (-13152398453113/4603201000000:ℝ)*δ^1*p^0 + (11945996453113/2301600500000:ℝ)*δ^1*p^1 + (-50229364805937785287/21189459446401000000:ℝ)*δ^1*p^2
theorem admission_power_Cphysold_11_expanded (δ p : ℝ) : admissionGuard .Cphysold δ p 11 = admission_power_Cphysold_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphysold_11] <;> ring

def admission_power_Cphysold_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cphysold_12_expanded (δ p : ℝ) : admissionGuard .Cphysold δ p 12 = admission_power_Cphysold_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphysold_12] <;> ring

def admission_power_Cphysold_13 (δ p : ℝ) : ℝ := (262253340591/5000000000000:ℝ)*δ^0*p^0
theorem admission_power_Cphysold_13_expanded (δ p : ℝ) : admissionGuard .Cphysold δ p 13 = admission_power_Cphysold_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphysold_13] <;> ring

def admission_power_Cphysold_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cphysold_14_expanded (δ p : ℝ) : admissionGuard .Cphysold δ p 14 = admission_power_Cphysold_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphysold_14] <;> ring

def admission_power_Pwide_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-1:ℝ)*δ^0*p^1
theorem admission_power_Pwide_00_expanded (δ p : ℝ) : admissionGuard .Pwide δ p 0 = admission_power_Pwide_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pwide_00] <;> ring

def admission_power_Pwide_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0
theorem admission_power_Pwide_01_expanded (δ p : ℝ) : admissionGuard .Pwide δ p 1 = admission_power_Pwide_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pwide_01] <;> ring

def admission_power_Pwide_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-899999/5000000:ℝ)*δ^0*p^1
theorem admission_power_Pwide_02_expanded (δ p : ℝ) : admissionGuard .Pwide δ p 2 = admission_power_Pwide_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pwide_02] <;> ring

def admission_power_Pwide_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-5/6:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1
theorem admission_power_Pwide_03_expanded (δ p : ℝ) : admissionGuard .Pwide δ p 3 = admission_power_Pwide_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pwide_03] <;> ring

def admission_power_Pwide_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-5899999/5000000:ℝ)*δ^1*p^1 + (899999/5000000:ℝ)*δ^1*p^2
theorem admission_power_Pwide_04_expanded (δ p : ℝ) : admissionGuard .Pwide δ p 4 = admission_power_Pwide_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pwide_04] <;> ring

def admission_power_Pwide_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-833/4000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (4650499/5000000:ℝ)*δ^1*p^1 + (-899999/5000000:ℝ)*δ^1*p^2
theorem admission_power_Pwide_05_expanded (δ p : ℝ) : admissionGuard .Pwide δ p 5 = admission_power_Pwide_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pwide_05] <;> ring

def admission_power_Pwide_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-135100111/222000000:ℝ)*δ^0*p^1 + (36700037/222000000:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-424899889/185000000:ℝ)*δ^1*p^1 + (103299963/185000000:ℝ)*δ^1*p^2
theorem admission_power_Pwide_06_expanded (δ p : ℝ) : admissionGuard .Pwide δ p 6 = admission_power_Pwide_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pwide_06] <;> ring

def admission_power_Pwide_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-7699997/6000000:ℝ)*δ^0*p^1 + (899999/6000000:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (7699997/5000000:ℝ)*δ^1*p^1 + (-899999/5000000:ℝ)*δ^1*p^2
theorem admission_power_Pwide_07_expanded (δ p : ℝ) : admissionGuard .Pwide δ p 7 = admission_power_Pwide_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pwide_07] <;> ring

def admission_power_Pwide_08 (δ p : ℝ) : ℝ := (-1310003/4000000:ℝ)*δ^0*p^0 + (1805003/3000000:ℝ)*δ^0*p^1 + (-1970003/12000000:ℝ)*δ^0*p^2 + (11310003/10000000:ℝ)*δ^1*p^0 + (-11229999/5000000:ℝ)*δ^1*p^1 + (11629993/10000000:ℝ)*δ^1*p^2 + (-899999/5000000:ℝ)*δ^1*p^3
theorem admission_power_Pwide_08_expanded (δ p : ℝ) : admissionGuard .Pwide δ p 8 = admission_power_Pwide_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pwide_08] <;> ring

def admission_power_Pwide_09 (δ p : ℝ) : ℝ := (1207023167826357369008856401/2693850807314214858132000000:ℝ)*δ^0*p^0 + (-27559894024201363980959/40407762109713222871980:ℝ)*δ^0*p^1 + (4304955637013915427182943599/24244657265827933723188000000:ℝ)*δ^0*p^2 + (-7941650186111894514338856401/6734627018285537145330000000:ℝ)*δ^1*p^0 + (22364171396173022639646143599/10101940527428305717995000000:ℝ)*δ^1*p^1 + (-4634462903207730836623776401/4040776210971322287198000000:ℝ)*δ^1*p^2 + (899999/5000000:ℝ)*δ^1*p^3
theorem admission_power_Pwide_09_expanded (δ p : ℝ) : admissionGuard .Pwide δ p 9 = admission_power_Pwide_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pwide_09] <;> ring

def admission_power_Pwide_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-4324999/6000000:ℝ)*δ^1*p^1 + (599999/6000000:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (6274999/5000000:ℝ)*δ^2*p^1 + (-1199999/5000000:ℝ)*δ^2*p^2
theorem admission_power_Pwide_10_expanded (δ p : ℝ) : admissionGuard .Pwide δ p 10 = admission_power_Pwide_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pwide_10] <;> ring

def admission_power_Pwide_11 (δ p : ℝ) : ℝ := (12699997/6000000:ℝ)*δ^0*p^0 + (-899999/1000000:ℝ)*δ^0*p^1 + (899999/6000000:ℝ)*δ^0*p^2 + (-10899999/5000000:ℝ)*δ^1*p^0 + (899999/2500000:ℝ)*δ^1*p^1 + (899999/5000000:ℝ)*δ^1*p^2
theorem admission_power_Pwide_11_expanded (δ p : ℝ) : admissionGuard .Pwide δ p 11 = admission_power_Pwide_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pwide_11] <;> ring

def admission_power_Pwide_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Pwide_12_expanded (δ p : ℝ) : admissionGuard .Pwide δ p 12 = admission_power_Pwide_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pwide_12] <;> ring

def admission_power_Pwide_13 (δ p : ℝ) : ℝ := (527367216886410068273181401/10101940527428305717995000000:ℝ)*δ^0*p^0
theorem admission_power_Pwide_13_expanded (δ p : ℝ) : admissionGuard .Pwide δ p 13 = admission_power_Pwide_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pwide_13] <;> ring

def admission_power_Pwide_14 (δ p : ℝ) : ℝ := (899997/2000000:ℝ)*δ^0*p^0 + (-299999/1000000:ℝ)*δ^0*p^1 + (299999/6000000:ℝ)*δ^0*p^2 + (-899997/5000000:ℝ)*δ^1*p^0 + (-299999/2500000:ℝ)*δ^1*p^1 + (299999/5000000:ℝ)*δ^1*p^2
theorem admission_power_Pwide_14_expanded (δ p : ℝ) : admissionGuard .Pwide δ p 14 = admission_power_Pwide_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pwide_14] <;> ring

def admission_power_Pcount_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-1:ℝ)*δ^0*p^1
theorem admission_power_Pcount_00_expanded (δ p : ℝ) : admissionGuard .Pcount δ p 0 = admission_power_Pcount_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pcount_00] <;> ring

def admission_power_Pcount_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0
theorem admission_power_Pcount_01_expanded (δ p : ℝ) : admissionGuard .Pcount δ p 1 = admission_power_Pcount_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pcount_01] <;> ring

def admission_power_Pcount_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-1009899/5000000:ℝ)*δ^0*p^1
theorem admission_power_Pcount_02_expanded (δ p : ℝ) : admissionGuard .Pcount δ p 2 = admission_power_Pcount_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pcount_02] <;> ring

def admission_power_Pcount_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-5/6:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1
theorem admission_power_Pcount_03_expanded (δ p : ℝ) : admissionGuard .Pcount δ p 3 = admission_power_Pcount_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pcount_03] <;> ring

def admission_power_Pcount_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-6009899/5000000:ℝ)*δ^1*p^1 + (1009899/5000000:ℝ)*δ^1*p^2
theorem admission_power_Pcount_04_expanded (δ p : ℝ) : admissionGuard .Pcount δ p 4 = admission_power_Pcount_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pcount_04] <;> ring

def admission_power_Pcount_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-833/4000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (4760399/5000000:ℝ)*δ^1*p^1 + (-1009899/5000000:ℝ)*δ^1*p^2
theorem admission_power_Pcount_05_expanded (δ p : ℝ) : admissionGuard .Pcount δ p 5 = admission_power_Pcount_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pcount_05] <;> ring

def admission_power_Pcount_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-122901211/222000000:ℝ)*δ^0*p^1 + (32633737/222000000:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-437098789/185000000:ℝ)*δ^1*p^1 + (107366263/185000000:ℝ)*δ^1*p^2
theorem admission_power_Pcount_06_expanded (δ p : ℝ) : admissionGuard .Pcount δ p 6 = admission_power_Pcount_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pcount_06] <;> ring

def admission_power_Pcount_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-8029697/6000000:ℝ)*δ^0*p^1 + (336633/2000000:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (8029697/5000000:ℝ)*δ^1*p^1 + (-1009899/5000000:ℝ)*δ^1*p^2
theorem admission_power_Pcount_07_expanded (δ p : ℝ) : admissionGuard .Pcount δ p 7 = admission_power_Pcount_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pcount_07] <;> ring

def admission_power_Pcount_08 (δ p : ℝ) : ℝ := (-1310003/4000000:ℝ)*δ^0*p^0 + (1640153/3000000:ℝ)*δ^0*p^1 + (-583401/4000000:ℝ)*δ^0*p^2 + (11310003/10000000:ℝ)*δ^1*p^0 + (-11229999/5000000:ℝ)*δ^1*p^1 + (12289393/10000000:ℝ)*δ^1*p^2 + (-1009899/5000000:ℝ)*δ^1*p^3
theorem admission_power_Pcount_08_expanded (δ p : ℝ) : admissionGuard .Pcount δ p 8 = admission_power_Pcount_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pcount_08] <;> ring

def admission_power_Pcount_09 (δ p : ℝ) : ℝ := (730950819584738955320547226943/1865765111440568080000000000000:ℝ)*δ^0*p^0 + (-1649981468676410357752607226943/2798647667160852120000000000000:ℝ)*δ^0*p^1 + (285445790863120195576074136327/1865765111440568080000000000000:ℝ)*δ^0*p^2 + (-5395363598186159155320547226943/4664412778601420200000000000000:ℝ)*δ^1*p^0 + (5198164635173410581559817591019/2332206389300710100000000000000:ℝ)*δ^1*p^1 + (-5692309726290777876695697591019/4664412778601420200000000000000:ℝ)*δ^1*p^2 + (1009899/5000000:ℝ)*δ^1*p^3
theorem admission_power_Pcount_09_expanded (δ p : ℝ) : admissionGuard .Pcount δ p 9 = admission_power_Pcount_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pcount_09] <;> ring

def admission_power_Pcount_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-4434899/6000000:ℝ)*δ^1*p^1 + (236633/2000000:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (6384899/5000000:ℝ)*δ^2*p^1 + (-1309899/5000000:ℝ)*δ^2*p^2
theorem admission_power_Pcount_10_expanded (δ p : ℝ) : admissionGuard .Pcount δ p 10 = admission_power_Pcount_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pcount_10] <;> ring

def admission_power_Pcount_11 (δ p : ℝ) : ℝ := (13029697/6000000:ℝ)*δ^0*p^0 + (-1009899/1000000:ℝ)*δ^0*p^1 + (336633/2000000:ℝ)*δ^0*p^2 + (-11009899/5000000:ℝ)*δ^1*p^0 + (1009899/2500000:ℝ)*δ^1*p^1 + (1009899/5000000:ℝ)*δ^1*p^2
theorem admission_power_Pcount_11_expanded (δ p : ℝ) : admissionGuard .Pcount δ p 11 = admission_power_Pcount_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pcount_11] <;> ring

def admission_power_Pcount_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Pcount_12_expanded (δ p : ℝ) : admissionGuard .Pcount δ p 12 = admission_power_Pcount_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pcount_12] <;> ring

def admission_power_Pcount_13 (δ p : ℝ) : ℝ := (64972424551037892165253918981/2332206389300710100000000000000:ℝ)*δ^0*p^0
theorem admission_power_Pcount_13_expanded (δ p : ℝ) : admissionGuard .Pcount δ p 13 = admission_power_Pcount_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pcount_13] <;> ring

def admission_power_Pcount_14 (δ p : ℝ) : ℝ := (1064847/2000000:ℝ)*δ^0*p^0 + (-354949/1000000:ℝ)*δ^0*p^1 + (354949/6000000:ℝ)*δ^0*p^2 + (-1064847/5000000:ℝ)*δ^1*p^0 + (-354949/2500000:ℝ)*δ^1*p^1 + (354949/5000000:ℝ)*δ^1*p^2
theorem admission_power_Pcount_14_expanded (δ p : ℝ) : admissionGuard .Pcount δ p 14 = admission_power_Pcount_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pcount_14] <;> ring

def admission_power_Pcountmid_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-1:ℝ)*δ^0*p^1
theorem admission_power_Pcountmid_00_expanded (δ p : ℝ) : admissionGuard .Pcountmid δ p 0 = admission_power_Pcountmid_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pcountmid_00] <;> ring

def admission_power_Pcountmid_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0
theorem admission_power_Pcountmid_01_expanded (δ p : ℝ) : admissionGuard .Pcountmid δ p 1 = admission_power_Pcountmid_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pcountmid_01] <;> ring

def admission_power_Pcountmid_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-1004899/5000000:ℝ)*δ^0*p^1
theorem admission_power_Pcountmid_02_expanded (δ p : ℝ) : admissionGuard .Pcountmid δ p 2 = admission_power_Pcountmid_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pcountmid_02] <;> ring

def admission_power_Pcountmid_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-5/6:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1
theorem admission_power_Pcountmid_03_expanded (δ p : ℝ) : admissionGuard .Pcountmid δ p 3 = admission_power_Pcountmid_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pcountmid_03] <;> ring

def admission_power_Pcountmid_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-6004899/5000000:ℝ)*δ^1*p^1 + (1004899/5000000:ℝ)*δ^1*p^2
theorem admission_power_Pcountmid_04_expanded (δ p : ℝ) : admissionGuard .Pcountmid δ p 4 = admission_power_Pcountmid_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pcountmid_04] <;> ring

def admission_power_Pcountmid_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-833/4000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (4755399/5000000:ℝ)*δ^1*p^1 + (-1004899/5000000:ℝ)*δ^1*p^2
theorem admission_power_Pcountmid_05_expanded (δ p : ℝ) : admissionGuard .Pcountmid δ p 5 = admission_power_Pcountmid_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pcountmid_05] <;> ring

def admission_power_Pcountmid_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-123456211/222000000:ℝ)*δ^0*p^1 + (10939579/74000000:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-436543789/185000000:ℝ)*δ^1*p^1 + (107181263/185000000:ℝ)*δ^1*p^2
theorem admission_power_Pcountmid_06_expanded (δ p : ℝ) : admissionGuard .Pcountmid δ p 6 = admission_power_Pcountmid_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pcountmid_06] <;> ring

def admission_power_Pcountmid_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-8014697/6000000:ℝ)*δ^0*p^1 + (1004899/6000000:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (8014697/5000000:ℝ)*δ^1*p^1 + (-1004899/5000000:ℝ)*δ^1*p^2
theorem admission_power_Pcountmid_07_expanded (δ p : ℝ) : admissionGuard .Pcountmid δ p 7 = admission_power_Pcountmid_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pcountmid_07] <;> ring

def admission_power_Pcountmid_08 (δ p : ℝ) : ℝ := (-1310003/4000000:ℝ)*δ^0*p^0 + (1647653/3000000:ℝ)*δ^0*p^1 + (-1760203/12000000:ℝ)*δ^0*p^2 + (11310003/10000000:ℝ)*δ^1*p^0 + (-11229999/5000000:ℝ)*δ^1*p^1 + (12259393/10000000:ℝ)*δ^1*p^2 + (-1004899/5000000:ℝ)*δ^1*p^3
theorem admission_power_Pcountmid_08_expanded (δ p : ℝ) : admissionGuard .Pcountmid δ p 8 = admission_power_Pcountmid_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pcountmid_08] <;> ring

def admission_power_Pcountmid_09 (δ p : ℝ) : ℝ := (736949070429946979787972226943/1865765111440568080000000000000:ℝ)*δ^0*p^0 + (-1662976338689520512520032226943/2798647667160852120000000000000:ℝ)*δ^0*p^1 + (863001202316364681750697408981/5597295334321704240000000000000:ℝ)*δ^0*p^2 + (-5401361849031367179787972226943/4664412778601420200000000000000:ℝ)*δ^1*p^0 + (5196165218225007906737342591019/2332206389300710100000000000000:ℝ)*δ^1*p^1 + (-5676317071006570941273222591019/4664412778601420200000000000000:ℝ)*δ^1*p^2 + (1004899/5000000:ℝ)*δ^1*p^3
theorem admission_power_Pcountmid_09_expanded (δ p : ℝ) : admissionGuard .Pcountmid δ p 9 = admission_power_Pcountmid_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pcountmid_09] <;> ring

def admission_power_Pcountmid_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-1476633/2000000:ℝ)*δ^1*p^1 + (704899/6000000:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (6379899/5000000:ℝ)*δ^2*p^1 + (-1304899/5000000:ℝ)*δ^2*p^2
theorem admission_power_Pcountmid_10_expanded (δ p : ℝ) : admissionGuard .Pcountmid δ p 10 = admission_power_Pcountmid_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pcountmid_10] <;> ring

def admission_power_Pcountmid_11 (δ p : ℝ) : ℝ := (13014697/6000000:ℝ)*δ^0*p^0 + (-1004899/1000000:ℝ)*δ^0*p^1 + (1004899/6000000:ℝ)*δ^0*p^2 + (-11004899/5000000:ℝ)*δ^1*p^0 + (1004899/2500000:ℝ)*δ^1*p^1 + (1004899/5000000:ℝ)*δ^1*p^2
theorem admission_power_Pcountmid_11_expanded (δ p : ℝ) : admissionGuard .Pcountmid δ p 11 = admission_power_Pcountmid_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pcountmid_11] <;> ring

def admission_power_Pcountmid_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Pcountmid_12_expanded (δ p : ℝ) : admissionGuard .Pcountmid δ p 12 = admission_power_Pcountmid_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pcountmid_12] <;> ring

def admission_power_Pcountmid_13 (δ p : ℝ) : ℝ := (64972424551037892165253918981/2332206389300710100000000000000:ℝ)*δ^0*p^0
theorem admission_power_Pcountmid_13_expanded (δ p : ℝ) : admissionGuard .Pcountmid δ p 13 = admission_power_Pcountmid_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pcountmid_13] <;> ring

def admission_power_Pcountmid_14 (δ p : ℝ) : ℝ := (1057347/2000000:ℝ)*δ^0*p^0 + (-352449/1000000:ℝ)*δ^0*p^1 + (117483/2000000:ℝ)*δ^0*p^2 + (-1057347/5000000:ℝ)*δ^1*p^0 + (-352449/2500000:ℝ)*δ^1*p^1 + (352449/5000000:ℝ)*δ^1*p^2
theorem admission_power_Pcountmid_14_expanded (δ p : ℝ) : admissionGuard .Pcountmid δ p 14 = admission_power_Pcountmid_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pcountmid_14] <;> ring

def admission_power_Cbridge0_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-70462953437438059/25000000000000000:ℝ)*δ^0*p^1
theorem admission_power_Cbridge0_00_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 0 = admission_power_Cbridge0_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_00] <;> ring

def admission_power_Cbridge0_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-45462953437438059/25000000000000000:ℝ)*δ^0*p^1
theorem admission_power_Cbridge0_01_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 1 = admission_power_Cbridge0_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_01] <;> ring

def admission_power_Cbridge0_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-350250521339895109/391588771790181327:ℝ)*δ^0*p^1
theorem admission_power_Cbridge0_02_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 2 = admission_power_Cbridge0_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_02] <;> ring

def admission_power_Cbridge0_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-70462953437438059/30000000000000000:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (45462953437438059/25000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge0_03_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 3 = admission_power_Cbridge0_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_03] <;> ring

def admission_power_Cbridge0_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-741839293130076436/391588771790181327:ℝ)*δ^1*p^1 + (350250521339895109/391588771790181327:ℝ)*δ^1*p^2
theorem admission_power_Cbridge0_04_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 4 = admission_power_Cbridge0_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_04] <;> ring

def admission_power_Cbridge0_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-58695640213385903147/100000000000000000000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (6439812590597101223827/3915887717901813270000:ℝ)*δ^1*p^1 + (-43073477870770868349365204653630191793/97897192947545331750000000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge0_05_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 5 = admission_power_Cbridge0_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_05] <;> ring

def admission_power_Cbridge0_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-36100263196191222870174086580382419/48295948520789030330000000000000000:ℝ)*δ^0*p^1 + (2195389129594731059087516768704622099928842771071009/5433294208588765912125000000000000000000000000000000:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-672580313047742244998766212213752913/120739871301972575825000000000000000:ℝ)*δ^1*p^1 + (409432051235667710813492644848047471/72443922781183545495000000000000000:ℝ)*δ^1*p^2 + (-22424177798334287498659566231812367/11562500000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge0_06_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 6 = admission_power_Cbridge0_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_06] <;> ring

def admission_power_Cbridge0_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-5984587832640804237663278437880477/1305295905967271090000000000000000:ℝ)*δ^0*p^1 + (24679686176611434309058672744553431/11747663153705439810000000000000000:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (17953763497922412712989835313641431/3263239764918177725000000000000000:ℝ)*δ^1*p^1 + (-24679686176611434309058672744553431/9789719294754533175000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge0_07_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 7 = admission_power_Cbridge0_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_07] <;> ring

def admission_power_Cbridge0_08 (δ p : ℝ) : ℝ := (-8642580076475777206374785833091630924293/23737042798027429051959341254565724000000:ℝ)*δ^0*p^0 + (709281501393636917789675800621963839553639211008250867287/890139104926028589448475297046214650000000000000000000000:ℝ)*δ^0*p^1 + (-57045488408451732104367040818072924166252308914635742805274889008646875933/133520865738904288417271294556932197500000000000000000000000000000000000000:ℝ)*δ^0*p^2 + (67985187071544349836273138969505940924293/59342606995068572629898353136414310000000:ℝ)*δ^1*p^0 + (-13043634614582348037263770444147329433905198204120395867287/4450695524630142947242376485231073250000000000000000000000:ℝ)*δ^1*p^1 + (2606018541029873899374170860328818259613621535547821632713/1112673881157535736810594121307768312500000000000000000000:ℝ)*δ^1*p^2 + (-3522788630503072697189550191490538312519/6250000000000000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge0_08_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 8 = admission_power_Cbridge0_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_08] <;> ring

def admission_power_Cbridge0_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-9856241147933790709704657552261490433569/6526479529836355450000000000000000000000:ℝ)*δ^0*p^1 + (2238954045976610743360047431266515459827972508005620407713/2936915788426359952500000000000000000000000000000000000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (730377278153966167736941/250000000000000000000000:ℝ)*δ^1*p^1 + (-15690359973691735191288994792439702066431/8158099412295444312500000000000000000000:ℝ)*δ^1*p^2 + (744484477358725148991531299358275197689702491994379592287/2447429823688633293750000000000000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge0_09_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 9 = admission_power_Cbridge0_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_09] <;> ring

def admission_power_Cbridge0_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-2611769033420791151672823339595044089/2349532630741087962000000000000000000:ℝ)*δ^1*p^1 + (355035647495043571358091482177227121/587383157685271990500000000000000000:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (30848338040573601421/15663550871607253080:ℝ)*δ^2*p^1 + (-2349404354896585381402176660404955911/1957943858950906635000000000000000000:ℝ)*δ^2*p^2 + (136388860312314177/1250000000000000000:ℝ)*δ^2*p^3
theorem admission_power_Cbridge0_10_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 10 = admission_power_Cbridge0_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_10] <;> ring

def admission_power_Cbridge0_11 (δ p : ℝ) : ℝ := (9348481863826875912010164686358569/3915887717901813270000000000000000:ℝ)*δ^0*p^0 + (-1751252606699475545/391588771790181327:ℝ)*δ^0*p^1 + (24679686176611434309058672744553431/11747663153705439810000000000000000:ℝ)*δ^0*p^2 + (-1133428064920257763/391588771790181327:ℝ)*δ^1*p^0 + (26559045132017949513969505940924293/4894859647377266587500000000000000:ℝ)*δ^1*p^1 + (-6242485552034312662007044671369431/2447429823688633293750000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge0_11_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 11 = admission_power_Cbridge0_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_11] <;> ring

def admission_power_Cbridge0_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge0_12_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 12 = admission_power_Cbridge0_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_12] <;> ring

def admission_power_Cbridge0_13 (δ p : ℝ) : ℝ := (4691728799798896328068747835996491850707/89013910492602858944847529704621465000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge0_13_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 13 = admission_power_Cbridge0_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_13] <;> ring

def admission_power_Cbridge0_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cbridge0_14_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 14 = admission_power_Cbridge0_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_14] <;> ring

def admission_power_Cbridge1_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-22698276729921387/7812500000000000:ℝ)*δ^0*p^1
theorem admission_power_Cbridge1_00_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 0 = admission_power_Cbridge1_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_00] <;> ring

def admission_power_Cbridge1_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-14885776729921387/7812500000000000:ℝ)*δ^0*p^1
theorem admission_power_Cbridge1_01_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 1 = admission_power_Cbridge1_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_01] <;> ring

def admission_power_Cbridge1_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-5193/5579:ℝ)*δ^0*p^1
theorem admission_power_Cbridge1_02_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 2 = admission_power_Cbridge1_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_02] <;> ring

def admission_power_Cbridge1_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-7566092243307129/3125000000000000:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (14885776729921387/7812500000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge1_03_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 3 = admission_power_Cbridge1_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_03] <;> ring

def admission_power_Cbridge1_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-10772/5579:ℝ)*δ^1*p^1 + (5193/5579:ℝ)*δ^1*p^2
theorem admission_power_Cbridge1_04_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 4 = admission_power_Cbridge1_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_04] <;> ring

def admission_power_Cbridge1_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-18907664516024515371/31250000000000000000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (93778079/55790000:ℝ)*δ^1*p^1 + (-198166801807797686235573/435859375000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge1_05_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 5 = admission_power_Cbridge1_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_05] <;> ring

def admission_power_Cbridge1_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-482826182894292216477/645071875000000000000:ℝ)*δ^0*p^1 + (146874084989013102715277636940342417/359973144531250000000000000000000000:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-9246488837653322615679/1612679687500000000000:ℝ)*δ^1*p^1 + (274918474949508132333/46076562500000000000:ℝ)*δ^1*p^2 + (-2365170356889059283937486400026383/1129150390625000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge1_06_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 6 = admission_power_Cbridge1_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_06] <;> ring

def admission_power_Cbridge1_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-82781541125410472691/17434375000000000000:ℝ)*δ^0*p^1 + (5612959574213417271/2490625000000000000:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (248344623376231418073/43585937500000000000:ℝ)*δ^1*p^1 + (-16838878722640251813/6226562500000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge1_07_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 7 = admission_power_Cbridge1_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_07] <;> ring

def admission_power_Cbridge1_08 (δ p : ℝ) : ℝ := (-125142928459055947964254219/332190993504925672292000000:ℝ)*δ^0*p^0 + (1068974495695742067183163816599948736027251/1297621068378615907390625000000000000000000:ℝ)*δ^0*p^1 + (-1287431179139600574843315028145626975795403267002181653197/2896475599059410507568359375000000000000000000000000000000:ℝ)*δ^0*p^2 + (955620412221370128694254219/830477483762314180730000000:ℝ)*δ^1*p^0 + (-19228843743653854151566159665364160821027251/6488105341893079536953125000000000000000000:ℝ)*δ^1*p^1 + (554020066900469323913791774605040329496107/231718047924752840605468750000000000000000:ℝ)*δ^1*p^2 + (-354624415305577709106242919644799996231/610351562500000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge1_08_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 8 = admission_power_Cbridge1_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_08] <;> ring

def admission_power_Cbridge1_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-133782859153962643479306927/87171875000000000000000000:ℝ)*δ^0*p^1 + (153470009539167960432107744145799144740369/194580078125000000000000000000000000000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (231177860096133268853613/78125000000000000000000:ℝ)*δ^1*p^1 + (-214552845735735413248193073/108964843750000000000000000:ℝ)*δ^1*p^2 + (150851762432736081800001462875102565778893/486450195312500000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge1_09_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 9 = admission_power_Cbridge1_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_09] <;> ring

def admission_power_Cbridge1_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-11843046731341751712029/10460625000000000000000:ℝ)*δ^1*p^1 + (549538189123768581927/871718750000000000000:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (447617/223160:ℝ)*δ^2*p^1 + (-10879382956158248287971/8717187500000000000000:ℝ)*δ^2*p^2 + (44657330189764161/390625000000000000:ℝ)*δ^2*p^3
theorem admission_power_Cbridge1_10_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 10 = admission_power_Cbridge1_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_10] <;> ring

def admission_power_Cbridge1_11 (δ p : ℝ) : ℝ := (41945021374589527309/17434375000000000000:ℝ)*δ^0*p^0 + (-25965/5579:ℝ)*δ^0*p^1 + (5612959574213417271/2490625000000000000:ℝ)*δ^0*p^2 + (-16351/5579:ℝ)*δ^1*p^0 + (123618060876231418073/21792968750000000000:ℝ)*δ^1*p^1 + (-29944818608678295191/10896484375000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge1_11_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 11 = admission_power_Cbridge1_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_11] <;> ring

def admission_power_Cbridge1_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge1_12_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 12 = admission_power_Cbridge1_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_12] <;> ring

def admission_power_Cbridge1_13 (δ p : ℝ) : ℝ := (20369880553175740602856927/415238741881157090365000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge1_13_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 13 = admission_power_Cbridge1_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_13] <;> ring

def admission_power_Cbridge1_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cbridge1_14_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 14 = admission_power_Cbridge1_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_14] <;> ring

def admission_power_Cbridge2_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-149996347815657103/50000000000000000:ℝ)*δ^0*p^1
theorem admission_power_Cbridge2_00_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 0 = admission_power_Cbridge2_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_00] <;> ring

def admission_power_Cbridge2_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-99996347815657103/50000000000000000:ℝ)*δ^0*p^1
theorem admission_power_Cbridge2_01_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 1 = admission_power_Cbridge2_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_01] <;> ring

def admission_power_Cbridge2_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-15239/15717:ℝ)*δ^0*p^1
theorem admission_power_Cbridge2_02_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 2 = admission_power_Cbridge2_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_02] <;> ring

def admission_power_Cbridge2_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-149996347815657103/60000000000000000:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (99996347815657103/50000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge2_03_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 3 = admission_power_Cbridge2_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_03] <;> ring

def admission_power_Cbridge2_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-30956/15717:ℝ)*δ^1*p^1 + (15239/15717:ℝ)*δ^1*p^2
theorem admission_power_Cbridge2_04_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 4 = admission_power_Cbridge2_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_04] <;> ring

def admission_power_Cbridge2_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-124946957730442366799/200000000000000000000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (270283217/157170000:ℝ)*δ^1*p^1 + (-3691965146051911963060351/7858500000000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge2_05_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 5 = admission_power_Cbridge2_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_05] <;> ring

def admission_power_Cbridge2_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-8741900711692695442999/11630580000000000000000:ℝ)*δ^0*p^1 + (360947190031127929070609622020599689571/872293500000000000000000000000000000000:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-57268159922743233940191/9692150000000000000000:ℝ)*δ^1*p^1 + (36717655252813955689297/5815290000000000000000:ℝ)*δ^1*p^2 + (-104993608770769083571513941720468263/46250000000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge2_06_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 6 = admission_power_Cbridge2_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_06] <;> ring

def admission_power_Cbridge2_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-1547780866206227562617/314340000000000000000:ℝ)*δ^0*p^1 + (2285794344362798592617/943020000000000000000:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (1547780866206227562617/261950000000000000000:ℝ)*δ^1*p^1 + (-2285794344362798592617/785850000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge2_07_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 7 = admission_power_Cbridge2_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_07] <;> ring

def admission_power_Cbridge2_08 (δ p : ℝ) : ℝ := (-809151651280322992512687851/2095523464824910250468000000:ℝ)*δ^0*p^0 + (133309789537542128924565693688136553044955653/157164259861868268785100000000000000000000000:ℝ)*δ^0*p^1 + (-21786937504107884882214006262984063340481717779478036454453259/47149277958560480635530000000000000000000000000000000000000000:ℝ)*δ^0*p^2 + (6047960313342598618682687851/5238808662062275626170000000:ℝ)*δ^1*p^0 + (-2357441809662061179503742187947803145799955653/785821299309341343925500000000000000000000000:ℝ)*δ^1*p^1 + (480419806811747725078574936679196743332544347/196455324827335335981375000000000000000000000:ℝ)*δ^1*p^2 + (-14998104819365804910533475498008325647391/25000000000000000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge2_08_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 8 = admission_power_Cbridge2_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_08] <;> ring

def admission_power_Cbridge2_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-2457248800502066193187887149/1571700000000000000000000000:ℝ)*δ^0*p^1 + (386488559317756538848949285557781662399269347/471510000000000000000000000000000000000000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (1499984204306369154817897/500000000000000000000000:ℝ)*δ^1*p^1 + (-1320434571042000904451537617/654875000000000000000000000:ℝ)*δ^1*p^2 + (123319097258903661464695071892218337600730653/392925000000000000000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge2_09_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 9 = admission_power_Cbridge2_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_09] <;> ring

def admission_power_Cbridge2_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-217617099837295567428023/188604000000000000000000:ℝ)*δ^1*p^1 + (31025022204143951936447/47151000000000000000000:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (1285391/628680:ℝ)*δ^2*p^1 + (-204254550162704432571977/157170000000000000000000:ℝ)*δ^2*p^2 + (299989043446971309/2500000000000000000:ℝ)*δ^2*p^3
theorem admission_power_Cbridge2_10_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 10 = admission_power_Cbridge2_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_10] <;> ring

def admission_power_Cbridge2_11 (δ p : ℝ) : ℝ := (253989711264590812461/104780000000000000000:ℝ)*δ^0*p^0 + (-76195/15717:ℝ)*δ^0*p^1 + (2285794344362798592617/943020000000000000000:ℝ)*δ^0*p^2 + (-46673/15717:ℝ)*δ^1*p^0 + (2333592598618682687851/392925000000000000000:ℝ)*δ^1*p^1 + (-194461411915123440039/65487500000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge2_11_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 11 = admission_power_Cbridge2_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_11] <;> ring

def admission_power_Cbridge2_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge2_12_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 12 = admission_power_Cbridge2_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_12] <;> ring

def admission_power_Cbridge2_13 (δ p : ℝ) : ℝ := (350632617631598756361737149/7858212993093413439255000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge2_13_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 13 = admission_power_Cbridge2_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_13] <;> ring

def admission_power_Cbridge2_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cbridge2_14_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 14 = admission_power_Cbridge2_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_14] <;> ring

def admission_power_Cbridge3_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-77645851112471137/25000000000000000:ℝ)*δ^0*p^1
theorem admission_power_Cbridge3_00_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 0 = admission_power_Cbridge3_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_00] <;> ring

def admission_power_Cbridge3_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-52645851112471137/25000000000000000:ℝ)*δ^0*p^1
theorem admission_power_Cbridge3_01_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 1 = admission_power_Cbridge3_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_01] <;> ring

def admission_power_Cbridge3_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-74551/73653:ℝ)*δ^0*p^1
theorem admission_power_Cbridge3_02_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 2 = admission_power_Cbridge3_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_02] <;> ring

def admission_power_Cbridge3_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-77645851112471137/30000000000000000:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (52645851112471137/25000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge3_03_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 3 = admission_power_Cbridge3_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_03] <;> ring

def admission_power_Cbridge3_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-148204/73653:ℝ)*δ^1*p^1 + (74551/73653:ℝ)*δ^1*p^2
theorem admission_power_Cbridge3_04_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 4 = admission_power_Cbridge3_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_04] <;> ring

def admission_power_Cbridge3_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-64678993976688457121/100000000000000000000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (1297981153/736530000:ℝ)*δ^1*p^1 + (-8947815344904895203000961/18413250000000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge3_05_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 5 = admission_power_Cbridge3_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_05] <;> ring

def admission_power_Cbridge3_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-6878546553709035856963/9083870000000000000000:ℝ)*δ^0*p^1 + (431098430956852754134210354313235586099/1021935375000000000000000000000000000000:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-138582740685232414343201/22709675000000000000000:ℝ)*δ^1*p^1 + (91419449828767754953967/13625805000000000000000:ℝ)*δ^1*p^2 + (-28614123420177798147784514606509383/11562500000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge3_06_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 6 = admission_power_Cbridge3_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_06] <;> ring

def admission_power_Cbridge3_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-1256686096887426294829/245510000000000000000:ℝ)*δ^0*p^1 + (5788575846285835734487/2209590000000000000000:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (3770058290662278884487/613775000000000000000:ℝ)*δ^1*p^1 + (-5788575846285835734487/1841325000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge3_07_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 7 = admission_power_Cbridge3_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_07] <;> ring

def admission_power_Cbridge3_08 (δ p : ℝ) : ℝ := (-2030392918552083141966653461/5170033162649115537948000000:ℝ)*δ^0*p^0 + (168841011959970689766364819228685000438655157/193876243599341832673050000000000000000000000:ℝ)*δ^0*p^1 + (-13978616558745156611132161207970668791399319347940823773703509/29081436539901274900957500000000000000000000000000000000000000:ℝ)*δ^0*p^2 + (14955475825174871986836653461/12925082906622788844870000000:ℝ)*δ^1*p^0 + (-2947713616339701620750424822585407759033655157/969381217996709163365250000000000000000000000:ℝ)*δ^1*p^1 + (607768978400917579937351939630926378858844843/242345304499177290841312500000000000000000000:ℝ)*δ^1*p^2 + (-3881896356343521702501271745069341927231/6250000000000000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge3_08_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 8 = admission_power_Cbridge3_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_08] <;> ring

def admission_power_Cbridge3_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-1961242841393934038982390513/1227550000000000000000000000:ℝ)*δ^0*p^1 + (473350071013864507838207947922412799520369843/552397500000000000000000000000000000000000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (761443303415586555053863/250000000000000000000000:ℝ)*δ^1*p^1 + (-3171404596743381698090109487/1534437500000000000000000000:ℝ)*δ^1*p^2 + (145000428423465405646346340552587200479630157/460331250000000000000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge3_09_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 9 = admission_power_Cbridge3_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_09] <;> ring

def admission_power_Cbridge3_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-520323353456355410356553/441918000000000000000000:ℝ)*δ^1*p^1 + (76032200384039490039617/110479500000000000000000:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (6149119/2946120:ℝ)*δ^2*p^1 + (-499544071543644589643447/368265000000000000000000:ℝ)*δ^2*p^2 + (157937553337413411/1250000000000000000:ℝ)*δ^2*p^3
theorem admission_power_Cbridge3_10_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 10 = admission_power_Cbridge3_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_10] <;> ring

def admission_power_Cbridge3_11 (δ p : ℝ) : ℝ := (1798816709337721115513/736530000000000000000:ℝ)*δ^0*p^0 + (-372755/73653:ℝ)*δ^0*p^1 + (5788575846285835734487/2209590000000000000000:ℝ)*δ^0*p^2 + (-221857/73653:ℝ)*δ^1*p^0 + (5741299871986836653461/920662500000000000000:ℝ)*δ^1*p^1 + (-1484637679568168096987/460331250000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge3_11_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 11 = admission_power_Cbridge3_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_11] <;> ring

def admission_power_Cbridge3_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge3_12_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 12 = admission_power_Cbridge3_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_12] <;> ring

def admission_power_Cbridge3_13 (δ p : ℝ) : ℝ := (762652368482059486944521539/19387624359934183267305000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge3_13_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 13 = admission_power_Cbridge3_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_13] <;> ring

def admission_power_Cbridge3_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cbridge3_14_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 14 = admission_power_Cbridge3_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_14] <;> ring

def admission_power_Cbridge4_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-805351991031465447/250000000000000000:ℝ)*δ^0*p^1
theorem admission_power_Cbridge4_00_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 0 = admission_power_Cbridge4_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_00] <;> ring

def admission_power_Cbridge4_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-555351991031465447/250000000000000000:ℝ)*δ^0*p^1
theorem admission_power_Cbridge4_01_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 1 = admission_power_Cbridge4_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_01] <;> ring

def admission_power_Cbridge4_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-73001/69003:ℝ)*δ^0*p^1
theorem admission_power_Cbridge4_02_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 2 = admission_power_Cbridge4_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_02] <;> ring

def admission_power_Cbridge4_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-268450663677155149/100000000000000000:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (555351991031465447/250000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge4_03_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 3 = admission_power_Cbridge4_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_03] <;> ring

def admission_power_Cbridge4_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-142004/69003:ℝ)*δ^1*p^1 + (73001/69003:ℝ)*δ^1*p^2
theorem admission_power_Cbridge4_04_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 4 = admission_power_Cbridge4_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_04] <;> ring

def admission_power_Cbridge4_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-670858208529210717351/1000000000000000000000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (1247601503/690030000:ℝ)*δ^1*p^1 + (-86738437360576618611886841/172507500000000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge4_05_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 5 = admission_power_Cbridge4_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_05] <;> ring

def admission_power_Cbridge4_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-195364103848592627083009/255311100000000000000000:ℝ)*δ^0*p^1 + (13790927777280836281990634665338963617663/31913887500000000000000000000000000000000:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-1342819476351438945168281/212759250000000000000000:ℝ)*δ^1*p^1 + (304184627885315473998109/42551850000000000000000:ℝ)*δ^1*p^2 + (-3130776821903354680205100198484368663/1156250000000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge4_06_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 6 = admission_power_Cbridge4_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_06] <;> ring

def admission_power_Cbridge4_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-36774151145714736746447/6900300000000000000000:ℝ)*δ^0*p^1 + (19597166899096003032149/6900300000000000000000:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (36774151145714736746447/5750250000000000000000:ℝ)*δ^1*p^1 + (-19597166899096003032149/5750250000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge4_07_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 7 = admission_power_Cbridge4_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_07] <;> ring

def admission_power_Cbridge4_08 (δ p : ℝ) : ℝ := (-1066737448174003667354749439/2689189714887312999252000000:ℝ)*δ^0*p^0 + (899091945852842940110772984280708104726134233/1008446143082742374719500000000000000000000000:ℝ)*δ^0*p^1 + (-252097928120993001037191815988274506448260177817073035936115717/504223071541371187359750000000000000000000000000000000000000000:ℝ)*δ^0*p^2 + (7789711735392286165484749439/6722974287218282498130000000:ℝ)*δ^1*p^0 + (-157150183841982531190394953193269461230112467/50931623388017291652500000000000000000000000:ℝ)*δ^1*p^1 + (1082887653145488013815770755361092057933788589/420185892951142656133125000000000000000000000:ℝ)*δ^1*p^2 + (-402634877986353934015686470699971645090191/625000000000000000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge4_08_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 8 = admission_power_Cbridge4_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_08] <;> ring

def admission_power_Cbridge4_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-56476806065371588408704585659/34501500000000000000000000000:ℝ)*δ^0*p^1 + (15528545229030659129943879267547336043918408191/17250750000000000000000000000000000000000000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (7739397305859097026809553/2500000000000000000000000:ℝ)*δ^1*p^1 + (-30471893057784251152470971447/14375625000000000000000000000:ℝ)*δ^1*p^2 + (4500418253798113548467752870702663956081591809/14375625000000000000000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge4_09_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 9 = admission_power_Cbridge4_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_09] <;> ring

def admission_power_Cbridge4_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-4978737007197106323537793/4140180000000000000000000:ℝ)*δ^1*p^1 + (745797389688567369281977/1035045000000000000000000:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (5887169/2760120:ℝ)*δ^2*p^1 + (-4891724742802893676462207/3450150000000000000000000:ℝ)*δ^2*p^2 + (1666055973094396341/12500000000000000000:ℝ)*δ^2*p^3
theorem admission_power_Cbridge4_10_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 10 = admission_power_Cbridge4_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_10] <;> ring

def admission_power_Cbridge4_11 (δ p : ℝ) : ℝ := (16977098854285263253553/6900300000000000000000:ℝ)*δ^0*p^0 + (-365005/69003:ℝ)*δ^0*p^1 + (19597166899096003032149/6900300000000000000000:ℝ)*δ^0*p^2 + (-211007/69003:ℝ)*δ^1*p^0 + (56571203437144210239341/8625375000000000000000:ℝ)*δ^1*p^1 + (-15152988533608054833947/4312687500000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge4_11_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 11 = admission_power_Cbridge4_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_11] <;> ring

def admission_power_Cbridge4_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge4_12_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 12 = admission_power_Cbridge4_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_12] <;> ring

def admission_power_Cbridge4_13 (δ p : ℝ) : ℝ := (105145140358981206076064519/3141061757142968052405000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge4_13_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 13 = admission_power_Cbridge4_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_13] <;> ring

def admission_power_Cbridge4_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cbridge4_14_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 14 = admission_power_Cbridge4_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_14] <;> ring

def admission_power_Cbridge5_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-197595118769160153/62500000000000000:ℝ)*δ^0*p^1
theorem admission_power_Cbridge5_00_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 0 = admission_power_Cbridge5_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_00] <;> ring

def admission_power_Cbridge5_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-135095118769160153/62500000000000000:ℝ)*δ^0*p^1
theorem admission_power_Cbridge5_01_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 1 = admission_power_Cbridge5_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_01] <;> ring

def admission_power_Cbridge5_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-1537/1486:ℝ)*δ^0*p^1
theorem admission_power_Cbridge5_02_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 2 = admission_power_Cbridge5_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_02] <;> ring

def admission_power_Cbridge5_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-65865039589720051/25000000000000000:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (135095118769160153/62500000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge5_03_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 3 = admission_power_Cbridge5_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_03] <;> ring

def admission_power_Cbridge5_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-3023/1486:ℝ)*δ^1*p^1 + (1537/1486:ℝ)*δ^1*p^2
theorem admission_power_Cbridge5_04_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 4 = admission_power_Cbridge5_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_04] <;> ring

def admission_power_Cbridge5_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-164596733934710407449/250000000000000000000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (13258243/7430000:ℝ)*δ^1*p^1 + (-229473692559530501796179/464375000000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge5_05_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 5 = admission_power_Cbridge5_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_05] <;> ring

def admission_power_Cbridge5_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-522916797512613900971/687275000000000000000:ℝ)*δ^0*p^1 + (9162754895060332737462094352158903403/21477343750000000000000000000000000000:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-10658546734646177854617/1718187500000000000000:ℝ)*δ^1*p^1 + (4755872442555560006601/687275000000000000000:ℝ)*δ^1*p^2 + (-186858952268281981904814142740883863/72265625000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge5_06_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 6 = admission_power_Cbridge5_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_06] <;> ring

def admission_power_Cbridge5_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-96968974415161997893/18575000000000000000:ℝ)*δ^0*p^1 + (101234565849399718387/37150000000000000000:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (290906923245485993679/46437500000000000000:ℝ)*δ^1*p^1 + (-303703697548199155161/92875000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge5_07_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 7 = admission_power_Cbridge5_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_07] <;> ring

def admission_power_Cbridge5_08 (δ p : ℝ) : ℝ := (-158584209797159799667981037/401502692981943974716000000:ℝ)*δ^0*p^0 + (11057456600481976055375405734444791351672887/12546959155685749209875000000000000000000000:ℝ)*δ^0*p^1 + (-768629069008350591850374382659462732438817367177082251957237/1568369894460718651234375000000000000000000000000000000000000:ℝ)*δ^0*p^2 + (1162340942252019736457981037/1003756732454859936790000000:ℝ)*δ^1*p^0 + (-192115710622716792134324961887772579496672887/62734795778428746049375000000000000000000000:ℝ)*δ^1*p^1 + (39854208411055738056504733451594102720827113/15683698944607186512343750000000000000000000:ℝ)*δ^1*p^2 + (-24696868513634520152070960026551037016591/39062500000000000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge5_08_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 8 = admission_power_Cbridge5_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_08] <;> ring

def admission_power_Cbridge5_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-150121955397743687710681321/92875000000000000000000000:ℝ)*δ^0*p^1 + (10186313401767142300844435714516843579867371/11609375000000000000000000000000000000000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (1918661378581498892564847/625000000000000000000000:ℝ)*δ^1*p^1 + (-242932086437036307021818679/116093750000000000000000000:ℝ)*δ^1*p^2 + (9126486511795677920946775418949469260397887/29023437500000000000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge5_09_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 9 = admission_power_Cbridge5_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_09] <;> ring

def admission_power_Cbridge5_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-13258044322371878170667/11145000000000000000000:ℝ)*δ^1*p^1 + (1961122980263542018963/2786250000000000000000:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (62689/29720:ℝ)*δ^2*p^1 + (-12873643177628121829333/9287500000000000000000:ℝ)*δ^2*p^2 + (405285356307480459/3125000000000000000:ℝ)*δ^2*p^3
theorem admission_power_Cbridge5_10_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 10 = admission_power_Cbridge5_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_10] <;> ring

def admission_power_Cbridge5_11 (δ p : ℝ) : ℝ := (45531025584838002107/18575000000000000000:ℝ)*δ^0*p^0 + (-7685/1486:ℝ)*δ^0*p^1 + (101234565849399718387/37150000000000000000:ℝ)*δ^0*p^2 + (-4509/1486:ℝ)*δ^1*p^0 + (148406923245485993679/23218750000000000000:ℝ)*δ^1*p^1 + (-312330044039171142519/92875000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge5_11_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 11 = admission_power_Cbridge5_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_11] <;> ring

def admission_power_Cbridge5_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge5_12_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 12 = admission_power_Cbridge5_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_12] <;> ring

def admission_power_Cbridge5_13 (δ p : ℝ) : ℝ := (18325019962599831852331321/501878366227429968395000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge5_13_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 13 = admission_power_Cbridge5_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_13] <;> ring

def admission_power_Cbridge5_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cbridge5_14_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 14 = admission_power_Cbridge5_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_14] <;> ring

def admission_power_Cbridge6_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-410743304480045413/125000000000000000:ℝ)*δ^0*p^1
theorem admission_power_Cbridge6_00_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 0 = admission_power_Cbridge6_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_00] <;> ring

def admission_power_Cbridge6_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-285743304480045413/125000000000000000:ℝ)*δ^0*p^1
theorem admission_power_Cbridge6_01_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 1 = admission_power_Cbridge6_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_01] <;> ring

def admission_power_Cbridge6_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-36113/33339:ℝ)*δ^0*p^1
theorem admission_power_Cbridge6_02_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 2 = admission_power_Cbridge6_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_02] <;> ring

def admission_power_Cbridge6_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-410743304480045413/150000000000000000:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (285743304480045413/125000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge6_03_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 3 = admission_power_Cbridge6_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_03] <;> ring

def admission_power_Cbridge6_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-69452/33339:ℝ)*δ^1*p^1 + (36113/33339:ℝ)*δ^1*p^2
theorem admission_power_Cbridge6_04_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 4 = admission_power_Cbridge6_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_04] <;> ring

def admission_power_Cbridge6_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-342149172631877829029/500000000000000000000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (611205839/333390000:ℝ)*δ^1*p^1 + (-21334786325877475174006507/41673750000000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge6_05_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 5 = admission_power_Cbridge6_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_05] <;> ring

def admission_power_Cbridge6_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-47513121106276999709443/61677150000000000000000:ℝ)*δ^0*p^1 + (5070660882294261919850658410413645609237/11564465625000000000000000000000000000000:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-330351452881795127517387/51397625000000000000000:ℝ)*δ^1*p^1 + (228129765378964933066429/30838575000000000000000:ℝ)*δ^1*p^2 + (-821570043806271323317408917796383983/289062500000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge6_06_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 6 = admission_power_Cbridge6_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_06] <;> ring

def admission_power_Cbridge6_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-9078715342686744674669/1666950000000000000000:ℝ)*δ^0*p^1 + (14833172954687879999669/5000850000000000000000:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (9078715342686744674669/1389125000000000000000:ℝ)*δ^1*p^1 + (-14833172954687879999669/4167375000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge6_07_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 7 = admission_power_Cbridge6_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_07] <;> ring

def admission_power_Cbridge6_08 (δ p : ℝ) : ℝ := (-5052697909278581313544024007/12701861370746978698676000000:ℝ)*δ^0*p^0 + (2147462504701642782864455685569976342607229891/2381599007015058506001750000000000000000000000:ℝ)*δ^0*p^1 + (-911670712429467327638401016776950233865062919782543767116039983/1786199255261293879501312500000000000000000000000000000000000000:ℝ)*δ^0*p^2 + (36807351336146028060234024007/31754653426867446746690000000:ℝ)*δ^1*p^0 + (-37039601471137751432972046899710130059092229891/11907995035075292530008750000000000000000000000:ℝ)*δ^1*p^1 + (7788681989194543139117034173468850515635270109/2976998758768823132502187500000000000000000000:ℝ)*δ^1*p^2 + (-102675337484424116921704133227297457659431/156250000000000000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge6_08_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 8 = admission_power_Cbridge6_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_08] <;> ring

def admission_power_Cbridge6_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-13831969289155760720251250993/8334750000000000000000000000:ℝ)*δ^0*p^1 + (5785030281378698943636487336045443835186345109/6251062500000000000000000000000000000000000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (3904589756132891931179587/1250000000000000000000000:ℝ)*δ^1*p^1 + (-7460912866093283655473749669/3472812500000000000000000000:ℝ)*δ^1*p^2 + (1618162968944986568063044038079556164813654891/5209218750000000000000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge6_09_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 9 = admission_power_Cbridge6_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_09] <;> ring

def admission_power_Cbridge6_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-1216542682242373681351811/1000170000000000000000000:ℝ)*δ^1*p^1 + (184624936915819297927979/250042500000000000000000:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (2878097/1333560:ℝ)*δ^2*p^1 + (-1210046192757626318648189/833475000000000000000000:ℝ)*δ^2*p^2 + (857229913440136239/6250000000000000000:ℝ)*δ^2*p^3
theorem admission_power_Cbridge6_10_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 10 = admission_power_Cbridge6_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_10] <;> ring

def admission_power_Cbridge6_11 (δ p : ℝ) : ℝ := (1372303219104418441777/555650000000000000000:ℝ)*δ^0*p^0 + (-180565/33339:ℝ)*δ^0*p^1 + (14833172954687879999669/5000850000000000000000:ℝ)*δ^0*p^2 + (-102791/33339:ℝ)*δ^1*p^0 + (14040521028060234024007/2083687500000000000000:ℝ)*δ^1*p^1 + (-1277609915229009501973/347281250000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge6_11_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 11 = admission_power_Cbridge6_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_11] <;> ring

def admission_power_Cbridge6_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge6_12_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 12 = admission_power_Cbridge6_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_12] <;> ring

def admission_power_Cbridge6_13 (δ p : ℝ) : ℝ := (84655548087850575643276529/2801881184723598242355000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge6_13_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 13 = admission_power_Cbridge6_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_13] <;> ring

def admission_power_Cbridge6_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cbridge6_14_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 14 = admission_power_Cbridge6_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_14] <;> ring

end
end Qrh.JointDetector.RayCurveReturn
