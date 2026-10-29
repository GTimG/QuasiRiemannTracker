/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/restart_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
A finite count-source bank and physical source remain explicit; no missing estimate is asserted. -/
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Formulas
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unnecessarySeqFocus false
namespace Qrh.JointDetector.BoundarySeedReturn
open QRH.Record1252270103Return
noncomputable section

def admission_power_Cnew_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-104155411868628792253421/31249981773642476253421:ℝ)*δ^0*p^1
theorem admission_power_Cnew_00_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 0 = admission_power_Cnew_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_00] <;> ring

def admission_power_Cnew_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-72905430094986316000000/31249981773642476253421:ℝ)*δ^0*p^1
theorem admission_power_Cnew_01_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 1 = admission_power_Cnew_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_01] <;> ring

def admission_power_Cnew_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-1721098925400634718392023912703/1562499088682123812671050000000:ℝ)*δ^0*p^1
theorem admission_power_Cnew_02_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 2 = admission_power_Cnew_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_02] <;> ring

def admission_power_Cnew_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-520777059343143961267105/187499890641854857520526:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (72905430094986316000000/31249981773642476253421:ℝ)*δ^1*p^2
theorem admission_power_Cnew_03_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 3 = admission_power_Cnew_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_03] <;> ring

def admission_power_Cnew_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-3283598014082758531063073912703/1562499088682123812671050000000:ℝ)*δ^1*p^1 + (1721098925400634718392023912703/1562499088682123812671050000000:ℝ)*δ^1*p^2
theorem admission_power_Cnew_04_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 4 = admission_power_Cnew_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_04] <;> ring

def admission_power_Cnew_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-86761458086567783947099693/124999927094569905013684000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (2893129491821095790276578517703/1562499088682123812671050000000:ℝ)*δ^1*p^1 + (-810145576363780699972023912703/1562499088682123812671050000000:ℝ)*δ^1*p^2
theorem admission_power_Cnew_05_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 5 = admission_power_Cnew_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_05] <;> ring

def admission_power_Cnew_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-53723237171807208054024695689967/69374959537486297282594620000000:ℝ)*δ^0*p^1 + (961159479721561039232368523830144508089361108687042369/2167966221093631064403218972430108464731531195020000000:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-376445666093042764965132904310033/57812466281238581068828850000000:ℝ)*δ^1*p^1 + (13695499760612205989660643067315822316481723428712957631/1806638517578025887002682477025090387276275995850000000:ℝ)*δ^1*p^2 + (-106308931386039542642720726931965188618504000000/36132770351560517740053649540501807745525519917:ℝ)*δ^1*p^3
theorem admission_power_Cnew_06_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 6 = admission_power_Cnew_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_06] <;> ring

def admission_power_Cnew_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-10371067369633343767847121738109/1874998906418548575205260000000:ℝ)*δ^0*p^1 + (179261767441757529674404571993487250628945436757106963/58593681651179217956843756011624553100852194460000000:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (10371067369633343767847121738109/1562499088682123812671050000000:ℝ)*δ^1*p^1 + (-179261767441757529674404571993487250628945436757106963/48828068042649348297369796676353794250710162050000000:ℝ)*δ^1*p^2
theorem admission_power_Cnew_07_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 7 = admission_power_Cnew_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_07] <;> ring

def admission_power_Cnew_08 (δ p : ℝ) : ℝ := (-571246604737446886195203303739/1458108601899726320000000000000:ℝ)*δ^0*p^0 + (61119616781527123517291984329882101860245911502841119/68348800850036641237976750893798295611080000000000000:ℝ)*δ^0*p^1 + (-2178264905238642033456485879316725026333249089640957499150608984627428406033/4271797561627928853129726444324208413522532077746244212271009360000000000000:ℝ)*δ^0*p^2 + (4216518109486762686195203303739/3645271504749315800000000000000:ℝ)*δ^1*p^0 + (-178184475147765187151736152045340886309801227853719627/56957334041697201031647292411498579675900000000000000:ℝ)*δ^1*p^1 + (302309000736724384450117555972698292063796991011719627/113914668083394402063294584822997159351800000000000000:ℝ)*δ^1*p^2 + (-3287070732671559647497454724210298717944834684882659/4882806804264934829736979667635379425071016205000000:ℝ)*δ^1*p^3
theorem admission_power_Cnew_08_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 8 = admission_power_Cnew_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_08] <;> ring

def admission_power_Cnew_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-3143094195658885968170485409261/1874998906418548575205260000000:ℝ)*δ^0*p^1 + (2305572633622640166613186974522996905404267204104243/2441403402132467414868489833817689712535508102500000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (491251542811308068504587428421/156249908868212381267105000000:ℝ)*δ^1*p^1 + (-1694484212460259826402796940107/781249544341061906335525000000:ℝ)*δ^1*p^2 + (15052473893296945427895821543479211768287871937106963/48828068042649348297369796676353794250710162050000000:ℝ)*δ^1*p^3
theorem admission_power_Cnew_09_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 9 = admission_power_Cnew_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_09] <;> ring

def admission_power_Cnew_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-766433049335577299023897720901/624999635472849525068420000000:ℝ)*δ^1*p^1 + (1408632689794748341631760912703/1874998906418548575205260000000:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (3400785445733917817013402662703/1562499088682123812671050000000:ℝ)*δ^2*p^1 + (-2306960523862719780152286912703/1562499088682123812671050000000:ℝ)*δ^2*p^2 + (4374325805699178960000/31249981773642476253421:ℝ)*δ^2*p^3
theorem admission_power_Cnew_10_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 10 = admission_power_Cnew_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_10] <;> ring

def admission_power_Cnew_11 (δ p : ℝ) : ℝ := (4643023448816835980518171738109/1874998906418548575205260000000:ℝ)*δ^0*p^0 + (-1721098925400634718392023912703/312499817736424762534210000000:ℝ)*δ^0*p^1 + (179261767441757529674404571993487250628945436757106963/58593681651179217956843756011624553100852194460000000:ℝ)*δ^0*p^2 + (-4846097102764882343734123912703/1562499088682123812671050000000:ℝ)*δ^1*p^0 + (5366370430149950518392023912703/781249544341061906335525000000:ℝ)*δ^1*p^1 + (-185607815426340958014219068604810853805981707538893037/48828068042649348297369796676353794250710162050000000:ℝ)*δ^1*p^2
theorem admission_power_Cnew_11_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 11 = admission_power_Cnew_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_11] <;> ring

def admission_power_Cnew_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cnew_12_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 12 = admission_power_Cnew_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_12] <;> ring

def admission_power_Cnew_13 (δ p : ℝ) : ℝ := (50768377248659994775418378493/1822635752374657900000000000000:ℝ)*δ^0*p^0
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

def admission_power_Pnew_09 (δ p : ℝ) : ℝ := (72993245719108077770888471719/107753345489513122037708000000:ℝ)*δ^0*p^0 + (-7878985137169249785266539/8081500911713484152828100:ℝ)*δ^0*p^1 + (26907351085295768182197009809/107753345489513122037708000000:ℝ)*δ^0*p^2 + (-342376609442890882865158471719/269383363723782805094270000000:ℝ)*δ^1*p^0 + (289949509104710580019685509427/134691681861891402547135000000:ℝ)*δ^1*p^1 + (-51093655383609629339587178573/53876672744756561018854000000:ℝ)*δ^1*p^2 + (619999/5000000:ℝ)*δ^1*p^3
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

def admission_power_Pnew_13 (δ p : ℝ) : ℝ := (7031348831827564418447715573/134691681861891402547135000000:ℝ)*δ^0*p^0
theorem admission_power_Pnew_13_expanded (δ p : ℝ) : admissionGuard .Pnew δ p 13 = admission_power_Pnew_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pnew_13] <;> ring

def admission_power_Pnew_14 (δ p : ℝ) : ℝ := (479997/2000000:ℝ)*δ^0*p^0 + (-159999/1000000:ℝ)*δ^0*p^1 + (53333/2000000:ℝ)*δ^0*p^2 + (-479997/5000000:ℝ)*δ^1*p^0 + (-159999/2500000:ℝ)*δ^1*p^1 + (159999/5000000:ℝ)*δ^1*p^2
theorem admission_power_Pnew_14_expanded (δ p : ℝ) : admissionGuard .Pnew δ p 14 = admission_power_Pnew_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pnew_14] <;> ring

def admission_power_Cphys_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-141566884230346339/50000000000000000:ℝ)*δ^0*p^1
theorem admission_power_Cphys_00_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 0 = admission_power_Cphys_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_00] <;> ring

def admission_power_Cphys_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-91566884230346339/50000000000000000:ℝ)*δ^0*p^1
theorem admission_power_Cphys_01_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 1 = admission_power_Cphys_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_01] <;> ring

def admission_power_Cphys_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-264731/294193:ℝ)*δ^0*p^1
theorem admission_power_Cphys_02_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 2 = admission_power_Cphys_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_02] <;> ring

def admission_power_Cphys_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-141566884230346339/60000000000000000:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (91566884230346339/50000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cphys_03_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 3 = admission_power_Cphys_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_03] <;> ring

def admission_power_Cphys_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-558924/294193:ℝ)*δ^1*p^1 + (264731/294193:ℝ)*δ^1*p^2
theorem admission_power_Cphys_04_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 4 = admission_power_Cphys_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_04] <;> ring

def admission_power_Cphys_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-117925214563878500387/200000000000000000000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (4854051693/2941930000:ℝ)*δ^1*p^1 + (-65046597405426677006941927/147096500000000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cphys_05_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 5 = admission_power_Cphys_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_05] <;> ring

def admission_power_Cphys_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-488198309501779183943069/653108460000000000000000:ℝ)*δ^0*p^1 + (6605472539443595780603859577506951064271/16327711500000000000000000000000000000000:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-3044966036564700451716821/544257050000000000000000:ℝ)*δ^1*p^1 + (620227244306596985062169/108851410000000000000000:ℝ)*δ^1*p^2 + (-90739869494196762063943515234920447/46250000000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cphys_06_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 6 = admission_power_Cphys_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_06] <;> ring

def admission_power_Cphys_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-81357636372378280509427/17651580000000000000000:ℝ)*δ^0*p^1 + (37477142829183816669809/17651580000000000000000:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (81357636372378280509427/14709650000000000000000:ℝ)*δ^1*p^1 + (-37477142829183816669809/14709650000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cphys_07_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 7 = admission_power_Cphys_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_07] <;> ring

def admission_power_Cphys_08 (δ p : ℝ) : ℝ := (-39464231139126312040571528281/107753345489513122037708000000:ℝ)*δ^0*p^0 + (6474265351957481155613141744624139599928313259/8081500911713484152828100000000000000000000000:ℝ)*δ^0*p^1 + (-347391093439383350430554559294842967034609312695303752996936267/808150091171348415282810000000000000000000000000000000000000000:ℝ)*δ^0*p^2 + (308847594862909117134841528281/269383363723782805094270000000:ℝ)*δ^1*p^0 + (-39539322051014752798597371924040653929564437753/13469168186189140254713500000000000000000000000:ℝ)*δ^1*p^1 + (7910560877604017331978422400245757164818062247/3367292046547285063678375000000000000000000000:ℝ)*δ^1*p^2 + (-14155245634665408231010090865212109297079/25000000000000000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cphys_08_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 8 = admission_power_Cphys_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_08] <;> ring

def admission_power_Cphys_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-133594316375757669927838796719/88257900000000000000000000000:ℝ)*δ^0*p^1 + (2253839147148763977752791577168237421239095749/2941930000000000000000000000000000000000000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (1463526782729363685828661/500000000000000000000000:ℝ)*δ^1*p^1 + (-70981007673658510448576234427/36774125000000000000000000000:ℝ)*δ^1*p^2 + (2244857529181192607991188547145287736282712753/7354825000000000000000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cphys_09_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 9 = admission_power_Cphys_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_09] <;> ring

def admission_power_Cphys_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-1311732322648595475415157/1176772000000000000000000:ℝ)*δ^1*p^1 + (536883540882865158471719/882579000000000000000000:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (23239539/11767720:ℝ)*δ^2*p^1 + (-3551160882054213573754529/2941930000000000000000000:ℝ)*δ^2*p^2 + (274700652691039017/2500000000000000000:ℝ)*δ^2*p^3
theorem admission_power_Cphys_10_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 10 = admission_power_Cphys_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_10] <;> ring

def admission_power_Cphys_11 (δ p : ℝ) : ℝ := (42190613627621719490573/17651580000000000000000:ℝ)*δ^0*p^0 + (-1323655/294193:ℝ)*δ^0*p^1 + (37477142829183816669809/17651580000000000000000:ℝ)*δ^0*p^2 + (-853117/294193:ℝ)*δ^1*p^0 + (40174886372378280509427/7354825000000000000000:ℝ)*δ^1*p^1 + (-9485594800390524294809/3677412500000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cphys_11_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 11 = admission_power_Cphys_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_11] <;> ring

def admission_power_Cphys_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cphys_12_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 12 = admission_power_Cphys_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_12] <;> ring

def admission_power_Cphys_13 (δ p : ℝ) : ℝ := (7031348831827564418447715573/134691681861891402547135000000:ℝ)*δ^0*p^0
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

def admission_power_Pwide_09 (δ p : ℝ) : ℝ := (48281033719108077770888471719/107753345489513122037708000000:ℝ)*δ^0*p^0 + (-1102392881905872400774121/1616300182342696830565620:ℝ)*δ^0*p^1 + (57399180887355467461311909427/323260036468539366113124000000:ℝ)*δ^0*p^2 + (-317664397442890882865158471719/269383363723782805094270000000:ℝ)*δ^1*p^0 + (298186913104710580019685509427/134691681861891402547135000000:ℝ)*δ^1*p^1 + (-61792417204728731590754650573/53876672744756561018854000000:ℝ)*δ^1*p^2 + (899999/5000000:ℝ)*δ^1*p^3
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

def admission_power_Pwide_13 (δ p : ℝ) : ℝ := (7031348831827564418447715573/134691681861891402547135000000:ℝ)*δ^0*p^0
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

def admission_power_Pcount_09 (δ p : ℝ) : ℝ := (571244417574544036605723303739/1458108601899726320000000000000:ℝ)*δ^0*p^0 + (-1289473355736753153474463303739/2187162902849589480000000000000:ℝ)*δ^0*p^1 + (669234097966320756781067767913/4374325805699178960000000000000:ℝ)*δ^0*p^2 + (-4216515922323859836605723303739/3645271504749315800000000000000:ℝ)*δ^1*p^0 + (4062401949682687087798092232087/1822635752374657900000000000000:ℝ)*δ^1*p^1 + (-4448579825732926754060612232087/3645271504749315800000000000000:ℝ)*δ^1*p^2 + (1009899/5000000:ℝ)*δ^1*p^3
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

def admission_power_Pcount_13 (δ p : ℝ) : ℝ := (50768377248659994775418378493/1822635752374657900000000000000:ℝ)*δ^0*p^0
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

def admission_power_Pcountmid_09 (δ p : ℝ) : ℝ := (575931914840590408043736453739/1458108601899726320000000000000:ℝ)*δ^0*p^0 + (-1299628760259923498612476453739/2187162902849589480000000000000:ℝ)*δ^0*p^1 + (224813956186584065464579605971/1458108601899726320000000000000:ℝ)*δ^0*p^2 + (-4221203419589906208043736453739/3645271504749315800000000000000:ℝ)*δ^1*p^0 + (4060839450594004963985421182087/1822635752374657900000000000000:ℝ)*δ^1*p^1 + (-4436081512129996682847941182087/3645271504749315800000000000000:ℝ)*δ^1*p^2 + (1004899/5000000:ℝ)*δ^1*p^3
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

def admission_power_Pcountmid_13 (δ p : ℝ) : ℝ := (50768377248659994775418378493/1822635752374657900000000000000:ℝ)*δ^0*p^0
theorem admission_power_Pcountmid_13_expanded (δ p : ℝ) : admissionGuard .Pcountmid δ p 13 = admission_power_Pcountmid_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pcountmid_13] <;> ring

def admission_power_Pcountmid_14 (δ p : ℝ) : ℝ := (1057347/2000000:ℝ)*δ^0*p^0 + (-352449/1000000:ℝ)*δ^0*p^1 + (117483/2000000:ℝ)*δ^0*p^2 + (-1057347/5000000:ℝ)*δ^1*p^0 + (-352449/2500000:ℝ)*δ^1*p^1 + (352449/5000000:ℝ)*δ^1*p^2
theorem admission_power_Pcountmid_14_expanded (δ p : ℝ) : admissionGuard .Pcountmid δ p 14 = admission_power_Pcountmid_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pcountmid_14] <;> ring

def admission_power_Cbridge0_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-88061366882099949/31250000000000000:ℝ)*δ^0*p^1
theorem admission_power_Cbridge0_00_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 0 = admission_power_Cbridge0_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_00] <;> ring

def admission_power_Cbridge0_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-56811366882099949/31250000000000000:ℝ)*δ^0*p^1
theorem admission_power_Cbridge0_01_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 1 = admission_power_Cbridge0_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_01] <;> ring

def admission_power_Cbridge0_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-1913133368143585465357/2139492268956934700071:ℝ)*δ^0*p^1
theorem admission_power_Cbridge0_02_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 2 = admission_power_Cbridge0_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_02] <;> ring

def admission_power_Cbridge0_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-29353788960699983/12500000000000000:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (56811366882099949/31250000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge0_03_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 3 = admission_power_Cbridge0_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_03] <;> ring

def admission_power_Cbridge0_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-4052625637100520165428/2139492268956934700071:ℝ)*δ^1*p^1 + (1913133368143585465357/2139492268956934700071:ℝ)*δ^1*p^2
theorem admission_power_Cbridge0_04_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 4 = admission_power_Cbridge0_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_04] <;> ring

def admission_power_Cbridge0_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-73355118612789257517/125000000000000000000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (35179665190881821838802571/21394922689569347000710000:ℝ)*δ^1*p^1 + (-294107024442281394759278667401716468448879/668591334049042093772187500000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge0_05_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 5 = admission_power_Cbridge0_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_05] <;> ring

def admission_power_Cbridge0_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-739643156746497656051425462801030543271/989515174392582298782837500000000000000:ℝ)*δ^0*p^1 + (6246957918405512968440033255034443608662250592968930899/15461174599884098418481835937500000000000000000000000000:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-13777617087428799859259036849644066116717/2473787935981455746957093750000000000000:ℝ)*δ^1*p^1 + (2795238583900726220084444271933622393713/494757587196291149391418750000000000000:ℝ)*δ^1*p^2 + (-35020206354547304007536916180618207/18066406250000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge0_06_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 6 = admission_power_Cbridge0_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_06] <;> ring

def admission_power_Cbridge0_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-122587622300498074523692563038319798793/26743653361961683750887500000000000000:ℝ)*δ^0*p^1 + (56157713142159955562246020443516988931/26743653361961683750887500000000000000:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (367762866901494223571077689114959396379/66859133404904209377218750000000000000:ℝ)*δ^1*p^1 + (-168473139426479866686738061330550966793/66859133404904209377218750000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge0_07_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 7 = admission_power_Cbridge0_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_07] <;> ring

def admission_power_Cbridge0_08 (δ p : ℝ) : ℝ := (-3611710431656763687346656190479048593636513/9922243284337051168705321560404848684000000:ℝ)*δ^0*p^0 + (123505934901923746405971021127448491168979342219481412279279/155035051317766424511020649381325760687500000000000000000000:ℝ)*δ^0*p^1 + (-4138722328130105331182275256108189575043026148500677276188458306958421552257/9689690707360401531938790586332860042968750000000000000000000000000000000000:ℝ)*δ^0*p^2 + (28417318642499391609109960091491170303636513/24805608210842627921763303901012121710000000:ℝ)*δ^1*p^0 + (-2271640536449282848058164721457161060314946555764946877279279/775175256588832122555103246906628803437500000000000000000000:ℝ)*δ^1*p^1 + (453829386672087111425985648321788892239235037990751320220721/193793814147208030638775811726657200859375000000000000000000:ℝ)*δ^1*p^2 + (-5503274539866181478385650709011974197399/9765625000000000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge0_08_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 8 = admission_power_Cbridge0_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_08] <;> ring

def admission_power_Cbridge0_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-201920304075389087136890902621661280414778621/133718266809808418754437500000000000000000000:ℝ)*δ^0*p^1 + (6369896606798451031087035672120707504214295898995004738463443/8357391675613026172152343750000000000000000000000000000000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (912896667453715397325051/312500000000000000000000:ℝ)*δ^1*p^1 + (-321423015513664074661536792372575716567721379/167147833512260523443046875000000000000000000:ℝ)*δ^1*p^2 + (6354635666413380024093696665302261061725194209264985784609671/20893479189032565430380859375000000000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge0_09_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 9 = admission_power_Cbridge0_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_09] <;> ring

def admission_power_Cbridge0_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-17835002861074806169110933643896096297767/16046192017177010250532500000000000000000:ℝ)*δ^1*p^1 + (2424051046810253031038735682655121810863/4011548004294252562633125000000000000000:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (168523502290891610717333/85579690758277388002840:ℝ)*δ^2*p^1 + (-16041175118050739345057160106103903702233/13371826680980841875443750000000000000000:ℝ)*δ^2*p^2 + (170434100646299847/1562500000000000000:ℝ)*δ^2*p^3
theorem admission_power_Cbridge0_10_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 10 = admission_power_Cbridge0_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_10] <;> ring

def admission_power_Cbridge0_11 (δ p : ℝ) : ℝ := (63842346613380226438338686961680201207/26743653361961683750887500000000000000:ℝ)*δ^0*p^0 + (-9565666840717927326785/2139492268956934700071:ℝ)*δ^0*p^1 + (56157713142159955562246020443516988931/26743653361961683750887500000000000000:ℝ)*δ^0*p^2 + (-6192117906057454865499/2139492268956934700071:ℝ)*δ^1*p^0 + (181332897987615922609046439114959396379/33429566702452104688609375000000000000:ℝ)*δ^1*p^1 + (-42612446037658662979641437611377590793/16714783351226052344304687500000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge0_11_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 11 = admission_power_Cbridge0_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_11] <;> ring

def admission_power_Cbridge0_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge0_12_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 12 = admission_power_Cbridge0_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_12] <;> ring

def admission_power_Cbridge0_13 (δ p : ℝ) : ℝ := (32045590227898497128466861000111495701428621/607737401165644384083200945574796981895000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge0_13_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 13 = admission_power_Cbridge0_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_13] <;> ring

def admission_power_Cbridge0_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cbridge0_14_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 14 = admission_power_Cbridge0_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_14] <;> ring

def admission_power_Cbridge1_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-181548106471923757/62500000000000000:ℝ)*δ^0*p^1
theorem admission_power_Cbridge1_00_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 0 = admission_power_Cbridge1_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_00] <;> ring

def admission_power_Cbridge1_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-119048106471923757/62500000000000000:ℝ)*δ^0*p^1
theorem admission_power_Cbridge1_01_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 1 = admission_power_Cbridge1_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_01] <;> ring

def admission_power_Cbridge1_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-194767/209301:ℝ)*δ^0*p^1
theorem admission_power_Cbridge1_02_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 2 = admission_power_Cbridge1_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_02] <;> ring

def admission_power_Cbridge1_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-181548106471923757/75000000000000000:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (119048106471923757/62500000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge1_03_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 3 = admission_power_Cbridge1_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_03] <;> ring

def admission_power_Cbridge1_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-404068/209301:ℝ)*δ^1*p^1 + (194767/209301:ℝ)*δ^1*p^2
theorem admission_power_Cbridge1_04_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 4 = admission_power_Cbridge1_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_04] <;> ring

def admission_power_Cbridge1_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-151229572691112489581/250000000000000000000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (3517636801/2093010000:ℝ)*δ^1*p^1 + (-59462072556032394454621357/130813125000000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge1_05_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 5 = admission_power_Cbridge1_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_05] <;> ring

def admission_power_Cbridge1_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-48302149826218374489031/64534475000000000000000:ℝ)*δ^0*p^1 + (7404994674556254354146005402014793255243/18150321093750000000000000000000000000000:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-924856597617214209356237/161336187500000000000000:ℝ)*δ^1*p^1 + (577357709999824370164379/96801712500000000000000:ℝ)*δ^1*p^2 + (-151290708163320109508043614946965343/72265625000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge1_06_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 6 = admission_power_Cbridge1_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_06] <;> ring

def admission_power_Cbridge1_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-8279668081408901584873/1744175000000000000000:ℝ)*δ^0*p^1 + (35359580053217174379619/15697575000000000000000:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (24839004244226704754619/4360437500000000000000:ℝ)*δ^1*p^1 + (-35359580053217174379619/13081312500000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge1_07_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 7 = admission_power_Cbridge1_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_07] <;> ring

def admission_power_Cbridge1_08 (δ p : ℝ) : ℝ := (-12513124899745685133924263857/33222516976906819018476000000:ℝ)*δ^0*p^0 + (2565264645451110138637657369340999512769750749/3114610966585014282982125000000000000000000000:ℝ)*δ^0*p^1 + (-519008847963234888306195675956184597266335160191296050076643993/1167979112469380356118296875000000000000000000000000000000000000:ℝ)*δ^0*p^2 + (95569417342012732680114263857/83056292442267047546190000000:ℝ)*δ^1*p^0 + (-46150345502215271199513101741871307430684750749/15573054832925071414910625000000000000000000000:ℝ)*δ^1*p^1 + (9307142847263903802575195671814779446187749251/3893263708231267853727656250000000000000000000:ℝ)*δ^1*p^2 + (-22691199651187952541837945279483579004951/39062500000000000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge1_08_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 8 = admission_power_Cbridge1_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_08] <;> ring

def admission_power_Cbridge1_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-13382385595669245912657420381/8720875000000000000000000000:ℝ)*δ^0*p^1 + (7736273697589142699687885018141404116304674251/9810984375000000000000000000000000000000000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (1849258066442963777101243/625000000000000000000000:ℝ)*δ^1*p^1 + (-21460950478149883049525079619/10901093750000000000000000000:ℝ)*δ^1*p^2 + (2535112427919686144753818803296095883695325749/8175820312500000000000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge1_09_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 9 = admission_power_Cbridge1_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_09] <;> ring

def admission_power_Cbridge1_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-3553971343717636914875861/3139515000000000000000000:ℝ)*δ^1*p^1 + (494652274301959657208429/784878750000000000000000:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (16790623/8372040:ℝ)*δ^2*p^1 + (-3264319218782363085124139/2616262500000000000000000:ℝ)*δ^2*p^2 + (357144319415771271/3125000000000000000:ℝ)*δ^2*p^3
theorem admission_power_Cbridge1_10_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 10 = admission_power_Cbridge1_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_10] <;> ring

def admission_power_Cbridge1_11 (δ p : ℝ) : ℝ := (12588183255773295245381/5232525000000000000000:ℝ)*δ^0*p^0 + (-973835/209301:ℝ)*δ^0*p^1 + (35359580053217174379619/15697575000000000000000:ℝ)*δ^0*p^2 + (-613369/209301:ℝ)*δ^1*p^0 + (37089825232680114263857/6540656250000000000000:ℝ)*δ^1*p^1 + (-8982648196474322160869/3270328125000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge1_11_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 11 = admission_power_Cbridge1_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_11] <;> ring

def admission_power_Cbridge1_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge1_12_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 12 = admission_power_Cbridge1_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_12] <;> ring

def admission_power_Cbridge1_13 (δ p : ℝ) : ℝ := (6114996976645773128704211143/124584438663400571319285000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge1_13_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 13 = admission_power_Cbridge1_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_13] <;> ring

def admission_power_Cbridge1_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cbridge1_14_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 14 = admission_power_Cbridge1_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_14] <;> ring

def admission_power_Cbridge2_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-749992190281953781/250000000000000000:ℝ)*δ^0*p^1
theorem admission_power_Cbridge2_00_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 0 = admission_power_Cbridge2_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_00] <;> ring

def admission_power_Cbridge2_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-499992190281953781/250000000000000000:ℝ)*δ^0*p^1
theorem admission_power_Cbridge2_01_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 1 = admission_power_Cbridge2_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_01] <;> ring

def admission_power_Cbridge2_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-253981/261943:ℝ)*δ^0*p^1
theorem admission_power_Cbridge2_02_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 2 = admission_power_Cbridge2_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_02] <;> ring

def admission_power_Cbridge2_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-749992190281953781/300000000000000000:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (499992190281953781/250000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge2_03_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 3 = admission_power_Cbridge2_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_03] <;> ring

def admission_power_Cbridge2_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-515924/261943:ℝ)*δ^1*p^1 + (253981/261943:ℝ)*δ^1*p^2
theorem admission_power_Cbridge2_04_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 4 = admission_power_Cbridge2_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_04] <;> ring

def admission_power_Cbridge2_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-624743494504867499573/1000000000000000000000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (4504644443/2619430000:ℝ)*δ^1*p^1 + (-307659833706734477678048983/654857500000000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge2_05_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 5 = admission_power_Cbridge2_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_05] <;> ring

def admission_power_Cbridge2_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-2185421852054213505054701/2907567300000000000000000:ℝ)*δ^0*p^1 + (150391662781601359358416863566305934285561/363445912500000000000000000000000000000000:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-14316843948877593842899109/2422972750000000000000000:ℝ)*δ^1*p^1 + (3059797860101095859738601/484594550000000000000000:ℝ)*δ^1*p^2 + (-2624931665394037455480071002341371727/1156250000000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge2_06_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 6 = admission_power_Cbridge2_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_06] <;> ring

def admission_power_Cbridge2_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-386940954299025819256483/78582900000000000000000:ℝ)*δ^0*p^1 + (190483766480000903252161/78582900000000000000000:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (386940954299025819256483/65485750000000000000000:ℝ)*δ^1*p^1 + (-190483766480000903252161/65485750000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge2_07_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 7 = admission_power_Cbridge2_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_07] <;> ring

def admission_power_Cbridge2_08 (δ p : ℝ) : ℝ := (-67429511427534901504209256483/174625939065367759008644000000:ℝ)*δ^0*p^0 + (5049643137706864259672963895405567218571419293/5953157013592082693476500000000000000000000000:ℝ)*δ^0*p^1 + (-15129977966636511205985595254125833696606644553450340149593221721/32742363574756454814120750000000000000000000000000000000000000000:ℝ)*δ^0*p^2 + (503994359090954299025819256483/436564847663419397521610000000:ℝ)*δ^1*p^0 + (-327422323729617419739637798620047074585996870741/109141211915854849380402500000000000000000000000:ℝ)*δ^1*p^1 + (66725249063192613438354958475855417590855629259/27285302978963712345100625000000000000000000000:ℝ)*δ^1*p^2 + (-374957845545129738400137288561285379804039/625000000000000000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge2_08_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 8 = admission_power_Cbridge2_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_08] <;> ring

def admission_power_Cbridge2_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-614300914919118011492994155551/392914500000000000000000000000:ℝ)*δ^0*p^1 + (53678456577218828027270549447037361879957954259/65485750000000000000000000000000000000000000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (7499966222977259820871219/2500000000000000000000000:ℝ)*δ^1*p^1 + (-330103176057669678882737781483/163714375000000000000000000000:ℝ)*δ^1*p^2 + (51381770802864108232805781288137914360126137223/163714375000000000000000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge2_09_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 9 = admission_power_Cbridge2_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_09] <;> ring

def admission_power_Cbridge2_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-18134422483926302880074959/15716580000000000000000000:ℝ)*δ^1*p^1 + (2585396887102922542230551/3929145000000000000000000:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (21422789/10477720:ℝ)*δ^2*p^1 + (-17021054266073697119925041/13097150000000000000000000:ℝ)*δ^2*p^2 + (1499976570845861343/12500000000000000000:ℝ)*δ^2*p^3
theorem admission_power_Cbridge2_10_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 10 = admission_power_Cbridge2_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_10] <;> ring

def admission_power_Cbridge2_11 (δ p : ℝ) : ℝ := (190487795700974180743517/78582900000000000000000:ℝ)*δ^0*p^0 + (-1269905/261943:ℝ)*δ^0*p^1 + (190483766480000903252161/78582900000000000000000:ℝ)*δ^0*p^2 + (-777867/261943:ℝ)*δ^1*p^0 + (194464704299025819256483/32742875000000000000000:ℝ)*δ^1*p^1 + (-48615680194756680627161/16371437500000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge2_11_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 11 = admission_power_Cbridge2_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_11] <;> ring

def admission_power_Cbridge2_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge2_12_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 12 = admission_power_Cbridge2_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_12] <;> ring

def admission_power_Cbridge2_13 (δ p : ℝ) : ℝ := (29217898215759032689891768517/654847271495129096282415000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge2_13_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 13 = admission_power_Cbridge2_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_13] <;> ring

def admission_power_Cbridge2_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cbridge2_14_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 14 = admission_power_Cbridge2_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_14] <;> ring

def admission_power_Cbridge3_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-388120991411016197/125000000000000000:ℝ)*δ^0*p^1
theorem admission_power_Cbridge3_00_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 0 = admission_power_Cbridge3_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_00] <;> ring

def admission_power_Cbridge3_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-263120991411016197/125000000000000000:ℝ)*δ^0*p^1
theorem admission_power_Cbridge3_01_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 1 = admission_power_Cbridge3_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_01] <;> ring

def admission_power_Cbridge3_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-49709/49127:ℝ)*δ^0*p^1
theorem admission_power_Cbridge3_02_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 2 = admission_power_Cbridge3_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_02] <;> ring

def admission_power_Cbridge3_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-388120991411016197/150000000000000000:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (263120991411016197/125000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge3_03_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 3 = admission_power_Cbridge3_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_03] <;> ring

def admission_power_Cbridge3_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-98836/49127:ℝ)*δ^1*p^1 + (49709/49127:ℝ)*δ^1*p^2
theorem admission_power_Cbridge3_04_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 4 = admission_power_Cbridge3_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_04] <;> ring

def admission_power_Cbridge3_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-323304785845376492101/500000000000000000000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (865591627/491270000:ℝ)*δ^1*p^1 + (-29833313982322567217662519/61408750000000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge3_05_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 5 = admission_power_Cbridge3_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_05] <;> ring

def admission_power_Cbridge3_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-206446962417302657370893/272654850000000000000000:ℝ)*δ^0*p^1 + (7187409697429120697330238598272132244201/17040928125000000000000000000000000000000:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-1386175183736126832330437/227212375000000000000000:ℝ)*δ^1*p^1 + (304738500463720228963593/45442475000000000000000:ℝ)*δ^1*p^2 + (-19320525954931123988141010199308099/7812500000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge3_06_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 6 = admission_power_Cbridge3_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_06] <;> ring

def admission_power_Cbridge3_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-37708094945048992710019/7369050000000000000000:ℝ)*δ^0*p^1 + (19293106362050204136673/7369050000000000000000:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (37708094945048992710019/6140875000000000000000:ℝ)*δ^1*p^1 + (-19293106362050204136673/6140875000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge3_07_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 7 = admission_power_Cbridge3_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_07] <;> ring

def admission_power_Cbridge3_08 (δ p : ℝ) : ℝ := (-2255978966532767560754236673/5745042197799552315564000000:ℝ)*δ^0*p^0 + (937915184551078687953423149891549739609392581/1077195412087416059168250000000000000000000000:ℝ)*δ^0*p^1 + (-388213199647187998310386896400558029941753010021723299217634457/807896559065562044376187500000000000000000000000000000000000000:ℝ)*δ^0*p^2 + (16618584461031648349664236673/14362605494498880788910000000:ℝ)*δ^1*p^0 + (-16375983485287684380931382103728623727244392581/5385977060437080295841250000000000000000000000:ℝ)*δ^1*p^1 + (3376130254826754813116747891308237254208107419/1346494265109270073960312500000000000000000000:ℝ)*δ^1*p^2 + (-97020345674940873597941812683231803657191/156250000000000000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge3_08_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 8 = admission_power_Cbridge3_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_08] <;> ring

def admission_power_Cbridge3_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-58856646860105881715423394943/36845250000000000000000000000:ℝ)*δ^0*p^1 + (2630096360472202188597158100641708270668432419/3070437500000000000000000000000000000000000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (3806748274731653641008803/1250000000000000000000000:ℝ)*δ^1*p^1 + (-31723988843099283353208035019/15352187500000000000000000000:ℝ)*δ^1*p^2 + (2417924317973011986938458820699875187994702743/7676093750000000000000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge3_09_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 9 = admission_power_Cbridge3_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_09] <;> ring

def admission_power_Cbridge3_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-1735013561483677196829487/1473810000000000000000000:ℝ)*δ^1*p^1 + (253479590164853021869943/368452500000000000000000:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (4100821/1965080:ℝ)*δ^2*p^1 + (-1665426813516322803170513/1228175000000000000000000:ℝ)*δ^2*p^2 + (789362974233048591/6250000000000000000:ℝ)*δ^2*p^3
theorem admission_power_Cbridge3_10_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 10 = admission_power_Cbridge3_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_10] <;> ring

def admission_power_Cbridge3_11 (δ p : ℝ) : ℝ := (17996280054951007289981/7369050000000000000000:ℝ)*δ^0*p^0 + (-248545/49127:ℝ)*δ^0*p^1 + (19293106362050204136673/7369050000000000000000:ℝ)*δ^0*p^2 + (-147963/49127:ℝ)*δ^1*p^0 + (19139969945048992710019/3070437500000000000000:ℝ)*δ^1*p^1 + (-4948050326774799211673/1535218750000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge3_11_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 11 = admission_power_Cbridge3_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_11] <;> ring

def admission_power_Cbridge3_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge3_12_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 12 = admission_power_Cbridge3_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_12] <;> ring

def admission_power_Cbridge3_13 (δ p : ℝ) : ℝ := (2545257904568161480175114981/64631724725244963550095000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge3_13_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 13 = admission_power_Cbridge3_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_13] <;> ring

def admission_power_Cbridge3_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cbridge3_14_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 14 = admission_power_Cbridge3_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_14] <;> ring

def admission_power_Cbridge4_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-161120530973824351/50000000000000000:ℝ)*δ^0*p^1
theorem admission_power_Cbridge4_00_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 0 = admission_power_Cbridge4_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_00] <;> ring

def admission_power_Cbridge4_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-111120530973824351/50000000000000000:ℝ)*δ^0*p^1
theorem admission_power_Cbridge4_01_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 1 = admission_power_Cbridge4_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_01] <;> ring

def admission_power_Cbridge4_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-48659/45977:ℝ)*δ^0*p^1
theorem admission_power_Cbridge4_02_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 2 = admission_power_Cbridge4_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_02] <;> ring

def admission_power_Cbridge4_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-161120530973824351/60000000000000000:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (111120530973824351/50000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge4_03_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 3 = admission_power_Cbridge4_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_03] <;> ring

def admission_power_Cbridge4_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-94636/45977:ℝ)*δ^1*p^1 + (48659/45977:ℝ)*δ^1*p^2
theorem admission_power_Cbridge4_04_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 4 = admission_power_Cbridge4_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_04] <;> ring

def admission_power_Cbridge4_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-134213402301195684383/200000000000000000000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (831463477/459770000:ℝ)*δ^1*p^1 + (-11562137357193778057368427/22988500000000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge4_05_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 5 = admission_power_Cbridge4_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_05] <;> ring

def admission_power_Cbridge4_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-78110966671425542738569/102068940000000000000000:ℝ)*δ^0*p^1 + (367639218867522087012144410400411586213/850574500000000000000000000000000000000:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-536989439009421010276321/85057450000000000000000:ℝ)*δ^1*p^1 + (121673185892184809787669/17011490000000000000000:ℝ)*δ^1*p^2 + (-125326592668171121628701486203998407/46250000000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge4_06_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 6 = admission_power_Cbridge4_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_06] <;> ring

def admission_power_Cbridge4_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-14706688652583522185927/2758620000000000000000:ℝ)*δ^0*p^1 + (7839963916655319095309/2758620000000000000000:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (14706688652583522185927/2298850000000000000000:ℝ)*δ^1*p^1 + (-7839963916655319095309/2298850000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge4_07_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 7 = admission_power_Cbridge4_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_07] <;> ring

def admission_power_Cbridge4_08 (δ p : ℝ) : ℝ := (-8106921904230735891296557781/20435954610334088743708000000:ℝ)*δ^0*p^0 + (1366745946498996663268303047016931401501325131/1532696595775056655778100000000000000000000000:ℝ)*δ^0*p^1 + (-76655795742029657337989404141431139786656895319735414323688327/153269659577505665577810000000000000000000000000000000000000000:ℝ)*δ^0*p^2 + (59196808430065957750566557781/51089886525835221859270000000:ℝ)*δ^1*p^0 + (-7882916292774648257498572705479747314462108377/2554494326291761092963500000000000000000000000:ℝ)*δ^1*p^1 + (1646223999827657573316130746018907956480391623/638623581572940273240875000000000000000000000:ℝ)*δ^1*p^2 + (-16110407876220646878180381614073399428799/25000000000000000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge4_08_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 8 = admission_power_Cbridge4_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_08] <;> ring

def admission_power_Cbridge4_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-22583241030837631682201267219/13793100000000000000000000000:ℝ)*δ^0*p^1 + (1242141777956769813190745378955301304268416623/1379310000000000000000000000000000000000000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (1548096285341259344250649/500000000000000000000000:ℝ)*δ^1*p^1 + (-12184719830236224594205410927/5747125000000000000000000000:ℝ)*δ^1*p^2 + (359802960272484230339859074694698695731583377/1149425000000000000000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge4_09_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 9 = admission_power_Cbridge4_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_09] <;> ring

def admission_power_Cbridge4_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-663589756380244900979971/551724000000000000000000:ℝ)*δ^1*p^1 + (99423984042249433442219/137931000000000000000000:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (3923371/1839080:ℝ)*δ^2*p^1 + (-652118893619755099020029/459770000000000000000000:ℝ)*δ^2*p^2 + (333361592921473053/2500000000000000000:ℝ)*δ^2*p^3
theorem admission_power_Cbridge4_10_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 10 = admission_power_Cbridge4_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_10] <;> ring

def admission_power_Cbridge4_11 (δ p : ℝ) : ℝ := (6787561347416477814073/2758620000000000000000:ℝ)*δ^0*p^0 + (-243295/45977:ℝ)*δ^0*p^1 + (7839963916655319095309/2758620000000000000000:ℝ)*δ^0*p^2 + (-140613/45977:ℝ)*δ^1*p^0 + (7541938652583522185927/1149425000000000000000:ℝ)*δ^1*p^1 + (-2020763142309710320309/574712500000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge4_11_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 11 = admission_power_Cbridge4_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_11] <;> ring

def admission_power_Cbridge4_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge4_12_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 12 = admission_power_Cbridge4_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_12] <;> ring

def admission_power_Cbridge4_13 (δ p : ℝ) : ℝ := (853804370887613962343539073/25544943262917610929635000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge4_13_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 13 = admission_power_Cbridge4_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_13] <;> ring

def admission_power_Cbridge4_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cbridge4_14_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 14 = admission_power_Cbridge4_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_14] <;> ring

def admission_power_Cbridge5_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-790613321763782193/250000000000000000:ℝ)*δ^0*p^1
theorem admission_power_Cbridge5_00_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 0 = admission_power_Cbridge5_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_00] <;> ring

def admission_power_Cbridge5_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-540613321763782193/250000000000000000:ℝ)*δ^0*p^1
theorem admission_power_Cbridge5_01_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 1 = admission_power_Cbridge5_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_01] <;> ring

def admission_power_Cbridge5_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-147527/142581:ℝ)*δ^0*p^1
theorem admission_power_Cbridge5_02_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 2 = admission_power_Cbridge5_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_02] <;> ring

def admission_power_Cbridge5_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-263537773921260731/100000000000000000:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (540613321763782193/250000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge5_03_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 3 = admission_power_Cbridge5_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_03] <;> ring

def admission_power_Cbridge5_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-290108/142581:ℝ)*δ^1*p^1 + (147527/142581:ℝ)*δ^1*p^2
theorem admission_power_Cbridge5_04_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 4 = admission_power_Cbridge5_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_04] <;> ring

def admission_power_Cbridge5_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-658580897029230566769/1000000000000000000000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (2544770081/1425810000:ℝ)*δ^1*p^1 + (-176191611112025829678527633/356452500000000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge5_05_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 5 = admission_power_Cbridge5_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_05] <;> ring

def admission_power_Cbridge5_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-401422779142961985475417/527549700000000000000000:ℝ)*δ^0*p^1 + (28138637357806842468039253682624170360561/65943712500000000000000000000000000000000:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-2727894274899747354594353/439624750000000000000000:ℝ)*δ^1*p^1 + (16452508208895109464641/2376350000000000000000:ℝ)*δ^1*p^2 + (-2991912658765913719131044010407224743/1156250000000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge5_06_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 6 = admission_power_Cbridge5_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_06] <;> ring

def admission_power_Cbridge5_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-74457229343467276286711/14258100000000000000000:ℝ)*δ^0*p^1 + (38878937173281831862237/14258100000000000000000:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (74457229343467276286711/11881750000000000000000:ℝ)*δ^1*p^1 + (-38878937173281831862237/11881750000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge5_07_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 7 = admission_power_Cbridge5_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_07] <;> ring

def admission_power_Cbridge5_08 (δ p : ℝ) : ℝ := (-40596983987015267534718860133/102774917373869105146844000000:ℝ)*δ^0*p^0 + (33971712987449475039542307289395028009958011669/38540594015200914430066500000000000000000000000:ℝ)*δ^0*p^1 + (-9447014760927538254584544064418702410777014810469923696554470039/19270297007600457215033250000000000000000000000000000000000000000:ℝ)*δ^0*p^2 + (297534277421688030401828860133/256937293434672762867110000000:ℝ)*δ^1*p^0 + (-196730921857565055897790668035268383232024337223/64234323358668190716777500000000000000000000000:ℝ)*δ^1*p^1 + (40815796413622010054300841647874177611033162777/16058580839667047679194375000000000000000000000:ℝ)*δ^1*p^2 + (-395266307493047916083007909850855656110751/625000000000000000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge5_08_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 8 = admission_power_Cbridge5_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_08] <;> ring

def admission_power_Cbridge5_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-115255585037713497984691364867/71290500000000000000000000000:ℝ)*δ^0*p^1 + (31288319747237699259873847416710122026465137777/35645250000000000000000000000000000000000000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (7675652576015036220942807/2500000000000000000000000:ℝ)*δ^1*p^1 + (-62170580424839064244028711711/29704375000000000000000000000:ℝ)*δ^1*p^2 + (9340157899016457358313349655539877973534862223/29704375000000000000000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge5_09_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 9 = admission_power_Cbridge5_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_09] <;> ring

def admission_power_Cbridge5_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-10178557173179150620776409/8554860000000000000000000:ℝ)*δ^1*p^1 + (1505908185908794513419601/2138715000000000000000000:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (12032063/5703240:ℝ)*δ^2*p^1 + (-9885285076820849379223591/7129050000000000000000000:ℝ)*δ^2*p^2 + (1621839965291346579/12500000000000000000:ℝ)*δ^2*p^3
theorem admission_power_Cbridge5_10_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 10 = admission_power_Cbridge5_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_10] <;> ring

def admission_power_Cbridge5_11 (δ p : ℝ) : ℝ := (34951520656532723713289/14258100000000000000000:ℝ)*δ^0*p^0 + (-737635/142581:ℝ)*δ^0*p^1 + (38878937173281831862237/14258100000000000000000:ℝ)*δ^0*p^2 + (-432689/142581:ℝ)*δ^1*p^0 + (113962938030401828860133/17822625000000000000000:ℝ)*δ^1*p^1 + (-29988624887561831111711/8911312500000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge5_11_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 11 = admission_power_Cbridge5_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_11] <;> ring

def admission_power_Cbridge5_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge5_12_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 12 = admission_power_Cbridge5_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_12] <;> ring

def admission_power_Cbridge5_13 (δ p : ℝ) : ℝ := (230394481915148520952392047/6318130166426379414765000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge5_13_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 13 = admission_power_Cbridge5_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_13] <;> ring

def admission_power_Cbridge5_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cbridge5_14_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 14 = admission_power_Cbridge5_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_14] <;> ring

def admission_power_Cbridge6_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-82148659256046931/25000000000000000:ℝ)*δ^0*p^1
theorem admission_power_Cbridge6_00_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 0 = admission_power_Cbridge6_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_00] <;> ring

def admission_power_Cbridge6_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-57148659256046931/25000000000000000:ℝ)*δ^0*p^1
theorem admission_power_Cbridge6_01_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 1 = admission_power_Cbridge6_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_01] <;> ring

def admission_power_Cbridge6_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-36113/33339:ℝ)*δ^0*p^1
theorem admission_power_Cbridge6_02_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 2 = admission_power_Cbridge6_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_02] <;> ring

def admission_power_Cbridge6_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-82148659256046931/30000000000000000:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (57148659256046931/25000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge6_03_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 3 = admission_power_Cbridge6_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_03] <;> ring

def admission_power_Cbridge6_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-69452/33339:ℝ)*δ^1*p^1 + (36113/33339:ℝ)*δ^1*p^2
theorem admission_power_Cbridge6_04_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 4 = admission_power_Cbridge6_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_04] <;> ring

def admission_power_Cbridge6_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-68429833160287093523/100000000000000000000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (611205839/333390000:ℝ)*δ^1*p^1 + (-4266957401807565767110109/8334750000000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge6_05_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 5 = admission_power_Cbridge6_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_05] <;> ring

def admission_power_Cbridge6_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-3167541121561709525847/4111810000000000000000:ℝ)*δ^0*p^1 + (202826399802504094185935883913066810853/462578625000000000000000000000000000000:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-66070290157186339516669/10279525000000000000000:ℝ)*δ^1*p^1 + (45625952025179113547323/6167715000000000000000:ℝ)*δ^1*p^2 + (-32862800153154522851937622121631327/11562500000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge6_06_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 6 = admission_power_Cbridge6_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_06] <;> ring

def admission_power_Cbridge6_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-605247683437483181401/111130000000000000000:ℝ)*δ^0*p^1 + (2966634531713622819203/1000170000000000000000:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (1815743050312449544203/277825000000000000000:ℝ)*δ^1*p^1 + (-2966634531713622819203/833475000000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge6_07_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 7 = admission_power_Cbridge6_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_07] <;> ring

def admission_power_Cbridge6_08 (δ p : ℝ) : ℝ := (-1010539764104655495318632609/2540372201249798176812000000:ℝ)*δ^0*p^0 + (85898508211920974916337302244277032615972979/95263957546867431630450000000000000000000000:ℝ)*δ^0*p^1 + (-7293365778385104727031951437665902905988494397303406266877449/14289593632030114744567500000000000000000000000000000000000000:ℝ)*δ^0*p^2 + (7361470267229150937348632609/6350930503124495442030000000:ℝ)*δ^1*p^0 + (-1481584005766953418939159709881911987580972979/476319787734337158152250000000000000000000000:ℝ)*δ^1*p^1 + (311547261495729250092559485830790444866527021/119079946933584289538062500000000000000000000:ℝ)*δ^1*p^2 + (-4107013417387367348066614008911125481239/6250000000000000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge6_08_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 8 = admission_power_Cbridge6_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_08] <;> ring

def admission_power_Cbridge6_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-922131237495878059223430797/555650000000000000000000000:ℝ)*δ^0*p^1 + (231401187210075099890182224014375720553202021/250042500000000000000000000000000000000000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (780917944133743720528069/250000000000000000000000:ℝ)*δ^1*p^1 + (-1492182606479079894279069203/694562500000000000000000000:ℝ)*δ^1*p^2 + (64726536891171947576950085760624279446797979/208368750000000000000000000000000000000000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge6_09_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 9 = admission_power_Cbridge6_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_09] <;> ring

def admission_power_Cbridge6_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-243308537924691586919557/200034000000000000000000:ℝ)*δ^1*p^1 + (36924987547187954102173/50008500000000000000000:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (2878097/1333560:ℝ)*δ^2*p^1 + (-242009237075308413080443/166695000000000000000000:ℝ)*δ^2*p^2 + (171445977768140793/1250000000000000000:ℝ)*δ^2*p^3
theorem admission_power_Cbridge6_10_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 10 = admission_power_Cbridge6_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_10] <;> ring

def admission_power_Cbridge6_11 (δ p : ℝ) : ℝ := (823381949687550455797/333390000000000000000:ℝ)*δ^0*p^0 + (-180565/33339:ℝ)*δ^0*p^1 + (2966634531713622819203/1000170000000000000000:ℝ)*δ^0*p^2 + (-102791/33339:ℝ)*δ^1*p^0 + (2808104150937348632609/416737500000000000000:ℝ)*δ^1*p^1 + (-766565920662742862953/208368750000000000000:ℝ)*δ^1*p^2
theorem admission_power_Cbridge6_11_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 11 = admission_power_Cbridge6_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_11] <;> ring

def admission_power_Cbridge6_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge6_12_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 12 = admission_power_Cbridge6_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_12] <;> ring

def admission_power_Cbridge6_13 (δ p : ℝ) : ℝ := (287829099966816226617442391/9526395754686743163045000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge6_13_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 13 = admission_power_Cbridge6_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_13] <;> ring

def admission_power_Cbridge6_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cbridge6_14_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 14 = admission_power_Cbridge6_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_14] <;> ring

end
end Qrh.JointDetector.BoundarySeedReturn
