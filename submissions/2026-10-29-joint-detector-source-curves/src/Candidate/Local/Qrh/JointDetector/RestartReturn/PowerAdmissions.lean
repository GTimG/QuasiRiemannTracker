/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/restart_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
A finite count-source bank and physical source remain explicit; no missing estimate is asserted. -/
import Candidate.Local.Qrh.JointDetector.RestartReturn.Formulas
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unnecessarySeqFocus false
namespace Qrh.JointDetector.RestartReturn
open QRH.Record1252270103Return
noncomputable section

def admission_power_Cnew_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-1142923181897/342923181897:ℝ)*δ^0*p^1
theorem admission_power_Cnew_00_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 0 = admission_power_Cnew_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_00] <;> ring

def admission_power_Cnew_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-800000000000/342923181897:ℝ)*δ^0*p^1
theorem admission_power_Cnew_01_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 1 = admission_power_Cnew_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_01] <;> ring

def admission_power_Cnew_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-94429431246019/85730795474250:ℝ)*δ^0*p^1
theorem admission_power_Cnew_02_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 2 = admission_power_Cnew_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_02] <;> ring

def admission_power_Cnew_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-5714615909485/2057539091382:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (800000000000/342923181897:ℝ)*δ^1*p^2
theorem admission_power_Cnew_03_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 3 = admission_power_Cnew_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_03] <;> ring

def admission_power_Cnew_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-180160226720269/85730795474250:ℝ)*δ^1*p^1 + (94429431246019/85730795474250:ℝ)*δ^1*p^2
theorem admission_power_Cnew_04_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 4 = admission_power_Cnew_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_04] <;> ring

def admission_power_Cnew_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-952055010520201/1371692727588000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (6349444037250157/3429231818970000:ℝ)*δ^1*p^1 + (-44449431246019/85730795474250:ℝ)*δ^1*p^2
theorem admission_power_Cnew_05_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 5 = admission_power_Cnew_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_05] <;> ring

def admission_power_Cnew_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-2947680518981641/3806447319056700:ℝ)*δ^0*p^1 + (192903405369260416910921303/435106342124742909518853300:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-20654168574134359/3172039432547250:ℝ)*δ^1*p^1 + (8245573400538359388897499091/1087765855311857273797133250:ℝ)*δ^1*p^2 + (-12800739637246400000000000/4351063421247429095188533:ℝ)*δ^1*p^3
theorem admission_power_Cnew_06_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 6 = admission_power_Cnew_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_06] <;> ring

def admission_power_Cnew_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-569019089212307/102876954569100:ℝ)*δ^0*p^1 + (107925586024424028894118043/35278892604708884555582700:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (569019089212307/85730795474250:ℝ)*δ^1*p^1 + (-107925586024424028894118043/29399077170590737129652250:ℝ)*δ^1*p^2
theorem admission_power_Cnew_07_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 7 = admission_power_Cnew_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_07] <;> ring

def admission_power_Cnew_08 (δ p : ℝ) : ℝ := (-626813739337344791/1600000000000000000:ℝ)*δ^0*p^0 + (735939967309738864809098448527/823015636552800000000000000000:ℝ)*δ^0*p^1 + (-287818527990590036634054828755468304238573/564462281675342152889323200000000000000000:ℝ)*δ^0*p^2 + (4626813739337344791/4000000000000000000:ℝ)*δ^1*p^0 + (-715189008926957653821211283497/228615454598000000000000000000:ℝ)*δ^1*p^1 + (3640156875590971212263633850491/1371692727588000000000000000000:ℝ)*δ^1*p^2 + (-395814160152415622945994710491/587981543411814742593045000000:ℝ)*δ^1*p^3
theorem admission_power_Cnew_08_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 8 = admission_power_Cnew_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_08] <;> ring

def admission_power_Cnew_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-3449043072097889309/2057539091382000000:ℝ)*δ^0*p^1 + (1332607706528098879015313686391/1411155704188355382223308000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (5390704909673656897/1714615909485000000:ℝ)*δ^1*p^1 + (-2479208116570312299/1143077272990000000:ℝ)*δ^1*p^2 + (9062753648797166834118043/29399077170590737129652250:ℝ)*δ^1*p^3
theorem admission_power_Cnew_09_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 9 = admission_power_Cnew_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_09] <;> ring

def admission_power_Cnew_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-504620104583521/411507818276400:ℝ)*δ^1*p^1 + (19321395879391/25719238642275:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (746360145523351/342923181897000:ℝ)*δ^2*p^1 + (-63286639487237/42865397737125:ℝ)*δ^2*p^2 + (16000000000/114307727299:ℝ)*δ^2*p^3
theorem admission_power_Cnew_10_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 10 = admission_power_Cnew_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_10] <;> ring

def admission_power_Cnew_11 (δ p : ℝ) : ℝ := (254749884686557/102876954569100:ℝ)*δ^0*p^0 + (-94429431246019/17146159094850:ℝ)*δ^0*p^1 + (107925586024424028894118043/35278892604708884555582700:ℝ)*δ^0*p^2 + (-265891022194519/85730795474250:ℝ)*δ^1*p^0 + (98143143748673/14288465912375:ℝ)*δ^1*p^1 + (-111746140348606371105881957/29399077170590737129652250:ℝ)*δ^1*p^2
theorem admission_power_Cnew_11_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 11 = admission_power_Cnew_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_11] <;> ring

def admission_power_Cnew_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cnew_12_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 12 = admission_power_Cnew_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_12] <;> ring

def admission_power_Cnew_13 (δ p : ℝ) : ℝ := (55710927428098103/2000000000000000000:ℝ)*δ^0*p^0
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

def admission_power_Pnew_09 (δ p : ℝ) : ℝ := (1083837862247965691/1600000000000000000:ℝ)*δ^0*p^0 + (-2339839062247965691/2400000000000000000:ℝ)*δ^0*p^1 + (1198613420749321897/4800000000000000000:ℝ)*δ^0*p^2 + (-5083837862247965691/4000000000000000000:ℝ)*δ^1*p^0 + (4305387379250678103/2000000000000000000:ℝ)*δ^1*p^1 + (-3793384979250678103/4000000000000000000:ℝ)*δ^1*p^2 + (619999/5000000:ℝ)*δ^1*p^3
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

def admission_power_Pnew_13 (δ p : ℝ) : ℝ := (104404765249998103/2000000000000000000:ℝ)*δ^0*p^0
theorem admission_power_Pnew_13_expanded (δ p : ℝ) : admissionGuard .Pnew δ p 13 = admission_power_Pnew_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pnew_13] <;> ring

def admission_power_Pnew_14 (δ p : ℝ) : ℝ := (479997/2000000:ℝ)*δ^0*p^0 + (-159999/1000000:ℝ)*δ^0*p^1 + (53333/2000000:ℝ)*δ^0*p^2 + (-479997/5000000:ℝ)*δ^1*p^0 + (-159999/2500000:ℝ)*δ^1*p^1 + (159999/5000000:ℝ)*δ^1*p^2
theorem admission_power_Pnew_14_expanded (δ p : ℝ) : admissionGuard .Pnew δ p 14 = admission_power_Pnew_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pnew_14] <;> ring

def admission_power_Cphys_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-1236853181897/436853181897:ℝ)*δ^0*p^1
theorem admission_power_Cphys_00_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 0 = admission_power_Cphys_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_00] <;> ring

def admission_power_Cphys_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-800000000000/436853181897:ℝ)*δ^0*p^1
theorem admission_power_Cphys_01_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 1 = admission_power_Cphys_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_01] <;> ring

def admission_power_Cphys_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-49136538916807/54606647737125:ℝ)*δ^0*p^1
theorem admission_power_Cphys_02_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 2 = admission_power_Cphys_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_02] <;> ring

def admission_power_Cphys_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-6184265909485/2621119091382:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (800000000000/436853181897:ℝ)*δ^1*p^2
theorem admission_power_Cphys_03_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 3 = admission_power_Cphys_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_03] <;> ring

def admission_power_Cphys_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-103743186653932/54606647737125:ℝ)*δ^1*p^1 + (49136538916807/54606647737125:ℝ)*δ^1*p^2
theorem admission_power_Cphys_04_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 4 = admission_power_Cphys_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_04] <;> ring

def admission_power_Cphys_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-1030298700520201/1747412727588000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (7207758830753957/4368531818970000:ℝ)*δ^1*p^1 + (-24146538916807/54606647737125:ℝ)*δ^1*p^2
theorem admission_power_Cphys_05_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 5 = admission_power_Cphys_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_05] <;> ring

def admission_power_Cphys_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-906178311939649/1212267579764175:ℝ)*δ^0*p^1 + (9116953446785502323705941/22535444660874685005920850:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-11303587922678702/2020445966273625:ℝ)*δ^1*p^1 + (5029012374803248180600952273/882638249217591829398566625:ℝ)*δ^1*p^2 + (-13852755637246400000000000/7061105993740734635188533:ℝ)*δ^1*p^3
theorem admission_power_Cphys_06_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 6 = admission_power_Cphys_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_06] <;> ring

def admission_power_Cphys_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-151008132243773/32763988642275:ℝ)*δ^0*p^1 + (60774684506658507721442879/28626105380030005277791350:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (302016264487546/54606647737125:ℝ)*δ^1*p^1 + (-60774684506658507721442879/23855087816691671064826125:ℝ)*δ^1*p^2
theorem admission_power_Cphys_07_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 7 = admission_power_Cphys_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_07] <;> ring

def admission_power_Cphys_08 (δ p : ℝ) : ℝ := (-585958690839954791/1600000000000000000:ℝ)*δ^0*p^0 + (839897367012862590827979618527/1048447636552800000000000000000:ℝ)*δ^0*p^1 + (-393752153891543289333328522316994734068573/916035372160960168889323200000000000000000:ℝ)*δ^0*p^2 + (4585958690839954791/4000000000000000000:ℝ)*δ^1*p^0 + (-233162124373949913890061223681/79427851254000000000000000000:ℝ)*δ^1*p^1 + (4105034311324975303590673460491/1747412727588000000000000000000:ℝ)*δ^1*p^2 + (-540268180661807445248388620491/954203512667666842593045000000:ℝ)*δ^1*p^3
theorem admission_power_Cphys_08_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 8 = admission_power_Cphys_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_08] <;> ring

def admission_power_Cphys_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-3967515745052189309/2621119091382000000:ℝ)*δ^0*p^1 + (584811255615432544131395028797/763362810134133474074436000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (6393407753603656897/2184265909485000000:ℝ)*δ^1*p^1 + (-2810638261384112299/1456177272990000000:ℝ)*δ^1*p^2 + (2426932252715025563814293/7951695938897223688275375:ℝ)*δ^1*p^3
theorem admission_power_Cphys_09_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 9 = admission_power_Cphys_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_09] <;> ring

def admission_power_Cphys_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-584336740933901/524223818276400:ℝ)*δ^1*p^1 + (79720280105159/131055954569100:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (862709481873731/436853181897000:ℝ)*δ^2*p^1 + (-131825875562069/109213295474250:ℝ)*δ^2*p^2 + (16000000000/145617727299:ℝ)*δ^2*p^3
theorem admission_power_Cphys_10_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 10 = admission_power_Cphys_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_10] <;> ring

def admission_power_Cphys_11 (δ p : ℝ) : ℝ := (156622912224671/65527977284550:ℝ)*δ^0*p^0 + (-49136538916807/10921329547425:ℝ)*δ^0*p^1 + (60774684506658507721442879/28626105380030005277791350:ℝ)*δ^0*p^2 + (-158349834391057/54606647737125:ℝ)*δ^1*p^0 + (298273077833614/54606647737125:ℝ)*δ^1*p^1 + (-61529095949932692278557121/23855087816691671064826125:ℝ)*δ^1*p^2
theorem admission_power_Cphys_11_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 11 = admission_power_Cphys_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_11] <;> ring

def admission_power_Cphys_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cphys_12_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 12 = admission_power_Cphys_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_12] <;> ring

def admission_power_Cphys_13 (δ p : ℝ) : ℝ := (104404765249998103/2000000000000000000:ℝ)*δ^0*p^0
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

def admission_power_Pwide_09 (δ p : ℝ) : ℝ := (716881189454485691/1600000000000000000:ℝ)*δ^0*p^0 + (-1636882389454485691/2400000000000000000:ℝ)*δ^0*p^1 + (852294529818161897/4800000000000000000:ℝ)*δ^0*p^2 + (-4716881189454485691/4000000000000000000:ℝ)*δ^1*p^0 + (4427706270181838103/2000000000000000000:ℝ)*δ^1*p^1 + (-4587703870181838103/4000000000000000000:ℝ)*δ^1*p^2 + (899999/5000000:ℝ)*δ^1*p^3
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

def admission_power_Pwide_13 (δ p : ℝ) : ℝ := (104404765249998103/2000000000000000000:ℝ)*δ^0*p^0
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

def admission_power_Pcount_09 (δ p : ℝ) : ℝ := (626811339337344791/1600000000000000000:ℝ)*δ^0*p^0 + (-1414932539337344791/2400000000000000000:ℝ)*δ^0*p^1 + (734351246445781597/4800000000000000000:ℝ)*δ^0*p^2 + (-4626811339337344791/4000000000000000000:ℝ)*δ^1*p^0 + (4457729553554218403/2000000000000000000:ℝ)*δ^1*p^1 + (-4881487153554218403/4000000000000000000:ℝ)*δ^1*p^2 + (1009899/5000000:ℝ)*δ^1*p^3
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

def admission_power_Pcount_13 (δ p : ℝ) : ℝ := (55710927428098103/2000000000000000000:ℝ)*δ^0*p^0
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

def admission_power_Pcountmid_09 (δ p : ℝ) : ℝ := (631955187065799791/1600000000000000000:ℝ)*δ^0*p^0 + (-1426076387065799791/2400000000000000000:ℝ)*δ^0*p^1 + (740065862355266597/4800000000000000000:ℝ)*δ^0*p^2 + (-4631955187065799791/4000000000000000000:ℝ)*δ^1*p^0 + (4456014937644733403/2000000000000000000:ℝ)*δ^1*p^1 + (-4867772537644733403/4000000000000000000:ℝ)*δ^1*p^2 + (1004899/5000000:ℝ)*δ^1*p^3
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

def admission_power_Pcountmid_13 (δ p : ℝ) : ℝ := (55710927428098103/2000000000000000000:ℝ)*δ^0*p^0
theorem admission_power_Pcountmid_13_expanded (δ p : ℝ) : admissionGuard .Pcountmid δ p 13 = admission_power_Pcountmid_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pcountmid_13] <;> ring

def admission_power_Pcountmid_14 (δ p : ℝ) : ℝ := (1057347/2000000:ℝ)*δ^0*p^0 + (-352449/1000000:ℝ)*δ^0*p^1 + (117483/2000000:ℝ)*δ^0*p^2 + (-1057347/5000000:ℝ)*δ^1*p^0 + (-352449/2500000:ℝ)*δ^1*p^1 + (352449/5000000:ℝ)*δ^1*p^2
theorem admission_power_Pcountmid_14_expanded (δ p : ℝ) : admissionGuard .Pcountmid δ p 14 = admission_power_Pcountmid_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pcountmid_14] <;> ring

def admission_power_Cbridge0_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-1240003181897/440003181897:ℝ)*δ^0*p^1
theorem admission_power_Cbridge0_00_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 0 = admission_power_Cbridge0_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_00] <;> ring

def admission_power_Cbridge0_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-800000000000/440003181897:ℝ)*δ^0*p^1
theorem admission_power_Cbridge0_01_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 1 = admission_power_Cbridge0_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_01] <;> ring

def admission_power_Cbridge0_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-49185954837182/55000397737125:ℝ)*δ^0*p^1
theorem admission_power_Cbridge0_02_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 2 = admission_power_Cbridge0_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_02] <;> ring

def admission_power_Cbridge0_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-6200015909485/2640019091382:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (800000000000/440003181897:ℝ)*δ^1*p^2
theorem admission_power_Cbridge0_03_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 3 = admission_power_Cbridge0_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_03] <;> ring

def admission_power_Cbridge0_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-104186352574307/55000397737125:ℝ)*δ^1*p^1 + (49185954837182/55000397737125:ℝ)*δ^1*p^2
theorem admission_power_Cbridge0_04_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 4 = admission_power_Cbridge0_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_04] <;> ring

def admission_power_Cbridge0_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-1032922650520201/1760012727588000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (7235340254383957/4400031818970000:ℝ)*δ^1*p^1 + (-24195954837182/55000397737125:ℝ)*δ^1*p^2
theorem admission_power_Cbridge0_05_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 5 = admission_power_Cbridge0_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_05] <;> ring

def admission_power_Cbridge0_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-1825377706717673/2442017659528350:ℝ)*δ^0*p^1 + (72359401808171422167746392/179082590073523133379713325:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-11334666839840327/2035014716273625:ℝ)*δ^1*p^1 + (5059480117363967106808653148/895412950367615666898566625:ℝ)*δ^1*p^2 + (-13888035637246400000000000/7163303602940925335188533:ℝ)*δ^1*p^3
theorem admission_power_Cbridge0_06_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 6 = admission_power_Cbridge0_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_06] <;> ring

def admission_power_Cbridge0_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-302558262248671/66000477284550:ℝ)*δ^0*p^1 + (30495370251373909282447127/14520210005961335138895675:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (302558262248671/55000397737125:ℝ)*δ^1*p^1 + (-60990740502747818564894254/24200350009935558564826125:ℝ)*δ^1*p^2
theorem admission_power_Cbridge0_07_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 7 = admission_power_Cbridge0_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_07] <;> ring

def admission_power_Cbridge0_08 (δ p : ℝ) : ℝ := (-582439555734954791/1600000000000000000:ℝ)*δ^0*p^0 + (841307433983283015225444618527/1056007636552800000000000000000:ℝ)*δ^0*p^1 + (-396961377730114951302707143923345119068573/929293440381525448889323200000000000000000:ℝ)*δ^0*p^2 + (4582439555734954791/4000000000000000000:ℝ)*δ^1*p^0 + (-859638345673991859330506153497/293335454598000000000000000000:ℝ)*δ^1*p^1 + (4121832870715501828791518460491/1760012727588000000000000000000:ℝ)*δ^1*p^2 + (-545549743455906404187288620491/968014000397422342593045000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge0_08_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 8 = admission_power_Cbridge0_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_08] <;> ring

def admission_power_Cbridge0_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-3986707075157189309/2640019091382000000:ℝ)*δ^0*p^1 + (1770893351243293726466975086391/2323233600953813622223308000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (6427034006753656897/2200015909485000000:ℝ)*δ^1*p^1 + (-940183428688037433/488892424330000000:ℝ)*δ^1*p^2 + (7360615285734387534894254/24200350009935558564826125:ℝ)*δ^1*p^3
theorem admission_power_Cbridge0_09_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 9 = admission_power_Cbridge0_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_09] <;> ring

def admission_power_Cbridge0_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-586889818296901/528003818276400:ℝ)*δ^1*p^1 + (79771861945909/132000954569100:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (866491059236731/440003181897000:ℝ)*δ^2*p^1 + (-131971957402819/110000795474250:ℝ)*δ^2*p^2 + (16000000000/146667727299:ℝ)*δ^2*p^3
theorem admission_power_Cbridge0_10_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 10 = admission_power_Cbridge0_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_10] <;> ring

def admission_power_Cbridge0_11 (δ p : ℝ) : ℝ := (78779329992898/33000238642275:ℝ)*δ^0*p^0 + (-49185954837182/11000079547425:ℝ)*δ^0*p^1 + (30495370251373909282447127/14520210005961335138895675:ℝ)*δ^0*p^2 + (-159186750311432/55000397737125:ℝ)*δ^1*p^0 + (99457303224788/18333465912375:ℝ)*δ^1*p^1 + (-61707105426443381435105746/24200350009935558564826125:ℝ)*δ^1*p^2
theorem admission_power_Cbridge0_11_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 11 = admission_power_Cbridge0_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_11] <;> ring

def admission_power_Cbridge0_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge0_12_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 12 = admission_power_Cbridge0_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_12] <;> ring

def admission_power_Cbridge0_13 (δ p : ℝ) : ℝ := (105436398914998103/2000000000000000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge0_13_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 13 = admission_power_Cbridge0_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_13] <;> ring

def admission_power_Cbridge0_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cbridge0_14_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 14 = admission_power_Cbridge0_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_14] <;> ring

def admission_power_Cbridge1_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-1220003181897/420003181897:ℝ)*δ^0*p^1
theorem admission_power_Cbridge1_00_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 0 = admission_power_Cbridge1_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_00] <;> ring

def admission_power_Cbridge1_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-800000000000/420003181897:ℝ)*δ^0*p^1
theorem admission_power_Cbridge1_01_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 1 = admission_power_Cbridge1_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_01] <;> ring

def admission_power_Cbridge1_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-48854077528557/52500397737125:ℝ)*δ^0*p^1
theorem admission_power_Cbridge1_02_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 2 = admission_power_Cbridge1_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_02] <;> ring

def admission_power_Cbridge1_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-2033338636495/840006363794:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (800000000000/420003181897:ℝ)*δ^1*p^2
theorem admission_power_Cbridge1_03_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 3 = admission_power_Cbridge1_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_03] <;> ring

def admission_power_Cbridge1_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-101354475265682/52500397737125:ℝ)*δ^1*p^1 + (48854077528557/52500397737125:ℝ)*δ^1*p^2
theorem admission_power_Cbridge1_04_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 4 = admission_power_Cbridge1_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_04] <;> ring

def admission_power_Cbridge1_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-1016262650520201/1680012727588000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (7058770069693957/4200031818970000:ℝ)*δ^1*p^1 + (-23864077528557/52500397737125:ℝ)*δ^1*p^2
theorem admission_power_Cbridge1_05_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 5 = admission_power_Cbridge1_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_05] <;> ring

def admission_power_Cbridge1_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-290786014662508/388502943254725:ℝ)*δ^0*p^1 + (10241917319975999544591243/25103457283589866673802050:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-856563727583304/149424208944125:ℝ)*δ^1*p^1 + (4866001307268351657576073023/815862361716670666898566625:ℝ)*δ^1*p^2 + (-13664035637246400000000000/6526898893733365335188533:ℝ)*δ^1*p^3
theorem admission_power_Cbridge1_06_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 6 = admission_power_Cbridge1_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_06] <;> ring

def admission_power_Cbridge1_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-49843771720466/10500079547425:ℝ)*δ^0*p^1 + (19867376677827421960977543/8820133640180223425930450:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (299062630322796/52500397737125:ℝ)*δ^1*p^1 + (-59602130033482265882932629/22050334100450558564826125:ℝ)*δ^1*p^2
theorem admission_power_Cbridge1_07_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 7 = admission_power_Cbridge1_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_07] <;> ring

def admission_power_Cbridge1_08 (δ p : ℝ) : ℝ := (-602608218699954791/1600000000000000000:ℝ)*δ^0*p^0 + (276731528891497367250016539509/336002545517600000000000000000:ℝ)*δ^0*p^1 + (-125417035934111699399767491642285671356191/282244276485767149629774400000000000000000:ℝ)*δ^0*p^2 + (4602608218699954791/4000000000000000000:ℝ)*δ^1*p^0 + (-2489330154915572549149983460491/840006363794000000000000000000:ℝ)*δ^1*p^1 + (4016185371423098799949983460491/1680012727588000000000000000000:ℝ)*δ^1*p^2 + (-512352977392881268067288620491/882013364018022342593045000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge1_08_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 8 = admission_power_Cbridge1_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_08] <;> ring

def admission_power_Cbridge1_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-1289010804064063103/840006363794000000:ℝ)*δ^0*p^1 + (556397229172161405634635028797/705610691214417874074436000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (6213533986753656897/2100015909485000000:ℝ)*δ^1*p^1 + (-8268500284122336897/4200031818970000000:ℝ)*δ^1*p^2 + (6837004616468834852932629/22050334100450558564826125:ℝ)*δ^1*p^3
theorem admission_power_Cbridge1_09_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 9 = admission_power_Cbridge1_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_09] <;> ring

def admission_power_Cbridge1_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-570534799827901/504003818276400:ℝ)*δ^1*p^1 + (26469369109553/42000318189700:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (842336040767731/420003181897000:ℝ)*δ^2*p^1 + (-131008202785569/105000795474250:ℝ)*δ^2*p^2 + (48000000000/420003181897:ℝ)*δ^2*p^3
theorem admission_power_Cbridge1_10_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 10 = admission_power_Cbridge1_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_10] <;> ring

def admission_power_Cbridge1_11 (δ p : ℝ) : ℝ := (50521009353307/21000159094850:ℝ)*δ^0*p^0 + (-48854077528557/10500079547425:ℝ)*δ^0*p^1 + (19867376677827421960977543/8820133640180223425930450:ℝ)*δ^0*p^2 + (-153854873002807/52500397737125:ℝ)*δ^1*p^0 + (297708155057114/52500397737125:ℝ)*δ^1*p^1 + (-60564712201908934117067371/22050334100450558564826125:ℝ)*δ^1*p^2
theorem admission_power_Cbridge1_11_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 11 = admission_power_Cbridge1_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_11] <;> ring

def admission_power_Cbridge1_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge1_12_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 12 = admission_power_Cbridge1_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_12] <;> ring

def admission_power_Cbridge1_13 (δ p : ℝ) : ℝ := (98161326569998103/2000000000000000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge1_13_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 13 = admission_power_Cbridge1_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_13] <;> ring

def admission_power_Cbridge1_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cbridge1_14_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 14 = admission_power_Cbridge1_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_14] <;> ring

def admission_power_Cbridge2_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-1200003181897/400003181897:ℝ)*δ^0*p^1
theorem admission_power_Cbridge2_00_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 0 = admission_power_Cbridge2_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_00] <;> ring

def admission_power_Cbridge2_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-800000000000/400003181897:ℝ)*δ^0*p^1
theorem admission_power_Cbridge2_01_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 1 = admission_power_Cbridge2_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_01] <;> ring

def admission_power_Cbridge2_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-8814676867413/9090981406750:ℝ)*δ^0*p^1
theorem admission_power_Cbridge2_02_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 2 = admission_power_Cbridge2_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_02] <;> ring

def admission_power_Cbridge2_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-6000015909485/2400019091382:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (800000000000/400003181897:ℝ)*δ^1*p^2
theorem admission_power_Cbridge2_03_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 3 = admission_power_Cbridge2_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_03] <;> ring

def admission_power_Cbridge2_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-17905658274163/9090981406750:ℝ)*δ^1*p^1 + (8814676867413/9090981406750:ℝ)*δ^1*p^2
theorem admission_power_Cbridge2_04_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 4 = admission_power_Cbridge2_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_04] <;> ring

def admission_power_Cbridge2_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-999602650520201/1600012727588000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (625352880824647/363639256270000:ℝ)*δ^1*p^1 + (-46981445541543/100000795474250:ℝ)*δ^1*p^2
theorem admission_power_Cbridge2_05_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 5 = admission_power_Cbridge2_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_05] <;> ring

def admission_power_Cbridge2_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-3337316932178477/4440035319056700:ℝ)*δ^0*p^1 + (734927130636417120750389873/1776028255357741600556559900:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-21862772160937523/3700029432547250:ℝ)*δ^1*p^1 + (849558558538841287170897557/134547595102859212163375750:ℝ)*δ^1*p^2 + (-13440035637246400000000000/5920094184525805335188533:ℝ)*δ^1*p^3
theorem admission_power_Cbridge2_06_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 6 = admission_power_Cbridge2_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_06] <;> ring

def admission_power_Cbridge2_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-590885132098879/120000954569100:ℝ)*δ^0*p^1 + (3525880096096493463607487/1454568595706586077441900:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (590885132098879/100000795474250:ℝ)*δ^1*p^1 + (-10577640288289480390822461/3636421489266465193604750:ℝ)*δ^1*p^2
theorem admission_power_Cbridge2_07_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 7 = admission_power_Cbridge2_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_07] <;> ring

def admission_power_Cbridge2_08 (δ p : ℝ) : ℝ := (-617799587765694791/1600000000000000000:ℝ)*δ^0*p^0 + (814293141890456662100958398527/960007636552800000000000000000:ℝ)*δ^0*p^1 + (-118296955364764378911068904809513933096191/256004072844359149629774400000000000000000:ℝ)*δ^0*p^2 + (4617799587765694791/4000000000000000000:ℝ)*δ^1*p^0 + (-2400014193594448362366347200491/800006363794000000000000000000:ℝ)*δ^1*p^1 + (3912797710475678613166347200491/1600012727588000000000000000000:ℝ)*δ^1*p^2 + (-479956130529856131947288620491/800012727638622342593045000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge2_08_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 8 = admission_power_Cbridge2_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_08] <;> ring

def admission_power_Cbridge2_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-3752335043126449309/2400019091382000000:ℝ)*δ^0*p^1 + (1573869861279640391456632566391/1920030546332693622223308000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (6000033966753656897/2000015909485000000:ℝ)*δ^1*p^1 + (-733217738386710627/363639256270000000:ℝ)*δ^1*p^2 + (12553791937157422239047071/40000636381931117129652250:ℝ)*δ^1*p^3
theorem admission_power_Cbridge2_09_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 9 = admission_power_Cbridge2_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_09] <;> ring

def admission_power_Cbridge2_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-553847961765617/480003818276400:ℝ)*δ^1*p^1 + (6580116484424/10000079547425:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (74349927518677/36363925627000:ℝ)*δ^2*p^1 + (-64980746634999/50000397737125:ℝ)*δ^2*p^2 + (48000000000/400003181897:ℝ)*δ^2*p^3
theorem admission_power_Cbridge2_10_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 10 = admission_power_Cbridge2_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_10] <;> ring

def admission_power_Cbridge2_11 (δ p : ℝ) : ℝ := (290885927573129/120000954569100:ℝ)*δ^0*p^0 + (-8814676867413/1818196281350:ℝ)*δ^0*p^1 + (3525880096096493463607487/1454568595706586077441900:ℝ)*δ^0*p^2 + (-26996639680913/9090981406750:ℝ)*δ^1*p^0 + (296961445541543/50000397737125:ℝ)*δ^1*p^1 + (-981693438633756328107049/330583771751496835782250:ℝ)*δ^1*p^2
theorem admission_power_Cbridge2_11_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 11 = admission_power_Cbridge2_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_11] <;> ring

def admission_power_Cbridge2_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge2_12_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 12 = admission_power_Cbridge2_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_12] <;> ring

def admission_power_Cbridge2_13 (δ p : ℝ) : ℝ := (89227156258578103/2000000000000000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge2_13_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 13 = admission_power_Cbridge2_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_13] <;> ring

def admission_power_Cbridge2_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cbridge2_14_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 14 = admission_power_Cbridge2_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_14] <;> ring

def admission_power_Cbridge3_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-1180003181897/380003181897:ℝ)*δ^0*p^1
theorem admission_power_Cbridge3_00_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 0 = admission_power_Cbridge3_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_00] <;> ring

def admission_power_Cbridge3_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-800000000000/380003181897:ℝ)*δ^0*p^1
theorem admission_power_Cbridge3_01_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 1 = admission_power_Cbridge3_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_01] <;> ring

def admission_power_Cbridge3_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-6409094655157/6333386364950:ℝ)*δ^0*p^1
theorem admission_power_Cbridge3_02_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 2 = admission_power_Cbridge3_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_02] <;> ring

def admission_power_Cbridge3_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-5900015909485/2280019091382:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (800000000000/380003181897:ℝ)*δ^1*p^2
theorem admission_power_Cbridge3_03_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 3 = admission_power_Cbridge3_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_03] <;> ring

def admission_power_Cbridge3_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-12742481020107/6333386364950:ℝ)*δ^1*p^1 + (6409094655157/6333386364950:ℝ)*δ^1*p^2
theorem admission_power_Cbridge3_04_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 4 = admission_power_Cbridge3_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_04] <;> ring

def admission_power_Cbridge3_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-982942650520201/1520012727588000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (2231953553501199/1266677272990000:ℝ)*δ^1*p^1 + (-3077094655157/6333386364950:ℝ)*δ^1*p^2
theorem admission_power_Cbridge3_05_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 5 = admission_power_Cbridge3_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_05] <;> ring

def admission_power_Cbridge3_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-638778957290669/843607063811340:ℝ)*δ^0*p^1 + (135219774936692056392722281/320573368519094720111311980:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-4289238861332531/703005886509450:ℝ)*δ^1*p^1 + (597251433929936733177776773/89048157921970755586475550:ℝ)*δ^1*p^2 + (-13216035637246400000000000/5342889475318245335188533:ℝ)*δ^1*p^3
theorem admission_power_Cbridge3_06_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 6 = admission_power_Cbridge3_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_06] <;> ring

def admission_power_Cbridge3_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-116682010991263/22800190913820:ℝ)*δ^0*p^1 + (7562752086164315960092829/2888048365036889370372180:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (116682010991263/19000159094850:ℝ)*δ^1*p^1 + (-7562752086164315960092829/2406706970864074475310150:ℝ)*δ^1*p^2
theorem admission_power_Cbridge3_07_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 7 = admission_power_Cbridge3_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_07] <;> ring

def admission_power_Cbridge3_08 (δ p : ℝ) : ℝ := (-628291984914414791/1600000000000000000:ℝ)*δ^0*p^0 + (794118829296871376601680238527/912007636552800000000000000000:ℝ)*δ^0*p^1 + (-333095670976521333006974945406135309448573/693131607608853448889323200000000000000000:ℝ)*δ^0*p^2 + (4628291984914414791/4000000000000000000:ℝ)*δ^1*p^0 + (-2310869462365302124199439920491/760006363794000000000000000000:ℝ)*δ^1*p^1 + (1270486956129014791666479973497/506670909196000000000000000000:ℝ)*δ^1*p^2 + (-448359202866830995827288620491/722012091259222342593045000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge3_08_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 8 = admission_power_Cbridge3_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_08] <;> ring

def admission_power_Cbridge3_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-3642336645977729309/2280019091382000000:ℝ)*δ^0*p^1 + (1484509833560368463242818006391/1732829019022133622223308000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (5786533946753656897/1900015909485000000:ℝ)*δ^1*p^1 + (-2617630672183752299/1266677272990000000:ℝ)*δ^1*p^2 + (2274205931687575468278487/7220120912592223425930450:ℝ)*δ^1*p^3
theorem admission_power_Cbridge3_09_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 9 = admission_power_Cbridge3_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_09] <;> ring

def admission_power_Cbridge3_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-11929952420197/10133418183920:ℝ)*δ^1*p^1 + (261454573663/380003181897:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (52869939989913/25333545459800:ℝ)*δ^2*p^1 + (-4294548918527/3166693182475:ℝ)*δ^2*p^2 + (16000000000/126667727299:ℝ)*δ^2*p^3
theorem admission_power_Cbridge3_10_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 10 = admission_power_Cbridge3_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_10] <;> ring

def admission_power_Cbridge3_11 (δ p : ℝ) : ℝ := (55682170086113/22800190913820:ℝ)*δ^0*p^0 + (-6409094655157/1266677272990:ℝ)*δ^0*p^1 + (7562752086164315960092829/2888048365036889370372180:ℝ)*δ^0*p^2 + (-19075867385057/6333386364950:ℝ)*δ^1*p^0 + (59227283965471/9500079547425:ℝ)*δ^1*p^1 + (-2586169484682294679969057/802235656954691491770050:ℝ)*δ^1*p^2
theorem admission_power_Cbridge3_11_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 11 = admission_power_Cbridge3_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_11] <;> ring

def admission_power_Cbridge3_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge3_12_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 12 = admission_power_Cbridge3_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_12] <;> ring

def admission_power_Cbridge3_13 (δ p : ℝ) : ℝ := (78726661974818103/2000000000000000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge3_13_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 13 = admission_power_Cbridge3_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_13] <;> ring

def admission_power_Cbridge3_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cbridge3_14_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 14 = admission_power_Cbridge3_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_14] <;> ring

def admission_power_Cbridge4_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-1160003181897/360003181897:ℝ)*δ^0*p^1
theorem admission_power_Cbridge4_00_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 0 = admission_power_Cbridge4_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_00] <;> ring

def admission_power_Cbridge4_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-800000000000/360003181897:ℝ)*δ^0*p^1
theorem admission_power_Cbridge4_01_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 1 = admission_power_Cbridge4_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_01] <;> ring

def admission_power_Cbridge4_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-47621575591377/45000397737125:ℝ)*δ^0*p^1
theorem admission_power_Cbridge4_02_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 2 = admission_power_Cbridge4_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_02] <;> ring

def admission_power_Cbridge4_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-1933338636495/720006363794:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (800000000000/360003181897:ℝ)*δ^1*p^2
theorem admission_power_Cbridge4_03_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 3 = admission_power_Cbridge4_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_03] <;> ring

def admission_power_Cbridge4_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-92621973328502/45000397737125:ℝ)*δ^1*p^1 + (47621575591377/45000397737125:ℝ)*δ^1*p^2
theorem admission_power_Cbridge4_04_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 4 = admission_power_Cbridge4_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_04] <;> ring

def admission_power_Cbridge4_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-966282650520201/1440012727588000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (6510109914719557/3600031818970000:ℝ)*δ^1*p^1 + (-22631575591377/45000397737125:ℝ)*δ^1*p^2
theorem admission_power_Cbridge4_05_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 5 = admission_power_Cbridge4_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_05] <;> ring

def admission_power_Cbridge4_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-254837300500338/333002943254725:ℝ)*δ^0*p^1 + (103629762546847376435528499/239764238305534266759426650:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-10511020743555972/1665014716273625:ℝ)*δ^1*p^1 + (4286745458710133510508546003/599410595763835666898566625:ℝ)*δ^1*p^2 + (-12992035637246400000000000/4795284766110685335188533:ℝ)*δ^1*p^3
theorem admission_power_Cbridge4_06_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 6 = admission_power_Cbridge4_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_06] <;> ring

def admission_power_Cbridge4_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-47977520751876/9000079547425:ℝ)*δ^0*p^1 + (18413726404315276491900723/6480114548798223425930450:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (287865124511256/45000397737125:ℝ)*δ^1*p^1 + (-55241179212945829475702169/16200286371995558564826125:ℝ)*δ^1*p^2
theorem admission_power_Cbridge4_07_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 7 = admission_power_Cbridge4_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_07] <;> ring

def admission_power_Cbridge4_08 (δ p : ℝ) : ℝ := (-634689806238354791/1600000000000000000:ℝ)*δ^0*p^0 + (256804310053995319320798139509/288002545517600000000000000000:ℝ)*δ^0*p^1 + (-103702179129269341896947232906692569756191/207363665561543149629774400000000000000000:ℝ)*δ^0*p^2 + (4634689806238354791/4000000000000000000:ℝ)*δ^1*p^0 + (-2221810039763314597079201860491/720006363794000000000000000000:ℝ)*δ^1*p^1 + (3711847165255480847879201860491/1440012727588000000000000000000:ℝ)*δ^1*p^2 + (-417562194403805859707288620491/648011454879822342593045000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge4_08_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 8 = admission_power_Cbridge4_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_08] <;> ring

def admission_power_Cbridge4_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-1178810941551263103/720006363794000000:ℝ)*δ^0*p^1 + (466818748185079319040780628797/518409163903857874074436000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (5573033926753656897/1800015909485000000:ℝ)*δ^1*p^1 + (-7632199759199136897/3600031818970000000:ℝ)*δ^1*p^2 + (5071053195932398445702169/16200286371995558564826125:ℝ)*δ^1*p^3
theorem admission_power_Cbridge4_09_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 9 = admission_power_Cbridge4_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_09] <;> ring

def admission_power_Cbridge4_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-519574784330461/432003818276400:ℝ)*δ^1*p^1 + (25947701151433/36000318189700:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (767976025270291/360003181897000:ℝ)*δ^2*p^1 + (-127643198911209/90000795474250:ℝ)*δ^2*p^2 + (48000000000/360003181897:ℝ)*δ^2*p^3
theorem admission_power_Cbridge4_10_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 10 = admission_power_Cbridge4_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_10] <;> ring

def admission_power_Cbridge4_11 (δ p : ℝ) : ℝ := (44288507416127/18000159094850:ℝ)*δ^0*p^0 + (-47621575591377/9000079547425:ℝ)*δ^0*p^1 + (18413726404315276491900723/6480114548798223425930450:ℝ)*δ^0*p^2 + (-137622371065627/45000397737125:ℝ)*δ^1*p^0 + (295243151182754/45000397737125:ℝ)*δ^1*p^1 + (-56953659922957370524297831/16200286371995558564826125:ℝ)*δ^1*p^2
theorem admission_power_Cbridge4_11_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 11 = admission_power_Cbridge4_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_11] <;> ring

def admission_power_Cbridge4_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge4_12_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 12 = admission_power_Cbridge4_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_12] <;> ring

def admission_power_Cbridge4_13 (δ p : ℝ) : ℝ := (66861309082798103/2000000000000000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge4_13_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 13 = admission_power_Cbridge4_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_13] <;> ring

def admission_power_Cbridge4_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cbridge4_14_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 14 = admission_power_Cbridge4_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_14] <;> ring

def admission_power_Cbridge5_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-1170003181897/370003181897:ℝ)*δ^0*p^1
theorem admission_power_Cbridge5_00_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 0 = admission_power_Cbridge5_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_00] <;> ring

def admission_power_Cbridge5_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-800000000000/370003181897:ℝ)*δ^0*p^1
theorem admission_power_Cbridge5_01_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 1 = admission_power_Cbridge5_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_01] <;> ring

def admission_power_Cbridge5_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-47848933494537/46250397737125:ℝ)*δ^0*p^1
theorem admission_power_Cbridge5_02_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 2 = admission_power_Cbridge5_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_02] <;> ring

def admission_power_Cbridge5_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-5850015909485/2220019091382:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (800000000000/370003181897:ℝ)*δ^1*p^2
theorem admission_power_Cbridge5_03_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 3 = admission_power_Cbridge5_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_03] <;> ring

def admission_power_Cbridge5_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-94099331231662/46250397737125:ℝ)*δ^1*p^1 + (47848933494537/46250397737125:ℝ)*δ^1*p^2
theorem admission_power_Cbridge5_04_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 4 = admission_power_Cbridge5_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_04] <;> ring

def admission_power_Cbridge5_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-974612650520201/1480012727588000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (6603308546972357/3700031818970000:ℝ)*δ^1*p^1 + (-22858933494537/46250397737125:ℝ)*δ^1*p^2
theorem admission_power_Cbridge5_05_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 5 = admission_power_Cbridge5_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_05] <;> ring

def admission_power_Cbridge5_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-781268537875634/1026758829764175:ℝ)*δ^0*p^1 + (324202065643442329636088257/759808068107169800278279950:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-10617507470806732/1711264716273625:ℝ)*δ^1*p^1 + (4382982903440023310179043243/633173390089308166898566625:ℝ)*δ^1*p^2 + (-13104035637246400000000000/5065387120714465335188533:ℝ)*δ^1*p^3
theorem admission_power_Cbridge5_06_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 6 = admission_power_Cbridge5_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_06] <;> ring

def admission_power_Cbridge5_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-144898599110368/27750238642275:ℝ)*δ^0*p^1 + (18661134812995409822265563/6845117730695223425930450:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (289797198220736/46250397737125:ℝ)*δ^1*p^1 + (-55983404438986229466796689/17112794326738058564826125:ℝ)*δ^1*p^2
theorem admission_power_Cbridge5_07_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 7 = admission_power_Cbridge5_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_07] <;> ring

def admission_power_Cbridge5_08 (δ p : ℝ) : ℝ := (-631975784617554791/1600000000000000000:ℝ)*δ^0*p^0 + (782671234940616252713736818527/888007636552800000000000000000:ℝ)*δ^0*p^1 + (-107371034831849486905342407417514628956191/219043767382247149629774400000000000000000:ℝ)*δ^0*p^2 + (4631975784617554791/4000000000000000000:ℝ)*δ^1*p^0 + (-2266333936404891165495421060491/740006363794000000000000000000:ℝ)*δ^1*p^1 + (3761454246545377416295421060491/1480012727588000000000000000000:ℝ)*δ^1*p^2 + (-432860708735318427767288620491/684511773069522342593045000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge5_08_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 8 = admission_power_Cbridge5_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_08] <;> ring

def admission_power_Cbridge5_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-3588899846274589309/2220019091382000000:ℝ)*δ^0*p^1 + (1441850978406032819894780286391/1642828255366853622223308000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (5679783936753656897/1850015909485000000:ℝ)*δ^1*p^1 + (-7743515665957536897/3700031818970000000:ℝ)*δ^1*p^2 + (5380778521972798436796689/17112794326738058564826125:ℝ)*δ^1*p^3
theorem admission_power_Cbridge5_09_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 9 = admission_power_Cbridge5_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_09] <;> ring

def admission_power_Cbridge5_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-528243647555741/444003818276400:ℝ)*δ^1*p^1 + (26049273086873/37000318189700:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (780544888495571/370003181897000:ℝ)*δ^2*p^1 + (-128247914717529/92500795474250:ℝ)*δ^2*p^2 + (48000000000/370003181897:ℝ)*δ^2*p^3
theorem admission_power_Cbridge5_10_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 10 = admission_power_Cbridge5_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_10] <;> ring

def admission_power_Cbridge5_11 (δ p : ℝ) : ℝ := (136047595957861/55500477284550:ℝ)*δ^0*p^0 + (-47848933494537/9250079547425:ℝ)*δ^0*p^1 + (18661134812995409822265563/6845117730695223425930450:ℝ)*δ^0*p^2 + (-140349728968787/46250397737125:ℝ)*δ^1*p^0 + (295697866989074/46250397737125:ℝ)*δ^1*p^1 + (-57575207341972970533203311/17112794326738058564826125:ℝ)*δ^1*p^2
theorem admission_power_Cbridge5_11_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 11 = admission_power_Cbridge5_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_11] <;> ring

def admission_power_Cbridge5_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge5_12_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 12 = admission_power_Cbridge5_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_12] <;> ring

def admission_power_Cbridge5_13 (δ p : ℝ) : ℝ := (72955615209198103/2000000000000000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge5_13_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 13 = admission_power_Cbridge5_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_13] <;> ring

def admission_power_Cbridge5_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cbridge5_14_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 14 = admission_power_Cbridge5_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_14] <;> ring

def admission_power_Cbridge6_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-1150003181897/350003181897:ℝ)*δ^0*p^1
theorem admission_power_Cbridge6_00_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 0 = admission_power_Cbridge6_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_00] <;> ring

def admission_power_Cbridge6_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-800000000000/350003181897:ℝ)*δ^0*p^1
theorem admission_power_Cbridge6_01_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 1 = admission_power_Cbridge6_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_01] <;> ring

def admission_power_Cbridge6_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-94772395367213/87500795474250:ℝ)*δ^0*p^1
theorem admission_power_Cbridge6_02_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 2 = admission_power_Cbridge6_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_02] <;> ring

def admission_power_Cbridge6_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-5750015909485/2100019091382:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (800000000000/350003181897:ℝ)*δ^1*p^2
theorem admission_power_Cbridge6_03_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 3 = admission_power_Cbridge6_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_03] <;> ring

def admission_power_Cbridge6_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-182273190841463/87500795474250:ℝ)*δ^1*p^1 + (94772395367213/87500795474250:ℝ)*δ^1*p^2
theorem admission_power_Cbridge6_04_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 4 = admission_power_Cbridge6_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_04] <;> ring

def admission_power_Cbridge6_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-957952650520201/1400012727588000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (6416269682097917/3500031818970000:ℝ)*δ^1*p^1 + (-44792395367213/87500795474250:ℝ)*δ^1*p^2
theorem admission_power_Cbridge6_05_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 5 = admission_power_Cbridge6_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_05] <;> ring

def admission_power_Cbridge6_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-2992801501529107/3885035319056700:ℝ)*δ^0*p^1 + (596199033859353925104238243/1359774723452071600556559900:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-20807287591586893/3237529432547250:ℝ)*δ^1*p^1 + (8381370013376417354526024757/1133145602876726333797133250:ℝ)*δ^1*p^2 + (-12880035637246400000000000/4532582411506905335188533:ℝ)*δ^1*p^3
theorem admission_power_Cbridge6_06_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 6 = admission_power_Cbridge6_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_06] <;> ring

def admission_power_Cbridge6_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-571817981575889/105000954569100:ℝ)*δ^0*p^1 + (108988556228295451748943061/36750668201407340555582700:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (571817981575889/87500795474250:ℝ)*δ^1*p^1 + (-108988556228295451748943061/30625556834506117129652250:ℝ)*δ^1*p^2
theorem admission_power_Cbridge6_07_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 7 = admission_power_Cbridge6_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_07] <;> ring

def admission_power_Cbridge6_08 (δ p : ℝ) : ℝ := (-636441427305894791/1600000000000000000:ℝ)*δ^0*p^0 + (757378541473735229994717798527/840007636552800000000000000000:ℝ)*δ^0*p^1 + (-300092339954220863070072372936209659888573/588010691222517448889323200000000000000000:ℝ)*δ^0*p^2 + (4636441427305894791/4000000000000000000:ℝ)*δ^1*p^0 + (-2177288197610742173068427400491/700006363794000000000000000000:ℝ)*δ^1*p^1 + (3662627098675892423868427400491/1400012727588000000000000000000:ℝ)*δ^1*p^2 + (-402463659872293291647288620491/612511136690122342593045000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge6_08_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 8 = admission_power_Cbridge6_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_08] <;> ring

def admission_power_Cbridge6_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-3484928203586249309/2100019091382000000:ℝ)*δ^0*p^1 + (453433526775019794386930988797/490008909352097874074436000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (5466283916753656897/1750015909485000000:ℝ)*δ^1*p^1 + (-2506319683778072299/1166677272990000000:ℝ)*δ^1*p^2 + (3171101331422863229647687/10208518944835372376550750:ℝ)*δ^1*p^3
theorem admission_power_Cbridge6_09_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 9 = admission_power_Cbridge6_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_09] <;> ring

def admission_power_Cbridge6_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-510841761068297/420003818276400:ℝ)*δ^1*p^1 + (38761173819379/52500477284550:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (755343002008127/350003181897000:ℝ)*δ^2*p^1 + (-63511221547834/43750397737125:ℝ)*δ^2*p^2 + (16000000000/116667727299:ℝ)*δ^2*p^3
theorem admission_power_Cbridge6_10_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 10 = admission_power_Cbridge6_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_10] <;> ring

def admission_power_Cbridge6_11 (δ p : ℝ) : ℝ := (259318777050139/105000954569100:ℝ)*δ^0*p^0 + (-94772395367213/17500159094850:ℝ)*δ^0*p^1 + (108988556228295451748943061/36750668201407340555582700:ℝ)*δ^0*p^2 + (-269773986315713/87500795474250:ℝ)*δ^1*p^0 + (294772395367213/43750397737125:ℝ)*δ^1*p^1 + (-112647912738645348251056939/30625556834506117129652250:ℝ)*δ^1*p^2
theorem admission_power_Cbridge6_11_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 11 = admission_power_Cbridge6_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_11] <;> ring

def admission_power_Cbridge6_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge6_12_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 12 = admission_power_Cbridge6_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_12] <;> ring

def admission_power_Cbridge6_13 (δ p : ℝ) : ℝ := (60446202771978103/2000000000000000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge6_13_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 13 = admission_power_Cbridge6_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_13] <;> ring

def admission_power_Cbridge6_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cbridge6_14_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 14 = admission_power_Cbridge6_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_14] <;> ring

end
end Qrh.JointDetector.RestartReturn
