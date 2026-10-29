/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/restart_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
A finite count-source bank and physical source remain explicit; no missing estimate is asserted. -/
import Candidate.Local.Qrh.JointDetector.CurvedRestartReturn.Formulas
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unnecessarySeqFocus false
namespace Qrh.JointDetector.CurvedRestartReturn
open QRH.Record1252270103Return
noncomputable section

def admission_power_Cnew_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-5714560586289/1714560586289:ℝ)*δ^0*p^1
theorem admission_power_Cnew_00_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 0 = admission_power_Cnew_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_00] <;> ring

def admission_power_Cnew_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-4000000000000/1714560586289:ℝ)*δ^0*p^1
theorem admission_power_Cnew_01_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 1 = admission_power_Cnew_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_01] <;> ring

def admission_power_Cnew_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-47214537432223/42864014657225:ℝ)*δ^0*p^1
theorem admission_power_Cnew_02_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 2 = admission_power_Cnew_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_02] <;> ring

def admission_power_Cnew_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-9524267643815/3429121172578:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (4000000000000/1714560586289:ℝ)*δ^1*p^2
theorem admission_power_Cnew_03_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 3 = admission_power_Cnew_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_03] <;> ring

def admission_power_Cnew_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-90078552089448/42864014657225:ℝ)*δ^1*p^1 + (47214537432223/42864014657225:ℝ)*δ^1*p^2
theorem admission_power_Cnew_04_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 4 = admission_power_Cnew_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_04] <;> ring

def admission_power_Cnew_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-4760228968378737/6858242345156000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (31746733930642989/17145605862890000:ℝ)*δ^1*p^1 + (-22224537432223/42864014657225:ℝ)*δ^1*p^2
theorem admission_power_Cnew_05_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 5 = admission_power_Cnew_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_05] <;> ring

def admission_power_Cnew_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-245632505652137/317193708463465:ℝ)*δ^0*p^1 + (482229519585634755465061937/1087695661500601383472862770:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-10326974607696378/1585968542317325:ℝ)*δ^1*p^1 + (20613422968909671323958878889/2719239153751503458682156925:ℝ)*δ^1*p^2 + (-320015392832184000000000000/108769566150060138347286277:ℝ)*δ^1*p^3
theorem admission_power_Cnew_06_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 6 = admission_power_Cnew_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_06] <;> ring

def admission_power_Cnew_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-47417937825649/8572802931445:ℝ)*δ^0*p^1 + (89936778236682734493530149/29397180040556794147915210:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (284507626953894/42864014657225:ℝ)*δ^1*p^1 + (-269810334710048203480590447/73492950101391985369788025:ℝ)*δ^1*p^2
theorem admission_power_Cnew_07_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 7 = admission_power_Cnew_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_07] <;> ring

def admission_power_Cnew_08 (δ p : ℝ) : ℝ := (-3134129394735775567/8000000000000000000:ℝ)*δ^0*p^0 + (6132777751903087444799547133621/6858242345156000000000000000000:ℝ)*δ^0*p^1 + (-11992001707567253143710608730662303727840823/23517744032445435318332168000000000000000000:ℝ)*δ^0*p^2 + (23134129394735775567/20000000000000000000:ℝ)*δ^1*p^0 + (-53637948365719263689200452866379/17145605862890000000000000000000:ℝ)*δ^1*p^1 + (91002455971749810287200452866379/34291211725780000000000000000000:ℝ)*δ^1*p^2 + (-9894938929587353251318542266379/14698590020278397073957605000000:ℝ)*δ^1*p^3
theorem admission_power_Cnew_08_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 8 = admission_power_Cnew_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_08] <;> ring

def admission_power_Cnew_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-5748293690879738711/3429121172578000000:ℝ)*δ^0*p^1 + (11104636704306079236352578244493/11758872016222717659166084000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (26952933973195661289/8572802931445000000:ℝ)*δ^1*p^1 + (-37187593960418261289/17145605862890000000:ℝ)*δ^1*p^2 + (22655646498654816370590447/73492950101391985369788025:ℝ)*δ^1*p^3
theorem admission_power_Cnew_09_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 9 = admission_power_Cnew_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_09] <;> ring

def admission_power_Cnew_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-168203699926459/137164846903120:ℝ)*δ^1*p^1 + (77285393105579/102873635177340:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (746346825509919/342912117257800:ℝ)*δ^2*p^1 + (-126572756623313/85728029314450:ℝ)*δ^2*p^2 + (240000000000/1714560586289:ℝ)*δ^2*p^3
theorem admission_power_Cnew_10_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 10 = admission_power_Cnew_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_10] <;> ring

def admission_power_Cnew_11 (δ p : ℝ) : ℝ := (42457213870373/17145605862890:ℝ)*δ^0*p^0 + (-47214537432223/8572802931445:ℝ)*δ^0*p^1 + (89936778236682734493530149/29397180040556794147915210:ℝ)*δ^0*p^2 + (-132942566746673/42864014657225:ℝ)*δ^1*p^0 + (294429074864446/42864014657225:ℝ)*δ^1*p^1 + (-279362023376635796519409553/73492950101391985369788025:ℝ)*δ^1*p^2
theorem admission_power_Cnew_11_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 11 = admission_power_Cnew_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_11] <;> ring

def admission_power_Cnew_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cnew_12_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 12 = admission_power_Cnew_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_12] <;> ring

def admission_power_Cnew_13 (δ p : ℝ) : ℝ := (278535595997313711/10000000000000000000:ℝ)*δ^0*p^0
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

def admission_power_Pnew_09 (δ p : ℝ) : ℝ := (5419246950466018867/8000000000000000000:ℝ)*δ^0*p^0 + (-11699252950466018867/12000000000000000000:ℝ)*δ^0*p^1 + (1997695438940668763/8000000000000000000:ℝ)*δ^0*p^2 + (-25419246950466018867/20000000000000000000:ℝ)*δ^1*p^0 + (21526917683177993711/10000000000000000000:ℝ)*δ^1*p^1 + (-18966905683177993711/20000000000000000000:ℝ)*δ^1*p^2 + (619999/5000000:ℝ)*δ^1*p^3
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

def admission_power_Pnew_13 (δ p : ℝ) : ℝ := (522025336013313711/10000000000000000000:ℝ)*δ^0*p^0
theorem admission_power_Pnew_13_expanded (δ p : ℝ) : admissionGuard .Pnew δ p 13 = admission_power_Pnew_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pnew_13] <;> ring

def admission_power_Pnew_14 (δ p : ℝ) : ℝ := (479997/2000000:ℝ)*δ^0*p^0 + (-159999/1000000:ℝ)*δ^0*p^1 + (53333/2000000:ℝ)*δ^0*p^2 + (-479997/5000000:ℝ)*δ^1*p^0 + (-159999/2500000:ℝ)*δ^1*p^1 + (159999/5000000:ℝ)*δ^1*p^2
theorem admission_power_Pnew_14_expanded (δ p : ℝ) : admissionGuard .Pnew δ p 14 = admission_power_Pnew_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pnew_14] <;> ring

def admission_power_Cphys_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-6184210586289/2184210586289:ℝ)*δ^0*p^1
theorem admission_power_Cphys_00_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 0 = admission_power_Cphys_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_00] <;> ring

def admission_power_Cphys_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-4000000000000/2184210586289:ℝ)*δ^0*p^1
theorem admission_power_Cphys_01_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 1 = admission_power_Cphys_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_01] <;> ring

def admission_power_Cphys_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-49136463480553/54605264657225:ℝ)*δ^0*p^1
theorem admission_power_Cphys_02_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 2 = admission_power_Cphys_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_02] <;> ring

def admission_power_Cphys_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-10307017643815/4368421172578:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (4000000000000/2184210586289:ℝ)*δ^1*p^2
theorem admission_power_Cphys_03_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 3 = admission_power_Cphys_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_03] <;> ring

def admission_power_Cphys_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-103741728137778/54605264657225:ℝ)*δ^1*p^1 + (49136463480553/54605264657225:ℝ)*δ^1*p^2
theorem admission_power_Cphys_04_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 4 = admission_power_Cphys_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_04] <;> ring

def admission_power_Cphys_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-5151447418378737/8736842345156000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (36038348999974989/21842105862890000:ℝ)*δ^1*p^1 + (-24146463480553/54605264657225:ℝ)*δ^1*p^2
theorem admission_power_Cphys_05_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 5 = admission_power_Cphys_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_05] <;> ring

def admission_power_Cphys_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-302049998758032/404078958463465:ℝ)*δ^0*p^1 + (714120803055765293339777707/1765187077545066732472862770:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-11303489649061008/2020394792317325:ℝ)*δ^1*p^1 + (25144549635340160100334731579/4412967693862666831182156925:ℝ)*δ^1*p^2 + (-346315792832184000000000000/176518707754506673247286277:ℝ)*δ^1*p^3
theorem admission_power_Cphys_06_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 6 = admission_power_Cphys_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_06] <;> ring

def admission_power_Cphys_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-50335775849814/10921052931445:ℝ)*δ^0*p^1 + (101290079209746235226645939/47707758852569371147915210:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (302014655098884/54605264657225:ℝ)*δ^1*p^1 + (-303870237629238705679937817/119269397131423427869788025:ℝ)*δ^1*p^2
theorem admission_power_Cphys_07_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 7 = admission_power_Cphys_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_07] <;> ring

def admission_power_Cphys_08 (δ p : ℝ) : ℝ := (-2929914145272445567/8000000000000000000:ℝ)*δ^0*p^0 + (6999185253446048305844636343621/8736842345156000000000000000000:ℝ)*δ^0*p^1 + (-16405958579986628076149205635976807225070823/38166207082055496918332168000000000000000000:ℝ)*δ^0*p^2 + (22929914145272445567/20000000000000000000:ℝ)*δ^1*p^0 + (-64118339945917642828155363656379/21842105862890000000000000000000:ℝ)*δ^1*p^1 + (102624261564720169426155363656379/43684211725780000000000000000000:ℝ)*δ^1*p^2 + (-13506241592550492830142927056379/23853879426284685573957605000000:ℝ)*δ^1*p^3
theorem admission_power_Cphys_08_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 8 = admission_power_Cphys_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_08] <;> ring

def admission_power_Cphys_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-6612394261563738711/4368421172578000000:ℝ)*δ^0*p^1 + (14619719564393198393520362244493/19083103541027748459166084000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (31966448192845661289/10921052931445000000:ℝ)*δ^1*p^1 + (-42159169438064261289/21842105862890000000:ℝ)*δ^1*p^2 + (36403191614345318569937817/119269397131423427869788025:ℝ)*δ^1*p^3
theorem admission_power_Cphys_09_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 9 = admission_power_Cphys_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_09] <;> ring

def admission_power_Cphys_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-194776186055339/174736846903120:ℝ)*δ^1*p^1 + (79720295202239/131052635177340:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (862696983896559/436842117257800:ℝ)*δ^2*p^1 + (-131825558719973/109210529314450:ℝ)*δ^2*p^2 + (240000000000/2184210586289:ℝ)*δ^2*p^3
theorem admission_power_Cphys_10_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 10 = admission_power_Cphys_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_10] <;> ring

def admission_power_Cphys_11 (δ p : ℝ) : ℝ := (52206639918703/21842105862890:ℝ)*δ^0*p^0 + (-49136463480553/10921052931445:ℝ)*δ^0*p^1 + (101290079209746235226645939/47707758852569371147915210:ℝ)*δ^0*p^2 + (-158346992795003/54605264657225:ℝ)*δ^1*p^0 + (298272926961106/54605264657225:ℝ)*δ^1*p^1 + (-307642528844085294320062183/119269397131423427869788025:ℝ)*δ^1*p^2
theorem admission_power_Cphys_11_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 11 = admission_power_Cphys_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_11] <;> ring

def admission_power_Cphys_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cphys_12_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 12 = admission_power_Cphys_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_12] <;> ring

def admission_power_Cphys_13 (δ p : ℝ) : ℝ := (522025336013313711/10000000000000000000:ℝ)*δ^0*p^0
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

def admission_power_Pwide_09 (δ p : ℝ) : ℝ := (3584510057983258867/8000000000000000000:ℝ)*δ^0*p^0 + (-8184516057983258867/12000000000000000000:ℝ)*δ^0*p^1 + (1420502450887028763/8000000000000000000:ℝ)*δ^0*p^2 + (-23584510057983258867/20000000000000000000:ℝ)*δ^1*p^0 + (22138496647338913711/10000000000000000000:ℝ)*δ^1*p^1 + (-22938484647338913711/20000000000000000000:ℝ)*δ^1*p^2 + (899999/5000000:ℝ)*δ^1*p^3
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

def admission_power_Pwide_13 (δ p : ℝ) : ℝ := (522025336013313711/10000000000000000000:ℝ)*δ^0*p^0
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

def admission_power_Pcount_09 (δ p : ℝ) : ℝ := (3134117394735775567/8000000000000000000:ℝ)*δ^0*p^0 + (-7074723394735775567/12000000000000000000:ℝ)*δ^0*p^1 + (1223925488303975063/8000000000000000000:ℝ)*δ^0*p^2 + (-23134117394735775567/20000000000000000000:ℝ)*δ^1*p^0 + (22288627535088074811/10000000000000000000:ℝ)*δ^1*p^1 + (-24407415535088074811/20000000000000000000:ℝ)*δ^1*p^2 + (1009899/5000000:ℝ)*δ^1*p^3
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

def admission_power_Pcount_13 (δ p : ℝ) : ℝ := (278535595997313711/10000000000000000000:ℝ)*δ^0*p^0
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

def admission_power_Pcountmid_09 (δ p : ℝ) : ℝ := (3159835803530110567/8000000000000000000:ℝ)*δ^0*p^0 + (-7130441803530110567/12000000000000000000:ℝ)*δ^0*p^1 + (1233449755947790063/8000000000000000000:ℝ)*δ^0*p^2 + (-23159835803530110567/20000000000000000000:ℝ)*δ^1*p^0 + (22280054732156629811/10000000000000000000:ℝ)*δ^1*p^1 + (-24338842732156629811/20000000000000000000:ℝ)*δ^1*p^2 + (1004899/5000000:ℝ)*δ^1*p^3
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

def admission_power_Pcountmid_13 (δ p : ℝ) : ℝ := (278535595997313711/10000000000000000000:ℝ)*δ^0*p^0
theorem admission_power_Pcountmid_13_expanded (δ p : ℝ) : admissionGuard .Pcountmid δ p 13 = admission_power_Pcountmid_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pcountmid_13] <;> ring

def admission_power_Pcountmid_14 (δ p : ℝ) : ℝ := (1057347/2000000:ℝ)*δ^0*p^0 + (-352449/1000000:ℝ)*δ^0*p^1 + (117483/2000000:ℝ)*δ^0*p^2 + (-1057347/5000000:ℝ)*δ^1*p^0 + (-352449/2500000:ℝ)*δ^1*p^1 + (352449/5000000:ℝ)*δ^1*p^2
theorem admission_power_Pcountmid_14_expanded (δ p : ℝ) : admissionGuard .Pcountmid δ p 14 = admission_power_Pcountmid_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pcountmid_14] <;> ring

def admission_power_Cbridge0_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-6200010586289/2200010586289:ℝ)*δ^0*p^1
theorem admission_power_Cbridge0_00_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 0 = admission_power_Cbridge0_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_00] <;> ring

def admission_power_Cbridge0_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-4000000000000/2200010586289:ℝ)*δ^0*p^1
theorem admission_power_Cbridge0_01_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 1 = admission_power_Cbridge0_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_01] <;> ring

def admission_power_Cbridge0_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-49186036982968/55000264657225:ℝ)*δ^0*p^1
theorem admission_power_Cbridge0_02_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 2 = admission_power_Cbridge0_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_02] <;> ring

def admission_power_Cbridge0_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-31000052931445/13200063517734:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (4000000000000/2200010586289:ℝ)*δ^1*p^2
theorem admission_power_Cbridge0_03_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 3 = admission_power_Cbridge0_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_03] <;> ring

def admission_power_Cbridge0_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-104186301640193/55000264657225:ℝ)*δ^1*p^1 + (49186036982968/55000264657225:ℝ)*δ^1*p^2
theorem admission_power_Cbridge0_04_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 4 = admission_power_Cbridge0_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_04] <;> ring

def admission_power_Cbridge0_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-5164608818378737/8800042345156000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (36176694200940989/22000105862890000:ℝ)*δ^1*p^1 + (-24196036982968/55000264657225:ℝ)*δ^1*p^2
theorem admission_power_Cbridge0_05_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 5 = admission_power_Cbridge0_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_05] <;> ring

def admission_power_Cbridge0_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-1825362333780127/2442011750780790:ℝ)*δ^0*p^1 + (361791632471556878974329921/895408617259978860236431385:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-11334667307829073/2035009792317325:ℝ)*δ^1*p^1 + (25297371735846827386508085174/4477043086299894301182156925:ℝ)*δ^1*p^2 + (-347200592832184000000000000/179081723451995772047286277:ℝ)*δ^1*p^3
theorem admission_power_Cbridge0_06_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 6 = admission_power_Cbridge0_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_06] <;> ring

def admission_power_Cbridge0_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-302558375606129/66000317588670:ℝ)*δ^0*p^1 + (152476974996001933193662876/72600698696755042721872815:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (302558375606129/55000264657225:ℝ)*δ^1*p^1 + (-304953949992003866387325752/121001164494591737869788025:ℝ)*δ^1*p^2
theorem admission_power_Cbridge0_07_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 7 = admission_power_Cbridge0_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_07] <;> ring

def admission_power_Cbridge0_08 (δ p : ℝ) : ℝ := (-2912263034121445567/8000000000000000000:ℝ)*δ^0*p^0 + (21032923124939485741883870030863/26400127035468000000000000000000:ℝ)*δ^0*p^1 + (-49620306248593194158435958917801061718212469/116161117914808068354996504000000000000000000:ℝ)*δ^0*p^2 + (22912263034121445567/20000000000000000000:ℝ)*δ^1*p^0 + (-64472752534449195886705376656379/22000105862890000000000000000000:ℝ)*δ^1*p^1 + (103045557225953722484705376656379/44000211725780000000000000000000:ℝ)*δ^1*p^2 + (-13638698875937078030170527056379/24200232898918347573957605000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge0_08_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 8 = admission_power_Cbridge0_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_08] <;> ring

def admission_power_Cbridge0_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-19933443635842216133/13200063517734000000:ℝ)*δ^0*p^1 + (44271949306230954000873512733479/58080558957404034177498252000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (32135113208645661289/11000052931445000000:ℝ)*δ^1*p^1 + (-42308322656762261289/22000105862890000000:ℝ)*δ^1*p^2 + (36803554135110479277325752/121001164494591737869788025:ℝ)*δ^1*p^3
theorem admission_power_Cbridge0_09_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 9 = admission_power_Cbridge0_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_09] <;> ring

def admission_power_Cbridge0_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-586889746185337/528002540709360:ℝ)*δ^1*p^1 + (79772042207069/132000635177340:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (866490571915879/440002117257800:ℝ)*δ^2*p^1 + (-131972105724803/110000529314450:ℝ)*δ^2*p^2 + (240000000000/2200010586289:ℝ)*δ^2*p^3
theorem admission_power_Cbridge0_10_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 10 = admission_power_Cbridge0_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_10] <;> ring

def admission_power_Cbridge0_11 (δ p : ℝ) : ℝ := (78779320131677/33000158794335:ℝ)*δ^0*p^0 + (-49186036982968/11000052931445:ℝ)*δ^0*p^1 + (152476974996001933193662876/72600698696755042721872815:ℝ)*δ^0*p^2 + (-159186566297418/55000264657225:ℝ)*δ^1*p^0 + (298372073965936/55000264657225:ℝ)*δ^1*p^1 + (-308535404500640133612674248/121001164494591737869788025:ℝ)*δ^1*p^2
theorem admission_power_Cbridge0_11_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 11 = admission_power_Cbridge0_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_11] <;> ring

def admission_power_Cbridge0_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge0_12_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 12 = admission_power_Cbridge0_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_12] <;> ring

def admission_power_Cbridge0_13 (δ p : ℝ) : ℝ := (527200020696313711/10000000000000000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge0_13_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 13 = admission_power_Cbridge0_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_13] <;> ring

def admission_power_Cbridge0_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cbridge0_14_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 14 = admission_power_Cbridge0_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_14] <;> ring

def admission_power_Cbridge1_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-6100010586289/2100010586289:ℝ)*δ^0*p^1
theorem admission_power_Cbridge1_00_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 0 = admission_power_Cbridge1_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_00] <;> ring

def admission_power_Cbridge1_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-4000000000000/2100010586289:ℝ)*δ^0*p^1
theorem admission_power_Cbridge1_01_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 1 = admission_power_Cbridge1_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_01] <;> ring

def admission_power_Cbridge1_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-9770832513817/10500052931445:ℝ)*δ^0*p^1
theorem admission_power_Cbridge1_02_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 2 = admission_power_Cbridge1_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_02] <;> ring

def admission_power_Cbridge1_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-30500052931445/12600063517734:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (4000000000000/2100010586289:ℝ)*δ^1*p^2
theorem admission_power_Cbridge1_03_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 3 = admission_power_Cbridge1_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_03] <;> ring

def admission_power_Cbridge1_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-20270885445262/10500052931445:ℝ)*δ^1*p^1 + (9770832513817/10500052931445:ℝ)*δ^1*p^2
theorem admission_power_Cbridge1_04_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 4 = admission_power_Cbridge1_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_04] <;> ring

def admission_power_Cbridge1_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-725901259768391/1200006049308000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (35293844435387789/21000105862890000:ℝ)*δ^1*p^1 + (-4772832513817/10500052931445:ℝ)*δ^1*p^2
theorem admission_power_Cbridge1_05_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 5 = admission_power_Cbridge1_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_05] <;> ring

def admission_power_Cbridge1_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-174470039372114/233101175078079:ℝ)*δ^0*p^1 + (14793641302461251003517307/36260365580768260454952506:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-2227065849577612/388501958463465:ℝ)*δ^1*p^1 + (4865995694552687954975845651/815858225567285860236431385:ℝ)*δ^1*p^2 + (-48800084690312000000000000/23310235016208167435326611:ℝ)*δ^1*p^3
theorem admission_power_Cbridge1_06_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 6 = admission_power_Cbridge1_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_06] <;> ring

def admission_power_Cbridge1_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-29906275236448/6300031758867:ℝ)*δ^0*p^1 + (59602181771140461863255113/26460266775155217088749126:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (59812550472896/10500052931445:ℝ)*δ^1*p^1 + (-59602181771140461863255113/22050222312629347573957605:ℝ)*δ^1*p^2
theorem admission_power_Cbridge1_07_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 7 = admission_power_Cbridge1_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_07] <;> ring

def admission_power_Cbridge1_08 (δ p : ℝ) : ℝ := (-3013108085791645567/8000000000000000000:ℝ)*δ^0*p^0 + (20755102000950022385853757830863/25200127035468000000000000000000:ℝ)*δ^0*p^1 + (-47031514275613022352434662628552144509612469/105841067100620868354996504000000000000000000:ℝ)*δ^0*p^2 + (23013108085791645567/20000000000000000000:ℝ)*δ^1*p^0 + (-20744377592668650112905138018793/7000035287630000000000000000000:ℝ)*δ^1*p^1 + (9127669869651825176065037641489/3818201065980000000000000000000:ℝ)*δ^1*p^2 + (-12808780788893121067970527056379/22050222312629347573957605000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge1_08_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 8 = admission_power_Cbridge1_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_08] <;> ring

def admission_power_Cbridge1_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-19335068584172016133/12600063517734000000:ℝ)*δ^0*p^1 + (41729407833613709087093587533479/52920533550310434177498252000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (4438230444092237327/1500007561635000000:ℝ)*δ^1*p^1 + (-13780857753367553763/7000035287630000000:ℝ)*δ^1*p^2 + (6837102399761784441255113/22050222312629347573957605:ℝ)*δ^1*p^3
theorem admission_power_Cbridge1_09_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 9 = admission_power_Cbridge1_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_09] <;> ring

def admission_power_Cbridge1_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-570534750874273/504002540709360:ℝ)*δ^1*p^1 + (11344041911329/18000090739620:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (168467115320963/84000423451560:ℝ)*δ^2*p^1 + (-131008356897037/105000529314450:ℝ)*δ^2*p^2 + (80000000000/700003528763:ℝ)*δ^2*p^3
theorem admission_power_Cbridge1_10_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 10 = admission_power_Cbridge1_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_10] <;> ring

def admission_power_Cbridge1_11 (δ p : ℝ) : ℝ := (30312603404341/12600063517734:ℝ)*δ^0*p^0 + (-9770832513817/2100010586289:ℝ)*δ^0*p^1 + (59602181771140461863255113/26460266775155217088749126:ℝ)*δ^0*p^2 + (-30770938376707/10500052931445:ℝ)*δ^1*p^0 + (19847221675878/3500017643815:ℝ)*δ^1*p^1 + (-60564690065175538136744887/22050222312629347573957605:ℝ)*δ^1*p^2
theorem admission_power_Cbridge1_11_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 11 = admission_power_Cbridge1_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_11] <;> ring

def admission_power_Cbridge1_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge1_12_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 12 = admission_power_Cbridge1_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_12] <;> ring

def admission_power_Cbridge1_13 (δ p : ℝ) : ℝ := (490825237919713711/10000000000000000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge1_13_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 13 = admission_power_Cbridge1_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_13] <;> ring

def admission_power_Cbridge1_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cbridge1_14_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 14 = admission_power_Cbridge1_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_14] <;> ring

def admission_power_Cbridge2_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-6000010586289/2000010586289:ℝ)*δ^0*p^1
theorem admission_power_Cbridge2_00_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 0 = admission_power_Cbridge2_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_00] <;> ring

def admission_power_Cbridge2_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-4000000000000/2000010586289:ℝ)*δ^0*p^1
theorem admission_power_Cbridge2_01_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 1 = admission_power_Cbridge2_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_01] <;> ring

def admission_power_Cbridge2_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-96961605236449/100000529314450:ℝ)*δ^0*p^1
theorem admission_power_Cbridge2_02_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 2 = admission_power_Cbridge2_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_02] <;> ring

def admission_power_Cbridge2_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-10000017643815/4000021172578:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (4000000000000/2000010586289:ℝ)*δ^1*p^2
theorem admission_power_Cbridge2_03_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 3 = admission_power_Cbridge2_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_03] <;> ring

def admission_power_Cbridge2_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-196962134550899/100000529314450:ℝ)*δ^1*p^1 + (96961605236449/100000529314450:ℝ)*δ^1*p^2
theorem admission_power_Cbridge2_04_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 4 = admission_power_Cbridge2_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_04] <;> ring

def admission_power_Cbridge2_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-4998008818378737/8000042345156000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (34394400455043589/20000105862890000:ℝ)*δ^1*p^1 + (-46981605236449/100000529314450:ℝ)*δ^1*p^2
theorem admission_power_Cbridge2_05_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 5 = admission_power_Cbridge2_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_05] <;> ring

def admission_power_Cbridge2_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-1112428898844437/1480007833853860:ℝ)*δ^0*p^1 + (1224858194420699330914499181/2960031335498371440945725540:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-21862772586685089/3700019584634650:ℝ)*δ^1*p^1 + (46725662549768399327964631857/7400078338745928602364313850:ℝ)*δ^1*p^2 + (-336000592832184000000000000/148001566774918572047286277:ℝ)*δ^1*p^3
theorem admission_power_Cbridge2_06_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 6 = admission_power_Cbridge2_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_06] <;> ring

def admission_power_Cbridge2_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-196961781674599/40000211725780:ℝ)*δ^0*p^1 + (193923552627422978987482587/80000846905361390295830420:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (590885345023797/100000529314450:ℝ)*δ^1*p^1 + (-581770657882268936962447761/200002117263403475739576050:ℝ)*δ^1*p^2
theorem admission_power_Cbridge2_07_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 7 = admission_power_Cbridge2_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_07] <;> ring

def admission_power_Cbridge2_08 (δ p : ℝ) : ℝ := (-3089061815275345567/8000000000000000000:ℝ)*δ^0*p^0 + (6785848771457929590474249043621/8000042345156000000000000000000:ℝ)*δ^0*p^1 + (-14787152113727853382751666157924477915170823/32000338762144556118332168000000000000000000:ℝ)*δ^0*p^2 + (23089061815275345567/20000000000000000000:ℝ)*δ^1*p^0 + (-60000236112842961543525750956379/20000105862890000000000000000000:ℝ)*δ^1*p^1 + (97819685642039688141525750956379/40000211725780000000000000000000:ℝ)*δ^1*p^2 + (-11998860681849164105770527056379/20000211726340347573957605000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge2_08_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 8 = admission_power_Cbridge2_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_08] <;> ring

def admission_power_Cbridge2_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-6253861618229438711/4000021172578000000:ℝ)*δ^0*p^1 + (13115460617434325892971420444493/16000169381072278059166084000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (30000113008645661289/10000052931445000000:ℝ)*δ^1*p^1 + (-40327041219070061289/20000105862890000000:ℝ)*δ^1*p^2 + (62769862168482162742447761/200002117263403475739576050:ℝ)*δ^1*p^3
theorem admission_power_Cbridge2_09_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 9 = admission_power_Cbridge2_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_09] <;> ring

def admission_power_Cbridge2_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-553847871267389/480002540709360:ℝ)*δ^1*p^1 + (39480786738791/60000317588670:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (817848696997931/400002117257800:ℝ)*δ^2*p^1 + (-64980818497658/50000264657225:ℝ)*δ^2*p^2 + (240000000000/2000010586289:ℝ)*δ^2*p^3
theorem admission_power_Cbridge2_10_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 10 = admission_power_Cbridge2_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_10] <;> ring

def admission_power_Cbridge2_11 (δ p : ℝ) : ℝ := (96961958112749/40000211725780:ℝ)*δ^0*p^0 + (-96961605236449/20000105862890:ℝ)*δ^0*p^1 + (193923552627422978987482587/80000846905361390295830420:ℝ)*δ^0*p^2 + (-296962663865349/100000529314450:ℝ)*δ^1*p^0 + (296961605236449/50000264657225:ℝ)*δ^1*p^1 + (-593924301267123063037552239/200002117263403475739576050:ℝ)*δ^1*p^2
theorem admission_power_Cbridge2_11_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 11 = admission_power_Cbridge2_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_11] <;> ring

def admission_power_Cbridge2_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge2_12_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 12 = admission_power_Cbridge2_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_12] <;> ring

def admission_power_Cbridge2_13 (δ p : ℝ) : ℝ := (446153347747613711/10000000000000000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge2_13_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 13 = admission_power_Cbridge2_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_13] <;> ring

def admission_power_Cbridge2_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cbridge2_14_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 14 = admission_power_Cbridge2_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_14] <;> ring

def admission_power_Cbridge3_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-5900010586289/1900010586289:ℝ)*δ^0*p^1
theorem admission_power_Cbridge3_00_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 0 = admission_power_Cbridge3_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_00] <;> ring

def admission_power_Cbridge3_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-4000000000000/1900010586289:ℝ)*δ^0*p^1
theorem admission_power_Cbridge3_01_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 1 = admission_power_Cbridge3_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_01] <;> ring

def admission_power_Cbridge3_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-96136568108477/95000529314450:ℝ)*δ^0*p^1
theorem admission_power_Cbridge3_02_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 2 = admission_power_Cbridge3_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_02] <;> ring

def admission_power_Cbridge3_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-29500052931445/11400063517734:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (4000000000000/1900010586289:ℝ)*δ^1*p^2
theorem admission_power_Cbridge3_03_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 3 = admission_power_Cbridge3_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_03] <;> ring

def admission_power_Cbridge3_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-191137097422927/95000529314450:ℝ)*δ^1*p^1 + (96136568108477/95000529314450:ℝ)*δ^1*p^2
theorem admission_power_Cbridge3_04_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 4 = admission_power_Cbridge3_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_04] <;> ring

def admission_power_Cbridge3_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-4914708818378737/7600042345156000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (33479293029449189/19000105862890000:ℝ)*δ^1*p^1 + (-46156568108477/95000529314450:ℝ)*δ^1*p^2
theorem admission_power_Cbridge3_05_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 5 = admission_power_Cbridge3_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_05] <;> ring

def admission_power_Cbridge3_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-3193865817738203/4218023501561580:ℝ)*δ^0*p^1 + (1126812322917933791027268713/2671429768727599440945725540:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-21446193465480197/3515019584634650:ℝ)*δ^1*p^1 + (44793797200115775947626323261/6678574421818998602364313850:ℝ)*δ^1*p^2 + (-330400592832184000000000000/133571488436379972047286277:ℝ)*δ^1*p^3
theorem admission_power_Cbridge3_06_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 6 = admission_power_Cbridge3_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_06] <;> ring

def admission_power_Cbridge3_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-583410233639881/114000635177340:ℝ)*δ^0*p^1 + (567206769569507764520871853/216602413680616170887491260:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (583410233639881/95000529314450:ℝ)*δ^1*p^1 + (-567206769569507764520871853/180502011400513475739576050:ℝ)*δ^1*p^2
theorem admission_power_Cbridge3_07_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 7 = admission_power_Cbridge3_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_07] <;> ring

def admission_power_Cbridge3_08 (δ p : ℝ) : ℝ := (-3141520376883745567/8000000000000000000:ℝ)*δ^0*p^0 + (19853168478460507925549974730863/22800127035468000000000000000000:ℝ)*δ^0*p^1 + (-41637030545271370623116311924869381204312469/86640965472246468354996504000000000000000000:ℝ)*δ^0*p^2 + (23141520376883745567/20000000000000000000:ℝ)*δ^1*p^0 + (-57771619940291921825483341756379/19000105862890000000000000000000:ℝ)*δ^1*p^1 + (95286273546271848423483341756379/38000211725780000000000000000000:ℝ)*δ^1*p^2 + (-11208938554805207143570527056379/18050201140051347573957605000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge3_08_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 8 = admission_power_Cbridge3_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_08] <;> ring

def admission_power_Cbridge3_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-18211596293079916133/11400063517734000000:ℝ)*δ^0*p^1 + (37112401547717344425029442933479/43320482736123234177498252000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (28932612908645661289/9500052931445000000:ℝ)*δ^1*p^1 + (-39264518842286861289/19000105862890000000:ℝ)*δ^1*p^2 + (56855971855720990300871853/180502011400513475739576050:ℝ)*δ^1*p^3
theorem admission_power_Cbridge3_09_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 9 = admission_power_Cbridge3_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_09] <;> ring

def admission_power_Cbridge3_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-536847722755501/456002540709360:ℝ)*δ^1*p^1 + (7843653634961/11400063517734:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (793048548486043/380002117257800:ℝ)*δ^2*p^1 + (-64418299933672/47500264657225:ℝ)*δ^2*p^2 + (240000000000/1900010586289:ℝ)*δ^2*p^3
theorem admission_power_Cbridge3_10_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 10 = admission_power_Cbridge3_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_10] <;> ring

def admission_power_Cbridge3_11 (δ p : ℝ) : ℝ := (278410762954331/114000635177340:ℝ)*δ^0*p^0 + (-96136568108477/19000105862890:ℝ)*δ^0*p^1 + (567206769569507764520871853/216602413680616170887491260:ℝ)*δ^0*p^2 + (-286137626737377/95000529314450:ℝ)*δ^1*p^0 + (296136568108477/47500264657225:ℝ)*δ^1*p^1 + (-581887892556108235479128147/180502011400513475739576050:ℝ)*δ^1*p^2
theorem admission_power_Cbridge3_11_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 11 = admission_power_Cbridge3_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_11] <;> ring

def admission_power_Cbridge3_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge3_12_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 12 = admission_power_Cbridge3_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_12] <;> ring

def admission_power_Cbridge3_13 (δ p : ℝ) : ℝ := (393649734950413711/10000000000000000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge3_13_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 13 = admission_power_Cbridge3_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_13] <;> ring

def admission_power_Cbridge3_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cbridge3_14_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 14 = admission_power_Cbridge3_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_14] <;> ring

def admission_power_Cbridge4_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-5800010586289/1800010586289:ℝ)*δ^0*p^1
theorem admission_power_Cbridge4_00_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 0 = admission_power_Cbridge4_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_00] <;> ring

def admission_power_Cbridge4_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-4000000000000/1800010586289:ℝ)*δ^0*p^1
theorem admission_power_Cbridge4_01_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 1 = admission_power_Cbridge4_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_01] <;> ring

def admission_power_Cbridge4_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-47621644908577/45000264657225:ℝ)*δ^0*p^1
theorem admission_power_Cbridge4_02_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 2 = admission_power_Cbridge4_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_02] <;> ring

def admission_power_Cbridge4_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-29000052931445/10800063517734:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (4000000000000/1800010586289:ℝ)*δ^1*p^2
theorem admission_power_Cbridge4_03_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 3 = admission_power_Cbridge4_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_03] <;> ring

def admission_power_Cbridge4_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-92621909565802/45000264657225:ℝ)*δ^1*p^1 + (47621644908577/45000264657225:ℝ)*δ^1*p^2
theorem admission_power_Cbridge4_04_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 4 = admission_power_Cbridge4_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_04] <;> ring

def admission_power_Cbridge4_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-4831408818378737/7200042345156000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (32550537371184589/18000105862890000:ℝ)*δ^1*p^1 + (-22631644908577/45000264657225:ℝ)*δ^1*p^2
theorem admission_power_Cbridge4_05_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 5 = admission_power_Cbridge4_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_05] <;> ring

def admission_power_Cbridge4_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-764504927018764/999005875390395:ℝ)*δ^0*p^1 + (1554419329941600799913104489/3596442302935241161418588310:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-10511019787571672/1665009792317325:ℝ)*δ^1*p^1 + (579289088443587239471377303/81000952768811737869788025:ℝ)*δ^1*p^2 + (-324800592832184000000000000/119881410097841372047286277:ℝ)*δ^1*p^3
theorem admission_power_Cbridge4_06_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 6 = admission_power_Cbridge4_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_06] <;> ring

def admission_power_Cbridge4_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-143932599691478/27000158794335:ℝ)*δ^0*p^1 + (276206044606242257574700753/97201143322574085443745630:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (287865199382956/45000264657225:ℝ)*δ^1*p^1 + (-276206044606242257574700753/81000952768811737869788025:ℝ)*δ^1*p^2
theorem admission_power_Cbridge4_07_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 7 = admission_power_Cbridge4_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_07] <;> ring

def admission_power_Cbridge4_08 (δ p : ℝ) : ℝ := (-3173506589486845567/8000000000000000000:ℝ)*δ^0*p^0 + (19260503787279204000708870630863/21600127035468000000000000000000:ℝ)*δ^0*p^1 + (-38888366782210915664854332506438253976012469/77760914658059268354996504000000000000000000:ℝ)*δ^0*p^2 + (23173506589486845567/20000000000000000000:ℝ)*δ^1*p^0 + (-55545136254156489800430376456379/18000105862890000000000000000000:ℝ)*δ^1*p^1 + (92795938634930216398430376456379/36000211725780000000000000000000:ℝ)*δ^1*p^2 + (-10439014407761250181370527056379/16200190553762347573957605000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge4_08_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 8 = admission_power_Cbridge4_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_08] <;> ring

def admission_power_Cbridge4_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-17682080080476816133/10800063517734000000:ℝ)*δ^0*p^1 + (3890119959109347395235945814831/4320050814336626019722028000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (27865112808645661289/9000052931445000000:ℝ)*δ^1*p^1 + (-12720350589164353763/6000035287630000000:ℝ)*δ^1*p^2 + (8451881583116290154900251/27000317589603912623262675:ℝ)*δ^1*p^3
theorem admission_power_Cbridge4_09_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 9 = admission_power_Cbridge4_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_09] <;> ring

def admission_power_Cbridge4_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-519574609590209/432002540709360:ℝ)*δ^1*p^1 + (77843258058287/108000635177340:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (767975435320751/360002117257800:ℝ)*δ^2*p^1 + (-127643321576021/90000529314450:ℝ)*δ^2*p^2 + (80000000000/600003528763:ℝ)*δ^2*p^3
theorem admission_power_Cbridge4_10_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 10 = admission_power_Cbridge4_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_10] <;> ring

def admission_power_Cbridge4_11 (δ p : ℝ) : ℝ := (132865464040181/54000317588670:ℝ)*δ^0*p^0 + (-47621644908577/9000052931445:ℝ)*δ^0*p^1 + (276206044606242257574700753/97201143322574085443745630:ℝ)*δ^0*p^2 + (-137622174223027/45000264657225:ℝ)*δ^1*p^0 + (295243289817154/45000264657225:ℝ)*δ^1*p^1 + (-284768173291273742425299247/81000952768811737869788025:ℝ)*δ^1*p^2
theorem admission_power_Cbridge4_11_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 11 = admission_power_Cbridge4_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_11] <;> ring

def admission_power_Cbridge4_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge4_12_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 12 = admission_power_Cbridge4_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_12] <;> ring

def admission_power_Cbridge4_13 (δ p : ℝ) : ℝ := (334322005818113711/10000000000000000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge4_13_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 13 = admission_power_Cbridge4_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_13] <;> ring

def admission_power_Cbridge4_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cbridge4_14_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 14 = admission_power_Cbridge4_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_14] <;> ring

def admission_power_Cbridge5_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-5850010586289/1850010586289:ℝ)*δ^0*p^1
theorem admission_power_Cbridge5_00_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 0 = admission_power_Cbridge5_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_00] <;> ring

def admission_power_Cbridge5_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-4000000000000/1850010586289:ℝ)*δ^0*p^1
theorem admission_power_Cbridge5_01_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 1 = admission_power_Cbridge5_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_01] <;> ring

def admission_power_Cbridge5_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-47849004961086/46250264657225:ℝ)*δ^0*p^1
theorem admission_power_Cbridge5_02_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 2 = admission_power_Cbridge5_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_02] <;> ring

def admission_power_Cbridge5_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-9750017643815/3700021172578:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (4000000000000/1850010586289:ℝ)*δ^1*p^2
theorem admission_power_Cbridge5_03_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 3 = admission_power_Cbridge5_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_03] <;> ring

def admission_power_Cbridge5_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-94099269618311/46250264657225:ℝ)*δ^1*p^1 + (47849004961086/46250264657225:ℝ)*δ^1*p^2
theorem admission_power_Cbridge5_04_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 4 = admission_power_Cbridge5_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_04] <;> ring

def admission_power_Cbridge5_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-4873058818378737/7400042345156000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (33016531392188189/18500105862890000:ℝ)*δ^1*p^1 + (-22859004961086/46250264657225:ℝ)*δ^1*p^2
theorem admission_power_Cbridge5_05_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 5 = admission_power_Cbridge5_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_05] <;> ring

def admission_power_Cbridge5_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-520840962736343/684503916926930:ℝ)*δ^0*p^1 + (270163747493334008673581292/633169746335553360236431385:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-10617506753400171/1711259792317325:ℝ)*δ^1*p^1 + (21914883858434554608312576948/3165848731677766801182156925:ℝ)*δ^1*p^2 + (-327600592832184000000000000/126633949267110672047286277:ℝ)*δ^1*p^3
theorem admission_power_Cbridge5_06_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 6 = admission_power_Cbridge5_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_06] <;> ring

def admission_power_Cbridge5_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-96599093180161/18500105862890:ℝ)*δ^0*p^1 + (46652864260957996748358309/17112695846906847573957605:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (289797279540483/46250264657225:ℝ)*δ^1*p^1 + (-279917185565747980490149854/85563479234534237869788025:ℝ)*δ^1*p^2
theorem admission_power_Cbridge5_07_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 7 = admission_power_Cbridge5_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_07] <;> ring

def admission_power_Cbridge5_08 (δ p : ℝ) : ℝ := (-3159937770992245567/8000000000000000000:ℝ)*δ^0*p^0 + (6522323107301967435559443743621/7400042345156000000000000000000:ℝ)*δ^0*p^1 + (-13421399288086415875968471907110333071270823/27380313355050956118332168000000000000000000:ℝ)*δ^0*p^2 + (23159937770992245567/20000000000000000000:ℝ)*δ^1*p^0 + (-56658232751288123698440556256379/18500105862890000000000000000000:ℝ)*δ^1*p^1 + (94036112169051050296440556256379/37000211725780000000000000000000:ℝ)*δ^1*p^2 + (-10821476733783228662470527056379/17112695846906847573957605000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge5_08_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 8 = admission_power_Cbridge5_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_08] <;> ring

def admission_power_Cbridge5_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-5981471299657138711/3700021172578000000:ℝ)*δ^0*p^1 + (12015313248083590420681290644493/13690156677525478059166084000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (28398862858645661289/9250052931445000000:ℝ)*δ^1*p^1 + (-38717633880503861289/18500105862890000000:ℝ)*δ^1*p^2 + (26904286208854593380149854/85563479234534237869788025:ℝ)*δ^1*p^3
theorem admission_power_Cbridge5_09_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 9 = admission_power_Cbridge5_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_09] <;> ring

def admission_power_Cbridge5_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-528243490010281/444002540709360:ℝ)*δ^1*p^1 + (5209865210887/7400042345156:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (780544315740823/370002117257800:ℝ)*δ^2*p^1 + (-128248041681039/92500529314450:ℝ)*δ^2*p^2 + (240000000000/1850010586289:ℝ)*δ^2*p^3
theorem admission_power_Cbridge5_10_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 10 = admission_power_Cbridge5_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_10] <;> ring

def admission_power_Cbridge5_11 (δ p : ℝ) : ℝ := (22674590699618/9250052931445:ℝ)*δ^0*p^0 + (-47849004961086/9250052931445:ℝ)*δ^0*p^1 + (46652864260957996748358309/17112695846906847573957605:ℝ)*δ^0*p^2 + (-140349534275536/46250264657225:ℝ)*δ^1*p^0 + (295698009922172/46250264657225:ℝ)*δ^1*p^1 + (-287875912751840019509850146/85563479234534237869788025:ℝ)*δ^1*p^2
theorem admission_power_Cbridge5_11_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 11 = admission_power_Cbridge5_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_11] <;> ring

def admission_power_Cbridge5_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge5_12_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 12 = admission_power_Cbridge5_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_12] <;> ring

def admission_power_Cbridge5_13 (δ p : ℝ) : ℝ := (364793966319913711/10000000000000000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge5_13_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 13 = admission_power_Cbridge5_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_13] <;> ring

def admission_power_Cbridge5_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cbridge5_14_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 14 = admission_power_Cbridge5_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_14] <;> ring

def admission_power_Cbridge6_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-5750010586289/1750010586289:ℝ)*δ^0*p^1
theorem admission_power_Cbridge6_00_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 0 = admission_power_Cbridge6_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_00] <;> ring

def admission_power_Cbridge6_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-4000000000000/1750010586289:ℝ)*δ^0*p^1
theorem admission_power_Cbridge6_01_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 1 = admission_power_Cbridge6_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_01] <;> ring

def admission_power_Cbridge6_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-94772530782231/87500529314450:ℝ)*δ^0*p^1
theorem admission_power_Cbridge6_02_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 2 = admission_power_Cbridge6_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_02] <;> ring

def admission_power_Cbridge6_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-28750052931445/10500063517734:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (4000000000000/1750010586289:ℝ)*δ^1*p^2
theorem admission_power_Cbridge6_03_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 3 = admission_power_Cbridge6_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_03] <;> ring

def admission_power_Cbridge6_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-182273060096681/87500529314450:ℝ)*δ^1*p^1 + (94772530782231/87500529314450:ℝ)*δ^1*p^2
theorem admission_power_Cbridge6_04_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 4 = admission_power_Cbridge6_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_04] <;> ring

def admission_power_Cbridge6_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-97750179966913/142858007044000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (32081335564199989/17500105862890000:ℝ)*δ^1*p^1 + (-44792530782231/87500529314450:ℝ)*δ^1*p^2
theorem admission_power_Cbridge6_05_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 5 = admission_power_Cbridge6_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_05] <;> ring

def admission_power_Cbridge6_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-427539137278787/555003357365940:ℝ)*δ^0*p^1 + (2980942174077448892897126617/6798832255714324322837176620:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-2972469331752413/462502797804950:ℝ)*δ^1*p^1 + (41906787548550748427811002783/5665693546428603602364313850:ℝ)*δ^1*p^2 + (-46000084690312000000000000/16187695846938867435326611:ℝ)*δ^1*p^3
theorem admission_power_Cbridge6_06_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 6 = admission_power_Cbridge6_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_06] <;> ring

def admission_power_Cbridge6_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-81688303094449/15000090739620:ℝ)*δ^0*p^1 + (181647685095742790697810253/61250741042471390295830420:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (81688303094449/12500075616350:ℝ)*δ^1*p^1 + (-544943055287228372093430759/153126852606178475739576050:ℝ)*δ^1*p^2
theorem admission_power_Cbridge6_07_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 7 = admission_power_Cbridge6_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_07] <;> ring

def admission_power_Cbridge6_08 (δ p : ℝ) : ℝ := (-3182263729009945567/8000000000000000000:ℝ)*δ^0*p^0 + (2704948217674585218173949504409/3000018147924000000000000000000:ℝ)*δ^0*p^1 + (-12503861162329518143314193908314925062570823/24500296416988556118332168000000000000000000:ℝ)*δ^0*p^2 + (23182263729009945567/20000000000000000000:ℝ)*δ^1*p^0 + (-7776013013529475089275350165197/2500015123270000000000000000000:ℝ)*δ^1*p^1 + (13080777113776264603275350165197/5000030246540000000000000000000:ℝ)*δ^1*p^2 + (-10061551576739271700270527056379/15312685260617847573957605000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge6_08_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 8 = admission_power_Cbridge6_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_08] <;> ring

def admission_power_Cbridge6_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-355603223284769717/214287010566000000:ℝ)*δ^0*p^1 + (34007194915966421297217661733479/36750444625482834177498252000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (3904480394092237327/1250007561635000000:ℝ)*δ^1*p^1 + (-5370692328077037327/2500015123270000000:ℝ)*δ^1*p^2 + (47567254573441597873430759/153126852606178475739576050:ℝ)*δ^1*p^3
theorem admission_power_Cbridge6_09_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 9 = admission_power_Cbridge6_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_09] <;> ring

def admission_power_Cbridge6_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-510841573450517/420002540709360:ℝ)*δ^1*p^1 + (6460208251947/8750052931445:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (755342399181059/350002117257800:ℝ)*δ^2*p^1 + (-9073040181507/6250037808175:ℝ)*δ^2*p^2 + (240000000000/1750010586289:ℝ)*δ^2*p^3
theorem admission_power_Cbridge6_10_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 10 = admission_power_Cbridge6_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_10] <;> ring

def admission_power_Cbridge6_11 (δ p : ℝ) : ℝ := (13648350051347/5526349219860:ℝ)*δ^0*p^0 + (-94772530782231/17500105862890:ℝ)*δ^0*p^1 + (181647685095742790697810253/61250741042471390295830420:ℝ)*δ^0*p^2 + (-269773589411131/87500529314450:ℝ)*δ^1*p^0 + (294772530782231/43750264657225:ℝ)*δ^1*p^1 + (-563239308228419627906569241/153126852606178475739576050:ℝ)*δ^1*p^2
theorem admission_power_Cbridge6_11_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 11 = admission_power_Cbridge6_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_11] <;> ring

def admission_power_Cbridge6_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge6_12_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 12 = admission_power_Cbridge6_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_12] <;> ring

def admission_power_Cbridge6_13 (δ p : ℝ) : ℝ := (302246152325813711/10000000000000000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge6_13_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 13 = admission_power_Cbridge6_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_13] <;> ring

def admission_power_Cbridge6_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cbridge6_14_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 14 = admission_power_Cbridge6_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_14] <;> ring

end
end Qrh.JointDetector.CurvedRestartReturn
