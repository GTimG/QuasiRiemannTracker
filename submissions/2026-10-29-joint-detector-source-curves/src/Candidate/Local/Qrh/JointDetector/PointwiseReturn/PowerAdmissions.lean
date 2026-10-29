/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/pointwise_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
The actual selected all-source norm remains an explicit analytic premise. -/
import Candidate.Local.Qrh.JointDetector.PointwiseReturn.Formulas
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unnecessarySeqFocus false
namespace Qrh.JointDetector.PointwiseReturn
open QRH.Record1252270103Return
noncomputable section

def admission_power_capP_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-1:ℝ)*δ^0*p^1
theorem admission_power_capP_00_expanded (δ p : ℝ) : admissionGuard .capP δ p 0 = admission_power_capP_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_capP_00] <;> ring

def admission_power_capP_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0
theorem admission_power_capP_01_expanded (δ p : ℝ) : admissionGuard .capP δ p 1 = admission_power_capP_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_capP_01] <;> ring

def admission_power_capP_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-619999/5000000:ℝ)*δ^0*p^1
theorem admission_power_capP_02_expanded (δ p : ℝ) : admissionGuard .capP δ p 2 = admission_power_capP_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_capP_02] <;> ring

def admission_power_capP_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-5/6:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1
theorem admission_power_capP_03_expanded (δ p : ℝ) : admissionGuard .capP δ p 3 = admission_power_capP_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_capP_03] <;> ring

def admission_power_capP_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-5619999/5000000:ℝ)*δ^1*p^1 + (619999/5000000:ℝ)*δ^1*p^2
theorem admission_power_capP_04_expanded (δ p : ℝ) : admissionGuard .capP δ p 4 = admission_power_capP_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_capP_04] <;> ring

def admission_power_capP_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-833/4000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (4370499/5000000:ℝ)*δ^1*p^1 + (-619999/5000000:ℝ)*δ^1*p^2
theorem admission_power_capP_05_expanded (δ p : ℝ) : admissionGuard .capP δ p 5 = admission_power_capP_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_capP_05] <;> ring

def admission_power_capP_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-166180111/222000000:ℝ)*δ^0*p^1 + (15686679/74000000:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-393819889/185000000:ℝ)*δ^1*p^1 + (92939963/185000000:ℝ)*δ^1*p^2
theorem admission_power_capP_06_expanded (δ p : ℝ) : admissionGuard .capP δ p 6 = admission_power_capP_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_capP_06] <;> ring

def admission_power_capP_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-6859997/6000000:ℝ)*δ^0*p^1 + (619999/6000000:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (6859997/5000000:ℝ)*δ^1*p^1 + (-619999/5000000:ℝ)*δ^1*p^2
theorem admission_power_capP_07_expanded (δ p : ℝ) : admissionGuard .capP δ p 7 = admission_power_capP_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_capP_07] <;> ring

def admission_power_capP_08 (δ p : ℝ) : ℝ := (-1310003/4000000:ℝ)*δ^0*p^0 + (2225003/3000000:ℝ)*δ^0*p^1 + (-2530003/12000000:ℝ)*δ^0*p^2 + (11310003/10000000:ℝ)*δ^1*p^0 + (-11229999/5000000:ℝ)*δ^1*p^1 + (9949993/10000000:ℝ)*δ^1*p^2 + (-619999/5000000:ℝ)*δ^1*p^3
theorem admission_power_capP_08_expanded (δ p : ℝ) : admissionGuard .capP δ p 8 = admission_power_capP_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_capP_08] <;> ring

def admission_power_capP_09 (δ p : ℝ) : ℝ := (2656489938074470141631/4000000000000000000000:ℝ)*δ^0*p^0 + (-5796492938074470141631/6000000000000000000000:ℝ)*δ^0*p^1 + (2978831979358156713877/12000000000000000000000:ℝ)*δ^0*p^2 + (-12656489938074470141631/10000000000000000000000:ℝ)*δ^1*p^0 + (10781170020641843286123/5000000000000000000000:ℝ)*δ^1*p^1 + (-9501164020641843286123/10000000000000000000000:ℝ)*δ^1*p^2 + (619999/5000000:ℝ)*δ^1*p^3
theorem admission_power_capP_09_expanded (δ p : ℝ) : admissionGuard .capP δ p 9 = admission_power_capP_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_capP_09] <;> ring

def admission_power_capP_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-1348333/2000000:ℝ)*δ^1*p^1 + (319999/6000000:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (5994999/5000000:ℝ)*δ^2*p^1 + (-919999/5000000:ℝ)*δ^2*p^2
theorem admission_power_capP_10_expanded (δ p : ℝ) : admissionGuard .capP δ p 10 = admission_power_capP_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_capP_10] <;> ring

def admission_power_capP_11 (δ p : ℝ) : ℝ := (11859997/6000000:ℝ)*δ^0*p^0 + (-619999/1000000:ℝ)*δ^0*p^1 + (619999/6000000:ℝ)*δ^0*p^2 + (-10619999/5000000:ℝ)*δ^1*p^0 + (619999/2500000:ℝ)*δ^1*p^1 + (619999/5000000:ℝ)*δ^1*p^2
theorem admission_power_capP_11_expanded (δ p : ℝ) : admissionGuard .capP δ p 11 = admission_power_capP_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_capP_11] <;> ring

def admission_power_capP_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_capP_12_expanded (δ p : ℝ) : admissionGuard .capP δ p 12 = admission_power_capP_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_capP_12] <;> ring

def admission_power_capP_13 (δ p : ℝ) : ℝ := (263461388040213633877/5000000000000000000000:ℝ)*δ^0*p^0
theorem admission_power_capP_13_expanded (δ p : ℝ) : admissionGuard .capP δ p 13 = admission_power_capP_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_capP_13] <;> ring

def admission_power_capP_14 (δ p : ℝ) : ℝ := (479997/2000000:ℝ)*δ^0*p^0 + (-159999/1000000:ℝ)*δ^0*p^1 + (53333/2000000:ℝ)*δ^0*p^2 + (-479997/5000000:ℝ)*δ^1*p^0 + (-159999/2500000:ℝ)*δ^1*p^1 + (159999/5000000:ℝ)*δ^1*p^2
theorem admission_power_capP_14_expanded (δ p : ℝ) : admissionGuard .capP δ p 14 = admission_power_capP_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_capP_14] <;> ring

def admission_power_C_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-1224191237967/424191237967:ℝ)*δ^0*p^1
theorem admission_power_C_00_expanded (δ p : ℝ) : admissionGuard .C δ p 0 = admission_power_C_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_C_00] <;> ring

def admission_power_C_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-800000000000/424191237967:ℝ)*δ^0*p^1
theorem admission_power_C_01_expanded (δ p : ℝ) : admissionGuard .C δ p 1 = admission_power_C_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_C_01] <;> ring

def admission_power_C_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-38904970431209593637883/42419123796700000000000:ℝ)*δ^0*p^1
theorem admission_power_C_02_expanded (δ p : ℝ) : admissionGuard .C δ p 2 = admission_power_C_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_C_02] <;> ring

def admission_power_C_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-2040318729945/848382475934:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (800000000000/424191237967:ℝ)*δ^1*p^2
theorem admission_power_C_03_expanded (δ p : ℝ) : admissionGuard .C δ p 3 = admission_power_C_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_C_03] <;> ring

def admission_power_C_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-81324094227909593637883/42419123796700000000000:ℝ)*δ^1*p^1 + (38904970431209593637883/42419123796700000000000:ℝ)*δ^1*p^2
theorem admission_power_C_04_expanded (δ p : ℝ) : admissionGuard .C δ p 4 = admission_power_C_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_C_04] <;> ring

def admission_power_C_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-145678757318073/242394993124000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (70723555191114263637883/42419123796700000000000:ℝ)*δ^1*p^1 + (-18912970431209593637883/42419123796700000000000:ℝ)*δ^1*p^2
theorem admission_power_C_05_expanded (δ p : ℝ) : admissionGuard .C δ p 5 = admission_power_C_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_C_05] <;> ring

def admission_power_C_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-478415700193545035398329/627803032191160000000000:ℝ)*δ^0*p^1 + (111966092365640782668155238491052381/266308545424604512993771720000000000:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-8915694764649764893805013/1569507580477900000000000:ℝ)*δ^1*p^1 + (3914493819871650514416183484526842857/665771363561511282484429300000000000:ℝ)*δ^1*p^2 + (-1958705980747200000000000/951101947945016117834899:ℝ)*δ^1*p^3
theorem admission_power_C_06_expanded (δ p : ℝ) : admissionGuard .C δ p 6 = admission_power_C_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_C_06] <;> ring

def admission_power_C_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-79711345030109593637883/16967649518680000000000:ℝ)*δ^0*p^1 + (15875707971750667416268998959701287/7197528254719040891723560000000000:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (239134035090328780913649/42419123796700000000000:ℝ)*δ^1*p^1 + (-47627123915252002248806996879103861/17993820636797602229308900000000000:ℝ)*δ^1*p^2
theorem admission_power_C_07_expanded (δ p : ℝ) : admissionGuard .C δ p 7 = admission_power_C_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_C_07] <;> ring

def admission_power_C_08 (δ p : ℝ) : ℝ := (-11266031614510860933649/32000000000000000000000:ℝ)*δ^0*p^0 + (5357820730123966067357048918883861/6787059807472000000000000000000000:ℝ)*δ^0*p^1 + (-2496690040394642186808482490723556120495583529/5758022603775232713378848000000000000000000000:ℝ)*δ^0*p^2 + (91266031614510860933649/80000000000000000000000:ℝ)*δ^1*p^0 + (-50167002459676540850949351081116139/16967649518680000000000000000000000:ℝ)*δ^1*p^1 + (81052044038486532461489751081116139/33935299037360000000000000000000000:ℝ)*δ^1*p^2 + (-519238258654209936314837398011/899691031839880111465445000000:ℝ)*δ^1*p^3
theorem admission_power_C_08_expanded (δ p : ℝ) : admissionGuard .C δ p 8 = admission_power_C_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_C_08] <;> ring

def admission_power_C_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-26181172570211147022117/16967649518680000000000:ℝ)*δ^0*p^1 + (5729740730345829854536293146668713/7197528254719040891723560000000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (894034498498423281/302993741405000000:ℝ)*δ^1*p^1 + (-82387800290168410583649/42419123796700000000000:ℝ)*δ^1*p^2 + (5270116875123705984806996879103861/17993820636797602229308900000000000:ℝ)*δ^1*p^3
theorem admission_power_C_09_expanded (δ p : ℝ) : admissionGuard .C δ p 9 = admission_power_C_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_C_09] <;> ring

def admission_power_C_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-57162070231949093637883/50902948556040000000000:ℝ)*δ^1*p^1 + (1502848714447980649423/2423949931240000000000:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (84505528512662093637883/42419123796700000000000:ℝ)*δ^2*p^1 + (-52250117859011593637883/42419123796700000000000:ℝ)*δ^2*p^2 + (48000000000/424191237967:ℝ)*δ^2*p^3
theorem admission_power_C_10_expanded (δ p : ℝ) : admissionGuard .C δ p 10 = admission_power_C_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_C_10] <;> ring

def admission_power_C_11 (δ p : ℝ) : ℝ := (40517719629009593637883/16967649518680000000000:ℝ)*δ^0*p^0 + (-38904970431209593637883/8483824759340000000000:ℝ)*δ^0*p^1 + (15875707971750667416268998959701287/7197528254719040891723560000000000:ℝ)*δ^0*p^2 + (-123743218024609593637883/42419123796700000000000:ℝ)*δ^1*p^0 + (118904970431209593637883/21209561898350000000000:ℝ)*δ^1*p^1 + (-48556127812043347571805803120896139/17993820636797602229308900000000000:ℝ)*δ^1*p^2
theorem admission_power_C_11_expanded (δ p : ℝ) : admissionGuard .C δ p 11 = admission_power_C_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_C_11] <;> ring

def admission_power_C_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_C_12_expanded (δ p : ℝ) : admissionGuard .C δ p 12 = admission_power_C_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_C_12] <;> ring

def admission_power_C_13 (δ p : ℝ) : ℝ := (1759806519582834297883/40000000000000000000000:ℝ)*δ^0*p^0
theorem admission_power_C_13_expanded (δ p : ℝ) : admissionGuard .C δ p 13 = admission_power_C_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_C_13] <;> ring

def admission_power_C_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_C_14_expanded (δ p : ℝ) : admissionGuard .C δ p 14 = admission_power_C_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_C_14] <;> ring

def admission_power_Cphys_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-157755268577/57755268577:ℝ)*δ^0*p^1
theorem admission_power_Cphys_00_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 0 = admission_power_Cphys_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_00] <;> ring

def admission_power_Cphys_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-100000000000/57755268577:ℝ)*δ^0*p^1
theorem admission_power_Cphys_01_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 1 = admission_power_Cphys_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_01] <;> ring

def admission_power_Cphys_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-4934995154607585173877/5775526857700000000000:ℝ)*δ^0*p^1
theorem admission_power_Cphys_02_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 2 = admission_power_Cphys_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_02] <;> ring

def admission_power_Cphys_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-788776342885/346531611462:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (100000000000/57755268577:ℝ)*δ^1*p^2
theorem admission_power_Cphys_03_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 3 = admission_power_Cphys_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_03] <;> ring

def admission_power_Cphys_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-10710522012307585173877/5775526857700000000000:ℝ)*δ^1*p^1 + (4934995154607585173877/5775526857700000000000:ℝ)*δ^1*p^2
theorem admission_power_Cphys_04_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 4 = admission_power_Cphys_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_04] <;> ring

def admission_power_Cphys_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-131410138724641/231021074308000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (9267217850568355173877/5775526857700000000000:ℝ)*δ^1*p^1 + (-2435995154607585173877/5775526857700000000000:ℝ)*δ^1*p^2
theorem admission_power_Cphys_05_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 5 = admission_power_Cphys_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_05] <;> ring

def admission_power_Cphys_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-193665300150458045699653/256433392481880000000000:ℝ)*δ^0*p^1 + (6036119685793375235484932963567927/14810379454902232005884760000000000:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-1153193707911941954300347/213694493734900000000000:ℝ)*δ^1*p^1 + (65818184854410554858316267036432073/12341982879085193338237300000000000:ℝ)*δ^1*p^2 + (-220857376007800000000000/123419828790851933382373:ℝ)*δ^1*p^3
theorem admission_power_Cphys_06_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 6 = admission_power_Cphys_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_06] <;> ring

def admission_power_Cphys_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-30580512321522755521631/6930632229240000000000:ℝ)*δ^0*p^1 + (259507162013771079382123126454343/133426841936056144197160000000000:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (30580512321522755521631/5775526857700000000000:ℝ)*δ^1*p^1 + (-778521486041313238146369379363029/333567104840140360492900000000000:ℝ)*δ^1*p^2
theorem admission_power_Cphys_07_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 7 = admission_power_Cphys_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_07] <;> ring

def admission_power_Cphys_08 (δ p : ℝ) : ℝ := (-1340022346130332141631/4000000000000000000000:ℝ)*δ^0*p^0 + (259922654806834427567664007829087/346531611462000000000000000000000:ℝ)*δ^0*p^1 + (-5406618792345450830977386832346611155299911/13342684193605614419716000000000000000000000:ℝ)*δ^0*p^2 + (11340022346130332141631/10000000000000000000000:ℝ)*δ^1*p^0 + (-837014055667192539198478664056971/288776342885000000000000000000000:ℝ)*δ^1*p^1 + (1327732907244918270116928664056971/577552685770000000000000000000000:ℝ)*δ^1*p^2 + (-9110269787349458513164902171/16678355242007018024645000000:ℝ)*δ^1*p^3
theorem admission_power_Cphys_08_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 8 = admission_power_Cphys_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_08] <;> ring

def admission_power_Cphys_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-45226945016998383661/30264769560000000000:ℝ)*δ^0*p^1 + (297829111125849829752773821346971/400280525808168432591480000000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (832787499814743577/288776342885000000:ℝ)*δ^1*p^1 + (-10782601533120191291631/5775526857700000000000:ℝ)*δ^1*p^2 + (96230107201056815146369379363029/333567104840140360492900000000000:ℝ)*δ^1*p^3
theorem admission_power_Cphys_09_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 9 = admission_power_Cphys_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_09] <;> ring

def admission_power_Cphys_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-7541231052132085173877/6930632229240000000000:ℝ)*δ^1*p^1 + (1329487847715195057959/2310210743080000000000:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (11143686526635085173877/5775526857700000000000:ℝ)*δ^2*p^1 + (-6631526766069585173877/5775526857700000000000:ℝ)*δ^2*p^2 + (6000000000/57755268577:ℝ)*δ^2*p^3
theorem admission_power_Cphys_10_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 10 = admission_power_Cphys_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_10] <;> ring

def admission_power_Cphys_11 (δ p : ℝ) : ℝ := (16356039179222755521631/6930632229240000000000:ℝ)*δ^0*p^0 + (-4934995154607585173877/1155105371540000000000:ℝ)*δ^0*p^1 + (259507162013771079382123126454343/133426841936056144197160000000000:ℝ)*δ^0*p^2 + (-16486048870007585173877/5775526857700000000000:ℝ)*δ^1*p^0 + (14934995154607585173877/2887763428850000000000:ℝ)*δ^1*p^1 + (-786030230650203796629030620636971/333567104840140360492900000000000:ℝ)*δ^1*p^2
theorem admission_power_Cphys_11_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 11 = admission_power_Cphys_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_11] <;> ring

def admission_power_Cphys_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cphys_12_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 12 = admission_power_Cphys_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_12] <;> ring

def admission_power_Cphys_13 (δ p : ℝ) : ℝ := (263461388040213633877/5000000000000000000000:ℝ)*δ^0*p^0
theorem admission_power_Cphys_13_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 13 = admission_power_Cphys_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_13] <;> ring

def admission_power_Cphys_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cphys_14_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 14 = admission_power_Cphys_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_14] <;> ring

end
end Qrh.JointDetector.PointwiseReturn
