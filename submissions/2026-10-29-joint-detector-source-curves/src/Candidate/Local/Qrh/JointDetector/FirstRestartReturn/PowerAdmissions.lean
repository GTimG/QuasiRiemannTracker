/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/restart_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
A finite count-source bank and physical source remain explicit; no missing estimate is asserted. -/
import Candidate.Local.Qrh.JointDetector.FirstRestartReturn.Formulas
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unnecessarySeqFocus false
namespace Qrh.JointDetector.FirstRestartReturn
open QRH.Record1252270103Return
noncomputable section

def admission_power_Cnew_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-2857870970349/857870970349:ℝ)*δ^0*p^1
theorem admission_power_Cnew_00_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 0 = admission_power_Cnew_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_00] <;> ring

def admission_power_Cnew_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-2000000000000/857870970349:ℝ)*δ^0*p^1
theorem admission_power_Cnew_01_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 1 = admission_power_Cnew_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_01] <;> ring

def admission_power_Cnew_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-4721737658978/4289354851745:ℝ)*δ^0*p^1
theorem admission_power_Cnew_02_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 2 = admission_power_Cnew_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_02] <;> ring

def admission_power_Cnew_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-4763118283915/1715741940698:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (2000000000000/857870970349:ℝ)*δ^1*p^2
theorem admission_power_Cnew_03_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 3 = admission_power_Cnew_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_03] <;> ring

def admission_power_Cnew_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-9011092510723/4289354851745:ℝ)*δ^1*p^1 + (4721737658978/4289354851745:ℝ)*δ^1*p^2
theorem admission_power_Cnew_04_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 4 = admission_power_Cnew_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_04] <;> ring

def admission_power_Cnew_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-2380606518300717/3431483881396000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (15878365466543849/8578709703490000:ℝ)*δ^1*p^1 + (-2222737658978/4289354851745:ℝ)*δ^1*p^2
theorem admission_power_Cnew_05_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 5 = admission_power_Cnew_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_05] <;> ring

def admission_power_Cnew_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-49162265961819/63482451805826:ℝ)*δ^0*p^1 + (12072920894860525945320526/27229876265398788975726637:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-1032920945509983/158706129514565:ℝ)*δ^1*p^1 + (1031206053971451721533528984/136149381326993944878633185:ℝ)*δ^1*p^2 + (-80020387169772000000000000/27229876265398788975726637:ℝ)*δ^1*p^3
theorem admission_power_Cnew_06_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 6 = admission_power_Cnew_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_06] <;> ring

def admission_power_Cnew_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-9484855942893/1715741940698:ℝ)*δ^0*p^1 + (2249019497532812085273887/735942601767534837181801:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (28454567828679/4289354851745:ℝ)*δ^1*p^1 + (-13494116985196872511643322/3679713008837674185909005:ℝ)*δ^1*p^2
theorem admission_power_Cnew_07_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 7 = admission_power_Cnew_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_07] <;> ring

def admission_power_Cnew_08 (δ p : ℝ) : ℝ := (-1566126871680545747/4000000000000000000:ℝ)*δ^0*p^0 + (1533310132423441694108258351901/1715741940698000000000000000000:ℝ)*δ^0*p^1 + (-1500087667579095739429468577467231459594483/2943770407070139348727204000000000000000000:ℝ)*δ^0*p^2 + (11566126871680545747/10000000000000000000:ℝ)*δ^1*p^0 + (-13416025351599104052891741648099/4289354851745000000000000000000:ℝ)*δ^1*p^1 + (22758715838680466811891741648099/8578709703490000000000000000000:ℝ)*δ^1*p^2 + (-2475950909880430817535063648099/3679713008837674185909005000000:ℝ)*δ^1*p^3
theorem admission_power_Cnew_08_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 8 = admission_power_Cnew_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_08] <;> ring

def admission_power_Cnew_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-2875433145995454651/1715741940698000000:ℝ)*δ^0*p^1 + (2778625800620686661329936047733/2943770407070139348727204000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (13482772466346545349/4289354851745000000:ℝ)*δ^1*p^1 + (-18598852568469545349/8578709703490000000:ℝ)*δ^1*p^2 + (1133827896308417860643322/3679713008837674185909005:ℝ)*δ^1*p^3
theorem admission_power_Cnew_09_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 9 = admission_power_Cnew_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_09] <;> ring

def admission_power_Cnew_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-252397829296933/205889032883760:ℝ)*δ^1*p^1 + (38643763678733/51472258220940:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (74662352996831/34314838813960:ℝ)*δ^2*p^1 + (-63290989500827/42893548517450:ℝ)*δ^2*p^2 + (120000000000/857870970349:ℝ)*δ^2*p^3
theorem admission_power_Cnew_10_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 10 = admission_power_Cnew_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_10] <;> ring

def admission_power_Cnew_11 (δ p : ℝ) : ℝ := (2123987113404/857870970349:ℝ)*δ^0*p^0 + (-4721737658978/857870970349:ℝ)*δ^0*p^1 + (2249019497532812085273887/735942601767534837181801:ℝ)*δ^0*p^2 + (-13300447362468/4289354851745:ℝ)*δ^1*p^0 + (29443475317956/4289354851745:ℝ)*δ^1*p^1 + (-13971543354205127488356678/3679713008837674185909005:ℝ)*δ^1*p^2
theorem admission_power_Cnew_11_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 11 = admission_power_Cnew_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_11] <;> ring

def admission_power_Cnew_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cnew_12_expanded (δ p : ℝ) : admissionGuard .Cnew δ p 12 = admission_power_Cnew_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cnew_12] <;> ring

def admission_power_Cnew_13 (δ p : ℝ) : ℝ := (139374510002329651/5000000000000000000:ℝ)*δ^0*p^0
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

def admission_power_Pnew_09 (δ p : ℝ) : ℝ := (2708859260885121047/4000000000000000000:ℝ)*δ^0*p^0 + (-5848862260885121047/6000000000000000000:ℝ)*δ^0*p^1 + (2996288420295040349/12000000000000000000:ℝ)*δ^0*p^2 + (-12708859260885121047/10000000000000000000:ℝ)*δ^1*p^0 + (10763713579704959651/5000000000000000000:ℝ)*δ^1*p^1 + (-9483707579704959651/10000000000000000000:ℝ)*δ^1*p^2 + (619999/5000000:ℝ)*δ^1*p^3
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

def admission_power_Pnew_13 (δ p : ℝ) : ℝ := (260922945564779651/5000000000000000000:ℝ)*δ^0*p^0
theorem admission_power_Pnew_13_expanded (δ p : ℝ) : admissionGuard .Pnew δ p 13 = admission_power_Pnew_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pnew_13] <;> ring

def admission_power_Pnew_14 (δ p : ℝ) : ℝ := (479997/2000000:ℝ)*δ^0*p^0 + (-159999/1000000:ℝ)*δ^0*p^1 + (53333/2000000:ℝ)*δ^0*p^2 + (-479997/5000000:ℝ)*δ^1*p^0 + (-159999/2500000:ℝ)*δ^1*p^1 + (159999/5000000:ℝ)*δ^1*p^2
theorem admission_power_Pnew_14_expanded (δ p : ℝ) : admissionGuard .Pnew δ p 14 = admission_power_Pnew_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pnew_14] <;> ring

def admission_power_Cphys_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-3092620970349/1092620970349:ℝ)*δ^0*p^1
theorem admission_power_Cphys_00_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 0 = admission_power_Cphys_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_00] <;> ring

def admission_power_Cphys_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-2000000000000/1092620970349:ℝ)*δ^0*p^1
theorem admission_power_Cphys_01_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 1 = admission_power_Cphys_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_01] <;> ring

def admission_power_Cphys_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-98274226585809/109262097034900:ℝ)*δ^0*p^1
theorem admission_power_Cphys_02_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 2 = admission_power_Cphys_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_02] <;> ring

def admission_power_Cphys_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-5154368283915/2185241940698:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (2000000000000/1092620970349:ℝ)*δ^1*p^2
theorem admission_power_Cphys_03_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 3 = admission_power_Cphys_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_03] <;> ring

def admission_power_Cphys_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-207536323620709/109262097034900:ℝ)*δ^1*p^1 + (98274226585809/109262097034900:ℝ)*δ^1*p^2
theorem admission_power_Cphys_04_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 4 = admission_power_Cphys_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_04] <;> ring

def admission_power_Cphys_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-2576153268300717/4370483881396000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (18023172557168749/10926209703490000:ℝ)*δ^1*p^1 + (-48294226585809/109262097034900:ℝ)*δ^1*p^2
theorem admission_power_Cphys_05_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 5 = admission_power_Cphys_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_05] <;> ring

def admission_power_Cphys_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-1208959803205167/1617079036116520:ℝ)*δ^0*p^1 + (714934565109189308335653261/1766854465572657699029065480:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-22610475458293299/4042697590291300:ℝ)*δ^1*p^1 + (25153926244105525019102083017/4417136163931644247572663700:ℝ)*δ^1*p^2 + (-86593387169772000000000000/44171361639316442475726637:ℝ)*δ^1*p^3
theorem admission_power_Cphys_06_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 6 = admission_power_Cphys_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_06] <;> ring

def admission_power_Cphys_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-201361592264109/43704838813960:ℝ)*δ^0*p^1 + (101308311328034040964392447/47752823393855613487272040:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (604084776792327/109262097034900:ℝ)*δ^1*p^1 + (-303924933984102122893177341/119382058484639033718180100:ℝ)*δ^1*p^2
theorem admission_power_Cphys_07_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 7 = admission_power_Cphys_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_07] <;> ring

def admission_power_Cphys_08 (δ p : ℝ) : ℝ := (-1463605140978365747/4000000000000000000:ℝ)*δ^0*p^0 + (1749448938391316139901121411901/2185241940698000000000000000000:ℝ)*δ^0*p^1 + (-2051547739318663707877899695928843845574483/4775282339385561348727204000000000000000000:ℝ)*δ^0*p^2 + (11463605140978365747/10000000000000000000:ℝ)*δ^1*p^0 + (-16035391144616599607098878588099/5463104851745000000000000000000:ℝ)*δ^1*p^1 + (25663738845679202366098878588099/10926209703490000000000000000000:ℝ)*δ^1*p^2 + (-3378718147608340004757745638099/5969102924231951685909005000000:ℝ)*δ^1*p^3
theorem admission_power_Cphys_08_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 8 = admission_power_Cphys_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_08] <;> ring

def admission_power_Cphys_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-3307502990933004651/2185241940698000000:ℝ)*δ^0*p^1 + (3657704617927886558867739347733/4775282339385561348727204000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (15988728951096545349/5463104851745000000:ℝ)*δ^1*p^1 + (-21082901075094245349/10926209703490000000:ℝ)*δ^1*p^2 + (36413281901333029873177341/119382058484639033718180100:ℝ)*δ^1*p^3
theorem admission_power_Cphys_09_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 9 = admission_power_Cphys_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_09] <;> ring

def admission_power_Cphys_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-292237526109431/262229032883760:ℝ)*δ^1*p^1 + (5314566717581/8740967762792:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (431461961796653/218524194069800:ℝ)*δ^2*p^1 + (-131829952407903/109262097034900:ℝ)*δ^2*p^2 + (120000000000/1092620970349:ℝ)*δ^2*p^3
theorem admission_power_Cphys_10_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 10 = admission_power_Cphys_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_10] <;> ring

def admission_power_Cphys_11 (δ p : ℝ) : ℝ := (104448957942409/43704838813960:ℝ)*δ^0*p^0 + (-98274226585809/21852419406980:ℝ)*δ^0*p^1 + (101308311328034040964392447/47752823393855613487272040:ℝ)*δ^0*p^2 + (-316798420655609/109262097034900:ℝ)*δ^1*p^0 + (298274226585809/54631048517450:ℝ)*δ^1*p^1 + (-307696166428933877106822659/119382058484639033718180100:ℝ)*δ^1*p^2
theorem admission_power_Cphys_11_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 11 = admission_power_Cphys_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_11] <;> ring

def admission_power_Cphys_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cphys_12_expanded (δ p : ℝ) : admissionGuard .Cphys δ p 12 = admission_power_Cphys_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cphys_12] <;> ring

def admission_power_Cphys_13 (δ p : ℝ) : ℝ := (260922945564779651/5000000000000000000:ℝ)*δ^0*p^0
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

def admission_power_Pwide_09 (δ p : ℝ) : ℝ := (1791057645791961047/4000000000000000000:ℝ)*δ^0*p^0 + (-4091060645791961047/6000000000000000000:ℝ)*δ^0*p^1 + (2130354548597320349/12000000000000000000:ℝ)*δ^0*p^2 + (-11791057645791961047/10000000000000000000:ℝ)*δ^1*p^0 + (11069647451402679651/5000000000000000000:ℝ)*δ^1*p^1 + (-11469641451402679651/10000000000000000000:ℝ)*δ^1*p^2 + (899999/5000000:ℝ)*δ^1*p^3
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

def admission_power_Pwide_13 (δ p : ℝ) : ℝ := (260922945564779651/5000000000000000000:ℝ)*δ^0*p^0
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

def admission_power_Pcount_09 (δ p : ℝ) : ℝ := (1566120871680545747/4000000000000000000:ℝ)*δ^0*p^0 + (-3536423871680545747/6000000000000000000:ℝ)*δ^0*p^1 + (1835575623893515249/12000000000000000000:ℝ)*δ^0*p^2 + (-11566120871680545747/10000000000000000000:ℝ)*δ^1*p^0 + (11144626376106484751/5000000000000000000:ℝ)*δ^1*p^1 + (-12204020376106484751/10000000000000000000:ℝ)*δ^1*p^2 + (1009899/5000000:ℝ)*δ^1*p^3
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

def admission_power_Pcount_13 (δ p : ℝ) : ℝ := (139374510002329651/5000000000000000000:ℝ)*δ^0*p^0
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

def admission_power_Pcountmid_09 (δ p : ℝ) : ℝ := (1578988936235780747/4000000000000000000:ℝ)*δ^0*p^0 + (-3564291936235780747/6000000000000000000:ℝ)*δ^0*p^1 + (1849864978745260249/12000000000000000000:ℝ)*δ^0*p^2 + (-11578988936235780747/10000000000000000000:ℝ)*δ^1*p^0 + (11140337021254739751/5000000000000000000:ℝ)*δ^1*p^1 + (-12169731021254739751/10000000000000000000:ℝ)*δ^1*p^2 + (1004899/5000000:ℝ)*δ^1*p^3
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

def admission_power_Pcountmid_13 (δ p : ℝ) : ℝ := (139374510002329651/5000000000000000000:ℝ)*δ^0*p^0
theorem admission_power_Pcountmid_13_expanded (δ p : ℝ) : admissionGuard .Pcountmid δ p 13 = admission_power_Pcountmid_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pcountmid_13] <;> ring

def admission_power_Pcountmid_14 (δ p : ℝ) : ℝ := (1057347/2000000:ℝ)*δ^0*p^0 + (-352449/1000000:ℝ)*δ^0*p^1 + (117483/2000000:ℝ)*δ^0*p^2 + (-1057347/5000000:ℝ)*δ^1*p^0 + (-352449/2500000:ℝ)*δ^1*p^1 + (352449/5000000:ℝ)*δ^1*p^2
theorem admission_power_Pcountmid_14_expanded (δ p : ℝ) : admissionGuard .Pcountmid δ p 14 = admission_power_Pcountmid_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Pcountmid_14] <;> ring

def admission_power_Cbridge0_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-3100120970349/1100120970349:ℝ)*δ^0*p^1
theorem admission_power_Cbridge0_00_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 0 = admission_power_Cbridge0_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_00] <;> ring

def admission_power_Cbridge0_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-2000000000000/1100120970349:ℝ)*δ^0*p^1
theorem admission_power_Cbridge0_01_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 1 = admission_power_Cbridge0_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_01] <;> ring

def admission_power_Cbridge0_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-98368350440523/110012097034900:ℝ)*δ^0*p^1
theorem admission_power_Cbridge0_02_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 2 = admission_power_Cbridge0_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_02] <;> ring

def admission_power_Cbridge0_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-5166868283915/2200241940698:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (2000000000000/1100120970349:ℝ)*δ^1*p^2
theorem admission_power_Cbridge0_03_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 3 = admission_power_Cbridge0_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_03] <;> ring

def admission_power_Cbridge0_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-208380447475423/110012097034900:ℝ)*δ^1*p^1 + (98368350440523/110012097034900:ℝ)*δ^1*p^2
theorem admission_power_Cbridge0_04_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 4 = admission_power_Cbridge0_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_04] <;> ring

def admission_power_Cbridge0_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-2582400768300717/4400483881396000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (18088842442640149/11001209703490000:ℝ)*δ^1*p^1 + (-48388350440523/110012097034900:ℝ)*δ^1*p^2
theorem admission_power_Cbridge0_05_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 5 = admission_power_Cbridge0_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_05] <;> ring

def admission_power_Cbridge0_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-1217227220580749/1628179036116520:ℝ)*δ^0*p^1 + (723919986800801210108525967/1791193901114405499029065480:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-22669673206166553/4070447590291300:ℝ)*δ^1*p^1 + (25299017559785347313783464899/4477984752786013747572663700:ℝ)*δ^1*p^2 + (-86803387169772000000000000/44779847527860137475726637:ℝ)*δ^1*p^3
theorem admission_power_Cbridge0_06_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 6 = admission_power_Cbridge0_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_06] <;> ring

def admission_power_Cbridge0_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-201705716118823/44004838813960:ℝ)*δ^0*p^1 + (101651262006434881457017509/48410645976065013487272040:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (605117148356469/110012097034900:ℝ)*δ^1*p^1 + (-304953786019304644371052527/121026614940162533718180100:ℝ)*δ^1*p^2
theorem admission_power_Cbridge0_07_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 7 = admission_power_Cbridge0_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_07] <;> ring

def admission_power_Cbridge0_08 (δ p : ℝ) : ℝ := (-1455225991685465747/4000000000000000000:ℝ)*δ^0*p^0 + (1752242966362527292529880711901/2200241940698000000000000000000:ℝ)*δ^0*p^1 + (-2067464194065939429037812740551915677474483/4841064597606501348727204000000000000000000:ℝ)*δ^0*p^2 + (11455225991685465747/10000000000000000000:ℝ)*δ^1*p^0 + (-16119511774616788454470119288099/5500604851745000000000000000000:ℝ)*δ^1*p^1 + (25763734079972291213470119288099/11001209703490000000000000000000:ℝ)*δ^1*p^2 + (-3410160528661554926022745638099/6051330747008126685909005000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge0_08_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 8 = admission_power_Cbridge0_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_08] <;> ring

def admission_power_Cbridge0_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-3322734290697304651/2200241940698000000:ℝ)*δ^0*p^1 + (3690368556839744782860233147733/4841064597606501348727204000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (16068791458596545349/5500604851745000000:ℝ)*δ^1*p^1 + (-21153700739008445349/11001209703490000000:ℝ)*δ^1*p^2 + (36793384086535551351052527/121026614940162533718180100:ℝ)*δ^1*p^3
theorem admission_power_Cbridge0_09_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 9 = admission_power_Cbridge0_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_09] <;> ring

def admission_power_Cbridge0_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-293453273818859/264029032883760:ℝ)*δ^1*p^1 + (26589208206143/44004838813960:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (433262709506081/220024194069800:ℝ)*δ^2*p^1 + (-131969076262617/110012097034900:ℝ)*δ^2*p^2 + (120000000000/1100120970349:ℝ)*δ^2*p^3
theorem admission_power_Cbridge0_10_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 10 = admission_power_Cbridge0_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_10] <;> ring

def admission_power_Cbridge0_11 (δ p : ℝ) : ℝ := (105043081797123/44004838813960:ℝ)*δ^0*p^0 + (-98368350440523/22002419406980:ℝ)*δ^0*p^1 + (101651262006434881457017509/48410645976065013487272040:ℝ)*δ^0*p^2 + (-318392544510323/110012097034900:ℝ)*δ^1*p^0 + (298368350440523/55006048517450:ℝ)*δ^1*p^1 + (-308543809812587355628947473/121026614940162533718180100:ℝ)*δ^1*p^2
theorem admission_power_Cbridge0_11_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 11 = admission_power_Cbridge0_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_11] <;> ring

def admission_power_Cbridge0_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge0_12_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 12 = admission_power_Cbridge0_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_12] <;> ring

def admission_power_Cbridge0_13 (δ p : ℝ) : ℝ := (263379130800479651/5000000000000000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge0_13_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 13 = admission_power_Cbridge0_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_13] <;> ring

def admission_power_Cbridge0_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cbridge0_14_expanded (δ p : ℝ) : admissionGuard .Cbridge0 δ p 14 = admission_power_Cbridge0_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge0_14] <;> ring

def admission_power_Cbridge1_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-3050120970349/1050120970349:ℝ)*δ^0*p^1
theorem admission_power_Cbridge1_00_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 0 = admission_power_Cbridge1_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_00] <;> ring

def admission_power_Cbridge1_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-2000000000000/1050120970349:ℝ)*δ^0*p^1
theorem admission_power_Cbridge1_01_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 1 = admission_power_Cbridge1_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_01] <;> ring

def admission_power_Cbridge1_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-48852168020443/52506048517450:ℝ)*δ^0*p^1
theorem admission_power_Cbridge1_02_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 2 = admission_power_Cbridge1_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_02] <;> ring

def admission_power_Cbridge1_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-15250604851745/6300725822094:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (2000000000000/1050120970349:ℝ)*δ^1*p^2
theorem admission_power_Cbridge1_03_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 3 = admission_power_Cbridge1_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_03] <;> ring

def admission_power_Cbridge1_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-101358216537893/52506048517450:ℝ)*δ^1*p^1 + (48852168020443/52506048517450:ℝ)*δ^1*p^2
theorem admission_power_Cbridge1_04_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 4 = admission_power_Cbridge1_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_04] <;> ring

def admission_power_Cbridge1_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-2540750768300717/4200483881396000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (17647391002676449/10501209703490000:ℝ)*δ^1*p^1 + (-23862168020443/52506048517450:ℝ)*δ^1*p^2
theorem admission_power_Cbridge1_05_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 5 = admission_power_Cbridge1_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_05] <;> ring

def admission_power_Cbridge1_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-1745193630050977/2331268554174780:ℝ)*δ^0*p^1 + (333026911655255373253336747/816037998751376749514532740:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-11135483803903423/1942723795145650:ℝ)*δ^1*p^1 + (12165791089279249352294511159/2040094996878441873786331850:ℝ)*δ^1*p^2 + (-85403387169772000000000000/40801899937568837475726637:ℝ)*δ^1*p^3
theorem admission_power_Cbridge1_06_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 6 = admission_power_Cbridge1_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_06] <;> ring

def admission_power_Cbridge1_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-27187504779889/5727932565540:ℝ)*δ^0*p^1 + (149005022126165989628844607/66165243142003520230908060:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (27187504779889/4773277137950:ℝ)*δ^1*p^1 + (-149005022126165989628844607/55137702618336266859090050:ℝ)*δ^1*p^2
theorem admission_power_Cbridge1_07_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 7 = admission_power_Cbridge1_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_07] <;> ring

def admission_power_Cbridge1_08 (δ p : ℝ) : ℝ := (-1505608681739915747/4000000000000000000:ℝ)*δ^0*p^0 + (5187243058926530535885145185703/6300725822094000000000000000000:ℝ)*δ^0*p^1 + (-5878800621097644700556533633143726720573449/13233048628400704046181612000000000000000000:ℝ)*δ^0*p^2 + (11505608681739915747/10000000000000000000:ℝ)*δ^1*p^0 + (-15559590464706772235038284938099/5250604851745000000000000000000:ℝ)*δ^1*p^1 + (25103460380007824994038284938099/10501209703490000000000000000000:ℝ)*δ^1*p^2 + (-3202669440348455450922745638099/5513770261833626685909005000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge1_08_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 8 = admission_power_Cbridge1_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_08] <;> ring

def admission_power_Cbridge1_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-9669055182037463953/6300725822094000000:ℝ)*δ^0*p^1 + (10435490335052655394817030743199/13233048628400704046181612000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (15535041408596545349/5250604851745000000:ℝ)*δ^1*p^1 + (-20670746369117345349/10501209703490000000:ℝ)*δ^1*p^2 + (17087320659781443118844607/55137702618336266859090050:ℝ)*δ^1*p^3
theorem admission_power_Cbridge1_09_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 9 = admission_power_Cbridge1_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_09] <;> ring

def admission_power_Cbridge1_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-57055049003917/50405806576752:ℝ)*δ^1*p^1 + (9925451277349/15751814555235:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (421184680706807/210024194069800:ℝ)*δ^2*p^1 + (-6550253093149/5250604851745:ℝ)*δ^2*p^2 + (120000000000/1050120970349:ℝ)*δ^2*p^3
theorem admission_power_Cbridge1_10_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 10 = admission_power_Cbridge1_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_10] <;> ring

def admission_power_Cbridge1_11 (δ p : ℝ) : ℝ := (151568601096229/63007258220940:ℝ)*δ^0*p^0 + (-48852168020443/10501209703490:ℝ)*δ^0*p^1 + (149005022126165989628844607/66165243142003520230908060:ℝ)*δ^0*p^2 + (-153864265055343/52506048517450:ℝ)*δ^1*p^0 + (148852168020443/26253024258725:ℝ)*δ^1*p^1 + (-151415746990506010371155393/55137702618336266859090050:ℝ)*δ^1*p^2
theorem admission_power_Cbridge1_11_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 11 = admission_power_Cbridge1_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_11] <;> ring

def admission_power_Cbridge1_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge1_12_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 12 = admission_power_Cbridge1_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_12] <;> ring

def admission_power_Cbridge1_13 (δ p : ℝ) : ℝ := (245178460818629651/5000000000000000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge1_13_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 13 = admission_power_Cbridge1_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_13] <;> ring

def admission_power_Cbridge1_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cbridge1_14_expanded (δ p : ℝ) : admissionGuard .Cbridge1 δ p 14 = admission_power_Cbridge1_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge1_14] <;> ring

def admission_power_Cbridge2_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-3000120970349/1000120970349:ℝ)*δ^0*p^1
theorem admission_power_Cbridge2_00_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 0 = admission_power_Cbridge2_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_00] <;> ring

def admission_power_Cbridge2_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-2000000000000/1000120970349:ℝ)*δ^0*p^1
theorem admission_power_Cbridge2_01_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 1 = admission_power_Cbridge2_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_01] <;> ring

def admission_power_Cbridge2_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-48478748967367/50006048517450:ℝ)*δ^0*p^1
theorem admission_power_Cbridge2_02_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 2 = admission_power_Cbridge2_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_02] <;> ring

def admission_power_Cbridge2_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-15000604851745/6000725822094:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (2000000000000/1000120970349:ℝ)*δ^1*p^2
theorem admission_power_Cbridge2_03_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 3 = admission_power_Cbridge2_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_03] <;> ring

def admission_power_Cbridge2_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-98484797484817/50006048517450:ℝ)*δ^1*p^1 + (48478748967367/50006048517450:ℝ)*δ^1*p^2
theorem admission_power_Cbridge2_04_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 4 = admission_power_Cbridge2_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_04] <;> ring

def admission_power_Cbridge2_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-2499100768300717/4000483881396000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (17197657192061249/10001209703490000:ℝ)*δ^1*p^1 + (-23488748967367/50006048517450:ℝ)*δ^1*p^2
theorem admission_power_Cbridge2_05_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 5 = admission_power_Cbridge2_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_05] <;> ring

def admission_power_Cbridge2_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-1669143144942413/2220268554174780:ℝ)*δ^0*p^1 + (919149964158019102330020629/2220537140836652248543598220:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-10931534289011987/1850223795145650:ℝ)*δ^1*p^1 + (11682204924238136369724500771/1850447617363876873786331850:ℝ)*δ^1*p^2 + (-84003387169772000000000000/37008952347277537475726637:ℝ)*δ^1*p^3
theorem admission_power_Cbridge2_06_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 6 = admission_power_Cbridge2_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_06] <;> ring

def admission_power_Cbridge2_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-295442295419551/60007258220940:ℝ)*δ^0*p^1 + (145442111393282665775601083/60014517319909520230908060:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (295442295419551/50006048517450:ℝ)*δ^1*p^1 + (-145442111393282665775601083/50012097766591266859090050:ℝ)*δ^1*p^2
theorem admission_power_Cbridge2_07_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 7 = admission_power_Cbridge2_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_07] <;> ring

def admission_power_Cbridge2_08 (δ p : ℝ) : ℝ := (-1543567815817115747/4000000000000000000:ℝ)*δ^0*p^0 + (5087870334923631805212087985703/6000725822094000000000000000000:ℝ)*δ^0*p^1 + (-5545074083958434942497589354470549732973449/12002903463981904046181612000000000000000000:ℝ)*δ^0*p^2 + (11543567815817115747/10000000000000000000:ℝ)*δ^1*p^0 + (-15001349078759205145262637338099/5000604851745000000000000000000:ℝ)*δ^1*p^1 + (24457290159983057904262637338099/10001209703490000000000000000000:ℝ)*δ^1*p^2 + (-3000177847035355975822745638099/5001209776659126685909005000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge2_08_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 8 = admission_power_Cbridge2_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_08] <;> ring

def admission_power_Cbridge2_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-9382331047960263953/6000725822094000000:ℝ)*δ^0*p^1 + (3279902654821824900121911847733/4000967821327301348727204000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (15001291358596545349/5000604851745000000:ℝ)*δ^1*p^1 + (-6720981629090581783/3333736567830000000:ℝ)*δ^1*p^2 + (5228969808966039755200361/16670699255530422286363350:ℝ)*δ^1*p^3
theorem admission_power_Cbridge2_09_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 9 = admission_power_Cbridge2_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_09] <;> ring

def admission_power_Cbridge2_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-276931568807281/240029032883760:ℝ)*δ^1*p^1 + (1973919302816/3000362911047:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (408941004494503/200024194069800:ℝ)*δ^2*p^1 + (-32489555939207/25003024258725:ℝ)*δ^2*p^2 + (40000000000/333373656783:ℝ)*δ^2*p^3
theorem admission_power_Cbridge2_10_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 10 = admission_power_Cbridge2_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_10] <;> ring

def admission_power_Cbridge2_11 (δ p : ℝ) : ℝ := (145448343937001/60007258220940:ℝ)*δ^0*p^0 + (-48478748967367/10001209703490:ℝ)*δ^0*p^1 + (145442111393282665775601083/60014517319909520230908060:ℝ)*δ^0*p^2 + (-148490846002267/50006048517450:ℝ)*δ^1*p^0 + (148478748967367/25003024258725:ℝ)*δ^1*p^1 + (-148484981511085334224398917/50012097766591266859090050:ℝ)*δ^1*p^2
theorem admission_power_Cbridge2_11_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 11 = admission_power_Cbridge2_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_11] <;> ring

def admission_power_Cbridge2_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge2_12_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 12 = admission_power_Cbridge2_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_12] <;> ring

def admission_power_Cbridge2_13 (δ p : ℝ) : ℝ := (222836605511029651/5000000000000000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge2_13_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 13 = admission_power_Cbridge2_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_13] <;> ring

def admission_power_Cbridge2_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cbridge2_14_expanded (δ p : ℝ) : admissionGuard .Cbridge2 δ p 14 = admission_power_Cbridge2_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge2_14] <;> ring

def admission_power_Cbridge3_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-2950120970349/950120970349:ℝ)*δ^0*p^1
theorem admission_power_Cbridge3_00_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 0 = admission_power_Cbridge3_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_00] <;> ring

def admission_power_Cbridge3_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-2000000000000/950120970349:ℝ)*δ^0*p^1
theorem admission_power_Cbridge3_01_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 1 = admission_power_Cbridge3_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_01] <;> ring

def admission_power_Cbridge3_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-96132504200737/95012097034900:ℝ)*δ^0*p^1
theorem admission_power_Cbridge3_02_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 2 = admission_power_Cbridge3_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_02] <;> ring

def admission_power_Cbridge3_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-4916868283915/1900241940698:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (2000000000000/950120970349:ℝ)*δ^1*p^2
theorem admission_power_Cbridge3_03_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 3 = admission_power_Cbridge3_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_03] <;> ring

def admission_power_Cbridge3_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-191144601235637/95012097034900:ℝ)*δ^1*p^1 + (96132504200737/95012097034900:ℝ)*δ^1*p^2
theorem admission_power_Cbridge3_04_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 4 = admission_power_Cbridge3_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_04] <;> ring

def admission_power_Cbridge3_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-2457450768300717/3800483881396000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (16740107818661549/9501209703490000:ℝ)*δ^1*p^1 + (-46152504200737/95012097034900:ℝ)*δ^1*p^2
theorem admission_power_Cbridge3_05_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 5 = admission_power_Cbridge3_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_05] <;> ring

def admission_power_Cbridge3_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-36722535567339/48488932279880:ℝ)*δ^0*p^1 + (563735374101355286193158173/1336040190279449499029065480:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-21446494273550307/3515447590291300:ℝ)*δ^1*p^1 + (22398469782790525085529568281/3340100475698623747572663700:ℝ)*δ^1*p^2 + (-82603387169772000000000000/33401004756986237475726637:ℝ)*δ^1*p^3
theorem admission_power_Cbridge3_06_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 6 = admission_power_Cbridge3_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_06] <;> ring

def admission_power_Cbridge3_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-194469869879037/38004838813960:ℝ)*δ^0*p^1 + (94534172191585852373649071/36109194331877013487272040:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (583409609637111/95012097034900:ℝ)*δ^1*p^1 + (-283602516574757557120947213/90272985829692533718180100:ℝ)*δ^1*p^2
theorem admission_power_Cbridge3_07_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 7 = admission_power_Cbridge3_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_07] <;> ring

def admission_power_Cbridge3_08 (δ p : ℝ) : ℝ := (-1569803605717565747/4000000000000000000:ℝ)*δ^0*p^0 + (1653946586063771355324615011901/1900241940698000000000000000000:ℝ)*δ^0*p^1 + (-1734857637155844454584566152264743434374483/3610919433187701348727204000000000000000000:ℝ)*δ^0*p^2 + (11569803605717565747/10000000000000000000:ℝ)*δ^1*p^0 + (-14444178080936944391675384988099/4750604851745000000000000000000:ℝ)*δ^1*p^1 + (23823913672260347150675384988099/9501209703490000000000000000000:ℝ)*δ^1*p^2 + (-2802685748722256500722745638099/4513649291484626685909005000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge3_08_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 8 = admission_power_Cbridge3_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_08] <;> ring

def admission_power_Cbridge3_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-3035776752686604651/1900241940698000000:ℝ)*δ^0*p^1 + (3093713021160802226097076947733/3610919433187701348727204000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (14467541308596545349/4750604851745000000:ℝ)*δ^1*p^1 + (-19631696717072645349/9501209703490000000:ℝ)*δ^1*p^2 + (28417111641988464100947213/90272985829692533718180100:ℝ)*δ^1*p^3
theorem admission_power_Cbridge3_09_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 9 = admission_power_Cbridge3_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_09] <;> ring

def admission_power_Cbridge3_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-268431581339287/228029032883760:ℝ)*δ^1*p^1 + (78431778378643/114014516441880:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (396541017026509/190024194069800:ℝ)*δ^2*p^1 + (-128833230022831/95012097034900:ℝ)*δ^2*p^2 + (120000000000/950120970349:ℝ)*δ^2*p^3
theorem admission_power_Cbridge3_10_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 10 = admission_power_Cbridge3_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_10] <;> ring

def admission_power_Cbridge3_11 (δ p : ℝ) : ℝ := (92807235557337/38004838813960:ℝ)*δ^0*p^0 + (-96132504200737/19002419406980:ℝ)*δ^0*p^1 + (94534172191585852373649071/36109194331877013487272040:ℝ)*δ^0*p^2 + (-286156698270537/95012097034900:ℝ)*δ^1*p^0 + (296132504200737/47506048517450:ℝ)*δ^1*p^1 + (-290951694297990442879052787/90272985829692533718180100:ℝ)*δ^1*p^2
theorem admission_power_Cbridge3_11_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 11 = admission_power_Cbridge3_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_11] <;> ring

def admission_power_Cbridge3_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge3_12_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 12 = admission_power_Cbridge3_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_12] <;> ring

def admission_power_Cbridge3_13 (δ p : ℝ) : ℝ := (196586968811179651/5000000000000000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge3_13_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 13 = admission_power_Cbridge3_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_13] <;> ring

def admission_power_Cbridge3_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cbridge3_14_expanded (δ p : ℝ) : admissionGuard .Cbridge3 δ p 14 = admission_power_Cbridge3_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge3_14] <;> ring

def admission_power_Cbridge4_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-2900120970349/900120970349:ℝ)*δ^0*p^1
theorem admission_power_Cbridge4_00_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 0 = admission_power_Cbridge4_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_00] <;> ring

def admission_power_Cbridge4_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-2000000000000/900120970349:ℝ)*δ^0*p^1
theorem admission_power_Cbridge4_01_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 1 = admission_power_Cbridge4_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_01] <;> ring

def admission_power_Cbridge4_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-95239424367701/90012097034900:ℝ)*δ^0*p^1
theorem admission_power_Cbridge4_02_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 2 = admission_power_Cbridge4_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_02] <;> ring

def admission_power_Cbridge4_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-14500604851745/5400725822094:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (2000000000000/900120970349:ℝ)*δ^1*p^2
theorem admission_power_Cbridge4_03_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 3 = admission_power_Cbridge4_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_03] <;> ring

def admission_power_Cbridge4_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-185251521402601/90012097034900:ℝ)*δ^1*p^1 + (95239424367701/90012097034900:ℝ)*δ^1*p^2
theorem admission_power_Cbridge4_04_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 4 = admission_power_Cbridge4_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_04] <;> ring

def admission_power_Cbridge4_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-2415800768300717/3600483881396000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (16275749835357949/9001209703490000:ℝ)*δ^1*p^1 + (-45259424367701/90012097034900:ℝ)*δ^1*p^2
theorem admission_power_Cbridge4_05_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 5 = admission_power_Cbridge4_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_05] <;> ring

def admission_power_Cbridge4_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-3058992455825489/3996537108349560:ℝ)*δ^0*p^1 + (518455260883319445321836129/1199122286667797499029065480:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-21022362412083311/3330447590291300:ℝ)*δ^1*p^1 + (21435276250746912608143534413/2997805716669493747572663700:ℝ)*δ^1*p^2 + (-81203387169772000000000000/29978057166694937475726637:ℝ)*δ^1*p^3
theorem admission_power_Cbridge4_06_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 6 = admission_power_Cbridge4_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_06] <;> ring

def admission_power_Cbridge4_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-575730370138003/108014516441880:ℝ)*δ^0*p^1 + (276205851812737219894297649/97226131351443040461816120:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (575730370138003/90012097034900:ℝ)*δ^1*p^1 + (-276205851812737219894297649/81021776126202533718180100:ℝ)*δ^1*p^2
theorem admission_power_Cbridge4_07_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 7 = admission_power_Cbridge4_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_07] <;> ring

def admission_power_Cbridge4_08 (δ p : ℝ) : ℝ := (-1585826480762165747/4000000000000000000:ℝ)*δ^0*p^0 + (4813779828782961907276410435703/5400725822094000000000000000000:ℝ)*δ^0*p^1 + (-4861058089825343422671041615516191411323449/9722613135144304046181612000000000000000000:ℝ)*δ^0*p^2 + (11585826480762165747/10000000000000000000:ℝ)*δ^1*p^0 + (-13887541590769461777907863188099/4500604851745000000000000000000:ℝ)*δ^1*p^1 + (23201284607048264536907863188099/9001209703490000000000000000000:ℝ)*δ^1*p^2 + (-2610193145409157025622745638099/4051088806310126685909005000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge4_08_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 8 = admission_power_Cbridge4_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_08] <;> ring

def admission_power_Cbridge4_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-8842542383015213953/5400725822094000000:ℝ)*δ^0*p^1 + (8755691012520594935856187243199/9722613135144304046181612000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (13933791258596545349/4500604851745000000:ℝ)*δ^1*p^1 + (-19080022717161845349/9001209703490000000:ℝ)*δ^1*p^2 + (25345445879968126874297649/81021776126202533718180100:ℝ)*δ^1*p^3
theorem admission_power_Cbridge4_09_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 9 = admission_power_Cbridge4_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_09] <;> ring

def admission_power_Cbridge4_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-51959084334643/43205806576752:ℝ)*δ^1*p^1 + (77838698545607/108014516441880:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (384004857360437/180024194069800:ℝ)*δ^2*p^1 + (-25528030037959/18002419406980:ℝ)*δ^2*p^2 + (120000000000/900120970349:ℝ)*δ^2*p^3
theorem admission_power_Cbridge4_10_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 10 = admission_power_Cbridge4_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_10] <;> ring

def admission_power_Cbridge4_11 (δ p : ℝ) : ℝ := (265742467172903/108014516441880:ℝ)*δ^0*p^0 + (-95239424367701/18002419406980:ℝ)*δ^0*p^1 + (276205851812737219894297649/97226131351443040461816120:ℝ)*δ^0*p^2 + (-275263618437501/90012097034900:ℝ)*δ^1*p^0 + (295239424367701/45006048517450:ℝ)*δ^1*p^1 + (-284776039727866780105702351/81021776126202533718180100:ℝ)*δ^1*p^2
theorem admission_power_Cbridge4_11_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 11 = admission_power_Cbridge4_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_11] <;> ring

def admission_power_Cbridge4_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge4_12_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 12 = admission_power_Cbridge4_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_12] <;> ring

def admission_power_Cbridge4_13 (δ p : ℝ) : ℝ := (166933027159379651/5000000000000000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge4_13_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 13 = admission_power_Cbridge4_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_13] <;> ring

def admission_power_Cbridge4_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cbridge4_14_expanded (δ p : ℝ) : admissionGuard .Cbridge4 δ p 14 = admission_power_Cbridge4_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge4_14] <;> ring

def admission_power_Cbridge5_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-2925120970349/925120970349:ℝ)*δ^0*p^1
theorem admission_power_Cbridge5_00_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 0 = admission_power_Cbridge5_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_00] <;> ring

def admission_power_Cbridge5_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-2000000000000/925120970349:ℝ)*δ^0*p^1
theorem admission_power_Cbridge5_01_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 1 = admission_power_Cbridge5_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_01] <;> ring

def admission_power_Cbridge5_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-95694034153033/92512097034900:ℝ)*δ^0*p^1
theorem admission_power_Cbridge5_02_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 2 = admission_power_Cbridge5_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_02] <;> ring

def admission_power_Cbridge5_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-14625604851745/5550725822094:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (2000000000000/925120970349:ℝ)*δ^1*p^2
theorem admission_power_Cbridge5_03_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 3 = admission_power_Cbridge5_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_03] <;> ring

def admission_power_Cbridge5_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-188206131187933/92512097034900:ℝ)*δ^1*p^1 + (95694034153033/92512097034900:ℝ)*δ^1*p^2
theorem admission_power_Cbridge5_04_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 4 = admission_power_Cbridge5_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_04] <;> ring

def admission_power_Cbridge5_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-2436625768300717/3700483881396000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (16508735813891149/9251209703490000:ℝ)*δ^1*p^1 + (-45714034153033/92512097034900:ℝ)*δ^1*p^2
theorem admission_power_Cbridge5_05_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 5 = admission_power_Cbridge5_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_05] <;> ring

def admission_power_Cbridge5_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-3126030769653637/4107537108349560:ℝ)*δ^0*p^1 + (540650201409148921720678757/1266656238473623499029065480:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-21235324098255163/3422947590291300:ℝ)*δ^1*p^1 + (21916458365018284178947006529/3166640596184058747572663700:ℝ)*δ^1*p^2 + (-81903387169772000000000000/31666405961840587475726637:ℝ)*δ^1*p^3
theorem admission_power_Cbridge5_06_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 6 = admission_power_Cbridge5_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_06] <;> ring

def admission_power_Cbridge5_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-579594199493999/111014516441880:ℝ)*δ^0*p^1 + (279916626038330235321418517/102701857173537040461816120:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (579594199493999/92512097034900:ℝ)*δ^1*p^1 + (-279916626038330235321418517/85584880977947533718180100:ℝ)*δ^1*p^2
theorem admission_power_Cbridge5_07_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 7 = admission_power_Cbridge5_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_07] <;> ring

def admission_power_Cbridge5_08 (δ p : ℝ) : ℝ := (-1579025523561965747/4000000000000000000:ℝ)*δ^0*p^0 + (4890340400477465008694540635703/5550725822094000000000000000000:ℝ)*δ^0*p^1 + (-5033002269236467032278831958682123557923449/10270185717353704046181612000000000000000000:ℝ)*δ^0*p^2 + (11579025523561965747/10000000000000000000:ℝ)*δ^1*p^0 + (-4721941095690386914700606596033/1541868283915000000000000000000:ℝ)*δ^1*p^1 + (23511352110550163503101819788099/9251209703490000000000000000000:ℝ)*δ^1*p^2 + (-2705814510190706763172745638099/4279244048897376685909005000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge5_08_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 8 = admission_power_Cbridge5_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_08] <;> ring

def admission_power_Cbridge5_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-8973725840215413953/5550725822094000000:ℝ)*δ^0*p^1 + (9014467729168216125694100443199/10270185717353704046181612000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (14200666283596545349/4625604851745000000:ℝ)*δ^1*p^1 + (-6452760225920481783/3083736567830000000:ℝ)*δ^1*p^2 + (26893720605561142301418517/85584880977947533718180100:ℝ)*δ^1*p^3
theorem admission_power_Cbridge5_09_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 9 = admission_power_Cbridge5_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_09] <;> ring

def admission_power_Cbridge5_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-264129641243879/222029032883760:ℝ)*δ^1*p^1 + (78143308330939/111014516441880:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (390289076931101/185024194069800:ℝ)*δ^2*p^1 + (-128244759975127/92512097034900:ℝ)*δ^2*p^2 + (40000000000/308373656783:ℝ)*δ^2*p^3
theorem admission_power_Cbridge5_10_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 10 = admission_power_Cbridge5_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_10] <;> ring

def admission_power_Cbridge5_11 (δ p : ℝ) : ℝ := (272106296528899/111014516441880:ℝ)*δ^0*p^0 + (-95694034153033/18502419406980:ℝ)*δ^0*p^1 + (279916626038330235321418517/102701857173537040461816120:ℝ)*δ^0*p^2 + (-280718228222833/92512097034900:ℝ)*δ^1*p^0 + (98564678051011/15418682839150:ℝ)*δ^1*p^1 + (-287883704643601764678581483/85584880977947533718180100:ℝ)*δ^1*p^2
theorem admission_power_Cbridge5_11_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 11 = admission_power_Cbridge5_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_11] <;> ring

def admission_power_Cbridge5_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge5_12_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 12 = admission_power_Cbridge5_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_12] <;> ring

def admission_power_Cbridge5_13 (δ p : ℝ) : ℝ := (182163491425979651/5000000000000000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge5_13_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 13 = admission_power_Cbridge5_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_13] <;> ring

def admission_power_Cbridge5_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cbridge5_14_expanded (δ p : ℝ) : admissionGuard .Cbridge5 δ p 14 = admission_power_Cbridge5_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge5_14] <;> ring

def admission_power_Cbridge6_00 (δ p : ℝ) : ℝ := (3:ℝ)*δ^0*p^0 + (-2875120970349/875120970349:ℝ)*δ^0*p^1
theorem admission_power_Cbridge6_00_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 0 = admission_power_Cbridge6_00 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_00] <;> ring

def admission_power_Cbridge6_01 (δ p : ℝ) : ℝ := (2:ℝ)*δ^0*p^0 + (-2000000000000/875120970349:ℝ)*δ^0*p^1
theorem admission_power_Cbridge6_01_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 1 = admission_power_Cbridge6_01 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_01] <;> ring

def admission_power_Cbridge6_02 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0 + (-94768797030979/87512097034900:ℝ)*δ^0*p^1
theorem admission_power_Cbridge6_02_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 2 = admission_power_Cbridge6_02 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_02] <;> ring

def admission_power_Cbridge6_03 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-4791868283915/1750241940698:ℝ)*δ^0*p^1 + (-1:ℝ)*δ^1*p^0 + (-1:ℝ)*δ^1*p^1 + (2000000000000/875120970349:ℝ)*δ^1*p^2
theorem admission_power_Cbridge6_03_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 3 = admission_power_Cbridge6_03 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_03] <;> ring

def admission_power_Cbridge6_04 (δ p : ℝ) : ℝ := (1:ℝ)*δ^1*p^0 + (-182280894065879/87512097034900:ℝ)*δ^1*p^1 + (94768797030979/87512097034900:ℝ)*δ^1*p^2
theorem admission_power_Cbridge6_04_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 4 = admission_power_Cbridge6_04 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_04] <;> ring

def admission_power_Cbridge6_05 (δ p : ℝ) : ℝ := (2499/4000:ℝ)*δ^0*p^0 + (-2394975768300717/3500483881396000:ℝ)*δ^0*p^1 + (-12499/10000:ℝ)*δ^1*p^0 + (16041162101685749/8751209703490000:ℝ)*δ^1*p^1 + (-44788797030979/87512097034900:ℝ)*δ^1*p^2
theorem admission_power_Cbridge6_05_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 5 = admission_power_Cbridge6_05 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_05] <;> ring

def admission_power_Cbridge6_06 (δ p : ℝ) : ℝ := (25/74:ℝ)*δ^0*p^0 + (-997910696733877/1295179036116520:ℝ)*δ^0*p^1 + (497131290563907294132393191/1133438334861971499029065480:ℝ)*δ^0*p^2 + (69/37:ℝ)*δ^1*p^0 + (-20807622777707169/3237947590291300:ℝ)*δ^1*p^1 + (20954981225856289061711863227/2833595837154928747572663700:ℝ)*δ^1*p^2 + (-80503387169772000000000000/28335958371549287475726637:ℝ)*δ^1*p^3
theorem admission_power_Cbridge6_06_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 6 = admission_power_Cbridge6_06 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_06] <;> ring

def admission_power_Cbridge6_07 (δ p : ℝ) : ℝ := (5/2:ℝ)*δ^0*p^0 + (-190606162709279/35004838813960:ℝ)*δ^0*p^1 + (90823918559505257564480557/30633468509783013487272040:ℝ)*δ^0*p^2 + (-3:ℝ)*δ^1*p^0 + (571818488127837/87512097034900:ℝ)*δ^1*p^1 + (-272471755678515772693441671/76583671274457533718180100:ℝ)*δ^1*p^2
theorem admission_power_Cbridge6_07_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 7 = admission_power_Cbridge6_07 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_07] <;> ring

def admission_power_Cbridge6_08 (δ p : ℝ) : ℝ := (-1590224805253865747/4000000000000000000:ℝ)*δ^0*p^0 + (1577457994084231346599337911901/1750241940698000000000000000000:ℝ)*δ^0*p^1 + (-1562998588314915308279580936195248865074483/3063346850978301348727204000000000000000000:ℝ)*δ^0*p^2 + (11590224805253865747/10000000000000000000:ℝ)*δ^1*p^0 + (-13609273230940684400400662088099/4375604851745000000000000000000:ℝ)*δ^1*p^1 + (22893633072727787159400662088099/8751209703490000000000000000000:ℝ)*δ^1*p^2 + (-2515821654377607288072745638099/3829183563722876685909005000000:ℝ)*δ^1*p^3
theorem admission_power_Cbridge6_08_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 8 = admission_power_Cbridge6_08 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_08] <;> ring

def admission_power_Cbridge6_09 (δ p : ℝ) : ℝ := (2974997/4000000:ℝ)*δ^0*p^0 + (-2904587186174504651/1750241940698000000:ℝ)*δ^0*p^1 + (2834884245161938974463928347733/3063346850978301348727204000000:ℝ)*δ^0*p^2 + (-12974997/10000000:ℝ)*δ^1*p^0 + (13666916233596545349/4375604851745000000:ℝ)*δ^1*p^1 + (-18796959491145245349/8751209703490000000:ℝ)*δ^1*p^2 + (23773849245746679673441671/76583671274457533718180100:ℝ)*δ^1*p^3
theorem admission_power_Cbridge6_09_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 9 = admission_power_Cbridge6_09 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_09] <;> ring

def admission_power_Cbridge6_10 (δ p : ℝ) : ℝ := (119/240:ℝ)*δ^1*p^0 + (-255429166999771/210029032883760:ℝ)*δ^1*p^1 + (15503614241777/21002903288376:ℝ)*δ^1*p^2 + (-173/200:ℝ)*δ^2*p^0 + (377688602686993/175024194069800:ℝ)*δ^2*p^1 + (-127019522853073/87512097034900:ℝ)*δ^2*p^2 + (120000000000/875120970349:ℝ)*δ^2*p^3
theorem admission_power_Cbridge6_10_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 10 = admission_power_Cbridge6_10 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_10] <;> ring

def admission_power_Cbridge6_11 (δ p : ℝ) : ℝ := (86443528387579/35004838813960:ℝ)*δ^0*p^0 + (-94768797030979/17502419406980:ℝ)*δ^0*p^1 + (90823918559505257564480557/30633468509783013487272040:ℝ)*δ^0*p^2 + (-269792991100779/87512097034900:ℝ)*δ^1*p^0 + (294768797030979/43756048517450:ℝ)*δ^1*p^1 + (-281627626515200227306558329/76583671274457533718180100:ℝ)*δ^1*p^2
theorem admission_power_Cbridge6_11_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 11 = admission_power_Cbridge6_11 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_11] <;> ring

def admission_power_Cbridge6_12 (δ p : ℝ) : ℝ := (74999/10000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge6_12_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 12 = admission_power_Cbridge6_12 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_12] <;> ring

def admission_power_Cbridge6_13 (δ p : ℝ) : ℝ := (150901685323279651/5000000000000000000:ℝ)*δ^0*p^0
theorem admission_power_Cbridge6_13_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 13 = admission_power_Cbridge6_13 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_13] <;> ring

def admission_power_Cbridge6_14 (δ p : ℝ) : ℝ := (1:ℝ)*δ^0*p^0
theorem admission_power_Cbridge6_14_expanded (δ p : ℝ) : admissionGuard .Cbridge6 δ p 14 = admission_power_Cbridge6_14 δ p := by
  norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,countCB,countCL,countCap,naturalK,sMinus,mMinus,reserve,numeratorCap, admission_power_Cbridge6_14] <;> ring

end
end Qrh.JointDetector.FirstRestartReturn
