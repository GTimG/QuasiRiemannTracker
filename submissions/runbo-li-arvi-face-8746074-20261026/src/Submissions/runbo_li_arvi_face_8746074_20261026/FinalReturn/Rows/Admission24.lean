/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.runbo_li_arvi_face_8746074_20261026.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission24_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1:ℝ), (0:ℝ)]]
theorem admission24_00_identity (δ p : ℝ) : admissionGuard .capP δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (5/2:ℝ) admission24_00_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 0 := by
 rw [admission24_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_00_coefficients]
def admission24_01_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission24_01_identity (δ p : ℝ) : admissionGuard .capP δ p 1 =
 Record12518109.Bernstein.bsum 0 0 (2:ℝ) admission24_01_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 1 := by
 rw [admission24_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_01_coefficients]
def admission24_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(429999/5000000:ℝ), (0:ℝ)]]
theorem admission24_02_identity (δ p : ℝ) : admissionGuard .capP δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (9570001/10000000:ℝ) admission24_02_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 2 := by
 rw [admission24_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_02_coefficients]
def admission24_03_coefficients : Fin 2 → Fin 2 → ℝ := ![![(224/9:ℝ), (12:ℝ)],
![(125/9:ℝ), (0:ℝ)]]
theorem admission24_03_identity (δ p : ℝ) : admissionGuard .capP δ p 3 =
 Record12518109.Bernstein.bsum 1 1 (265/192:ℝ) admission24_03_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 3 := by
 rw [admission24_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_03_coefficients]
def admission24_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(40429999/1250000:ℝ), (32:ℝ), (0:ℝ)],
![(355270011/5000000:ℝ), (15820001/156250:ℝ), (9570001/312500:ℝ)]]
theorem admission24_04_identity (δ p : ℝ) : admissionGuard .capP δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (28710003/160000000:ℝ) admission24_04_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 4 := by
 rw [admission24_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_04_coefficients]
def admission24_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(60701203/1000000:ℝ), (962422033/7500000:ℝ), (1009166033/15000000:ℝ)],
![(0:ℝ), (19639997/1500000:ℝ), (37989997/3000000:ℝ)]]
theorem admission24_05_identity (δ p : ℝ) : admissionGuard .capP δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (41806791/409600000:ℝ) admission24_05_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 5 := by
 rw [admission24_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_05_coefficients]
def admission24_06_coefficients : Fin 2 → Fin 3 → ℝ := ![![(43814836919/416250000:ℝ), (291387823/2890625:ℝ), (0:ℝ)],
![(60085679731/333000000:ℝ), (21998893/92500:ℝ), (144090037/2312500:ℝ)]]
theorem admission24_06_identity (δ p : ℝ) : admissionGuard .capP δ p 6 =
 Record12518109.Bernstein.bsum 1 2 (1215009593/3552000000:ℝ) admission24_06_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 6 := by
 rw [admission24_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_06_coefficients]
def admission24_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2243009993/11250000:ℝ), (495110023/1406250:ℝ), (9570001/62500:ℝ)],
![(331169881/9000000:ℝ), (20509993/562500:ℝ), (0:ℝ)]]
theorem admission24_07_identity (δ p : ℝ) : admissionGuard .capP δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (66990007/76800000:ℝ) admission24_07_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 7 := by
 rw [admission24_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_07_coefficients]
def admission24_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (1214395547/11250000:ℝ), (817213561/3750000:ℝ), (246675029/2250000:ℝ)],
![(251454147/1000000:ℝ), (1710834067/2250000:ℝ), (580875017/750000:ℝ), (596595317/2250000:ℝ)]]
theorem admission24_08_identity (δ p : ℝ) : admissionGuard .capP δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (17400761/4096000000:ℝ) admission24_08_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 8 := by
 rw [admission24_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_08_coefficients]
def admission24_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(606052306744430326537949711464921/1616282092830720000000000000000:ℝ), (4587408635355760334011417161000299/4848846278492160000000000000000:ℝ), (132900500844484836516434296295027/173173081374720000000000000000:ℝ), (5297946154243501935049245942529/26938034880512000000000000000:ℝ)],
![(108490651528274583118175806627097/1293025674264576000000000000000:ℝ), (95934334233881070592829970034501/554153860399104000000000000000:ℝ), (43050048226452433068626296295027/484884627849216000000000000000:ℝ), (0:ℝ)]]
theorem admission24_09_identity (δ p : ℝ) : admissionGuard .capP δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (1867444103611338750369114994893/88270552696461721600000000000000:ℝ) admission24_09_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 9 := by
 rw [admission24_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_09_coefficients]
def admission24_10_coefficients : Fin 3 → Fin 3 → ℝ := ![![(39394999/281250:ℝ), (99246667/468750:ℝ), (65466667/937500:ℝ)],
![(16043333/75000:ℝ), (14421667/46875:ℝ), (8346667/93750:ℝ)],
![(83429993/1800000:ℝ), (247/5:ℝ), (0:ℝ)]]
theorem admission24_10_identity (δ p : ℝ) : admissionGuard .capP δ p 10 =
 Record12518109.Bernstein.bsum 2 2 (3920007/819200000:ℝ) admission24_10_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 10 := by
 rw [admission24_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_10_coefficients]
def admission24_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(562703141/3750000:ℝ), (64586656/234375:ℝ), (39570001/312500:ℝ)],
![(64356517/3000000:ℝ), (7596649/375000:ℝ), (0:ℝ)]]
theorem admission24_11_identity (δ p : ℝ) : admissionGuard .capP δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (11629999/15360000:ℝ) admission24_11_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 11 := by
 rw [admission24_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_11_coefficients]
def admission24_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission24_12_identity (δ p : ℝ) : admissionGuard .capP δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (164999/10000000:ℝ) admission24_12_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 12 := by
 rw [admission24_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_12_coefficients]
def admission24_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission24_13_identity (δ p : ℝ) : admissionGuard .capP δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (28158065595289932996737123901/1231453023109120000000000000000:ℝ) admission24_13_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 13 := by
 rw [admission24_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_13_coefficients]
def admission24_14_coefficients : Fin 2 → Fin 3 → ℝ := ![![(64843559/11250000:ℝ), (5489878/703125:ℝ), (134997/62500:ℝ)],
![(33164263/9000000:ℝ), (4004911/1125000:ℝ), (0:ℝ)]]
theorem admission24_14_identity (δ p : ℝ) : admissionGuard .capP δ p 14 =
 Record12518109.Bernstein.bsum 1 2 (2384947/76800000:ℝ) admission24_14_coefficients (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission24_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission24_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 14 := by
 rw [admission24_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission24_14_coefficients]
theorem admission24_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .capP δ p j := by
 fin_cases j
 · exact admission24_00_pos hδ hp
 · exact admission24_01_pos hδ hp
 · exact admission24_02_pos hδ hp
 · exact admission24_03_pos hδ hp
 · exact admission24_04_pos hδ hp
 · exact admission24_05_pos hδ hp
 · exact admission24_06_pos hδ hp
 · exact admission24_07_pos hδ hp
 · exact admission24_08_pos hδ hp
 · exact admission24_09_pos hδ hp
 · exact admission24_10_pos hδ hp
 · exact admission24_11_pos hδ hp
 · exact admission24_12_pos hδ hp
 · exact admission24_13_pos hδ hp
 · exact admission24_14_pos hδ hp
end
end QRH.RepeatedMarks.Return
