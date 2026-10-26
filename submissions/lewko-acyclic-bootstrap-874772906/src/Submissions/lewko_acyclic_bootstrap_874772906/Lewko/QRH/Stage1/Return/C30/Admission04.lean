/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.C30.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Return.C30
noncomputable section
def admission04_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(21:ℝ), (20:ℝ)]]
theorem admission04_00_identity (δ p : ℝ) : admissionGuard .capC δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (5/4:ℝ) admission04_00_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 0 := by
 rw [admission04_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_00_coefficients]
def admission04_01_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1:ℝ)]]
theorem admission04_01_identity (δ p : ℝ) : admissionGuard .capC δ p 1 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission04_01_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 1 := by
 rw [admission04_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_01_coefficients]
def admission04_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(38680003/5000000:ℝ), (9560001/1250000:ℝ)]]
theorem admission04_02_identity (δ p : ℝ) : admissionGuard .capC δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (9560001/20000000:ℝ) admission04_02_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 2 := by
 rw [admission04_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_02_coefficients]
def admission04_03_coefficients : Fin 2 → Fin 2 → ℝ := ![![(892/3:ℝ), (2444/9:ℝ)],
![(823/3:ℝ), (2228/9:ℝ)]]
theorem admission04_03_identity (δ p : ℝ) : admissionGuard .capC δ p 3 =
 Record12518109.Bernstein.bsum 1 1 (557/768:ℝ) admission04_03_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 3 := by
 rw [admission04_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_03_coefficients]
def admission04_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(386360031/625000:ℝ), (86480008/78125:ℝ), (38240004/78125:ℝ)],
![(3783160311/5000000:ℝ), (21370002/15625:ℝ), (9560001/15625:ℝ)]]
theorem admission04_04_identity (δ p : ℝ) : admissionGuard .capC δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (28680003/320000000:ℝ) admission04_04_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 4 := by
 rw [admission04_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_04_coefficients]
def admission04_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(19521822677/30000000:ℝ), (19916894629/15000000:ℝ), (6763615543/10000000:ℝ)],
![(12609246299/30000000:ℝ), (2637396449/3000000:ℝ), (916063883/2000000:ℝ)]]
theorem admission04_05_identity (δ p : ℝ) : admissionGuard .capC δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (12609246299/163840000000:ℝ) admission04_05_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 5 := by
 rw [admission04_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_05_coefficients]
def admission04_06_coefficients : Fin 2 → Fin 3 → ℝ := ![![(93564369437/69375000:ℝ), (59236865348/26015625:ℝ), (4876318372/5203125:ℝ)],
![(900547907353/555000000:ℝ), (145637357023/52031250:ℝ), (1233959741/1040625:ℝ)]]
theorem admission04_06_identity (δ p : ℝ) : admissionGuard .capC δ p 6 =
 Record12518109.Bernstein.bsum 1 2 (1219079593/7104000000:ℝ) admission04_06_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 6 := by
 rw [admission04_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_06_coefficients]
def admission04_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(19586121577/5625000:ℝ), (4765960441/703125:ℝ), (309106699/93750:ℝ)],
![(128305490033/45000000:ℝ), (7784660711/1406250:ℝ), (251746693/93750:ℝ)]]
theorem admission04_07_identity (δ p : ℝ) : admissionGuard .capC δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (251746693/512000000:ℝ) admission04_07_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 7 := by
 rw [admission04_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_07_coefficients]
def admission04_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1249982539/2250000:ℝ), (28501379227/11250000:ℝ), (38332458779/11250000:ℝ), (1071538151/750000:ℝ)],
![(19579868119/9000000:ℝ), (78871895731/11250000:ℝ), (84533454347/11250000:ℝ), (2008498919/750000:ℝ)]]
theorem admission04_08_identity (δ p : ℝ) : admissionGuard .capC δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (1249982539/196608000000:ℝ) admission04_08_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 8 := by
 rw [admission04_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_08_coefficients]
def admission04_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(3977237367767317711991/1406250000000000000:ℝ), (1143572143387164008311/156250000000000000:ℝ), (2162356403070947427487/351562500000000000:ℝ), (12975020485092396373/7812500000000000:ℝ)],
![(11612012395235002396159/11250000000000000000:ℝ), (2887330318243756465399/1250000000000000000:ℝ), (1061124525162591000617/703125000000000000:ℝ), (1814542995411562651/7812500000000000:ℝ)]]
theorem admission04_09_identity (δ p : ℝ) : admissionGuard .capC δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (5443628986234687953/2048000000000000000000:ℝ) admission04_09_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 9 := by
 rw [admission04_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_09_coefficients]
def admission04_10_coefficients : Fin 3 → Fin 3 → ℝ := ![![(578413361831/351562500:ℝ), (2397702570967/878906250:ℝ), (1890788305279/1757812500:ℝ)],
![(4966571087593/1757812500:ℝ), (80652900332/17578125:ℝ), (1534928194991/878906250:ℝ)],
![(3396985099309/3125000000:ℝ), (1320726246623/781250000:ℝ), (116027021113/195312500:ℝ)]]
theorem admission04_10_identity (δ p : ℝ) : admissionGuard .capC δ p 10 =
 Record12518109.Bernstein.bsum 2 2 (1044243190017/204800000000000:ℝ) admission04_10_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 10 := by
 rw [admission04_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_10_coefficients]
def admission04_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(16439157911/5625000:ℝ), (4042359631/703125:ℝ), (3978119777/1406250:ℝ)],
![(21708116627/9000000:ℝ), (13309238479/2812500:ℝ), (3266039759/1406250:ℝ)]]
theorem admission04_11_identity (δ p : ℝ) : admissionGuard .capC δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (3266039759/7680000000:ℝ) admission04_11_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 11 := by
 rw [admission04_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_11_coefficients]
def admission04_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(411573941/50000000000:ℝ)]]
theorem admission04_12_identity (δ p : ℝ) : admissionGuard .capC δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (411573941/50000000000:ℝ) admission04_12_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 12 := by
 rw [admission04_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_12_coefficients]
def admission04_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(82552311962667713/20000000000000000000:ℝ)]]
theorem admission04_13_identity (δ p : ℝ) : admissionGuard .capC δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (82552311962667713/20000000000000000000:ℝ) admission04_13_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 13 := by
 rw [admission04_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_13_coefficients]
def admission04_14_coefficients : Fin 2 → Fin 3 → ℝ := ![![(699636007/5625000:ℝ), (54548909/234375:ℝ), (30549389/281250:ℝ)],
![(5172746543/45000000:ℝ), (200345993/937500:ℝ), (27849443/281250:ℝ)]]
theorem admission04_14_identity (δ p : ℝ) : admissionGuard .capC δ p 14 =
 Record12518109.Bernstein.bsum 1 2 (27849443/1536000000:ℝ) admission04_14_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 14 := by
 rw [admission04_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_14_coefficients]
theorem admission04_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .capC δ p j := by
 fin_cases j
 · exact admission04_00_pos hδ hp
 · exact admission04_01_pos hδ hp
 · exact admission04_02_pos hδ hp
 · exact admission04_03_pos hδ hp
 · exact admission04_04_pos hδ hp
 · exact admission04_05_pos hδ hp
 · exact admission04_06_pos hδ hp
 · exact admission04_07_pos hδ hp
 · exact admission04_08_pos hδ hp
 · exact admission04_09_pos hδ hp
 · exact admission04_10_pos hδ hp
 · exact admission04_11_pos hδ hp
 · exact admission04_12_pos hδ hp
 · exact admission04_13_pos hδ hp
 · exact admission04_14_pos hδ hp
#print axioms admission04_all
end
end LewkoStage1Return.C30
