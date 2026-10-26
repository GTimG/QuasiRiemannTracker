/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.runbo_li_arvi_face_8746074_20261026.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission02_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1:ℝ), (0:ℝ)]]
theorem admission02_00_identity (δ p : ℝ) : admissionGuard .capP δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (5/2:ℝ) admission02_00_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 0 := by
 rw [admission02_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_00_coefficients]
def admission02_01_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission02_01_identity (δ p : ℝ) : admissionGuard .capP δ p 1 =
 Record12518109.Bernstein.bsum 0 0 (2:ℝ) admission02_01_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 1 := by
 rw [admission02_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_01_coefficients]
def admission02_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(429999/5000000:ℝ), (0:ℝ)]]
theorem admission02_02_identity (δ p : ℝ) : admissionGuard .capP δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (9570001/10000000:ℝ) admission02_02_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 2 := by
 rw [admission02_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_02_coefficients]
def admission02_03_coefficients : Fin 2 → Fin 2 → ℝ := ![![(914/9:ℝ), (48:ℝ)],
![(491/9:ℝ), (0:ℝ)]]
theorem admission02_03_identity (δ p : ℝ) : admissionGuard .capP δ p 3 =
 Record12518109.Bernstein.bsum 1 1 (1087/768:ℝ) admission02_03_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 3 := by
 rw [admission02_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_03_coefficients]
def admission02_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1443869991/2500000:ℝ), (576:ℝ), (0:ℝ)],
![(5498090237/5000000:ℝ), (124060008/78125:ℝ), (38280004/78125:ℝ)]]
theorem admission02_04_identity (δ p : ℝ) : admissionGuard .capP δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (258390027/1280000000:ℝ) admission02_04_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 4 := by
 rw [admission02_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_04_coefficients]
def admission02_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(897919651/1000000:ℝ), (14599966711/7500000:ℝ), (15707918711/15000000:ℝ)],
![(0:ℝ), (1312485943/7500000:ℝ), (2600461943/15000000:ℝ)]]
theorem admission02_05_identity (δ p : ℝ) : admissionGuard .capP δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (17910931893/131072000000:ℝ) admission02_05_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 5 := by
 rw [admission02_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_05_coefficients]
def admission02_06_coefficients : Fin 2 → Fin 3 → ℝ := ![![(288186467999/166500000:ℝ), (4949025094/2890625:ℝ), (0:ℝ)],
![(925031846917/333000000:ℝ), (10856036537/2890625:ℝ), (576360148/578125:ℝ)]]
theorem admission02_06_identity (δ p : ℝ) : admissionGuard .capP δ p 6 =
 Record12518109.Bernstein.bsum 1 2 (11016887077/28416000000:ℝ) admission02_06_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 6 := by
 rw [admission02_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_06_coefficients]
def admission02_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(111954001/36000:ℝ), (3908140202/703125:ℝ), (38280004/15625:ℝ)],
![(5600908063/9000000:ℝ), (436569851/703125:ℝ), (0:ℝ)]]
theorem admission02_07_identity (δ p : ℝ) : admissionGuard .capP δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (1425930149/1536000000:ℝ) admission02_07_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 7 := by
 rw [admission02_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_07_coefficients]
def admission02_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (92071168099/22500000:ℝ), (61885417697/7500000:ℝ), (93550255073/22500000:ℝ)],
![(57084792687/5000000:ℝ), (829254536899/22500000:ℝ), (59327264941/1500000:ℝ), (317499239393/22500000:ℝ)]]
theorem admission02_08_identity (δ p : ℝ) : admissionGuard .capP δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (373157877429/10485760000000:ℝ) admission02_08_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 8 := by
 rw [admission02_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_08_coefficients]
def admission02_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(5678086450838080645352948287808451/269380348805120000000000000000:ℝ), (3794058516417635344629007058632457/69269232549888000000000000000:ℝ), (3506302714600795399036508034088343/75763223101440000000000000000:ℝ), (5297946154243501935049245942529/420906795008000000000000000:ℝ)],
![(3798427702622489799350611474547601/538760697610240000000000000000:ℝ), (13724593014871673287760599457852581/969769255698432000000000000000:ℝ), (153701753367689812113739741153279/21646635171840000000000000000:ℝ), (0:ℝ)]]
theorem admission02_09_identity (δ p : ℝ) : admissionGuard .capP δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (53242720534957280812530037725447/1765411053929234432000000000000000:ℝ) admission02_09_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 9 := by
 rw [admission02_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_09_coefficients]
def admission02_10_coefficients : Fin 3 → Fin 3 → ℝ := ![![(32831396707/3750000:ℝ), (3180423368/234375:ℝ), (1119466684/234375:ℝ)],
![(142575289987/11250000:ℝ), (4180923392/234375:ℝ), (1191466696/234375:ℝ)],
![(161028987169/45000000:ℝ), (452732/125:ℝ), (0:ℝ)]]
theorem admission02_10_identity (δ p : ℝ) : admissionGuard .capP δ p 10 =
 Record12518109.Bernstein.bsum 2 2 (2515602831/327680000000:ℝ) admission02_10_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 10 := by
 rw [admission02_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_10_coefficients]
def admission02_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(17784191029/7500000:ℝ), (205903301/46875:ℝ), (158280004/78125:ℝ)],
![(202242863/600000:ℝ), (155802971/468750:ℝ), (0:ℝ)]]
theorem admission02_11_identity (δ p : ℝ) : admissionGuard .capP δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (6171129509/7680000000:ℝ) admission02_11_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 11 := by
 rw [admission02_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_11_coefficients]
def admission02_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission02_12_identity (δ p : ℝ) : admissionGuard .capP δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (164999/10000000:ℝ) admission02_12_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 12 := by
 rw [admission02_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_12_coefficients]
def admission02_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission02_13_identity (δ p : ℝ) : admissionGuard .capP δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (28158065595289932996737123901/1231453023109120000000000000000:ℝ) admission02_13_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 13 := by
 rw [admission02_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_13_coefficients]
def admission02_14_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2057039287/22500000:ℝ), (88243039/703125:ℝ), (539988/15625:ℝ)],
![(2572277837/45000000:ℝ), (79693229/1406250:ℝ), (0:ℝ)]]
theorem admission02_14_identity (δ p : ℝ) : admissionGuard .capP δ p 14 =
 Record12518109.Bernstein.bsum 1 2 (48913913/1536000000:ℝ) admission02_14_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 14 := by
 rw [admission02_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_14_coefficients]
theorem admission02_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .capP δ p j := by
 fin_cases j
 · exact admission02_00_pos hδ hp
 · exact admission02_01_pos hδ hp
 · exact admission02_02_pos hδ hp
 · exact admission02_03_pos hδ hp
 · exact admission02_04_pos hδ hp
 · exact admission02_05_pos hδ hp
 · exact admission02_06_pos hδ hp
 · exact admission02_07_pos hδ hp
 · exact admission02_08_pos hδ hp
 · exact admission02_09_pos hδ hp
 · exact admission02_10_pos hδ hp
 · exact admission02_11_pos hδ hp
 · exact admission02_12_pos hδ hp
 · exact admission02_13_pos hδ hp
 · exact admission02_14_pos hδ hp
end
end QRH.RepeatedMarks.Return
