/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.runbo_li_arvi_face_8746074_20261026.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission23_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1:ℝ), (0:ℝ)]]
theorem admission23_00_identity (δ p : ℝ) : admissionGuard .capP δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (5/2:ℝ) admission23_00_coefficients (513/1024:ℝ) (1029/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (513/1024:ℝ) (1029/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 0 := by
 rw [admission23_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_00_coefficients]
def admission23_01_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission23_01_identity (δ p : ℝ) : admissionGuard .capP δ p 1 =
 Record12518109.Bernstein.bsum 0 0 (2:ℝ) admission23_01_coefficients (513/1024:ℝ) (1029/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (513/1024:ℝ) (1029/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 1 := by
 rw [admission23_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_01_coefficients]
def admission23_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(429999/5000000:ℝ), (0:ℝ)]]
theorem admission23_02_identity (δ p : ℝ) : admissionGuard .capP δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (9570001/10000000:ℝ) admission23_02_coefficients (513/1024:ℝ) (1029/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (513/1024:ℝ) (1029/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 2 := by
 rw [admission23_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_02_coefficients]
def admission23_03_coefficients : Fin 2 → Fin 2 → ℝ := ![![(15110/9:ℝ), (768:ℝ)],
![(8207/9:ℝ), (0:ℝ)]]
theorem admission23_03_identity (δ p : ℝ) : admissionGuard .capP δ p 3 =
 Record12518109.Bernstein.bsum 1 1 (16339/12288:ℝ) admission23_03_coefficients (513/1024:ℝ) (1029/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (513/1024:ℝ) (1029/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 3 := by
 rw [admission23_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_03_coefficients]
def admission23_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(437833529829/2500000:ℝ), (175104:ℝ), (0:ℝ)],
![(1505407075193/5000000:ℝ), (33319362048/78125:ℝ), (9799681024/78125:ℝ)]]
theorem admission23_04_identity (δ p : ℝ) : admissionGuard .capP δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (4909410513/20480000000:ℝ) admission23_04_coefficients (513/1024:ℝ) (1029/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (513/1024:ℝ) (1029/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 4 := by
 rw [admission23_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_04_coefficients]
def admission23_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(224084732707/1000000:ℝ), (3800888617579/7500000:ℝ), (4240065065579/15000000:ℝ)],
![(0:ℝ), (442499300971/7500000:ℝ), (884556132971/15000000:ℝ)]]
theorem admission23_05_identity (δ p : ℝ) : admissionGuard .capP δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (49143594556497/536870912000000:ℝ) admission23_05_coefficients (513/1024:ℝ) (1029/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (513/1024:ℝ) (1029/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 5 := by
 rw [admission23_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_05_coefficients]
def admission23_06_coefficients : Fin 2 → Fin 3 → ℝ := ![![(16033495838857/33300000:ℝ), (1390856632096/2890625:ℝ), (0:ℝ)],
![(245587208253793/333000000:ℝ), (2868633170384/2890625:ℝ), (147548197888/578125:ℝ)]]
theorem admission23_06_identity (δ p : ℝ) : admissionGuard .capP δ p 6 =
 Record12518109.Bernstein.bsum 1 2 (211284072223/454656000000:ℝ) admission23_06_coefficients (513/1024:ℝ) (1029/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (513/1024:ℝ) (1029/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 6 := by
 rw [admission23_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_06_coefficients]
def admission23_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(3435061075607/4500000:ℝ), (977700219488/703125:ℝ), (9799681024/15625:ℝ)],
![(244020906647/1800000:ℝ), (95307007472/703125:ℝ), (0:ℝ)]]
theorem admission23_07_identity (δ p : ℝ) : admissionGuard .capP δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (19455812033/24576000000:ℝ) admission23_07_coefficients (513/1024:ℝ) (1029/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (513/1024:ℝ) (1029/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 7 := by
 rw [admission23_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_07_coefficients]
def admission23_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(59694787226893/22500000:ℝ), (741087134368/140625:ℝ), (204443805696/78125:ℝ), (0:ℝ)],
![(1970588207272769/45000000:ℝ), (3608824015184/28125:ℝ), (9788405597184/78125:ℝ), (637010444288/15625:ℝ)]]
theorem admission23_08_identity (δ p : ℝ) : admissionGuard .capP δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (769082699/12288000000:ℝ) admission23_08_coefficients (513/1024:ℝ) (1029/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (513/1024:ℝ) (1029/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 8 := by
 rw [admission23_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_08_coefficients]
def admission23_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(3374815047769978448736382017996206507/50508815400960000000000000000:ℝ), (1122600320822751412325908716318133033/6061057848115200000000000000:ℝ), (50298238089403665752145517466758337/295950090240000000000000000:ℝ), (5297946154243501935049245942529/102760448000000000000000:ℝ)],
![(1504822306572834666035086431817222231/101017630801920000000000000000:ℝ), (1807400037052514366584301501017310977/60610578481152000000000000000:ℝ), (8833055324434838043216412784443141/591900180480000000000000000:ℝ), (0:ℝ)]]
theorem admission23_09_identity (δ p : ℝ) : admissionGuard .capP δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (232023828512826766599718828331259/28246576862867750912000000000000000:ℝ) admission23_09_coefficients (513/1024:ℝ) (1029/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (513/1024:ℝ) (1029/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 9 := by
 rw [admission23_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_09_coefficients]
def admission23_10_coefficients : Fin 3 → Fin 3 → ℝ := ![![(137946937445563/3750000:ℝ), (2984919257344/46875:ℝ), (1259902364672/46875:ℝ)],
![(524511710989813/11250000:ℝ), (17252095172864/234375:ℝ), (6317943826432/234375:ℝ)],
![(439121211412681/45000000:ℝ), (1221606848/125:ℝ), (0:ℝ)]]
theorem admission23_10_identity (δ p : ℝ) : admissionGuard .capP δ p 10 =
 Record12518109.Bernstein.bsum 2 2 (4253897319/83886080000000:ℝ) admission23_10_coefficients (513/1024:ℝ) (1029/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (513/1024:ℝ) (1029/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 10 := by
 rw [admission23_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_10_coefficients]
def admission23_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(4490998597039/7500000:ℝ), (261884389168/234375:ℝ), (40519681024/78125:ℝ)],
![(48009531683/600000:ℝ), (18735343096/234375:ℝ), (0:ℝ)]]
theorem admission23_11_identity (δ p : ℝ) : admissionGuard .capP δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (84849001793/122880000000:ℝ) admission23_11_coefficients (513/1024:ℝ) (1029/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (513/1024:ℝ) (1029/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 11 := by
 rw [admission23_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_11_coefficients]
def admission23_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission23_12_identity (δ p : ℝ) : admissionGuard .capP δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (164999/10000000:ℝ) admission23_12_coefficients (513/1024:ℝ) (1029/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (513/1024:ℝ) (1029/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 12 := by
 rw [admission23_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_12_coefficients]
def admission23_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission23_13_identity (δ p : ℝ) : admissionGuard .capP δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (28158065595289932996737123901/1231453023109120000000000000000:ℝ) admission23_13_coefficients (513/1024:ℝ) (1029/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (513/1024:ℝ) (1029/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 13 := by
 rw [admission23_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_13_coefficients]
def admission23_14_coefficients : Fin 2 → Fin 3 → ℝ := ![![(529608845653/22500000:ℝ), (22765174096/703125:ℝ), (138236928/15625:ℝ)],
![(661303099049/45000000:ℝ), (10327090504/703125:ℝ), (0:ℝ)]]
theorem admission23_14_identity (δ p : ℝ) : admissionGuard .capP δ p 14 =
 Record12518109.Bernstein.bsum 1 2 (735238661/24576000000:ℝ) admission23_14_coefficients (513/1024:ℝ) (1029/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission23_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission23_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (513/1024:ℝ) (1029/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capP δ p 14 := by
 rw [admission23_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission23_14_coefficients]
theorem admission23_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (513/1024:ℝ) (1029/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .capP δ p j := by
 fin_cases j
 · exact admission23_00_pos hδ hp
 · exact admission23_01_pos hδ hp
 · exact admission23_02_pos hδ hp
 · exact admission23_03_pos hδ hp
 · exact admission23_04_pos hδ hp
 · exact admission23_05_pos hδ hp
 · exact admission23_06_pos hδ hp
 · exact admission23_07_pos hδ hp
 · exact admission23_08_pos hδ hp
 · exact admission23_09_pos hδ hp
 · exact admission23_10_pos hδ hp
 · exact admission23_11_pos hδ hp
 · exact admission23_12_pos hδ hp
 · exact admission23_13_pos hδ hp
 · exact admission23_14_pos hδ hp
end
end QRH.RepeatedMarks.Return
