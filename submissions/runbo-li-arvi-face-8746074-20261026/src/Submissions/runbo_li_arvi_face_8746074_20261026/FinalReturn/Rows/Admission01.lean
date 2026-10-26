/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.runbo_li_arvi_face_8746074_20261026.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission01_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1:ℝ), (0:ℝ)]]
theorem admission01_00_identity (δ p : ℝ) : admissionGuard .capC δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (5/2:ℝ) admission01_00_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 0 := by
 rw [admission01_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_00_coefficients]
def admission01_01_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission01_01_identity (δ p : ℝ) : admissionGuard .capC δ p 1 =
 Record12518109.Bernstein.bsum 0 0 (2:ℝ) admission01_01_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 1 := by
 rw [admission01_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_01_coefficients]
def admission01_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(519999/5000000:ℝ), (0:ℝ)]]
theorem admission01_02_identity (δ p : ℝ) : admissionGuard .capC δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (9480001/10000000:ℝ) admission01_02_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 2 := by
 rw [admission01_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_02_coefficients]
def admission01_03_coefficients : Fin 2 → Fin 2 → ℝ := ![![(448/9:ℝ), (24:ℝ)],
![(241/9:ℝ), (0:ℝ)]]
theorem admission01_03_identity (δ p : ℝ) : admissionGuard .capC δ p 3 =
 Record12518109.Bernstein.bsum 1 1 (557/384:ℝ) admission01_03_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 3 := by
 rw [admission01_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_03_coefficients]
def admission01_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(80519999/625000:ℝ), (128:ℝ), (0:ℝ)],
![(266280011/1000000:ℝ), (30210002/78125:ℝ), (9480001/78125:ℝ)]]
theorem admission01_04_identity (δ p : ℝ) : admissionGuard .capC δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (28440003/160000000:ℝ) admission01_04_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 4 := by
 rw [admission01_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_04_coefficients]
def admission01_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1147056063/5000000:ℝ), (728124833/1500000:ℝ), (765520033/3000000:ℝ)],
![(0:ℝ), (291027973/7500000:ℝ), (568015973/15000000:ℝ)]]
theorem admission01_05_identity (δ p : ℝ) : admissionGuard .capC δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (12745326299/81920000000:ℝ) admission01_05_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 5 := by
 rw [admission01_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_05_coefficients]
def admission01_06_coefficients : Fin 2 → Fin 3 → ℝ := ![![(84565893431/208125000:ℝ), (1149271292/2890625:ℝ), (0:ℝ)],
![(1124980323019/1665000000:ℝ), (5260483287/5781250:ℝ), (140760037/578125:ℝ)]]
theorem admission01_06_identity (δ p : ℝ) : admissionGuard .capC δ p 6 =
 Record12518109.Bernstein.bsum 1 2 (1251639593/3552000000:ℝ) admission01_06_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 6 := by
 rw [admission01_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_06_coefficients]
def admission01_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(4481559997/5625000:ℝ), (986080046/703125:ℝ), (9480001/15625:ℝ)],
![(7675637393/45000000:ℝ), (238579921/1406250:ℝ), (0:ℝ)]]
theorem admission01_07_identity (δ p : ℝ) : admissionGuard .capC δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (748920079/768000000:ℝ) admission01_07_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 7 := by
 rw [admission01_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_07_coefficients]
def admission01_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (4383420571/5625000:ℝ), (2950533449/1875000:ℝ), (892699957/1125000:ℝ)],
![(1652137107/1000000:ℝ), (30158358823/5625000:ℝ), (10863819377/1875000:ℝ), (2344221109/1125000:ℝ)]]
theorem admission01_08_identity (δ p : ℝ) : admissionGuard .capC δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (23279513/32768000000:ℝ) admission01_08_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 8 := by
 rw [admission01_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_08_coefficients]
def admission01_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(510689271283849061065037531767/211392921600000000000000000:ℝ), (440998650728863366650325809341/70464307200000000000000000:ℝ), (19847362690274640586241969971/3774873600000000000000000:ℝ), (831448634236614887176695617/587202560000000000000000:ℝ)],
![(1082688547159879336857428353643/1691143372800000000000000000:ℝ), (734776891274273168610554053129/563714457600000000000000000:ℝ), (70003701219378590000889612859/105696460800000000000000000:ℝ), (0:ℝ)]]
theorem admission01_09_identity (δ p : ℝ) : admissionGuard .capC δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (788265949562752995268828741/153931627888640000000000000000:ℝ) admission01_09_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 9 := by
 rw [admission01_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_09_coefficients]
def admission01_10_coefficients : Fin 3 → Fin 3 → ℝ := ![![(740649982/703125:ℝ), (361406662/234375:ℝ), (113143331/234375:ℝ)],
![(4610859919/2812500:ℝ), (518366668/234375:ℝ), (130873334/234375:ℝ)],
![(2469779921/5000000:ℝ), (62766/125:ℝ), (0:ℝ)]]
theorem admission01_10_identity (δ p : ℝ) : admissionGuard .capC δ p 10 =
 Record12518109.Bernstein.bsum 2 2 (774810711/81920000000:ℝ) admission01_10_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 10 := by
 rw [admission01_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_10_coefficients]
def admission01_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(3079999/5000:ℝ), (262186624/234375:ℝ), (39480001/78125:ℝ)],
![(528838983/5000000:ℝ), (96546481/937500:ℝ), (0:ℝ)]]
theorem admission01_11_identity (δ p : ℝ) : admissionGuard .capC δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (3285319759/3840000000:ℝ) admission01_11_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 11 := by
 rw [admission01_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_11_coefficients]
def admission01_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission01_12_identity (δ p : ℝ) : admissionGuard .capC δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (164999/10000000:ℝ) admission01_12_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 12 := by
 rw [admission01_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_12_coefficients]
def admission01_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission01_13_identity (δ p : ℝ) : admissionGuard .capC δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (32724690064483136330185461/1503238553600000000000000000:ℝ) admission01_13_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 13 := by
 rw [admission01_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_13_coefficients]
def admission01_14_coefficients : Fin 2 → Fin 3 → ℝ := ![![(28529683/625000:ℝ), (43919512/703125:ℝ), (269997/15625:ℝ)],
![(143368407/5000000:ℝ), (79289119/2812500:ℝ), (0:ℝ)]]
theorem admission01_14_identity (δ p : ℝ) : admissionGuard .capC δ p 14 =
 Record12518109.Bernstein.bsum 1 2 (50129443/768000000:ℝ) admission01_14_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 14 := by
 rw [admission01_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_14_coefficients]
theorem admission01_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .capC δ p j := by
 fin_cases j
 · exact admission01_00_pos hδ hp
 · exact admission01_01_pos hδ hp
 · exact admission01_02_pos hδ hp
 · exact admission01_03_pos hδ hp
 · exact admission01_04_pos hδ hp
 · exact admission01_05_pos hδ hp
 · exact admission01_06_pos hδ hp
 · exact admission01_07_pos hδ hp
 · exact admission01_08_pos hδ hp
 · exact admission01_09_pos hδ hp
 · exact admission01_10_pos hδ hp
 · exact admission01_11_pos hδ hp
 · exact admission01_12_pos hδ hp
 · exact admission01_13_pos hδ hp
 · exact admission01_14_pos hδ hp
end
end QRH.RepeatedMarks.Return
