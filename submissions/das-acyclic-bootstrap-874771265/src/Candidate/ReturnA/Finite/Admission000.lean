/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def admission000_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7340032/3:ℝ),(65011712/9:ℝ),(63963136/9:ℝ),(20971520/9:ℝ)],
![(14680064/3:ℝ),(130023424/9:ℝ),(127926272/9:ℝ),(41943040/9:ℝ)],
![(7340032/3:ℝ),(65011712/9:ℝ),(63963136/9:ℝ),(20971520/9:ℝ)]]
theorem admission000_00_identity (δ p : ℝ) : admissionGuard .capC δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (5/4:ℝ) admission000_00_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission000_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission000_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (27/64:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 0 := by
 rw [admission000_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission000_00_coefficients]
def admission000_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(16777216/9:ℝ),(16777216/3:ℝ),(16777216/3:ℝ),(16777216/9:ℝ)],
![(33554432/9:ℝ),(33554432/3:ℝ),(33554432/3:ℝ),(33554432/9:ℝ)],
![(16777216/9:ℝ),(16777216/3:ℝ),(16777216/3:ℝ),(16777216/9:ℝ)]]
theorem admission000_01_identity (δ p : ℝ) : admissionGuard .capC δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (1/1:ℝ) admission000_01_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission000_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission000_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (27/64:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 1 := by
 rw [admission000_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission000_01_coefficients]
def admission000_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(633733169152/703125:ℝ),(378798112768/140625:ℝ),(1886781620224/703125:ℝ),(208841408512/234375:ℝ)],
![(1267466338304/703125:ℝ),(757596225536/140625:ℝ),(3773563240448/703125:ℝ),(417682817024/234375:ℝ)],
![(633733169152/703125:ℝ),(378798112768/140625:ℝ),(1886781620224/703125:ℝ),(208841408512/234375:ℝ)]]
theorem admission000_02_identity (δ p : ℝ) : admissionGuard .capC δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (9560001/20000000:ℝ) admission000_02_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission000_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission000_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (27/64:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 2 := by
 rw [admission000_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission000_02_coefficients]
def admission000_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(14614528/9:ℝ),(127729664/27:ℝ),(123928576/27:ℝ),(40042496/27:ℝ)],
![(28098560/9:ℝ),(245137408/27:ℝ),(237387776/27:ℝ),(76546048/27:ℝ)],
![(13484032/9:ℝ),(117407744/27:ℝ),(113459200/27:ℝ),(36503552/27:ℝ)]]
theorem admission000_03_identity (δ p : ℝ) : admissionGuard .capC δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (557/768:ℝ) admission000_03_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission000_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission000_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (27/64:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 3 := by
 rw [admission000_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission000_03_coefficients]
def admission000_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(16484694656/78125:ℝ),(27601922432/46875:ℝ),(127713292288/234375:ℝ),(13052588032/78125:ℝ)],
![(36661549648/78125:ℝ),(307954587376/234375:ℝ),(286074907648/234375:ℝ),(29368323072/78125:ℝ)],
![(20176854992/78125:ℝ),(56648325072/78125:ℝ),(10557441024/15625:ℝ),(3263147008/15625:ℝ)]]
theorem admission000_04_identity (δ p : ℝ) : admissionGuard .capC δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (28680003/320000000:ℝ) admission000_04_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission000_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission000_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (27/64:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 4 := by
 rw [admission000_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission000_04_coefficients]
def admission000_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(156174581416/703125:ℝ),(94968979096/140625:ℝ),(480997087096/703125:ℝ),(54108924344/234375:ℝ)],
![(257048551808/703125:ℝ),(786710581792/703125:ℝ),(801916468976/703125:ℝ),(90751479664/234375:ℝ)],
![(100873970392/703125:ℝ),(311865686312/703125:ℝ),(64183876376/140625:ℝ),(7328511064/46875:ℝ)]]
theorem admission000_05_identity (δ p : ℝ) : admissionGuard .capC δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (12609246299/163840000000:ℝ) admission000_05_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission000_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission000_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (27/64:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 5 := by
 rw [admission000_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission000_05_coefficients]
def admission000_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(11976239287936/26015625:ℝ),(19317453596032/15609375:ℝ),(85625300180992/78046875:ℝ),(4993350012928/15609375:ℝ)],
![(26385005805584/26015625:ℝ),(42875978865776/15609375:ℝ),(191780996346368/78046875:ℝ),(11311223886848/15609375:ℝ)],
![(14408766517648/26015625:ℝ),(23558525269744/15609375:ℝ),(106155696165376/78046875:ℝ),(1263574774784/3121875:ℝ)]]
theorem admission000_06_identity (δ p : ℝ) : admissionGuard .capC δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (1219079593/7104000000:ℝ) admission000_06_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission000_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission000_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (27/64:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 6 := by
 rw [admission000_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission000_06_coefficients]
def admission000_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2507023561856/2109375:ℝ),(492491136896/140625:ℝ),(7254282939904/2109375:ℝ),(158262629888/140625:ℝ)],
![(4559911402384/2109375:ℝ),(35802669808/5625:ℝ),(13173443826176/2109375:ℝ),(287156936704/140625:ℝ)],
![(2052887840528/2109375:ℝ),(402575608304/140625:ℝ),(5919160886272/2109375:ℝ),(128894306816/140625:ℝ)]]
theorem admission000_07_identity (δ p : ℝ) : admissionGuard .capC δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (251746693/512000000:ℝ) admission000_07_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission000_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission000_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (27/64:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 7 := by
 rw [admission000_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission000_07_coefficients]
def admission000_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4999930156/421875:ℝ),(114005516908/2109375:ℝ),(153329835116/2109375:ℝ),(4286152604/140625:ℝ)],
![(983191931/16875:ℝ),(429493099832/2109375:ℝ),(491463652504/2109375:ℝ),(2464029656/28125:ℝ)],
![(19579868119/421875:ℝ),(315487582924/2109375:ℝ),(338133817388/2109375:ℝ),(8033995676/140625:ℝ)]]
theorem admission000_08_identity (δ p : ℝ) : admissionGuard .capC δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (1249982539/196608000000:ℝ) admission000_08_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission000_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission000_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (27/64:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 8 := by
 rw [admission000_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission000_08_coefficients]
def admission000_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(10142993744577777163/164794921875000:ℝ),(26304331302673174307/164794921875000:ℝ),(1847682791211930097/13732910156250:ℝ),(300666546541138201/8239746093750:ℝ)],
![(111651940491627798091/1318359375000000:ℝ),(279625203741013695419/1318359375000000:ℝ),(4663402822981777321/27465820312500:ℝ),(174725459869107544/4119873046875:ℝ)],
![(30507990535005580787/1318359375000000:ℝ),(69190553319628300963/1318359375000000:ℝ),(968037240557917127/27465820312500:ℝ),(48784373197076887/8239746093750:ℝ)]]
theorem admission000_09_identity (δ p : ℝ) : admissionGuard .capC δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (48784373197076887/15360000000000000000:ℝ) admission000_09_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission000_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission000_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (27/64:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 9 := by
 rw [admission000_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission000_09_coefficients]
def admission000_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(57863795342627/2197265625:ℝ),(256357738640671/3662109375:ℝ),(222978166318207/3662109375:ℝ),(189180259745743/10986328125:ℝ)],
![(496900716869206/10986328125:ℝ),(434631141126202/3662109375:ℝ),(371399480195698/3662109375:ℝ),(307205734077694/10986328125:ℝ)],
![(42491224932641/2441406250:ℝ),(217165075228623/4882812500:ℝ),(7145824485081/195312500:ℝ),(11615746690921/1220703125:ℝ)]]
theorem admission000_10_identity (δ p : ℝ) : admissionGuard .capC δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (104541720218289/20480000000000000:ℝ) admission000_10_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission000_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission000_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (27/64:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 10 := by
 rw [admission000_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission000_10_coefficients]
def admission000_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2104212212608/2109375:ℝ),(6243588474752/2109375:ℝ),(6176173587968/2109375:ℝ),(2036797325824/2109375:ℝ)],
![(3840861542768/2109375:ℝ),(11387402855536/2109375:ℝ),(450222039808/84375:ℝ),(3709009682432/2109375:ℝ)],
![(347329866032/421875:ℝ),(5143814380784/2109375:ℝ),(5079377407232/2109375:ℝ),(1672212356608/2109375:ℝ)]]
theorem admission000_11_identity (δ p : ℝ) : admissionGuard .capC δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (3266039759/7680000000:ℝ) admission000_11_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission000_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission000_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (27/64:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 11 := by
 rw [admission000_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission000_11_coefficients]
def admission000_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(168484760563712/10986328125:ℝ),(168484760563712/3662109375:ℝ),(168484760563712/3662109375:ℝ),(168484760563712/10986328125:ℝ)],
![(336969521127424/10986328125:ℝ),(336969521127424/3662109375:ℝ),(336969521127424/3662109375:ℝ),(336969521127424/10986328125:ℝ)],
![(168484760563712/10986328125:ℝ),(168484760563712/3662109375:ℝ),(168484760563712/3662109375:ℝ),(168484760563712/10986328125:ℝ)]]
theorem admission000_12_identity (δ p : ℝ) : admissionGuard .capC δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (41133974747/5000000000000:ℝ) admission000_12_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission000_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission000_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (27/64:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 12 := by
 rw [admission000_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission000_12_coefficients]
def admission000_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5929188164403456/762939453125:ℝ),(17787564493210368/762939453125:ℝ),(17787564493210368/762939453125:ℝ),(5929188164403456/762939453125:ℝ)],
![(11858376328806912/762939453125:ℝ),(35575128986420736/762939453125:ℝ),(35575128986420736/762939453125:ℝ),(11858376328806912/762939453125:ℝ)],
![(5929188164403456/762939453125:ℝ),(17787564493210368/762939453125:ℝ),(17787564493210368/762939453125:ℝ),(5929188164403456/762939453125:ℝ)]]
theorem admission000_13_identity (δ p : ℝ) : admissionGuard .capC δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (208448021404809/50000000000000000:ℝ) admission000_13_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission000_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission000_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (27/64:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 13 := by
 rw [admission000_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission000_13_coefficients]
def admission000_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(89553408896/2109375:ℝ),(257127657344/2109375:ℝ),(245780684288/2109375:ℝ),(15641287168/421875:ℝ)],
![(172317353584/2109375:ℝ),(493757324656/2109375:ℝ),(470940980992/2109375:ℝ),(29900201984/421875:ℝ)],
![(82763944688/2109375:ℝ),(236629667312/2109375:ℝ),(225160296704/2109375:ℝ),(14258914816/421875:ℝ)]]
theorem admission000_14_identity (δ p : ℝ) : admissionGuard .capC δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (27849443/1536000000:ℝ) admission000_14_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission000_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission000_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (27/64:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 14 := by
 rw [admission000_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission000_14_coefficients]
theorem admission000_all {δ p : ℝ}
 (hd : δ∈Set.Icc (3/8:ℝ) (27/64:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .capC δ p j := by
 intro j
 fin_cases j
 · exact admission000_00_pos hd hp
 · exact admission000_01_pos hd hp
 · exact admission000_02_pos hd hp
 · exact admission000_03_pos hd hp
 · exact admission000_04_pos hd hp
 · exact admission000_05_pos hd hp
 · exact admission000_06_pos hd hp
 · exact admission000_07_pos hd hp
 · exact admission000_08_pos hd hp
 · exact admission000_09_pos hd hp
 · exact admission000_10_pos hd hp
 · exact admission000_11_pos hd hp
 · exact admission000_12_pos hd hp
 · exact admission000_13_pos hd hp
 · exact admission000_14_pos hd hp
end
end DasStageAFinite
#print axioms DasStageAFinite.admission000_all
