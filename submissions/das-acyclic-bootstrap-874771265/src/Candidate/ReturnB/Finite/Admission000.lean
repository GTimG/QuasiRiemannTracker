/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
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
def admission000_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(101430599794694903/1647949218750:ℝ),(87681738259022389/549316406250:ℝ),(110861876386022942/823974609375:ℝ),(2004462924447454/54931640625:ℝ)],
![(1116529600772713271/13183593750000:ℝ),(932093750856210013/4394531250000:ℝ),(139903826260503703/823974609375:ℝ),(2329709655899552/54931640625:ℝ)],
![(305084802415154047/13183593750000:ℝ),(230639844784030901/4394531250000:ℝ),(29041949874480761/823974609375:ℝ),(325246731452098/54931640625:ℝ)]]
theorem admission000_09_identity (δ p : ℝ) : admissionGuard .capC δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (162623365726049/51200000000000000:ℝ) admission000_09_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission000_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission000_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (27/64:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 9 := by
 rw [admission000_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission000_09_coefficients]
def admission000_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2314585457228/87890625:ℝ),(3418157445748/48828125:ℝ),(8919284018348/146484375:ℝ),(7567362329452/439453125:ℝ)],
![(19876393596484/439453125:ℝ),(5795199608676/48828125:ℝ),(14856320648072/146484375:ℝ),(12288559062616/439453125:ℝ)],
![(3399384611773/195312500:ℝ),(8686854405897/195312500:ℝ),(71460674271/1953125:ℝ),(464649408244/48828125:ℝ)]]
theorem admission000_10_identity (δ p : ℝ) : admissionGuard .capC δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (1045461168549/204800000000000:ℝ) admission000_10_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
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
def admission000_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6739246727168/439453125:ℝ),(6739246727168/146484375:ℝ),(6739246727168/146484375:ℝ),(6739246727168/439453125:ℝ)],
![(13478493454336/439453125:ℝ),(13478493454336/146484375:ℝ),(13478493454336/146484375:ℝ),(13478493454336/439453125:ℝ)],
![(6739246727168/439453125:ℝ),(6739246727168/146484375:ℝ),(6739246727168/146484375:ℝ),(6739246727168/439453125:ℝ)]]
theorem admission000_12_identity (δ p : ℝ) : admissionGuard .capC δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (411330977/50000000000:ℝ) admission000_12_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission000_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission000_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (3/8:ℝ) (27/64:ℝ)) (hp : p∈Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 12 := by
 rw [admission000_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission000_12_coefficients]
def admission000_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2134323762159616/274658203125:ℝ),(2134323762159616/91552734375:ℝ),(2134323762159616/91552734375:ℝ),(2134323762159616/274658203125:ℝ)],
![(4268647524319232/274658203125:ℝ),(4268647524319232/91552734375:ℝ),(4268647524319232/91552734375:ℝ),(4268647524319232/274658203125:ℝ)],
![(2134323762159616/274658203125:ℝ),(2134323762159616/91552734375:ℝ),(2134323762159616/91552734375:ℝ),(2134323762159616/274658203125:ℝ)]]
theorem admission000_13_identity (δ p : ℝ) : admissionGuard .capC δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (260537568623/62500000000000:ℝ) admission000_13_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
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
end DasStageBFinite
#print axioms DasStageBFinite.admission000_all
