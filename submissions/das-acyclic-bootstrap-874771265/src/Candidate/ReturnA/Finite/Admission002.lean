/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def admission002_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2415919104/1:ℝ),(64961380352/9:ℝ),(64692944896/9:ℝ),(21474836480/9:ℝ)],
![(4831838208/1:ℝ),(129922760704/9:ℝ),(129385889792/9:ℝ),(42949672960/9:ℝ)],
![(2415919104/1:ℝ),(64961380352/9:ℝ),(64692944896/9:ℝ),(21474836480/9:ℝ)]]
theorem admission002_00_identity (δ p : ℝ) : admissionGuard .capC δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (5/4:ℝ) admission002_00_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission002_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission002_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (111/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 0 := by
 rw [admission002_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission002_00_coefficients]
def admission002_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(17179869184/9:ℝ),(17179869184/3:ℝ),(17179869184/3:ℝ),(17179869184/9:ℝ)],
![(34359738368/9:ℝ),(34359738368/3:ℝ),(34359738368/3:ℝ),(34359738368/9:ℝ)],
![(17179869184/9:ℝ),(17179869184/3:ℝ),(17179869184/3:ℝ),(17179869184/9:ℝ)]]
theorem admission002_01_identity (δ p : ℝ) : admissionGuard .capC δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (1/1:ℝ) admission002_01_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission002_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission002_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (111/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 1 := by
 rw [admission002_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission002_01_coefficients]
def admission002_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(128681259302912/140625:ℝ),(1928373399977984/703125:ℝ),(1926527910412288/703125:ℝ),(213853602316288/234375:ℝ)],
![(257362518605824/140625:ℝ),(3856746799955968/703125:ℝ),(3853055820824576/703125:ℝ),(427707204632576/234375:ℝ)],
![(128681259302912/140625:ℝ),(1928373399977984/703125:ℝ),(1926527910412288/703125:ℝ),(213853602316288/234375:ℝ)]]
theorem admission002_02_identity (δ p : ℝ) : admissionGuard .capC δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (9560001/20000000:ℝ) admission002_02_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission002_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission002_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (111/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 2 := by
 rw [admission002_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission002_02_coefficients]
def admission002_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1438646272/1:ℝ),(115519520768/27:ℝ),(114508693504/27:ℝ),(37832622080/27:ℝ)],
![(8532262912/3:ℝ),(228340006912/27:ℝ),(226308915200/27:ℝ),(74759274496/27:ℝ)],
![(4216324096/3:ℝ),(112820486144/27:ℝ),(111800221696/27:ℝ),(36926652416/27:ℝ)]]
theorem admission002_03_identity (δ p : ℝ) : admissionGuard .capC δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (2201/3072:ℝ) admission002_03_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission002_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission002_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (111/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 3 := by
 rw [admission002_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission002_03_coefficients]
def admission002_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(16020973089792/78125:ℝ),(9415435183104/15625:ℝ),(46092784238592/78125:ℝ),(15036581412864/78125:ℝ)],
![(6580931205376/15625:ℝ),(290145298839296/234375:ℝ),(284156916137984/234375:ℝ),(30908528459776/78125:ℝ)],
![(16883682937088/78125:ℝ),(148913771092736/234375:ℝ),(145878563422208/234375:ℝ),(15871947046912/78125:ℝ)]]
theorem admission002_04_identity (δ p : ℝ) : admissionGuard .capC δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (258120027/2560000000:ℝ) admission002_04_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission002_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission002_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (111/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 4 := by
 rw [admission002_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission002_04_coefficients]
def admission002_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(22717847874176/140625:ℝ),(343061133993344/703125:ℝ),(345342384781696/703125:ℝ),(38623496719744/234375:ℝ)],
![(213579624836096/703125:ℝ),(129102145336832/140625:ℝ),(650257910756096/703125:ℝ),(72775602969344/234375:ℝ)],
![(99990385465216/703125:ℝ),(302449592690816/703125:ℝ),(12196621038976/28125:ℝ),(1366084249984/9375:ℝ)]]
theorem admission002_05_identity (δ p : ℝ) : admissionGuard .capC δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (781174886447/10485760000000:ℝ) admission002_05_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission002_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission002_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (111/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 5 := by
 rw [admission002_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission002_05_coefficients]
def admission002_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1181033836626944/2890625:ℝ),(92716602432072704/78046875:ℝ),(89785421993476096/78046875:ℝ),(5791346630066176/15609375:ℝ)],
![(7279313216156416/8671875:ℝ),(190604380152285952/78046875:ℝ),(184699418049609728/78046875:ℝ),(11921771368546304/15609375:ℝ)],
![(3736211706275584/8671875:ℝ),(97887777720213248/78046875:ℝ),(94913996056133632/78046875:ℝ),(6130424738480128/15609375:ℝ)]]
theorem admission002_06_identity (δ p : ℝ) : admissionGuard .capC δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (11046117077/56832000000:ℝ) admission002_06_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission002_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission002_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (111/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 6 := by
 rw [admission002_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission002_06_coefficients]
def admission002_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2066682099516416/2109375:ℝ),(685503593096192/234375:ℝ),(6139053971341312/2109375:ℝ),(5429876621312/5625:ℝ)],
![(4019721783693568/2109375:ℝ),(1333222944246016/234375:ℝ),(11938917819908096/2109375:ℝ),(263975540359168/140625:ℝ)],
![(1953039684177152/2109375:ℝ),(647719351149824/234375:ℝ),(5799863848566784/2109375:ℝ),(128228624826368/140625:ℝ)]]
theorem admission002_07_identity (δ p : ℝ) : admissionGuard .capC δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (978306769/2048000000:ℝ) admission002_07_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission002_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission002_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (111/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 7 := by
 rw [admission002_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission002_07_coefficients]
def admission002_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(71530498756472/2109375:ℝ),(220483190032792/2109375:ℝ),(226424578740632/2109375:ℝ),(25823772408536/703125:ℝ)],
![(158494830202828/2109375:ℝ),(486217298526512/2109375:ℝ),(497057976488752/2109375:ℝ),(56444783949232/703125:ℝ)],
![(86964331446356/2109375:ℝ),(53146821698744/421875:ℝ),(54126679549624/421875:ℝ),(30621011540696/703125:ℝ)]]
theorem admission002_08_identity (δ p : ℝ) : admissionGuard .capC δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (8941312344559/503316480000000:ℝ) admission002_08_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission002_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission002_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (111/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 8 := by
 rw [admission002_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission002_08_coefficients]
def admission002_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(11894294125066813163/823974609375:ℝ),(800540657221979446819/20599365234375:ℝ),(236222675404193939648/6866455078125:ℝ),(8219611634184658048/823974609375:ℝ)],
![(338736510839706516599/16479492187500:ℝ),(4389479609370342001283/82397460937500:ℝ),(307904654133383359504/6866455078125:ℝ),(49955198153806732288/4119873046875:ℝ)],
![(100850628338370253339/16479492187500:ℝ),(1187316980482424214007/82397460937500:ℝ),(71681978729189419856/6866455078125:ℝ),(8857139982883442048/4119873046875:ℝ)]]
theorem admission002_09_identity (δ p : ℝ) : admissionGuard .capC δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (69196406116276891/61440000000000000000:ℝ) admission002_09_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission002_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission002_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (111/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 9 := by
 rw [admission002_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission002_09_coefficients]
def admission002_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(142547531500998416/10986328125:ℝ),(5403240978679664/146484375:ℝ),(127579132373734784/3662109375:ℝ),(120041855221227968/10986328125:ℝ)],
![(28772174978233288/1220703125:ℝ),(81453640081544936/1220703125:ℝ),(76566398800015008/1220703125:ℝ),(4776986739340672/244140625:ℝ)],
![(115493212520376541/10986328125:ℝ),(108386391730521787/3662109375:ℝ),(101241850152338908/3662109375:ℝ),(94059587785827904/10986328125:ℝ)]]
theorem admission002_10_identity (δ p : ℝ) : admissionGuard .capC δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (1469681059153561/327680000000000000:ℝ) admission002_10_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission002_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission002_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (111/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 10 := by
 rw [admission002_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission002_10_coefficients]
def admission002_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1775182440315904/2109375:ℝ),(5309268625144832/2109375:ℝ),(5293098514055168/2109375:ℝ),(351802465845248/421875:ℝ)],
![(3456837500792576/2109375:ℝ),(10338147724734208/2109375:ℝ),(10306001130274816/2109375:ℝ),(3424690906333184/2109375:ℝ)],
![(1681655060476672/2109375:ℝ),(5028879099589376/2109375:ℝ),(5012902616219648/2109375:ℝ),(1665678577106944/2109375:ℝ)]]
theorem admission002_11_identity (δ p : ℝ) : admissionGuard .capC δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (12708119027/30720000000:ℝ) admission002_11_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission002_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission002_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (111/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 11 := by
 rw [admission002_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission002_11_coefficients]
def admission002_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(172528394817241088/10986328125:ℝ),(172528394817241088/3662109375:ℝ),(172528394817241088/3662109375:ℝ),(172528394817241088/10986328125:ℝ)],
![(345056789634482176/10986328125:ℝ),(345056789634482176/3662109375:ℝ),(345056789634482176/3662109375:ℝ),(345056789634482176/10986328125:ℝ)],
![(172528394817241088/10986328125:ℝ),(172528394817241088/3662109375:ℝ),(172528394817241088/3662109375:ℝ),(172528394817241088/10986328125:ℝ)]]
theorem admission002_12_identity (δ p : ℝ) : admissionGuard .capC δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (41133974747/5000000000000:ℝ) admission002_12_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission002_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission002_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (111/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 12 := by
 rw [admission002_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission002_12_coefficients]
def admission002_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6071488680349138944/762939453125:ℝ),(18214466041047416832/762939453125:ℝ),(18214466041047416832/762939453125:ℝ),(6071488680349138944/762939453125:ℝ)],
![(12142977360698277888/762939453125:ℝ),(36428932082094833664/762939453125:ℝ),(36428932082094833664/762939453125:ℝ),(12142977360698277888/762939453125:ℝ)],
![(6071488680349138944/762939453125:ℝ),(18214466041047416832/762939453125:ℝ),(18214466041047416832/762939453125:ℝ),(6071488680349138944/762939453125:ℝ)]]
theorem admission002_13_identity (δ p : ℝ) : admissionGuard .capC δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (208448021404809/50000000000000000:ℝ) admission002_13_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission002_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission002_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (111/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 13 := by
 rw [admission002_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission002_13_coefficients]
def admission002_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3071580167168/84375:ℝ),(227457031568384/2109375:ℝ),(224557889552384/2109375:ℝ),(2955614486528/84375:ℝ)],
![(30363411919616/421875:ℝ),(449620613807872/2109375:ℝ),(443814841925632/2109375:ℝ),(29202257543168/421875:ℝ)],
![(15005511083776/421875:ℝ),(222163582239488/2109375:ℝ),(219256952373248/2109375:ℝ),(14424185110528/421875:ℝ)]]
theorem admission002_14_identity (δ p : ℝ) : admissionGuard .capC δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (110047799/6144000000:ℝ) admission002_14_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission002_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission002_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (27/64:ℝ) (111/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .capC δ p 14 := by
 rw [admission002_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission002_14_coefficients]
theorem admission002_all {δ p : ℝ}
 (hd : δ∈Set.Icc (27/64:ℝ) (111/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .capC δ p j := by
 intro j
 fin_cases j
 · exact admission002_00_pos hd hp
 · exact admission002_01_pos hd hp
 · exact admission002_02_pos hd hp
 · exact admission002_03_pos hd hp
 · exact admission002_04_pos hd hp
 · exact admission002_05_pos hd hp
 · exact admission002_06_pos hd hp
 · exact admission002_07_pos hd hp
 · exact admission002_08_pos hd hp
 · exact admission002_09_pos hd hp
 · exact admission002_10_pos hd hp
 · exact admission002_11_pos hd hp
 · exact admission002_12_pos hd hp
 · exact admission002_13_pos hd hp
 · exact admission002_14_pos hd hp
end
end DasStageAFinite
#print axioms DasStageAFinite.admission002_all
