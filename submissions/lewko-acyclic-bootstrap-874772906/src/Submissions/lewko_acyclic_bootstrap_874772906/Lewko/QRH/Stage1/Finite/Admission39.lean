/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def admission39_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(601785011089117439/314793053919999:ℝ),(601070218035197440/314793053919999:ℝ)]]
theorem admission39_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (1173965269599995/1259172215679996:ℝ) admission39_00_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission39_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_00_coefficients]
def admission39_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(440296174428157952/314793053919999:ℝ),(439896174428157952/314793053919999:ℝ)]]
theorem admission39_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (214793053919999/314793053919999:ℝ) admission39_01_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission39_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_01_coefficients]
def admission39_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(739290297430724/1038920970033:ℝ),(738655141313536/1038920970033:ℝ)]]
theorem admission39_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (721342911439/2077841940066:ℝ) admission39_02_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission39_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_02_coefficients]
def admission39_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(16464705072470338530603008/2833137485279991:ℝ),(10967127906442023869796352/944379161759997:ℝ),(16436683146855733078786048/2833137485279991:ℝ)],
![(162877760587181372999680/28050866190891:ℝ),(10957760925443487346898944/944379161759997:ℝ),(16422633460625143367729152/2833137485279991:ℝ)]]
theorem admission39_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (15661843739152091377/30945416372551581696:ℝ) admission39_03_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission39_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_03_coefficients]
def admission39_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(948139012509757045000/1038920970033:ℝ),(1893616799445936640000/1038920970033:ℝ),(945478580881326080000/1038920970033:ℝ)],
![(949653906584469911500/1038920970033:ℝ),(1896644458614903511040/1038920970033:ℝ),(946991346610736201728/1038920970033:ℝ)]]
theorem admission39_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (450839319649375/5673893724340224:ℝ) admission39_04_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission39_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_04_coefficients]
def admission39_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(106329626616345753259957474/196745658699999375:ℝ),(638030542693502812005774364/590236976099998125:ℝ),(319041446065629205435276942/590236976099998125:ℝ)],
![(105798895761645722053806886/196745658699999375:ℝ),(634847448483424585226135452/590236976099998125:ℝ),(317450544246228003196657294/590236976099998125:ℝ)]]
theorem admission39_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (52899447880822861026903443/1126688226328633587793920000:ℝ) admission39_05_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission39_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_05_coefficients]
def admission39_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(88745843955733491405395940503913011374530560/32998524043161039460837289280333:ℝ),(88607416305896765905421614410507499147386880/10999508014387013153612429760111:ℝ),(265407225997703051032566900239546829378682880/32998524043161039460837289280333:ℝ),(88330820990714282324738060511937343311052800/32998524043161039460837289280333:ℝ)],
![(88876578445954950346972938164603068858806272/32998524043161039460837289280333:ℝ),(88738081050758343563067389526600665423908864/10999508014387013153612429760111:ℝ),(265799011135003748976967492124954783771525120/32998524043161039460837289280333:ℝ),(88461346383615680667860756760155856358604800/32998524043161039460837289280333:ℝ)]]
theorem admission39_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (10283060952871372262567521598182775/90107969653858411754393024594829312:ℝ) admission39_06_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission39_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_06_coefficients]
def admission39_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(8220727428654209263359616783913838920/2943405944443942508325509703:ℝ),(16424652325415577191975827778169671680/2943405944443942508325509703:ℝ),(8203929087229185981409035734634987520/2943405944443942508325509703:ℝ)],
![(8204727639060023596871522072569238060/2943405944443942508325509703:ℝ),(16392669130061120872218781438048933888/2943405944443942508325509703:ℝ),(8187945677382868701653070517271265280/2943405944443942508325509703:ℝ)]]
theorem admission39_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (7808633496649616910603590504905/32149841995846369370936767315968:ℝ) admission39_07_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission39_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_07_coefficients]
def admission39_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1089609071460033237561441255892488135423819532426149838877/19354427108648319878963312500195312500000000000:ℝ),(9853368084859593491119194627806323844589163819687914828649/58063281325944959636889937500585937500000000000:ℝ),(29700746282792930918402019257098865786105249914466627128561/174189843977834878910669812501757812500000000000:ℝ),(9947123627846453187196405861244663888411900311691356192507/174189843977834878910669812501757812500000000000:ℝ)],
![(2832635061238401195114487480811419034471340512266750583897/48386067771620799697408281250488281250000000000:ℝ),(25206860052926857292811521844620639763374541866841872243/142872247357148030602583507629394531250000000:ℝ),(154359660292509707625977202714753584072302706981975616587957/870949219889174394553349062508789062500000000000:ℝ),(2067442891777791724638813284958068731488939934761300456191/34837968795566975782133962500351562500000000000:ℝ)]]
theorem admission39_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (1089609071460033237561441255892488135423819532426149838877/453982243304572915141258475231460615782400000000000000000000:ℝ) admission39_08_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission39_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_08_coefficients]
def admission39_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(356227414704427435873502111669558967854868949736/1741898439778348789106698125017578125:ℝ),(355323851721108512781630174645975102279904958704/580632813259449596368899375005859375:ℝ),(1063261619125271121210527607108637339022414741504/1741898439778348789106698125017578125:ℝ),(353517479028143661292901966982500952000459440128/1741898439778348789106698125017578125:ℝ)],
![(1759660806947694602146490346335176384199794241548/8709492198891743945533490625087890625:ℝ),(1755158681808469023229392818463241470763563031688/2903164066297247981844496875029296875:ℝ),(5251973411745183397245649099336274049544374501376/8709492198891743945533490625087890625:ℝ),(349231635015554245008597980416288940215156867072/1741898439778348789106698125017578125:ℝ)]]
theorem admission39_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (83263310197723923923635001281807169965543/9741402124741449919393840496738304000000000:ℝ) admission39_09_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission39_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_09_coefficients]
def admission39_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(456579191388432927731986627931820032/3074150917187490234375:ℝ),(1365491398418688032155713412294660096/3074150917187490234375:ℝ),(12251214767345743806566143467144740864/27667358254687412109375:ℝ),(4071004907808799429252602407879180288/27667358254687412109375:ℝ)],
![(100783083722032639310668659775533056/341572324131943359375:ℝ),(2712661826612260637667482863919951872/3074150917187490234375:ℝ),(24337639014662656411179426077904601088/27667358254687412109375:ℝ),(8087112364113634143836241744443211776/27667358254687412109375:ℝ)],
![(90092619161876605316933117734298624/614830183437498046875:ℝ),(449051346914593388535746963615988736/1024716972395830078125:ℝ),(1342919651476820244661092076241453056/3074150917187490234375:ℝ),(446228706958126496263516774064979968/3074150917187490234375:ℝ)]]
theorem admission39_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (26597303566821008697957800273/11736335690923266539520000000000:ℝ) admission39_10_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission39_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_10_coefficients]
def admission39_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(6741964773524692252721594286505813688/2943405944443942508325509703:ℝ),(13470187778581493565338686235005075456/2943405944443942508325509703:ℝ),(6728227019091765742443888157841686528/2943405944443942508325509703:ℝ)],
![(6728514306070675711264506971522524628/2943405944443942508325509703:ℝ),(13443300885038764081963572709987459072/2943405944443942508325509703:ℝ),(6714790588775859891140475536394944512/2943405944443942508325509703:ℝ)]]
theorem admission39_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (3201861662280969567842710273931/16074920997923184685468383657984:ℝ) admission39_11_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission39_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_11_coefficients]
def admission39_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission39_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission39_12_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission39_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_12_coefficients]
def admission39_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(8139931613966420001/2000000000000000000000:ℝ)]]
theorem admission39_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (8139931613966420001/2000000000000000000000:ℝ) admission39_13_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission39_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_13_coefficients]
def admission39_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission39_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission39_14_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission39_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission39_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission39_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission39_14_coefficients]
theorem admission39_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (1875/4096:ℝ) (3753/8192:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission39_00_pos hδ hp
 · exact admission39_01_pos hδ hp
 · exact admission39_02_pos hδ hp
 · exact admission39_03_pos hδ hp
 · exact admission39_04_pos hδ hp
 · exact admission39_05_pos hδ hp
 · exact admission39_06_pos hδ hp
 · exact admission39_07_pos hδ hp
 · exact admission39_08_pos hδ hp
 · exact admission39_09_pos hδ hp
 · exact admission39_10_pos hδ hp
 · exact admission39_11_pos hδ hp
 · exact admission39_12_pos hδ hp
 · exact admission39_13_pos hδ hp
 · exact admission39_14_pos hδ hp
#print axioms admission39_all
end
end LewkoStage1Finite
