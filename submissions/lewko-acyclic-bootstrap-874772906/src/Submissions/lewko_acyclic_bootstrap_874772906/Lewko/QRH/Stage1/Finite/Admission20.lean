/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def admission20_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(38281681681119839/314793053919999:ℝ),(37566888627199840/314793053919999:ℝ)]]
theorem admission20_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (1173965269599995/1259172215679996:ℝ) admission20_00_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission20_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_00_coefficients]
def admission20_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(27893510901759872/314793053919999:ℝ),(27493510901759872/314793053919999:ℝ)]]
theorem admission20_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (214793053919999/314793053919999:ℝ) admission20_01_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission20_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_01_coefficients]
def admission20_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(46801102449284/1038920970033:ℝ),(46165946332096/1038920970033:ℝ)]]
theorem admission20_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (721342911439/2077841940066:ℝ) admission20_02_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission20_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_02_coefficients]
def admission20_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(4151754078015429087488/2833137485279991:ℝ),(910387913047063345408/314793053919999:ℝ),(4042017939408141021184/2833137485279991:ℝ)],
![(4096777932775303867520/2833137485279991:ℝ),(898181098371689314432/314793053919999:ℝ),(3987136352569899962368/2833137485279991:ℝ)]]
theorem admission20_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (973421961076635733/1934088523284473856:ℝ) admission20_03_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission20_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_03_coefficients]
def admission20_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(80294177743924456/346306990011:ℝ),(157097798381485312/346306990011:ℝ),(76820134696607744/346306990011:ℝ)],
![(82308463800854356/346306990011:ℝ),(483244859289636736/1038920970033:ℝ),(236369645220331520/1038920970033:ℝ)]]
theorem admission20_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (9377457848707/118206119257088:ℝ) admission20_04_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission20_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_04_coefficients]
def admission20_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(9013587285353363492234/65581886233333125:ℝ),(32493206507655413731652/118047395219999625:ℝ),(81330219970708757493154/590236976099998125:ℝ)],
![(8314110134259594872558/65581886233333125:ℝ),(149956451369466282269068/590236976099998125:ℝ),(75115759738672811248546/590236976099998125:ℝ)]]
theorem admission20_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (4157055067129797436279/91690122585338019840000:ℝ) admission20_05_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission20_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_05_coefficients]
def admission20_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1448005118603378826776360546277871033856/32998524043161039460837289280333:ℝ),(1413606731295244675823284826493244017152/10999508014387013153612429760111:ℝ),(4138647591053982904013816704511047270400/32998524043161039460837289280333:ℝ),(1345829705777174133020253971309186252800/32998524043161039460837289280333:ℝ)],
![(1480696618118613305068360186012790175488/32998524043161039460837289280333:ℝ),(1446020334631874669922499646743073029376/10999508014387013153612429760111:ℝ),(4235063488575526280451350639250838077440/32998524043161039460837289280333:ℝ),(1377696256778492087884193485034409164800/32998524043161039460837289280333:ℝ)]]
theorem admission20_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (641741612328135553846480355887025/5631748103366150734649564037176832:ℝ) admission20_06_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission20_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_06_coefficients]
def admission20_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2102073574031678986820468967557240/2943405944443942508325509703:ℝ),(4137892231039879324471994648299264/2943405944443942508325509703:ℝ),(2036081072002656948079770527887360/2943405944443942508325509703:ℝ)],
![(2038610814409015610440397162564060/2943405944443942508325509703:ℝ),(4011998362751665561058772300564352/2943405944443942508325509703:ℝ),(1973645877290480074033031397560320/2943405944443942508325509703:ℝ)]]
theorem admission20_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (481847138010371111824470556045/2009365124740398085683547957248:ℝ) admission20_07_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission20_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_07_coefficients]
def admission20_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(125760181965801716700431817492762641188125700279637359/172039352076873954479673888890625000000000000000:ℝ),(3705865968594890482798372023397090032456519697132773913/1548354168691865590317065000015625000000000000000:ℝ),(36140778922147278187440732214640884686859462582917654179/13935187518226790312853585000140625000000000000000:ℝ),(12974342752105194557194290406603923291741160781373315041/13935187518226790312853585000140625000000000000000:ℝ)],
![(5584338941343448544499707769281013810536956682169097/4300983801921848861991847222265625000000000000:ℝ),(126183996128622036017247469431854201505018165620223797/30967083373837311806341300000312500000000000000:ℝ),(59283064360261049453066029364524221546404236326557596451/13935187518226790312853585000140625000000000000000:ℝ),(20593304295904128854023598288355481280663023322684762081/13935187518226790312853585000140625000000000000000:ℝ)]]
theorem admission20_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (125760181965801716700431817492762641188125700279637359/61575282566266942700366004127531008000000000000000000000:ℝ) admission20_08_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission20_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_08_coefficients]
def admission20_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(33095466445845384819245775418242434319401599/8709492198891743945533490625087890625:ℝ),(31975620213707077404644233809438016124957629/2903164066297247981844496875029296875:ℝ),(92581888098893849907619578424983877953140608/8709492198891743945533490625087890625:ℝ),(5950121355211695857383512158131455263908864/1741898439778348789106698125017578125:ℝ)],
![(55357218827648003263298908200318352127278439/17418984397783487891066981250175781250:ℝ),(53241888266102472931448079854811398246139509/5806328132594495963688993750058593750:ℝ),(76702972262434700263228464676717355152821184/8709492198891743945533490625087890625:ℝ),(4903772719325607897348359187864850824137728/1741898439778348789106698125017578125:ℝ)]]
theorem admission20_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (4788840546216413962254257019399268382947/608837632796340619962115031046144000000000:ℝ) admission20_09_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission20_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_09_coefficients]
def admission20_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4919583978439653814872232097536/27667358254687412109375:ℝ),(4723026071873013783629117385472/9222452751562470703125:ℝ),(1509031287616787399368740891136/3074150917187490234375:ℝ),(4331801895934199058303547961344/27667358254687412109375:ℝ)],
![(88915335279977829234774287104/273934240145419921875:ℝ),(1719081846845595046785521878784/1844490550312494140625:ℝ),(24634680977177460376758507371008/27667358254687412109375:ℝ),(2609643866611265142562627395584/9222452751562470703125:ℝ)],
![(809694843594145811187516107456/5533471650937482421875:ℝ),(1286709447885795400206106351168/3074150917187490234375:ℝ),(11017039834877527816671737709184/27667358254687412109375:ℝ),(3485143941766723270754361085952/27667358254687412109375:ℝ)]]
theorem admission20_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (850865220157891423524013937/412605551634021089280000000000:ℝ) admission20_10_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission20_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_10_coefficients]
def admission20_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1724525227921726413891687356463752/2943405944443942508325509703:ℝ),(3394790589128587214073626615575552/2943405944443942508325509703:ℝ),(1670516766791251337530003769565184/2943405944443942508325509703:ℝ)],
![(1671157887874948498833302758764452/2943405944443942508325509703:ℝ),(3288941420353211452747697877764608/2943405944443942508325509703:ℝ),(1618030710869744105876048217038848/2943405944443942508325509703:ℝ)]]
theorem admission20_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (197513514510466809799322292119/1004682562370199042841773978624:ℝ) admission20_11_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission20_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_11_coefficients]
def admission20_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission20_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission20_12_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission20_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_12_coefficients]
def admission20_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(8139931613966420001/2000000000000000000000:ℝ)]]
theorem admission20_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (8139931613966420001/2000000000000000000000:ℝ) admission20_13_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission20_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_13_coefficients]
def admission20_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission20_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission20_14_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission20_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission20_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission20_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission20_14_coefficients]
theorem admission20_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission20_00_pos hδ hp
 · exact admission20_01_pos hδ hp
 · exact admission20_02_pos hδ hp
 · exact admission20_03_pos hδ hp
 · exact admission20_04_pos hδ hp
 · exact admission20_05_pos hδ hp
 · exact admission20_06_pos hδ hp
 · exact admission20_07_pos hδ hp
 · exact admission20_08_pos hδ hp
 · exact admission20_09_pos hδ hp
 · exact admission20_10_pos hδ hp
 · exact admission20_11_pos hδ hp
 · exact admission20_12_pos hδ hp
 · exact admission20_13_pos hδ hp
 · exact admission20_14_pos hδ hp
#print axioms admission20_all
end
end LewkoStage1Finite
