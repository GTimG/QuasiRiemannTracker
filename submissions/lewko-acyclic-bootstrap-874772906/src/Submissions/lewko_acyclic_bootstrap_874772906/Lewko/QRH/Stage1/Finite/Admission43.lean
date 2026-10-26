/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def admission43_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(2404995665194709759/314793053919999:ℝ),(2404280872140789760/314793053919999:ℝ)]]
theorem admission43_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (1173965269599995/1259172215679996:ℝ) admission43_00_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission43_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_00_coefficients]
def admission43_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1759984697712631808/314793053919999:ℝ),(1759584697712631808/314793053919999:ℝ)]]
theorem admission43_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (214793053919999/314793053919999:ℝ) admission43_01_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission43_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_01_coefficients]
def admission43_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(2955255721371332/1038920970033:ℝ),(2954620565254144/1038920970033:ℝ)]]
theorem admission43_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (721342911439/2077841940066:ℝ) admission43_02_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission43_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_02_coefficients]
def admission43_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1051496806897154259832168448/2833137485279991:ℝ),(233616147817684826151870464/314793053919999:ℝ),(1051048541480009175534665728/2833137485279991:ℝ)],
![(1051272005638927103868944384/2833137485279991:ℝ),(233566192679738538225188864/314793053919999:ℝ),(1050823746500319740157755392/2833137485279991:ℝ)]]
theorem admission43_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (31316988065848342781/61890832745103163392:ℝ) admission43_03_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission43_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_03_coefficients]
def admission43_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(60613739741673124746740/1038920970033:ℝ),(121184876368298032209920/1038920970033:ℝ),(60571139805581273989120/1038920970033:ℝ)],
![(60637952504819429321912/1038920970033:ℝ),(40411097794159914205184/346306990011:ℝ),(20198448019083945312256/346306990011:ℝ)]]
theorem admission43_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (3610321271752195/45391149794721792:ℝ) admission43_04_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission43_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_04_coefficients]
def admission43_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2257186872780057246487216264/65581886233333125:ℝ),(40630228848435557929753682392/590236976099998125:ℝ),(20315546125432581978819073516/590236976099998125:ℝ)],
![(2254358029272396624920000116/65581886233333125:ℝ),(40579314827929616168908255192/590236976099998125:ℝ),(20290091696322162743001159148/590236976099998125:ℝ)]]
theorem admission43_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (563589507318099156230000029/12018007747505424936468480000:ℝ) admission43_05_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission43_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_05_coefficients]
def admission43_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(22660139948075544604682784921872378841384304640/32998524043161039460837289280333:ℝ),(22651283323730989980082560454655147725462814720/10999508014387013153612429760111:ℝ),(67927284259784813323034898920611986310241976320/32998524043161039460837289280333:ℝ),(22633574236487080010032574890770921975237836800/32998524043161039460837289280333:ℝ)],
![(22668496917113564299307092021248478837176762368/32998524043161039460837289280333:ℝ),(22659639177953292214620765355138650495423512576/10999508014387013153612429760111:ℝ),(67952348478559425851554976650521979459374940160/32998524043161039460837289280333:ℝ),(22641927861632769503992427450656906810281164800/32998524043161039460837289280333:ℝ)]]
theorem admission43_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (82340463401076995105659352305414075/720863757230867294035144196758634496:ℝ) admission43_06_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission43_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_06_coefficients]
def admission43_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(524296918996023484446154526958468950420/2943405944443942508325509703:ℝ),(1048325425607086042273214809045251235840/2943405944443942508325509703:ℝ),(524028523352503596905796513105360977920/2943405944443942508325509703:ℝ)],
![(524041118931749074302591606270488636024/2943405944443942508325509703:ℝ),(1047813890989356602280043458468038950912/2943405944443942508325509703:ℝ),(523772788794962520429701069627541422080/2943405944443942508325509703:ℝ)]]
theorem admission43_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (15609645509569720042637022424565/64299683991692738741873534631936:ℝ) admission43_07_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission43_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_07_coefficients]
def admission43_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(15965508747138468194171313200567944728867689396846359298521/1075245950480462215497961805566406250000000000:ℝ),(86312941128450343503125533308160952906835444268001053466851/1935442710864831987896331250019531250000000000:ℝ),(3888545941484041786361036031202574089913886497299743624576773/87094921988917439455334906250878906250000000000:ℝ),(1297669799134889243663669597948768549731928398045286477998679/87094921988917439455334906250878906250000000000:ℝ)],
![(80598544586392823045287167270275410857967518160829326187039/5376229752402311077489809027832031250000000000:ℝ),(435727298223218685149124463536446313956345239485265220150921/9677213554324159939481656250097656250000000000:ℝ),(19630009837623871313036074810323389207555451916137310562286361/435474609944587197276674531254394531250000000000:ℝ),(262030541145649883523118947196446060468195595526594230565803/17418984397783487891066981250175781250000000000:ℝ)]]
theorem admission43_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (15965508747138468194171313200567944728867689396846359298521/6456636349220592570897898314402995424460800000000000000000000:ℝ) admission43_08_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission43_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_08_coefficients]
def admission43_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(89575945806754389108066774846978795106688622634364/1741898439778348789106698125017578125:ℝ),(89518392735901055187270643316889702879081371274848/580632813259449596368899375005859375:ℝ),(268382530963482133523160971950602793497976235098112/1741898439778348789106698125017578125:ℝ),(89403298563981886722201082986569968695080157970432/1741898439778348789106698125017578125:ℝ)],
![(446507506479393720019360092917680815311519766590344/8709492198891743945533490625087890625:ℝ),(89243998395800301834401511058761702989393390505536/580632813259449596368899375005859375:ℝ),(1337797492186247532550194166446030716675380135591936/8709492198891743945533490625087890625:ℝ),(89129004547176164080005627846332399940820793294848/1741898439778348789106698125017578125:ℝ)]]
theorem admission43_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (166015707975581593960534088027351349481979/19482804249482899838787680993476608000000000:ℝ) admission43_09_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission43_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_09_coefficients]
def admission43_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4122195156193154017956750213807090225152/27667358254687412109375:ℝ),(4118945574660746621311292843875901796352/9222452751562470703125:ℝ),(12347088473050922979411641163282140102656/27667358254687412109375:ℝ),(50770949448416325301853553647673147392/341572324131943359375:ℝ)],
![(8230298845029658177737043746445219446784/27667358254687412109375:ℝ),(8223801782151766010410918593513238380544/9222452751562470703125:ℝ),(8217305048135996541465853540658057314304/9222452751562470703125:ℝ),(8210808643102144133089348587879676248064/27667358254687412109375:ℝ)],
![(40674262823693266251305566323703300096/273934240145419921875:ℝ),(91218956986597257148085159870934728704/204943394479166015625:ℝ),(12304817243722493898800777870621636820992/27667358254687412109375:ℝ),(4098358595784793223753643486739481755648/27667358254687412109375:ℝ)]]
theorem admission43_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (954223469780942710059146277313/422508084873237595422720000000000:ℝ) admission43_10_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission43_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_10_coefficients]
def admission43_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(429966072904807963877219480176248665708/2943405944443942508325509703:ℝ),(859712654551459103737829661725217488896/2943405944443942508325509703:ℝ),(429746597681655033032990434329276448768/2943405944443942508325509703:ℝ)],
![(429751033883882606223906338693191849352/2943405944443942508325509703:ℝ),(859282632649706445373047304710425214976/2943405944443942508325509703:ℝ),(429531614796600539412135832386128576512/2943405944443942508325509703:ℝ)]]
theorem admission43_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (6400519829937823704065916424783/32149841995846369370936767315968:ℝ) admission43_11_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission43_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_11_coefficients]
def admission43_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission43_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission43_12_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission43_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_12_coefficients]
def admission43_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(8139931613966420001/2000000000000000000000:ℝ)]]
theorem admission43_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (8139931613966420001/2000000000000000000000:ℝ) admission43_13_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission43_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_13_coefficients]
def admission43_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission43_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission43_14_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission43_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_14_coefficients]
theorem admission43_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission43_00_pos hδ hp
 · exact admission43_01_pos hδ hp
 · exact admission43_02_pos hδ hp
 · exact admission43_03_pos hδ hp
 · exact admission43_04_pos hδ hp
 · exact admission43_05_pos hδ hp
 · exact admission43_06_pos hδ hp
 · exact admission43_07_pos hδ hp
 · exact admission43_08_pos hδ hp
 · exact admission43_09_pos hδ hp
 · exact admission43_10_pos hδ hp
 · exact admission43_11_pos hδ hp
 · exact admission43_12_pos hδ hp
 · exact admission43_13_pos hδ hp
 · exact admission43_14_pos hδ hp
#print axioms admission43_all
end
end LewkoStage1Finite
