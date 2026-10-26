/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage1Finite
noncomputable section
def admission29_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(38281681681119839/314793053919999:ℝ),(37566888627199840/314793053919999:ℝ)]]
theorem admission29_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (1173965269599995/1259172215679996:ℝ) admission29_00_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission29_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_00_coefficients]
def admission29_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(27893510901759872/314793053919999:ℝ),(27493510901759872/314793053919999:ℝ)]]
theorem admission29_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (214793053919999/314793053919999:ℝ) admission29_01_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission29_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_01_coefficients]
def admission29_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(46801102449284/1038920970033:ℝ),(46165946332096/1038920970033:ℝ)]]
theorem admission29_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (721342911439/2077841940066:ℝ) admission29_02_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission29_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_02_coefficients]
def admission29_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(16236709322017874944/22308169175433:ℝ),(452134072987864484864/314793053919999:ℝ),(2007288572994510245888/2833137485279991:ℝ)],
![(2007085938656144897920/2833137485279991:ℝ),(439927258312490453888/314793053919999:ℝ),(1952406986156269187072/2833137485279991:ℝ)]]
theorem admission29_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (476661861854557907/967044261642236928:ℝ) admission29_03_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission29_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_03_coefficients]
def admission29_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(123529504221422240/1038920970033:ℝ),(241688920586900480/1038920970033:ℝ),(118184822610165760/1038920970033:ℝ)],
![(129572362392211940/1038920970033:ℝ),(84546794910693760/346306990011:ℝ),(41364687913558016/346306990011:ℝ)]]
theorem admission29_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (3606714557195/44327294721408:ℝ) admission29_04_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission29_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_04_coefficients]
def admission29_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(4331924354903239591198/65581886233333125:ℝ),(78166376640093624305564/590236976099998125:ℝ),(39172120523201370684782/590236976099998125:ℝ)],
![(3632447203809470971522/65581886233333125:ℝ),(65656795471282837916372/590236976099998125:ℝ),(32957660291165424440174/590236976099998125:ℝ)]]
theorem admission29_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (1816223601904735485761/45845061292669009920000:ℝ) admission29_05_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission29_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_05_coefficients]
def admission29_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(740760783316264914248210156011243202560/32998524043161039460837289280333:ℝ),(723283693483593354578887476633839564800/10999508014387013153612429760111:ℝ),(2117939866546557896148533016407480074240/32998524043161039460837289280333:ℝ),(688848128389246043942096742517204582400/32998524043161039460837289280333:ℝ)],
![(773452282831499392540209795746162344192/32998524043161039460837289280333:ℝ),(755697296820223348678102296883668577024/10999508014387013153612429760111:ℝ),(2214355764068101272586066951147270881280/32998524043161039460837289280333:ℝ),(720714679390563998806036256242427494400/32998524043161039460837289280333:ℝ)]]
theorem admission29_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (82117095993667369358789532484675/703968512920768841831195504647104:ℝ) admission29_06_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission29_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_06_coefficients]
def admission29_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1034400423427308772565217026530720/2943405944443942508325509703:ℝ),(2036705039299991209892883671905280/2943405944443942508325509703:ℝ),(1002431737323284255528200481361920/2943405944443942508325509703:ℝ)],
![(970937663804645396185145221537540/2943405944443942508325509703:ℝ),(1910811171011777446479661324170368/2943405944443942508325509703:ℝ),(939996542611107381481461351034880/2943405944443942508325509703:ℝ)]]
theorem admission29_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (229491343410914888056997400155/1004682562370199042841773978624:ℝ) admission29_07_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission29_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_07_coefficients]
def admission29_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(5584338941343448544499707769281013810536956682169097/8601967603843697723983694444531250000000000000:ℝ),(156924312517325876044458740031735662868619438892429743/77417708434593279515853250000781250000000000000:ℝ),(1467632487655157950608977466193435649406108407186644853/696759375911339515642679250007031250000000000000:ℝ),(507639560224505722985220755363758211492083198410474023/696759375911339515642679250007031250000000000000:ℝ)],
![(209300154514805195969550648664098187444091700650508461/172039352076873954479673888890625000000000000000:ℝ),(5741820088182728838953176248830333300166777361727010797/1548354168691865590317065000015625000000000000000:ℝ),(13123733797804232569451211618438012461916735471843209833/3483796879556697578213396250035156250000000000000:ℝ),(7108701099315619502613489195610688887505410603808371/5574075007290716125141434000056250000000000000:ℝ)]]
theorem admission29_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (5584338941343448544499707769281013810536956682169097/1539382064156673567509150103188275200000000000000000000:ℝ) admission29_08_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission29_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_08_coefficients]
def admission29_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(3010936715094827814431678005907545110616036/1741898439778348789106698125017578125:ℝ),(582277656430821104541349866447458308389308/116126562651889919273779875001171875:ℝ),(8436690073341252971962829275944943224735232/1741898439778348789106698125017578125:ℝ),(2713473518634325938682967836499076522011648/1741898439778348789106698125017578125:ℝ)],
![(19275653086905511769124137422908934594635601/17418984397783487891066981250175781250:ℝ),(18404530660229373349227105558308281415689651/5806328132594495963688993750058593750:ℝ),(26304534530247115215423032631458193323356736/8709492198891743945533490625087890625:ℝ),(1667124882748237978647814866232472082240512/1741898439778348789106698125017578125:ℝ)]]
theorem admission29_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (1628051643308826151023256705305148517813/304418816398170309981057515523072000000000:ℝ) admission29_09_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission29_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_09_coefficients]
def admission29_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1123621156953875201575441850368/27667358254687412109375:ℝ),(1078655620523765097837698490368/9222452751562470703125:ℝ),(3101445871462908481699865391104/27667358254687412109375:ℝ),(329701330615162796587403923456/9222452751562470703125:ℝ)],
![(1793101433372221200829972376576/27667358254687412109375:ℝ),(1707480148893353529649738382336/9222452751562470703125:ℝ),(16060170084045441009650538496/91311413381806640625:ℝ),(1536900363407929237804870393856/27667358254687412109375:ℝ)],
![(131417921910193623470428032704/5533471650937482421875:ℝ),(205523236557337727377288979008/3074150917187490234375:ℝ),(1728426110254014178456146131584/27667358254687412109375:ℝ),(535810609429567749412685484032/27667358254687412109375:ℝ)]]
theorem admission29_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (130813137067765563821456417/103151387908505272320000000000:ℝ) admission29_10_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission29_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_10_coefficients]
def admission29_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(848259815855215715627925744927328/2943405944443942508325509703:ℝ),(1670275209671178693191817898766336/2943405944443942508325509703:ℝ),(822136869415248860851512996651008/2943405944443942508325509703:ℝ)],
![(794892475808437800569541147228028/2943405944443942508325509703:ℝ),(1564426040895802931865889160955392/2943405944443942508325509703:ℝ),(769650813493741629197557444124672/2943405944443942508325509703:ℝ)]]
theorem admission29_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (93951515319060257470404961441/502341281185099521420886989312:ℝ) admission29_11_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission29_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_11_coefficients]
def admission29_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission29_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission29_12_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission29_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_12_coefficients]
def admission29_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(8139931613966420001/2000000000000000000000:ℝ)]]
theorem admission29_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (8139931613966420001/2000000000000000000000:ℝ) admission29_13_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission29_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_13_coefficients]
def admission29_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission29_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission29_14_coefficients (15/32:ℝ) (123/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission29_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission29_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission29_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission29_14_coefficients]
theorem admission29_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission29_00_pos hδ hp
 · exact admission29_01_pos hδ hp
 · exact admission29_02_pos hδ hp
 · exact admission29_03_pos hδ hp
 · exact admission29_04_pos hδ hp
 · exact admission29_05_pos hδ hp
 · exact admission29_06_pos hδ hp
 · exact admission29_07_pos hδ hp
 · exact admission29_08_pos hδ hp
 · exact admission29_09_pos hδ hp
 · exact admission29_10_pos hδ hp
 · exact admission29_11_pos hδ hp
 · exact admission29_12_pos hδ hp
 · exact admission29_13_pos hδ hp
 · exact admission29_14_pos hδ hp
#print axioms admission29_all
end
end LewkoStage1Finite
