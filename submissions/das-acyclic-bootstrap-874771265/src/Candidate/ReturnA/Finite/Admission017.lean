/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def admission017_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(24861401629028205461504/3376969689:ℝ),(1561353596719510425960448/70916363469:ℝ),(1556438890810243907846144/70916363469:ℝ),(517174728300325796577280/70916363469:ℝ)],
![(49722803258056410923008/3376969689:ℝ),(3122707193439020851920896/70916363469:ℝ),(3112877781620487815692288/70916363469:ℝ),(1034349456600651593154560/70916363469:ℝ)],
![(24861401629028205461504/3376969689:ℝ),(1561353596719510425960448/70916363469:ℝ),(1556438890810243907846144/70916363469:ℝ),(517174728300325796577280/70916363469:ℝ)]]
theorem admission017_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (29397979705/31518383764:ℝ) admission017_00_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission017_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission017_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission017_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission017_00_coefficients]
def admission017_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(54472027088695519608832/10130909067:ℝ),(1141163789793165911785472/70916363469:ℝ),(1138415010723725911785472/70916363469:ℝ),(126185136850476212420608/23638787823:ℝ)],
![(108944054177391039217664/10130909067:ℝ),(2282327579586331823570944/70916363469:ℝ),(2276830021447451823570944/70916363469:ℝ),(252370273700952424841216/23638787823:ℝ)],
![(54472027088695519608832/10130909067:ℝ),(1141163789793165911785472/70916363469:ℝ),(1138415010723725911785472/70916363469:ℝ),(126185136850476212420608/23638787823:ℝ)]]
theorem admission017_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (5379595941/7879595941:ℝ) admission017_01_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission017_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission017_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission017_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission017_01_coefficients]
def admission017_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(17311695442804554403414016/6331818166875:ℝ),(72543748545218844150464512/8864545433625:ℝ),(361891881153292799032950784/44322727168125:ℝ),(120355006526830459104526336/44322727168125:ℝ)],
![(34623390885609108806828032/6331818166875:ℝ),(145087497090437688300929024/8864545433625:ℝ),(723783762306585598065901568/44322727168125:ℝ),(240710013053660918209052672/44322727168125:ℝ)],
![(17311695442804554403414016/6331818166875:ℝ),(72543748545218844150464512/8864545433625:ℝ),(361891881153292799032950784/44322727168125:ℝ),(120355006526830459104526336/44322727168125:ℝ)]]
theorem admission017_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218924481535997/630367675280000:ℝ) admission017_02_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission017_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission017_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission017_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission017_02_coefficients]
def admission017_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(283028405943077647155200/70916363469:ℝ),(362250132100304997449728/30392727201:ℝ),(360608736264744448557056/30392727201:ℝ),(837595446980309099216896/212749090407:ℝ)],
![(80727905431101022142464/10130909067:ℝ),(5062851051578733879099392/212749090407:ℝ),(5039874024057303363223552/212749090407:ℝ),(1672308986531690949115904/212749090407:ℝ)],
![(282066932074629507842048/70916363469:ℝ),(2527100126876598896951296/212749090407:ℝ),(2515612870204092223324160/212749090407:ℝ),(119244791364483121414144/30392727201:ℝ)]]
theorem admission017_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (6940960381441/13832067846144:ℝ) admission017_03_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission017_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission017_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission017_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission017_03_coefficients]
def admission017_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(9524617517981055751929856/14774242389375:ℝ),(378177591152155511832576/196989898525:ℝ),(28153286063793218850390016/14774242389375:ℝ),(9314584245362611214876672/14774242389375:ℝ)],
![(2729809242074507892604928/2110606055625:ℝ),(18968087835286534263586816/4924747463125:ℝ),(56483534395093948907388928/14774242389375:ℝ),(6229311861251967121620992/4924747463125:ℝ)],
![(1916809435308099899260928/2954848477875:ℝ),(1359092579497520923967488/703535351875:ℝ),(9443416110433576685666304/4924747463125:ℝ),(9373351338393290149986304/14774242389375:ℝ)]]
theorem admission017_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (208197181940733147/2581985997946880000:ℝ) admission017_04_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission017_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission017_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission017_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission017_04_coefficients]
def admission017_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(629472533832076633341952/1772909086725:ℝ),(47243074747601841568612352/44322727168125:ℝ),(6753569767233582520385536/6331818166875:ℝ),(30035670416828860776448/84424242225:ℝ)],
![(6229033503219451335000064/8864545433625:ℝ),(2671511223837225218686976/1266363633375:ℝ),(3742753546850614722854912/1772909086725:ℝ),(693580296734660935385088/984949492625:ℝ)],
![(3081670834059068168290304/8864545433625:ℝ),(46259818086701041085431808/44322727168125:ℝ),(46293850300630290428674048/44322727168125:ℝ),(1029492425614972678979584/2954848477875:ℝ)]]
theorem admission017_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (188090260867863047381/4230325859036168192000:ℝ) admission017_05_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission017_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission017_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission017_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission017_05_coefficients]
def admission017_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4044994759222495866967776285552001024/4307357233418767486494375:ℝ),(21578039861793391475037753432239423488/7753243020153781475689875:ℝ),(106572138618280088749618649072196911104/38766215100768907378449375:ℝ),(7017376600247256882347653696193560576/7753243020153781475689875:ℝ)],
![(231800574338133882754523336106622976/123067349526250499614125:ℝ),(43279915471078328199956351710667423744/7753243020153781475689875:ℝ),(42752164588004127121338452359725973504/7753243020153781475689875:ℝ),(14075681638029267162027470823775797248/7753243020153781475689875:ℝ)],
![(1356008447537396676480180159393267712/1435785744472922495498125:ℝ),(21701875609284936724918598278428000256/7753243020153781475689875:ℝ),(107188684321740546857073612726432956416/38766215100768907378449375:ℝ),(7058305037782010279679817127582236672/7753243020153781475689875:ℝ)]]
theorem admission017_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (52283529939109510796872181417/451659141838931753591832576000:ℝ) admission017_06_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission017_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission017_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission017_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission017_06_coefficients]
def admission017_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1998174349558102818953835754029924352/1047735543264024523741875:ℝ),(1192466409537674114771806811531788288/209547108652804904748375:ℝ),(1976734990634941005939026710239379456/349245181088008174580625:ℝ),(393209454754911052582376365417824256/209547108652804904748375:ℝ)],
![(796134490041897795840168900961091584/209547108652804904748375:ℝ),(2375552629414500716979157673324429312/209547108652804904748375:ℝ),(787575769342532361001879450308050944/69849036217601634916125:ℝ),(783309168654994161866649578560815104/209547108652804904748375:ℝ)],
![(1982498100651386160247008750775533568/1047735543264024523741875:ℝ),(1183086219876826602207350861792641024/209547108652804904748375:ℝ),(1961143856077720799070370541300875264/349245181088008174580625:ℝ),(390099713900083109284273213142990848/209547108652804904748375:ℝ)]]
theorem admission017_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (1453234679624747892038051833/6103501916742320994484224000:ℝ) admission017_07_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission017_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission017_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission017_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission017_07_coefficients]
def admission017_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1130310037957206965339674153433518780856188/47369409327258053192901611328125:ℝ),(18801628989487700534471946757763220189242396/255794810367193487241668701171875:ℝ),(10717766454857996303859504599963206654399652/142108227981774159578704833984375:ℝ),(32970068904304506768526580983941295089001964/1278974051835967436208343505859375:ℝ)],
![(2404904305224561382804092626541657803307344/47369409327258053192901611328125:ℝ),(199631186890626581618549225705345822039176064/1278974051835967436208343505859375:ℝ),(22718095381502418817818892727847255477342536/142108227981774159578704833984375:ℝ),(69763977075967962420297958756521086383705048/1278974051835967436208343505859375:ℝ)],
![(1274594267267354417464418473108139022451156/47369409327258053192901611328125:ℝ),(105623041943188078946189491916529721092964084/1278974051835967436208343505859375:ℝ),(4000109642214807504653129375961349607647628/47369409327258053192901611328125:ℝ),(36793908171663455651771377772579791294703084/1278974051835967436208343505859375:ℝ)]]
theorem admission017_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (2543197585403715672014266845225417256926423/833331461699218226446912716800000000000000000:ℝ) admission017_08_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission017_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission017_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission017_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission017_08_coefficients]
def admission017_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(134425174983528476154545822883944065679168/2046358482937547897933349609375:ℝ),(14640115168733034475853621651849697764096/75791054923612885108642578125:ℝ),(387307233177777266622298847274409685745664/2046358482937547897933349609375:ℝ),(2809986050058492641633357744268873039872/45474632954167731065185546875:ℝ)],
![(7486131288928285261453047445885454361152/58467385226787082798095703125:ℝ),(17115060466689643708461269173669442806528/45474632954167731065185546875:ℝ),(30173771071749343983188162340020561051648/81854339317501915917333984375:ℝ),(1823565173568530557337888033818412056576/15158210984722577021728515625:ℝ)],
![(127589420128961507996310837722046836961152/2046358482937547897933349609375:ℝ),(41654956827249115114745480912798120740352/227373164770838655325927734375:ℝ),(367037043615956332957405211226104340545536/2046358482937547897933349609375:ℝ),(54300193278512225109802170554823737344/928053733758525123779296875:ℝ)]]
theorem admission017_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (38838524779209297973968151012533/5190052650291089281024000000000000:ℝ) admission017_09_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission017_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission017_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission017_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission017_09_coefficients]
def admission017_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1506821073852703385080169823688/86567826500244140625:ℝ),(4408858806927154816084528264712/86567826500244140625:ℝ),(859484207886220422480200036672/17313565300048828125:ℝ),(155042673008904112169071304704/9618647388916015625:ℝ)],
![(585154908393539382613533086432/17313565300048828125:ℝ),(8555369437097252942357215332704/86567826500244140625:ℝ),(8333743838514252512571371868928/86567826500244140625:ℝ),(300461161063121657864646885376/9618647388916015625:ℝ)],
![(472882755787768353473887481696/28855942166748046875:ℝ),(197409528399267074206231982752/4122277452392578125:ℝ),(269027821151307321664004562688/5771188433349609375:ℝ),(145385138190632126616762138624/9618647388916015625:ℝ)]]
theorem admission017_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (79862441633037667208914749/41311775967150080000000000000:ℝ) admission017_10_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission017_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission017_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission017_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission017_10_coefficients]
def admission017_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(546177002393769047170235772864708608/349245181088008174580625:ℝ),(4889268684845740616914864922877411328/1047735543264024523741875:ℝ),(972601103567953339611445242431012864/209547108652804904748375:ℝ),(537422613391777740884356202623926272/349245181088008174580625:ℝ)],
![(1087960509210812518687662639212904448/349245181088008174580625:ℝ),(9739105482250734775198850784510820352/1047735543264024523741875:ℝ),(9686688458512774042153337119657951232/1047735543264024523741875:ℝ),(1070488167964825607672491417595281408/349245181088008174580625:ℝ)],
![(108356701363408694303485373269639168/69849036217601634916125:ℝ),(4849836797404994158283985861633409024/1047735543264024523741875:ℝ),(4823682940673007344096110907502886912/1047735543264024523741875:ℝ),(533065554573047866788135214971355136/349245181088008174580625:ℝ)]]
theorem admission017_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (1985823938895195226327088531/10172503194570534990807040000:ℝ) admission017_11_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission017_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission017_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission017_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission017_11_coefficients]
def admission017_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(706676305171419496448/10986328125:ℝ),(706676305171419496448/3662109375:ℝ),(706676305171419496448/3662109375:ℝ),(706676305171419496448/10986328125:ℝ)],
![(1413352610342838992896/10986328125:ℝ),(1413352610342838992896/3662109375:ℝ),(1413352610342838992896/3662109375:ℝ),(1413352610342838992896/10986328125:ℝ)],
![(706676305171419496448/10986328125:ℝ),(706676305171419496448/3662109375:ℝ),(706676305171419496448/3662109375:ℝ),(706676305171419496448/10986328125:ℝ)]]
theorem admission017_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (41133974747/5000000000000:ℝ) admission017_12_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission017_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission017_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission017_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission017_12_coefficients]
def admission017_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(24868817634710073114624/762939453125:ℝ),(74606452904130219343872/762939453125:ℝ),(74606452904130219343872/762939453125:ℝ),(24868817634710073114624/762939453125:ℝ)],
![(49737635269420146229248/762939453125:ℝ),(149212905808260438687744/762939453125:ℝ),(149212905808260438687744/762939453125:ℝ),(49737635269420146229248/762939453125:ℝ)],
![(24868817634710073114624/762939453125:ℝ),(74606452904130219343872/762939453125:ℝ),(74606452904130219343872/762939453125:ℝ),(24868817634710073114624/762939453125:ℝ)]]
theorem admission017_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (208448021404809/50000000000000000:ℝ) admission017_13_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission017_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission017_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission017_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission017_13_coefficients]
def admission017_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(35184372088832/9:ℝ),(35184372088832/3:ℝ),(35184372088832/3:ℝ),(35184372088832/9:ℝ)],
![(70368744177664/9:ℝ),(70368744177664/3:ℝ),(70368744177664/3:ℝ),(70368744177664/9:ℝ)],
![(35184372088832/9:ℝ),(35184372088832/3:ℝ),(35184372088832/3:ℝ),(35184372088832/9:ℝ)]]
theorem admission017_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission017_14_coefficients (951/2048:ℝ) (477/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission017_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission017_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission017_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission017_14_coefficients]
theorem admission017_all {δ p : ℝ}
 (hd : δ∈Set.Icc (951/2048:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission017_00_pos hd hp
 · exact admission017_01_pos hd hp
 · exact admission017_02_pos hd hp
 · exact admission017_03_pos hd hp
 · exact admission017_04_pos hd hp
 · exact admission017_05_pos hd hp
 · exact admission017_06_pos hd hp
 · exact admission017_07_pos hd hp
 · exact admission017_08_pos hd hp
 · exact admission017_09_pos hd hp
 · exact admission017_10_pos hd hp
 · exact admission017_11_pos hd hp
 · exact admission017_12_pos hd hp
 · exact admission017_13_pos hd hp
 · exact admission017_14_pos hd hp
end
end DasStageAFinite
#print axioms DasStageAFinite.admission017_all
