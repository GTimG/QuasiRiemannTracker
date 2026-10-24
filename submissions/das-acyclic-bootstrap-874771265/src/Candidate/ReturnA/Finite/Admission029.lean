/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def admission029_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(605961147583908262872875008/10130909067:ℝ),(12720151440410984605781327872/70916363469:ℝ),(12715118781559895691232280576/70916363469:ℝ),(4236695374236268925561077760/70916363469:ℝ)],
![(1211922295167816525745750016/10130909067:ℝ),(25440302880821969211562655744/70916363469:ℝ),(25430237563119791382464561152/70916363469:ℝ),(8473390748472537851122155520/70916363469:ℝ)],
![(605961147583908262872875008/10130909067:ℝ),(12720151440410984605781327872/70916363469:ℝ),(12715118781559895691232280576/70916363469:ℝ),(4236695374236268925561077760/70916363469:ℝ)]]
theorem admission029_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (29397979705/31518383764:ℝ) admission029_00_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission029_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission029_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission029_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission029_00_coefficients]
def admission029_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(443420096143487136635551744/10130909067:ℝ),(9309007269246123309346586624/70916363469:ℝ),(9306192519479016749346586624/70916363469:ℝ),(1033708641079101132149620736/23638787823:ℝ)],
![(886840192286974273271103488/10130909067:ℝ),(18618014538492246618693173248/70916363469:ℝ),(18612385038958033498693173248/70916363469:ℝ),(2067417282158202264299241472/23638787823:ℝ)],
![(443420096143487136635551744/10130909067:ℝ),(9309007269246123309346586624/70916363469:ℝ),(9306192519479016749346586624/70916363469:ℝ),(1033708641079101132149620736/23638787823:ℝ)]]
theorem admission029_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (5379595941/7879595941:ℝ) admission029_01_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission029_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission029_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission029_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission029_01_coefficients]
def admission029_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(46990234272302084610710306816/2110606055625:ℝ),(2959538052904482674634112630784/44322727168125:ℝ),(591738269330786803758695186432/8864545433625:ℝ),(985948213467795120984279744512/44322727168125:ℝ)],
![(93980468544604169221420613632/2110606055625:ℝ),(5919076105808965349268225261568/44322727168125:ℝ),(1183476538661573607517390372864/8864545433625:ℝ),(1971896426935590241968559489024/44322727168125:ℝ)],
![(46990234272302084610710306816/2110606055625:ℝ),(2959538052904482674634112630784/44322727168125:ℝ),(591738269330786803758695186432/8864545433625:ℝ),(985948213467795120984279744512/44322727168125:ℝ)]]
theorem admission029_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218924481535997/630367675280000:ℝ) admission029_02_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission029_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission029_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission029_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission029_02_coefficients]
def admission029_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(987808595854516091329970176/30392727201:ℝ),(2961745054225752717946519552/30392727201:ℝ),(20720452135162449573321900032/212749090407:ℝ),(6902896926563793187006054400/212749090407:ℝ)],
![(13823417541349973396849426432/212749090407:ℝ),(41446723010009641841107927040/212749090407:ℝ),(41423197175372811811667574784/212749090407:ℝ),(1971413100959020481058439168/30392727201:ℝ)],
![(6908757370368360757539635200/212749090407:ℝ),(20714507630429372815482290176/212749090407:ℝ),(20702745040210362238345674752/212749090407:ℝ),(6896994780149350180403019776/212749090407:ℝ)]]
theorem admission029_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (98012190792209/193648949846016:ℝ) admission029_03_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission029_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission029_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission029_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission029_03_coefficients]
def admission029_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(25164601741172621212890169344/4924747463125:ℝ),(75423201298189645944920211456/4924747463125:ℝ),(75352618417861175455323783168/4924747463125:ℝ),(25094018860844150723293741056/4924747463125:ℝ)],
![(151108134717064544476228747264/14774242389375:ℝ),(452900611285254715233345732608/14774242389375:ℝ),(452476944739781905555983958016/14774242389375:ℝ),(150684468171591734798866972672/14774242389375:ℝ)],
![(75614329493546680837558239232/14774242389375:ℝ),(45326201478137155479717019648/2954848477875:ℝ),(32345584212314054170001801216/2110606055625:ℝ),(10771773084151326089855107072/2110606055625:ℝ)]]
theorem admission029_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (821623579204596741/10327943991787520000:ℝ) admission029_04_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission029_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission029_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission029_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission029_04_coefficients]
def admission029_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2971228753801318689632944128/984949492625:ℝ),(57305542119334159198376689664/6331818166875:ℝ),(401161616845792623559441383424/44322727168125:ℝ),(133728115931512850204287041536/44322727168125:ℝ)],
![(88913900158368268125214343168/14774242389375:ℝ),(800271469492159176145212276736/44322727168125:ℝ),(800317655362797641769559261184/44322727168125:ℝ),(266787886345743269999990013952/44322727168125:ℝ)],
![(44345468851348487780720181248/14774242389375:ℝ),(399132674656820061756575449088/44322727168125:ℝ),(79831207703401003642023575552/8864545433625:ℝ),(133059770414230419795702972416/44322727168125:ℝ)]]
theorem admission029_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (126873404077573264448319/2707408549783147642880000:ℝ) admission029_05_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission029_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission029_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission029_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission029_05_coefficients]
def admission029_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(285201734893176034632910064387118676312064/38766215100768907378449375:ℝ),(854271970301214773770637428697368476778496/38766215100768907378449375:ℝ),(852939569895437851852454333838267674263552/38766215100768907378449375:ℝ),(56773866868620541239433678065603574759424/7753243020153781475689875:ℝ)],
![(570823247931369572685412280579194937147392/38766215100768907378449375:ℝ),(244257514806856554274092585741926647988224/5538030728681272482635625:ℝ),(1707137131891895752300705691407747389587456/38766215100768907378449375:ℝ),(16233079311044608205229089548384451166208/1107606145736254496527125:ℝ)],
![(285621513038193538052502216192076260835328/38766215100768907378449375:ℝ),(855530633346781106148010671496118059139072/38766215100768907378449375:ℝ),(854197561996457900448251357569479715323904/38766215100768907378449375:ℝ),(56857688308691716197169948773087583404032/7753243020153781475689875:ℝ)]]
theorem admission029_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (206542124464687881261611175671/1806636567355727014367330304000:ℝ) admission029_06_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission029_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission029_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission029_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission029_06_coefficients]
def admission029_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(16362160447690268032458054762728286322688/1047735543264024523741875:ℝ),(49053078066131719296178784770074145718272/1047735543264024523741875:ℝ),(5446631456630741661455877765546666622976/116415060362669391526875:ℝ),(653150619649408947575286795302965608448/41909421730560980949675:ℝ)],
![(32692444554448625373858500932538876821504/1047735543264024523741875:ℝ),(98010559712167245805944396555632596484096/1047735543264024523741875:ℝ),(10882644710426181074608628789883078443008/116415060362669391526875:ℝ),(6525137447223401847878352697170797264896/209547108652804904748375:ℝ)],
![(333271104219558313089805023873685520384/21382358025796418851875:ℝ),(999132278490520949178890036439968382976/21382358025796418851875:ℝ),(110939045995825294145974510700743098368/2375817558421824316875:ℝ),(66518047938293002244937116748081004544/4276471605159283770375:ℝ)]]
theorem admission029_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (60497812172155138109644319/249122527213972285489152000:ℝ) admission029_07_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission029_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission029_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission029_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission029_07_coefficients]
def admission029_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(64024282094589490704334519215945254773436282944/426324683945322478736114501953125:ℝ),(579039699331913680079995360269499747813724785856/1278974051835967436208343505859375:ℝ),(193953506534670263092708292219564163981888689984/426324683945322478736114501953125:ℝ),(194893665683451748437405836732412859176000132928/1278974051835967436208343505859375:ℝ)],
![(130665080018410387329643958882345583790117070336/426324683945322478736114501953125:ℝ),(1181609707167590712626659527277418653247330018944/1278974051835967436208343505859375:ℝ),(395744341014779737913547970833811719949834989184/426324683945322478736114501953125:ℝ),(397618554186454624187697017287957358581276159616/1278974051835967436208343505859375:ℝ)],
![(66640797923820896625309439666400329016680787392/426324683945322478736114501953125:ℝ),(602570007835677032546664167007918905433605233088/1278974051835967436208343505859375:ℝ),(8071633379204378992833587144569902238717851968/17052987357812899149444580078125:ℝ),(4137242622510262770414105725623357130719918912/26101511261958519106292724609375:ℝ)]]
theorem admission029_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (1000379407727960792255226862749144605834941921/426665708389999731940819311001600000000000000000:ℝ) admission029_08_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission029_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission029_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission029_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission029_08_coefficients]
def admission029_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(380279993829199226929854201963680625698958592/682119494312515965977783203125:ℝ),(3413852135708256029349224496882990625882759168/2046358482937547897933349609375:ℝ),(3405186717461543548777931527230613600853819392/2046358482937547897933349609375:ℝ),(335459130193612140415789484350206266834944/606328439388903080869140625:ℝ)],
![(755964149613901784031526749919573636897392896/682119494312515965977783203125:ℝ),(6786371928223474884152439896594402479268716544/2046358482937547897933349609375:ℝ),(6769071276304056596103312092069860235905335296/2046358482937547897933349609375:ℝ),(7144735870629612420931739058826565675646976/6496376136309675866455078125:ℝ)],
![(375684155784702557101672547955893011198434304/682119494312515965977783203125:ℝ),(3372519792515218854803215399711411853385957376/2046358482937547897933349609375:ℝ),(3363884558842513047325380564839246635051515904/2046358482937547897933349609375:ℝ),(24853716329886376415337962085520489716908032/45474632954167731065185546875:ℝ)]]
theorem admission029_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (4340030077708601558465387570704419/508625159728526749540352000000000000:ℝ) admission029_09_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission029_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission029_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission029_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission029_09_coefficients]
def admission029_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1418450597820665736127287833569344/9618647388916015625:ℝ),(4242094712676699459887988356467264/9618647388916015625:ℝ),(4228840309359970589859072837226496/9618647388916015625:ℝ),(1405196195803009961801497314328576/9618647388916015625:ℝ)],
![(25359634802021227504178007224964608/86567826500244140625:ℝ),(10834369295578983122787867645004288/12366832357177734375:ℝ),(75602313780826698230565404355166208/86567826500244140625:ℝ),(15950072087109238918795770200064/54963699365234375:ℝ)],
![(503737016922409363468306249081856/3462713060009765625:ℝ),(37661270981772998184025928349279232/86567826500244140625:ℝ),(37542289645800967095842962017419264/86567826500244140625:ℝ),(1386049344310951114419409988354048/9618647388916015625:ℝ)]]
theorem admission029_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (371767404639678002291163501/165247103868600320000000000000:ℝ) admission029_10_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission029_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission029_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission029_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission029_10_coefficients]
def admission029_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(13422399926166722465484407170623974408192/1047735543264024523741875:ℝ),(13413292804072757758117063585084602843136/349245181088008174580625:ℝ),(40212565018443814993970993857277225598976/1047735543264024523741875:ℝ),(893005768826150945673614018176492765184/69849036217601634916125:ℝ)],
![(26818002158315606328062891835765109030912/1047735543264024523741875:ℝ),(26799797225139272829401914382103516545024/349245181088008174580625:ℝ),(80344792812504464183904090107702826500096/1047735543264024523741875:ℝ),(8921134431800750674587079599052461965312/349245181088008174580625:ℝ)],
![(54675927478158709643177488429147488256/4276471605159283770375:ℝ),(1912357774438073581612121542431273385984/49892168726858310654375:ℝ),(1146635079830304262569517035726445740032/29935301236114986392625:ℝ),(636586512524285135174144215452856877056/49892168726858310654375:ℝ)]]
theorem admission029_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (578972060360943155659828531/2906429484163009997373440000:ℝ) admission029_11_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission029_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission029_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission029_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission029_11_coefficients]
def admission029_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5789092291964268514902016/10986328125:ℝ),(5789092291964268514902016/3662109375:ℝ),(5789092291964268514902016/3662109375:ℝ),(5789092291964268514902016/10986328125:ℝ)],
![(11578184583928537029804032/10986328125:ℝ),(11578184583928537029804032/3662109375:ℝ),(11578184583928537029804032/3662109375:ℝ),(11578184583928537029804032/10986328125:ℝ)],
![(5789092291964268514902016/10986328125:ℝ),(5789092291964268514902016/3662109375:ℝ),(5789092291964268514902016/3662109375:ℝ),(5789092291964268514902016/10986328125:ℝ)]]
theorem admission029_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (41133974747/5000000000000:ℝ) admission029_12_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission029_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission029_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission029_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission029_12_coefficients]
def admission029_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(203725354063544918954999808/762939453125:ℝ),(611176062190634756864999424/762939453125:ℝ),(611176062190634756864999424/762939453125:ℝ),(203725354063544918954999808/762939453125:ℝ)],
![(407450708127089837909999616/762939453125:ℝ),(1222352124381269513729998848/762939453125:ℝ),(1222352124381269513729998848/762939453125:ℝ),(407450708127089837909999616/762939453125:ℝ)],
![(203725354063544918954999808/762939453125:ℝ),(611176062190634756864999424/762939453125:ℝ),(611176062190634756864999424/762939453125:ℝ),(203725354063544918954999808/762939453125:ℝ)]]
theorem admission029_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (208448021404809/50000000000000000:ℝ) admission029_13_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission029_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission029_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission029_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission029_13_coefficients]
def admission029_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(288230376151711744/9:ℝ),(288230376151711744/3:ℝ),(288230376151711744/3:ℝ),(288230376151711744/9:ℝ)],
![(576460752303423488/9:ℝ),(576460752303423488/3:ℝ),(576460752303423488/3:ℝ),(576460752303423488/9:ℝ)],
![(288230376151711744/9:ℝ),(288230376151711744/3:ℝ),(288230376151711744/3:ℝ),(288230376151711744/9:ℝ)]]
theorem admission029_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission029_14_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission029_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission029_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission029_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission029_14_coefficients]
theorem admission029_all {δ p : ℝ}
 (hd : δ∈Set.Icc (3753/8192:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission029_00_pos hd hp
 · exact admission029_01_pos hd hp
 · exact admission029_02_pos hd hp
 · exact admission029_03_pos hd hp
 · exact admission029_04_pos hd hp
 · exact admission029_05_pos hd hp
 · exact admission029_06_pos hd hp
 · exact admission029_07_pos hd hp
 · exact admission029_08_pos hd hp
 · exact admission029_09_pos hd hp
 · exact admission029_10_pos hd hp
 · exact admission029_11_pos hd hp
 · exact admission029_12_pos hd hp
 · exact admission029_13_pos hd hp
 · exact admission029_14_pos hd hp
end
end DasStageAFinite
#print axioms DasStageAFinite.admission029_all
