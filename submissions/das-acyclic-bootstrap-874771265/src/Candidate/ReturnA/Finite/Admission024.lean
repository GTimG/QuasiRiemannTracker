/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def admission024_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6215350407257051365376/3376969689:ℝ),(390338399179877606490112/70916363469:ℝ),(389109722702560976961536/70916363469:ℝ),(129293682075081449144320/70916363469:ℝ)],
![(12430700814514102730752/3376969689:ℝ),(780676798359755212980224/70916363469:ℝ),(778219445405121953923072/70916363469:ℝ),(258587364150162898288640/70916363469:ℝ)],
![(6215350407257051365376/3376969689:ℝ),(390338399179877606490112/70916363469:ℝ),(389109722702560976961536/70916363469:ℝ),(129293682075081449144320/70916363469:ℝ)]]
theorem admission024_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (29397979705/31518383764:ℝ) admission024_00_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission024_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission024_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission024_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission024_00_coefficients]
def admission024_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(13618006772173879902208/10130909067:ℝ),(285290947448291477946368/70916363469:ℝ),(284603752680931477946368/70916363469:ℝ),(31546284212619053105152/23638787823:ℝ)],
![(27236013544347759804416/10130909067:ℝ),(570581894896582955892736/70916363469:ℝ),(569207505361862955892736/70916363469:ℝ),(63092568425238106210304/23638787823:ℝ)],
![(13618006772173879902208/10130909067:ℝ),(285290947448291477946368/70916363469:ℝ),(284603752680931477946368/70916363469:ℝ),(31546284212619053105152/23638787823:ℝ)]]
theorem admission024_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (5379595941/7879595941:ℝ) admission024_01_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission024_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission024_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission024_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission024_01_coefficients]
def admission024_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4327923860701138600853504/6331818166875:ℝ),(18135937136304711037616128/8864545433625:ℝ),(90472970288323199758237696/44322727168125:ℝ),(30088751631707614776131584/44322727168125:ℝ)],
![(8655847721402277201707008/6331818166875:ℝ),(36271874272609422075232256/8864545433625:ℝ),(180945940576646399516475392/44322727168125:ℝ),(60177503263415229552263168/44322727168125:ℝ)],
![(4327923860701138600853504/6331818166875:ℝ),(18135937136304711037616128/8864545433625:ℝ),(90472970288323199758237696/44322727168125:ℝ),(30088751631707614776131584/44322727168125:ℝ)]]
theorem admission024_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218924481535997/630367675280000:ℝ) admission024_02_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission024_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission024_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission024_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission024_02_coefficients]
def admission024_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(71478625916508377710592/70916363469:ℝ),(640428367314062978056192/212749090407:ℝ),(637552781881310556717056/212749090407:ℝ),(211560292316772711792640/212749090407:ℝ)],
![(20353787842684669394944/10130909067:ℝ),(1276531335715357913513984/212749090407:ℝ),(1270781421938061655146496/212749090407:ℝ),(421679630919081798926336/212749090407:ℝ)],
![(70997888982284308054016/70916363469:ℝ),(636102968401294935457792/212749090407:ℝ),(90461234293821585489920/30392727201:ℝ),(210119338602309087133696/212749090407:ℝ)]]
theorem admission024_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (48922220850901/96824474923008:ℝ) admission024_03_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission024_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission024_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission024_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission024_03_coefficients]
def admission024_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(781198913146711197319168/4924747463125:ℝ),(93053161229867917737984/196989898525:ℝ),(2309102326998812902555648/4924747463125:ℝ),(763972209398826156425216/4924747463125:ℝ)],
![(8984587253638074392576/28141414075:ℝ),(4682262200332775222878208/4924747463125:ℝ),(13943095095746633018638336/14774242389375:ℝ),(4613216802908296406106112/14774242389375:ℝ)],
![(791103856239951821381632/4924747463125:ℝ),(336561881369439611346944/703535351875:ℝ),(7015788114750194310971392/14774242389375:ℝ),(2321300174711817936830464/14774242389375:ℝ)]]
theorem admission024_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (25614164339711649/322748249743360000:ℝ) admission024_04_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission024_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission024_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission024_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission024_04_coefficients]
def admission024_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(836109543616082040492032/8864545433625:ℝ),(12547150749766598507982848/44322727168125:ℝ),(1793211559557841562865664/6331818166875:ℝ),(39865503668749548900352/422121211125:ℝ)],
![(1639373169681506581774336/8864545433625:ℝ),(3514667595583256682053632/6331818166875:ℝ),(24614392798807388273106944/44322727168125:ℝ),(36482602125031664033792/196989898525:ℝ)],
![(803263626065424541282304/8864545433625:ℝ),(12055522419316198266392576/44322727168125:ℝ),(12061911881902497333047296/44322727168125:ℝ),(268180506194228118204416/2954848477875:ℝ)]]
theorem admission024_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (196109283707379038399/4230325859036168192000:ℝ) admission024_05_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission024_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission024_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission024_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission024_05_coefficients]
def admission024_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(996671723601406748835767799835426816/4307357233418767486494375:ℝ),(5316456101461578926406188734177902592/7753243020153781475689875:ℝ),(26256056627132762653074989869523009536/38766215100768907378449375:ℝ),(1728763876602593347254311279430467584/7753243020153781475689875:ℝ)],
![(668286246299220192969305898661584896/1435785744472922495498125:ℝ),(10694830076668930477752799891450093568/7753243020153781475689875:ℝ),(52820386105995754359877461566164041728/38766215100768907378449375:ℝ),(3477991971972563393174704274555273216/7753243020153781475689875:ℝ)],
![(1008187015296253830072149896149327872/4307357233418767486494375:ℝ),(5378373975207351551346611157272190976/7753243020153781475689875:ℝ),(3794904211266141672400353099520147456/5538030728681272482635625:ℝ),(1749228095369970045920392995124805632/7753243020153781475689875:ℝ)]]
theorem admission024_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (6440147297839050543510583339/56457392729866469198979072000:ℝ) admission024_06_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission024_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission024_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission024_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission024_06_coefficients]
def admission024_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(511364546385851669876734811888386048/1047735543264024523741875:ℝ),(61035445635647200890273382328926208/41909421730560980949675:ℝ),(72271187674027235975045572577984512/49892168726858310654375:ℝ),(20126933865969744123834291112116224/41909421730560980949675:ℝ)],
![(1014890968318345010400056122149576704/1047735543264024523741875:ℝ),(605664361526048252620505848419688448/209547108652804904748375:ℝ),(1004001060157771200216309931622531072/349245181088008174580625:ℝ),(199714468232283469589291334983745536/209547108652804904748375:ℝ)],
![(503526421932493340523321310261190656/1047735543264024523741875:ℝ),(300487133347812248169138936775057408/209547108652804904748375:ℝ),(498102746439580548390990923576639488/349245181088008174580625:ℝ),(99079798902434748970119879423164416/209547108652804904748375:ℝ)]]
theorem admission024_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (1476404054499190285356639019/6103501916742320994484224000:ℝ) admission024_07_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission024_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission024_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission024_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission024_07_coefficients]
def admission024_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(192399866170459583756953338561742044217192/47369409327258053192901611328125:ℝ),(3257560820199774017923583394217929956771624/255794810367193487241668701171875:ℝ),(629279104617015243847236179419829270630856/47369409327258053192901611328125:ℝ),(5897514511486178842680709654696420092039176/1278974051835967436208343505859375:ℝ)],
![(65277406713713270510896976708684887033124/6767058475322579027557373046875:ℝ),(38383056699872528316150713006036109641092292/1278974051835967436208343505859375:ℝ),(4416955863595304568133358840479396708056752/142108227981774159578704833984375:ℝ),(13706948656651832126983817703712088286928912/1278974051835967436208343505859375:ℝ)],
![(264541980825533309819325498399052165014676/47369409327258053192901611328125:ℝ),(22095252598873658226532796034946459857234172/1278974051835967436208343505859375:ℝ),(2529118549744258836591650302219908896164184/142108227981774159578704833984375:ℝ),(7809434145165653284303108049015668194889736/1278974051835967436208343505859375:ℝ)]]
theorem admission024_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (216449849441767031726572505881959799744341/104166432712402278305864089600000000000000000:ℝ) admission024_08_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission024_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission024_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission024_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission024_08_coefficients]
def admission024_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5541752039619210426176647280571582763136/292336926133935413990478515625:ℝ),(1813178268521687023358794412743880669696/32481880681548379332275390625:ℝ),(112088376136451414977110788250914684010496/2046358482937547897933349609375:ℝ),(162890789414633673769625595275820138496/9094926590833546213037109375:ℝ)],
![(74166651127385461887355569347053544324896/2046358482937547897933349609375:ℝ),(24251801419828624170615429757038843099776/227373164770838655325927734375:ℝ),(214041657491992363121774758477676695420928/2046358482937547897933349609375:ℝ),(1554269604440639932069730259216946429952/45474632954167731065185546875:ℝ)],
![(35374386850050988904119038383052464982944/2046358482937547897933349609375:ℝ),(3853184513392271669034622955943892803968/75791054923612885108642578125:ℝ),(101953281355540948144663970226762011410432/2046358482937547897933349609375:ℝ),(246605219122490521073867427612615245824/15158210984722577021728515625:ℝ)]]
theorem admission024_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (2116629573919691743531042908204591/254312579864263374770176000000000000:ℝ) admission024_09_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission024_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission024_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission024_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission024_09_coefficients]
def admission024_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(29441572494229297861867878272/5771188433349609375:ℝ),(431811011982445811461785928064/28855942166748046875:ℝ),(422014249462208080353303682048/28855942166748046875:ℝ),(45803720184417502733619048448/9618647388916015625:ℝ)],
![(840839375716466345138865057472/86567826500244140625:ℝ),(2464244652443594363573872121024/86567826500244140625:ℝ),(2406063785666975502056024069632/86567826500244140625:ℝ),(17392419441883763524911489024/1923729477783203125:ℝ)],
![(398910587551338409645013720008/86567826500244140625:ℝ),(1167901082710767361246698906632/86567826500244140625:ℝ),(227823111093362137157161955648/17313565300048828125:ℝ),(41125027161415895812124954624/9618647388916015625:ℝ)]]
theorem admission024_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (90362608508970474196563621/41311775967150080000000000000:ℝ) admission024_10_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission024_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission024_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission024_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission024_10_coefficients]
def admission024_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(139857590659984294310459582535532544/349245181088008174580625:ℝ),(50080010633123351763372824513511424/41909421730560980949675:ℝ),(177899690890586633361815177059631104/149676506180574931963125:ℝ),(27524689492398368158650958279081984/69849036217601634916125:ℝ)],
![(277518433531605800794514711812808704/349245181088008174580625:ℝ),(2484284587935794358853201695053570048/1047735543264024523741875:ℝ),(2470934383884833190084854826508746752/1047735543264024523741875:ℝ),(273068365514618744538399088964534272/349245181088008174580625:ℝ)],
![(27532168574324301296811025855455232/69849036217601634916125:ℝ),(1232284322107710564768881082215784448/1047735543264024523741875:ℝ),(1225636547650726756552148587091329024/1047735543264024523741875:ℝ),(135444918052626903745144297569124352/349245181088008174580625:ℝ)]]
theorem admission024_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (2018286556789679881112937593/10172503194570534990807040000:ℝ) admission024_11_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission024_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission024_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission024_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission024_11_coefficients]
def admission024_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(176669076292854874112/10986328125:ℝ),(176669076292854874112/3662109375:ℝ),(176669076292854874112/3662109375:ℝ),(176669076292854874112/10986328125:ℝ)],
![(353338152585709748224/10986328125:ℝ),(353338152585709748224/3662109375:ℝ),(353338152585709748224/3662109375:ℝ),(353338152585709748224/10986328125:ℝ)],
![(176669076292854874112/10986328125:ℝ),(176669076292854874112/3662109375:ℝ),(176669076292854874112/3662109375:ℝ),(176669076292854874112/10986328125:ℝ)]]
theorem admission024_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (41133974747/5000000000000:ℝ) admission024_12_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission024_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission024_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission024_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission024_12_coefficients]
def admission024_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6217204408677518278656/762939453125:ℝ),(18651613226032554835968/762939453125:ℝ),(18651613226032554835968/762939453125:ℝ),(6217204408677518278656/762939453125:ℝ)],
![(12434408817355036557312/762939453125:ℝ),(37303226452065109671936/762939453125:ℝ),(37303226452065109671936/762939453125:ℝ),(12434408817355036557312/762939453125:ℝ)],
![(6217204408677518278656/762939453125:ℝ),(18651613226032554835968/762939453125:ℝ),(18651613226032554835968/762939453125:ℝ),(6217204408677518278656/762939453125:ℝ)]]
theorem admission024_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (208448021404809/50000000000000000:ℝ) admission024_13_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission024_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission024_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission024_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission024_13_coefficients]
def admission024_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8796093022208/9:ℝ),(8796093022208/3:ℝ),(8796093022208/3:ℝ),(8796093022208/9:ℝ)],
![(17592186044416/9:ℝ),(17592186044416/3:ℝ),(17592186044416/3:ℝ),(17592186044416/9:ℝ)],
![(8796093022208/9:ℝ),(8796093022208/3:ℝ),(8796093022208/3:ℝ),(8796093022208/9:ℝ)]]
theorem admission024_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission024_14_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission024_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission024_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission024_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission024_14_coefficients]
theorem admission024_all {δ p : ℝ}
 (hd : δ∈Set.Icc (117/256:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission024_00_pos hd hp
 · exact admission024_01_pos hd hp
 · exact admission024_02_pos hd hp
 · exact admission024_03_pos hd hp
 · exact admission024_04_pos hd hp
 · exact admission024_05_pos hd hp
 · exact admission024_06_pos hd hp
 · exact admission024_07_pos hd hp
 · exact admission024_08_pos hd hp
 · exact admission024_09_pos hd hp
 · exact admission024_10_pos hd hp
 · exact admission024_11_pos hd hp
 · exact admission024_12_pos hd hp
 · exact admission024_13_pos hd hp
 · exact admission024_14_pos hd hp
end
end DasStageAFinite
#print axioms DasStageAFinite.admission024_all
