/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def admission018_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(16468879378714338525184/70916363469:ℝ),(49099469016813858193408/70916363469:ℝ),(48792299897484700811264/70916363469:ℝ),(16161710259385181143040/70916363469:ℝ)],
![(32937758757428677050368/70916363469:ℝ),(98198938033627716386816/70916363469:ℝ),(97584599794969401622528/70916363469:ℝ),(32323420518770362286080/70916363469:ℝ)],
![(16468879378714338525184/70916363469:ℝ),(49099469016813858193408/70916363469:ℝ),(48792299897484700811264/70916363469:ℝ),(16161710259385181143040/70916363469:ℝ)]]
theorem admission018_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (29397979705/31518383764:ℝ) admission018_00_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission018_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission018_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission018_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission018_00_coefficients]
def admission018_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(12001655271572144914432/70916363469:ℝ),(35833167122876434743296/70916363469:ℝ),(35661368431036434743296/70916363469:ℝ),(3943285526577381638144/23638787823:ℝ)],
![(24003310543144289828864/70916363469:ℝ),(71666334245752869486592/70916363469:ℝ),(71322736862072869486592/70916363469:ℝ),(7886571053154763276288/23638787823:ℝ)],
![(12001655271572144914432/70916363469:ℝ),(35833167122876434743296/70916363469:ℝ),(35661368431036434743296/70916363469:ℝ),(3943285526577381638144/23638787823:ℝ)]]
theorem admission018_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (5379595941/7879595941:ℝ) admission018_01_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission018_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission018_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission018_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission018_01_coefficients]
def admission018_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1270924267421180234825728/14774242389375:ℝ),(11386639558490533255970816/44322727168125:ℝ),(2266992142038088879702016/8864545433625:ℝ),(3761093953963451847016448/44322727168125:ℝ)],
![(2541848534842360469651456/14774242389375:ℝ),(22773279116981066511941632/44322727168125:ℝ),(4533984284076177759404032/8864545433625:ℝ),(7522187907926903694032896/44322727168125:ℝ)],
![(1270924267421180234825728/14774242389375:ℝ),(11386639558490533255970816/44322727168125:ℝ),(2266992142038088879702016/8864545433625:ℝ),(3761093953963451847016448/44322727168125:ℝ)]]
theorem admission018_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218924481535997/630367675280000:ℝ) admission018_02_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission018_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission018_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission018_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission018_02_coefficients]
def admission018_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(26893749080326326452224/212749090407:ℝ),(79960480238467312254976/212749090407:ℝ),(79241588876275645153280/212749090407:ℝ),(26174857718134659350528/212749090407:ℝ)],
![(53607070572532553744384/212749090407:ℝ),(159379974289906473107456/212749090407:ℝ),(157942499939335284981760/212749090407:ℝ),(7452799460280195088384/30392727201:ℝ)],
![(26713321492206227292160/212749090407:ℝ),(79419494051439160852480/212749090407:ℝ),(78700911063059639828480/212749090407:ℝ),(25994738503826706268160/212749090407:ℝ)]]
theorem admission018_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (1513092924365/3025764841344:ℝ) admission018_03_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission018_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission018_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission018_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission018_03_coefficients]
def admission018_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(101732942835677800558592/4924747463125:ℝ),(300777986752319681589248/4924747463125:ℝ),(296378041748703867305984/4924747463125:ℝ),(97332997832061986275328/4924747463125:ℝ)],
![(614153618158741138952192/14774242389375:ℝ),(259407484548480227454976/2110606055625:ℝ),(357873940797481960865792/2954848477875:ℝ),(117534186061357870219264/2954848477875:ℝ)],
![(308954789651707737276416/14774242389375:ℝ),(913518431582402547417088/14774242389375:ℝ),(128605082677328314630144/2110606055625:ℝ),(42238848115800484610048/2110606055625:ℝ)]]
theorem admission018_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (104426977692670569/1290992998973440000:ℝ) admission018_04_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission018_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission018_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission018_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission018_04_coefficients]
def admission018_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7798212806197102014464/703535351875:ℝ),(59044994563816483721216/1772909086725:ℝ),(1478297087583850753097728/44322727168125:ℝ),(98691926055771217395712/8864545433625:ℝ)],
![(45805400897157580214272/2110606055625:ℝ),(578106244170468109144064/8864545433625:ℝ),(2895140776031583427493888/44322727168125:ℝ),(193304594803910413254656/8864545433625:ℝ)],
![(4482152495713254834176/422121211125:ℝ),(282881271351385690537984/8864545433625:ℝ),(283368737689546534879232/8864545433625:ℝ),(94612668748139195858944/8864545433625:ℝ)]]
theorem admission018_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (205176658434139473/4721345824817152000:ℝ) admission018_05_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission018_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission018_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission018_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission018_05_coefficients]
def admission018_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1182619838847284576367646253027151872/38766215100768907378449375:ℝ),(3464074599498626587040110807535833088/38766215100768907378449375:ℝ),(3381119681101259032467460712616165376/38766215100768907378449375:ℝ),(219932525594207299406679231621496832/7753243020153781475689875:ℝ)],
![(2378360694786708148277244699614236672/38766215100768907378449375:ℝ),(6967177867685401519566439976175259648/38766215100768907378449375:ℝ),(6800937164946244018367888665084952576/38766215100768907378449375:ℝ),(12640659386695333889903390791565312/221521229147250899305425:ℝ)],
![(47829634237576942876383937863483392/1550648604030756295137975:ℝ),(700620653637354986505265833727885312/7753243020153781475689875:ℝ),(136792699353799399436017118098751488/1550648604030756295137975:ℝ),(222490552940129386739939446083289088/7753243020153781475689875:ℝ)]]
theorem admission018_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (26218000125194466043314842179/225829570919465876795916288000:ℝ) admission018_06_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission018_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission018_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission018_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission018_06_coefficients]
def admission018_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(9063275352297349117501900508106752/149676506180574931963125:ℝ),(26902410472890840375170608131739648/149676506180574931963125:ℝ),(6900478635170714472951009646739456/38805020120889797175625:ℝ),(12287795461090970393199261419307008/209547108652804904748375:ℝ)],
![(17985440873291443386013459199168512/149676506180574931963125:ℝ),(53383782630132333265191285445234688/149676506180574931963125:ℝ),(13692390847839340770577043067764736/38805020120889797175625:ℝ),(24381232118755194330267075821436928/209547108652804904748375:ℝ)],
![(1784433104198818853702311738212352/29935301236114986392625:ℝ),(5296274431448298578004135462699008/29935301236114986392625:ℝ),(194054634647675037075029526315008/1108714860596851347875:ℝ),(345526761647549255344794697203712/5987060247222997278525:ℝ)]]
theorem admission018_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (1287187493024577406588177/5449555282805643745075200:ℝ) admission018_07_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission018_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission018_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission018_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission018_07_coefficients]
def admission018_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6648658321617450685716967814336441228633/8700503753986173035430908203125:ℝ),(440139722180409698005401272376034210986179/182710578833709633744049072265625:ℝ),(1076598364629974358454485516837215287080677/426324683945322478736114501953125:ℝ),(160879421659015873617544479092170441242547/182710578833709633744049072265625:ℝ)],
![(2996886013408057439438049647231188262336/1740100750797234607086181640625:ℝ),(197053847444956393811906251578305918566892/36542115766741926748809814453125:ℝ),(2395167701969924240493627557354840374508746/426324683945322478736114501953125:ℝ),(2491301857436156535848422506580292190251978/1278974051835967436208343505859375:ℝ)],
![(8335771745422836511473280421819500083047/8700503753986173035430908203125:ℝ),(545129515044372271054129985515495381848281/182710578833709633744049072265625:ℝ),(1318569337339949882039142040517625087428069/426324683945322478736114501953125:ℝ),(1365145905823045420525611152935099101554149/1278974051835967436208343505859375:ℝ)]]
theorem admission018_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (6648658321617450685716967814336441228633/2125845565559230169507430400000000000000000:ℝ) admission018_08_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission018_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission018_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission018_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission018_08_coefficients]
def admission018_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1481213774760727519726388934512267033696/682119494312515965977783203125:ℝ),(12836824627344978716303742607269151401664/2046358482937547897933349609375:ℝ),(12344707716096638572894718796505890512896/2046358482937547897933349609375:ℝ),(87812064064327895051042429508402282496/45474632954167731065185546875:ℝ)],
![(2817532144428427522204319214148689018976/682119494312515965977783203125:ℝ),(24384550978724083550048659051916273495744/2046358482937547897933349609375:ℝ),(23415162875749294032625354165482290241536/2046358482937547897933349609375:ℝ),(3393762079907014069362635659676483584/928053733758525123779296875:ℝ)],
![(267263673933540000495586055927284397056/136423898862503193195556640625:ℝ),(2309545270275820966748983288929424418816/409271696587509579586669921875:ℝ),(2214091031930531091946127073795279945728/409271696587509579586669921875:ℝ),(5232151856741052956515114521049694208/3031642196944515404345703125:ℝ)]]
theorem admission018_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (11226979901950234558257110283243/1589453624151646092313600000000000:ℝ) admission018_09_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission018_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission018_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission018_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission018_09_coefficients]
def admission018_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(16843462540341572349144125756/28855942166748046875:ℝ),(6889262837278013255107182772/4122277452392578125:ℝ),(1312169845963069876953510544/824455490478515625:ℝ),(4848210081239386543922238464/9618647388916015625:ℝ)],
![(19090310968036135336032918272/17313565300048828125:ℝ),(2181445289414331565107384064/692542612001953125:ℝ),(51809077011199987328770448384/17313565300048828125:ℝ),(259735424853219579954266112/274818496826171875:ℝ)],
![(1795295260134429147955843072/3462713060009765625:ℝ),(5115642392735115260976828416/3462713060009765625:ℝ),(4846149462643729806086127616/3462713060009765625:ℝ),(169534442227004854785015808/384745895556640625:ℝ)]]
theorem admission018_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (2910251579366767297869/1613741248716800000000000:ℝ) admission018_10_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission018_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission018_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission018_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission018_10_coefficients]
def admission018_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7431684678893425863387412852109312/149676506180574931963125:ℝ),(2451100668379933990431897638957056/16630722908952770218125:ℝ),(152780919361161023561406055285522432/1047735543264024523741875:ℝ),(16794456668493054402636131331997696/349245181088008174580625:ℝ)],
![(2106386538413737661506779746308096/21382358025796418851875:ℝ),(1620955084983276997078591840243712/5543574302984256739375:ℝ),(303097362162012682056797003044093952/1047735543264024523741875:ℝ),(33316597160815491674258450935709696/349245181088008174580625:ℝ)],
![(1462604218000547553432009074409472/29935301236114986392625:ℝ),(68907559616282771451539368050688/475163511684364863375:ℝ),(4294755508595761671296884221673472/29935301236114986392625:ℝ),(18882446276939928310425508118528/399137349814866485235:ℝ)]]
theorem admission018_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (70342593926712603533363/363303685520376249671680:ℝ) admission018_11_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission018_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission018_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission018_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission018_11_coefficients]
def admission018_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(22083634536606859264/10986328125:ℝ),(22083634536606859264/3662109375:ℝ),(22083634536606859264/3662109375:ℝ),(22083634536606859264/10986328125:ℝ)],
![(44167269073213718528/10986328125:ℝ),(44167269073213718528/3662109375:ℝ),(44167269073213718528/3662109375:ℝ),(44167269073213718528/10986328125:ℝ)],
![(22083634536606859264/10986328125:ℝ),(22083634536606859264/3662109375:ℝ),(22083634536606859264/3662109375:ℝ),(22083634536606859264/10986328125:ℝ)]]
theorem admission018_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (41133974747/5000000000000:ℝ) admission018_12_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission018_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission018_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission018_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission018_12_coefficients]
def admission018_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(777150551084689784832/762939453125:ℝ),(2331451653254069354496/762939453125:ℝ),(2331451653254069354496/762939453125:ℝ),(777150551084689784832/762939453125:ℝ)],
![(1554301102169379569664/762939453125:ℝ),(4662903306508138708992/762939453125:ℝ),(4662903306508138708992/762939453125:ℝ),(1554301102169379569664/762939453125:ℝ)],
![(777150551084689784832/762939453125:ℝ),(2331451653254069354496/762939453125:ℝ),(2331451653254069354496/762939453125:ℝ),(777150551084689784832/762939453125:ℝ)]]
theorem admission018_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (208448021404809/50000000000000000:ℝ) admission018_13_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission018_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission018_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission018_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission018_13_coefficients]
def admission018_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1099511627776/9:ℝ),(1099511627776/3:ℝ),(1099511627776/3:ℝ),(1099511627776/9:ℝ)],
![(2199023255552/9:ℝ),(2199023255552/3:ℝ),(2199023255552/3:ℝ),(2199023255552/9:ℝ)],
![(1099511627776/9:ℝ),(1099511627776/3:ℝ),(1099511627776/3:ℝ),(1099511627776/9:ℝ)]]
theorem admission018_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission018_14_coefficients (477/1024:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission018_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission018_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission018_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission018_14_coefficients]
theorem admission018_all {δ p : ℝ}
 (hd : δ∈Set.Icc (477/1024:ℝ) (15/32:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission018_00_pos hd hp
 · exact admission018_01_pos hd hp
 · exact admission018_02_pos hd hp
 · exact admission018_03_pos hd hp
 · exact admission018_04_pos hd hp
 · exact admission018_05_pos hd hp
 · exact admission018_06_pos hd hp
 · exact admission018_07_pos hd hp
 · exact admission018_08_pos hd hp
 · exact admission018_09_pos hd hp
 · exact admission018_10_pos hd hp
 · exact admission018_11_pos hd hp
 · exact admission018_12_pos hd hp
 · exact admission018_13_pos hd hp
 · exact admission018_14_pos hd hp
end
end DasStageAFinite
#print axioms DasStageAFinite.admission018_all
