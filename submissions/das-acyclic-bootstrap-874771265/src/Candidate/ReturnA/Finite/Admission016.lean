/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def admission016_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(24861401629028205461504/3376969689:ℝ),(1561353596719510425960448/70916363469:ℝ),(1556438890810243907846144/70916363469:ℝ),(517174728300325796577280/70916363469:ℝ)],
![(49722803258056410923008/3376969689:ℝ),(3122707193439020851920896/70916363469:ℝ),(3112877781620487815692288/70916363469:ℝ),(1034349456600651593154560/70916363469:ℝ)],
![(24861401629028205461504/3376969689:ℝ),(1561353596719510425960448/70916363469:ℝ),(1556438890810243907846144/70916363469:ℝ),(517174728300325796577280/70916363469:ℝ)]]
theorem admission016_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (29397979705/31518383764:ℝ) admission016_00_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission016_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission016_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission016_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission016_00_coefficients]
def admission016_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(54472027088695519608832/10130909067:ℝ),(1141163789793165911785472/70916363469:ℝ),(1138415010723725911785472/70916363469:ℝ),(126185136850476212420608/23638787823:ℝ)],
![(108944054177391039217664/10130909067:ℝ),(2282327579586331823570944/70916363469:ℝ),(2276830021447451823570944/70916363469:ℝ),(252370273700952424841216/23638787823:ℝ)],
![(54472027088695519608832/10130909067:ℝ),(1141163789793165911785472/70916363469:ℝ),(1138415010723725911785472/70916363469:ℝ),(126185136850476212420608/23638787823:ℝ)]]
theorem admission016_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (5379595941/7879595941:ℝ) admission016_01_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission016_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission016_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission016_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission016_01_coefficients]
def admission016_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(17311695442804554403414016/6331818166875:ℝ),(72543748545218844150464512/8864545433625:ℝ),(361891881153292799032950784/44322727168125:ℝ),(120355006526830459104526336/44322727168125:ℝ)],
![(34623390885609108806828032/6331818166875:ℝ),(145087497090437688300929024/8864545433625:ℝ),(723783762306585598065901568/44322727168125:ℝ),(240710013053660918209052672/44322727168125:ℝ)],
![(17311695442804554403414016/6331818166875:ℝ),(72543748545218844150464512/8864545433625:ℝ),(361891881153292799032950784/44322727168125:ℝ),(120355006526830459104526336/44322727168125:ℝ)]]
theorem admission016_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218924481535997/630367675280000:ℝ) admission016_02_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission016_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission016_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission016_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission016_02_coefficients]
def admission016_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(283509561906704578248704/70916363469:ℝ),(2540078861384280193368064/212749090407:ℝ),(2528586576358939182497792/212749090407:ℝ),(839036400694772723875840/212749090407:ℝ)],
![(566057649944961017184256/70916363469:ℝ),(724500989277574900219904/30392727201:ℝ),(5048524869068759448420352/212749090407:ℝ),(1675190893960618198433792/212749090407:ℝ)],
![(282548088038256438935552/70916363469:ℝ),(2531428063558744108171264/212749090407:ℝ),(2519938292709820265922560/212749090407:ℝ),(836154493265845474557952/212749090407:ℝ)]]
theorem admission016_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (97341194430581/193648949846016:ℝ) admission016_03_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission016_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission016_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission016_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission016_03_coefficients]
def admission016_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(9494571405936951475109888/14774242389375:ℝ),(376984601905618743656448/196989898525:ℝ),(28064474435831726046445568/14774242389375:ℝ),(9285200698847271747321856/14774242389375:ℝ)],
![(3809714494086669338918912/2954848477875:ℝ),(2701205481851385122111488/703535351875:ℝ),(18768637046390321099833344/4924747463125:ℝ),(18629168490725222429753344/14774242389375:ℝ)],
![(9554001064496395219484672/14774242389375:ℝ),(9483823325319227263369216/4924747463125:ℝ),(28241436703339237253054464/14774242389375:ℝ),(3114655930625983560810496/4924747463125:ℝ)]]
theorem admission016_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (51885102124031289/645496499486720000:ℝ) admission016_04_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission016_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission016_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission016_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission016_04_coefficients]
def admission016_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(454315512387291523702784/1266363633375:ℝ),(47733642645242779563646976/44322727168125:ℝ),(47763437677380002368577536/44322727168125:ℝ),(14160744858393267675136/39397979705:ℝ)],
![(1258945067664153266683904/1772909086725:ℝ),(94484028629584758644113408/44322727168125:ℝ),(94545737284755217523130368/44322727168125:ℝ),(2102355689784952703074304/2954848477875:ℝ)],
![(3114516751609725667500032/8864545433625:ℝ),(46750385984341979080466432/44322727168125:ℝ),(46782299607375215154552832/44322727168125:ℝ),(1040299825405457627439104/2954848477875:ℝ)]]
theorem admission016_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (380190033155484090271/8460651718072336384000:ℝ) admission016_05_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission016_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission016_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission016_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission016_05_coefficients]
def admission016_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4033333186259122092642835268309942272/4307357233418767486494375:ℝ),(21515596770603976321155153733133860864/7753243020153781475689875:ℝ),(106262556196330281122154911153375936512/38766215100768907378449375:ℝ),(6996912381479880183681571980499222528/7753243020153781475689875:ℝ)],
![(8089696955907938347758434729247686656/4307357233418767486494375:ℝ),(43155029288699497892191152312456298496/7753243020153781475689875:ℝ),(213141658096121020351764785960987918336/38766215100768907378449375:ℝ),(14034753200494513764695307392387121152/7753243020153781475689875:ℝ)],
![(1352121256549605418371866486979248128/1435785744472922495498125:ℝ),(21639432518095521571035998579322437632/7753243020153781475689875:ℝ),(15268443128541534175658553543944568832/5538030728681272482635625:ℝ),(7037840819014633581013735411887898624/7753243020153781475689875:ℝ)]]
theorem admission016_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (13032764906957522376778669619/112914785459732938397958144000:ℝ) admission016_06_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission016_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission016_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission016_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission016_06_coefficients]
def admission016_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2006076246327749619415404876597231616/1047735543264024523741875:ℝ),(239436397583255942477821606571737088/41909421730560980949675:ℝ),(283507396150727336366060714070114304/49892168726858310654375:ℝ),(78952865036465004846285588311048192/41909421730560980949675:ℝ)],
![(3996476243748782580123982749940072448/1047735543264024523741875:ℝ),(2384983786171711912213760115978223616/209547108652804904748375:ℝ),(3953512411552962502256193828043096064/349245181088008174580625:ℝ),(786418909509822105164752730835648512/209547108652804904748375:ℝ)],
![(1990399997421032960708577873342840832/1047735543264024523741875:ℝ),(1187801798255432199824652083119538176/209547108652804904748375:ℝ),(1968960638497871147693768829552295936/349245181088008174580625:ℝ),(391654584327497080933324789280407552/209547108652804904748375:ℝ)]]
theorem admission016_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (2918054046686716980735397259/12207003833484641988968448000:ℝ) admission016_07_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission016_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission016_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission016_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission016_07_coefficients]
def admission016_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1058167923302133239277301993596208660058704/47369409327258053192901611328125:ℝ),(17647351847749979641916424121584920116811216/255794810367193487241668701171875:ℝ),(10084483014967233628320970510578155573033776/142108227981774159578704833984375:ℝ),(31094066732632548488965832510910172144832912/1278974051835967436208343505859375:ℝ)],
![(2260620075914413930679348306867037561712376/47369409327258053192901611328125:ℝ),(188088415473249372692993999343562821314864264/1278974051835967436208343505859375:ℝ),(7150509500573631155580608183025717771536928/47369409327258053192901611328125:ℝ),(66011972732624045861176461810458840495366944/1278974051835967436208343505859375:ℝ)],
![(1202452152612280691402046313270828901653672/47369409327258053192901611328125:ℝ),(14264522319214210640487411247948317247258312/182710578833709633744049072265625:ℝ),(11367045486753659838420854038498997741577008/142108227981774159578704833984375:ℝ),(34917905999991497372210629299548668350534032/1278974051835967436208343505859375:ℝ)]]
theorem admission016_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (595219456857449947093482371397867371283021/208332865424804556611728179200000000000000000:ℝ) admission016_08_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission016_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission016_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission016_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission016_08_coefficients]
def admission016_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(137902206801339088059587151836484821421824/2046358482937547897933349609375:ℝ),(45066159839563639655978363595181241519104/227373164770838655325927734375:ℝ),(397501253629329131527611514694645612019712/2046358482937547897933349609375:ℝ),(576924867952837889451976687562025598976/9094926590833546213037109375:ℝ)],
![(268968658748111207960939318511072414125632/2046358482937547897933349609375:ℝ),(87866931000177290999141343147611510486272/227373164770838655325927734375:ℝ),(774732317696837329390329393340985878839296/2046358482937547897933349609375:ℝ),(5619972100116985283266715488537746079744/45474632954167731065185546875:ℝ)],
![(18723778849538874271621738096369656100544/292336926133935413990478515625:ℝ),(14266923720204550447720993184143422989056/75791054923612885108642578125:ℝ),(377231064067508197862717878646340266819584/2046358482937547897933349609375:ℝ),(911782586784265278668944016909206028288/15158210984722577021728515625:ℝ)]]
theorem admission016_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (3912946358231729272852180553523471/508625159728526749540352000000000000:ℝ) admission016_09_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission016_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission016_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission016_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission016_09_coefficients]
def admission016_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(310184914431300167924323925632/17313565300048828125:ℝ),(4539919729852050132998380289152/86567826500244140625:ℝ),(4427237077918841444465151693824/86567826500244140625:ℝ),(159804740690869266787599003648/9618647388916015625:ℝ)],
![(1004863980026222919094077122624/28855942166748046875:ℝ),(2939770783506007570689516747328/28855942166748046875:ℝ),(2865062293038937442373427126784/28855942166748046875:ℝ),(62010399230844561051865833472/1923729477783203125:ℝ)],
![(1463362167170479450094778576328/86567826500244140625:ℝ),(4278482086880483011128354522632/86567826500244140625:ℝ),(833408863876886061488965288256/17313565300048828125:ℝ),(150213905599768119392916721664/9618647388916015625:ℝ)]]
theorem admission016_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (330059851171365496712951781/165247103868600320000000000000:ℝ) admission016_10_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission016_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission016_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission016_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission016_10_coefficients]
def admission016_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(548391968561129685774934185554935808/349245181088008174580625:ℝ),(981818761520440528422549907936968704/209547108652804904748375:ℝ),(697531618617463088369335296052953088/149676506180574931963125:ℝ),(107920228560228535586493339290042368/69849036217601634916125:ℝ)],
![(1092390441545533795897059464593358848/349245181088008174580625:ℝ),(9778755727763658825594620018125684736/1047735543264024523741875:ℝ),(9726120083477723883209578840089165824/1047735543264024523741875:ℝ),(1074845226783555481768712405247852544/349245181088008174580625:ℝ)],
![(108799694596880822024425055807684608/69849036217601634916125:ℝ),(4869661920161456183481870478440841216/1047735543264024523741875:ℝ),(4843398753155482264624231767718494208/1047735543264024523741875:ℝ),(535244083982412803836245708797640704/349245181088008174580625:ℝ)]]
theorem admission016_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (3987879186737632780047101593/20345006389141069981614080000:ℝ) admission016_11_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission016_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission016_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission016_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission016_11_coefficients]
def admission016_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(706676305171419496448/10986328125:ℝ),(706676305171419496448/3662109375:ℝ),(706676305171419496448/3662109375:ℝ),(706676305171419496448/10986328125:ℝ)],
![(1413352610342838992896/10986328125:ℝ),(1413352610342838992896/3662109375:ℝ),(1413352610342838992896/3662109375:ℝ),(1413352610342838992896/10986328125:ℝ)],
![(706676305171419496448/10986328125:ℝ),(706676305171419496448/3662109375:ℝ),(706676305171419496448/3662109375:ℝ),(706676305171419496448/10986328125:ℝ)]]
theorem admission016_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (41133974747/5000000000000:ℝ) admission016_12_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission016_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission016_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission016_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission016_12_coefficients]
def admission016_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(24868817634710073114624/762939453125:ℝ),(74606452904130219343872/762939453125:ℝ),(74606452904130219343872/762939453125:ℝ),(24868817634710073114624/762939453125:ℝ)],
![(49737635269420146229248/762939453125:ℝ),(149212905808260438687744/762939453125:ℝ),(149212905808260438687744/762939453125:ℝ),(49737635269420146229248/762939453125:ℝ)],
![(24868817634710073114624/762939453125:ℝ),(74606452904130219343872/762939453125:ℝ),(74606452904130219343872/762939453125:ℝ),(24868817634710073114624/762939453125:ℝ)]]
theorem admission016_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (208448021404809/50000000000000000:ℝ) admission016_13_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission016_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission016_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission016_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission016_13_coefficients]
def admission016_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(35184372088832/9:ℝ),(35184372088832/3:ℝ),(35184372088832/3:ℝ),(35184372088832/9:ℝ)],
![(70368744177664/9:ℝ),(70368744177664/3:ℝ),(70368744177664/3:ℝ),(70368744177664/9:ℝ)],
![(35184372088832/9:ℝ),(35184372088832/3:ℝ),(35184372088832/3:ℝ),(35184372088832/9:ℝ)]]
theorem admission016_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission016_14_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission016_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission016_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission016_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission016_14_coefficients]
theorem admission016_all {δ p : ℝ}
 (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission016_00_pos hd hp
 · exact admission016_01_pos hd hp
 · exact admission016_02_pos hd hp
 · exact admission016_03_pos hd hp
 · exact admission016_04_pos hd hp
 · exact admission016_05_pos hd hp
 · exact admission016_06_pos hd hp
 · exact admission016_07_pos hd hp
 · exact admission016_08_pos hd hp
 · exact admission016_09_pos hd hp
 · exact admission016_10_pos hd hp
 · exact admission016_11_pos hd hp
 · exact admission016_12_pos hd hp
 · exact admission016_13_pos hd hp
 · exact admission016_14_pos hd hp
end
end DasStageAFinite
#print axioms DasStageAFinite.admission016_all
