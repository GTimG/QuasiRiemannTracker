/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def admission007_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6215350407257051365376/3376969689:ℝ),(390338399179877606490112/70916363469:ℝ),(389109722702560976961536/70916363469:ℝ),(129293682075081449144320/70916363469:ℝ)],
![(12430700814514102730752/3376969689:ℝ),(780676798359755212980224/70916363469:ℝ),(778219445405121953923072/70916363469:ℝ),(258587364150162898288640/70916363469:ℝ)],
![(6215350407257051365376/3376969689:ℝ),(390338399179877606490112/70916363469:ℝ),(389109722702560976961536/70916363469:ℝ),(129293682075081449144320/70916363469:ℝ)]]
theorem admission007_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (29397979705/31518383764:ℝ) admission007_00_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission007_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission007_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission007_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission007_00_coefficients]
def admission007_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(13618006772173879902208/10130909067:ℝ),(285290947448291477946368/70916363469:ℝ),(284603752680931477946368/70916363469:ℝ),(31546284212619053105152/23638787823:ℝ)],
![(27236013544347759804416/10130909067:ℝ),(570581894896582955892736/70916363469:ℝ),(569207505361862955892736/70916363469:ℝ),(63092568425238106210304/23638787823:ℝ)],
![(13618006772173879902208/10130909067:ℝ),(285290947448291477946368/70916363469:ℝ),(284603752680931477946368/70916363469:ℝ),(31546284212619053105152/23638787823:ℝ)]]
theorem admission007_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (5379595941/7879595941:ℝ) admission007_01_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission007_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission007_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission007_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission007_01_coefficients]
def admission007_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4327923860701138600853504/6331818166875:ℝ),(18135937136304711037616128/8864545433625:ℝ),(90472970288323199758237696/44322727168125:ℝ),(30088751631707614776131584/44322727168125:ℝ)],
![(8655847721402277201707008/6331818166875:ℝ),(36271874272609422075232256/8864545433625:ℝ),(180945940576646399516475392/44322727168125:ℝ),(60177503263415229552263168/44322727168125:ℝ)],
![(4327923860701138600853504/6331818166875:ℝ),(18135937136304711037616128/8864545433625:ℝ),(90472970288323199758237696/44322727168125:ℝ),(30088751631707614776131584/44322727168125:ℝ)]]
theorem admission007_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218924481535997/630367675280000:ℝ) admission007_02_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission007_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission007_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission007_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission007_02_coefficients]
def admission007_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(10348705406251748556800/10130909067:ℝ),(92726320096907628642304/30392727201:ℝ),(646203626892766641913856/212749090407:ℝ),(214442199745699961110528/212749090407:ℝ)],
![(144401138753300410138624/70916363469:ℝ),(1293843082443938758393856/212749090407:ℝ),(1288083111960973825540096/212749090407:ℝ),(61063349396705185366016/30392727201:ℝ)],
![(71960200909538170241024/70916363469:ℝ),(644758841765585357897728/212749090407:ℝ),(641879485068207183626240/212749090407:ℝ),(213001246031236336451584/212749090407:ℝ)]]
theorem admission007_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (49593217212529/96824474923008:ℝ) admission007_03_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission007_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission007_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission007_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission007_03_coefficients]
def admission007_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2283504515351925038317568/14774242389375:ℝ),(90667182736794381385728/196989898525:ℝ),(6749683725073453099778048/14774242389375:ℝ),(2233149535165799534166016/14774242389375:ℝ)],
![(4596723859983571948822528/14774242389375:ℝ),(4562963275679098405265408/4924747463125:ℝ),(13587848583900661802860544/14774242389375:ℝ),(1498560872282312845295616/4924747463125:ℝ)],
![(462643868926329382100992/2954848477875:ℝ),(2296283707259238870622208/4924747463125:ℝ),(325626898039390890622976/703535351875:ℝ),(323219011668734143102976/2110606055625:ℝ)]]
theorem admission007_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (12478695447551829/161374124871680000:ℝ) admission007_04_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission007_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission007_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission007_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission007_04_coefficients]
def admission007_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(901801378717397038911488/8864545433625:ℝ),(1932612363578353499721728/6331818166875:ℝ),(13529379530394740391817216/44322727168125:ℝ),(100224441754072246407168/984949492625:ℝ)],
![(1770756839884136578613248/8864545433625:ℝ),(5312988951929309750902784/8864545433625:ℝ),(5313638005157417435324416/8864545433625:ℝ),(118093726207482950868992/590969695575:ℝ)],
![(173791092233347907940352/1772909086725:ℝ),(13036658214598074256461824/44322727168125:ℝ),(13038810495392346784804864/44322727168125:ℝ),(289795305775198015123456/2954848477875:ℝ)]]
theorem admission007_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (42429465877282204087/846065171807233638400:ℝ) admission007_05_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission007_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission007_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission007_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission007_05_coefficients]
def admission007_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(973348577674659200185885765351309312/4307357233418767486494375:ℝ),(5191569919082748618640989335966777344/7753243020153781475689875:ℝ),(25636891783233147398147514031881060352/38766215100768907378449375:ℝ),(1687835439067839949922147848041791488/7753243020153781475689875:ℝ)],
![(130547496469611032107210241801101312/287157148894584499099625:ℝ),(1492151101701609980317485870718263296/1107606145736254496527125:ℝ),(10316411283639304770004501978176028672/7753243020153781475689875:ℝ),(485162156700436656930053915968274432/1107606145736254496527125:ℝ)],
![(984863869369506281422267861665210368/4307357233418767486494375:ℝ),(5253487792828521243581411759061065728/7753243020153781475689875:ℝ),(25945164634963376451874995858999083008/38766215100768907378449375:ℝ),(1708299657835216648588229563736129536/7753243020153781475689875:ℝ)]]
theorem admission007_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (3143838493279814626876540199/28228696364933234599489536000:ℝ) admission007_06_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission007_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission007_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission007_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission007_06_coefficients]
def admission007_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(527168339925145270799873057023000576/1047735543264024523741875:ℝ),(314608384935447199685969354298425344/209547108652804904748375:ℝ),(521531878558491349072115584548732928/349245181088008174580625:ℝ),(103744410184676663917274607835414528/209547108652804904748375:ℝ)],
![(209299711079386442449266522483761152/209547108652804904748375:ℝ),(624526675040470643089710733727277056/209547108652804904748375:ℝ),(207053637967674518941980616925642752/69849036217601634916125:ℝ),(205933949941939356185497639533412352/209547108652804904748375:ℝ)],
![(74190030781683848778065650770829312/149676506180574931963125:ℝ),(44274041443574777629105911346978816/29935301236114986392625:ℝ),(73390901611411606519683928582782976/49892168726858310654375:ℝ),(14598505679608956038317575956856832/29935301236114986392625:ℝ)]]
theorem admission007_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (217534686321153581713401913/871928845248902999212032000:ℝ) admission007_07_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission007_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission007_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission007_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission007_07_coefficients]
def admission007_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(48115636860312131632209018887121802622224/47369409327258053192901611328125:ℝ),(949006536724332232812538121861329811909264/255794810367193487241668701171875:ℝ),(621270434069520380464640359489385649160816/142108227981774159578704833984375:ℝ),(2145510168142262283559212708634174203701072/1278974051835967436208343505859375:ℝ)],
![(168373388375697989326790197611553726041932/47369409327258053192901611328125:ℝ),(15297513865118110465040260282470108192468692/1278974051835967436208343505859375:ℝ),(1883822104032253865979222482939192382593248/142108227981774159578704833984375:ℝ),(6202939969963999008740823811587596510252704/1278974051835967436208343505859375:ℝ)],
![(120257751515385857694581178724431923419708/47369409327258053192901611328125:ℝ),(10552481181496449300977569673163459132922372/1278974051835967436208343505859375:ℝ),(420850556654244495171527374483268911144144/47369409327258053192901611328125:ℝ),(579632828831676675025944443279060329507376/182710578833709633744049072265625:ℝ)]]
theorem admission007_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (27065045733925574043117573124006013975001/52083216356201139152932044800000000000000000:ℝ) admission007_08_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission007_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission007_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission007_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission007_08_coefficients]
def admission007_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(45746327912955696793319188869082590827264/2046358482937547897933349609375:ℝ),(14983876546380881620346558168471461141504/227373164770838655325927734375:ℝ),(132476417039555144787736123091386536558592/2046358482937547897933349609375:ℝ),(321243508828187326700393121153870200832/15158210984722577021728515625:ℝ)],
![(17614955679725581901504177031443313459104/409271696587509579586669921875:ℝ),(1922337250219117938952361621037829067136/15158210984722577021728515625:ℝ),(50963547859639964548605085631724080103424/409271696587509579586669921875:ℝ),(264688966180489593510833290483138035712/6496376136309675866455078125:ℝ)],
![(42328450485672212714201696288133976468256/2046358482937547897933349609375:ℝ),(13851182206905887463938866147095974865536/227373164770838655325927734375:ℝ),(122341322258644677955289305067233863958528/2046358482937547897933349609375:ℝ),(889092236778865174474653669920355647488/45474632954167731065185546875:ℝ)]]
theorem admission007_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (2543713293396564029144249925385539/254312579864263374770176000000000000:ℝ) admission007_09_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission007_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission007_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission007_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission007_09_coefficients]
def admission007_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(523955990047658055412404904448/86567826500244140625:ℝ),(1540103427842577485110781235712/86567826500244140625:ℝ),(301679027690763614991469551616/17313565300048828125:ℝ),(54694208140224849473219047424/9618647388916015625:ℝ)],
![(201589157399682252126860765056/17313565300048828125:ℝ),(422981386645427286937034637952/12366832357177734375:ℝ),(2898012420309687771533323455488/86567826500244140625:ℝ),(15001410289959551962037854208/1374092484130859375:ℝ)],
![(53742732911007193072896195272/9618647388916015625:ℝ),(157761749432213772834071755528/9618647388916015625:ℝ),(30860262223162869363681610048/1923729477783203125:ℝ),(50282314025906595182232489984/9618647388916015625:ℝ)]]
theorem admission007_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (110483600154579921054710061/41311775967150080000000000000:ℝ) admission007_10_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission007_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission007_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission007_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission007_10_coefficients]
def admission007_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(144287522994705571519856407915986944/349245181088008174580625:ℝ),(1291650511341007844480089846452649984/1047735543264024523741875:ℝ),(256945892239811254917789591969726464/209547108652804904748375:ℝ),(141980506280721714889475779047981056/349245181088008174580625:ℝ)],
![(286378298201048355213308362573717504/349245181088008174580625:ℝ),(2563585078961642459644740162283298816/1047735543264024523741875:ℝ),(2549797633814732872197338267371175936/1047735543264024523741875:ℝ),(281782483152078492730841064269676544/349245181088008174580625:ℝ)],
![(4059736434466936676955770133078016/9978433745371662130875:ℝ),(181704938231519230737807187975806976/149676506180574931963125:ℝ),(180724024659382371086912901074649088/149676506180574931963125:ℝ),(19971710981622396834480755031670784/49892168726858310654375:ℝ)]]
theorem admission007_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (297601684654092741526376531/1453214742081504998686720000:ℝ) admission007_11_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission007_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission007_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission007_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission007_11_coefficients]
def admission007_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(176669076292854874112/10986328125:ℝ),(176669076292854874112/3662109375:ℝ),(176669076292854874112/3662109375:ℝ),(176669076292854874112/10986328125:ℝ)],
![(353338152585709748224/10986328125:ℝ),(353338152585709748224/3662109375:ℝ),(353338152585709748224/3662109375:ℝ),(353338152585709748224/10986328125:ℝ)],
![(176669076292854874112/10986328125:ℝ),(176669076292854874112/3662109375:ℝ),(176669076292854874112/3662109375:ℝ),(176669076292854874112/10986328125:ℝ)]]
theorem admission007_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (41133974747/5000000000000:ℝ) admission007_12_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission007_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission007_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission007_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission007_12_coefficients]
def admission007_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6217204408677518278656/762939453125:ℝ),(18651613226032554835968/762939453125:ℝ),(18651613226032554835968/762939453125:ℝ),(6217204408677518278656/762939453125:ℝ)],
![(12434408817355036557312/762939453125:ℝ),(37303226452065109671936/762939453125:ℝ),(37303226452065109671936/762939453125:ℝ),(12434408817355036557312/762939453125:ℝ)],
![(6217204408677518278656/762939453125:ℝ),(18651613226032554835968/762939453125:ℝ),(18651613226032554835968/762939453125:ℝ),(6217204408677518278656/762939453125:ℝ)]]
theorem admission007_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (208448021404809/50000000000000000:ℝ) admission007_13_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission007_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission007_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission007_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission007_13_coefficients]
def admission007_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8796093022208/9:ℝ),(8796093022208/3:ℝ),(8796093022208/3:ℝ),(8796093022208/9:ℝ)],
![(17592186044416/9:ℝ),(17592186044416/3:ℝ),(17592186044416/3:ℝ),(17592186044416/9:ℝ)],
![(8796093022208/9:ℝ),(8796093022208/3:ℝ),(8796093022208/3:ℝ),(8796093022208/9:ℝ)]]
theorem admission007_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission007_14_coefficients (57/128:ℝ) (459/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission007_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission007_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission007_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission007_14_coefficients]
theorem admission007_all {δ p : ℝ}
 (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission007_00_pos hd hp
 · exact admission007_01_pos hd hp
 · exact admission007_02_pos hd hp
 · exact admission007_03_pos hd hp
 · exact admission007_04_pos hd hp
 · exact admission007_05_pos hd hp
 · exact admission007_06_pos hd hp
 · exact admission007_07_pos hd hp
 · exact admission007_08_pos hd hp
 · exact admission007_09_pos hd hp
 · exact admission007_10_pos hd hp
 · exact admission007_11_pos hd hp
 · exact admission007_12_pos hd hp
 · exact admission007_13_pos hd hp
 · exact admission007_14_pos hd hp
end
end DasStageAFinite
#print axioms DasStageAFinite.admission007_all
