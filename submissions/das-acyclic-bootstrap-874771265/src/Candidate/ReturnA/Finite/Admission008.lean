/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def admission008_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1039264162509918111268864/70916363469:ℝ),(3112877781620487815692288/70916363469:ℝ),(3107963075711221297577984/70916363469:ℝ),(1034349456600651593154560/70916363469:ℝ)],
![(2078528325019836222537728/70916363469:ℝ),(6225755563240975631384576/70916363469:ℝ),(6215926151422442595155968/70916363469:ℝ),(2068698913201303186309120/70916363469:ℝ)],
![(1039264162509918111268864/70916363469:ℝ),(3112877781620487815692288/70916363469:ℝ),(3107963075711221297577984/70916363469:ℝ),(1034349456600651593154560/70916363469:ℝ)]]
theorem admission008_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (29397979705/31518383764:ℝ) admission008_00_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission008_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission008_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission008_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission008_00_coefficients]
def admission008_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(759859600172297274523648/70916363469:ℝ),(2276830021447451823570944/70916363469:ℝ),(2274081242378011823570944/70916363469:ℝ),(252370273700952424841216/23638787823:ℝ)],
![(1519719200344594549047296/70916363469:ℝ),(4553660042894903647141888/70916363469:ℝ),(4548162484756023647141888/70916363469:ℝ),(504740547401904849682432/23638787823:ℝ)],
![(759859600172297274523648/70916363469:ℝ),(2276830021447451823570944/70916363469:ℝ),(2274081242378011823570944/70916363469:ℝ),(252370273700952424841216/23638787823:ℝ)]]
theorem admission008_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (5379595941/7879595941:ℝ) admission008_01_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission008_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission008_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission008_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission008_01_coefficients]
def admission008_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(26837430514051371103158272/4924747463125:ℝ),(723783762306585598065901568/44322727168125:ℝ),(722956900733784176346529792/44322727168125:ℝ),(240710013053660918209052672/44322727168125:ℝ)],
![(53674861028102742206316544/4924747463125:ℝ),(1447567524613171196131803136/44322727168125:ℝ),(1445913801467568352693059584/44322727168125:ℝ),(481420026107321836418105344/44322727168125:ℝ)],
![(26837430514051371103158272/4924747463125:ℝ),(723783762306585598065901568/44322727168125:ℝ),(722956900733784176346529792/44322727168125:ℝ),(240710013053660918209052672/44322727168125:ℝ)]]
theorem admission008_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218924481535997/630367675280000:ℝ) admission008_02_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission008_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission008_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission008_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission008_02_coefficients]
def admission008_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1727052880848106723213312/212749090407:ℝ),(5169636187401973135310848/212749090407:ℝ),(5158120904519466100981760/212749090407:ℝ),(1715537597965599688884224/212749090407:ℝ)],
![(3442573056441750111911936/212749090407:ℝ),(10304679287393390604320768/212749090407:ℝ),(10281653797167130872905728/212749090407:ℝ),(488506795173641482928128/30392727201:ℝ)],
![(245074310799091912671232/30392727201:ℝ),(5135043099991417469009920/212749090407:ℝ),(5123532892647664771923968/212749090407:ℝ),(1704009968249890691612672/212749090407:ℝ)]]
theorem admission008_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (49593217212529/96824474923008:ℝ) admission008_03_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission008_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission008_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission008_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission008_03_coefficients]
def admission008_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2580910925835822325170176/2110606055625:ℝ),(53997709521807766811967488/14774242389375:ℝ),(53796529322283406809104384/14774242389375:ℝ),(17865196281326396273328128/14774242389375:ℝ)],
![(12123048295922822501122048/4924747463125:ℝ),(108703269690758868858355712/14774242389375:ℝ),(108299585737765909642084352/14774242389375:ℝ),(11988486978258502762364928/4924747463125:ℝ)],
![(18302768406917711227174912/14774242389375:ℝ),(18235186722983700682129408/4924747463125:ℝ),(2595383638832500134903808/703535351875:ℝ),(2585752093349873144823808/2110606055625:ℝ)]]
theorem admission008_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (12478695447551829/161374124871680000:ℝ) admission008_04_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission008_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission008_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission008_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission008_04_coefficients]
def admission008_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(12024098090024065827823616/14774242389375:ℝ),(108221254751601656025473024/44322727168125:ℝ),(15460754419300601937043456/6331818166875:ℝ),(5153760064796393573900288/6331818166875:ℝ)],
![(23611663764877677586939904/14774242389375:ℝ),(212517954948461251970891776/44322727168125:ℝ),(212530242222535482352910336/44322727168125:ℝ),(70847278568707263142838272/44322727168125:ℝ)],
![(3862521891617870586372096/4924747463125:ℝ),(14899528599551370849345536/6331818166875:ℝ),(104304961287431268793606144/44322727168125:ℝ),(34770958115132508125536256/44322727168125:ℝ)]]
theorem admission008_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (4243493289130961337567/84606517180723363840000:ℝ) admission008_05_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission008_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission008_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission008_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission008_05_coefficients]
def admission008_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(13758811154611604608527234368017137664/7753243020153781475689875:ℝ),(205098329495795274276664384928445759488/38766215100768907378449375:ℝ),(203817693477002986587918927010031730688/38766215100768907378449375:ℝ),(13502683512542719599377182784334331904/7753243020153781475689875:ℝ)],
![(3954626642447589871090279573373075456/1107606145736254496527125:ℝ),(82532571139798098395525074573427326976/7753243020153781475689875:ℝ),(82019266297393898262142536854039166976/7753243020153781475689875:ℝ),(3881297253603493255440431327746195456/1107606145736254496527125:ℝ)],
![(13923575342521524489104722645594390528/7753243020153781475689875:ℝ),(207564526203195217700960987938690875392/38766215100768907378449375:ℝ),(206278638009966504722793757260164104192/38766215100768907378449375:ℝ),(13666397262681733188705836509889036288/7753243020153781475689875:ℝ)]]
theorem admission008_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (3143838493279814626876540199/28228696364933234599489536000:ℝ) admission008_06_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission008_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission008_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission008_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission008_06_coefficients]
def admission008_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(836705590240247727206487924267679744/209547108652804904748375:ℝ),(12516798697596668103243318792631484416/1047735543264024523741875:ℝ),(1387005239309166224877984831634407424/116415060362669391526875:ℝ),(829955281477413311338196862683316224/209547108652804904748375:ℝ)],
![(1660921249964819998550416746521378816/209547108652804904748375:ℝ),(4969300705344671650596174707762741248/209547108652804904748375:ℝ),(550650117212818500169971008612073472/23283012072533878305375:ℝ),(1647471599535514849483981116267298816/209547108652804904748375:ℝ)],
![(117745094246367467334846974607671296/29935301236114986392625:ℝ),(1761386404160955735676793535168888832/149676506180574931963125:ℝ),(195177906679275182281695744489422848/16630722908952770218125:ℝ),(116788045436871648306540607654854656/29935301236114986392625:ℝ)]]
theorem admission008_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (217534686321153581713401913/871928845248902999212032000:ℝ) admission008_07_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission008_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission008_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission008_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission008_07_coefficients]
def admission008_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(447668083619360275156119595239183187831392/47369409327258053192901611328125:ℝ),(5663811416416244105176209633788188085135264/182710578833709633744049072265625:ℝ),(2868645037101597340630890831313937579937376/85264936789064495747222900390625:ℝ),(15470020649242791271815620677233756924561376/1278974051835967436208343505859375:ℝ)],
![(1467141217249097258744491103420115308855496/47369409327258053192901611328125:ℝ),(125465899119809512177828986869238900989527336/1278974051835967436208343505859375:ℝ),(6289929105207489776199686151134488746005056/60903526277903211248016357421875:ℝ),(46235398367921378076610428509021498671927232/1278974051835967436208343505859375:ℝ)],
![(1019473133629736983588371508180932121024104/47369409327258053192901611328125:ℝ),(85819219204895803441595519432721584393580488/1278974051835967436208343505859375:ℝ),(29686278550944441730243348901371733322348512/426324683945322478736114501953125:ℝ),(30765377718678586804794807831787741747365856/1278974051835967436208343505859375:ℝ)]]
theorem admission008_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (125906648517945077387658636161020271577579/208332865424804556611728179200000000000000000:ℝ) admission008_08_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission008_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission008_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission008_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission008_08_coefficients]
def admission008_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5657865199392762940773450902102932615424/32481880681548379332275390625:ℝ),(211964537628781636588900193506533461891072/409271696587509579586669921875:ℝ),(1050320152459884048405581348634815871582208/2046358482937547897933349609375:ℝ),(2569948070625498613603144969230961606656/15158210984722577021728515625:ℝ)],
![(15239668240516952799222835970180719402784/45474632954167731065185546875:ℝ),(407712832166617293244942853865565267538176/409271696587509579586669921875:ℝ),(403959049871009990888610310132148675411968/409271696587509579586669921875:ℝ),(2117511729443916748086666323865104285696/6496376136309675866455078125:ℝ)],
![(36593284806835423410700023536183068705952/227373164770838655325927734375:ℝ),(195748294537835656656042660359031805647104/409271696587509579586669921875:ℝ),(969475096895165906037470202025927505477632/2046358482937547897933349609375:ℝ),(7112737894230921395797229359362845179904/45474632954167731065185546875:ℝ)]]
theorem admission008_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (2543713293396564029144249925385539/254312579864263374770176000000000000:ℝ) admission008_09_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission008_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission008_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission008_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission008_09_coefficients]
def admission008_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4064702429606077260739505325056/86567826500244140625:ℝ),(2413454929814513828320956412928/17313565300048828125:ℝ),(11940555032959556042937048154112/86567826500244140625:ℝ),(437553665121798795785752379392/9618647388916015625:ℝ)],
![(7811916762093541814335254561536/86567826500244140625:ℝ),(23184322183879443744902087643904/86567826500244140625:ℝ),(917324634417926894777356464128/3462713060009765625:ℝ),(120011282319676415696302833664/1374092484130859375:ℝ)],
![(416088107484941907907608491024/9618647388916015625:ℝ),(246884525496624900807034130384/1923729477783203125:ℝ),(1220593012774136529460422080768/9618647388916015625:ℝ),(402258512207252761457859919872/9618647388916015625:ℝ)]]
theorem admission008_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (110483600154579921054710061/41311775967150080000000000000:ℝ) admission008_10_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission008_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission008_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission008_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission008_10_coefficients]
def admission008_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3435184060366345978297034367193186304/1047735543264024523741875:ℝ),(3425955993510410551775511851721162752/349245181088008174580625:ℝ),(10250216070902206834376919885121847296/1047735543264024523741875:ℝ),(1135844050245773719115806232383848448/349245181088008174580625:ℝ)],
![(6817865056835755875674526710184656896/1047735543264024523741875:ℝ),(6799481796639876425744657516968493056/349245181088008174580625:ℝ),(20343359928733757227099631383193059328/1047735543264024523741875:ℝ),(2254259865216627941846728514157412352/349245181088008174580625:ℝ)],
![(483240142352772842482498906141638656/149676506180574931963125:ℝ),(481932257589923696281306523606761472/49892168726858310654375:ℝ),(205982527710847967198422683634106368/21382358025796418851875:ℝ),(159773687852979174675846040253366272/49892168726858310654375:ℝ)]]
theorem admission008_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (297601684654092741526376531/1453214742081504998686720000:ℝ) admission008_11_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission008_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission008_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission008_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission008_11_coefficients]
def admission008_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1413352610342838992896/10986328125:ℝ),(1413352610342838992896/3662109375:ℝ),(1413352610342838992896/3662109375:ℝ),(1413352610342838992896/10986328125:ℝ)],
![(2826705220685677985792/10986328125:ℝ),(2826705220685677985792/3662109375:ℝ),(2826705220685677985792/3662109375:ℝ),(2826705220685677985792/10986328125:ℝ)],
![(1413352610342838992896/10986328125:ℝ),(1413352610342838992896/3662109375:ℝ),(1413352610342838992896/3662109375:ℝ),(1413352610342838992896/10986328125:ℝ)]]
theorem admission008_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (41133974747/5000000000000:ℝ) admission008_12_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission008_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission008_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission008_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission008_12_coefficients]
def admission008_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(49737635269420146229248/762939453125:ℝ),(149212905808260438687744/762939453125:ℝ),(149212905808260438687744/762939453125:ℝ),(49737635269420146229248/762939453125:ℝ)],
![(99475270538840292458496/762939453125:ℝ),(298425811616520877375488/762939453125:ℝ),(298425811616520877375488/762939453125:ℝ),(99475270538840292458496/762939453125:ℝ)],
![(49737635269420146229248/762939453125:ℝ),(149212905808260438687744/762939453125:ℝ),(149212905808260438687744/762939453125:ℝ),(49737635269420146229248/762939453125:ℝ)]]
theorem admission008_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (208448021404809/50000000000000000:ℝ) admission008_13_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission008_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission008_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission008_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission008_13_coefficients]
def admission008_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(70368744177664/9:ℝ),(70368744177664/3:ℝ),(70368744177664/3:ℝ),(70368744177664/9:ℝ)],
![(140737488355328/9:ℝ),(140737488355328/3:ℝ),(140737488355328/3:ℝ),(140737488355328/9:ℝ)],
![(70368744177664/9:ℝ),(70368744177664/3:ℝ),(70368744177664/3:ℝ),(70368744177664/9:ℝ)]]
theorem admission008_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission008_14_coefficients (57/128:ℝ) (459/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission008_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission008_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission008_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission008_14_coefficients]
theorem admission008_all {δ p : ℝ}
 (hd : δ∈Set.Icc (57/128:ℝ) (459/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission008_00_pos hd hp
 · exact admission008_01_pos hd hp
 · exact admission008_02_pos hd hp
 · exact admission008_03_pos hd hp
 · exact admission008_04_pos hd hp
 · exact admission008_05_pos hd hp
 · exact admission008_06_pos hd hp
 · exact admission008_07_pos hd hp
 · exact admission008_08_pos hd hp
 · exact admission008_09_pos hd hp
 · exact admission008_10_pos hd hp
 · exact admission008_11_pos hd hp
 · exact admission008_12_pos hd hp
 · exact admission008_13_pos hd hp
 · exact admission008_14_pos hd hp
end
end DasStageAFinite
#print axioms DasStageAFinite.admission008_all
