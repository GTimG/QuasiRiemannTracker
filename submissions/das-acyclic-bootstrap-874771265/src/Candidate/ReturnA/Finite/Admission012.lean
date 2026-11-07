/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def admission012_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6215350407257051365376/3376969689:ℝ),(390338399179877606490112/70916363469:ℝ),(389109722702560976961536/70916363469:ℝ),(129293682075081449144320/70916363469:ℝ)],
![(12430700814514102730752/3376969689:ℝ),(780676798359755212980224/70916363469:ℝ),(778219445405121953923072/70916363469:ℝ),(258587364150162898288640/70916363469:ℝ)],
![(6215350407257051365376/3376969689:ℝ),(390338399179877606490112/70916363469:ℝ),(389109722702560976961536/70916363469:ℝ),(129293682075081449144320/70916363469:ℝ)]]
theorem admission012_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (29397979705/31518383764:ℝ) admission012_00_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission012_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission012_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission012_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission012_00_coefficients]
def admission012_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(13618006772173879902208/10130909067:ℝ),(285290947448291477946368/70916363469:ℝ),(284603752680931477946368/70916363469:ℝ),(31546284212619053105152/23638787823:ℝ)],
![(27236013544347759804416/10130909067:ℝ),(570581894896582955892736/70916363469:ℝ),(569207505361862955892736/70916363469:ℝ),(63092568425238106210304/23638787823:ℝ)],
![(13618006772173879902208/10130909067:ℝ),(285290947448291477946368/70916363469:ℝ),(284603752680931477946368/70916363469:ℝ),(31546284212619053105152/23638787823:ℝ)]]
theorem admission012_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (5379595941/7879595941:ℝ) admission012_01_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission012_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission012_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission012_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission012_01_coefficients]
def admission012_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4327923860701138600853504/6331818166875:ℝ),(18135937136304711037616128/8864545433625:ℝ),(90472970288323199758237696/44322727168125:ℝ),(30088751631707614776131584/44322727168125:ℝ)],
![(8655847721402277201707008/6331818166875:ℝ),(36271874272609422075232256/8864545433625:ℝ),(180945940576646399516475392/44322727168125:ℝ),(60177503263415229552263168/44322727168125:ℝ)],
![(4327923860701138600853504/6331818166875:ℝ),(18135937136304711037616128/8864545433625:ℝ),(90472970288323199758237696/44322727168125:ℝ),(30088751631707614776131584/44322727168125:ℝ)]]
theorem admission012_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218924481535997/630367675280000:ℝ) admission012_02_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission012_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission012_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission012_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission012_02_coefficients]
def admission012_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(71719203898321843257344/70916363469:ℝ),(642592335655135583666176/212749090407:ℝ),(639715493134174578016256/212749090407:ℝ),(212280769174004524122112/212749090407:ℝ)],
![(142957670862419616858112/70916363469:ℝ),(1280859272397503124733952/212749090407:ℝ),(1275106844443789697744896/212749090407:ℝ),(423120584633545423585280/212749090407:ℝ)],
![(71238466964097773600768/70916363469:ℝ),(638266936742367541067776/212749090407:ℝ),(635391351309615119728640/212749090407:ℝ),(210839815459540899463168/212749090407:ℝ)]]
theorem admission012_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (12272492485327/24206118730752:ℝ) admission012_03_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission012_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission012_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission012_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission012_03_coefficients]
def admission012_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(465714736683616290709504/2954848477875:ℝ),(18491333321319906729984/39397979705:ℝ),(1376580233403138461138944/2954848477875:ℝ),(455444970987761747099648/2954848477875:ℝ)],
![(4686862196115884779282432/14774242389375:ℝ),(664633924167050859782144/703535351875:ℝ),(13854283467785140214693888/14774242389375:ℝ),(1527944418797652312850432/4924747463125:ℝ)],
![(2358288512697803325734912/14774242389375:ℝ),(2341020804004367677227008/4924747463125:ℝ),(2323794100256482636333056/4924747463125:ℝ),(2306608401454148203053056/14774242389375:ℝ)]]
theorem admission012_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (20359976782847721/258198599794688000:ℝ) admission012_04_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission012_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission012_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission012_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission012_04_coefficients]
def admission012_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(121790357484487255728128/1266363633375:ℝ),(2558486939717413501100032/8864545433625:ℝ),(2559341114055470660599808/8864545433625:ℝ),(94820741858829772177408/984949492625:ℝ)],
![(1672219087232164080984064/8864545433625:ℝ),(25093241066723734769410048/44322727168125:ℝ),(25102842105552312998985728/44322727168125:ℝ),(22321857266638396358656/118193939115:ℝ)],
![(819686584840753290887168/8864545433625:ℝ),(12300806368136667263909888/44322727168125:ℝ),(12306136535274959695986688/44322727168125:ℝ),(273584206089470592434176/2954848477875:ℝ)]]
theorem admission012_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (50029698781784258477/1057581464759042048000:ℝ) admission012_05_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission012_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission012_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission012_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission012_05_coefficients]
def admission012_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(198168187423943972334659458242879488/861471446683753497298875:ℝ),(1057046911173374269892977776925024256/1550648604030756295137975:ℝ),(5220253083231571767868624182022504448/7753243020153781475689875:ℝ),(343706353443780999584254084316659712/1550648604030756295137975:ℝ)],
![(664399055311428934860992226247565312/1435785744472922495498125:ℝ),(10632386985479515323870200192344530944/7753243020153781475689875:ℝ),(52510803684045946732413723647343067136/38766215100768907378449375:ℝ),(3457527753205186694508622558860935168/7753243020153781475689875:ℝ)],
![(1002356228814566942909679387528298496/4307357233418767486494375:ℝ),(5347152429612643974405311307719409664/7753243020153781475689875:ℝ),(26409538267888087893070602737230544896/38766215100768907378449375:ℝ),(1738995985986281696587352137277636608/7753243020153781475689875:ℝ)]]
theorem admission012_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (5121623776015356176856966083/45165914183893175359183257600:ℝ) admission012_06_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission012_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission012_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission012_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission012_06_coefficients]
def admission012_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(103063098954135014021503874634407936/209547108652804904748375:ℝ),(307535017367538803260017522308079616/209547108652804904748375:ℝ),(101961340985653165227403630434320384/69849036217601634916125:ℝ),(101412104543555706443697243629289472/209547108652804904748375:ℝ)],
![(146113266441141687265946463530983424/149676506180574931963125:ℝ),(24415197596186154009512282789863424/8381884346112196189935:ℝ),(1011817842577921548839708219873951744/349245181088008174580625:ℝ),(40253867731939488247668582224232448/41909421730560980949675:ℝ)],
![(507477370317316740754105871544844288/1047735543264024523741875:ℝ),(302844922537115046977789547438505984/209547108652804904748375:ℝ),(502011137649655722702690067702349824/349245181088008174580625:ℝ),(99857234116141734794645667491872768/209547108652804904748375:ℝ)]]
theorem admission012_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (371997185484102870503983153/1525875479185580248621056000:ℝ) admission012_07_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission012_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission012_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission012_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission012_07_coefficients]
def admission012_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6253152353716908829030690345723479352738/1894776373090322127716064453125:ℝ),(2680422249330913571645822076128779920556034/255794810367193487241668701171875:ℝ),(314239118781132878754488298713392454241926/28421645596354831915740966796875:ℝ),(198380537026007988116013416727234344798186/51158962073438697448333740234375:ℝ)],
![(384799732340919167513906677123484088434384/47369409327258053192901611328125:ℝ),(32611670991183923853373099825144609278936392/1278974051835967436208343505859375:ℝ),(3783672423704541892594824751094345626690876/142108227981774159578704833984375:ℝ),(2366189296995974769484613846136193068551972/255794810367193487241668701171875:ℝ)],
![(32638703356856635255448488354342443516562/6767058475322579027557373046875:ℝ),(2744222820647050856449141349214387096593746/182710578833709633744049072265625:ℝ),(737492276599625832940794419175794451827082/47369409327258053192901611328125:ℝ),(1374286611865934828904546762500021344561042/255794810367193487241668701171875:ℝ)]]
theorem admission012_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (28139185591726089730638106555755657087321/16666629233984364528938254336000000000000000:ℝ) admission012_08_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission012_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission012_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission012_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission012_08_coefficients]
def admission012_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8106156037247955787151439088054291442656/409271696587509579586669921875:ℝ),(2653031009266815455544062041804647760256/45474632954167731065185546875:ℝ),(23437077272445469485953424392206529429504/409271696587509579586669921875:ℝ),(283924363975338923887130274383242723328/15158210984722577021728515625:ℝ)],
![(11091954706456581970342414042799185723936/292336926133935413990478515625:ℝ),(8465871917731053466344309465556997108864/75791054923612885108642578125:ℝ),(224235677943544228027087425897912621694976/2046358482937547897933349609375:ℝ),(325781578829267347539251190551640276992/9094926590833546213037109375:ℝ)],
![(37112902758956294856639702859322842854272/2046358482937547897933349609375:ℝ),(12132460706859083121312618187647752525312/227373164770838655325927734375:ℝ),(107050291581316880597320303936879974547456/2046358482937547897933349609375:ℝ),(777134802220319966034865129608473214976/45474632954167731065185546875:ℝ)]]
theorem admission012_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (555850125947227453733586165624957/63578144966065843692544000000000000:ℝ) admission012_09_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission012_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission012_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission012_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission012_09_coefficients]
def admission012_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(462672067168656359932632879176/86567826500244140625:ℝ),(1357981565802406678200215534728/86567826500244140625:ℝ),(189713803124119278924747936704/12366832357177734375:ℝ),(48076366968747468036739211264/9618647388916015625:ℝ)],
![(883546736730277064279760794432/86567826500244140625:ℝ),(2591162779724711987087218482496/86567826500244140625:ℝ),(2531782496258478075303279581696/86567826500244140625:ℝ),(91574090505249586388424654848/9618647388916015625:ℝ)],
![(140189822936644078927098250624/28855942166748046875:ℝ),(410756893378938580315062505856/28855942166748046875:ℝ),(80192026171740169841316051968/5771188433349609375:ℝ),(6209196238988099896124571648/1374092484130859375:ℝ)]]
theorem admission012_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (852703340925489792863787/368855142563840000000000000:ℝ) admission012_10_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission012_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission012_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission012_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission012_10_coefficients]
def admission012_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(140965073743664613612808788880646144/349245181088008174580625:ℝ),(1261912827206314806683262921241501696/1047735543264024523741875:ℝ),(1255155742475343893796766669525221376/1047735543264024523741875:ℝ),(138712712166674309317310038308552704/349245181088008174580625:ℝ)],
![(39961914242709491342744732071862272/49892168726858310654375:ℝ),(500821942138451276810217262372200448/209547108652804904748375:ℝ),(2490650196367308110612975686724354048/1047735543264024523741875:ℝ),(55049378984796736317301916558163968/69849036217601634916125:ℝ)],
![(27753665191060365157280867124477952/69849036217601634916125:ℝ),(1242196883485941577367823390619500544/1047735543264024523741875:ℝ),(1235494453891964216816209017199132672/1047735543264024523741875:ℝ),(136534182757309372269199544482267136/349245181088008174580625:ℝ)]]
theorem admission012_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (508629466434230552126465531/2543125798642633747701760000:ℝ) admission012_11_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission012_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission012_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission012_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission012_11_coefficients]
def admission012_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(176669076292854874112/10986328125:ℝ),(176669076292854874112/3662109375:ℝ),(176669076292854874112/3662109375:ℝ),(176669076292854874112/10986328125:ℝ)],
![(353338152585709748224/10986328125:ℝ),(353338152585709748224/3662109375:ℝ),(353338152585709748224/3662109375:ℝ),(353338152585709748224/10986328125:ℝ)],
![(176669076292854874112/10986328125:ℝ),(176669076292854874112/3662109375:ℝ),(176669076292854874112/3662109375:ℝ),(176669076292854874112/10986328125:ℝ)]]
theorem admission012_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (41133974747/5000000000000:ℝ) admission012_12_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission012_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission012_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission012_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission012_12_coefficients]
def admission012_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6217204408677518278656/762939453125:ℝ),(18651613226032554835968/762939453125:ℝ),(18651613226032554835968/762939453125:ℝ),(6217204408677518278656/762939453125:ℝ)],
![(12434408817355036557312/762939453125:ℝ),(37303226452065109671936/762939453125:ℝ),(37303226452065109671936/762939453125:ℝ),(12434408817355036557312/762939453125:ℝ)],
![(6217204408677518278656/762939453125:ℝ),(18651613226032554835968/762939453125:ℝ),(18651613226032554835968/762939453125:ℝ),(6217204408677518278656/762939453125:ℝ)]]
theorem admission012_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (208448021404809/50000000000000000:ℝ) admission012_13_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission012_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission012_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission012_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission012_13_coefficients]
def admission012_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8796093022208/9:ℝ),(8796093022208/3:ℝ),(8796093022208/3:ℝ),(8796093022208/9:ℝ)],
![(17592186044416/9:ℝ),(17592186044416/3:ℝ),(17592186044416/3:ℝ),(17592186044416/9:ℝ)],
![(8796093022208/9:ℝ),(8796093022208/3:ℝ),(8796093022208/3:ℝ),(8796093022208/9:ℝ)]]
theorem admission012_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission012_14_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission012_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission012_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission012_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission012_14_coefficients]
theorem admission012_all {δ p : ℝ}
 (hd : δ∈Set.Icc (465/1024:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission012_00_pos hd hp
 · exact admission012_01_pos hd hp
 · exact admission012_02_pos hd hp
 · exact admission012_03_pos hd hp
 · exact admission012_04_pos hd hp
 · exact admission012_05_pos hd hp
 · exact admission012_06_pos hd hp
 · exact admission012_07_pos hd hp
 · exact admission012_08_pos hd hp
 · exact admission012_09_pos hd hp
 · exact admission012_10_pos hd hp
 · exact admission012_11_pos hd hp
 · exact admission012_12_pos hd hp
 · exact admission012_13_pos hd hp
 · exact admission012_14_pos hd hp
end
end DasStageAFinite
#print axioms DasStageAFinite.admission012_all
