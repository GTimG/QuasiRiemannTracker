/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def admission011_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6215350407257051365376/3376969689:ℝ),(390338399179877606490112/70916363469:ℝ),(389109722702560976961536/70916363469:ℝ),(129293682075081449144320/70916363469:ℝ)],
![(12430700814514102730752/3376969689:ℝ),(780676798359755212980224/70916363469:ℝ),(778219445405121953923072/70916363469:ℝ),(258587364150162898288640/70916363469:ℝ)],
![(6215350407257051365376/3376969689:ℝ),(390338399179877606490112/70916363469:ℝ),(389109722702560976961536/70916363469:ℝ),(129293682075081449144320/70916363469:ℝ)]]
theorem admission011_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (29397979705/31518383764:ℝ) admission011_00_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission011_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission011_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission011_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission011_00_coefficients]
def admission011_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(13618006772173879902208/10130909067:ℝ),(285290947448291477946368/70916363469:ℝ),(284603752680931477946368/70916363469:ℝ),(31546284212619053105152/23638787823:ℝ)],
![(27236013544347759804416/10130909067:ℝ),(570581894896582955892736/70916363469:ℝ),(569207505361862955892736/70916363469:ℝ),(63092568425238106210304/23638787823:ℝ)],
![(13618006772173879902208/10130909067:ℝ),(285290947448291477946368/70916363469:ℝ),(284603752680931477946368/70916363469:ℝ),(31546284212619053105152/23638787823:ℝ)]]
theorem admission011_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (5379595941/7879595941:ℝ) admission011_01_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission011_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission011_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission011_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission011_01_coefficients]
def admission011_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4327923860701138600853504/6331818166875:ℝ),(18135937136304711037616128/8864545433625:ℝ),(90472970288323199758237696/44322727168125:ℝ),(30088751631707614776131584/44322727168125:ℝ)],
![(8655847721402277201707008/6331818166875:ℝ),(36271874272609422075232256/8864545433625:ℝ),(180945940576646399516475392/44322727168125:ℝ),(60177503263415229552263168/44322727168125:ℝ)],
![(4327923860701138600853504/6331818166875:ℝ),(18135937136304711037616128/8864545433625:ℝ),(90472970288323199758237696/44322727168125:ℝ),(30088751631707614776131584/44322727168125:ℝ)]]
theorem admission011_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218924481535997/630367675280000:ℝ) admission011_02_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission011_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission011_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission011_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission011_02_coefficients]
def admission011_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(71959781880135308804096/70916363469:ℝ),(644756303996208189276160/212749090407:ℝ),(641878204387038599315456/212749090407:ℝ),(213001246031236336451584/212749090407:ℝ)],
![(143438826826046547951616/70916363469:ℝ),(1285187209079648335953920/212749090407:ℝ),(1279432266949517740343296/212749090407:ℝ),(424561538348009048244224/212749090407:ℝ)],
![(71479044945911239147520/70916363469:ℝ),(640430905083440146677760/212749090407:ℝ),(637554062562479141027840/212749090407:ℝ),(211560292316772711792640/212749090407:ℝ)]]
theorem admission011_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (49257719031715/96824474923008:ℝ) admission011_03_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission011_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission011_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission011_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission011_03_coefficients]
def admission011_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(330507232485147045019648/2110606055625:ℝ),(13122881711904449937408/28141414075:ℝ),(976927907576420843388928/2110606055625:ℝ),(323219011668734143102976/2110606055625:ℝ)],
![(4656816084071780502462464/14774242389375:ℝ),(4622612738005936814071808/4924747463125:ℝ),(917698122654909827383296/984949492625:ℝ),(910889941975523494199296/2954848477875:ℝ)],
![(2343265456675751187324928/14774242389375:ℝ),(2326108438422658075025408/4924747463125:ℝ),(6926976486788701507026944/14774242389375:ℝ),(763972209398826156425216/4924747463125:ℝ)]]
theorem admission011_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (7224507890687901/92213785640960000:ℝ) admission011_04_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission011_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission011_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission011_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission011_04_coefficients]
def admission011_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(173791092233347907940352/1772909086725:ℝ),(13037718647407536503017472/44322727168125:ℝ),(13040930223649815665938432/44322727168125:ℝ),(289865925471731790761984/2954848477875:ℝ)],
![(243580714968974511456256/1266363633375:ℝ),(25583808964364672764444672/44322727168125:ℝ),(25591291412297237724864512/44322727168125:ℝ),(113770766291288971485184/590969695575:ℝ)],
![(836109543616082040492032/8864545433625:ℝ),(501843612678285450457088/1772909086725:ℝ),(2510072237729484411785216/8864545433625:ℝ),(92995968661571022221312/984949492625:ℝ)]]
theorem admission011_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (204128306546895029417/4230325859036168192000:ℝ) admission011_05_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission011_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission011_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission011_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission011_05_coefficients]
def admission011_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(985010150638032974510826782593368064/4307357233418767486494375:ℝ),(5254013010272163772523589035072339968/7753243020153781475689875:ℝ),(25946474205182955025611251950702034944/38766215100768907378449375:ℝ),(1708299657835216648588229563736129536/7753243020153781475689875:ℝ)],
![(660511864323637676752678553833545728/1435785744472922495498125:ℝ),(2113988778858020033997520098647793664/1550648604030756295137975:ℝ),(52201221262096139104949985728522092544/38766215100768907378449375:ℝ),(687412706887561999168508168633319424/1550648604030756295137975:ℝ)],
![(28472155495225144449920253683064832/123067349526250499614125:ℝ),(5315930884017936397464011458166628352/7753243020153781475689875:ℝ),(1050189882276527363173549351112802304/1550648604030756295137975:ℝ),(1728763876602593347254311279430467584/7753243020153781475689875:ℝ)]]
theorem admission011_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (12727824284398679797263663737/112914785459732938397958144000:ℝ) admission011_06_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission011_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission011_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission011_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission011_06_coefficients]
def admission011_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(519266443155498470338303934455693312/1047735543264024523741875:ℝ),(44270400936691657438381161853075456/29935301236114986392625:ℝ),(513715096138341000448717296297312256/349245181088008174580625:ℝ),(14598505679608956038317575956856832/29935301236114986392625:ℝ)],
![(1030694761857638611323194367284191232/1047735543264024523741875:ℝ),(615095518283259447855108291073482752/209547108652804904748375:ℝ),(145662089285438842494729501160767488/49892168726858310654375:ℝ),(202824209087111412887394487258578944/209547108652804904748375:ℝ)],
![(102285663740428028196978086565699584/209547108652804904748375:ℝ),(61040542345283569157288031620390912/41909421730560980949675:ℝ),(101183905771946179402877842365612032/69849036217601634916125:ℝ),(20126933865969744123834291112116224/41909421730560980949675:ℝ)]]
theorem admission011_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (299914685874726535735045241/1220700383348464198896844800:ℝ) admission011_07_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission011_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission011_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission011_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission011_07_coefficients]
def admission011_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(120257751515385857694581178724431923419708/47369409327258053192901611328125:ℝ),(300469096923150446481151536862804269191492/36542115766741926748809814453125:ℝ),(1254553873960283056003174448874436730526692/142108227981774159578704833984375:ℝ),(574501762830602937588565883095042449695732/182710578833709633744049072265625:ℝ)],
![(12506304707433817658061380691446958705476/1894776373090322127716064453125:ℝ),(26840285282495319390595486644253108916780492/1278974051835967436208343505859375:ℝ),(336041491606803116486004337248991418168/15158210984722577021728515625:ℝ),(9954944313307915567862320757649842398590808/1278974051835967436208343505859375:ℝ)],
![(192399866170459583756953338561742044217192/47369409327258053192901611328125:ℝ),(16323866890185053763755182854054959495078272/1278974051835967436208343505859375:ℝ),(1895835109853496161053116212834857814798308/142108227981774159578704833984375:ℝ),(5933431973493695004742359575984545250720684/1278974051835967436208343505859375:ℝ)]]
theorem admission011_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (270579940909618179812807652129971827694343/208332865424804556611728179200000000000000000:ℝ) admission011_08_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission011_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission011_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission011_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission011_08_coefficients]
def admission011_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(42269296095145084888277859916541835084608/2046358482937547897933349609375:ℝ),(4612687404338781797309686509613104304896/75791054923612885108642578125:ℝ),(122282396588003279882423455671150610284544/2046358482937547897933349609375:ℝ),(889092236778865174474653669920355647488/45474632954167731065185546875:ℝ)],
![(81120714763006685697438227252135055810208/2046358482937547897933349609375:ℝ),(26543430086557696627450427036303139553408/227373164770838655325927734375:ℝ),(234429698395096092932400093318148547969024/2046358482937547897933349609375:ℝ),(567848727950677847774260548766485446656/15158210984722577021728515625:ℝ)],
![(222008106673494861766630670489104118432/11693477045357416559619140625:ℝ),(2541073574708270247104273501492765327744/45474632954167731065185546875:ℝ),(22429460361418562609995327529399587536896/409271696587509579586669921875:ℝ),(162890789414633673769625595275820138496/9094926590833546213037109375:ℝ)]]
theorem admission011_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (466034286731625577267529283359013/50862515972852674954035200000000000:ℝ) admission011_09_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission011_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission011_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission011_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission011_09_coefficients]
def admission011_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(483410294192765088514902235936/86567826500244140625:ℝ),(283921894880660620251881072032/17313565300048828125:ℝ),(1389039978040770828593916512512/86567826500244140625:ℝ),(50315663889492014261045932032/9618647388916015625:ℝ)],
![(8815558021732109110247293664/824455490478515625:ℝ),(181082644299832264605948599584/5771188433349609375:ℝ),(177045344815295398531016532224/5771188433349609375:ℝ),(19223876814781903398932996096/1923729477783203125:ℝ)],
![(17676723893496716019809217416/3462713060009765625:ℝ),(51828786252347651995520328136/3462713060009765625:ℝ),(50629388495004782966441129024/3462713060009765625:ℝ),(1830814812833283346192224256/384745895556640625:ℝ)]]
theorem admission011_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (4022786453979382352473149/1652471038686003200000000000:ℝ) admission011_10_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission011_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission011_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission011_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission011_10_coefficients]
def admission011_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(142072556827344932915157995225759744/349245181088008174580625:ℝ),(25955620175194812638412351625412608/21382358025796418851875:ℝ),(1265013648716581354060827099633025024/1047735543264024523741875:ℝ),(19971710981622396834480755031670784/49892168726858310654375:ℝ)],
![(281948365866327078003911537193263104/349245181088008174580625:ℝ),(2523934833448718409248970928668434432/1047735543264024523741875:ℝ),(358623715549969004448728078134280192/149676506180574931963125:ℝ),(277425424333348618634620076617105408/349245181088008174580625:ℝ)],
![(27975161807796429017750708393500672/69849036217601634916125:ℝ),(250421888972834517993353139804643328/209547108652804904748375:ℝ),(249070472026640335416053889461387264/209547108652804904748375:ℝ),(27524689492398368158650958279081984/69849036217601634916125:ℝ)]]
theorem admission011_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (410149834936832907179757331/2034500638914106998161408000:ℝ) admission011_11_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission011_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission011_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission011_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission011_11_coefficients]
def admission011_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(176669076292854874112/10986328125:ℝ),(176669076292854874112/3662109375:ℝ),(176669076292854874112/3662109375:ℝ),(176669076292854874112/10986328125:ℝ)],
![(353338152585709748224/10986328125:ℝ),(353338152585709748224/3662109375:ℝ),(353338152585709748224/3662109375:ℝ),(353338152585709748224/10986328125:ℝ)],
![(176669076292854874112/10986328125:ℝ),(176669076292854874112/3662109375:ℝ),(176669076292854874112/3662109375:ℝ),(176669076292854874112/10986328125:ℝ)]]
theorem admission011_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (41133974747/5000000000000:ℝ) admission011_12_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission011_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission011_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission011_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission011_12_coefficients]
def admission011_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6217204408677518278656/762939453125:ℝ),(18651613226032554835968/762939453125:ℝ),(18651613226032554835968/762939453125:ℝ),(6217204408677518278656/762939453125:ℝ)],
![(12434408817355036557312/762939453125:ℝ),(37303226452065109671936/762939453125:ℝ),(37303226452065109671936/762939453125:ℝ),(12434408817355036557312/762939453125:ℝ)],
![(6217204408677518278656/762939453125:ℝ),(18651613226032554835968/762939453125:ℝ),(18651613226032554835968/762939453125:ℝ),(6217204408677518278656/762939453125:ℝ)]]
theorem admission011_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (208448021404809/50000000000000000:ℝ) admission011_13_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission011_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission011_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission011_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission011_13_coefficients]
def admission011_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8796093022208/9:ℝ),(8796093022208/3:ℝ),(8796093022208/3:ℝ),(8796093022208/9:ℝ)],
![(17592186044416/9:ℝ),(17592186044416/3:ℝ),(17592186044416/3:ℝ),(17592186044416/9:ℝ)],
![(8796093022208/9:ℝ),(8796093022208/3:ℝ),(8796093022208/3:ℝ),(8796093022208/9:ℝ)]]
theorem admission011_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission011_14_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission011_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission011_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission011_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission011_14_coefficients]
theorem admission011_all {δ p : ℝ}
 (hd : δ∈Set.Icc (231/512:ℝ) (465/1024:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission011_00_pos hd hp
 · exact admission011_01_pos hd hp
 · exact admission011_02_pos hd hp
 · exact admission011_03_pos hd hp
 · exact admission011_04_pos hd hp
 · exact admission011_05_pos hd hp
 · exact admission011_06_pos hd hp
 · exact admission011_07_pos hd hp
 · exact admission011_08_pos hd hp
 · exact admission011_09_pos hd hp
 · exact admission011_10_pos hd hp
 · exact admission011_11_pos hd hp
 · exact admission011_12_pos hd hp
 · exact admission011_13_pos hd hp
 · exact admission011_14_pos hd hp
end
end DasStageAFinite
#print axioms DasStageAFinite.admission011_all
