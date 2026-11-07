/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def admission026_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(14745696847008495675899904/7879595941:ℝ),(397819273691036326089981952/70916363469:ℝ),(397504732512843268930666496/70916363469:ℝ),(132396730444883403923783680/70916363469:ℝ)],
![(29491393694016991351799808/7879595941:ℝ),(795638547382072652179963904/70916363469:ℝ),(795009465025686537861332992/70916363469:ℝ),(264793460889766807847567360/70916363469:ℝ)],
![(14745696847008495675899904/7879595941:ℝ),(397819273691036326089981952/70916363469:ℝ),(397504732512843268930666496/70916363469:ℝ),(132396730444883403923783680/70916363469:ℝ)]]
theorem admission026_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (29397979705/31518383764:ℝ) admission026_00_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission026_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission026_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (1875/4096:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission026_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission026_00_coefficients]
def admission026_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(97086106961609891139026944/70916363469:ℝ),(291082399024385513417080832/70916363469:ℝ),(290906477163941353417080832/70916363469:ℝ),(32303395033721910379675648/23638787823:ℝ)],
![(194172213923219782278053888/70916363469:ℝ),(582164798048771026834161664/70916363469:ℝ),(581812954327882706834161664/70916363469:ℝ),(64606790067443820759351296/23638787823:ℝ)],
![(97086106961609891139026944/70916363469:ℝ),(291082399024385513417080832/70916363469:ℝ),(290906477163941353417080832/70916363469:ℝ),(32303395033721910379675648/23638787823:ℝ)]]
theorem admission026_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (5379595941/7879595941:ℝ) admission026_01_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission026_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission026_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (1875/4096:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission026_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission026_01_coefficients]
def admission026_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6172760162305577704159707136/8864545433625:ℝ),(92538483293924374572355813376/44322727168125:ℝ),(92485564153265083582316019712/44322727168125:ℝ),(30810881670868597530758742016/44322727168125:ℝ)],
![(12345520324611155408319414272/8864545433625:ℝ),(185076966587848749144711626752/44322727168125:ℝ),(184971128306530167164632039424/44322727168125:ℝ),(61621763341737195061517484032/44322727168125:ℝ)],
![(6172760162305577704159707136/8864545433625:ℝ),(92538483293924374572355813376/44322727168125:ℝ),(92485564153265083582316019712/44322727168125:ℝ),(30810881670868597530758742016/44322727168125:ℝ)]]
theorem admission026_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218924481535997/630367675280000:ℝ) admission026_02_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission026_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission026_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (1875/4096:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission026_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission026_02_coefficients]
def admission026_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(24091095146718658318827520/23638787823:ℝ),(92817698599263490677932032/30392727201:ℝ),(648988446980397734882705408/212749090407:ℝ),(216084413106021225006628864/212749090407:ℝ)],
![(48141194100436192492257280/23638787823:ℝ),(185477280626754083851599872/30392727201:ℝ),(1296870159544492616631451648/212749090407:ℝ),(431799942061139762100568064/212749090407:ℝ)],
![(8016699651239178057809920/7879595941:ℝ),(92659582027490593173667840/30392727201:ℝ),(647881712564094881748746240/212749090407:ℝ),(215715528955118537093939200/212749090407:ℝ)]]
theorem admission026_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (196192130674825/387297899692032:ℝ) admission026_03_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission026_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission026_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (1875/4096:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission026_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission026_03_coefficients]
def admission026_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(786709705634310837986394112/4924747463125:ℝ),(471144865875300884252983296/984949492625:ℝ),(2351322166166591567457943552/4924747463125:ℝ),(782307542424397984179421184/4924747463125:ℝ)],
![(1575933861986664478572412928/4924747463125:ℝ),(4718984951952767974539132928/4924747463125:ℝ),(22608833139764200474673152/23638787823:ℝ),(7522187907926903694032896/23638787823:ℝ)],
![(789224156352353640586018816/4924747463125:ℝ),(2363260622576263553274216448/4924747463125:ℝ),(7076554213852850594296889344/14774242389375:ℝ),(2354444815181120856232296448/14774242389375:ℝ)]]
theorem admission026_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (25614164339711649/322748249743360000:ℝ) admission026_04_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission026_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission026_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (1875/4096:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission026_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission026_04_coefficients]
def admission026_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(602825542751951088017932288/6331818166875:ℝ),(12660678209744830051016966144/44322727168125:ℝ),(12662008666281914423671717888/44322727168125:ℝ),(281407283720049465918685184/2954848477875:ℝ)],
![(1199674037625977253782355968/6331818166875:ℝ),(25195906172566342579739951104/44322727168125:ℝ),(25198634825955833880287510528/44322727168125:ℝ),(112005958890284427693654016/590969695575:ℝ)],
![(119369698974805233152884736/1266363633375:ℝ),(2507045592564302505744596992/8864545433625:ℝ),(2507325231934783891323158528/8864545433625:ℝ),(92874170243790890849861632/984949492625:ℝ)]]
theorem admission026_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (1821437057110675554701/38677264996902109184000:ℝ) admission026_05_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission026_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission026_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (1875/4096:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission026_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission026_05_coefficients]
def admission026_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2978157440106033655427315588053373812736/12922071700256302459483125:ℝ),(26720111591133092635508025959113004417024/38766215100768907378449375:ℝ),(26636910355007862599556863345636877008896/38766215100768907378449375:ℝ),(1770254209641055587588414750136798806016/7753243020153781475689875:ℝ)],
![(5965074254786211482732900700474797326336/12922071700256302459483125:ℝ),(53518973518469482739287860473376652263424/38766215100768907378449375:ℝ),(53352487122576504750710600869409001046016/38766215100768907378449375:ℝ),(709149451857311922007069283898269630464/1550648604030756295137975:ℝ)],
![(119476672587207113092223404496856940544/516882868010252098379325:ℝ),(1071954477093455604151193380570545913856/1550648604030756295137975:ℝ),(5343115353513728430230747504754424807424/7753243020153781475689875:ℝ),(253641864235072003206704524193507049472/1107606145736254496527125:ℝ)]]
theorem admission026_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (6440147297839050543510583339/56457392729866469198979072000:ℝ) admission026_06_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission026_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission026_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (1875/4096:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission026_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission026_06_coefficients]
def admission026_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(514357973563047040346124945087765938176/1047735543264024523741875:ℝ),(1540979059768379621778309206487049699328/1047735543264024523741875:ℝ),(512961747317841068478721029228539674624/349245181088008174580625:ℝ),(102452831149638124800795765257267052544/209547108652804904748375:ℝ)],
![(1026721637641561786136507273439964430336/1047735543264024523741875:ℝ),(3075979268450871454503002282200568823808/1047735543264024523741875:ℝ),(146275986102790525364936506851303882752/49892168726858310654375:ℝ),(204507615469858272859434327023355428864/209547108652804904748375:ℝ)],
![(102472732815702949158076465670439698432/209547108652804904748375:ℝ),(307000041736498366544938615142703824896/209547108652804904748375:ℝ),(102194031080338521815166903746117500928/69849036217601634916125:ℝ),(20410956864044029611727712353217675264/41909421730560980949675:ℝ)]]
theorem admission026_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (1188074056061684946280887371/4882801533393856795587379200:ℝ) admission026_07_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission026_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission026_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (1875/4096:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission026_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission026_07_coefficients]
def admission026_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7604602902467643132185735100570863588583424/1740100750797234607086181640625:ℝ),(2421136484954672197537592784942331326547950592/182710578833709633744049072265625:ℝ),(634359840936237482506505308647288507903076352/47369409327258053192901611328125:ℝ),(46153145810631968035686218336356747801249792/10231792414687739489666748046875:ℝ)],
![(15878244133131245047758021085683722334089984/1740100750797234607086181640625:ℝ),(5052692319270382351037280406374580932869634752/182710578833709633744049072265625:ℝ),(3969563901270076898026061622013629875394277376/142108227981774159578704833984375:ℝ),(2405547575775987493195377714606982892928438272/255794810367193487241668701171875:ℝ)],
![(1654728246132720383114457197022571749101312/348020150159446921417236328125:ℝ),(526311166863142030699937524286449921264336832/36542115766741926748809814453125:ℝ),(413296875692272890101309139214352870337009664/28421645596354831915740966796875:ℝ),(1251718930510188292303222256198064197897193472/255794810367193487241668701171875:ℝ)]]
theorem admission026_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (3713185010970528873137565967075616986613/1700676452447384135605944320000000000000000:ℝ) admission026_08_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission026_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission026_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (1875/4096:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission026_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission026_08_coefficients]
def admission026_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7357537712216777834450795236822011750283264/409271696587509579586669921875:ℝ),(36605120400381011795781513750198259499958272/682119494312515965977783203125:ℝ),(2229958379288455843115003641429401266028544/41762418019133630570068359375:ℝ),(805339738555936836339897181492357206376448/45474632954167731065185546875:ℝ)],
![(14542353824742576351597290268021555046530176/409271696587509579586669921875:ℝ),(72347892322185173632957273612450278027016192/682119494312515965977783203125:ℝ),(30850378662159820220879173504278032084369408/292336926133935413990478515625:ℝ),(1591572074947215290439403785438153144270848/45474632954167731065185546875:ℝ)],
![(7184816112525798517146495031199543296246912/409271696587509579586669921875:ℝ),(7148554384360832367435151972450403705411584/136423898862503193195556640625:ℝ),(609626800285625172762965920570888928886784/11693477045357416559619140625:ℝ),(10483097818550379387993421385943945838592/606328439388903080869140625:ℝ)]]
theorem admission026_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (351473243411456847533363075828163/40690012778282139963228160000000000:ℝ) admission026_09_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission026_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission026_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (1875/4096:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission026_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission026_09_coefficients]
def admission026_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(27562893706609667604900340883456/5771188433349609375:ℝ),(410937484626753413355525658271744/28855942166748046875:ℝ),(408432584407387691860442203291648/28855942166748046875:ℝ),(45103189761106705509806083145728/9618647388916015625:ℝ)],
![(163229133563531409971279419526144/17313565300048828125:ℝ),(486687957315858169526307494038528/17313565300048828125:ℝ),(483689731599022232532422729498624/17313565300048828125:ℝ),(3560686866936114677275436777472/384745895556640625:ℝ)],
![(128858551060233842111506018976/27701704480078125:ℝ),(384182253738546767405932572832/27701704480078125:ℝ),(54541403229290273588629941248/3957386354296875:ℝ),(2810358241345708454466289664/615593432890625:ℝ)]]
theorem admission026_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (96485993088193420754229/42303258590361681920000000:ℝ) admission026_10_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission026_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission026_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (1875/4096:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission026_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission026_10_coefficients]
def admission026_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(46886931951143512540032674290510856192/116415060362669391526875:ℝ),(1264233340131094713531918687088068788224/1047735543264024523741875:ℝ),(50500820691778145124363201950091575296/41909421730560980949675:ℝ),(140089854907883509145818476759606099968/349245181088008174580625:ℝ)],
![(93587574767204720615555348215464067072/116415060362669391526875:ℝ),(2523440367344122047990305607064014946304/1047735543264024523741875:ℝ),(72000520380005381304921984983539646464/29935301236114986392625:ℝ),(279622006286969594407320667099683094528/349245181088008174580625:ℝ)],
![(9340128563212241615104534784990642176/23283012072533878305375:ℝ),(251841405442605466891677383995189231616/209547108652804904748375:ℝ),(251499539201146943512637885134319648768/209547108652804904748375:ℝ),(27906430275817217052300438068015398912/69849036217601634916125:ℝ)]]
theorem admission026_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (1624368030800089301326104793/8138002555656427992645632000:ℝ) admission026_11_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission026_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission026_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (1875/4096:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission026_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission026_11_coefficients]
def admission026_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(180909134123883391090688/10986328125:ℝ),(180909134123883391090688/3662109375:ℝ),(180909134123883391090688/3662109375:ℝ),(180909134123883391090688/10986328125:ℝ)],
![(361818268247766782181376/10986328125:ℝ),(361818268247766782181376/3662109375:ℝ),(361818268247766782181376/3662109375:ℝ),(361818268247766782181376/10986328125:ℝ)],
![(180909134123883391090688/10986328125:ℝ),(180909134123883391090688/3662109375:ℝ),(180909134123883391090688/3662109375:ℝ),(180909134123883391090688/10986328125:ℝ)]]
theorem admission026_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (41133974747/5000000000000:ℝ) admission026_12_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission026_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission026_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (1875/4096:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission026_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission026_12_coefficients]
def admission026_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6366417314485778717343744/762939453125:ℝ),(19099251943457336152031232/762939453125:ℝ),(19099251943457336152031232/762939453125:ℝ),(6366417314485778717343744/762939453125:ℝ)],
![(12732834628971557434687488/762939453125:ℝ),(38198503886914672304062464/762939453125:ℝ),(38198503886914672304062464/762939453125:ℝ),(12732834628971557434687488/762939453125:ℝ)],
![(6366417314485778717343744/762939453125:ℝ),(19099251943457336152031232/762939453125:ℝ),(19099251943457336152031232/762939453125:ℝ),(6366417314485778717343744/762939453125:ℝ)]]
theorem admission026_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (208448021404809/50000000000000000:ℝ) admission026_13_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission026_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission026_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (1875/4096:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission026_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission026_13_coefficients]
def admission026_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(9007199254740992/9:ℝ),(9007199254740992/3:ℝ),(9007199254740992/3:ℝ),(9007199254740992/9:ℝ)],
![(18014398509481984/9:ℝ),(18014398509481984/3:ℝ),(18014398509481984/3:ℝ),(18014398509481984/9:ℝ)],
![(9007199254740992/9:ℝ),(9007199254740992/3:ℝ),(9007199254740992/3:ℝ),(9007199254740992/9:ℝ)]]
theorem admission026_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission026_14_coefficients (117/256:ℝ) (1875/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission026_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission026_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (1875/4096:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission026_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission026_14_coefficients]
theorem admission026_all {δ p : ℝ}
 (hd : δ∈Set.Icc (117/256:ℝ) (1875/4096:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission026_00_pos hd hp
 · exact admission026_01_pos hd hp
 · exact admission026_02_pos hd hp
 · exact admission026_03_pos hd hp
 · exact admission026_04_pos hd hp
 · exact admission026_05_pos hd hp
 · exact admission026_06_pos hd hp
 · exact admission026_07_pos hd hp
 · exact admission026_08_pos hd hp
 · exact admission026_09_pos hd hp
 · exact admission026_10_pos hd hp
 · exact admission026_11_pos hd hp
 · exact admission026_12_pos hd hp
 · exact admission026_13_pos hd hp
 · exact admission026_14_pos hd hp
end
end DasStageAFinite
#print axioms DasStageAFinite.admission026_all
