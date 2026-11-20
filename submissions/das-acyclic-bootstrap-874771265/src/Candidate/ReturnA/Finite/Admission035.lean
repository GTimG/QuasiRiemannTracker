/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def admission035_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(45218258172392676083579748352/23638787823:ℝ),(406883801009916662119432978432/70916363469:ℝ),(406803278468299239486648221696/70916363469:ℝ),(135574251975560605617954488320/70916363469:ℝ)],
![(90436516344785352167159496704/23638787823:ℝ),(813767602019833324238865956864/70916363469:ℝ),(813606556936598478973296443392/70916363469:ℝ),(271148503951121211235908976640/70916363469:ℝ)],
![(45218258172392676083579748352/23638787823:ℝ),(406883801009916662119432978432/70916363469:ℝ),(406803278468299239486648221696/70916363469:ℝ),(135574251975560605617954488320/70916363469:ℝ)]]
theorem admission035_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (29397979705/31518383764:ℝ) admission035_00_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission035_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission035_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (7509/16384:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission035_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission035_00_coefficients]
def admission035_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(99281065539867413646363590656/70916363469:ℝ),(297798160623328535979090771968/70916363469:ℝ),(297753124627054831019090771968/70916363469:ℝ),(33078676514531236228787863552/23638787823:ℝ)],
![(198562131079734827292727181312/70916363469:ℝ),(595596321246657071958181543936/70916363469:ℝ),(595506249254109662038181543936/70916363469:ℝ),(66157353029062472457575727104/23638787823:ℝ)],
![(99281065539867413646363590656/70916363469:ℝ),(297798160623328535979090771968/70916363469:ℝ),(297753124627054831019090771968/70916363469:ℝ),(33078676514531236228787863552/23638787823:ℝ)]]
theorem admission035_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (5379595941/7879595941:ℝ) admission035_01_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission035_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission035_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (7509/16384:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission035_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission035_01_coefficients]
def admission035_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(31563890130978222364947139002368/44322727168125:ℝ),(18935624618585177720278245965824/8864545433625:ℝ),(94664575792917110107941042651136/44322727168125:ℝ),(31550342830969443871496951824384/44322727168125:ℝ)],
![(63127780261956444729894278004736/44322727168125:ℝ),(37871249237170355440556491931648/8864545433625:ℝ),(189329151585834220215882085302272/44322727168125:ℝ),(63100685661938887742993903648768/44322727168125:ℝ)],
![(31563890130978222364947139002368/44322727168125:ℝ),(18935624618585177720278245965824/8864545433625:ℝ),(94664575792917110107941042651136/44322727168125:ℝ),(31550342830969443871496951824384/44322727168125:ℝ)]]
theorem admission035_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218924481535997/630367675280000:ℝ) admission035_02_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission035_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission035_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (7509/16384:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission035_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission035_02_coefficients]
def admission035_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(73662152955630380278022668288/70916363469:ℝ),(662771169923578782266681196544/212749090407:ℝ),(662582978364097935311158378496/212749090407:ℝ),(31542609615344327696935026688/30392727201:ℝ)],
![(147292826050506974933716828160/70916363469:ℝ),(1325259026333963964933742788608/212749090407:ℝ),(189268949779233219969147731968/30392727201:ℝ),(441502100272189499651441819648/212749090407:ℝ)],
![(10518667584982370665099165696/10130909067:ℝ),(662487856410385182667061592064/212749090407:ℝ),(662299670090534604472875745280/212749090407:ℝ),(220703832964779205772896632832/212749090407:ℝ)]]
theorem admission035_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (98012190792209/193648949846016:ℝ) admission035_03_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission035_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission035_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (7509/16384:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission035_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission035_03_coefficients]
def admission035_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(344768211110738736636573515776/2110606055625:ℝ),(482449540064115399463276642304/984949492625:ℝ),(7233354273879812948602170376192/14774242389375:ℝ),(2409988650693253113109035352064/14774242389375:ℝ)],
![(4828681989560916993003745181696/14774242389375:ℝ),(689488854754627149059770548224/703535351875:ℝ),(4824162313925729550271726485504/4924747463125:ℝ),(4821902981490935513563743125504/14774242389375:ℝ)],
![(2415304511785745836547730571264/14774242389375:ℝ),(2414174282961813046102010626048/4924747463125:ℝ),(1447826533579475140442601816064/2954848477875:ℝ),(160794288719845493363647184896/984949492625:ℝ)]]
theorem admission035_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (1643903931853801473/20655887983575040000:ℝ) admission035_04_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission035_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission035_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (7509/16384:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission035_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission035_04_coefficients]
def admission035_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(853610029586427054369252835328/8864545433625:ℝ),(12804519930761513540533568405504/44322727168125:ℝ),(12804888688941796075952599465984/44322727168125:ℝ),(284561260407494520484353015808/2954848477875:ℝ)],
![(1705080486616212922305989312512/8864545433625:ℝ),(25576950607971260862841294422016/44322727168125:ℝ),(25577692458838512979304593227776/44322727168125:ℝ),(189469872976629260622072119296/984949492625:ℝ)],
![(851470457029785867936736477184/8864545433625:ℝ),(1824632953887106760329675145216/6331818166875:ℝ),(12772803769896716903351993761792/44322727168125:ℝ),(56769671704478652276372668416/590969695575:ℝ)]]
theorem admission035_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (101503188255999787799923/2165926839826518114304000:ℝ) admission035_05_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission035_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission035_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (7509/16384:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission035_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission035_05_coefficients]
def admission035_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(82058456406421603476271329589625305956352/349245181088008174580625:ℝ),(5460828441511468797869620611491862742564864/7753243020153781475689875:ℝ),(27282825103604095915869728267006837058961408/38766215100768907378449375:ℝ),(1817434311316426719323767863759186461458432/7753243020153781475689875:ℝ)],
![(867794685867119785242624891078166496411648/1846010242893757494211875:ℝ),(10925682458101876838887250303682472520450048/7753243020153781475689875:ℝ),(54585772716824893215434185208761451483758592/38766215100768907378449375:ℝ),(519458537953427462567330865548302437318656/1107606145736254496527125:ℝ)],
![(3038399914032239168076335042731029154496512/12922071700256302459483125:ℝ),(5464854016590408041017629692190609777885184/7753243020153781475689875:ℝ),(27302947613220797299564456941754614424797184/38766215100768907378449375:ℝ),(363755090871513103729509639015786119954432/1550648604030756295137975:ℝ)]]
theorem admission035_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (413236719240655183812979854283/3613273134711454028734660608000:ℝ) admission035_06_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission035_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission035_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (7509/16384:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission035_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission035_06_coefficients]
def admission035_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(522544987793137020181344640165946331234304/1047735543264024523741875:ℝ),(313420180966551626293660004184871973945344/209547108652804904748375:ℝ),(522188970939164419705741198844025773228032/349245181088008174580625:ℝ),(104402199155574429566053643154732756238336/209547108652804904748375:ℝ)],
![(1044580214920475516659546283276652706267136/1047735543264024523741875:ℝ),(626534557684949694448130261838397416931328/209547108652804904748375:ℝ),(1043868355039454080337226745664651078402048/349245181088008174580625:ℝ),(208702498322817857086115042215723771363328/209547108652804904748375:ℝ)],
![(10653780145455887683228604961442987245568/21382358025796418851875:ℝ),(6390089320783634043968780768439294754816/4276471605159283770375:ℝ),(10646518042863054298601745853482149085184/7127452675265472950625:ℝ),(2128577534025376071837987735938592145408/4276471605159283770375:ℝ)]]
theorem admission035_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (60497812172155138109644319/249122527213972285489152000:ℝ) admission035_07_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission035_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission035_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (7509/16384:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission035_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission035_07_coefficients]
def admission035_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(296743907856852917445332821718058102484447806592/60903526277903211248016357421875:ℝ),(3747970542304514314895305476506243422598022280832/255794810367193487241668701171875:ℝ),(2087204059232184912691361497875225644775122804864/142108227981774159578704833984375:ℝ),(6276605883069953828267276865258842043376897778048/1278974051835967436208343505859375:ℝ)],
![(4196230085094158399385908218117457565806977746944/426324683945322478736114501953125:ℝ),(37855897201585351168049507391366091946876437943552/1278974051835967436208343505859375:ℝ),(200770996214492574420258775063394827402752457984/6767058475322579027557373046875:ℝ),(12678511331252725693540719231687790330422209856256/1278974051835967436208343505859375:ℝ)],
![(84760909203847519090743138643642033936633724032/17052987357812899149444580078125:ℝ),(19116044490062779593572980008834874833886326539392/1278974051835967436208343505859375:ℝ),(85159474450886366005362911138242629227307152512/5684329119270966383148193359375:ℝ),(6401905448182771865273442366428948287045312078208/1278974051835967436208343505859375:ℝ)]]
theorem admission035_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (2318311780131663417541662669672328925659748489/975235904891427958721872710860800000000000000000:ℝ) admission035_08_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission035_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission035_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (7509/16384:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission035_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission035_08_coefficients]
def admission035_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(36147854905235129489887660083906703627390055936/2046358482937547897933349609375:ℝ),(36101719838102095752186076655100303352754372608/682119494312515965977783203125:ℝ),(108166773392392322671070444021287718395133820928/2046358482937547897933349609375:ℝ),(114315773930073798734907824941225050810351616/6496376136309675866455078125:ℝ)],
![(72075351119462035538382947692973741864564606464/2046358482937547897933349609375:ℝ),(71983161477395177793585013750927426646811901952/682119494312515965977783203125:ℝ),(215672953606427104485406531163439922344479424512/2046358482937547897933349609375:ℝ),(531843113355626878811723187108410342204506112/15158210984722577021728515625:ℝ)],
![(35927496214226906048495287609067038237174550528/2046358482937547897933349609375:ℝ),(35881441639293082041398937095827123294057529344/682119494312515965977783203125:ℝ),(107506180214034781814336087142152203949345603584/2046358482937547897933349609375:ℝ),(795318922556364045290814786736655670941057024/45474632954167731065185546875:ℝ)]]
theorem admission035_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (4340030077708601558465387570704419/508625159728526749540352000000000000:ℝ) admission035_09_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission035_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission035_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (7509/16384:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission035_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission035_09_coefficients]
def admission035_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(11538473247984963714765590763529088/2473366471435546875:ℝ),(1209633522162638158804174904510991488/86567826500244140625:ℝ),(1207727545622142014337658133101428736/86567826500244140625:ℝ),(44660065242864623096081336701550592/9618647388916015625:ℝ)],
![(268311171658642251789376197425416192/28855942166748046875:ℝ),(114809079691778791836576712487622656/4122277452392578125:ℝ),(802393728738163057312558618550468608/28855942166748046875:ℝ),(89013780861856304634049276187508736/9618647388916015625:ℝ)],
![(401085720597731037585404945955725312/86567826500244140625:ℝ),(1201353460558164899720287376557416448/86567826500244140625:ℝ),(239889990215029270992534501449531392/17313565300048828125:ℝ),(44353579017950435661421119627329536/9618647388916015625:ℝ)]]
theorem admission035_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (371767404639678002291163501/165247103868600320000000000000:ℝ) admission035_10_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission035_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission035_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (7509/16384:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission035_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission035_10_coefficients]
def admission035_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(142883726627760094015955975924623914041344/349245181088008174580625:ℝ),(1285516748746534011709190559012753441292288/1047735543264024523741875:ℝ),(1285080021589689762041502451993399873503232/1047735543264024523741875:ℝ),(142738150908812010793393273584839391444992/349245181088008174580625:ℝ)],
![(285624606697652182155986858366135208771584/349245181088008174580625:ℝ),(2569748101869340468586725202736256850591744/1047735543264024523741875:ℝ),(102754994836765582613438774447067568799744/41909421730560980949675:ℝ),(285333529714251881072401577846279331905536/349245181088008174580625:ℝ)],
![(4078310859139773946858025212614608420864/9978433745371662130875:ℝ),(183461621874686636696790663389071915614208/149676506180574931963125:ℝ),(183399264189921400470638129883327049498624/149676506180574931963125:ℝ),(20370768400777124325572614894491420065792/49892168726858310654375:ℝ)]]
theorem admission035_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (578972060360943155659828531/2906429484163009997373440000:ℝ) admission035_11_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission035_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission035_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (7509/16384:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission035_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission035_11_coefficients]
def admission035_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(185250953342856592476864512/10986328125:ℝ),(185250953342856592476864512/3662109375:ℝ),(185250953342856592476864512/3662109375:ℝ),(185250953342856592476864512/10986328125:ℝ)],
![(370501906685713184953729024/10986328125:ℝ),(370501906685713184953729024/3662109375:ℝ),(370501906685713184953729024/3662109375:ℝ),(370501906685713184953729024/10986328125:ℝ)],
![(185250953342856592476864512/10986328125:ℝ),(185250953342856592476864512/3662109375:ℝ),(185250953342856592476864512/3662109375:ℝ),(185250953342856592476864512/10986328125:ℝ)]]
theorem admission035_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (41133974747/5000000000000:ℝ) admission035_12_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission035_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission035_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (7509/16384:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission035_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission035_12_coefficients]
def admission035_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6519211330033437406559993856/762939453125:ℝ),(19557633990100312219679981568/762939453125:ℝ),(19557633990100312219679981568/762939453125:ℝ),(6519211330033437406559993856/762939453125:ℝ)],
![(13038422660066874813119987712/762939453125:ℝ),(39115267980200624439359963136/762939453125:ℝ),(39115267980200624439359963136/762939453125:ℝ),(13038422660066874813119987712/762939453125:ℝ)],
![(6519211330033437406559993856/762939453125:ℝ),(19557633990100312219679981568/762939453125:ℝ),(19557633990100312219679981568/762939453125:ℝ),(6519211330033437406559993856/762939453125:ℝ)]]
theorem admission035_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (208448021404809/50000000000000000:ℝ) admission035_13_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission035_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission035_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (7509/16384:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission035_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission035_13_coefficients]
def admission035_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(9223372036854775808/9:ℝ),(9223372036854775808/3:ℝ),(9223372036854775808/3:ℝ),(9223372036854775808/9:ℝ)],
![(18446744073709551616/9:ℝ),(18446744073709551616/3:ℝ),(18446744073709551616/3:ℝ),(18446744073709551616/9:ℝ)],
![(9223372036854775808/9:ℝ),(9223372036854775808/3:ℝ),(9223372036854775808/3:ℝ),(9223372036854775808/9:ℝ)]]
theorem admission035_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission035_14_coefficients (7509/16384:ℝ) (939/2048:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission035_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission035_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (7509/16384:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission035_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission035_14_coefficients]
theorem admission035_all {δ p : ℝ}
 (hd : δ∈Set.Icc (7509/16384:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (2047/4096:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission035_00_pos hd hp
 · exact admission035_01_pos hd hp
 · exact admission035_02_pos hd hp
 · exact admission035_03_pos hd hp
 · exact admission035_04_pos hd hp
 · exact admission035_05_pos hd hp
 · exact admission035_06_pos hd hp
 · exact admission035_07_pos hd hp
 · exact admission035_08_pos hd hp
 · exact admission035_09_pos hd hp
 · exact admission035_10_pos hd hp
 · exact admission035_11_pos hd hp
 · exact admission035_12_pos hd hp
 · exact admission035_13_pos hd hp
 · exact admission035_14_pos hd hp
end
end DasStageAFinite
#print axioms DasStageAFinite.admission035_all
