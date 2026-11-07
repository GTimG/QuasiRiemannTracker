/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def admission029_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(84833816866648844184584192/1418317983:ℝ),(254400797713356264732360704/1418317983:ℝ),(254300144826765996910968832/1418317983:ℝ),(84733163980058576363192320/1418317983:ℝ)],
![(169667633733297688369168384/1418317983:ℝ),(508801595426712529464721408/1418317983:ℝ),(508600289653531993821937664/1418317983:ℝ),(169466327960117152726384640/1418317983:ℝ)],
![(84833816866648844184584192/1418317983:ℝ),(254400797713356264732360704/1418317983:ℝ),(254300144826765996910968832/1418317983:ℝ),(84733163980058576363192320/1418317983:ℝ)]]
theorem admission029_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (587954435/630363548:ℝ) admission029_00_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission029_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission029_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission029_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission029_00_coefficients]
def admission029_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(62078218656354757410553856/1418317983:ℝ),(186178360973722141031661568/1418317983:ℝ),(186122065978380009831661568/1418317983:ℝ),(6891324851223625134505984/157590887:ℝ)],
![(124156437312709514821107712/1418317983:ℝ),(372356721947444282063323136/1418317983:ℝ),(372244131956760019663323136/1418317983:ℝ),(13782649702447250269011968/157590887:ℝ)],
![(62078218656354757410553856/1418317983:ℝ),(186178360973722141031661568/1418317983:ℝ),(186122065978380009831661568/1418317983:ℝ),(6891324851223625134505984/157590887:ℝ)]]
theorem admission029_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (107590887/157590887:ℝ) admission029_01_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission029_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission029_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission029_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission029_01_coefficients]
def admission029_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(493392974467301171934292606976/22161218484375:ℝ),(493251856864233406265450037248/7387072828125:ℝ),(98622147852233128119321493504/1477414565625:ℝ),(492969621658097874927764897792/22161218484375:ℝ)],
![(986785948934602343868585213952/22161218484375:ℝ),(986503713728466812530900074496/7387072828125:ℝ),(197244295704466256238642987008/1477414565625:ℝ),(985939243316195749855529795584/22161218484375:ℝ)],
![(493392974467301171934292606976/22161218484375:ℝ),(493251856864233406265450037248/7387072828125:ℝ),(98622147852233128119321493504/1477414565625:ℝ),(492969621658097874927764897792/22161218484375:ℝ)]]
theorem admission029_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218922489762229/630363548000000:ℝ) admission029_02_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission029_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission029_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission029_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission029_02_coefficients]
def admission029_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(138291956161687806462132224/4254953949:ℝ),(414640566943016879283765248/4254953949:ℝ),(414405303179905327981133824/4254953949:ℝ),(138056692398576255159500800/4254953949:ℝ)],
![(276465857290997845536538624/4254953949:ℝ),(828926981842996722694881280/4254953949:ℝ),(718522521596763985412096/3690333:ℝ),(275995342849069998021804032/4254953949:ℝ)],
![(138173901129310039074406400/4254953949:ℝ),(414286414899979843411116032/4254953949:ℝ),(414051164221163547199012864/4254953949:ℝ),(137938650450493742862303232/4254953949:ℝ)]]
theorem admission029_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (1960226121163/3872953638912:ℝ) admission029_03_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission029_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission029_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission029_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission029_03_coefficients]
def admission029_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(12582186486954547776452296704/2462357609375:ℝ),(37711257729214124683023876096/2462357609375:ℝ),(37675966520056623650033369088/2462357609375:ℝ),(12546895277797046743461789696/2462357609375:ℝ)],
![(75553380508693117820632039424/7387072828125:ℝ),(226448246479751427390501552128/7387072828125:ℝ),(226236414593609400806388269056/7387072828125:ℝ),(75341548622551091236518756352/7387072828125:ℝ)],
![(37806821047829474491275149312/7387072828125:ℝ),(22662894658421810668285984768/1477414565625:ℝ),(113208515033439529856288161792/7387072828125:ℝ),(37700862789159951006133387264/7387072828125:ℝ)]]
theorem admission029_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (821616104077645437/10327876370432000000:ℝ) admission029_04_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission029_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission029_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission029_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission029_04_coefficients]
def admission029_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1916904713976772451106816/635447125:ℝ),(200567611621345535661716537344/22161218484375:ℝ),(6470291032648005369880641536/714878015625:ℝ),(66863462290682570036933558272/22161218484375:ℝ)],
![(57363295929420729941229568/9531706875:ℝ),(400132171910775641443363192832/22161218484375:ℝ),(400155263615880007164806299648/22161218484375:ℝ),(133392754741007562834801852416/22161218484375:ℝ)],
![(28609725219769143174627328/9531706875:ℝ),(199564560289430105781646655488/22161218484375:ℝ),(199576241603791840698506412032/22161218484375:ℝ),(66529292450324992797868294144/22161218484375:ℝ)]]
theorem admission029_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (163706160849203928993/3493407513871646720000:ℝ) admission029_05_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission029_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission029_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission029_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission029_05_coefficients]
def admission029_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(950655684561136353261126730357106016256/129219024884277719953125:ℝ),(8542569012822778272997467373527389437952/387657074652833159859375:ℝ),(8529245204241641785161973560952827674624/387657074652833159859375:ℝ),(189242882910620844693251945233117085696/25843804976855543990625:ℝ)],
![(1902710602596219529040592725709946093568/129219024884277719953125:ℝ),(17097724413110991534510665456585497378816/387657074652833159859375:ℝ),(17071070086597992379745150493380388585472/387657074652833159859375:ℝ),(378765165225905745606196107594981965824/25843804976855543990625:ℝ)],
![(952054918035083175779465995352840077312/129219024884277719953125:ℝ),(8555155400288213261513198083058107940864/387657074652833159859375:ℝ),(8541824882356350594583176932427560910848/387657074652833159859375:ℝ),(189522282315284900912944162361864880128/25843804976855543990625:ℝ)]]
theorem admission029_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (1376923194843554263157798743/12044086065516123953561600000:ℝ) admission029_06_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission029_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission029_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission029_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission029_06_coefficients]
def admission029_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(163618682462485703973674530586191200256/10477218233860355671875:ℝ),(490522018274596474176556726883576971264/10477218233860355671875:ℝ),(490188072366274036430488315816111505408/10477218233860355671875:ℝ),(6531389462166530649104244780749029376/419088729354414226875:ℝ)],
![(326918607210493641330901918563674882048/10477218233860355671875:ℝ),(980088089429186147336837875825412145152/10477218233860355671875:ℝ),(979420523554757398288656656737830436864/10477218233860355671875:ℝ),(65250208267212978456544139895218634752/2095443646772071134375:ℝ)],
![(163299924748007937357227387977483681792/10477218233860355671875:ℝ),(489566071154589673160281148941835173888/10477218233860355671875:ℝ),(489232451188483361858168340921718931456/10477218233860355671875:ℝ),(32593260956380325211022915991473487872/2095443646772071134375:ℝ)]]
theorem admission029_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (59286796306660699358004269/244136879706407917977600000:ℝ) admission029_07_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission029_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission029_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission029_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission029_07_coefficients]
def admission029_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1065888558693200953294855193529974739904/7097924683665802001953125:ℝ),(298838978612177233143402473752467848547776/660106995580919586181640625:ℝ),(9309141086307562961822299465098783653068352/20463316863008507171630859375:ℝ),(1039363150028025808893939590738602024410176/6821105621002835723876953125:ℝ)],
![(2175339712981439499955858332077839448576/7097924683665802001953125:ℝ),(609822458836389494227963583855586534193024/660106995580919586181640625:ℝ),(18994468531928257245723565525448936871885952/20463316863008507171630859375:ℝ),(2120492224199178608502933890829476197382272/6821105621002835723876953125:ℝ)],
![(1109451154288238546661003138547864708672/7097924683665802001953125:ℝ),(310983480224212261084561110103118685645248/660106995580919586181640625:ℝ),(387413097824827771356050642414006128752704/818532674520340286865234375:ℝ),(1081129074171152799608994300090874172972096/6821105621002835723876953125:ℝ)]]
theorem admission029_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (16654508729581264895232112398905855311/7103602435658033687166976000000000000000:ℝ) admission029_08_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission029_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission029_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission029_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission029_08_coefficients]
def admission029_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(18253871479568180887046330869571118033536/32741306980813611474609375:ℝ),(54622929485351559261113419691638835150848/32741306980813611474609375:ℝ),(18161427593607064413689582305677729071104/10913768993604537158203125:ℝ),(144921798349107398736052029502540218368/261930455846508891796875:ℝ)],
![(36287145508873807089241287749351823165568/32741306980813611474609375:ℝ),(108584549801010651252629846598528762281984/32741306980813611474609375:ℝ),(36102579779637589321731093962282082762752/10913768993604537158203125:ℝ),(7202067016798402468983986736855796154368/6548261396162722294921875:ℝ)],
![(18033274029305626202194956879780705132032/32741306980813611474609375:ℝ),(53961620315659091991516426906889927131136/32741306980813611474609375:ℝ),(17941152186030524908041511656604353691648/10913768993604537158203125:ℝ),(3579022058070717500582685999292290695168/6548261396162722294921875:ℝ)]]
theorem admission029_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (52081625589500145005625177863/6103421992660197949440000000000:ℝ) admission029_09_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission029_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission029_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission029_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission029_09_coefficients]
def admission029_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(10213465584285420940081903563808/69253807763671875:ℝ),(10181648454307520206060068920416/23084602587890625:ℝ),(10149837750385297778617838977024/23084602587890625:ℝ),(10118033481872079946817713733632/69253807763671875:ℝ)],
![(6762984087716067372911953948928/23084602587890625:ℝ),(60676200500599021488446704691968/69253807763671875:ℝ),(60485582651568440555506322243584/69253807763671875:ℝ),(89325930812618787214646575104/307794701171875:ℝ)],
![(403014539227838261529260876288/2770152310546875:ℝ),(30130885801202440753145129345536/69253807763671875:ℝ),(30035700321859521856822683369472/69253807763671875:ℝ),(9980178010721323266909075931136/69253807763671875:ℝ)]]
theorem admission029_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (74358120640526140234687/33049204385382400000000000:ℝ) admission029_10_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission029_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission029_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission029_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission029_10_coefficients]
def admission029_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(134221561550530475491371057399304290304/10477218233860355671875:ℝ),(134130491249122823014794908150019653632/3492406077953451890625:ℝ),(134039447522624531729227613692078587904/3492406077953451890625:ℝ),(26789686074207120326933834805096218624/2095443646772071134375:ℝ)],
![(268175150830005489735738765930515922944/10477218233860355671875:ℝ),(267993103336462115805328255740641804288/3492406077953451890625:ℝ),(267811108964740132528930581516998672384/3492406077953451890625:ℝ),(267629167714839539906545743259586527232/10477218233860355671875:ℝ)],
![(26790717855895002848873541706242326528/2095443646772071134375:ℝ),(133862612087339292790533347590622150656/3492406077953451890625:ℝ),(26754332288423120159940593564984016896/698481215590690378125:ℝ),(133680737343803938271876569234105434112/10477218233860355671875:ℝ)]]
theorem admission029_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (243163844686576227599064749/1220684398532039589888000000:ℝ) admission029_11_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission029_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission029_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission029_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission029_11_coefficients]
def admission029_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(231558754342892757581824/439453125:ℝ),(231558754342892757581824/146484375:ℝ),(231558754342892757581824/146484375:ℝ),(231558754342892757581824/439453125:ℝ)],
![(463117508685785515163648/439453125:ℝ),(463117508685785515163648/146484375:ℝ),(463117508685785515163648/146484375:ℝ),(463117508685785515163648/439453125:ℝ)],
![(231558754342892757581824/439453125:ℝ),(231558754342892757581824/146484375:ℝ),(231558754342892757581824/146484375:ℝ),(231558754342892757581824/439453125:ℝ)]]
theorem admission029_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (411330977/50000000000:ℝ) admission029_12_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission029_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission029_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission029_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission029_12_coefficients]
def admission029_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(73334806060409864415346688/274658203125:ℝ),(73334806060409864415346688/91552734375:ℝ),(73334806060409864415346688/91552734375:ℝ),(73334806060409864415346688/274658203125:ℝ)],
![(146669612120819728830693376/274658203125:ℝ),(146669612120819728830693376/91552734375:ℝ),(146669612120819728830693376/91552734375:ℝ),(146669612120819728830693376/274658203125:ℝ)],
![(73334806060409864415346688/274658203125:ℝ),(73334806060409864415346688/91552734375:ℝ),(73334806060409864415346688/91552734375:ℝ),(73334806060409864415346688/274658203125:ℝ)]]
theorem admission029_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (260537568623/62500000000000:ℝ) admission029_13_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
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
end DasStageBFinite
#print axioms DasStageBFinite.admission029_all
