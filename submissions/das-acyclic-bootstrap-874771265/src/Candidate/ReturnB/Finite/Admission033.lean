/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def admission033_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(925649530507344389088502349824/472772661:ℝ),(8330433500342625764800100040704/1418317983:ℝ),(8330021226119152027803678932992/1418317983:ℝ),(2776536317298559430269085941760/1418317983:ℝ)],
![(1851299061014688778177004699648/472772661:ℝ),(16660867000685251529600200081408/1418317983:ℝ),(16660042452238304055607357865984/1418317983:ℝ),(5553072634597118860538171883520/1418317983:ℝ)],
![(925649530507344389088502349824/472772661:ℝ),(8330433500342625764800100040704/1418317983:ℝ),(8330021226119152027803678932992/1418317983:ℝ),(2776536317298559430269085941760/1418317983:ℝ)]]
theorem admission033_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (587954435/630363548:ℝ) admission033_00_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission033_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission033_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (30033/65536:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission033_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission033_00_coefficients]
def admission033_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2032564978824983105062628753408/1418317983:ℝ),(6097464352174027945792686260224/1418317983:ℝ),(6097233767873106576397486260224/1418317983:ℝ),(225814932724895748407492083712/157590887:ℝ)],
![(4065129957649966210125257506816/1418317983:ℝ),(12194928704348055891585372520448/1418317983:ℝ),(12194467535746213152794972520448/1418317983:ℝ),(451629865449791496814984167424/157590887:ℝ)],
![(2032564978824983105062628753408/1418317983:ℝ),(6097464352174027945792686260224/1418317983:ℝ),(6097233767873106576397486260224/1418317983:ℝ),(225814932724895748407492083712/157590887:ℝ)]]
theorem admission033_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (107590887/157590887:ℝ) admission033_01_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission033_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission033_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (30033/65536:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission033_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission033_01_coefficients]
def admission033_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3231072523119809574034347533533184/4432243696875:ℝ),(16154784597896882301992158502060032/7387072828125:ℝ),(16154206580194716733812579336454144/7387072828125:ℝ),(16153628562492551165633000170848256/22161218484375:ℝ)],
![(6462145046239619148068695067066368/4432243696875:ℝ),(32309569195793764603984317004120064/7387072828125:ℝ),(32308413160389433467625158672908288/7387072828125:ℝ),(32307257124985102331266000341696512/22161218484375:ℝ)],
![(3231072523119809574034347533533184/4432243696875:ℝ),(16154784597896882301992158502060032/7387072828125:ℝ),(16154206580194716733812579336454144/7387072828125:ℝ),(16153628562492551165633000170848256/22161218484375:ℝ)]]
theorem admission033_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218922489762229/630363548000000:ℝ) admission033_02_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission033_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission033_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (30033/65536:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission033_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission033_02_coefficients]
def admission033_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1507543146292705047167818006528/1418317983:ℝ),(13566924805739039960579484680192/4254953949:ℝ),(13565961314190414681480607301632/4254953949:ℝ),(4521665947329489862404576641024/4254953949:ℝ)],
![(3014925123741398665016278777856/1418317983:ℝ),(27132399098592732639590304710656/4254953949:ℝ),(27130472122208170398981300420608/4254953949:ℝ),(9042848394839633754439832043520/4254953949:ℝ)],
![(1507381977448693617848460771328/1418317983:ℝ),(13565474292853692679010820030464/4254953949:ℝ),(13564510808017755717500693118976/4254953949:ℝ),(4521182447510143892035255402496/4254953949:ℝ)]]
theorem admission033_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (62744010646961/123934516445184:ℝ) admission033_03_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission033_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission033_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (30033/65536:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission033_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission033_03_coefficients]
def admission033_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7961871677931738070616928944128/47658534375:ℝ),(148073467287698042769462423191552/295482913125:ℝ),(740280610062484320059533650034688/1477414565625:ℝ),(246731295639877986401346331344896/1477414565625:ℝ)],
![(2468426748289535985640793662554112/7387072828125:ℝ),(7404412905455510592106013942349824/7387072828125:ℝ),(7403545598375583519416147475693568/7387072828125:ℝ),(822519813736536304316975731965952/2462357609375:ℝ)],
![(1234336638210116584695169676214272/7387072828125:ℝ),(1234192074421019840956484454187008/2462357609375:ℝ),(1234047516021053973039493075173376/2462357609375:ℝ),(1233902963010218980944195539173376/7387072828125:ℝ)]]
theorem admission033_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (657424236755973687/8262301096345600000:ℝ) admission033_04_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission033_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission033_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (30033/65536:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission033_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission033_04_coefficients]
def admission033_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2184607770951741414326112163463168/22161218484375:ℝ),(6553870187342974625881738040049664/22161218484375:ℝ),(6553917038514305442871282440863744/22161218484375:ℝ),(728218207374357410438552188092416/7387072828125:ℝ)],
![(873569328708158079896631910596608/4432243696875:ℝ),(13103633818296789069698082648621056/22161218484375:ℝ),(13103727659336038496475024902324224/22161218484375:ℝ),(485326720508893314028900200742912/2462357609375:ℝ)],
![(2183238872589048985157047389519872/22161218484375:ℝ),(6549763630953814443816344608571392/22161218484375:ℝ),(1309962124164346610720748492292096/4432243696875:ℝ),(145552390830464506329629682827264/1477414565625:ℝ)]]
theorem admission033_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (260262354920989153999930309/5544736406017077673984000000:ℝ) admission033_05_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission033_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission033_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (30033/65536:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission033_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission033_05_coefficients]
def admission033_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(148941407072488893746622384624239003041792/620251319444533055775:ℝ),(148912310762573705528935742796952210767872/206750439814844351925:ℝ),(446649650187621478978723836594412788383744/620251319444533055775:ℝ),(9923608331482764501094942500413010608128/41350087962968870385:ℝ)],
![(186193928573229494673670945221029726303289344/387657074652833159859375:ℝ),(186157557041342051426579468718677002031202304/129219024884277719953125:ℝ),(558363565065705798620940412647735493182619648/387657074652833159859375:ℝ),(12405654834314959600644537446875614226153472/25843804976855543990625:ℝ)],
![(3003404811384643099420385639705817722650624/12505066924284940640625:ℝ),(93087362814733485470994629470581870301282304/129219024884277719953125:ℝ),(279207533698442374259238014776227500442779648/387657074652833159859375:ℝ),(6203399627138231787460198384117482596073472/25843804976855543990625:ℝ)]]
theorem admission033_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (8813934765579358289051497/77082150819303193302794240:ℝ) admission033_06_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission033_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission033_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (30033/65536:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission033_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission033_06_coefficients]
def admission033_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(356400808234923622165500110941752685232128/698481215590690378125:ℝ),(3207333823487575078063692539738582681649152/2095443646772071134375:ℝ),(3207060381378903282784558860352254380081152/2095443646772071134375:ℝ),(1068928982596099071217366653438929754128384/2095443646772071134375:ℝ)],
![(3563573261220830858969831368010668101861376/3492406077953451890625:ℝ),(32069425011571332390212284658698920755462144/10477218233860355671875:ℝ),(32066690757330646847329931743012890414678016/10477218233860355671875:ℝ),(3420155369414978250888685180270711668736/3352709834835313815:ℝ)],
![(1781569220046212748142330813301904675700736/3492406077953451890625:ℝ),(16032755894133456999893821960006007347216384/10477218233860355671875:ℝ),(16031388850436130433407137441251618514272256/10477218233860355671875:ℝ),(1068668123288262335588061584230265038831616/2095443646772071134375:ℝ)]]
theorem admission033_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (1898335929852134881180457143/7812380150605053375283200000:ℝ) admission033_07_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission033_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission033_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (30033/65536:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission033_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission033_07_coefficients]
def admission033_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(20371009609311337954844724228236874595886562304/4092663372601701434326171875:ℝ),(20383312727603825253462002592983013419026482176/1364221124200567144775390625:ℝ),(12237369396065328201493672147018048134732028928/818532674520340286865234375:ℝ),(658319948601541897714849325908059243524750336/132021399116183917236328125:ℝ)],
![(40844693163202729033965555156800761924608386048/4092663372601701434326171875:ℝ),(204346446980091072316606598236704616694506268672/6821105621002835723876953125:ℝ),(613408278868395437524092842952537998378278352896/20463316863008507171630859375:ℝ),(40918480748469746550701976660003817130840295424/4092663372601701434326171875:ℝ)],
![(20473683553891391079120830928563887328721823744/4092663372601701434326171875:ℝ),(102429883342071946049296585271789549599373857792/6821105621002835723876953125:ℝ),(307474043966762232486751039277086795009977629696/20463316863008507171630859375:ℝ),(20510562341821947721541647556853980581573035008/4092663372601701434326171875:ℝ)]]
theorem admission033_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (19893564071593103471528051004137572847545471/8388479312692064714793939684556800000000000000:ℝ) admission033_08_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission033_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission033_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (30033/65536:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission033_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission033_08_coefficients]
def admission033_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(118021960160448425293155105224859150352775168/6548261396162722294921875:ℝ),(353952423507651780836052280216486108985294848/6548261396162722294921875:ℝ),(117946323483214925611153430339476490291249152/2182753798720907431640625:ℝ),(117908507102679556677741115712665916356427776/6548261396162722294921875:ℝ)],
![(235863553087011154041972256873667177073335296/6548261396162722294921875:ℝ),(3536818973747188002577898943433649984219643904/32741306980813611474609375:ℝ),(38018114949796684221333319842342553746669568/352057064309823779296875:ℝ),(47127339280853634921459437091474587407876096/1309652279232544458984375:ℝ)],
![(117841592926562728748817151648808026720560128/6548261396162722294921875:ℝ),(1767056856208929098397637542351219439293169664/32741306980813611474609375:ℝ),(588829946027622582805565763415236714690510848/10913768993604537158203125:ℝ),(117728189301588617929556069744707020682952704/6548261396162722294921875:ℝ)]]
theorem admission033_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (1673018194048674699978904381861/195309503765126334382080000000000:ℝ) admission033_09_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission033_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission033_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (30033/65536:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission033_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission033_09_coefficients]
def admission033_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(329397620830605659332320626053292032/69253807763671875:ℝ),(329267428045530937082860678300306432/23084602587890625:ℝ),(987411715649448246616998251641962496/69253807763671875:ℝ),(329007052344059946860893092794335232/69253807763671875:ℝ)],
![(658230711275432025524419130113122304/69253807763671875:ℝ),(657970367760291648937638876154123264/23084602587890625:ℝ),(1973130092464154939045080830073372672/69253807763671875:ℝ),(657449700459909841727677081724125184/69253807763671875:ℝ)],
![(36537003053657718375875277276612608/7694867529296875:ℝ),(109567625586118146182789763314266368/7694867529296875:ℝ),(328572729320662970490133710541684736/23084602587890625:ℝ),(109480861723481344341694939928723456/23084602587890625:ℝ)]]
theorem admission033_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (76471498508575380087151383/33842385290631577600000000000:ℝ) admission033_10_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission033_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission033_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (30033/65536:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission033_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission033_10_coefficients]
def admission033_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4385406222227527385704615208881457991778304/10477218233860355671875:ℝ),(4385033484055635181088413630408153244893184/3492406077953451890625:ℝ),(4384660759486512910940823961765110018473984/3492406077953451890625:ℝ),(4384288048520160575261846202952328312520704/10477218233860355671875:ℝ)],
![(8769715830880304507600954557710679253450752/10477218233860355671875:ℝ),(8768970402183381717823902829617776963878912/3492406077953451890625:ℝ),(8768225000690206967753482609273944521310208/3492406077953451890625:ℝ),(1753495925280156051477938779335836385148928/2095443646772071134375:ℝ)],
![(4384309608652777121896339348829221261672448/10477218233860355671875:ℝ),(4383936918127746536735489199209623718985728/3492406077953451890625:ℝ),(4383564241203694056812658647508834502836224/3492406077953451890625:ℝ),(4383191577880619682127847693726853613223936/10477218233860355671875:ℝ)]]
theorem admission033_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (7786112337769814363724392503/39061900753025266876416000000:ℝ) admission033_11_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission033_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission033_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (30033/65536:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission033_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission033_11_coefficients]
def admission033_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7587717262307909880441208832/439453125:ℝ),(7587717262307909880441208832/146484375:ℝ),(7587717262307909880441208832/146484375:ℝ),(7587717262307909880441208832/439453125:ℝ)],
![(15175434524615819760882417664/439453125:ℝ),(15175434524615819760882417664/146484375:ℝ),(15175434524615819760882417664/146484375:ℝ),(15175434524615819760882417664/439453125:ℝ)],
![(7587717262307909880441208832/439453125:ℝ),(7587717262307909880441208832/146484375:ℝ),(7587717262307909880441208832/146484375:ℝ),(7587717262307909880441208832/439453125:ℝ)]]
theorem admission033_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (411330977/50000000000:ℝ) admission033_12_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission033_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission033_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (30033/65536:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission033_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission033_12_coefficients]
def admission033_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2403034924987510437162080272384/274658203125:ℝ),(2403034924987510437162080272384/91552734375:ℝ),(2403034924987510437162080272384/91552734375:ℝ),(2403034924987510437162080272384/274658203125:ℝ)],
![(4806069849975020874324160544768/274658203125:ℝ),(4806069849975020874324160544768/91552734375:ℝ),(4806069849975020874324160544768/91552734375:ℝ),(4806069849975020874324160544768/274658203125:ℝ)],
![(2403034924987510437162080272384/274658203125:ℝ),(2403034924987510437162080272384/91552734375:ℝ),(2403034924987510437162080272384/91552734375:ℝ),(2403034924987510437162080272384/274658203125:ℝ)]]
theorem admission033_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (260537568623/62500000000000:ℝ) admission033_13_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission033_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission033_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (30033/65536:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission033_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission033_13_coefficients]
def admission033_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(9444732965739290427392/9:ℝ),(9444732965739290427392/3:ℝ),(9444732965739290427392/3:ℝ),(9444732965739290427392/9:ℝ)],
![(18889465931478580854784/9:ℝ),(18889465931478580854784/3:ℝ),(18889465931478580854784/3:ℝ),(18889465931478580854784/9:ℝ)],
![(9444732965739290427392/9:ℝ),(9444732965739290427392/3:ℝ),(9444732965739290427392/3:ℝ),(9444732965739290427392/9:ℝ)]]
theorem admission033_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission033_14_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission033_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission033_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (30033/65536:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission033_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission033_14_coefficients]
theorem admission033_all {δ p : ℝ}
 (hd : δ∈Set.Icc (15015/32768:ℝ) (30033/65536:ℝ)) (hp : p∈Set.Icc (8191/16384:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission033_00_pos hd hp
 · exact admission033_01_pos hd hp
 · exact admission033_02_pos hd hp
 · exact admission033_03_pos hd hp
 · exact admission033_04_pos hd hp
 · exact admission033_05_pos hd hp
 · exact admission033_06_pos hd hp
 · exact admission033_07_pos hd hp
 · exact admission033_08_pos hd hp
 · exact admission033_09_pos hd hp
 · exact admission033_10_pos hd hp
 · exact admission033_11_pos hd hp
 · exact admission033_12_pos hd hp
 · exact admission033_13_pos hd hp
 · exact admission033_14_pos hd hp
end
end DasStageBFinite
#print axioms DasStageBFinite.admission033_all
