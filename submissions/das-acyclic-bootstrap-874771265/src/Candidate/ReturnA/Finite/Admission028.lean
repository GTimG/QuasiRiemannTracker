/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def admission028_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(605961147583908262872875008/10130909067:ℝ),(12720151440410984605781327872/70916363469:ℝ),(12715118781559895691232280576/70916363469:ℝ),(4236695374236268925561077760/70916363469:ℝ)],
![(1211922295167816525745750016/10130909067:ℝ),(25440302880821969211562655744/70916363469:ℝ),(25430237563119791382464561152/70916363469:ℝ),(8473390748472537851122155520/70916363469:ℝ)],
![(605961147583908262872875008/10130909067:ℝ),(12720151440410984605781327872/70916363469:ℝ),(12715118781559895691232280576/70916363469:ℝ),(4236695374236268925561077760/70916363469:ℝ)]]
theorem admission028_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (29397979705/31518383764:ℝ) admission028_00_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission028_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission028_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (3753/8192:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission028_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission028_00_coefficients]
def admission028_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(443420096143487136635551744/10130909067:ℝ),(9309007269246123309346586624/70916363469:ℝ),(9306192519479016749346586624/70916363469:ℝ),(1033708641079101132149620736/23638787823:ℝ)],
![(886840192286974273271103488/10130909067:ℝ),(18618014538492246618693173248/70916363469:ℝ),(18612385038958033498693173248/70916363469:ℝ),(2067417282158202264299241472/23638787823:ℝ)],
![(443420096143487136635551744/10130909067:ℝ),(9309007269246123309346586624/70916363469:ℝ),(9306192519479016749346586624/70916363469:ℝ),(1033708641079101132149620736/23638787823:ℝ)]]
theorem admission028_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (5379595941/7879595941:ℝ) admission028_01_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission028_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission028_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (3753/8192:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission028_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission028_01_coefficients]
def admission028_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(46990234272302084610710306816/2110606055625:ℝ),(2959538052904482674634112630784/44322727168125:ℝ),(591738269330786803758695186432/8864545433625:ℝ),(985948213467795120984279744512/44322727168125:ℝ)],
![(93980468544604169221420613632/2110606055625:ℝ),(5919076105808965349268225261568/44322727168125:ℝ),(1183476538661573607517390372864/8864545433625:ℝ),(1971896426935590241968559489024/44322727168125:ℝ)],
![(46990234272302084610710306816/2110606055625:ℝ),(2959538052904482674634112630784/44322727168125:ℝ),(591738269330786803758695186432/8864545433625:ℝ),(985948213467795120984279744512/44322727168125:ℝ)]]
theorem admission028_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218924481535997/630367675280000:ℝ) admission028_02_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission028_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission028_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (3753/8192:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission028_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission028_02_coefficients]
def admission028_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6917611898387643017778429952/212749090407:ℝ),(20741069909109500725864431616/212749090407:ℝ),(20729306010492872398393573376/212749090407:ℝ),(6905847999771014690307571712/212749090407:ℝ)],
![(13829320996162034153786703872/212749090407:ℝ),(5923490295581157891655073792/30392727201:ℝ),(5920129275147665351687274496/30392727201:ℝ),(13805793853127586374012108800/212749090407:ℝ)],
![(6911709097774391136008273920/212749090407:ℝ),(20723362159958604515721084928/212749090407:ℝ),(20711598915540785063417348096/212749090407:ℝ),(985706550479510240529219584/30392727201:ℝ)]]
theorem admission028_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (56030930322749/110656542769152:ℝ) admission028_03_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission028_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission028_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (3753/8192:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission028_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission028_03_coefficients]
def admission028_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(120693533530803938670936064/23638787823:ℝ),(361741972653187750335348736/23638787823:ℝ),(361403445649214270768939008/23638787823:ℝ),(120355006526830459104526336/23638787823:ℝ)],
![(2013165882447116540500770816/196989898525:ℝ),(452538869312601527483010383872/14774242389375:ℝ),(452115541294132691285215019008/14774242389375:ℝ),(50188037721688301446587482112/4924747463125:ℝ)],
![(431737044153035879246987264/84424242225:ℝ),(75483378801453061174472474624/4924747463125:ℝ),(75412795921124590684876046336/4924747463125:ℝ),(75342234085795867399433486336/14774242389375:ℝ)]]
theorem admission028_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (656773444607991/8262355193430016:ℝ) admission028_04_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission028_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission028_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (3753/8192:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission028_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission028_04_coefficients]
def admission028_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(44679912534855426626381152256/14774242389375:ℝ),(402141583963337350483715293184/44322727168125:ℝ),(402163864124059412371781976064/44322727168125:ℝ),(134062017765288341767210139648/44322727168125:ℝ)],
![(5942457507602637379265888256/984949492625:ℝ),(802277047748155648335369207808/44322727168125:ℝ),(114617449988475888484891492352/6331818166875:ℝ),(38207955716184893303690887168/6331818166875:ℝ)],
![(44456950079184134062607171584/14774242389375:ℝ),(400135463784818297851653914624/44322727168125:ℝ),(16006331431810872280898338816/1772909086725:ℝ),(133393672248005911358626070528/44322727168125:ℝ)]]
theorem admission028_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (508769417715272530318533/10829634199132590571520000:ℝ) admission028_05_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission028_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission028_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (3753/8192:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission028_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission028_05_coefficients]
def admission028_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1540494650531548478960316699193897910272/209547108652804904748375:ℝ),(170728393611236450715257243240949791850496/7753243020153781475689875:ℝ),(170462047718990323087935868082637139607552/7753243020153781475689875:ℝ),(11346391229716990752113108542372314087424/1550648604030756295137975:ℝ)],
![(570402798841690440634909330506699811323904/38766215100768907378449375:ℝ),(1708542599157930839529945675208247500865536/38766215100768907378449375:ℝ),(243696924184417611353593672079654776733696/5538030728681272482635625:ℝ),(113547733737241082478867356131207149518848/7753243020153781475689875:ℝ)],
![(285411288493353972027250741155828697923584/38766215100768907378449375:ℝ),(122128661585964083707665637000499791659008/5538030728681272482635625:ℝ),(853568230695971664035476364144397739098112/38766215100768907378449375:ℝ),(8116539655522304102614544774192225583104/1107606145736254496527125:ℝ)]]
theorem admission028_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (20638965415340845997185367273/180663656735572701436733030400:ℝ) admission028_06_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission028_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission028_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (3753/8192:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission028_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission028_06_coefficients]
def admission028_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(93589228088259769450453572662850486272/5987060247222997278525:ℝ),(9820181773339550974706618667129679904768/209547108652804904748375:ℝ),(218077694736285502127876338408314896384/4656602414506775661075:ℝ),(3268937472882388551813691604444257452032/209547108652804904748375:ℝ)],
![(32724353489959008616601141839079974371328/1047735543264024523741875:ℝ),(98106221313299316960653013686781104095232/1047735543264024523741875:ℝ),(10893266533978972858090690179205490016256/116415060362669391526875:ℝ),(1306301239298817895150573590605931216896/41909421730560980949675:ℝ)],
![(16346238574513548962771766623081139273728/1047735543264024523741875:ℝ),(49005312446601562087119920351132704571392/1047735543264024523741875:ℝ),(5441324165571835304893781718997617606656/116415060362669391526875:ℝ),(3262568723611700923939176348585398632448/209547108652804904748375:ℝ)]]
theorem admission028_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (11869155873179628266149580117/48828015333938567955873792000:ℝ) admission028_07_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission028_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission028_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (3753/8192:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission028_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission028_07_coefficients]
def admission028_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(12543204835994757548769411798143543530362806144/85264936789064495747222900390625:ℝ),(113456742411938330851542739111625684857688921728/255794810367193487241668701171875:ℝ),(38008190466615632049207857300112676672139567488/85264936789064495747222900390625:ℝ),(38197443321549546001196574716992766062318199168/255794810367193487241668701171875:ℝ)],
![(128048564189178981408669038431890509546872565888/426324683945322478736114501953125:ℝ),(165442533231878094426013742550668000885252809216/182710578833709633744049072265625:ℝ),(387919232611595532220209959395810158707453284096/426324683945322478736114501953125:ℝ),(77961131207009317464970218198611860170491577088/255794810367193487241668701171875:ℝ)],
![(65332540009205193664821979441172791895058535168/426324683945322478736114501953125:ℝ),(590814020563455006724382502296547581908325055872/1278974051835967436208343505859375:ℝ),(197878280278517371974170672895246775346755446656/426324683945322478736114501953125:ℝ),(7952737577091954292754728696323818821634675584/51158962073438697448333740234375:ℝ)]]
theorem admission028_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (97993787781209043349761029672996433830959423/42666570838999973194081931100160000000000000000:ℝ) admission028_08_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission028_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission028_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (3753/8192:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission028_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission028_08_coefficients]
def admission028_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(76516588722787378177837797333176177596327424/136423898862503193195556640625:ℝ),(686909696912692430215122354060856645683789824/409271696587509579586669921875:ℝ),(685170576348548599482172133174338879339102208/409271696587509579586669921875:ℝ),(25312293981838177589107335946637960160477184/45474632954167731065185546875:ℝ)],
![(760570049183377111950196319323974161462749952/682119494312515965977783203125:ℝ),(6827764625933887127605214443436987684341096448/2046358482937547897933349609375:ℝ),(6810403604866455493369170369352021827588718592/2046358482937547897933349609375:ℝ),(670918260387224280831578968700412533669888/606328439388903080869140625:ℝ)],
![(377987105569440221061007332658093273481112832/682119494312515965977783203125:ℝ),(3393216141370424976529602673132704455922147328/2046358482937547897933349609375:ℝ),(3384550723123712495958309703480327430893207552/2046358482937547897933349609375:ℝ),(3572367935314806210465869529413282837823488/6496376136309675866455078125:ℝ)]]
theorem admission028_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (2495270177243374900752121719587559/290642948416300999737344000000000000:ℝ) admission028_09_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission028_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission028_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (3753/8192:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission028_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission028_09_coefficients]
def admission028_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(12852216508847480765714610818728192/86567826500244140625:ℝ),(38437028004885620581305183251384576/86567826500244140625:ℝ),(38317430725963717429980596546584576/86567826500244140625:ℝ),(1414735471288727916355836012658688/9618647388916015625:ℝ)],
![(3647466436584887052852224121394432/12366832357177734375:ℝ),(76357859597022709817136149516479232/86567826500244140625:ℝ),(76118972365846654125044859983675392/86567826500244140625:ℝ),(401482188067980598433520306618368/1374092484130859375:ℝ)],
![(281775434414927262487248834116416/1923729477783203125:ℝ),(601910633634087312687836766786496/1374092484130859375:ℝ),(4200120032121882318785941848264704/9618647388916015625:ℝ),(1395622770056980538110453651341312/9618647388916015625:ℝ)]]
theorem admission028_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (5989363160377895757195512229/2643953661897605120000000000000:ℝ) admission028_10_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission028_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission028_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (3753/8192:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission028_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission028_10_coefficients]
def admission028_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(274200259908029038676872220449757462528/21382358025796418851875:ℝ),(13426696302387862271725685499081593454592/349245181088008174580625:ℝ),(40252747588753566278338118841922754707456/1047735543264024523741875:ℝ),(4469490472361134119442600382238696669184/349245181088008174580625:ℝ)],
![(26844827776969007187427555098593391542272/1047735543264024523741875:ℝ),(26826604221769481856619158210097497767936/349245181088008174580625:ℝ),(80425157953123966752638340076993884717056/1047735543264024523741875:ℝ),(1786011537652301891347228036352985530368/69849036217601634916125:ℝ)],
![(536360601659023371690432651862211035136/41909421730560980949675:ℝ),(13399907919381619584893472711015904313344/349245181088008174580625:ℝ),(1606896414574816018972008849402845200384/41909421730560980949675:ℝ),(4460567215900375337293539799526230982656/349245181088008174580625:ℝ)]]
theorem admission028_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (16227448999053650685868123399/81380025556564279926456320000:ℝ) admission028_11_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission028_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission028_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (3753/8192:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission028_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission028_11_coefficients]
def admission028_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5789092291964268514902016/10986328125:ℝ),(5789092291964268514902016/3662109375:ℝ),(5789092291964268514902016/3662109375:ℝ),(5789092291964268514902016/10986328125:ℝ)],
![(11578184583928537029804032/10986328125:ℝ),(11578184583928537029804032/3662109375:ℝ),(11578184583928537029804032/3662109375:ℝ),(11578184583928537029804032/10986328125:ℝ)],
![(5789092291964268514902016/10986328125:ℝ),(5789092291964268514902016/3662109375:ℝ),(5789092291964268514902016/3662109375:ℝ),(5789092291964268514902016/10986328125:ℝ)]]
theorem admission028_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (41133974747/5000000000000:ℝ) admission028_12_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission028_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission028_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (3753/8192:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission028_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission028_12_coefficients]
def admission028_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(203725354063544918954999808/762939453125:ℝ),(611176062190634756864999424/762939453125:ℝ),(611176062190634756864999424/762939453125:ℝ),(203725354063544918954999808/762939453125:ℝ)],
![(407450708127089837909999616/762939453125:ℝ),(1222352124381269513729998848/762939453125:ℝ),(1222352124381269513729998848/762939453125:ℝ),(407450708127089837909999616/762939453125:ℝ)],
![(203725354063544918954999808/762939453125:ℝ),(611176062190634756864999424/762939453125:ℝ),(611176062190634756864999424/762939453125:ℝ),(203725354063544918954999808/762939453125:ℝ)]]
theorem admission028_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (208448021404809/50000000000000000:ℝ) admission028_13_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission028_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission028_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (3753/8192:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission028_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission028_13_coefficients]
def admission028_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(288230376151711744/9:ℝ),(288230376151711744/3:ℝ),(288230376151711744/3:ℝ),(288230376151711744/9:ℝ)],
![(576460752303423488/9:ℝ),(576460752303423488/3:ℝ),(576460752303423488/3:ℝ),(576460752303423488/9:ℝ)],
![(288230376151711744/9:ℝ),(288230376151711744/3:ℝ),(288230376151711744/3:ℝ),(288230376151711744/9:ℝ)]]
theorem admission028_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission028_14_coefficients (1875/4096:ℝ) (3753/8192:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission028_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission028_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (3753/8192:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission028_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission028_14_coefficients]
theorem admission028_all {δ p : ℝ}
 (hd : δ∈Set.Icc (1875/4096:ℝ) (3753/8192:ℝ)) (hp : p∈Set.Icc (1023/2048:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission028_00_pos hd hp
 · exact admission028_01_pos hd hp
 · exact admission028_02_pos hd hp
 · exact admission028_03_pos hd hp
 · exact admission028_04_pos hd hp
 · exact admission028_05_pos hd hp
 · exact admission028_06_pos hd hp
 · exact admission028_07_pos hd hp
 · exact admission028_08_pos hd hp
 · exact admission028_09_pos hd hp
 · exact admission028_10_pos hd hp
 · exact admission028_11_pos hd hp
 · exact admission028_12_pos hd hp
 · exact admission028_13_pos hd hp
 · exact admission028_14_pos hd hp
end
end DasStageAFinite
#print axioms DasStageAFinite.admission028_all
