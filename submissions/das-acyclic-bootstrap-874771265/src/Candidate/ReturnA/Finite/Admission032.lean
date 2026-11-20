/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def admission032_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4339664423883818141899099734016/70916363469:ℝ),(13017704910985575663572743094272/70916363469:ℝ),(13016416550319696901448186986496/70916363469:ℝ),(4338376063217939379774543626240/70916363469:ℝ)],
![(8679328847767636283798199468032/70916363469:ℝ),(26035409821971151327145486188544/70916363469:ℝ),(26032833100639393802896373972992/70916363469:ℝ),(8676752126435878759549087252480/70916363469:ℝ)],
![(4339664423883818141899099734016/70916363469:ℝ),(13017704910985575663572743094272/70916363469:ℝ),(13016416550319696901448186986496/70916363469:ℝ),(4338376063217939379774543626240/70916363469:ℝ)]]
theorem admission032_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (29397979705/31518383764:ℝ) admission032_00_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission032_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission032_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission032_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission032_00_coefficients]
def admission032_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3176273521335377957323634900992/70916363469:ℝ),(9528099988065754592610904702976/70916363469:ℝ),(9527379412125375313250904702976/70916363469:ℝ),(1058517648464999559321211633664/23638787823:ℝ)],
![(6352547042670755914647269801984/70916363469:ℝ),(19056199976131509185221809405952/70916363469:ℝ),(19054758824250750626501809405952/70916363469:ℝ),(2117035296929999118642423267328/23638787823:ℝ)],
![(3176273521335377957323634900992/70916363469:ℝ),(9528099988065754592610904702976/70916363469:ℝ),(9527379412125375313250904702976/70916363469:ℝ),(1058517648464999559321211633664/23638787823:ℝ)]]
theorem admission032_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (5379595941/7879595941:ℝ) admission032_01_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission032_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission032_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission032_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission032_01_coefficients]
def admission032_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(336609242463720886594368484409344/14774242389375:ℝ),(3029266425373347523454113364836352/44322727168125:ℝ),(3029049668573207067558910369988608/44322727168125:ℝ),(1009610970591022203887902458380288/44322727168125:ℝ)],
![(673218484927441773188736968818688/14774242389375:ℝ),(6058532850746695046908226729672704/44322727168125:ℝ),(6058099337146414135117820739977216/44322727168125:ℝ),(2019221941182044407775804916760576/44322727168125:ℝ)],
![(336609242463720886594368484409344/14774242389375:ℝ),(3029266425373347523454113364836352/44322727168125:ℝ),(3029049668573207067558910369988608/44322727168125:ℝ),(1009610970591022203887902458380288/44322727168125:ℝ)]]
theorem admission032_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218924481535997/630367675280000:ℝ) admission032_02_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission032_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission032_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission032_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission032_02_coefficients]
def admission032_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7068555539789113950292506836992/212749090407:ℝ),(21202655512498606149498459652096/212749090407:ℝ),(21199644526546621603319398793216/212749090407:ℝ),(1009363507691018486301920854016/30392727201:ℝ)],
![(14135600088154929149763941040128/212749090407:ℝ),(42400778092644358196624397172736/212749090407:ℝ),(42394756162681590445396971225088/212749090407:ℝ),(14129578158192161398536515092480/212749090407:ℝ)],
![(7067044548365815199471434203136/212749090407:ℝ),(21198122580145752047125937520640/212749090407:ℝ),(3027873090876424120296796061696/30392727201:ℝ),(7064033604355031994423069114368/212749090407:ℝ)]]
theorem admission032_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (784265275428079/1549191598768128:ℝ) admission032_03_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission032_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission032_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission032_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission032_03_coefficients]
def admission032_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2204526792627507354412018302976/422121211125:ℝ),(6612031509252192761762245771264/422121211125:ℝ),(6610482756091790130799477522432/422121211125:ℝ),(2202978039467104723449250054144/422121211125:ℝ)],
![(4409934205601087558390042853376/422121211125:ℝ),(154311553317580659795273170550784/4924747463125:ℝ),(154275412133690704693715424772096/4924747463125:ℝ),(154239273644368199238978262532096/14774242389375:ℝ)],
![(29405432172981069386373660672/5628282815:ℝ),(231513557128915232724140909658112/14774242389375:ℝ),(231459339937859459503164561031168/14774242389375:ℝ),(25711680754339844639418170212352/4924747463125:ℝ)]]
theorem admission032_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (93918602578942713/1180336456204288000:ℝ) admission032_04_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission032_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission032_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission032_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission032_04_coefficients]
def admission032_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6503834430342463583104148701184/2110606055625:ℝ),(58535347795200889991037710237696/6331818166875:ℝ),(58536184884589044393272468832256/6331818166875:ℝ),(19512340380415545151547204698112/6331818166875:ℝ)],
![(866634650625620095464512684032/140707070375:ℝ),(32759260417077061399294863474688/1772909086725:ℝ),(818993264353249534848113435475968/44322727168125:ℝ),(273001668873393329937063344078848/44322727168125:ℝ)],
![(6495685329041837848863541559296/2110606055625:ℝ),(409234075860520305045107615203328/44322727168125:ℝ),(409239970161126224095206153650176/44322727168125:ℝ),(136415286210484513876232911192064/44322727168125:ℝ)]]
theorem admission032_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (2323038099661530679057911/49506899196034699755520000:ℝ) admission032_05_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission032_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission032_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission032_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission032_05_coefficients]
def admission032_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(465722914359470425111886783370339056353280/62025944161230251805519:ℝ),(1396623093888082279863138286800182026698752/62025944161230251805519:ℝ),(1396077530074678937955299376282131079626752/62025944161230251805519:ℝ),(465177350542372356990162631917888109281280/62025944161230251805519:ℝ)],
![(116452195462348010723738321154018728782856192/7753243020153781475689875:ℝ),(1746100827521083573720867689391369341305356288/38766215100768907378449375:ℝ),(1745418829835218939432535689509015365057773568/38766215100768907378449375:ℝ),(116315795924251310036721143280587933533339648/7753243020153781475689875:ℝ)],
![(58236831167414207584752473232726346738696192/7753243020153781475689875:ℝ),(873211393841032148806406260141255574618636288/38766215100768907378449375:ℝ),(872870373538544603210473579332683440291053568/38766215100768907378449375:ℝ),(58168627106454765412950814290851919873179648/7753243020153781475689875:ℝ)]]
theorem admission032_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (6610567745360247570689617645/57812370155383264459754569728:ℝ) admission032_06_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission032_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission032_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission032_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission032_06_coefficients]
def admission032_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3342579458109650654882561235717323071946752/209547108652804904748375:ℝ),(10026029182721474751567148306558215054688256/209547108652804904748375:ℝ),(53038730675080454194700019321652593557504/1108714860596851347875:ℝ),(3340870372978381746113716580951448199626752/209547108652804904748375:ℝ)],
![(6683528099273363069024394508934293055602688/209547108652804904748375:ℝ),(100235831658818822012346017840769104227598336/1047735543264024523741875:ℝ),(3711805292339605332025253021411584505806848/38805020120889797175625:ℝ),(53440882769147739675932458051224228331520/1676376869222439237987:ℝ)],
![(3340948641163712414141833273216969983655936/209547108652804904748375:ℝ),(50105685745211448254510276307978028954157056/1047735543264024523741875:ℝ),(1855449718711789435210752345153743731294208/38805020120889797175625:ℝ),(3339239973165085713377840675451580341813248/209547108652804904748375:ℝ)]]
theorem admission032_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (23726727058922035335639866641/97656030667877135911747584000:ℝ) admission032_07_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission032_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission032_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission032_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission032_07_coefficients]
def admission032_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(270433747942785490026839668397095082349660871936/1740100750797234607086181640625:ℝ),(3411584730276998710548899488956734427584450357504/7308423153348385349761962890625:ℝ),(39849881308852007284064777384304290194931157129472/85264936789064495747222900390625:ℝ),(39897939311658251853198142318446280966382857050368/255794810367193487241668701171875:ℝ)],
![(2717983502384418803105686014513743437521190472704/8700503753986173035430908203125:ℝ),(34287753692552638351669995138740955475643071138304/36542115766741926748809814453125:ℝ),(400503996858381998835322168586343913960440229886464/426324683945322478736114501953125:ℝ),(80196837231677521424816014240636901912504639861248/255794810367193487241668701171875:ℝ)],
![(1365814762670491352971487672528268025772886113024/8700503753986173035430908203125:ℝ),(17229830041167644798925497693957283337720819350784/36542115766741926748809814453125:ℝ),(201254590314121962414998281664822462985784444239104/426324683945322478736114501953125:ℝ),(8059779584003853914323574384438124189224356562176/51158962073438697448333740234375:ℝ)]]
theorem admission032_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (1056381827901505820417342454676152665428362781/445822127950367066844284667822080000000000000000:ℝ) admission032_08_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission032_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission032_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission032_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission032_08_coefficients]
def admission032_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(76967930500673163403286353294986995399172987904/136423898862503193195556640625:ℝ),(692268152658185349265216370008584909184059441152/409271696587509579586669921875:ℝ),(691824961395473715388197017120987423726209335296/409271696587509579586669921875:ℝ),(3658104765762361559517050398119201625931251712/6496376136309675866455078125:ℝ)],
![(768504702514245187370265234626449216775058248704/682119494312515965977783203125:ℝ),(1382422407098808525301586315380290037162993647616/409271696587509579586669921875:ℝ),(6907682053977392077506272129296716862185870983168/2046358482937547897933349609375:ℝ),(10227040560281324219916413153607621561467011072/9094926590833546213037109375:ℝ)],
![(383665050010879370353833468151514239779193309184/682119494312515965977783203125:ℝ),(690154254440623176036369945371705127978934206464/409271696587509579586669921875:ℝ),(3448557247000023500565287043691779743554824306688/2046358482937547897933349609375:ℝ),(8509489813690030060987570993734565475272097792/15158210984722577021728515625:ℝ)]]
theorem admission032_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (34827011551538030539126402319930589/4069001277828213996322816000000000000:ℝ) admission032_09_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission032_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission032_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission032_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission032_09_coefficients]
def admission032_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1841797583918834418442750523143149824/12366832357177734375:ℝ),(5521033416745913826740629056012412672/12366832357177734375:ℝ),(5516674301960359557196233355095375872/12366832357177734375:ℝ),(204159829906668291148211299691790336/1374092484130859375:ℝ)],
![(1225764370765532645520831839367259136/4122277452392578125:ℝ),(25720714794636912510656964735062557696/28855942166748046875:ℝ),(25700378830137545033575508233412673536/28855942166748046875:ℝ),(2853338210328048945169892957973643264/9618647388916015625:ℝ)],
![(1835494122601785579071767388558820352/12366832357177734375:ℝ),(1100425170015748774766179551919492096/2473366471435546875:ℝ),(38484386865708860435136453808629219328/86567826500244140625:ℝ),(203459758310434420017148471608868864/1374092484130859375:ℝ)]]
theorem admission032_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (3410759986925702132572114923/1510830663941488640000000000000:ℝ) admission032_10_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission032_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission032_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission032_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission032_10_coefficients]
def admission032_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(13709851398557273513523727803652792817549312/1047735543264024523741875:ℝ),(4569173863806045753023467857646178369798144/116415060362669391526875:ℝ),(5873653694706155899979033882758199155621888/149676506180574931963125:ℝ),(4567620829081984345388584754714860526239744/349245181088008174580625:ℝ)],
![(5482569589875834224309642462853558419062784/209547108652804904748375:ℝ),(3045354325637429503948209427346331336179712/38805020120889797175625:ℝ),(82210590756361468812694472224849143491723264/1047735543264024523741875:ℝ),(1826591460902002888509402000051065967345664/69849036217601634916125:ℝ)],
![(13702996550821897608024484510614999277764608/1047735543264024523741875:ℝ),(4566889113106242758821160424392815638740992/116415060362669391526875:ℝ),(41095014893418377512841235045541749402370048/1047735543264024523741875:ℝ),(4565336475428030097158425245540469310488576/349245181088008174580625:ℝ)]]
theorem admission032_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (32438666689160059044343322267/162760051113128559852912640000:ℝ) admission032_11_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission032_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission032_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission032_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission032_11_coefficients]
def admission032_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5928030506971410959259664384/10986328125:ℝ),(5928030506971410959259664384/3662109375:ℝ),(5928030506971410959259664384/3662109375:ℝ),(5928030506971410959259664384/10986328125:ℝ)],
![(11856061013942821918519328768/10986328125:ℝ),(11856061013942821918519328768/3662109375:ℝ),(11856061013942821918519328768/3662109375:ℝ),(11856061013942821918519328768/10986328125:ℝ)],
![(5928030506971410959259664384/10986328125:ℝ),(5928030506971410959259664384/3662109375:ℝ),(5928030506971410959259664384/3662109375:ℝ),(5928030506971410959259664384/10986328125:ℝ)]]
theorem admission032_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (41133974747/5000000000000:ℝ) admission032_12_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission032_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission032_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission032_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission032_12_coefficients]
def admission032_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(208614762561069997009919803392/762939453125:ℝ),(625844287683209991029759410176/762939453125:ℝ),(625844287683209991029759410176/762939453125:ℝ),(208614762561069997009919803392/762939453125:ℝ)],
![(417229525122139994019839606784/762939453125:ℝ),(1251688575366419982059518820352/762939453125:ℝ),(1251688575366419982059518820352/762939453125:ℝ),(417229525122139994019839606784/762939453125:ℝ)],
![(208614762561069997009919803392/762939453125:ℝ),(625844287683209991029759410176/762939453125:ℝ),(625844287683209991029759410176/762939453125:ℝ),(208614762561069997009919803392/762939453125:ℝ)]]
theorem admission032_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (208448021404809/50000000000000000:ℝ) admission032_13_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission032_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission032_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission032_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission032_13_coefficients]
def admission032_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(295147905179352825856/9:ℝ),(295147905179352825856/3:ℝ),(295147905179352825856/3:ℝ),(295147905179352825856/9:ℝ)],
![(590295810358705651712/9:ℝ),(590295810358705651712/3:ℝ),(590295810358705651712/3:ℝ),(590295810358705651712/9:ℝ)],
![(295147905179352825856/9:ℝ),(295147905179352825856/3:ℝ),(295147905179352825856/3:ℝ),(295147905179352825856/9:ℝ)]]
theorem admission032_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission032_14_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission032_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission032_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (15015/32768:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission032_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission032_14_coefficients]
theorem admission032_all {δ p : ℝ}
 (hd : δ∈Set.Icc (15015/32768:ℝ) (7509/16384:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission032_00_pos hd hp
 · exact admission032_01_pos hd hp
 · exact admission032_02_pos hd hp
 · exact admission032_03_pos hd hp
 · exact admission032_04_pos hd hp
 · exact admission032_05_pos hd hp
 · exact admission032_06_pos hd hp
 · exact admission032_07_pos hd hp
 · exact admission032_08_pos hd hp
 · exact admission032_09_pos hd hp
 · exact admission032_10_pos hd hp
 · exact admission032_11_pos hd hp
 · exact admission032_12_pos hd hp
 · exact admission032_13_pos hd hp
 · exact admission032_14_pos hd hp
end
end DasStageAFinite
#print axioms DasStageAFinite.admission032_all
