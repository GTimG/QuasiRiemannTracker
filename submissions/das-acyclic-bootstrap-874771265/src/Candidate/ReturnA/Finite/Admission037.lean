/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def admission037_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6215350407257051365376/3376969689:ℝ),(390338399179877606490112/70916363469:ℝ),(389109722702560976961536/70916363469:ℝ),(129293682075081449144320/70916363469:ℝ)],
![(12430700814514102730752/3376969689:ℝ),(780676798359755212980224/70916363469:ℝ),(778219445405121953923072/70916363469:ℝ),(258587364150162898288640/70916363469:ℝ)],
![(6215350407257051365376/3376969689:ℝ),(390338399179877606490112/70916363469:ℝ),(389109722702560976961536/70916363469:ℝ),(129293682075081449144320/70916363469:ℝ)]]
theorem admission037_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (29397979705/31518383764:ℝ) admission037_00_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission037_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission037_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (471/1024:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission037_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission037_00_coefficients]
def admission037_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(13618006772173879902208/10130909067:ℝ),(285290947448291477946368/70916363469:ℝ),(284603752680931477946368/70916363469:ℝ),(31546284212619053105152/23638787823:ℝ)],
![(27236013544347759804416/10130909067:ℝ),(570581894896582955892736/70916363469:ℝ),(569207505361862955892736/70916363469:ℝ),(63092568425238106210304/23638787823:ℝ)],
![(13618006772173879902208/10130909067:ℝ),(285290947448291477946368/70916363469:ℝ),(284603752680931477946368/70916363469:ℝ),(31546284212619053105152/23638787823:ℝ)]]
theorem admission037_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (5379595941/7879595941:ℝ) admission037_01_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission037_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission037_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (471/1024:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission037_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission037_01_coefficients]
def admission037_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4327923860701138600853504/6331818166875:ℝ),(18135937136304711037616128/8864545433625:ℝ),(90472970288323199758237696/44322727168125:ℝ),(30088751631707614776131584/44322727168125:ℝ)],
![(8655847721402277201707008/6331818166875:ℝ),(36271874272609422075232256/8864545433625:ℝ),(180945940576646399516475392/44322727168125:ℝ),(60177503263415229552263168/44322727168125:ℝ)],
![(4327923860701138600853504/6331818166875:ℝ),(18135937136304711037616128/8864545433625:ℝ),(90472970288323199758237696/44322727168125:ℝ),(30088751631707614776131584/44322727168125:ℝ)]]
theorem admission037_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218924481535997/630367675280000:ℝ) admission037_02_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission037_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission037_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (471/1024:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission037_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission037_02_coefficients]
def admission037_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(71238047934694912163840/70916363469:ℝ),(638264398972990372446208/212749090407:ℝ),(635390070628446535417856/212749090407:ℝ),(210839815459540899463168/212749090407:ℝ)],
![(141995358935165754671104/70916363469:ℝ),(1272203399033212702294016/212749090407:ℝ),(1266455999432333612548096/212749090407:ℝ),(420238677204618174267392/212749090407:ℝ)],
![(70757311000470842507264/70916363469:ℝ),(90562714294317475692544/30392727201:ℝ),(631065928803887077130240/212749090407:ℝ),(209398861745077274804224/212749090407:ℝ)]]
theorem admission037_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (24377235880247/48412237461504:ℝ) admission037_03_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission037_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission037_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (471/1024:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission037_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission037_03_coefficients]
def admission037_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2358619795462185730367488/14774242389375:ℝ),(93649655853136301826048/196989898525:ℝ),(6971712794977185109639168/14774242389375:ℝ),(2306608401454148203053056/14774242389375:ℝ)],
![(4746954420204093332922368/14774242389375:ℝ),(4712086931496194427281408/4924747463125:ℝ),(4677302241236041940860928/4924747463125:ℝ),(4642600349423635873660928/14774242389375:ℝ)],
![(477666924948381520510976/2954848477875:ℝ),(2370845535167786881630208/4924747463125:ℝ),(7060193928730940712943616/14774242389375:ℝ),(778663982656495890202624/4924747463125:ℝ)]]
theorem admission037_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (103113430803454587/1290992998973440000:ℝ) admission037_04_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission037_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission037_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (471/1024:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission037_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission037_04_coefficients]
def admission037_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(819686584840753290887168/8864545433625:ℝ),(12301866800946129510465536/44322727168125:ℝ),(12308256263532428577120256/44322727168125:ℝ),(273654825786004368072704/2954848477875:ℝ)],
![(1606527252130849082564608/8864545433625:ℝ),(964484210857674351173632/1772909086725:ℝ),(4825188698412492709445632/8864545433625:ℝ),(107286326416998002409472/590969695575:ℝ)],
![(157368133458019158335488/1772909086725:ℝ),(11810238470495729268875264/44322727168125:ℝ),(11817687228530034970107904/44322727168125:ℝ),(87592268766328547991552/984949492625:ℝ)]]
theorem admission037_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (19209977228762104289/423032585903616819200:ℝ) admission037_05_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission037_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission037_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (471/1024:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission037_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission037_05_coefficients]
def admission037_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1002502510083093635998238308456456192/4307357233418767486494375:ℝ),(5347677647056286503347488583730683904/7753243020153781475689875:ℝ),(26410847838107666466806858828933496832/38766215100768907378449375:ℝ),(1738995985986281696587352137277636608/7753243020153781475689875:ℝ)],
![(19204955351057470030789130602160128/41022449842083499871375:ℝ),(290737112644820152206362151096098816/209547108652804904748375:ℝ),(10625993705589112397468239896997003264/7753243020153781475689875:ℝ),(3498456190739940091840785990249611264/7753243020153781475689875:ℝ)],
![(1014017801777940717234620404770357248/4307357233418767486494375:ℝ),(5409595520802059128287911006824972288/7753243020153781475689875:ℝ),(26719120689837895520534340656051519488/38766215100768907378449375:ℝ),(1759460204753658395253433852971974656/7753243020153781475689875:ℝ)]]
theorem admission037_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (25913059502635623463799836297/225829570919465876795916288000:ℝ) admission037_06_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission037_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission037_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (471/1024:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission037_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission037_06_coefficients]
def admission037_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(507413598001028269645950250604732416/1047735543264024523741875:ℝ),(302819438988933205642716300981182464/209547108652804904748375:ℝ),(501989922508115477513619863920181248/349245181088008174580625:ℝ),(99857234116141734794645667491872768/209547108652804904748375:ℝ)],
![(201397814309739641987697399916453888/209547108652804904748375:ℝ),(600948783147442655003204627092791296/209547108652804904748375:ℝ),(39847371109504834063716465734844416/13969807243520326983225:ℝ),(198159597804869497940239758846328832/209547108652804904748375:ℝ)],
![(499575473547669940292536748977537024/1047735543264024523741875:ℝ),(298129344158509449360488326111608832/209547108652804904748375:ℝ),(494194355229505374079291779450929152/349245181088008174580625:ℝ),(98302363688727763145594091354456064/209547108652804904748375:ℝ)]]
theorem admission037_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (732409683530984544348672713/3051750958371160497242112000:ℝ) admission037_07_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission037_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission037_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (471/1024:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission037_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission037_07_coefficients]
def admission037_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(32638703356856635255448488354342443516562/6767058475322579027557373046875:ℝ),(3834699391068634464201344712307079992987214/255794810367193487241668701171875:ℝ),(2204479033796427069310975582952013352575506/142108227981774159578704833984375:ℝ),(6835515597322157982461083891211981564123702/1278974051835967436208343505859375:ℝ)],
![(529083961651066619638650996798104330029352/47369409327258053192901611328125:ℝ),(44154442408561132778928326186927610003248192/1278974051835967436208343505859375:ℝ),(1683413101162022414557297643288149263140876/47369409327258053192901611328125:ℝ),(15582950828323790406544566176743211231097964/1278974051835967436208343505859375:ℝ)],
![(300613038153070172850511578317707225413418/47369409327258053192901611328125:ℝ),(24980945453217960457921602625392210038312122/1278974051835967436208343505859375:ℝ),(2845760269689640174360917346912434436847122/142108227981774159578704833984375:ℝ),(8747435231001632424083482285531229666974262/1278974051835967436208343505859375:ℝ)]]
theorem admission037_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (146874165105854858649518197594540995824529/59523675835658444746208051200000000000000000:ℝ) admission037_08_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission037_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission037_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (471/1024:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission037_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission037_08_coefficients]
def admission037_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(37053748368429167030715866487730701470624/2046358482937547897933349609375:ℝ),(4039780237656513683100937189797030191488/75791054923612885108642578125:ℝ),(106991365910675482524454454540796720873472/2046358482937547897933349609375:ℝ),(777134802220319966034865129608473214976/45474632954167731065185546875:ℝ)],
![(14137923861914969996462848078902557716448/409271696587509579586669921875:ℝ),(4621197417292817588439586223481338974592/45474632954167731065185546875:ℝ),(40769527408088099643292418211488153829376/409271696587509579586669921875:ℝ),(493210438244981042147734855225230491648/15158210984722577021728515625:ℝ)],
![(33635870941145682951598373906782087111616/2046358482937547897933349609375:ℝ),(1569520910499220984699302792573657756928/32481880681548379332275390625:ℝ),(96856271129765015692007636516644048273408/2046358482937547897933349609375:ℝ),(702496512514623160408339436067218259968/45474632954167731065185546875:ℝ)]]
theorem admission037_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (1004929322025236836063870576954677/127156289932131687385088000000000000:ℝ) admission037_09_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission037_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission037_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (471/1024:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission037_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission037_09_coefficients]
def admission037_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(420264854927114412501058120648/86567826500244140625:ℝ),(1231963884838095369814832108552/86567826500244140625:ℝ),(240635671518827738870788596032/17313565300048828125:ℝ),(43497723536502118351685443584/9618647388916015625:ℝ)],
![(17722477983120873314517302752/1923729477783203125:ℝ),(37071194962763985691256982688/1374092484130859375:ℝ),(253169337828324806469275716352/9618647388916015625:ℝ),(82283404186417210703063351296/9618647388916015625:ℝ)],
![(376941453561636419086387339808/86567826500244140625:ℝ),(1102610864030546160792542370592/86567826500244140625:ℝ),(214888040209448797731847044352/17313565300048828125:ℝ),(38752330786329673272564465664/9618647388916015625:ℝ)]]
theorem admission037_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (21287291081357852749821789/10327943991787520000000000000:ℝ) admission037_10_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission037_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission037_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (471/1024:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission037_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission037_10_coefficients]
def admission037_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(138750107576303975008110376190418944/349245181088008174580625:ℝ),(1242087704449852781485378304434069504/1047735543264024523741875:ℝ),(247087985998573794653729161861922816/209547108652804904748375:ℝ),(136534182757309372269199544482267136/349245181088008174580625:ℝ)],
![(275303467364245162189816299122581504/349245181088008174580625:ℝ),(2464459465179332333655317078246137856/1047735543264024523741875:ℝ),(2451218571402358269556733966293139456/1047735543264024523741875:ℝ),(270889836105253807490288595138248704/349245181088008174580625:ℝ)],
![(27310671957588237436341184586432512/69849036217601634916125:ℝ),(1222371760729479552169938773812068352/1047735543264024523741875:ℝ),(1215778641409489296288088156983525376/1047735543264024523741875:ℝ),(134355653347944435221089050655981568/349245181088008174580625:ℝ)]]
theorem admission037_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (1001027623921218776860006531/5086251597285267495403520000:ℝ) admission037_11_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission037_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission037_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (471/1024:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission037_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission037_11_coefficients]
def admission037_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(176669076292854874112/10986328125:ℝ),(176669076292854874112/3662109375:ℝ),(176669076292854874112/3662109375:ℝ),(176669076292854874112/10986328125:ℝ)],
![(353338152585709748224/10986328125:ℝ),(353338152585709748224/3662109375:ℝ),(353338152585709748224/3662109375:ℝ),(353338152585709748224/10986328125:ℝ)],
![(176669076292854874112/10986328125:ℝ),(176669076292854874112/3662109375:ℝ),(176669076292854874112/3662109375:ℝ),(176669076292854874112/10986328125:ℝ)]]
theorem admission037_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (41133974747/5000000000000:ℝ) admission037_12_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission037_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission037_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (471/1024:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission037_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission037_12_coefficients]
def admission037_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6217204408677518278656/762939453125:ℝ),(18651613226032554835968/762939453125:ℝ),(18651613226032554835968/762939453125:ℝ),(6217204408677518278656/762939453125:ℝ)],
![(12434408817355036557312/762939453125:ℝ),(37303226452065109671936/762939453125:ℝ),(37303226452065109671936/762939453125:ℝ),(12434408817355036557312/762939453125:ℝ)],
![(6217204408677518278656/762939453125:ℝ),(18651613226032554835968/762939453125:ℝ),(18651613226032554835968/762939453125:ℝ),(6217204408677518278656/762939453125:ℝ)]]
theorem admission037_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (208448021404809/50000000000000000:ℝ) admission037_13_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission037_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission037_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (471/1024:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission037_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission037_13_coefficients]
def admission037_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8796093022208/9:ℝ),(8796093022208/3:ℝ),(8796093022208/3:ℝ),(8796093022208/9:ℝ)],
![(17592186044416/9:ℝ),(17592186044416/3:ℝ),(17592186044416/3:ℝ),(17592186044416/9:ℝ)],
![(8796093022208/9:ℝ),(8796093022208/3:ℝ),(8796093022208/3:ℝ),(8796093022208/9:ℝ)]]
theorem admission037_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission037_14_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission037_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission037_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (471/1024:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission037_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission037_14_coefficients]
theorem admission037_all {δ p : ℝ}
 (hd : δ∈Set.Icc (471/1024:ℝ) (237/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission037_00_pos hd hp
 · exact admission037_01_pos hd hp
 · exact admission037_02_pos hd hp
 · exact admission037_03_pos hd hp
 · exact admission037_04_pos hd hp
 · exact admission037_05_pos hd hp
 · exact admission037_06_pos hd hp
 · exact admission037_07_pos hd hp
 · exact admission037_08_pos hd hp
 · exact admission037_09_pos hd hp
 · exact admission037_10_pos hd hp
 · exact admission037_11_pos hd hp
 · exact admission037_12_pos hd hp
 · exact admission037_13_pos hd hp
 · exact admission037_14_pos hd hp
end
end DasStageAFinite
#print axioms DasStageAFinite.admission037_all
