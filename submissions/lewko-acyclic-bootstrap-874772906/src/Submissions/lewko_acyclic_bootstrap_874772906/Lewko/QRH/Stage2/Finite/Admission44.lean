/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Finite.ReturnFormulas
set_option autoImplicit false
namespace LewkoStage2Finite
noncomputable section
def admission44_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(801543869193840483/52465400575843:ℝ),(2404274211379793920/157396201727529:ℝ)]]
theorem admission44_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (586981008637645/629584806910116:ℝ) admission44_00_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission44_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_00_coefficients]
def admission44_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(586593123034611712/52465400575843:ℝ),(1759579369103835136/157396201727529:ℝ)]]
theorem admission44_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (107396201727529/157396201727529:ℝ) admission44_01_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission44_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_01_coefficients]
def admission44_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(298447864373120426/52465400575843:ℝ),(298415788989202432/52465400575843:ℝ)]]
theorem admission44_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (18213854308423/52465400575843:ℝ) admission44_02_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission44_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_02_coefficients]
def admission44_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(467205988986460611360555008/157396201727529:ℝ),(8408811272275094467633905664/1416565815547761:ℝ),(4203957389414948965388910592/1416565815547761:ℝ)],
![(467156033979664884612087808/157396201727529:ℝ),(8407912088431357064226979840/1416565815547761:ℝ),(4203507800634173102718189568/1416565815547761:ℝ)]]
theorem admission44_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (62637147316845850687/123781409716984086528:ℝ) admission44_03_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission44_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_03_coefficients]
def admission44_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(24479272503665628175026500/52465400575843:ℝ),(48949939838020493848576000/52465400575843:ℝ),(24470667655429458692669440/52465400575843:ℝ)],
![(24484162607577625686202094/52465400575843:ℝ),(48959719186187215068479488/52465400575843:ℝ),(24475556899716257785315328/52465400575843:ℝ)]]
theorem admission44_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (273481022440971345/3438372492138446848:ℝ) admission44_04_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission44_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_04_coefficients]
def admission44_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(16246783156745193245504751647/59023575647823375:ℝ),(32493912015742035365157148646/59023575647823375:ℝ),(5415709561800116657714154833/19674525215941125:ℝ)],
![(16236600381269851502516475917/59023575647823375:ℝ),(162367737486407791398955547518/295117878239116875:ℝ),(27061578237329787206428263061/98372626079705625:ℝ)]]
theorem admission44_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (16236600381269851502516475917/346117907934390148040491008000:ℝ) admission44_05_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission44_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_05_coefficients]
def admission44_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(90586939364680564099691605653623107884026429440/8249596917978249986997496465053:ℝ),(271707686918956211229516808568210992086650060800/8249596917978249986997496465053:ℝ),(271654559905212961758013701361084162784792412160/8249596917978249986997496465053:ℝ),(90533812350847160721510325801188278582168780800/8249596917978249986997496465053:ℝ)],
![(2448747293292835024117585460598071990642016256/222962078864277026675608012569:ℝ),(271757815036541560585470363452654321749521793024/8249596917978249986997496465053:ℝ),(271704684679198066457521570901996345021559734272/8249596917978249986997496465053:ℝ),(90550519494401238851339413312431886925792542720/8249596917978249986997496465053:ℝ)]]
theorem admission44_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (41170011332199992794590037101983525/360430389077748394098578618889142272:ℝ) admission44_06_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission44_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_06_coefficients]
def admission44_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(105867345938805478856733295356134917639420/74320692954759008891869337523:ℝ),(211707584010262526909456345262479769763840/74320692954759008891869337523:ℝ),(105840238916899051169418130542378793041920/74320692954759008891869337523:ℝ)],
![(105841513588943453602020247860138498998002/74320692954759008891869337523:ℝ),(211655922618617203666162265080101144150016/74320692954759008891869337523:ℝ),(105814409875012580597405907947851171758080/74320692954759008891869337523:ℝ)]]
theorem admission44_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (788378789089713846127732902376735/3247120622322057604491699269271552:ℝ) admission44_07_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission44_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_07_coefficients]
def admission44_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(647109221555931189935061238010868279299027997992103143927429/2721705064261194173286230622180175781250000000:ℝ),(1942443569492425874946155462985988219720258215698055110639903/2721705064261194173286230622180175781250000000:ℝ),(388711891497000241576456571642415467333927394045356702141053/544341012852238834657246124436035156250000000:ℝ),(648225109543062601025114463499089408192443134883355958055291/2721705064261194173286230622180175781250000000:ℝ)],
![(325115425619052702857543824244097205770303053769016500387247/1360852532130597086643115311090087890625000000:ℝ),(4879518862860689059553844668773672974678232849092500707928813/6804262660652985433215576555450439453125000000:ℝ),(9764612599000684408071838609155443289383615700585578493920821/13608525321305970866431153110900878906250000000:ℝ),(651345825888522197813507061926117932650106859649640115605883/2721705064261194173286230622180175781250000000:ℝ)]]
theorem admission44_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (647109221555931189935061238010868279299027997992103143927429/261492691482007593575999082468532754684313600000000000000000000:ℝ) admission44_08_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission44_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_08_coefficients]
def admission44_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(357684234715267689912447833794996062924945805877188/435472810281791067725796899548828125:ℝ),(1072707411236070167599406361099808198274657333949568/435472810281791067725796899548828125:ℝ),(1072362130296791317599215295849765532586455959863296/435472810281791067725796899548828125:ℝ),(357338953776713104079565104440586719915578455228416/435472810281791067725796899548828125:ℝ)],
![(357135498715750515186358713211041108191298860602798/435472810281791067725796899548828125:ℝ),(5355306768654567798486799585915916488684090734290624/2177364051408955338628984497744140625:ℝ),(5353581116379511756729830775171124478583480547016704/2177364051408955338628984497744140625:ℝ),(356790368261463643356335955123140168043085655179264/435472810281791067725796899548828125:ℝ)]]
theorem admission44_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (166143462183635515792451778018446717431343/19482723733932345626950195615629312000000000:ℝ) admission44_09_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission44_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_09_coefficients]
def admission44_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(65820478265367200792054750894795947933696/13833650542458603515625:ℝ),(197383449001427563212595636299293464690688/13833650542458603515625:ℝ),(197305465181785450939562973418263085580288/13833650542458603515625:ℝ),(65742494445844858951053338013765568823296/13833650542458603515625:ℝ)],
![(131528250338239669049241917084214580314112/13833650542458603515625:ℝ),(394428804624575414496604642452213611134976/13833650542458603515625:ℝ),(394272862183004863602978854869921081327616/13833650542458603515625:ℝ),(131372307896908682949834879501922050506752/13833650542458603515625:ℝ)],
![(21902586500544951504889914371941344796672/4611216847486201171875:ℝ),(65681772637576904556428010122555797184512/4611216847486201171875:ℝ),(65655786431365936672790103036072199979008/4611216847486201171875:ℝ),(21876600294373915075712944785457747591168/4611216847486201171875:ℝ)]]
theorem admission44_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (2546771463748756222859134989029/1126685898223926263152640000000000:ℝ) admission44_10_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission44_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_10_coefficients]
def admission44_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(28939879275899445371130420304898626223020/24773564318253002963956445841:ℝ),(173617108719677556780746332063562620272640/74320692954759008891869337523:ℝ),(9644163522416246848011239428455021936640/8257854772751000987985481947:ℝ)],
![(28932640613623097404089063920021975498842/24773564318253002963956445841:ℝ),(173573679580873135480687241101416122908672/74320692954759008891869337523:ℝ),(9641750949962678634828447461858229616640/8257854772751000987985481947:ℝ)]]
theorem admission44_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (143673285096327642125315181342635/721582360516012800998155393171456:ℝ) admission44_11_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission44_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_11_coefficients]
def admission44_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(41135459/5000000000:ℝ)]]
theorem admission44_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission44_12_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission44_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_12_coefficients]
def admission44_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(4070076386348412471/1000000000000000000000:ℝ)]]
theorem admission44_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (4070076386348412471/1000000000000000000000:ℝ) admission44_13_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission44_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_13_coefficients]
def admission44_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(1/2:ℝ)]]
theorem admission44_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission44_14_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission44_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_14_coefficients]
theorem admission44_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission44_00_pos hδ hp
 · exact admission44_01_pos hδ hp
 · exact admission44_02_pos hδ hp
 · exact admission44_03_pos hδ hp
 · exact admission44_04_pos hδ hp
 · exact admission44_05_pos hδ hp
 · exact admission44_06_pos hδ hp
 · exact admission44_07_pos hδ hp
 · exact admission44_08_pos hδ hp
 · exact admission44_09_pos hδ hp
 · exact admission44_10_pos hδ hp
 · exact admission44_11_pos hδ hp
 · exact admission44_12_pos hδ hp
 · exact admission44_13_pos hδ hp
 · exact admission44_14_pos hδ hp
#print axioms admission44_all
end
end LewkoStage2Finite
