/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def admission009_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6215350407257051365376/3376969689:ℝ),(390338399179877606490112/70916363469:ℝ),(389109722702560976961536/70916363469:ℝ),(129293682075081449144320/70916363469:ℝ)],
![(12430700814514102730752/3376969689:ℝ),(780676798359755212980224/70916363469:ℝ),(778219445405121953923072/70916363469:ℝ),(258587364150162898288640/70916363469:ℝ)],
![(6215350407257051365376/3376969689:ℝ),(390338399179877606490112/70916363469:ℝ),(389109722702560976961536/70916363469:ℝ),(129293682075081449144320/70916363469:ℝ)]]
theorem admission009_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (29397979705/31518383764:ℝ) admission009_00_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission009_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission009_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission009_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission009_00_coefficients]
def admission009_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(13618006772173879902208/10130909067:ℝ),(285290947448291477946368/70916363469:ℝ),(284603752680931477946368/70916363469:ℝ),(31546284212619053105152/23638787823:ℝ)],
![(27236013544347759804416/10130909067:ℝ),(570581894896582955892736/70916363469:ℝ),(569207505361862955892736/70916363469:ℝ),(63092568425238106210304/23638787823:ℝ)],
![(13618006772173879902208/10130909067:ℝ),(285290947448291477946368/70916363469:ℝ),(284603752680931477946368/70916363469:ℝ),(31546284212619053105152/23638787823:ℝ)]]
theorem admission009_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (5379595941/7879595941:ℝ) admission009_01_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission009_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission009_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission009_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission009_01_coefficients]
def admission009_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4327923860701138600853504/6331818166875:ℝ),(18135937136304711037616128/8864545433625:ℝ),(90472970288323199758237696/44322727168125:ℝ),(30088751631707614776131584/44322727168125:ℝ)],
![(8655847721402277201707008/6331818166875:ℝ),(36271874272609422075232256/8864545433625:ℝ),(180945940576646399516475392/44322727168125:ℝ),(60177503263415229552263168/44322727168125:ℝ)],
![(4327923860701138600853504/6331818166875:ℝ),(18135937136304711037616128/8864545433625:ℝ),(90472970288323199758237696/44322727168125:ℝ),(30088751631707614776131584/44322727168125:ℝ)]]
theorem admission009_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218924481535997/630367675280000:ℝ) admission009_02_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission009_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission009_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission009_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission009_02_coefficients]
def admission009_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(72200359861948774350848/70916363469:ℝ),(646920272337280794886144/212749090407:ℝ),(92005845091414660087808/30392727201:ℝ),(30531674698352592683008/30392727201:ℝ)],
![(143919982789673479045120/70916363469:ℝ),(1289515145761793547173888/212749090407:ℝ),(1283757689455245782941696/212749090407:ℝ),(426002492062472672903168/212749090407:ℝ)],
![(10245660418246386384896/10130909067:ℝ),(642594873424512752287744/212749090407:ℝ),(639716773815343162327040/212749090407:ℝ),(212280769174004524122112/212749090407:ℝ)]]
theorem admission009_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (24712734061061/48412237461504:ℝ) admission009_03_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission009_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission009_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission009_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission009_03_coefficients]
def admission009_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(766175857124659058909184/4924747463125:ℝ),(91263677360062765473792/196989898525:ℝ),(2264696513018066500583424/4924747463125:ℝ),(749280436141156422647808/4924747463125:ℝ)],
![(1542256657342558741880832/4924747463125:ℝ),(4592788006842517609668608/4924747463125:ℝ),(1953808601694593515257856/2110606055625:ℝ),(646438023337468286205952/2110606055625:ℝ)],
![(776080800217899682971648/4924747463125:ℝ),(2311196072840948472823808/4924747463125:ℝ),(1376514134561591021010944/2954848477875:ℝ),(455444970987761747099648/2954848477875:ℝ)]]
theorem admission009_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (100486337025022623/1290992998973440000:ℝ) admission009_04_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission009_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission009_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission009_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission009_04_coefficients]
def admission009_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(885378419942068289306624/8864545433625:ℝ),(13283002596228005500534784/44322727168125:ℝ),(13285154877022278028877824/44322727168125:ℝ),(295269625366974264991744/2954848477875:ℝ)],
![(347582184466695815880704/1772909086725:ℝ),(26074376862005610759479296/44322727168125:ℝ),(26079740719042162450743296/44322727168125:ℝ),(38644082083128653725696/196989898525:ℝ)],
![(121790357484487255728128/1266363633375:ℝ),(1827339180825372179849216/6331818166875:ℝ),(1827797977431412060266496/6331818166875:ℝ),(40627372268565077270528/422121211125:ℝ)]]
theorem admission009_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (14866986997618073209/302166132788297728000:ℝ) admission009_05_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission009_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission009_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission009_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission009_05_coefficients]
def admission009_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(139882766308049441049765181996048384/615336747631252498070625:ℝ),(746113066382493742226041312217079808/1107606145736254496527125:ℝ),(3684526142029721601697054713041649664/5538030728681272482635625:ℝ),(242581078350218328465026957984137216/1107606145736254496527125:ℝ)],
![(656624673335846418644364881419526144/1435785744472922495498125:ℝ),(10507500803100685016105000794133405696/7753243020153781475689875:ℝ),(51891638840146331477486247809701117952/38766215100768907378449375:ℝ),(3416599315670433297176459127472259072/7753243020153781475689875:ℝ)],
![(26775531239221436988776712710438912/116415060362669391526875:ℝ),(1056941867684645764104542321722769408/1550648604030756295137975:ℝ),(26099955845938280265606864818409570304/38766215100768907378449375:ℝ),(343706353443780999584254084316659712/1550648604030756295137975:ℝ)]]
theorem admission009_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (3614739751073991186395689219/32261367274209410970845184000:ℝ) admission009_06_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission009_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission009_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission009_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission009_06_coefficients]
def admission009_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(523217391540321870569088495739346944/1047735543264024523741875:ℝ),(312250595746144400877318743634976768/209547108652804904748375:ℝ),(517623487348416174760416440423022592/349245181088008174580625:ℝ),(102966974970969678092748819766706176/209547108652804904748375:ℝ)],
![(1038596658627285411784763489851498496/1047735543264024523741875:ℝ),(88544442380266435067487073200054272/29935301236114986392625:ℝ),(1027451407418222246086504796376793088/349245181088008174580625:ℝ),(29197011359217912076635151913713664/29935301236114986392625:ℝ)],
![(515379267086963541215674994112151552/1047735543264024523741875:ℝ),(307560500915720644595090768765403136/209547108652804904748375:ℝ),(509827920069806071326088355953770496/349245181088008174580625:ℝ),(101412104543555706443697243629289472/209547108652804904748375:ℝ)]]
theorem admission009_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (755579058405426937667259899/3051750958371160497242112000:ℝ) admission009_07_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission009_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission009_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission009_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission009_07_coefficients]
def admission009_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(84186694187848994663395098805776863020966/47369409327258053192901611328125:ℝ),(1526145107593192679090299439950479848124854/255794810367193487241668701171875:ℝ),(312637384671633906077969134727303729947918/47369409327258053192901611328125:ℝ),(3083511253978241423339586945149735675785598/1278974051835967436208343505859375:ℝ)],
![(240515503030771715389162357448863846839416/47369409327258053192901611328125:ℝ),(21068899573806714927817873463361608554624592/1278974051835967436208343505859375:ℝ),(2517105543923016541517756572324243463959124/142108227981774159578704833984375:ℝ),(1154134591662279612614510326374102779203108/182710578833709633744049072265625:ℝ)],
![(6253152353716908829030690345723479352738/1894776373090322127716064453125:ℝ),(13438174035840751532366376263609209314000322/1278974051835967436208343505859375:ℝ),(315838677981622964656769833628466454823074/28421645596354831915740966796875:ℝ),(4995430887657715864961985339468983778636158/1278974051835967436208343505859375:ℝ)]]
theorem admission009_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (378840123845320475985277944625995883594347/416665730849609113223456358400000000000000000:ℝ) admission009_08_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission009_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission009_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission009_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission009_08_coefficients]
def admission009_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(44007812004050390840798524392812212955936/2046358482937547897933349609375:ℝ),(14410969379698613506137808848655387028096/227373164770838655325927734375:ℝ),(127379406813779212335079789381268573421568/2046358482937547897933349609375:ℝ),(132344483090244796755416645241569017856/6496376136309675866455078125:ℝ)],
![(84597746580817297602479556204675811552864/2046358482937547897933349609375:ℝ),(565086620814739446038120932161944648576/4640268668792625618896484375:ℝ),(244623718846647957837712760738384474243072/2046358482937547897933349609375:ℝ),(1778184473557730348949307339840711294976/45474632954167731065185546875:ℝ)],
![(40589934576766906761681031811863598596928/2046358482937547897933349609375:ℝ),(4426091680074539783243372275759966917376/75791054923612885108642578125:ℝ),(117244312032868745502632971357115900821504/2046358482937547897933349609375:ℝ),(283924363975338923887130274383242723328/15158210984722577021728515625:ℝ)]]
theorem admission009_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (1218471181763672978870474085545151/127156289932131687385088000000000000:ℝ) admission009_09_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission009_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission009_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission009_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission009_09_coefficients]
def admission009_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(11196405966350347859440583208/1923729477783203125:ℝ),(164479640194447411506991917832/9618647388916015625:ℝ),(161019201878047985491328212544/9618647388916015625:ℝ),(52521610946651141406539210752/9618647388916015625:ℝ)],
![(967099942371249522027480178336/86567826500244140625:ℝ),(2839475306761910309579903654816/86567826500244140625:ℝ),(2777756813579834210041929274624/86567826500244140625:ℝ),(100597977915398609443278422016/9618647388916015625:ℝ)],
![(66136639019113628683831538656/12366832357177734375:ℝ),(194035430175199148296451566304/12366832357177734375:ℝ),(37933671853253193297419203328/2473366471435546875:ℝ),(6863288157880292708275109888/1374092484130859375:ℝ)]]
theorem admission009_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (3770116785944985008207763/1475420570255360000000000000:ℝ) admission009_10_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission009_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission009_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission009_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission009_10_coefficients]
def admission009_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(143180039911025252217507201570873344/349245181088008174580625:ℝ),(1281737949962776831881147538048933888/1047735543264024523741875:ℝ),(1274871554957818814324887529740828672/1047735543264024523741875:ℝ),(140891241576039246365420532134838272/349245181088008174580625:ℝ)],
![(284163332033687716608609949883490304/349245181088008174580625:ℝ),(363394279457882919206693649353695232/149676506180574931963125:ℝ),(506016364266451590333843481431113728/209547108652804904748375:ℝ),(39943421963244793668961510063341568/49892168726858310654375:ℝ)],
![(28196658424532492878220549662523392/69849036217601634916125:ℝ),(1262022006242403602565708007426932736/1047735543264024523741875:ℝ),(1255210266374439137344329877414739968/1047735543264024523741875:ℝ),(138712712166674309317310038308552704/349245181088008174580625:ℝ)]]
theorem admission009_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (1033490241815703431645855593/5086251597285267495403520000:ℝ) admission009_11_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission009_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission009_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission009_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission009_11_coefficients]
def admission009_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(176669076292854874112/10986328125:ℝ),(176669076292854874112/3662109375:ℝ),(176669076292854874112/3662109375:ℝ),(176669076292854874112/10986328125:ℝ)],
![(353338152585709748224/10986328125:ℝ),(353338152585709748224/3662109375:ℝ),(353338152585709748224/3662109375:ℝ),(353338152585709748224/10986328125:ℝ)],
![(176669076292854874112/10986328125:ℝ),(176669076292854874112/3662109375:ℝ),(176669076292854874112/3662109375:ℝ),(176669076292854874112/10986328125:ℝ)]]
theorem admission009_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (41133974747/5000000000000:ℝ) admission009_12_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission009_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission009_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission009_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission009_12_coefficients]
def admission009_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6217204408677518278656/762939453125:ℝ),(18651613226032554835968/762939453125:ℝ),(18651613226032554835968/762939453125:ℝ),(6217204408677518278656/762939453125:ℝ)],
![(12434408817355036557312/762939453125:ℝ),(37303226452065109671936/762939453125:ℝ),(37303226452065109671936/762939453125:ℝ),(12434408817355036557312/762939453125:ℝ)],
![(6217204408677518278656/762939453125:ℝ),(18651613226032554835968/762939453125:ℝ),(18651613226032554835968/762939453125:ℝ),(6217204408677518278656/762939453125:ℝ)]]
theorem admission009_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (208448021404809/50000000000000000:ℝ) admission009_13_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission009_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission009_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission009_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission009_13_coefficients]
def admission009_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8796093022208/9:ℝ),(8796093022208/3:ℝ),(8796093022208/3:ℝ),(8796093022208/9:ℝ)],
![(17592186044416/9:ℝ),(17592186044416/3:ℝ),(17592186044416/3:ℝ),(17592186044416/9:ℝ)],
![(8796093022208/9:ℝ),(8796093022208/3:ℝ),(8796093022208/3:ℝ),(8796093022208/9:ℝ)]]
theorem admission009_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission009_14_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission009_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission009_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission009_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission009_14_coefficients]
theorem admission009_all {δ p : ℝ}
 (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission009_00_pos hd hp
 · exact admission009_01_pos hd hp
 · exact admission009_02_pos hd hp
 · exact admission009_03_pos hd hp
 · exact admission009_04_pos hd hp
 · exact admission009_05_pos hd hp
 · exact admission009_06_pos hd hp
 · exact admission009_07_pos hd hp
 · exact admission009_08_pos hd hp
 · exact admission009_09_pos hd hp
 · exact admission009_10_pos hd hp
 · exact admission009_11_pos hd hp
 · exact admission009_12_pos hd hp
 · exact admission009_13_pos hd hp
 · exact admission009_14_pos hd hp
end
end DasStageAFinite
#print axioms DasStageAFinite.admission009_all
