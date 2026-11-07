/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnA.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageAFinite
noncomputable section
def admission027_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(14745696847008495675899904/7879595941:ℝ),(397819273691036326089981952/70916363469:ℝ),(397504732512843268930666496/70916363469:ℝ),(132396730444883403923783680/70916363469:ℝ)],
![(29491393694016991351799808/7879595941:ℝ),(795638547382072652179963904/70916363469:ℝ),(795009465025686537861332992/70916363469:ℝ),(264793460889766807847567360/70916363469:ℝ)],
![(14745696847008495675899904/7879595941:ℝ),(397819273691036326089981952/70916363469:ℝ),(397504732512843268930666496/70916363469:ℝ),(132396730444883403923783680/70916363469:ℝ)]]
theorem admission027_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (29397979705/31518383764:ℝ) admission027_00_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission027_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission027_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission027_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission027_00_coefficients]
def admission027_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(97086106961609891139026944/70916363469:ℝ),(291082399024385513417080832/70916363469:ℝ),(290906477163941353417080832/70916363469:ℝ),(32303395033721910379675648/23638787823:ℝ)],
![(194172213923219782278053888/70916363469:ℝ),(582164798048771026834161664/70916363469:ℝ),(581812954327882706834161664/70916363469:ℝ),(64606790067443820759351296/23638787823:ℝ)],
![(97086106961609891139026944/70916363469:ℝ),(291082399024385513417080832/70916363469:ℝ),(290906477163941353417080832/70916363469:ℝ),(32303395033721910379675648/23638787823:ℝ)]]
theorem admission027_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (5379595941/7879595941:ℝ) admission027_01_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission027_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission027_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission027_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission027_01_coefficients]
def admission027_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6172760162305577704159707136/8864545433625:ℝ),(92538483293924374572355813376/44322727168125:ℝ),(92485564153265083582316019712/44322727168125:ℝ),(30810881670868597530758742016/44322727168125:ℝ)],
![(12345520324611155408319414272/8864545433625:ℝ),(185076966587848749144711626752/44322727168125:ℝ),(184971128306530167164632039424/44322727168125:ℝ),(61621763341737195061517484032/44322727168125:ℝ)],
![(6172760162305577704159707136/8864545433625:ℝ),(92538483293924374572355813376/44322727168125:ℝ),(92485564153265083582316019712/44322727168125:ℝ),(30810881670868597530758742016/44322727168125:ℝ)]]
theorem admission027_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218924481535997/630367675280000:ℝ) admission027_02_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission027_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission027_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission027_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission027_02_coefficients]
def admission027_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(24070592517656572390801408/23638787823:ℝ),(649170400418788184084709376/212749090407:ℝ),(648435038790448913617780736/212749090407:ℝ),(215899971030569881050284032/212749090407:ℝ)],
![(48100188842312020636205056/23638787823:ℝ),(1297233984835166085639569408/212749090407:ℝ),(1295763343164594974101602304/212749090407:ℝ),(431431057910237074187878400/212749090407:ℝ)],
![(8009865441551816081801216/7879595941:ℝ),(648063584416377901554860032/212749090407:ℝ),(647328304374146060483821568/212749090407:ℝ),(215531086879667193137594368/212749090407:ℝ)]]
theorem admission027_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (98012190792209/193648949846016:ℝ) admission027_03_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission027_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission027_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission027_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission027_03_coefficients]
def admission027_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3782258200164955951857664/23638787823:ℝ),(3775199245795680162283520/7879595941:ℝ),(11304433491185536382009344/23638787823:ℝ),(3761093953963451847016448/23638787823:ℝ)],
![(4735366102360323347620954112/14774242389375:ℝ),(4726535350444359334863699968/4924747463125:ℝ),(4717709859778332123144912896/4924747463125:ℝ),(4708889630362241712464592896/14774242389375:ℝ)],
![(2371454727257225877709914112/14774242389375:ℝ),(2367035821822059233436499968/4924747463125:ℝ),(7087858647344036130678898688/14774242389375:ℝ),(786068636378361436026437632/4924747463125:ℝ)]]
theorem admission027_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (656773444607991/8262355193430016:ℝ) admission027_04_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission027_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission027_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission027_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission027_04_coefficients]
def admission027_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(599837018812988626891177984/6331818166875:ℝ),(12597986965539724212384825344/44322727168125:ℝ),(12599385162392131140277633024/44322727168125:ℝ),(466695258727036368459005952/4924747463125:ℝ)],
![(238739397949610466305769472/1266363633375:ℝ),(25070523684156130902475669504/44322727168125:ℝ),(1002935512727050692539973632/1772909086725:ℝ),(2786247687418834243908534272/14774242389375:ℝ)],
![(593859970935063704637669376/6331818166875:ℝ),(2494507343723281338018168832/8864545433625:ℝ),(12474002655784136173221707776/44322727168125:ℝ),(1386161911237725138531516416/14774242389375:ℝ)]]
theorem admission027_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (4530792014580258977033/96693162492255272960000:ℝ) admission027_05_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission027_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission027_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission027_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission027_05_coefficients]
def admission027_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(596510222935294159651364202614659612672/2584414340051260491896625:ℝ),(5351914125460605368468191524026103758848/7753243020153781475689875:ℝ),(5335257093507055777942972125927798996992/7753243020153781475689875:ℝ),(354574725928655961003534641949134815232/1550648604030756295137975:ℝ)],
![(5973861603927085768391911550514645827584/12922071700256302459483125:ℝ),(53597891590809351152953723795411681017856/38766215100768907378449375:ℝ),(53431237347631337331026595437413236998144/38766215100768907378449375:ℝ),(507283728470144006413409048387014098944/1107606145736254496527125:ℝ)],
![(2991310489250614970135090537441347764224/12922071700256302459483125:ℝ),(26838320963506324310612766175281162223616/38766215100768907378449375:ℝ),(26754951880096058441311734807774242013184/38766215100768907378449375:ℝ),(1778112469647728239876190128963424616448/7753243020153781475689875:ℝ)]]
theorem admission027_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (20638965415340845997185367273/180663656735572701436733030400:ℝ) admission027_06_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission027_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission027_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission027_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission027_06_coefficients]
def admission027_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2095341963885957908758266681959776256/4276471605159283770375:ℝ),(43942444568660761665453488625638834176/29935301236114986392625:ℝ),(20478610899009502037249101098341367808/13969807243520326983225:ℝ),(102253807734929136429717163511677714432/209547108652804904748375:ℝ)],
![(20912719445297695525220572600504549376/21382358025796418851875:ℝ),(438570324102909361075446867574455402496/149676506180574931963125:ℝ),(1021938953034326642459568544419116220416/349245181088008174580625:ℝ),(40821913728088059223455424706435350528/41909421730560980949675:ℝ)],
![(10436009625867905981429239190705668096/21382358025796418851875:ℝ),(31265443037086507535454203492323033088/21382358025796418851875:ℝ),(10407626133858961051598796264501673984/7127452675265472950625:ℝ),(2078688998071656320154284898377531392/4276471605159283770375:ℝ)]]
theorem admission027_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (60497812172155138109644319/249122527213972285489152000:ℝ) admission027_07_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission027_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission027_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission027_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission027_07_coefficients]
def admission027_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7939122066565622523879010542841861167044992/1740100750797234607086181640625:ℝ),(505236459524969329023261171423377073821258048/36542115766741926748809814453125:ℝ),(396905436651471899908338642543073988992392832/28421645596354831915740966796875:ℝ),(1202544613387785321724310766184227553863342976/255794810367193487241668701171875:ℝ)],
![(3309456492265440766228914394045143498202624/348020150159446921417236328125:ℝ),(5262783944610731246194706550723689017986314048/182710578833709633744049072265625:ℝ),(1377486407389123667356805398520212905966582528/47369409327258053192901611328125:ℝ),(357568501717137104979955475736800087227519232/36542115766741926748809814453125:ℝ)],
![(8608160394761581307265561427383856323968128/1740100750797234607086181640625:ℝ),(2736601646985884601078400693606803648880023808/182710578833709633744049072265625:ℝ),(2147932038910011502528722982845268772937783424/142108227981774159578704833984375:ℝ),(1300434898632174413135377563973373056729291648/255794810367193487241668701171875:ℝ)]]
theorem admission027_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (62024391145043925967804769865952040367539/27210823239158146169695109120000000000000000:ℝ) admission027_08_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission027_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission027_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission027_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission027_08_coefficients]
def admission027_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7270799422266761237228252630159069004416128/409271696587509579586669921875:ℝ),(289381507764071803500676382856397176543232/5456955954500127727822265625:ℝ),(21594887939219769206949080016859689635545088/409271696587509579586669921875:ℝ),(795786037473607645219701892719076572135424/45474632954167731065185546875:ℝ)],
![(14368877244842543157152205054695669554795904/409271696587509579586669921875:ℝ),(71483028462441100916563341826153053162907648/682119494312515965977783203125:ℝ),(213365608857047760990374657838461796875239424/2046358482937547897933349609375:ℝ),(20966195637100758775986842771887891677184/606328439388903080869140625:ℝ)],
![(7098077822575781919923952424536600550379776/409271696587509579586669921875:ℝ),(35310339991932125478978793969103406095003648/682119494312515965977783203125:ℝ),(105391169160948914955629257754163348697513984/2046358482937547897933349609375:ℝ),(776678635308949262979311315172515303653376/45474632954167731065185546875:ℝ)]]
theorem admission027_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (4340030077708601558465387570704419/508625159728526749540352000000000000:ℝ) admission027_09_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission027_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission027_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission027_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission027_09_coefficients]
def admission027_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(408063221665016007077319234075424/86567826500244140625:ℝ),(173815755962616342797161152060896/12366832357177734375:ℝ),(1209233944446080486187868739126272/86567826500244140625:ℝ),(44509653032336166876464989863936/9618647388916015625:ℝ)],
![(89482968848759608610572665457792/9618647388916015625:ℝ),(266791098084806138646199693206656/9618647388916015625:ℝ),(37876279717119036178034662862848/1374092484130859375:ℝ),(87825829433322856023115612291072/9618647388916015625:ℝ)],
![(397264207818539191233399079965824/86567826500244140625:ℝ),(1184351801258868888814247969156224/86567826500244140625:ℝ),(1176913968600195440698807948414976/86567826500244140625:ℝ),(43314042009717222325606562136064/9618647388916015625:ℝ)]]
theorem admission027_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (371767404639678002291163501/165247103868600320000000000000:ℝ) admission027_10_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission027_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission027_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission027_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission027_10_coefficients]
def admission027_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2228266352580672002678193094994034688/5543574302984256739375:ℝ),(180245241870373677419687172694832447488/149676506180574931963125:ℝ),(1260007361885323125042612714559479218176/1047735543264024523741875:ℝ),(139811003143484797203660333549841547264/349245181088008174580625:ℝ)],
![(4447661793966948554665433791628181504/5543574302984256739375:ℝ),(359772439038166300686012664373647376384/149676506180574931963125:ℝ),(2514991902481927339539334806038267297792/1047735543264024523741875:ℝ),(55812860551634434104600876136030797824/69849036217601634916125:ℝ)],
![(317056491626610935998177242376306688/791939186140608105625:ℝ),(179527197167792623266325491678814928896/149676506180574931963125:ℝ),(25611929399930698255035144724056899584/21382358025796418851875:ℝ),(19893328516383910474192006732901777408/49892168726858310654375:ℝ)]]
theorem admission027_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (578972060360943155659828531/2906429484163009997373440000:ℝ) admission027_11_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission027_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission027_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission027_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission027_11_coefficients]
def admission027_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(180909134123883391090688/10986328125:ℝ),(180909134123883391090688/3662109375:ℝ),(180909134123883391090688/3662109375:ℝ),(180909134123883391090688/10986328125:ℝ)],
![(361818268247766782181376/10986328125:ℝ),(361818268247766782181376/3662109375:ℝ),(361818268247766782181376/3662109375:ℝ),(361818268247766782181376/10986328125:ℝ)],
![(180909134123883391090688/10986328125:ℝ),(180909134123883391090688/3662109375:ℝ),(180909134123883391090688/3662109375:ℝ),(180909134123883391090688/10986328125:ℝ)]]
theorem admission027_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (41133974747/5000000000000:ℝ) admission027_12_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission027_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission027_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission027_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission027_12_coefficients]
def admission027_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6366417314485778717343744/762939453125:ℝ),(19099251943457336152031232/762939453125:ℝ),(19099251943457336152031232/762939453125:ℝ),(6366417314485778717343744/762939453125:ℝ)],
![(12732834628971557434687488/762939453125:ℝ),(38198503886914672304062464/762939453125:ℝ),(38198503886914672304062464/762939453125:ℝ),(12732834628971557434687488/762939453125:ℝ)],
![(6366417314485778717343744/762939453125:ℝ),(19099251943457336152031232/762939453125:ℝ),(19099251943457336152031232/762939453125:ℝ),(6366417314485778717343744/762939453125:ℝ)]]
theorem admission027_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (208448021404809/50000000000000000:ℝ) admission027_13_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission027_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission027_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission027_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission027_13_coefficients]
def admission027_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(9007199254740992/9:ℝ),(9007199254740992/3:ℝ),(9007199254740992/3:ℝ),(9007199254740992/9:ℝ)],
![(18014398509481984/9:ℝ),(18014398509481984/3:ℝ),(18014398509481984/3:ℝ),(18014398509481984/9:ℝ)],
![(9007199254740992/9:ℝ),(9007199254740992/3:ℝ),(9007199254740992/3:ℝ),(9007199254740992/9:ℝ)]]
theorem admission027_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission027_14_coefficients (1875/4096:ℝ) (939/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission027_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission027_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (1875/4096:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission027_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission027_14_coefficients]
theorem admission027_all {δ p : ℝ}
 (hd : δ∈Set.Icc (1875/4096:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (511/1024:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission027_00_pos hd hp
 · exact admission027_01_pos hd hp
 · exact admission027_02_pos hd hp
 · exact admission027_03_pos hd hp
 · exact admission027_04_pos hd hp
 · exact admission027_05_pos hd hp
 · exact admission027_06_pos hd hp
 · exact admission027_07_pos hd hp
 · exact admission027_08_pos hd hp
 · exact admission027_09_pos hd hp
 · exact admission027_10_pos hd hp
 · exact admission027_11_pos hd hp
 · exact admission027_12_pos hd hp
 · exact admission027_13_pos hd hp
 · exact admission027_14_pos hd hp
end
end DasStageAFinite
#print axioms DasStageAFinite.admission027_all
