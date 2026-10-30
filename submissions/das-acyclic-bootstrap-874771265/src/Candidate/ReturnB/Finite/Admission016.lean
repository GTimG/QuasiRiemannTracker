/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def admission016_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3480565880240100868096/472772661:ℝ),(31226799087600099393536/1418317983:ℝ),(31128505253039290974208/1418317983:ℝ),(10343403806159494184960/1418317983:ℝ)],
![(6961131760480201736192/472772661:ℝ),(62453598175200198787072/1418317983:ℝ),(62257010506078581948416/1418317983:ℝ),(20686807612318988369920/1418317983:ℝ)],
![(3480565880240100868096/472772661:ℝ),(31226799087600099393536/1418317983:ℝ),(31128505253039290974208/1418317983:ℝ),(10343403806159494184960/1418317983:ℝ)]]
theorem admission016_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (587954435/630363548:ℝ) admission016_00_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission016_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission016_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission016_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission016_00_coefficients]
def admission016_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7626011184539755347968/1418317983:ℝ),(22823057972230466043904/1418317983:ℝ),(22768082390841666043904/1418317983:ℝ),(841226178127883927552/157590887:ℝ)],
![(15252022369079510695936/1418317983:ℝ),(45646115944460932087808/1418317983:ℝ),(45536164781683332087808/1418317983:ℝ),(1682452356255767855104/157590887:ℝ)],
![(7626011184539755347968/1418317983:ℝ),(22823057972230466043904/1418317983:ℝ),(22768082390841666043904/1418317983:ℝ),(841226178127883927552/157590887:ℝ)]]
theorem admission016_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (107590887/157590887:ℝ) admission016_01_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission016_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission016_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission016_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission016_01_coefficients]
def admission016_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(60590386246548370480955392/22161218484375:ℝ),(12090515217460501113995264/1477414565625:ℝ),(60314765928056640658997248/7387072828125:ℝ),(60176955768810775748018176/22161218484375:ℝ)],
![(121180772493096740961910784/22161218484375:ℝ),(24181030434921002227990528/1477414565625:ℝ),(120629531856113281317994496/7387072828125:ℝ),(120353911537621551496036352/22161218484375:ℝ)],
![(60590386246548370480955392/22161218484375:ℝ),(12090515217460501113995264/1477414565625:ℝ),(60314765928056640658997248/7387072828125:ℝ),(60176955768810775748018176/22161218484375:ℝ)]]
theorem admission016_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218922489762229/630363548000000:ℝ) admission016_02_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission016_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission016_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission016_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission016_02_coefficients]
def admission016_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5670140364647330480128/1418317983:ℝ),(50801120469227455643648/4254953949:ℝ),(50571275871643336966144/4254953949:ℝ),(16780576496357872762880/4254953949:ℝ)],
![(11321051411049026158592/1418317983:ℝ),(101429226415300538269696/4254953949:ℝ),(100969587504907041112064/4254953949:ℝ),(33503515322753581318144/4254953949:ℝ)],
![(5650911046401695678464/1418317983:ℝ),(50628105946073082626048/4254953949:ℝ),(50398311633263704145920/4254953949:ℝ),(16722938826395708555264/4254953949:ℝ)]]
theorem admission016_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (1946806305367/3872953638912:ℝ) admission016_03_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission016_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission016_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission016_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission016_03_coefficients]
def admission016_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4747242780642017325252608/7387072828125:ℝ),(565471779545622034939904/295482913125:ℝ),(14032109819068896130367488/7387072828125:ℝ),(4642558111070362582122496/7387072828125:ℝ)],
![(1904840024213586917384192/1477414565625:ℝ),(9454133529158944926867456/2462357609375:ℝ),(9384233322577871664840704/2462357609375:ℝ),(9314499501324714800840704/7387072828125:ℝ)],
![(4776957340425917261668352/7387072828125:ℝ),(14225606098836283907104768/7387072828125:ℝ),(14120590148664718864154624/7387072828125:ℝ),(1557313796751450739572736/2462357609375:ℝ)]]
theorem admission016_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (51884630073648273/645492273152000000:ℝ) admission016_04_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission016_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission016_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission016_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission016_04_coefficients]
def admission016_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1590090175411634987732992/4432243696875:ℝ),(23866608936508268656586752/22161218484375:ℝ),(23881505836180153419788288/22161218484375:ℝ),(2655115925576686567288832/7387072828125:ℝ)],
![(15736673596177397928460288/22161218484375:ℝ),(377932750617089796653056/177289747875:ℝ),(47272446917056847795642368/22161218484375:ℝ),(5255842228699340380823552/7387072828125:ℝ)],
![(7786222719119222989795328/22161218484375:ℝ),(23374984890627955925045248/22161218484375:ℝ),(4678188216175338875170816/4432243696875:ℝ),(173381753541510254235648/492471521875:ℝ)]]
theorem admission016_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (1900933281034966550243/42302981613289472000000:ℝ) admission016_05_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission016_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission016_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission016_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission016_05_coefficients]
def admission016_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(362993614209330096244981749776613376/387657074652833159859375:ℝ),(71717394275469654161382521694355456/25843804976855543990625:ℝ),(1062606830206755092630245815451910144/387657074652833159859375:ℝ),(23322629277458155532379315987546112/25843804976855543990625:ℝ)],
![(728059941034250317449444776102862848/387657074652833159859375:ℝ),(143847566422836983265907184459177984/25843804976855543990625:ℝ),(2131378998523125793740266326334636032/387657074652833159859375:ℝ),(46781684045474932265780222369988608/25843804976855543990625:ℝ)],
![(365066326824920221204463026326249472/387657074652833159859375:ℝ),(72130172147367329104524662764822528/25843804976855543990625:ℝ),(1068772168316370701110020510882725888/387657074652833159859375:ℝ),(23459054768016776733400906382442496/25843804976855543990625:ℝ)]]
theorem admission016_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (86883564581938667343479827/752755379094757747097600000:ℝ) admission016_06_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission016_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission016_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission016_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission016_06_coefficients]
def admission016_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6686802054929423738621692268478464/3492406077953451890625:ℝ),(2394321361197905902383330882912256/419088729354414226875:ℝ),(59535491353056723190049789714628608/10477218233860355671875:ℝ),(789514539515893873853263777890304/419088729354414226875:ℝ)],
![(13321350877799683168273627568545792/3492406077953451890625:ℝ),(23849413388312963486913766288187392/2095443646772071134375:ℝ),(118603257020160832631936753078370304/10477218233860355671875:ℝ),(7864048542399012940437760868614144/2095443646772071134375:ℝ)],
![(6634548822870259429651935300067328/3492406077953451890625:ℝ),(11877806582323433974997111873626112/2095443646772071134375:ℝ),(59067765667104109441886963363741696/10477218233860355671875:ℝ),(3916475844819543571171441979162624/2095443646772071134375:ℝ)]]
theorem admission016_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (58360037875466697978547841/244136879706407917977600000:ℝ) admission016_07_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission016_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission016_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission016_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission016_07_coefficients]
def admission016_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(457101763065166554365566283482777668608/20463316863008507171630859375:ℝ),(94113833070924445315724346696716089472/1364221124200567144775390625:ℝ),(1452084588511656694311763432233629686784/20463316863008507171630859375:ℝ),(497477974041587402289465449903616013312/20463316863008507171630859375:ℝ)],
![(976533422116635930874679845450572247552/20463316863008507171630859375:ℝ),(1003083562207582712882764735829447182688/6821105621002835723876953125:ℝ),(99640501008565334889810186039042942976/660106995580919586181640625:ℝ),(1056136501027208482384186821709974431744/20463316863008507171630859375:ℝ)],
![(519431659051469376509113561967794578944/20463316863008507171630859375:ℝ),(532514396852960486304143002345866735328/6821105621002835723876953125:ℝ),(1636770942753868687272352334976701545472/20463316863008507171630859375:ℝ),(558658526985621080094721371806358418432/20463316863008507171630859375:ℝ)]]
theorem admission016_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (446388440493326713247623323713650067/156247603012101067505664000000000000000:ℝ) admission016_08_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission016_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission016_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission016_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission016_08_coefficients]
def admission016_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2206489801017568606301783265171240064/32741306980813611474609375:ℝ),(6489690391489054563471654091655991296/32741306980813611474609375:ℝ),(2120061112137003100376718819741138944/10913768993604537158203125:ℝ),(83079356822335147199907886870298624/1309652279232544458984375:ℝ)],
![(4303608901100609284059854430568681952/32741306980813611474609375:ℝ),(12653168918978245746505010934962940928/32741306980813611474609375:ℝ),(133290835712177262279643254356180992/352057064309823779296875:ℝ),(809298011261941575603270891031494656/6548261396162722294921875:ℝ)],
![(1818837033896826259980981062790496/28396623573992724609375:ℝ),(6163478527489191183033356843306949632/32741306980813611474609375:ℝ),(2011954794940492030292222065300471808/10913768993604537158203125:ℝ),(393901227150265839603731456680001536/6548261396162722294921875:ℝ)]]
theorem admission016_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (46956685441764097166506225667/6103421992660197949440000000000:ℝ) admission016_09_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission016_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission016_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission016_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission016_09_coefficients]
def admission016_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(248163403967536137811452736/13850761552734375:ℝ),(1210722477237281079314455232/23084602587890625:ℝ),(3542020874795556391159140352/69253807763671875:ℝ),(127852339968557649141448704/7694867529296875:ℝ)],
![(2411829203396665277214748256/69253807763671875:ℝ),(2351971982238341977615821344/23084602587890625:ℝ),(764068298687608364884998144/7694867529296875:ℝ),(446505828447710425666453504/13850761552734375:ℝ)],
![(12588903487496963959070708/744664599609375:ℝ),(380335565787124126388796804/7694867529296875:ℝ),(666773886404403777897695488/13850761552734375:ℝ),(1081617964853908462682882048/69253807763671875:ℝ)]]
theorem admission016_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (66016721487665311443047/33049204385382400000000000:ℝ) admission016_10_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission016_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission016_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission016_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission016_10_coefficients]
def admission016_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(16451462005830259014068293418713088/10477218233860355671875:ℝ),(3272669972632998803171105925922816/698481215590690378125:ℝ),(16275442493500109696904467226558464/3492406077953451890625:ℝ),(3237547979367121211443021241909248/2095443646772071134375:ℝ)],
![(32771121432864728603675002379542528/10477218233860355671875:ℝ),(32595262386731758040101111282130944/3492406077953451890625:ℝ),(32419812011682932334898322442551296/3492406077953451890625:ℝ),(32244770307718251488066635860803584/10477218233860355671875:ℝ)],
![(3263931885406893917921341792165888/2095443646772071134375:ℝ),(16231912523566764024245581652516864/3492406077953451890625:ℝ),(16144369518182822637993855215992832/3492406077953451890625:ℝ),(16057030410882645430851529651257344/10477218233860355671875:ℝ)]]
theorem admission016_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (239268398447076163155608321/1220684398532039589888000000:ℝ) admission016_11_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission016_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission016_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission016_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission016_11_coefficients]
def admission016_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(28266449504747651072/439453125:ℝ),(28266449504747651072/146484375:ℝ),(28266449504747651072/146484375:ℝ),(28266449504747651072/439453125:ℝ)],
![(56532899009495302144/439453125:ℝ),(56532899009495302144/146484375:ℝ),(56532899009495302144/146484375:ℝ),(56532899009495302144/439453125:ℝ)],
![(28266449504747651072/439453125:ℝ),(28266449504747651072/146484375:ℝ),(28266449504747651072/146484375:ℝ),(28266449504747651072/439453125:ℝ)]]
theorem admission016_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (411330977/50000000000:ℝ) admission016_12_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission016_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission016_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission016_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission016_12_coefficients]
def admission016_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8952002692921126027264/274658203125:ℝ),(8952002692921126027264/91552734375:ℝ),(8952002692921126027264/91552734375:ℝ),(8952002692921126027264/274658203125:ℝ)],
![(17904005385842252054528/274658203125:ℝ),(17904005385842252054528/91552734375:ℝ),(17904005385842252054528/91552734375:ℝ),(17904005385842252054528/274658203125:ℝ)],
![(8952002692921126027264/274658203125:ℝ),(8952002692921126027264/91552734375:ℝ),(8952002692921126027264/91552734375:ℝ),(8952002692921126027264/274658203125:ℝ)]]
theorem admission016_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (260537568623/62500000000000:ℝ) admission016_13_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission016_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission016_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission016_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission016_13_coefficients]
def admission016_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(35184372088832/9:ℝ),(35184372088832/3:ℝ),(35184372088832/3:ℝ),(35184372088832/9:ℝ)],
![(70368744177664/9:ℝ),(70368744177664/3:ℝ),(70368744177664/3:ℝ),(70368744177664/9:ℝ)],
![(35184372088832/9:ℝ),(35184372088832/3:ℝ),(35184372088832/3:ℝ),(35184372088832/9:ℝ)]]
theorem admission016_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission016_14_coefficients (237/512:ℝ) (951/2048:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission016_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission016_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission016_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission016_14_coefficients]
theorem admission016_all {δ p : ℝ}
 (hd : δ∈Set.Icc (237/512:ℝ) (951/2048:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission016_00_pos hd hp
 · exact admission016_01_pos hd hp
 · exact admission016_02_pos hd hp
 · exact admission016_03_pos hd hp
 · exact admission016_04_pos hd hp
 · exact admission016_05_pos hd hp
 · exact admission016_06_pos hd hp
 · exact admission016_07_pos hd hp
 · exact admission016_08_pos hd hp
 · exact admission016_09_pos hd hp
 · exact admission016_10_pos hd hp
 · exact admission016_11_pos hd hp
 · exact admission016_12_pos hd hp
 · exact admission016_13_pos hd hp
 · exact admission016_14_pos hd hp
end
end DasStageBFinite
#print axioms DasStageBFinite.admission016_all
