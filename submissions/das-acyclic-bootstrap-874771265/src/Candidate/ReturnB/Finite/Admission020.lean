/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def admission020_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(873745047558815744/472772661:ℝ),(7767715355216052224/1418317983:ℝ),(7671725282402762752/1418317983:ℝ),(2525245069863157760/1418317983:ℝ)],
![(1747490095117631488/472772661:ℝ),(15535430710432104448/1418317983:ℝ),(15343450564805525504/1418317983:ℝ),(5050490139726315520/1418317983:ℝ)],
![(873745047558815744/472772661:ℝ),(7767715355216052224/1418317983:ℝ),(7671725282402762752/1418317983:ℝ),(2525245069863157760/1418317983:ℝ)]]
theorem admission020_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (587954435/630363548:ℝ) admission020_00_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission020_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission020_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission020_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission020_00_coefficients]
def admission020_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1902084455250526208/1418317983:ℝ),(5652566274551578624/1418317983:ℝ),(5598879183351578624/1418317983:ℝ),(205377484894502912/157590887:ℝ)],
![(3804168910501052416/1418317983:ℝ),(11305132549103157248/1418317983:ℝ),(11197758366703157248/1418317983:ℝ),(410754969789005824/157590887:ℝ)],
![(1902084455250526208/1418317983:ℝ),(5652566274551578624/1418317983:ℝ),(5598879183351578624/1418317983:ℝ),(205377484894502912/157590887:ℝ)]]
theorem admission020_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (107590887/157590887:ℝ) admission020_01_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission020_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission020_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission020_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission020_01_coefficients]
def admission020_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3019076058582087630848/4432243696875:ℝ),(14960800059271898202112/7387072828125:ℝ),(14826219825633358249984/7387072828125:ℝ),(14691639591994818297856/22161218484375:ℝ)],
![(6038152117164175261696/4432243696875:ℝ),(29921600118543796404224/7387072828125:ℝ),(29652439651266716499968/7387072828125:ℝ),(29383279183989636595712/22161218484375:ℝ)],
![(3019076058582087630848/4432243696875:ℝ),(14960800059271898202112/7387072828125:ℝ),(14826219825633358249984/7387072828125:ℝ),(14691639591994818297856/22161218484375:ℝ)]]
theorem admission020_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218922489762229/630363548000000:ℝ) admission020_02_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission020_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission020_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission020_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission020_02_coefficients]
def admission020_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1447691301586731008/1418317983:ℝ),(12802896140353667072/4254953949:ℝ),(12577750214426755072/4254953949:ℝ),(4117927978833281024/4254953949:ℝ)],
![(2857734501324292096/1418317983:ℝ),(25267300604267462656/4254953949:ℝ),(24817379483816296448/4254953949:ℝ),(8123282383521710080/4254953949:ℝ)],
![(1410043199737561088/1418317983:ℝ),(12464404463913795584/4254953949:ℝ),(12239629269389541376/4254953949:ℝ),(4005354404688429056/4254953949:ℝ)]]
theorem admission020_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (238737726491/484119204864:ℝ) admission020_03_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission020_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission020_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission020_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission020_03_coefficients]
def admission020_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(250409760379901990912/1477414565625:ℝ),(146035850074120812544/295482913125:ℝ),(709326358615621107712/1477414565625:ℝ),(229556868624919035904/1477414565625:ℝ)],
![(2564093432424622537472/7387072828125:ℝ),(2493049578578903591168/2462357609375:ℝ),(2422671068905836118016/2462357609375:ℝ),(2352957903405420118016/7387072828125:ℝ)],
![(1312044630525112582912/7387072828125:ℝ),(3828252483883690459904/7387072828125:ℝ),(3721381413639402815488/7387072828125:ℝ),(401724520093608312832/2462357609375:ℝ)]]
theorem admission020_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (656767469286687/8068653414400000:ℝ) admission020_04_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission020_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission020_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission020_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission020_04_coefficients]
def admission020_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(64411182984038634368/714878015625:ℝ),(6011413599237875246464/22161218484375:ℝ),(6031165481348373171584/22161218484375:ℝ),(672166184871898530176/7387072828125:ℝ)],
![(23654850235125204992/142975603125:ℝ),(11050190429767469820416/22161218484375:ℝ),(11097996558487856061184/22161218484375:ℝ),(412700879462754779392/2462357609375:ℝ)],
![(53863068191587390592/714878015625:ℝ),(5038776830529594573952/22161218484375:ℝ),(202673243085579315584/886448739375:ℝ),(4527491628130926464/59096582625:ℝ)]]
theorem admission020_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (420805220246776489/10661033672704000000:ℝ) admission020_05_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission020_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission020_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission020_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission020_05_coefficients]
def admission020_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(19910607813491030289961682192384/77531414930566631971875:ℝ),(19016941041251753501638127949824/25843804976855543990625:ℝ),(54422349564066784798953553788928/77531414930566631971875:ℝ),(1152123059500751852266723475456/5168760995371108798125:ℝ)],
![(203311913879758656810954818050304/387657074652833159859375:ℝ),(194304109827171811873975860556544/129219024884277719953125:ℝ),(556418634728653339749660691038208/387657074652833159859375:ℝ),(11787686631254825555912528494592/25843804976855543990625:ℝ)],
![(103758874812303505361146407088384/387657074652833159859375:ℝ),(99219404620913044365785220807424/129219024884277719953125:ℝ),(284306886908319415754892922093568/387657074652833159859375:ℝ),(6027071333751066294578911117312/25843804976855543990625:ℝ)]]
theorem admission020_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (1098750171185256817118381/9409442238684471838720000:ℝ) admission020_06_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission020_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission020_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission020_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission020_06_coefficients]
def admission020_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(345840385870295927467291265024/698481215590690378125:ℝ),(3049699722639827374221776377856/2095443646772071134375:ℝ),(2987329438251439119751698055168/2095443646772071134375:ℝ),(975150873222499527931795472384/2095443646772071134375:ℝ)],
![(3353835859223316922748111964416/3492406077953451890625:ℝ),(29565988333791055499124104125184/10477218233860355671875:ℝ),(28952309285612449638177440628736/10477218233860355671875:ℝ),(377913141179653796291906895872/419088729354414226875:ℝ)],
![(1624633929871837285411655639296/3492406077953451890625:ℝ),(14317489720591918628015222235904/10477218233860355671875:ℝ),(14015662094355254039418950352896/10477218233860355671875:ℝ),(914414832675769453527739006976/2095443646772071134375:ℝ)]]
theorem admission020_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (6976431523710399273130333/30517109963300989747200000:ℝ) admission020_07_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission020_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission020_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission020_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission020_07_coefficients]
def admission020_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(26830825988974832684998386150484/4258754810199481201171875:ℝ),(100771423861016937477549577350492/4889681448747552490234375:ℝ),(91339289160016968800730355152018436/4092663372601701434326171875:ℝ),(32775241697392484025852069512771756/4092663372601701434326171875:ℝ)],
![(80421631244905335956972300009897/4258754810199481201171875:ℝ),(4372643861076209404798017414951239/73345221731213287353515625:ℝ),(1280815626898108890341390102003789416/20463316863008507171630859375:ℝ),(89449136888548123444382233518802264/4092663372601701434326171875:ℝ)],
![(53590805255930503271973913859413/4258754810199481201171875:ℝ),(2861072503160955342634773754693859/73345221731213287353515625:ℝ),(824119181098024046337738326243697236/20463316863008507171630859375:ℝ),(56673895191155639418530164006030508/4092663372601701434326171875:ℝ)]]
theorem admission020_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (6707706497243708171249596537621/2032356959054384332800000000000000:ℝ) admission020_08_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission020_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission020_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission020_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission020_08_coefficients]
def admission020_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(133243199453702905395690674667488/6548261396162722294921875:ℝ),(375588612880653241384884066525952/6548261396162722294921875:ℝ),(23441922322774073972607751356416/436550759744181486328125:ℝ),(109287138562937153465149267787776/6548261396162722294921875:ℝ)],
![(221510830450685216474631756088972/6548261396162722294921875:ℝ),(3096442426385920979545976134970464/32741306980813611474609375:ℝ),(957268158394766522066193519597568/10913768993604537158203125:ℝ),(35318153487124120606447215837184/1309652279232544458984375:ℝ)],
![(88267630996982311078941081421484/6548261396162722294921875:ℝ),(1218499361982654772621555802340704/32741306980813611474609375:ℝ),(371220100325414672750999735687168/10913768993604537158203125:ℝ),(67303628872683449567086811398144/6548261396162722294921875:ℝ)]]
theorem admission020_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (4107887504436245701116138391/762927749082524743680000000000:ℝ) admission020_09_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission020_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission020_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission020_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission020_09_coefficients]
def admission020_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(393828308816343150014272/69253807763671875:ℝ),(121841279378365433711424/7694867529296875:ℝ),(1012112807166930341762816/69253807763671875:ℝ),(103126388025994862791424/23084602587890625:ℝ)],
![(641412701083032708648784/69253807763671875:ℝ),(587541227970758158186864/23084602587890625:ℝ),(533932507739546783474944/23084602587890625:ℝ),(480606143514398584513024/69253807763671875:ℝ)],
![(81192493232296048099819/23084602587890625:ℝ),(218096604266291700680539/23084602587890625:ℝ),(578177427380200588625488/69253807763671875:ℝ),(167475140879776130883328/69253807763671875:ℝ)]]
theorem admission020_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (654199769061625511263/516393818521600000000000:ℝ) admission020_10_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission020_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission020_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission020_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission020_10_coefficients]
def admission020_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4254992411201007442894304036864/10477218233860355671875:ℝ),(4169192776554019807424368646144/3492406077953451890625:ℝ),(4084179365867636385440758759424/3492406077953451890625:ℝ),(3999952179141857176943474376704/10477218233860355671875:ℝ)],
![(8246091552240941010322930984192/10477218233860355671875:ℝ),(8077386725894297253175556814592/3492406077953451890625:ℝ),(7910227006324596293241442582528/3492406077953451890625:ℝ),(61956899148254705044164706304/83817745870882845375:ℝ)],
![(3991099141039933567428626947328/10477218233860355671875:ℝ),(3908193949340277445751188168448/3492406077953451890625:ℝ),(3826047640456959907800683823104/3492406077953451890625:ℝ),(3744660214389980953577113911296/10477218233860355671875:ℝ)]]
theorem admission020_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (28569490161056373242012893/152585549816504948736000000:ℝ) admission020_11_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission020_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission020_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission020_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission020_11_coefficients]
def admission020_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6900988648620032/439453125:ℝ),(6900988648620032/146484375:ℝ),(6900988648620032/146484375:ℝ),(6900988648620032/439453125:ℝ)],
![(13801977297240064/439453125:ℝ),(13801977297240064/146484375:ℝ),(13801977297240064/146484375:ℝ),(13801977297240064/439453125:ℝ)],
![(6900988648620032/439453125:ℝ),(6900988648620032/146484375:ℝ),(6900988648620032/146484375:ℝ),(6900988648620032/439453125:ℝ)]]
theorem admission020_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (411330977/50000000000:ℝ) admission020_12_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission020_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission020_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission020_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission020_12_coefficients]
def admission020_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2185547532451446784/274658203125:ℝ),(2185547532451446784/91552734375:ℝ),(2185547532451446784/91552734375:ℝ),(2185547532451446784/274658203125:ℝ)],
![(4371095064902893568/274658203125:ℝ),(4371095064902893568/91552734375:ℝ),(4371095064902893568/91552734375:ℝ),(4371095064902893568/274658203125:ℝ)],
![(2185547532451446784/274658203125:ℝ),(2185547532451446784/91552734375:ℝ),(2185547532451446784/91552734375:ℝ),(2185547532451446784/274658203125:ℝ)]]
theorem admission020_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (260537568623/62500000000000:ℝ) admission020_13_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission020_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission020_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission020_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission020_13_coefficients]
def admission020_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8589934592/9:ℝ),(8589934592/3:ℝ),(8589934592/3:ℝ),(8589934592/9:ℝ)],
![(17179869184/9:ℝ),(17179869184/3:ℝ),(17179869184/3:ℝ),(17179869184/9:ℝ)],
![(8589934592/9:ℝ),(8589934592/3:ℝ),(8589934592/3:ℝ),(8589934592/9:ℝ)]]
theorem admission020_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission020_14_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission020_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission020_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission020_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission020_14_coefficients]
theorem admission020_all {δ p : ℝ}
 (hd : δ∈Set.Icc (15/32:ℝ) (123/256:ℝ)) (hp : p∈Set.Icc (31/64:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission020_00_pos hd hp
 · exact admission020_01_pos hd hp
 · exact admission020_02_pos hd hp
 · exact admission020_03_pos hd hp
 · exact admission020_04_pos hd hp
 · exact admission020_05_pos hd hp
 · exact admission020_06_pos hd hp
 · exact admission020_07_pos hd hp
 · exact admission020_08_pos hd hp
 · exact admission020_09_pos hd hp
 · exact admission020_10_pos hd hp
 · exact admission020_11_pos hd hp
 · exact admission020_12_pos hd hp
 · exact admission020_13_pos hd hp
 · exact admission020_14_pos hd hp
end
end DasStageBFinite
#print axioms DasStageBFinite.admission020_all
