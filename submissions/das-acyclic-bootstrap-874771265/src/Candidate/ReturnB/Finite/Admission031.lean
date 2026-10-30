/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def admission031_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(86792527054547090758185254912/1418317983:ℝ),(260351814024674163712279445504/1418317983:ℝ),(260326046885707055150003126272/1418317983:ℝ),(86766759915579982195908935680/1418317983:ℝ)],
![(173585054109094181516370509824/1418317983:ℝ),(520703628049348327424558891008/1418317983:ℝ),(520652093771414110300006252544/1418317983:ℝ),(173533519831159964391817871360/1418317983:ℝ)],
![(86792527054547090758185254912/1418317983:ℝ),(260351814024674163712279445504/1418317983:ℝ),(260326046885707055150003126272/1418317983:ℝ),(86766759915579982195908935680/1418317983:ℝ)]]
theorem admission031_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (587954435/630363548:ℝ) admission031_00_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission031_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission031_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (15015/32768:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission031_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission031_00_coefficients]
def admission031_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(63524861347684514826807148544/1418317983:ℝ),(190560172524245958893221445632/1418317983:ℝ),(190545761005438373306021445632/1418317983:ℝ),(7056716647652992137734127616/157590887:ℝ)],
![(127049722695369029653614297088/1418317983:ℝ),(381120345048491917786442891264/1418317983:ℝ),(381091522010876746612042891264/1418317983:ℝ),(14113433295305984275468255232/157590887:ℝ)],
![(63524861347684514826807148544/1418317983:ℝ),(190560172524245958893221445632/1418317983:ℝ),(190545761005438373306021445632/1418317983:ℝ),(7056716647652992137734127616/157590887:ℝ)]]
theorem admission031_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (107590887/157590887:ℝ) admission031_01_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission031_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission031_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (15015/32768:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission031_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission031_01_coefficients]
def admission031_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(504909270897048267959702348890112/22161218484375:ℝ),(504873144790662919948478651039744/7387072828125:ℝ),(504837018684277571937254953189376/7387072828125:ℝ),(504800892577892223926031255339008/22161218484375:ℝ)],
![(1009818541794096535919404697780224/22161218484375:ℝ),(1009746289581325839896957302079488/7387072828125:ℝ),(1009674037368555143874509906378752/7387072828125:ℝ),(1009601785155784447852062510678016/22161218484375:ℝ)],
![(504909270897048267959702348890112/22161218484375:ℝ),(504873144790662919948478651039744/7387072828125:ℝ),(504837018684277571937254953189376/7387072828125:ℝ),(504800892577892223926031255339008/22161218484375:ℝ)]]
theorem admission031_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218922489762229/630363548000000:ℝ) admission031_02_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission031_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission031_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (15015/32768:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission031_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission031_02_coefficients]
def admission031_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(141384945177879439845078597632/4254953949:ℝ),(424094612845985440968162148352/4254953949:ℝ),(424034392576184401684288503808/4254953949:ℝ),(141324724908078400561204953088/4254953949:ℝ)],
![(282739670778205308753880809472/4254953949:ℝ),(848098567797671433094888947712/4254953949:ℝ),(27354133164416574268236627968/137256579:ℝ),(282619231077447677974327328768/4254953949:ℝ)],
![(141354725600325868908802211840/4254953949:ℝ),(13677546933925354584733122560/137256579:ℝ),(423943735520729400631046963200/4254953949:ℝ),(141294506169369277413122375680/4254953949:ℝ)]]
theorem admission031_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (31373682800455/61967258222592:ℝ) admission031_03_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission031_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission031_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (15015/32768:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission031_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission031_03_coefficients]
def admission031_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(12857053293690028747988681097216/2462357609375:ℝ),(38562126678404744234028314394624/2462357609375:ℝ),(38553094149178891351344505946112/2462357609375:ℝ),(12848020764464175865304872648704/2462357609375:ℝ)],
![(77157730478002375248491615092736/7387072828125:ℝ),(231418986802425945782964816183296/7387072828125:ℝ),(46272957242377088256978785927168/1477414565625:ℝ),(15420705977492374150084145709056/1477414565625:ℝ)],
![(38586570596932289004525571801088/7387072828125:ℝ),(115732606767211713080879872999424/7387072828125:ℝ),(115705503764348767230860411797504/7387072828125:ℝ),(38559467594069343154506110599168/7387072828125:ℝ)]]
theorem admission031_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (821616104077645437/10327876370432000000:ℝ) admission031_04_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission031_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission031_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (15015/32768:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission031_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission031_04_coefficients]
def admission031_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4555495722908724833005367984128/1477414565625:ℝ),(205000222762982495814724328882176/22161218484375:ℝ),(205003135081102256565961814441984/22161218484375:ℝ),(68335348161750633246318005321728/22161218484375:ℝ)],
![(9105287124717704469115681374208/1477414565625:ℝ),(409743768414423424110383171895296/22161218484375:ℝ),(409749610388027583793083254308864/22161218484375:ℝ),(136585148844369726719435303026688/22161218484375:ℝ)],
![(303319426787265309074020892672/98494304375:ℝ),(40948709130288185659131768602624/4432243696875:ℝ),(40949295061385065445424287973376/4432243696875:ℝ),(13649960136523818694623459540992/4432243696875:ℝ)]]
theorem admission031_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (1301705761473363772233099/27723682030085388369920000:ℝ) admission031_05_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission031_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission031_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (15015/32768:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission031_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission031_05_coefficients]
def admission031_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(64670666136578830949689095886094704050176/8614601658951847996875:ℝ),(8727130100292740549423126179754033612324864/387657074652833159859375:ℝ),(8723720805676916689600252458860450366357504/387657074652833159859375:ℝ),(193784712100475744965889991918711895752704/25843804976855543990625:ℝ)],
![(129365183893134503453766492945877835972608/8614601658951847996875:ℝ),(17457479740026163188670545141516418819293184/387657074652833159859375:ℝ),(17450660721609472188741602689487664603725824/387657074652833159859375:ℝ),(620225520717672781318433906275813163008/41350087962968870385:ℝ)],
![(64694517756555672504077397059783131922432/8614601658951847996875:ℝ),(1746069927946684527849483792352477041393664/77531414930566631971875:ℝ),(1745387983186511099828270046125442847473664/77531414930566631971875:ℝ),(193856238348069743358131199503671331127296/25843804976855543990625:ℝ)]]
theorem admission031_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (1376923194843554263157798743/12044086065516123953561600000:ℝ) admission031_06_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission031_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission031_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (15015/32768:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission031_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission031_06_coefficients]
def admission031_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(33433353321634784890826585059567748513792/2095443646772071134375:ℝ),(501414820322172118899200264747609057394688/10477218233860355671875:ℝ),(501329346144912909235899254645383881555968/10477218233860355671875:ℝ),(33416258486182942958166383039122713346048/2095443646772071134375:ℝ)],
![(66850398765249026961274429944223384993792/2095443646772071134375:ℝ),(1002585043331739195668681057567781775474688/10477218233860355671875:ℝ),(1002414115833624510559814904110184260435968/10477218233860355671875:ℝ),(66816213265626089939501199252703881986048/2095443646772071134375:ℝ)],
![(53467272709782787312716551815449018368/3352709834835313815:ℝ),(801872356815307322831169268512276348928/16763549174176569075:ℝ),(801735631501938562118265039143680606208/16763549174176569075:ℝ),(53439927647109035170135705941729869824/3352709834835313815:ℝ)]]
theorem admission031_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (1518854095567946705220257/6249904120484042700226560:ℝ) admission031_07_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission031_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission031_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (15015/32768:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission031_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission031_07_coefficients]
def admission031_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1054679723723421420004894989563319848410913792/6821105621002835723876953125:ℝ),(9503670794539951747286736865334792955181171712/20463316863008507171630859375:ℝ),(380608949006978106215427985546942269370016768/818532674520340286865234375:ℝ),(1058530700527143111205647532518889687033996288/6821105621002835723876953125:ℝ)],
![(424011555276683559769113326097566199299107328/1364221124200567144775390625:ℝ),(19103607790063026055318580110764184908410865664/20463316863008507171630859375:ℝ),(19126694894264269155340067677203927393423788032/20463316863008507171630859375:ℝ),(2127753477634926732034349070631961044099844096/6821105621002835723876953125:ℝ)],
![(1065378052659996378840671640924511148084622848/6821105621002835723876953125:ℝ),(9599936995523074308031843245429391953229693952/20463316863008507171630859375:ℝ),(9611471169089816499954368038530370659173368832/20463316863008507171630859375:ℝ),(1069222777107783620828701538113071357065847808/6821105621002835723876953125:ℝ)]]
theorem admission031_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (1029960667698653730473530263245429539463783/436899964202711703895517691904000000000000000:ℝ) admission031_08_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission031_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission031_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (15015/32768:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission031_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission031_08_coefficients]
def admission031_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(18500952420998639558975154290821020379424768/32741306980813611474609375:ℝ),(11093473722104180701926735031302423893245952/6548261396162722294921875:ℝ),(18477294136216341230353787605016627258589184/10913768993604537158203125:ℝ),(3693093243884873900000583895768883120832512/6548261396162722294921875:ℝ)],
![(36945524631786890592743695583499511697448448/32741306980813611474609375:ℝ),(22153125498305126886967789249373860080910336/6548261396162722294921875:ℝ),(36898228661717095163240228539752192319422464/10913768993604537158203125:ℝ),(7374916625201564128239602418540335262072832/6548261396162722294921875:ℝ)],
![(3688914442157650206753708258535698263604736/6548261396162722294921875:ℝ),(11059651776200946185041054218071436187664384/6548261396162722294921875:ℝ),(3684186905100150786577288186947113012166656/2182753798720907431640625:ℝ),(736364676263338045647803704554290428248064/1309652279232544458984375:ℝ)]]
theorem admission031_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (167429942908560871193868411991/19530950376512633438208000000000:ℝ) admission031_09_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission031_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission031_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (15015/32768:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission031_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission031_09_coefficients]
def admission031_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(10332344895918547161698608021977088/69253807763671875:ℝ),(10324202179596464029140586558068736/23084602587890625:ℝ),(10316059874990903970078659794960384/23084602587890625:ℝ),(10307917982251520205137827732652032/69253807763671875:ℝ)],
![(458431433367732385955479994381312/1538973505859375:ℝ),(12367880594190510878986954825198592/13850761552734375:ℝ),(2471622596227864335732772125540352/2770152310546875:ℝ),(457346143035363947134858416881664/1538973505859375:ℝ)],
![(411882469333128273899295178510208/2770152310546875:ℝ),(1234670912775417785444127502383232/2770152310546875:ℝ),(246738893376573195474401203847168/554030462109375:ℝ),(410906023446564987428736195362816/2770152310546875:ℝ)]]
theorem admission031_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (765372111362526169845343/338423852906315776000000000:ℝ) admission031_10_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission031_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission031_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (15015/32768:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission031_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission031_10_coefficients]
def admission031_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(137130304852286393003883455746089227911168/10477218233860355671875:ℝ),(137107001059891228667227361778148292165632/3492406077953451890625:ℝ),(137083698968290263446795834516853344960512/3492406077953451890625:ℝ),(137060398577483497342588873962204386295808/10477218233860355671875:ℝ)],
![(274192062422028372891135218845446085541888/10477218233860355671875:ℝ),(274145460793543703957390037494140913057792/3492406077953451890625:ℝ),(274098862566199475948445911578264419172352/3492406077953451890625:ℝ),(274052267739995688864302841097816603885568/10477218233860355671875:ℝ)],
![(27412351513948395977450352619871371526144/2095443646772071134375:ℝ),(27407691946730495058032535143198524178432/698481215590690378125:ℝ),(27403032719581842500330015412282214842368/698481215590690378125:ℝ),(27398373832502438304342793427122443517952/2095443646772071134375:ℝ)]]
theorem admission031_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (778708619932968937983525661/3906190075302526687641600000:ℝ) admission031_11_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission031_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission031_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (15015/32768:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission031_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission031_11_coefficients]
def admission031_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(237116164447122183763787776/439453125:ℝ),(237116164447122183763787776/146484375:ℝ),(237116164447122183763787776/146484375:ℝ),(237116164447122183763787776/439453125:ℝ)],
![(474232328894244367527575552/439453125:ℝ),(474232328894244367527575552/146484375:ℝ),(474232328894244367527575552/146484375:ℝ),(474232328894244367527575552/439453125:ℝ)],
![(237116164447122183763787776/439453125:ℝ),(237116164447122183763787776/146484375:ℝ),(237116164447122183763787776/146484375:ℝ),(237116164447122183763787776/439453125:ℝ)]]
theorem admission031_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (411330977/50000000000:ℝ) admission031_12_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission031_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission031_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (15015/32768:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission031_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission031_12_coefficients]
def admission031_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(75094841405859701161315008512/274658203125:ℝ),(75094841405859701161315008512/91552734375:ℝ),(75094841405859701161315008512/91552734375:ℝ),(75094841405859701161315008512/274658203125:ℝ)],
![(150189682811719402322630017024/274658203125:ℝ),(150189682811719402322630017024/91552734375:ℝ),(150189682811719402322630017024/91552734375:ℝ),(150189682811719402322630017024/274658203125:ℝ)],
![(75094841405859701161315008512/274658203125:ℝ),(75094841405859701161315008512/91552734375:ℝ),(75094841405859701161315008512/91552734375:ℝ),(75094841405859701161315008512/274658203125:ℝ)]]
theorem admission031_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (260537568623/62500000000000:ℝ) admission031_13_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission031_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission031_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (15015/32768:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission031_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission031_13_coefficients]
def admission031_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(295147905179352825856/9:ℝ),(295147905179352825856/3:ℝ),(295147905179352825856/3:ℝ),(295147905179352825856/9:ℝ)],
![(590295810358705651712/9:ℝ),(590295810358705651712/3:ℝ),(590295810358705651712/3:ℝ),(590295810358705651712/9:ℝ)],
![(295147905179352825856/9:ℝ),(295147905179352825856/3:ℝ),(295147905179352825856/3:ℝ),(295147905179352825856/9:ℝ)]]
theorem admission031_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission031_14_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission031_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission031_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (3753/8192:ℝ) (15015/32768:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission031_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission031_14_coefficients]
theorem admission031_all {δ p : ℝ}
 (hd : δ∈Set.Icc (3753/8192:ℝ) (15015/32768:ℝ)) (hp : p∈Set.Icc (4095/8192:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission031_00_pos hd hp
 · exact admission031_01_pos hd hp
 · exact admission031_02_pos hd hp
 · exact admission031_03_pos hd hp
 · exact admission031_04_pos hd hp
 · exact admission031_05_pos hd hp
 · exact admission031_06_pos hd hp
 · exact admission031_07_pos hd hp
 · exact admission031_08_pos hd hp
 · exact admission031_09_pos hd hp
 · exact admission031_10_pos hd hp
 · exact admission031_11_pos hd hp
 · exact admission031_12_pos hd hp
 · exact admission031_13_pos hd hp
 · exact admission031_14_pos hd hp
end
end DasStageBFinite
#print axioms DasStageBFinite.admission031_all
