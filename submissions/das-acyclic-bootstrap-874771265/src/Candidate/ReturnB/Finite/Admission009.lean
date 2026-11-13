/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def admission009_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(870141470060025217024/472772661:ℝ),(7806699771900024848384/1418317983:ℝ),(7782126313259822743552/1418317983:ℝ),(2585850951539873546240/1418317983:ℝ)],
![(1740282940120050434048/472772661:ℝ),(15613399543800049696768/1418317983:ℝ),(15564252626519645487104/1418317983:ℝ),(5171701903079747092480/1418317983:ℝ)],
![(870141470060025217024/472772661:ℝ),(7806699771900024848384/1418317983:ℝ),(7782126313259822743552/1418317983:ℝ),(2585850951539873546240/1418317983:ℝ)]]
theorem admission009_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (587954435/630363548:ℝ) admission009_00_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission009_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission009_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission009_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission009_00_coefficients]
def admission009_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1906502796134938836992/1418317983:ℝ),(5705764493057616510976/1418317983:ℝ),(5692020597710416510976/1418317983:ℝ),(210306544531970981888/157590887:ℝ)],
![(3813005592269877673984/1418317983:ℝ),(11411528986115233021952/1418317983:ℝ),(11384041195420833021952/1418317983:ℝ),(420613089063941963776/157590887:ℝ)],
![(1906502796134938836992/1418317983:ℝ),(5705764493057616510976/1418317983:ℝ),(5692020597710416510976/1418317983:ℝ),(210306544531970981888/157590887:ℝ)]]
theorem admission009_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (107590887/157590887:ℝ) admission009_01_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission009_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission009_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission009_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission009_01_coefficients]
def admission009_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(15147596561637092620238848/22161218484375:ℝ),(3022628804365125278498816/1477414565625:ℝ),(15078691482014160164749312/7387072828125:ℝ),(15044238942202693937004544/22161218484375:ℝ)],
![(30295193123274185240477696/22161218484375:ℝ),(6045257608730250556997632/1477414565625:ℝ),(30157382964028320329498624/7387072828125:ℝ),(30088477884405387874009088/22161218484375:ℝ)],
![(15147596561637092620238848/22161218484375:ℝ),(3022628804365125278498816/1477414565625:ℝ),(15078691482014160164749312/7387072828125:ℝ),(15044238942202693937004544/22161218484375:ℝ)]]
theorem admission009_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218922489762229/630363548000000:ℝ) admission009_02_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission009_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission009_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission009_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission009_02_coefficients]
def admission009_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1443994260540108046336/1418317983:ℝ),(12938289289070492254208/4254953949:ℝ),(12880702427737612091392/4254953949:ℝ),(4274395920287443976192/4254953949:ℝ)],
![(2878373861957398691840/1418317983:ℝ),(25790071316563797999616/4254953949:ℝ),(25674922736285407772672/4254953949:ℝ),(8519973005593805848576/4254953949:ℝ)],
![(1434379601417290645504/1418317983:ℝ),(12851782027493305745408/4254953949:ℝ),(12794220308547795681280/4254953949:ℝ),(4245577085306361872384/4254953949:ℝ)]]
theorem admission009_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (494250222727/968238409728:ℝ) admission009_03_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission009_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission009_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission009_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission009_03_coefficients]
def admission009_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(383084464893580512006144/2462357609375:ℝ),(45631425248143550287872/98494304375:ℝ),(1132337975905876111785984/2462357609375:ℝ),(374636809595867866595328/2462357609375:ℝ)],
![(771121356417811013414912/2462357609375:ℝ),(6889119592319399059984384/7387072828125:ℝ),(6838268020233168037609472/7387072828125:ℝ),(2262512497167202017869824/7387072828125:ℝ)],
![(388036891524230501408768/2462357609375:ℝ),(3466762698708632788393984/7387072828125:ℝ),(22201639306551869046784/47658534375:ℝ),(7345819795997409148928/47658534375:ℝ)]]
theorem admission009_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (100485422800863111/1290984546304000000:ℝ) admission009_04_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission009_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission009_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission009_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission009_04_coefficients]
def admission009_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2213426436430602664361984/22161218484375:ℝ),(1328288463156777233113088/4432243696875:ℝ),(6642518314259723137347584/22161218484375:ℝ),(738167478302146545381376/7387072828125:ℝ)],
![(4344738793891729354289152/22161218484375:ℝ),(13037072608627615965360128/22161218484375:ℝ),(13039754250867716752728064/22161218484375:ℝ),(1449140145377276713885696/7387072828125:ℝ)],
![(2131312357461126689927168/22161218484375:ℝ),(6395630292843729799794688/22161218484375:ℝ),(1279447187321598723076096/4432243696875:ℝ),(47398177805008677900288/492471521875:ℝ)]]
theorem admission009_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (520339931020782883283/10575745403322368000000:ℝ) admission009_05_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission009_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission009_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission009_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission009_05_coefficients]
def admission009_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(88124599961331359181697065974370304/387657074652833159859375:ℝ),(17408999478718055686321241728282624/25843804976855543990625:ℝ),(257912296121572194515589174998859776/387657074652833159859375:ℝ),(5660125456166262381817841003266048/25843804976855543990625:ℝ)],
![(177285556230457780843134770223558656/387657074652833159859375:ℝ),(35024387893384948844213553991798784/25843804976855543990625:ℝ),(518907261297952193271065697713127424/387657074652833159859375:ℝ),(11388463657611835364146477203980288/25843804976855543990625:ℝ)],
![(89160956269126421661437704249188352/387657074652833159859375:ℝ),(3523077682933378631578462452703232/5168760995371108798125:ℝ),(260994965176379998755476522714267648/387657074652833159859375:ℝ),(1145667640289114596465727240142848/5168760995371108798125:ℝ)]]
theorem admission009_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (168684883599467944557006389/1505510758189515494195200000:ℝ) admission009_06_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission009_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission009_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission009_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission009_06_coefficients]
def admission009_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1744026994955405835651921281355776/3492406077953451890625:ℝ),(3122450382597871651707810383753216/2095443646772071134375:ℝ),(15528427662821967325068465444749312/10477218233860355671875:ℝ),(1029651346939765314697035474010112/2095443646772071134375:ℝ)],
![(3461927373881229516818964078505984/3492406077953451890625:ℝ),(6198000653362695534955849497038848/2095443646772071134375:ℝ),(30822992482667627776055517714055168/10477218233860355671875:ℝ),(2043754267499567730346632492875776/2095443646772071134375:ℝ)],
![(1717900378925823681167042797150208/3492406077953451890625:ℝ),(3075550270764823883248039113285632/2095443646772071134375:ℝ),(15294564819845660450987052269305856/10477218233860355671875:ℝ),(1014102920559802415649597018865664/2095443646772071134375:ℝ)]]
theorem admission009_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (15111311086413300270581201/61034219926601979494400000:ℝ) admission009_07_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission009_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission009_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission009_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission009_07_coefficients]
def admission009_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(36363070783413110911957472764423279232/20463316863008507171630859375:ℝ),(8138316515137687002057271864290105968/1364221124200567144775390625:ℝ),(135042371471019774214770895519541188736/20463316863008507171630859375:ℝ),(49330481133191183738660655825319128448/20463316863008507171630859375:ℝ)],
![(103891089559977632895688584771355013632/20463316863008507171630859375:ℝ),(112355780900545999883333353074044203664/6821105621002835723876953125:ℝ),(362427920063145544909836242410618306816/20463316863008507171630859375:ℝ),(129251238738399206379949272602009459456/20463316863008507171630859375:ℝ)],
![(2701120751062580879349244480277269376/818532674520340286865234375:ℝ),(71664198324857564873046993752593673824/6821105621002835723876953125:ℝ),(45477109718425154139013069378215423616/4092663372601701434326171875:ℝ),(79920757605208022641288616776690331008/20463316863008507171630859375:ℝ)]]
theorem admission009_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (284086490495414928999667755972056869/312495206024202135011328000000000000000:ℝ) admission009_08_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission009_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission009_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission009_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission009_08_coefficients]
def admission009_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(704136694682781305708306191325165296/32741306980813611474609375:ℝ),(2075214734148130090284397020580181504/32741306980813611474609375:ℝ),(679368563117597783079001716634812416/10913768993604537158203125:ℝ),(133405586849857541544120827886174208/6548261396162722294921875:ℝ)],
![(1353588038898298647144756332763431504/32741306980813611474609375:ℝ),(3987323536296328490349645416985842176/32741306980813611474609375:ℝ),(1304683967636940031115755056049291264/10913768993604537158203125:ℝ),(256063395219010134890337666936602624/6548261396162722294921875:ℝ)],
![(649451344215517341436450141438266208/32741306980813611474609375:ℝ),(1912108802148198400065248396405660672/32741306980813611474609375:ℝ),(625315404519342248036753339414478848/10913768993604537158203125:ℝ),(122657808369152593346216839050428416/6548261396162722294921875:ℝ)]]
theorem admission009_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (14621950193542551201130967027/1525855498165049487360000000000:ℝ) admission009_09_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission009_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission009_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission009_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission009_09_coefficients]
def admission009_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(80617738479922231752848756/13850761552734375:ℝ),(394769186195281977335142508/23084602587890625:ℝ),(386464106598618486927828736/23084602587890625:ℝ),(378173593514972250042302464/69253807763671875:ℝ)],
![(773716558877543666717685328/69253807763671875:ℝ),(757229962669339055513497456/23084602587890625:ℝ),(2222314922599392205563978752/69253807763671875:ℝ),(80482430567605550637907968/7694867529296875:ℝ)],
![(123461235752055189329844272/23084602587890625:ℝ),(120739322944789519681126416/7694867529296875:ℝ),(212439644286527348292625408/13850761552734375:ℝ),(345928163925852882322522112/69253807763671875:ℝ)]]
theorem admission009_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (5278444884122511021767/2065575274086400000000000:ℝ) admission009_10_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission009_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission009_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission009_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission009_10_coefficients]
def admission009_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4295323776749957610012010871312384/10477218233860355671875:ℝ),(4272382643089742778329728722071552/3492406077953451890625:ℝ),(4249494889971164366843623204978688/3492406077953451890625:ℝ),(4226660517394222375553694320033792/10477218233860355671875:ℝ)],
![(8524746264102020507793229513682944/10477218233860355671875:ℝ),(8479046616380370560854483455594496/3492406077953451890625:ℝ),(1686690658456737040846388080934912/698481215590690378125:ℝ),(8387966291811964437925600360923136/10477218233860355671875:ℝ)],
![(845884497470412579556243728474112/2095443646772071134375:ℝ),(4206663973290627782524754733522944/3492406077953451890625:ℝ),(4183958402312520837388317199695872/3492406077953451890625:ℝ),(4161305774417742062371906040889344/10477218233860355671875:ℝ)]]
theorem admission009_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (62008288121487827038346321/305171099633009897472000000:ℝ) admission009_11_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission009_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission009_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission009_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission009_11_coefficients]
def admission009_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7066612376186912768/439453125:ℝ),(7066612376186912768/146484375:ℝ),(7066612376186912768/146484375:ℝ),(7066612376186912768/439453125:ℝ)],
![(14133224752373825536/439453125:ℝ),(14133224752373825536/146484375:ℝ),(14133224752373825536/146484375:ℝ),(14133224752373825536/439453125:ℝ)],
![(7066612376186912768/439453125:ℝ),(7066612376186912768/146484375:ℝ),(7066612376186912768/146484375:ℝ),(7066612376186912768/439453125:ℝ)]]
theorem admission009_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (411330977/50000000000:ℝ) admission009_12_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission009_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission009_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (459/1024:ℝ) (231/512:ℝ)) (hp : p∈Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission009_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission009_12_coefficients]
def admission009_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2238000673230281506816/274658203125:ℝ),(2238000673230281506816/91552734375:ℝ),(2238000673230281506816/91552734375:ℝ),(2238000673230281506816/274658203125:ℝ)],
![(4476001346460563013632/274658203125:ℝ),(4476001346460563013632/91552734375:ℝ),(4476001346460563013632/91552734375:ℝ),(4476001346460563013632/274658203125:ℝ)],
![(2238000673230281506816/274658203125:ℝ),(2238000673230281506816/91552734375:ℝ),(2238000673230281506816/91552734375:ℝ),(2238000673230281506816/274658203125:ℝ)]]
theorem admission009_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (260537568623/62500000000000:ℝ) admission009_13_coefficients (459/1024:ℝ) (231/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
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
end DasStageBFinite
#print axioms DasStageBFinite.admission009_all
