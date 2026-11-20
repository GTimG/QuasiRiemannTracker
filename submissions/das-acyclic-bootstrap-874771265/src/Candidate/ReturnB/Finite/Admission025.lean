/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def admission025_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(83140405787519187156992/1418317983:ℝ),(249028042024314327793664/1418317983:ℝ),(248634866686071094116352/1418317983:ℝ),(82747230449275953479680/1418317983:ℝ)],
![(166280811575038374313984/1418317983:ℝ),(498056084048628655587328/1418317983:ℝ),(497269733372142188232704/1418317983:ℝ),(165494460898551906959360/1418317983:ℝ)],
![(83140405787519187156992/1418317983:ℝ),(249028042024314327793664/1418317983:ℝ),(248634866686071094116352/1418317983:ℝ),(82747230449275953479680/1418317983:ℝ)]]
theorem admission025_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (587954435/630363548:ℝ) admission025_00_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission025_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission025_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission025_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission025_00_coefficients]
def admission025_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(60788187150762842783744/1418317983:ℝ),(182144659126733328351232/1418317983:ℝ),(181924756801178128351232/1418317983:ℝ),(6729809425023071420416/157590887:ℝ)],
![(121576374301525685567488/1418317983:ℝ),(364289318253466656702464/1418317983:ℝ),(363849513602356256702464/1418317983:ℝ),(13459618850046142840832/157590887:ℝ)],
![(60788187150762842783744/1418317983:ℝ),(182144659126733328351232/1418317983:ℝ),(181924756801178128351232/1418317983:ℝ),(6729809425023071420416/157590887:ℝ)]]
theorem admission025_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (107590887/157590887:ℝ) admission025_01_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission025_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission025_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission025_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission025_01_coefficients]
def admission025_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(483069368061436584915894272/22161218484375:ℝ),(482518127424453125271977984/7387072828125:ℝ),(481966886787469665628061696/7387072828125:ℝ),(481415646150486205984145408/22161218484375:ℝ)],
![(966138736122873169831788544/22161218484375:ℝ),(965036254848906250543955968/7387072828125:ℝ),(963933773574939331256123392/7387072828125:ℝ),(962831292300972411968290816/22161218484375:ℝ)],
![(483069368061436584915894272/22161218484375:ℝ),(482518127424453125271977984/7387072828125:ℝ),(481966886787469665628061696/7387072828125:ℝ),(481415646150486205984145408/22161218484375:ℝ)]]
theorem admission025_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218922489762229/630363548000000:ℝ) admission025_02_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission025_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission025_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission025_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission025_02_coefficients]
def admission025_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(136086408756708327292928/4254953949:ℝ),(407339043323392664010752/4254953949:ℝ),(406419449256941946142720/4254953949:ℝ),(135166814690257609424896/4254953949:ℝ)],
![(271711513127183580135424/4254953949:ℝ),(813294374627185065459712/4254953949:ℝ),(811455389520819390513152/4254953949:ℝ),(269872528020817905188864/4254953949:ℝ)],
![(135625104370475252842496/4254953949:ℝ),(405955331303792401448960/4254953949:ℝ),(405035940263877444370432/4254953949:ℝ),(134705713330560295763968/4254953949:ℝ)]]
theorem admission025_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (1960226121163/3872953638912:ℝ) admission025_03_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission025_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission025_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission025_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission025_03_coefficients]
def admission025_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(398744930659439567044608/79430890625:ℝ),(36945465821765195010015232/2462357609375:ℝ),(36807817111862257255448576/2462357609375:ℝ),(12223444140539688823816192/2462357609375:ℝ)],
![(74402946881415204810702848/7387072828125:ℝ),(222380639144469864882028544/7387072828125:ℝ),(221553423339764710106988544/7387072828125:ℝ),(73575731076710050035662848/7387072828125:ℝ)],
![(37319668330087325075554304/7387072828125:ℝ),(111544241679174279851982848/7387072828125:ℝ),(111129972004177938340642816/7387072828125:ℝ),(36905398655090983564214272/7387072828125:ℝ)]]
theorem admission025_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (25613931302180793/322746136576000000:ℝ) admission025_04_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission025_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission025_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission025_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission025_04_coefficients]
def admission025_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4416720810395151685443584/1477414565625:ℝ),(198795075417239705896050688/22161218484375:ℝ),(198837004654251383212040192/22161218484375:ℝ),(66292741392938952597643264/22161218484375:ℝ)],
![(2915378633008216190615552/492471521875:ℝ),(78733126103466472117141504/4432243696875:ℝ),(2540346605670604845891584/142975603125:ℝ),(26256026369396223821037568/4432243696875:ℝ)],
![(4329415088629496886403072/1477414565625:ℝ),(194870555100092654689656832/22161218484375:ℝ),(194916719224692367901155328/22161218484375:ℝ),(64987390454042166507544576/22161218484375:ℝ)]]
theorem admission025_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (1585479158433653644923/33842385290631577600000:ℝ) admission025_05_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission025_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission025_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission025_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission025_05_coefficients]
def admission025_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(187869234053058048007999269959237632/25843804976855543990625:ℝ),(8401920206281876896790917838331052032/387657074652833159859375:ℝ),(8349855181015638630672865012672888832/387657074652833159859375:ℝ),(184398226370727305042689081582026752/25843804976855543990625:ℝ)],
![(376836874850252774389446002849202176/25843804976855543990625:ℝ),(3370632679061884476777428365208010752/77531414930566631971875:ℝ),(3349785660554058302289743015630077952/77531414930566631971875:ℝ),(369887856665923579693550886323224576/25843804976855543990625:ℝ)],
![(188967640797194726381446732889964544/25843804976855543990625:ℝ),(8451243189027545487096223987709001728/387657074652833159859375:ℝ),(8399073121754652880775850065477500928/387657074652833159859375:ℝ),(185489630295196274650861804741197824/25843804976855543990625:ℝ)]]
theorem admission025_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (42933557734528394658744587/376377689547378873548800000:ℝ) admission025_06_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission025_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission025_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission025_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission025_06_coefficients]
def admission025_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(32339985974387355672963271653195776/2095443646772071134375:ℝ),(483789211990200814633356963704602624/10477218233860355671875:ℝ),(482479938242236874886783513839796224/10477218233860355671875:ℝ),(32078131224794567723648581680234496/2095443646772071134375:ℝ)],
![(64430177795922668675897704403943424/2095443646772071134375:ℝ),(192767322683426488992404177857527808/2095443646772071134375:ℝ),(192244632515013549379044621531742208/2095443646772071134375:ℝ),(63907487627509729062538148078157824/2095443646772071134375:ℝ)],
![(32090191821535313002934432750747648/2095443646772071134375:ℝ),(480047401426931630328663925583036416/10477218233860355671875:ℝ),(478743224332830872008439593818914816/10477218233860355671875:ℝ),(31829356402715161338889566397923328/2095443646772071134375:ℝ)]]
theorem admission025_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (59286796306660699358004269/244136879706407917977600000:ℝ) admission025_07_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission025_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission025_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission025_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission025_07_coefficients]
def admission025_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(305503107529630926515742610836790328192/2273701873667611907958984375:ℝ),(8428479106195528451196042118001184323456/20463316863008507171630859375:ℝ),(1721656848724125894309494548710090181504/4092663372601701434326171875:ℝ),(325481359430919513870042318741364393088/2273701873667611907958984375:ℝ)],
![(665898714800102216596591433864435105056/2273701873667611907958984375:ℝ),(591434139871423758045777515856929943232/660106995580919586181640625:ℝ),(18689480539538511048600372160906098111232/20463316863008507171630859375:ℝ),(235115144196622987855659596761722159872/757900624555870635986328125:ℝ)],
![(360395607270471290080848823027644776864/2273701873667611907958984375:ℝ),(9905979229818608048223060873563643916736/20463316863008507171630859375:ℝ),(10081196295917881577052899417355647203712/20463316863008507171630859375:ℝ),(379864073158949449696936471543802086528/2273701873667611907958984375:ℝ)]]
theorem admission025_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (7160229082725724840212717441487273317/3333282197591489440120832000000000000000:ℝ) admission025_08_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission025_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission025_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission025_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission025_08_coefficients]
def admission025_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(18883220097887115444094810773297983744/32741306980813611474609375:ℝ),(11220269790806933850303076386023161856/6548261396162722294921875:ℝ),(18517881205925704242849612037045092352/10913768993604537158203125:ℝ),(3667103184275964230329243117555810304/6548261396162722294921875:ℝ)],
![(7379812178888651377395016409358733664/6548261396162722294921875:ℝ),(21921626332973836401853193796020156416/6548261396162722294921875:ℝ),(7234685200767433255489015500579536896/2182753798720907431640625:ℝ),(7162241912860649289492022413739687936/6548261396162722294921875:ℝ)],
![(18015840796556141442880271273495684576/32741306980813611474609375:ℝ),(2140271308433380510310023481999398912/1309652279232544458984375:ℝ),(17655544797911462034595465465852592128/10913768993604537158203125:ℝ),(3495138728584685059162779296183877632/6548261396162722294921875:ℝ)]]
theorem admission025_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (52081625589500145005625177863/6103421992660197949440000000000:ℝ) admission025_09_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission025_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission025_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission025_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission025_09_coefficients]
def admission025_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(10659214383770526218078806528/69253807763671875:ℝ),(702254392070670178082843136/1538973505859375:ℝ),(3469506388266563154347229184/7694867529296875:ℝ),(10283324816771936593475928064/69253807763671875:ℝ)],
![(2308829069487825703350205312/7694867529296875:ℝ),(61589831962779372157380495232/69253807763671875:ℝ),(12168376503360508652111249408/13850761552734375:ℝ),(6677171115569325811109199872/23084602587890625:ℝ)],
![(10118310160440547788010492808/69253807763671875:ℝ),(5996517848454346815063031016/13850761552734375:ℝ),(29610546084908376977645556736/69253807763671875:ℝ),(9746267588595042252840894464/69253807763671875:ℝ)]]
theorem admission025_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (74358120640526140234687/33049204385382400000000000:ℝ) admission025_10_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission025_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission025_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission025_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission025_10_coefficients]
def admission025_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(132664399235395010997293529180798976/10477218233860355671875:ℝ),(132306939928240386798299904104071168/3492406077953451890625:ℝ),(131949897166419455959048085913468928/3492406077953451890625:ℝ),(131593270949932218479538074608992256/10477218233860355671875:ℝ)],
![(264278755461294720792200217382436864/10477218233860355671875:ℝ),(263565294304109244125010311095107584/3492406077953451890625:ℝ),(262852664487757921176999417551519744/3492406077953451890625:ℝ),(262140866012240751948167536751673344/10477218233860355671875:ℝ)],
![(131614356225899709794906688201637888/10477218233860355671875:ℝ),(131258354375868857326710406991036416/3492406077953451890625:ℝ),(130902767321338465217951331638050816/3492406077953451890625:ℝ),(130547595062308533468629462142681088/10477218233860355671875:ℝ)]]
theorem admission025_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (243163844686576227599064749/1220684398532039589888000000:ℝ) admission025_11_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission025_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission025_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission025_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission025_11_coefficients]
def admission025_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(226131596037981208576/439453125:ℝ),(226131596037981208576/146484375:ℝ),(226131596037981208576/146484375:ℝ),(226131596037981208576/439453125:ℝ)],
![(452263192075962417152/439453125:ℝ),(452263192075962417152/146484375:ℝ),(452263192075962417152/146484375:ℝ),(452263192075962417152/439453125:ℝ)],
![(226131596037981208576/439453125:ℝ),(226131596037981208576/146484375:ℝ),(226131596037981208576/146484375:ℝ),(226131596037981208576/439453125:ℝ)]]
theorem admission025_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (411330977/50000000000:ℝ) admission025_12_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission025_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission025_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission025_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission025_12_coefficients]
def admission025_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(71616021543369008218112/274658203125:ℝ),(71616021543369008218112/91552734375:ℝ),(71616021543369008218112/91552734375:ℝ),(71616021543369008218112/274658203125:ℝ)],
![(143232043086738016436224/274658203125:ℝ),(143232043086738016436224/91552734375:ℝ),(143232043086738016436224/91552734375:ℝ),(143232043086738016436224/274658203125:ℝ)],
![(71616021543369008218112/274658203125:ℝ),(71616021543369008218112/91552734375:ℝ),(71616021543369008218112/91552734375:ℝ),(71616021543369008218112/274658203125:ℝ)]]
theorem admission025_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (260537568623/62500000000000:ℝ) admission025_13_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission025_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission025_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission025_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission025_13_coefficients]
def admission025_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(281474976710656/9:ℝ),(281474976710656/3:ℝ),(281474976710656/3:ℝ),(281474976710656/9:ℝ)],
![(562949953421312/9:ℝ),(562949953421312/3:ℝ),(562949953421312/3:ℝ),(562949953421312/9:ℝ)],
![(281474976710656/9:ℝ),(281474976710656/3:ℝ),(281474976710656/3:ℝ),(281474976710656/9:ℝ)]]
theorem admission025_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission025_14_coefficients (117/256:ℝ) (939/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission025_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission025_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (117/256:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission025_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission025_14_coefficients]
theorem admission025_all {δ p : ℝ}
 (hd : δ∈Set.Icc (117/256:ℝ) (939/2048:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission025_00_pos hd hp
 · exact admission025_01_pos hd hp
 · exact admission025_02_pos hd hp
 · exact admission025_03_pos hd hp
 · exact admission025_04_pos hd hp
 · exact admission025_05_pos hd hp
 · exact admission025_06_pos hd hp
 · exact admission025_07_pos hd hp
 · exact admission025_08_pos hd hp
 · exact admission025_09_pos hd hp
 · exact admission025_10_pos hd hp
 · exact admission025_11_pos hd hp
 · exact admission025_12_pos hd hp
 · exact admission025_13_pos hd hp
 · exact admission025_14_pos hd hp
end
end DasStageBFinite
#print axioms DasStageBFinite.admission025_all
