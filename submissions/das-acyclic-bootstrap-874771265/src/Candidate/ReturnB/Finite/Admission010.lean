/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def admission010_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2656247851633344512/45752193:ℝ),(245495209036888408064/1418317983:ℝ),(243959367871875776512/1418317983:ℝ),(80807842235621048320/1418317983:ℝ)],
![(5312495703266689024/45752193:ℝ),(490990418073776816128/1418317983:ℝ),(487918735743751553024/1418317983:ℝ),(161615684471242096640/1418317983:ℝ)],
![(2656247851633344512/45752193:ℝ),(245495209036888408064/1418317983:ℝ),(243959367871875776512/1418317983:ℝ),(80807842235621048320/1418317983:ℝ)]]
theorem admission010_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (587954435/630363548:ℝ) admission010_00_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission010_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission010_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission010_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission010_00_coefficients]
def admission010_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1935732551897317376/45752193:ℝ),(179164133867250515968/1418317983:ℝ),(178305140408050515968/1418317983:ℝ),(6572079516624093184/157590887:ℝ)],
![(3871465103794634752/45752193:ℝ),(358328267734501031936/1418317983:ℝ),(356610280816101031936/1418317983:ℝ),(13144159033248186368/157590887:ℝ)],
![(1935732551897317376/45752193:ℝ),(179164133867250515968/1418317983:ℝ),(178305140408050515968/1418317983:ℝ),(6572079516624093184/157590887:ℝ)]]
theorem admission010_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (107590887/157590887:ℝ) admission010_01_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission010_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission010_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission010_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission010_01_coefficients]
def admission010_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(15373945747047874297856/714878015625:ℝ),(474439034420267463999488/7387072828125:ℝ),(94457150136410164953088/1477414565625:ℝ),(470132466943834185531392/22161218484375:ℝ)],
![(30747891494095748595712/714878015625:ℝ),(948878068840534927998976/7387072828125:ℝ),(188914300272820329906176/1477414565625:ℝ),(940264933887668371062784/22161218484375:ℝ)],
![(15373945747047874297856/714878015625:ℝ),(474439034420267463999488/7387072828125:ℝ),(94457150136410164953088/1477414565625:ℝ),(470132466943834185531392/22161218484375:ℝ)]]
theorem admission010_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218922489762229/630363548000000:ℝ) admission010_02_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission010_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission010_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission010_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission010_02_coefficients]
def admission010_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(137177021587877003264/4254953949:ℝ),(407919832395136630784/4254953949:ℝ),(404317683316242251776/4254953949:ℝ),(133574872508982624256/4254953949:ℝ)],
![(272549782173415112704/4254953949:ℝ),(810429847634477842432/4254953949:ℝ),(803228633292710346752/4254953949:ℝ),(265348567831647617024/4254953949:ℝ)],
![(135372760585538109440/4254953949:ℝ),(402510015239341211648/4254953949:ℝ),(398910949976468094976/4254953949:ℝ),(131773695322664992768/4254953949:ℝ)]]
theorem admission010_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (245447634389/484119204864:ℝ) admission010_03_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission010_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission010_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission010_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission010_03_coefficients]
def admission010_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(12316613527109213099008/2462357609375:ℝ),(109243849078849230355456/7387072828125:ℝ),(107645766265759122587648/7387072828125:ℝ),(35351757768237531529216/7387072828125:ℝ)],
![(74838662959402878215168/7387072828125:ℝ),(221283790656186276619264/7387072828125:ℝ),(218066870707758137606144/7387072828125:ℝ),(23873914336991579734016/2462357609375:ℝ)],
![(37888822378075238918144/7387072828125:ℝ),(37346647192445682087936/2462357609375:ℝ),(36807034813999671672832/2462357609375:ℝ),(36269985242737207672832/7387072828125:ℝ)]]
theorem admission010_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (50571095135074899/645492273152000000:ℝ) admission010_04_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission010_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission010_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission010_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission010_04_coefficients]
def admission010_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1536851958680903550976/492471521875:ℝ),(207591787787704576811008/22161218484375:ℝ),(207697614066476434936832/22161218484375:ℝ),(69264164419412517919744/22161218484375:ℝ)],
![(8876758162012120282112/1477414565625:ℝ),(79950816587621146135552/4432243696875:ℝ),(80006402448336678324224/4432243696875:ℝ),(26685860346751893035008/4432243696875:ℝ)],
![(4266202285969409629184/1477414565625:ℝ),(192162295150401153866752/22161218484375:ℝ),(192334398175206956684288/22161218484375:ℝ),(64165137314346947255296/22161218484375:ℝ)]]
theorem admission010_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (12498639509676004773/264393635083059200000:ℝ) admission010_05_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission010_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission010_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission010_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission010_05_coefficients]
def admission010_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(10295430893198852720671531879424/1389451880476104515625:ℝ),(8411996139711246567029011938857984/387657074652833159859375:ℝ),(8208747641216397649833485139181568/387657074652833159859375:ℝ),(177944744650184927564788706312192/25843804976855543990625:ℝ)],
![(129121205903243830702679275240448/8614601658951847996875:ℝ),(680765274865069746256572517952512/15506282986113326394375:ℝ),(3322196113637141953143255449993216/77531414930566631971875:ℝ),(360152785880326767661502112464896/25843804976855543990625:ℝ)],
![(326447671827054719172578887940096/43073008294759239984375:ℝ),(8607135731915497089385301009954816/387657074652833159859375:ℝ),(8402232926969312115882792110784512/387657074652833159859375:ℝ),(182208041230141840096713406152704/25843804976855543990625:ℝ)]]
theorem admission010_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (84850666356174911291498521/752755379094757747097600000:ℝ) admission010_06_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission010_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission010_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission010_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission010_06_coefficients]
def admission010_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(166092526491106687562861143309312/10477218233860355671875:ℝ),(493047385625322361920878290582528/10477218233860355671875:ℝ),(487837882093554004779428940087296/10477218233860355671875:ℝ),(32176604591867666084282358562816/2095443646772071134375:ℝ)],
![(2111266429682902584937203346432/67594956347486165625:ℝ),(194271738494439302786084447048704/2095443646772071134375:ℝ),(192203911709256973631130956988416/2095443646772071134375:ℝ),(63381432534987650978099813679104/2095443646772071134375:ℝ)],
![(161153770109743213102405375387648/10477218233860355671875:ℝ),(478311306846874152009543944660992/10477218233860355671875:ℝ),(473181676452730863376225844854784/10477218233860355671875:ℝ),(31204827943119984893817455116288/2095443646772071134375:ℝ)]]
theorem admission010_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (7439810739307399962858547/30517109963300989747200000:ℝ) admission010_07_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission010_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission010_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission010_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission010_07_coefficients]
def admission010_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(476391566024385557573356879136546738/6821105621002835723876953125:ℝ),(5064965615019626742966063278088468242/20463316863008507171630859375:ℝ),(5840539553245117675656577517313363134/20463316863008507171630859375:ℝ),(734898313023751250272956553583386702/6821105621002835723876953125:ℝ)],
![(1614122147160789537626347978232480344/6821105621002835723876953125:ℝ),(16009275600142759057171732215032412616/20463316863008507171630859375:ℝ),(17488299408125327617107218777686616956/20463316863008507171630859375:ℝ),(2107094052547853311017328960320340124/6821105621002835723876953125:ℝ)],
![(1137730581136403980052991099095933606/6821105621002835723876953125:ℝ),(10944309985123132314205668936943944374/20463316863008507171630859375:ℝ),(11647759854880209941450641260373253822/20463316863008507171630859375:ℝ),(1372195739524102060744372406736953422/6821105621002835723876953125:ℝ)]]
theorem admission010_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (238195783012192778786678439568273369/208330137349468090007552000000000000000:ℝ) admission010_08_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission010_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission010_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission010_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission010_08_coefficients]
def admission010_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(23109931962661262303423854103029592/32741306980813611474609375:ℝ),(67054192409642179593180185341922176/32741306980813611474609375:ℝ),(21596270612388945947873200867360768/10913768993604537158203125:ℝ),(4168924589058048173253775871442944/6548261396162722294921875:ℝ)],
![(8548483598509587139341738871957064/6548261396162722294921875:ℝ),(24759145688466439795544901604390528/6548261396162722294921875:ℝ),(1591783087008649853092414043734016/436550759744181486328125:ℝ),(7666113023072037084138552440651776/6548261396162722294921875:ℝ)],
![(19632486029886673393284840256755728/32741306980813611474609375:ℝ),(56741536032690019384544322680030464/32741306980813611474609375:ℝ),(18198306562827300379437150225989632/10913768993604537158203125:ℝ),(3497188434013988910884776569208832/6548261396162722294921875:ℝ)]]
theorem admission010_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (6670357578304269620675614489/762927749082524743680000000000:ℝ) admission010_09_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission010_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission010_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission010_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission010_09_coefficients]
def admission010_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2674300584801976711551658/13850761552734375:ℝ),(38578268119856746974439826/69253807763671875:ℝ),(37047165589490510922036032/69253807763671875:ℝ),(11840435828682710005354496/69253807763671875:ℝ)],
![(24654489152646626430053336/69253807763671875:ℝ),(70949597312152185707732696/69253807763671875:ℝ),(67945561322855717344880384/69253807763671875:ℝ),(21650524953818908067201024/69253807763671875:ℝ)],
![(750130522142045580236792/4616920517578125:ℝ),(10759754764284450974460632/23084602587890625:ℝ),(10269114838666504786544384/23084602587890625:ℝ),(3260024805561031713267712/23084602587890625:ℝ)]]
theorem admission010_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (1193856740317760637183/516393818521600000000000:ℝ) admission010_10_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission010_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission010_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission010_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission010_10_coefficients]
def admission010_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(136350362555088533346639930409984/10477218233860355671875:ℝ),(26984267508166563475621527845888/698481215590690378125:ℝ),(133498930411993122674578644926464/3492406077953451890625:ℝ),(132083141168569449236052947501056/10477218233860355671875:ℝ)],
![(8662824881438859789023750104064/337974781737430828125:ℝ),(265712458110517748594936515195904/3492406077953451890625:ℝ),(262890471302685823741105806639104/3492406077953451890625:ℝ),(260081610901108878898244127555584/10477218233860355671875:ℝ)],
![(1057577670156128960904770582528/83817745870882845375:ℝ),(130791120569684931216828875966464/3492406077953451890625:ℝ),(25878308178138540213305432342528/698481215590690378125:ℝ),(127998469732539429662191180054528/10477218233860355671875:ℝ)]]
theorem admission010_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (30517213280806405463741107/152585549816504948736000000:ℝ) admission010_11_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission010_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission010_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission010_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission010_11_coefficients]
def admission010_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(220831636755841024/439453125:ℝ),(220831636755841024/146484375:ℝ),(220831636755841024/146484375:ℝ),(220831636755841024/439453125:ℝ)],
![(441663273511682048/439453125:ℝ),(441663273511682048/146484375:ℝ),(441663273511682048/146484375:ℝ),(441663273511682048/439453125:ℝ)],
![(220831636755841024/439453125:ℝ),(220831636755841024/146484375:ℝ),(220831636755841024/146484375:ℝ),(220831636755841024/439453125:ℝ)]]
theorem admission010_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (411330977/50000000000:ℝ) admission010_12_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission010_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission010_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission010_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission010_12_coefficients]
def admission010_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(69937521038446297088/274658203125:ℝ),(69937521038446297088/91552734375:ℝ),(69937521038446297088/91552734375:ℝ),(69937521038446297088/274658203125:ℝ)],
![(139875042076892594176/274658203125:ℝ),(139875042076892594176/91552734375:ℝ),(139875042076892594176/91552734375:ℝ),(139875042076892594176/274658203125:ℝ)],
![(69937521038446297088/274658203125:ℝ),(69937521038446297088/91552734375:ℝ),(69937521038446297088/91552734375:ℝ),(69937521038446297088/274658203125:ℝ)]]
theorem admission010_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (260537568623/62500000000000:ℝ) admission010_13_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission010_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission010_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission010_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission010_13_coefficients]
def admission010_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(274877906944/9:ℝ),(274877906944/3:ℝ),(274877906944/3:ℝ),(274877906944/9:ℝ)],
![(549755813888/9:ℝ),(549755813888/3:ℝ),(549755813888/3:ℝ),(549755813888/9:ℝ)],
![(274877906944/9:ℝ),(274877906944/3:ℝ),(274877906944/3:ℝ),(274877906944/9:ℝ)]]
theorem admission010_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission010_14_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission010_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission010_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission010_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission010_14_coefficients]
theorem admission010_all {δ p : ℝ}
 (hd : δ∈Set.Icc (231/512:ℝ) (117/256:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission010_00_pos hd hp
 · exact admission010_01_pos hd hp
 · exact admission010_02_pos hd hp
 · exact admission010_03_pos hd hp
 · exact admission010_04_pos hd hp
 · exact admission010_05_pos hd hp
 · exact admission010_06_pos hd hp
 · exact admission010_07_pos hd hp
 · exact admission010_08_pos hd hp
 · exact admission010_09_pos hd hp
 · exact admission010_10_pos hd hp
 · exact admission010_11_pos hd hp
 · exact admission010_12_pos hd hp
 · exact admission010_13_pos hd hp
 · exact admission010_14_pos hd hp
end
end DasStageBFinite
#print axioms DasStageBFinite.admission010_all
