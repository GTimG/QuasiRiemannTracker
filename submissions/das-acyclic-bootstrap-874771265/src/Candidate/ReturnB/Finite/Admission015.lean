/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def admission015_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(10624991406533378048/45752193:ℝ),(981980836147553632256/1418317983:ℝ),(975837471487503106048/1418317983:ℝ),(323231368942484193280/1418317983:ℝ)],
![(21249982813066756096/45752193:ℝ),(1963961672295107264512/1418317983:ℝ),(1951674942975006212096/1418317983:ℝ),(646462737884968386560/1418317983:ℝ)],
![(10624991406533378048/45752193:ℝ),(981980836147553632256/1418317983:ℝ),(975837471487503106048/1418317983:ℝ),(323231368942484193280/1418317983:ℝ)]]
theorem admission015_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (587954435/630363548:ℝ) admission015_00_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission015_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission015_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission015_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission015_00_coefficients]
def admission015_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(7742930207589269504/45752193:ℝ),(716656535469002063872/1418317983:ℝ),(713220561632202063872/1418317983:ℝ),(26288318066496372736/157590887:ℝ)],
![(15485860415178539008/45752193:ℝ),(1433313070938004127744/1418317983:ℝ),(1426441123264404127744/1418317983:ℝ),(52576636132992745472/157590887:ℝ)],
![(7742930207589269504/45752193:ℝ),(716656535469002063872/1418317983:ℝ),(713220561632202063872/1418317983:ℝ),(26288318066496372736/157590887:ℝ)]]
theorem admission015_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (107590887/157590887:ℝ) admission015_01_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission015_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission015_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission015_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission015_01_coefficients]
def admission015_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(61495782988191497191424/714878015625:ℝ),(1897756137681069855997952/7387072828125:ℝ),(377828600545640659812352/1477414565625:ℝ),(1880529867775336742125568/22161218484375:ℝ)],
![(122991565976382994382848/714878015625:ℝ),(3795512275362139711995904/7387072828125:ℝ),(755657201091281319624704/1477414565625:ℝ),(3761059735550673484251136/22161218484375:ℝ)],
![(61495782988191497191424/714878015625:ℝ),(1897756137681069855997952/7387072828125:ℝ),(377828600545640659812352/1477414565625:ℝ),(1880529867775336742125568/22161218484375:ℝ)]]
theorem admission015_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218922489762229/630363548000000:ℝ) admission015_02_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission015_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission015_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission015_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission015_02_coefficients]
def admission015_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(539677529891749756928/4254953949:ℝ),(1604611387011041853440/4254953949:ℝ),(1590227461223634436096/4254953949:ℝ),(525293604104342339584/4254953949:ℝ)],
![(1075746537778821726208/4254953949:ℝ),(3198403139710492868608/4254953949:ℝ),(3169641455767720558592/4254953949:ℝ),(1046984853836049416192/4254953949:ℝ)],
![(536069007887071969280/4254953949:ℝ),(1593791752699451015168/4254953949:ℝ),(1579413994544086122496/4254953949:ℝ),(16828749991345389568/137256579:ℝ)]]
theorem admission015_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (31345989539/62466994176:ℝ) admission015_03_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission015_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission015_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission015_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission015_03_coefficients]
def admission015_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(50546102267097549860864/2462357609375:ℝ),(448325406609303334965248/7387072828125:ℝ),(441767040778959516073984/7387072828125:ℝ),(145079940970948830691328/7387072828125:ℝ)],
![(305154577196080498407424/7387072828125:ℝ),(36089719928623292069888/295482913125:ℝ),(889084757910398817009664/7387072828125:ℝ),(97332112296965671223296/2462357609375:ℝ)],
![(153516270394787848824832/7387072828125:ℝ),(151305863868759655593984/2462357609375:ℝ),(29821181142095953395712/492471521875:ℝ),(29383279183989636595712/1477414565625:ℝ)]]
theorem admission015_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (51884630073648273/645492273152000000:ℝ) admission015_04_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission015_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission015_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission015_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission015_04_coefficients]
def admission015_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(16720455553804337492992/1477414565625:ℝ),(753418944712286561895424/22161218484375:ℝ),(754372463795645551932416/22161218484375:ℝ),(251760352390424052431872/22161218484375:ℝ)],
![(10917401309154024312832/492471521875:ℝ),(47612222714515041222656/714878015625:ℝ),(1478018495808752147359744/22161218484375:ℝ),(493322650570716963534848/22161218484375:ℝ)],
![(16031748373657735445504/1477414565625:ℝ),(722559959437679716006912/22161218484375:ℝ),(723646032013106595427328/22161218484375:ℝ),(241562298180292911102976/22161218484375:ℝ)]]
theorem admission015_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (46968012813450396813/1057574540332236800000:ℝ) admission015_05_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission015_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission015_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission015_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission015_05_coefficients]
def admission015_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1306525966660067265804529818202112/43073008294759239984375:ℝ),(34441707912086746191219914352914432/387657074652833159859375:ℝ),(33615479466496662071981950358257664/387657074652833159859375:ℝ),(728832164920567360386853624610816/25843804976855543990625:ℝ)],
![(2627630561595915101272582435760128/43073008294759239984375:ℝ),(69273695008581993427152406848022528/387657074652833159859375:ℝ),(67617929504499153076062514659721216/387657074652833159859375:ℝ),(1466190923001048545837556648902656/25843804976855543990625:ℝ)],
![(42616277255995091466711374759936/1389451880476104515625:ℝ),(34831987096495247235932492495108096/387657074652833159859375:ℝ),(34002450038002491004080564301463552/387657074652833159859375:ℝ),(147471751616096237090140604858368/5168760995371108798125:ℝ)]]
theorem admission015_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (86883564581938667343479827/752755379094757747097600000:ℝ) admission015_06_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission015_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission015_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission015_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission015_06_coefficients]
def admission015_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(639436704644734172424771981561856/10477218233860355671875:ℝ),(1898030861467349421963759050051584/10477218233860355671875:ℝ),(1877831832441276541463011653582848/10477218233860355671875:ℝ),(3995081778184911560800158613504/67594956347486165625:ℝ)],
![(1268995896526741395928632427280384/10477218233860355671875:ℝ),(3766589565377802424104849408260096/10477218233860355671875:ℝ),(120204879148416348390955390861312/337974781737430828125:ℝ),(245751516949969154388680027144192/2095443646772071134375:ℝ)],
![(629559191882007223503860445718528/10477218233860355671875:ℝ),(1868558703910453002141090358208512/10477218233860355671875:ℝ),(1848519421159630258656605463117824/10477218233860355671875:ℝ),(121903981826236896003875110125568/2095443646772071134375:ℝ)]]
theorem admission015_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (29064174133834098816841867/122068439853203958988800000:ℝ) admission015_07_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission015_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission015_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission015_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission015_07_coefficients]
def admission015_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4550922324545615920211964396383734424/6821105621002835723876953125:ℝ),(43486412876873888332514266464659754776/20463316863008507171630859375:ℝ),(46011716082028545619711988095194650792/20463316863008507171630859375:ℝ),(5392616603649737794944616159724533096/6821105621002835723876953125:ℝ)],
![(10424522679315268685383197232686242584/6821105621002835723876953125:ℝ),(98731514493954787807507744247030461816/20463316863008507171630859375:ℝ),(20727574553465455154202420735301816592/4092663372601701434326171875:ℝ),(12059828060300177210832064025756199632/6821105621002835723876953125:ℝ)],
![(1174720070953930553034246567260501632/1364221124200567144775390625:ℝ),(11049020323416179894998695556474141408/4092663372601701434326171875:ℝ),(57626156685298730151300115581314432168/20463316863008507171630859375:ℝ),(6667211456650439415887447866031666536/6821105621002835723876953125:ℝ)]]
theorem admission015_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (568865290568201990026495549547966803/208330137349468090007552000000000000000:ℝ) admission015_08_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission015_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission015_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission015_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission015_08_coefficients]
def admission015_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(74696202714109226868118295175439136/32741306980813611474609375:ℝ),(215943645599934103510238808673090048/32741306980813611474609375:ℝ),(69277412378723508179539387871985664/10913768993604537158203125:ℝ),(13317017581011896381170106974601216/6548261396162722294921875:ℝ)],
![(142437513562669275915958562658330544/32741306980813611474609375:ℝ),(411261978445963886603205892022396672/32741306980813611474609375:ℝ),(131758896658323725222206674461229056/10913768993604537158203125:ℝ),(25290562851935674237602215344734208/6548261396162722294921875:ℝ)],
![(67741310848560049047840267482891408/32741306980813611474609375:ℝ),(195318332846029783092967083349306624/32741306980813611474609375:ℝ),(62481484279600217042667286589243392/10913768993604537158203125:ℝ),(386243395836250898594584140972032/211234238585894267578125:ℝ)]]
theorem admission015_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (736700812981130406560104639/98442290204196741120000000000:ℝ) admission015_09_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission015_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission015_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission015_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission015_09_coefficients]
def admission015_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(42687618338354578559416072/69253807763671875:ℝ),(122403106316054498545946632/69253807763671875:ℝ),(116760267679299884219170048/69253807763671875:ℝ),(37044928900506214232639488/69253807763671875:ℝ)],
![(80949976113914402397960328/69253807763671875:ℝ),(46331163116289938826062312/13850761552734375:ℝ),(220494585907423622934267136/69253807763671875:ℝ),(69789046726294581201915904/69253807763671875:ℝ)],
![(2548755291936917644653406/4616920517578125:ℝ),(36386881455317703258151318/23084602587890625:ℝ),(34547755670252682217295296/23084602587890625:ℝ),(10904701039111754682411008/23084602587890625:ℝ)]]
theorem admission015_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (15973683162761359398063/8262301096345600000000000:ℝ) admission015_10_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission015_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission015_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission015_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission015_10_coefficients]
def admission015_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(524430234243864886239796163227648/10477218233860355671875:ℝ),(518897628702238238943785753153536/3492406077953451890625:ℝ),(513390619785659176555488016334848/3492406077953451890625:ℝ),(16384167983681538679835579121664/337974781737430828125:ℝ)],
![(1040554160916584946012505111267328/10477218233860355671875:ℝ),(205906964692436141113002795956224/698481215590690378125:ℝ),(32856982597700564835318486007808/112658260579143609375:ℝ),(1007649072116195359002082370650112/10477218233860355671875:ℝ)],
![(103224785334544011954541789607936/2095443646772071134375:ℝ),(510637194759942466621228226627584/3492406077953451890625:ℝ),(20207033629722333333575401996288/139696243118138075625:ℝ),(499739864622067659927179417878528/10477218233860355671875:ℝ)]]
theorem admission015_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (119147268443600573522372107/610342199266019794944000000:ℝ) admission015_11_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission015_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission015_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission015_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission015_11_coefficients]
def admission015_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(883326547023364096/439453125:ℝ),(883326547023364096/146484375:ℝ),(883326547023364096/146484375:ℝ),(883326547023364096/439453125:ℝ)],
![(1766653094046728192/439453125:ℝ),(1766653094046728192/146484375:ℝ),(1766653094046728192/146484375:ℝ),(1766653094046728192/439453125:ℝ)],
![(883326547023364096/439453125:ℝ),(883326547023364096/146484375:ℝ),(883326547023364096/146484375:ℝ),(883326547023364096/439453125:ℝ)]]
theorem admission015_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (411330977/50000000000:ℝ) admission015_12_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission015_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission015_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission015_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission015_12_coefficients]
def admission015_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(279750084153785188352/274658203125:ℝ),(279750084153785188352/91552734375:ℝ),(279750084153785188352/91552734375:ℝ),(279750084153785188352/274658203125:ℝ)],
![(559500168307570376704/274658203125:ℝ),(559500168307570376704/91552734375:ℝ),(559500168307570376704/91552734375:ℝ),(559500168307570376704/274658203125:ℝ)],
![(279750084153785188352/274658203125:ℝ),(279750084153785188352/91552734375:ℝ),(279750084153785188352/91552734375:ℝ),(279750084153785188352/274658203125:ℝ)]]
theorem admission015_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (260537568623/62500000000000:ℝ) admission015_13_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission015_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission015_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission015_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission015_13_coefficients]
def admission015_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1099511627776/9:ℝ),(1099511627776/3:ℝ),(1099511627776/3:ℝ),(1099511627776/9:ℝ)],
![(2199023255552/9:ℝ),(2199023255552/3:ℝ),(2199023255552/3:ℝ),(2199023255552/9:ℝ)],
![(1099511627776/9:ℝ),(1099511627776/3:ℝ),(1099511627776/3:ℝ),(1099511627776/9:ℝ)]]
theorem admission015_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission015_14_coefficients (237/512:ℝ) (477/1024:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission015_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission015_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission015_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission015_14_coefficients]
theorem admission015_all {δ p : ℝ}
 (hd : δ∈Set.Icc (237/512:ℝ) (477/1024:ℝ)) (hp : p∈Set.Icc (63/128:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission015_00_pos hd hp
 · exact admission015_01_pos hd hp
 · exact admission015_02_pos hd hp
 · exact admission015_03_pos hd hp
 · exact admission015_04_pos hd hp
 · exact admission015_05_pos hd hp
 · exact admission015_06_pos hd hp
 · exact admission015_07_pos hd hp
 · exact admission015_08_pos hd hp
 · exact admission015_09_pos hd hp
 · exact admission015_10_pos hd hp
 · exact admission015_11_pos hd hp
 · exact admission015_12_pos hd hp
 · exact admission015_13_pos hd hp
 · exact admission015_14_pos hd hp
end
end DasStageBFinite
#print axioms DasStageBFinite.admission015_all
