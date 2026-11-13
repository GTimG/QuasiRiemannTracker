/- Exact finite certificates generated for Subhanjan Das, AI-assisted with OpenAI Codex.
Uses Hailey Collet's Bernstein and return definitions, Apache-2.0, with inherited notices retained. -/
import Candidate.ReturnB.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace DasStageBFinite
noncomputable section
def admission036_00_coefficients : Fin 3 → Fin 4 → ℝ := ![![(83140405787519187156992/1418317983:ℝ),(249028042024314327793664/1418317983:ℝ),(248634866686071094116352/1418317983:ℝ),(82747230449275953479680/1418317983:ℝ)],
![(166280811575038374313984/1418317983:ℝ),(498056084048628655587328/1418317983:ℝ),(497269733372142188232704/1418317983:ℝ),(165494460898551906959360/1418317983:ℝ)],
![(83140405787519187156992/1418317983:ℝ),(249028042024314327793664/1418317983:ℝ),(248634866686071094116352/1418317983:ℝ),(82747230449275953479680/1418317983:ℝ)]]
theorem admission036_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 2 3 (587954435/630363548:ℝ) admission036_00_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission036_00_coefficients,Fin.sum_univ_succ]
 ring
theorem admission036_00_pos {δ p : ℝ} (hd : δ∈Set.Icc (939/2048:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission036_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission036_00_coefficients]
def admission036_01_coefficients : Fin 3 → Fin 4 → ℝ := ![![(60788187150762842783744/1418317983:ℝ),(182144659126733328351232/1418317983:ℝ),(181924756801178128351232/1418317983:ℝ),(6729809425023071420416/157590887:ℝ)],
![(121576374301525685567488/1418317983:ℝ),(364289318253466656702464/1418317983:ℝ),(363849513602356256702464/1418317983:ℝ),(13459618850046142840832/157590887:ℝ)],
![(60788187150762842783744/1418317983:ℝ),(182144659126733328351232/1418317983:ℝ),(181924756801178128351232/1418317983:ℝ),(6729809425023071420416/157590887:ℝ)]]
theorem admission036_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 2 3 (107590887/157590887:ℝ) admission036_01_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission036_01_coefficients,Fin.sum_univ_succ]
 ring
theorem admission036_01_pos {δ p : ℝ} (hd : δ∈Set.Icc (939/2048:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission036_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission036_01_coefficients]
def admission036_02_coefficients : Fin 3 → Fin 4 → ℝ := ![![(483069368061436584915894272/22161218484375:ℝ),(482518127424453125271977984/7387072828125:ℝ),(481966886787469665628061696/7387072828125:ℝ),(481415646150486205984145408/22161218484375:ℝ)],
![(966138736122873169831788544/22161218484375:ℝ),(965036254848906250543955968/7387072828125:ℝ),(963933773574939331256123392/7387072828125:ℝ),(962831292300972411968290816/22161218484375:ℝ)],
![(483069368061436584915894272/22161218484375:ℝ),(482518127424453125271977984/7387072828125:ℝ),(481966886787469665628061696/7387072828125:ℝ),(481415646150486205984145408/22161218484375:ℝ)]]
theorem admission036_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 2 3 (218922489762229/630363548000000:ℝ) admission036_02_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission036_02_coefficients,Fin.sum_univ_succ]
 ring
theorem admission036_02_pos {δ p : ℝ} (hd : δ∈Set.Icc (939/2048:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission036_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission036_02_coefficients]
def admission036_03_coefficients : Fin 3 → Fin 4 → ℝ := ![![(135855655050323909672960/4254953949:ℝ),(406646983343338371940352/4254953949:ℝ),(405727592303423414861824/4254953949:ℝ),(134936264010408952594432/4254953949:ℝ)],
![(271250005714414744895488/4254953949:ℝ),(811910254667076481318912/4254953949:ℝ),(810071675613782327951360/4254953949:ℝ),(269411426661120591527936/4254953949:ℝ)],
![(4367559698841639845888/137256579:ℝ),(405263271323738109378560/4254953949:ℝ),(404344083310358913089536/4254953949:ℝ),(134475162650711638933504/4254953949:ℝ)]]
theorem admission036_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 2 3 (978435583607/1936476819456:ℝ) admission036_03_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission036_03_coefficients,Fin.sum_univ_succ]
 ring
theorem admission036_03_pos {δ p : ℝ} (hd : δ∈Set.Icc (939/2048:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission036_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission036_03_coefficients]
def admission036_04_coefficients : Fin 3 → Fin 4 → ℝ := ![![(400022959283348027195392/79430890625:ℝ),(111191642328966404212834304/7387072828125:ℝ),(110777372653970062701494272/7387072828125:ℝ),(36787865538355025017831424/7387072828125:ℝ)],
![(74640660205462178398748672/7387072828125:ℝ),(14872741924787433549840384/492471521875:ℝ),(74087088658843763992428544/2462357609375:ℝ),(73810797310181967128428544/7387072828125:ℝ)],
![(37438524992110811869577216/7387072828125:ℝ),(111899486542845099034771456/7387072828125:ℝ),(22296778664512245855158272/1477414565625:ℝ),(2468195451455129474039808/492471521875:ℝ)]]
theorem admission036_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 2 3 (205568217886733031/2581969092608000000:ℝ) admission036_04_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission036_04_coefficients,Fin.sum_univ_succ]
 ring
theorem admission036_04_pos {δ p : ℝ} (hd : δ∈Set.Icc (939/2048:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission036_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission036_04_coefficients]
def admission036_05_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1457689316504108095307776/492471521875:ℝ),(196834933839819887668068352/22161218484375:ℝ),(6351003160142567770308608/714878015625:ℝ),(65642183367284577500348416/22161218484375:ℝ)],
![(8658830177258993772806144/1477414565625:ℝ),(389745347362492724129742848/22161218484375:ℝ),(389841910499280186448248832/22161218484375:ℝ),(129979015795672368910598144/22161218484375:ℝ)],
![(4285762227746669486882816/1477414565625:ℝ),(192910413522672836461674496/22161218484375:ℝ),(192960812534860585568681984/22161218484375:ℝ),(64336832428387791410249728/22161218484375:ℝ)]]
theorem admission036_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 2 3 (784746501662598172647/16921192645315788800000:ℝ) admission036_05_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission036_05_coefficients,Fin.sum_univ_succ]
 ring
theorem admission036_05_pos {δ p : ℝ} (hd : δ∈Set.Icc (939/2048:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission036_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission036_05_coefficients]
def admission036_06_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5092484833377303826415145170550784/698481215590690378125:ℝ),(8426686600726993670912337716627652608/387657074652833159859375:ℝ),(8374516533454101064591963794396151808/387657074652833159859375:ℝ),(184943928332961789846775443161612288/25843804976855543990625:ℝ)],
![(377942284414057161528168205551484928/25843804976855543990625:ℝ),(16902696184199655932129981582633254912/387657074652833159859375:ℝ),(16798251007647216379286912641596915712/387657074652833159859375:ℝ),(370979260590392549301723609482395648/25843804976855543990625:ℝ)],
![(37904069115819383990161566848221184/5168760995371108798125:ℝ),(8476009583472662261217643866005602304/387657074652833159859375:ℝ),(8423734474193115314694948847200763904/387657074652833159859375:ℝ),(37207066451486151890989633264156672/5168760995371108798125:ℝ)]]
theorem admission036_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 2 3 (344484910989109035295947349/3011021516379030988390400000:ℝ) admission036_06_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission036_06_coefficients,Fin.sum_univ_succ]
 ring
theorem admission036_06_pos {δ p : ℝ} (hd : δ∈Set.Icc (939/2048:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission036_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission036_06_coefficients]
def admission036_07_coefficients : Fin 3 → Fin 4 → ℝ := ![![(32214579232575016195313940391903232/2095443646772071134375:ℝ),(481913212592527178214356540200370176/10477218233860355671875:ℝ),(480609035498426419894132208436248576/10477218233860355671875:ℝ),(31953743813754864531269074039078912/2095443646772071134375:ℝ)],
![(64179364312297989720599041881358336/2095443646772071134375:ℝ),(960084614621785172124020042279174144/10477218233860355671875:ℝ),(957481357087446836909920496851615744/10477218233860355671875:ℝ),(63658712805430322677779132795846656/2095443646772071134375:ℝ)],
![(1031122099345902371783390370627584/67594956347486165625:ℝ),(15424883936427677222892371034800128/337974781737430828125:ℝ),(15382978115774852161799622206947328/337974781737430828125:ℝ),(1022740935215337359564840605057024/67594956347486165625:ℝ)]]
theorem admission036_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 2 3 (952501720949390306663551/3937691608167869644800000:ℝ) admission036_07_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission036_07_coefficients,Fin.sum_univ_succ]
 ring
theorem admission036_07_pos {δ p : ℝ} (hd : δ∈Set.Icc (939/2048:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission036_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission036_07_coefficients]
def admission036_08_coefficients : Fin 3 → Fin 4 → ℝ := ![![(332949357400051108298295716932217552528/2273701873667611907958984375:ℝ),(9164930483317263140094127008987108859664/20463316863008507171630859375:ℝ),(1868029509883307333784793110555822429328/4092663372601701434326171875:ℝ),(352417823288529267914383365448374862192/2273701873667611907958984375:ℝ)],
![(720791214540942580161697646055289553728/2273701873667611907958984375:ℝ),(19807361090257605877215272773536677312608/20463316863008507171630859375:ℝ),(20153207151130325443353357779363420589472/20463316863008507171630859375:ℝ),(759218360305088471655660883699187417824/2273701873667611907958984375:ℝ)],
![(15513674285635658874536077164922880048/90948074946704476318359375:ℝ),(10642430606940342737121145764549568452944/20463316863008507171630859375:ℝ),(10813059601713788774429392226584308442832/20463316863008507171630859375:ℝ),(135600179005519734580425839416937518544/757900624555870635986328125:ℝ)]]
theorem admission036_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 2 3 (62428004512509582805930446924790791099/26666257580731915520966656000000000000000:ℝ) admission036_08_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission036_08_coefficients,Fin.sum_univ_succ]
 ring
theorem admission036_08_pos {δ p : ℝ} (hd : δ∈Set.Icc (939/2048:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission036_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission036_08_coefficients]
def admission036_09_coefficients : Fin 3 → Fin 4 → ℝ := ![![(18445751935784339370796430826925516256/32741306980813611474609375:ℝ),(10959303225703821308299813142054893568/6548261396162722294921875:ℝ),(18085455937139659962511625019282423808/10913768993604537158203125:ℝ),(3581120956430324644746011206869843968/6548261396162722294921875:ℝ)],
![(36024124570237704740378322154048733344/32741306980813611474609375:ℝ),(4279938640553522263569333461616723968/1309652279232544458984375:ℝ),(35308575466265077716769103467372347392/10913768993604537158203125:ℝ),(6990277457169370118325558592367755264/6548261396162722294921875:ℝ)],
![(17578372634453365369581891327123217088/32741306980813611474609375:ℝ),(10440389977063790009546854166028726272/6548261396162722294921875:ℝ),(17223119529125417754257478448089923584/10913768993604537158203125:ℝ),(3409156500739045473579547385497911296/6548261396162722294921875:ℝ)]]
theorem admission036_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 2 3 (25400195276283066522922719907/3051710996330098974720000000000:ℝ) admission036_09_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission036_09_coefficients,Fin.sum_univ_succ]
 ring
theorem admission036_09_pos {δ p : ℝ} (hd : δ∈Set.Icc (939/2048:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission036_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission036_09_coefficients]
def admission036_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3462919905289997848446262232/23084602587890625:ℝ),(30793937908560071347300036744/69253807763671875:ℝ),(1216875790047868569985217536/2770152310546875:ℝ),(3338905714674829336723062784/23084602587890625:ℝ)],
![(809387125089226053461868448/2770152310546875:ℝ),(6662580259876026520872209824/7694867529296875:ℝ),(6580333239489737688221749248/7694867529296875:ℝ),(19494456118531083092692566016/69253807763671875:ℝ)],
![(9843981330181300467145376032/69253807763671875:ℝ),(5832697870599337454442490528/13850761552734375:ℝ),(28795325466715827050579677184/69253807763671875:ℝ),(9475818033165596495512600576/69253807763671875:ℝ)]]
theorem admission036_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (18073688570338433257127/8262301096345600000000000:ℝ) admission036_10_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission036_10_coefficients,Fin.sum_univ_succ]
 ring
theorem admission036_10_pos {δ p : ℝ} (hd : δ∈Set.Icc (939/2048:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission036_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission036_10_coefficients]
def admission036_11_coefficients : Fin 3 → Fin 4 → ℝ := ![![(132137194169711552300360994434793472/10477218233860355671875:ℝ),(1054249538557445598657317705793536/27939248623627615125:ℝ),(5257024210606012308936225514848256/139696243118138075625:ℝ),(131070433006120375974083768375836672/10477218233860355671875:ℝ)],
![(263224345329927803398335147890425856/10477218233860355671875:ℝ),(262513799086989870192739929335349248/3492406077953451890625:ℝ),(261804080685219624705714521466994688/3492406077953451890625:ℝ),(261095190124617066937258924285362176/10477218233860355671875:ℝ)],
![(4228617779361814551547553337278464/337974781737430828125:ℝ),(4217180863461586140663716648747008/112658260579143609375:ℝ),(4205757271615139257493834954702848/112658260579143609375:ℝ),(4194347003822473902037908255145984/337974781737430828125:ℝ)]]
theorem admission036_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 2 3 (3906290050430664701422591/19688458040839348224000000:ℝ) admission036_11_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission036_11_coefficients,Fin.sum_univ_succ]
 ring
theorem admission036_11_pos {δ p : ℝ} (hd : δ∈Set.Icc (939/2048:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission036_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission036_11_coefficients]
def admission036_12_coefficients : Fin 3 → Fin 4 → ℝ := ![![(226131596037981208576/439453125:ℝ),(226131596037981208576/146484375:ℝ),(226131596037981208576/146484375:ℝ),(226131596037981208576/439453125:ℝ)],
![(452263192075962417152/439453125:ℝ),(452263192075962417152/146484375:ℝ),(452263192075962417152/146484375:ℝ),(452263192075962417152/439453125:ℝ)],
![(226131596037981208576/439453125:ℝ),(226131596037981208576/146484375:ℝ),(226131596037981208576/146484375:ℝ),(226131596037981208576/439453125:ℝ)]]
theorem admission036_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 2 3 (411330977/50000000000:ℝ) admission036_12_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission036_12_coefficients,Fin.sum_univ_succ]
 ring
theorem admission036_12_pos {δ p : ℝ} (hd : δ∈Set.Icc (939/2048:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission036_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission036_12_coefficients]
def admission036_13_coefficients : Fin 3 → Fin 4 → ℝ := ![![(71616021543369008218112/274658203125:ℝ),(71616021543369008218112/91552734375:ℝ),(71616021543369008218112/91552734375:ℝ),(71616021543369008218112/274658203125:ℝ)],
![(143232043086738016436224/274658203125:ℝ),(143232043086738016436224/91552734375:ℝ),(143232043086738016436224/91552734375:ℝ),(143232043086738016436224/274658203125:ℝ)],
![(71616021543369008218112/274658203125:ℝ),(71616021543369008218112/91552734375:ℝ),(71616021543369008218112/91552734375:ℝ),(71616021543369008218112/274658203125:ℝ)]]
theorem admission036_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 2 3 (260537568623/62500000000000:ℝ) admission036_13_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission036_13_coefficients,Fin.sum_univ_succ]
 ring
theorem admission036_13_pos {δ p : ℝ} (hd : δ∈Set.Icc (939/2048:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission036_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission036_13_coefficients]
def admission036_14_coefficients : Fin 3 → Fin 4 → ℝ := ![![(281474976710656/9:ℝ),(281474976710656/3:ℝ),(281474976710656/3:ℝ),(281474976710656/9:ℝ)],
![(562949953421312/9:ℝ),(562949953421312/3:ℝ),(562949953421312/3:ℝ),(562949953421312/9:ℝ)],
![(281474976710656/9:ℝ),(281474976710656/3:ℝ),(281474976710656/3:ℝ),(281474976710656/9:ℝ)]]
theorem admission036_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 2 3 (1/2:ℝ) admission036_14_coefficients (939/2048:ℝ) (471/1024:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,naturalM,lowerM,upperM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission036_14_coefficients,Fin.sum_univ_succ]
 ring
theorem admission036_14_pos {δ p : ℝ} (hd : δ∈Set.Icc (939/2048:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission036_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hd hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission036_14_coefficients]
theorem admission036_all {δ p : ℝ}
 (hd : δ∈Set.Icc (939/2048:ℝ) (471/1024:ℝ)) (hp : p∈Set.Icc (255/512:ℝ) (1/2:ℝ)) :
 ∀j:Fin 15,0<admissionGuard .C δ p j := by
 intro j
 fin_cases j
 · exact admission036_00_pos hd hp
 · exact admission036_01_pos hd hp
 · exact admission036_02_pos hd hp
 · exact admission036_03_pos hd hp
 · exact admission036_04_pos hd hp
 · exact admission036_05_pos hd hp
 · exact admission036_06_pos hd hp
 · exact admission036_07_pos hd hp
 · exact admission036_08_pos hd hp
 · exact admission036_09_pos hd hp
 · exact admission036_10_pos hd hp
 · exact admission036_11_pos hd hp
 · exact admission036_12_pos hd hp
 · exact admission036_13_pos hd hp
 · exact admission036_14_pos hd hp
end
end DasStageBFinite
#print axioms DasStageBFinite.admission036_all
