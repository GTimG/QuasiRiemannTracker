/- Recertified exact full-window admission coefficients, 2026-10-23.
Original mathematical/formal interface: Hailey Collet and Mark Lewko, Apache-2.0.
Generated source; kernel replay status is recorded separately. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RH20261023Finite
noncomputable section
def admission40_00_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(1504458354978329833/786981005458153:ℝ),(1502671373972871680/786981005458153:ℝ)]
]
theorem admission40_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (2934905027290765/3147924021832612:ℝ) admission40_00_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission40_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_00_coefficients]
def admission40_01_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(1100737099178297344/786981005458153:ℝ),(1099737099178297344/786981005458153:ℝ)]
]
theorem admission40_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (536981005458153/786981005458153:ℝ) admission40_01_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission40_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_01_coefficients]
def admission40_02_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(560010731857724662/786981005458153:ℝ),(559529601098954752/786981005458153:ℝ)]
]
theorem admission40_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (273207813036599/786981005458153:ℝ) admission40_02_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission40_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_02_coefficients]
def admission40_03_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(41144079262388957664188416/7082829049123377:ℝ),(27406032158329031782991872/2360943016374459:ℝ),(41074028471598137684787200/7082829049123377:ℝ)],
  ![(41108951221704768703897600/7082829049123377:ℝ),(27382614767328274941239296/2360943016374459:ℝ),(41038904348280056119820288/7082829049123377:ℝ)]
]
theorem admission40_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (9784437262601865797/19340845190139568128:ℝ) admission40_03_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission40_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_03_coefficients]
def admission40_04_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(718787732723838683360802/786981005458153:ℝ),(1435557978547446874429440/786981005458153:ℝ),(716770847718187412226048/786981005458153:ℝ)],
  ![(719935261565119279760152/786981005458153:ℝ),(1437851423530647371390976/786981005458153:ℝ),(717916764341238071558144/786981005458153:ℝ)]
]
theorem admission40_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (1025348922326356047/12893896793426378752:ℝ) admission40_04_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission40_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_04_coefficients]
def admission40_05_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(4821090048779328202722822/8942965971115375:ℝ),(1591094898567875914768762952/1475589385234036875:ℝ),(72328590739876201968123052/134144489566730625:ℝ)],
  ![(23984829934941437801677084/44714829855576875:ℝ),(1583137185467444273744652488/1475589385234036875:ℝ),(791637254800170613925583716/1475589385234036875:ℝ)]
]
theorem admission40_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (17988622451206078351257813/384097463751814162677760000:ℝ) admission40_05_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission40_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_05_coefficients]
def admission40_06_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(185022582811649327082917474649453445854748672/68746640427663724059495193026399:ℝ),(1662606431285362415803741883668053931932590080/206239921282991172178485579079197:ℝ),(1660011243312856506989357754833764566333128704/206239921282991172178485579079197:ℝ),(1659076757299601815219283694702915831726080/619339102951925441977434171409:ℝ)],
  ![(185294944590371441737348700562524841045950464/68746640427663724059495193026399:ℝ),(1665056379574111304761251022420827266888335360/206239921282991172178485579079197:ℝ),(1662459884749325560027132809009786009407193088/206239921282991172178485579079197:ℝ),(151047867503256552799588680376885958410240/56303554813811403816130379219:ℝ)]
]
theorem admission40_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (2317703455639446827423689460432505/20294503725528692882716562928730112:ℝ) admission40_06_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission40_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_06_coefficients]
def admission40_07_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(15552747784076986937073193577807795750782/5574051926567328977796907542681:ℝ),(10357902303029885258880872014640421853184/1858017308855776325932302514227:ℝ),(15520967052965919892082968980638243225600/5574051926567328977796907542681:ℝ)],
  ![(15522448356915041321727992148281320970344/5574051926567328977796907542681:ℝ),(10337713027181675658500628699623178641408/1858017308855776325932302514227:ℝ),(15490698644845292962715959940372643184640/5574051926567328977796907542681:ℝ)]
]
theorem admission40_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (1846635180097257252063269608065205/7610438897073259831018711098273792:ℝ) admission40_07_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission40_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_07_coefficients]
def admission40_08_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(4304912240837255272926092265700883812362977264475415647431/74978100337994589598895213803710937500000000000:ℝ),(428171340428708199084579993787142958912854271508782934665209/2474277311153821456763542055522460937500000000000:ℝ),(4731717428897923544655760222454461780907849002151516851629433/27217050422692036024398962610747070312500000000000:ℝ),(528171940267504790545954310992890440837994831637990879276529/9072350140897345341466320870249023437500000000000:ℝ)],
  ![(4473215995617795818442895413474510727576728390394624731233/74978100337994589598895213803710937500000000000:ℝ),(444820426268900939269660201762463919264142447155206944969907/2474277311153821456763542055522460937500000000000:ℝ),(196588584035558394194621876306679577394435316084607291782241/1088682016907681440975958504429882812500000000000:ℝ),(548489103843776091501101324114963118779745633812520309108209/9072350140897345341466320870249023437500000000000:ℝ)]
]
theorem admission40_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (4304912240837255272926092265700883812362977264475415647431/1758704920537187989106396916492240158720000000000000000000000:ℝ) admission40_08_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission40_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_08_coefficients]
def admission40_09_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(11064847260567051164004849454894226259105457327142/54434100845384072048797925221494140625:ℝ),(33110127321517824628275060056572185657889074034456/54434100845384072048797925221494140625:ℝ),(11008578749026850035172199896653575737020059762688/18144700281794690682932641740498046875:ℝ),(87843649579553145366797058875467513199272656896/435472806763072576390383401771953125:ℝ)],
  ![(10930621211834537232936859821699799445600238136904/54434100845384072048797925221494140625:ℝ),(32707743357324338821516342770443816238566214690592/54434100845384072048797925221494140625:ℝ),(10874548774084571317851460026610890834459464237056/18144700281794690682932641740498046875:ℝ),(2169304837617464630479113810786978226769280106496/10886820169076814409759585044298828125:ℝ)]
]
theorem admission40_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (129300644255725421338028538870035304234581/15220877794146519662037422196547584000000000:ℝ) admission40_09_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission40_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_09_coefficients]
def admission40_10_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(10204179740309736582376998855184595968/69168252432845478515625:ℝ),(10172415476773787053009730184855540736/23056084144281826171875:ℝ),(10140657643897732835303776757486485504/23056084144281826171875:ℝ),(10108906251034900218321638573077430272/69168252432845478515625:ℝ)],
  ![(2252291640147399932767044558266474496/7685361381427275390625:ℝ),(60621534863769973753514421295540707328/69168252432845478515625:ℝ),(60431233911063280451650058111806603264/69168252432845478515625:ℝ),(89245883677073386802395723736285184/307414455257091015625:ℝ)],
  ![(402652881186094913054319815394050048/2766730097313819140625:ℝ),(30103919717016453366549890469395808256/69168252432845478515625:ℝ),(2728081138226710526591306914232532992/6288022948440498046875:ℝ),(9971294842498020877312480972013305856/69168252432845478515625:ℝ)]
]
theorem admission40_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (37145967939861196567537192151/16504187895585764802560000000000:ℝ) admission40_10_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission40_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_10_coefficients]
def admission40_11_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(12754775340744291869254808631661429002370/5574051926567328977796907542681:ℝ),(25483553870904015354192799796099651194880/5574051926567328977796907542681:ℝ),(12728786123726654519117803579306651156480/5574051926567328977796907542681:ℝ)],
  ![(12729303658164521760094079322926985332632/5574051926567328977796907542681:ℝ),(25432637096506623582619854133830896697344/5574051926567328977796907542681:ℝ),(12703341023903793893295310750512685514752/5574051926567328977796907542681:ℝ)]
]
theorem admission40_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (3028712516761730645488574683788463/15220877794146519662037422196547584:ℝ) admission40_11_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission40_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_11_coefficients]
def admission40_12_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(41135459/5000000000:ℝ)]
]
theorem admission40_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission40_12_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission40_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_12_coefficients]
def admission40_13_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(20350383012772521847/5000000000000000000000:ℝ)]
]
theorem admission40_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (20350383012772521847/5000000000000000000000:ℝ) admission40_13_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission40_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_13_coefficients]
def admission40_14_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(1/2:ℝ)]
]
theorem admission40_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission40_14_coefficients (3753/8192:ℝ) (939/2048:ℝ) (1023/2048:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission40_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission40_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission40_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission40_14_coefficients]
theorem admission40_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (939/2048:ℝ))
 (hp : p ∈ Set.Icc (1023/2048:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission40_00_pos hδ hp
 · exact admission40_01_pos hδ hp
 · exact admission40_02_pos hδ hp
 · exact admission40_03_pos hδ hp
 · exact admission40_04_pos hδ hp
 · exact admission40_05_pos hδ hp
 · exact admission40_06_pos hδ hp
 · exact admission40_07_pos hδ hp
 · exact admission40_08_pos hδ hp
 · exact admission40_09_pos hδ hp
 · exact admission40_10_pos hδ hp
 · exact admission40_11_pos hδ hp
 · exact admission40_12_pos hδ hp
 · exact admission40_13_pos hδ hp
 · exact admission40_14_pos hδ hp
#print axioms admission40_all
end
end RH20261023Finite
