/- Recertified exact full-window admission coefficients, 2026-10-23.
Original mathematical/formal interface: Hailey Collet and Mark Lewko, Apache-2.0.
Generated source; kernel replay status is recorded separately. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RH20261023Finite
noncomputable section
def admission41_00_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(273375429904654683/71543727768923:ℝ),(3005342747945743360/786981005458153:ℝ)]
]
theorem admission41_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (2934905027290765/3147924021832612:ℝ) admission41_00_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission41_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_00_coefficients]
def admission41_01_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(200043108941508608/71543727768923:ℝ),(2199474198356594688/786981005458153:ℝ)]
]
theorem admission41_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (536981005458153/786981005458153:ℝ) admission41_01_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission41_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_01_coefficients]
def admission41_02_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(101776393905152674/71543727768923:ℝ),(1119059202197909504/786981005458153:ℝ)]
]
theorem admission41_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (273207813036599/786981005458153:ℝ) admission41_02_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission41_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_02_coefficients]
def admission41_03_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(109600720057104072755322880/2360943016374459:ℝ),(657324117179461156614332416/7082829049123377:ℝ),(29865634502377176213487616/643893549920307:ℝ)],
  ![(109553885278102559071817728/2360943016374459:ℝ),(657043116340184289303949312/7082829049123377:ℝ),(328381483032876612088496128/7082829049123377:ℝ)]
]
theorem admission41_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (78292246587962296507/154726761521116545024:ℝ) admission41_03_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission41_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_03_coefficients]
def admission41_04_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(5742233117978945940032580/786981005458153:ℝ),(11476398695935286795526144/786981005458153:ℝ),(5734166781745499297808384/786981005458153:ℝ)],
  ![(5746820008426477692725562/786981005458153:ℝ),(11485569252393890426777600/786981005458153:ℝ),(5738750448237701935136768/786981005458153:ℝ)]
]
theorem admission41_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (1025348922326356047/12893896793426378752:ℝ) admission41_04_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission41_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_04_coefficients]
def admission41_05_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(6356144519484583557059658331/1475589385234036875:ℝ),(2542565519865872677383933686/295117877046807375:ℝ),(2118893998361160916839907533/491863128411345625:ℝ)],
  ![(6340229092850162602317856153/1475589385234036875:ℝ),(12681003199774629673976368078/1475589385234036875:ℝ),(84543640289728164261661909/19674525136453825:ℝ)]
]
theorem admission41_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (6340229092850162602317856153/135202307240638585262571520000:ℝ) admission41_05_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission41_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_05_coefficients]
def admission41_06_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(8860315966427868617019747065572499615589498880/206239921282991172178485579079197:ℝ),(8853395464604503524248695739125061307324268544/68746640427663724059495193026399:ℝ),(26539431390841269763147377326735819857819860992/206239921282991172178485579079197:ℝ),(26545228116793629043508539115246653307617280/619339102951925441977434171409:ℝ)],
  ![(806077038179355841037745163829542806625894400/18749083752999197470771416279927:ℝ),(805447743243601595558588997178533034131275776/6249694584333065823590472093309:ℝ),(26559015298391082156540939934053453154419212288/206239921282991172178485579079197:ℝ),(26564826398683391168118073430789290993909760/619339102951925441977434171409:ℝ)]
]
theorem admission41_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (2317703455639446827423689460432505/20294503725528692882716562928730112:ℝ) admission41_06_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission41_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_06_coefficients]
def admission41_07_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(13803811852891541261429282124911489887772/619339102951925441977434171409:ℝ),(248341490427603474525766179859728607879168/5574051926567328977796907542681:ℝ),(124107199607486105277929733764574745722880/5574051926567328977796907542681:ℝ)],
  ![(13790352334799630000778955412151067170358/619339102951925441977434171409:ℝ),(22554480103639246291456062164414795313152/506731993324302634345173412971:ℝ),(123986125975003597560461697603512345559040/5574051926567328977796907542681:ℝ)]
]
theorem admission41_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (14780297991633844084794723701895755/60883511176586078648149688786190336:ℝ) admission41_07_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission41_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_07_coefficients]
def admission41_08_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(6272566571307885270718386629784123266613269301675821172733349/6804262605673009006099740652686767578125000000000:ℝ),(114311303467167324550705376942692061601287088088903096606511/41237955185897024279392367592041015625000000000:ℝ),(18905027789774361475849596062821631583712926032814316572245777/6804262605673009006099740652686767578125000000000:ℝ),(6316229285597866872121751071928245318993711665998372898654811/6804262605673009006099740652686767578125000000000:ℝ)],
  ![(1598653072198677978500453504630349743019882819000617214632927/1701065651418252251524935163171691894531250000000:ℝ),(3204559908714654297732046097278385025139227835078898478986551/1134043767612168167683290108781127929687500000000:ℝ),(19270879433951839494655705866132813339141717152348746883657489/6804262605673009006099740652686767578125000000000:ℝ),(6438132267055494677852633150660681386644216479045549477644891/6804262605673009006099740652686767578125000000000:ℝ)]
]
theorem admission41_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (6272566571307885270718386629784123266613269301675821172733349/2553639544619996960182488322746732710461440000000000000000000000:ℝ) admission41_08_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission41_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_08_coefficients]
def admission41_09_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(15984236910526532551225093627247905862879714473204/4948554622307642913527084111044921875:ℝ),(526804689519763577185979866393193253926194536832096/54434100845384072048797925221494140625:ℝ),(175376551534340665574358404826701927031182408679424/18144700281794690682932641740498046875:ℝ),(3184574020394163830177779355071651533350810681344/989710924461528582705416822208984375:ℝ)],
  ![(174753974068682202155233040064777565535104312514726/54434100845384072048797925221494140625:ℝ),(523587969835928340853889173547433008160445582359664/54434100845384072048797925221494140625:ℝ),(174304703597144270631259192124536995356689300258816/18144700281794690682932641740498046875:ℝ),(34816023009364890102429071616990490041158626967552/10886820169076814409759585044298828125:ℝ)]
]
theorem admission41_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (1037598341982510390950115669280007184778411/121767022353172157296299377572380672000000000:ℝ) admission41_09_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission41_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_09_coefficients]
def admission41_10_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(323907839209907387394863699030345703424/69168252432845478515625:ℝ),(323399713921303825067818444192440819712/23056084144281826171875:ℝ),(2583133120923141843122509690385727488/184448673154254609375:ℝ),(322383617829587408518599500347671052288/69168252432845478515625:ℝ)],
  ![(129122778346676144037676920316871696384/13833650486569095703125:ℝ),(644598297275002520931367711589829320704/23056084144281826171875:ℝ),(1930748416880292528113999704992620478464/69168252432845478515625:ℝ),(71396379651502466948836796867498999808/7685361381427275390625:ℝ)],
  ![(35745007735887980721253098379967707136/7685361381427275390625:ℝ),(107065866932208350990267800527156803584/7685361381427275390625:ℝ),(192414109978581236222252428883986874368/13833650486569095703125:ℝ),(320182817163466066541692325095232503808/69168252432845478515625:ℝ)]
]
theorem admission41_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (2385547885026529927117320337111/1056268025317488947363840000000000:ℝ) admission41_10_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission41_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_10_coefficients]
def admission41_11_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(101883340471104202233485838356547531424004/5574051926567328977796907542681:ℝ),(203662724074137855066423656503675951464448/5574051926567328977796907542681:ℝ),(101779398790167514901297442976865277968384/5574051926567328977796907542681:ℝ)],
  ![(101781506914304179726929670556750367615002/5574051926567328977796907542681:ℝ),(18496282738731966274544344896723870900224/506731993324302634345173412971:ℝ),(101677618390876072398007471661689415401472/5574051926567328977796907542681:ℝ)]
]
theorem admission41_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (24241833303183572864057414927885393/121767022353172157296299377572380672:ℝ) admission41_11_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission41_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_11_coefficients]
def admission41_12_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(41135459/5000000000:ℝ)]
]
theorem admission41_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission41_12_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission41_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_12_coefficients]
def admission41_13_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(20350383012772521847/5000000000000000000000:ℝ)]
]
theorem admission41_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (20350383012772521847/5000000000000000000000:ℝ) admission41_13_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission41_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_13_coefficients]
def admission41_14_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(1/2:ℝ)]
]
theorem admission41_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission41_14_coefficients (3753/8192:ℝ) (7509/16384:ℝ) (2047/4096:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission41_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission41_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission41_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission41_14_coefficients]
theorem admission41_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (2047/4096:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission41_00_pos hδ hp
 · exact admission41_01_pos hδ hp
 · exact admission41_02_pos hδ hp
 · exact admission41_03_pos hδ hp
 · exact admission41_04_pos hδ hp
 · exact admission41_05_pos hδ hp
 · exact admission41_06_pos hδ hp
 · exact admission41_07_pos hδ hp
 · exact admission41_08_pos hδ hp
 · exact admission41_09_pos hδ hp
 · exact admission41_10_pos hδ hp
 · exact admission41_11_pos hδ hp
 · exact admission41_12_pos hδ hp
 · exact admission41_13_pos hδ hp
 · exact admission41_14_pos hδ hp
#print axioms admission41_all
end
end RH20261023Finite
