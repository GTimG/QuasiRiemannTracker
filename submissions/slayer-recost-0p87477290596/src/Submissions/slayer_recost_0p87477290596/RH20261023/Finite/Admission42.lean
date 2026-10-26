/- Recertified exact full-window admission coefficients, 2026-10-23.
Original mathematical/formal interface: Hailey Collet and Mark Lewko, Apache-2.0.
Generated source; kernel replay status is recorded separately. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RH20261023Finite
noncomputable section
def admission42_00_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(6012472476896944873/786981005458153:ℝ),(6010685495891486720/786981005458153:ℝ)]
]
theorem admission42_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (2934905027290765/3147924021832612:ℝ) admission42_00_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission42_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_00_coefficients]
def admission42_01_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(4399948396713189376/786981005458153:ℝ),(4398948396713189376/786981005458153:ℝ)]
]
theorem admission42_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (536981005458153/786981005458153:ℝ) admission42_01_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission42_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_01_coefficients]
def admission42_02_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(2238599535154588918/786981005458153:ℝ),(2238118404395819008/786981005458153:ℝ)]
]
theorem admission42_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (273207813036599/786981005458153:ℝ) admission42_02_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission42_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_02_coefficients]
def admission42_03_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(2629015520767299973937594368/7082829049123377:ℝ),(1752303439651315609401589760/2360943016374459:ℝ),(2627894843222646854267174912/7082829049123377:ℝ)],
  ![(2628453519097746239316828160/7082829049123377:ℝ),(1751928777100767929514844160/2360943016374459:ℝ),(2627332857249557549227704320/7082829049123377:ℝ)]
]
theorem admission42_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (156601241663071963145/309453523042233090048:ℝ) admission42_03_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission42_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_03_coefficients]
def admission42_04_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(45905597191319464066734216/786981005458153:ℝ),(91778929037705141564571648/786981005458153:ℝ),(45873334253963994382467072/786981005458153:ℝ)],
  ![(45923938304717802088007038/786981005458153:ℝ),(91815604816591159376388096/786981005458153:ℝ),(45891668919932804931780608/786981005458153:ℝ)]
]
theorem admission42_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (1025348922326356047/12893896793426378752:ℝ) admission42_04_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission42_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_04_coefficients]
def admission42_05_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(16939464961689864217686854983/491863128411345625:ℝ),(20327787934506956415992277394/295117877046807375:ℝ),(50820542617942595268220247021/1475589385234036875:ℝ)],
  ![(3383649739035104503632025533/98372625682269125:ℝ),(20302330996001966586098893714/295117877046807375:ℝ),(2030276268981084541785597173/59023575409361475:ℝ)]
]
theorem admission42_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (10150949217105313510896076599/216323691585021736420114432000:ℝ) admission42_05_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission42_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_05_coefficients]
def admission42_06_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(47199663142649951616267703423373759297879146496/68746640427663724059495193026399:ℝ),(424630928256691542054023489787912921167688761344/206239921282991172178485579079197:ℝ),(424464914236144841420899263222937812097036189696/206239921282991172178485579079197:ℝ),(424723649868698064696136625843946452921876480/619339102951925441977434171409:ℝ)],
  ![(47217073383379781914924815743527829000475607040/68746640427663724059495193026399:ℝ),(424787599520557220513942289158670456860017131520/206239921282991172178485579079197:ℝ),(3509269128932029590449695973364601037007093760/1704462159363563406433765116357:ℝ),(424880436123816161693012900368287554412216320/619339102951925441977434171409:ℝ)]
]
theorem admission42_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (2317703455639446827423689460432505/20294503725528692882716562928730112:ℝ) admission42_06_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission42_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_06_coefficients]
def admission42_07_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(993123846157261886878182833174888724856312/5574051926567328977796907542681:ℝ),(220637696004485856606292271656806977404928/619339102951925441977434171409:ℝ),(992615449594923826788501797794473165455360/5574051926567328977796907542681:ℝ)],
  ![(992639427574380412495112360547816660801250/5574051926567328977796907542681:ℝ),(220530061215033238660806589796075719680000/619339102951925441977434171409:ℝ),(992131155064993795918629653150223564800000/5574051926567328977796907542681:ℝ)]
]
theorem admission42_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (29567812534123474237878014241165625/121767022353172157296299377572380672:ℝ) admission42_07_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission42_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_07_coefficients]
def admission42_08_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(8377976774102150361275267833195931372203202579047007580464587/567021883806084083841645054390563964843750000000:ℝ),(75489116397200202116074061595618286138149765006979548629149207/1701065651418252251524935163171691894531250000000:ℝ),(274823415206949797023901554966759388839703747164747841400143/6185693277884553641908855138806152343750000000:ℝ),(2802361456146284165281638589695742247313146237061750393795431/189007294602028027947215018130187988281250000000:ℝ)],
  ![(16918586002092175673108253776209698330267831055212787579270031/1134043767612168167683290108781127929687500000000:ℝ),(152441639407333560922478878422182363976731624167973867551937069/3402131302836504503049870326343383789062500000000:ℝ),(76307999770461555617571683655367321889298836028981616433421277/1701065651418252251524935163171691894531250000000:ℝ),(2829451007581312566555167940525172484568813973294456300237671/189007294602028027947215018130187988281250000000:ℝ)]
]
theorem admission42_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (8377976774102150361275267833195931372203202579047007580464587/3404852726159995946909984430328976947281920000000000000000000000:ℝ) admission42_08_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission42_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_08_coefficients]
def admission42_09_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(2803539218221094644674087924827980131177420608554424/54434100845384072048797925221494140625:ℝ),(152822134099365885248623008698782703034957701339776/989710924461528582705416822208984375:ℝ),(2799939156948739169282560129069188554409810158682112/18144700281794690682932641740498046875:ℝ),(559627862729489185993183161337419962566941517807616/10886820169076814409759585044298828125:ℝ)],
  ![(558992573340741201491364819519357461460623665898698/10886820169076814409759585044298828125:ℝ),(1675898604880393823161419700330323738105249929575712/10886820169076814409759585044298828125:ℝ),(558273188180107069783926650496915058239566382891008/3628940056358938136586528348099609375:ℝ),(111582706601944377951394230205407709592267838717952/2177364033815362881951917008859765625:ℝ)]
]
theorem admission42_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (415677974380345560429223739375947824091717/48706808941268862918519751028952268800000000:ℝ) admission42_09_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission42_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_09_coefficients]
def admission42_10_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(10323051743787492203419223875922089934848/69168252432845478515625:ℝ),(10314922563042567909204148149614491795456/23056084144281826171875:ℝ),(10306793794308836576810396598856333656064/23056084144281826171875:ℝ),(10298665437735951426862969223647615516672/69168252432845478515625:ℝ)],
  ![(1374059376372070172330603087650143174656/4611216828856365234375:ℝ),(1123343865370905521763246987765794701312/1257604589688099609375:ℝ),(2469406228970433835163811647898246971392/2766730097313819140625:ℝ),(456936306105365800483627848557546962944/1537072276285455078125:ℝ)],
  ![(37410294700764294775448385640746815488/251520917937619921875:ℝ),(112142259393243684086571065085381988352/251520917937619921875:ℝ),(22410727834417366396789849845672706048/50304183587523984375:ℝ),(37321674480151853727514069783728357376/251520917937619921875:ℝ)]
]
theorem admission42_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (34758517965815825134063204549/15363898550072566507110400000000:ℝ) admission42_10_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission42_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_10_coefficients]
def admission42_11_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(814447365872236259395833933043825796579848/5574051926567328977796907542681:ℝ),(1628478965020725769462914284568922579337216/5574051926567328977796907542681:ℝ),(814031629522757234203799601184570498613248/5574051926567328977796907542681:ℝ)],
  ![(814040137968058568339551931289139398641950/5574051926567328977796907542681:ℝ),(1627664615527387547356882674028792385945600/5574051926567328977796907542681:ℝ),(813624507925591464190639715923867048345600/5574051926567328977796907542681:ℝ)]
]
theorem admission42_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (48495799775456873428263647313348475/243534044706344314592598755144761344:ℝ) admission42_11_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission42_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_11_coefficients]
def admission42_12_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(41135459/5000000000:ℝ)]
]
theorem admission42_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission42_12_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission42_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_12_coefficients]
def admission42_13_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(20350383012772521847/5000000000000000000000:ℝ)]
]
theorem admission42_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (20350383012772521847/5000000000000000000000:ℝ) admission42_13_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission42_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_13_coefficients]
def admission42_14_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(1/2:ℝ)]
]
theorem admission42_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission42_14_coefficients (3753/8192:ℝ) (15015/32768:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission42_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission42_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission42_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission42_14_coefficients]
theorem admission42_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (3753/8192:ℝ) (15015/32768:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission42_00_pos hδ hp
 · exact admission42_01_pos hδ hp
 · exact admission42_02_pos hδ hp
 · exact admission42_03_pos hδ hp
 · exact admission42_04_pos hδ hp
 · exact admission42_05_pos hδ hp
 · exact admission42_06_pos hδ hp
 · exact admission42_07_pos hδ hp
 · exact admission42_08_pos hδ hp
 · exact admission42_09_pos hδ hp
 · exact admission42_10_pos hδ hp
 · exact admission42_11_pos hδ hp
 · exact admission42_12_pos hδ hp
 · exact admission42_13_pos hδ hp
 · exact admission42_14_pos hδ hp
#print axioms admission42_all
end
end RH20261023Finite
