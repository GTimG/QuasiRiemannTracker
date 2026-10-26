/- Recertified exact full-window admission coefficients, 2026-10-23.
Original mathematical/formal interface: Hailey Collet and Mark Lewko, Apache-2.0.
Generated source; kernel replay status is recorded separately. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RH20261023Finite
noncomputable section
def admission28_00_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(48745461442110393/786981005458153:ℝ),(46958480436652240/786981005458153:ℝ)]
]
theorem admission28_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (2934905027290765/3147924021832612:ℝ) admission28_00_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission28_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_00_coefficients]
def admission28_01_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(35366784349321792/786981005458153:ℝ),(34366784349321792/786981005458153:ℝ)]
]
theorem admission28_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (536981005458153/786981005458153:ℝ) admission28_01_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission28_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_01_coefficients]
def admission28_02_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(17966430793112246/786981005458153:ℝ),(17485300034342336/786981005458153:ℝ)]
]
theorem admission28_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (273207813036599/786981005458153:ℝ) admission28_02_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission28_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_02_coefficients]
def admission28_03_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(441066186772407996928/2360943016374459:ℝ),(2577390336285126189568/7082829049123377:ℝ),(1254551775967902198784/7082829049123377:ℝ)],
  ![(429594653232851286208/2360943016374459:ℝ),(2508665833988642029120/7082829049123377:ℝ),(1220250874290088170496/7082829049123377:ℝ)]
]
theorem admission28_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (1191651244423914229/2417605648767446016:ℝ) admission28_03_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission28_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_03_coefficients]
def admission28_04_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(24415100648281858160/786981005458153:ℝ),(46777039461889251840/786981005458153:ℝ),(22381184043958190080/786981005458153:ℝ)],
  ![(25585007765587859366/786981005458153:ℝ),(49065524650634392640/786981005458153:ℝ),(23500243246156099584/786981005458153:ℝ)]
]
theorem admission28_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (4098117195548985/50366784349321792:ℝ) admission28_04_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission28_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_04_coefficients]
def admission28_05_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(4866058838095136496347/295117877046807375:ℝ),(9783520222155884013494/295117877046807375:ℝ),(1637997640893066289049/98372625682269125:ℝ)],
  ![(4069001640163483292981/295117877046807375:ℝ),(41048721981071574464146/1475589385234036875:ℝ),(6895312638557907055997/491863128411345625:ℝ)]
]
theorem admission28_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (4069001640163483292981/103151174347411030016000:ℝ) admission28_05_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission28_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_05_coefficients]
def admission28_06_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(620085432431929789766192407816838379520/206239921282991172178485579079197:ℝ),(592233631799981436017301696727442401280/68746640427663724059495193026399:ℝ),(1694784171838183818761208755879258193920/206239921282991172178485579079197:ℝ),(1616095202660365739893021241783091200/619339102951925441977434171409:ℝ)],
  ![(646283704987949590969837657112311958272/206239921282991172178485579079197:ℝ),(617988495487406251337532231783438592256/68746640427663724059495193026399:ℝ),(1770746299111874388210616909495373459456/206239921282991172178485579079197:ℝ),(1690856714996189274322702316088197120/619339102951925441977434171409:ℝ)]
]
theorem admission28_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (9247370925867266120298507166575/79275405177846456573111573940352:ℝ) admission28_06_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission28_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_06_coefficients]
def admission28_07_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(5100774317502534100298959620177200/56303554813811403816130379219:ℝ),(979321964529152186545564099468664320/5574051926567328977796907542681:ℝ),(474586043123979090010070130032465920/5574051926567328977796907542681:ℝ)],
  ![(52715647105915624281039636655714794/619339102951925441977434171409:ℝ),(919234876688085764915878801433365696/5574051926567328977796907542681:ℝ),(445027050818679354300100364148090880/5574051926567328977796907542681:ℝ)]
]
theorem admission28_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (217298364657558278466845880931685/951304862134157478877338887284224:ℝ) admission28_07_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission28_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_07_coefficients]
def admission28_08_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(1658753101551805294757287755676880168542901293513097263/21773640338153628819519170088597656250000000000000:ℝ),(1802841126833641089433282621273061301084088185753028891/7257880112717876273173056696199218750000000000000:ℝ),(48271736186912732070004379108825122329371153175582667/179947440811187015037348513128906250000000000000:ℝ),(2090935768200728594103662383977977564103327520499513297/21773640338153628819519170088597656250000000000000:ℝ)],
  ![(13040505364120764587291995705110101267647834011245451439/87094561352614515278076680354390625000000000000000:ℝ),(67316823331833620876099842719573119298609003446970070001/145157602254357525463461133923984375000000000000000:ℝ),(52082924066601363086331807776684875370183975423129765807/108868201690768144097595850442988281250000000000000:ℝ),(325364479302014706320860819011798639140013986512891411/1979421848923057165410833644417968750000000000000:ℝ)]
]
theorem admission28_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (1658753101551805294757287755676880168542901293513097263/487068089412688629185197510289522688000000000000000000000:ℝ) admission28_08_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission28_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_08_coefficients]
def admission28_09_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(2586514364655768909498242780210455823356402/10886820169076814409759585044298828125:ℝ),(7289308347980234552690826307659744946205858/10886820169076814409759585044298828125:ℝ),(454841529622723018621444891319935885752064/725788011271787627317305669619921875:ℝ),(2119901315078919065342654355036160882181504/10886820169076814409759585044298828125:ℝ)],
  ![(6843053678271052582810202402252905785386269/43547280676307257639038340177195312500:ℝ),(94424905558401830830756924871007929361813289/217736403381536288195191700885976562500:ℝ),(7188088164533578938811471071117037768925872/18144700281794690682932641740498046875:ℝ),(1302445203281921882395490625186624651330176/10886820169076814409759585044298828125:ℝ)]
]
theorem admission28_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (10175353150640014706214770509270505088517/1902609724268314957754677774568448000000000:ℝ) admission28_09_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission28_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_09_coefficients]
def admission28_10_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(393401375622089314603306803712/69168252432845478515625:ℝ),(365143873488567737885110323712/23056084144281826171875:ℝ),(1011114297062448993400741531136/69168252432845478515625:ℝ),(103031204906278364782905787904/23056084144281826171875:ℝ)],
  ![(640813590066547060836432062464/69168252432845478515625:ℝ),(587032440379292543227268422144/23056084144281826171875:ℝ),(533514383600147039970304781824/23056084144281826171875:ℝ),(480279022854110551065541141504/69168252432845478515625:ℝ)],
  ![(2458706662997866282316923328/698669216493388671875:ℝ),(72658106462127995979845951648/7685361381427275390625:ℝ),(52540074678529409678038945568/6288022948440498046875:ℝ),(167439869543022804589190245888/69168252432845478515625:ℝ)]
]
theorem admission28_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (327030995201216415213262199/257877935868527575040000000000:ℝ) admission28_10_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission28_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_10_coefficients]
def admission28_11_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(37643487807902932825209960877634896/506731993324302634345173412971:ℝ),(803076569457134701762813503172621312/5574051926567328977796907542681:ℝ),(389228247788986668241586194094867456/5574051926567328977796907542681:ℝ)],
  ![(388391169362502773147306010604337414/5574051926567328977796907542681:ℝ),(752548647875906294204507050658681728/5574051926567328977796907542681:ℝ),(364379517493224338336808040975760384/5574051926567328977796907542681:ℝ)]
]
theorem admission28_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (355839372551976892907039102515391/1902609724268314957754677774568448:ℝ) admission28_11_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission28_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_11_coefficients]
def admission28_12_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(41135459/5000000000:ℝ)]
]
theorem admission28_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission28_12_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission28_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_12_coefficients]
def admission28_13_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(20350383012772521847/5000000000000000000000:ℝ)]
]
theorem admission28_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (20350383012772521847/5000000000000000000000:ℝ) admission28_13_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission28_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_13_coefficients]
def admission28_14_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(1/2:ℝ)]
]
theorem admission28_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission28_14_coefficients (15/32:ℝ) (123/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission28_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_14_coefficients]
theorem admission28_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (123/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission28_00_pos hδ hp
 · exact admission28_01_pos hδ hp
 · exact admission28_02_pos hδ hp
 · exact admission28_03_pos hδ hp
 · exact admission28_04_pos hδ hp
 · exact admission28_05_pos hδ hp
 · exact admission28_06_pos hδ hp
 · exact admission28_07_pos hδ hp
 · exact admission28_08_pos hδ hp
 · exact admission28_09_pos hδ hp
 · exact admission28_10_pos hδ hp
 · exact admission28_11_pos hδ hp
 · exact admission28_12_pos hδ hp
 · exact admission28_13_pos hδ hp
 · exact admission28_14_pos hδ hp
#print axioms admission28_all
end
end RH20261023Finite
