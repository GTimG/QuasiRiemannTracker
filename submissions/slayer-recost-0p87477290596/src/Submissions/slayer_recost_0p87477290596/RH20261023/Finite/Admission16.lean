/- Recertified exact full-window admission coefficients, 2026-10-23.
Original mathematical/formal interface: Hailey Collet and Mark Lewko, Apache-2.0.
Generated source; kernel replay status is recorded separately. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RH20261023Finite
noncomputable section
def admission16_00_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(95703941878762633/786981005458153:ℝ),(93916960873304480/786981005458153:ℝ)]
]
theorem admission16_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (2934905027290765/3147924021832612:ℝ) admission16_00_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission16_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_00_coefficients]
def admission16_01_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(69733568698643584/786981005458153:ℝ),(68733568698643584/786981005458153:ℝ)]
]
theorem admission16_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (536981005458153/786981005458153:ℝ) admission16_01_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission16_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_01_coefficients]
def admission16_02_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(35451730827454582/786981005458153:ℝ),(34970600068684672/786981005458153:ℝ)]
]
theorem admission16_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (273207813036599/786981005458153:ℝ) admission16_02_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission16_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_02_coefficients]
def admission16_03_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(10448194145496897494656/7082829049123377:ℝ),(6873706319983790399360/2360943016374459:ℝ),(10173617814454473703424/7082829049123377:ℝ)],
  ![(10310754140903929173760/7082829049123377:ℝ),(6782155449549048921344/2360943016374459:ℝ),(10036414207743217590272/7082829049123377:ℝ)]
]
theorem admission16_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (1225148218718654491/2417605648767446016:ℝ) admission16_03_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission16_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_03_coefficients]
def admission16_04_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(16375331726972627514/71543727768923:ℝ),(32038792642431971200/71543727768923:ℝ),(15666828830770733056/71543727768923:ℝ)],
  ![(184706100504947954164/786981005458153:ℝ),(361479926253033602816/786981005458153:ℝ),(176811353947269701632/786981005458153:ℝ)]
]
theorem admission16_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (5737364073768579/73260777235377152:ℝ) admission16_04_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission16_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_04_coefficients]
def admission16_05_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(70224758784032510773452/491863128411345625:ℝ),(421699678644260354962196/1475589385234036875:ℝ),(42198403670273083377118/295117877046807375:ℝ)],
  ![(64978694845003049177486/491863128411345625:ℝ),(390425813593955571084572/1475589385234036875:ℝ),(195455911560476324214614/1475589385234036875:ℝ)]
]
theorem admission16_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (97468042267504573766229/2063023486948220600320000:ℝ) admission16_05_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission16_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_05_coefficients]
def admission16_06_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(2981748561368809366257294603412685494784/68746640427663724059495193026399:ℝ),(26195980817419062035124264174912097062400/206239921282991172178485579079197:ℝ),(25562560707082826709921797967971147235328/206239921282991172178485579079197:ℝ),(24960385094535969425132166976868188160/619339102951925441977434171409:ℝ)],
  ![(3049855419535414050783570872020411390976/68746640427663724059495193026399:ℝ),(26803732010285348626633782786174136898560/206239921282991172178485579079197:ℝ),(26165156219471539831300436155358811553792/206239921282991172178485579079197:ℝ),(2323497926656596154597237779209912320/56303554813811403816130379219:ℝ)]
]
theorem admission16_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (142824469153610054541390420781335/1268406482845543305169785183045632:ℝ) admission16_06_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission16_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_06_coefficients]
def admission16_07_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(4041843132606995663510390345969695714/5574051926567328977796907542681:ℝ),(884029195659293450355672240312075136/619339102951925441977434171409:ℝ),(3914924314213031662920440103797227520/5574051926567328977796907542681:ℝ)],
  ![(3921661218981119248770495009553912396/5574051926567328977796907542681:ℝ),(857539179558923251900200055911175424/619339102951925441977434171409:ℝ),(3796688344991832720080561040259727360/5574051926567328977796907542681:ℝ)]
]
theorem admission16_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (231731466369130415043979555679915/951304862134157478877338887284224:ℝ) admission16_07_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission16_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_07_coefficients]
def admission16_08_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(64919264966117891363906085909995766455358871184738865937/145157602254357525463461133923984375000000000000000:ℝ),(680621248056021262057887638757689527418720369612909968333/435472806763072576390383401771953125000000000000000:ℝ),(776737514813300703599303822046232821610770645915211884391/435472806763072576390383401771953125000000000000000:ℝ),(32318595716018805126599845209633287910115551997946501541/48385867418119175154487044641328125000000000000000:ℝ)],
  ![(147280275616636364213255939396918245645544571522121746619/145157602254357525463461133923984375000000000000000:ℝ),(1412806452097864600577256110194108604827333811771878024651/435472806763072576390383401771953125000000000000000:ℝ),(1499931534578751228645163946736197435330239809419798054503/435472806763072576390383401771953125000000000000000:ℝ),(58773235789288728245280851878998753980103575662698363301/48385867418119175154487044641328125000000000000000:ℝ)]
]
theorem admission16_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (64919264966117891363906085909995766455358871184738865937/51953929537353453779754401097549086720000000000000000000000:ℝ) admission16_08_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission16_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_08_coefficients]
def admission16_09_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(448705166730571123083440540500230093151335793/108868201690768144097595850442988281250:ℝ),(1301789683414940468003690016641810081035057229/108868201690768144097595850442988281250:ℝ),(209610637204175380999747692411019200319155136/18144700281794690682932641740498046875:ℝ),(40458069935638682509059779519374863961714688/10886820169076814409759585044298828125:ℝ)],
  ![(190497382502456342172067136746440398021158931/54434100845384072048797925221494140625:ℝ),(550495126740544930081204481241749156312328103/54434100845384072048797925221494140625:ℝ),(176529714664097451233905812966503038202625664/18144700281794690682932641740498046875:ℝ),(33918421041262705045482469680578574114904064/10886820169076814409759585044298828125:ℝ)]
]
theorem admission16_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (16561729024054055197989487148720006892043/1902609724268314957754677774568448000000000:ℝ) admission16_09_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission16_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_09_coefficients]
def admission16_10_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(2671280858478688980980379669568/13833650486569095703125:ℝ),(38535480141186466310533540412096/69168252432845478515625:ℝ),(37006888611451445173711280780672/69168252432845478515625:ℝ),(11827848197697486268079638716416/69168252432845478515625:ℝ)],
  ![(24627970532151212320786726797056/69168252432845478515625:ℝ),(70874979651657858628175383183616/69168252432845478515625:ℝ),(67875888271524041943564045976064/69168252432845478515625:ℝ),(21628950942486145636175389589504/69168252432845478515625:ℝ)],
  ![(749372644771376980480922661632/4611216828856365234375:ℝ),(10749196221598385673417780822272/23056084144281826171875:ℝ),(10259367022622963488038061720064/23056084144281826171875:ℝ),(3257046145350212717024894205952/23056084144281826171875:ℝ)]
]
theorem admission16_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (596382961184731332463054359/257877935868527575040000000000:ℝ) admission16_10_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission16_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_10_coefficients]
def admission16_11_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(3317168069104269299104457802938167966/5574051926567328977796907542681:ℝ),(6529904868444753278714669668056634112/5574051926567328977796907542681:ℝ),(3213220903494942665551802165235367936/5574051926567328977796907542681:ℝ)],
  ![(3216104220702849073711369638255474868/5574051926567328977796907542681:ℝ),(6329454104099247143978944150552326656/5574051926567328977796907542681:ℝ),(3113825982311893345932689552758939648/5574051926567328977796907542681:ℝ)]
]
theorem admission16_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (380105710731432293204674017670769/1902609724268314957754677774568448:ℝ) admission16_11_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission16_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_11_coefficients]
def admission16_12_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(41135459/5000000000:ℝ)]
]
theorem admission16_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission16_12_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission16_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_12_coefficients]
def admission16_13_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(20350383012772521847/5000000000000000000000:ℝ)]
]
theorem admission16_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (20350383012772521847/5000000000000000000000:ℝ) admission16_13_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission16_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_13_coefficients]
def admission16_14_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(1/2:ℝ)]
]
theorem admission16_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission16_14_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission16_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_14_coefficients]
theorem admission16_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission16_00_pos hδ hp
 · exact admission16_01_pos hδ hp
 · exact admission16_02_pos hδ hp
 · exact admission16_03_pos hδ hp
 · exact admission16_04_pos hδ hp
 · exact admission16_05_pos hδ hp
 · exact admission16_06_pos hδ hp
 · exact admission16_07_pos hδ hp
 · exact admission16_08_pos hδ hp
 · exact admission16_09_pos hδ hp
 · exact admission16_10_pos hδ hp
 · exact admission16_11_pos hδ hp
 · exact admission16_12_pos hδ hp
 · exact admission16_13_pos hδ hp
 · exact admission16_14_pos hδ hp
#print axioms admission16_all
end
end RH20261023Finite
