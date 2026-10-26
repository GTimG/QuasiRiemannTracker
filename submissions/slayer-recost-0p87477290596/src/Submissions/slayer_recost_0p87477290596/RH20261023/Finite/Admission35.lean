/- Recertified exact full-window admission coefficients, 2026-10-23.
Original mathematical/formal interface: Hailey Collet and Mark Lewko, Apache-2.0.
Generated source; kernel replay status is recorded separately. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RH20261023Finite
noncomputable section
def admission35_00_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(189620902752067113/786981005458153:ℝ),(187833921746608960/786981005458153:ℝ)]
]
theorem admission35_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (2934905027290765/3147924021832612:ℝ) admission35_00_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission35_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_00_coefficients]
def admission35_01_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(138467137397287168/786981005458153:ℝ),(137467137397287168/786981005458153:ℝ)]
]
theorem admission35_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (536981005458153/786981005458153:ℝ) admission35_01_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission35_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_01_coefficients]
def admission35_02_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(70422330896139254/786981005458153:ℝ),(69941200137369344/786981005458153:ℝ)]
]
theorem admission35_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (273207813036599/786981005458153:ℝ) admission35_02_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission35_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_02_coefficients]
def admission35_03_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(27220558869337033094144/2360943016374459:ℝ),(162225993483379352230912/7082829049123377:ℝ),(80565720875368252948480/7082829049123377:ℝ)],
  ![(27037460128467550138112/2360943016374459:ℝ),(161127873833925878910208/7082829049123377:ℝ),(7274264222593020772352/643893549920307:ℝ)]
]
theorem admission35_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (443985853429749803/879129326824525824:ℝ) admission35_03_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission35_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_03_coefficients]
def admission35_04_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(1428089814175335965160/786981005458153:ℝ),(2824600642119958920192/786981005458153:ℝ),(1396585884342991060992/786981005458153:ℝ)],
  ![(1446196709678658574302/786981005458153:ℝ),(2860612003727689311488/786981005458153:ℝ),(1414490831578157613056/786981005458153:ℝ)]
]
theorem admission35_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (31965314125282083/402934274794574336:ℝ) admission35_04_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission35_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_04_coefficients]
def admission35_05_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(63673449186344750545189/59023575409361475:ℝ),(3185751767419106233988074/1475589385234036875:ℝ),(531282634254515757227783/491863128411345625:ℝ)],
  ![(1529288066000336502293227/1475589385234036875:ℝ),(278278146377721845049902/134144489566730625:ℝ),(102113565039999393399963/98372625682269125:ℝ)]
]
theorem admission35_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (1529288066000336502293227/33008375791171529605120000:ℝ) admission35_05_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission35_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_05_coefficients]
def admission35_06_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(139665537436511413483383864030089765539840/206239921282991172178485579079197:ℝ),(45987544512036426692346523893749632651264/22915546809221241353165064342133:ℝ),(408804647431303786296059767722001052205056/206239921282991172178485579079197:ℝ),(404150898302068217005614260385417789440/619339102951925441977434171409:ℝ)],
  ![(141279369385128861145571520016511449553920/206239921282991172178485579079197:ℝ),(4229381546028192618929053811187012563968/2083231528111021941196824031103:ℝ),(413605005507210245530222365054937335529472/206239921282991172178485579079197:ℝ),(37175966826505538473555804467358597120/56303554813811403816130379219:ℝ)]
]
theorem admission35_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (72267812186849394501259492704645/634203241422771652584892591522816:ℝ) admission35_06_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission35_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_06_coefficients]
def admission35_07_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(10369625432816306785861823744367812488/1858017308855776325932302514227:ℝ),(61717861100940694600411206589030134784/5574051926567328977796907542681:ℝ),(30609978698377059646324246449152819200/5574051926567328977796907542681:ℝ)],
  ![(10210682756899504404635482391180685526/1858017308855776325932302514227:ℝ),(60768096934249235256853191015663939328/5574051926567328977796907542681:ℝ),(30137034821492263874964730195002818560/5574051926567328977796907542681:ℝ)]
]
theorem admission35_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (919709314620735591887351385345545/3805219448536629915509355549136896:ℝ) admission35_07_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission35_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_07_coefficients]
def admission35_08_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(680200036852119108600432700483993494730469053144507421401/54434100845384072048797925221494140625000000000000:ℝ),(47282668947041023977646554380615071744007944636532050979/1209646685452979378862176116033203125000000000000:ℝ),(2214755559723311610016758392397107104798088874204431186293/54434100845384072048797925221494140625000000000000:ℝ),(767233797151785347998059148797958675643548535892496313639/54434100845384072048797925221494140625000000000000:ℝ)],
  ![(1845538577808807864746217205120847070293071086203632248881/108868201690768144097595850442988281250000000000000:ℝ),(633540496445467590488436427188884933481036580149567213349/12096466854529793788621761160332031250000000000000:ℝ),(2933490210595180834641882044778523203602661775430874405109/54434100845384072048797925221494140625000000000000:ℝ),(1005325557811214656066188208822247870273440748875263069479/54434100845384072048797925221494140625000000000000:ℝ)]
]
theorem admission35_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (680200036852119108600432700483993494730469053144507421401/311723577224120722678526406585294520320000000000000000000000:ℝ) admission35_08_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission35_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_08_coefficients]
def admission35_09_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(3011140494770733851636349007357108875967981172/54434100845384072048797925221494140625:ℝ),(8866177855038839500482144207325561379815209628/54434100845384072048797925221494140625:ℝ),(2899767536850807360962091487731093067153380352/18144700281794690682932641740498046875:ℝ),(113770666447541438116405750848888469045141504/2177364033815362881951917008859765625:ℝ)],
  ![(2744944566848865651730643159246748407624630159/54434100845384072048797925221494140625:ℝ),(8072217887792774411543441304669166970602136221/54434100845384072048797925221494140625:ℝ),(2636650868802976092627177773177102621751049984/18144700281794690682932641740498046875:ℝ),(46957831007518124624855479594006547859202048/989710924461528582705416822208984375:ℝ)]
]
theorem admission35_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (5732157105409927322370053661377752424219/691858081552114530092610099843072000000000:ℝ) admission35_09_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission35_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_09_coefficients]
def admission35_10_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(70592584231834480182183333705728/13833650486569095703125:ℝ),(345125799421190645944841162893312/23056084144281826171875:ℝ),(112433779045602888588698792419328/7685361381427275390625:ℝ),(329489679751651460374682311622656/69168252432845478515625:ℝ)],
  ![(672059934883847646135054446642176/69168252432845478515625:ℝ),(59686000282059550823859832935424/2096007649480166015625:ℝ),(1923170356045325042457268273811456/69168252432845478515625:ℝ),(41706171625143000760329882238976/4611216828856365234375:ℝ)],
  ![(35428140378874463299479848999296/7685361381427275390625:ℝ),(28288891185812055037363432360832/2096007649480166015625:ℝ),(182108635712245593066354400566784/13833650486569095703125:ℝ),(295863180155589381294097375920128/69168252432845478515625:ℝ)]
]
theorem admission35_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (9029027714709148599063030271/4126046973896441200640000000000:ℝ) admission35_10_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission35_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_10_coefficients]
def admission35_11_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(25517558456594077766484231908086338920/5574051926567328977796907542681:ℝ),(50626003959624332621853743474186536960/5574051926567328977796907542681:ℝ),(25109397700861245406699741647024373760/5574051926567328977796907542681:ℝ)],
  ![(25116648922664102086736305613422910078/5574051926567328977796907542681:ℝ),(49827522746201123073905841989272208896/5574051926567328977796907542681:ℝ),(24711818016129048128223291197118660608/5574051926567328977796907542681:ℝ)]
]
theorem admission35_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (1508289673836001472669878613105387/7610438897073259831018711098273792:ℝ) admission35_11_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission35_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_11_coefficients]
def admission35_12_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(41135459/5000000000:ℝ)]
]
theorem admission35_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission35_12_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission35_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_12_coefficients]
def admission35_13_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(20350383012772521847/5000000000000000000000:ℝ)]
]
theorem admission35_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (20350383012772521847/5000000000000000000000:ℝ) admission35_13_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission35_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_13_coefficients]
def admission35_14_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(1/2:ℝ)]
]
theorem admission35_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission35_14_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission35_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission35_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission35_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission35_14_coefficients]
theorem admission35_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission35_00_pos hδ hp
 · exact admission35_01_pos hδ hp
 · exact admission35_02_pos hδ hp
 · exact admission35_03_pos hδ hp
 · exact admission35_04_pos hδ hp
 · exact admission35_05_pos hδ hp
 · exact admission35_06_pos hδ hp
 · exact admission35_07_pos hδ hp
 · exact admission35_08_pos hδ hp
 · exact admission35_09_pos hδ hp
 · exact admission35_10_pos hδ hp
 · exact admission35_11_pos hδ hp
 · exact admission35_12_pos hδ hp
 · exact admission35_13_pos hδ hp
 · exact admission35_14_pos hδ hp
#print axioms admission35_all
end
end RH20261023Finite
