/- Recertified exact full-window admission coefficients, 2026-10-23.
Original mathematical/formal interface: Hailey Collet and Mark Lewko, Apache-2.0.
Generated source; kernel replay status is recorded separately. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RH20261023Finite
noncomputable section
def admission48_00_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(189620902752067113/786981005458153:ℝ),(187833921746608960/786981005458153:ℝ)]
]
theorem admission48_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (2934905027290765/3147924021832612:ℝ) admission48_00_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission48_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_00_coefficients]
def admission48_01_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(138467137397287168/786981005458153:ℝ),(137467137397287168/786981005458153:ℝ)]
]
theorem admission48_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (536981005458153/786981005458153:ℝ) admission48_01_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission48_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_01_coefficients]
def admission48_02_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(70422330896139254/786981005458153:ℝ),(69941200137369344/786981005458153:ℝ)]
]
theorem admission48_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (273207813036599/786981005458153:ℝ) admission48_02_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission48_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_02_coefficients]
def admission48_03_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(27128929199608387546880/2360943016374459:ℝ),(161676688260770903362816/7082829049123377:ℝ),(80291313661945740722176/7082829049123377:ℝ)],
  ![(26945830458738904590848/2360943016374459:ℝ),(160578568611317430042112/7082829049123377:ℝ),(79742499235100716269568/7082829049123377:ℝ)]
]
theorem admission48_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (2433547950289938851/4835211297534892032:ℝ) admission48_03_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission48_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_03_coefficients]
def admission48_04_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(1437244236061075298270/786981005458153:ℝ),(2842707056492522759424/786981005458153:ℝ),(1405538357960574337024/786981005458153:ℝ)],
  ![(1455351131564397907412/786981005458153:ℝ),(2878718418100253150720/786981005458153:ℝ),(1423443305195740889088/786981005458153:ℝ)]
]
theorem admission48_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (128680879940238129/1611737099178297344:ℝ) admission48_04_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission48_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_04_coefficients]
def admission48_05_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(1560562147829477632961476/1475589385234036875:ℝ),(56792868614785864670644/26828897913346125:ℝ),(520992519143044010555898/491863128411345625:ℝ)],
  ![(1498013984171195371624978/1475589385234036875:ℝ),(2998915616549056618446268/1475589385234036875:ℝ),(100055542017705044065586/98372625682269125:ℝ)]
]
theorem admission48_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (749006992085597685812489/16504187895585764802560000:ℝ) admission48_05_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission48_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_05_coefficients]
def admission48_06_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(140482710709678325562688838488716240870400/206239921282991172178485579079197:ℝ),(46257644114493273613925364747125401975808/22915546809221241353165064342133:ℝ),(411215029480858638781574320471551709478912/206239921282991172178485579079197:ℝ),(406543266696814570107364054763181178880/619339102951925441977434171409:ℝ)],
  ![(142096542658295773224876494475137924884480/206239921282991172178485579079197:ℝ),(46793296608766965729798432776432907528192/22915546809221241353165064342133:ℝ),(416015387556765098015736917804487992803328/206239921282991172178485579079197:ℝ),(411328003486307276310863643518707957760/619339102951925441977434171409:ℝ)]
]
theorem admission48_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (290782403967486312466166535446535/2536812965691086610339570366091264:ℝ) admission48_06_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission48_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_06_coefficients]
def admission48_07_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(10289506736380303699862068433539018966/1858017308855776325932302514227:ℝ),(61241040811134031028212707269813939968/5574051926567328977796907542681:ℝ),(30373506759934661760644488322077818880/5574051926567328977796907542681:ℝ)],
  ![(10130564060463501318635727080351892004/1858017308855776325932302514227:ℝ),(60291276644442571684654691696447744512/5574051926567328977796907542681:ℝ),(29900562883049865989284972067927818240/5574051926567328977796907542681:ℝ)]
]
theorem admission48_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (456246381882474761799392273985715/1902609724268314957754677774568448:ℝ) admission48_07_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission48_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_07_coefficients]
def admission48_08_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(3205938651513046081947082606088834059754009192492647091683/217736403381536288195191700885976562500000000000000:ℝ),(221073631637882393025684450598696634670272433398852391601/4838586741811917515448704464132812500000000000000:ℝ),(10278545330067014395931472766655512571914248161979645402199/217736403381536288195191700885976562500000000000000:ℝ),(3536163727140288976719401031136131400261630015586434871837/217736403381536288195191700885976562500000000000000:ℝ)],
  ![(4176215659722185377037786214394554221418275152321881903841/217736403381536288195191700885976562500000000000000:ℝ),(1426795772139526666552364019758951605433276434562755365123/24192933709059587577243522320664062500000000000000:ℝ),(13153483933554491294431967376181176967132539766885418277463/217736403381536288195191700885976562500000000000000:ℝ),(4488530769778006208991917271233288178781198867517501895197/217736403381536288195191700885976562500000000000000:ℝ)]
]
theorem admission48_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (3205938651513046081947082606088834059754009192492647091683/1246894308896482890714105626341178081280000000000000000000000:ℝ) admission48_08_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission48_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_08_coefficients]
def admission48_09_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(2875737544736385201002189356022674204560842639/54434100845384072048797925221494140625:ℝ),(8464596821455333059358079894996944361410773661/54434100845384072048797925221494140625:ℝ),(2767443846690495641898723969953028418687262464/18144700281794690682932641740498046875:ℝ),(542694736660203280727719514889257185838465024/10886820169076814409759585044298828125:ℝ)],
  ![(2609541616814517001096483507912313736217491626/54434100845384072048797925221494140625:ℝ),(7670636854209267970419376992340549952197700254/54434100845384072048797925221494140625:ℝ),(2504327178642664373563810255399037973284932096/18144700281794690682932641740498046875:ℝ),(490377545505195461019101036178886867063980032/10886820169076814409759585044298828125:ℝ)]
]
theorem admission48_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (29930270111401090150091615977715262882323/3805219448536629915509355549136896000000000:ℝ) admission48_09_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission48_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_09_coefficients]
def admission48_10_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(335906227677805378971779654886784/69168252432845478515625:ℝ),(328230767311867814687458769862272/23056084144281826171875:ℝ),(192340414273006718632231008902656/13833650486569095703125:ℝ),(104305381474508196856852796604416/23056084144281826171875:ℝ)],
  ![(127491809458300690239828429023744/13833650486569095703125:ℝ),(622271137608945781134454889373184/23056084144281826171875:ℝ),(607106714602399358176195273627648/23056084144281826171875:ℝ),(591966074781082932324363297882112/69168252432845478515625:ℝ)],
  ![(33478785477654777410949261456896/7685361381427275390625:ℝ),(293797969659546158740376876083712/23056084144281826171875:ℝ),(171778981273698680308044727433216/13833650486569095703125:ℝ),(278810215887654172017636362027008/69168252432845478515625:ℝ)]
]
theorem admission48_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (2127153136349900604382601639/1031511743474110300160000000000:ℝ) admission48_10_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission48_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_10_coefficients]
def admission48_11_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(25315438765030200725974530838375766654/5574051926567328977796907542681:ℝ),(50225102430933320352382292439177922048/5574051926567328977796907542681:ℝ),(24910607858495146767461516422071517184/5574051926567328977796907542681:ℝ)],
  ![(24914529231100225046226604543712337812/5574051926567328977796907542681:ℝ),(49426621217510110804434390954263593984/5574051926567328977796907542681:ℝ),(24513028173762949488985065972165804032/5574051926567328977796907542681:ℝ)]
]
theorem admission48_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (748078252373136886260530577763849/3805219448536629915509355549136896:ℝ) admission48_11_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission48_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_11_coefficients]
def admission48_12_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(41135459/5000000000:ℝ)]
]
theorem admission48_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission48_12_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission48_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_12_coefficients]
def admission48_13_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(20350383012772521847/5000000000000000000000:ℝ)]
]
theorem admission48_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (20350383012772521847/5000000000000000000000:ℝ) admission48_13_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission48_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_13_coefficients]
def admission48_14_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(1/2:ℝ)]
]
theorem admission48_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission48_14_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission48_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission48_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission48_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission48_14_coefficients]
theorem admission48_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission48_00_pos hδ hp
 · exact admission48_01_pos hδ hp
 · exact admission48_02_pos hδ hp
 · exact admission48_03_pos hδ hp
 · exact admission48_04_pos hδ hp
 · exact admission48_05_pos hδ hp
 · exact admission48_06_pos hδ hp
 · exact admission48_07_pos hδ hp
 · exact admission48_08_pos hδ hp
 · exact admission48_09_pos hδ hp
 · exact admission48_10_pos hδ hp
 · exact admission48_11_pos hδ hp
 · exact admission48_12_pos hδ hp
 · exact admission48_13_pos hδ hp
 · exact admission48_14_pos hδ hp
#print axioms admission48_all
end
end RH20261023Finite
