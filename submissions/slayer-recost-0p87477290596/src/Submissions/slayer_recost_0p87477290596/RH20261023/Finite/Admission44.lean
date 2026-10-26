/- Recertified exact full-window admission coefficients, 2026-10-23.
Original mathematical/formal interface: Hailey Collet and Mark Lewko, Apache-2.0.
Generated source; kernel replay status is recorded separately. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RH20261023Finite
noncomputable section
def admission44_00_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(12023157972788431593/786981005458153:ℝ),(12021370991782973440/786981005458153:ℝ)]
]
theorem admission44_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (2934905027290765/3147924021832612:ℝ) admission44_00_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission44_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_00_coefficients]
def admission44_01_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(8798896793426378752/786981005458153:ℝ),(8797896793426378752/786981005458153:ℝ)]
]
theorem admission44_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (536981005458153/786981005458153:ℝ) admission44_01_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission44_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_01_coefficients]
def admission44_02_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(4476717939550407926/786981005458153:ℝ),(4476236808791638016/786981005458153:ℝ)]
]
theorem admission44_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (273207813036599/786981005458153:ℝ) admission44_02_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission44_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_02_coefficients]
def admission44_03_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(7008089795748464588085690368/2360943016374459:ℝ),(42044056127098032768157646848/7082829049123377:ℝ),(21019786829942639003900575744/7082829049123377:ℝ)],
  ![(7007340470650369228312199168/2360943016374459:ℝ),(42039560207902389468679290880/7082829049123377:ℝ),(21017538886050281783742693376/7082829049123377:ℝ)]
]
theorem admission44_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (313185734838996556159/618907046084466180096:ℝ) admission44_03_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission44_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_03_coefficients]
def admission44_04_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(33380825947146208235917940/71543727768923:ℝ),(66749917572552417505935360/71543727768923:ℝ),(33369092063235199750635520/71543727768923:ℝ)],
  ![(367262436976861456977500146/786981005458153:ℝ),(734395783519723870386176000/786981005458153:ℝ),(367133351359462439454244864/786981005458153:ℝ)]
]
theorem admission44_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (372928664794957635/4688689743064137728:ℝ) admission44_04_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission44_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_04_coefficients]
def admission44_05_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(81233915364982302446670004379/295117877046807375:ℝ),(14769959931015003789587967802/26828897913346125:ℝ),(27078547669400092835415992981/98372625682269125:ℝ)],
  ![(81183001487885611252344520769/295117877046807375:ℝ),(811838683247113383234083121526/1475589385234036875:ℝ),(135307890489113155212306207977/491863128411345625:ℝ)]
]
theorem admission44_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (81183001487885611252344520769/1730589532680173891360915456000:ℝ) admission44_05_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission44_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_05_coefficients]
def admission44_06_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(2264673460417771246694128094645176155546875330560/206239921282991172178485579079197:ℝ),(754743566876477675170813246969417623953706188800/22915546809221241353165064342133:ℝ),(6791363926556839576606829615961753855574503587840/206239921282991172178485579079197:ℝ),(6796832687940113811113196209697872058672742400/619339102951925441977434171409:ℝ)],
  ![(2265091222591411481373491979947180400524098404352/206239921282991172178485579079197:ℝ),(754882811645808816372330157353624762363222228992/22915546809221241353165064342133:ℝ),(6792617045890814448300403007177736550653190209536/206239921282991172178485579079197:ℝ),(6798086977981058587088206405892600870595461120/619339102951925441977434171409:ℝ)]
]
theorem admission44_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (9272524977777876044155886406357975/81178014902114771530866251714920448:ℝ) admission44_06_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission44_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_06_coefficients]
def admission44_07_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(2646683618736402258153915644337980868917740/1858017308855776325932302514227:ℝ),(15878068622380867082617563036437512829501440/5574051926567328977796907542681:ℝ),(7938017829579810429088781514490287719710720/5574051926567328977796907542681:ℝ)],
  ![(2646037809997107235899811059665346540839482/1858017308855776325932302514227:ℝ),(15874194018050999836119332184367351787831296/5574051926567328977796907542681:ℝ),(7936080651460090305609292935913289317089280/5574051926567328977796907542681:ℝ)]
]
theorem admission44_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (59128408517391162407467461644957135/243534044706344314592598755144761344:ℝ) admission44_07_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission44_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_07_coefficients]
def admission44_08_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(80888640024790004271615288598440391333412516470513204042316797/340213130283650450304987032634338378906250000000:ℝ),(26978378686577798042731080059280670644385761555748288398868031/37801458920405605589443003626037597656250000000:ℝ),(48588978836004621890635959335999363175093117231541060930834229/68042626056730090060997406526867675781250000000:ℝ),(81028126024932441113416119287365517395320070719218410176988163/340213130283650450304987032634338378906250000000:ℝ)],
  ![(40639421866271402917653891796937496798975208346002187719227671/170106565141825225152493516317169189453125000000:ℝ),(67771084757812613779221942611188842407951035786330983743561601/94503647301014013973607509065093994140625000000:ℝ),(1220576384809300060347435177447596504834461268536362601360145453/1701065651418252251524935163171691894531250000000:ℝ),(81418215565596850091754941939309312811801686120969375229756419/340213130283650450304987032634338378906250000000:ℝ)]
]
theorem admission44_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (80888640024790004271615288598440391333412516470513204042316797/32686586171135961090335850531158178693906432000000000000000000000:ℝ) admission44_08_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission44_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_08_coefficients]
def admission44_09_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(8942105870421425432467919285976455502914233172345812/10886820169076814409759585044298828125:ℝ),(26817685288598015199378116349296295900973891121378432/10886820169076814409759585044298828125:ℝ),(8936351088397700861272030453433154508029653908717568/3628940056358938136586528348099609375:ℝ),(8933473847034619421056386457674142425803836394307584/10886820169076814409759585044298828125:ℝ)],
  ![(8928387470556627201997064988912781570327298660617702/10886820169076814409759585044298828125:ℝ),(133882669256692302119714764964591817955364799098013376/54434100845384072048797925221494140625:ℝ),(44613175983400343100184204554619691195188310082322432/18144700281794690682932641740498046875:ℝ),(8919759209276481051166690375191091108959017800564736/10886820169076814409759585044298828125:ℝ)]
]
theorem admission44_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (4153586555866748584046350035439753490015407/487068089412688629185197510289522688000000000:ℝ) admission44_09_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission44_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_09_coefficients]
def admission44_10_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(329102388425989862083210824228021692956672/69168252432845478515625:ℝ),(109657470700741777053173914768131540353024/7685361381427275390625:ℝ),(986527317210542123089701750297950647484416/69168252432845478515625:ℝ),(328712469330454843854503591612788477263872/69168252432845478515625:ℝ)],
  ![(657641245892884728831660345119252858896384/69168252432845478515625:ℝ),(219127111748009874799635629009157244878848/7685361381427275390625:ℝ),(1971364293528388944556885512324115031130112/69168252432845478515625:ℝ),(656861533690382624162918946360952686116864/69168252432845478515625:ℝ)],
  ![(36504310512300799267965214987756377120768/7685361381427275390625:ℝ),(109469620097036486410635723792421328969728/7685361381427275390625:ℝ),(328278929260746664738954851107605059731456/23056084144281826171875:ℝ),(109383000506739260583248012193610204184576/23056084144281826171875:ℝ)]
]
theorem admission44_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (38201571619163474737403918590959/16900288405079823157821440000000000:ℝ) admission44_10_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission44_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_10_coefficients]
def admission44_11_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(6511472766036406699800468413005004566401596/5574051926567328977796907542681:ℝ),(13021283011902944983005287964548919731617792/5574051926567328977796907542681:ℝ),(6509810306599063253551437497912343287300096/5574051926567328977796907542681:ℝ)],
  ![(6509844067041725016624994915449484524804434/5574051926567328977796907542681:ℝ),(13018025826527605458740585202425845543763968/5574051926567328977796907542681:ℝ),(6508181820210400173498797956869529486229504/5574051926567328977796907542681:ℝ)]
]
theorem admission44_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (96979466381824019156378477169119261/487068089412688629185197510289522688:ℝ) admission44_11_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission44_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_11_coefficients]
def admission44_12_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(41135459/5000000000:ℝ)]
]
theorem admission44_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission44_12_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission44_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_12_coefficients]
def admission44_13_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(20350383012772521847/5000000000000000000000:ℝ)]
]
theorem admission44_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (20350383012772521847/5000000000000000000000:ℝ) admission44_13_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission44_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_13_coefficients]
def admission44_14_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(1/2:ℝ)]
]
theorem admission44_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission44_14_coefficients (15015/32768:ℝ) (30033/65536:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission44_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission44_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission44_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission44_14_coefficients]
theorem admission44_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (30033/65536:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission44_00_pos hδ hp
 · exact admission44_01_pos hδ hp
 · exact admission44_02_pos hδ hp
 · exact admission44_03_pos hδ hp
 · exact admission44_04_pos hδ hp
 · exact admission44_05_pos hδ hp
 · exact admission44_06_pos hδ hp
 · exact admission44_07_pos hδ hp
 · exact admission44_08_pos hδ hp
 · exact admission44_09_pos hδ hp
 · exact admission44_10_pos hδ hp
 · exact admission44_11_pos hδ hp
 · exact admission44_12_pos hδ hp
 · exact admission44_13_pos hδ hp
 · exact admission44_14_pos hδ hp
#print axioms admission44_all
end
end RH20261023Finite
