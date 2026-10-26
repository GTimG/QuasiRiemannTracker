/- Recertified exact full-window admission coefficients, 2026-10-23.
Original mathematical/formal interface: Hailey Collet and Mark Lewko, Apache-2.0.
Generated source; kernel replay status is recorded separately. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RH20261023Finite
noncomputable section
def admission43_00_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(6012472476896944873/786981005458153:ℝ),(6010685495891486720/786981005458153:ℝ)]
]
theorem admission43_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (2934905027290765/3147924021832612:ℝ) admission43_00_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission43_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_00_coefficients]
def admission43_01_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(4399948396713189376/786981005458153:ℝ),(4398948396713189376/786981005458153:ℝ)]
]
theorem admission43_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (536981005458153/786981005458153:ℝ) admission43_01_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission43_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_01_coefficients]
def admission43_02_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(2238599535154588918/786981005458153:ℝ),(2238118404395819008/786981005458153:ℝ)]
]
theorem admission43_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (273207813036599/786981005458153:ℝ) admission43_02_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission43_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_02_coefficients]
def admission43_03_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(2628734512084290891836563456/7082829049123377:ℝ),(1752116105758464364528001024/2360943016374459:ℝ),(2627613850236102201747439616/7082829049123377:ℝ)],
  ![(2628172510414737157215797248/7082829049123377:ℝ),(159249222109810607694659584/214631183306769:ℝ),(2627051864263012896707969024/7082829049123377:ℝ)]
]
theorem admission43_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (78292246587962296507/154726761521116545024:ℝ) admission43_03_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission43_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_03_coefficients]
def admission43_04_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(4174070088339399710304570/71543727768923:ℝ),(8345206377329304438824960/71543727768923:ℝ),(4171136507904399968829440/71543727768923:ℝ)],
  ![(45933112085131734834623092/786981005458153:ℝ),(91833945929508366638891008/786981005458153:ℝ),(45900836252917210206437376/786981005458153:ℝ)]
]
theorem admission43_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (372928664794957635/4688689743064137728:ℝ) admission43_04_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission43_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_04_coefficients]
def admission43_05_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(16928856828432693367923491324/491863128411345625:ℝ),(101575303779552858029074650524/1475589385234036875:ℝ),(50788731124298626093930020302/1475589385234036875:ℝ)],
  ![(16907640561918351668396764006/491863128411345625:ℝ),(101448019087027908879607732124/1475589385234036875:ℝ),(50725095230883144370349702606/1475589385234036875:ℝ)]
]
theorem admission43_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (25361460842877527502595146009/540809228962554341050286080000:ℝ) admission43_05_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission43_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_05_coefficients]
def admission43_06_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(47208371746220727531598182507426897867761745920/68746640427663724059495193026399:ℝ),(424709284786125731064002590033762076665592381440/206239921282991172178485579079197:ℝ),(424543249866344090994473513652208345283433594880/206239921282991172178485579079197:ℝ),(424802042996257113194574763106117003667046400/619339102951925441977434171409:ℝ)],
  ![(47225781986950557830255294827580967570358206464/68746640427663724059495193026399:ℝ),(424865956049991409523921389404519612357920751616/206239921282991172178485579079197:ℝ),(424699900230974830017987463206387258664255750144/206239921282991172178485579079197:ℝ),(424958829251375210191451037630458105157386240/619339102951925441977434171409:ℝ)]
]
theorem admission43_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (9272524977777876044155886406357975/81178014902114771530866251714920448:ℝ) admission43_06_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission43_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_06_coefficients]
def admission43_07_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(992881574839345427930048432869941461128930/5574051926567328977796907542681:ℝ),(220583871718358797646347939200992341975040/619339102951925441977434171409:ℝ),(992373302329958811353565725472348365127680/5574051926567328977796907542681:ℝ)],
  ![(992397156256463953546977960242869397073868/5574051926567328977796907542681:ℝ),(220476236928906179700862257340261084250112/619339102951925441977434171409:ℝ),(991889007800028780483693580828098764472320/5574051926567328977796907542681:ℝ)]
]
theorem admission43_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (14780297991633844084794723701895755/60883511176586078648149688786190336:ℝ) admission43_07_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission43_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_07_coefficients]
def admission43_08_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(6734907910059295279131757888520312214934847242661360548039841/453617507044867267073316043512451171875000000000:ℝ),(12136783469187049891597531754240168307228416610475151333552257/272170504226920360243989626107470703125000000000:ℝ),(60753661399371069583053454326621753456888502208371502793723479/1360852521134601801219948130537353515625000000000:ℝ),(2252718642472525056540286478432282281930956118827646878967413/151205835681622422357772014504150390625000000000:ℝ)],
  ![(33999804458072226296774225662237232246397088007544347576880919/2268087535224336335366580217562255859375000000000:ℝ),(61269279991108512134119960863579158216314920713981664785216747/1360852521134601801219948130537353515625000000000:ℝ),(27881322668277890332660208708285702465269430297869214014740473/618569327788455364190885513880615234375000000000:ℝ),(454878056724109555511821991819165294347098061562762320824241/30241167136324484471554402900830078125000000000:ℝ)]
]
theorem admission43_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (6734907910059295279131757888520312214934847242661360548039841/2723882180927996757527987544263181557825536000000000000000000000:ℝ) admission43_08_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission43_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_08_coefficients]
def admission43_09_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(559849738200624849609470824674548168763424828007626/10886820169076814409759585044298828125:ℝ),(1678470099460044767515737715795895860013653415902496/10886820169076814409759585044298828125:ℝ),(559130353039990717902032655652105765542367544999936/3628940056358938136586528348099609375:ℝ),(558770697869605537875077156182229255264140355698688/10886820169076814409759585044298828125:ℝ)],
  ![(2790672339485735610830090296141548019942821860977196/54434100845384072048797925221494140625:ℝ),(1673325229247413852942304320439609864734368630740672/10886820169076814409759585044298828125:ℝ),(2787078549151749769147236401675915564499859480772608/18144700281794690682932641740498046875:ℝ),(557056368149838241638865145871847840658538031480832/10886820169076814409759585044298828125:ℝ)]
]
theorem admission43_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (1037598341982510390950115669280007184778411/121767022353172157296299377572380672000000000:ℝ) admission43_09_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission43_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_09_coefficients]
def admission43_10_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(3435147125173675569660173612894410805248/23056084144281826171875:ℝ),(30891952331574550061003687260913621266432/69168252432845478515625:ℝ),(30867581770756415732782687900233545285632/69168252432845478515625:ℝ),(1142341201650289491199842664222572937216/7685361381427275390625:ℝ)],
  ![(20575654190881362959498607465025065730048/69168252432845478515625:ℝ),(20559411578011107557547625330556209184768/23056084144281826171875:ℝ),(20543169787299914392547390559536952639488/23056084144281826171875:ℝ),(20526928819047269369966653151967296094208/69168252432845478515625:ℝ)],
  ![(10270204956276956932226570238717149888512/69168252432845478515625:ℝ),(6157251765865737153216018350191963979776/13833650486569095703125:ℝ),(30761904022132870091781425915290110132224/69168252432845478515625:ℝ),(10245850149230914129334154403047440121856/69168252432845478515625:ℝ)]
]
theorem admission43_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (2385547885026529927117320337111/1056268025317488947363840000000000:ℝ) admission43_10_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission43_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_10_coefficients]
def admission43_11_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(814243698766641453346131873919491123775774/5574051926567328977796907542681:ℝ),(1628071737124553317370042559289495836213248/5574051926567328977796907542681:ℝ),(813828068724174349197219658554218773479424/5574051926567328977796907542681:ℝ)],
  ![(813836470862463762289849872164804725837876/5574051926567328977796907542681:ℝ),(1627257387631215095264010948749365642821632/5574051926567328977796907542681:ℝ),(813420947127008579184059773293515323211776/5574051926567328977796907542681:ℝ)]
]
theorem admission43_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (24241833303183572864057414927885393/121767022353172157296299377572380672:ℝ) admission43_11_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission43_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_11_coefficients]
def admission43_12_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(41135459/5000000000:ℝ)]
]
theorem admission43_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission43_12_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission43_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_12_coefficients]
def admission43_13_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(20350383012772521847/5000000000000000000000:ℝ)]
]
theorem admission43_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (20350383012772521847/5000000000000000000000:ℝ) admission43_13_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission43_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_13_coefficients]
def admission43_14_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(1/2:ℝ)]
]
theorem admission43_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission43_14_coefficients (15015/32768:ℝ) (7509/16384:ℝ) (4095/8192:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission43_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission43_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission43_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission43_14_coefficients]
theorem admission43_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (15015/32768:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (4095/8192:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission43_00_pos hδ hp
 · exact admission43_01_pos hδ hp
 · exact admission43_02_pos hδ hp
 · exact admission43_03_pos hδ hp
 · exact admission43_04_pos hδ hp
 · exact admission43_05_pos hδ hp
 · exact admission43_06_pos hδ hp
 · exact admission43_07_pos hδ hp
 · exact admission43_08_pos hδ hp
 · exact admission43_09_pos hδ hp
 · exact admission43_10_pos hδ hp
 · exact admission43_11_pos hδ hp
 · exact admission43_12_pos hδ hp
 · exact admission43_13_pos hδ hp
 · exact admission43_14_pos hδ hp
#print axioms admission43_all
end
end RH20261023Finite
