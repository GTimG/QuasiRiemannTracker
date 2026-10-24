/- Recertified exact full-window admission coefficients, 2026-10-23.
Original mathematical/formal interface: Hailey Collet and Mark Lewko, Apache-2.0.
Generated source; kernel replay status is recorded separately. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RH20261023Finite
noncomputable section
def admission45_00_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(12023157972788431593/786981005458153:ℝ),(12021370991782973440/786981005458153:ℝ)]
]
theorem admission45_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (2934905027290765/3147924021832612:ℝ) admission45_00_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission45_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_00_coefficients]
def admission45_01_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(8798896793426378752/786981005458153:ℝ),(8797896793426378752/786981005458153:ℝ)]
]
theorem admission45_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (536981005458153/786981005458153:ℝ) admission45_01_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission45_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_01_coefficients]
def admission45_02_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(4476717939550407926/786981005458153:ℝ),(4476236808791638016/786981005458153:ℝ)]
]
theorem admission45_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (273207813036599/786981005458153:ℝ) admission45_02_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission45_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_02_coefficients]
def admission45_03_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(7007715127965762098338512896/2360943016374459:ℝ),(42041808151794746688837173248/7082829049123377:ℝ),(21018662857996460393821634560/7082829049123377:ℝ)],
  ![(7006965802867666738565021696/2360943016374459:ℝ),(42037312232599103389358817280/7082829049123377:ℝ),(21016414914104103173663752192/7082829049123377:ℝ)]
]
theorem admission45_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (78292246587962296507/154726761521116545024:ℝ) admission45_03_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission45_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_03_coefficients]
def admission45_04_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(367225767644923835878873074/786981005458153:ℝ),(734322444855848628188921856/786981005458153:ℝ),(367096682027524818355617792/786981005458153:ℝ)],
  ![(367299119203177002261275880/786981005458153:ℝ),(734469135077495906009808896/786981005458153:ℝ),(367170020691400060552871936/786981005458153:ℝ)]
]
theorem admission45_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (8205250248928177767/103151174347411030016:ℝ) admission45_04_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission45_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_04_coefficients]
def admission45_05_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(81208458426433956849507262574/295117877046807375:ℝ),(812093252632596839205710539576/1475589385234036875:ℝ),(135350318720027064540910777652/491863128411345625:ℝ)],
  ![(81157544549337265655181778964/295117877046807375:ℝ),(73780376333989546728405039272/134144489566730625:ℝ),(135265470862139755576137020724/491863128411345625:ℝ)]
]
theorem admission45_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (20289386137334316413795444741/432647383170043472840228864000:ℝ) admission45_05_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission45_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_05_coefficients]
def admission45_06_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(2264882383299594176173652782280758053338965737472/206239921282991172178485579079197:ℝ),(754813198548536381305717091464817313301511340032/22915546809221241353165064342133:ℝ),(6791990528015362532700885414178469509097792208896/206239921282991172178485579079197:ℝ),(6797459832960586199100701307795236464634101760/619339102951925441977434171409:ℝ)],
  ![(61224328256033362455486936961696278332869967872/5574051926567328977796907542681:ℝ),(754952443317867522507234001849024451711027380224/22915546809221241353165064342133:ℝ),(6793243647349337404394458805394452204176478830592/206239921282991172178485579079197:ℝ),(618064920272866452279610136726360479686983680/56303554813811403816130379219:ℝ)]
]
theorem admission45_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (18546761110775840822772901377343905/162356029804229543061732503429840896:ℝ) admission45_06_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission45_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_06_coefficients]
def admission45_07_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(2646360673017060589813059156094846274609722/1858017308855776325932302514227:ℝ),(15876131196170719959598820762944350190452736/5574051926567328977796907542681:ℝ),(7937049240519950367349037225201788518400000/5574051926567328977796907542681:ℝ)],
  ![(2645714864277765567558954571422211946531464/1858017308855776325932302514227:ℝ),(15872256591840852713100589910874189148782592/5574051926567328977796907542681:ℝ),(7935112062400230243869548646624790115778560/5574051926567328977796907542681:ℝ)]
]
theorem admission45_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (14780297991633844084794723701895755/60883511176586078648149688786190336:ℝ) admission45_07_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission45_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_07_coefficients]
def admission45_08_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(1340227138490353802536554315638970123399693662500145284965059/5623357525349594219917141035278320312500000000:ℝ),(270433999518329119177400278785697699190907642776171982647348829/378014589204056055894430036260375976562500000000:ℝ),(2435299714002308097239482929963673975700854033750357631778212731/3402131302836504503049870326343383789062500000000:ℝ),(162446227423440898619817388883184023359065472020447579063374293/680426260567300900609974065268676757812500000000:ℝ)],
  ![(162947891172838413234308062183184589460438733605499922273049229/680426260567300900609974065268676757812500000000:ℝ),(271734551683801593866977248637646362378854170364013033632914923/378014589204056055894430036260375976562500000000:ℝ),(2447003541820677123402555318058898826615120709246029787956792187/3402131302836504503049870326343383789062500000000:ℝ),(32645281300953943315299006837414322838405740564789901833782161/136085252113460180121994813053735351562500000000:ℝ)]
]
theorem admission45_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (1340227138490353802536554315638970123399693662500145284965059/540274151589024150253485132746416176758784000000000000000000000:ℝ) admission45_08_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission45_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_08_coefficients]
def admission45_09_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(8935244789435696386941913030154307228749707957489126/10886820169076814409759585044298828125:ℝ),(133985529039878339893887485583214702831700938551084736/54434100845384072048797925221494140625:ℝ),(44647462577795689024908444760827319487300356566679552/18144700281794690682932641740498046875:ℝ),(1785323305631110047222307683286523353476285419487232/2177364033815362881951917008859765625:ℝ)],
  ![(811047853597354377861005339371875754196615767796456/989710924461528582705416822208984375:ℝ),(133779771853580566016711668801325041282196282042205952/54434100845384072048797925221494140625:ℝ),(44578883119207527818732497048281238142340397105414144/18144700281794690682932641740498046875:ℝ),(8912901890397411866221842333949565450536608503693312/10886820169076814409759585044298828125:ℝ)]
]
theorem admission45_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (1037598341982510390950115669280007184778411/121767022353172157296299377572380672000000000:ℝ) admission45_09_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission45_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_09_coefficients]
def admission45_10_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(29892781032321429365703457324829083885568/6288022948440498046875:ℝ),(65738131407187597768591653412115303112704/4611216828856365234375:ℝ),(109520242001858398116668648930305862795264/7685361381427275390625:ℝ),(328430798265046311360795132264143141208064/69168252432845478515625:ℝ)],
  ![(657077526039601104037189585806601774759936/69168252432845478515625:ℝ),(59710699946369570159165817258928115482624/2096007649480166015625:ℝ),(1969673638069542209976879275067020857573376/69168252432845478515625:ℝ),(43753204392009704137210626088599654760448/4611216828856365234375:ℝ)],
  ![(36472985758653078630854329914673120018432/7685361381427275390625:ℝ),(328126979523432448900387751441819628077056/23056084144281826171875:ℝ),(983991271517209799676542225990918887964672/69168252432845478515625:ℝ),(327867204775389252138692940897518083899392/69168252432845478515625:ℝ)]
]
theorem admission45_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (2385547885026529927117320337111/1056268025317488947363840000000000:ℝ) admission45_10_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission45_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_10_coefficients]
def admission45_11_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(6510658310236056556651314685970891425339730/5574051926567328977796907542681:ℝ),(13019654312916268538793224743468659344834560/5574051926567328977796907542681:ℝ),(6508996063404731713525117727390936386764800/5574051926567328977796907542681:ℝ)],
  ![(6509029611241374873475841188415371383742568/5574051926567328977796907542681:ℝ),(13016397127540929014528521981345585156980736/5574051926567328977796907542681:ℝ),(6507367577016068633472478186348122585694208/5574051926567328977796907542681:ℝ)]
]
theorem admission45_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (24241833303183572864057414927885393/121767022353172157296299377572380672:ℝ) admission45_11_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission45_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_11_coefficients]
def admission45_12_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(41135459/5000000000:ℝ)]
]
theorem admission45_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission45_12_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission45_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_12_coefficients]
def admission45_13_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(20350383012772521847/5000000000000000000000:ℝ)]
]
theorem admission45_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (20350383012772521847/5000000000000000000000:ℝ) admission45_13_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission45_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_13_coefficients]
def admission45_14_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(1/2:ℝ)]
]
theorem admission45_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission45_14_coefficients (30033/65536:ℝ) (7509/16384:ℝ) (8191/16384:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission45_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission45_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission45_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission45_14_coefficients]
theorem admission45_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (30033/65536:ℝ) (7509/16384:ℝ))
 (hp : p ∈ Set.Icc (8191/16384:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission45_00_pos hδ hp
 · exact admission45_01_pos hδ hp
 · exact admission45_02_pos hδ hp
 · exact admission45_03_pos hδ hp
 · exact admission45_04_pos hδ hp
 · exact admission45_05_pos hδ hp
 · exact admission45_06_pos hδ hp
 · exact admission45_07_pos hδ hp
 · exact admission45_08_pos hδ hp
 · exact admission45_09_pos hδ hp
 · exact admission45_10_pos hδ hp
 · exact admission45_11_pos hδ hp
 · exact admission45_12_pos hδ hp
 · exact admission45_13_pos hδ hp
 · exact admission45_14_pos hδ hp
#print axioms admission45_all
end
end RH20261023Finite
