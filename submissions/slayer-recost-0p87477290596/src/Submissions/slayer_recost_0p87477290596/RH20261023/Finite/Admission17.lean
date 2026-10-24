/- Recertified exact full-window admission coefficients, 2026-10-23.
Original mathematical/formal interface: Hailey Collet and Mark Lewko, Apache-2.0.
Generated source; kernel replay status is recorded separately. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Finite.ReturnFormulas
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RH20261023Finite
noncomputable section
def admission17_00_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(189620902752067113/786981005458153:ℝ),(187833921746608960/786981005458153:ℝ)]
]
theorem admission17_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (2934905027290765/3147924021832612:ℝ) admission17_00_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission17_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_00_coefficients]
def admission17_01_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(138467137397287168/786981005458153:ℝ),(137467137397287168/786981005458153:ℝ)]
]
theorem admission17_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (536981005458153/786981005458153:ℝ) admission17_01_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission17_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_01_coefficients]
def admission17_02_coefficients : Fin 1 → Fin 2 → ℝ := ![
  ![(70422330896139254/786981005458153:ℝ),(69941200137369344/786981005458153:ℝ)]
]
theorem admission17_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (273207813036599/786981005458153:ℝ) admission17_02_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission17_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_02_coefficients]
def admission17_03_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(2491256200799484017152/214631183306769:ℝ),(163324603928596249967104/7082829049123377:ℝ),(81114535302213277401088/7082829049123377:ℝ)],
  ![(27220719467924841232640/2360943016374459:ℝ),(162226484279142776646400/7082829049123377:ℝ),(80565720875368252948480/7082829049123377:ℝ)]
]
theorem admission17_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (4917341362021988095/9670422595069784064:ℝ) admission17_03_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission17_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_03_coefficients]
def admission17_04_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(128161906400350663540/71543727768923:ℝ),(253489801215893749248/71543727768923:ℝ),(125334630646165864448/71543727768923:ℝ)],
  ![(1427887865907179908082/786981005458153:ℝ),(2824399174982561633024/786981005458153:ℝ),(1396585884342991060992/786981005458153:ℝ)]
]
theorem admission17_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (5737364073768579/73260777235377152:ℝ) admission17_04_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission17_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_04_coefficients]
def admission17_05_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(1654384393316901024966223/1475589385234036875:ℝ),(3310039754630873588193382/1475589385234036875:ℝ),(551862864477459250571553/491863128411345625:ℝ)],
  ![(63673449186344750545189/59023575409361475:ℝ),(637069519473341529950846/295117877046807375:ℝ),(106229611084588092068717/98372625682269125:ℝ)]
]
theorem admission17_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (63673449186344750545189/1320335031646861184204800:ℝ) admission17_05_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission17_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_05_coefficients]
def admission17_06_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(138031190890177589324773915112836814878720/206239921282991172178485579079197:ℝ),(45447345307122732849188842186998094002176/22915546809221241353165064342133:ℝ),(403983883332194081325030662222899737657344/206239921282991172178485579079197:ℝ),(399366161512575510802114671629891010560/619339102951925441977434171409:ℝ)],
  ![(139645022838795036986961571099258498892800/206239921282991172178485579079197:ℝ),(45982997801396424965061910216305599554560/22915546809221241353165064342133:ℝ),(408784241408100540559193259555836020981760/206239921282991172178485579079197:ℝ),(404150898302068217005614260385417789440/619339102951925441977434171409:ℝ)]
]
theorem admission17_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (142824469153610054541390420781335/1268406482845543305169785183045632:ℝ) admission17_06_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission17_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_06_coefficients]
def admission17_07_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(10529862825688312957861334366025399532/1858017308855776325932302514227:ℝ),(62671501680554021744808205227462524416/5574051926567328977796907542681:ℝ),(31082922575261855417683762703302819840/5574051926567328977796907542681:ℝ)],
  ![(10370920149771510576634993012838272570/1858017308855776325932302514227:ℝ),(61721737513862562401250189654096328960/5574051926567328977796907542681:ℝ),(30609978698377059646324246449152819200/5574051926567328977796907542681:ℝ)]
]
theorem admission17_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (934142416332307728464485060093775/3805219448536629915509355549136896:ℝ) admission17_07_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission17_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_07_coefficients]
def admission17_08_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(875261569599668569655513596815126908628805126374397436723/108868201690768144097595850442988281250000000000000:ℝ),(5692943822214886440017715971363072344888657674576355843/219935760991450796156759293824218750000000000000:ℝ),(3009988028272855264169077587727130056874285083246941715559/108868201690768144097595850442988281250000000000000:ℝ),(1067239055770423111268953861651620653599661199768543009997/108868201690768144097595850442988281250000000000000:ℝ)],
  ![(680200036852119108600432700483993494730469053144507421401/54434100845384072048797925221494140625000000000000:ℝ),(118456429299219026228236315451925798752458326471486568731/3024116713632448447155440290083007812500000000000:ℝ),(4447457330016593713419324892489962254483430885699828153191/108868201690768144097595850442988281250000000000000:ℝ),(140311143371752884309564725609109003896313238703097865607/9897109244615285827054168222089843750000000000000:ℝ)]
]
theorem admission17_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (875261569599668569655513596815126908628805126374397436723/623447154448241445357052813170589040640000000000000000000000:ℝ) admission17_08_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission17_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_08_coefficients]
def admission17_09_coefficients : Fin 2 → Fin 4 → ℝ := ![
  ![(3281946394839431152904668310025978218782258238/54434100845384072048797925221494140625:ℝ),(9669339922205852382730272831982795416624081562/54434100845384072048797925221494140625:ℝ),(3164414917171430799088826523287222364085616128/18144700281794690682932641740498046875:ℝ),(621170523392715010290647232954812664000192512/10886820169076814409759585044298828125:ℝ)],
  ![(120630018676702518119958498476624710017556289/2177364033815362881951917008859765625:ℝ),(1775075990991957458758313985865280201482201631/10886820169076814409759585044298828125:ℝ),(580259649824719906150782561746646383736657152/3628940056358938136586528348099609375:ℝ),(113770666447541438116405750848888469045141504/2177364033815362881951917008859765625:ℝ)]
]
theorem admission17_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (13888020806584648207569061382920955693987/1522087779414651966203742219654758400000000:ℝ) admission17_09_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission17_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_09_coefficients]
def admission17_10_coefficients : Fin 3 → Fin 4 → ℝ := ![
  ![(386332949642788500824781511218688/69168252432845478515625:ℝ),(75636120644871594285679225303552/4611216828856365234375:ℝ),(1110126325288321854234831385450496/69168252432845478515625:ℝ),(40213067444243632308269390790656/7685361381427275390625:ℝ)],
  ![(147954998622060029615612136100352/13833650486569095703125:ℝ),(144725042651823388171209012649472/4611216828856365234375:ℝ),(47166836624351135014204029732864/1537072276285455078125:ℝ),(138281457349968830229821365747712/13833650486569095703125:ℝ)],
  ![(1569770191789806985442044587392/307414455257091015625:ℝ),(13808088375889086468841187732096/922243365771273046875:ℝ),(3678756933577484151189610230272/251520917937619921875:ℝ),(13169998611269891625540550623232/2766730097313819140625:ℝ)]
]
theorem admission17_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (401916461525570423142716999/165041878955857648025600000000:ℝ) admission17_10_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission17_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_10_coefficients]
def admission17_11_coefficients : Fin 2 → Fin 3 → ℝ := ![
  ![(25921797839721831847503634047507483452/5574051926567328977796907542681:ℝ),(51427807017006357160796645544203766784/5574051926567328977796907542681:ℝ),(25506977385593442685176192096930086912/5574051926567328977796907542681:ℝ)],
  ![(25520888305791856167755707752844054610/5574051926567328977796907542681:ℝ),(50629325803583147612848744059289438720/5574051926567328977796907542681:ℝ),(25109397700861245406699741647024373760/5574051926567328977796907542681:ℝ)]
]
theorem admission17_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (1532556012015456872967513528260765/7610438897073259831018711098273792:ℝ) admission17_11_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission17_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_11_coefficients]
def admission17_12_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(41135459/5000000000:ℝ)]
]
theorem admission17_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/5000000000:ℝ) admission17_12_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission17_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_12_coefficients]
def admission17_13_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(20350383012772521847/5000000000000000000000:ℝ)]
]
theorem admission17_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (20350383012772521847/5000000000000000000000:ℝ) admission17_13_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission17_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_13_coefficients]
def admission17_14_coefficients : Fin 1 → Fin 1 → ℝ := ![
  ![(1/2:ℝ)]
]
theorem admission17_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1/2:ℝ) admission17_14_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD,edgeC,oldCapacity,newCapacity,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission17_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission17_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission17_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission17_14_coefficients]
theorem admission17_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission17_00_pos hδ hp
 · exact admission17_01_pos hδ hp
 · exact admission17_02_pos hδ hp
 · exact admission17_03_pos hδ hp
 · exact admission17_04_pos hδ hp
 · exact admission17_05_pos hδ hp
 · exact admission17_06_pos hδ hp
 · exact admission17_07_pos hδ hp
 · exact admission17_08_pos hδ hp
 · exact admission17_09_pos hδ hp
 · exact admission17_10_pos hδ hp
 · exact admission17_11_pos hδ hp
 · exact admission17_12_pos hδ hp
 · exact admission17_13_pos hδ hp
 · exact admission17_14_pos hδ hp
#print axioms admission17_all
end
end RH20261023Finite
